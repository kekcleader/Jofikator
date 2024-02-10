MODULE Jofikator;
IMPORT Files, Out, Args, Strings, Int, TB := TermBox, Env, Kernel, Random;
CONST
  version = '1.0.0-alpha1';
  lineLen = 82; (** Maximum length of a single line of text plus 0AX:0DX *)
  promptH = 8; (** Height of the prompt panel in the bottom *)
  defDictFname = 'jo.txt'; (** Default dictionary file name *)
  maxDictLen = 70000; (** Maximum number of words in dictionary *)
  maxWordLen = 27; (** Maximum word length + '*', in letters *)

TYPE
  Mark = POINTER TO MarkDesc; (** Mark inside a line *)
  MarkDesc = RECORD
    begin, end: INTEGER;
    star: BOOLEAN;
    fixed: BOOLEAN;
    original: POINTER TO Word;
    next: Mark
  END;

  Line = POINTER TO LineDesc;
  LineDesc = RECORD
    s: ARRAY lineLen + 1 OF CHAR;
    len: INTEGER; (** Actual length of string s *)
    marks: Mark; (** List of marks *)
    lastMark: Mark; (** Pointer to the last mark *)
    prev, next: Line
  END;

  Text = RECORD
    first, last: Line;
    topVisible: Line; (** The first visible line on the screen *)
    y: INTEGER; (** 0-based visible offset from the top of the text *)
    lineCount: INTEGER
  END;

  Word = ARRAY maxWordLen + 1 OF CHAR;

  Dict = RECORD
    words: ARRAY maxDictLen OF Word;
    len: INTEGER
  END;

  MarkCriteria = PROCEDURE (m: Mark): BOOLEAN;

VAR
  inFile: ARRAY 256 OF CHAR; (** File name of in-file *)
  outFile: ARRAY 256 OF CHAR; (** File name of out-file *)
  dictFname: ARRAY 256 OF CHAR; (** File name of yo-dictionary *)
  autoMode: BOOLEAN; (** Is set to TRUE using option "-s" *)
  T: Text; (** The edited text *)
  redraw: BOOLEAN; (** TRUE when interface needs to be redrawn *)
  quit: BOOLEAN; (** Main loop ends in Run when quit becomes TRUE *)
  W, H: INTEGER; (** Size of TermBox screen *)
  fg, bg: INTEGER; (** Main foreground and background colors *)
  fg2, bg2: INTEGER; (** Secondary foreground and background colors *)
  dict: Dict; (** The yo-dictionary *)
  colors: ARRAY 8 OF INTEGER;

  (** Correction Interface **)
  curLine: Line; (** The line with the current mark, or nil *)
  curMark: Mark; (** The current starred mark in question *)
  curReplacement: Word; (** Currently proposed variation *)

PROCEDURE IsCyr(c: CHAR): BOOLEAN;
RETURN ('а' <= c) & (c <= 'я') OR
       ('А' <= c) & (c <= 'Я') OR
       (c = 'ё') OR (c = 'Ё')
END IsCyr;

(** Dictionary **)

PROCEDURE LoadDict(): BOOLEAN;
VAR ok: BOOLEAN;
  F: Files.File;
  R: Files.Rider;
  c: CHAR;
  errLine: INTEGER;
  i: INTEGER; (* Index of character inside a word *)
  star, done: BOOLEAN;
  s: ARRAY 256 OF CHAR;
BEGIN
  ok := FALSE;
  dict.len := 0;
  F := Files.Old(dictFname);

  (* Try app dir, if default *)
  IF (F = NIL) & (dictFname = defDictFname) THEN
    Env.GetAppDir(s);
    Strings.Append(dictFname, s);
    F := Files.Old(s)
  END;

  IF F = NIL THEN
    Out.String('Ошибка: Невозможно открыть файл со словарём "');
    Out.String(dictFname); Out.Char('"'); Out.Ln
  ELSE
    Files.Set(R, F, 0);
    Files.ReadChar(R, c);
    errLine := -1;
    i := 0;
    star := FALSE;
    done := FALSE;
    WHILE ~done DO
      IF (c = 0AX) OR (c = 0DX) OR (c = 0X) THEN
        IF i # 0 THEN
          IF star THEN
            dict.words[dict.len, i] := '*';
            INC(i);
            star := FALSE
          END;
          dict.words[dict.len, i] := 0X;
          INC(dict.len);
          i := 0
        END;
        IF R.eof THEN done := TRUE END
      ELSIF c = '*' THEN
        star := TRUE
      ELSIF IsCyr(c) THEN
        IF i < maxWordLen - 1 THEN
          dict.words[dict.len, i] := c;
          INC(i)
        ELSIF errLine = -1 THEN
          errLine := dict.len + 1
        END
      ELSIF errLine = -1 THEN
        errLine := dict.len + 1
      END;
      Files.ReadChar(R, c)
    END;
    IF errLine # -1 THEN
      Out.String('Ошибка: в файле словаря на строке '); Out.Int(errLine, 0);
      Out.String(' найдена неопознанная литера или строка слишком длинная');
      Out.Ln
    ELSE
      ok := TRUE
    END
  END;
RETURN ok END LoadDict;

(** Coverts Russian letter to a small letter, converting yo to ye. *)
PROCEDURE Unify(c: CHAR): CHAR;
BEGIN
  IF ('А' <= c) & (c <= 'Я') THEN
    c := CHR(ORD('а') - ORD('А') + ORD(c))
  ELSIF (c = 'Ё') OR (c = 'ё') THEN c := 'е'
  END
RETURN c END Unify;

(** Returns -1 if a < b, +1 if a > b, and 0 if a = b.
    Does a case-insensitive comparison and treats letters
    yo and ye as one and the same letter. *)
PROCEDURE WordsCmp(a, b: Word): INTEGER;
VAR i, x, y, res: INTEGER;
  ac, bc: CHAR;
BEGIN
  i := 0;
  WHILE (a[i] # 0X) & (Unify(a[i]) = Unify(b[i])) DO INC(i) END;
  ac := a[i]; bc := b[i];
  IF ac = '*' THEN ac := 0X END;
  IF bc = '*' THEN bc := 0X END;
  IF ac = bc THEN
    res := 0
  ELSE
    x := ORD(Unify(ac)) - ORD('а');
    y := ORD(Unify(bc)) - ORD('а');
    ASSERT(x # y);
    IF x < y THEN res := -1 ELSE res := 1 END
  END
RETURN res END WordsCmp;

(** Searches s in dict, puts what is found in found, but
    without a star if any, sets star to TRUE if there was a star.
    When searching for a word, does a smart compare: checks yo and ye,
    big and small letters. When found, found is the same as s, but
    with one or more letters ye changed to yo (preserving case).
    Does a binary search.
     If nothing is found, puts empty string in found. *)
PROCEDURE SearchDict(s: Word; VAR found: Word; VAR star: BOOLEAN);
VAR L, C, R: INTEGER; (* left, center, right *)
  cmp: INTEGER;
  i: INTEGER;
  corrected: BOOLEAN;
BEGIN
  found := '';
  L := 0; R := dict.len;
  WHILE L + 1 # R DO
    C := (L + R) DIV 2;
    cmp := WordsCmp(s, dict.words[C]);
    IF cmp < 0 THEN (* s is less *)
      R := C
    ELSIF cmp > 0 THEN (* s is more *)
      L := C
    ELSE (* found *)
      L := C; R := C + 1
    END
  END;

  cmp := WordsCmp(s, dict.words[L]);
  IF cmp = 0 THEN (* Found *)
    corrected := FALSE;
    i := 0;
    WHILE dict.words[L, i] # 0X DO
      IF (dict.words[L, i] = 'ё') & (s[i] # 'ё') & (s[i] # 'Ё') THEN
        IF s[i] = 'е' THEN
          found[i] := 'ё'
        ELSE
          found[i] := 'Ё'
        END;
        corrected := TRUE
      ELSE
        found[i] := s[i]
      END;
      INC(i)
    END;
    IF corrected THEN
      IF dict.words[L, i - 1] = '*' THEN
        star := TRUE;
        DEC(i)
      ELSE
        star := FALSE
      END
    ELSE
      i := 0
    END;
    found[i] := 0X
  END
END SearchDict;

(** Line **)

PROCEDURE NewLine(): Line;
VAR L: Line;
BEGIN
  NEW(L);
  L.s := '';
  L.len := 0;
  L.prev := NIL;
  L.next := NIL;
  L.marks := NIL;
  L.lastMark := NIL
RETURN L END NewLine;

PROCEDURE LineAddMark(L: Line; begin, end: INTEGER;
    star: BOOLEAN; found: Word);
VAR
  M: Mark;
BEGIN
  NEW(M);
  M.next := NIL;
  IF L.marks = NIL THEN
    L.marks := M
  ELSE
    L.lastMark.next := M
  END;
  L.lastMark := M;
  M.begin := begin;
  M.end := end;
  M.star := star;
  M.fixed := FALSE;
  M.original := NIL
END LineAddMark;

(** Appends c to the end of line L. *)
PROCEDURE AppendToLine(L: Line; c: CHAR);
BEGIN
  ASSERT(L.len < LEN(L.s) - 1);
  L.s[L.len] := c;
  INC(L.len);
  L.s[L.len] := 0X
END AppendToLine;

(** Text **)

PROCEDURE InitText(VAR T: Text);
BEGIN
  T.first := NIL;
  T.last := NIL;
  T.topVisible := NIL;
  T.y := 0;
  T.lineCount := 0
END InitText;

PROCEDURE AppendLineToText(L: Line; VAR T: Text);
BEGIN
  IF T.first = NIL THEN
    T.first := L;
    T.topVisible := L;
    L.prev := NIL
  ELSE
    T.last.next := L;
    L.prev := T.last
  END;
  T.last := L;
  L.next := NIL;
  INC(T.lineCount)
END AppendLineToText;

(** Splits line L, shortening it and producing L2 as a new line with
    the characters that are moved from L. L Must be long. *)
PROCEDURE SplitLine(L: Line; VAR L2: Line);
CONST maxSplit = 30;
VAR limit, i, j, point: INTEGER;
BEGIN
  limit := L.len - maxSplit;
  ASSERT(limit > 0);

  (* Find the split point (preferably, a space) *)
  i := L.len - 1;
  WHILE (i # limit) & (L.s[i] # ' ') DO DEC(i) END;
  INC(i);
  point := i;

  (* Copy characters from L to L2 *)
  L2 := NewLine();
  j := 0;
  WHILE i # L.len DO
    L2.s[j] := L.s[i];
    INC(i);
    INC(j)
  END;
  L2.s[j] := 0X;
  L2.len := j;

  (* Truncate L *)
  L.s[point] := 0X;
  L.len := point
END SplitLine;

PROCEDURE SaveTextToFile(VAR T: Text; VAR R: Files.Rider);
VAR L: Line;
  i: INTEGER;
BEGIN
  L := T.first;
  WHILE L # NIL DO
    i := 0;
    WHILE i # L.len DO
      Files.WriteChar(R, L.s[i]);
      INC(i)
    END;
    L := L.next
  END
END SaveTextToFile;

PROCEDURE LoadTextFromFile(VAR T: Text; VAR R: Files.Rider);
VAR c: CHAR;
  L, L2: Line;
BEGIN
  InitText(T);
  Files.ReadChar(R, c);
  L := NewLine();
  WHILE ~R.eof DO
    WHILE ~R.eof & (c # 0AX) & (L.len < lineLen - 2) DO
      AppendToLine(L, c);
      Files.ReadChar(R, c)
    END;
    IF c = 0AX THEN (* Also append 0AX or 0AX:0DX *)
      AppendToLine(L, c);
      Files.ReadChar(R, c);
      IF c = 0DX THEN
        AppendToLine(L, c);
        Files.ReadChar(R, c)
      END;
      AppendLineToText(L, T);
      L := NewLine()
    ELSE
      SplitLine(L, L2);
      AppendLineToText(L, T);
      L := L2
    END
  END
END LoadTextFromFile;

(** Parse **)

PROCEDURE ReplaceInLine(L: Line; pos: INTEGER; s: Word);
VAR i: INTEGER;
BEGIN
  i := 0;
  WHILE s[i] # 0X DO
    L.s[pos] := s[i];
    INC(pos);
    INC(i)
  END
END ReplaceInLine;

(** Parses a single word s inside line L, which (s) starts from begin
    and ends in (end - 1). *)
PROCEDURE ParseWord(L: Line; s: Word; begin, end: INTEGER);
VAR i: INTEGER;
  found: Word;
  star: BOOLEAN;
BEGIN
  SearchDict(s, found, star);
  IF found # '' THEN
    IF ~star THEN
      ReplaceInLine(L, begin, found)
    END;
    LineAddMark(L, begin, end, star, found)
  END
END ParseWord;

PROCEDURE ParseLine(L: Line);
VAR
  i: INTEGER; (* Index on L.s *)
  j: INTEGER; (* Index on word *)
  c: CHAR; (* Current character *)
  lastCyr: BOOLEAN; (* TRUE = previous character was a cyrillic letter *)
  cyr: BOOLEAN; (* TRUE = c is a cyrillic letter *)
  word: Word;
  done: BOOLEAN;
BEGIN
  lastCyr := FALSE; j := 0;
  i := 0; c := L.s[0]; cyr := IsCyr(c);
  done := FALSE;
  WHILE ~done DO
    IF cyr THEN
      IF j < LEN(word) - 2 THEN (* 2 because of a star in the dictionary *)
        word[j] := c;
        INC(j)
      ELSE
        j := 0 (* Dispose the word, as it is too long *)
      END
    ELSIF j # 0 THEN (* And current character is not a cyrillic letter *)
      word[j] := 0X;
      ParseWord(L, word, i - j, i);
      j := 0
    END;
    INC(i);
    IF i < L.len THEN
      c := L.s[i]; cyr := IsCyr(c)
    ELSIF c = 0X THEN
      done := TRUE
    ELSE
      c := 0X; cyr := FALSE
    END
  END
END ParseLine;

PROCEDURE ParseText;
VAR L: Line;
BEGIN
  L := T.first;
  WHILE L # NIL DO
    ParseLine(L);
    L := L.next
  END
END ParseText;

(** Interface **)

PROCEDURE DrawLine(L: Line; x, y, w: INTEGER);
VAR i: INTEGER;
  c: CHAR;
  M: Mark;
  FG, BG: INTEGER;
BEGIN
  M := L.marks;
  i := 0; c := L.s[0];
  WHILE (c # 0X) & (i < w) &
        ((c # 0AX) OR (i < L.len - 2)) &
        ((c # 0DX) OR (i < L.len - 1))
  DO
    IF L = curLine THEN BG := 1 ELSE BG := 0 END;
    IF (M # NIL) & (M.begin <= i) & (i < M.end) THEN
      IF M = curMark THEN FG := 4; BG := 3
      ELSIF M.fixed THEN FG := 6
      ELSIF ~M.star THEN FG := 5
      ELSIF M = curMark THEN FG := 4
      ELSE FG := 3
      END;
    ELSE
      FG := 2;
      IF (M # NIL) & (i >= M.end) THEN
        M := M.next
      END
    END;
    TB.SetCell(x + i, y, L.s[i], colors[FG], colors[BG]);
    INC(i);
    c := L.s[i]
  END;
  IF (i < w) & (c # 0AX) THEN
    TB.SetCell(x + i, y, '»', colors[7], colors[BG])
  END
END DrawLine;

PROCEDURE DrawText(x, y, w, h: INTEGER);
VAR L: Line;
  Y: INTEGER;
BEGIN
  Y := y;
  L := T.topVisible;
  WHILE (L # NIL) & (Y < y + h) DO
    DrawLine(L, x, Y, w);
    L := L.next;
    INC(Y)
  END
END DrawText;

PROCEDURE DrawFrame(x, y, w, h, fg, bg: INTEGER);
VAR i, x2, y2: INTEGER;
BEGIN
  x2 := x + w - 1;
  y2 := y + h - 1;

  FOR i := x + 1 TO x2 - 1 DO
    TB.SetCell(i, y, TB.doubleHor, fg, bg);
    TB.SetCell(i, y2, TB.doubleHor, fg, bg)
  END;

  FOR i := y + 1 TO y2 - 1 DO
    TB.SetCell(x, i, TB.doubleVert, fg, bg);
    TB.SetCell(x2, i, TB.doubleVert, fg, bg)
  END;

  (* Corners: *)
  TB.SetCell(x2, y2, TB.doubleUpLeft, fg, bg);
  TB.SetCell(x , y2, TB.doubleUpRight, fg, bg);
  TB.SetCell(x2, y , TB.doubleDownLeft, fg, bg);
  TB.SetCell(x , y , TB.doubleDownRight, fg, bg)
END DrawFrame;

PROCEDURE DrawPrompt(x, y, w, h: INTEGER);
VAR len, percent: INTEGER;
    s: ARRAY 7 OF CHAR;
BEGIN
  TB.Fill(x + 1, y + 1, w - 2, h - 2, ' ', colors[2], colors[1]);
  DrawFrame(x, y, w, h, colors[2], colors[1]);
  len := Strings.Length(curReplacement);
  IF len # 0 THEN
    TB.Print(x + (w - len) DIV 2,
      y + 1, -1, curReplacement, colors[2], colors[1]);
    TB.SetCell(x + (w - len) DIV 2 + len,
      y + 1, '?', colors[4], colors[1]);
  END;

  TB.Print(x + w - 12, y + h - 1, -1,
    ' Ёфикатор ', colors[2], colors[1]);

  percent := T.y * 100 DIV (T.lineCount - (H - promptH));
  s := ' '; Int.Append(percent, s); Strings.Append('% ', s);
  TB.Print(x + w - 2 - Strings.Length(s), y, -1, s, colors[2], colors[1]);

  INC(y, 2);
  TB.Print(x + 2, y, w - 4,
    'Используемые клавиши',
    colors[4], colors[1]);

  x := x + (w - 74) DIV 2 + 1;

  TB.Print(x, y + 1, w - 4,
    '1 - ВПИСАТЬ "Ё"      2 - ОСТАВИТЬ "Е"      3 - ОТЛОЖИТЬ',
    colors[4], colors[1]);
  TB.Print(x, y + 2, w - 4,
    'Забой - на предыдущий "1" или "2"',
    colors[4], colors[1]);
  TB.Print(x, y + 3, w - 4,
    'Таб - к следующему необработанному     Сдвиг+Таб - к предыдущ. необработ.',
    colors[4], colors[1]);
  TB.Print(x, y + 4, w - 4,
    'Ф2 - сохранить        Сдвиг+Выход - завершить программу',
    colors[4], colors[1])
END DrawPrompt;

PROCEDURE Draw;
VAR p: Line;
  i: INTEGER;
BEGIN
  TB.Fill(0, 0, W, H, ' ', colors[2], colors[0]);
  DrawText(0, 0, W, H - promptH);
  DrawPrompt(0, H - promptH, W, promptH);
  TB.Flush
END Draw;

PROCEDURE MoveVert(down, ignoreBottomLimit: BOOLEAN);
BEGIN
  IF T.topVisible # NIL THEN
    IF down THEN
      IF (T.topVisible.next # NIL) &
         (ignoreBottomLimit OR (T.y < T.lineCount - (H - promptH)))
      THEN
        T.topVisible := T.topVisible.next;
        INC(T.y)
      END
    ELSIF T.topVisible.prev # NIL THEN
      T.topVisible := T.topVisible.prev;
      DEC(T.y)
    END
  END
END MoveVert;

PROCEDURE MovePageVert(down: BOOLEAN);
VAR i: INTEGER;
BEGIN
  FOR i := 1 TO H - promptH DO
    MoveVert(down, FALSE)
  END
END MovePageVert;

PROCEDURE MoveToLimit(down: BOOLEAN);
VAR i: INTEGER;
BEGIN
  IF T.topVisible # NIL THEN
    IF down THEN
      T.topVisible := T.last;
      T.y := T.lineCount - 1;
      IF T.y < 0 THEN T.y := 0 END;
      FOR i := 1 TO H - promptH - 1 DO
        MoveVert(FALSE, FALSE)
      END
    ELSE
      T.topVisible := T.first;
      T.y := 0
    END
  END
END MoveToLimit;

PROCEDURE CenterOnLine(L: Line);
VAR i: INTEGER;
BEGIN
  IF (T.topVisible # NIL) & (L # NIL) THEN
    MoveToLimit(FALSE);
    WHILE (T.topVisible.next # NIL) & (T.topVisible # L) DO
      MoveVert(TRUE, TRUE)
    END;
    FOR i := (H - promptH) DIV 2 TO 1 BY -1 DO
      MoveVert(FALSE, FALSE)
    END
  END
END CenterOnLine;

PROCEDURE SetReplacementWord;
VAR s: Word;
  i, j: INTEGER;
  star: BOOLEAN;
BEGIN
  IF curMark = NIL THEN
    curReplacement := ''
  ELSE
    i := curMark.begin; j := 0;
    WHILE i # curMark.end DO
      s[j] := curLine.s[i];
      INC(i); INC(j)
    END;
    s[j] := 0X;

    SearchDict(s, curReplacement, star)
  END
END SetReplacementWord;

PROCEDURE FixCurMark;
VAR s, found: Word;
  i, j: INTEGER;
  star: BOOLEAN;
BEGIN
  i := curMark.begin; j := 0;
  WHILE i # curMark.end DO
    s[j] := curLine.s[i];
    INC(i); INC(j)
  END;
  s[j] := 0X;

  SearchDict(s, found, star);
  IF found # '' THEN
    NEW(curMark.original);
    curMark.original^ := s;
    ReplaceInLine(curLine, curMark.begin, found)
  END
END FixCurMark;

PROCEDURE RestoreCurMark;
BEGIN
  ReplaceInLine(curLine, curMark.begin, curMark.original^)
END RestoreCurMark;

PROCEDURE PrevLineWithMark(L: Line): Line;
BEGIN
  IF L = NIL THEN L := T.last ELSE L := L.prev END;
  WHILE (L # NIL) & (L.marks = NIL) DO
    L := L.prev
  END
RETURN L END PrevLineWithMark;

PROCEDURE NextLineWithMark(L: Line): Line;
BEGIN
  IF L = NIL THEN L := T.first ELSE L := L.next END;
  WHILE (L # NIL) & (L.marks = NIL) DO
    L := L.next
  END
RETURN L END NextLineWithMark;

PROCEDURE GoToFirstMark;
BEGIN
  curMark := NIL;
  curLine := NextLineWithMark(NIL);
  WHILE (curMark = NIL) & (curLine # NIL) DO
    curMark := curLine.marks;
    WHILE (curMark # NIL) & ~curMark.star DO
      curMark := curMark.next
    END;

    IF curMark = NIL THEN
      curLine := NextLineWithMark(curLine)
    END
  END;
  CenterOnLine(curLine)
END GoToFirstMark;

PROCEDURE GoToLastMark;
VAR M: Mark;
BEGIN
  curMark := NIL;
  curLine := PrevLineWithMark(NIL);
  WHILE (curMark = NIL) & (curLine # NIL) DO
    M := curLine.marks;
    WHILE M # NIL DO
      IF M.star THEN curMark := M END;
      M := M.next
    END;

    IF curMark = NIL THEN
      curLine := PrevLineWithMark(curLine)
    END
  END;
  CenterOnLine(curLine)
END GoToLastMark;

PROCEDURE GoToPrevMark(criteria: MarkCriteria);
VAR M, Q: Mark;
  done: BOOLEAN;
BEGIN
  done := FALSE;
  IF curMark = NIL THEN
    GoToLastMark;
    IF (curMark # NIL) & criteria(curMark) THEN
      done := TRUE
    END
  END;
  IF (curMark # NIL) & ~done THEN
    Q := NIL;
    M := curLine.marks;
    WHILE M # curMark DO
      IF criteria(M) THEN Q := M END;
      M := M.next
    END;
    IF Q # NIL THEN
      curMark := Q
    ELSE
      curLine := PrevLineWithMark(curLine);
      curMark := NIL;
      WHILE (curMark = NIL) & (curLine # NIL) DO
        Q := NIL;
        M := curLine.marks;
        WHILE M # NIL DO
          IF criteria(M) THEN Q := M END;
          M := M.next
        END;
        IF Q # NIL THEN
          curMark := Q
        ELSE
          curLine := PrevLineWithMark(curLine)
        END
      END;
      IF curLine = NIL THEN curMark := NIL END
    END
  END;
  CenterOnLine(curLine)
END GoToPrevMark;

PROCEDURE GoToNextMark(criteria: MarkCriteria);
VAR done: BOOLEAN;
BEGIN
  done := FALSE;
  IF curMark = NIL THEN
    GoToFirstMark;
    IF (curMark # NIL) & criteria(curMark) THEN
      done := TRUE
    END
  END;
  IF (curMark # NIL) & ~done THEN
    curMark := curMark.next;
    WHILE (curMark # NIL) & ~criteria(curMark) DO
      curMark := curMark.next
    END;

    IF curMark = NIL THEN
      curLine := NextLineWithMark(curLine);

      WHILE (curMark = NIL) & (curLine # NIL) DO
        curMark := curLine.marks;
        WHILE (curMark # NIL) & ~criteria(curMark) DO
          curMark := curMark.next
        END;

        IF curMark = NIL THEN
          curLine := NextLineWithMark(curLine)
        END
      END;
      IF curLine = NIL THEN curMark := NIL END
    END
  END;
  CenterOnLine(curLine)
END GoToNextMark;

PROCEDURE MarkStarredAndNotFixed(m: Mark): BOOLEAN;
RETURN m.star & ~m.fixed END MarkStarredAndNotFixed;

PROCEDURE MarkFixed(m: Mark): BOOLEAN;
RETURN m.fixed END MarkFixed;

PROCEDURE MarkStarred(m: Mark): BOOLEAN;
RETURN m.star END MarkStarred;

PROCEDURE OnCommand(command: INTEGER);
BEGIN
  IF curMark # NIL THEN
    IF command = 1 THEN
      FixCurMark
    ELSIF (command = 2) & (curMark.original # NIL) THEN
      RestoreCurMark
    END;
    IF command # 3 THEN
      curMark.fixed := TRUE
    ELSIF curMark.original # NIL THEN
      RestoreCurMark;
      curMark.fixed := FALSE
    END
  END;
  GoToNextMark(MarkStarredAndNotFixed);
  SetReplacementWord
END OnCommand;

PROCEDURE OnTab;
VAR M: Mark;
  L: Line;
BEGIN
  M := curMark; L := curLine;
  GoToNextMark(MarkStarredAndNotFixed);
  IF curMark = NIL THEN
    GoToNextMark(MarkStarredAndNotFixed);
    IF curMark = NIL THEN
      curMark := M; curLine := L;
      GoToNextMark(MarkStarred)
    END
  END;
  SetReplacementWord
END OnTab;

PROCEDURE OnShiftTab;
VAR M: Mark;
  L: Line;
BEGIN
  M := curMark; L := curLine;
  GoToPrevMark(MarkStarredAndNotFixed);
  IF curMark = NIL THEN
    GoToPrevMark(MarkStarredAndNotFixed);
    IF curMark = NIL THEN
      curMark := M; curLine := L;
      GoToPrevMark(MarkStarred)
    END
  END;
  SetReplacementWord
END OnShiftTab;

PROCEDURE OnBackspace;
BEGIN
  GoToPrevMark(MarkStarred);
  SetReplacementWord
END OnBackspace;

PROCEDURE DoSave;
VAR F: Files.File;
  R: Files.Rider;
BEGIN
  F := Files.New(outFile);
  Files.Set(R, F, 0);
  SaveTextToFile(T, R);
  Files.Register(F)
END DoSave;

PROCEDURE OnSave;
CONST w = 30; h = 5;
BEGIN
  DoSave;

  TB.Fill((W - w - 4) DIV 2, (H - h - 2) DIV 2, w + 4, h + 2, ' ', 15, 15);
  TB.Fill((W - w) DIV 2, (H - h) DIV 2, w, h, ' ', 15, 2);
  TB.Print((W - 11) DIV 2, H DIV 2, -1, ' СОХРАНЕНО ', 15, 2);
  TB.Sync;
  TB.Delay(1000);
  redraw := TRUE
END OnSave;

PROCEDURE HandleKey(key: INTEGER; shift: BOOLEAN);
BEGIN
  redraw := TRUE;
  IF    key = TB.kUp        THEN MoveVert(FALSE, FALSE)
  ELSIF key = TB.kDown      THEN MoveVert(TRUE, FALSE)
  ELSIF key = TB.kPgUp      THEN MovePageVert(FALSE)
  ELSIF key = TB.kPgDn      THEN MovePageVert(TRUE)
  ELSIF key = TB.kHome      THEN MoveToLimit(FALSE)
  ELSIF key = TB.kEnd       THEN MoveToLimit(TRUE)
  ELSIF key = TB.k1         THEN OnCommand(1)
  ELSIF key = TB.k2         THEN OnCommand(2)
  ELSIF key = TB.k3         THEN OnCommand(3)
  ELSIF key = TB.kBackspace THEN OnBackspace
  ELSIF key = TB.kF2        THEN OnSave
  ELSIF key = TB.kTab THEN
    IF shift THEN OnShiftTab ELSE OnTab END
  ELSIF key = TB.kEsc THEN
    IF shift THEN quit := TRUE END
  ELSE redraw := FALSE
  END
END HandleKey;

PROCEDURE Run;
VAR E: TB.Event;
BEGIN
  quit := FALSE;
  redraw := TRUE;
  WHILE ~quit DO
    IF redraw & ~TB.HasEvents() THEN
      Draw;
      redraw := FALSE
    END;
    TB.WaitEvent(E);
    IF E.type = TB.key THEN
      HandleKey(E.key, TB.mShift IN E.mod)
    END
  END
END Run;

(** Prepares the invokation on Run: reads the in-file,
    opens the out-file. Marks words with Ye,
    replaces some with Yo, marks uncertain words.
    Returns TRUE on success, or FALSE. *)
PROCEDURE Init(): BOOLEAN;
VAR inF: Files.File;
  R: Files.Rider;
BEGIN
  IF LoadDict() THEN
    inF := Files.Old(inFile);
    IF inF = NIL THEN
      Out.String('Ошибка: Невозможно открыть входной файл'); Out.Ln
    ELSE
      Files.Set(R, inF, 0);
      LoadTextFromFile(T, R);
      ParseText;
      IF ~autoMode THEN
        TB.SetFontFile('Data/Fonts/Main');
        TB.Settings(80, 25, {TB.exact});
        TB.Init;
        IF ~TB.Done THEN
          Out.String('Ошибка: Невозможно загрузить текстовую систему'); Out.Ln
        ELSE
          TB.HideCursor;
          TB.Size(W, H)
        END;
        GoToFirstMark;
        SetReplacementWord
      END
    END
  END
RETURN (inF # NIL) & (autoMode OR TB.Done) END Init;

PROCEDURE Close;
BEGIN
  TB.Close
END Close;

PROCEDURE Usage;
VAR s: ARRAY 256 OF CHAR;
BEGIN
  Out.String('Ёфикатор, версия '); Out.String(version); Out.Ln;
  Out.String('Средство полуавтоматической ёфикации (ёфикатор)'); Out.Ln;
  Out.String('Использование:'); Out.Ln;
  Out.String('  '); Args.Get(0, s); Out.String(s);
  Out.String(' {опции} вхФайл'); Out.Ln; Out.Ln;
  Out.String('  вхФайл  - подлежащий ёфикации текстовый файл'); Out.Ln;
  Out.String('Опции:'); Out.Ln;
  Out.String('  -o выхФайл   Куда сохранить ёфицированный файл'); Out.Ln;
  Out.String('               (если не указан, приписывается расширение ".jo".)');
  Out.Ln;
  Out.String('  -d словарь   Имя файла со словарём'); Out.Ln;
  Out.String('               (по умолчанию '); Out.String(defDictFname);
  Out.Char(')'); Out.Ln;
  Out.String('  -a           Автоматический режим. Обрабатывает файл, расставляя');
  Out.Ln;
  Out.String('               буквы Ё только в безусловных местах и сохраняет');
  Out.Ln;
  Out.String('               результат в тот же файл (если не указано иное).');
  Out.Ln;
  Out.String('  -c цвета     Основной цвет текста и фона, затем второстепенный');
  Out.Ln;
  Out.String('               цвет текста и фона в формате 1:2:3:4 (числа от 0 до 15);');
  Out.Ln;
  Out.String('               можно указать от 1 до 4 цветов.');
  Out.Ln; Out.Ln
END Usage;

PROCEDURE Do;
VAR i: INTEGER;
  s: ARRAY 256 OF CHAR;
  T: Text;

  PROCEDURE ParseColorArgs(VAR s: ARRAY OF CHAR);
  VAR i, n, col: INTEGER;
  BEGIN
    i := Strings.Pos(':', s, 0);
    n := 0;
    WHILE (i # -1) & (n # LEN(colors)) DO
      s[i] := 0X;
      colors[n] := Int.Val(s) MOD 16;
      s[i] := ':';
      Strings.Delete(s, 0, i + 1);
      i := Strings.Pos(':', s, 0);
      INC(n)
    END
  END ParseColorArgs;

BEGIN
  IF Args.Count() = 0 THEN
    Usage
  ELSE
    inFile := ''; outFile := ''; dictFname := defDictFname;
    autoMode := FALSE;
    i := 1;
    WHILE i <= Args.Count() DO
      Args.Get(i, s);
      IF s[0] = '-' THEN
        IF s = '-o' THEN
          INC(i);
          IF outFile = '' THEN
            Args.Get(i, outFile)
          ELSE
            Out.String('Ошибка: Выходной файл уже указан: ');
            Out.String(outFile); Out.Ln
          END
        ELSIF s = '-c' THEN
          INC(i);
          Args.Get(i, s);
          ParseColorArgs(s)
        ELSIF s = '-d' THEN
          INC(i);
          Args.Get(i, dictFname)
        ELSIF s = '-a' THEN
          autoMode := TRUE
        ELSE
          Out.String('Ошибка: неизвестная опция '); Out.String(s); Out.Ln
        END
      ELSIF inFile = '' THEN
        Args.Get(i, inFile)
      ELSE
        Out.String('Ошибка: Входной файл уже указан: ');
        Out.String(inFile); Out.Ln
      END;
      INC(i)
    END;
    IF inFile = '' THEN
      Out.String('Ошибка: Входной файл не указан.'); Out.Ln
    ELSE
      IF outFile = '' THEN
        Strings.Copy(inFile, outFile);
        IF ~autoMode THEN
          Strings.Append('.jo', outFile)
        END
      END;
      IF Init() THEN
        IF autoMode THEN
          DoSave
        ELSE
          Run;
          Close
        END
      END
    END
  END
END Do;

BEGIN
  colors[0] :=  1; (* Main background *)
  colors[1] :=  6; (* Highlighted background *)
  colors[2] := 15; (* Main text color *)
  colors[3] := 14; (* Current mark background *)
  colors[4] :=  0; (* Current mark text color *)
  colors[5] := 10; (* Text color of autocorrected word *)
  colors[6] := 12; (* Text color of user-corrected word *)
  colors[7] := 11; (* Text color of no-new-line indicator *)
  curReplacement := '';
  Do
END Jofikator.
