# Ёфикатор

Эта программа проставляет буквы Ё в русском тексте. В тех случаях, когда
невозможно определить, нужно ли ставить в данном слове букву Ё (в таких,
словах, как, например, «все», «чем», «нем», «совершенная», «небе», «перед»,
«вселенная», «моем», «отличен»), программа запрашивает об этом оператора ЭВМ.

## Компиляция

Программа написана на языке Оберон с помощью среды
[Free Oberon](https://free.oberon.org/).

Скачайте Free Oberon (версии 1.1.0-alpha7), поместите каталог `Jofikator` в
подкаталог `Programs`, откройте в Free Oberon файл `Jofikator.Mod` и нажмите
`F9`. Также программу можно скомпилировать с помощью `foc` (компилятора
командной строки, поставляемого с Free Oberon).

## Использование

Чтобы в автоматическом режиме расставить буквы Ё в файле, запустите программу
из командной строки, указав ключ `-a`.

```
Jofikator -a myfile.txt
```

## История

Программа была разработана специально для содействия процессу ёфикации работы
Г. В. Ф. Гегеля «Наука логики» в процессе вычитки
[её нового издания](https://github.com/kekcleader/Hegel) в 2024 году.
