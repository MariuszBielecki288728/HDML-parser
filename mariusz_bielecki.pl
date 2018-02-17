% Definiujemy moduł zawierający rozwiązanie.
% Należy zmienić nazwę modułu na {imie}_{nazwisko} gdzie za
% {imie} i {nazwisko} należy podstawić odpowiednio swoje imię
% i nazwisko bez wielkich liter oraz znaków diakrytycznych
:- module(mariusz_bielecki, [parse/3]).

% Główny predykat rozwiązujący zadanie.
% UWAGA: to nie jest jeszcze rozwiązanie; należy zmienić jego
% definicję.


parse(_Path, Codes, Program) :-
  phrase(lexer(TokList), Codes),
  phrase(program(Program), TokList).


%faza pierwsza lexer
lexer(Tokens) -->
   white_space,
   (  (  "(",       !, { Token = tokLNaw }
      ;  ")",       !, { Token = tokPNaw }
      ;  "[",       !, { Token = tokLNawKw}
      ;  "]",       !, { Token = tokPNawKw }
      ;  "..",      !, { Token = tokDwukropek }
      ;  ",",       !, { Token = tokPrzecinek }
      ;  "=",       !, { Token = tokRowny }
      ;  "<>",      !, { Token = tokRozny }
      ;  "<",       !, { Token = tokMniejszy }
      ;  ">",       !, { Token = tokWiekszy }
      ;  "<=",      !, { Token = tokMniejszyRowny }
      ;  ">=",      !, { Token = tokWiekszyRowny }
      ;  "^",       !, { Token = tokDaszek }
      ;  "|",       !, { Token = tokPatyczek }
      ;  "+",       !, { Token = tokPlus }
      ;  "-",       !, { Token = tokMinus }
      ;  "&",       !, { Token = tokEt }
      ;  "*",       !, { Token = tokRazy }
      ;  "/",       !, { Token = tokDziel }
      ;  "%",       !, { Token = tokProcent }
      ;  "@",       !, { Token = tokMalpa }
      ;  "#",       !, { Token = tokDrabinka }
      ;  "~",       !, { Token = tokFala }

      ;  digit(D),  !,
            number(D, N),
            { Token = tokLiczba(N) }
      ;  letter(L), !, identifier(L, Id),
            {  member((Id, Token), [ (def, tokDef),
                                     (else, tokElse),
                                     (if, tokIf),
                                     (in, tokIn),
                                     (let, tokLet),
                                     (then, tokThen),
                                     ('_', tokDzikaKarta)]),
               !
            ;  Token = tokIdentyfikator(Id)
            }
    %  ;
      %  "_",       !, { Token = tokDzikaKarta}
      ;  [_],
            { Token = tokUnknown }
      ),
      !,
         { Tokens = [Token | TokList] },
      lexer(TokList)
   ;  [],
         { Tokens = [] }
   ).

%tu usuwam komentarze
comment(0) -->
  !.
comment(I) -->
  "*)",
  !,
  {NewI is I - 1},
  comment(NewI).
comment(I) -->
  "(*",!,
  {NewI is I+1},
  comment(NewI).
comment(I) -->
  [_],
  comment(I).

white_space -->
   [Char], { code_type(Char, space) }, !, white_space.
white_space -->
  "(*", !, comment(1), white_space.
white_space -->
   [].

digit(D) -->
   [D],
      { code_type(D, digit) }.

digits([D|T]) -->
   digit(D),
   !,
   digits(T).
digits([]) -->
   [].

number(D, N) -->
   digits(Ds),
      { number_chars(N, [D|Ds]) }.

letter(L) -->
   [L], { code_type(L, csymf) }.


alphanum([A|T]) -->
   [A], { code_type(A, csym) }, !, alphanum(T).
alphanum([A|T]) -->
   [A], {A = 39},!, alphanum(T).
alphanum([]) -->
   [].



identifier(L, Id) -->
   alphanum(As),
      { atom_codes(Id, [L|As]) }.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%faza 2
%gramatyka prawie przepisana, ale usunięte lewostronne rekursje 
%i operatory obslugujace lacznosc i priorytet
program(AST) -->
  definicje(AST).

definicje([H|T]) -->
  definicja(H),
  definicje(T).
definicje([])-->
  [].

definicja(Def)-->
  [tokDef], [tokIdentyfikator(Id)],
  [tokLNaw],!, wzorzec(Wz), [tokPNaw],
  [tokRowny], wyrazenie(Wyr),
  {Def = def(Id, Wz, Wyr)}.

wzorzec(Y)-->
  wzorzec_(Y).
wzorzec(Wz)-->
  wzorzec_(X),[tokPrzecinek],!, wzorzec(Y),
  {Wz = pair(no, X, Y)}.

wzorzec_(Wz)-->
  [tokDzikaKarta],!,
  {Wz = wildcard(no)}.
wzorzec_(Wz)-->
  zmienna(Wz).
wzorzec_(Wz)-->
  [tokLNaw],wzorzec(Wz),!,[tokPNaw].



wyrazenie(Wyr) -->
  [tokIf],!, wyrazenie(E1),
  [tokThen],!, wyrazenie(E2),
  [tokElse],!, wyrazenie(E3),
  {Wyr = if(no, E1, E2, E3)}.

wyrazenie(Wyr) -->
  [tokLet],!, wzorzec(P),
  [tokRowny], wyrazenie(E1),
  [tokIn],!, wyrazenie(E2),
  {Wyr = let(no, P, E1, E2)}.

wyrazenie(Wyr) -->
  wyrazenieOp(Wyr).


wyrazenieOp(WyrP) -->
  wyr1(WyrP);
  operatorUn(X),!, wyrazenieProste(Y),
  {WyrP = op(no, X, Y)};
  wyrazenieProste(WyrP).


wyr1(S) --> wyr2(S).
wyr1(S) -->
  wyr2(X), op_1(_),!, wyr1(Y),
  {S = pair(no, X, Y)}.

wyr2(S) --> wyr3(S).
wyr2(S) -->
  wyr3(X), op_2(Op),!, wyr3(Y),
  {S = op(no, Op, X, Y)}.

wyr3(S) --> wyr4(S).
wyr3(S) -->
  wyr4(P), op_3(Op),!, wyr3(L),
  {S = op(no, Op, P, L)}.

wyr4(S) --> wyr5(S).
wyr4(S) -->
  wyr5(P), wyr4(P, S).
wyr4(Acc, Expr) -->
  op_4(Op), !, wyr5(P),
  {Acc1 = op(no, Op, Acc, P)}, wyr4(Acc1, Expr).
wyr4(Acc, Acc) -->
  [].

wyr5(S) --> wyr6(S).
wyr5(S) -->
  wyr6(P), wyr5(P, S).
wyr5(Acc, Expr) -->
  op_5(Op), !, wyr6(P),
  {Acc1 = op(no, Op, Acc, P)}, wyr5(Acc1, Expr).
wyr5(Acc, Acc) -->
  [].

wyr6(S) -->
  operatorUn(X),!, wyrazenieProste(Y),
  {S = op(no, X, Y)}.
wyr6(S) -->
  wyrazenieProste(S).


op_5(Op) -->
	[tokEt], !, {Op = '&'}      ;
	[tokRazy], !, {Op = '*'}    ;
	[tokDziel], !, {Op = '/'}   ;
	[tokProcent], {Op = '%'}    .

op_4(Op) -->
	[tokPatyczek], !, {Op = '|'};
	[tokDaszek], !, {Op = '^'}  ;
	[tokPlus], !, {Op = '+'}    ;
	[tokMinus], {Op = '-'}      .

op_3(Op) --> [tokMalpa],{Op = '@'}.

op_2(Op) -->
	[tokMniejszy], !, {Op = '<'}       ;
	[tokMniejszyRowny], !, {Op = '<='} ;
	[tokWiekszy], !, {Op = '>'}        ;
	[tokWiekszyRowny], !, {Op = '>='}  ;
	[tokRozny], !, {Op = '<>'}         ;
	[tokRowny], {Op = '='}             .

op_1(',') --> [tokPrzecinek].

operatorUn('-') -->
  [tokMinus],!.
operatorUn('#') -->
  [tokDrabinka],!.
operatorUn('~') -->
  [tokFala].


wyrazenieProste(Wyr) -->
  [tokLNaw], wyrazenie(Wyr), [tokPNaw],!.

wyrazenieProste(Wyr) -->
  wyrazenieAtom(Wyr).

wyrazenieProste(Wyr_) -->
  wyrazenieAtom(Wyr), wyrazenieProste(Wyr, Wyr_).
wyrazenieProste(Acc, Wyr) -->
  wybBit(W),!,
  {Acc1 = bitsel(no, Acc, W)}, wyrazenieProste(Acc1, Wyr).
wyrazenieProste(Acc, Wyr) -->
  wybBity(W, WW),!,
  {Acc1 = bitsel(no, Acc, W, WW)}, wyrazenieProste(Acc1, Wyr).
wyrazenieProste(Acc, Acc) -->
  [].

wybBit(E2)-->
  [tokLNawKw],!, wyrazenie(E2), [tokPNawKw].

wybBity(E2, E3) -->
  [tokLNawKw],
  wyrazenie(E2), [tokDwukropek],!, wyrazenie(E3), [tokPNawKw].

wyrazenieAtom(Atom) -->
  zmienna(Atom).
wyrazenieAtom(Atom) -->
  wywolanie(Atom).
wyrazenieAtom(Atom) -->
  [tokLiczba(X)],!,
  {Atom=num(no, X)}.
wyrazenieAtom(Atom) -->
  pustyWek(Atom).
wyrazenieAtom(Atom) -->
  pojBit(Atom).

zmienna(Zm) -->
  [tokIdentyfikator(Id)],
  {Zm = var(no, Id)}.

wywolanie(Wyw) -->
  [tokIdentyfikator(Id)],
  [tokLNaw], wyrazenie(E), [tokPNaw],
  {Wyw = call(no, Id, E)}.

pustyWek(Wek) -->
  [tokLNawKw], [tokPNawKw],
  {Wek = empty(no)}.

pojBit(Bit) -->
  [tokLNawKw], wyrazenie(Wyr), [tokPNawKw],
{Bit = bit(no, Wyr)}.
