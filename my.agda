module my where

module ThrowAwayIntroduction where

data Bool : Set where
  true false : Bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data Id (A : Set) : Set where
  pack : A → Id A

data ⊥ : Set where

idℕ₀ : ℕ → ℕ
idℕ₀ x = x

idℕ₁ : (n : ℕ) → ℕ
idℕ₁ x = x

idℕ₂ : (_ : ℕ) → ℕ
idℕ₂ x = x

id₀ : (A : Set) → A → A
id₀ _ a = a

not : Bool → Bool
not true  = false
not false = true

id : {A : Set} → A → A
id a = a

unpack : ∀ {A} → Id A → A
unpack (pack x) = x

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then a else _ = a
if false then _ else b = b

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

[_] : {A : Set} → A → List A
[ a ] = a ∷ []

record Pair (A B : Set) : Set where
  field 
    first  : A
    second : B

getFirst : ∀ {A B} → Pair A B → A
getFirst = Pair.first

record ⊤ : Set where

tt : ⊤
tt = record {}

even : ℕ → Set
even zero = ⊤
even (succ zero) = ⊥
even (succ (succ n)) = even n

div2e : (n : ℕ) → even n → ℕ
div2e zero y = zero
div2e (succ zero) ()
div2e (succ (succ x)) y = succ (div2e x y)

data Even : ℕ → Set where
  ezero  : Even zero
  e2succ : {n : ℕ} → Even n → Even (succ (succ n))

twoIsEven : Even (succ (succ zero))
twoIsEven = e2succ ezero

div2E : (n : ℕ) → Even n → ℕ
div2E zero ezero = zero
div2E (succ zero) ()
div2E (succ (succ x)) (e2succ y) = succ (div2E x y)

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (succ n)

head : ∀ {A n} → Vec A (succ n) → A
head (x ∷ xs) = x

_++_ : ∀ {A} → List A → List A → List A
[] ++ bs = bs
(x ∷ xs) ++ bs = x ∷ (xs ++ bs)

infix 6 _+_
_+_ : ℕ → ℕ → ℕ
zero + y = y
succ x + y = succ (x + y)

_++v_ : ∀ {A n m} → Vec A n → Vec A m → Vec A (n + m)
[] ++v bs = bs
(x ∷ xs) ++v bs = x ∷ (xs ++v bs)

infix 6 _-_
_-_ : ℕ → ℕ → ℕ
zero - y = zero
succ x - zero = succ x
succ x - succ y = x - y

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {n m} → n ≤ m → succ n ≤ succ m

sub₀ : (n m : ℕ) → m ≤ n → ℕ
sub₀ n zero (z≤n .{n}) = n
sub₀ .(succ n) .(succ m) (s≤s {m} {n} y) = sub₀ n m y

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (succ a) b c = cong succ (+-assoc a b c)

lemma-+zero : ∀ a → a + zero ≡ a
lemma-+zero zero = refl
lemma-+zero (succ a) = cong succ (lemma-+zero a)

lemma-+succ : ∀ a b → succ a + b ≡ a + succ b
lemma-+succ zero b = refl
lemma-+succ (succ a) b = cong succ (lemma-+succ a b)

infixr 5 _~_
_~_ = trans

+-comm : ∀ a b → a + b ≡ b + a
+-comm zero b = sym (lemma-+zero b)
+-comm (succ a) b = cong succ (+-comm a b) ~ lemma-+succ b a

module Exercise where

infix 7 _*_
_*_ : ℕ → ℕ → ℕ
zero   * m = zero
succ n * m = m + n * m

*+-dist : ∀ a b c → (a + b) * c ≡ a * c + b * c
*+-dist zero     b c = refl
*+-dist (succ a) b c = cong (λ x → c + x) (*+-dist a b c)
  ~ sym (+-assoc c (a * c) (b * c))

*-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
*-assoc zero b c = refl
*-assoc (succ a) b c = *+-dist b (a * b) c
  ~ cong (λ x → b * c + x) (*-assoc a b c)

lemma-*zero : ∀ a → a * zero ≡ zero
lemma-*zero zero = refl
lemma-*zero (succ a) = lemma-*zero a

lemma-+swap : ∀ a b c → a + (b + c) ≡ b + (a + c)
lemma-+swap a b c = sym (+-assoc a b c)
  ~ cong (λ x → x + c) (+-comm a b)
  ~ +-assoc b a  c

lemma-*succ : ∀ a b → a + a * b ≡ a * succ b
lemma-*succ zero b = refl
lemma-*succ (succ a) b = cong succ
  (lemma-+swap a b (a * b)
    ~ cong (λ x → b + x) (lemma-*succ a b))

*-comm : ∀ a b → a * b ≡ b * a
*-comm a zero = lemma-*zero a
*-comm a (succ b) = sym (lemma-*succ a b)
  ~ cong (λ x → a + x) (*-comm a b)


filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ l) with p x
... | true  = x ∷ (filter p l)
... | false = filter p l

filterN : {A : Set} → (A → Bool) → List A → List A
filterN p [] = []
filterN p (a ∷ as) with p a
filterN p (a ∷ as) | true  with as
filterN p (a ∷ as) | true | [] = a ∷ []
filterN p (a ∷ as) | true | b ∷ bs with p b
filterN p (a ∷ as) | true | b ∷ bs | true  = a ∷ (b ∷ filterN p bs)
filterN p (a ∷ as) | true | b ∷ bs | false = a ∷ filterN p bs
filterN p (a ∷ as) | false = filterN p as
                                       
filter≡filterN₀ : {A : Set} → (p : A → Bool) → (as : List A)
  → filter p as ≡ filterN p as
filter≡filterN₀ p [] = {!!}
filter≡filterN₀ p (x ∷ as) = {!!}