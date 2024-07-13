# agda-funspaces

Results regarding the possible "sizes" of function spaces in Martin-Löf type
theory without functional extensionality axioms.

Our concrete question is the following:
given an inhabited type `B`, when can we consistently have an injection
from some type `C` into the function space `A → B`?

For example, can we always have an injection from `ℕ` to `A → B`?
In the presence of function extensionality, the answer is negative: e.g.
`⊤ → ⊤` has but one element, whereas a type which admits an injection from the
naturals is necessarily infinite.

However, this sort of reasoning doesn't work in most variants of Martin-Löf
type theory which do not assume and cannot prove function extensionality.


* `BigLEM.agda`: Some results in the presence of LEM (following a proof of
  Cantor's theorem about injections.
