/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Basic

/-!
# Cup products of mod-two Kummer classes

For a field `K` in which `2` is invertible, multiplication in `𝔽₂` gives a pairing on the
trivial coefficient object (`TauCeti.trivialF2TopPairing`). Composing its degree-`(1,1)` cup
product with the Kummer isomorphism gives the bilinear pairing

```text
Kˣ/(Kˣ)² × Kˣ/(Kˣ)² → H²(G_K, 𝔽₂),   ([a], [b]) ↦ [a] ⌣ [b].
```

The source is the additive square-class group `TauCeti.SquareClassGroup K`; consequently
biadditivity and invariance under changing representatives are carried by the type. The
representative formula `TauCeti.kummerCup_squareClass_squareClass` identifies this pairing with
the cup of the classes constructed in `TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic`, and
`TauCeti.kummerCup_comm` records that the pairing is symmetric.

## Main definitions

* `TauCeti.kummerCup`: the bilinear cup pairing on square classes.

## Main results

* `TauCeti.kummerCup_comm`: the Kummer cup pairing is symmetric.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (6.2.2).
-/

public section

noncomputable section

namespace TauCeti

open _root_.ContinuousCohomology

universe u

variable (K : Type u) [Field K] [Invertible (2 : K)]

/-- **The mod-two Kummer cup pairing on square classes.** It sends `([a], [b])` to the cup
product of their Kummer classes in `H²(G_K, 𝔽₂)`. -/
noncomputable def kummerCup :
    SquareClassGroup K →+ SquareClassGroup K →+
      continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K)) where
  toFun x :=
    { toFun := fun y ↦ (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerSquareClassEquiv K x) (kummerSquareClassEquiv K y)
      map_zero' := by simp
      map_add' := by simp }
  map_zero' := by
    ext y
    simp
  map_add' x y := by
    ext z
    simp

/-- The Kummer cup pairing is the cup product after applying the square-class Kummer
isomorphism in both variables. -/
@[simp]
theorem kummerCup_apply (x y : SquareClassGroup K) :
    kummerCup K x y = (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
      (kummerSquareClassEquiv K x) (kummerSquareClassEquiv K y) :=
  (rfl)

-- Not `@[simp]`: `simp` proves it from `kummerCup_apply` and
-- `kummerSquareClassEquiv_squareClass`.
/-- The Kummer cup on representatives is the cup product of their Kummer classes. -/
theorem kummerCup_squareClass_squareClass (a b : Kˣ) :
    kummerCup K (squareClass a) (squareClass b) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass a) (kummerClass b) := by
  rw [kummerCup_apply, kummerSquareClassEquiv_squareClass, kummerSquareClassEquiv_squareClass]

/-- **The Kummer cup pairing is symmetric**: `[a] ⌣ [b] = [b] ⌣ [a]`. -/
theorem kummerCup_comm (x y : SquareClassGroup K) : kummerCup K x y = kummerCup K y x := by
  rw [kummerCup_apply, trivialF2TopPairing_cup_comm, ContinuousCohomology.degreeCast_rfl,
    CategoryTheory.Iso.refl_hom, CategoryTheory.ConcreteCategory.id_apply, ← kummerCup_apply]

end TauCeti
