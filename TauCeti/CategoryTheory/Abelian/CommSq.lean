/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Pullback squares from exact Mayer–Vietoris sequences

In an abelian category, a commutative square
```
P --a--> B
|        |
b        c
v        v
D --d--> Z
```
is a pullback square exactly when `P` is the kernel of `(c, -d) : B ⊞ D ⟶ Z` through
`(a, b) : P ⟶ B ⊞ D` (`CategoryTheory.CommSq.isLimitEquivIsLimitKernelFork`). Mayer–Vietoris
sequences put the sign on the other map: they read `P ⟶ B ⊞ D ⟶ Z` with maps `(a, -b)` and
`(c, d)`. This file records that exactness of this sequence, together with injectivity of its
first map, also makes the square a pullback
(`CategoryTheory.IsPullback.of_exact_biprod_lift_neg`): changing the sign of the summand `D`
identifies the two sequences.
-/

public section

namespace CategoryTheory.IsPullback

open Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- **A pullback square from an exact Mayer–Vietoris sequence.** For maps `a : P ⟶ B`,
`b : P ⟶ D`, `c : B ⟶ Z` and `d : D ⟶ Z` such that the sequence `P ⟶ B ⊞ D ⟶ Z` with maps
`(a, -b)` and `(c, d)` is exact and begins with a monomorphism, the square with sides `a`, `b`,
`c` and `d` is a pullback square. -/
theorem of_exact_biprod_lift_neg {P B D Z : C} {a : P ⟶ B} {b : P ⟶ D} {c : B ⟶ Z}
    {d : D ⟶ Z} (w : biprod.lift a (-b) ≫ biprod.desc c d = 0)
    (hex : (ShortComplex.mk _ _ w).Exact) (hmono : Mono (biprod.lift a (-b))) :
    IsPullback a b c d := by
  have sq : CommSq a b c d := ⟨by simpa [add_neg_eq_zero] using w⟩
  -- Changing the sign of the summand `D` identifies the sequence with that of the square, whose
  -- maps are `(a, b)` and `(c, -d)`.
  let τ : B ⊞ D ⟶ B ⊞ D := biprod.map (𝟙 B) (-𝟙 D)
  have hτ : τ ≫ τ = 𝟙 _ := by apply biprod.hom_ext' <;> simp [τ]
  have hf : biprod.lift a b = biprod.lift a (-b) ≫ τ := by apply biprod.hom_ext <;> simp [τ]
  let S : ShortComplex C := ShortComplex.mk (biprod.lift a b) (biprod.desc c (-d)) (by simp [sq.w])
  let e : ShortComplex.mk _ _ w ≅ S :=
    ShortComplex.isoMk (Iso.refl _) ⟨τ, τ, hτ, hτ⟩ (Iso.refl _) (by simp [S, hf])
      (by apply biprod.hom_ext' <;> simp [S, τ])
  have : IsIso τ := ⟨τ, hτ, hτ⟩
  have : Mono (biprod.lift a b) := by
    rw [hf]
    infer_instance
  -- `S` is the short complex `sq.shortComplex'` of the square, whose kernel property is the
  -- pullback property.
  exact IsPullback.of_isLimit
    (sq.isLimitEquivIsLimitKernelFork.symm ((ShortComplex.exact_iff_of_iso e).1 hex).fIsKernel)

end CategoryTheory.IsPullback
