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

For a commutative square
```
P --a--> B
|        |
b        c
v        v
D --d--> Z
```
in a preadditive category, Mathlib attaches two short complexes `P ⟶ B ⊞ D ⟶ Z`:
`CategoryTheory.CommSq.shortComplex`, with maps `(a, -b)` and `(c, d)`, whose cokernel property
is the pushout property, and `CategoryTheory.CommSq.shortComplex'`, with maps `(a, b)` and
`(c, -d)`, whose kernel property is the pullback property
(`CategoryTheory.CommSq.isLimitEquivIsLimitKernelFork`). Changing the sign of the summand `D`
identifies them (`CategoryTheory.CommSq.shortComplexIsoShortComplex'`).

Mayer–Vietoris sequences have the shape of `CategoryTheory.CommSq.shortComplex`. In an abelian
category, exactness of this short complex, together with injectivity of its first map, makes the
square a pullback (`CategoryTheory.IsPullback.of_exact_shortComplex`).
-/

public section

namespace CategoryTheory

open Limits

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

/-- The two short complexes `P ⟶ B ⊞ D ⟶ Z` of a commutative square, with maps `(a, -b)`,
`(c, d)` and with maps `(a, b)`, `(c, -d)`, are isomorphic through the sign change of the summand
`D`. -/
-- The body is exposed so that `simps!` can state its components, among them the sign change
-- `biprod.map (𝟙 B) (-𝟙 D)` on the middle term, as definitional simp lemmas.
@[expose, simps!]
noncomputable def CommSq.shortComplexIsoShortComplex' {P B D Z : C} {a : P ⟶ B} {b : P ⟶ D}
    {c : B ⟶ Z} {d : D ⟶ Z} [HasBinaryBiproduct B D] (sq : CommSq a b c d) :
    sq.shortComplex ≅ sq.shortComplex' :=
  ShortComplex.isoMk (Iso.refl _)
    (show B ⊞ D ≅ B ⊞ D from
      { hom := biprod.map (𝟙 B) (-𝟙 D)
        inv := biprod.map (𝟙 B) (-𝟙 D)
        hom_inv_id := by apply biprod.hom_ext' <;> simp
        inv_hom_id := by apply biprod.hom_ext' <;> simp })
    (Iso.refl _)
    (by dsimp [CommSq.shortComplex, CommSq.shortComplex']; apply biprod.hom_ext <;> simp)
    (by dsimp [CommSq.shortComplex, CommSq.shortComplex']; apply biprod.hom_ext' <;> simp)

end Preadditive

namespace IsPullback

variable {C : Type*} [Category* C] [Abelian C]

/-- **A pullback square from an exact Mayer–Vietoris sequence.** A commutative square with sides
`a`, `b`, `c` and `d` is a pullback square if the sequence `P ⟶ B ⊞ D ⟶ Z` with maps `(a, -b)` and
`(c, d)` (`CategoryTheory.CommSq.shortComplex`) is exact and begins with a monomorphism. -/
theorem of_exact_shortComplex {P B D Z : C} {a : P ⟶ B} {b : P ⟶ D} {c : B ⟶ Z} {d : D ⟶ Z}
    (sq : CommSq a b c d) (hex : sq.shortComplex.Exact) (hmono : Mono sq.shortComplex.f) :
    IsPullback a b c d := by
  obtain ⟨hex', _⟩ :=
    (ShortComplex.exact_and_mono_f_iff_of_iso sq.shortComplexIsoShortComplex').1 ⟨hex, hmono⟩
  exact IsPullback.of_isLimit (sq.isLimitEquivIsLimitKernelFork.symm hex'.fIsKernel)

end IsPullback

end CategoryTheory
