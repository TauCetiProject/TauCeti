/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import TauCeti.RingTheory.KoszulComplex.Augmentation
public import TauCeti.RingTheory.KoszulComplex.Regular

/-!
# The Koszul resolution of a regular quotient

For a finite weakly regular sequence `x`, the Koszul augmentation is a quasi-isomorphism.
`TauCeti.koszulComplex.projectiveResolution` bundles the existing exterior-power complex as a
Mathlib `ProjectiveResolution` of `R/(x)`. Its terms are finite free and vanish above the
length of `x`. This makes the Koszul resolution available to derived-functor computations
with its specified differential and quotient augmentation.

The construction uses `TauCeti.koszulComplex.exactAt_of_isWeaklyRegular`; the mathematics is the
augmented Koszul resolution in
[The Stacks Project, Tag 062F](https://stacks.math.columbia.edu/tag/062F).
-/

public section

noncomputable section

universe u

open CategoryTheory HomologicalComplex

namespace TauCeti.koszulComplex

variable {R : Type u} [CommRing R]

variable {n : ℕ} (x : Fin n → R)

/-- The augmentation of the Koszul complex of a weakly regular sequence is a
quasi-isomorphism onto its quotient ring in degree zero. -/
theorem quasiIso_augmentation_of_isWeaklyRegular
    (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) :
    QuasiIso (augmentation (Fintype.linearCombination R x) (Ideal.span (Set.range x))
      (Fintype.range_linearCombination R x).le) := by
  constructor
  intro k
  cases k with
  | zero => exact quasiIsoAt_augmentation_zero _ _ (Fintype.range_linearCombination R x)
  | succ k =>
    rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
    exact exactAt_of_isWeaklyRegular x hx k

/-- The Koszul projective resolution of the quotient by a finite weakly regular sequence.
Its underlying complex is the exterior-power Koszul complex, with its quotient augmentation. -/
def projectiveResolution (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span (Set.range x))) where
  complex := koszulComplex (Fintype.linearCombination R x)
  projective k := inferInstanceAs (Projective (ModuleCat.of R (⋀[R]^k (Fin n → R))))
  π := augmentation (Fintype.linearCombination R x) (Ideal.span (Set.range x))
    (Fintype.range_linearCombination R x).le
  quasiIso := quasiIso_augmentation_of_isWeaklyRegular x hx

/-- The resolution retains the exterior-power complex and its Koszul differential. -/
@[simp]
theorem projectiveResolution_complex
    (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) :
    (projectiveResolution x hx).complex = koszulComplex (Fintype.linearCombination R x) :=
  (rfl)

/-- The resolution retains the quotient augmentation. -/
@[simp]
theorem projectiveResolution_π
    (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) :
    eqToHom (projectiveResolution_complex x hx).symm ≫ (projectiveResolution x hx).π =
      augmentation (Fintype.linearCombination R x) (Ideal.span (Set.range x))
        (Fintype.range_linearCombination R x).le := by
  rfl

/-- Every term of the Koszul resolution is free. -/
instance projectiveResolution_free
    (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) (k : ℕ) :
    Module.Free R ((projectiveResolution x hx).complex.X k) := by
  rw [projectiveResolution_complex, koszulComplex_X]
  infer_instance

/-- Every term of the Koszul resolution is finitely generated. -/
instance projectiveResolution_finite
    (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) (k : ℕ) :
    Module.Finite R ((projectiveResolution x hx).complex.X k) := by
  rw [projectiveResolution_complex, koszulComplex_X]
  infer_instance

/-- The Koszul resolution of a length-`n` sequence vanishes in degrees greater than `n`. -/
theorem isZero_projectiveResolution_X
    (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) (k : ℕ) (hk : n < k) :
    Limits.IsZero ((projectiveResolution x hx).complex.X k) := by
  rw [projectiveResolution_complex, koszulComplex_X]
  let : Subsingleton (⋀[R]^k (Fin n → R)) :=
    exteriorPower.subsingleton_of_span_eq_top_of_card_lt
      (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n)).span_eq k (by simpa using hk)
  exact ModuleCat.isZero_of_subsingleton _

end TauCeti.koszulComplex
