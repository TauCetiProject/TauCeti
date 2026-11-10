/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Affine
import TauCeti.AlgebraicGeometry.Cohomology.Spec
import TauCeti.AlgebraicGeometry.Modules.Tilde.Pushforward
import TauCeti.AlgebraicGeometry.Morphisms.Proper
import TauCeti.RingTheory.Flat.NonZeroDivisors

/-!
# Tests for the hypotheses of finiteness of coherent cohomology

The coherence of the higher direct images `R^q f_* F` of a coherent sheaf `F` along a proper
morphism `f` to a locally Noetherian scheme needs no flatness of `f` or of `F`, but it does need
properness. These examples test both boundaries on affine schemes.

* **Properness is used.** For a nonzero ring `R`, the affine line `Spec R[t] ⟶ Spec R` is not
  proper, and the zeroth cohomology `H⁰(Spec R[t], 𝒪) = R[t]` of its structure sheaf is not a
  finite `R`-module.
* **Flatness is not used.** For an element `t` of a ring `A`, the closed immersion
  `i : Spec (A ⧸ (t)) ⟶ Spec A` is finite, hence proper. Its direct image `i_* 𝒪` is the sheaf
  associated with the `A`-module `A ⧸ (t)`, and its positive higher direct images vanish, so
  every `R^q i_* 𝒪` is coherent when `A` is Noetherian. The zeroth cohomology
  `H⁰(Spec (A ⧸ (t)), 𝒪) = A ⧸ (t)` is a finite `A`-module killed by `t`. When `t` is a
  nonzerodivisor and not a unit, as `t` is in the power series ring `k⟦t⟧` over a field, neither
  `i` nor `H⁰` is flat over `A`.
-/

open CategoryTheory Limits AlgebraicGeometry PowerSeries

namespace TauCeti.AlgebraicGeometry

open Scheme.Modules

universe u

section AffineLine

variable (R : Type u) [CommRing R] [Nontrivial R]

/-- The affine line over a nonzero ring is not proper. -/
example : ¬ IsProper (Spec (.of (Polynomial R)) ↘ Spec (.of R)) := by
  rw [specOverSpec_over, IsProper.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
  exact Polynomial.not_finite

/-- The global functions `R[t]` on the affine line over a nonzero ring `R` are not a finite
`R`-module, so finiteness of cohomology fails without properness. -/
example :
    ¬ Module.Finite R (Cohomology (InvertibleSheaf.trivial (Spec (.of (Polynomial R)))).obj 0) :=
  fun _ ↦ Polynomial.not_finite (R := R)
    (.equiv (cohomologyZeroTrivialSpecLinearEquiv R (.of (Polynomial R))))

/-- The structure sheaf of the affine line has no higher cohomology. -/
example (q : ℕ) :
    Subsingleton (Cohomology (InvertibleSheaf.trivial (Spec (.of (Polynomial R)))).obj (q + 1)) :=
  inferInstance

end AffineLine

section Quotient

variable {A : Type u} [CommRing A] (t : A)

/-- The closed immersion `Spec (A ⧸ (t)) ⟶ Spec A` is finite. -/
example : IsFinite (Spec (.of (A ⧸ Ideal.span {t})) ↘ Spec (.of A)) := by
  rw [specOverSpec_over, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom,
    Ideal.Quotient.algebraMap_eq]
  exact .of_surjective _ Ideal.Quotient.mk_surjective

/-- The closed immersion `Spec (A ⧸ (t)) ⟶ Spec A` is proper. -/
example : IsProper (Spec (.of (A ⧸ Ideal.span {t})) ↘ Spec (.of A)) := by
  rw [specOverSpec_over, IsProper.SpecMap_iff, CommRingCat.hom_ofHom,
    Ideal.Quotient.algebraMap_eq]
  exact .of_surjective _ Ideal.Quotient.mk_surjective

/-- When `t` is a nonzerodivisor and not a unit, the closed immersion `Spec (A ⧸ (t)) ⟶ Spec A`
is not flat. -/
example (ht : t ∈ nonZeroDivisors A) (ht' : ¬ IsUnit t) :
    ¬ Flat (Spec (.of (A ⧸ Ideal.span {t})) ↘ Spec (.of A)) := by
  rw [specOverSpec_over, Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
  exact Module.Flat.not_quotient_of_mem_nonZeroDivisors
    (by rwa [ne_eq, Ideal.span_singleton_eq_top]) ht (Ideal.mem_span_singleton_self t)

/-- The direct image of the structure sheaf along `Spec (A ⧸ (t)) ⟶ Spec A` is the sheaf
associated with the `A`-module `A ⧸ (t)`. -/
noncomputable example :
    (pushforward (Spec (.of (A ⧸ Ideal.span {t})) ↘ Spec (.of A))).obj
      (SheafOfModules.unit.{u} (Spec (.of (A ⧸ Ideal.span {t}))).ringCatSheaf) ≅
    tilde ((ModuleCat.restrictScalars
      (CommRingCat.ofHom (algebraMap A (A ⧸ Ideal.span {t}))).hom).obj
        (.of (A ⧸ Ideal.span {t}) (A ⧸ Ideal.span {t}))) :=
  (tildeRestrictScalarsIsoPushforward (CommRingCat.ofHom (algebraMap A (A ⧸ Ideal.span {t})))
    (.of (A ⧸ Ideal.span {t}) (A ⧸ Ideal.span {t}))).symm

/-- The positive higher direct images of the structure sheaf along `Spec (A ⧸ (t)) ⟶ Spec A`
vanish, with no flatness hypothesis. -/
example (q : ℕ) :
    IsZero (((Spec (.of (A ⧸ Ideal.span {t})) ↘ Spec (.of A)).higherDirectImage (q + 1)).obj
      (SheafOfModules.unit.{u} (Spec (.of (A ⧸ Ideal.span {t}))).ringCatSheaf)) :=
  Scheme.Hom.isZero_higherDirectImage_succ_of_isAffineHom _ _ q

/-- Over a Noetherian ring `A`, every higher direct image of the structure sheaf along
`Spec (A ⧸ (t)) ⟶ Spec A` is coherent, with no flatness hypothesis. -/
example [IsNoetherianRing A] (q : ℕ) :
    (((Spec (.of (A ⧸ Ideal.span {t})) ↘ Spec (.of A)).higherDirectImage q).obj
      (SheafOfModules.unit.{u}
        (Spec (.of (A ⧸ Ideal.span {t}))).ringCatSheaf)).IsFinitePresentation := by
  have : IsFinite (Spec (.of (A ⧸ Ideal.span {t})) ↘ Spec (.of A)) := by
    rw [specOverSpec_over, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom,
      Ideal.Quotient.algebraMap_eq]
    exact .of_surjective _ Ideal.Quotient.mk_surjective
  exact Scheme.Hom.isFinitePresentation_higherDirectImage_of_isFinite _ _ q

/-- The zeroth cohomology of the structure sheaf of `Spec (A ⧸ (t))` is killed by `t`. -/
example (x : Cohomology (InvertibleSheaf.trivial (Spec (.of (A ⧸ Ideal.span {t})))).obj 0) :
    t • x = 0 := by
  apply (cohomologyZeroTrivialSpecLinearEquiv A (.of (A ⧸ Ideal.span {t}))).injective
  rw [LinearEquiv.map_smul, map_zero, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.mk_singleton_self, zero_mul]

/-- The zeroth cohomology of the structure sheaf of `Spec (A ⧸ (t))` is a finite `A`-module. -/
example :
    Module.Finite A
      (Cohomology (InvertibleSheaf.trivial (Spec (.of (A ⧸ Ideal.span {t})))).obj 0) :=
  .equiv (cohomologyZeroTrivialSpecLinearEquiv A (.of (A ⧸ Ideal.span {t}))).symm

/-- When `t` is a nonzerodivisor and not a unit, the zeroth cohomology of the structure sheaf of
`Spec (A ⧸ (t))` is not flat over `A`. -/
example (ht : t ∈ nonZeroDivisors A) (ht' : ¬ IsUnit t) :
    ¬ Module.Flat A
      (Cohomology (InvertibleSheaf.trivial (Spec (.of (A ⧸ Ideal.span {t})))).obj 0) :=
  fun _ ↦ Module.Flat.not_quotient_of_mem_nonZeroDivisors
    (by rwa [ne_eq, Ideal.span_singleton_eq_top]) ht (Ideal.mem_span_singleton_self t)
    (.of_linearEquiv (cohomologyZeroTrivialSpecLinearEquiv A (.of (A ⧸ Ideal.span {t}))).symm)

end Quotient

section PowerSeries

variable (k : Type u) [Field k]

/-- The finite closed immersion `Spec (k⟦t⟧ ⧸ (t)) ⟶ Spec k⟦t⟧` is not flat, since `t` is a
nonzerodivisor of `k⟦t⟧` and not a unit. -/
example : ¬ Flat (Spec (.of (k⟦X⟧ ⧸ Ideal.span {(X : k⟦X⟧)})) ↘ Spec (.of k⟦X⟧)) := by
  rw [specOverSpec_over, Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
  refine Module.Flat.not_quotient_of_mem_nonZeroDivisors ?_
    (mem_nonZeroDivisors_of_ne_zero X_ne_zero) (Ideal.mem_span_singleton_self _)
  rw [ne_eq, Ideal.span_singleton_eq_top, isUnit_iff_constantCoeff, constantCoeff_X]
  exact not_isUnit_zero

end PowerSeries

end TauCeti.AlgebraicGeometry
