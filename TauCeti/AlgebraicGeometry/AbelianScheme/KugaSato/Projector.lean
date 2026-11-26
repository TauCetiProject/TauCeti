/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Defs
public import TauCeti.RingTheory.Idempotents.Correction
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Idempotents
import TauCeti.Algebra.Module.Filtration.Endomorphism
import TauCeti.LinearAlgebra.End.Aeval
import TauCeti.LinearAlgebra.LinearMap.Range

/-!
# Corrected coefficient projectors for Kuga–Sato cohomology

The relative-degree selector on the cohomology of an abelian power is idempotent on the
graded pieces of the Leray filtration. On the total cohomology, a filtration of length
`d` bounds the nilpotence exponent of its idempotence error by `d`. Correcting the selector
with `Polynomial.idempotentCorrection` and multiplying by the commuting Young idempotent gives
an idempotent on the whole module. Its image is preserved by the comparisons that intertwine
both operators.

## References

* R. Taylor and T. Yoshida, *Compatibility of local and global Langlands correspondences*,
  arXiv:math/0412357v2, §2.
* A. Caraiani, *Local-global compatibility and the action of monodromy on nearby cycles*,
  arXiv:1010.2188v1, §2.1.
-/

public section

namespace TauCeti.KugaSato

open LinearMap Polynomial

variable {R V W : Type*} [CommRing R]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The Young operator composed with the polynomial correction of the relative-degree selector. -/
noncomputable def coefficientProjector (d : ℕ) (young selector : Module.End R V) :
    Module.End R V :=
  young * aeval selector (idempotentCorrection (R := R) d)

/-- The defining formula for the coefficient projector as a composite. -/
theorem coefficientProjector_def (d : ℕ) (young selector : Module.End R V) :
    coefficientProjector d young selector = young ∘ₗ
      aeval selector (idempotentCorrection (R := R) d) :=
  (rfl)

/-- For an idempotence error bounded by `d`, the corrected selector and the commuting Young
idempotent compose to an idempotent. -/
theorem isIdempotentElem_coefficientProjector {d : ℕ} {young selector : Module.End R V}
    (hy : IsIdempotentElem young) (hc : Commute young selector)
    (hs : (selector - selector ^ 2) ^ d = 0) :
    IsIdempotentElem (coefficientProjector d young selector) := by
  have hc' := Algebra.commute_of_mem_adjoin_singleton_of_commute
    (aeval_mem_adjoin_singleton R selector (p := idempotentCorrection d)) hc
  exact IsIdempotentElem.mul_of_commute hc' hy (by
    simpa using isIdempotentElem_one_sub_one_sub_pow_pow selector d hs)

/-- A length-`d` filtration on whose graded pieces the selector is idempotent suffices for
the corrected coefficient projector to be idempotent on the entire module. -/
theorem isIdempotentElem_coefficientProjector_of_graded {d : ℕ}
    {young selector : Module.End R V} (hy : IsIdempotentElem young)
    (hc : Commute young selector) {F : ℕ → Submodule R V} (hbot : F 0 = ⊥) (htop : F d = ⊤)
    (hgrade : ∀ i < d, ∀ v ∈ F (i + 1),
      (Submodule.Quotient.mk (selector v) : V ⧸ F i) =
        Submodule.Quotient.mk (selector (selector v))) :
    IsIdempotentElem (coefficientProjector d young selector) :=
  isIdempotentElem_coefficientProjector hy hc
    (selector.sub_sq_pow_eq_zero_of_graded_idempotent hbot htop hgrade)

/-- On a graded quotient where the selector is idempotent, the corrected projector induces
the same action as the Young operator composed with the original selector. -/
theorem coefficientProjector_mk_eq {d : ℕ} (hd : d ≠ 0)
    {young selector : Module.End R V} {S : Submodule R V}
    (hy : S ≤ S.comap young) (hs : S ≤ S.comap selector) {v : V}
    (hv : (Submodule.Quotient.mk (selector (selector v)) : V ⧸ S) =
      Submodule.Quotient.mk (selector v)) :
    (Submodule.Quotient.mk (coefficientProjector d young selector v) : V ⧸ S) =
      Submodule.Quotient.mk (young (selector v)) := by
  obtain ⟨q, hq⟩ := X_mul_X_sub_one_dvd_idempotentCorrection_sub_X (R := R) hd
  have hq' : aeval selector (idempotentCorrection (R := R) d) - selector =
      aeval selector q * (selector ^ 2 - selector) := by
    rw [mul_comm ((X : R[X]) * (X - 1)) q] at hq
    simpa only [map_sub, map_one, map_mul, aeval_X, mul_sub, mul_one, pow_two] using
      congrArg (aeval selector) hq
  have hmem : ((selector ^ 2 - selector) : Module.End R V) v ∈ S := by
    simpa [pow_two, _root_.mul_apply_eq_comp] using (Submodule.Quotient.eq S).mp hv
  have hp := aeval_apply_smul_mem_of_le_comap hmem q selector hs
  rw [← _root_.mul_apply_eq_comp, ← hq'] at hp
  rw [Submodule.Quotient.eq, coefficientProjector_def, comp_apply, ← map_sub]
  exact hy hp

/-- Any linear map intertwining the selector and the Young operator also intertwines the
corrected projectors. -/
theorem coefficientProjector_comp_eq (d : ℕ) {young selector : Module.End R V}
    {young' selector' : Module.End R W} {f : V →ₗ[R] W}
    (hy : young' ∘ₗ f = f ∘ₗ young) (hs : selector' ∘ₗ f = f ∘ₗ selector) :
    coefficientProjector d young' selector' ∘ₗ f = f ∘ₗ coefficientProjector d young selector := by
  have h := Module.End.aeval_comp_of_comp_eq hs (idempotentCorrection (R := R) d)
  ext v
  have hv := LinearMap.congr_fun h v
  simp only [LinearMap.comp_apply] at hv
  simp only [coefficientProjector_def, LinearMap.comp_apply, hv]
  exact LinearMap.congr_fun hy _

/-- An intertwining linear equivalence restricts to an equivalence of the corrected images. -/
noncomputable def coefficientProjectorRangeEquiv (d : ℕ)
    {young selector : Module.End R V} {young' selector' : Module.End R W} (e : V ≃ₗ[R] W)
    (hy : young' ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ young)
    (hs : selector' ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ selector) :
    range (coefficientProjector d young selector) ≃ₗ[R]
      range (coefficientProjector d young' selector') :=
  e.ofSubmodules _ _ (map_range_eq_range_of_comp_eq _ e.surjective
    (coefficientProjector_comp_eq d hy hs))

/-- The equivalence of corrected images acts by the given underlying equivalence. -/
@[simp]
theorem coe_coefficientProjectorRangeEquiv_apply (d : ℕ)
    {young selector : Module.End R V} {young' selector' : Module.End R W} (e : V ≃ₗ[R] W)
    (hy : young' ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ young)
    (hs : selector' ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ selector)
    (v : range (coefficientProjector d young selector)) :
    (coefficientProjectorRangeEquiv d e hy hs v : W) = e v :=
  (rfl)

end TauCeti.KugaSato
