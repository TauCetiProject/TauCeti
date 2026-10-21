/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# The powers of the extended ideal in the adic completion of a ring

Let `I` be a finitely generated ideal of a commutative ring `R` and `R̂ = AdicCompletion I R`.
The kernel of the projection `R̂ → R ⧸ I ^ n` is the extension `I ^ n R̂` of `I ^ n`. Mathlib
records the case `n = 1` (`AdicCompletion.ker_evalOneₐ_eq_map`); the general case identifies
the `I R̂`-adic filtration of `R̂` with the kernels of the projections. Consequently the
canonical map `R → R̂` identifies `I ^ n` with the preimage of `I ^ n R̂`, and every element of
`R̂` is congruent modulo `I ^ n R̂` to the image of an element of `R`, so the image of `R` is
dense modulo every `I ^ n R̂`.

## Main results

* `AdicCompletion.ker_evalₐ_eq_map_pow`: the kernel of `R̂ → R ⧸ I ^ n` is `I ^ n R̂`.
* `AdicCompletion.algebraMap_mem_map_pow_iff`: the image of `x ∈ R` lies in `I ^ n R̂` if and
  only if `x ∈ I ^ n`.
* `AdicCompletion.exists_sub_algebraMap_mem_map_pow`: every element of `R̂` is congruent
  modulo `I ^ n R̂` to the image of an element of `R`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.2.
-/

public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- For a finitely generated ideal `I`, the kernel of the projection of the adic completion
onto `R ⧸ I ^ n` is the extension of `I ^ n` to the completion. -/
theorem ker_evalₐ_eq_map_pow (fg : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n) = (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  ext x
  trans x ∈ (eval I R n).ker
  · have eq : (I ^ n • ⊤ : Ideal R) = I ^ n := by simp
    rw [RingHom.mem_ker, ← factor_eval_eq_evalₐ I x eq.le, LinearMap.mem_ker]
    -- The factor map is the quotient equivalence from which `evalₐ` is built.
    exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R eq).injective
  · simp [← pow_smul_top_eq_ker_eval fg, Ideal.smul_top_eq_map]

/-- For a finitely generated ideal `I`, an element of `R` maps into the extension of `I ^ n` to
the adic completion if and only if it lies in `I ^ n`. -/
theorem algebraMap_mem_map_pow_iff (fg : I.FG) (n : ℕ) {x : R} :
    algebraMap R (AdicCompletion I R) x ∈ (I ^ n).map (algebraMap R (AdicCompletion I R)) ↔
      x ∈ I ^ n := by
  simp [← ker_evalₐ_eq_map_pow fg, algebraMap_apply, Ideal.Quotient.eq_zero_iff_mem]

/-- For a finitely generated ideal `I`, every element of the adic completion is congruent modulo
the extension of `I ^ n` to the image of an element of `R`. -/
theorem exists_sub_algebraMap_mem_map_pow (fg : I.FG) (n : ℕ) (x : AdicCompletion I R) :
    ∃ y : R, x - algebraMap R (AdicCompletion I R) y ∈
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  refine ⟨y, ?_⟩
  rw [← ker_evalₐ_eq_map_pow fg, RingHom.mem_ker, map_sub, ← hy]
  exact sub_eq_zero.mpr (evalₐ_of I n y).symm

end AdicCompletion
