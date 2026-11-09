/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer

/-!
# Power comparison of Tate ring norms

A continuous ring homomorphism carrying a multiplicative pseudo-uniformiser of norm `r` to
one of norm `s` satisfies `‖f x‖ ≤ C * ‖x‖ ^ (log s / log r)`. Thus compatible Tate norms
with a common multiplicative pseudo-uniformiser are comparable by powers, not necessarily by
constant multiples. If the two norms of that unit agree, the comparison is linear.

The results use native seminormed rings and ring homomorphisms, allowing different normed
models of the same ring. Neither completeness nor ultrametricity is required. The local-ball
estimate uses the shell rescaling of `NormedRing.PseudoUniformizer.exists_zpow_mul_norm_lt`;
the exponent records the different scaling factors in source and target. In particular these
comparisons apply when changing the scale of a norm or comparing a Tate gauge with a given norm.

## References

* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1, Lemmas 2.1.6–2.1.7.
-/

public section

open Filter Topology
open TauCeti.NormedRing

namespace RingHom

variable {R S : Type*} [SeminormedRing R] [SeminormedRing S]

/-- A ring homomorphism bounded by one on a ball satisfies a global power bound if it carries
chosen multiplicative pseudo-uniformisers to each other. The exponent matches their scales. -/
theorem norm_le_mul_rpow_of_forall_norm_lt (f : R →+* S)
    (ϖ : PseudoUniformizer R) (ψ : PseudoUniformizer S)
    (hϖ : Units.map f.toMonoidHom ϖ.unit = ψ.unit) {t δ : ℝ} (ht : 0 < t)
    (hrt : ‖(ϖ.unit : R)‖ ^ t = ‖(ψ.unit : S)‖) (k : ℤ)
    (hδ : ‖(ϖ.unit : R)‖ ^ k < δ) (hf : ∀ x, ‖x‖ < δ → ‖f x‖ ≤ 1) (x : R) :
    ‖f x‖ ≤ ((‖(ϖ.unit : R)‖ ^ (k + 1))⁻¹) ^ t * ‖x‖ ^ t := by
  have hmap (n : ℤ) (y : R) :
      ‖f (((ϖ.unit ^ n : Rˣ) : R) * y)‖ = ‖(ψ.unit : S)‖ ^ n * ‖f y‖ := by
    have heq : f ((ϖ.unit ^ n : Rˣ) : R) = ((ψ.unit ^ n : Sˣ) : S) := by
      rw [← hϖ, ← map_zpow]
      rfl
    rw [map_mul, heq]
    exact ψ.norm_zpow_smul n (f y)
  have hsource (n : ℤ) (y : R) :
      ‖((ϖ.unit ^ n : Rˣ) : R) * y‖ = ‖(ϖ.unit : R)‖ ^ n * ‖y‖ :=
    ϖ.norm_zpow_smul n y
  rcases eq_or_ne ‖x‖ 0 with hx | hx
  · have hbound (n : ℕ) : ‖f x‖ ≤ ‖(ψ.unit : S)‖ ^ n := by
      have hsmall : ‖((ϖ.unit ^ (-(n : ℤ)) : Rˣ) : R) * x‖ < δ := by
        rw [hsource, hx, mul_zero]
        exact (zpow_pos ϖ.norm_pos k).trans hδ
      have h := hf _ hsmall
      rw [hmap, zpow_neg, zpow_natCast] at h
      simpa using (inv_mul_le_iff₀ (pow_pos ψ.norm_pos n)).mp h
    have hzero : ‖f x‖ ≤ 0 := ge_of_tendsto'
      (tendsto_pow_atTop_nhds_zero_of_lt_one ψ.norm_pos.le ψ.norm_lt_one) hbound
    simpa [hx, Real.zero_rpow ht.ne'] using hzero
  obtain ⟨n, hn, hscale⟩ := ϖ.exists_zpow_mul_norm_lt hx k hδ
  have h := hf (((ϖ.unit ^ n : Rˣ) : R) * x) (by rwa [hsource])
  rw [hmap] at h
  calc
    ‖f x‖ ≤ (‖(ψ.unit : S)‖ ^ n)⁻¹ := by
      simpa using (le_inv_mul_iff₀ (zpow_pos ψ.norm_pos n)).mpr h
    _ = ((‖(ϖ.unit : R)‖ ^ n)⁻¹) ^ t := by
      rw [Real.inv_rpow (zpow_nonneg ϖ.norm_pos.le n), ← Real.rpow_zpow_comm ϖ.norm_pos.le, hrt]
    _ ≤ ((‖(ϖ.unit : R)‖ ^ (k + 1))⁻¹ * ‖x‖) ^ t :=
      Real.rpow_le_rpow (by positivity) hscale ht.le
    _ = _ := Real.mul_rpow (by positivity) (norm_nonneg x)

/-- A continuous ring homomorphism preserving a chosen multiplicative pseudo-uniformiser is
bounded by a power of the source norm. Its exponent is determined by the two norms of the unit. -/
theorem exists_pos_norm_le_mul_rpow_of_continuous (f : R →+* S) (hf : Continuous f)
    (ϖ : PseudoUniformizer R) (ψ : PseudoUniformizer S)
    (hϖ : Units.map f.toMonoidHom ϖ.unit = ψ.unit) :
    ∃ C > 0, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ (Real.log ‖(ψ.unit : S)‖ / Real.log ‖(ϖ.unit : R)‖) := by
  obtain ⟨δ, hδ, hfδ⟩ : ∃ δ > 0, ∀ x : R, ‖x‖ < δ → ‖f x‖ < 1 := by
    simpa [dist_eq_norm, map_zero] using Metric.continuous_iff.mp hf 0 1 one_pos
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖(ϖ.unit : R)‖ ^ k < δ :=
    exists_pow_lt_of_lt_one hδ ϖ.norm_lt_one
  have ht : 0 < Real.log ‖(ψ.unit : S)‖ / Real.log ‖(ϖ.unit : R)‖ :=
    div_pos_of_neg_of_neg (Real.log_neg ψ.norm_pos ψ.norm_lt_one)
      (Real.log_neg ϖ.norm_pos ϖ.norm_lt_one)
  refine ⟨((‖(ϖ.unit : R)‖ ^ ((k : ℤ) + 1))⁻¹) ^
    (Real.log ‖(ψ.unit : S)‖ / Real.log ‖(ϖ.unit : R)‖),
    Real.rpow_pos_of_pos (inv_pos.mpr (zpow_pos ϖ.norm_pos _)) _, fun x ↦ ?_⟩
  exact f.norm_le_mul_rpow_of_forall_norm_lt ϖ ψ hϖ ht
    (Real.rpow_logb ϖ.norm_pos ϖ.norm_lt_one.ne ψ.norm_pos) k (by simpa using hk)
    (fun y hy ↦ (hfδ y hy).le) x

end RingHom

namespace RingEquiv

variable {R S : Type*} [SeminormedRing R] [SeminormedRing S]

/-- Two compatible seminormed ring structures with a common multiplicative pseudo-uniformiser
are comparable in both directions by powers determined by the norms of that unit. -/
theorem exists_pos_norm_le_mul_rpow (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous e.symm) (ϖ : PseudoUniformizer R) (ψ : PseudoUniformizer S)
    (hϖ : Units.map e.toRingHom.toMonoidHom ϖ.unit = ψ.unit) :
    ∃ C > 0, ∃ D > 0, ∀ x,
      ‖e x‖ ≤ C * ‖x‖ ^ (Real.log ‖(ψ.unit : S)‖ / Real.log ‖(ϖ.unit : R)‖) ∧
      ‖x‖ ≤ D * ‖e x‖ ^ (Real.log ‖(ϖ.unit : R)‖ / Real.log ‖(ψ.unit : S)‖) := by
  obtain ⟨C, hC, hbound⟩ := e.toRingHom.exists_pos_norm_le_mul_rpow_of_continuous he ϖ ψ hϖ
  have hinv : Units.map e.symm.toRingHom.toMonoidHom ψ.unit = ϖ.unit := by
    apply Units.ext
    simpa using congrArg e.symm (congrArg Units.val hϖ).symm
  obtain ⟨D, hD, hbound'⟩ :=
    e.symm.toRingHom.exists_pos_norm_le_mul_rpow_of_continuous he' ψ ϖ hinv
  exact ⟨C, hC, D, hD, fun x ↦ ⟨hbound x, by simpa using hbound' (e x)⟩⟩

/-- If compatible Tate norms give a common multiplicative pseudo-uniformiser the same norm,
they are bounded-equivalent, rather than merely comparable by powers. -/
theorem exists_pos_norm_le_mul_of_norm_pseudoUniformizer_eq (e : R ≃+* S)
    (he : Continuous e) (he' : Continuous e.symm)
    (ϖ : PseudoUniformizer R) (ψ : PseudoUniformizer S)
    (hϖ : Units.map e.toRingHom.toMonoidHom ϖ.unit = ψ.unit)
    (hnorm : ‖(ϖ.unit : R)‖ = ‖(ψ.unit : S)‖) :
    ∃ C > 0, ∃ D > 0, ∀ x, ‖e x‖ ≤ C * ‖x‖ ∧ ‖x‖ ≤ D * ‖e x‖ := by
  have hlog : Real.log ‖(ϖ.unit : R)‖ ≠ 0 :=
    (Real.log_neg ϖ.norm_pos ϖ.norm_lt_one).ne
  simpa [← hnorm, div_self hlog] using e.exists_pos_norm_le_mul_rpow he he' ϖ ψ hϖ

end RingEquiv
