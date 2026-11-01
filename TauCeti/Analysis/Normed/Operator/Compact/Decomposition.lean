/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.RieszTheory
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import TauCeti.Analysis.Normed.Module.RieszLemma
import TauCeti.LinearAlgebra.End.RangePow

/-!
# Stable kernel and range splittings for compact operators

For a compact operator `K` on a real or complex Banach space and a nonzero scalar `μ`,
the kernels and ranges of powers of `K - μ • 1` stabilise.
Their stable values are topological complements. This is the closed-subspace splitting
underlying the nilpotent and invertible parts of Riesz--Schauder theory; in particular,
`Submodule.projectionL` and `Submodule.prodEquivOfIsTopCompl` supply bounded coordinate
projections and a bounded direct-sum equivalence without choosing an arbitrary complement.

The ascending-kernel argument uses Riesz's lemma: a strictly increasing chain would
produce a bounded sequence whose images under `K` stay separated. The corresponding
closed-range and descending-chain results come from `Compact.RieszTheory`.

## References

* J. B. Conway, *A Course in Functional Analysis*, Chapter VI, Section 5.
-/

public section

open Module Submodule

namespace IsCompactOperator

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] {K : X →L[𝕜] X}

/-- The kernels of powers of a compact perturbation of the identity eventually stabilise.
Completeness of the ambient space is not needed for this assertion. -/
theorem exists_ker_pow_succ_eq_one_sub (hK : IsCompactOperator K) :
    ∃ p : ℕ, LinearMap.ker (((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ (p + 1)) =
      LinearMap.ker (((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ p) := by
  let A : X →L[𝕜] X := 1 - K
  let V (n : ℕ) := LinearMap.ker ((A : X →ₗ[𝕜] X) ^ n)
  have hmono : Monotone V := (A : X →ₗ[𝕜] X).iterateKer.monotone
  have hclosed (n : ℕ) : IsClosed (V n : Set X) := by
    simpa only [ContinuousLinearMap.toLinearMap_pow] using (A ^ n).isClosed_ker
  have hstep (n : ℕ) (x : X) (hx : x ∈ V (n + 1)) : A x ∈ V n := by
    simpa only [V, LinearMap.mem_ker, pow_succ, Module.End.mul_apply,
      ContinuousLinearMap.coe_coe] using hx
  by_contra! hcon
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  choose f hfmem hfnorm hfsep using fun n ↦
    TauCeti.riesz_lemma_of_norm_lt_of_lt hc (lt_add_one ‖c‖) (hclosed n)
      ((hmono (Nat.le_succ n)).lt_of_ne (hcon n).symm)
  have hsep (m n : ℕ) (hmn : m < n) : 1 ≤ ‖K (f n) - K (f m)‖ := by
    have hy : A (f n) + f m - A (f m) ∈ V n :=
      (V n).sub_mem ((V n).add_mem (hstep n _ (hfmem n))
        (hmono hmn (hfmem m))) (hmono hmn.le (hstep m _ (hfmem m)))
    have heq : K (f n) - K (f m) = f n - (A (f n) + f m - A (f m)) := by
      simp only [A, sub_apply, one_apply_eq_self]
      abel
    rw [heq]
    exact hfsep n _ hy
  obtain ⟨m, n, hmn, hlt⟩ := hK.exists_dist_lt_of_norm_le hfnorm one_pos
  rw [dist_eq_norm] at hlt
  rcases hmn.lt_or_gt with h | h
  · exact (hsep m n h).not_gt (by rwa [norm_sub_rev])
  · exact (hsep n m h).not_gt hlt

variable [CompleteSpace 𝕜] [IsRCLikeNormedField 𝕜] [CompleteSpace X]

/-- **The stable Riesz splitting at `1`.** For a compact operator `K`, the kernels and ranges
of powers of `1 - K` are constant from some stage onward, and their stable values are
topological complements. The assertion includes the zero space and the invertible case,
where the stable kernel can be zero. -/
theorem exists_stable_ker_range_pow_one_sub (hK : IsCompactOperator K) :
    ∃ p : ℕ,
      (∀ n, p ≤ n →
        LinearMap.ker (((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ n) =
          LinearMap.ker (((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ p) ∧
        LinearMap.range (((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ n) =
          LinearMap.range (((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ p)) ∧
      (LinearMap.ker (((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ p)).IsTopCompl
        (LinearMap.range (((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ p)) := by
  let A : X →L[𝕜] X := 1 - K
  let f : X →ₗ[𝕜] X := A
  obtain ⟨a, ha⟩ := hK.exists_ker_pow_succ_eq_one_sub
  obtain ⟨b, hb⟩ := hK.exists_range_pow_succ_eq_one_sub
  have hk (n : ℕ) (hn : a ≤ n) : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ a) := by
    simpa only [Nat.add_sub_of_le hn] using (End.ker_pow_constant ha.symm (n - a)).symm
  have hr (n : ℕ) (hn : b ≤ n) : LinearMap.range (f ^ n) = LinearMap.range (f ^ b) := by
    simpa only [Nat.add_sub_of_le hn] using
      LinearMap.range_pow_add_eq_of_range_pow_succ_eq hb (n - b)
  let p := max a b
  have hap : a ≤ p := le_max_left _ _
  have hbp : b ≤ p := le_max_right _ _
  have hstable (n : ℕ) (hn : p ≤ n) :
      LinearMap.ker (f ^ n) = LinearMap.ker (f ^ p) ∧
      LinearMap.range (f ^ n) = LinearMap.range (f ^ p) :=
    ⟨(hk n (hap.trans hn)).trans (hk p hap).symm,
      (hr n (hbp.trans hn)).trans (hr p hbp).symm⟩
  have hdisj : Disjoint (LinearMap.ker (f ^ p)) (LinearMap.range (f ^ p)) := by
    rw [Submodule.disjoint_def]
    rintro x hx ⟨y, rfl⟩
    have hy : y ∈ LinearMap.ker (f ^ (p + p)) := by
      simpa only [LinearMap.mem_ker, pow_add, End.mul_apply] using hx
    rw [(hstable (p + p) (Nat.le_add_right p p)).1] at hy
    exact LinearMap.mem_ker.mp hy
  have hcod : Codisjoint (LinearMap.ker (f ^ p)) (LinearMap.range (f ^ p)) :=
    LinearMap.codisjoint_ker_pow_range_pow_of_range_pow_succ_eq
      (hstable (p + 1) (Nat.le_succ p)).2
  have hc : IsCompl (LinearMap.ker (f ^ p)) (LinearMap.range (f ^ p)) := ⟨hdisj, hcod⟩
  refine ⟨p, hstable, hc.isTopCompl_of_isClosed ?_ ?_⟩
  · simpa only [ContinuousLinearMap.toLinearMap_pow] using (A ^ p).isClosed_ker
  · exact hK.isClosed_range_pow_one_sub p

/-- **The stable Riesz splitting at a nonzero scalar.** The kernels and ranges of powers of
`K - μ • 1` stabilise and are topological complements. No eigenvalue hypothesis is needed:
if `μ` lies in the resolvent, the kernel summand is zero. -/
theorem exists_stable_ker_range_pow_sub_smul (hK : IsCompactOperator K) {μ : 𝕜} (hμ : μ ≠ 0) :
    ∃ p : ℕ,
      (∀ n, p ≤ n →
        LinearMap.ker (((K - μ • 1 : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ n) =
          LinearMap.ker (((K - μ • 1 : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ p) ∧
        LinearMap.range (((K - μ • 1 : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ n) =
          LinearMap.range (((K - μ • 1 : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ p)) ∧
      (LinearMap.ker (((K - μ • 1 : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ p)).IsTopCompl
        (LinearMap.range (((K - μ • 1 : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ p)) := by
  have hscale : (K - μ • 1 : X →L[𝕜] X) = (-μ) • (1 - μ⁻¹ • K) := by
    simp [smul_smul, hμ, sub_eq_add_neg, add_comm]
  have hk (n : ℕ) :
      LinearMap.ker (((K - μ • 1 : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ n) =
        LinearMap.ker (((1 - μ⁻¹ • K : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ n) := by
    rw [hscale, ContinuousLinearMap.toLinearMap_smul, smul_pow,
      LinearMap.ker_smul _ _ (pow_ne_zero _ (neg_ne_zero.mpr hμ))]
  have hr (n : ℕ) :
      LinearMap.range (((K - μ • 1 : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ n) =
        LinearMap.range (((1 - μ⁻¹ • K : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ n) := by
    rw [hscale, ContinuousLinearMap.toLinearMap_smul, smul_pow,
      LinearMap.range_smul _ _ (pow_ne_zero _ (neg_ne_zero.mpr hμ))]
  have hs : IsCompactOperator (μ⁻¹ • K : X →L[𝕜] X) := hK.smul μ⁻¹
  obtain ⟨p, hp, hc⟩ := hs.exists_stable_ker_range_pow_one_sub
  refine ⟨p, fun n hn ↦ ?_, ?_⟩
  · simpa only [hk, hr] using hp n hn
  · simpa only [hk, hr] using hc

/-- A compact operator has a bounded idempotent commuting with it whose range is the stable
kernel of powers of `K - μ • 1` and whose kernel is the stable range. These are the coordinate
projections of the Riesz splitting, not necessarily orthogonal projections. -/
theorem exists_projection_ker_range_pow_sub_smul (hK : IsCompactOperator K) {μ : 𝕜}
    (hμ : μ ≠ 0) :
    ∃ (p : ℕ) (P : X →L[𝕜] X), IsIdempotentElem P ∧ Commute P K ∧
      ∀ n, p ≤ n →
        P.range = LinearMap.ker (((K - μ • 1 : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ n) ∧
        P.ker = LinearMap.range (((K - μ • 1 : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ n) := by
  obtain ⟨p, hp, hc⟩ := hK.exists_stable_ker_range_pow_sub_smul hμ
  let f : X →ₗ[𝕜] X := K - μ • 1
  let M := LinearMap.ker (f ^ p)
  let N := LinearMap.range (f ^ p)
  let P := M.projectionL N hc
  have hP : IsIdempotentElem P := Submodule.isIdempotentElem_projectionL hc
  have hPM : P.range = M := Submodule.range_projectionL hc
  have hPN : P.ker = N := Submodule.ker_projectionL hc
  have hcomm : Commute (K : X →ₗ[𝕜] X) f :=
    (Commute.refl _).sub_right ((Commute.one_right _).smul_right μ)
  have happly (x : X) : (f ^ p) (K x) = K ((f ^ p) x) :=
    LinearMap.congr_fun (hcomm.pow_right p).eq.symm x
  have hPK : Commute P K := by
    rw [ContinuousLinearMap.IsIdempotentElem.commute_iff hP, hPM, hPN]
    constructor
    · intro x hx
      simp only [M, Submodule.mem_comap, LinearMap.mem_ker,
        ContinuousLinearMap.coe_coe] at hx ⊢
      rw [happly, hx, map_zero]
    · rintro x ⟨y, rfl⟩
      exact ⟨K y, happly y⟩
  refine ⟨p, P, hP, hPK, fun n hn ↦ ?_⟩
  exact ⟨hPM.trans (hp n hn).1.symm, hPN.trans (hp n hn).2.symm⟩

end IsCompactOperator
