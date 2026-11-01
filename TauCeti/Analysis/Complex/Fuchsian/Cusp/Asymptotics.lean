/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Growth

/-!
# Exact exponential growth criteria at a cusp

For a cusp-invariant function holomorphic at sufficiently large normalized heights,
meromorphic extension across the cusp is equivalent to an exponential growth bound. More
precisely, growth of rate at most `2πk / w` is equivalent to a meromorphic extension whose order
is at least `-k`. Integer rates treat zeros and poles together, and include the zero germ.

The necessity follows by multiplying the meromorphic germ by `q^k`: a nonnegative order gives
a finite limit, hence boundedness. Mathlib's meromorphic-order and limit theorems supply this
step; the exponential factor is the reciprocal norm of `q^k`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §2.4.
* Otto Forster, *Lectures on Riemann Surfaces*, §19.
-/

public noncomputable section

open Asymptotics Filter Function MulAction UpperHalfPlane
open scoped Manifold MatrixGroups Topology

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)}

/-- A meromorphic cusp germ makes its invariant pullback holomorphic at every sufficiently
large normalized height. Poles away from the cusp are allowed. -/
theorem eventually_mdifferentiableAt_of_meromorphicAt_cuspExtension (D : Γ.CuspDatum)
    (f : ℍ → ℂ) (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hmero : MeromorphicAt (cuspExtension D f) 0) :
    ∀ᶠ z in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (D.scaling⁻¹ • z) := by
  have hpull : cuspExtension D f ∘ coordinate D = f :=
    funext (cuspExtension_coordinate D f hf)
  filter_upwards [(TauCeti.UpperHalfPlane.tendsto_qParam_atImInfty D.width_pos).eventually
    hmero.eventually_analyticAt] with z hz
  have hq : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (cuspExtension D f)
      (coordinate D (D.scaling⁻¹ • z)) := by
    rw [coordinate_inv_smul]
    exact hz.differentiableAt.mdifferentiableAt
  exact hpull ▸ hq.comp (D.scaling⁻¹ • z) (mdifferentiable_coordinate D _)

/-- A meromorphic cusp germ of order at least `-k` has exponential growth of rate at most
`2πk / w` in the normalized scaling coordinate. No holomorphy assumption upstairs is needed
for this direction. -/
theorem isBigO_exp_of_neg_le_meromorphicOrderAt_cuspExtension (D : Γ.CuspDatum) (k : ℤ)
    (f : ℍ → ℂ) (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hmero : MeromorphicAt (cuspExtension D f) 0)
    (horder : ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspExtension D f) 0) :
    (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width) := by
  let g : ℂ → ℂ := id ^ k * cuspExtension D f
  have hg : MeromorphicAt g 0 := ((MeromorphicAt.id 0).zpow k).mul hmero
  have hgorder : 0 ≤ meromorphicOrderAt g 0 := by
    rw [meromorphicOrderAt_mul ((MeromorphicAt.id 0).zpow k) hmero,
      meromorphicOrderAt_zpow (MeromorphicAt.id 0), meromorphicOrderAt_id, mul_one]
    cases ho : meromorphicOrderAt (cuspExtension D f) 0 with
    | top => simp
    | coe m =>
      rw [ho] at horder
      have hkm : -k ≤ m := WithTop.coe_le_coe.mp horder
      have hnonneg : (0 : ℤ) ≤ k + m := by omega
      exact_mod_cast hnonneg
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hg hgorder
  have hbound :=
    (hc.comp (TauCeti.UpperHalfPlane.tendsto_qParam_atImInfty D.width_pos)).isBigO_one ℝ
  apply (TauCeti.UpperHalfPlane.isBoundedAtImInfty_qParam_zpow_mul_iff D.width k).1
  rw [IsBoundedAtImInfty, BoundedAtFilter]
  refine hbound.congr_left fun z ↦ ?_
  dsimp only [g, comp_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
  rw [← coordinate_inv_smul D z, cuspExtension_coordinate D f hf]

/-- For a meromorphic cusp germ, the exponential bound of integer rate `k` is equivalent to
order at least `-k`. Negative rates characterize zeros, positive rates bound poles, and the zero
germ satisfies every bound. -/
theorem isBigO_exp_iff_neg_le_meromorphicOrderAt_cuspExtension (D : Γ.CuspDatum) (k : ℤ)
    (f : ℍ → ℂ) (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hmero : MeromorphicAt (cuspExtension D f) 0) :
    ((fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) ↔
      ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspExtension D f) 0 :=
  ⟨neg_le_meromorphicOrderAt_cuspExtension D k f hf
    (eventually_mdifferentiableAt_of_meromorphicAt_cuspExtension D f hf hmero),
    isBigO_exp_of_neg_le_meromorphicOrderAt_cuspExtension D k f hf hmero⟩

/-- An invariant function has a meromorphic cusp extension exactly when it is holomorphic
sufficiently high and has at most exponential growth in the normalized scaling coordinate. -/
theorem meromorphicAt_cuspExtension_zero_iff (D : Γ.CuspDatum)
    (f : ℍ → ℂ) (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z) :
    MeromorphicAt (cuspExtension D f) 0 ↔
      (∀ᶠ z in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (D.scaling⁻¹ • z)) ∧
        ∃ k : ℤ, (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
          fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width) := by
  constructor
  · intro hm
    refine ⟨eventually_mdifferentiableAt_of_meromorphicAt_cuspExtension D f hf hm, ?_⟩
    cases ho : meromorphicOrderAt (cuspExtension D f) 0 with
    | top =>
      exact ⟨0, isBigO_exp_of_neg_le_meromorphicOrderAt_cuspExtension D 0 f hf hm (by simp [ho])⟩
    | coe m =>
      exact ⟨-m, isBigO_exp_of_neg_le_meromorphicOrderAt_cuspExtension D (-m) f hf hm
        (by simp [ho])⟩
  · rintro ⟨hhol, k, hk⟩
    exact meromorphicAt_cuspExtension_zero D k f hf hhol hk

end TauCeti.Subgroup.CuspDatum
