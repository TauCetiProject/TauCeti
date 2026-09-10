/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.LieAlgebra

/-!
# A limit criterion for the Lie algebra of a closed subgroup

Let `K` be a closed subgroup of a finite-dimensional Lie group. Its Lie algebra consists exactly
of the limits `X` for which there are positive real numbers `tₙ → 0` and derivations `Xₙ → X`
such that

`lieExp (tₙ • Xₙ) ∈ K`.

The reverse implication is the substantive one. For a fixed positive parameter `s`, the integers
`mₙ = ⌊s / tₙ⌋₊` satisfy `mₙ tₙ → s`. Since `K` contains
`lieExp (tₙ • Xₙ)`, it also contains its `mₙ`-th power, which is
`lieExp ((mₙ tₙ) • Xₙ)`. Closedness of `K` and continuity of `lieExp` then give
`lieExp (s • X) ∈ K`. Negative parameters follow by inversion.

This is the limit criterion used in the local-separation step of the closed-subgroup theorem. In
that application, a hypothetical sequence of nonzero transverse coordinates `Yₙ → 0` is written
as

`Yₙ = ‖Yₙ‖ • (‖Yₙ‖⁻¹ • Yₙ)`.

A convergent subsequence of the normalized directions therefore satisfies the criterion below,
forcing its limit into the subgroup Lie algebra and contradicting transversality.

## Main results

* `TauCeti.Lie.mem_lieSubalgebraOfSubgroup_of_tendsto`: a convergent family of rescaled
  infinitesimal elements whose exponentials lie in a closed subgroup has its limit in the
  subgroup Lie algebra.
* `TauCeti.Lie.mem_lieSubalgebraOfSubgroup_iff_exists_tendsto`: the resulting sequential
  characterization.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
-/

public section

noncomputable section

namespace TauCeti.Lie

open Filter
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- A limit criterion for the Lie algebra of a closed subgroup. Suppose eventually positive scales
`tₙ` tend to zero, derivations `Xₙ` tend to `X`, and eventually `lieExp (tₙ • Xₙ)` lies in
`K`. Then `X` belongs to the Lie algebra of `K`.

The positivity assumption makes natural-number powers sufficient to recover all positive
parameters. The full one-parameter subgroup is then obtained using inverses. -/
theorem mem_lieSubalgebraOfSubgroup_of_tendsto {K : Subgroup G}
    (hK : IsClosed (K : Set G)) {X : LeftInvariantDerivation I G} {t : ℕ → ℝ}
    (ht_pos : ∀ᶠ n in atTop, 0 < t n) (ht : Tendsto t atTop (𝓝 0))
    {Xn : ℕ → LeftInvariantDerivation I G} (hXn : Tendsto Xn atTop (𝓝 X))
    (hmem : ∀ᶠ n in atTop, lieExp (I := I) (t n • Xn n) ∈ K) :
    X ∈ lieSubalgebraOfSubgroup (I := I) K := by
  apply (mem_lieSubalgebraOfSubgroup hK).2
  intro s
  by_cases hs0 : s = 0
  · simp [hs0]
  have hpos : ∀ {r : ℝ}, 0 < r → lieExp (I := I) (r • X) ∈ K := by
    intro r hr
    let m : ℕ → ℕ := fun n => ⌊r / t n⌋₊
    have hc : Tendsto (fun n => (m n : ℝ) * t n) atTop (𝓝 r) := by
      have ht' : Tendsto t atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.mpr ⟨ht, ht_pos⟩
      have hdiv : Tendsto (fun n => r / t n) atTop atTop := by
        simpa only [div_eq_mul_inv, Pi.inv_apply] using
          ht'.inv_tendsto_nhdsGT_zero.const_mul_atTop hr
      have hfloor := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hdiv
      simpa only [one_mul] using (hfloor.mul_const r).congr' (by
        filter_upwards [ht_pos] with n htn
        simp only [m, Function.comp_apply]
        field_simp [ne_of_gt hr, ne_of_gt htn])
    have hv : Tendsto (fun n => ((m n : ℝ) * t n) • Xn n) atTop (𝓝 (r • X)) :=
      hc.smul hXn
    refine hK.mem_of_tendsto
      ((contMDiff_lieExp (I := I) (G := G)).continuous.continuousAt.tendsto.comp hv) ?_
    filter_upwards [hmem] with n hn
    -- `filter_upwards` exposes membership in the underlying set; restate it as subgroup
    -- membership so that `Subgroup.pow_mem` applies to the approximating exponential.
    change lieExp (I := I) (((m n : ℝ) * t n) • Xn n) ∈ K
    have hp := K.pow_mem hn (m n)
    rw [← lieExp_nsmul (I := I) (G := G) (t n • Xn n) (m n)] at hp
    simpa only [Function.comp_apply, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul] using hp
  by_cases hs : 0 < s
  · exact hpos hs
  · have hneg : 0 < -s := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hs) hs0)
    have hm := K.inv_mem (hpos hneg)
    simpa only [← lieExp_neg, neg_smul, neg_neg] using hm

/-- Membership in the Lie algebra of a closed subgroup is equivalent to being a limit of
derivations whose exponentials at eventually positive scales tending to zero eventually lie in the
subgroup. -/
theorem mem_lieSubalgebraOfSubgroup_iff_exists_tendsto {K : Subgroup G}
    (hK : IsClosed (K : Set G)) {X : LeftInvariantDerivation I G} :
    X ∈ lieSubalgebraOfSubgroup (I := I) K ↔
      ∃ (t : ℕ → ℝ) (Xn : ℕ → LeftInvariantDerivation I G),
        (∀ᶠ n in atTop, 0 < t n) ∧ Tendsto t atTop (𝓝 0) ∧ Tendsto Xn atTop (𝓝 X) ∧
          ∀ᶠ n in atTop, lieExp (I := I) (t n • Xn n) ∈ K := by
  constructor
  · intro hX
    refine ⟨fun n => 1 / (n + 1 : ℝ), fun _ => X, ?_, ?_, tendsto_const_nhds, ?_⟩
    · filter_upwards with n
      positivity
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · filter_upwards with n
      exact lieExp_smul_mem_of_mem_lieSubalgebraOfSubgroup hK hX _
  · rintro ⟨t, Xn, ht_pos, ht, hXn, hmem⟩
    exact mem_lieSubalgebraOfSubgroup_of_tendsto hK ht_pos ht hXn hmem

end TauCeti.Lie
