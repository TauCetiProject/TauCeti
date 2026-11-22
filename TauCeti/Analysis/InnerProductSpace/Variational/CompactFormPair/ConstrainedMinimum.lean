/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.InnerProductSpace.Variational.CompactFormPair.Basic
public import TauCeti.Analysis.InnerProductSpace.Variational.Rayleigh
public import TauCeti.Analysis.Variational.BoundedSublevels
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Topology.Semicontinuity.Basic
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian
import TauCeti.Analysis.Normed.Operator.DunfordPettis.Basic
import TauCeti.Analysis.Variational.DirectMethod
import TauCeti.Order.Filter.Extr

/-!
# Constrained Rayleigh minima and restricted Euler–Lagrange equations

Given a compact form pair `P : CompactFormPair 𝕜 E H` and a submodule `W : Submodule 𝕜 H`, the
**constrained unit sphere** is

`P.unitConstraint W = {u : E | P.inclusion u ∈ W ∧ ‖P.inclusion u‖ = 1}`.

This file establishes the direct variational theory of `P.energy` on `P.unitConstraint W`:

* Basic properties of `P.unitConstraint W`: nonemptiness criterion, phase invariance,
  monotonicity in `W`, interaction with shifts and transports, the quantitative lower bound
  `-ω ≤ P.energy u`, and norm-boundedness of energy sublevels (`HasBoundedSublevelsOn`).
* Sequential weak closedness of `P.unitConstraint W` when `W` is norm-closed and sequential weak
  lower semicontinuity of `P.energy`.
* Weak compactness of bounded parts `P.unitConstraint W ∩ closedBall 0 R` and of energy sublevels
  `{u ∈ P.unitConstraint W | P.energy u ≤ b}` in reflexive spaces, together with norm compactness
  and weak compactness of the set of constrained minimizers.
* Attainment of the constrained Rayleigh minimum (`CompactFormPair.exists_minimum_on_unitConstraint`
  and its reflexive form `exists_minimum_on_unitConstraint_of_surjective`), its Rayleigh-quotient
  characterization, and identification with `‖IsCoercive.formSolutionOperator‖⁻¹` over `ℝ`.
* The restricted Euler–Lagrange equation (`CompactFormPair.equation_of_constrained_minimum`): every
  minimizer `u` of `P.energy` on `P.unitConstraint W` satisfies
  `P.form u v = (P.energy u : 𝕜) * ⟪P.inclusion u, P.inclusion v⟫_𝕜` for all `v : E` with
  `P.inclusion v ∈ W`, without assuming `W` is closed.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, Sections 4.8 and 4.10.
* V. Ivrii, *Partial Differential Equations*, Section 13.1, Theorem 4.
-/

public section

noncomputable section

open Bornology Filter Metric Set Topology
open scoped InnerProductSpace

namespace TauCeti

namespace CompactFormPair

section UnitConstraint

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The constrained unit sphere `S_W = {u : E | j u ∈ W ∧ ‖j u‖ = 1}` of a submodule `W ≤ H`. -/
def unitConstraint (P : CompactFormPair 𝕜 E H) (W : Submodule 𝕜 H) : Set E :=
  {u | P.inclusion u ∈ W ∧ ‖P.inclusion u‖ = 1}

@[simp]
theorem mem_unitConstraint_iff (P : CompactFormPair 𝕜 E H) {W : Submodule 𝕜 H} {u : E} :
    u ∈ P.unitConstraint W ↔ P.inclusion u ∈ W ∧ ‖P.inclusion u‖ = 1 :=
  Iff.rfl

/-- Every vector in `P.unitConstraint W` has nonzero image under `P.inclusion`. -/
theorem inclusion_ne_zero_of_mem_unitConstraint (P : CompactFormPair 𝕜 E H) {W : Submodule 𝕜 H}
    {u : E} (hu : u ∈ P.unitConstraint W) : P.inclusion u ≠ 0 := by
  intro h
  have h1 := hu.2
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-- Every vector in `P.unitConstraint W` is nonzero. -/
theorem ne_zero_of_mem_unitConstraint (P : CompactFormPair 𝕜 E H) {W : Submodule 𝕜 H}
    {u : E} (hu : u ∈ P.unitConstraint W) : u ≠ 0 :=
  fun h => P.inclusion_ne_zero_of_mem_unitConstraint hu (by simp [h])

/-- The constrained sphere is monotone in the ambient submodule `W`. -/
theorem unitConstraint_mono (P : CompactFormPair 𝕜 E H) {W₁ W₂ : Submodule 𝕜 H} (h : W₁ ≤ W₂) :
    P.unitConstraint W₁ ⊆ P.unitConstraint W₂ :=
  fun _ hu => ⟨h hu.1, hu.2⟩

/-- Phase invariance of the constrained sphere: scaling by a unit scalar `‖c‖ = 1` preserves
membership in `P.unitConstraint W`. -/
theorem smul_mem_unitConstraint_iff (P : CompactFormPair 𝕜 E H) {W : Submodule 𝕜 H}
    {c : 𝕜} (hc : ‖c‖ = 1) {u : E} :
    c • u ∈ P.unitConstraint W ↔ u ∈ P.unitConstraint W := by
  have hcne : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc
    exact zero_ne_one hc
  simp only [mem_unitConstraint_iff, map_smul, W.smul_mem_iff hcne, norm_smul, hc, one_mul]

/-- Phase invariance of constrained minimizers: multiplying by a unit scalar `‖c‖ = 1` preserves
minimality on `P.unitConstraint W`. -/
@[simp]
theorem isMinOn_unitConstraint_smul_iff (P : CompactFormPair 𝕜 E H) {W : Submodule 𝕜 H}
    {c : 𝕜} (hc : ‖c‖ = 1) {u : E} :
    IsMinOn P.energy (P.unitConstraint W) (c • u) ↔
      IsMinOn P.energy (P.unitConstraint W) u := by
  simp only [isMinOn_iff, P.energy_smul, hc, one_pow, one_mul]

theorem mem_unitConstraint_comapEquiv {E' : Type*} [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (P : CompactFormPair 𝕜 E H) (e : E' ≃L[𝕜] E) (W : Submodule 𝕜 H) (u : E') :
    u ∈ (P.comapEquiv e).unitConstraint W ↔ e u ∈ P.unitConstraint W := by
  simp [mem_unitConstraint_iff]

theorem mem_unitConstraint_mapLinearIsometryEquiv {H' : Type*}
    [SeminormedAddCommGroup H'] [NormedSpace 𝕜 H']
    (P : CompactFormPair 𝕜 E H) (U : H ≃ₗᵢ[𝕜] H') (W : Submodule 𝕜 H') (u : E) :
    u ∈ (P.mapLinearIsometryEquiv U).unitConstraint W ↔
      u ∈ P.unitConstraint (W.comap U.toLinearMap) := by
  simp [mem_unitConstraint_iff, U.norm_map]

@[simp]
theorem unitConstraint_restrictScalars [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
    (P : CompactFormPair 𝕜 E H) (W : Submodule 𝕜 H) :
    P.restrictScalars.unitConstraint (W.restrictScalars ℝ) = P.unitConstraint W := by
  ext u
  simp [mem_unitConstraint_iff]

/-- Quantitative lower bound on the constrained sphere: any shifted lower bound
`c ‖u‖² ≤ q(u) + ω ‖j u‖²` with `0 ≤ c` forces `-ω ≤ q(u)` on `P.unitConstraint W`. -/
theorem neg_le_energy_of_mem_unitConstraint (P : CompactFormPair 𝕜 E H) {W : Submodule 𝕜 H}
    {c ω : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ v : E, c * ‖v‖ ^ 2 ≤ P.energy v + ω * ‖P.inclusion v‖ ^ 2)
    {u : E} (hu : u ∈ P.unitConstraint W) :
    -ω ≤ P.energy u := by
  have h1 := hbound u
  rw [hu.2] at h1
  have hnonneg : 0 ≤ c * ‖u‖ ^ 2 := mul_nonneg hc (sq_nonneg _)
  linarith

/-- The energy is bounded below on every constrained sphere `P.unitConstraint W`. -/
theorem bddBelow_energy_image_unitConstraint (P : CompactFormPair 𝕜 E H) (W : Submodule 𝕜 H) :
    BddBelow (P.energy '' P.unitConstraint W) := by
  obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
  simp_rw [← P.energy_def] at hbound
  refine ⟨-ω, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact P.neg_le_energy_of_mem_unitConstraint hc.le hbound hu

/-- Every energy sublevel `{u ∈ P.unitConstraint W | P.energy u ≤ b}` is norm-bounded in `E`. -/
theorem hasBoundedSublevelsOn_energy_unitConstraint (P : CompactFormPair 𝕜 E H)
    (W : Submodule 𝕜 H) :
    HasBoundedSublevelsOn P.energy (P.unitConstraint W) := by
  obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
  rw [hasBoundedSublevelsOn_iff]
  intro b
  refine isBounded_iff_forall_norm_le.mpr ⟨Real.sqrt ((b + ω) / c), ?_⟩
  rintro u ⟨huW, hub⟩
  have hsq : ‖u‖ ^ 2 ≤ (b + ω) / c := by
    rw [le_div_iff₀ hc]
    have h1 := hbound u
    rw [← P.energy_def, huW.2] at h1
    nlinarith
  exact Real.le_sqrt_of_sq_le hsq

end UnitConstraint

section UnitConstraintShift

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H]

@[simp]
theorem unitConstraint_shift (P : CompactFormPair 𝕜 E H) (α : ℝ) (W : Submodule 𝕜 H) :
    (P.shift α).unitConstraint W = P.unitConstraint W := by
  ext u
  simp [mem_unitConstraint_iff]

end UnitConstraintShift

section Normalization

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Normalizing a vector `u` with `P.inclusion u ∈ W` and `P.inclusion u ≠ 0` lands in
`P.unitConstraint W`. -/
theorem inv_norm_smul_mem_unitConstraint (P : CompactFormPair 𝕜 E H) {W : Submodule 𝕜 H}
    {u : E} (huW : P.inclusion u ∈ W) (hu : P.inclusion u ≠ 0) :
    ((‖P.inclusion u‖⁻¹ : ℝ) : 𝕜) • u ∈ P.unitConstraint W := by
  refine ⟨?_, ?_⟩
  · rw [map_smul]
    exact W.smul_mem _ huW
  · rw [map_smul, RCLike.ofReal_inv]
    exact norm_smul_inv_norm (𝕜 := 𝕜) hu

/-- The constrained sphere `P.unitConstraint W` is nonempty if and only if some form-domain vector
has a nonzero image in `W`. -/
theorem unitConstraint_nonempty_iff (P : CompactFormPair 𝕜 E H) (W : Submodule 𝕜 H) :
    (P.unitConstraint W).Nonempty ↔ ∃ u : E, P.inclusion u ∈ W ∧ P.inclusion u ≠ 0 := by
  refine ⟨fun ⟨u, hu⟩ => ⟨u, hu.1, P.inclusion_ne_zero_of_mem_unitConstraint hu⟩, ?_⟩
  rintro ⟨u, huW, hu⟩
  exact ⟨_, P.inv_norm_smul_mem_unitConstraint huW hu⟩

/-- A vector `u` minimizes `P.energy` on `P.unitConstraint W` if and only if
`P.energy u * ‖P.inclusion v‖² ≤ P.energy v` for every `v` with `P.inclusion v ∈ W`. -/
theorem isMinOn_unitConstraint_iff_forall_mul_norm_sq_le (P : CompactFormPair 𝕜 E H)
    {W : Submodule 𝕜 H} {u : E} :
    IsMinOn P.energy (P.unitConstraint W) u ↔
      ∀ v : E, P.inclusion v ∈ W → P.energy u * ‖P.inclusion v‖ ^ 2 ≤ P.energy v := by
  refine ⟨fun hmin v hvW => ?_, fun hle v hv => ?_⟩
  · by_cases hv0 : P.inclusion v = 0
    · have hvz : v = 0 := (P.inclusion.toLinearMap.map_eq_zero_iff P.injective).mp hv0
      simp [hvz]
    · have hpos : 0 < ‖P.inclusion v‖ := norm_pos_iff.mpr hv0
      have hnorm : ((‖P.inclusion v‖⁻¹ : ℝ) : 𝕜) • v ∈ P.unitConstraint W :=
        P.inv_norm_smul_mem_unitConstraint hvW hv0
      have hle' : P.energy u ≤ P.energy (((‖P.inclusion v‖⁻¹ : ℝ) : 𝕜) • v) := hmin hnorm
      rw [P.energy_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hpos)] at hle'
      have hmul := mul_le_mul_of_nonneg_right hle' (sq_nonneg ‖P.inclusion v‖)
      have hcancel : (‖P.inclusion v‖⁻¹) ^ 2 * P.energy v * ‖P.inclusion v‖ ^ 2 = P.energy v := by
        field_simp
      linarith
  · have h := hle v hv.1
    rw [hv.2] at h
    simpa using h

/-- Rayleigh-quotient characterization of constrained minimizers: `u ∈ P.unitConstraint W`
minimizes `P.energy` on `P.unitConstraint W` if and only if `P.energy u` is the least value of
`P.energy v / ‖P.inclusion v‖²` over `v : E` with `P.inclusion v ∈ W` and `P.inclusion v ≠ 0`. -/
theorem isMinOn_unitConstraint_iff_isLeast_rayleighQuotient (P : CompactFormPair 𝕜 E H)
    {W : Submodule 𝕜 H} {u : E} (hu : u ∈ P.unitConstraint W) :
    IsMinOn P.energy (P.unitConstraint W) u ↔
      IsLeast {r : ℝ | ∃ v : E, P.inclusion v ∈ W ∧ P.inclusion v ≠ 0 ∧
        P.energy v / ‖P.inclusion v‖ ^ 2 = r} (P.energy u) := by
  rw [P.isMinOn_unitConstraint_iff_forall_mul_norm_sq_le]
  refine ⟨fun hle => ⟨⟨u, hu.1, P.inclusion_ne_zero_of_mem_unitConstraint hu, by simp [hu.2]⟩,
    ?_⟩, fun ⟨_, hlb⟩ v hvW => ?_⟩
  · rintro r ⟨v, hvW, hvne, rfl⟩
    rw [le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hvne))]
    exact hle v hvW
  · by_cases hvne : P.inclusion v = 0
    · have hvz : v = 0 := (P.inclusion.toLinearMap.map_eq_zero_iff P.injective).mp hvne
      simp [hvz]
    · have hpos : (0 : ℝ) < ‖P.inclusion v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hvne)
      exact (le_div_iff₀ hpos).mp (hlb ⟨v, hvW, hvne, rfl⟩)

end Normalization

section WeakSequential

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- For a norm-closed submodule `W ≤ H`, the constrained sphere `P.unitConstraint W` is
sequentially weakly closed in `E`. -/
theorem mem_unitConstraint_of_tendsto_toWeakSpace (P : CompactFormPair 𝕜 E H)
    {W : Submodule 𝕜 H} (hW : IsClosed (W : Set H)) {u : ℕ → E} {x : E}
    (hu : ∀ n, u n ∈ P.unitConstraint W)
    (hlim : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    x ∈ P.unitConstraint W := by
  have hj := ContinuousLinearMap.isDunfordPettis_def.mp P.compact.isDunfordPettis hlim
  refine ⟨hW.mem_of_tendsto hj (Eventually.of_forall fun n => (hu n).1), ?_⟩
  have hnorm : Tendsto (fun n => ‖P.inclusion (u n)‖) atTop (𝓝 (1 : ℝ)) := by
    simpa only [fun n => (hu n).2] using tendsto_const_nhds
  exact tendsto_nhds_unique hj.norm hnorm

private theorem tendsto_energy_sub_lower (P : CompactFormPair 𝕜 E H)
    {u : ℕ → E} {x : E} (ω : ℝ)
    (hlim : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    Tendsto (fun n => 2 * RCLike.re (P.form x (u n - x)) - ω * ‖P.inclusion (u n - x)‖ ^ 2)
      atTop (𝓝 0) := by
  have hform : Tendsto (fun n => RCLike.re (P.form x (u n - x))) atTop (𝓝 0) := by
    have hev : Tendsto (fun n => P.form x (u n)) atTop (𝓝 (P.form x x)) :=
      ((WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip (P.form x)).tendsto
        (toWeakSpace 𝕜 E x)).comp hlim
    have hsub : Tendsto (fun n => P.form x (u n - x)) atTop (𝓝 0) := by
      simpa only [map_sub, sub_self] using hev.sub_const (P.form x x)
    simpa only [Function.comp_def, map_zero] using (RCLike.continuous_re.tendsto 0).comp hsub
  have hj : Tendsto (fun n => ‖P.inclusion (u n - x)‖ ^ 2) atTop (𝓝 0) := by
    have hjsub : Tendsto (fun n => P.inclusion (u n - x)) atTop (𝓝 0) := by
      simpa only [map_sub, sub_self] using
        (ContinuousLinearMap.isDunfordPettis_def.mp P.compact.isDunfordPettis hlim).sub_const
          (P.inclusion x)
    simpa using hjsub.norm.pow 2
  simpa using (hform.const_mul 2).sub (hj.const_mul ω)

private theorem energy_add_coercive_le (P : CompactFormPair 𝕜 E H) {c ω : ℝ}
    (hbound : ∀ w : E, c * ‖w‖ ^ 2 ≤ RCLike.re (P.form w w) + ω * ‖P.inclusion w‖ ^ 2)
    (v x : E) :
    P.energy x + c * ‖v - x‖ ^ 2 +
        (2 * RCLike.re (P.form x (v - x)) - ω * ‖P.inclusion (v - x)‖ ^ 2) ≤
      P.energy v := by
  have h1 := hbound (v - x)
  have h2 := P.energy_sub_energy v x
  rw [← P.energy_def] at h1
  linarith

private theorem energy_le_of_tendsto_toWeakSpace_of_le_tendsto (P : CompactFormPair 𝕜 E H)
    {u : ℕ → E} {x : E} {f : ℕ → ℝ} {r : ℝ}
    (hlim : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)))
    (hf : Tendsto f atTop (𝓝 r)) (hle : ∀ n, P.energy (u n) ≤ f n) :
    P.energy x ≤ r := by
  obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
  have hlhs :
      Tendsto (fun n => P.energy x +
        (2 * RCLike.re (P.form x (u n - x)) - ω * ‖P.inclusion (u n - x)‖ ^ 2))
        atTop (𝓝 (P.energy x)) := by
    simpa using tendsto_const_nhds.add (P.tendsto_energy_sub_lower ω hlim)
  refine le_of_tendsto_of_tendsto hlhs hf (Eventually.of_forall fun n => ?_)
  have h1 := P.energy_add_coercive_le hbound (u n) x
  have hnonneg : 0 ≤ c * ‖u n - x‖ ^ 2 := mul_nonneg hc.le (sq_nonneg _)
  linarith [hle n]

/-- The energy of a compact form pair is sequentially weakly lower semicontinuous: along any
weakly convergent sequence `u n ⇀ x` with `P.energy (u n) → r`, we have `P.energy x ≤ r`. -/
theorem energy_le_of_tendsto_toWeakSpace (P : CompactFormPair 𝕜 E H)
    {u : ℕ → E} {x : E} {r : ℝ}
    (hlim : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)))
    (hr : Tendsto (fun n => P.energy (u n)) atTop (𝓝 r)) :
    P.energy x ≤ r :=
  P.energy_le_of_tendsto_toWeakSpace_of_le_tendsto hlim hr fun _ => le_rfl

/-- Sequential weak closedness of energy sublevels: if `u n ⇀ x` weakly and `P.energy (u n) ≤ b`
for all `n`, then `P.energy x ≤ b`. -/
theorem energy_le_of_tendsto_toWeakSpace_of_le (P : CompactFormPair 𝕜 E H)
    {u : ℕ → E} {x : E} {b : ℝ}
    (hlim : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)))
    (hb : ∀ n, P.energy (u n) ≤ b) :
    P.energy x ≤ b :=
  P.energy_le_of_tendsto_toWeakSpace_of_le_tendsto hlim tendsto_const_nhds hb

/-- Weak convergence `u n ⇀ x` together with energy convergence `P.energy (u n) → P.energy x`
implies strong (norm) convergence `u n → x`. -/
theorem tendsto_of_tendsto_toWeakSpace_of_tendsto_energy (P : CompactFormPair 𝕜 E H)
    {u : ℕ → E} {x : E}
    (hlim : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)))
    (henergy : Tendsto (fun n => P.energy (u n)) atTop (𝓝 (P.energy x))) :
    Tendsto u atTop (𝓝 x) := by
  obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
  have hsq_le : ∀ n,
      ‖u n - x‖ ^ 2 ≤
        (P.energy (u n) - P.energy x -
          (2 * RCLike.re (P.form x (u n - x)) - ω * ‖P.inclusion (u n - x)‖ ^ 2)) / c := by
    intro n
    rw [le_div_iff₀ hc]
    linarith [P.energy_add_coercive_le hbound (u n) x]
  have hrhs :
      Tendsto (fun n =>
        (P.energy (u n) - P.energy x -
          (2 * RCLike.re (P.form x (u n - x)) - ω * ‖P.inclusion (u n - x)‖ ^ 2)) / c)
        atTop (𝓝 0) := by
    have hdiff := (henergy.sub_const (P.energy x)).sub (P.tendsto_energy_sub_lower ω hlim)
    simpa using hdiff.div_const c
  have hnorm_sq : Tendsto (fun n => ‖u n - x‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) hsq_le hrhs
  have hnorm : Tendsto (fun n => ‖u n - x‖) atTop (𝓝 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hnorm_sq
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

end WeakSequential

section WeakCompactness

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

private theorem isCompact_toWeakSpace_of_isBounded_of_seqClosed {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hE : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E))
    {S : Set E} (hS : IsBounded S)
    (hclosed : ∀ ⦃u : ℕ → E⦄ ⦃x : E⦄, (∀ n, u n ∈ S) →
      Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)) → x ∈ S) :
    IsCompact (toWeakSpace 𝕜 E '' S) := by
  rw [TauCeti.isCompact_toWeakSpace_iff_isSeqCompact]
  intro w hw
  choose u hu hwu using hw
  have hcomp : IsCompact (closure (toWeakSpace 𝕜 E '' S)) :=
    TauCeti.isCompact_closure_toWeakSpace_of_isBounded hE hS
  obtain ⟨x, φ, hφ, hlim⟩ :=
    TauCeti.tendsto_subseq_toWeakSpace_of_isCompact_closure hcomp hu
  refine ⟨toWeakSpace 𝕜 E x, mem_image_of_mem _ (hclosed (fun n => hu (φ n)) hlim), φ, hφ, ?_⟩
  simpa only [Function.comp_def, hwu] using hlim

/-- Weak compactness of bounded parts of the constrained sphere in a reflexive space: for closed
`W ≤ H` and every radius `R`, `P.unitConstraint W ∩ closedBall 0 R` is weakly compact. -/
theorem isCompact_toWeakSpace_unitConstraint_inter_closedBall (P : CompactFormPair 𝕜 E H)
    (hE : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E))
    (W : Submodule 𝕜 H) (hW : IsClosed (W : Set H)) (R : ℝ) :
    IsCompact (toWeakSpace 𝕜 E '' (P.unitConstraint W ∩ closedBall 0 R)) := by
  refine isCompact_toWeakSpace_of_isBounded_of_seqClosed hE
    (isBounded_closedBall.subset inter_subset_right) fun u x hu hlim => ⟨?_, ?_⟩
  · exact P.mem_unitConstraint_of_tendsto_toWeakSpace hW (fun n => (hu n).1) hlim
  · have hclosed := (TauCeti.isCompact_toWeakSpace_closedBall hE 0 R).isClosed
    exact (toWeakSpace 𝕜 E).injective.mem_set_image.mp <|
      hclosed.mem_of_tendsto hlim (Eventually.of_forall fun n => mem_image_of_mem _ (hu n).2)

/-- Weak compactness of every constrained energy sublevel in a reflexive space. -/
theorem isCompact_toWeakSpace_sublevel_unitConstraint (P : CompactFormPair 𝕜 E H)
    (hE : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E))
    (W : Submodule 𝕜 H) (hW : IsClosed (W : Set H)) (b : ℝ) :
    IsCompact (toWeakSpace 𝕜 E '' {u ∈ P.unitConstraint W | P.energy u ≤ b}) := by
  refine isCompact_toWeakSpace_of_isBounded_of_seqClosed hE
    ((P.hasBoundedSublevelsOn_energy_unitConstraint W).isBounded_sublevel b)
    fun u x hu hlim => ⟨?_, ?_⟩
  · exact P.mem_unitConstraint_of_tendsto_toWeakSpace hW (fun n => (hu n).1) hlim
  · exact P.energy_le_of_tendsto_toWeakSpace_of_le hlim fun n => (hu n).2

/-- Norm compactness of the set of constrained minimizers on `P.unitConstraint W` in a reflexive
space whenever `W` is norm-closed. -/
theorem isCompact_minimizers_unitConstraint_of_surjective (P : CompactFormPair 𝕜 E H)
    (hE : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E))
    (W : Submodule 𝕜 H) (hW : IsClosed (W : Set H)) :
    IsCompact {u ∈ P.unitConstraint W | IsMinOn P.energy (P.unitConstraint W) u} := by
  rw [isCompact_iff_isSeqCompact]
  intro u hu
  have hsub_eq :
      {v ∈ P.unitConstraint W | IsMinOn P.energy (P.unitConstraint W) v} =
        {v ∈ P.unitConstraint W | P.energy v ≤ P.energy (u 0)} :=
    (hu 0).2.minimizers_eq_sublevel (hu 0).1
  have hcomp := P.isCompact_toWeakSpace_sublevel_unitConstraint hE W hW (P.energy (u 0))
  obtain ⟨_, ⟨x, hxsub, rfl⟩, φ, hφ, hlim⟩ :=
    TauCeti.isSeqCompact_toWeakSpace_of_isCompact hcomp fun n =>
      mem_image_of_mem (toWeakSpace 𝕜 E) (hsub_eq ▸ hu n)
  have hxmin : x ∈ {v ∈ P.unitConstraint W | IsMinOn P.energy (P.unitConstraint W) v} :=
    hsub_eq ▸ hxsub
  refine ⟨x, hxmin, φ, hφ, P.tendsto_of_tendsto_toWeakSpace_of_tendsto_energy hlim ?_⟩
  have heq_energy : ∀ n, P.energy (u (φ n)) = P.energy x :=
    fun n => le_antisymm ((hu (φ n)).2 hxmin.1) (hxmin.2 (hu (φ n)).1)
  exact tendsto_const_nhds.congr fun n => (heq_energy n).symm

/-- Weak compactness of the set of constrained minimizers in a reflexive space. -/
theorem isCompact_toWeakSpace_minimizers_unitConstraint_of_surjective (P : CompactFormPair 𝕜 E H)
    (hE : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E))
    (W : Submodule 𝕜 H) (hW : IsClosed (W : Set H)) :
    IsCompact (toWeakSpace 𝕜 E ''
      {u ∈ P.unitConstraint W | IsMinOn P.energy (P.unitConstraint W) u}) := by
  simpa only [toWeakSpaceCLM_eq_toWeakSpace] using
    (P.isCompact_minimizers_unitConstraint_of_surjective hE W hW).image
      (toWeakSpaceCLM 𝕜 E).continuous

/-- **Constrained Rayleigh minimum** (reflexive form): if `E` is reflexive and `W ≤ H` is a
norm-closed submodule containing a nonzero image of `P.inclusion`, then `P.energy` attains its
minimum on `P.unitConstraint W`. -/
theorem exists_minimum_on_unitConstraint_of_surjective (P : CompactFormPair 𝕜 E H)
    (hE : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E))
    (W : Submodule 𝕜 H) (hW : IsClosed (W : Set H))
    (hne : ∃ u : E, P.inclusion u ∈ W ∧ P.inclusion u ≠ 0) :
    ∃ u ∈ P.unitConstraint W, IsMinOn P.energy (P.unitConstraint W) u := by
  obtain ⟨u₀, hu₀⟩ := (P.unitConstraint_nonempty_iff W).mpr hne
  let S₀ : Set E := {v ∈ P.unitConstraint W | P.energy v ≤ P.energy u₀}
  have hcomp : IsCompact (toWeakSpace 𝕜 E '' S₀) :=
    P.isCompact_toWeakSpace_sublevel_unitConstraint hE W hW (P.energy u₀)
  have hlsc :
      LowerSemicontinuousOn (fun w : WeakSpace 𝕜 E => P.energy ((toWeakSpace 𝕜 E).symm w))
        (toWeakSpace 𝕜 E '' S₀) := by
    rw [lowerSemicontinuousOn_iff_preimage_Iic]
    intro b
    refine ⟨toWeakSpace 𝕜 E '' {v ∈ P.unitConstraint W | P.energy v ≤ min (P.energy u₀) b},
      (P.isCompact_toWeakSpace_sublevel_unitConstraint hE W hW (min (P.energy u₀) b)).isClosed, ?_⟩
    ext w
    refine ⟨fun ⟨hw, hvb⟩ => ⟨hw, ?_⟩, fun ⟨hw, hwC⟩ => ⟨hw, ?_⟩⟩
    · obtain ⟨v, ⟨hvW, hvu₀⟩, rfl⟩ := hw
      exact ⟨v, ⟨hvW, le_min hvu₀ (by simpa using hvb)⟩, rfl⟩
    · obtain ⟨v', ⟨_, hv'min⟩, rfl⟩ := hwC
      simpa using (le_min_iff.mp hv'min).2
  exact TauCeti.exists_isMinOn_of_isCompact_toWeakSpace_sublevel ⟨u₀, hu₀, le_rfl⟩ hcomp hlsc

end WeakCompactness

section Hilbert

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- **Constrained Rayleigh minimum** on a Hilbert form domain: for a complete inner-product space
`E` and a norm-closed submodule `W ≤ H` containing a nonzero image of `P.inclusion`, `P.energy`
attains its minimum on `P.unitConstraint W`. -/
theorem exists_minimum_on_unitConstraint (P : CompactFormPair 𝕜 E H)
    (W : Submodule 𝕜 H) (hW : IsClosed (W : Set H))
    (hne : ∃ u : E, P.inclusion u ∈ W ∧ P.inclusion u ≠ 0) :
    ∃ u ∈ P.unitConstraint W, IsMinOn P.energy (P.unitConstraint W) u := by
  have : UniformConvexSpace E :=
    let _ : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
    inferInstance
  exact P.exists_minimum_on_unitConstraint_of_surjective
    (TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace (𝕜 := 𝕜) (E := E)) W hW hne

/-- On a Hilbert form domain, the set of constrained minimizers on `P.unitConstraint W` is
norm-compact whenever `W` is norm-closed. -/
theorem isCompact_minimizers_unitConstraint (P : CompactFormPair 𝕜 E H)
    (W : Submodule 𝕜 H) (hW : IsClosed (W : Set H)) :
    IsCompact {u ∈ P.unitConstraint W | IsMinOn P.energy (P.unitConstraint W) u} := by
  have : UniformConvexSpace E :=
    let _ : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
    inferInstance
  exact P.isCompact_minimizers_unitConstraint_of_surjective
    (TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace (𝕜 := 𝕜) (E := E)) W hW

end Hilbert

section RealComparison

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Over `ℝ`, when `P.form` is coercive, the minimum of `P.energy` on the full unit sphere
`P.unitConstraint ⊤` agrees with `‖hB.formSolutionOperator P.inclusion‖⁻¹`. -/
theorem energy_eq_inv_norm_formSolutionOperator (P : CompactFormPair ℝ E H)
    (hB : IsCoercive P.form) {u : E} (hu : u ∈ P.unitConstraint ⊤)
    (hmin : IsMinOn P.energy (P.unitConstraint ⊤) u) :
    P.energy u = ‖hB.formSolutionOperator P.inclusion‖⁻¹ := by
  have hJne : P.inclusion ≠ 0 := by
    intro h
    exact P.inclusion_ne_zero_of_mem_unitConstraint hu (by simp [h])
  have hsymm : ∀ x y : E, P.form x y = P.form y x := fun x y => by
    simpa only [star_trivial] using P.hermitian x y
  have hleast₁ :
      IsLeast {r : ℝ | ∃ v : E, P.inclusion v ≠ 0 ∧ P.form v v / ‖P.inclusion v‖ ^ 2 = r}
        ‖hB.formSolutionOperator P.inclusion‖⁻¹ :=
    hB.isLeast_rayleighQuotient P.compact hsymm hJne
  have hleast₂ :
      IsLeast {r : ℝ | ∃ v : E, P.inclusion v ≠ 0 ∧ P.form v v / ‖P.inclusion v‖ ^ 2 = r}
        (P.energy u) := by
    simpa only [Submodule.mem_top, true_and, energy_def, RCLike.re_to_real] using
      (P.isMinOn_unitConstraint_iff_isLeast_rayleighQuotient hu).mp hmin
  exact hleast₂.unique hleast₁

/-- Over `ℝ`, after a shift `α` making `(P.shift α).form` coercive, the shifted minimum
`P.energy u + α` on `P.unitConstraint ⊤` equals `‖hB.formSolutionOperator P.inclusion‖⁻¹`. -/
theorem energy_add_eq_inv_norm_formSolutionOperator_shift (P : CompactFormPair ℝ E H)
    {α : ℝ} (hB : IsCoercive (P.shift α).form) {u : E} (hu : u ∈ P.unitConstraint ⊤)
    (hmin : IsMinOn P.energy (P.unitConstraint ⊤) u) :
    P.energy u + α = ‖hB.formSolutionOperator P.inclusion‖⁻¹ := by
  have hmin' : IsMinOn (P.shift α).energy ((P.shift α).unitConstraint ⊤) u := by
    rw [unitConstraint_shift, isMinOn_iff]
    intro v hv
    simp only [shift_energy, hu.2, hv.2]
    linarith [isMinOn_iff.mp hmin v hv]
  have h := (P.shift α).energy_eq_inv_norm_formSolutionOperator hB
    (by simpa only [unitConstraint_shift] using hu) hmin'
  simpa only [shift_energy, shift_inclusion, hu.2, one_pow, mul_one] using h

end RealComparison

section EulerLagrange

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

private theorem re_shift_form_eq_zero_of_isMinOn (P : CompactFormPair 𝕜 E H)
    (W : Submodule 𝕜 H) {u : E} (hu : u ∈ P.unitConstraint W)
    (hmin : IsMinOn P.energy (P.unitConstraint W) u) :
    ∀ w : E, P.inclusion w ∈ W →
      RCLike.re ((P.shift (-P.energy u)).form u w) = 0 := by
  have hquad : ∀ v : E, P.inclusion v ∈ W → P.energy u * ‖P.inclusion v‖ ^ 2 ≤ P.energy v :=
    P.isMinOn_unitConstraint_iff_forall_mul_norm_sq_le.mp hmin
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let _ : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
  let _ : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
  let _ : IsScalarTower ℝ 𝕜 H := RestrictScalars.isScalarTower ℝ 𝕜 H
  let P' := (P.shift (-P.energy u)).restrictScalars
  let V₀ : Submodule ℝ E := (W.comap P.inclusion.toLinearMap).restrictScalars ℝ
  let B : LinearMap.BilinForm ℝ V₀ := P'.form.toBilinForm.domRestrict₁₂ V₀ V₀
  have hB_apply : ∀ x y : V₀, B x y = P'.form x.1 y.1 := fun _ _ => by
    rw [LinearMap.domRestrict₁₂_apply, ContinuousLinearMap.toBilinForm_apply]
  have hB_diag : ∀ x : V₀, B x x = P.energy x.1 - P.energy u * ‖P.inclusion x.1‖ ^ 2 := fun x => by
    rw [hB_apply, ← RCLike.re_to_real (x := P'.form x.1 x.1), ← energy_def,
      restrictScalars_energy, shift_energy]
    ring
  have hs : ∀ x : V₀, 0 ≤ B x x := fun x => by
    rw [hB_diag]
    linarith [hquad x.1 x.2]
  have hB : LinearMap.IsSymm B := ⟨fun x y => by
    rw [hB_apply, hB_apply, RingHom.id_apply, P'.hermitian x.1 y.1, star_trivial]⟩
  have hBu : B ⟨u, hu.1⟩ ⟨u, hu.1⟩ = 0 := by
    rw [hB_diag]
    dsimp only
    rw [hu.2]
    ring
  have hker : ⟨u, hu.1⟩ ∈ LinearMap.ker B := (B.apply_apply_same_eq_zero_iff hs hB).mp hBu
  intro w hwW
  have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hker) ⟨w, hwW⟩
  rw [hB_apply, restrictScalars_form_apply] at h
  exact h

/-- **The restricted Euler–Lagrange equation**: any minimizer `u` of `P.energy` on the constrained
sphere `P.unitConstraint W` satisfies
`P.form u v = (P.energy u : 𝕜) * ⟪P.inclusion u, P.inclusion v⟫_𝕜`
for every `v : E` with `P.inclusion v ∈ W`. No closedness of `W` is required. -/
theorem equation_of_constrained_minimum (P : CompactFormPair 𝕜 E H)
    (W : Submodule 𝕜 H) (u : E)
    (hu : u ∈ P.unitConstraint W)
    (hmin : IsMinOn P.energy (P.unitConstraint W) u) :
    ∀ v : E, P.inclusion v ∈ W →
      P.form u v = (P.energy u : 𝕜) * ⟪P.inclusion u, P.inclusion v⟫_𝕜 := by
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let _ : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
  let V : Submodule 𝕜 E := W.comap P.inclusion.toLinearMap
  let φ : StrongDual 𝕜 V := ((P.shift (-P.energy u)).form u).comp V.subtypeL
  have hre : (StrongDual.extendRCLikeL (𝕜 := 𝕜) (F := V)).symm φ = 0 := by
    ext w
    rw [StrongDual.extendRCLikeL_symm_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', RCLike.reCLM_apply, zero_apply]
    exact P.re_shift_form_eq_zero_of_isMinOn W hu hmin w.1 w.2
  have hφ : φ = 0 := (StrongDual.extendRCLikeL (𝕜 := 𝕜) (F := V)).symm.injective
    (by simpa only [map_zero] using hre)
  intro v hvW
  have h := DFunLike.congr_fun hφ ⟨v, hvW⟩
  simp only [φ, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, shift_form_apply,
    RCLike.ofReal_neg, neg_mul, zero_apply] at h
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)

end EulerLagrange

end CompactFormPair

end TauCeti
