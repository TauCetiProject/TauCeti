/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.InnerProductSpace.Variational.CompactFormPair.Basic
public import TauCeti.Analysis.InnerProductSpace.Variational.Rayleigh
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Module.WeakSpace.SeqCompact
import TauCeti.Analysis.Normed.Operator.DunfordPettis.Basic
import TauCeti.Analysis.Variational.MinimizingSequence
import TauCeti.Analysis.Variational.QuadraticEnergy
import TauCeti.Order.Filter.Extr

/-!
# Constrained Rayleigh minima and restricted Euler–Lagrange equations

This file complements `TauCeti.Analysis.InnerProductSpace.Variational.CompactFormPair` with
additional theory for `P.energy` on the constrained unit sphere `P.unitConstraint W`:

* Transport, shift, and scalar-restriction identities for `P.unitConstraint W`, phase invariance of
  minimizers (`CompactFormPair.isMinOn_unitConstraint_smul_iff`), and the explicit `IsLeast`
  Rayleigh-quotient equivalence
  (`CompactFormPair.isMinOn_unitConstraint_iff_isLeast_rayleighQuotient`).
* Sequential weak-to-strong convergence
  (`CompactFormPair.tendsto_of_tendsto_toWeakSpace_of_tendsto_energy`), reflexive-space attainment
  (`CompactFormPair.exists_isMinOn_energy_unitConstraint_of_surjective`), and norm compactness of
  the set of constrained minimizers (`CompactFormPair.isCompact_minimizers_unitConstraint`).
* Over `ℝ`, identification of the constrained minimum on `P.unitConstraint ⊤` with
  `‖IsCoercive.formSolutionOperator‖⁻¹` (`CompactFormPair.energy_eq_inv_norm_formSolutionOperator`
  and `CompactFormPair.energy_add_eq_inv_norm_formSolutionOperator_shift`).
* The restricted Euler–Lagrange equation (`CompactFormPair.equation_of_constrained_minimum`): every
  minimizer `u` of `P.energy` on `P.unitConstraint W` satisfies
  `P.form u v = (P.energy u : 𝕜) * ⟪P.inclusion u, P.inclusion v⟫_𝕜` for all `v : V` with
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

variable {𝕜 V H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Every vector in `P.unitConstraint W` has nonzero image under `P.inclusion`. -/
theorem inclusion_ne_zero_of_mem_unitConstraint (P : CompactFormPair 𝕜 V H) {W : Submodule 𝕜 H}
    {u : V} (hu : u ∈ P.unitConstraint W) : P.inclusion u ≠ 0 := by
  intro h
  have h1 := (mem_unitConstraint.1 hu).2
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-- Every vector in `P.unitConstraint W` is nonzero. -/
theorem ne_zero_of_mem_unitConstraint (P : CompactFormPair 𝕜 V H) {W : Submodule 𝕜 H}
    {u : V} (hu : u ∈ P.unitConstraint W) : u ≠ 0 :=
  fun h => P.inclusion_ne_zero_of_mem_unitConstraint hu (by simp [h])

/-- Phase invariance of the constrained sphere: scaling by a unit scalar `‖c‖ = 1` preserves
membership in `P.unitConstraint W`. -/
theorem smul_mem_unitConstraint_iff (P : CompactFormPair 𝕜 V H) {W : Submodule 𝕜 H}
    {c : 𝕜} (hc : ‖c‖ = 1) {u : V} :
    c • u ∈ P.unitConstraint W ↔ u ∈ P.unitConstraint W := by
  have hcne : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc
    exact zero_ne_one hc
  simp only [mem_unitConstraint, map_smul, W.smul_mem_iff hcne, norm_smul, hc, one_mul]

/-- Phase invariance of constrained minimizers: multiplying by a unit scalar `‖c‖ = 1` preserves
minimality on `P.unitConstraint W`. -/
@[simp]
theorem isMinOn_unitConstraint_smul_iff (P : CompactFormPair 𝕜 V H) {W : Submodule 𝕜 H}
    {c : 𝕜} (hc : ‖c‖ = 1) {u : V} :
    IsMinOn P.energy (P.unitConstraint W) (c • u) ↔
      IsMinOn P.energy (P.unitConstraint W) u := by
  simp only [isMinOn_iff, P.energy_smul, hc, one_pow, one_mul]

theorem mem_unitConstraint_comapEquiv {V' : Type*} [NormedAddCommGroup V']
    [InnerProductSpace 𝕜 V'] (P : CompactFormPair 𝕜 V H) (e : V' ≃L[𝕜] V)
    (W : Submodule 𝕜 H) (u : V') :
    u ∈ (P.comapEquiv e).unitConstraint W ↔ e u ∈ P.unitConstraint W := by
  simp [mem_unitConstraint]

theorem mem_unitConstraint_mapLinearIsometryEquiv {H' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']
    (P : CompactFormPair 𝕜 V H) (U : H ≃ₗᵢ[𝕜] H') (W : Submodule 𝕜 H') (u : V) :
    u ∈ (P.mapLinearIsometryEquiv U).unitConstraint W ↔
      u ∈ P.unitConstraint (W.comap U.toLinearMap) := by
  simp [mem_unitConstraint, U.norm_map]

@[simp]
theorem unitConstraint_restrictScalars [InnerProductSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    [InnerProductSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
    (P : CompactFormPair 𝕜 V H) (W : Submodule 𝕜 H) :
    P.restrictScalars.unitConstraint (W.restrictScalars ℝ) = P.unitConstraint W := by
  ext u
  simp [mem_unitConstraint]

@[simp]
theorem unitConstraint_shift (P : CompactFormPair 𝕜 V H) (α : ℝ) (W : Submodule 𝕜 H) :
    (P.shift α).unitConstraint W = P.unitConstraint W := by
  ext u
  simp [mem_unitConstraint]

end UnitConstraint

section Normalization

variable {𝕜 V H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

private theorem image_energy_unitConstraint (P : CompactFormPair 𝕜 V H) (W : Submodule 𝕜 H) :
    P.energy '' P.unitConstraint W =
      {r : ℝ | ∃ v : V, P.inclusion v ∈ W ∧ P.inclusion v ≠ 0 ∧
        P.energy v / ‖P.inclusion v‖ ^ 2 = r} := by
  ext r
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, (mem_unitConstraint.1 hv).1, P.inclusion_ne_zero_of_mem_unitConstraint hv,
      by simp [(mem_unitConstraint.1 hv).2]⟩
  · rintro ⟨v, hvW, hvne, rfl⟩
    refine ⟨((‖P.inclusion v‖⁻¹ : ℝ) : 𝕜) • v, inv_norm_smul_mem_unitConstraint hvW hvne, ?_⟩
    simp [div_eq_inv_mul]

/-- Rayleigh-quotient characterization of constrained minimizers: `u ∈ P.unitConstraint W`
minimizes `P.energy` on `P.unitConstraint W` if and only if `P.energy u` is the least value of
`P.energy v / ‖P.inclusion v‖²` over `v : V` with `P.inclusion v ∈ W` and `P.inclusion v ≠ 0`. -/
theorem isMinOn_unitConstraint_iff_isLeast_rayleighQuotient (P : CompactFormPair 𝕜 V H)
    {W : Submodule 𝕜 H} {u : V} (hu : u ∈ P.unitConstraint W) :
    IsMinOn P.energy (P.unitConstraint W) u ↔
      IsLeast {r : ℝ | ∃ v : V, P.inclusion v ∈ W ∧ P.inclusion v ≠ 0 ∧
        P.energy v / ‖P.inclusion v‖ ^ 2 = r} (P.energy u) := by
  rw [← P.image_energy_unitConstraint W]
  exact ⟨fun hmin => ⟨mem_image_of_mem P.energy hu, forall_mem_image.mpr hmin⟩,
    fun hleast _ hv => hleast.2 (mem_image_of_mem P.energy hv)⟩

end Normalization

section WeakSequential

variable {𝕜 V H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The compact inclusion `P.inclusion` maps weakly convergent sequences to norm-convergent
sequences. -/
theorem tendsto_inclusion_of_tendsto_toWeakSpace (P : CompactFormPair 𝕜 V H)
    {u : ℕ → V} {x : V}
    (hlim : Tendsto (fun n => toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V x))) :
    Tendsto (fun n => P.inclusion (u n)) atTop (𝓝 (P.inclusion x)) :=
  ContinuousLinearMap.isDunfordPettis_def.mp P.isCompactOperator.isDunfordPettis hlim

private theorem tendsto_energy_sub_lower (P : CompactFormPair 𝕜 V H)
    {u : ℕ → V} {x : V} (ω : ℝ)
    (hlim : Tendsto (fun n => toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V x))) :
    Tendsto (fun n => 2 * RCLike.re (P.form x (u n - x)) - ω * ‖P.inclusion (u n - x)‖ ^ 2)
      atTop (𝓝 0) := by
  have hform : Tendsto (fun n => RCLike.re (P.form x (u n - x))) atTop (𝓝 0) := by
    have hev : Tendsto (fun n => P.form x (u n)) atTop (𝓝 (P.form x x)) :=
      ((WeakBilin.eval_continuous (topDualPairing 𝕜 V).flip (P.form x)).tendsto
        (toWeakSpace 𝕜 V x)).comp hlim
    have hsub : Tendsto (fun n => P.form x (u n - x)) atTop (𝓝 0) := by
      simpa only [map_sub, sub_self] using hev.sub_const (P.form x x)
    simpa only [Function.comp_def, map_zero] using (RCLike.continuous_re.tendsto 0).comp hsub
  have hj : Tendsto (fun n => ‖P.inclusion (u n - x)‖ ^ 2) atTop (𝓝 0) := by
    have hjsub : Tendsto (fun n => P.inclusion (u n - x)) atTop (𝓝 0) := by
      simpa only [map_sub, sub_self] using
        (P.tendsto_inclusion_of_tendsto_toWeakSpace hlim).sub_const (P.inclusion x)
    simpa using hjsub.norm.pow 2
  simpa using (hform.const_mul 2).sub (hj.const_mul ω)

private theorem energy_add_coercive_le (P : CompactFormPair 𝕜 V H) {c ω : ℝ}
    (hbound : ∀ w : V, c * ‖w‖ ^ 2 ≤ RCLike.re (P.form w w) + ω * ‖P.inclusion w‖ ^ 2)
    (v x : V) :
    P.energy x + c * ‖v - x‖ ^ 2 +
        (2 * RCLike.re (P.form x (v - x)) - ω * ‖P.inclusion (v - x)‖ ^ 2) ≤
      P.energy v := by
  have h1 := hbound (v - x)
  have h2 := P.energy_sub_energy v x
  rw [← P.energy_def] at h1
  linarith

/-- Weak convergence `u n ⇀ x` together with energy convergence `P.energy (u n) → P.energy x`
implies strong (norm) convergence `u n → x`. -/
theorem tendsto_of_tendsto_toWeakSpace_of_tendsto_energy (P : CompactFormPair 𝕜 V H)
    {u : ℕ → V} {x : V}
    (hlim : Tendsto (fun n => toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V x)))
    (henergy : Tendsto (fun n => P.energy (u n)) atTop (𝓝 (P.energy x))) :
    Tendsto u atTop (𝓝 x) := by
  obtain ⟨c, hc, ω, hbound⟩ := P.exists_shifted_coercive
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

variable {𝕜 V H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Constrained Rayleigh minimum** (reflexive form): if `V` is reflexive and `W ≤ H` is a
norm-closed submodule with nonempty constrained sphere `P.unitConstraint W`, then `P.energy`
attains its minimum on `P.unitConstraint W`. -/
theorem exists_isMinOn_energy_unitConstraint_of_surjective (P : CompactFormPair 𝕜 V H)
    (hV : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 V))
    (W : Submodule 𝕜 H) (hW : IsClosed (W : Set H))
    (hne : (P.unitConstraint W).Nonempty) :
    ∃ u ∈ P.unitConstraint W, IsMinOn P.energy (P.unitConstraint W) u :=
  exists_isMinOn_of_isSeqClosed hV hne
    (P.isSeqClosed_toWeakSpace_unitConstraint W hW)
    (P.lowerSemicontinuousOn_energy_comp_toWeakSpace_symm_unitConstraint
      W).seqLowerSemicontinuousOn
    (P.hasBoundedSublevelsOn_energy_unitConstraint W)

/-- Norm compactness of the set of constrained minimizers on `P.unitConstraint W` in a reflexive
space whenever `W` is norm-closed. -/
theorem isCompact_minimizers_unitConstraint_of_surjective (P : CompactFormPair 𝕜 V H)
    (hV : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 V))
    (W : Submodule 𝕜 H) (hW : IsClosed (W : Set H)) :
    IsCompact {u ∈ P.unitConstraint W | IsMinOn P.energy (P.unitConstraint W) u} := by
  rw [isCompact_iff_isSeqCompact]
  intro u hu
  have hsub_eq :
      {v ∈ P.unitConstraint W | IsMinOn P.energy (P.unitConstraint W) v} =
        {v ∈ P.unitConstraint W | P.energy v ≤ P.energy (u 0)} :=
    (hu 0).2.minimizers_eq_sublevel (hu 0).1
  have hcomp :
      IsCompact (toWeakSpace 𝕜 V '' {v ∈ P.unitConstraint W | P.energy v ≤ P.energy (u 0)}) :=
    isCompact_toWeakSpace_sublevel_of_isSeqClosed hV
      (P.isSeqClosed_toWeakSpace_unitConstraint W hW)
      (P.lowerSemicontinuousOn_energy_comp_toWeakSpace_symm_unitConstraint
        W).seqLowerSemicontinuousOn
      (P.energy (u 0))
      ((P.hasBoundedSublevelsOn_energy_unitConstraint W).isBounded_sublevel (P.energy (u 0)))
  obtain ⟨_, ⟨x, hxsub, rfl⟩, φ, hφ, hlim⟩ :=
    TauCeti.isSeqCompact_toWeakSpace_of_isCompact hcomp fun n =>
      mem_image_of_mem (toWeakSpace 𝕜 V) (hsub_eq ▸ hu n)
  have hxmin : x ∈ {v ∈ P.unitConstraint W | IsMinOn P.energy (P.unitConstraint W) v} :=
    hsub_eq ▸ hxsub
  refine ⟨x, hxmin, φ, hφ, P.tendsto_of_tendsto_toWeakSpace_of_tendsto_energy hlim ?_⟩
  have heq_energy : ∀ n, P.energy (u (φ n)) = P.energy x :=
    fun n => le_antisymm ((hu (φ n)).2 hxmin.1) (hxmin.2 (hu (φ n)).1)
  exact tendsto_const_nhds.congr fun n => (heq_energy n).symm

end WeakCompactness

section Hilbert

variable {𝕜 V H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- On a Hilbert form domain, the set of constrained minimizers on `P.unitConstraint W` is
norm-compact whenever `W` is norm-closed. -/
theorem isCompact_minimizers_unitConstraint (P : CompactFormPair 𝕜 V H)
    (W : Submodule 𝕜 H) (hW : IsClosed (W : Set H)) :
    IsCompact {u ∈ P.unitConstraint W | IsMinOn P.energy (P.unitConstraint W) u} :=
  P.isCompact_minimizers_unitConstraint_of_surjective
    (TauCeti.surjective_inclusionInDoubleDual_of_innerProductSpace (𝕜 := 𝕜)) W hW

end Hilbert

section RealComparison

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Over `ℝ`, when `P.form` is coercive, the minimum of `P.energy` on the full unit sphere
`P.unitConstraint ⊤` agrees with `‖hB.formSolutionOperator P.inclusion‖⁻¹`. -/
theorem energy_eq_inv_norm_formSolutionOperator (P : CompactFormPair ℝ V H)
    (hB : IsCoercive P.form) {u : V} (hu : u ∈ P.unitConstraint ⊤)
    (hmin : IsMinOn P.energy (P.unitConstraint ⊤) u) :
    P.energy u = ‖hB.formSolutionOperator P.inclusion‖⁻¹ := by
  have hJne : P.inclusion ≠ 0 := by
    intro h
    exact P.inclusion_ne_zero_of_mem_unitConstraint hu (by simp [h])
  have hsymm : ∀ x y : V, P.form x y = P.form y x := fun x y => by
    simpa only [star_trivial] using P.hermitian x y
  have hleast₁ :
      IsLeast {r : ℝ | ∃ v : V, P.inclusion v ≠ 0 ∧ P.form v v / ‖P.inclusion v‖ ^ 2 = r}
        ‖hB.formSolutionOperator P.inclusion‖⁻¹ :=
    hB.isLeast_rayleighQuotient P.isCompactOperator hsymm hJne
  have hleast₂ :
      IsLeast {r : ℝ | ∃ v : V, P.inclusion v ≠ 0 ∧ P.form v v / ‖P.inclusion v‖ ^ 2 = r}
        (P.energy u) := by
    simpa only [Submodule.mem_top, true_and, energy_def, RCLike.re_to_real] using
      (P.isMinOn_unitConstraint_iff_isLeast_rayleighQuotient hu).mp hmin
  exact hleast₂.unique hleast₁

/-- Over `ℝ`, after a shift `α` making `(P.shift α).form` coercive, the shifted minimum
`P.energy u + α` on `P.unitConstraint ⊤` equals `‖hB.formSolutionOperator P.inclusion‖⁻¹`. -/
theorem energy_add_eq_inv_norm_formSolutionOperator_shift (P : CompactFormPair ℝ V H)
    {α : ℝ} (hB : IsCoercive (P.shift α).form) {u : V} (hu : u ∈ P.unitConstraint ⊤)
    (hmin : IsMinOn P.energy (P.unitConstraint ⊤) u) :
    P.energy u + α = ‖hB.formSolutionOperator P.inclusion‖⁻¹ := by
  have hmin' : IsMinOn (P.shift α).energy ((P.shift α).unitConstraint ⊤) u := by
    rw [unitConstraint_shift, isMinOn_iff]
    intro v hv
    simp only [shift_energy, (mem_unitConstraint.1 hu).2, (mem_unitConstraint.1 hv).2]
    linarith [isMinOn_iff.mp hmin v hv]
  have h := (P.shift α).energy_eq_inv_norm_formSolutionOperator hB
    (by simpa only [unitConstraint_shift] using hu) hmin'
  simpa only [shift_energy, shift_inclusion, (mem_unitConstraint.1 hu).2, one_pow, mul_one] using h

end RealComparison

section EulerLagrange

variable {𝕜 V H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **The restricted Euler–Lagrange equation**: any minimizer `u` of `P.energy` on the constrained
sphere `P.unitConstraint W` satisfies
`P.form u v = (P.energy u : 𝕜) * ⟪P.inclusion u, P.inclusion v⟫_𝕜`
for every `v : V` with `P.inclusion v ∈ W`. No closedness of `W` is required. -/
theorem equation_of_constrained_minimum (P : CompactFormPair 𝕜 V H)
    (W : Submodule 𝕜 H) {u : V}
    (hu : u ∈ P.unitConstraint W)
    (hmin : IsMinOn P.energy (P.unitConstraint W) u) :
    ∀ v : V, P.inclusion v ∈ W →
      P.form u v = (P.energy u : 𝕜) * ⟪P.inclusion u, P.inclusion v⟫_𝕜 := by
  obtain ⟨huW, hu1⟩ := mem_unitConstraint.1 hu
  let V₀ : Submodule 𝕜 V := W.comap P.inclusion.toLinearMap
  let P' := (P.shift (-P.energy u)).restrict V₀
  have hq : ∀ w : V₀, 0 ≤ RCLike.re (P'.form w w) := fun w => by
    rw [← P'.energy_def, (P.shift (-P.energy u)).restrict_energy V₀ w, P.shift_energy]
    linarith [P.mul_norm_sq_le_energy_of_isMinOn hmin w.property]
  have hu₀ : RCLike.re (P'.form ⟨u, huW⟩ ⟨u, huW⟩) = 0 := by
    rw [← P'.energy_def, (P.shift (-P.energy u)).restrict_energy V₀ ⟨u, huW⟩, P.shift_energy, hu1]
    ring
  have hker : P'.form ⟨u, huW⟩ = 0 :=
    (ContinuousLinearMap.re_apply_self_eq_zero_iff P'.hermitian hq).mp hu₀
  intro v hvW
  have h := DFunLike.congr_fun hker ⟨v, hvW⟩
  simp only [P', restrict_form_apply, shift_form_apply, RCLike.ofReal_neg, neg_mul,
    zero_apply] at h
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)

end EulerLagrange

end CompactFormPair

end TauCeti
