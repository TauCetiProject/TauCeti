/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Monodromy
public import TauCeti.Geometry.Manifold.Flow.TransverseDilation
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# The flow-box dilation of a closed orbit

This file supplies the two halves of the flow-box perturbation step of the Kupka–Smale theorem for
closed orbits, which makes a closed orbit and all its covers nondegenerate by a perturbation
supported near one point of the orbit.

**The local dilation.** Let `u ≠ 0` be a vector of a finite-dimensional real normed space `E`, and
fix `ℓ` with `ℓ u = 1`. The transverse dilation fields of
`TauCeti.Geometry.Manifold.Flow.TransverseDilation` give a smooth field `Z` supported in a slab
`s₀ < ℓ z < s₁` and vanishing on the axis `ℝ • u`, such that the flow of `u + a • Z` dilates the
directions of `ker ℓ` by `exp a` across the slab. Cut off to a prescribed open set containing the
segment `[s₀, s₁] • u`, `W = χ • Z` is a smooth compactly supported field vanishing on the axis,
and the flow of `u + a • W` still runs along the axis, with time-`t` map of derivative
`w ↦ w + (exp a - 1) • (w - ℓ w • u)` at `0` for `t ≥ s₁`
(`TauCeti.exists_contDiff_flowOf_const_add_smul_axis`). This derivative is multiplication by
`exp a` modulo the flow line `ℝ ∙ u`.

**The effect on the return maps.** On a manifold, let `w` agree with `v` off a closed set avoided
by the orbit of `p` from time `σ` to the period `T₀`, and let the time-`σ` map of `w` at `p` be that
of `v` composed with a map acting as `c` modulo the flow line `ℝ ∙ v p`. Since the orbit returns to
`p` through the region where the fields agree, `p` is a closed orbit of `w` of the same period and
the linearized return maps of `w` are `c` times those of `v`
(`TauCeti.returnDerivative_eq_smul_of_eqOn_compl`, from
`TauCeti.returnDerivative_eq_smul_of_mfderiv_flowOf_eq` and
`TauCeti.mfderiv_flowOf_add_eq_of_eqOn`).

Together, in a chart in which `v` is the constant field `u` near `p`, they give the perturbation
`TauCeti.Geometry.Manifold.Flow.DilationPerturbation.Manifold`.

## Main results

* `TauCeti.exists_contDiff_flowOf_const_add_smul_axis`: the flow-box dilation field `W` of a
  constant field `u`, supported in a prescribed open set around a segment of the axis.
* `TauCeti.returnDerivative_eq_smul_of_eqOn_compl`: a field agreeing with `v` off a set avoided by
  the rest of a closed orbit, whose flow near `p` composes that of `v` with a map acting as `c`
  modulo the flow line, has `c` times the linearized return maps of `v`.

## References

* M. M. Peixoto, *On an approximation theorem of Kupka and Smale*, J. Differential Equations 3
  (1967), 214–227, §2 (local perturbations of closed orbits in flow boxes).
* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 3, §§3–4
  (the Kupka–Smale theorem).
-/

public section

noncomputable section

open Filter Function Metric Set
open scoped Manifold Topology ContDiff

namespace TauCeti

section Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]

/-- **A local change of the monodromy of a closed orbit.** Let `p` return to itself at time `T₀`
under a `C¹` field `v`, and let a `C¹` field `w` agree with `v` off a closed set `S` avoided by the
orbit of `p` from time `σ` to time `T₀`. Suppose that at time `σ` the flow of `w` carries `p` to the
same point as that of `v`, with derivative that of `v` precomposed with a map `D` of `T_p M` acting
as multiplication by `c` modulo the flow line `ℝ ∙ v p`. Then `p` also returns at time `T₀` under
`w`, and the linearized return map of every section `{g = g p}` transverse to `v` is multiplied by
`c`. -/
theorem returnDerivative_eq_smul_of_eqOn_compl {v w : (x : M) → TangentSpace I x} {p : M}
    {T₀ σ c : ℝ} (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p) (hσ : 0 ≤ σ) (hσT : σ ≤ T₀)
    (hw : CMDiff 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle I M))) (hwp : w p = v p)
    (hσw : (σ, p) ∈ flowDomain w) (hσvw : flowOf w σ p = flowOf v σ p)
    {D : TangentSpace I p → TangentSpace I p} (hD : ∀ ξ, D ξ - c • ξ ∈ ℝ ∙ v p)
    (hDσ : ∀ ξ : TangentSpace I p,
      -- The tangent spaces at the two values are both the model space `E`.
      @Eq E (mfderiv I I (flowOf w σ) p ξ) (mfderiv I I (flowOf v σ) p (D ξ)))
    {S : Set M} (hS : IsClosed S) (hwv : EqOn w v Sᶜ) (hSv : ∀ t ∈ Icc σ T₀, flowOf v t p ∉ S) :
    (T₀, p) ∈ flowDomain w ∧ flowOf w T₀ p = p ∧
      ∀ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g p → mvfderiv I g p (v p) ≠ 0 →
        returnDerivative w g T₀ p = c • returnDerivative v g T₀ p := by
  have hdom : ∀ t ∈ Icc 0 T₀, (t, p) ∈ flowDomain v := fun t ht ↦
    uIcc_subset_setOf_mem_flowDomain hP (Icc_subset_uIcc ht)
  have hσdom := hdom σ ⟨hσ, hσT⟩
  set q := flowOf v σ p
  -- After time `σ`, the trajectory runs where `w = v`, back to `p` at time `T₀`.
  have hleg : (T₀ - σ, q) ∈ flowDomain v := by
    rw [mem_flowDomain_flowOf_iff hv hσdom, add_sub_cancel]
    exact hP
  have hlegS : MapsTo (fun s ↦ flowOf v s q) (uIcc 0 (T₀ - σ)) Sᶜ := by
    intro s hs
    rw [uIcc_of_le (by linarith)] at hs
    have hσs : σ + s ∈ Icc σ T₀ := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    dsimp only [q]
    rw [(flowOf_add hv hσdom ((mem_flowDomain_flowOf_iff hv hσdom).2
      (hdom _ ⟨hσ.trans hσs.1, hσs.2⟩))).2]
    exact hSv _ hσs
  obtain ⟨hdomw, hvalw, hderw⟩ :=
    mfderiv_flowOf_add_eq_of_eqOn hv hw hS.isOpen_compl hwv hσw hσvw hleg hlegS
  rw [add_sub_cancel] at hdomw hvalw hderw
  have hvalv : flowOf v (T₀ - σ) q = p := by
    rw [(flowOf_add hv hσdom hleg).2, add_sub_cancel, hp]
  refine ⟨hdomw, hvalw.trans hvalv, fun g hg hgv ↦
    returnDerivative_eq_smul_of_mfderiv_flowOf_eq hv hP hp hg hgv hw hdomw (hvalw.trans hvalv)
      hwp hD fun ξ ↦ ?_⟩
  -- The monodromy of `w` is that of `v` composed with `D`.
  have h₁ := mfderiv_flowOf_add_apply hv hσdom rfl hleg (D ξ)
  rw [add_sub_cancel] at h₁
  rw [hderw ξ, hDσ ξ]
  exact h₁

end Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {u : E}

/-- **The flow-box dilation field.** Let `u ≠ 0`, let `0 ≤ s₀ < s₁`, and let `Ω` be an open set
containing the segment `[s₀, s₁] • u` of the axis `ℝ • u`. There are a functional `ℓ` with
`ℓ u = 1` and a smooth compactly supported field `W`, supported in `Ω` and vanishing on the axis,
such that for every `a` the flow of `u + a • W` runs along the axis, carrying `0` to `t • u` at
time `t`, and for `t ≥ s₁` its time-`t` map has derivative
`w ↦ w + (exp a - 1) • (w - ℓ w • u)` at `0`: it dilates the directions of `ker ℓ` by `exp a`.

`W` is a transverse dilation field of `TauCeti.Geometry.Manifold.Flow.TransverseDilation`,
supported in the slab `s₀ < ℓ z < s₁`, cut off to `Ω` by a smooth function equal to `1` near the
segment. -/
theorem exists_contDiff_flowOf_const_add_smul_axis (hu : u ≠ 0) {s₀ s₁ : ℝ} (hs₀ : 0 ≤ s₀)
    (hs₀₁ : s₀ < s₁) {Ω : Set E} (hΩ : IsOpen Ω) (hΩu : ∀ s ∈ Icc s₀ s₁, s • u ∈ Ω) :
    ∃ (ℓ : StrongDual ℝ E) (W : E → E), ℓ u = 1 ∧ ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
      tsupport W ⊆ Ω ∧ (∀ s : ℝ, W (s • u) = 0) ∧ ∀ a t : ℝ,
        (t, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) (fun z ↦ u + a • W z) ∧
        flowOf (I := 𝓘(ℝ, E)) (fun z ↦ u + a • W z) t 0 = t • u ∧
        (s₁ ≤ t → HasFDerivAt (flowOf (I := 𝓘(ℝ, E)) (fun z ↦ u + a • W z) t)
          (1 + (Real.exp a - 1) • (1 - ℓ.smulRight u)) 0) := by
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hu
  obtain ⟨Ψ, hΨ, hΨ₀, hΨ₁, -, Z, hZ, hZout, hZaxis, hZa⟩ :=
    exists_contDiff_hasFDerivAt_flowOf_add_smul (E := E) hℓ hs₀₁
  -- The cut-off `χ` is `1` near the segment `[s₀, s₁] • u` carrying the dilation, and supported
  -- in `Ω`.
  obtain ⟨χ, hχ, -, hχ1, hχc, hχΩ⟩ :=
    (isCompact_Icc.image (continuous_id.smul continuous_const)).exists_contDiff_cutoff hΩ <| by
      rintro _ ⟨s, hs, rfl⟩
      exact hΩu s hs
  set W : E → E := fun z ↦ χ z • Z z
  refine ⟨ℓ, W, hℓ, hχ.smul hZ, hχc.smul_right, (tsupport_smul_subset_left χ Z).trans hχΩ,
    fun s ↦ by simp [W, hZaxis], fun a t ↦ ?_⟩
  have haΨ : ContDiff ℝ 2 fun s ↦ a * Ψ s := contDiff_const.mul (hΨ.of_le (by simp))
  have hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun z : E ↦ (⟨z, u + a • W z⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.2
      (contDiff_const.add (((hχ.smul hZ).of_le (by simp)).const_smul a))
  -- The field `u + a • W` is the dilation field of `s ↦ a * Ψ s` where `χ = 1` nearby and
  -- outside the closed slab, an open set containing the whole axis.
  set U : Set E := interior (χ ⁻¹' {1}) ∪ ℓ ⁻¹' (Icc s₀ s₁)ᶜ
  have hU : IsOpen U :=
    isOpen_interior.union (isClosed_Icc.preimage ℓ.continuous).isOpen_compl
  have hwU : EqOn (fun z ↦ u + a • W z) (transverseDilationField u ℓ fun s ↦ a * Ψ s) U := by
    intro z hz
    rw [← congrFun (hZa a).1 z]
    rcases hz with hz | hz
    · simp [W, show χ z = 1 from interior_subset hz]
    · simp [W, hZout z fun h ↦ hz (Ioo_subset_Icc_self h)]
  have haxis : ∀ τ ∈ uIcc 0 t, (0 + τ) • u ∈ U := fun τ _ ↦ by
    rw [zero_add]
    by_cases h : τ ∈ Icc s₀ s₁
    · exact Or.inl (hχ1 ⟨τ, h, rfl⟩)
    · exact Or.inr (by simpa [hℓ] using h)
  have hflow := flowOf_smul_of_eqOn_transverseDilationField hℓ haΨ hw hU hwU haxis
  rw [zero_add, zero_smul] at hflow
  refine ⟨hflow.1, hflow.2, fun ht ↦ ?_⟩
  have hderiv := hasFDerivAt_flowOf_of_eqOn_transverseDilationField hℓ haΨ hw hU hwU haxis
  rwa [zero_add, zero_smul, hΨ₁ t ht, hΨ₀ 0 hs₀, mul_one, mul_zero, sub_zero] at hderiv

end TauCeti
