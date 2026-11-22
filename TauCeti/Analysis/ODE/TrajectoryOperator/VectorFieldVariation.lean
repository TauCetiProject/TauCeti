/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.ODE.EnergyEstimate.Cokernel
public import TauCeti.Analysis.ODE.TrajectoryOperator.Kernel
import TauCeti.Analysis.Calculus.BumpFunction.Path
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.ODE.Caratheodory
import TauCeti.LinearAlgebra.Submodule.Quotient
import TauCeti.MeasureTheory.Function.L2Space.Basic

/-!
# Vertical variations of a lifted vector field make the linearized equation onto

Let `π : E → F` be a surjective linear map of finite-dimensional real inner product spaces, and let
`W` be a vector field on `E` lifting a vector field `b` on `F`, that is `π ∘ W = b ∘ π`. Along a
trajectory `γ' = W(γ)` the linearized equation `ξ' = DW(γ) ξ` is block triangular: since
`π ∘ DW(x) = Db(π x) ∘ π`, the fibre directions `ker π` are invariant, and the quotient equation
is the linearization `η' = Db(π γ) η` along the base trajectory `π ∘ γ`. Varying `W` only by
**vertical** fields `Y`, with values in `ker π`, keeps the lifted structure and the base field.

In the convention `D_A u = u' + A u` of `TauCeti.WeakDerivStep.trajectoryOperator`, the coefficients
are `A(s) = -DW(γ s)` on `E` and `B(s) = -Db(π (γ s))` on `F`, and the lifting property reads
`π ∘ A(s) = B(s) ∘ π`. The universal linearization in the trajectory and the vertical field is
`(ξ, Y) ↦ D_A ξ - Y(γ)`. The **vertical variations** localized in `U`
(`TauCeti.vectorFieldVariations γ K U`, with `K = ker π`) are the classes in `L²(ℝ, E)` of the paths
`s ↦ Y (γ s)` for smooth compactly supported fields `Y` with values in `K` and support in `U`.

This file proves that if the base operator `D_B` is onto, the operator `D_A` has closed range of
finite codimension, and `γ` passes through a point `γ s₀` only once, then the range of `D_A` and
the vertical variations localized near `γ s₀` together span `L²(ℝ, E)`
(`TauCeti.range_trajectoryOperator_sup_span_vectorFieldVariations_eq_top`). In other words, the
universal linearization of a fixed-base lift is onto as soon as the linearization of the base is.
The form `TauCeti.range_trajectoryOperator_sup_span_vectorFieldVariations_eq_top_of_comp_eq_comp`
states this for the derivatives of a lift `π ∘ W = b ∘ π`.

The proof goes through the cokernel. A path `v` orthogonal to the range of `D_A` is almost
everywhere a solution `w` of the adjoint equation `w' = A† w`
(`TauCeti.WeakDerivStep.exists_hasDerivAt_adjoint_of_mem_orthogonal_range_trajectoryOperator`).
Since `A` preserves `ker π`, its adjoint preserves `(ker π)ᗮ`. If `v` is also orthogonal to the
vertical variations near `γ s₀`, a bump field with values in `ker π` shows that `w s₀ ∈ (ker π)ᗮ`;
then `w s ∈ (ker π)ᗮ` for all `s`, because a linear equation preserves the invariant subspaces of
its coefficients (`Continuous.mem_of_hasDerivAt_clm_apply`). Finally `(ker π)ᗮ` is the range of
`π†`, so `w = π† u` with `u` a square-integrable solution of the base adjoint equation
`u' = B† u`, which vanishes because `D_B` is onto
(`TauCeti.WeakDerivStep.squareIntegrableSolutions_neg_adjoint_eq_bot_of_surjective`,
`TauCeti.eq_zero_of_hasDerivAt_adjoint_of_mem_orthogonal_ker`).

This adapts the proof of `TauCeti.range_trajectoryOperator_sup_span_metricVariations_eq_top` in
`TauCeti.Analysis.Calculus.Morse.MorseSmale.MetricVariation`, with vertical vector-field variations
in place of metric variations. The two share the localization by a bump function along a
once-visited point (`TauCeti.exists_contDiff_tsupport_subset_integral_comp_mul_pos`).

## Main definitions

* `TauCeti.vectorFieldVariations γ K U`: the variations along `γ` by vector fields with values in
  `K` localized in `U`.

## Main results

* `TauCeti.eq_zero_of_hasDerivAt_adjoint_of_mem_orthogonal_ker`: for a coefficient lifting one
  whose trajectory operator is onto, a square-integrable solution of the adjoint equation that is
  orthogonal to `ker π` at one time vanishes.
* `TauCeti.orthogonal_range_trajectoryOperator_sup_span_vectorFieldVariations_eq_bot`: a path
  orthogonal to the range of `D_A` and to the vertical variations near a once-visited point
  vanishes.
* `TauCeti.range_trajectoryOperator_sup_span_vectorFieldVariations_eq_top`: the range of `D_A`
  and the vertical variations span `L²(ℝ, E)`; finitely many variations suffice
  (`TauCeti.exists_finset_subset_vectorFieldVariations_range_trajectoryOperator_sup_span_eq_top`).

## References

* M. Schwarz, *Morse Homology*, Progress in Mathematics **111**, Birkhäuser, 1993, Chapter 2
  (transversality of the universal section through the cokernel of the linearized operator).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., §3.2 and
  §6.7 (surjectivity of universal linearizations by unique continuation for the formal adjoint).
-/

public section

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ContDiff ENNReal RealInnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {γ : ℝ → E}

/-! ### Vertical variations -/

variable (γ) in
/-- The **variations along `γ` by vector fields with values in `K` localized in `U`**: the classes
in `L²(ℝ, E)` of the paths `s ↦ Y (γ s)`, for smooth compactly supported vector fields `Y` with
values in `K` and support in `U`. Varying the vector field `W` of `γ' = W(γ)` in the direction `Y`
moves the equation at `γ` by `Y (γ s)`. For `K = ker π`, these are the vertical variations of a
lift `π ∘ W = b ∘ π`, which leave the base field `b` unchanged. -/
def vectorFieldVariations (K : Submodule ℝ E) (U : Set E) :
    Set (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :=
  {g | ∃ Y : E → E, ContDiff ℝ ∞ Y ∧ HasCompactSupport Y ∧ tsupport Y ⊆ U ∧ (∀ x, Y x ∈ K) ∧
    g =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ Y (γ s)}

/-- Membership in the variations along `γ` by vector fields with values in `K` localized in
`U`. -/
theorem mem_vectorFieldVariations {K : Submodule ℝ E} {U : Set E}
    {g : Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))} :
    g ∈ vectorFieldVariations γ K U ↔ ∃ Y : E → E, ContDiff ℝ ∞ Y ∧ HasCompactSupport Y ∧
      tsupport Y ⊆ U ∧ (∀ x, Y x ∈ K) ∧
      g =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ Y (γ s) :=
  Iff.rfl

/-- Variations by fields with values in a smaller subspace and localized in a smaller set are
variations for the larger subspace and set. -/
theorem vectorFieldVariations_mono {K K' : Submodule ℝ E} {U U' : Set E} (hK : K ≤ K')
    (hU : U ⊆ U') : vectorFieldVariations γ K U ⊆ vectorFieldVariations γ K' U' :=
  fun _ ⟨Y, hY, hc, hYU, hYK, hg⟩ ↦ ⟨Y, hY, hc, hYU.trans hU, fun x ↦ hK (hYK x), hg⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-! ### The adjoint equation of a lifted coefficient -/

/-- **Square-integrable adjoint solutions of a lifted coefficient.** Let `π : E → F` be onto and
let the coefficients `A` on `E` and `B` on `F` satisfy `π ∘ A(s) = B(s) ∘ π`, with `B` continuous
and its trajectory operator `D_B u = u' + B u` from `W^{1,2}(ℝ, F)` onto `L²(ℝ, F)`. A
square-integrable solution `w` of the adjoint equation `w' = A(s)† w` with `w s₀ ⊥ ker π` at one
time vanishes. -/
theorem eq_zero_of_hasDerivAt_adjoint_of_mem_orthogonal_ker {π : E →L[ℝ] F}
    (hπ : Function.Surjective π) {A : ℝ → E →L[ℝ] E} {B : ℝ → F →L[ℝ] F} (hA : Continuous A)
    (hB : Continuous B) (hAB : ∀ s, π ∘L A s = B s ∘L π)
    {BL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] B)
    (hsurj : Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) BL))
    {w : ℝ → E} (hw : ∀ s, HasDerivAt w (ContinuousLinearMap.adjoint (A s) (w s)) s)
    (hw2 : MemLp w 2) {s₀ : ℝ} (hs₀ : w s₀ ∈ π.kerᗮ) : w = 0 := by
  have hπA (s : ℝ) (x : E) : π (A s x) = B s (π x) := by
    simpa using congrArg (fun T : E →L[ℝ] F ↦ T x) (hAB s)
  have hAπ (s : ℝ) (y : F) : ContinuousLinearMap.adjoint (A s) (ContinuousLinearMap.adjoint π y) =
      ContinuousLinearMap.adjoint π (ContinuousLinearMap.adjoint (B s) y) := by
    simpa [ContinuousLinearMap.adjoint_comp] using
      congrArg (fun T : E →L[ℝ] F ↦ ContinuousLinearMap.adjoint T y) (hAB s)
  -- The adjoint of `A(s)` preserves `(ker π)ᗮ`, so `w` stays in `(ker π)ᗮ`.
  have hinv (s : ℝ) (x : E) (hx : x ∈ π.kerᗮ) : ContinuousLinearMap.adjoint (A s) x ∈ π.kerᗮ :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1
      (ContinuousLinearMap.orthogonal_mem_invtSubmodule (T := ContinuousLinearMap.adjoint (A s))
        ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun y hy ↦ by
          have hy' : π y = 0 := LinearMap.mem_ker.1 hy
          simp [hπA, hy'])) x hx
  have hmem (s : ℝ) : w s ∈ π.kerᗮ := hA.clm_adjoint.mem_of_hasDerivAt_clm_apply
    (Submodule.ClosedComplemented.of_finiteDimensional_quotient
      (Submodule.isClosed_of_finiteDimensional _)) hinv hw hs₀ s
  -- Since `π` is onto, `π†` is injective with range `(ker π)ᗮ`; let `L` be a left inverse.
  have hinj : Function.Injective (ContinuousLinearMap.adjoint π) := by
    have h := π.orthogonal_range
    rw [LinearMap.range_eq_top.2 hπ, Submodule.top_orthogonal_eq_bot] at h
    exact LinearMap.ker_eq_bot.1 h.symm
  obtain ⟨L₀, hL₀⟩ := LinearMap.exists_leftInverse_of_injective
    (ContinuousLinearMap.adjoint π : F →ₗ[ℝ] E) (LinearMap.ker_eq_bot.2 hinj)
  set L := LinearMap.toContinuousLinearMap L₀
  have hL (y : F) : L (ContinuousLinearMap.adjoint π y) = y := by
    simpa [L] using LinearMap.congr_fun hL₀ y
  have hrange (s : ℝ) : ContinuousLinearMap.adjoint π (L (w s)) = w s := by
    have h := hmem s
    rw [π.orthogonal_ker,
      (Submodule.isClosed_of_finiteDimensional _).submodule_topologicalClosure_eq] at h
    obtain ⟨y, hy⟩ := h
    simp only [ContinuousLinearMap.coe_coe] at hy
    rw [← hy, hL]
  -- `u = L w` is a square-integrable solution of the base adjoint equation `u' = B† u`.
  set u : ℝ → F := fun s ↦ L (w s)
  have hu (s : ℝ) : HasDerivAt u (ContinuousLinearMap.adjoint (B s) (u s)) s :=
    -- `L (A(s)† w) = L (A(s)† π† u) = L (π† B(s)† u) = B(s)† u`
    (L.hasFDerivAt.comp_hasDerivAt s (hw s)).congr_deriv (by rw [← hrange s, hAπ, hL])
  have hu0 : u 0 = 0 := by
    have : u 0 ∈ squareIntegrableSolutions fun s ↦ -ContinuousLinearMap.adjoint (B s) :=
      mem_squareIntegrableSolutions.2 ⟨u, rfl, fun s ↦ by simpa using hu s, L.comp_memLp' hw2⟩
    rwa [WeakDerivStep.squareIntegrableSolutions_neg_adjoint_eq_bot_of_surjective hB hBL hsurj,
      Submodule.mem_bot] at this
  have hu_eq : u = fun _ ↦ 0 := hB.clm_adjoint.eq_of_hasDerivAt_clm_apply hu
    (fun s ↦ by simpa using hasDerivAt_const s (0 : F)) hu0
  funext s
  rw [← hrange s]
  simpa using congrArg (ContinuousLinearMap.adjoint π) (congrFun hu_eq s)

/-- Near a point `γ s₀` that `γ` passes through only once, a continuous path `w` with `w s₀` not
orthogonal to `K` pairs positively with the path of a vector field with values in `K` localized in
a given neighbourhood of `γ s₀`. The field is `ψ • e` for a bump function `ψ` at `γ s₀`
(`TauCeti.exists_contDiff_tsupport_subset_integral_comp_mul_pos`) and the projection `e` of `w s₀`
to `K`. -/
private theorem exists_integral_inner_vectorFieldVariation_pos (hγ : Continuous γ) {s₀ : ℝ}
    (hvisit : comap γ (𝓝 (γ s₀)) ≤ 𝓝 s₀) {U : Set E} (hU : U ∈ 𝓝 (γ s₀)) {K : Submodule ℝ E}
    {w : ℝ → E} (hwc : Continuous w) (hw0 : w s₀ ∉ Kᗮ) :
    ∃ Y : E → E, ContDiff ℝ ∞ Y ∧ HasCompactSupport Y ∧ tsupport Y ⊆ U ∧ (∀ x, Y x ∈ K) ∧
      HasCompactSupport (fun s ↦ Y (γ s)) ∧ 0 < ∫ s, ⟪Y (γ s), w s⟫ := by
  set e := K.starProjection (w s₀)
  have he : 0 < ⟪e, w s₀⟫ := by
    have h0 : ⟪e, w s₀ - e⟫ = 0 := Submodule.inner_right_of_mem_orthogonal
      (K.starProjection_apply_mem _) (K.sub_starProjection_mem_orthogonal _)
    rw [inner_sub_right, sub_eq_zero] at h0
    rw [h0, real_inner_self_eq_norm_sq]
    exact pow_pos
      (norm_pos_iff.2 fun h ↦ hw0 ((Submodule.starProjection_apply_eq_zero_iff _).1 h)) 2
  obtain ⟨ψ, hψ, hψc, hψU, hψγ, hpos⟩ := exists_contDiff_tsupport_subset_integral_comp_mul_pos hγ
    hvisit hU (continuous_const.inner hwc) he
  refine ⟨fun x ↦ ψ x • e, hψ.smul contDiff_const, hψc.smul_right,
    (tsupport_smul_subset_left _ _).trans hψU, fun x ↦ K.smul_mem _ (K.starProjection_apply_mem _),
    hψγ.smul_right, ?_⟩
  simpa only [real_inner_smul_left] using hpos

/-! ### Surjectivity of the universal linearization -/

/-- **Only zero is orthogonal to the range and to the vertical variations.** Let `π : E → F` be
onto, and let the continuous coefficients `A` on `E` and `B` on `F` satisfy
`π ∘ A(s) = B(s) ∘ π`, with the trajectory operator `D_B u = u' + B u` from `W^{1,2}(ℝ, F)` onto
`L²(ℝ, F)`. Let `γ` be a continuous path passing through `γ s₀` only once, in the sense that
`γ s → γ s₀` forces `s → s₀`, and let `U` be a neighbourhood of `γ s₀`. A path `v ∈ L²(ℝ, E)`
orthogonal to the range of `D_A u = u' + A u` and to every variation along `γ` by a vector field
with values in `ker π` localized in `U` vanishes. No closedness of the range is needed. -/
theorem orthogonal_range_trajectoryOperator_sup_span_vectorFieldVariations_eq_bot
    {π : E →L[ℝ] F} (hπ : Function.Surjective π) {A : ℝ → E →L[ℝ] E} {B : ℝ → F →L[ℝ] F}
    (hA : Continuous A) (hB : Continuous B) (hAB : ∀ s, π ∘L A s = B s ∘L π)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    {BL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] B)
    (hsurj : Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) BL))
    (hγ : Continuous γ) {s₀ : ℝ} (hvisit : comap γ (𝓝 (γ s₀)) ≤ 𝓝 s₀) {U : Set E}
    (hU : U ∈ 𝓝 (γ s₀)) :
    ((WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔
      Submodule.span ℝ (vectorFieldVariations γ π.ker U))ᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [← Submodule.inf_orthogonal] at hv
  have hvar (g) (hg : g ∈ vectorFieldVariations γ π.ker U) : ⟪g, v⟫ = 0 :=
    (Submodule.mem_orthogonal _ _).1 hv.2 g (Submodule.subset_span hg)
  have hvol : volume.restrict ((⊤ : Opens ℝ) : Set ℝ) = volume := by simp
  obtain ⟨w, hw, hvw⟩ :=
    WeakDerivStep.exists_hasDerivAt_adjoint_of_mem_orthogonal_range_trajectoryOperator hA hAL hv.1
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun s ↦ (hw s).continuousAt
  -- The vertical variations force `w s₀ ⊥ ker π`.
  have hs₀ : w s₀ ∈ π.kerᗮ := by
    by_contra h
    obtain ⟨Y, hY, hYc, hYU, hYK, hpath, hpos⟩ :=
      exists_integral_inner_vectorFieldVariation_pos hγ hvisit hU hwc h
    have hmem : MemLp (fun s ↦ Y (γ s)) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by
      rw [hvol]
      exact (hY.continuous.comp hγ).memLp_of_hasCompactSupport hpath
    have hint : ∫ s, ⟪Y (γ s), w s⟫ = ⟪hmem.toLp _, v⟫ := by
      rw [L2.toLp_inner_of_ae_eq hmem hvw, hvol]
    exact hpos.ne' (hint.trans (hvar _ ⟨Y, hY, hYc, hYU, hYK, hmem.coeFn_toLp⟩))
  have hw2 : MemLp w 2 := by
    simpa [hvol] using (Lp.memLp v).ae_eq hvw
  have hw0 := eq_zero_of_hasDerivAt_adjoint_of_mem_orthogonal_ker hπ hA hB hAB hBL hsurj hw hw2 hs₀
  exact (Submodule.mem_bot ℝ).2
    (Lp.eq_zero_iff_ae_eq_zero.2 (hvw.trans (.of_forall fun s ↦ by simp [hw0])))

/-- **Vertical variations make the linearization of a lift onto.** Let `π : E → F` be onto, and
let the continuous coefficients `A` on `E` and `B` on `F` satisfy `π ∘ A(s) = B(s) ∘ π`. Suppose
the trajectory operator `D_A u = u' + A u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` has closed range of
finite codimension, and `D_B u = u' + B u` maps `W^{1,2}(ℝ, F)` onto `L²(ℝ, F)`. If `γ` is a
continuous path passing through `γ s₀` only once and `U` is a neighbourhood of `γ s₀`, then the
range of `D_A` and the variations along `γ` by vector fields with values in `ker π` localized in
`U` together span `L²(ℝ, E)`. -/
theorem range_trajectoryOperator_sup_span_vectorFieldVariations_eq_top {π : E →L[ℝ] F}
    (hπ : Function.Surjective π) {A : ℝ → E →L[ℝ] E} {B : ℝ → F →L[ℝ] F} (hA : Continuous A)
    (hB : Continuous B) (hAB : ∀ s, π ∘L A s = B s ∘L π)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (hclosed : IsClosed ((WeakDerivStep.trajectoryOperator (p := 2) AL).range :
      Set (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (hcoker : (WeakDerivStep.trajectoryOperator (p := 2) AL).range.CoFG)
    {BL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] B)
    (hsurj : Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) BL))
    (hγ : Continuous γ) {s₀ : ℝ} (hvisit : comap γ (𝓝 (γ s₀)) ≤ 𝓝 s₀) {U : Set E}
    (hU : U ∈ 𝓝 (γ s₀)) :
    (WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔
      Submodule.span ℝ (vectorFieldVariations γ π.ker U) = ⊤ := by
  have := hcoker
  -- The sum contains the closed range, of finite codimension, so it is closed.
  have hK : IsClosed (((WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔
      Submodule.span ℝ (vectorFieldVariations γ π.ker U) : Submodule ℝ _) : Set
        (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :=
    Submodule.isClosed_mono_of_finiteDimensional_quotient hclosed le_sup_left
  have := hK.completeSpace_coe
  rw [← Submodule.orthogonal_eq_bot_iff]
  exact orthogonal_range_trajectoryOperator_sup_span_vectorFieldVariations_eq_bot hπ hA hB hAB hAL
    hBL hsurj hγ hvisit hU

/-- **Finitely many vertical variations make the linearization of a lift onto.** Under the
hypotheses of `TauCeti.range_trajectoryOperator_sup_span_vectorFieldVariations_eq_top`, finitely
many variations along `γ` by vector fields with values in `ker π` localized in `U` already span
`L²(ℝ, E)` together with the range of `D_A`, which has finite codimension. -/
theorem exists_finset_subset_vectorFieldVariations_range_trajectoryOperator_sup_span_eq_top
    {π : E →L[ℝ] F} (hπ : Function.Surjective π) {A : ℝ → E →L[ℝ] E} {B : ℝ → F →L[ℝ] F}
    (hA : Continuous A) (hB : Continuous B) (hAB : ∀ s, π ∘L A s = B s ∘L π)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (hclosed : IsClosed ((WeakDerivStep.trajectoryOperator (p := 2) AL).range :
      Set (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (hcoker : (WeakDerivStep.trajectoryOperator (p := 2) AL).range.CoFG)
    {BL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] B)
    (hsurj : Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) BL))
    (hγ : Continuous γ) {s₀ : ℝ} (hvisit : comap γ (𝓝 (γ s₀)) ≤ 𝓝 s₀) {U : Set E}
    (hU : U ∈ 𝓝 (γ s₀)) :
    ∃ t : Finset (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))),
      (t : Set _) ⊆ vectorFieldVariations γ π.ker U ∧
        (WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔ Submodule.span ℝ t = ⊤ := by
  have := hcoker
  exact Submodule.exists_finset_subset_sup_span_eq_top
    (range_trajectoryOperator_sup_span_vectorFieldVariations_eq_top hπ hA hB hAB hAL hclosed
      hcoker hBL hsurj hγ hvisit hU)

/-- **Vertical variations make the linearization of a lifted vector field onto.** Let `π : E → F`
be onto and let the `C¹` vector field `W` on `E` lift the `C¹` vector field `b` on `F`, that is
`π ∘ W = b ∘ π`. Along a continuous path `γ`, typically a trajectory `γ' = W(γ)`, take the
coefficients `A(s) = -DW(γ s)` and `B(s) = -Db(π (γ s))`, the linearizations of the equation and
of its base along `π ∘ γ`. If `D_A` has closed range of finite codimension, `D_B` is onto, and `γ`
passes through `γ s₀` only once, then the range of `D_A` and the variations of `W` by vertical
fields with values in `ker π` localized near `γ s₀` together span `L²(ℝ, E)`. -/
theorem range_trajectoryOperator_sup_span_vectorFieldVariations_eq_top_of_comp_eq_comp
    {π : E →L[ℝ] F} (hπ : Function.Surjective π) {W : E → E} {b : F → F} (hW : ContDiff ℝ 1 W)
    (hb : ContDiff ℝ 1 b) (hlift : π ∘ W = b ∘ π)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ -fderiv ℝ W (γ s))
    (hclosed : IsClosed ((WeakDerivStep.trajectoryOperator (p := 2) AL).range :
      Set (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (hcoker : (WeakDerivStep.trajectoryOperator (p := 2) AL).range.CoFG)
    {BL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ -fderiv ℝ b (π (γ s)))
    (hsurj : Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) BL))
    (hγ : Continuous γ) {s₀ : ℝ} (hvisit : comap γ (𝓝 (γ s₀)) ≤ 𝓝 s₀) {U : Set E}
    (hU : U ∈ 𝓝 (γ s₀)) :
    (WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔
      Submodule.span ℝ (vectorFieldVariations γ π.ker U) = ⊤ := by
  -- Differentiating `π ∘ W = b ∘ π` gives `π ∘ DW(x) = Db(π x) ∘ π`.
  have hAB (s : ℝ) : π ∘L (-fderiv ℝ W (γ s)) = (-fderiv ℝ b (π (γ s))) ∘L π := by
    have h₁ := (π.hasFDerivAt.comp (γ s) (hW.differentiable one_ne_zero (γ s)).hasFDerivAt).fderiv
    have h₂ := ((hb.differentiable one_ne_zero (π (γ s))).hasFDerivAt.comp (γ s)
      π.hasFDerivAt).fderiv
    rw [hlift] at h₁
    rw [ContinuousLinearMap.comp_neg, ContinuousLinearMap.neg_comp, ← h₁.symm.trans h₂]
  exact range_trajectoryOperator_sup_span_vectorFieldVariations_eq_top hπ
    ((hW.continuous_fderiv one_ne_zero).comp hγ).neg
    ((hb.continuous_fderiv one_ne_zero).comp (π.continuous.comp hγ)).neg hAB hAL hclosed hcoker hBL
    hsurj hγ hvisit hU

end TauCeti
