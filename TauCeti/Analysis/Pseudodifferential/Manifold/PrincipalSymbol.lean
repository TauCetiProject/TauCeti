/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.Pseudodifferential.CoordinateChange.Chart
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# The principal symbol of a classical pseudodifferential operator on a manifold

Let `P` be a classical pseudodifferential operator of order `m` on a manifold `M` modelled on
`ℝⁿ` (`TauCeti.classicalPseudodifferentialOperators`): in every chart `e` and for all cutoffs `φ`,
`ψ` with compact supports in the chart target, its compression `u ↦ φ · (P ((ψ u) ∘ e)) ∘ e⁻¹` is
`Op(a)` for a classical symbol `a` of order `m`. This file shows that the principal symbols of these
local symbols are the readings in the charts of one function on the cotangent bundle, the
**principal symbol** of `P`,

`TauCeti.pseudodifferentialPrincipalSymbol P p ξ : ℂ →L[ℂ] ℂ` for `ξ ∈ T*ₚM`,

in the sense that for every chart `e`, every pair of cutoffs and every point `p` of the chart
source,

`σ(a)(e p, η) = φ(e p) ψ(e p) σ(P)(p, ⟪η, de_p ·⟫)`

(`TauCeti.coefficient_principal_eq_pseudodifferentialPrincipalSymbol`): the frequency `η` at `e p`
is the covector `⟪η, ·⟫` of `ℝⁿ`, which the differential `de_p` of the chart pulls back to `T*ₚM`.
This is the angular-frequency convention of `Op(a)`, in which `∂ⱼ` has symbol `i ξⱼ`. The principal
symbol is homogeneous of degree `m` in `ξ` and linear in `P`, and its kernel consists of the
operators of order `m - 1` (`TauCeti.pseudodifferentialPrincipalSymbol_eq_zero_iff`). For the
complexification of a differential operator `D` of order at most `m` on the real-valued functions,
it is `i ^ m σ_geom(D)(ξ)` at nonzero `ξ`, where `σ_geom(D)` is the geometric principal symbol of
`D` (`TauCeti.pseudodifferentialPrincipalSymbol_complexifyLinearMap`).

## The argument

The principal symbol at `p` is defined in the chart at `p`, with cutoffs equal to `1` near the
image of `p`. In another chart `e`, with arbitrary cutoffs `φ` and `ψ`, cut both off further by a
cutoff `χ` near `e p`, so that the cut-off compression `χ φ · (P ((χ ψ u) ∘ e)) ∘ e⁻¹` only sees the
part of `P` where the cutoffs of the chart at `p` equal `1`. Read in the chart `e` it is
`u ↦ χ · Op(a) (χ u)`, and read through the transition `κ` from `e` to the chart at `p` it is
`u ↦ χ φ · Op(a₀) ((χ ψ u) ∘ κ⁻¹) ∘ κ`. By the change of coordinates theorem
(`TauCeti.ClassicalSymbol.exists_smul_quantizeSchwartzValue_comp_eq`) both are quantizations of
classical symbols, whose principal symbols are `χ² σ(a)` and `χ² φ ψ σ(a₀)(κ ·, (Dκ*)⁻¹ ·)`. A
symbol is determined by its quantization
(`TauCeti.Symbol.coefficient_eq_of_forall_quantizeSchwartzValue_eq`), so these agree, and `(Dκ*)⁻¹`
carries the frequency read in `e` to the one read in the chart at `p`.

## Main definitions and results

* `TauCeti.pseudodifferentialPrincipalSymbol`: the principal symbol of a classical
  pseudodifferential operator, a function on the cotangent bundle.
* `TauCeti.coefficient_principal_eq_pseudodifferentialPrincipalSymbol`: in every chart and for all
  cutoffs, the principal symbol of the local symbol is the principal symbol of `P` read in the
  chart, times the cutoffs.
* `TauCeti.pseudodifferentialPrincipalSymbol_smul_covector`: homogeneity of degree `m`.
* `TauCeti.pseudodifferentialPrincipalSymbol_add`, `TauCeti.pseudodifferentialPrincipalSymbol_smul`:
  linearity in the operator.
* `TauCeti.pseudodifferentialPrincipalSymbol_eq_zero_iff`: the principal symbol vanishes exactly
  on the operators of order `m - 1`; so two operators with the same principal symbol differ by an
  operator of order `m - 1`
  (`TauCeti.sub_mem_classicalPseudodifferentialOperators_of_pseudodifferentialPrincipalSymbol_eq`).
* `TauCeti.pseudodifferentialPrincipalSymbol_complexifyLinearMap`: for a differential operator,
  the principal symbol is `i ^ m` times its geometric principal symbol.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem 18.1.17
  and the definition of the principal symbol after Definition 18.1.20.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M] {m : ℝ}

/-! ### Two charts -/

section Transition

variable {e e₀ : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (he₀ : e₀ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)

include he he₀ in
/-- The inverse of the derivative at `e p` of the transition `κ = e₀ ∘ e⁻¹` is
`de_p ∘ (de₀_p)⁻¹`. -/
private theorem ring_inverse_fderiv_transition {p : M} (hp : p ∈ e.source)
    (hp₀ : p ∈ e₀.source) :
    Ring.inverse (fderiv ℝ (e.symm.trans e₀) (e p)) =
      ((mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) e p).comp
        (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) e₀.symm (e₀ p)) :
          CoordinateSpace n →L[ℝ] CoordinateSpace n) := by
  set D := fderiv ℝ (e.symm.trans e₀) (e p)
  set L : CoordinateSpace n →L[ℝ] CoordinateSpace n :=
    (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) e p).comp
      (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) e₀.symm (e₀ p))
  have he1 : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have he₀1 : e₀ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he₀
  have hw : e p ∈ (e.symm.trans e₀).source := by
    simp [e.map_source hp, e.left_inv hp, hp₀]
  have hκp : e.symm.trans e₀ (e p) = e₀ p := by simp [e.left_inv hp]
  -- `L` evaluates as a composite (`ContinuousLinearMap.comp_apply`); the tangent spaces in its
  -- middle are the model space only up to unfolding, so this is stated by `rfl`.
  have hL (w : CoordinateSpace n) : L w = mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n)
      e p (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) e₀.symm (e₀ p) w) := rfl
  -- `L ∘ D = id`: the chain rule `d(e⁻¹) = d(e₀⁻¹) ∘ Dκ` at `e p`, followed by `de_p`.
  have hchain := OpenPartialHomeomorph.mfderiv_symm_eq_mfderiv_symm_comp_fderiv_symm_trans
    (I := 𝓘(ℝ, CoordinateSpace n)) hw
    (by rw [hκp]; exact mdifferentiableAt_symm_of_mem_maximalAtlas he₀1 (e₀.map_source hp₀))
    ((contDiffAt_symm_trans_of_mem_maximalAtlas he he₀ hw).differentiableAt (by simp))
  rw [hκp] at hchain
  have hLD (v : CoordinateSpace n) : L (D v) = v := by
    have h := e.mfderiv_apply_mfderiv_symm_apply (I := 𝓘(ℝ, CoordinateSpace n))
      (J := 𝓘(ℝ, CoordinateSpace n)) (e.map_source hp)
      (by rw [e.left_inv hp]; exact mdifferentiableAt_of_mem_maximalAtlas he1 hp)
      (mdifferentiableAt_symm_of_mem_maximalAtlas he1 (e.map_source hp)) v
    rw [e.left_inv hp] at h
    rw [hL]
    exact (congrArg _ (DFunLike.congr_fun hchain v)).symm.trans h
  -- In finite dimension a left inverse is a right inverse.
  have hDL : (D : CoordinateSpace n →ₗ[ℝ] CoordinateSpace n) ∘ₗ L = LinearMap.id :=
    (LinearMap.comp_eq_id_comm ℝ (CoordinateSpace n)).1 (LinearMap.ext hLD)
  exact Ring.inverse_unit ⟨D, L, ContinuousLinearMap.ext (LinearMap.congr_fun hDL),
    ContinuousLinearMap.ext hLD⟩

end Transition

/-! ### Comparison of the symbols in two charts -/

section Comparison

variable [T2Space M] {e e₀ : OpenPartialHomeomorph M (CoordinateSpace n)}
  {he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {he₀ : e₀ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}

/-- The functions `(ψ w) ∘ e` and `(ψ₀ v) ∘ e₀` on `M` agree when `w = χ u` and `v = (χ ψ u) ∘ κ⁻¹`
for the transition `κ = e₀ ∘ e⁻¹`, provided `χ` is supported in the source of `κ`, at points that
`κ` sends to where `ψ₀ = 1`. -/
private theorem complexCutoffPullback_eq_complexCutoffPullback
    (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ₀ : 𝓓(⟨e₀.target, e₀.open_target⟩, ℝ))
    {U : Set (CoordinateSpace n)} (hψ₀ : ∀ z ∈ U, ψ₀ z = 1) {χ : CoordinateSpace n → ℝ}
    (hχ : tsupport χ ⊆ (e.symm.trans e₀).source ∩ (e.symm.trans e₀) ⁻¹' U)
    {u w v : 𝓢(CoordinateSpace n, ℂ)} (hw : ∀ y, w y = χ y • u y)
    (hv : ∀ y ∈ (e.symm.trans e₀).source, v (e.symm.trans e₀ y) = (χ y * ψ y) • u y)
    (hv0 : ∀ z ∉ (e.symm.trans e₀).target, v z = 0) :
    e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff w (w.smooth ⊤)) =
      e₀.complexCutoffPullback he₀ ψ₀ (ContMDiffMap.ofContDiff v (v.smooth ⊤)) := by
  ext q
  by_cases hq : q ∈ e.source
  · have hκq : e.symm.trans e₀ (e q) = e₀ q := by simp [e.left_inv hq]
    rw [e.complexCutoffPullback_apply_of_mem he _ _ hq, ContMDiffMap.coe_ofContDiff, hw]
    by_cases hχq : χ (e q) = 0
    · rw [hχq, zero_smul, smul_zero]
      by_cases hq₀ : q ∈ e₀.source
      · have hqκ : e q ∈ (e.symm.trans e₀).source := by
          simp [e.map_source hq, e.left_inv hq, hq₀]
        rw [e₀.complexCutoffPullback_apply_of_mem he₀ _ _ hq₀, ContMDiffMap.coe_ofContDiff,
          ← hκq, hv _ hqκ, hχq]
        simp
      · rw [e₀.complexCutoffPullback_apply_of_notMem he₀ _ _ hq₀]
    · have hmem := hχ (subset_tsupport _ hχq)
      have hq₀ : q ∈ e₀.source := by simpa [e.left_inv hq] using hmem.1.2
      rw [e₀.complexCutoffPullback_apply_of_mem he₀ _ _ hq₀, ContMDiffMap.coe_ofContDiff, ← hκq,
        hv _ hmem.1, hψ₀ _ hmem.2, one_smul, smul_smul, mul_comm]
  · rw [e.complexCutoffPullback_apply_of_notMem he _ _ hq]
    by_cases hq₀ : q ∈ e₀.source
    · rw [e₀.complexCutoffPullback_apply_of_mem he₀ _ _ hq₀, ContMDiffMap.coe_ofContDiff,
        hv0 _ fun h ↦ hq (by simpa [e₀.left_inv hq₀] using h.2), smul_zero]
    · rw [e₀.complexCutoffPullback_apply_of_notMem he₀ _ _ hq₀]

variable {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
  {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} {φ₀ ψ₀ : 𝓓(⟨e₀.target, e₀.open_target⟩, ℝ)}
  {a a₀ : ClassicalSymbol n ℂ ℂ m}

/-- **The cut-off compression in two charts.** With `χ` as in
`complexCutoffPullback_eq_complexCutoffPullback`, where now `φ₀ = ψ₀ = 1` on `U`, the compression
of `P` in `e` cut off by `χ` on both sides, read through `Op(a)` in `e`, agrees with its reading
through `Op(a₀)` in `e₀` and the transition `κ = e₀ ∘ e⁻¹`:
`χ · Op(a) (χ u) = χ φ · Op(a₀) ((χ ψ u) ∘ κ⁻¹) ∘ κ`. -/
private theorem smul_quantizeSchwartzValue_eq_smul_quantizeSchwartzValue_comp
    (ha : ∀ u x, quantizeSchwartzValue a.toSymbol.coefficient u x =
      e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    (ha₀ : ∀ u x, quantizeSchwartzValue a₀.toSymbol.coefficient u x =
      e₀.complexChartCompression he₀ φ₀ ψ₀ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    {U : Set (CoordinateSpace n)} (hU1 : ∀ z ∈ U, φ₀ z = 1 ∧ ψ₀ z = 1)
    {χ : CoordinateSpace n → ℝ}
    (hχ : tsupport χ ⊆ (e.symm.trans e₀).source ∩ (e.symm.trans e₀) ⁻¹' U)
    {u w v : 𝓢(CoordinateSpace n, ℂ)} (hw : ∀ y, w y = χ y • u y)
    (hv : ∀ y ∈ (e.symm.trans e₀).source, v (e.symm.trans e₀ y) = (χ y * ψ y) • u y)
    (hv0 : ∀ z ∉ (e.symm.trans e₀).target, v z = 0) (x : CoordinateSpace n) :
    χ x • quantizeSchwartzValue a.toSymbol.coefficient w x =
      (χ x * φ x) • quantizeSchwartzValue a₀.toSymbol.coefficient v (e.symm.trans e₀ x) := by
  rw [ha₀, ha, OpenPartialHomeomorph.complexChartCompression_apply,
    OpenPartialHomeomorph.complexChartCompression_apply]
  by_cases hx : χ x = 0
  · simp [hx]
  have hxU := hχ (subset_tsupport _ hx)
  have hx₀ : e₀.symm (e.symm.trans e₀ x) = e.symm x := e₀.left_inv (by simpa using hxU.1.2)
  rw [hx₀, (hU1 _ hxU.2).1, one_smul, complexCutoffPullback_eq_complexCutoffPullback (he := he)
    (he₀ := he₀) ψ ψ₀ (fun z hz ↦ (hU1 z hz).2) hχ hw hv hv0, mul_smul]

/-- **The principal symbols in two charts.** Let the compressions of `P` in a chart `e` by `φ`, `ψ`
and in a chart `e₀` by `φ₀`, `ψ₀` be `Op(a)` and `Op(a₀)`. At a point `p` of both chart sources
near whose image `φ₀ = ψ₀ = 1`, the principal symbols are related by the transition
`κ = e₀ ∘ e⁻¹`: `σ(a)(e p, η) = φ(e p) ψ(e p) σ(a₀)(e₀ p, (Dκ(e p)*)⁻¹ η)`. -/
private theorem coefficient_principal_eq_of_transition
    (ha : ∀ u x, quantizeSchwartzValue a.toSymbol.coefficient u x =
      e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    (ha₀ : ∀ u x, quantizeSchwartzValue a₀.toSymbol.coefficient u x =
      e₀.complexChartCompression he₀ φ₀ ψ₀ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    {p : M} (hp : p ∈ e.source) (hp₀ : p ∈ e₀.source)
    (h1 : ∀ᶠ z in 𝓝 (e₀ p), φ₀ z = 1 ∧ ψ₀ z = 1) (η : CoordinateSpace n) :
    a.principal.coefficient (e p, η) = (φ (e p) * ψ (e p)) • a₀.principal.coefficient
      (e₀ p, ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ (e.symm.trans e₀) (e p))) η) := by
  have hκ := contDiffOn_symm_trans_of_mem_maximalAtlas he he₀
  have hκ' : ContDiffOn ℝ ∞ (e.symm.trans e₀).symm (e.symm.trans e₀).target := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
    exact contDiffOn_symm_trans_of_mem_maximalAtlas he₀ he
  obtain ⟨U, hU1, hUo, hpU⟩ := eventually_nhds_iff.1 h1
  have hκp : e.symm.trans e₀ (e p) = e₀ p := by simp [e.left_inv hp]
  have hw : e p ∈ (e.symm.trans e₀).source := by simp [e.map_source hp, e.left_inv hp, hp₀]
  -- A cutoff `χ` equal to `1` at `e p`, supported where the transition `κ` is defined and lands
  -- where `φ₀ = ψ₀ = 1`.
  obtain ⟨χ, hχ, -, hχ1, hχc, hχs⟩ := IsCompact.exists_contDiff_cutoff isCompact_singleton
    ((e.symm.trans e₀).isOpen_inter_preimage hUo)
    (singleton_subset_iff.2 ⟨hw, by rw [mem_preimage, hκp]; exact hpU⟩)
  have hχp : χ (e p) = 1 := interior_subset (hχ1 rfl)
  have hχκ : tsupport χ ⊆ (e.symm.trans e₀).source := hχs.trans inter_subset_left
  -- In the chart `e`, the compression cut off by `χ` is `u ↦ χ · Op(a) (χ u)`, the quantization of
  -- a symbol `c` with principal symbol `χ² σ(a)` ...
  obtain ⟨c, hc, hcop⟩ := a.exists_smul_quantizeSchwartzValue_comp_eq
    (OpenPartialHomeomorph.refl _) contDiffOn_id contDiffOn_id hχ hχc (subset_univ _) hχ hχc
    (subset_univ _)
  -- ... and through the transition it is `u ↦ χ φ · Op(a₀) ((χ ψ u) ∘ κ⁻¹) ∘ κ`, the quantization
  -- of a symbol `b` with principal symbol `χ² φ ψ σ(a₀)(κ ·, (Dκ*)⁻¹ ·)`.
  obtain ⟨b, hb, hbop⟩ := a₀.exists_smul_quantizeSchwartzValue_comp_eq (e.symm.trans e₀) hκ hκ'
    (hχ.mul φ.contDiff) hχc.mul_right (tsupport_mul_subset_left.trans hχκ)
    (hχ.mul ψ.contDiff) hχc.mul_right (tsupport_mul_subset_left.trans hχκ)
  -- Both are the same operator, so `b = c`.
  have hbc : b = c := by
    refine ClassicalSymbol.ext (Symbol.ext (Symbol.coefficient_eq_of_forall_quantizeSchwartzValue_eq
      fun u _ ↦ funext fun x ↦ ?_))
    obtain ⟨v, hv, hv0⟩ := (e.symm.trans e₀).exists_schwartzMap_apply_eq_smul hκ'
      (hχ.mul ψ.contDiff) hχc.mul_right (tsupport_mul_subset_left.trans hχκ) u
    have hw (y : CoordinateSpace n) : SchwartzMap.smulLeftCLM ℂ χ u y = χ y • u y :=
      SchwartzMap.smulLeftCLM_apply_apply (hχc.hasTemperateGrowth hχ) u y
    rw [← hbop u v hv hv0 x, ← hcop u _ (fun y _ ↦ hw y) (fun z hz ↦ absurd (mem_univ z) hz) x,
      ← smul_quantizeSchwartzValue_eq_smul_quantizeSchwartzValue_comp ha ha₀ hU1 hχs hw hv hv0,
      OpenPartialHomeomorph.refl_apply, id_eq]
  have hid : Ring.inverse (ContinuousLinearMap.id ℝ (CoordinateSpace n)) =
      ContinuousLinearMap.id ℝ (CoordinateSpace n) :=
    Ring.inverse_one _
  have h := congrArg (fun s : ClassicalSymbol n ℂ ℂ m ↦ s.principal.coefficient (e p, η)) hbc
  simp only [hb, hc, hχp, hκp, one_mul] at h
  simpa [hid, ContinuousLinearMap.adjoint_id] using h.symm

end Comparison

/-! ### The principal symbol -/

section PrincipalSymbol

/-- The frequency `η` at `e p` and the covector `ξ = ⟪η, de_p ·⟫` at `p` determine each other:
`η = ((de_p)⁻¹)* ξ`. -/
private theorem innerSL_toDual_symm_comp_mfderiv {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M) {p : M} (hp : p ∈ e.source)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) p →L[ℝ] ℝ) :
    (innerSL ℝ ((InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
      (ξ.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) e.symm (e p))))).comp
        (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) e p) = ξ := by
  have he1 : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have h := e.mfderiv_symm_apply_mfderiv_apply hp (mdifferentiableAt_of_mem_maximalAtlas he1 hp)
    (mdifferentiableAt_symm_of_mem_maximalAtlas he1 (e.map_source hp)) v
  -- The tangent spaces at `p` and at `e⁻¹ (e p)` are both the model space but are not
  -- syntactically equal, so the composites are not rewritten: `exact` compares them by
  -- unfolding `ContinuousLinearMap.comp_apply` and `innerSL_apply_apply`.
  exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := CoordinateSpace n)).trans
    (congrArg ξ h)

/-- A cutoff in the target of the chart at `p` equal to `1` near the image of `p`. -/
private theorem exists_cutoff_chartAt (p : M) :
    ∃ θ : 𝓓(⟨(chartAt (CoordinateSpace n) p).target,
      (chartAt (CoordinateSpace n) p).open_target⟩, ℝ),
        ∀ᶠ z in 𝓝 (chartAt (CoordinateSpace n) p p), θ z = 1 := by
  obtain ⟨θ, -, hθ, -⟩ := TestFunction.exists_cutoff_tsupport_subset (n := ⊤)
    (Ω := ⟨(chartAt (CoordinateSpace n) p).target, (chartAt (CoordinateSpace n) p).open_target⟩)
    isCompact_singleton (chartAt (CoordinateSpace n) p).open_target
    (singleton_subset_iff.2 (mem_chart_target _ p)) fun _ h ↦ h
  exact ⟨θ, by simpa using hθ⟩

/-- The cutoff in the target of the chart at `p`, equal to `1` near the image of `p`, through which
the principal symbol at `p` is read. -/
private def chartCutoff (p : M) :
    𝓓(⟨(chartAt (CoordinateSpace n) p).target, (chartAt (CoordinateSpace n) p).open_target⟩, ℝ) :=
  Classical.choose (exists_cutoff_chartAt p)

private theorem chartCutoff_eventuallyEq_one (p : M) :
    ∀ᶠ z in 𝓝 (chartAt (CoordinateSpace n) p p), chartCutoff p z = 1 :=
  Classical.choose_spec (exists_cutoff_chartAt p)

variable [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- The frequency at `e p` read from a covector `ξ` at `p` in the chart `e` at `p`: the vector `η`
with `⟪η, de_p ·⟫ = ξ`, that is `η = ((de_p)⁻¹)* ξ`. -/
private def chartFrequency (p : M) :
    (TangentSpace 𝓘(ℝ, CoordinateSpace n) p →L[ℝ] ℝ) →ₗ[ℝ] CoordinateSpace n where
  toFun ξ := (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
    (ξ.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n)
      (chartAt (CoordinateSpace n) p).symm (chartAt (CoordinateSpace n) p p)))
  map_add' ξ ζ := by
    rw [← map_add]
    exact congrArg _ (ContinuousLinearMap.ext fun _ ↦ rfl)
  map_smul' c ξ := by
    rw [RingHom.id_apply, ← map_smul]
    exact congrArg _ (ContinuousLinearMap.ext fun _ ↦ rfl)

/-- The symbol of the compression of `P` in the chart at `p` by the cutoffs `chartCutoff p`, through
which the principal symbol at `p` is read. -/
private def chartSymbol (P : classicalPseudodifferentialOperators (n := n) (M := M) m) (p : M) :
    ClassicalSymbol n ℂ ℂ m :=
  Classical.choose ((mem_classicalPseudodifferentialOperators_iff.1 P.property).2
    (chartAt (CoordinateSpace n) p) (IsManifold.chart_mem_maximalAtlas p) (chartCutoff p)
      (chartCutoff p))

private theorem quantizeSchwartzValue_chartSymbol
    (P : classicalPseudodifferentialOperators (n := n) (M := M) m) (p : M)
    (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (chartSymbol P p).toSymbol.coefficient u x =
      (chartAt (CoordinateSpace n) p).complexChartCompression
        (IsManifold.chart_mem_maximalAtlas p) (chartCutoff p) (chartCutoff p) P
          (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x :=
  Classical.choose_spec ((mem_classicalPseudodifferentialOperators_iff.1 P.property).2
    (chartAt (CoordinateSpace n) p) (IsManifold.chart_mem_maximalAtlas p) (chartCutoff p)
      (chartCutoff p)) u x

/-- The **principal symbol** `σ(P)(p, ξ)` of a classical pseudodifferential operator `P` of order
`m` on `M`, at a covector `ξ ∈ T*ₚM`. It is the principal symbol of the local symbol of `P` in the
chart `e` at `p`, with cutoffs equal to `1` near `e p`, at `e p` and at the frequency `η` with
`⟪η, de_p ·⟫ = ξ`. It does not depend on these choices: in every chart and for all cutoffs, the
principal symbol of the local symbol is this one read in the chart, times the cutoffs
(`TauCeti.coefficient_principal_eq_pseudodifferentialPrincipalSymbol`). It vanishes at `ξ = 0` and
is homogeneous of degree `m` in `ξ` (`TauCeti.pseudodifferentialPrincipalSymbol_smul_covector`). -/
def pseudodifferentialPrincipalSymbol (P : classicalPseudodifferentialOperators (n := n) (M := M) m)
    (p : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) p →L[ℝ] ℝ) : ℂ →L[ℂ] ℂ :=
  (chartSymbol P p).principal.coefficient (chartAt (CoordinateSpace n) p p, chartFrequency p ξ)

/-- The principal symbol at `p` is read from any symbol of the compression of `P` in the chart at
`p` by the cutoffs `chartCutoff p`: such a symbol is the chosen one. -/
private theorem pseudodifferentialPrincipalSymbol_eq_of_chartAt
    (P : classicalPseudodifferentialOperators (n := n) (M := M) m) (p : M)
    {a : ClassicalSymbol n ℂ ℂ m} (ha : ∀ u x, quantizeSchwartzValue a.toSymbol.coefficient u x =
      (chartAt (CoordinateSpace n) p).complexChartCompression
        (IsManifold.chart_mem_maximalAtlas p) (chartCutoff p) (chartCutoff p) P
          (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) p →L[ℝ] ℝ) :
    pseudodifferentialPrincipalSymbol P p ξ =
      a.principal.coefficient (chartAt (CoordinateSpace n) p p, chartFrequency p ξ) := by
  have h : chartSymbol P p = a :=
    ClassicalSymbol.ext (Symbol.ext (Symbol.coefficient_eq_of_forall_quantizeSchwartzValue_eq
      fun u _ ↦ funext fun x ↦ (quantizeSchwartzValue_chartSymbol P p u x).trans (ha u x).symm))
  rw [pseudodifferentialPrincipalSymbol, h]

/-- **The principal symbol in a chart.** Let `P` be a classical pseudodifferential operator of
order `m`, `e` a chart of the maximal atlas and `φ`, `ψ` cutoffs with compact supports in its
target, and let the compression of `P` by `φ` and `ψ` be `Op(a)`. At a point `p` of the chart source
and a frequency `η`, the principal symbol of `a` is the principal symbol of `P` at the covector
`⟪η, de_p ·⟫`, times the cutoffs:

`σ(a)(e p, η) = φ(e p) ψ(e p) σ(P)(p, ⟪η, de_p ·⟫)`. -/
theorem coefficient_principal_eq_pseudodifferentialPrincipalSymbol
    (P : classicalPseudodifferentialOperators (n := n) (M := M) m)
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {a : ClassicalSymbol n ℂ ℂ m}
    (ha : ∀ u x, quantizeSchwartzValue a.toSymbol.coefficient u x =
      e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    {p : M} (hp : p ∈ e.source) (η : CoordinateSpace n) :
    a.principal.coefficient (e p, η) = (φ (e p) * ψ (e p)) •
      pseudodifferentialPrincipalSymbol P p
        ((innerSL ℝ η).comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) e p)) := by
  have hspec := quantizeSchwartzValue_chartSymbol P p
  rw [coefficient_principal_eq_of_transition ha hspec hp (mem_chart_source _ p)
      ((chartCutoff_eventuallyEq_one p).mono fun _ hz ↦ ⟨hz, hz⟩) η,
    ring_inverse_fderiv_transition he (IsManifold.chart_mem_maximalAtlas p) hp
      (mem_chart_source _ p), pseudodifferentialPrincipalSymbol_eq_of_chartAt P p hspec]
  congr 3
  exact (InnerProductSpace.toDual_symm_innerSL_comp η _).symm

/-- The principal symbol vanishes at the zero covector. -/
@[simp]
theorem pseudodifferentialPrincipalSymbol_zero_covector
    (P : classicalPseudodifferentialOperators (n := n) (M := M) m) (p : M) :
    pseudodifferentialPrincipalSymbol P p 0 = 0 := by
  rw [pseudodifferentialPrincipalSymbol, map_zero, HomogeneousSymbol.zero_covector]

/-- **Homogeneity.** The principal symbol of an operator of order `m` is positively homogeneous of
degree `m` in the covector. -/
theorem pseudodifferentialPrincipalSymbol_smul_covector
    (P : classicalPseudodifferentialOperators (n := n) (M := M) m) (p : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) p →L[ℝ] ℝ) {t : ℝ} (ht : 0 < t) :
    pseudodifferentialPrincipalSymbol P p (t • ξ) =
      t ^ m • pseudodifferentialPrincipalSymbol P p ξ := by
  rw [pseudodifferentialPrincipalSymbol, pseudodifferentialPrincipalSymbol, map_smul]
  exact HomogeneousSymbol.homogeneous _ _ _ t ht

/-- The principal symbol is additive in the operator. -/
@[simp]
theorem pseudodifferentialPrincipalSymbol_add
    (P Q : classicalPseudodifferentialOperators (n := n) (M := M) m) (p : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) p →L[ℝ] ℝ) :
    pseudodifferentialPrincipalSymbol (P + Q) p ξ =
      pseudodifferentialPrincipalSymbol P p ξ + pseudodifferentialPrincipalSymbol Q p ξ := by
  rw [pseudodifferentialPrincipalSymbol_eq_of_chartAt (P + Q) p
      (a := chartSymbol P p + chartSymbol Q p) (fun u x ↦ by
        rw [ClassicalSymbol.quantizeSchwartzValue_toSymbol_add, quantizeSchwartzValue_chartSymbol,
          quantizeSchwartzValue_chartSymbol, Submodule.coe_add, map_add, LinearMap.add_apply,
          ContMDiffMap.coe_add, Pi.add_apply]),
    ClassicalSymbol.principal_add, HomogeneousSymbol.coefficient_add, Pi.add_apply,
    pseudodifferentialPrincipalSymbol, pseudodifferentialPrincipalSymbol]

/-- The principal symbol is linear over `ℂ` in the operator. -/
@[simp]
theorem pseudodifferentialPrincipalSymbol_smul
    (c : ℂ) (P : classicalPseudodifferentialOperators (n := n) (M := M) m) (p : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) p →L[ℝ] ℝ) :
    pseudodifferentialPrincipalSymbol (c • P) p ξ =
      c • pseudodifferentialPrincipalSymbol P p ξ := by
  rw [pseudodifferentialPrincipalSymbol_eq_of_chartAt (c • P) p (a := c • chartSymbol P p)
      (fun u x ↦ by
        rw [ClassicalSymbol.quantizeSchwartzValue_toSymbol_smul, quantizeSchwartzValue_chartSymbol,
          Submodule.coe_smul, map_smul, LinearMap.smul_apply, ContMDiffMap.complex_smul_apply,
          smul_eq_mul]),
    ClassicalSymbol.principal_smul, HomogeneousSymbol.coefficient_smul, Pi.smul_apply,
    pseudodifferentialPrincipalSymbol]

/-- A classical symbol whose quantization vanishes at the position `y` vanishes at `y`, and so
does its principal symbol. -/
private theorem coefficient_principal_eq_zero_of_quantizeSchwartzValue_eq_zero
    {a : ClassicalSymbol n ℂ ℂ m} {y : CoordinateSpace n}
    (h : ∀ u : 𝓢(CoordinateSpace n, ℂ), quantizeSchwartzValue a.toSymbol.coefficient u y = 0)
    (η : CoordinateSpace n) : a.principal.coefficient (y, η) = 0 := by
  rcases eq_or_ne η 0 with rfl | hη
  · simp
  obtain ⟨C, hC⟩ := a.toSymbol.exists_norm_coefficient_le {y} isCompact_singleton
  have h0 (ζ : CoordinateSpace n) : a.toSymbol.coefficient (y, ζ) = 0 :=
    eq_zero_of_forall_quantizeSchwartzValue_eq_zero (a.toSymbol.continuous_coefficient_slice y)
      (hC y rfl) (fun u _ ↦ h u) ζ
  -- The principal symbol is the limit of `t ^ (-m) a(y, t η)`, which vanishes identically.
  refine tendsto_nhds_unique ((a.tendsto_rpow_neg_smul_coefficient_smul hη).comp
    (tendsto_id.prodMk tendsto_const_nhds)) ?_
  simp [Function.comp_def, h0]

/-- **The kernel of the principal symbol.** A classical pseudodifferential operator of order `m`
has vanishing principal symbol exactly when it is a classical pseudodifferential operator of order
`m - 1`. -/
theorem pseudodifferentialPrincipalSymbol_eq_zero_iff
    (P : classicalPseudodifferentialOperators (n := n) (M := M) m) :
    (∀ p ξ, pseudodifferentialPrincipalSymbol P p ξ = 0) ↔
      (P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
        C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) ∈
          classicalPseudodifferentialOperators (m - 1) := by
  have hP := mem_classicalPseudodifferentialOperators_iff.1 P.property
  refine ⟨fun h ↦ mem_classicalPseudodifferentialOperators_iff.2 ⟨hP.1, fun e he φ ψ ↦ ?_⟩,
    fun h p ξ ↦ ?_⟩
  · -- In every chart, the principal symbol of the local symbol vanishes: on the chart target by
    -- `coefficient_principal_eq_pseudodifferentialPrincipalSymbol`, and off it because there the
    -- output cutoff, and hence the symbol, vanishes.
    obtain ⟨a, ha⟩ := hP.2 e he φ ψ
    have h0 : a.principal = 0 := by
      refine HomogeneousSymbol.ext_of_ne_zero fun y η _ ↦ ?_
      rw [HomogeneousSymbol.coefficient_zero, Pi.zero_apply]
      by_cases hy : y ∈ e.target
      · rw [← e.right_inv hy, coefficient_principal_eq_pseudodifferentialPrincipalSymbol P he φ ψ ha
          (e.map_target hy), h]
        simp
      · refine coefficient_principal_eq_zero_of_quantizeSchwartzValue_eq_zero (fun u ↦ ?_) η
        rw [ha, OpenPartialHomeomorph.complexChartCompression_apply,
          image_eq_zero_of_notMem_tsupport fun h ↦ hy (φ.tsupport_subset h), zero_smul]
    obtain ⟨b, rfl⟩ := (ClassicalSymbol.principal_eq_zero_iff_exists_inclusion a).1 h0
    exact ⟨b, fun u x ↦ by
      rw [← ha, ClassicalSymbol.toSymbol_inclusion, Symbol.coefficient_inclusion]⟩
  · obtain ⟨b, hb⟩ := (mem_classicalPseudodifferentialOperators_iff.1 h).2
      (chartAt (CoordinateSpace n) p) (IsManifold.chart_mem_maximalAtlas p)
      (chartCutoff p) (chartCutoff p)
    rw [pseudodifferentialPrincipalSymbol_eq_of_chartAt P p
      (a := ClassicalSymbol.inclusion 1 (by simp) b) (fun u x ↦ by
        rw [ClassicalSymbol.toSymbol_inclusion, Symbol.coefficient_inclusion, hb]),
      (ClassicalSymbol.principal_eq_zero_iff_exists_inclusion _).2 ⟨b, rfl⟩,
      HomogeneousSymbol.coefficient_zero, Pi.zero_apply]

/-- Two classical pseudodifferential operators of order `m` with the same principal symbol differ
by an operator of order `m - 1`. -/
theorem sub_mem_classicalPseudodifferentialOperators_of_pseudodifferentialPrincipalSymbol_eq
    {P Q : classicalPseudodifferentialOperators (n := n) (M := M) m}
    (h : ∀ p ξ, pseudodifferentialPrincipalSymbol P p ξ = pseudodifferentialPrincipalSymbol Q p ξ) :
    (P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) - Q ∈
        classicalPseudodifferentialOperators (m - 1) := by
  -- Write `P - Q` as the operator `P + (-1) • Q` of the class, whose principal symbol vanishes.
  have hPQ : (P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) - Q =
        ((P + (-1 : ℂ) • Q : classicalPseudodifferentialOperators (n := n) (M := M) m) :
          C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
            C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) := by
    rw [Submodule.coe_add, Submodule.coe_smul, neg_one_smul, sub_eq_add_neg]
  rw [hPQ, ← pseudodifferentialPrincipalSymbol_eq_zero_iff]
  intro p ξ
  rw [pseudodifferentialPrincipalSymbol_add, pseudodifferentialPrincipalSymbol_smul, h]
  -- The scalar `-1` here carries the instance path of the action on the submodule, which
  -- `neg_one_smul` matches only up to instance unfolding, so it is applied rather than rewritten.
  exact (congrArg _ (neg_one_smul ℂ _)).trans (add_neg_cancel _)

/-- **The principal symbol of a differential operator.** The complexification of a differential
operator `D` of order at most `m` on the real-valued smooth functions on `M` has, at a nonzero
covector `ξ`, the principal symbol `i ^ m σ_geom(D)(ξ)`, where `σ_geom(D)` is the geometric
principal symbol of `D` (`TauCeti.smoothPrincipalSymbol`). This is the angular-frequency convention
in which `∂ⱼ` has symbol `i ξⱼ`. -/
theorem pseudodifferentialPrincipalSymbol_complexifyLinearMap {m : ℕ}
    {D : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ m)
    {p : M} {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) p →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    pseudodifferentialPrincipalSymbol ⟨ContMDiffMap.complexifyLinearMap D,
      complexifyLinearMap_mem_classicalPseudodifferentialOperators hD⟩ p ξ =
        (Complex.I ^ m * (smoothPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) (x := p)
          BoundarylessManifold.isInteriorPoint ⟨D, hD⟩ ξ : ℂ)) • ContinuousLinearMap.id ℂ ℂ := by
  set e₀ := chartAt (CoordinateSpace n) p
  have he₀ := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞) p
  have hξη : (innerSL ℝ (chartFrequency p ξ)).comp
      (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) e₀ p) = ξ :=
    innerSL_toDual_symm_comp_mfderiv he₀ (mem_chart_source _ p) ξ
  have hη : chartFrequency p ξ ≠ 0 := by
    intro hη
    rw [hη, map_zero] at hξη
    exact hξ (hξη.symm.trans (ContinuousLinearMap.ext fun _ ↦ rfl))
  have h1 := (chartCutoff_eventuallyEq_one (n := n) p).self_of_nhds
  rw [pseudodifferentialPrincipalSymbol_eq_of_chartAt ⟨ContMDiffMap.complexifyLinearMap D,
      complexifyLinearMap_mem_classicalPseudodifferentialOperators hD⟩ p
      (ClassicalSymbol.quantizeSchwartzValue_ofDifferentialOperator_eq_complexChartCompression hD
        he₀ (chartCutoff p) (chartCutoff p)),
    ClassicalSymbol.coefficient_principal_ofDifferentialOperator_chartCompression he₀ _ _ _
      (mem_chart_target _ p) hη, h1, one_mul, one_mul]
  -- Read the covector `⟪η, de₀ ·⟫` at `e₀⁻¹ (e₀ p) = p` as `ξ`.
  have hp : e₀.symm (e₀ p) = p := e₀.left_inv (mem_chart_source _ p)
  rw [hp, hξη]

end PrincipalSymbol

end TauCeti
