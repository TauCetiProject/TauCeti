/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Radial.Contraction
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Radial contractions as local diffeomorphisms

On a finite-dimensional real normed space, the Euclidean radial contraction with a nonnegative
parameter is a local diffeomorphism. Families of these contractions preserve manifold smoothness
for every regularity at most `∞`.

For a positive radius `r`, the contraction with parameter `r⁻²` is packaged as a `C^n` partial
diffeomorphism `TauCeti.radialContractionPartialDiffeomorph` with source `univ` and target
`Euclidean.ball c r`. Composing its inverse with a restricted extended chart shrinks any
neighbourhood of an interior point of a `C^n` manifold (`n ≤ ∞`) to an open submanifold `C^n`
diffeomorphic to the entire model space `E`
(`TauCeti.exists_diffeomorph_modelSpace_of_isInteriorPoint` and
`TauCeti.exists_diffeomorph_modelSpace`).
-/

public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ∞ω}

/-- A radial contraction with nonnegative parameter is a local diffeomorphism. -/
theorem isLocalDiffeomorph_radialContraction (c : E) (hn : n ≤ ∞) {κ : ℝ} (hκ : 0 ≤ κ) :
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n (radialContraction c κ) := by
  rcases hκ.eq_or_lt with rfl | hκ
  · have : radialContraction c 0 = id := funext (radialContraction_zero c)
    rw [this]
    exact (Diffeomorph.refl 𝓘(ℝ, E) E n).isLocalDiffeomorph
  obtain ⟨Θ, hsource, hΘ, hΘsymm, hΘeq⟩ := exists_radialContraction_eq_openPartialHomeomorph c hκ
  exact fun y => isLocalDiffeomorphAt_of_eqOn
    (Φ := PartialDiffeomorph.ofOpenPartialHomeomorph Θ (hΘ.of_le hn) (hΘsymm.of_le hn))
    (by simp [hsource])
    fun z _ => by simp [← hΘeq]

/-- A `C^n` family of radial contractions with nonnegative parameters, applied to a `C^n`
family of points, is `C^n` for `n ≤ ∞`. -/
theorem contMDiff_radialContraction {E' H' X : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H' X] (c : E) (hn : n ≤ ∞) {κ : X → ℝ} {y : X → E} (hκ : ContMDiff J 𝓘(ℝ) n κ)
    (hκ₀ : ∀ x, 0 ≤ κ x) (hy : ContMDiff J 𝓘(ℝ, E) n y) :
    ContMDiff J 𝓘(ℝ, E) n fun x => radialContraction c (κ x) (y x) :=
  ((contDiffOn_radialContraction c).of_le hn).contMDiffOn.comp_contMDiff (hκ.prodMk_space hy)
    fun x => add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (hκ₀ x) (sq_nonneg _))

/-- For `r > 0` and `n ≤ ∞`, the radial contraction about `c` with parameter `r⁻²` as a `C^n`
partial diffeomorphism of `E` with source `univ` and target `Euclidean.ball c r`. -/
def radialContractionPartialDiffeomorph (c : E) (hn : n ≤ ∞) {r : ℝ} (hr : 0 < r) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n :=
  let h := exists_radialContraction_eq_openPartialHomeomorph c (κ := r⁻¹ ^ 2) (by positivity)
  PartialDiffeomorph.ofOpenPartialHomeomorph h.choose
    (h.choose_spec.2.1.of_le hn) (h.choose_spec.2.2.1.of_le hn)

/-- The forward map of `radialContractionPartialDiffeomorph` is `radialContraction c (r⁻¹ ^ 2)`. -/
@[simp]
theorem coe_radialContractionPartialDiffeomorph (c : E) (hn : n ≤ ∞) {r : ℝ} (hr : 0 < r) :
    ⇑(radialContractionPartialDiffeomorph c hn hr) = radialContraction c (r⁻¹ ^ 2) := by
  let h := exists_radialContraction_eq_openPartialHomeomorph c (κ := r⁻¹ ^ 2) (by positivity)
  ext x
  rw [radialContractionPartialDiffeomorph,
    PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv]
  exact congrFun h.choose_spec.2.2.2 x

/-- The source of `radialContractionPartialDiffeomorph` is `Set.univ`. -/
@[simp]
theorem radialContractionPartialDiffeomorph_source (c : E) (hn : n ≤ ∞) {r : ℝ} (hr : 0 < r) :
    (radialContractionPartialDiffeomorph c hn hr).source = univ := by
  let h := exists_radialContraction_eq_openPartialHomeomorph c (κ := r⁻¹ ^ 2) (by positivity)
  rw [radialContractionPartialDiffeomorph,
    PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv]
  exact h.choose_spec.1

/-- The target of `radialContractionPartialDiffeomorph` is `Euclidean.ball c r`. -/
@[simp]
theorem radialContractionPartialDiffeomorph_target (c : E) (hn : n ≤ ∞) {r : ℝ} (hr : 0 < r) :
    (radialContractionPartialDiffeomorph c hn hr).target = Euclidean.ball c r := by
  rw [← (radialContractionPartialDiffeomorph c hn hr).image_source_eq_target,
    radialContractionPartialDiffeomorph_source, image_univ, coe_radialContractionPartialDiffeomorph,
    range_radialContraction c hr]

/-- `radialContractionPartialDiffeomorph` fixes its centre `c`. -/
@[simp]
theorem radialContractionPartialDiffeomorph_self (c : E) (hn : n ≤ ∞) {r : ℝ} (hr : 0 < r) :
    radialContractionPartialDiffeomorph c hn hr c = c := by
  simp

/-- Every neighbourhood `U` of an interior point `x₀` of a `C^n` manifold (`n ≤ ∞`) contains an
open neighbourhood `W` of `x₀` admitting a `C^n` diffeomorphism onto the whole model space `E`
sending `x₀` to `0`. -/
theorem exists_diffeomorph_modelSpace_of_isInteriorPoint
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
    (hn : n ≤ ∞) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ (W : TopologicalSpace.Opens M) (hx₀W : x₀ ∈ W) (Φ : W ≃ₘ^n⟮I, 𝓘(ℝ, E)⟯ E),
      (W : Set M) ⊆ U ∧ Φ ⟨x₀, hx₀W⟩ = 0 := by
  obtain ⟨U₀, hU₀U, hU₀open, hx₀U₀⟩ := mem_nhds_iff.1 hU
  let ψ := (extChartPartialDiffeomorph I n x₀).restrOpen U₀ hU₀open
  have hx₀ψ : x₀ ∈ ψ.source := by
    rw [PartialDiffeomorph.restrOpen_source]
    exact ⟨(mem_extChartPartialDiffeomorph_source I n x₀).2 hx₀, hx₀U₀⟩
  set z₀ : E := ψ x₀
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, Euclidean.ball z₀ r ⊆ ψ.target :=
    Euclidean.nhds_basis_ball.mem_iff.1 (ψ.open_target.mem_nhds (ψ.map_source hx₀ψ))
  let τ : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E := Diffeomorph.smulAdd (𝕜 := ℝ) (n := n) 1 z₀ one_ne_zero
  let ρ := radialContractionPartialDiffeomorph z₀ hn hr
  let Ξ : PartialDiffeomorph 𝓘(ℝ, E) I E M n := (τ.toPartialDiffeomorph.trans ρ).trans ψ.symm
  have hΞsource : Ξ.source = univ := by
    rw [PartialDiffeomorph.trans_source, PartialDiffeomorph.trans_source,
      PartialDiffeomorph.coe_trans]
    have hτsource : τ.toPartialDiffeomorph.source = univ := by simp
    rw [hτsource, radialContractionPartialDiffeomorph_source, preimage_univ, univ_inter,
      univ_inter]
    exact eq_univ_of_forall fun y ↦
      hball (by simpa [ρ] using radialContraction_mem_ball z₀ (τ y) hr)
  have hΞ0 : Ξ 0 = x₀ := by
    simp only [Ξ, PartialDiffeomorph.coe_trans, Function.comp_apply]
    have hτ0 : τ.toPartialDiffeomorph 0 = z₀ := by simp [τ]
    rw [hτ0, radialContractionPartialDiffeomorph_self]
    exact ψ.left_inv hx₀ψ
  have hx₀Ξ : x₀ ∈ Ξ.target := hΞ0 ▸ Ξ.map_source (hΞsource ▸ mem_univ 0)
  let W : TopologicalSpace.Opens M := ⟨Ξ.target, Ξ.open_target⟩
  have hS : (⟨Ξ.source, Ξ.open_source⟩ : TopologicalSpace.Opens E) = ⊤ :=
    TopologicalSpace.Opens.ext hΞsource
  let Φ : W ≃ₘ^n⟮I, 𝓘(ℝ, E)⟯ E :=
    Ξ.toDiffeomorphSourceTarget.symm.trans (Diffeomorph.ofTop _ hS)
  refine ⟨W, hx₀Ξ, Φ, ?_, ?_⟩
  · rw [TopologicalSpace.Opens.coe_mk]
    intro y hy
    rw [PartialDiffeomorph.trans_target] at hy
    have hy' : y ∈ ψ.source := by simpa using hy.1
    rw [PartialDiffeomorph.restrOpen_source] at hy'
    exact hU₀U hy'.2
  · simp only [Φ, Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.ofTop_apply, ← hΞ0]
    rw [Ξ.toDiffeomorphSourceTarget_symm_apply_coe]
    exact Ξ.left_inv (hΞsource ▸ mem_univ 0)

/-- On a boundaryless `C^n` manifold (`n ≤ ∞`), every neighbourhood `U` of `x₀` contains an open
neighbourhood `W` of `x₀` admitting a `C^n` diffeomorphism onto the whole model space `E` sending
`x₀` to `0`. -/
theorem exists_diffeomorph_modelSpace
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M] [BoundarylessManifold I M]
    (hn : n ≤ ∞) (x₀ : M) {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ (W : TopologicalSpace.Opens M) (hx₀W : x₀ ∈ W) (Φ : W ≃ₘ^n⟮I, 𝓘(ℝ, E)⟯ E),
      (W : Set M) ⊆ U ∧ Φ ⟨x₀, hx₀W⟩ = 0 :=
  exists_diffeomorph_modelSpace_of_isInteriorPoint hn BoundarylessManifold.isInteriorPoint hU

end TauCeti
