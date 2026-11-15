/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.HodgeStar
public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
import TauCeti.LinearAlgebra.Eigenspace.Involution
import TauCeti.LinearAlgebra.Eigenspace.Separation

/-!
# Self-dual and anti-self-dual forms on an oriented Riemannian manifold

Let `M` be an oriented Riemannian manifold of dimension `k + k` with `k` even, for instance a
four-manifold and `k = 2`. On each exterior-form fibre `Λᵏ T*_x M`, the Hodge star
(`TauCeti.formHodgeStarCLM`) is an involution, splitting the fibre orthogonally into its `+1` and
`-1` eigenspaces `Λ⁺_x` (`TauCeti.selfDualSubspace`) and `Λ⁻_x` (`TauCeti.antiSelfDualSubspace`)
via the projections `P±_x = (1 ± ⋆) / 2` (`TauCeti.selfDualProjCLM`, `TauCeti.antiSelfDualProjCLM`,
and their codomain-restricted linear counterparts `TauCeti.selfDualProj`,
`TauCeti.antiSelfDualProj`). When `0 < k`, both fibre subspaces have dimension
`(k + k).choose k / 2`: three for two-forms on a four-manifold.

Globally, in even middle degree, the Hodge star `⋆` of middle-degree forms
(`TauCeti.RoughForm.hodgeStar`) is an involution, `⋆⋆ = 1`. Its `+1` and `-1` eigenspaces are the
**self-dual** forms `Ω⁺` (`TauCeti.RoughForm.selfDualForms`) and the **anti-self-dual** forms `Ω⁻`
(`TauCeti.RoughForm.antiSelfDualForms`), the rough sections of the eigenbundles `Λ⁺` and `Λ⁻` of
`Λᵏ T*M`. In every middle degree, a form decomposes algebraically as `α = α⁺ + α⁻` into its
self-dual part `α⁺ = (α + ⋆α) / 2` (`TauCeti.RoughForm.selfDualPart`) and its anti-self-dual part
`α⁻ = (α - ⋆α) / 2` (`TauCeti.RoughForm.antiSelfDualPart`); when `k` is even, these are the
projections `(1 ± ⋆) / 2` onto `Ω±`, and `Ω⁺ ⊕ Ω⁻` is all of the middle-degree forms.

Since `⋆` is a pointwise isometry, self-dual and anti-self-dual covectors are orthogonal in every
middle degree, and `⟨α, β⟩ = ⟨P⁺ α, P⁺ β⟩ + ⟨P⁻ α, P⁻ β⟩` (`|α|² = |α⁺|² + |α⁻|²`). In even
middle degree, the wedge square is `α ∧ α = (|α⁺|² - |α⁻|²) vol`. For the curvature `F` of a
connection on a four-manifold this compares the integral of `F ∧ F`, a characteristic number, with
the energies of `F⁺` and `F⁻`; the curvature equation of the Seiberg–Witten equations prescribes
the self-dual part `F⁺`.

For a `C^n` metric on a `C^(n+1)` manifold both `(1 ± ⋆) / 2` maps preserve `C^n` forms; on smooth
forms they are `TauCeti.SmoothForm.selfDualPart` and `TauCeti.SmoothForm.antiSelfDualPart`, which
for even `k` project onto the smooth self-dual and anti-self-dual forms
`TauCeti.SmoothForm.selfDualForms` and `TauCeti.SmoothForm.antiSelfDualForms`. Reversing the
orientation negates `⋆` and so exchanges the two parts
(`TauCeti.RoughForm.selfDualPart_neg_orientation`,
`TauCeti.RoughForm.antiSelfDualPart_neg_orientation`).

Integrating, a compactly supported form has `∫_M |α|² vol = ∫_M |α⁺|² vol + ∫_M |α⁻|² vol` in
every middle degree, and `∫_M α ∧ α = ∫_M |α⁺|² vol - ∫_M |α⁻|² vol` when `k` is even. On a
boundaryless manifold, Stokes' theorem makes
`∫_M ψ ∧ ψ` depend only on the de Rham class of a compactly supported closed form `ψ`
(`TauCeti.integralTopForm_wedge_self_eq_of_sub_mem_exactForms`). So if `ψ - φ` is exact, then
`∫_M |ψ⁺|² vol - ∫_M |ψ⁻|² vol = ∫_M |φ⁺|² vol - ∫_M |φ⁻|² vol` and
`∫_M |ψ|² vol = 2 ∫_M |ψ⁺|² vol - (∫_M |φ⁺|² vol - ∫_M |φ⁻|² vol)`. For the curvature forms of
two connections on a line bundle over a closed four-manifold, the difference is the exact form
`da` of the difference of the connections. This is the Chern–Weil step in the `L²` curvature
bounds of gauge theory: an equation prescribing the self-dual part `F⁺`, such as the curvature
equation of the Seiberg–Witten equations, controls the whole energy of `F`. For an exact form
`β = dα`, compared with `φ = 0`, the two parts have the same energy,
`∫_M |β⁺|² vol = ∫_M |β⁻|² vol`. Hence `β⁺ = 0` or `β⁻ = 0` forces `β = 0`: on a closed
four-manifold a one-form `a` with `(da)⁺ = 0` is closed.

## Main definitions

* `TauCeti.selfDualSubspace`, `TauCeti.antiSelfDualSubspace`: the fibrewise `+1` and `-1`
  eigenspaces `Λ⁺_x, Λ⁻_x ⊆ Λᵏ T*_x M` of the Hodge star.
* `TauCeti.selfDualProjCLM`, `TauCeti.antiSelfDualProjCLM`, `TauCeti.selfDualProj`,
  `TauCeti.antiSelfDualProj`: the fibrewise operators `(1 ± ⋆) / 2` on `Λᵏ T*_x M`, and for even
  `k` their codomain-restricted projections onto `Λ±_x`.
* `TauCeti.RoughForm.selfDualForms`, `TauCeti.RoughForm.antiSelfDualForms`: the `+1` and `-1`
  eigenspaces of the Hodge star of middle-degree forms.
* `TauCeti.RoughForm.selfDualPart`, `TauCeti.RoughForm.antiSelfDualPart`: the maps
  `α ↦ (α ± ⋆α) / 2` (projections onto `Ω±` when `k` is even).
* `TauCeti.SmoothForm.selfDualPart`, `TauCeti.SmoothForm.antiSelfDualPart`: the corresponding
  `(1 ± ⋆) / 2` maps on smooth forms.
* `TauCeti.SmoothForm.selfDualForms`, `TauCeti.SmoothForm.antiSelfDualForms`: the smooth
  self-dual and anti-self-dual forms, the `+1` and `-1` eigenspaces of the Hodge star of smooth
  middle-degree forms.

## Main results

* `TauCeti.isCompl_selfDualSubspace_antiSelfDualSubspace`,
  `TauCeti.alternatingFormInner_eq_zero_of_mem_selfDualSubspace_of_mem_antiSelfDualSubspace`,
  `TauCeti.alternatingFormInner_eq_add_selfDualProjCLM_antiSelfDualProjCLM`: for even `k` each
  fibre splits orthogonally as `Λ⁺_x ⊕ Λ⁻_x`, and in every middle degree the Gram pairing
  satisfies `⟨α, β⟩ = ⟨P⁺_x α, P⁺_x β⟩ + ⟨P⁻_x α, P⁻_x β⟩`.
* `TauCeti.finrank_selfDualSubspace`, `TauCeti.finrank_antiSelfDualSubspace`,
  `TauCeti.finrank_selfDualSubspace_two`, `TauCeti.finrank_antiSelfDualSubspace_two`: the fibre
  dimensions `(k + k).choose k / 2` for even `0 < k`, and `3` for `k = 2`.
* `TauCeti.RoughForm.isProj_selfDualPart`, `TauCeti.RoughForm.isProj_antiSelfDualPart`: for even
  `k`, the projections onto `Ω⁺` and `Ω⁻`, with kernels `Ω⁻` and `Ω⁺`.
* `TauCeti.RoughForm.isCompl_selfDualForms_antiSelfDualForms`: for even `k`, `Ω⁺ ⊕ Ω⁻` is all of
  the middle-degree forms.
* `TauCeti.RoughForm.alternatingFormInner_eq_zero_of_mem_selfDualForms`: self-dual and
  anti-self-dual forms are pointwise orthogonal.
* `TauCeti.RoughForm.alternatingFormInner_selfDualPart_of_mem_selfDualForms`,
  `TauCeti.RoughForm.alternatingFormInner_antiSelfDualPart_of_mem_antiSelfDualForms`: pairing with
  a self-dual, or anti-self-dual, form sees only the self-dual, or anti-self-dual, part.
* `TauCeti.RoughForm.alternatingFormInner_self_eq_add`: `|α|² = |α⁺|² + |α⁻|²` pointwise in every
  middle degree.
* `TauCeti.RoughForm.wedge_self_apply`: `α ∧ α = (|α⁺|² - |α⁻|²) vol` for even `k`.
* `TauCeti.RoughForm.map_proj_selfDualForms`, `TauCeti.RoughForm.map_proj_antiSelfDualForms`: the
  values at `x` of rough (anti-)self-dual forms are `selfDualSubspace o x` and
  `antiSelfDualSubspace o x`.
* `TauCeti.IsSmoothForm.selfDualPart`, `TauCeti.IsSmoothForm.antiSelfDualPart`: the `(1 ± ⋆) / 2`
  maps preserve `C^n` forms.
* `TauCeti.SmoothForm.isProj_selfDualPart`, `TauCeti.SmoothForm.isProj_antiSelfDualPart`: for even
  `k`, on smooth forms they are the projections onto the smooth `Ω⁺` and `Ω⁻`, which are the smooth
  forms lying in the rough `Ω⁺` and `Ω⁻` (`TauCeti.SmoothForm.coe_mem_selfDualForms_iff`).
* `TauCeti.SmoothForm.integralTopForm_inner_self_smul_riemannianVolumeForm_eq_add`,
  `TauCeti.SmoothForm.integralTopForm_wedge_self`: `∫_M |α|² vol = ∫_M |α⁺|² vol + ∫_M |α⁻|² vol`
  and `∫_M α ∧ α = ∫_M |α⁺|² vol - ∫_M |α⁻|² vol` for a compactly supported form.
* `integralTopForm_inner_selfDualPart_sub_inner_antiSelfDualPart_eq_of_sub_mem_exactForms`
  (in the namespace `TauCeti.SmoothForm`): `∫_M |ψ⁺|² vol - ∫_M |ψ⁻|² vol` agrees for compactly
  supported closed forms `φ`, `ψ` whose difference is exact.
* `TauCeti.SmoothForm.integralTopForm_inner_self_smul_riemannianVolumeForm_eq_two_mul_sub`: the
  energy of such a form is twice its self-dual energy, minus the invariant of its class.
* `TauCeti.SmoothForm.selfDualPart_wedge_zero_right`,
  `TauCeti.SmoothForm.alternatingFormEquiv_symm_selfDualPart`,
  `TauCeti.SmoothForm.hodgeStar_alternatingFormEquiv_symm_of_mem_selfDualForms`: right
  `C^∞(M)`-linearity and fibrewise `k`-vector characterization of smooth self-dual forms.
* `TauCeti.SmoothForm.integralTopForm_inner_selfDualPart_eq_inner_antiSelfDualPart`: a compactly
  supported exact form has `∫_M |β⁺|² vol = ∫_M |β⁻|² vol`.
* `TauCeti.SmoothForm.integralTopForm_inner_selfDualPart_eq_zero`,
  `TauCeti.SmoothForm.integralTopForm_inner_antiSelfDualPart_eq_zero`: the self-dual, or
  anti-self-dual, part of an exact form is `L²`-orthogonal to the compactly supported closed
  self-dual, or anti-self-dual, forms.
* `TauCeti.SmoothForm.eq_zero_of_selfDualPart_eq_zero`,
  `TauCeti.SmoothForm.eq_zero_of_antiSelfDualPart_eq_zero`: a compactly supported exact form with
  vanishing self-dual, or anti-self-dual, part is zero.
* `TauCeti.SmoothForm.integralTopForm_inner_smul_riemannianVolumeForm_eq_poincarePairing`: for a
  closed form `φ` and a compactly supported closed self-dual form `γ`, `∫_M ⟨φ, γ⟩ vol` is the
  Poincaré pairing of their de Rham classes, so it depends only on the class of `φ`.

## References

* M. F. Atiyah, N. J. Hitchin and I. M. Singer, *Self-duality in four-dimensional Riemannian
  geometry*, Proc. R. Soc. Lond. A 362 (1978), 425–461, §1.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University
  Press (1990), §1.1.
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

section Fibrewise

variable {k : ℕ}

/-! ### Fibrewise self-dual and anti-self-dual subspaces -/

/-- The subspace `Λ⁺_x` of self-dual real `k`-forms at `x`, defined as the `+1`-eigenspace of the
fibrewise Hodge star `formHodgeStarCLM o rfl x`. -/
def selfDualSubspace (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    Submodule ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :=
  Module.End.eigenspace
    (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) 1

/-- The subspace `Λ⁻_x` of anti-self-dual real `k`-forms at `x`, defined as the `-1`-eigenspace of
the fibrewise Hodge star `formHodgeStarCLM o rfl x`. -/
def antiSelfDualSubspace (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    Submodule ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :=
  Module.End.eigenspace
    (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) (-1)

/-- A covector `α ∈ Λᵏ T*_x M` lies in `selfDualSubspace o x` if and only if `⋆α = α`. -/
@[simp]
theorem mem_selfDualSubspace_iff {o : Manifold.Orientation I M (Fin (k + k))} {x : M}
    {α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ} :
    α ∈ selfDualSubspace o x ↔ formHodgeStarCLM o rfl x α = α := by
  rw [selfDualSubspace, Module.End.mem_eigenspace_iff, one_smul]
  rfl

/-- A covector `α ∈ Λᵏ T*_x M` lies in `antiSelfDualSubspace o x` if and only if `⋆α = -α`. -/
@[simp]
theorem mem_antiSelfDualSubspace_iff {o : Manifold.Orientation I M (Fin (k + k))} {x : M}
    {α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ} :
    α ∈ antiSelfDualSubspace o x ↔ formHodgeStarCLM o rfl x α = -α := by
  rw [antiSelfDualSubspace, Module.End.mem_eigenspace_iff, neg_one_smul]
  rfl

/-- Reversing the manifold orientation exchanges the self-dual and anti-self-dual subspaces. -/
@[simp]
theorem selfDualSubspace_neg_orientation (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    selfDualSubspace (-o) x = antiSelfDualSubspace o x := by
  ext α
  rw [mem_selfDualSubspace_iff, mem_antiSelfDualSubspace_iff, formHodgeStarCLM_neg_orientation,
    neg_apply, neg_eq_iff_eq_neg]

/-- Reversing the manifold orientation exchanges the anti-self-dual and self-dual subspaces. -/
@[simp]
theorem antiSelfDualSubspace_neg_orientation (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    antiSelfDualSubspace (-o) x = selfDualSubspace o x := by
  rw [← selfDualSubspace_neg_orientation, neg_neg]

/-- Self-dual and anti-self-dual covectors at `x` meet trivially. -/
theorem disjoint_selfDualSubspace_antiSelfDualSubspace
    (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    Disjoint (selfDualSubspace o x) (antiSelfDualSubspace o x) :=
  Module.End.disjoint_genEigenspace
    (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ))
    (by norm_num : (1 : ℝ) ≠ -1) 1 1

/-- Self-dual and anti-self-dual covectors at `x` are orthogonal for `alternatingFormInner` in
every middle degree `k`. -/
theorem alternatingFormInner_eq_zero_of_mem_selfDualSubspace_of_mem_antiSelfDualSubspace
    (o : Manifold.Orientation I M (Fin (k + k))) {x : M}
    {α β : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ}
    (hα : α ∈ selfDualSubspace o x) (hβ : β ∈ antiSelfDualSubspace o x) :
    alternatingFormInner (TangentSpace I x) k α β = 0 := by
  have h := alternatingFormInner_formHodgeStarCLM o rfl x α β
  rw [mem_selfDualSubspace_iff.mp hα, mem_antiSelfDualSubspace_iff.mp hβ, map_neg] at h
  linarith

/-- In an even middle degree, `formHodgeStarCLM` is an involution on every fibre. -/
theorem formHodgeStarCLM_involutive (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (x : M) :
    Function.Involutive (formHodgeStarCLM o rfl x) :=
  fun α ↦ congr($(formHodgeStarCLM_comp_self_of_even o hk x) α)

/-! ### Fibrewise `(1 ± ⋆) / 2` operators and eigenprojections -/

/-- The fibrewise continuous linear operator `P⁺_x = (1 + ⋆) / 2` on real `k`-forms at `x`. When
`k` is even, `P⁺_x` is the orthogonal projection onto `selfDualSubspace o x`. -/
def selfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ :=
  (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ + formHodgeStarCLM o rfl x)

/-- The fibrewise continuous linear operator `P⁻_x = (1 - ⋆) / 2` on real `k`-forms at `x`. When
`k` is even, `P⁻_x` is the orthogonal projection onto `antiSelfDualSubspace o x`. -/
def antiSelfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ :=
  (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ - formHodgeStarCLM o rfl x)

/-- Defining formula `(1 + ⋆) / 2` for `selfDualProjCLM`. -/
theorem selfDualProjCLM_def (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    selfDualProjCLM o x =
      (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ + formHodgeStarCLM o rfl x) :=
  (rfl)

/-- Defining formula `(1 - ⋆) / 2` for `antiSelfDualProjCLM`. -/
theorem antiSelfDualProjCLM_def (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    antiSelfDualProjCLM o x =
      (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ - formHodgeStarCLM o rfl x) :=
  (rfl)

/-- Explicit formula `(α + ⋆α) / 2` for `selfDualProjCLM`. -/
theorem selfDualProjCLM_apply (o : Manifold.Orientation I M (Fin (k + k))) (x : M)
    (α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    selfDualProjCLM o x α = (2⁻¹ : ℝ) • (α + formHodgeStarCLM o rfl x α) :=
  (rfl)

/-- Explicit formula `(α - ⋆α) / 2` for `antiSelfDualProjCLM`. -/
theorem antiSelfDualProjCLM_apply (o : Manifold.Orientation I M (Fin (k + k))) (x : M)
    (α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    antiSelfDualProjCLM o x α = (2⁻¹ : ℝ) • (α - formHodgeStarCLM o rfl x α) :=
  (rfl)

private theorem selfDualProjCLM_eq_halfOneAdd
    (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    letI := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
    selfDualProjCLM o x = halfOneAdd ℝ (formHodgeStarCLM o rfl x) := by
  let := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  rw [selfDualProjCLM_def, halfOneAdd_def, invOf_eq_inv, ContinuousLinearMap.one_def]

private theorem antiSelfDualProjCLM_eq_halfOneAdd
    (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    letI := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
    antiSelfDualProjCLM o x = halfOneAdd ℝ (-formHodgeStarCLM o rfl x) := by
  let := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  rw [antiSelfDualProjCLM_def, halfOneAdd_def, invOf_eq_inv, ContinuousLinearMap.one_def]
  congr 1

/-- Reversing the orientation exchanges `selfDualProjCLM` and `antiSelfDualProjCLM`. -/
@[simp]
theorem selfDualProjCLM_neg_orientation (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    selfDualProjCLM (-o) x = antiSelfDualProjCLM o x := by
  ext α v
  simp [selfDualProjCLM_apply, antiSelfDualProjCLM_apply, sub_eq_add_neg]

/-- Reversing the orientation exchanges `antiSelfDualProjCLM` and `selfDualProjCLM`. -/
@[simp]
theorem antiSelfDualProjCLM_neg_orientation (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    antiSelfDualProjCLM (-o) x = selfDualProjCLM o x := by
  rw [← selfDualProjCLM_neg_orientation, neg_neg]

/-- The fibrewise operators `P⁺_x = (1 + ⋆) / 2` and `P⁻_x = (1 - ⋆) / 2` sum to the identity on
every fibre (forming complementary eigenspace projections when `k` is even). -/
@[simp]
theorem selfDualProjCLM_add_antiSelfDualProjCLM
    (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    selfDualProjCLM o x + antiSelfDualProjCLM o x =
      ContinuousLinearMap.id ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) := by
  let := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  rw [selfDualProjCLM_eq_halfOneAdd, antiSelfDualProjCLM_eq_halfOneAdd]
  exact halfOneAdd_add_halfOneAdd_neg ℝ (formHodgeStarCLM o rfl x)

/-- Every middle-degree covector `α` is the sum `P⁺_x α + P⁻_x α` of its `(1 + ⋆) / 2` and
`(1 - ⋆) / 2` parts (its self-dual and anti-self-dual projections when `k` is even). -/
@[simp]
theorem selfDualProjCLM_add_antiSelfDualProjCLM_apply
    (o : Manifold.Orientation I M (Fin (k + k))) (x : M)
    (α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    selfDualProjCLM o x α + antiSelfDualProjCLM o x α = α :=
  congr($(selfDualProjCLM_add_antiSelfDualProjCLM o x) α)

/-- The difference `P⁺_x - P⁻_x` of `(1 + ⋆) / 2` and `(1 - ⋆) / 2` is the fibrewise Hodge star
`⋆`. -/
@[simp]
theorem selfDualProjCLM_sub_antiSelfDualProjCLM
    (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    selfDualProjCLM o x - antiSelfDualProjCLM o x = formHodgeStarCLM o rfl x := by
  let := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  rw [selfDualProjCLM_eq_halfOneAdd, antiSelfDualProjCLM_eq_halfOneAdd]
  exact halfOneAdd_sub_halfOneAdd_neg ℝ (formHodgeStarCLM o rfl x)

/-- The codomain-restricted linear projection `P⁺_x : Λᵏ T*_x M →ₗ[ℝ] Λ⁺_x` onto the self-dual
subspace in an even middle degree. -/
def selfDualProj (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) (x : M) :
    (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] selfDualSubspace o x :=
  letI := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  Module.End.eigenProjOfInvolutive
    (g := (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)))
    (formHodgeStarCLM_involutive o hk x) (one_mul (1 : ℝ))

/-- The codomain-restricted linear projection `P⁻_x : Λᵏ T*_x M →ₗ[ℝ] Λ⁻_x` onto the anti-self-dual
subspace in an even middle degree. -/
def antiSelfDualProj (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) (x : M) :
    (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] antiSelfDualSubspace o x :=
  letI := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  Module.End.eigenProjOfInvolutive
    (g := (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)))
    (formHodgeStarCLM_involutive o hk x) (by norm_num : (-1 : ℝ) * -1 = 1)

/-- Coercing `selfDualProj` back to the ambient exterior-form fibre gives `selfDualProjCLM`. -/
@[simp]
theorem coe_selfDualProj_apply (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (x : M) (α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    (selfDualProj o hk x α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) = selfDualProjCLM o x α := by
  let := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  -- `dsimp`/`unfold` leaves `(selfDualSubspace o x).addCommMonoid` unreduced inside the
  -- `LinearMap` instance argument, making the goal ill-typed at `implicit` transparency for `rw`.
  change (Module.End.eigenProjOfInvolutive
    (g := (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)))
    (formHodgeStarCLM_involutive o hk x) (one_mul (1 : ℝ)) α :
    TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) = selfDualProjCLM o x α
  rw [Module.End.coe_eigenProjOfInvolutive_apply, invOf_eq_inv, one_smul,
    ContinuousLinearMap.coe_coe, selfDualProjCLM_apply]

/-- Coercing `antiSelfDualProj` back to the ambient exterior-form fibre gives
`antiSelfDualProjCLM`. -/
@[simp]
theorem coe_antiSelfDualProj_apply (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (x : M) (α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    (antiSelfDualProj o hk x α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) =
      antiSelfDualProjCLM o x α := by
  let := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  -- `dsimp`/`unfold` leaves `(antiSelfDualSubspace o x).addCommMonoid` unreduced inside the
  -- `LinearMap` instance argument, making the goal ill-typed at `implicit` transparency for `rw`.
  change (Module.End.eigenProjOfInvolutive
    (g := (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)))
    (formHodgeStarCLM_involutive o hk x) (by norm_num : (-1 : ℝ) * -1 = 1) α :
    TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) = antiSelfDualProjCLM o x α
  rw [Module.End.coe_eigenProjOfInvolutive_apply, invOf_eq_inv, neg_one_smul,
    ContinuousLinearMap.coe_coe, antiSelfDualProjCLM_apply, sub_eq_add_neg]

/-- `selfDualProj` fixes every element of `selfDualSubspace o x`. -/
@[simp]
theorem selfDualProj_coe (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (x : M) (v : selfDualSubspace o x) :
    selfDualProj o hk x v = v := by
  let := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  exact Module.End.eigenProjOfInvolutive_apply_of_mem
    (g := (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)))
    (formHodgeStarCLM_involutive o hk x) (one_mul (1 : ℝ)) v

/-- `antiSelfDualProj` fixes every element of `antiSelfDualSubspace o x`. -/
@[simp]
theorem antiSelfDualProj_coe (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (x : M) (v : antiSelfDualSubspace o x) :
    antiSelfDualProj o hk x v = v := by
  let := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  exact Module.End.eigenProjOfInvolutive_apply_of_mem
    (g := (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)))
    (formHodgeStarCLM_involutive o hk x) (by norm_num : (-1 : ℝ) * -1 = 1) v

/-- `selfDualProj` kills every element of `antiSelfDualSubspace o x`. -/
@[simp]
theorem selfDualProj_coe_antiSelfDualSubspace (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) (v : antiSelfDualSubspace o x) :
    selfDualProj o hk x v = 0 := by
  let := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  exact Module.End.eigenProjOfInvolutive_apply_of_mem_neg
    (g := (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)))
    (formHodgeStarCLM_involutive o hk x) (one_mul (1 : ℝ)) (by norm_num : (1 : ℝ) * -1 = -1) v

/-- `antiSelfDualProj` kills every element of `selfDualSubspace o x`. -/
@[simp]
theorem antiSelfDualProj_coe_selfDualSubspace (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) (v : selfDualSubspace o x) :
    antiSelfDualProj o hk x v = 0 := by
  let := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  exact Module.End.eigenProjOfInvolutive_apply_of_mem_neg
    (g := (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)))
    (formHodgeStarCLM_involutive o hk x) (by norm_num : (-1 : ℝ) * -1 = 1)
    (by norm_num : (-1 : ℝ) * 1 = -1) v

/-- In an even middle degree, `selfDualProjCLM` maps every covector into `selfDualSubspace o x`. -/
theorem selfDualProjCLM_mem_selfDualSubspace (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) (α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    selfDualProjCLM o x α ∈ selfDualSubspace o x :=
  coe_selfDualProj_apply o hk x α ▸ (selfDualProj o hk x α).2

/-- In an even middle degree, `antiSelfDualProjCLM` maps every covector into
`antiSelfDualSubspace o x`. -/
theorem antiSelfDualProjCLM_mem_antiSelfDualSubspace (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) (α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    antiSelfDualProjCLM o x α ∈ antiSelfDualSubspace o x :=
  coe_antiSelfDualProj_apply o hk x α ▸ (antiSelfDualProj o hk x α).2

/-- `selfDualProjCLM` fixes every self-dual covector. -/
@[simp]
theorem selfDualProjCLM_eq_self_of_mem {o : Manifold.Orientation I M (Fin (k + k))} {x : M}
    {α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ} (hα : α ∈ selfDualSubspace o x) :
    selfDualProjCLM o x α = α := by
  rw [selfDualProjCLM_apply, mem_selfDualSubspace_iff.mp hα, ← two_smul ℝ α,
    inv_smul_smul₀ two_ne_zero]

/-- `antiSelfDualProjCLM` fixes every anti-self-dual covector. -/
@[simp]
theorem antiSelfDualProjCLM_eq_self_of_mem {o : Manifold.Orientation I M (Fin (k + k))} {x : M}
    {α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ} (hα : α ∈ antiSelfDualSubspace o x) :
    antiSelfDualProjCLM o x α = α := by
  rw [← selfDualProjCLM_neg_orientation]
  exact selfDualProjCLM_eq_self_of_mem ((selfDualSubspace_neg_orientation o x).symm ▸ hα)

/-- `selfDualProjCLM` vanishes on `α` if and only if `α` is anti-self-dual. -/
theorem selfDualProjCLM_eq_zero_iff {o : Manifold.Orientation I M (Fin (k + k))} {x : M}
    {α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ} :
    selfDualProjCLM o x α = 0 ↔ α ∈ antiSelfDualSubspace o x := by
  rw [selfDualProjCLM_apply, smul_eq_zero_iff_right (inv_ne_zero two_ne_zero),
    add_eq_zero_iff_neg_eq, mem_antiSelfDualSubspace_iff, eq_comm]

/-- `antiSelfDualProjCLM` vanishes on `α` if and only if `α` is self-dual. -/
theorem antiSelfDualProjCLM_eq_zero_iff {o : Manifold.Orientation I M (Fin (k + k))} {x : M}
    {α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ} :
    antiSelfDualProjCLM o x α = 0 ↔ α ∈ selfDualSubspace o x := by
  rw [← selfDualProjCLM_neg_orientation, selfDualProjCLM_eq_zero_iff,
    antiSelfDualSubspace_neg_orientation]

/-- In an even middle degree, `selfDualProjCLM` is idempotent. -/
theorem isIdempotentElem_selfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) :
    IsIdempotentElem (selfDualProjCLM o x) := by
  let := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  rw [selfDualProjCLM_eq_halfOneAdd]
  exact isIdempotentElem_halfOneAdd ℝ (formHodgeStarCLM_comp_self_of_even o hk x)

/-- In an even middle degree, `antiSelfDualProjCLM` is idempotent. -/
theorem isIdempotentElem_antiSelfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) :
    IsIdempotentElem (antiSelfDualProjCLM o x) := by
  let := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  rw [antiSelfDualProjCLM_eq_halfOneAdd]
  exact isIdempotentElem_halfOneAdd_neg ℝ (formHodgeStarCLM_comp_self_of_even o hk x)

/-- In an even middle degree, `P⁺_x ∘ P⁻_x = 0`. -/
@[simp]
theorem selfDualProjCLM_comp_antiSelfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) :
    (selfDualProjCLM o x).comp (antiSelfDualProjCLM o x) = 0 := by
  let := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  rw [← ContinuousLinearMap.mul_def, selfDualProjCLM_eq_halfOneAdd,
    antiSelfDualProjCLM_eq_halfOneAdd]
  exact halfOneAdd_mul_halfOneAdd_neg ℝ (formHodgeStarCLM_comp_self_of_even o hk x)

/-- In an even middle degree, `P⁻_x ∘ P⁺_x = 0`. -/
@[simp]
theorem antiSelfDualProjCLM_comp_selfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) :
    (antiSelfDualProjCLM o x).comp (selfDualProjCLM o x) = 0 := by
  simpa using selfDualProjCLM_comp_antiSelfDualProjCLM (-o) hk x

/-- In an even middle degree, the range of `selfDualProjCLM` is `selfDualSubspace o x`. -/
@[simp]
theorem range_selfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (x : M) :
    (selfDualProjCLM o x).range = selfDualSubspace o x := by
  ext α
  refine ⟨?_, fun hα ↦ ⟨α, selfDualProjCLM_eq_self_of_mem hα⟩⟩
  rintro ⟨β, rfl⟩
  exact selfDualProjCLM_mem_selfDualSubspace o hk x β

/-- In an even middle degree, the range of `antiSelfDualProjCLM` is `antiSelfDualSubspace o x`. -/
@[simp]
theorem range_antiSelfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (x : M) :
    (antiSelfDualProjCLM o x).range = antiSelfDualSubspace o x := by
  rw [← selfDualProjCLM_neg_orientation, range_selfDualProjCLM (-o) hk x,
    selfDualSubspace_neg_orientation]

/-- The kernel of `selfDualProjCLM` is `antiSelfDualSubspace o x`. -/
@[simp]
theorem ker_selfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    (selfDualProjCLM o x).ker = antiSelfDualSubspace o x := by
  ext α
  exact selfDualProjCLM_eq_zero_iff

/-- The kernel of `antiSelfDualProjCLM` is `selfDualSubspace o x`. -/
@[simp]
theorem ker_antiSelfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    (antiSelfDualProjCLM o x).ker = selfDualSubspace o x := by
  ext α
  exact antiSelfDualProjCLM_eq_zero_iff

/-- **Fibrewise direct-sum decomposition**: in an even middle degree, `Λ⁺_x` and `Λ⁻_x` are
complementary subspaces of `Λᵏ T*_x M`. -/
theorem isCompl_selfDualSubspace_antiSelfDualSubspace
    (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) (x : M) :
    IsCompl (selfDualSubspace o x) (antiSelfDualSubspace o x) :=
  isCompl_eigenspace_one_neg_one (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : ℝ) ≠ 0))
    (T := (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)))
    (formHodgeStarCLM_involutive o hk x)

/-- In an even middle degree, `selfDualProjCLM` is self-adjoint for `alternatingFormInner`. -/
theorem alternatingFormInner_selfDualProjCLM_left (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) (α β : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner (TangentSpace I x) k (selfDualProjCLM o x α) β =
      alternatingFormInner (TangentSpace I x) k α (selfDualProjCLM o x β) := by
  simp only [selfDualProjCLM_apply, map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
    alternatingFormInner_formHodgeStarCLM_left o hk x α β]

/-- In an even middle degree, `antiSelfDualProjCLM` is self-adjoint for `alternatingFormInner`. -/
theorem alternatingFormInner_antiSelfDualProjCLM_left (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) (α β : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner (TangentSpace I x) k (antiSelfDualProjCLM o x α) β =
      alternatingFormInner (TangentSpace I x) k α (antiSelfDualProjCLM o x β) := by
  rw [← selfDualProjCLM_neg_orientation]
  exact alternatingFormInner_selfDualProjCLM_left (-o) hk x α β

/-- **Gram pairing identity under `(1 ± ⋆) / 2`**: `⟨α, β⟩ = ⟨P⁺_x α, P⁺_x β⟩ + ⟨P⁻_x α, P⁻_x β⟩`
at every point and in every middle degree `k`. When `k` is even, this expresses the orthogonal
decomposition of the Gram pairing along `Λ⁺_x ⊕ Λ⁻_x`. -/
theorem alternatingFormInner_eq_add_selfDualProjCLM_antiSelfDualProjCLM
    (o : Manifold.Orientation I M (Fin (k + k))) (x : M)
    (α β : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner (TangentSpace I x) k α β =
      alternatingFormInner (TangentSpace I x) k
          (selfDualProjCLM o x α) (selfDualProjCLM o x β) +
        alternatingFormInner (TangentSpace I x) k
          (antiSelfDualProjCLM o x α) (antiSelfDualProjCLM o x β) := by
  simp only [selfDualProjCLM_apply, antiSelfDualProjCLM_apply, map_smul, map_add, map_sub,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, smul_eq_mul,
    alternatingFormInner_formHodgeStarCLM o rfl x α β, inv_eq_one_div]
  linarith

/-! ### Fibre dimensions -/

/-- Twice the dimension of `selfDualSubspace o x` is `(k + k).choose k` in an even positive middle
degree. -/
theorem two_mul_finrank_selfDualSubspace (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (hk₀ : 0 < k) (x : M) :
    2 * finrank ℝ (selfDualSubspace o x) = (k + k).choose k := by
  let := o.fact_finrank_tangentSpace x
  have heq : (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) =
      ((o.orientationAt x).formHodgeStar (o.fact_finrank_tangentSpace x).out.symm :
        Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) := by
    ext α v
    simp [formHodgeStarCLM_apply]
  rw [selfDualSubspace, heq]
  exact (o.orientationAt x).two_mul_finrank_eigenspace_formHodgeStar_one hk hk₀ _

/-- Twice the dimension of `antiSelfDualSubspace o x` is `(k + k).choose k` in an even positive
middle degree. -/
theorem two_mul_finrank_antiSelfDualSubspace (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (hk₀ : 0 < k) (x : M) :
    2 * finrank ℝ (antiSelfDualSubspace o x) = (k + k).choose k := by
  rw [← selfDualSubspace_neg_orientation]
  exact two_mul_finrank_selfDualSubspace (-o) hk hk₀ x

/-- **Rank of `Λ⁺`**: in an even positive middle degree, each fibre `selfDualSubspace o x` has
dimension `(k + k).choose k / 2`. -/
theorem finrank_selfDualSubspace (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (hk₀ : 0 < k) (x : M) :
    finrank ℝ (selfDualSubspace o x) = (k + k).choose k / 2 := by
  have h := two_mul_finrank_selfDualSubspace o hk hk₀ x
  omega

/-- **Rank of `Λ⁻`**: in an even positive middle degree, each fibre `antiSelfDualSubspace o x` has
dimension `(k + k).choose k / 2`. -/
theorem finrank_antiSelfDualSubspace (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (hk₀ : 0 < k) (x : M) :
    finrank ℝ (antiSelfDualSubspace o x) = (k + k).choose k / 2 := by
  rw [← selfDualSubspace_neg_orientation]
  exact finrank_selfDualSubspace (-o) hk hk₀ x

/-- **On an oriented Riemannian four-manifold, `Λ⁺` has rank three.** -/
@[simp]
theorem finrank_selfDualSubspace_two (o : Manifold.Orientation I M (Fin (2 + 2))) (x : M) :
    finrank ℝ (selfDualSubspace o x) = 3 := by
  rw [finrank_selfDualSubspace o even_two Nat.zero_lt_two x]
  decide

/-- **On an oriented Riemannian four-manifold, `Λ⁻` has rank three.** -/
@[simp]
theorem finrank_antiSelfDualSubspace_two (o : Manifold.Orientation I M (Fin (2 + 2))) (x : M) :
    finrank ℝ (antiSelfDualSubspace o x) = 3 := by
  rw [finrank_antiSelfDualSubspace o even_two Nat.zero_lt_two x]
  decide

end Fibrewise

variable {k : ℕ} (o : Manifold.Orientation I M (Fin (k + k)))

namespace RoughForm

/-! ### Self-dual and anti-self-dual forms -/

/-- The **self-dual** middle-degree forms `Ω⁺`: the `+1` eigenspace of the Hodge star, the forms
with `⋆α = α`. -/
def selfDualForms : Submodule ℝ (RoughForm I M ℝ k) :=
  Module.End.eigenspace (hodgeStar o rfl) 1

/-- The **anti-self-dual** middle-degree forms `Ω⁻`: the `-1` eigenspace of the Hodge star, the
forms with `⋆α = -α`. -/
def antiSelfDualForms : Submodule ℝ (RoughForm I M ℝ k) :=
  Module.End.eigenspace (hodgeStar o rfl) (-1)

variable {o} in
/-- A form is self-dual exactly when `⋆α = α`. -/
@[simp]
theorem mem_selfDualForms {α : RoughForm I M ℝ k} :
    α ∈ selfDualForms o ↔ hodgeStar o rfl α = α := by
  rw [selfDualForms, Module.End.mem_eigenspace_iff, one_smul]

variable {o} in
/-- A form is anti-self-dual exactly when `⋆α = -α`. -/
@[simp]
theorem mem_antiSelfDualForms {α : RoughForm I M ℝ k} :
    α ∈ antiSelfDualForms o ↔ hodgeStar o rfl α = -α := by
  rw [antiSelfDualForms, Module.End.mem_eigenspace_iff, neg_one_smul]

variable {o} in
/-- A rough middle-degree form is self-dual if and only if its value at every point lies in
`selfDualSubspace o x`. -/
theorem mem_selfDualForms_iff_forall_mem_selfDualSubspace {φ : RoughForm I M ℝ k} :
    φ ∈ selfDualForms o ↔ ∀ x, φ x ∈ selfDualSubspace o x := by
  simp [funext_iff, ← hodgeStar_eq_formHodgeStarCLM]

variable {o} in
/-- A rough middle-degree form is anti-self-dual if and only if its value at every point lies in
`antiSelfDualSubspace o x`. -/
theorem mem_antiSelfDualForms_iff_forall_mem_antiSelfDualSubspace {φ : RoughForm I M ℝ k} :
    φ ∈ antiSelfDualForms o ↔ ∀ x, φ x ∈ antiSelfDualSubspace o x := by
  simp [funext_iff, ← hodgeStar_eq_formHodgeStarCLM]

/-- The **self-dual part** `α⁺ = (α + ⋆α) / 2` of a middle-degree form. -/
def selfDualPart : RoughForm I M ℝ k →ₗ[ℝ] RoughForm I M ℝ k :=
  (2⁻¹ : ℝ) • (LinearMap.id + hodgeStar o rfl)

/-- The **anti-self-dual part** `α⁻ = (α - ⋆α) / 2` of a middle-degree form. -/
def antiSelfDualPart : RoughForm I M ℝ k →ₗ[ℝ] RoughForm I M ℝ k :=
  (2⁻¹ : ℝ) • (LinearMap.id - hodgeStar o rfl)

/-- The self-dual part as an explicit combination of `α` and `⋆α`. -/
theorem selfDualPart_apply (α : RoughForm I M ℝ k) :
    selfDualPart o α = (2⁻¹ : ℝ) • (α + hodgeStar o rfl α) :=
  (rfl)

/-- The anti-self-dual part as an explicit combination of `α` and `⋆α`. -/
theorem antiSelfDualPart_apply (α : RoughForm I M ℝ k) :
    antiSelfDualPart o α = (2⁻¹ : ℝ) • (α - hodgeStar o rfl α) :=
  (rfl)

/-- `RoughForm.selfDualPart` at `x` applies `selfDualProjCLM` to `φ x`. -/
theorem selfDualPart_eq_selfDualProjCLM (φ : RoughForm I M ℝ k) (x : M) :
    selfDualPart o φ x = selfDualProjCLM o x (φ x) := by
  simp [selfDualPart_apply, selfDualProjCLM_apply, formHodgeStarCLM_apply]

/-- `RoughForm.antiSelfDualPart` at `x` applies `antiSelfDualProjCLM` to `φ x`. -/
theorem antiSelfDualPart_eq_antiSelfDualProjCLM (φ : RoughForm I M ℝ k) (x : M) :
    antiSelfDualPart o φ x = antiSelfDualProjCLM o x (φ x) := by
  simp [antiSelfDualPart_apply, antiSelfDualProjCLM_apply, formHodgeStarCLM_apply]

/-- Reversing the orientation exchanges the self-dual and anti-self-dual parts. -/
@[simp]
theorem selfDualPart_neg_orientation (α : RoughForm I M ℝ k) :
    selfDualPart (-o) α = antiSelfDualPart o α := by
  rw [selfDualPart_apply, antiSelfDualPart_apply, hodgeStar_neg_orientation, sub_eq_add_neg]

/-- Reversing the orientation exchanges the anti-self-dual and self-dual parts. -/
@[simp]
theorem antiSelfDualPart_neg_orientation (α : RoughForm I M ℝ k) :
    antiSelfDualPart (-o) α = selfDualPart o α := by
  rw [← selfDualPart_neg_orientation, neg_neg]

/-- The self-dual part of a form is supported in the support of the form. -/
theorem tsupport_selfDualPart_subset (α : RoughForm I M ℝ k) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (selfDualPart o α) ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) α :=
  -- Supports are read in the model fibre; state the vanishing in the tangent fibre at `x`.
  closure_mono fun x hx hα ↦ hx
    (by simp [selfDualPart_apply, show α x = 0 from hα] : selfDualPart o α x = 0)

/-- The anti-self-dual part of a form is supported in the support of the form. -/
theorem tsupport_antiSelfDualPart_subset (α : RoughForm I M ℝ k) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (antiSelfDualPart o α) ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) α := by
  simpa only [selfDualPart_neg_orientation] using tsupport_selfDualPart_subset (-o) α

/-- A middle-degree form is the sum of its self-dual and anti-self-dual parts. -/
@[simp]
theorem selfDualPart_add_antiSelfDualPart (α : RoughForm I M ℝ k) :
    selfDualPart o α + antiSelfDualPart o α = α := by
  rw [selfDualPart_apply, antiSelfDualPart_apply]
  module

/-- The Hodge star of a middle-degree form is the difference of its self-dual and anti-self-dual
parts. -/
theorem selfDualPart_sub_antiSelfDualPart (α : RoughForm I M ℝ k) :
    selfDualPart o α - antiSelfDualPart o α = hodgeStar o rfl α := by
  rw [selfDualPart_apply, antiSelfDualPart_apply]
  module

/-- The self-dual part is self-dual: `⋆α⁺ = α⁺`. -/
@[simp]
theorem hodgeStar_selfDualPart (hk : Even k) (α : RoughForm I M ℝ k) :
    hodgeStar o rfl (selfDualPart o α) = selfDualPart o α := by
  rw [selfDualPart_apply, map_smul, map_add, hodgeStar_hodgeStar_of_even o hk, add_comm]

/-- The anti-self-dual part is anti-self-dual: `⋆α⁻ = -α⁻`. -/
@[simp]
theorem hodgeStar_antiSelfDualPart (hk : Even k) (α : RoughForm I M ℝ k) :
    hodgeStar o rfl (antiSelfDualPart o α) = -antiSelfDualPart o α := by
  rw [antiSelfDualPart_apply, map_smul, map_sub, hodgeStar_hodgeStar_of_even o hk]
  module

/-- `α ↦ (α + ⋆α) / 2` is a projection onto the self-dual forms. -/
theorem isProj_selfDualPart (hk : Even k) :
    LinearMap.IsProj (selfDualForms o) (selfDualPart o) where
  map_mem α := mem_selfDualForms.2 (hodgeStar_selfDualPart o hk α)
  map_id α hα := by
    rw [selfDualPart_apply, mem_selfDualForms.1 hα]
    module

/-- `α ↦ (α - ⋆α) / 2` is a projection onto the anti-self-dual forms. -/
theorem isProj_antiSelfDualPart (hk : Even k) :
    LinearMap.IsProj (antiSelfDualForms o) (antiSelfDualPart o) where
  map_mem α := mem_antiSelfDualForms.2 (hodgeStar_antiSelfDualPart o hk α)
  map_id α hα := by
    rw [antiSelfDualPart_apply, mem_antiSelfDualForms.1 hα]
    module

/-- Taking the self-dual part twice is taking it once. -/
@[simp]
theorem selfDualPart_selfDualPart (hk : Even k) (α : RoughForm I M ℝ k) :
    selfDualPart o (selfDualPart o α) = selfDualPart o α :=
  (isProj_selfDualPart o hk).map_id _ ((isProj_selfDualPart o hk).map_mem α)

/-- Taking the anti-self-dual part twice is taking it once. -/
@[simp]
theorem antiSelfDualPart_antiSelfDualPart (hk : Even k) (α : RoughForm I M ℝ k) :
    antiSelfDualPart o (antiSelfDualPart o α) = antiSelfDualPart o α :=
  (isProj_antiSelfDualPart o hk).map_id _ ((isProj_antiSelfDualPart o hk).map_mem α)

/-- The self-dual part of a form vanishes exactly when the form is anti-self-dual. -/
@[simp]
theorem ker_selfDualPart : LinearMap.ker (selfDualPart o) = antiSelfDualForms o := by
  ext α
  rw [LinearMap.mem_ker, selfDualPart_apply, mem_antiSelfDualForms, smul_eq_zero,
    eq_neg_iff_add_eq_zero, add_comm (hodgeStar o rfl α)]
  simp

/-- The anti-self-dual part of a form vanishes exactly when the form is self-dual. -/
@[simp]
theorem ker_antiSelfDualPart : LinearMap.ker (antiSelfDualPart o) = selfDualForms o := by
  ext α
  rw [LinearMap.mem_ker, antiSelfDualPart_apply, mem_selfDualForms, smul_eq_zero, sub_eq_zero,
    eq_comm (b := α)]
  simp

/-- The anti-self-dual part of a form has no self-dual part. -/
@[simp]
theorem selfDualPart_antiSelfDualPart (hk : Even k) (α : RoughForm I M ℝ k) :
    selfDualPart o (antiSelfDualPart o α) = 0 := by
  rw [← LinearMap.mem_ker, ker_selfDualPart]
  exact (isProj_antiSelfDualPart o hk).map_mem α

/-- The self-dual part of a form has no anti-self-dual part. -/
@[simp]
theorem antiSelfDualPart_selfDualPart (hk : Even k) (α : RoughForm I M ℝ k) :
    antiSelfDualPart o (selfDualPart o α) = 0 := by
  rw [← LinearMap.mem_ker, ker_antiSelfDualPart]
  exact (isProj_selfDualPart o hk).map_mem α

/-- **The splitting `Ω⁺ ⊕ Ω⁻`**: in an even middle degree, the self-dual and anti-self-dual forms
are complementary. -/
theorem isCompl_selfDualForms_antiSelfDualForms (hk : Even k) :
    IsCompl (selfDualForms o) (antiSelfDualForms o) := by
  simpa using (isProj_selfDualPart o hk).isCompl

/-! ### Pointwise orthogonality and the wedge square -/

/-- Self-dual and anti-self-dual forms are pointwise orthogonal. -/
theorem alternatingFormInner_eq_zero_of_mem_selfDualForms
    {α β : RoughForm I M ℝ k} (hα : α ∈ selfDualForms o) (hβ : β ∈ antiSelfDualForms o)
    (x : M) : alternatingFormInner (TangentSpace I x) k (α x) (β x) = 0 :=
  alternatingFormInner_eq_zero_of_mem_selfDualSubspace_of_mem_antiSelfDualSubspace o
    (mem_selfDualForms_iff_forall_mem_selfDualSubspace.mp hα x)
    (mem_antiSelfDualForms_iff_forall_mem_antiSelfDualSubspace.mp hβ x)

/-- The self-dual and anti-self-dual parts of two forms are pointwise orthogonal. -/
theorem alternatingFormInner_selfDualPart_antiSelfDualPart (hk : Even k)
    (α β : RoughForm I M ℝ k) (x : M) :
    alternatingFormInner (TangentSpace I x) k (selfDualPart o α x) (antiSelfDualPart o β x) =
      0 :=
  alternatingFormInner_eq_zero_of_mem_selfDualForms o ((isProj_selfDualPart o hk).map_mem α)
    ((isProj_antiSelfDualPart o hk).map_mem β) x

/-- Pairing with a self-dual form sees only the self-dual part: `⟨α⁺, γ⟩ = ⟨α, γ⟩` at every
point. -/
theorem alternatingFormInner_selfDualPart_of_mem_selfDualForms (hk : Even k)
    (α : RoughForm I M ℝ k) {γ : RoughForm I M ℝ k} (hγ : γ ∈ selfDualForms o) (x : M) :
    alternatingFormInner (TangentSpace I x) k (selfDualPart o α x) (γ x) =
      alternatingFormInner (TangentSpace I x) k (α x) (γ x) := by
  have h := alternatingFormInner_eq_zero_of_mem_selfDualForms o hγ
    ((isProj_antiSelfDualPart o hk).map_mem α) x
  rw [alternatingFormInner_comm] at h
  conv_rhs => rw [← selfDualPart_add_antiSelfDualPart o α]
  rw [Pi.add_apply, map_add, LinearMap.add_apply, h, add_zero]

/-- Pairing with an anti-self-dual form sees only the anti-self-dual part: `⟨α⁻, γ⟩ = ⟨α, γ⟩` at
every point. -/
theorem alternatingFormInner_antiSelfDualPart_of_mem_antiSelfDualForms (hk : Even k)
    (α : RoughForm I M ℝ k) {γ : RoughForm I M ℝ k} (hγ : γ ∈ antiSelfDualForms o) (x : M) :
    alternatingFormInner (TangentSpace I x) k (antiSelfDualPart o α x) (γ x) =
      alternatingFormInner (TangentSpace I x) k (α x) (γ x) := by
  have h := alternatingFormInner_eq_zero_of_mem_selfDualForms o
    ((isProj_selfDualPart o hk).map_mem α) hγ x
  conv_rhs => rw [← selfDualPart_add_antiSelfDualPart o α]
  rw [Pi.add_apply, map_add, LinearMap.add_apply, h, zero_add]

/-- **Pointwise energy identity under `(1 ± ⋆) / 2`**: `|α|² = |α⁺|² + |α⁻|²` at every point and in
every middle degree `k` (Pythagoras for the orthogonal splitting `Ω⁺ ⊕ Ω⁻` when `k` is even). -/
theorem alternatingFormInner_self_eq_add (α : RoughForm I M ℝ k) (x : M) :
    alternatingFormInner (TangentSpace I x) k (α x) (α x) =
      alternatingFormInner (TangentSpace I x) k (selfDualPart o α x) (selfDualPart o α x) +
        alternatingFormInner (TangentSpace I x) k (antiSelfDualPart o α x)
          (antiSelfDualPart o α x) := by
  rw [selfDualPart_eq_selfDualProjCLM, antiSelfDualPart_eq_antiSelfDualProjCLM]
  exact alternatingFormInner_eq_add_selfDualProjCLM_antiSelfDualProjCLM o x (α x) (α x)

/-- **The wedge square of a middle-degree form**: `α ∧ α = (|α⁺|² - |α⁻|²) vol`, where `vol` is
the Riemannian volume form. -/
theorem wedge_self_apply (hk : Even k) (α : RoughForm I M ℝ k) (x : M)
    (v : Fin (k + k) → TangentSpace I x) :
    α.wedge α x v =
      (alternatingFormInner (TangentSpace I x) k (selfDualPart o α x) (selfDualPart o α x) -
        alternatingFormInner (TangentSpace I x) k (antiSelfDualPart o α x)
          (antiSelfDualPart o α x)) * riemannianVolumeForm o x v := by
  -- Write the second factor as `⋆(⋆α)`, so that `α ∧ ⋆(⋆α) = ⟨α, ⋆α⟩ vol`.
  have hw : α.wedge α x v = (α x).wedge (hodgeStar o rfl (hodgeStar o rfl α) x) v := by
    rw [hodgeStar_hodgeStar_of_even o hk, wedge_def, wedgeWith_apply',
      ContinuousAlternatingMap.wedge_def]
  rw [hw, wedge_hodgeStar_apply, finCongr_refl, Equiv.coe_refl, Function.comp_id]
  congr 1
  -- Then `⟨α⁺ + α⁻, α⁺ - α⁻⟩ = |α⁺|² - |α⁻|²` by orthogonality.
  have h := alternatingFormInner_selfDualPart_antiSelfDualPart o hk α α x
  rw [alternatingFormInner_comm] at h
  have hα : α x = selfDualPart o α x + antiSelfDualPart o α x := by
    rw [← Pi.add_apply, selfDualPart_add_antiSelfDualPart]
  have hs : hodgeStar o rfl α x = selfDualPart o α x - antiSelfDualPart o α x := by
    rw [← Pi.sub_apply, selfDualPart_sub_antiSelfDualPart]
  rw [hs, hα]
  simp only [map_add, map_sub, LinearMap.add_apply, h,
    alternatingFormInner_selfDualPart_antiSelfDualPart o hk]
  ring

/-! ### The fibres of `Λ⁺` and `Λ⁻` -/

/-- The fibre of `Λ⁺` at `x`: the values at `x` of the self-dual forms make up
`selfDualSubspace o x`. -/
theorem map_proj_selfDualForms (x : M) :
    (selfDualForms o).map (LinearMap.proj x) = selfDualSubspace o x := by
  classical
  ext a
  simp only [Submodule.mem_map, mem_selfDualForms_iff_forall_mem_selfDualSubspace,
    LinearMap.coe_proj, Function.eval]
  refine ⟨by rintro ⟨α, hα, rfl⟩; exact hα x, fun ha ↦ ⟨Pi.single x a, fun y ↦ ?_, by simp⟩⟩
  rcases eq_or_ne y x with rfl | hy
  · simpa using ha
  · simp [Pi.single_eq_of_ne hy]

/-- The fibre of `Λ⁻` at `x`: the values at `x` of the anti-self-dual forms make up
`antiSelfDualSubspace o x`. -/
theorem map_proj_antiSelfDualForms (x : M) :
    (antiSelfDualForms o).map (LinearMap.proj x) = antiSelfDualSubspace o x := by
  classical
  ext a
  simp only [Submodule.mem_map, mem_antiSelfDualForms_iff_forall_mem_antiSelfDualSubspace,
    LinearMap.coe_proj, Function.eval]
  refine ⟨by rintro ⟨α, hα, rfl⟩; exact hα x, fun ha ↦ ⟨Pi.single x a, fun y ↦ ?_, by simp⟩⟩
  rcases eq_or_ne y x with rfl | hy
  · simpa using ha
  · simp [Pi.single_eq_of_ne hy]

end RoughForm

/-! ### Smooth forms -/

section Smooth

variable {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]

/-- The self-dual part of a `C^n` form is `C^n`, for a `C^n` metric on a `C^(n+1)` manifold. -/
theorem IsSmoothForm.selfDualPart {α : RoughForm I M ℝ k} (hα : IsSmoothForm I n α) :
    IsSmoothForm I n (RoughForm.selfDualPart o α) :=
  (hα.add (hα.hodgeStar o rfl)).smul _

/-- The anti-self-dual part of a `C^n` form is `C^n`, for a `C^n` metric on a `C^(n+1)`
manifold. -/
theorem IsSmoothForm.antiSelfDualPart {α : RoughForm I M ℝ k} (hα : IsSmoothForm I n α) :
    IsSmoothForm I n (RoughForm.antiSelfDualPart o α) := by
  rw [RoughForm.antiSelfDualPart_apply, sub_eq_add_neg]
  exact (hα.add (hα.hodgeStar o rfl).neg).smul _

end Smooth

namespace SmoothForm

variable [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The self-dual part `α⁺ = (α + ⋆α) / 2` of a smooth middle-degree form. -/
def selfDualPart : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ k :=
  haveI : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  (RoughForm.selfDualPart o).restrict fun α hα ↦
    ((SmoothForm.isSmoothForm ⟨α, hα⟩).selfDualPart o).mem_smoothBundleForms

/-- The anti-self-dual part `α⁻ = (α - ⋆α) / 2` of a smooth middle-degree form. -/
def antiSelfDualPart : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ k :=
  haveI : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  (RoughForm.antiSelfDualPart o).restrict fun α hα ↦
    ((SmoothForm.isSmoothForm ⟨α, hα⟩).antiSelfDualPart o).mem_smoothBundleForms

/-- The self-dual part of a smooth form is that of the underlying rough form. -/
@[simp]
theorem coe_selfDualPart (α : SmoothForm I M ℝ k) :
    (selfDualPart o α : RoughForm I M ℝ k) = RoughForm.selfDualPart o α :=
  (rfl)

/-- The anti-self-dual part of a smooth form is that of the underlying rough form. -/
@[simp]
theorem coe_antiSelfDualPart (α : SmoothForm I M ℝ k) :
    (antiSelfDualPart o α : RoughForm I M ℝ k) = RoughForm.antiSelfDualPart o α :=
  (rfl)

/-- A smooth middle-degree form is the sum of its self-dual and anti-self-dual parts. -/
@[simp]
theorem selfDualPart_add_antiSelfDualPart (α : SmoothForm I M ℝ k) :
    selfDualPart o α + antiSelfDualPart o α = α :=
  Subtype.ext (RoughForm.selfDualPart_add_antiSelfDualPart o α)

/-- The self-dual part of a smooth form is self-dual: `⋆α⁺ = α⁺`. -/
@[simp]
theorem hodgeStar_selfDualPart (hk : Even k) (α : SmoothForm I M ℝ k) :
    hodgeStar o rfl (selfDualPart o α) = selfDualPart o α :=
  Subtype.ext <| by
    rw [coe_hodgeStar, coe_selfDualPart, RoughForm.hodgeStar_selfDualPart o hk]

/-- The anti-self-dual part of a smooth form is anti-self-dual: `⋆α⁻ = -α⁻`. -/
@[simp]
theorem hodgeStar_antiSelfDualPart (hk : Even k) (α : SmoothForm I M ℝ k) :
    hodgeStar o rfl (antiSelfDualPart o α) = -antiSelfDualPart o α :=
  Subtype.ext <| by
    rw [coe_hodgeStar, coe_antiSelfDualPart, RoughForm.hodgeStar_antiSelfDualPart o hk,
      Submodule.coe_neg, coe_antiSelfDualPart]

/-- Taking the self-dual part of a smooth form twice is taking it once. -/
@[simp]
theorem selfDualPart_selfDualPart (hk : Even k) (α : SmoothForm I M ℝ k) :
    selfDualPart o (selfDualPart o α) = selfDualPart o α :=
  Subtype.ext <| by
    rw [coe_selfDualPart, coe_selfDualPart, RoughForm.selfDualPart_selfDualPart o hk]

/-- Taking the anti-self-dual part of a smooth form twice is taking it once. -/
@[simp]
theorem antiSelfDualPart_antiSelfDualPart (hk : Even k) (α : SmoothForm I M ℝ k) :
    antiSelfDualPart o (antiSelfDualPart o α) = antiSelfDualPart o α :=
  Subtype.ext <| by
    rw [coe_antiSelfDualPart, coe_antiSelfDualPart,
      RoughForm.antiSelfDualPart_antiSelfDualPart o hk]

/-- The anti-self-dual part of a smooth form has no self-dual part. -/
@[simp]
theorem selfDualPart_antiSelfDualPart (hk : Even k) (α : SmoothForm I M ℝ k) :
    selfDualPart o (antiSelfDualPart o α) = 0 :=
  Subtype.ext <| by
    rw [coe_selfDualPart, coe_antiSelfDualPart, RoughForm.selfDualPart_antiSelfDualPart o hk,
      Submodule.coe_zero]

/-- The self-dual part of a smooth form has no anti-self-dual part. -/
@[simp]
theorem antiSelfDualPart_selfDualPart (hk : Even k) (α : SmoothForm I M ℝ k) :
    antiSelfDualPart o (selfDualPart o α) = 0 :=
  Subtype.ext <| by
    rw [coe_antiSelfDualPart, coe_selfDualPart, RoughForm.antiSelfDualPart_selfDualPart o hk,
      Submodule.coe_zero]

/-- Reversing the orientation exchanges the self-dual and anti-self-dual parts of smooth forms. -/
@[simp]
theorem selfDualPart_neg_orientation (α : SmoothForm I M ℝ k) :
    selfDualPart (-o) α = antiSelfDualPart o α :=
  Subtype.ext (RoughForm.selfDualPart_neg_orientation o α)

/-- Reversing the orientation exchanges the anti-self-dual and self-dual parts of smooth forms. -/
@[simp]
theorem antiSelfDualPart_neg_orientation (α : SmoothForm I M ℝ k) :
    antiSelfDualPart (-o) α = selfDualPart o α :=
  Subtype.ext (RoughForm.antiSelfDualPart_neg_orientation o α)

/-- The **self-dual** smooth middle-degree forms `Ω⁺`: the `+1` eigenspace of the Hodge star, the
smooth forms with `⋆α = α`. -/
def selfDualForms : Submodule ℝ (SmoothForm I M ℝ k) :=
  Module.End.eigenspace (hodgeStar o rfl) 1

instance instAddCommGroupSelfDualForms : AddCommGroup (selfDualForms o) :=
  Submodule.addCommGroup _

instance instModuleSelfDualForms : Module ℝ (selfDualForms o) :=
  Submodule.module _

/-- The **anti-self-dual** smooth middle-degree forms `Ω⁻`: the `-1` eigenspace of the Hodge star,
the smooth forms with `⋆α = -α`. -/
def antiSelfDualForms : Submodule ℝ (SmoothForm I M ℝ k) :=
  Module.End.eigenspace (hodgeStar o rfl) (-1)

variable {o} in
/-- A smooth form is self-dual exactly when `⋆α = α`. -/
@[simp]
theorem mem_selfDualForms {α : SmoothForm I M ℝ k} :
    α ∈ selfDualForms o ↔ hodgeStar o rfl α = α := by
  rw [selfDualForms, Module.End.mem_eigenspace_iff, one_smul]

/-- A smooth self-dual form of positive middle degree is coclosed exactly when it is closed. -/
theorem codifferential_eq_zero_iff_mextDeriv_eq_zero_of_mem_selfDualForms
    (o : Manifold.Orientation I M (Fin ((k + 1) + (k + 1))))
    {γ : SmoothForm I M ℝ (k + 1)} (hγ : γ ∈ selfDualForms o) :
    codifferential o rfl γ = 0 ↔ mextDerivₗ I (k + 1) γ = 0 := by
  have hstar := mem_selfDualForms.mp hγ
  constructor
  · intro h
    -- The sign in ⋆d*γ = (-1)^(k+1) d⋆γ is nonzero, and ⋆γ = γ.
    have hs := hodgeStar_codifferential o rfl (by omega) γ
    rw [h, map_zero, hstar] at hs
    exact (smul_eq_zero.mp hs.symm).resolve_left (pow_ne_zero _ (by norm_num))
  · intro h
    simp [codifferential_apply o rfl (by omega), hstar, h]

variable {o} in
/-- A smooth form is anti-self-dual exactly when `⋆α = -α`. -/
@[simp]
theorem mem_antiSelfDualForms {α : SmoothForm I M ℝ k} :
    α ∈ antiSelfDualForms o ↔ hodgeStar o rfl α = -α := by
  rw [antiSelfDualForms, Module.End.mem_eigenspace_iff, neg_one_smul]

variable {o} in
/-- A smooth form is self-dual exactly when it is self-dual as a rough form. -/
theorem coe_mem_selfDualForms_iff {α : SmoothForm I M ℝ k} :
    (α : RoughForm I M ℝ k) ∈ RoughForm.selfDualForms o ↔ α ∈ selfDualForms o := by
  rw [RoughForm.mem_selfDualForms, mem_selfDualForms, ← coe_hodgeStar, SetLike.coe_eq_coe]

variable {o} in
/-- A smooth form is anti-self-dual exactly when it is anti-self-dual as a rough form. -/
theorem coe_mem_antiSelfDualForms_iff {α : SmoothForm I M ℝ k} :
    (α : RoughForm I M ℝ k) ∈ RoughForm.antiSelfDualForms o ↔ α ∈ antiSelfDualForms o := by
  rw [RoughForm.mem_antiSelfDualForms, mem_antiSelfDualForms, ← coe_hodgeStar,
    ← Submodule.coe_neg, SetLike.coe_eq_coe]

/-- The self-dual part of a smooth form is self-dual. -/
theorem selfDualPart_mem_selfDualForms (hk : Even k) (α : SmoothForm I M ℝ k) :
    selfDualPart o α ∈ selfDualForms o :=
  mem_selfDualForms.2 (hodgeStar_selfDualPart o hk α)

/-- The anti-self-dual part of a smooth form is anti-self-dual. -/
theorem antiSelfDualPart_mem_antiSelfDualForms (hk : Even k) (α : SmoothForm I M ℝ k) :
    antiSelfDualPart o α ∈ antiSelfDualForms o :=
  mem_antiSelfDualForms.2 (hodgeStar_antiSelfDualPart o hk α)

/-- `α ↦ (α + ⋆α) / 2` is a projection of smooth forms onto the smooth self-dual forms. -/
theorem isProj_selfDualPart (hk : Even k) :
    LinearMap.IsProj (selfDualForms o) (selfDualPart o) where
  map_mem := selfDualPart_mem_selfDualForms o hk
  map_id _ hα := Subtype.ext <|
    (RoughForm.isProj_selfDualPart o hk).map_id _ (coe_mem_selfDualForms_iff.2 hα)

/-- `α ↦ (α - ⋆α) / 2` is a projection of smooth forms onto the smooth anti-self-dual forms. -/
theorem isProj_antiSelfDualPart (hk : Even k) :
    LinearMap.IsProj (antiSelfDualForms o) (antiSelfDualPart o) where
  map_mem := antiSelfDualPart_mem_antiSelfDualForms o hk
  map_id _ hα := Subtype.ext <|
    (RoughForm.isProj_antiSelfDualPart o hk).map_id _ (coe_mem_antiSelfDualForms_iff.2 hα)

/-- The self-dual part of a smooth form vanishes exactly when the form is anti-self-dual. -/
@[simp]
theorem ker_selfDualPart :
    LinearMap.ker (selfDualPart o) = antiSelfDualForms (I := I) (M := M) o := by
  ext α
  rw [LinearMap.mem_ker, ← coe_mem_antiSelfDualForms_iff, ← RoughForm.ker_selfDualPart,
    LinearMap.mem_ker, ← coe_selfDualPart, ZeroMemClass.coe_eq_zero]

/-- The anti-self-dual part of a smooth form vanishes exactly when the form is self-dual. -/
@[simp]
theorem ker_antiSelfDualPart :
    LinearMap.ker (antiSelfDualPart o) = selfDualForms (I := I) (M := M) o := by
  ext α
  rw [LinearMap.mem_ker, ← coe_mem_selfDualForms_iff, ← RoughForm.ker_antiSelfDualPart,
    LinearMap.mem_ker, ← coe_antiSelfDualPart, ZeroMemClass.coe_eq_zero]

/-- `SmoothForm.selfDualPart` commutes with right multiplication by a smooth zero-form. -/
theorem selfDualPart_wedge_zero_right (φ : SmoothForm I M ℝ k) (f : SmoothForm I M ℝ 0) :
    selfDualPart o (wedge φ f) = wedge (selfDualPart o φ) f := by
  apply Subtype.ext
  funext x
  ext v
  simp only [coe_selfDualPart, RoughForm.selfDualPart_apply, wedge_apply_zero_right,
    Pi.smul_apply, Pi.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, smul_eq_mul]
  have hh := congrArg (fun ψ : SmoothForm I M ℝ k ↦ ψ.1 x v)
    (hodgeStar_wedge_zero_right o rfl φ f)
  simp only [coe_hodgeStar, wedge_apply_zero_right] at hh
  rw [hh]
  ring

/-- Under `alternatingFormEquiv`, `SmoothForm.selfDualPart` acts fibrewise as `(1 / 2) (y + ⋆y)` on
`⋀ᵏ T_x M`. -/
theorem alternatingFormEquiv_symm_selfDualPart (η : SmoothForm I M ℝ k) (x : M) :
    (letI := o.fact_finrank_tangentSpace x
     (alternatingFormEquiv (TangentSpace I x) k).symm ((selfDualPart o η).1 x)) =
      (letI := o.fact_finrank_tangentSpace x
       (2⁻¹ : ℝ) • ((alternatingFormEquiv (TangentSpace I x) k).symm (η.1 x) +
         (o.orientationAt x).hodgeStar (o.fact_finrank_tangentSpace x).out.symm
           ((alternatingFormEquiv (TangentSpace I x) k).symm (η.1 x)))) := by
  let _ := o.fact_finrank_tangentSpace x
  apply (alternatingFormEquiv (TangentSpace I x) k).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, map_add,
    ← (o.orientationAt x).formHodgeStar_alternatingFormEquiv, LinearEquiv.apply_symm_apply,
    coe_selfDualPart, RoughForm.selfDualPart_apply, Pi.smul_apply, Pi.add_apply,
    RoughForm.hodgeStar_apply]

/-- Every smooth self-dual `k`-form `η ∈ selfDualForms o` corresponds at `x` to a self-dual
`k`-vector under `alternatingFormEquiv`. -/
theorem hodgeStar_alternatingFormEquiv_symm_of_mem_selfDualForms
    {η : SmoothForm I M ℝ k} (hη : η ∈ selfDualForms o) (x : M) :
    (letI := o.fact_finrank_tangentSpace x
     (o.orientationAt x).hodgeStar (o.fact_finrank_tangentSpace x).out.symm
       ((alternatingFormEquiv (TangentSpace I x) k).symm (η.1 x))) =
      (letI := o.fact_finrank_tangentSpace x
       (alternatingFormEquiv (TangentSpace I x) k).symm (η.1 x)) := by
  let _ := o.fact_finrank_tangentSpace x
  apply (alternatingFormEquiv (TangentSpace I x) k).injective
  rw [← (o.orientationAt x).formHodgeStar_alternatingFormEquiv, LinearEquiv.apply_symm_apply]
  simpa only [coe_hodgeStar, RoughForm.hodgeStar_apply] using
    congrArg (fun ψ : SmoothForm I M ℝ k ↦ ψ.1 x) (mem_selfDualForms.1 hη)

/-- The self-dual part of a compactly supported smooth form is compactly supported. -/
theorem selfDualPart_mem_compactlySupportedForms {α : SmoothForm I M ℝ k}
    (hα : α ∈ compactlySupportedForms I M k) :
    selfDualPart o α ∈ compactlySupportedForms I M k :=
  (mem_compactlySupportedForms I).mpr (((mem_compactlySupportedForms I).mp hα).of_isClosed_subset
    (_root_.isClosed_tsupport _) (RoughForm.tsupport_selfDualPart_subset o α.1))

/-- The anti-self-dual part of a compactly supported smooth form is compactly supported. -/
theorem antiSelfDualPart_mem_compactlySupportedForms {α : SmoothForm I M ℝ k}
    (hα : α ∈ compactlySupportedForms I M k) :
    antiSelfDualPart o α ∈ compactlySupportedForms I M k := by
  simpa only [selfDualPart_neg_orientation] using selfDualPart_mem_compactlySupportedForms (-o) hα

/-! ### Integrated energies -/

/-- **`L²` energy identity under `(1 ± ⋆) / 2`**: on an oriented Riemannian manifold of dimension
`k + k`, a compactly supported smooth `k`-form `α` has
`∫_M |α|² vol = ∫_M |α⁺|² vol + ∫_M |α⁻|² vol` (the orthogonal `L²` splitting across `Ω⁺ ⊕ Ω⁻`
when `k` is even). -/
theorem integralTopForm_inner_self_smul_riemannianVolumeForm_eq_add
    {α : SmoothForm I M ℝ k} (hα : α ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (α.1 x) (α.1 x) •
        riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((selfDualPart o α).1 x) ((selfDualPart o α).1 x) • riemannianVolumeForm o x) +
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((antiSelfDualPart o α).1 x) ((antiSelfDualPart o α).1 x) • riemannianVolumeForm o x) := by
  have hsplit : (fun x ↦ alternatingFormInner (TangentSpace I x) k (α.1 x) (α.1 x) •
        riemannianVolumeForm o x) =
      (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((selfDualPart o α).1 x) ((selfDualPart o α).1 x) • riemannianVolumeForm o x) +
      fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((antiSelfDualPart o α).1 x) ((antiSelfDualPart o α).1 x) • riemannianVolumeForm o x := by
    funext x
    rw [RoughForm.alternatingFormInner_self_eq_add o, add_smul, Pi.add_apply,
      coe_selfDualPart, coe_antiSelfDualPart]
  rw [hsplit, integralTopForm_add o
    ((isSmoothForm_inner_smul_riemannianVolumeForm o rfl _ _).of_le bot_le)
    ((isSmoothForm_inner_smul_riemannianVolumeForm o rfl _ _).of_le bot_le)
    (RoughForm.isCompact_tsupport_inner_smul_riemannianVolumeForm o _ _
      ((mem_compactlySupportedForms I).mp (selfDualPart_mem_compactlySupportedForms o hα)))
    (RoughForm.isCompact_tsupport_inner_smul_riemannianVolumeForm o _ _
      ((mem_compactlySupportedForms I).mp (antiSelfDualPart_mem_compactlySupportedForms o hα)))]

/-- **The integral of a wedge square**: on an oriented Riemannian manifold of dimension `k + k`
with `k` even, a compactly supported smooth `k`-form `α` has
`∫_M α ∧ α = ∫_M |α⁺|² vol - ∫_M |α⁻|² vol`. -/
theorem integralTopForm_wedge_self (hk : Even k) {α : SmoothForm I M ℝ k}
    (hα : α ∈ compactlySupportedForms I M k) :
    integralTopForm o (RoughForm.wedge α.1 α.1) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((selfDualPart o α).1 x) ((selfDualPart o α).1 x) • riemannianVolumeForm o x) -
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((antiSelfDualPart o α).1 x) ((antiSelfDualPart o α).1 x) • riemannianVolumeForm o x) := by
  -- `|α⁺|² vol = α ∧ α + |α⁻|² vol` pointwise.
  have hsplit : (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((selfDualPart o α).1 x) ((selfDualPart o α).1 x) • riemannianVolumeForm o x) =
      RoughForm.wedge α.1 α.1 + fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((antiSelfDualPart o α).1 x) ((antiSelfDualPart o α).1 x) • riemannianVolumeForm o x := by
    funext x
    ext v
    simp only [RoughForm.wedge_self_apply o hk, coe_selfDualPart, coe_antiSelfDualPart,
      Pi.add_apply, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    ring
  have hw := (mem_compactlySupportedForms I).mp (wedge_mem_compactlySupportedForms α hα)
  rw [coe_wedge] at hw
  have hsw : IsSmoothForm I 0 (RoughForm.wedge α.1 α.1) := by
    simpa only [coe_wedge] using (wedge α α).isSmoothForm.of_le (by simp)
  rw [hsplit, integralTopForm_add o hsw
      ((isSmoothForm_inner_smul_riemannianVolumeForm o rfl _ _).of_le bot_le) hw
      (RoughForm.isCompact_tsupport_inner_smul_riemannianVolumeForm o _ _
        ((mem_compactlySupportedForms I).mp (antiSelfDualPart_mem_compactlySupportedForms o hα))),
    add_sub_cancel_right]

/-! ### Closed and exact forms on a boundaryless manifold -/

section Exact

variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **Chern–Weil invariance of the energy difference**: on an oriented boundaryless Riemannian
manifold of dimension `k + k` with `k` even, compactly supported closed `k`-forms `φ` and `ψ` whose
difference is exact satisfy
`∫_M |ψ⁺|² vol - ∫_M |ψ⁻|² vol = ∫_M |φ⁺|² vol - ∫_M |φ⁻|² vol`.
Both sides are the topological quantities `∫_M ψ ∧ ψ = ∫_M φ ∧ φ`. For the curvature forms of
two connections on a line bundle over a closed four-manifold, this fixes the anti-self-dual
energy of either curvature by its self-dual energy and a characteristic number. -/
theorem integralTopForm_inner_selfDualPart_sub_inner_antiSelfDualPart_eq_of_sub_mem_exactForms
    (hk : Even k) {φ ψ : SmoothForm I M ℝ k} (hφ : φ ∈ compactlySupportedClosedForms I M k)
    (hψ : ψ ∈ compactlySupportedClosedForms I M k) (hψφ : ψ - φ ∈ exactForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((selfDualPart o ψ).1 x) ((selfDualPart o ψ).1 x) • riemannianVolumeForm o x) -
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((antiSelfDualPart o ψ).1 x) ((antiSelfDualPart o ψ).1 x) • riemannianVolumeForm o x) =
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((selfDualPart o φ).1 x) ((selfDualPart o φ).1 x) • riemannianVolumeForm o x) -
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((antiSelfDualPart o φ).1 x) ((antiSelfDualPart o φ).1 x) • riemannianVolumeForm o x) := by
  rw [← integralTopForm_wedge_self o hk ((mem_compactlySupportedClosedForms I).mp hψ).1,
    ← integralTopForm_wedge_self o hk ((mem_compactlySupportedClosedForms I).mp hφ).1]
  exact integralTopForm_wedge_self_eq_of_sub_mem_exactForms o hk hφ hψ hψφ

/-- **The energy of a closed form from its self-dual energy**: on an oriented boundaryless
Riemannian manifold of dimension `k + k` with `k` even, compactly supported closed `k`-forms `φ`
and `ψ` whose difference is exact satisfy
`∫_M |ψ|² vol = 2 ∫_M |ψ⁺|² vol - (∫_M |φ⁺|² vol - ∫_M |φ⁻|² vol)`.
With `φ` a fixed reference curvature, a bound on the self-dual energy of the curvature `ψ` of a
connection on the same line bundle therefore bounds its whole energy. -/
theorem integralTopForm_inner_self_smul_riemannianVolumeForm_eq_two_mul_sub (hk : Even k)
    {φ ψ : SmoothForm I M ℝ k} (hφ : φ ∈ compactlySupportedClosedForms I M k)
    (hψ : ψ ∈ compactlySupportedClosedForms I M k) (hψφ : ψ - φ ∈ exactForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (ψ.1 x) (ψ.1 x) •
        riemannianVolumeForm o x) =
      2 * integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((selfDualPart o ψ).1 x) ((selfDualPart o ψ).1 x) • riemannianVolumeForm o x) -
      (integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((selfDualPart o φ).1 x) ((selfDualPart o φ).1 x) • riemannianVolumeForm o x) -
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((antiSelfDualPart o φ).1 x) ((antiSelfDualPart o φ).1 x) • riemannianVolumeForm o x)) := by
  rw [integralTopForm_inner_self_smul_riemannianVolumeForm_eq_add o
      ((mem_compactlySupportedClosedForms I).mp hψ).1,
    ← integralTopForm_inner_selfDualPart_sub_inner_antiSelfDualPart_eq_of_sub_mem_exactForms
      o hk hφ hψ hψφ]
  ring

/-- **The self-dual and anti-self-dual parts of an exact form have equal energy**: on an oriented
boundaryless Riemannian manifold of dimension `k + k` with `k` even, a compactly supported exact
`k`-form `β` satisfies `∫_M |β⁺|² vol = ∫_M |β⁻|² vol`. -/
theorem integralTopForm_inner_selfDualPart_eq_inner_antiSelfDualPart (hk : Even k)
    {β : SmoothForm I M ℝ k} (hβ : β ∈ exactForms I M k)
    (hc : β ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((selfDualPart o β).1 x) ((selfDualPart o β).1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((antiSelfDualPart o β).1 x) ((antiSelfDualPart o β).1 x) • riemannianVolumeForm o x) := by
  -- Compare `β` with the zero form, whose energies vanish.
  have h := integralTopForm_inner_selfDualPart_sub_inner_antiSelfDualPart_eq_of_sub_mem_exactForms
    o hk (zero_mem _)
    ((mem_compactlySupportedClosedForms I).mpr ⟨hc, exactForms_le_closedForms I k hβ⟩)
    (by rwa [sub_zero])
  simpa only [coe_selfDualPart, coe_antiSelfDualPart, map_zero, ZeroMemClass.coe_zero,
    Pi.zero_apply, LinearMap.zero_apply, zero_smul, sub_self, sub_eq_zero] using h

/-- On an oriented boundaryless Riemannian manifold of dimension `k + k` with `k` even, a compactly
supported exact `k`-form whose self-dual part vanishes is zero. In particular on a
closed four-manifold a one-form `a` with `(da)⁺ = 0` is closed. -/
theorem eq_zero_of_selfDualPart_eq_zero (hk : Even k)
    {β : SmoothForm I M ℝ k} (hβ : β ∈ exactForms I M k)
    (hc : β ∈ compactlySupportedForms I M k) (h : selfDualPart o β = 0) : β = 0 := by
  -- In degree zero only the zero form is exact.
  obtain rfl | hk₀ := k.eq_zero_or_pos
  · simpa using hβ
  have : NeZero (k + k) := ⟨by omega⟩
  have h0 := (integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff o rfl
    (h ▸ Submodule.zero_mem _)).mpr h
  rw [integralTopForm_inner_selfDualPart_eq_inner_antiSelfDualPart o hk hβ hc,
    integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff o rfl
      (antiSelfDualPart_mem_compactlySupportedForms o hc)] at h0
  rw [← selfDualPart_add_antiSelfDualPart o β, h, h0, add_zero]

/-- On an oriented boundaryless Riemannian manifold of dimension `k + k` with `k` even, a compactly
supported exact `k`-form whose anti-self-dual part vanishes is zero. -/
theorem eq_zero_of_antiSelfDualPart_eq_zero (hk : Even k)
    {β : SmoothForm I M ℝ k} (hβ : β ∈ exactForms I M k)
    (hc : β ∈ compactlySupportedForms I M k) (h : antiSelfDualPart o β = 0) : β = 0 :=
  eq_zero_of_selfDualPart_eq_zero (-o) hk hβ hc (by rwa [selfDualPart_neg_orientation])

/-- **The self-dual part of an exact form is orthogonal to the closed self-dual forms**: on an
oriented boundaryless Riemannian manifold of dimension `k + k` with `k` even, for an exact
`k`-form `β` and a compactly supported closed self-dual `k`-form `γ`,
`∫_M ⟨β⁺, γ⟩ vol = 0`. -/
theorem integralTopForm_inner_selfDualPart_eq_zero (hk : Even k) {β : SmoothForm I M ℝ k}
    (hβ : β ∈ exactForms I M k) {γ : SmoothForm I M ℝ k}
    (hγ : γ ∈ compactlySupportedClosedForms I M k) (hγ' : γ ∈ selfDualForms o) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
      ((selfDualPart o β).1 x) (γ.1 x) • riemannianVolumeForm o x) = 0 := by
  -- Pointwise `⟨β⁺, γ⟩ = ⟨β, γ⟩` and `⟨β, γ⟩ vol = β ∧ ⋆γ = β ∧ γ`.
  have h : (fun x ↦ alternatingFormInner (TangentSpace I x) k
      ((selfDualPart o β).1 x) (γ.1 x) • riemannianVolumeForm o x) =
      RoughForm.wedge β.1 γ.1 := by
    funext x
    ext v
    have hd := congrFun (inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar o rfl β γ) x
    rw [mem_selfDualForms.1 hγ'] at hd
    rw [coe_selfDualPart, RoughForm.alternatingFormInner_selfDualPart_of_mem_selfDualForms o hk _
      (coe_mem_selfDualForms_iff.2 hγ'), hd, cast_apply, coe_wedge]
    simp only [Function.comp_def, Fin.cast_eq_self]
  rw [h, ← coe_wedge]
  exact integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms o
    (wedge_mem_exactCompactlySupportedForms_of_left_mem hβ hγ)

/-- **The anti-self-dual part of an exact form is orthogonal to the closed anti-self-dual forms**:
on an oriented boundaryless Riemannian manifold of dimension `k + k` with `k` even, for an exact
`k`-form `β` and a compactly supported closed anti-self-dual `k`-form `γ`,
`∫_M ⟨β⁻, γ⟩ vol = 0`. -/
theorem integralTopForm_inner_antiSelfDualPart_eq_zero (hk : Even k) {β : SmoothForm I M ℝ k}
    (hβ : β ∈ exactForms I M k) {γ : SmoothForm I M ℝ k}
    (hγ : γ ∈ compactlySupportedClosedForms I M k) (hγ' : γ ∈ antiSelfDualForms o) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
      ((antiSelfDualPart o β).1 x) (γ.1 x) • riemannianVolumeForm o x) = 0 := by
  -- Pointwise `⟨β⁻, γ⟩ = ⟨β, γ⟩` and `⟨β, γ⟩ vol = β ∧ ⋆γ = β ∧ -γ`.
  have h : (fun x ↦ alternatingFormInner (TangentSpace I x) k
      ((antiSelfDualPart o β).1 x) (γ.1 x) • riemannianVolumeForm o x) =
      RoughForm.wedge β.1 (-γ).1 := by
    funext x
    ext v
    have hd := congrFun (inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar o rfl β γ) x
    rw [mem_antiSelfDualForms.1 hγ'] at hd
    rw [coe_antiSelfDualPart,
      RoughForm.alternatingFormInner_antiSelfDualPart_of_mem_antiSelfDualForms o hk _
        (coe_mem_antiSelfDualForms_iff.2 hγ'), hd, cast_apply, coe_wedge]
    simp only [Function.comp_def, Fin.cast_eq_self]
  rw [h, ← coe_wedge]
  exact integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms o
    (wedge_mem_exactCompactlySupportedForms_of_left_mem hβ (neg_mem hγ))

/-- **Pairings with a closed self-dual form are cohomological**: on an oriented boundaryless
Riemannian manifold of dimension `k + k`, for a closed `k`-form `φ` and a compactly supported
closed self-dual `k`-form `γ`, the integral `∫_M ⟨φ, γ⟩ vol` is the Poincaré pairing of the de Rham
classes `[φ]` and `[γ]`. In particular it depends only on the class of `φ`: for the curvature
`F_A` of a connection on a line bundle over a four-manifold, `∫_M ⟨i F_A, γ⟩ vol` depends only
on the bundle, by Chern–Weil theory. -/
theorem integralTopForm_inner_smul_riemannianVolumeForm_eq_poincarePairing
    {φ : SmoothForm I M ℝ k} (hφ : φ ∈ closedForms I M k) {γ : SmoothForm I M ℝ k}
    (hγ : γ ∈ compactlySupportedClosedForms I M k) (hγ' : γ ∈ selfDualForms o) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (φ.1 x) (γ.1 x) •
      riemannianVolumeForm o x) =
      poincarePairing I M o (deRhamCohomology.mk I k ⟨φ, hφ⟩)
        (compactlySupportedDeRhamCohomology.mk I k ⟨γ, hγ⟩) := by
  -- Pointwise `⟨φ, γ⟩ vol = φ ∧ ⋆γ = φ ∧ γ`.
  have h : (fun x ↦ alternatingFormInner (TangentSpace I x) k (φ.1 x) (γ.1 x) •
      riemannianVolumeForm o x) = RoughForm.wedge φ.1 γ.1 := by
    funext x
    ext v
    have hd := congrFun (inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar o rfl φ γ) x
    rw [mem_selfDualForms.1 hγ'] at hd
    rw [hd, cast_apply, coe_wedge]
    simp only [Function.comp_def, Fin.cast_eq_self]
  rw [h, poincarePairing_mk]

end Exact

end SmoothForm

end TauCeti
