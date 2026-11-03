/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.HodgeStar
public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
import TauCeti.Geometry.Manifold.DeRham.PoincarePairing
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.Riemannian.Codifferential

/-!
# Self-dual and anti-self-dual forms on an oriented Riemannian manifold

Let `M` be an oriented Riemannian manifold of dimension `k + k` with `k` even, for instance a
four-manifold and `k = 2`. The Hodge star `⋆` of middle-degree forms
(`TauCeti.RoughForm.hodgeStar`) is then an involution, `⋆⋆ = 1`. Its `+1` and `-1` eigenspaces
are the **self-dual** forms `Ω⁺` (`TauCeti.RoughForm.selfDualForms`) and the **anti-self-dual**
forms `Ω⁻` (`TauCeti.RoughForm.antiSelfDualForms`), the rough sections of the eigenbundles `Λ⁺`
and `Λ⁻` of `Λᵏ T*M`. Every middle-degree form splits as `α = α⁺ + α⁻` into its self-dual part
`α⁺ = (α + ⋆α) / 2` (`TauCeti.RoughForm.selfDualPart`) and its anti-self-dual part
`α⁻ = (α - ⋆α) / 2` (`TauCeti.RoughForm.antiSelfDualPart`). These are the projections
`(1 ± ⋆) / 2` onto `Ω±`, and `Ω⁺ ⊕ Ω⁻` is all of the middle-degree forms.

Since `⋆` is a self-adjoint isometry of each fibre, the two parts are pointwise orthogonal, and
`|α|² = |α⁺|² + |α⁻|²`. The fibre of `Λ±` at each point is the corresponding eigenspace of the
Hodge star of the tangent space, of dimension `(k + k).choose k / 2` when `0 < k`: three for
two-forms on a four-manifold. The wedge square is `α ∧ α = (|α⁺|² - |α⁻|²) vol`. For the
curvature `F` of a connection on a four-manifold this compares the integral of `F ∧ F`, a
characteristic number, with the energies of `F⁺` and `F⁻`; the curvature equation of the
Seiberg–Witten equations prescribes the self-dual part `F⁺`.

For a `C^n` metric on a `C^(n+1)` manifold both projections preserve `C^n` forms; on smooth forms
they are `TauCeti.SmoothForm.selfDualPart` and `TauCeti.SmoothForm.antiSelfDualPart`, the
projections onto the smooth self-dual and anti-self-dual forms `TauCeti.SmoothForm.selfDualForms`
and `TauCeti.SmoothForm.antiSelfDualForms`. Reversing the orientation negates `⋆` and so exchanges
the two parts (`TauCeti.RoughForm.selfDualPart_neg_orientation`,
`TauCeti.RoughForm.antiSelfDualPart_neg_orientation`).

On a boundaryless manifold, Stokes' theorem gives `∫_M β ∧ β = 0` for a compactly supported exact
form `β = dα`, so its self-dual and anti-self-dual parts have the same energy,
`∫_M |β⁺|² vol = ∫_M |β⁻|² vol`. Hence `β⁺ = 0` or `β⁻ = 0` forces `β = 0`: on a closed
four-manifold a one-form `a` with `(da)⁺ = 0` is closed.

## Main definitions

* `TauCeti.RoughForm.selfDualForms`, `TauCeti.RoughForm.antiSelfDualForms`: the `+1` and `-1`
  eigenspaces of the Hodge star of middle-degree forms.
* `TauCeti.RoughForm.selfDualPart`, `TauCeti.RoughForm.antiSelfDualPart`: the projections
  `α ↦ (α ± ⋆α) / 2`.
* `TauCeti.SmoothForm.selfDualPart`, `TauCeti.SmoothForm.antiSelfDualPart`: the same projections
  of smooth forms.
* `TauCeti.SmoothForm.selfDualForms`, `TauCeti.SmoothForm.antiSelfDualForms`: the smooth
  self-dual and anti-self-dual forms, the `+1` and `-1` eigenspaces of the Hodge star of smooth
  middle-degree forms.

## Main results

* `TauCeti.RoughForm.isProj_selfDualPart`, `TauCeti.RoughForm.isProj_antiSelfDualPart`: the
  projections onto `Ω⁺` and `Ω⁻`, with kernels `Ω⁻` and `Ω⁺`.
* `TauCeti.RoughForm.isCompl_selfDualForms_antiSelfDualForms`: `Ω⁺ ⊕ Ω⁻` is all of the
  middle-degree forms.
* `TauCeti.RoughForm.alternatingFormInner_eq_zero_of_mem_selfDualForms`: self-dual and
  anti-self-dual forms are pointwise orthogonal.
* `TauCeti.RoughForm.alternatingFormInner_selfDualPart_of_mem_selfDualForms`,
  `TauCeti.RoughForm.alternatingFormInner_antiSelfDualPart_of_mem_antiSelfDualForms`: pairing with
  a self-dual, or anti-self-dual, form sees only the self-dual, or anti-self-dual, part.
* `TauCeti.RoughForm.alternatingFormInner_self_eq_add`: `|α|² = |α⁺|² + |α⁻|²` pointwise.
* `TauCeti.RoughForm.wedge_self_apply`: `α ∧ α = (|α⁺|² - |α⁻|²) vol`.
* `TauCeti.RoughForm.map_proj_selfDualForms`,
  `TauCeti.RoughForm.two_mul_finrank_map_proj_selfDualForms`: the fibre of `Λ⁺` at a point is the
  self-dual subspace of the tangent forms, of dimension `(k + k).choose k / 2` when `0 < k`;
  likewise for `Λ⁻`.
* `TauCeti.IsSmoothForm.selfDualPart`, `TauCeti.IsSmoothForm.antiSelfDualPart`: the projections
  preserve `C^n` forms.
* `TauCeti.SmoothForm.isProj_selfDualPart`, `TauCeti.SmoothForm.isProj_antiSelfDualPart`: on
  smooth forms they are the projections onto the smooth `Ω⁺` and `Ω⁻`, which are the smooth forms
  lying in the rough `Ω⁺` and `Ω⁻` (`TauCeti.SmoothForm.coe_mem_selfDualForms_iff`).
* `TauCeti.SmoothForm.integralTopForm_inner_selfDualPart_eq_inner_antiSelfDualPart`: a compactly
  supported exact form has `∫_M |β⁺|² vol = ∫_M |β⁻|² vol`.
* `TauCeti.SmoothForm.integralTopForm_inner_selfDualPart_eq_zero`,
  `TauCeti.SmoothForm.integralTopForm_inner_antiSelfDualPart_eq_zero`: the self-dual, or
  anti-self-dual, part of an exact form is `L²`-orthogonal to the compactly supported closed
  self-dual, or anti-self-dual, forms.
* `TauCeti.SmoothForm.eq_zero_of_selfDualPart_eq_zero`,
  `TauCeti.SmoothForm.eq_zero_of_antiSelfDualPart_eq_zero`: a compactly supported exact form with
  vanishing self-dual, or anti-self-dual, part is zero.

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
  {k : ℕ} (o : Manifold.Orientation I M (Fin (k + k)))

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
    (x : M) : alternatingFormInner (TangentSpace I x) k (α x) (β x) = 0 := by
  let := o.fact_finrank_tangentSpace x
  -- The star is a pointwise isometry, so `⟨α, β⟩ = ⟨⋆α, ⋆β⟩ = ⟨α, -β⟩`.
  have h := (o.orientationAt x).alternatingFormInner_formHodgeStar
    (o.fact_finrank_tangentSpace x).out.symm (α x) (β x)
  rw [← hodgeStar_apply o rfl α x, ← hodgeStar_apply o rfl β x, mem_selfDualForms.1 hα,
    mem_antiSelfDualForms.1 hβ, Pi.neg_apply, map_neg] at h
  linarith

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

/-- **Pythagoras for the splitting `Ω⁺ ⊕ Ω⁻`**: `|α|² = |α⁺|² + |α⁻|²` at every point. -/
theorem alternatingFormInner_self_eq_add (hk : Even k) (α : RoughForm I M ℝ k) (x : M) :
    alternatingFormInner (TangentSpace I x) k (α x) (α x) =
      alternatingFormInner (TangentSpace I x) k (selfDualPart o α x) (selfDualPart o α x) +
        alternatingFormInner (TangentSpace I x) k (antiSelfDualPart o α x)
          (antiSelfDualPart o α x) := by
  have h := alternatingFormInner_selfDualPart_antiSelfDualPart o hk α α x
  rw [alternatingFormInner_comm] at h
  conv_lhs => rw [← selfDualPart_add_antiSelfDualPart o α]
  simp only [Pi.add_apply, map_add, LinearMap.add_apply, h,
    alternatingFormInner_selfDualPart_antiSelfDualPart o hk]
  ring

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

/-- The fibre of `Λ⁺` at `x`: the values at `x` of the self-dual forms make up the `+1`
eigenspace of the Hodge star of the tangent space at `x`. -/
theorem map_proj_selfDualForms (x : M) :
    (selfDualForms o).map (LinearMap.proj x) =
      (letI := o.fact_finrank_tangentSpace x
       Module.End.eigenspace ((o.orientationAt x).formHodgeStar
          (o.fact_finrank_tangentSpace x).out.symm :
          Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) 1) := by
  classical
  let := o.fact_finrank_tangentSpace x
  ext a
  simp only [Submodule.mem_map, mem_selfDualForms, LinearMap.coe_proj, Function.eval,
    Module.End.mem_eigenspace_iff, one_smul, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨α, hα, rfl⟩
    simpa using congrFun hα x
  · -- A self-dual covector is the value at `x` of the rough form supported at `x`.
    intro ha
    refine ⟨Pi.single x a, funext fun y ↦ ?_, by simp⟩
    rcases eq_or_ne y x with rfl | hy
    · simpa using ha
    · simp [Pi.single_eq_of_ne hy]

/-- The fibre of `Λ⁻` at `x`: the values at `x` of the anti-self-dual forms make up the `-1`
eigenspace of the Hodge star of the tangent space at `x`. -/
theorem map_proj_antiSelfDualForms (x : M) :
    (antiSelfDualForms o).map (LinearMap.proj x) =
      (letI := o.fact_finrank_tangentSpace x
       Module.End.eigenspace ((o.orientationAt x).formHodgeStar
          (o.fact_finrank_tangentSpace x).out.symm :
          Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) (-1)) := by
  classical
  let := o.fact_finrank_tangentSpace x
  ext a
  simp only [Submodule.mem_map, mem_antiSelfDualForms, LinearMap.coe_proj, Function.eval,
    Module.End.mem_eigenspace_iff, neg_one_smul, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨α, hα, rfl⟩
    simpa using congrFun hα x
  · -- An anti-self-dual covector is the value at `x` of the rough form supported at `x`.
    intro ha
    refine ⟨Pi.single x a, funext fun y ↦ ?_, by simp⟩
    rcases eq_or_ne y x with rfl | hy
    · simpa using ha
    · simp [Pi.single_eq_of_ne hy]

/-- **The rank of `Λ⁺`**: in an even positive middle degree, twice the dimension of the fibre of
`Λ⁺` is `(k + k).choose k`. For two-forms on a four-manifold the fibre has dimension three. -/
theorem two_mul_finrank_map_proj_selfDualForms (hk : Even k) (hk₀ : 0 < k) (x : M) :
    2 * finrank ℝ ((selfDualForms o).map (LinearMap.proj x)) = (k + k).choose k := by
  let := o.fact_finrank_tangentSpace x
  rw [map_proj_selfDualForms,
    (o.orientationAt x).two_mul_finrank_eigenspace_formHodgeStar_one hk hk₀]

/-- **The rank of `Λ⁻`**: in an even positive middle degree, twice the dimension of the fibre of
`Λ⁻` is `(k + k).choose k`. For two-forms on a four-manifold the fibre has dimension three. -/
theorem two_mul_finrank_map_proj_antiSelfDualForms (hk : Even k) (hk₀ : 0 < k) (x : M) :
    2 * finrank ℝ ((antiSelfDualForms o).map (LinearMap.proj x)) = (k + k).choose k := by
  let := o.fact_finrank_tangentSpace x
  rw [map_proj_antiSelfDualForms,
    (o.orientationAt x).two_mul_finrank_eigenspace_formHodgeStar_neg_one hk hk₀]

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

/-! ### Exact forms on a boundaryless manifold -/

section Exact

variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

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
  -- `|β⁺|² vol = β ∧ β + |β⁻|² vol` pointwise.
  have hsplit : (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((selfDualPart o β).1 x) ((selfDualPart o β).1 x) • riemannianVolumeForm o x) =
      RoughForm.wedge β.1 β.1 + fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((antiSelfDualPart o β).1 x) ((antiSelfDualPart o β).1 x) • riemannianVolumeForm o x := by
    funext x
    ext v
    simp only [RoughForm.wedge_self_apply o hk, coe_selfDualPart, coe_antiSelfDualPart,
      Pi.add_apply, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    ring
  have hw := (mem_compactlySupportedForms I).mp (wedge_mem_compactlySupportedForms β hc)
  rw [coe_wedge] at hw
  have hsw : IsSmoothForm I 0 (RoughForm.wedge β.1 β.1) := by
    simpa only [coe_wedge] using (wedge β β).isSmoothForm.of_le (by simp)
  rw [hsplit, integralTopForm_add o hsw
      ((isSmoothForm_inner_smul_riemannianVolumeForm o rfl _ _).of_le bot_le) hw
      (RoughForm.isCompact_tsupport_inner_smul_riemannianVolumeForm o _ _
        ((mem_compactlySupportedForms I).mp (antiSelfDualPart_mem_compactlySupportedForms o hc))),
    ← coe_wedge, integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms o
      (wedge_mem_exactCompactlySupportedForms_of_left_mem hβ
        ((mem_compactlySupportedClosedForms I).mpr ⟨hc, exactForms_le_closedForms I k hβ⟩)),
    zero_add]

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

end Exact

end SmoothForm

end TauCeti
