/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Curry
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.LinearAlgebra.BilinearForm.Contact.NormalForm
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Topology.Algebra.Module.Contact

/-!
# Contact forms

A real one-form `α` on a manifold `M` is a **contact form** when, at every point `x`, the covector
`α_x` is nonzero and the two-form `dα_x` is nondegenerate on the hyperplane `ker α_x`
(`TauCeti.SmoothForm.IsContactForm`). Its kernel `ξ = ker α` (`TauCeti.SmoothForm.kerDistribution`)
is then a field of hyperplanes, the contact distribution. Pointwise, this is the linear condition
`Module.Dual.IsContact` applied to `α_x` and `dα_x`.

This intrinsic formulation needs no dimension index. In finite dimension it forces the model
space to have odd dimension `2 n + 1` (`TauCeti.SmoothForm.IsContactForm.odd_finrank`), and the
contact distribution then has rank `2 n`
(`TauCeti.SmoothForm.IsContactForm.finrank_kerDistribution_add_one`). At each point the form
and its exterior derivative are then the standard `dz` and `Σᵢ dqᵢ ∧ dpᵢ` in suitable linear
coordinates on the tangent space
(`TauCeti.SmoothForm.IsContactForm.exists_linearEquiv_eq_stdContact`).

Only the hyperplane field `ξ` is invariant: multiplying `α` by a nowhere vanishing `C¹` function
`f` leaves `ξ` unchanged and gives again a contact form
(`TauCeti.SmoothForm.isContactForm_iff_of_eq_smul`). The proof is the Leibniz rule
`d(f α) = df ∧ α + f dα`: the term `df ∧ α` vanishes on `ξ × ξ`, so on `ξ` the form `d(f α)` is
`f dα`. In particular `-α`, which defines the opposite coorientation of `ξ`, is again a contact
form (`TauCeti.SmoothForm.isContactForm_neg_iff`).

A rough one-form satisfies the pointwise condition `TauCeti.IsContactFormAt` at `x` when it is
nonzero there and its exterior derivative is nondegenerate on its kernel. This condition imposes
no global regularity. For a smooth one-form it agrees with the canonical contact condition, by
`TauCeti.SmoothForm.isContactForm_iff_forall_isContactFormAt`. For a one-form and a scalar
function that are both differentiable at `x`, rescaling by the function preserves the pointwise
condition whenever its value at `x` is nonzero (`TauCeti.isContactFormAt_fun_smul_iff`). The
condition at `x` only depends on the value of the form at `x` and on its exterior derivative at `x`
restricted to the hyperplane (`TauCeti.isContactFormAt_congr`). At an interior point the
condition can be checked in the preferred chart
(`TauCeti.isContactFormAt_inChartAt_iff`), which reduces local questions about contact forms on
manifolds, such as the existence of Darboux charts, to open subsets of the model space. On a normed
space this is the linear condition `Module.Dual.IsContact` for the covector `α(x)` and the bilinear
form of `dα(x)` (`TauCeti.isContactFormAt_modelSpace_iff_isContact`). In finite dimension, since
linear contactness is open (`TauCeti.isOpen_setOf_isContact_continuousAlternatingMap`), a `C¹`
one-form that is contact at `x` remains contact on a neighbourhood of `x`
(`TauCeti.IsContactFormAt.eventually`, `TauCeti.IsContactFormAt.eventually_modelSpace`).

## Main declarations

* `TauCeti.SmoothForm.kerDistribution`: the hyperplane field `ker α` of a real one-form.
* `TauCeti.SmoothForm.IsContactForm`: the contact condition.
* `TauCeti.SmoothForm.isContactForm_def`, `TauCeti.SmoothForm.isContactForm_iff`: the pointwise
  and elementwise statements of the contact condition.
* `TauCeti.SmoothForm.isContactForm_iff_of_eq_smul`,
  `TauCeti.SmoothForm.kerDistribution_of_eq_smul`: rescaling by a nowhere vanishing function.
* `TauCeti.SmoothForm.apply_eq_smul_of_kerDistribution_le`: a one-form whose kernel at a point
  contains that of another is proportional to it there.
* `TauCeti.SmoothForm.isContactForm_smul_iff`, `TauCeti.SmoothForm.isContactForm_neg_iff`:
  rescaling by a nonzero constant.
* `TauCeti.SmoothForm.IsContactForm.odd_finrank`: contact manifolds are odd-dimensional.
* `TauCeti.SmoothForm.IsContactForm.exists_linearEquiv_eq_stdContact`: at each point, a contact
  form and its exterior derivative are standard in suitable linear coordinates.
* `TauCeti.IsContactFormAt`: the pointwise contact condition for a rough one-form, with
  `TauCeti.isContactFormAt_neg_iff`, `TauCeti.isContactFormAt_fun_smul_iff`,
  `TauCeti.isContactFormAt_congr`, `TauCeti.SmoothForm.isContactFormAt_iff_isContact`, and
  `TauCeti.SmoothForm.isContactForm_iff_forall_isContactFormAt`.
* `TauCeti.IsContactFormAt.eventually`, `TauCeti.IsContactFormAt.eventually_modelSpace`: openness
  of the pointwise contact condition in finite dimension.
* `TauCeti.isContactFormAt_inChartAt_iff`: at an interior point, the pointwise contact condition
  holds exactly when it holds for the coordinate expression in the preferred chart.
* `TauCeti.isContactFormAt_modelSpace_iff_isContact`: on a normed space, the pointwise contact
  condition is the linear contact condition for the values of `α` and `dα`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Sections 1.1 and 2.1.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017, Section 3.5.
-/

public section

noncomputable section

open Module
open scoped Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- The kernel `ker α_x` of a real one-form `α` at each point `x`, as a family of subspaces of
the tangent spaces. For a contact form this is the contact distribution. -/
def kerDistribution (α : SmoothForm I M ℝ 1) (x : M) : Submodule ℝ (TangentSpace I x) :=
  RoughForm.ker α.val x

@[simp]
theorem mem_kerDistribution {α : SmoothForm I M ℝ 1} {x : M} {v : TangentSpace I x} :
    v ∈ α.kerDistribution x ↔ α.val x ![v] = 0 := by
  exact RoughForm.mem_ker

/-- The kernel distribution of a smooth one-form is the pointwise kernel of its underlying rough
form. -/
theorem kerDistribution_eq_ker (α : SmoothForm I M ℝ 1) (x : M) :
    α.kerDistribution x = RoughForm.ker α.val x := by
  ext
  rw [mem_kerDistribution, RoughForm.mem_ker]

/-- At each point, `kerDistribution α` is the kernel of the covector `α_x`. -/
theorem kerDistribution_def (α : SmoothForm I M ℝ 1) (x : M) :
    α.kerDistribution x = LinearMap.ker (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ) := by
  ext v
  rw [mem_kerDistribution, LinearMap.mem_ker, degreeOneEquiv_coe_apply]

/-- Two tangent vectors are congruent modulo `ker α_x` exactly when `α` takes the same value on
them. -/
theorem sub_mem_kerDistribution_iff {α : SmoothForm I M ℝ 1} {x : M} {v w : TangentSpace I x} :
    v - w ∈ α.kerDistribution x ↔ α.val x ![v] = α.val x ![w] := by
  rw [kerDistribution_def, LinearMap.sub_mem_ker_iff, degreeOneEquiv_coe_apply,
    degreeOneEquiv_coe_apply]

/-- A real one-form `α` is a **contact form** when, at every point `x`, the covector `α_x` is
nonzero and `dα_x` restricts to a nondegenerate bilinear form on `ker α_x`. -/
def IsContactForm (α : SmoothForm I M ℝ 1) : Prop :=
  ∀ x, Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
    ((mextDerivₗ I 1 α).bilinFormAt x)

/-- The contact condition, pointwise: at each point, `α_x` is a contact covector for `dα_x`. -/
theorem isContactForm_def {α : SmoothForm I M ℝ 1} :
    α.IsContactForm ↔
      ∀ x, Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
        ((mextDerivₗ I 1 α).bilinFormAt x) :=
  Iff.rfl

/-- The contact condition, elementwise: at each point `α` does not vanish, and the only vector
of `ker α` which is `dα`-orthogonal to all of `ker α` is zero. -/
theorem isContactForm_iff {α : SmoothForm I M ℝ 1} :
    α.IsContactForm ↔
      ∀ x, (∃ v : TangentSpace I x, α.val x ![v] ≠ 0) ∧
        ∀ v : TangentSpace I x, α.val x ![v] = 0 →
          (∀ w : TangentSpace I x, α.val x ![w] = 0 → mextDeriv α.val x ![v, w] = 0) → v = 0 := by
  refine forall_congr' fun x ↦ ?_
  rw [Module.Dual.isContact_iff_of_isRefl (isAlt_bilinFormAt _ x).isRefl]
  simp only [degreeOneEquiv_coe_apply, ← mextDeriv_eq_bilinFormAt, ne_eq, LinearMap.ext_iff,
    LinearMap.zero_apply, not_forall]

/-- A contact form does not vanish. -/
theorem IsContactForm.exists_ne_zero {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) (x : M) :
    ∃ v : TangentSpace I x, α.val x ![v] ≠ 0 :=
  (isContactForm_iff.1 hα x).1

/-- A contact form vanishes nowhere. -/
theorem IsContactForm.apply_ne_zero {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) (x : M) :
    α.val x ≠ 0 := fun h ↦
  let ⟨_, hv⟩ := hα.exists_ne_zero x
  hv (by simp [h])

/-- Two one-forms with the same kernels vanish at the same points: a covector vanishes exactly
when its kernel is the whole tangent space. -/
theorem apply_eq_zero_iff_of_kerDistribution_eq {α β : SmoothForm I M ℝ 1}
    (hker : β.kerDistribution = α.kerDistribution) (x : M) : β.val x = 0 ↔ α.val x = 0 := by
  rw [← RoughForm.ker_eq_top_iff, ← RoughForm.ker_eq_top_iff]
  exact Eq.congr_left (congrFun hker x)

/-- If `β = f α` for a nowhere vanishing function `f`, then `α` and `β` have the same kernel. -/
theorem kerDistribution_of_eq_smul {α β : SmoothForm I M ℝ 1} {f : M → ℝ}
    (hf₀ : ∀ x, f x ≠ 0) (hβ : ∀ x, β.val x = f x • α.val x) :
    β.kerDistribution = α.kerDistribution := by
  ext x v
  rw [mem_kerDistribution, mem_kerDistribution, hβ, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, mul_eq_zero, or_iff_right (hf₀ x)]

/-- Conversely, if the kernel of `α` at `x` lies in that of `β`, then `β` is proportional to `α`
there: if `α_x(v) = 1`, then `β_x = β_x(v) α_x`. -/
theorem apply_eq_smul_of_kerDistribution_le {α β : SmoothForm I M ℝ 1} {x : M}
    {v : TangentSpace I x} (hker : α.kerDistribution x ≤ β.kerDistribution x)
    (hv : α.val x ![v] = 1) : β.val x = β.val x ![v] • α.val x := by
  ext w
  obtain ⟨u, rfl⟩ : ∃ u, w = ![u] := ⟨w 0, by
    rw [Matrix.vec_single_eq_const]
    exact funext fun i ↦ congrArg w (Subsingleton.elim i 0)⟩
  -- `u - α(u) v` lies in `ker α ⊆ ker β`.
  have hmem : u - α.val x ![u] • v ∈ β.kerDistribution x := hker <| by
    rw [kerDistribution_def, LinearMap.mem_ker, map_sub, map_smul, degreeOneEquiv_coe_apply,
      degreeOneEquiv_coe_apply, hv, smul_eq_mul, mul_one, sub_self]
  rw [kerDistribution_def, LinearMap.mem_ker, map_sub, map_smul, degreeOneEquiv_coe_apply,
    degreeOneEquiv_coe_apply, smul_eq_mul, sub_eq_zero] at hmem
  rw [ContinuousAlternatingMap.smul_apply, hmem, smul_eq_mul, mul_comm]

/-- **Rescaling of contact forms.** If `β = f α` for a nowhere vanishing `C¹` function `f`, then
`β` is a contact form exactly when `α` is. -/
theorem isContactForm_iff_of_eq_smul {α β : SmoothForm I M ℝ 1} {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) (hf₀ : ∀ x, f x ≠ 0) (hβ : ∀ x, β.val x = f x • α.val x) :
    β.IsContactForm ↔ α.IsContactForm := by
  refine forall_congr' fun x ↦ ?_
  set a := (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
  have ha : ∀ v, a v = α.val x ![v] := degreeOneEquiv_coe_apply α x
  have hb : (degreeOneEquiv β x : TangentSpace I x →ₗ[ℝ] ℝ) = f x • a := by
    ext v
    rw [degreeOneEquiv_coe_apply, hβ, LinearMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      ha]
  -- On `ker α`, the Leibniz rule `d(f α) = df ∧ α + f dα` reduces `dβ` to `f dα`.
  have hdβ : ∀ v w, a v = 0 → a w = 0 →
      (mextDerivₗ I 1 β).bilinFormAt x v w = (f x • (mextDerivₗ I 1 α).bilinFormAt x) v w := by
    intro v w hv hw
    have hβ' : β.val = fun y ↦ f y • α.val y := funext hβ
    rw [ha] at hv hw
    simp only [← mextDeriv_eq_bilinFormAt, LinearMap.smul_apply, smul_eq_mul, hβ',
      mextDeriv_fun_smul_apply ((hf x).mdifferentiableAt one_ne_zero) (α.mdifferentiableAt x),
      hv, hw, mul_zero, sub_zero, zero_add]
  rw [hb, Module.Dual.isContact_smul_iff (hf₀ x), Module.Dual.isContact_congr hdβ,
    Module.Dual.isContact_smul_bilinForm_iff (hf₀ x)]

/-- A nonzero constant multiple of a one-form has the same kernel as the form. -/
@[simp]
theorem kerDistribution_smul {α : SmoothForm I M ℝ 1} {c : ℝ} (hc : c ≠ 0) :
    (c • α).kerDistribution = α.kerDistribution :=
  kerDistribution_of_eq_smul (fun _ ↦ hc) fun _ ↦ by rw [Submodule.coe_smul, Pi.smul_apply]

/-- The negative of a one-form has the same kernel as the form. -/
@[simp]
theorem kerDistribution_neg {α : SmoothForm I M ℝ 1} :
    (-α).kerDistribution = α.kerDistribution := by
  rw [← neg_one_smul ℝ α, kerDistribution_smul (by norm_num)]

/-- A nonzero constant multiple of a one-form is a contact form exactly when the form is. -/
@[simp]
theorem isContactForm_smul_iff {α : SmoothForm I M ℝ 1} {c : ℝ} (hc : c ≠ 0) :
    (c • α).IsContactForm ↔ α.IsContactForm :=
  isContactForm_iff_of_eq_smul contMDiff_const (fun _ ↦ hc) fun _ ↦ by
    rw [Submodule.coe_smul, Pi.smul_apply]

/-- The negative of a one-form, which defines the opposite coorientation of its kernel, is a
contact form exactly when the form is. -/
@[simp]
theorem isContactForm_neg_iff {α : SmoothForm I M ℝ 1} :
    (-α).IsContactForm ↔ α.IsContactForm := by
  rw [← neg_one_smul ℝ α, isContactForm_smul_iff (by norm_num)]

/-- The contact distribution of a contact form has codimension one. -/
theorem IsContactForm.finrank_kerDistribution_add_one [FiniteDimensional ℝ E]
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) (x : M) :
    finrank ℝ (α.kerDistribution x) + 1 = finrank ℝ E := by
  rw [kerDistribution_def]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero (hα x).ne_zero

/-- The model space of a manifold carrying a contact form is odd-dimensional, as soon as the
manifold is nonempty. -/
theorem IsContactForm.odd_finrank [FiniteDimensional ℝ E] {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (x : M) : Odd (finrank ℝ E) :=
  (hα x).odd_finrank (isAlt_bilinFormAt _ x)

/-- **Linear normal form of a contact form at a point.** At each point `x`, there are linear
coordinates `e : T_x M ≃ ℝⁿ × ℝⁿ × ℝ` on the tangent space in which `α_x` is the standard contact
covector `dz` and `dα_x` is the standard form `Σᵢ dqᵢ ∧ dpᵢ`. These are the values at the origin
of the standard contact form `dz - Σᵢ pᵢ dqᵢ` and of its exterior derivative. -/
theorem IsContactForm.exists_linearEquiv_eq_stdContact [FiniteDimensional ℝ E]
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) (x : M) :
    ∃ (n : ℕ) (e : TangentSpace I x ≃ₗ[ℝ] (Fin n → ℝ) × (Fin n → ℝ) × ℝ),
      (∀ v, α.val x ![v] = stdContactCovector ℝ n (e v)) ∧
        ∀ v w, mextDeriv α.val x ![v, w] = stdContactBilinForm ℝ n (e v) (e w) := by
  obtain ⟨n, e, ha, hB⟩ := (hα x).exists_linearEquiv_eq_stdContact (isAlt_bilinFormAt _ x)
  refine ⟨n, e, fun v ↦ ?_, fun v w ↦ ?_⟩
  · rw [← degreeOneEquiv_coe_apply, ← ha, LinearMap.comp_apply, LinearEquiv.coe_coe]
  · simpa [bilinFormAt_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply] using
      (LinearMap.congr_fun₂ hB v w).symm

end SmoothForm

section Pointwise

open Bundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- A one-form `α` is a **contact form at `x`** when `α_x ≠ 0` and `dα_x` is nondegenerate on the
hyperplane `ker α_x`: the only vector of `ker α_x` that is `dα_x`-orthogonal to all of
`ker α_x` is zero. This is the pointwise algebraic condition only: it imposes no regularity on `α`,
and is meaningful when `α` is differentiable at `x`. The global notion
`TauCeti.SmoothForm.IsContactForm` is defined on smooth forms. -/
structure IsContactFormAt (α : RoughForm I M ℝ 1) (x : M) : Prop where
  /-- A contact form does not vanish, so its kernel is a hyperplane. -/
  ne_zero : α x ≠ 0
  /-- The exterior derivative of a contact form is nondegenerate on its kernel. -/
  nondegenerate : ∀ v ∈ α.ker x, (∀ w ∈ α.ker x, mextDeriv α x ![v, w] = 0) → v = 0

/-- Reversing the coorientation, `α ↦ -α`, preserves the contact condition. -/
@[simp]
theorem isContactFormAt_neg_iff {α : RoughForm I M ℝ 1} {x : M} :
    IsContactFormAt (-α) x ↔ IsContactFormAt α x := by
  suffices ∀ α : RoughForm I M ℝ 1, IsContactFormAt α x → IsContactFormAt (-α) x from
    ⟨fun h ↦ neg_neg α ▸ this _ h, this α⟩
  intro α h
  refine ⟨by simpa using h.ne_zero, fun v hv hvw ↦ h.nondegenerate v (by simpa using hv)
    fun w hw ↦ ?_⟩
  have := hvw w (by simpa using hw)
  simpa [mextDeriv_neg] using this

open Topology in
/-- **The contact condition in a chart.** At an interior point `x₀`, a one-form `α` is a contact
form exactly when its coordinate expression in the preferred chart at `x₀` is a contact form, on
the model space, at the chart image of `x₀`. No regularity of `α` is needed: both the value and
the exterior derivative of `α` at `x₀` are read off this coordinate expression. -/
theorem isContactFormAt_inChartAt_iff [IsManifold I 1 M] {α : RoughForm I M ℝ 1} {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) :
    IsContactFormAt (I := 𝓘(ℝ, E)) (α.inChartAt x₀) (extChartAt I x₀ x₀) ↔
      IsContactFormAt α x₀ := by
  have hval : α.inChartAt x₀ (extChartAt I x₀ x₀) = α x₀ := α.inChartAt_extChartAt_self x₀
  -- The model range is a neighbourhood of the chart image of an interior point, so the
  -- exterior derivative within it is the flat exterior derivative.
  have hnhds : Set.range I ∈ 𝓝 (extChartAt I x₀ x₀) := range_mem_nhds_isInteriorPoint hx₀
  have hd : mextDeriv (I := 𝓘(ℝ, E)) (α.inChartAt x₀) (extChartAt I x₀ x₀) = mextDeriv α x₀ := by
    refine (mextDeriv_eq_extDeriv (E := E) (F := ℝ) (k := 1) (α.inChartAt x₀) _).trans ?_
    rw [mextDeriv_def, ← extDerivWithin_univ,
      extDerivWithin_congr_set (Filter.eventuallyEqSet_univ.2 hnhds)]
  have hev (v : E) : α.inChartAt x₀ (extChartAt I x₀ x₀) ![v] = α x₀ ![v] :=
    congrArg (fun A : E [⋀^Fin 1]→L[ℝ] ℝ ↦ A ![v]) hval
  refine ⟨fun h ↦ ⟨hval ▸ h.ne_zero, fun v hv hvw ↦ ?_⟩,
    fun h ↦ ⟨hval ▸ h.ne_zero, fun v hv hvw ↦ ?_⟩⟩
  · refine h.nondegenerate v (RoughForm.mem_ker.2 ((hev v).trans (RoughForm.mem_ker.1 hv)))
      fun w hw ↦ (congrArg (fun A ↦ A ![v, w]) hd).trans (hvw w ?_)
    exact RoughForm.mem_ker.2 ((hev w).symm.trans (RoughForm.mem_ker.1 hw))
  · refine h.nondegenerate v (RoughForm.mem_ker.2 ((hev v).symm.trans (RoughForm.mem_ker.1 hv)))
      fun w hw ↦ (congrArg (fun A ↦ A ![v, w]) hd).symm.trans (hvw w ?_)
    exact RoughForm.mem_ker.2 ((hev w).trans (RoughForm.mem_ker.1 hw))

section Rescaling

variable [IsManifold I 1 M] {α : RoughForm I M ℝ 1} {f : M → ℝ} {x : M}

/-- **Rescaling a contact form**: for a one-form `α` differentiable at `x` and a function `f`
differentiable at `x` with `f x ≠ 0`, the one-form `f α` is a contact form at `x` exactly when
`α` is. On `ker α_x` the Leibniz rule reads `d(f α)_x = f x • dα_x`. -/
theorem isContactFormAt_fun_smul_iff (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x) (hfx : f x ≠ 0) :
    IsContactFormAt (fun y ↦ f y • α y) x ↔ IsContactFormAt α x := by
  have hd : ∀ v ∈ α.ker x, ∀ w ∈ α.ker x,
      mextDeriv (fun y ↦ f y • α y) x ![v, w] = f x * mextDeriv α x ![v, w] := by
    intro v hv w hw
    rw [RoughForm.mem_ker] at hv hw
    rw [mextDeriv_fun_smul_apply hf hα, hv, hw]
    ring
  constructor
  · intro h
    refine ⟨(smul_ne_zero_iff.mp h.ne_zero).2, fun v hv hvw ↦ ?_⟩
    refine h.nondegenerate v (by rwa [RoughForm.ker_fun_smul hfx]) fun w hw ↦ ?_
    rw [RoughForm.ker_fun_smul hfx] at hw
    rw [hd v hv w hw, hvw w hw, mul_zero]
  · intro h
    refine ⟨smul_ne_zero hfx h.ne_zero, fun v hv hvw ↦ ?_⟩
    rw [RoughForm.ker_fun_smul hfx] at hv hvw
    refine h.nondegenerate v hv fun w hw ↦ ?_
    have := hvw w hw
    rw [hd v hv w hw] at this
    exact (mul_eq_zero.mp this).resolve_left hfx

end Rescaling

private theorem roughForm_isContactFormAt_iff_isContact {α : RoughForm I M ℝ 1} {y : M}
    (l : TangentSpace I y →ₗ[ℝ] ℝ) (B : TangentSpace I y →ₗ[ℝ] TangentSpace I y →ₗ[ℝ] ℝ)
    (hl : ∀ v, l v = α y ![v]) (hB : ∀ v w, B v w = mextDeriv α y ![v, w]) :
    IsContactFormAt α y ↔ Module.Dual.IsContact l B := by
  have hB_alt : LinearMap.IsAlt B := fun v ↦ by
    rw [hB]
    exact (mextDeriv α y).map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl (by decide)
  rw [Module.Dual.isContact_iff_of_isRefl hB_alt.isRefl]
  refine ⟨fun h ↦ ⟨fun h0 ↦ h.ne_zero <| RoughForm.ker_eq_top_iff.1 <| eq_top_iff.2 fun v _ ↦
    RoughForm.mem_ker.2 <| hl v ▸ LinearMap.congr_fun h0 v,
    fun v hv hvw ↦ h.nondegenerate v (RoughForm.mem_ker.2 (hl v ▸ hv)) fun w hw ↦
      hB v w ▸ hvw w (hl w ▸ RoughForm.mem_ker.1 hw)⟩,
    fun ⟨h0, h⟩ ↦ ⟨fun hz ↦ h0 <| LinearMap.ext fun v ↦ by simp [hl, hz],
    fun v hv hvw ↦ h v (hl v ▸ RoughForm.mem_ker.1 hv) fun w hw ↦
      (hB v w).symm ▸ hvw w (RoughForm.mem_ker.2 (hl w ▸ hw))⟩⟩

private theorem isContactFormAt_iff_isContact_of_equiv {α : RoughForm I M ℝ 1} {y : M}
    (L : TangentSpace I y ≃L[ℝ] E) {a : E [⋀^Fin 1]→L[ℝ] ℝ} {b : E [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : ∀ u, a ![u] = α y ![L.symm u])
    (hb : ∀ u w, b ![u, w] = mextDeriv α y ![L.symm u, L.symm w]) :
    IsContactFormAt α y ↔
      Module.Dual.IsContact (ContinuousAlternatingMap.toDual a : E →ₗ[ℝ] ℝ)
        (ContinuousAlternatingMap.flatL ℝ E ℝ b).toLinearMap₁₂ := by
  rw [← Module.Dual.isContact_comp_linearEquiv_compl₁₂_iff L.toLinearEquiv]
  exact roughForm_isContactFormAt_iff_isContact _ _
    (fun v ↦ by simp [ha])
    (fun v w ↦ by simp [hb])

open scoped Topology in
/-- **Openness of the pointwise contact condition.** On a finite-dimensional `C²` manifold, a `C¹`
one-form that is a contact form at `x` remains a contact form on a neighbourhood of `x`. -/
theorem IsContactFormAt.eventually [FiniteDimensional ℝ E] [IsManifold I 2 M]
    {α : RoughForm I M ℝ 1} {x : M} (hc : IsContactFormAt α x)
    (hα : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) 1
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x) :
    ∀ᶠ y in 𝓝 x, IsContactFormAt α y := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by simp)
  have : IsManifold I ((1 : WithTop ℕ∞) + 1) M := ‹IsManifold I 2 M›
  let : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  obtain ⟨s, hs, hαs⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hα
  obtain ⟨U, hUs, hU, hxU⟩ := mem_nhds_iff.1 hs
  have hdU := contMDiffOn_mextDerivWithin (n := 0) α (hαs.mono hUs) hU.uniqueMDiffOn
    fun _ hy ↦ subset_closure (hU.interior_eq.symm ▸ hy)
  set dαU : RoughForm I M ℝ 2 := mextDerivWithin α U
  set T := FiberBundle.trivializationAt E (TangentSpace I) x
  have hxT : x ∈ T.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  set A₁ : M → E [⋀^Fin 1]→L[ℝ] ℝ := fun y ↦
    ContinuousAlternatingMap.inCoordinates E ℝ x y x y (α y)
  set A₂ : M → E [⋀^Fin 2]→L[ℝ] ℝ := fun y ↦
    ContinuousAlternatingMap.inCoordinates E ℝ x y x y (dαU y)
  have hA₁ : ContinuousAt A₁ x :=
    ((continuousAt_continuousAlternatingMap_bundle
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y))).1 hα.continuousAt).2
  have hA₂ : ContinuousAt A₂ x :=
    ((continuousAt_continuousAlternatingMap_bundle
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ) y (dαU y))).1
        ((hdU x hxU).contMDiffAt (hU.mem_nhds hxU)).continuousAt).2
  have hinCoord {y : M} (hyT : y ∈ T.baseSet) {k : ℕ} (ω : RoughForm I M ℝ k) (v : Fin k → E) :
      ContinuousAlternatingMap.inCoordinates E ℝ x y x y (ω y) v =
        ω y (fun i ↦ (T.continuousLinearEquivAt ℝ y hyT).symm (v i)) := by
    have hsymm : ∀ u, (trivializationAt E (TangentSpace I) x).symmL ℝ y u = T.symm y u :=
      T.symmL_apply hyT
    simp [ContinuousAlternatingMap.inCoordinates, Function.comp_def, hsymm]
  have hiff {y : M} (hyU : y ∈ U) (hyT : y ∈ T.baseSet) :
      IsContactFormAt α y ↔
        Module.Dual.IsContact (ContinuousAlternatingMap.toDual (A₁ y) : E →ₗ[ℝ] ℝ)
          (ContinuousAlternatingMap.flatL ℝ E ℝ (A₂ y)).toLinearMap₁₂ :=
    isContactFormAt_iff_isContact_of_equiv (T.continuousLinearEquivAt ℝ y hyT)
      (fun u ↦ by
        rw [hinCoord hyT α ![u]]
        congr 1; funext i; fin_cases i; rfl)
      (fun u w ↦ by
        dsimp only [A₂, dαU]
        rw [mextDerivWithin_of_isOpen hU hyU, hinCoord hyT (mextDeriv α) ![u, w]]
        congr 1; funext i; fin_cases i <;> rfl)
  filter_upwards [hU.mem_nhds hxU, T.open_baseSet.mem_nhds hxT,
    (hA₁.prodMk hA₂).eventually
      ((isOpen_setOf_isContact_continuousAlternatingMap (E := E)).mem_nhds
        ((hiff hxU hxT).1 hc))] with y hyU hyT hy
  exact (hiff hyU hyT).2 hy

/-- **The contact condition at a point is congruent.** Two one-forms with the same value at `x`
whose exterior derivatives at `x` agree on the common hyperplane `ker α_x` are contact at `x`
together. Their exterior derivatives may differ off `ker α_x`. -/
theorem isContactFormAt_congr {α β : RoughForm I M ℝ 1} {x : M} (hval : β x = α x)
    (hd : ∀ v ∈ α.ker x, ∀ w ∈ α.ker x, mextDeriv β x ![v, w] = mextDeriv α x ![v, w]) :
    IsContactFormAt β x ↔ IsContactFormAt α x := by
  have hker {v : TangentSpace I x} : v ∈ β.ker x ↔ v ∈ α.ker x := by
    rw [RoughForm.mem_ker, RoughForm.mem_ker, hval]
  refine ⟨fun h ↦ ⟨fun h0 ↦ h.ne_zero (hval.trans h0), fun v hv hvw ↦
      h.nondegenerate v (hker.2 hv) fun w hw ↦ ?_⟩,
    fun h ↦ ⟨fun h0 ↦ h.ne_zero (hval.symm.trans h0), fun v hv hvw ↦
      h.nondegenerate v (hker.1 hv) fun w hw ↦ ?_⟩⟩
  · rw [hd v hv w (hker.1 hw)]
    exact hvw w (hker.1 hw)
  · rw [← hd v (hker.1 hv) w hw]
    exact hvw w (hker.2 hw)

/-- For a smooth one-form, the pointwise contact condition at `x` is the linear contact condition
`Module.Dual.IsContact` for the covector `α_x` and the bilinear form of `dα_x`. -/
theorem SmoothForm.isContactFormAt_iff_isContact [IsManifold I 2 M] {α : SmoothForm I M ℝ 1}
    {x : M} :
    IsContactFormAt α.val x ↔ Module.Dual.IsContact
      (SmoothForm.degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
      ((mextDerivₗ I 1 α).bilinFormAt x) :=
  roughForm_isContactFormAt_iff_isContact _ _
    (SmoothForm.degreeOneEquiv_coe_apply α x)
    (fun v w ↦ (SmoothForm.mextDeriv_eq_bilinFormAt α x v w).symm)

/-- A smooth one-form is contact exactly when it satisfies the pointwise contact condition
at every point. -/
theorem SmoothForm.isContactForm_iff_forall_isContactFormAt [IsManifold I 2 M]
    {α : SmoothForm I M ℝ 1} : α.IsContactForm ↔ ∀ x, IsContactFormAt α.val x :=
  forall_congr' fun _ ↦ SmoothForm.isContactFormAt_iff_isContact.symm

end Pointwise

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On a normed space, a one-form `α` is a contact form at `x` exactly when the covector `α(x)` is
a contact covector for the bilinear form of `dα(x)`. -/
theorem isContactFormAt_modelSpace_iff_isContact {α : E → E [⋀^Fin 1]→L[ℝ] ℝ} {x : E} :
    IsContactFormAt (I := 𝓘(ℝ, E)) α x ↔
      Module.Dual.IsContact (ContinuousAlternatingMap.toDual (α x) : E →ₗ[ℝ] ℝ)
        (ContinuousAlternatingMap.flatL ℝ E ℝ (extDeriv α x)).toLinearMap₁₂ :=
  isContactFormAt_iff_isContact_of_equiv (α := (α : RoughForm 𝓘(ℝ, E) E ℝ 1))
    (NormedSpace.fromTangentSpace x)
    (fun _ ↦ by
      simp only [NormedSpace.fromTangentSpace_symm_apply]
      -- `TangentSpace 𝓘(ℝ, E) x` and `E` share the same carrier.
      rfl)
    (fun _ _ ↦ by
      simp only [NormedSpace.fromTangentSpace_symm_apply]
      exact (DFunLike.congr_fun (mextDeriv_eq_extDeriv α x) _).symm)

open scoped Topology in
/-- **Openness of the pointwise contact condition on a normed space.** On a finite-dimensional real
normed space, a one-form that is `C¹` at `x` and is a contact form at `x` remains a contact form
on a neighbourhood of `x`. -/
theorem IsContactFormAt.eventually_modelSpace [FiniteDimensional ℝ E]
    {α : E → E [⋀^Fin 1]→L[ℝ] ℝ} {x : E}
    (hc : IsContactFormAt (I := 𝓘(ℝ, E)) α x) (hα : ContDiffAt ℝ 1 α x) :
    ∀ᶠ y in 𝓝 x, IsContactFormAt (I := 𝓘(ℝ, E)) α y := by
  let αR : RoughForm 𝓘(ℝ, E) E ℝ 1 := α
  exact hc.eventually (contMDiffAt_form_modelSpace_iff (φ := αR).2 hα)

end ModelSpace

end TauCeti
