/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.LinearAlgebra.BilinearForm.Contact
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

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
(`TauCeti.SmoothForm.IsContactForm.finrank_kerDistribution_add_one`).

Only the hyperplane field `ξ` is invariant: multiplying `α` by a nowhere vanishing `C¹` function
`f` leaves `ξ` unchanged and gives again a contact form
(`TauCeti.SmoothForm.isContactForm_iff_of_eq_smul`). The proof is the Leibniz rule
`d(f α) = df ∧ α + f dα`: the term `df ∧ α` vanishes on `ξ × ξ`, so on `ξ` the form `d(f α)` is
`f dα`. In particular `-α`, which defines the opposite coorientation of `ξ`, is again a contact
form (`TauCeti.SmoothForm.isContactForm_neg_iff`).

## Main declarations

* `TauCeti.SmoothForm.kerDistribution`: the hyperplane field `ker α` of a real one-form.
* `TauCeti.SmoothForm.IsContactForm`: the contact condition.
* `TauCeti.SmoothForm.isContactForm_iff`: the elementwise statement of the contact condition.
* `TauCeti.SmoothForm.isContactForm_iff_of_eq_smul`,
  `TauCeti.SmoothForm.kerDistribution_of_eq_smul`: rescaling by a nowhere vanishing function.
* `TauCeti.SmoothForm.isContactForm_smul_iff`, `TauCeti.SmoothForm.isContactForm_neg_iff`:
  rescaling by a nonzero constant.
* `TauCeti.SmoothForm.IsContactForm.odd_finrank`: contact manifolds are odd-dimensional.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Sections 1.1 and 2.1.
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
  LinearMap.ker (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)

@[simp]
theorem mem_kerDistribution {α : SmoothForm I M ℝ 1} {x : M} {v : TangentSpace I x} :
    v ∈ α.kerDistribution x ↔ α.1 x ![v] = 0 := by
  rw [kerDistribution, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, degreeOneEquiv_apply_apply,
    Matrix.vec_single_eq_const]

/-- A real one-form `α` is a **contact form** when, at every point `x`, the covector `α_x` is
nonzero and `dα_x` restricts to a nondegenerate bilinear form on `ker α_x`. -/
def IsContactForm (α : SmoothForm I M ℝ 1) : Prop :=
  ∀ x, Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
    ((mextDerivₗ I 1 α).bilinFormAt x)

/-- The contact condition, elementwise: at each point `α` does not vanish, and the only vector
of `ker α` which is `dα`-orthogonal to all of `ker α` is zero. -/
theorem isContactForm_iff {α : SmoothForm I M ℝ 1} :
    α.IsContactForm ↔
      ∀ x, (∃ v : TangentSpace I x, α.1 x ![v] ≠ 0) ∧
        ∀ v : TangentSpace I x, α.1 x ![v] = 0 →
          (∀ w : TangentSpace I x, α.1 x ![w] = 0 → mextDeriv α.1 x ![v, w] = 0) → v = 0 := by
  refine forall_congr' fun x ↦ ?_
  rw [Module.Dual.isContact_iff_of_isRefl (isAlt_bilinFormAt _ x).isRefl]
  have hα : ∀ v : TangentSpace I x,
      (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ) v = α.1 x ![v] := fun v ↦ by
    rw [ContinuousLinearMap.coe_coe, degreeOneEquiv_apply_apply, Matrix.vec_single_eq_const]
  simp only [hα, bilinFormAt_apply, eval₂_apply, mextDerivₗ_apply, ne_eq, LinearMap.ext_iff,
    LinearMap.zero_apply, not_forall]

/-- A contact form does not vanish. -/
theorem IsContactForm.exists_ne_zero {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) (x : M) :
    ∃ v : TangentSpace I x, α.1 x ![v] ≠ 0 :=
  (isContactForm_iff.1 hα x).1

/-- If `β = f α` for a nowhere vanishing function `f`, then `α` and `β` have the same kernel. -/
theorem kerDistribution_of_eq_smul {α β : SmoothForm I M ℝ 1} {f : M → ℝ}
    (hf₀ : ∀ x, f x ≠ 0) (hβ : ∀ x, β.1 x = f x • α.1 x) :
    β.kerDistribution = α.kerDistribution := by
  ext x v
  rw [mem_kerDistribution, mem_kerDistribution, hβ, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, mul_eq_zero, or_iff_right (hf₀ x)]

/-- **Rescaling of contact forms.** If `β = f α` for a nowhere vanishing `C¹` function `f`, then
`β` is a contact form exactly when `α` is. -/
theorem isContactForm_iff_of_eq_smul {α β : SmoothForm I M ℝ 1} {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) (hf₀ : ∀ x, f x ≠ 0) (hβ : ∀ x, β.1 x = f x • α.1 x) :
    β.IsContactForm ↔ α.IsContactForm := by
  refine forall_congr' fun x ↦ ?_
  set a := (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
  have ha : ∀ v, a v = α.1 x ![v] := fun v ↦ by
    rw [ContinuousLinearMap.coe_coe, degreeOneEquiv_apply_apply, Matrix.vec_single_eq_const]
  have hb : (degreeOneEquiv β x : TangentSpace I x →ₗ[ℝ] ℝ) = f x • a := by
    ext v
    rw [ContinuousLinearMap.coe_coe, degreeOneEquiv_apply_apply, hβ, LinearMap.smul_apply,
      ContinuousAlternatingMap.smul_apply, ha, Matrix.vec_single_eq_const]
  -- On `ker α`, the Leibniz rule `d(f α) = df ∧ α + f dα` reduces `dβ` to `f dα`.
  have hdβ : ∀ v w, a v = 0 → a w = 0 →
      (mextDerivₗ I 1 β).bilinFormAt x v w = (f x • (mextDerivₗ I 1 α).bilinFormAt x) v w := by
    intro v w hv hw
    have hβ' : β.1 = fun y ↦ f y • α.1 y := funext hβ
    rw [ha] at hv hw
    simp only [bilinFormAt_apply, eval₂_apply, mextDerivₗ_apply, LinearMap.smul_apply,
      smul_eq_mul, hβ', mextDeriv_fun_smul_apply (hf x) (α.mdifferentiableAt x), hv, hw,
      mul_zero, sub_zero, zero_add]
  rw [hb, Module.Dual.isContact_smul_iff (hf₀ x), Module.Dual.isContact_congr hdβ,
    Module.Dual.isContact_smul_bilinForm_iff (hf₀ x)]

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
    finrank ℝ (α.kerDistribution x) + 1 = finrank ℝ E :=
  Module.Dual.finrank_ker_add_one_of_ne_zero (hα x).ne_zero

/-- The model space of a manifold carrying a contact form is odd-dimensional, as soon as the
manifold is nonempty. -/
theorem IsContactForm.odd_finrank [FiniteDimensional ℝ E] {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (x : M) : Odd (finrank ℝ E) :=
  (hα x).odd_finrank (isAlt_bilinFormAt _ x)

end SmoothForm

end TauCeti
