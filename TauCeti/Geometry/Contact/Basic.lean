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

A rough one-form satisfies the pointwise condition `TauCeti.IsContactFormAt` at `x` when it is
nonzero there and its exterior derivative is nondegenerate on its kernel. This condition imposes
no global regularity. For a smooth one-form it agrees with the canonical contact condition, by
`TauCeti.SmoothForm.isContactForm_iff_forall_isContactFormAt`. For a one-form and a scalar
function that are both differentiable at `x`, rescaling by the function preserves the pointwise
condition whenever its value at `x` is nonzero (`TauCeti.isContactFormAt_fun_smul_iff`).

## Main declarations

* `TauCeti.SmoothForm.kerDistribution`: the hyperplane field `ker α` of a real one-form.
* `TauCeti.SmoothForm.IsContactForm`: the contact condition.
* `TauCeti.SmoothForm.isContactForm_def`, `TauCeti.SmoothForm.isContactForm_iff`: the pointwise
  and elementwise statements of the contact condition.
* `TauCeti.SmoothForm.isContactForm_iff_of_eq_smul`,
  `TauCeti.SmoothForm.kerDistribution_of_eq_smul`: rescaling by a nowhere vanishing function.
* `TauCeti.SmoothForm.isContactForm_smul_iff`, `TauCeti.SmoothForm.isContactForm_neg_iff`:
  rescaling by a nonzero constant.
* `TauCeti.SmoothForm.IsContactForm.odd_finrank`: contact manifolds are odd-dimensional.
* `TauCeti.IsContactFormAt`: the pointwise contact condition for a rough one-form, with
  `TauCeti.isContactFormAt_neg_iff`, `TauCeti.isContactFormAt_fun_smul_iff` and
  `TauCeti.SmoothForm.isContactForm_iff_forall_isContactFormAt`.

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
  RoughForm.ker α.1 x

@[simp]
theorem mem_kerDistribution {α : SmoothForm I M ℝ 1} {x : M} {v : TangentSpace I x} :
    v ∈ α.kerDistribution x ↔ α.1 x ![v] = 0 := by
  exact RoughForm.mem_ker

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
      ∀ x, (∃ v : TangentSpace I x, α.1 x ![v] ≠ 0) ∧
        ∀ v : TangentSpace I x, α.1 x ![v] = 0 →
          (∀ w : TangentSpace I x, α.1 x ![w] = 0 → mextDeriv α.1 x ![v, w] = 0) → v = 0 := by
  refine forall_congr' fun x ↦ ?_
  rw [Module.Dual.isContact_iff_of_isRefl (isAlt_bilinFormAt _ x).isRefl]
  simp only [degreeOneEquiv_coe_apply, bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
    mextDerivₗ_apply, ne_eq, LinearMap.ext_iff, LinearMap.zero_apply, not_forall]

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
  have ha : ∀ v, a v = α.1 x ![v] := degreeOneEquiv_coe_apply α x
  have hb : (degreeOneEquiv β x : TangentSpace I x →ₗ[ℝ] ℝ) = f x • a := by
    ext v
    rw [degreeOneEquiv_coe_apply, hβ, LinearMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      ha]
  -- On `ker α`, the Leibniz rule `d(f α) = df ∧ α + f dα` reduces `dβ` to `f dα`.
  have hdβ : ∀ v w, a v = 0 → a w = 0 →
      (mextDerivₗ I 1 β).bilinFormAt x v w = (f x • (mextDerivₗ I 1 α).bilinFormAt x) v w := by
    intro v w hv hw
    have hβ' : β.1 = fun y ↦ f y • α.1 y := funext hβ
    rw [ha] at hv hw
    simp only [bilinFormAt_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply,
      LinearMap.smul_apply, smul_eq_mul, hβ',
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
  have hk : α.kerDistribution x =
      LinearMap.ker (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ) := by
    ext v
    rw [mem_kerDistribution, LinearMap.mem_ker, degreeOneEquiv_coe_apply]
  rw [hk]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero (hα x).ne_zero

/-- The model space of a manifold carrying a contact form is odd-dimensional, as soon as the
manifold is nonempty. -/
theorem IsContactForm.odd_finrank [FiniteDimensional ℝ E] {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (x : M) : Odd (finrank ℝ E) :=
  (hα x).odd_finrank (isAlt_bilinFormAt _ x)

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

/-- A smooth one-form is contact exactly when it satisfies the pointwise contact condition
at every point. -/
theorem SmoothForm.isContactForm_iff_forall_isContactFormAt [IsManifold I 2 M]
    {α : SmoothForm I M ℝ 1} : α.IsContactForm ↔ ∀ x, IsContactFormAt α.1 x := by
  rw [SmoothForm.isContactForm_iff]
  refine forall_congr' fun x ↦ ?_
  constructor
  · rintro ⟨⟨v, hv⟩, h⟩
    refine ⟨fun hz ↦ hv (by rw [hz]; rfl), ?_⟩
    simpa only [RoughForm.mem_ker] using h
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hn
      push Not at hn
      apply h.ne_zero
      ext v
      have hv : ![v 0] = v := by
        ext i
        fin_cases i
        rfl
      simpa only [hv, ContinuousAlternatingMap.coe_zero, Pi.zero_apply] using hn (v 0)
    · simpa only [RoughForm.mem_ker] using h.nondegenerate

end Pointwise

end TauCeti
