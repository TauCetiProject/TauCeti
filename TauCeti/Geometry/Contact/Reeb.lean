/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# The Reeb vector field of a contact form

Let `α` be a contact form on a finite-dimensional manifold `M`. At each point `x`, the two-form
`dα_x` is nondegenerate on the hyperplane `ξ_x = ker α_x`, so it has a one-dimensional kernel
transverse to `ξ_x`. The **Reeb vector field** `R_α` (`TauCeti.SmoothForm.reebVectorField`) is the
vector field spanning this kernel and normalized by `α`:

`α(R_α) = 1`, `ι_(R_α) dα = 0`.

These two equations determine `R_α` uniquely
(`TauCeti.SmoothForm.IsContactForm.eq_reebVectorField_iff`), and it is enough to test the second
one against vectors of `ξ`
(`TauCeti.SmoothForm.IsContactForm.eq_reebVectorField_iff_kerDistribution`).
At each point the tangent space splits as `ξ_x ⊕ ℝ R_α(x)`.

Unlike the contact distribution `ξ`, the Reeb field depends on the contact form, not only on its
kernel. For a nowhere vanishing function `f`, the **rescaling law**
(`TauCeti.SmoothForm.IsContactForm.reebVectorField_eq_inv_smul_add_iff`) reads

`R_(f α) = R_α / f + Y`,

where `Y` is the unique vector field in `ξ` with `dα(Y, w) = df(w) / f²` for all `w ∈ ξ`. For a
constant `c ≠ 0` this gives `R_(c α) = R_α / c`
(`TauCeti.SmoothForm.IsContactForm.reebVectorField_smul`), and in particular `R_(-α) = -R_α`.

All statements here are pointwise linear algebra at each point, applying
`Module.Dual.reebVector` to the covector `α_x` and the bilinear form `dα_x`.

## Main declarations

* `TauCeti.SmoothForm.reebVectorField`: the Reeb vector field of a one-form.
* `TauCeti.SmoothForm.IsContactForm.apply_reebVectorField`,
  `TauCeti.SmoothForm.IsContactForm.mextDeriv_reebVectorField_left`: the Reeb equations.
* `TauCeti.SmoothForm.IsContactForm.eq_reebVectorField_iff`: uniqueness.
* `TauCeti.SmoothForm.IsContactForm.isCompl_kerDistribution_span_reebVectorField`: the splitting
  `T_x M = ξ_x ⊕ ℝ R_α(x)`.
* `TauCeti.SmoothForm.IsContactForm.reebVectorField_eq_inv_smul_add_iff`: the rescaling law.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1.
-/

public section

noncomputable section

open Module
open scoped Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- The **Reeb vector field** of a one-form `α`: at each point `x`, the tangent vector `R` with
`α_x(R) = 1` and `dα_x(R, w) = 0` for every `w ∈ ker α_x`. For a contact form on a
finite-dimensional manifold it exists and is unique
(`TauCeti.SmoothForm.IsContactForm.eq_reebVectorField_iff`); it is the Reeb vector
`Module.Dual.reebVector` of the covector `α_x` for the bilinear form `dα_x`. -/
def reebVectorField (α : SmoothForm I M ℝ 1) (x : M) : TangentSpace I x :=
  Module.Dual.reebVector (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
    ((mextDerivₗ I 1 α).bilinFormAt x)

variable [FiniteDimensional ℝ E] {α : SmoothForm I M ℝ 1}

/-- **Characterization of the Reeb vector field**, tested on the contact distribution: `R_α(x)` is
the unique tangent vector `v` with `α(v) = 1` and `dα(v, w) = 0` for all `w ∈ ker α_x`. -/
theorem IsContactForm.eq_reebVectorField_iff_kerDistribution (hα : α.IsContactForm) {x : M}
    {v : TangentSpace I x} :
    v = α.reebVectorField x ↔
      α.1 x ![v] = 1 ∧ ∀ w : TangentSpace I x, α.1 x ![w] = 0 → mextDeriv α.1 x ![v, w] = 0 := by
  rw [reebVectorField, (isContactForm_def.1 hα x).eq_reebVector_iff]
  simp only [degreeOneEquiv_coe_apply, bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
    mextDerivₗ_apply]

/-- A contact form takes the value `1` on its Reeb vector field. -/
@[simp]
theorem IsContactForm.apply_reebVectorField (hα : α.IsContactForm) (x : M) :
    α.1 x ![α.reebVectorField x] = 1 :=
  (hα.eq_reebVectorField_iff_kerDistribution.1 rfl).1

/-- The Reeb vector field lies in the kernel of `dα`: `ι_(R_α) dα = 0`. -/
@[simp]
theorem IsContactForm.mextDeriv_reebVectorField_left (hα : α.IsContactForm) (x : M)
    (w : TangentSpace I x) : mextDeriv α.1 x ![α.reebVectorField x, w] = 0 := by
  have := (isContactForm_def.1 hα x).apply_reebVector_left (isAlt_bilinFormAt _ x) w
  rwa [bilinFormAt_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply] at this

/-- The Reeb vector field lies in the kernel of `dα`: `dα` vanishes when its second argument is
the Reeb vector field. -/
@[simp]
theorem IsContactForm.mextDeriv_reebVectorField_right (hα : α.IsContactForm) (x : M)
    (w : TangentSpace I x) : mextDeriv α.1 x ![w, α.reebVectorField x] = 0 := by
  have := (isContactForm_def.1 hα x).apply_reebVector_right (isAlt_bilinFormAt _ x) w
  rwa [bilinFormAt_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply] at this

/-- **Characterization of the Reeb vector field**: `R_α(x)` is the unique tangent vector `v` with
`α(v) = 1` and `ι_v dα = 0`. -/
theorem IsContactForm.eq_reebVectorField_iff (hα : α.IsContactForm) {x : M}
    {v : TangentSpace I x} :
    v = α.reebVectorField x ↔
      α.1 x ![v] = 1 ∧ ∀ w : TangentSpace I x, mextDeriv α.1 x ![v, w] = 0 := by
  rw [hα.eq_reebVectorField_iff_kerDistribution]
  refine and_congr_right fun _ ↦ ⟨fun h w ↦ ?_, fun h w _ ↦ h w⟩
  have hv : v = α.reebVectorField x :=
    hα.eq_reebVectorField_iff_kerDistribution.2 ⟨‹_›, h⟩
  rw [hv]
  exact hα.mextDeriv_reebVectorField_left x w

/-- The Reeb vector field of a contact form vanishes nowhere. -/
theorem IsContactForm.reebVectorField_ne_zero (hα : α.IsContactForm) (x : M) :
    α.reebVectorField x ≠ 0 :=
  (isContactForm_def.1 hα x).reebVector_ne_zero

/-- The Reeb vector field is transverse to the contact distribution. -/
theorem IsContactForm.reebVectorField_notMem_kerDistribution (hα : α.IsContactForm) (x : M) :
    α.reebVectorField x ∉ α.kerDistribution x := by
  rw [kerDistribution_def]
  exact (isContactForm_def.1 hα x).reebVector_notMem_ker

/-- The tangent space of a contact manifold splits as the contact hyperplane plus the Reeb line,
`T_x M = ξ_x ⊕ ℝ R_α(x)`. -/
theorem IsContactForm.isCompl_kerDistribution_span_reebVectorField (hα : α.IsContactForm)
    (x : M) : IsCompl (α.kerDistribution x) (ℝ ∙ α.reebVectorField x) := by
  rw [kerDistribution_def]
  exact (isContactForm_def.1 hα x).isCompl_ker_span_reebVector

/-- **Rescaling law for the Reeb vector field.** Let `α` be a contact form and `β = f α` for a
function `f`, `C¹` and nonzero at `x`. Then `R_β(x) = R_α(x) / f(x) + y` exactly when `y` lies in
`ξ_x = ker α_x` and `dα(y, w) = df(w) / f(x)²` for all `w ∈ ξ_x`. In particular
`R_β(x) - R_α(x) / f(x)` is the unique such vector. -/
theorem IsContactForm.reebVectorField_eq_inv_smul_add_iff (hα : α.IsContactForm)
    {β : SmoothForm I M ℝ 1} {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f x)
    (hf₀ : f x ≠ 0) (hβ : ∀ y, β.1 y = f y • α.1 y) (y : TangentSpace I x) :
    β.reebVectorField x = (f x)⁻¹ • α.reebVectorField x + y ↔
      α.1 x ![y] = 0 ∧ ∀ w : TangentSpace I x, α.1 x ![w] = 0 →
        mextDeriv α.1 x ![y, w] = mvfderiv I f x w / f x ^ 2 := by
  set a := (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
  have ha : ∀ v, a v = α.1 x ![v] := degreeOneEquiv_coe_apply α x
  have hb : (degreeOneEquiv β x : TangentSpace I x →ₗ[ℝ] ℝ) = f x • a := by
    ext v
    rw [degreeOneEquiv_coe_apply, hβ, LinearMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      ha]
  -- The Leibniz rule `d(f α) = df ∧ α + f dα`, evaluated against a vector of `ker α`.
  have hdβ : ∀ v w, a w = 0 → (mextDerivₗ I 1 β).bilinFormAt x v w =
      f x * (mextDerivₗ I 1 α).bilinFormAt x v w -
        (mvfderiv I f x : TangentSpace I x →ₗ[ℝ] ℝ) w * a v := by
    intro v w hw
    have hβ' : β.1 = fun y ↦ f y • α.1 y := funext hβ
    rw [ha] at hw
    simp only [bilinFormAt_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply, hβ',
      mextDeriv_fun_smul_apply (hf.mdifferentiableAt one_ne_zero)
        (α.mdifferentiableAt x), hw, ha, ContinuousLinearMap.coe_coe]
    ring
  rw [reebVectorField, reebVectorField, hb,
    (isContactForm_def.1 hα x).reebVector_smul_eq_inv_smul_add_iff hf₀ hdβ y]
  simp only [degreeOneEquiv_coe_apply, bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
    mextDerivₗ_apply]
  simp only [ContinuousLinearMap.coe_coe]

/-- Multiplying a contact form by a nonzero constant `c` divides its Reeb vector field by `c`. -/
theorem IsContactForm.reebVectorField_smul (hα : α.IsContactForm) {c : ℝ} (hc : c ≠ 0)
    (x : M) : (c • α).reebVectorField x = c⁻¹ • α.reebVectorField x := by
  have ha : (degreeOneEquiv (c • α) x : TangentSpace I x →ₗ[ℝ] ℝ) =
      c • (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ) := by
    ext v
    simp only [degreeOneEquiv_coe_apply, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
      ContinuousAlternatingMap.smul_apply]
  have hB : (mextDerivₗ I 1 (c • α)).bilinFormAt x = c • (mextDerivₗ I 1 α).bilinFormAt x := by
    ext v w
    simp only [map_smul, bilinFormAt_apply, SmoothBundleForm.eval₂_apply, LinearMap.smul_apply,
      Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply]
  rw [reebVectorField, reebVectorField, ha, hB, Module.Dual.reebVector_smul_bilinForm hc,
    (isContactForm_def.1 hα x).reebVector_smul hc]

/-- The Reeb vector field of `-α` is `-R_α`. -/
theorem IsContactForm.reebVectorField_neg (hα : α.IsContactForm) (x : M) :
    (-α).reebVectorField x = -α.reebVectorField x := by
  rw [← neg_one_smul ℝ α, hα.reebVectorField_smul (by norm_num), inv_neg, inv_one, neg_one_smul]

end SmoothForm

end TauCeti
