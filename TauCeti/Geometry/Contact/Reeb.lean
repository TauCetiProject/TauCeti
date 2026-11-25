/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.StableHamiltonian
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.LinearAlgebra.Projection.SplittingEquiv
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

where `Y` is the unique vector field in `ξ` with `dα(Y, w) = df(w) / f²` for all `w ∈ ξ`. Where
`f ≠ 0` it takes the normalized form
(`TauCeti.SmoothForm.IsContactForm.smul_reebVectorField_eq_add_iff`)

`R_(f α) = (R_α + Z) / f`,

where `Z = f Y = f R_(f α) - R_α` is the unique vector field in `ξ` with `dα(Z, w) = df(w) / f`
for all `w ∈ ξ`
(`TauCeti.SmoothForm.IsContactForm.eq_smul_reebVectorField_sub_reebVectorField_iff`).
Evaluating `α` on it gives `α(R_(f α)) = 1 / f`
(`TauCeti.SmoothForm.IsContactForm.apply_reebVectorField_of_eq_smul`), which is where the factor
`f²` in the equation for `Y` comes from. For a constant `c ≠ 0` this gives `R_(c α) = R_α / c`
(`TauCeti.SmoothForm.IsContactForm.reebVectorField_smul`), and in particular `R_(-α) = -R_α`.

The Reeb vector field is the characteristic vector field of the stable Hamiltonian structure
`(α, dα)` (`TauCeti.SmoothForm.characteristicVectorField_mextDerivₗ`), so its basic equations are
the special case `ω = dα` of those in `TauCeti.Geometry.Contact.StableHamiltonian`. The rescaling
law is pointwise linear algebra at each point, applying `Module.Dual.reebVector` to the covector
`α_x` and the bilinear form `dα_x`.

## Main declarations

* `TauCeti.SmoothForm.reebVectorField`: the Reeb vector field of a one-form.
* `TauCeti.SmoothForm.reebVectorField_congr`: the Reeb vector at a point only depends on the values
  of the form and of its exterior derivative there.
* `TauCeti.SmoothForm.IsContactForm.apply_reebVectorField`,
  `TauCeti.SmoothForm.IsContactForm.mextDeriv_reebVectorField_left`: the Reeb equations, with
  pointwise versions `TauCeti.SmoothForm.apply_reebVectorField_of_isContactFormAt` and
  `TauCeti.SmoothForm.mextDeriv_reebVectorField_left_of_isContactFormAt` at a single contact point.
* `TauCeti.SmoothForm.IsContactForm.interior_mextDeriv_reebVectorField`: the second Reeb
  equation `ι_(R_α) dα = 0` as an identity of one-forms.
* `TauCeti.SmoothForm.IsContactForm.eq_reebVectorField_iff`: uniqueness.
* `TauCeti.SmoothForm.IsContactForm.isCompl_kerDistribution_span_reebVectorField`: the splitting
  `T_x M = ξ_x ⊕ ℝ R_α(x)`.
* `TauCeti.SmoothForm.IsContactForm.kerSectionEquivKerDistribution`: projection along `R_α(x)` from
  the tangent hyperplane `ker dg_x` of a transverse function to `ξ_x`.
* `TauCeti.SmoothForm.IsContactForm.exists_contMDiffAt_and_mvfderiv_reebVectorField_eq_one`:
  existence of a function `g`, `C^n` at `x`, with `dg_x(R_α x) = 1`.
* `TauCeti.SmoothForm.IsContactForm.reebVectorField_eq_inv_smul_add_iff`: the rescaling law.
* `TauCeti.SmoothForm.IsContactForm.smul_reebVectorField_eq_add_iff`: its normalized form
  `f R_(f α) = R_α + Z`.
* `TauCeti.SmoothForm.IsContactForm.eq_smul_reebVectorField_sub_reebVectorField_iff`: the
  correction `Z = f R_(f α) - R_α` is the unique such vector.
* `TauCeti.SmoothForm.IsContactForm.apply_reebVectorField_of_eq_smul`: `α(R_(f α)) = 1 / f`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1.
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- The **Reeb vector field** of a one-form `α`: at each point `x`, the tangent vector `R` with
`α_x(R) = 1` and `dα_x(R, w) = 0` for every `w ∈ ker α_x`. For a contact form on a
finite-dimensional manifold it exists and is unique
(`TauCeti.SmoothForm.IsContactForm.eq_reebVectorField_iff`); it is the characteristic vector
field of the pair `(α, dα)`, the Reeb vector `Module.Dual.reebVector` of the covector `α_x` for
the bilinear form `dα_x`. -/
def reebVectorField (α : SmoothForm I M ℝ 1) (x : M) : TangentSpace I x :=
  α.characteristicVectorField (mextDerivₗ I 1 α) x

/-- The characteristic vector field of a one-form `α` and its exterior derivative is the Reeb
vector field of `α`. -/
@[simp]
theorem characteristicVectorField_mextDerivₗ (α : SmoothForm I M ℝ 1) :
    α.characteristicVectorField (mextDerivₗ I 1 α) = α.reebVectorField :=
  (rfl)

/-- The Reeb vector of a one-form at a point only depends on the values at that point of the form
and of its exterior derivative. -/
theorem reebVectorField_congr {α β : SmoothForm I M ℝ 1} {x : M} (h : α.val x = β.val x)
    (hd : mextDeriv α.val x = mextDeriv β.val x) :
    α.reebVectorField x = β.reebVectorField x := by
  rw [reebVectorField, reebVectorField, characteristicVectorField_def,
    characteristicVectorField_def]
  congr 1
  · ext v
    rw [degreeOneEquiv_coe_apply, degreeOneEquiv_coe_apply, h]
  · ext v w
    rw [bilinFormAt_apply, bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
      SmoothBundleForm.eval₂_apply, mextDerivₗ_apply, mextDerivₗ_apply, hd]

variable [FiniteDimensional ℝ E] {α : SmoothForm I M ℝ 1}

/-- **Characterization of the Reeb vector field**, tested on the contact distribution: `R_α(x)` is
the unique tangent vector `v` with `α(v) = 1` and `dα(v, w) = 0` for all `w ∈ ker α_x`. -/
theorem IsContactForm.eq_reebVectorField_iff_kerDistribution (hα : α.IsContactForm) {x : M}
    {v : TangentSpace I x} :
    v = α.reebVectorField x ↔
      α.val x ![v] = 1 ∧ ∀ w : TangentSpace I x, α.val x ![w] = 0 → mextDeriv α.val x ![v, w] = 0
          := by
  rw [reebVectorField, characteristicVectorField_def,
    (isContactForm_def.1 hα x).eq_reebVector_iff]
  simp only [degreeOneEquiv_coe_apply, ← mextDeriv_eq_bilinFormAt]

/-- At a point where `α` is a contact form, `α` takes the value `1` on the Reeb vector. -/
theorem apply_reebVectorField_of_isContactFormAt {x : M} (h : IsContactFormAt α.val x) :
    α.val x ![α.reebVectorField x] = 1 := by
  rw [← characteristicVectorField_mextDerivₗ]
  exact apply_characteristicVectorField (isContactFormAt_iff_isContact.1 h)

/-- At a point where `α` is a contact form, the Reeb vector lies in the kernel of `dα_x`. -/
theorem mextDeriv_reebVectorField_left_of_isContactFormAt {x : M} (h : IsContactFormAt α.val x)
    (w : TangentSpace I x) : mextDeriv α.val x ![α.reebVectorField x, w] = 0 := by
  rw [← characteristicVectorField_mextDerivₗ, ← mextDerivₗ_apply]
  exact apply_characteristicVectorField_left (isContactFormAt_iff_isContact.1 h) w

/-- At a point where `α` is a contact form, `dα_x` vanishes when its second argument is the Reeb
vector. -/
theorem mextDeriv_reebVectorField_right_of_isContactFormAt {x : M} (h : IsContactFormAt α.val x)
    (w : TangentSpace I x) : mextDeriv α.val x ![w, α.reebVectorField x] = 0 := by
  rw [← characteristicVectorField_mextDerivₗ, ← mextDerivₗ_apply]
  exact apply_characteristicVectorField_right (isContactFormAt_iff_isContact.1 h) w

/-- A contact form takes the value `1` on its Reeb vector field. -/
@[simp]
theorem IsContactForm.apply_reebVectorField (hα : α.IsContactForm) (x : M) :
    α.val x ![α.reebVectorField x] = 1 :=
  apply_reebVectorField_of_isContactFormAt (isContactForm_iff_forall_isContactFormAt.1 hα x)

/-- The Reeb vector field lies in the kernel of `dα`: `ι_(R_α) dα = 0`. -/
@[simp]
theorem IsContactForm.mextDeriv_reebVectorField_left (hα : α.IsContactForm) (x : M)
    (w : TangentSpace I x) : mextDeriv α.val x ![α.reebVectorField x, w] = 0 :=
  mextDeriv_reebVectorField_left_of_isContactFormAt
    (isContactForm_iff_forall_isContactFormAt.1 hα x) w

/-- The Reeb vector field lies in the kernel of `dα`: `dα` vanishes when its second argument is
the Reeb vector field. -/
@[simp]
theorem IsContactForm.mextDeriv_reebVectorField_right (hα : α.IsContactForm) (x : M)
    (w : TangentSpace I x) : mextDeriv α.val x ![w, α.reebVectorField x] = 0 :=
  mextDeriv_reebVectorField_right_of_isContactFormAt
    (isContactForm_iff_forall_isContactFormAt.1 hα x) w

/-- The second Reeb equation as an identity of one-forms: `ι_(R_α) dα = 0`. -/
theorem IsContactForm.interior_mextDeriv_reebVectorField (hα : α.IsContactForm) :
    (mextDeriv α.val).interior α.reebVectorField = 0 :=
  hα.isStableHamiltonian.interior_mextDeriv_characteristicVectorField

/-- **Characterization of the Reeb vector field**: `R_α(x)` is the unique tangent vector `v` with
`α(v) = 1` and `ι_v dα = 0`. -/
theorem IsContactForm.eq_reebVectorField_iff (hα : α.IsContactForm) {x : M}
    {v : TangentSpace I x} :
    v = α.reebVectorField x ↔
      α.val x ![v] = 1 ∧ ∀ w : TangentSpace I x, mextDeriv α.val x ![v, w] = 0 := by
  rw [reebVectorField, eq_characteristicVectorField_iff (isContactForm_def.1 hα x),
    mextDerivₗ_apply]

/-- The Reeb vector field of a contact form vanishes nowhere. -/
theorem IsContactForm.reebVectorField_ne_zero (hα : α.IsContactForm) (x : M) :
    α.reebVectorField x ≠ 0 :=
  characteristicVectorField_ne_zero (isContactForm_def.1 hα x)

/-- The Reeb vector field is transverse to the contact distribution. -/
theorem IsContactForm.reebVectorField_notMem_kerDistribution (hα : α.IsContactForm) (x : M) :
    α.reebVectorField x ∉ α.kerDistribution x :=
  characteristicVectorField_notMem_kerDistribution (isContactForm_def.1 hα x)

/-- The tangent space of a contact manifold splits as the contact hyperplane plus the Reeb line,
`T_x M = ξ_x ⊕ ℝ R_α(x)`. -/
theorem IsContactForm.isCompl_kerDistribution_span_reebVectorField (hα : α.IsContactForm)
    (x : M) : IsCompl (α.kerDistribution x) (ℝ ∙ α.reebVectorField x) :=
  isCompl_kerDistribution_span_characteristicVectorField (isContactForm_def.1 hα x)

/-- The projection along `R_α(x)` gives a linear equivalence between the tangent space `ker dg_x`
of any function `g` with `dg_x(R_α x) ≠ 0` and the contact hyperplane `ξ_x = ker α_x`. -/
def IsContactForm.kerSectionEquivKerDistribution (hα : α.IsContactForm) {g : M → ℝ} {x : M}
    (hgv : mvfderiv I g x (α.reebVectorField x) ≠ 0) :
    LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] α.kerDistribution x :=
  Submodule.equivOfIsCompl _ _ (ℝ ∙ α.reebVectorField x)
    (isCompl_ker_mvfderiv_span_singleton hgv)
    (hα.isCompl_kerDistribution_span_reebVectorField x)

/-- Unfolds `IsContactForm.kerSectionEquivKerDistribution` as `Submodule.equivOfIsCompl` along
`ℝ ∙ R_α(x)`. -/
theorem IsContactForm.kerSectionEquivKerDistribution_def (hα : α.IsContactForm) {g : M → ℝ}
    {x : M} (hgv : mvfderiv I g x (α.reebVectorField x) ≠ 0) :
    hα.kerSectionEquivKerDistribution hgv =
      Submodule.equivOfIsCompl _ _ (ℝ ∙ α.reebVectorField x)
        (isCompl_ker_mvfderiv_span_singleton hgv)
        (hα.isCompl_kerDistribution_span_reebVectorField x) :=
  (rfl)

/-- `kerSectionEquivKerDistribution` evaluates by projecting onto `α.kerDistribution x` along
`ℝ ∙ R_α(x)`. -/
@[simp]
theorem IsContactForm.kerSectionEquivKerDistribution_apply (hα : α.IsContactForm) {g : M → ℝ}
    {x : M} (hgv : mvfderiv I g x (α.reebVectorField x) ≠ 0)
    (v : LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ)) :
    hα.kerSectionEquivKerDistribution hgv v =
      (α.kerDistribution x).projectionOnto (ℝ ∙ α.reebVectorField x)
        (hα.isCompl_kerDistribution_span_reebVectorField x) v :=
  Submodule.equivOfIsCompl_apply _ _ _ _ _ v

/-- The inverse of `kerSectionEquivKerDistribution` evaluates by projecting onto `ker dg_x` along
`ℝ ∙ R_α(x)`. -/
@[simp]
theorem IsContactForm.kerSectionEquivKerDistribution_symm_apply (hα : α.IsContactForm)
    {g : M → ℝ} {x : M} (hgv : mvfderiv I g x (α.reebVectorField x) ≠ 0)
    (v : α.kerDistribution x) :
    (hα.kerSectionEquivKerDistribution hgv).symm v =
      (LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ)).projectionOnto
        (ℝ ∙ α.reebVectorField x) (isCompl_ker_mvfderiv_span_singleton hgv) v :=
  Submodule.equivOfIsCompl_symm_apply _ _ _ _ _ v

/-- At any point `x` and for any regularity `n`, there exists a function `g : M → ℝ`, `C^n` at
`x`, with `dg_x(R_α x) = 1`, whose level `{g = g x}` is a local section transverse to the Reeb
vector field. -/
theorem IsContactForm.exists_contMDiffAt_and_mvfderiv_reebVectorField_eq_one
    (hα : α.IsContactForm) (n : ℕ∞ω) (x : M) :
    ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) n g x ∧ mvfderiv I g x (α.reebVectorField x) = 1 :=
  exists_contMDiffAt_mvfderiv_eq_one (hα.reebVectorField_ne_zero x) n

/-- At a point where `α` is a contact form, removing its Reeb component `α(v) R_α` from a tangent
vector `v` leaves a vector of `ker α_x`. -/
theorem sub_smul_reebVectorField_mem_kerDistribution_of_isContactFormAt {x : M}
    (h : IsContactFormAt α.val x) (v : TangentSpace I x) :
    v - α.val x ![v] • α.reebVectorField x ∈ α.kerDistribution x := by
  simp [mem_kerDistribution, ContinuousAlternatingMap.vecCons_smul,
    apply_reebVectorField_of_isContactFormAt h]

/-- Removing its Reeb component `α(v) R_α` from a tangent vector `v` leaves a vector of the
contact distribution. -/
theorem IsContactForm.sub_smul_reebVectorField_mem_kerDistribution (hα : α.IsContactForm)
    {x : M} (v : TangentSpace I x) :
    v - α.val x ![v] • α.reebVectorField x ∈ α.kerDistribution x :=
  sub_smul_reebVectorField_mem_kerDistribution_of_isContactFormAt
    (isContactForm_iff_forall_isContactFormAt.1 hα x) v

/-- **Rescaling law for the Reeb vector field.** Let `α` be a contact form and `β = f α` for a
function `f`, `C¹` at `x`. Then `R_β(x) = R_α(x) / f(x) + y` exactly when `y` lies in
`ξ_x = ker α_x` and `dα(y, w) = df(w) / f(x)²` for all `w ∈ ξ_x`. In particular
`R_β(x) - R_α(x) / f(x)` is the unique such vector. For `f(x) = 0` both sides say `y = 0`, by the
junk values `0⁻¹ = 0` and `df(w) / 0 = 0`. -/
theorem IsContactForm.reebVectorField_eq_inv_smul_add_iff (hα : α.IsContactForm)
    {β : SmoothForm I M ℝ 1} {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f x)
    (hβ : ∀ y, β.val y = f y • α.val y) (y : TangentSpace I x) :
    β.reebVectorField x = (f x)⁻¹ • α.reebVectorField x + y ↔
      α.val x ![y] = 0 ∧ ∀ w : TangentSpace I x, α.val x ![w] = 0 →
        mextDeriv α.val x ![y, w] = mvfderiv I f x w / f x ^ 2 := by
  set a := (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
  have ha : ∀ v, a v = α.val x ![v] := degreeOneEquiv_coe_apply α x
  have hb : (degreeOneEquiv β x : TangentSpace I x →ₗ[ℝ] ℝ) = f x • a := by
    ext v
    rw [degreeOneEquiv_coe_apply, hβ, LinearMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      ha]
  -- The Leibniz rule `d(f α) = df ∧ α + f dα`, evaluated against a vector of `ker α`.
  have hdβ : ∀ v w, a w = 0 → (mextDerivₗ I 1 β).bilinFormAt x v w =
      f x * (mextDerivₗ I 1 α).bilinFormAt x v w -
        (mvfderiv I f x : TangentSpace I x →ₗ[ℝ] ℝ) w * a v := by
    intro v w hw
    have hβ' : β.val = fun y ↦ f y • α.val y := funext hβ
    rw [ha] at hw
    simp only [← mextDeriv_eq_bilinFormAt, hβ', mextDeriv_fun_smul_apply
      (hf.mdifferentiableAt one_ne_zero) (α.mdifferentiableAt x), hw, ha,
      ContinuousLinearMap.coe_coe]
    ring
  rw [reebVectorField, reebVectorField, characteristicVectorField_def,
    characteristicVectorField_def, hb,
    (isContactForm_def.1 hα x).reebVector_smul_eq_inv_smul_add_iff hdβ y]
  simp only [degreeOneEquiv_coe_apply, ← mextDeriv_eq_bilinFormAt]
  simp only [ContinuousLinearMap.coe_coe]

/-- **Normalized rescaling law for the Reeb vector field.** Let `α` be a contact form and
`β = f α` for a function `f`, `C¹` at `x`, with `f(x) ≠ 0`. Then `f(x) R_β(x) = R_α(x) + z`, that
is `R_β(x) = (R_α(x) + z) / f(x)`, exactly when `z` lies in `ξ_x = ker α_x` and
`dα(z, w) = df(w) / f(x)` for all `w ∈ ξ_x`. In particular `f(x) R_β(x) - R_α(x)` is the unique
such vector. -/
theorem IsContactForm.smul_reebVectorField_eq_add_iff (hα : α.IsContactForm)
    {β : SmoothForm I M ℝ 1} {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f x)
    (hfx : f x ≠ 0) (hβ : ∀ y, β.val y = f y • α.val y) (z : TangentSpace I x) :
    f x • β.reebVectorField x = α.reebVectorField x + z ↔
      α.val x ![z] = 0 ∧ ∀ w : TangentSpace I x, α.val x ![w] = 0 →
        mextDeriv α.val x ![z, w] = mvfderiv I f x w / f x := by
  -- This is the rescaling law for the correction `y = z / f(x)`.
  rw [← eq_inv_smul_iff₀ hfx, smul_add, hα.reebVectorField_eq_inv_smul_add_iff hf hβ,
    ContinuousAlternatingMap.vecCons_smul, smul_eq_zero, or_iff_right (inv_ne_zero hfx)]
  refine and_congr_right fun _ ↦ forall₂_congr fun w _ ↦ ?_
  rw [ContinuousAlternatingMap.vecCons_smul, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ hfx]
  field_simp

/-- **The correction term of the rescaled Reeb vector field.** Let `α` be a contact form and
`β = f α` for a function `f`, `C¹` at `x` with `f(x) ≠ 0`. The vector `f(x) R_β(x) - R_α(x)` is the
unique `z ∈ ξ_x = ker α_x` with `dα(z, w) = df(w) / f(x)` for all `w ∈ ξ_x`, so that
`R_β(x) = (R_α(x) + z) / f(x)`. -/
theorem IsContactForm.eq_smul_reebVectorField_sub_reebVectorField_iff
    (hα : α.IsContactForm) {β : SmoothForm I M ℝ 1} {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f x) (hfx : f x ≠ 0) (hβ : ∀ y, β.val y = f y • α.val y)
    (z : TangentSpace I x) :
    z = f x • β.reebVectorField x - α.reebVectorField x ↔
      α.val x ![z] = 0 ∧ ∀ w : TangentSpace I x, α.val x ![w] = 0 →
        mextDeriv α.val x ![z, w] = mvfderiv I f x w / f x := by
  rw [← hα.smul_reebVectorField_eq_add_iff hf hfx hβ, eq_sub_iff_add_eq', eq_comm]

/-- **The contact form on the rescaled Reeb vector field.** Let `α` be a contact form and
`β = f α` for a function `f`, `C¹` at `x`. Then `α(R_β(x)) = 1 / f(x)`. For `f(x) = 0` both sides
are `0`, by the junk value `0⁻¹ = 0`. -/
theorem IsContactForm.apply_reebVectorField_of_eq_smul (hα : α.IsContactForm)
    {β : SmoothForm I M ℝ 1} {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f x)
    (hβ : ∀ y, β.val y = f y • α.val y) : α.val x ![β.reebVectorField x] = (f x)⁻¹ := by
  -- By the rescaling law, `R_β(x) = R_α(x) / f(x) + y` with `y ∈ ξ_x`.
  have hy := (hα.reebVectorField_eq_inv_smul_add_iff hf hβ _).1
    (add_sub_cancel _ _).symm
  rw [← add_sub_cancel ((f x)⁻¹ • α.reebVectorField x) (β.reebVectorField x),
    ContinuousAlternatingMap.vecCons_add, ContinuousAlternatingMap.vecCons_smul,
    hα.apply_reebVectorField, hy.1, smul_eq_mul, mul_one, add_zero]

omit [FiniteDimensional ℝ E] in
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
  rw [reebVectorField, reebVectorField, characteristicVectorField_def,
    characteristicVectorField_def, ha, hB, Module.Dual.reebVector_smul_bilinForm hc,
    (isContactForm_def.1 hα x).reebVector_smul hc]

omit [FiniteDimensional ℝ E] in
/-- The Reeb vector field of `-α` is `-R_α`. -/
theorem IsContactForm.reebVectorField_neg (hα : α.IsContactForm) (x : M) :
    (-α).reebVectorField x = -α.reebVectorField x := by
  rw [← neg_one_smul ℝ α, hα.reebVectorField_smul (by norm_num), inv_neg, inv_one, neg_one_smul]

end SmoothForm

end TauCeti
