/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Coorientation
public import TauCeti.Geometry.Contact.Transition
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Cover
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The space of contact elements of the plane

A *contact element* of the plane at a point `q ∈ ℝ²` is a line through the origin of the tangent
plane `T_q ℝ² = ℝ²`. These lines are parametrized by `ℝ / πℤ`, a model of the real projective line:
the class `θ` of `τ ∈ ℝ` gives the line `ℓ_θ` perpendicular to `(cos τ, sin τ)`
(`TauCeti.contactElementLine`), which does not change when `τ` is replaced by `τ + π`, and distinct
classes give distinct lines (`TauCeti.contactElementLine_injective`). The space of contact elements
is the three-manifold `ℝ² × ℝP¹ = ℝ² × AddCircle π`, and it carries the hyperplane field `ξ` of
tangent vectors whose `ℝ²`-component lies in the contact element at their base point
(`TauCeti.contactElementDistribution`):

`ξ_(q, θ) = {(u, w) ∈ ℝ² × ℝ : u ∈ ℓ_θ}`.

On the cover `ℝ² × ℝ`, with coordinates `(x, y, τ)`, this hyperplane field is the kernel of the
one-form `α = cos τ dx + sin τ dy` (`TauCeti.contactElementForm`,
`TauCeti.comap_mfderiv_contactElementDistribution`), whose exterior derivative is
`dα = dτ ∧ (cos τ dy - sin τ dx)` (`TauCeti.mextDeriv_contactElementForm_apply`). It is a contact
form (`TauCeti.isContactForm_contactElementForm`): on its kernel, spanned by
`(-sin τ, cos τ, 0)` and `(0, 0, 1)`, `dα` takes the value `-1`. The quotient map
`ℝ² × ℝ → ℝ² × AddCircle π` is a surjective local diffeomorphism, so `ξ` is a contact structure
(`TauCeti.isContactDistribution_contactElementDistribution`), by descent of contact structures
along surjective local diffeomorphisms
(`TauCeti.IsContactDistribution.of_comap_mfderiv_of_isLocalDiffeomorph`).

The deck transformation `τ ↦ τ + π` sends `α` to `-α`, so `α` itself does not descend, and in fact
`ξ` is the kernel of no global one-form vanishing nowhere
(`TauCeti.not_exists_smoothForm_ker_eq_contactElementDistribution`). Such a form would pull back to
`f α` for a smooth function `f` vanishing nowhere on the connected space `ℝ² × ℝ`, and invariance
under the deck transformation forces `f (x, y, τ + π) = -f (x, y, τ)`, so `f` would change sign.
Hence the contact structure `ξ` has no global contact form
(`TauCeti.not_exists_isContactForm_kerDistribution_eq_contactElementDistribution`) and no
coorientation (`TauCeti.not_exists_isCoorientation_contactElementDistribution`): its contact line is
not trivial. A definition of contact structures as kernels of global contact forms would miss this
example.

## Main definitions

* `TauCeti.contactElementForm`: the contact form `cos τ dx + sin τ dy` on `ℝ² × ℝ`.
* `TauCeti.contactElementLine`: the line of `ℝ²` with angle class `θ ∈ ℝ / πℤ`.
* `TauCeti.contactElementDistribution`: the contact structure of the space of contact elements
  `ℝ² × AddCircle π`.

## Main results

* `TauCeti.isContactForm_contactElementForm`: `cos τ dx + sin τ dy` is a contact form.
* `TauCeti.isContactDistribution_contactElementDistribution`: the space of contact elements is a
  contact manifold.
* `TauCeti.not_exists_smoothForm_ker_eq_contactElementDistribution`,
  `TauCeti.not_exists_isContactForm_kerDistribution_eq_contactElementDistribution`,
  `TauCeti.not_exists_isCoorientation_contactElementDistribution`: its contact structure is not
  coorientable.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 1.2 (the space of contact elements) and Section 2.1 (coorientability).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Springer GTM 60 (1989),
  Appendix 4 (contact elements and the contact structure of their space).
-/

public section

noncomputable section

open Function Real
open scoped Manifold ContDiff

namespace TauCeti

local instance : Fact (0 < π) := ⟨pi_pos⟩

/-! ### The contact form on the cover -/

/-- The coordinate one-form `dx` on `ℝ² × ℝ`. -/
private def coverDx : ((ℝ × ℝ) × ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ ((ℝ × ℝ) × ℝ) ℝ (0 : Fin 1)
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ))

/-- The coordinate one-form `dy` on `ℝ² × ℝ`. -/
private def coverDy : ((ℝ × ℝ) × ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ ((ℝ × ℝ) × ℝ) ℝ (0 : Fin 1)
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ))

private theorem coverDx_apply {p : (ℝ × ℝ) × ℝ} (v : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p) :
    coverDx ![v] = v.1.1 :=
  ContinuousAlternatingMap.ofSubsingleton_apply_apply ..

private theorem coverDy_apply {p : (ℝ × ℝ) × ℝ} (v : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p) :
    coverDy ![v] = v.1.2 :=
  ContinuousAlternatingMap.ofSubsingleton_apply_apply ..

/-- A smooth function `g` of the angle `τ`, as a smooth function on `ℝ² × ℝ`. -/
private def angleFun (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) : C^∞⟮𝓘(ℝ, (ℝ × ℝ) × ℝ), (ℝ × ℝ) × ℝ; ℝ⟯ :=
  ⟨fun p ↦ g p.2, (hg.comp contDiff_snd).contMDiff⟩

private theorem coe_angleFun (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) :
    ⇑(angleFun g hg) = fun p ↦ g p.2 :=
  (rfl)

/-- The derivative of a function of the angle `τ` alone. -/
private theorem mvfderiv_comp_snd {g : ℝ → ℝ} {g' : ℝ → ℝ} (hg : ∀ τ, HasDerivAt g (g' τ) τ)
    (p : (ℝ × ℝ) × ℝ) (v : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p) :
    mvfderiv 𝓘(ℝ, (ℝ × ℝ) × ℝ) (fun q : (ℝ × ℝ) × ℝ ↦ g q.2) p v = g' p.2 * v.2 := by
  have h : HasFDerivAt (fun q : (ℝ × ℝ) × ℝ ↦ g q.2)
      (g' p.2 • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) p :=
    (hg p.2).comp_hasFDerivAt p hasFDerivAt_snd
  simp [mvfderiv_eq_fderiv, h.fderiv, NormedSpace.fromTangentSpace_apply]

/-- The exterior derivative of `g(τ) A` for a constant one-form `A`: `d(g A) = g'(τ) dτ ∧ A`. -/
private theorem mextDeriv_funSMulₗ_angleFun_apply {g g' : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg' : ∀ τ, HasDerivAt g (g' τ) τ) (A : ((ℝ × ℝ) × ℝ) [⋀^Fin 1]→L[ℝ] ℝ)
    (p : (ℝ × ℝ) × ℝ) (v w : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p) :
    mextDeriv (SmoothForm.funSMulₗ (angleFun g hg) (SmoothForm.const A)).val p ![v, w] =
      g' p.2 * (v.2 * A ![w] - w.2 * A ![v]) := by
  have hA := (SmoothForm.isClosed_def _).1 (SmoothForm.isClosed_const A)
  rw [SmoothForm.coe_funSMulₗ, mextDeriv_fun_smul_apply
    ((angleFun g hg).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    ((SmoothForm.const A).mdifferentiableAt p), hA, coe_angleFun, mvfderiv_comp_snd hg',
    mvfderiv_comp_snd hg']
  simp only [SmoothForm.const_apply_one, Pi.zero_apply, ContinuousAlternatingMap.coe_zero,
    mul_zero, add_zero]
  ring

/-- The contact form `cos τ dx + sin τ dy` on `ℝ² × ℝ`, with coordinates `p = ((x, y), τ)`. Its
kernel at `p` consists of the tangent vectors whose `ℝ²`-component is perpendicular to
`(cos τ, sin τ)`. -/
def contactElementForm : SmoothForm 𝓘(ℝ, (ℝ × ℝ) × ℝ) ((ℝ × ℝ) × ℝ) ℝ 1 :=
  SmoothForm.funSMulₗ (angleFun cos contDiff_cos) (SmoothForm.const coverDx) +
    SmoothForm.funSMulₗ (angleFun sin contDiff_sin) (SmoothForm.const coverDy)

/-- The form `cos τ dx + sin τ dy` evaluates a tangent vector `v = ((a, b), c)` at `((x, y), τ)`
as `cos τ a + sin τ b`. -/
@[simp]
theorem contactElementForm_apply (p : (ℝ × ℝ) × ℝ) (v : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p) :
    contactElementForm.val p ![v] = cos p.2 * v.1.1 + sin p.2 * v.1.2 := by
  simp only [contactElementForm, SmoothForm.add_toRoughForm, SmoothForm.coe_funSMulₗ, coe_angleFun,
    Pi.add_apply, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    SmoothForm.const_apply_one, coverDx_apply, coverDy_apply, smul_eq_mul]

/-- The exterior derivative of `cos τ dx + sin τ dy` is
`dτ ∧ (cos τ dy - sin τ dx)`. -/
theorem mextDeriv_contactElementForm_apply (p : (ℝ × ℝ) × ℝ)
    (v w : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p) :
    mextDeriv contactElementForm.val p ![v, w] =
      cos p.2 * (v.2 * w.1.2 - w.2 * v.1.2) - sin p.2 * (v.2 * w.1.1 - w.2 * v.1.1) := by
  have hsum : mextDeriv contactElementForm.val =
      mextDeriv (SmoothForm.funSMulₗ (angleFun cos contDiff_cos) (.const coverDx)).val +
        mextDeriv (SmoothForm.funSMulₗ (angleFun sin contDiff_sin) (.const coverDy)).val := by
    rw [← mextDerivₗ_apply, contactElementForm, map_add, SmoothForm.add_toRoughForm,
      mextDerivₗ_apply, mextDerivₗ_apply]
  rw [hsum, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    mextDeriv_funSMulₗ_angleFun_apply contDiff_cos hasDerivAt_cos,
    mextDeriv_funSMulₗ_angleFun_apply contDiff_sin hasDerivAt_sin]
  rw [coverDx_apply, coverDx_apply, coverDy_apply, coverDy_apply]
  ring

/-- The form `cos τ dx + sin τ dy` takes the value `1` on the unit normal `(cos τ, sin τ, 0)`. -/
private theorem exists_contactElementForm_apply_eq_one (p : (ℝ × ℝ) × ℝ) :
    ∃ e : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p, contactElementForm.val p ![e] = 1 := by
  obtain ⟨e, he⟩ : ∃ e : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p, e = ((cos p.2, sin p.2), 0) :=
    ⟨_, rfl⟩
  refine ⟨e, ?_⟩
  rw [contactElementForm_apply, he]
  nlinarith [sin_sq_add_cos_sq p.2]

/-- The form `cos τ dx + sin τ dy` vanishes nowhere. -/
theorem contactElementForm_apply_ne_zero (p : (ℝ × ℝ) × ℝ) : contactElementForm.val p ≠ 0 := by
  obtain ⟨e, he⟩ := exists_contactElementForm_apply_eq_one p
  intro h
  rw [h, ContinuousAlternatingMap.coe_zero, Pi.zero_apply] at he
  exact zero_ne_one he

/-- **The form `cos τ dx + sin τ dy` is a contact form** on `ℝ² × ℝ`. -/
theorem isContactForm_contactElementForm : contactElementForm.IsContactForm := by
  refine SmoothForm.isContactForm_iff.2 fun p ↦ ⟨?_, fun v hv hvw ↦ ?_⟩
  · obtain ⟨e, he⟩ := exists_contactElementForm_apply_eq_one p
    exact ⟨e, he ▸ one_ne_zero⟩
  rw [contactElementForm_apply] at hv
  -- Test against the frame `(-sin τ, cos τ, 0)`, `(0, 0, 1)` of the kernel.
  obtain ⟨e₁, he₁⟩ : ∃ e : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p, e = ((-sin p.2, cos p.2), 0) :=
    ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p, e = ((0, 0), 1) := ⟨_, rfl⟩
  have h₁ := hvw e₁ (by rw [contactElementForm_apply, he₁]; ring)
  have h₂ := hvw e₂ (by rw [contactElementForm_apply, he₂]; ring)
  rw [mextDeriv_contactElementForm_apply, he₁] at h₁
  rw [mextDeriv_contactElementForm_apply, he₂] at h₂
  simp only at h₁ h₂
  have hs := sin_sq_add_cos_sq p.2
  have h₁₁ : v.1.1 = 0 := by linear_combination cos p.2 * hv + sin p.2 * h₂ - v.1.1 * hs
  have h₁₂ : v.1.2 = 0 := by linear_combination sin p.2 * hv - cos p.2 * h₂ - v.1.2 * hs
  have h₂₂ : v.2 = 0 := by linear_combination h₁ - v.2 * hs
  -- The components of the zero tangent vector are by definition those of `0 : (ℝ × ℝ) × ℝ`.
  exact Prod.ext (Prod.ext h₁₁ h₁₂) h₂₂

/-- The deck transformation `τ ↦ τ + π` reverses the sign of `cos τ dx + sin τ dy`. -/
theorem contactElementForm_apply_add_pi (p : (ℝ × ℝ) × ℝ) (v : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p) :
    contactElementForm.val (p.1, p.2 + π) ![v] = -contactElementForm.val p ![v] := by
  rw [contactElementForm_apply (p.1, p.2 + π) v, contactElementForm_apply, cos_add_pi, sin_add_pi]
  ring

/-! ### The contact structure on the space of contact elements -/

/-- The linear form `u ↦ cos τ u₁ + sin τ u₂` on `ℝ²`. -/
private def angleCovector (τ : ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ :=
  cos τ • LinearMap.fst ℝ ℝ ℝ + sin τ • LinearMap.snd ℝ ℝ ℝ

private theorem angleCovector_apply (τ : ℝ) (u : ℝ × ℝ) :
    angleCovector τ u = cos τ * u.1 + sin τ * u.2 :=
  (rfl)

private theorem periodic_ker_angleCovector :
    Periodic (fun τ ↦ LinearMap.ker (angleCovector τ)) π := fun τ ↦ by
  have h : angleCovector (τ + π) = -angleCovector τ := by
    ext <;> simp [angleCovector_apply, cos_add_pi, sin_add_pi]
  simp only [h, LinearMap.ker_neg]

/-- The **contact element** of angle class `θ ∈ ℝ / πℤ`: the line of `ℝ²` perpendicular to
`(cos τ, sin τ)` for any representative `τ` of `θ`. -/
def contactElementLine : AddCircle π → Submodule ℝ (ℝ × ℝ) :=
  periodic_ker_angleCovector.lift

/-- A vector `u` lies on the contact element of angle `τ` exactly when it is perpendicular to
`(cos τ, sin τ)`. -/
@[simp]
theorem mem_contactElementLine_coe {τ : ℝ} {u : ℝ × ℝ} :
    u ∈ contactElementLine τ ↔ cos τ * u.1 + sin τ * u.2 = 0 := by
  rw [contactElementLine, Periodic.lift_coe, LinearMap.mem_ker, angleCovector_apply]

/-- Distinct angle classes give distinct contact elements. -/
theorem contactElementLine_injective : Injective contactElementLine := by
  intro θ θ' h
  induction θ using QuotientAddGroup.induction_on with | H τ => ?_
  induction θ' using QuotientAddGroup.induction_on with | H τ' => ?_
  -- The direction `(-sin τ, cos τ)` of the first line lies on the second one.
  have hmem : ((-sin τ, cos τ) : ℝ × ℝ) ∈ contactElementLine τ' := by
    rw [← h, mem_contactElementLine_coe]
    ring
  rw [mem_contactElementLine_coe] at hmem
  obtain ⟨k, hk⟩ := sin_eq_zero_iff.1 (show sin (τ' - τ) = 0 by
    rw [sin_sub]
    linear_combination hmem)
  refine (QuotientAddGroup.eq (s := AddSubgroup.zmultiples π)).2 ⟨k, ?_⟩
  simp only [zsmul_eq_mul, hk]
  ring

variable (z : (ℝ × ℝ) × AddCircle π)

/-- The **contact structure of the space of contact elements** `ℝ² × AddCircle π` of the plane: at
`(q, θ)`, the tangent vectors whose `ℝ²`-component lies on the contact element
`contactElementLine θ`. -/
def contactElementDistribution :
    Submodule ℝ (TangentSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) z) :=
  (contactElementLine z.2).comap (LinearMap.fst ℝ (ℝ × ℝ) ℝ)

variable {z} in
@[simp]
theorem mem_contactElementDistribution {v : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) z} :
    v ∈ contactElementDistribution z ↔ v.1 ∈ contactElementLine z.2 :=
  Iff.rfl

/-- The quotient map `ℝ² × ℝ → ℝ² × AddCircle π` pulls the contact structure of the space of
contact elements back to the kernel of `cos τ dx + sin τ dy`. -/
theorem comap_mfderiv_contactElementDistribution :
    (fun p ↦ (contactElementDistribution (Prod.map id ((↑) : ℝ → AddCircle π) p)).comap
      (mfderiv 𝓘(ℝ, (ℝ × ℝ) × ℝ) (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ))
        (Prod.map id ((↑) : ℝ → AddCircle π)) p).toLinearMap) =
      contactElementForm.kerDistribution := by
  ext p v
  rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, AddCircle.mfderiv_prodMap_id_coe_apply,
    SmoothForm.mem_kerDistribution, contactElementForm_apply]
  exact mem_contactElementDistribution.trans mem_contactElementLine_coe

/-- **The space of contact elements of the plane is a contact manifold.** The hyperplane field of
tangent vectors whose `ℝ²`-component lies on the contact element at their base point is a contact
structure on `ℝ² × AddCircle π`, of every class `C^n` with `n ≤ ∞`. -/
theorem isContactDistribution_contactElementDistribution {n : ℕ∞ω} [ENat.LEInfty n] :
    IsContactDistribution (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) n contactElementDistribution := by
  have h : IsContactDistribution (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) ∞ contactElementDistribution := by
    refine IsContactDistribution.of_comap_mfderiv_of_isLocalDiffeomorph (m := ω) ?_ (by simp)
      (AddCircle.isLocalDiffeomorph_prodMap_id_coe π ω) (by simp)
      (surjective_id.prodMap QuotientAddGroup.mk_surjective)
    rw [comap_mfderiv_contactElementDistribution]
    exact isContactForm_contactElementForm.isContactDistribution_kerDistribution
  exact h.of_le ENat.LEInfty.out

/-! ### The contact structure is not coorientable -/

/-- **The space of contact elements is not coorientable.** Its contact structure is not the kernel
of any smooth one-form on `ℝ² × AddCircle π` vanishing nowhere. -/
theorem not_exists_smoothForm_ker_eq_contactElementDistribution :
    ¬ ∃ β : SmoothForm (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) ((ℝ × ℝ) × AddCircle π) ℝ 1,
      ∀ z, β.val z ≠ 0 ∧ RoughForm.ker β.val z = contactElementDistribution z := by
  rintro ⟨β, hβ⟩
  set c : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × AddCircle π := Prod.map id ((↑) : ℝ → AddCircle π) with hc
  have hcs : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) ∞ c :=
    (AddCircle.isLocalDiffeomorph_prodMap_id_coe π ∞).contMDiff
  -- The pullback `β'` of `β` to the cover reads `β` through the identity differential.
  set β' := SmoothForm.mpullback c hcs β
  have hβ' (p : (ℝ × ℝ) × ℝ) (v : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p) :
      β'.val p ![v] = β.val (c p) ![v] := by
    rw [SmoothForm.mpullback_apply_one, hc, AddCircle.mfderiv_prodMap_id_coe_apply]
  -- It has the same kernel as `α = cos τ dx + sin τ dy`, so `β' = f α` with `f` vanishing nowhere.
  have hβD : β.kerDistribution = contactElementDistribution :=
    funext fun z ↦ (SmoothForm.kerDistribution_eq_ker ..).trans (hβ z).2
  have hker : β'.kerDistribution = contactElementForm.kerDistribution := by
    rw [← comap_mfderiv_contactElementDistribution, ← hβD]
    exact funext (SmoothForm.kerDistribution_mpullback c hcs β)
  obtain ⟨f, ⟨hf, hf₀, hβf⟩, -⟩ :=
    (SmoothForm.kerDistribution_eq_iff_existsUnique_fun_smul contactElementForm_apply_ne_zero).1
      hker
  -- The deck transformation fixes `β'` and reverses `α`, so it reverses the sign of `f`.
  have hdeck (p : (ℝ × ℝ) × ℝ) : f (p.1, p.2 + π) = -f p := by
    obtain ⟨e, h1⟩ := exists_contactElementForm_apply_eq_one p
    have hcp : c (p.1, p.2 + π) = c p := by
      rw [hc, Prod.map_apply, Prod.map_apply, AddCircle.coe_add_period]
    have key : β'.val (p.1, p.2 + π) ![e] = β'.val p ![e] := by
      rw [hβ' (p.1, p.2 + π) e, hβ' p e, hcp]
    rw [hβf, hβf, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      contactElementForm_apply_add_pi, h1, smul_eq_mul, smul_eq_mul] at key
    linarith
  -- A continuous function vanishing nowhere on the connected cover cannot change sign.
  have hfc : Continuous f := hf.continuous
  let p₀ : (ℝ × ℝ) × ℝ := ((0, 0), 0)
  rcases (hf₀ p₀).lt_or_gt with hneg | hpos
  · obtain ⟨p, hp⟩ := intermediate_value_univ p₀ (p₀.1, p₀.2 + π) hfc
      ⟨hneg.le, by rw [hdeck]; linarith⟩
    exact hf₀ p hp
  · obtain ⟨p, hp⟩ := intermediate_value_univ (p₀.1, p₀.2 + π) p₀ hfc
      ⟨by rw [hdeck]; linarith, hpos.le⟩
    exact hf₀ p hp

/-- The contact structure of the space of contact elements of the plane has no global contact
form. -/
theorem not_exists_isContactForm_kerDistribution_eq_contactElementDistribution :
    ¬ ∃ β : SmoothForm (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) ((ℝ × ℝ) × AddCircle π) ℝ 1,
      β.IsContactForm ∧ β.kerDistribution = contactElementDistribution := fun ⟨β, hβ, hβD⟩ ↦
  not_exists_smoothForm_ker_eq_contactElementDistribution
    ⟨β, fun z ↦ ⟨hβ.apply_ne_zero z, by rw [← SmoothForm.kerDistribution_eq_ker, hβD]⟩⟩

/-- The contact structure of the space of contact elements of the plane has no coorientation. -/
theorem not_exists_isCoorientation_contactElementDistribution :
    ¬ ∃ o, IsCoorientation (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) contactElementDistribution o := fun h ↦
  not_exists_isContactForm_kerDistribution_eq_contactElementDistribution <|
    (IsContactDistribution.exists_isContactForm_kerDistribution_eq_iff_exists_isCoorientation
      isContactDistribution_contactElementDistribution).2 h

end TauCeti
