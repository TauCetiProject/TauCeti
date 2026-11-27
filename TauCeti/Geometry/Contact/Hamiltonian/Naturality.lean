/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactomorphism
public import TauCeti.Geometry.Contact.Rescale
public import TauCeti.Geometry.Manifold.IntegralCurve.Basic

/-!
# Naturality of contact Hamiltonian vector fields and Jacobi brackets

Let `f : M → N` be a smooth map whose differentials are all bijective, for instance a
diffeomorphism, and let `α` be a contact form on `N`. Contact Hamiltonian vector fields
and Jacobi brackets are transported along `f` as follows.

* **Strict case.** For the pulled-back contact form `f^* α`, the differential of `f` carries the
  contact Hamiltonian vector field of `H ∘ f` to that of `H`,
  `df_x (X^(f^* α)_(H ∘ f)(x)) = X^α_H(f x)`
  (`TauCeti.SmoothForm.IsContactForm.mfderiv_contactHamiltonianVectorField_mpullback`), and
  Jacobi brackets are natural, `{g ∘ f, h ∘ f}_(f^* α) = {g, h}_α ∘ f`
  (`TauCeti.SmoothForm.IsContactForm.jacobiBracket_mpullback`).
* **Conformal case.** If `f^* α = u β` for a contact form `β` on `M` and a nowhere-zero `C¹`
  function `u`, as for a contactomorphism with multiplier `u`, the Hamiltonian is divided by the
  multiplier: `df_x (X^β_((H ∘ f) / u)(x)) = X^α_H(f x)`
  (`TauCeti.SmoothForm.IsContactForm.mfderiv_contactHamiltonianVectorField_comp_div`), that is
  `f^* X_H = X_((H ∘ f) / u)`. In particular `df(X^β_(1 / u)) = R_α`
  (`TauCeti.SmoothForm.IsContactForm.mfderiv_contactHamiltonianVectorField_inv`), so for a
  constant multiplier `c` the differential carries `R_β` to `c R_α`
  (`TauCeti.SmoothForm.IsContactForm.mfderiv_reebVectorField_of_mpullback_eq_const_smul`):
  for `c ≠ 0`, the scaling `(q, p, z) ↦ (q, c p, c z)` of the standard contact space
  `V × V × ℝ`, which pulls the standard contact form back to `c` times itself, carries its Reeb
  field to `c` times itself
  (`TauCeti.mfderiv_reebVectorField_innerProductContactForm_of_coe_eq`). Jacobi brackets
  transform by `{(g ∘ f) / u, (h ∘ f) / u}_β = ({g, h}_α ∘ f) / u`
  (`TauCeti.SmoothForm.IsContactForm.jacobiBracket_comp_div`), and `f` carries integral curves of
  `X^β_((H ∘ f) / u)` to integral curves of `X^α_H`
  (`TauCeti.SmoothForm.IsContactForm.isMIntegralCurve_comp_contactHamiltonianVectorField`).

The strict case is the case `u = 1` of the conformal one; the conformal statements reduce to it
through the change-of-form laws of `TauCeti.Geometry.Contact.Rescale`, applied to `f^* α = u β`.
For diffeomorphisms, `Diffeomorph.IsStrictContactomorphism.mfderiv_contactHamiltonianVectorField`
and `Diffeomorph.IsStrictContactomorphism.jacobiBracket_comp` restate the strict case.

## Main results

* `TauCeti.SmoothForm.IsContactForm.mfderiv_contactHamiltonianVectorField_mpullback`,
  `TauCeti.SmoothForm.IsContactForm.mfderiv_contactHamiltonianVectorField_comp_div`: transport of
  contact Hamiltonian vector fields.
* `TauCeti.SmoothForm.IsContactForm.jacobiBracket_mpullback`,
  `TauCeti.SmoothForm.IsContactForm.jacobiBracket_comp_div`: naturality of Jacobi brackets.
* `TauCeti.SmoothForm.IsContactForm.isMIntegralCurve_comp_contactHamiltonianVectorField`:
  transport of contact Hamiltonian integral curves.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.3 (contact Hamiltonians).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E HM M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {α : SmoothForm J N ℝ 1} {β : SmoothForm I M ℝ 1} {f : M → N} {u : M → ℝ}

omit [TopologicalSpace M] [TopologicalSpace N] in
/-- Multiplying back by the nowhere-zero multiplier recovers the composite. -/
private theorem mul_comp_div (hu₀ : ∀ x, u x ≠ 0) (H : N → ℝ) : u * ((H ∘ f) / u) = H ∘ f :=
  funext fun x ↦ mul_div_cancel₀ _ (hu₀ x)

namespace IsContactForm

variable (hα : α.IsContactForm) (hf : ContMDiff I J ∞ f)
  (hdf : ∀ x, Function.Bijective (mfderiv I J f x))
include hα hdf

/-- **Contact Hamiltonian vector fields are natural.** Let `f` be a smooth map with bijective
differentials and `α` a contact form on its target. The differential of `f` carries the contact
Hamiltonian vector field of `H ∘ f` for the pulled-back form `f^* α` to the contact Hamiltonian
vector field of `H` for `α`. -/
theorem mfderiv_contactHamiltonianVectorField_mpullback {H : N → ℝ} {x : M}
    (hH : MDifferentiableAt J 𝓘(ℝ) H (f x)) :
    mfderiv I J f x ((SmoothForm.mpullback f hf α).contactHamiltonianVectorField (H ∘ f) x) =
      α.contactHamiltonianVectorField H (f x) := by
  have : FiniteDimensional ℝ F := .of_surjective (mfderiv I J f x).toLinearMap (hdf x).2
  have hβ := hα.mpullback f hf hdf
  obtain ⟨v, hv⟩ := (hdf x).2 (α.contactHamiltonianVectorField H (f x))
  rw [← hv]
  congr 1
  -- The lift `v` satisfies the defining equations of the contact Hamiltonian field of `H ∘ f`.
  refine (hβ.isInvertible_contactFlat x).injective ?_
  rw [hβ.contactFlat_contactHamiltonianVectorField, eq_comm,
    contactFlat_apply_eq_smul_sub_mvfderiv_iff_of_isContactFormAt
      (isContactForm_iff_forall_isContactFormAt.1 hβ x)]
  have hfx : MDifferentiableAt I J f x := (hf x).mdifferentiableAt (by simp)
  refine ⟨?_, fun w ↦ ?_⟩
  · rw [mpullback_apply_one, hv, hα.apply_contactHamiltonianVectorField, Function.comp_apply]
  · rw [mextDeriv_mpullback_apply_two, hv, hα.mextDeriv_contactHamiltonianVectorField_left,
      mvfderiv_comp_apply x hH hfx, mvfderiv_comp_apply x hH hfx,
      hα.mfderiv_reebVectorField_mpullback f hf hdf x, mpullback_apply_one]

/-- **Jacobi brackets are natural.** Let `f` be a smooth map with bijective differentials and `α`
a contact form on its target. The Jacobi bracket of `g ∘ f` and `h ∘ f` for the pulled-back form
`f^* α` is the Jacobi bracket of `g` and `h` for `α` at the image point. -/
theorem jacobiBracket_mpullback {g h : N → ℝ} {x : M} (hg : MDifferentiableAt J 𝓘(ℝ) g (f x))
    (hh : MDifferentiableAt J 𝓘(ℝ) h (f x)) :
    (SmoothForm.mpullback f hf α).jacobiBracket (g ∘ f) (h ∘ f) x = α.jacobiBracket g h (f x) := by
  have : FiniteDimensional ℝ F := .of_surjective (mfderiv I J f x).toLinearMap (hdf x).2
  have hfx : MDifferentiableAt I J f x := (hf x).mdifferentiableAt (by simp)
  rw [(hα.mpullback f hf hdf).jacobiBracket_eq_mvfderiv, hα.jacobiBracket_eq_mvfderiv,
    mvfderiv_comp_apply x hh hfx, mvfderiv_comp_apply x hg hfx,
    hα.mfderiv_contactHamiltonianVectorField_mpullback hf hdf hg,
    hα.mfderiv_reebVectorField_mpullback f hf hdf x, Function.comp_apply]

variable (hu : ContMDiff I 𝓘(ℝ) 1 u) (hu₀ : ∀ x, u x ≠ 0)
  (hfα : ∀ x, (SmoothForm.mpullback f hf α).val x = u x • β.val x)
include hu hu₀ hfα

/-- **Contactomorphisms transport contact Hamiltonian vector fields.** Let `f` be a smooth map
with bijective differentials pulling a contact form `α` back to `u β`, for a nowhere-zero `C¹`
function `u`. Then the differential of `f` carries the contact Hamiltonian vector field of
`(H ∘ f) / u` for `β` to the contact Hamiltonian vector field of `H` for `α`: in short,
`f^* X^α_H = X^β_((H ∘ f) / u)`. -/
theorem mfderiv_contactHamiltonianVectorField_comp_div {H : N → ℝ}
    (hH : MDifferentiable J 𝓘(ℝ) H) (x : M) :
    mfderiv I J f x (β.contactHamiltonianVectorField ((H ∘ f) / u) x) =
      α.contactHamiltonianVectorField H (f x) := by
  have hβ := (isContactForm_iff_of_eq_smul hu hu₀ hfα).1 (hα.mpullback f hf hdf)
  rw [← hβ.contactHamiltonianVectorField_of_eq_smul hu hu₀ hfα
      ((hH.comp (hf.mdifferentiable (by simp))).div (hu.mdifferentiable one_ne_zero) hu₀),
    mul_comp_div hu₀]
  exact hα.mfderiv_contactHamiltonianVectorField_mpullback hf hdf (hH (f x))

/-- Let `f` be a smooth map with bijective differentials pulling a contact form `α` back to
`u β`, for a nowhere-zero `C¹` function `u`. Then the differential of `f` carries the contact
Hamiltonian vector field of `1 / u` for `β` to the Reeb vector field of `α`. -/
theorem mfderiv_contactHamiltonianVectorField_inv (x : M) :
    mfderiv I J f x (β.contactHamiltonianVectorField u⁻¹ x) = α.reebVectorField (f x) := by
  have : FiniteDimensional ℝ F := .of_surjective (mfderiv I J f x).toLinearMap (hdf x).2
  have h := hα.mfderiv_contactHamiltonianVectorField_comp_div hf hdf hu hu₀ hfα
    (H := 1) mdifferentiable_const x
  rwa [Pi.one_comp, one_div, hα.contactHamiltonianVectorField_one] at h

/-- **Contactomorphisms transport Jacobi brackets.** Let `f` be a smooth map with bijective
differentials pulling a contact form `α` back to `u β`, for a nowhere-zero `C¹` function `u`.
Then `{(g ∘ f) / u, (h ∘ f) / u}_β = ({g, h}_α ∘ f) / u`. -/
theorem jacobiBracket_comp_div {g h : N → ℝ} (hg : MDifferentiable J 𝓘(ℝ) g)
    (hh : MDifferentiable J 𝓘(ℝ) h) (x : M) :
    β.jacobiBracket ((g ∘ f) / u) ((h ∘ f) / u) x = α.jacobiBracket g h (f x) / u x := by
  have hβ := (isContactForm_iff_of_eq_smul hu hu₀ hfα).1 (hα.mpullback f hf hdf)
  have hfd : MDifferentiable I J f := hf.mdifferentiable (by simp)
  have hu' := hu.mdifferentiable one_ne_zero
  have h := hβ.jacobiBracket_of_eq_smul hu hu₀ hfα ((hg.comp hfd).div hu' hu₀)
    ((hh.comp hfd).div hu' hu₀) x
  rw [mul_comp_div hu₀, mul_comp_div hu₀,
    hα.jacobiBracket_mpullback hf hdf (hg (f x)) (hh (f x))] at h
  rw [h, mul_div_cancel_left₀ _ (hu₀ x)]

/-- **Contactomorphisms conjugate contact Hamiltonian flows.** Let `f` be a smooth map with
bijective differentials pulling a contact form `α` back to `u β`, for a nowhere-zero `C¹`
function `u`. Then `f` carries integral curves of the contact Hamiltonian vector field of
`(H ∘ f) / u` for `β` to integral curves of the contact Hamiltonian vector field of `H` for
`α`. -/
theorem isMIntegralCurve_comp_contactHamiltonianVectorField {H : N → ℝ}
    (hH : MDifferentiable J 𝓘(ℝ) H) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (β.contactHamiltonianVectorField ((H ∘ f) / u))) :
    IsMIntegralCurve (f ∘ γ) (α.contactHamiltonianVectorField H) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ ⊢
  exact hγ.map_of_mfderiv_eq (fun t _ ↦ (hf (γ t)).mdifferentiableAt (by simp))
    fun t _ ↦ hα.mfderiv_contactHamiltonianVectorField_comp_div hf hdf hu hu₀ hfα hH (γ t)

end IsContactForm

/-- Let `f` be a smooth map with bijective differentials pulling a contact form `α` back to
`c β` for a nonzero constant `c`. Then the differential of `f` carries the Reeb vector field of
`β` to `c` times the Reeb vector field of `α`. -/
theorem IsContactForm.mfderiv_reebVectorField_of_mpullback_eq_const_smul
    (hα : α.IsContactForm) (hf : ContMDiff I J ∞ f)
    (hdf : ∀ x, Function.Bijective (mfderiv I J f x)) {c : ℝ} (hc : c ≠ 0)
    (hfα : ∀ x, (SmoothForm.mpullback f hf α).val x = c • β.val x) (x : M) :
    mfderiv I J f x (β.reebVectorField x) = c • α.reebVectorField (f x) := by
  have hβ := (isContactForm_iff_of_eq_smul contMDiff_const (fun _ ↦ hc) hfα).1
    (hα.mpullback f hf hdf)
  have h := hα.mfderiv_contactHamiltonianVectorField_inv hf hdf contMDiff_const
    (fun _ ↦ hc) hfα x
  rw [Pi.inv_def, hβ.contactHamiltonianVectorField_const,
    Pi.smul_apply, map_smul] at h
  rw [← h, smul_inv_smul₀ hc]

end TauCeti.SmoothForm

namespace Diffeomorph

open TauCeti

variable {E HM M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {e : M ≃ₘ⟮I, J⟯ N} {α : SmoothForm I M ℝ 1} {β : SmoothForm J N ℝ 1} {x : M}

/-- The differential of a strict contactomorphism `e` from `α` to `β` carries the contact
Hamiltonian vector field of `H ∘ e` for `α` to the contact Hamiltonian vector field of `H` for
`β`. -/
theorem IsStrictContactomorphism.mfderiv_contactHamiltonianVectorField
    (h : e.IsStrictContactomorphism α β) (hβ : β.IsContactForm) {H : N → ℝ}
    (hH : MDifferentiableAt J 𝓘(ℝ) H (e x)) :
    mfderiv I J e x (α.contactHamiltonianVectorField (H ∘ e) x) =
      β.contactHamiltonianVectorField H (e x) := by
  rw [isStrictContactomorphism_def] at h
  subst h
  exact hβ.mfderiv_contactHamiltonianVectorField_mpullback e.contMDiff
    (fun _ ↦ (e.isInvertible_mfderiv (by simp)).bijective) hH

/-- **Strict contactomorphisms preserve Jacobi brackets.** For a strict contactomorphism `e` from
`α` to `β`, `{g ∘ e, k ∘ e}_α = {g, k}_β ∘ e`. -/
theorem IsStrictContactomorphism.jacobiBracket_comp (h : e.IsStrictContactomorphism α β)
    (hβ : β.IsContactForm) {g k : N → ℝ} (hg : MDifferentiableAt J 𝓘(ℝ) g (e x))
    (hk : MDifferentiableAt J 𝓘(ℝ) k (e x)) :
    α.jacobiBracket (g ∘ e) (k ∘ e) x = β.jacobiBracket g k (e x) := by
  rw [isStrictContactomorphism_def] at h
  subst h
  exact hβ.jacobiBracket_mpullback e.contMDiff
    (fun _ ↦ (e.isInvertible_mfderiv (by simp)).bijective) hg hk

end Diffeomorph

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- For `c ≠ 0`, the diffeomorphism `(q, p, z) ↦ (q, c p, c z)` of the standard contact space,
which pulls the standard contact form `α` back to `c α`, carries the Reeb vector field `R_α` to
`c R_α`. Equivalently, it carries the contact Hamiltonian vector field `X_(1 / c) = R_α / c` to
`X_1 = R_α`, as the transport law with multiplier `c` predicts. -/
theorem mfderiv_reebVectorField_innerProductContactForm_of_coe_eq {c : ℝ} (hc : c ≠ 0)
    {e : (V × V × ℝ) ≃ₘ[ℝ] (V × V × ℝ)} (he : ⇑e = fun x ↦ (x.1, c • x.2)) (x : V × V × ℝ) :
    mfderiv 𝓘(ℝ, V × V × ℝ) 𝓘(ℝ, V × V × ℝ) e x
        ((innerProductContactForm V).reebVectorField x) =
      c • (innerProductContactForm V).reebVectorField (e x) :=
  (isContactForm_innerProductContactForm V).mfderiv_reebVectorField_of_mpullback_eq_const_smul
    e.contMDiff (fun _ ↦ (e.isInvertible_mfderiv (by simp)).bijective) hc
    (mpullback_innerProductContactForm_apply_of_coe_eq he) x

end TauCeti
