/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup

/-!
# Eichler transvections of a quadratic form

Let `Q` be a quadratic form on `M` with un-halved polar form `B = polar Q`, so that
`B x x = 2 • Q x`. For an isotropic vector `u` (`Q u = 0`) and a vector `w` orthogonal to it
(`B u w = 0`), the **Eichler transvection** (also called a Siegel transformation) is

`E_{u,w} x = x + B x u • w - B x w • u - (Q w * B x u) • u`.

It is a proper isometry of `Q`. It fixes `u` and every vector orthogonal to both `u` and `w`, and it
depends on `w` only through its class modulo `R ∙ u`. For fixed `u`, the map `w ↦ E_{u,w}` turns
addition into composition. So the Eichler transvections with isotropic vector `u` are the image of
a homomorphism from the additive group `u^⊥ / R ∙ u` into `SO(Q)`. Over a field this homomorphism
is injective as soon as `u` is not in the kernel of the polar form. The orthogonal group acts on
these subgroups by conjugation, moving the pair `(u, w)`.

Nothing here assumes that `2` is invertible, and only the injectivity statements need a field. The
formula uses `B` and `Q`, never `B / 2`, so it makes sense verbatim for integral quadratic forms.

## Main definitions

* `QuadraticMap.transvection Q hu huw`: the Eichler transvection `E_{u,w}`, as a linear
  automorphism of `M` with determinant `1`.
* `QuadraticMap.transvectionHom Q hu`: the homomorphism `w ↦ E_{u,w}` from the additive
  group of `u^⊥ / R ∙ u` into `specialOrthogonalGroup Q`.

## Main results

* `QuadraticMap.transvection_apply`: the defining formula.
* `QuadraticMap.transvection_mem_specialOrthogonalGroup`: `E_{u,w}` is a proper isometry.
* `QuadraticMap.transvection_add`: `E_{u,w + w'} = E_{u,w} * E_{u,w'}`.
* `QuadraticMap.transvection_add_smul`: `E_{u,w + c • u} = E_{u,w}`.
* `QuadraticMap.transvection_conj`: `g * E_{u,w} * g⁻¹ = E_{g u, g w}` for `g ∈ O(Q)`.
* `QuadraticMap.transvection_eq_one_iff`: over a field, if `polarBilin Q u ≠ 0`, then
  `E_{u,w} = 1` exactly when `w ∈ K ∙ u`. Hence `transvectionHom_injective`.

## References

* M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Springer (1952).
-/

public section

open TauCeti.QuadraticMap

universe u v

namespace QuadraticMap

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) {u w w' : M}

/-- The Eichler transvection `E_{u,w} x = x + B x u • w - B x w • u - (Q w * B x u) • u`, for an
isotropic vector `u` and a vector `w` orthogonal to it, where `B = polar Q`. It is a proper
isometry of `Q`. -/
noncomputable def transvection (hu : Q u = 0) (huw : polar Q u w = 0) : M ≃ₗ[R] M :=
  -- Two linear transvections give the formula and show that its determinant is one.
  (LinearEquiv.transvection (f := Q.polarBilin u) (v := w) (by simpa using huw)).trans
    (LinearEquiv.transvection (f := Q w • Q.polarBilin u - Q.polarBilin w) (v := u) (by
      simp [polar_self, hu, polar_comm Q w u, huw]))

variable {Q}

/-- The Eichler transvection acts by
`E_{u,w} x = x + B x u • w - B x w • u - (Q w * B x u) • u`, where `B = polar Q`. -/
theorem transvection_apply (hu : Q u = 0) (huw : polar Q u w = 0) (x : M) :
    transvection Q hu huw x
      = x + polar Q x u • w - polar Q x w • u - (Q w * polar Q x u) • u := by
  simp only [transvection, LinearEquiv.trans_apply, LinearEquiv.transvection.apply,
    LinearMap.sub_apply, LinearMap.smul_apply, polarBilin_apply_apply, map_add, map_smul, huw,
    polar_self, polar_comm Q u x, polar_comm Q w x, smul_eq_mul, nsmul_eq_mul]
  module

/-- The determinant of an Eichler transvection is `1`, on any module. -/
@[simp]
theorem det_transvection (hu : Q u = 0) (huw : polar Q u w = 0) :
    LinearEquiv.det (transvection Q hu huw) = 1 := by
  rw [transvection, ← LinearEquiv.mul_eq_trans, map_mul, LinearEquiv.transvection.det_eq_one,
    LinearEquiv.transvection.det_eq_one, mul_one]

/-- An Eichler transvection is an isometry of `Q`. -/
theorem transvection_mem_orthogonalGroup (hu : Q u = 0) (huw : polar Q u w = 0) :
    transvection Q hu huw ∈ orthogonalGroup Q := by
  rw [mem_orthogonalGroup_iff]
  intro x
  rw [transvection_apply, sub_sub, ← add_smul, sub_eq_add_neg, ← neg_smul]
  simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_add_left, polar_smul_left,
    polar_smul_right, hu, polar_comm Q w u, huw, smul_eq_mul]
  ring

/-- An Eichler transvection is a proper isometry of `Q`. -/
theorem transvection_mem_specialOrthogonalGroup (hu : Q u = 0) (huw : polar Q u w = 0) :
    transvection Q hu huw ∈ specialOrthogonalGroup Q :=
  mem_specialOrthogonalGroup_iff.mpr
    ⟨transvection_mem_orthogonalGroup hu huw, det_transvection hu huw⟩

/-- An Eichler transvection `E_{u,w}` fixes its isotropic vector `u`. -/
@[simp]
theorem transvection_apply_self (hu : Q u = 0) (huw : polar Q u w = 0) :
    transvection Q hu huw u = u := by
  simp [transvection_apply, polar_self, hu, huw]

/-- An Eichler transvection fixes every vector orthogonal to both `u` and `w`. -/
@[simp]
theorem transvection_apply_of_polar_eq_zero (hu : Q u = 0) (huw : polar Q u w = 0) {x : M}
    (hxu : polar Q x u = 0) (hxw : polar Q x w = 0) : transvection Q hu huw x = x := by
  simp [transvection_apply, hxu, hxw]

/-- The Eichler transvection with `w = 0` is the identity. -/
@[simp]
theorem transvection_zero (hu : Q u = 0) : transvection Q (w := 0) hu (by simp) = 1 := by
  ext x
  simp [transvection_apply]

/-- The Eichler transvection `E_{u,w}` is trivial when `w` is a multiple of `u`. -/
@[simp]
theorem transvection_eq_one_of_mem_span (hu : Q u = 0) (huw : polar Q u w = 0)
    (hw : w ∈ R ∙ u) : transvection Q hu huw = 1 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  ext x
  simp only [transvection_apply, polar_smul_right, QuadraticMap.map_smul, hu, smul_eq_mul,
    LinearEquiv.coe_one, id_eq]
  module

/-- The Eichler transvections with a fixed isotropic vector `u` compose additively in `w`. -/
@[simp]
theorem transvection_add (hu : Q u = 0) (huw : polar Q u w = 0) (huw' : polar Q u w' = 0)
    : transvection Q (w := w + w') hu (by simp [huw, huw']) =
      transvection Q hu huw * transvection Q hu huw' := by
  ext x
  simp only [LinearEquiv.mul_apply, transvection_apply, polar_add_left, polar_sub_left,
    polar_smul_left, polar_add_right, QuadraticMap.map_add Q, polar_self, hu, polar_comm Q w' u,
    huw, huw', smul_eq_mul, nsmul_eq_mul, polar_comm Q w' w]
  module

/-- The inverse of an Eichler transvection is the Eichler transvection of `-w`. -/
@[simp]
theorem transvection_neg (hu : Q u = 0) (huw : polar Q u w = 0) :
    transvection Q (w := -w) hu (by simpa using huw) =
      (transvection Q hu huw)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← transvection_add hu (by simpa using huw) huw]
  exact transvection_eq_one_of_mem_span hu _ (by simp)

/-- An Eichler transvection depends on `w` only through its class modulo `R ∙ u`. -/
theorem transvection_add_smul (hu : Q u = 0) (huw : polar Q u w = 0) (c : R)
    : transvection Q (w := w + c • u) hu (by simp [polar_self, hu, huw]) =
      transvection Q hu huw := by
  have hcu : polar Q u (c • u) = 0 := by simp [polar_self, hu]
  rw [transvection_add hu huw hcu, transvection_eq_one_of_mem_span hu hcu
    (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self u)), mul_one]

/-- **The conjugation law.** Conjugating an Eichler transvection by an isometry moves the defining
pair of vectors: `g * E_{u,w} * g⁻¹ = E_{g u, g w}`. -/
theorem transvection_conj (hu : Q u = 0) (huw : polar Q u w = 0) {g : M ≃ₗ[R] M}
    (hg : g ∈ orthogonalGroup Q) :
    g * transvection Q hu huw * g⁻¹
      = transvection Q (u := g u) (w := g w) (by rw [map_app_of_mem_orthogonalGroup hg, hu])
          (by rw [polar_apply_of_mem_orthogonalGroup hg, huw]) := by
  ext x
  obtain ⟨y, rfl⟩ := g.surjective x
  simp [transvection_apply, polar_apply_of_mem_orthogonalGroup hg,
    map_app_of_mem_orthogonalGroup hg]

/-- The Eichler transvections with isotropic vector `u`, as a homomorphism out of the vectors
orthogonal to `u`. It descends to `u^⊥ / R ∙ u` as `transvectionHom`. -/
private noncomputable def transvectionAddHom (hu : Q u = 0) :
    LinearMap.ker (Q.polarBilin u) →+ Additive (specialOrthogonalGroup Q) :=
  AddMonoidHom.mk' (fun w => Additive.ofMul
      ⟨transvection Q hu (LinearMap.mem_ker.mp w.2),
        transvection_mem_specialOrthogonalGroup hu (LinearMap.mem_ker.mp w.2)⟩)
    fun w w' => by
      apply Additive.toMul.injective
      rw [toMul_add, toMul_ofMul, toMul_ofMul, toMul_ofMul]
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul]
      exact transvection_add hu (LinearMap.mem_ker.mp w.2) (LinearMap.mem_ker.mp w'.2)

private theorem coe_toMul_transvectionAddHom (hu : Q u = 0) (w : LinearMap.ker (Q.polarBilin u)) :
    ((Additive.toMul (transvectionAddHom hu w) : specialOrthogonalGroup Q) : M ≃ₗ[R] M) =
      transvection Q hu (LinearMap.mem_ker.mp w.2) := by
  rw [transvectionAddHom, AddMonoidHom.mk'_apply, toMul_ofMul]

variable (Q) in
/-- **The Eichler transvections with a fixed isotropic vector `u`**, as a homomorphism
`w ↦ E_{u,w}` from the additive group of `u^⊥ / R ∙ u` into `SO(Q)`. Over a field it is
injective when `u` is not in the kernel of the polar form (`transvectionHom_injective`). -/
noncomputable def transvectionHom (hu : Q u = 0) :
    (LinearMap.ker (Q.polarBilin u) ⧸
        (R ∙ u).comap (LinearMap.ker (Q.polarBilin u)).subtype) →+
      Additive (specialOrthogonalGroup Q) :=
  QuotientAddGroup.lift _ (transvectionAddHom hu) fun w hw => by
    -- The transvection is trivial on the span of `u`, so the map descends to the quotient.
    -- Membership in the comapped span is membership of the underlying vector in `R ∙ u`.
    have hw' : (w : M) ∈ R ∙ u := hw
    apply Additive.toMul.injective
    rw [toMul_zero]
    exact Subtype.ext ((coe_toMul_transvectionAddHom hu w).trans
      (transvection_eq_one_of_mem_span hu _ hw'))

/-- The quotient homomorphism sends the class of `w` to the Eichler transvection `E_{u,w}`. -/
@[simp]
theorem coe_transvectionHom_mk (hu : Q u = 0) (huw : polar Q u w = 0) :
    ((Additive.toMul (transvectionHom Q hu (Submodule.Quotient.mk ⟨w, by simpa using huw⟩)) :
        specialOrthogonalGroup Q) : M ≃ₗ[R] M) = transvection Q hu huw := by
  erw [transvectionHom, QuotientAddGroup.lift_mk']
  exact coe_toMul_transvectionAddHom hu _

end CommRing

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {u w : V}

/-- Over a field, an Eichler transvection `E_{u,w}` is trivial exactly when `w` is a multiple of
`u`, provided `u` is not in the kernel of the polar form (for instance, `u ≠ 0` and `Q`
nondegenerate). -/
theorem transvection_eq_one_iff (hu : Q u = 0) (huw : polar Q u w = 0)
    (hu₀ : Q.polarBilin u ≠ 0) : transvection Q hu huw = 1 ↔ w ∈ K ∙ u := by
  refine ⟨fun h => ?_, transvection_eq_one_of_mem_span hu huw⟩
  obtain ⟨x, hx⟩ : ∃ x, polar Q x u ≠ 0 := by
    by_contra! H
    exact hu₀ (LinearMap.ext fun x => by simp [polar_comm Q u x, H x])
  have hEx : transvection Q hu huw x = x := by rw [h, LinearEquiv.coe_one, id_eq]
  rw [transvection_apply] at hEx
  have hw : polar Q x u • w = (polar Q x w + Q w * polar Q x u) • u := by
    linear_combination (norm := module) hEx
  refine Submodule.mem_span_singleton.mpr
    ⟨(polar Q x u)⁻¹ * (polar Q x w + Q w * polar Q x u), ?_⟩
  rw [mul_smul, ← hw, smul_smul, inv_mul_cancel₀ hx, one_smul]

/-- Over a field, the Eichler transvections with isotropic vector `u` form a copy of the additive
group `u^⊥ / K ∙ u` inside `SO(Q)`, provided `u` is not in the kernel of the polar form. -/
theorem transvectionHom_injective (hu : Q u = 0) (hu₀ : Q.polarBilin u ≠ 0) :
    Function.Injective (transvectionHom Q hu) := by
  refine (injective_iff_map_eq_zero _).mpr fun q hq => ?_
  induction q using Submodule.Quotient.induction_on with | H w => ?_
  obtain ⟨w, hw⟩ := w
  have huw : polar Q u w = 0 := by simpa using hw
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    ← transvection_eq_one_iff hu huw hu₀]
  have := congrArg (fun a => ((Additive.toMul a : specialOrthogonalGroup Q) : V ≃ₗ[K] V)) hq
  simpa only [coe_transvectionHom_mk hu huw, toMul_zero, OneMemClass.coe_one] using this

end Field

end QuadraticMap
