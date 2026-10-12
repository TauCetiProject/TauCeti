/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Eichler transvections of a quadratic form

Let `Q` be a quadratic form on `M` with un-halved polar form `B = polar Q`, so that
`B x x = 2 • Q x`. For an isotropic vector `u` (`Q u = 0`) and a vector `w` orthogonal to it
(`B u w = 0`), the **Eichler transvection** (also called a Siegel transformation) is

`E_{u,w} x = x + B x u • w - B x w • u - (Q w * B x u) • u`.

It is a proper isometry of `Q`. It fixes `u` and every vector orthogonal to both `u` and `w`, and it
depends on `w` only through its class modulo `R ∙ u`. For fixed `u`, the map `w ↦ E_{u,w}` turns
addition into composition. So the Eichler transvections with isotropic vector `u` are the image of
a homomorphism from the additive group `u^⊥ / R ∙ u` into `SO(Q)`. This homomorphism is injective
as soon as the polar form pairs `u` with some vector to a unit; over a field, as soon as `u` is not
in the kernel of the polar form. The orthogonal group acts on these subgroups by conjugation, moving
the pair `(u, w)`.

Nothing here assumes that `2` is invertible or that the scalars form a field. The formula uses `B`
and `Q`, never `B / 2`, so it makes sense verbatim for integral quadratic forms.

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
* `QuadraticMap.IsometryEquiv.transvectionParameterEquiv`: an isometry transports the parameter
  space `u^⊥ / ((R ∙ u) ∩ u^⊥)` to the corresponding space for `e u`; when `u` is
  isotropic, this is `u^⊥ / R ∙ u`.
* `QuadraticMap.IsometryEquiv.specialOrthogonalGroupCongr_comp_transvectionHom`: Eichler
  root-subgroup homomorphisms are natural under isometric equivalences.
* `QuadraticMap.transvection_eq_one_iff_of_isUnit`: if `polar Q x u` is a unit for some `x`,
  then `E_{u,w} = 1` exactly when `w ∈ R ∙ u`. Hence `transvectionHom_injective_of_isUnit`.
* `QuadraticMap.transvection_eq_one_iff`: over a field, if `polarBilin Q u ≠ 0`, then
  `E_{u,w} = 1` exactly when `w ∈ K ∙ u`. Hence `transvectionHom_injective`.
* `QuadraticMap.finrank_transvectionParameter`: for an isotropic vector outside the polar
  radical, the parameter space `u^⊥ / K ∙ u` has dimension `dim V - 2`.
* `QuadraticMap.subsingleton_transvectionParameter_of_finrank_eq_two`: for an isotropic vector
  outside the polar radical in a binary quadratic space, the parameter space `u^⊥ / K ∙ u` is
  trivial; consequently every Eichler transvection is the identity.

## References

* M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Springer (1952).
-/

public section

open TauCeti.QuadraticMap

universe u v

namespace QuadraticMap

namespace IsometryEquiv

section Parameter

variable {R : Type*} [CommRing R]
  {M₁ : Type*} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

private theorem map_transvectionParameterSubmodule (e : Q₁.IsometryEquiv Q₂) (u : M₁) :
    ((R ∙ u).comap (LinearMap.ker (Q₁.polarBilin u)).subtype).map
        (e.polarKernelEquiv u).toLinearMap =
      (R ∙ e u).comap (LinearMap.ker (Q₂.polarBilin (e u))).subtype := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- Membership in the comapped span is membership of the underlying vector in `R ∙ u`.
    change ((e.polarKernelEquiv u x : LinearMap.ker (Q₂.polarBilin (e u))) : M₂) ∈ R ∙ e u
    rw [e.coe_polarKernelEquiv_apply]
    change (x : M₁) ∈ R ∙ u at hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    exact Submodule.mem_span_singleton.mpr ⟨c, by
      calc
        c • e u = e (c • u) := (map_smul e c u).symm
        _ = e x := congrArg e hc⟩
  · intro hy
    let x : LinearMap.ker (Q₁.polarBilin u) := (e.polarKernelEquiv u).symm y
    refine ⟨x, ?_, (e.polarKernelEquiv u).apply_symm_apply y⟩
    -- Again expose membership in the comapped spans through the subtype coercions.
    change (x : M₁) ∈ R ∙ u
    change (y : M₂) ∈ R ∙ e u at hy
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    apply e.injective
    rw [map_smul, e.coe_polarKernelEquiv_symm_apply]
    exact hc.trans (e.apply_symm_apply y).symm

/-- An isometric equivalence transports the quotient `u^⊥ / ((R ∙ u) ∩ u^⊥)` to the
corresponding quotient for `e u`. When `u` is isotropic, this is the Eichler-transvection parameter
space `u^⊥ / R ∙ u`. -/
noncomputable def transvectionParameterEquiv (e : Q₁.IsometryEquiv Q₂) (u : M₁) :
    (LinearMap.ker (Q₁.polarBilin u) ⧸
        (R ∙ u).comap (LinearMap.ker (Q₁.polarBilin u)).subtype) ≃ₗ[R]
      (LinearMap.ker (Q₂.polarBilin (e u)) ⧸
        (R ∙ e u).comap (LinearMap.ker (Q₂.polarBilin (e u))).subtype) :=
  Submodule.Quotient.equiv _ _ (e.polarKernelEquiv u)
    (map_transvectionParameterSubmodule e u)

/-- Transport of Eichler-transvection parameters sends the class of `w` to the class of `e w`. -/
@[simp]
theorem transvectionParameterEquiv_mk (e : Q₁.IsometryEquiv Q₂)
    (u : M₁) (w : LinearMap.ker (Q₁.polarBilin u)) :
    e.transvectionParameterEquiv u (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨e w, by
        rw [LinearMap.mem_ker, polarBilin_apply_apply, e.polar_apply]
        exact LinearMap.mem_ker.mp w.2⟩ := by
  rw [transvectionParameterEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  exact e.coe_polarKernelEquiv_apply u w

/-- Inverse transport of Eichler-transvection parameters sends the class of `w` to the class of
`e.symm w`. -/
@[simp]
theorem transvectionParameterEquiv_symm_mk (e : Q₁.IsometryEquiv Q₂)
    (u : M₁) (w : LinearMap.ker (Q₂.polarBilin (e u))) :
    (e.transvectionParameterEquiv u).symm (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨e.symm w, by
        rw [LinearMap.mem_ker, polarBilin_apply_apply]
        calc
          polar Q₁ u (e.symm (w : M₂)) =
              polar Q₂ (e u) (e (e.symm (w : M₂))) :=
            (e.polar_apply u (e.symm (w : M₂))).symm
          _ = polar Q₂ (e u) w := congrArg (polar Q₂ (e u)) (e.apply_symm_apply w)
          _ = 0 := by
            simpa only [polarBilin_apply_apply] using LinearMap.mem_ker.mp w.2⟩ := by
  rw [LinearEquiv.symm_apply_eq, transvectionParameterEquiv_mk]
  congr 1
  apply Subtype.ext
  exact (e.apply_symm_apply w).symm

/-- The identity isometry induces the identity equivalence on Eichler-transvection parameters. -/
-- The quotient type depends on the transported vector, so rewriting this as a simp rule can leave
-- propositionally equal module structures with different proof terms. Keep it as a named law.
theorem transvectionParameterEquiv_refl (Q₁ : QuadraticForm R M₁) (u : M₁) :
    (QuadraticMap.IsometryEquiv.refl Q₁).transvectionParameterEquiv u =
      LinearEquiv.refl R _ := by
  apply LinearEquiv.ext
  intro q
  induction q using Submodule.Quotient.induction_on with | H w =>
    rw [transvectionParameterEquiv_mk]
    rfl

/-- Transport of Eichler-transvection parameters respects composition of isometries. -/
-- As for `transvectionParameterEquiv_refl`, dependent quotient types make this unsuitable as a
-- global simp rule even though the named equality has the expected orientation.
theorem transvectionParameterEquiv_trans
    {M₃ : Type*} [AddCommGroup M₃] [Module R M₃] {Q₃ : QuadraticForm R M₃}
    (e : Q₁.IsometryEquiv Q₂) (f : Q₂.IsometryEquiv Q₃) (u : M₁) :
    (e.trans f).transvectionParameterEquiv u =
      (e.transvectionParameterEquiv u).trans (f.transvectionParameterEquiv (e u)) := by
  apply LinearEquiv.ext
  intro q
  induction q using Submodule.Quotient.induction_on with | H w =>
    rw [(e.trans f).transvectionParameterEquiv_mk]
    -- The two target quotient types are propositionally identified by `IsometryEquiv.trans_apply`;
    -- expose sequential application before using the representative rules.
    change Submodule.Quotient.mk _ =
      f.transvectionParameterEquiv (e u)
        (e.transvectionParameterEquiv u (Submodule.Quotient.mk w))
    rw [e.transvectionParameterEquiv_mk, f.transvectionParameterEquiv_mk]
    congr 1

end Parameter

end IsometryEquiv

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

/-- Transporting an Eichler transvection along an isometric equivalence transports both of its
defining vectors. -/
@[simp]
theorem IsometryEquiv.specialOrthogonalGroupCongr_transvection
    {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] {Q₂ : QuadraticForm R M₂}
    (e : Q.IsometryEquiv Q₂) (hu : Q u = 0) (huw : polar Q u w = 0) :
    e.specialOrthogonalGroupCongr
        ⟨transvection Q hu huw, transvection_mem_specialOrthogonalGroup hu huw⟩ =
      ⟨transvection Q₂ ((e.map_app u).trans hu) ((e.polar_apply u w).trans huw),
        transvection_mem_specialOrthogonalGroup _ _⟩ := by
  apply Subtype.ext
  ext x
  rw [e.coe_specialOrthogonalGroupCongr_apply]
  calc
    e (transvection Q hu huw (e.symm x)) =
        e (e.symm x + polar Q (e.symm x) u • w - polar Q (e.symm x) w • u -
          (Q w * polar Q (e.symm x) u) • u) :=
      congrArg e (transvection_apply hu huw (e.symm x))
    _ = x + polar Q₂ x (e u) • e w - polar Q₂ x (e w) • e u -
        (Q₂ (e w) * polar Q₂ x (e u)) • e u := by
      simp only [map_sub, map_add, map_smul, e.apply_symm_apply, e.map_app]
      rw [← e.polar_apply (e.symm x) u, ← e.polar_apply (e.symm x) w,
        e.apply_symm_apply]
    _ = transvection Q₂ (u := e u) (w := e w)
        ((e.map_app u).trans hu) ((e.polar_apply u w).trans huw) x :=
      (transvection_apply _ _ x).symm

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
`w ↦ E_{u,w}` from the additive group of `u^⊥ / R ∙ u` into `SO(Q)`. It is injective when the
polar form pairs `u` with some vector to a unit (`transvectionHom_injective_of_isUnit`). -/
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

/-- The quotient homomorphism sends the class of `w` to the Eichler transvection `E_{u,w}` as an
element of the special orthogonal group. -/
theorem toMul_transvectionHom_mk (hu : Q u = 0) (huw : polar Q u w = 0) :
    Additive.toMul (transvectionHom Q hu (Submodule.Quotient.mk ⟨w, by simpa using huw⟩)) =
      ⟨transvection Q hu huw, transvection_mem_specialOrthogonalGroup hu huw⟩ :=
  Subtype.ext (coe_transvectionHom_mk hu huw)

/-- Eichler root-subgroup homomorphisms are natural under isometric equivalences of quadratic
forms. -/
theorem IsometryEquiv.specialOrthogonalGroupCongr_comp_transvectionHom
    {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] {Q₂ : QuadraticForm R M₂}
    (e : Q.IsometryEquiv Q₂) (hu : Q u = 0) :
    e.specialOrthogonalGroupCongr.toMonoidHom.toAdditive.comp (transvectionHom Q hu) =
      (transvectionHom Q₂ ((e.map_app u).trans hu)).comp
        (e.transvectionParameterEquiv u).toLinearMap.toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro q
  induction q using Submodule.Quotient.induction_on with | H w =>
    obtain ⟨w, hw⟩ := w
    have huw : polar Q u w = 0 := by simpa using hw
    have hparam :
        (e.transvectionParameterEquiv u).toLinearMap.toAddMonoidHom
            (Submodule.Quotient.mk ⟨w, hw⟩) =
          e.transvectionParameterEquiv u (Submodule.Quotient.mk ⟨w, hw⟩) :=
      by
        rw [LinearEquiv.toAddMonoidHom_commutes]
        rfl
    have htransport :
        e.specialOrthogonalGroupCongr.toMonoidHom
            ⟨transvection Q hu huw, transvection_mem_specialOrthogonalGroup hu huw⟩ =
          e.specialOrthogonalGroupCongr
            ⟨transvection Q hu huw, transvection_mem_specialOrthogonalGroup hu huw⟩ :=
      congrFun e.specialOrthogonalGroupCongr.coe_toMonoidHom _
    apply Additive.toMul.injective
    simp only [AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply, toMul_ofMul]
    rw [hparam, e.transvectionParameterEquiv_mk, toMul_transvectionHom_mk hu huw,
      toMul_transvectionHom_mk ((e.map_app u).trans hu) ((e.polar_apply u w).trans huw),
      htransport, e.specialOrthogonalGroupCongr_transvection]

/-- An Eichler transvection `E_{u,w}` is trivial exactly when `w` is a multiple of `u`, provided
the polar form pairs `u` with some vector to a unit. -/
theorem transvection_eq_one_iff_of_isUnit (hu : Q u = 0) (huw : polar Q u w = 0)
    (hu₀ : ∃ x, IsUnit (polar Q x u)) : transvection Q hu huw = 1 ↔ w ∈ R ∙ u := by
  refine ⟨fun h => ?_, transvection_eq_one_of_mem_span hu huw⟩
  obtain ⟨x, a, ha⟩ := hu₀
  have hEx : transvection Q hu huw x = x := by rw [h, LinearEquiv.coe_one, id_eq]
  rw [transvection_apply] at hEx
  have hw : polar Q x u • w = (polar Q x w + Q w * polar Q x u) • u := by
    linear_combination (norm := module) hEx
  refine Submodule.mem_span_singleton.mpr ⟨↑a⁻¹ * (polar Q x w + Q w * polar Q x u), ?_⟩
  rw [mul_smul, ← hw, ← ha, smul_smul, Units.inv_mul, one_smul]

/-- The Eichler transvections with isotropic vector `u` form a copy of the additive group
`u^⊥ / R ∙ u` inside `SO(Q)`, provided the polar form pairs `u` with some vector to a unit. -/
theorem transvectionHom_injective_of_isUnit (hu : Q u = 0) (hu₀ : ∃ x, IsUnit (polar Q x u)) :
    Function.Injective (transvectionHom Q hu) := by
  refine (injective_iff_map_eq_zero _).mpr fun q hq => ?_
  induction q using Submodule.Quotient.induction_on with | H w => ?_
  obtain ⟨w, hw⟩ := w
  have huw : polar Q u w = 0 := by simpa using hw
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    ← transvection_eq_one_iff_of_isUnit hu huw hu₀]
  have := congrArg (fun a => ((Additive.toMul a : specialOrthogonalGroup Q) : M ≃ₗ[R] M)) hq
  simpa only [coe_transvectionHom_mk hu huw, toMul_zero, OneMemClass.coe_one] using this

end CommRing

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {u w : V}

private theorem exists_isUnit_polar_of_polarBilin_ne_zero (hu₀ : Q.polarBilin u ≠ 0) :
    ∃ x, IsUnit (polar Q x u) := by
  by_contra! H
  exact hu₀ (LinearMap.ext fun x => by simpa [polar_comm Q u x] using H x)

/-- Over a field, an Eichler transvection `E_{u,w}` is trivial exactly when `w` is a multiple of
`u`, provided `u` is not in the kernel of the polar form (for instance, `u ≠ 0` and `Q`
nondegenerate). -/
theorem transvection_eq_one_iff (hu : Q u = 0) (huw : polar Q u w = 0)
    (hu₀ : Q.polarBilin u ≠ 0) : transvection Q hu huw = 1 ↔ w ∈ K ∙ u :=
  transvection_eq_one_iff_of_isUnit hu huw (exists_isUnit_polar_of_polarBilin_ne_zero hu₀)

/-- Over a field, the Eichler transvections with isotropic vector `u` form a copy of the additive
group `u^⊥ / K ∙ u` inside `SO(Q)`, provided `u` is not in the kernel of the polar form. -/
theorem transvectionHom_injective (hu : Q u = 0) (hu₀ : Q.polarBilin u ≠ 0) :
    Function.Injective (transvectionHom Q hu) :=
  transvectionHom_injective_of_isUnit hu (exists_isUnit_polar_of_polarBilin_ne_zero hu₀)

/-- The Eichler-transvection parameter space `u^⊥ / K ∙ u` of an isotropic vector outside the
polar radical has dimension `dim V - 2`. -/
theorem finrank_transvectionParameter [FiniteDimensional K V] (hu : Q u = 0)
    (hpolar : Q.polarBilin u ≠ 0) :
    Module.finrank K (LinearMap.ker (Q.polarBilin u) ⧸
      (K ∙ u).comap (LinearMap.ker (Q.polarBilin u)).subtype) = Module.finrank K V - 2 := by
  have hu₀ : u ≠ 0 := by
    rintro rfl
    exact hpolar (by ext; simp)
  have hspan_le : K ∙ u ≤ LinearMap.ker (Q.polarBilin u) := by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, polarBilin_apply_apply,
      polar_self, hu]
    simp
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hpolar
  have hquot := Submodule.finrank_quotient_add_finrank
    ((K ∙ u).comap (LinearMap.ker (Q.polarBilin u)).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe hspan_le).finrank_eq, finrank_span_singleton hu₀] at hquot
  omega

/-- In a binary quadratic space, the Eichler-transvection parameter space `u^⊥ / K ∙ u` of an
isotropic vector outside the polar radical is trivial. This is the low-dimensional
exception to the nontrivial transvection families available in dimension at least three. -/
theorem subsingleton_transvectionParameter_of_finrank_eq_two [FiniteDimensional K V]
    (hV : Module.finrank K V = 2) (hu : Q u = 0) (hpolar : Q.polarBilin u ≠ 0) :
    Subsingleton (LinearMap.ker (Q.polarBilin u) ⧸
      (K ∙ u).comap (LinearMap.ker (Q.polarBilin u)).subtype) := by
  apply (Module.finrank_zero_iff (R := K)).mp
  rw [finrank_transvectionParameter hu hpolar, hV]

/-- Every Eichler transvection in a binary quadratic space whose isotropic direction is outside
the polar radical is the identity. -/
theorem transvection_eq_one_of_finrank_eq_two [FiniteDimensional K V]
    (hV : Module.finrank K V = 2) (hu : Q u = 0) (huw : polar Q u w = 0)
    (hpolar : Q.polarBilin u ≠ 0) : transvection Q hu huw = 1 := by
  apply (transvection_eq_one_iff hu huw hpolar).2
  have hsub := subsingleton_transvectionParameter_of_finrank_eq_two hV hu hpolar
  have hzero : Submodule.Quotient.mk
      (⟨w, by simpa only [LinearMap.mem_ker, polarBilin_apply_apply] using huw⟩ :
        LinearMap.ker (Q.polarBilin u)) = 0 := hsub.elim _ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype] at hzero
  exact hzero

/-- The Eichler root-subgroup homomorphism is zero in a binary quadratic space when its isotropic
direction is outside the polar radical. -/
theorem transvectionHom_eq_zero_of_finrank_eq_two [FiniteDimensional K V]
    (hV : Module.finrank K V = 2) (hu : Q u = 0) (hpolar : Q.polarBilin u ≠ 0) :
    transvectionHom Q hu = 0 := by
  have hsub := subsingleton_transvectionParameter_of_finrank_eq_two hV hu hpolar
  apply AddMonoidHom.ext
  intro q
  rw [hsub.elim q 0, map_zero, map_zero]

end Field

end QuadraticMap
