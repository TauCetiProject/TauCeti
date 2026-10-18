/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Primitive
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
public import TauCeti.LinearAlgebra.IntegralLattice.Norm
public import TauCeti.LinearAlgebra.QuadraticForm.Transvection.Basic

/-!
# Eichler transvections of integral lattices

Let `L` be an integral lattice with rational form `B`, and let `u ∈ L` be isotropic. For a
lattice vector `w` with `B(u, w) = 0`, the Eichler transvection of the rational half-norm
`x ↦ B(x, x) / 2` is

`E_{u,w}(x) = x + B(x, u) • w - B(x, w) • u - (B(w, w) / 2 * B(x, u)) • u`.

Every coefficient is an integer on lattice vectors as soon as `B(w, w)` is even, so these `w`
form a sublattice `L.evenOrthogonal u` of `L`, the intersection of `u^⊥` with the even-norm
submodule. Since `E_{u,w + k • u} = E_{u,w}`, the map `w ↦ E_{u,w}` descends to a homomorphism
from `L.evenOrthogonal u ⧸ ℤ ∙ u` into the special isometry group `SO(L)`. When `u` is not in the
radical of the form, `E_{u,w}` is trivial exactly when `w ∈ ℚ ∙ u`; if moreover `u` is primitive,
the homomorphism is injective.

If `L` is nondegenerate of rank at least three and its rational space has a nonzero isotropic
vector, then `L ∩ u^⊥` contains a vector outside `ℚ ∙ u`, whose Eichler transvection has infinite
order. Hence `SO(L)`, and with it the isometry group `O(L)`, is infinite. This is the isotropic
half of the infiniteness of `O(L)` for indefinite lattices of rank at least three; it contrasts
with the finiteness of `O(L)` for definite lattices. In rank two every Eichler transvection whose
isotropic vector is outside the radical of the form is trivial
(`QuadraticMap.transvection_eq_one_of_finrank_eq_two`), and the argument gives nothing.

## Main definitions

* `TauCeti.IntegralLattice.evenOrthogonal`: the lattice vectors `w` with `B(u, w) = 0` and
  `B(w, w)` even.
* `TauCeti.IntegralLattice.eichlerTransvection`: the Eichler transvection `E_{u,w}` as a
  self-isometry of `L`.
* `TauCeti.IntegralLattice.eichlerTransvectionHom`: the homomorphism `w ↦ E_{u,w}` from
  `L.evenOrthogonal u ⧸ ℤ ∙ u` into `SO(L)`.

## Main results

* `TauCeti.IntegralLattice.eichlerTransvection_apply`: the defining formula.
* `TauCeti.IntegralLattice.eichlerTransvection_mem_specialOrthogonalGroup`: `E_{u,w} ∈ SO(L)`.
* `TauCeti.IntegralLattice.eichlerTransvection_add`: `E_{u,w + w'} = E_{u,w} * E_{u,w'}`.
* `TauCeti.IntegralLattice.eichlerTransvection_add_zsmul`: `E_{u,w + k • u} = E_{u,w}`.
* `TauCeti.IntegralLattice.eichlerTransvection_eq_one_iff`: if `u` is not in the radical of the
  form, `E_{u,w} = 1` exactly when `w ∈ ℚ ∙ u`.
* `TauCeti.IntegralLattice.eichlerTransvectionHom_injective`: if `u` is primitive and not in the
  radical of the form, `w ↦ E_{u,w}` is injective on `L.evenOrthogonal u ⧸ ℤ ∙ u`.
* `TauCeti.IntegralLattice.not_isOfFinOrder_eichlerTransvection`: if `u` is not in the radical of
  the form and `w ∉ ℚ ∙ u`, then `E_{u,w}` has infinite order.
* `TauCeti.IntegralLattice.infinite_specialOrthogonalGroup_of_not_anisotropic` and
  `TauCeti.IntegralLattice.infinite_isometry_of_not_anisotropic`: a nondegenerate lattice of rank
  at least three whose rational norm form is isotropic has infinite `SO(L)` and `O(L)`.

## References

* M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Springer (1952).
* `QuadraticMap.transvection`, the Eichler transvection of a quadratic form, which this file
  restricts to the lattice.
-/

public section

open QuadraticMap

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

/-! ## The rational half-norm -/

/-- The rational half-norm `x ↦ B(x, x) / 2`, whose polar form is the lattice form. -/
private noncomputable def halfNorm (L : IntegralLattice V) : QuadraticForm ℚ V :=
  (2 : ℚ)⁻¹ • L.norm

private theorem halfNorm_apply (L : IntegralLattice V) (x : V) :
    L.halfNorm x = L.form x x / 2 := by
  simp only [halfNorm, smul_apply, norm_apply, smul_eq_mul]
  ring

private theorem polar_halfNorm (L : IntegralLattice V) (x y : V) :
    polar L.halfNorm x y = L.form x y := by
  have h := LinearMap.BilinMap.polar_toQuadraticMap (B := L.form) x y
  rw [L.isSymm.eq y x] at h
  simp only [polar, halfNorm, smul_apply, smul_eq_mul, norm_def] at h ⊢
  linear_combination h / 2

private theorem polarBilin_halfNorm (L : IntegralLattice V) : L.halfNorm.polarBilin = L.form :=
  LinearMap.ext₂ (polar_halfNorm L)

/-! ## Even vectors orthogonal to a lattice vector -/

/-- The even vectors of `L` orthogonal to `u`: the `w ∈ L` with `B(u, w) = 0` and `B(w, w)` even,
that is, the kernel of `B(u, -)` intersected with the even-norm submodule. For isotropic `u` these
are the parameters of the integral Eichler transvections `E_{u,w}`. -/
noncomputable def evenOrthogonal (L : IntegralLattice V) (u : L) : Submodule ℤ L :=
  LinearMap.ker (L.integralForm u) ⊓ L.evenSubmodule

@[simp]
theorem mem_evenOrthogonal_iff {u w : L} :
    w ∈ L.evenOrthogonal u ↔ L.integralForm u w = 0 ∧ Even (L.integralNorm w) := by
  rw [evenOrthogonal, Submodule.mem_inf, LinearMap.mem_ker, mem_evenSubmodule_iff]

/-- Every multiple of an isotropic vector `u` is an even vector orthogonal to `u`. -/
theorem zsmul_mem_evenOrthogonal {u : L} (hu : L.integralNorm u = 0) (k : ℤ) :
    k • u ∈ L.evenOrthogonal u := by
  have huu : L.integralForm u u = 0 := by rwa [← integralNorm_apply]
  refine mem_evenOrthogonal_iff.mpr ⟨by rw [map_zsmul, huu, smul_zero], ?_⟩
  rw [QuadraticMap.map_smul, hu, smul_zero]
  exact ⟨0, rfl⟩

/-! ## Eichler transvections -/

section Transvection

variable {u : L}

private theorem halfNorm_eq_zero (hu : L.integralNorm u = 0) : L.halfNorm (u : V) = 0 := by
  rw [halfNorm_apply, ← integralForm_cast, ← integralNorm_apply, hu]
  simp

private theorem polar_halfNorm_eq_zero (w : L.evenOrthogonal u) :
    polar L.halfNorm (u : V) ((w : L) : V) = 0 := by
  rw [polar_halfNorm, ← integralForm_cast, (mem_evenOrthogonal_iff.mp w.2).1, Int.cast_zero]

/-- The ambient Eichler transvection of the rational half-norm, before restriction to `L`. -/
private noncomputable abbrev ambientTransvection (hu : L.integralNorm u = 0)
    (w : L.evenOrthogonal u) : V ≃ₗ[ℚ] V :=
  QuadraticMap.transvection L.halfNorm (halfNorm_eq_zero hu) (polar_halfNorm_eq_zero w)

/-- The half-norm of a parameter is the integer `B(w, w) / 2`. -/
private theorem halfNorm_parameter (w : L.evenOrthogonal u) :
    L.halfNorm ((w : L) : V) = ((L.integralNorm w / 2 : ℤ) : ℚ) := by
  rw [halfNorm_apply, ← integralForm_cast, ← integralNorm_apply,
    Int.cast_div (even_iff_two_dvd.mp (mem_evenOrthogonal_iff.mp w.2).2) (by norm_num),
    Int.cast_ofNat]

private theorem ambientTransvection_apply (hu : L.integralNorm u = 0) (w : L.evenOrthogonal u)
    (x : V) :
    ambientTransvection hu w x = x + L.form x u • ((w : L) : V) - L.form x w • (u : V) -
      (L.form w w / 2 * L.form x u) • (u : V) := by
  rw [transvection_apply, polar_halfNorm, polar_halfNorm, halfNorm_apply]

/-- On a lattice vector the ambient transvection is given by the integral formula. -/
private theorem ambientTransvection_coe (hu : L.integralNorm u = 0) (w : L.evenOrthogonal u)
    (x : L) :
    ambientTransvection hu w x = ((x + L.integralForm x u • (w : L) - L.integralForm x w • u -
      (L.integralNorm w / 2 * L.integralForm x u) • u : L) : V) := by
  rw [transvection_apply, polar_halfNorm, polar_halfNorm, halfNorm_parameter,
    ← integralForm_cast, ← integralForm_cast, ← Int.cast_mul]
  simp only [Int.cast_smul_eq_zsmul, Submodule.coe_sub, Submodule.coe_add,
    Submodule.coe_smul_of_tower]

private theorem ambientTransvection_mem_carrier (hu : L.integralNorm u = 0)
    (w : L.evenOrthogonal u) {x : V} (hx : x ∈ L.carrier) :
    ambientTransvection hu w x ∈ L.carrier := by
  rw [ambientTransvection_coe hu w ⟨x, hx⟩]
  exact Subtype.property _

private theorem ambientTransvection_neg (hu : L.integralNorm u = 0) (w : L.evenOrthogonal u) :
    ambientTransvection hu (-w) = (ambientTransvection hu w)⁻¹ :=
  transvection_neg _ _

/-- The **Eichler transvection** `E_{u,w}` of an integral lattice, for an isotropic lattice vector
`u` and an even lattice vector `w` orthogonal to it:
`E_{u,w}(x) = x + B(x, u) • w - B(x, w) • u - (B(w, w) / 2 * B(x, u)) • u`. -/
noncomputable def eichlerTransvection (hu : L.integralNorm u = 0) (w : L.evenOrthogonal u) :
    Isometry L L where
  toLinearEquiv := ambientTransvection hu w
  map_app' x y := by
    rw [← polar_halfNorm, ← polar_halfNorm]
    exact QuadraticMap.polar_apply_of_mem_orthogonalGroup
      (transvection_mem_orthogonalGroup (halfNorm_eq_zero hu) (polar_halfNorm_eq_zero w)) x y
  map_carrier := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ambientTransvection_mem_carrier hu w hx
    · intro x hx
      refine ⟨ambientTransvection hu (-w) x, ambientTransvection_mem_carrier hu (-w) hx, ?_⟩
      rw [LinearEquiv.coe_toLinearMap, LinearEquiv.restrictScalars_apply, ambientTransvection_neg,
        ← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id_eq]

private theorem eichlerTransvection_apply_eq (hu : L.integralNorm u = 0)
    (w : L.evenOrthogonal u) (x : V) :
    eichlerTransvection hu w x = ambientTransvection hu w x := (rfl)

/-- The Eichler transvection acts by
`E_{u,w}(x) = x + B(x, u) • w - B(x, w) • u - (B(w, w) / 2 * B(x, u)) • u`. -/
theorem eichlerTransvection_apply (hu : L.integralNorm u = 0) (w : L.evenOrthogonal u) (x : V) :
    eichlerTransvection hu w x = x + L.form x u • ((w : L) : V) - L.form x w • (u : V) -
      (L.form w w / 2 * L.form x u) • (u : V) :=
  ambientTransvection_apply hu w x

/-- On the carrier, the Eichler transvection is given by the same formula with integral
coefficients. -/
theorem eichlerTransvection_carrierEquiv_apply (hu : L.integralNorm u = 0)
    (w : L.evenOrthogonal u) (x : L) :
    (eichlerTransvection hu w).carrierEquiv x = x + L.integralForm x u • (w : L) -
      L.integralForm x w • u - (L.integralNorm w / 2 * L.integralForm x u) • u :=
  Subtype.ext ((Isometry.coe_carrierEquiv_apply _ x).trans (ambientTransvection_coe hu w x))

/-- An Eichler transvection fixes its isotropic vector. -/
@[simp]
theorem eichlerTransvection_apply_self (hu : L.integralNorm u = 0) (w : L.evenOrthogonal u) :
    eichlerTransvection hu w u = u :=
  transvection_apply_self _ _

/-- An Eichler transvection fixes every vector orthogonal to both `u` and `w`. -/
@[simp]
theorem eichlerTransvection_apply_of_form_eq_zero (hu : L.integralNorm u = 0)
    (w : L.evenOrthogonal u) {x : V} (hxu : L.form x u = 0) (hxw : L.form x w = 0) :
    eichlerTransvection hu w x = x := by
  simp [eichlerTransvection_apply, hxu, hxw]

/-- An Eichler transvection has determinant one. -/
@[simp]
theorem det_eichlerTransvection (hu : L.integralNorm u = 0) (w : L.evenOrthogonal u) :
    Isometry.det L (eichlerTransvection hu w) = 1 := by
  -- On the carrier, `E_{u,w}` is the composite of the integral linear transvections
  -- `x ↦ x + B(u, x) • w` and `x ↦ x + (k B(u, x) - B(w, x)) • u`, where `2k = B(w, w)`.
  obtain ⟨h₁, hw⟩ := mem_evenOrthogonal_iff.mp w.2
  have huu : L.integralForm u u = 0 := by rwa [← integralNorm_apply]
  have hwu : L.integralForm w u = 0 := by rw [L.isSymm_integralForm.eq, h₁]
  have h₂ : ((L.integralNorm w / 2) • L.integralForm u - L.integralForm w) u = 0 := by
    simp [hwu, huu]
  have hcarrier : (eichlerTransvection hu w).carrierEquiv =
      (LinearEquiv.transvection h₁).trans (LinearEquiv.transvection h₂) := by
    refine LinearEquiv.ext fun x ↦ ?_
    have hww : L.integralForm w w = 2 * (L.integralNorm w / 2) := by
      rw [← integralNorm_apply, Int.mul_ediv_cancel' (even_iff_two_dvd.mp hw)]
    simp only [eichlerTransvection_carrierEquiv_apply, LinearEquiv.trans_apply,
      LinearEquiv.transvection.apply, LinearMap.sub_apply, LinearMap.smul_apply, map_add,
      map_smul, h₁, hww, L.isSymm_integralForm.eq x, smul_eq_mul]
    module
  rw [Isometry.det_apply, hcarrier, ← LinearEquiv.mul_eq_trans, map_mul,
    LinearEquiv.transvection.det_eq_one, LinearEquiv.transvection.det_eq_one, mul_one]

/-- An Eichler transvection is a proper isometry. -/
theorem eichlerTransvection_mem_specialOrthogonalGroup (hu : L.integralNorm u = 0)
    (w : L.evenOrthogonal u) : eichlerTransvection hu w ∈ specialOrthogonalGroup L :=
  mem_specialOrthogonalGroup_iff.mpr (det_eichlerTransvection hu w)

/-- The Eichler transvection with parameter `0` is the identity. -/
theorem eichlerTransvection_zero (hu : L.integralNorm u = 0) : eichlerTransvection hu 0 = 1 := by
  ext x
  simp [eichlerTransvection_apply]

/-- The Eichler transvections with a fixed isotropic vector `u` compose additively in `w`. -/
@[simp]
theorem eichlerTransvection_add (hu : L.integralNorm u = 0) (w w' : L.evenOrthogonal u) :
    eichlerTransvection hu (w + w') = eichlerTransvection hu w * eichlerTransvection hu w' := by
  ext x
  rw [Isometry.mul_apply, eichlerTransvection_apply_eq, eichlerTransvection_apply_eq,
    eichlerTransvection_apply_eq]
  exact LinearEquiv.congr_fun (transvection_add (halfNorm_eq_zero hu)
    (polar_halfNorm_eq_zero w) (polar_halfNorm_eq_zero w')) x

/-- The Eichler transvections with isotropic vector `u`, as a homomorphism out of the even
vectors orthogonal to `u`. It descends to `L.evenOrthogonal u ⧸ ℤ ∙ u` as
`eichlerTransvectionHom`. -/
private noncomputable def eichlerTransvectionAddHom (hu : L.integralNorm u = 0) :
    L.evenOrthogonal u →+ Additive (specialOrthogonalGroup L) :=
  AddMonoidHom.mk' (fun w ↦ Additive.ofMul
      ⟨eichlerTransvection hu w, eichlerTransvection_mem_specialOrthogonalGroup hu w⟩)
    fun w w' ↦ by
      apply Additive.toMul.injective
      exact Subtype.ext (eichlerTransvection_add hu w w')

private theorem coe_toMul_eichlerTransvectionAddHom (hu : L.integralNorm u = 0)
    (w : L.evenOrthogonal u) :
    ((Additive.toMul (eichlerTransvectionAddHom hu w) : specialOrthogonalGroup L) :
      Isometry L L) = eichlerTransvection hu w := (rfl)

/-- The inverse of an Eichler transvection is the Eichler transvection of `-w`. -/
@[simp]
theorem eichlerTransvection_neg (hu : L.integralNorm u = 0) (w : L.evenOrthogonal u) :
    eichlerTransvection hu (-w) = (eichlerTransvection hu w)⁻¹ := by
  have h := congrArg (fun a ↦ ((Additive.toMul a : specialOrthogonalGroup L) : Isometry L L))
    (map_neg (eichlerTransvectionAddHom hu) w)
  simpa only [toMul_neg, Subgroup.coe_inv, coe_toMul_eichlerTransvectionAddHom] using h

/-- Integer multiples of the parameter give powers of an Eichler transvection. -/
theorem eichlerTransvection_zsmul (hu : L.integralNorm u = 0) (w : L.evenOrthogonal u) (n : ℤ) :
    eichlerTransvection hu (n • w) = eichlerTransvection hu w ^ n := by
  have h := congrArg (fun a ↦ ((Additive.toMul a : specialOrthogonalGroup L) : Isometry L L))
    (map_zsmul (eichlerTransvectionAddHom hu) n w)
  simpa only [toMul_zsmul, Subgroup.coe_zpow, coe_toMul_eichlerTransvectionAddHom] using h

/-- An Eichler transvection whose parameter is a rational multiple of `u` is the identity. -/
@[simp]
theorem eichlerTransvection_eq_one_of_mem_span (hu : L.integralNorm u = 0)
    {w : L.evenOrthogonal u} (hw : ((w : L) : V) ∈ ℚ ∙ (u : V)) : eichlerTransvection hu w = 1 := by
  ext x
  rw [Isometry.one_apply, eichlerTransvection_apply_eq]
  exact LinearEquiv.congr_fun (transvection_eq_one_of_mem_span _ _ hw) x

/-- An Eichler transvection depends on its parameter only modulo `ℤ ∙ u`:
`E_{u,w + k • u} = E_{u,w}`. -/
theorem eichlerTransvection_add_zsmul (hu : L.integralNorm u = 0) (w : L.evenOrthogonal u)
    (k : ℤ) :
    eichlerTransvection hu (w + ⟨k • u, zsmul_mem_evenOrthogonal hu k⟩) =
      eichlerTransvection hu w := by
  rw [eichlerTransvection_add, eichlerTransvection_eq_one_of_mem_span hu
    (w := ⟨k • u, zsmul_mem_evenOrthogonal hu k⟩)
    (zsmul_mem (Submodule.mem_span_singleton_self (u : V)) k), mul_one]

/-- **The Eichler transvections with isotropic vector `u`**, as a homomorphism from the parameter
group `L.evenOrthogonal u ⧸ ℤ ∙ u` into the special isometry group, sending the class of `w` to
`E_{u,w}`. It is injective when `u` is primitive and not in the radical of the form
(`eichlerTransvectionHom_injective`). -/
noncomputable def eichlerTransvectionHom (hu : L.integralNorm u = 0) :
    (L.evenOrthogonal u ⧸ (ℤ ∙ u).comap (L.evenOrthogonal u).subtype) →+
      Additive (specialOrthogonalGroup L) :=
  QuotientAddGroup.lift _ (eichlerTransvectionAddHom hu) fun w hw ↦ by
    -- Membership in the comapped span is membership of the underlying vector in `ℤ ∙ u`.
    have hw' : (w : L) ∈ ℤ ∙ u := hw
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hw'
    apply Additive.toMul.injective
    refine Subtype.ext ((coe_toMul_eichlerTransvectionAddHom hu w).trans
      (eichlerTransvection_eq_one_of_mem_span hu ?_))
    rw [← hk]
    exact zsmul_mem (Submodule.mem_span_singleton_self (u : V)) k

/-- The homomorphism sends the class of `w` to the Eichler transvection `E_{u,w}`, as an element
of `specialOrthogonalGroup L`. -/
@[simp]
theorem toMul_eichlerTransvectionHom_mk (hu : L.integralNorm u = 0) (w : L.evenOrthogonal u) :
    Additive.toMul (eichlerTransvectionHom hu (Submodule.Quotient.mk w)) =
      ⟨eichlerTransvection hu w, eichlerTransvection_mem_specialOrthogonalGroup hu w⟩ := (rfl)

/-- The homomorphism sends the class of `w` to the Eichler transvection `E_{u,w}`, as an isometry
of `L`. -/
theorem coe_toMul_eichlerTransvectionHom_mk (hu : L.integralNorm u = 0)
    (w : L.evenOrthogonal u) :
    ((Additive.toMul (eichlerTransvectionHom hu (Submodule.Quotient.mk w)) :
      specialOrthogonalGroup L) : Isometry L L) = eichlerTransvection hu w := (rfl)

/-- If `u` is not in the radical of the form (for instance, `u ≠ 0` and `L` is nondegenerate),
then the Eichler transvection `E_{u,w}` is the identity exactly when `w` is a rational multiple
of `u`. -/
theorem eichlerTransvection_eq_one_iff (hu : L.integralNorm u = 0) (hu₀ : L.form u ≠ 0)
    (w : L.evenOrthogonal u) :
    eichlerTransvection hu w = 1 ↔ ((w : L) : V) ∈ ℚ ∙ (u : V) := by
  rw [← transvection_eq_one_iff (halfNorm_eq_zero hu) (polar_halfNorm_eq_zero w)
    (L.polarBilin_halfNorm ▸ hu₀)]
  constructor
  · intro h
    ext x
    have hx := congrArg (fun e : Isometry L L ↦ e x) h
    rw [Isometry.one_apply, eichlerTransvection_apply_eq] at hx
    exact hx
  · intro h
    ext x
    rw [Isometry.one_apply, eichlerTransvection_apply_eq]
    exact LinearEquiv.congr_fun h x

/-- If `u` is primitive and not in the radical of the form, the Eichler transvections with
isotropic vector `u` form a copy of the parameter group `L.evenOrthogonal u ⧸ ℤ ∙ u` inside
`SO(L)`. -/
theorem eichlerTransvectionHom_injective (hu : L.integralNorm u = 0) (hu₀ : L.form u ≠ 0)
    (hprim : IsPrimitive u) : Function.Injective (eichlerTransvectionHom hu) := by
  refine (injective_iff_map_eq_zero _).mpr fun q hq ↦ ?_
  induction q using Submodule.Quotient.induction_on with | H w => ?_
  have h := congrArg (fun a ↦ ((Additive.toMul a : specialOrthogonalGroup L) : Isometry L L)) hq
  simp only [coe_toMul_eichlerTransvectionHom_mk, toMul_zero, OneMemClass.coe_one] at h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((eichlerTransvection_eq_one_iff hu hu₀ w).mp h)
  obtain ⟨f, hf⟩ := isPrimitive_def.mp hprim
  -- Clearing the denominator of `c` and applying `f` with `f u = 1` shows that `c = f w`.
  have hden : (c.den : ℤ) • (w : L) = c.num • u := Subtype.ext <| by
    rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, ← hc,
      ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast,
      Rat.den_mul_eq_num]
  have hnum : (c.den : ℤ) * f w = c.num := by
    simpa [hf] using congrArg f hden
  have hcf : c = (f w : ℚ) := by
    rw [← Rat.num_div_den c, ← hnum, Int.cast_mul, Int.cast_natCast,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr c.den_nz)]
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    Submodule.mem_span_singleton]
  refine ⟨f w, Subtype.ext ?_⟩
  rw [Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ, ← hcf, hc]

/-- If `u` is not in the radical of the form, an Eichler transvection whose parameter is not a
rational multiple of `u` has infinite order. -/
theorem not_isOfFinOrder_eichlerTransvection (hu : L.integralNorm u = 0)
    (hu₀ : L.form u ≠ 0) {w : L.evenOrthogonal u} (hw : ((w : L) : V) ∉ ℚ ∙ (u : V)) :
    ¬ IsOfFinOrder (eichlerTransvection hu w) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, h⟩
  rw [← zpow_natCast, ← eichlerTransvection_zsmul, eichlerTransvection_eq_one_iff hu hu₀] at h
  apply hw
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← Submodule.smul_mem_iff _ hn']
  convert h using 1
  simp [Nat.cast_smul_eq_nsmul]

end Transvection

/-! ## Infinite isometry groups -/

/-- If `L` has rank at least three and `u` is not in the radical of the form, then some even
lattice vector orthogonal to `u` is not a rational multiple of `u`. -/
theorem exists_mem_evenOrthogonal_notMem_span (hrank : 3 ≤ Module.finrank ℤ L) {u : L}
    (hu₀ : L.form u ≠ 0) : ∃ w ∈ L.evenOrthogonal u, (w : V) ∉ ℚ ∙ (u : V) := by
  have := L.finiteDimensional
  obtain ⟨v, huv, hv⟩ := exists_polar_eq_zero_not_mem_span_of_finrank_ge_three L.halfNorm
    (L.polarBilin_halfNorm ▸ hu₀) (L.finrank_carrier ▸ hrank)
  rw [polar_halfNorm] at huv
  obtain ⟨s, hs, hsv⟩ := Submodule.IsLattice.exists_ne_zero_smul_mem ℚ L.carrier v
  -- Doubling makes the norm even; the scalar `2 * s` is nonzero, so `w` stays off the line.
  refine ⟨(2 : ℤ) • ⟨s • v, hsv⟩, mem_evenOrthogonal_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · apply Int.cast_injective (α := ℚ)
    simp [integralForm_cast, huv]
  · rw [QuadraticMap.map_smul, smul_eq_mul]
    exact (even_two.mul_right 2).mul_right _
  · have h2s : ((2 * s : ℤ) : ℚ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero hs
    have heq : ((((2 : ℤ) • ⟨s • v, hsv⟩ : L) : V)) = ((2 * s : ℤ) : ℚ) • v := by
      rw [Int.cast_smul_eq_zsmul, mul_smul]
      rfl
    rwa [heq, Submodule.smul_mem_iff _ h2s]

/-- **The isotropic case of the infiniteness of `SO(L)`.** A nondegenerate integral lattice of
rank at least three whose rational norm form represents zero nontrivially has infinitely many
proper isometries, already among its Eichler transvections. -/
theorem infinite_specialOrthogonalGroup_of_not_anisotropic [L.IsNondegenerate]
    (hrank : 3 ≤ Module.finrank ℤ L) (hiso : ¬ L.norm.Anisotropic) :
    Infinite (specialOrthogonalGroup L) := by
  obtain ⟨v, hv, hv₀⟩ : ∃ v : V, L.norm v = 0 ∧ v ≠ 0 := by
    simpa [QuadraticMap.Anisotropic] using hiso
  obtain ⟨s, hs, hsv⟩ := Submodule.IsLattice.exists_ne_zero_smul_mem ℚ L.carrier v
  set u : L := ⟨s • v, hsv⟩
  have hsv' : (s : ℚ) • v = (u : V) := Int.cast_smul_eq_zsmul ℚ s v
  have hu₀ : L.form u ≠ 0 := by
    intro h
    have hu0 : (u : V) = 0 := L.form_nondegenerate.1 u fun y ↦ by simp [h]
    rw [hu0] at hsv'
    exact hv₀ ((smul_eq_zero.mp hsv').resolve_left (Int.cast_ne_zero.mpr hs))
  have hu : L.integralNorm u = 0 := by
    apply Int.cast_injective (α := ℚ)
    rw [integralNorm_apply, integralForm_cast, Int.cast_zero, ← norm_apply, ← hsv',
      QuadraticMap.map_smul, hv, smul_zero]
  obtain ⟨w, hw, hwu⟩ := exists_mem_evenOrthogonal_notMem_span hrank hu₀
  refine not_finite_iff_infinite.mp fun hfin ↦
    not_isOfFinOrder_eichlerTransvection hu hu₀ (w := ⟨w, hw⟩) hwu ?_
  exact (specialOrthogonalGroup L).subtype.isOfFinOrder (isOfFinOrder_of_finite
    (⟨_, eichlerTransvection_mem_specialOrthogonalGroup hu ⟨w, hw⟩⟩ : specialOrthogonalGroup L))

/-- **The isotropic case of the infiniteness of `O(L)`.** A nondegenerate integral lattice of
rank at least three whose rational norm form represents zero nontrivially has infinitely many
isometries. -/
theorem infinite_isometry_of_not_anisotropic [L.IsNondegenerate]
    (hrank : 3 ≤ Module.finrank ℤ L) (hiso : ¬ L.norm.Anisotropic) : Infinite (Isometry L L) :=
  have := infinite_specialOrthogonalGroup_of_not_anisotropic hrank hiso
  Infinite.of_injective (Subtype.val : specialOrthogonalGroup L → Isometry L L)
    Subtype.val_injective

end TauCeti.IntegralLattice
