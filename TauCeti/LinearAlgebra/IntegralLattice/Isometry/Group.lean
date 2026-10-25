/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.RingTheory.QuotSMulTop
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Basic
import TauCeti.Algebra.Module.Torsion.Int

/-!
# The isometry group of an integral lattice

The self-isometries of an integral lattice `L` form a group `O(L) = Isometry L L` under
composition, with `f * g` the isometry `g` followed by `f`, as for `LinearEquiv.automorphismGroup`.
Restricting a self-isometry to the carrier is a group homomorphism into the automorphism group of
the carrier, and composing with the determinant gives the **determinant** of a self-isometry, a
unit of `ℤ`, hence `±1`; it is also the determinant of the ambient rational linear
equivalence. Its kernel is the **special isometry group** `SO(L)`, a subgroup of index at most
two. Negation is a self-isometry of every lattice, the element `-1` of `O(L)`, and its
determinant is `(-1) ^ rank L`; so `SO(L)` is a proper subgroup in odd rank. Conjugation by an
isometry `L → M` identifies `O(L)` with `O(M)` and `SO(L)` with `SO(M)`.

A self-isometry is the same as a rational isometry of the ambient form which, together with its
inverse, preserves the carrier; `toIsometryGroup` and `ofIsometryGroup` pass between the two. The
self-isometries acting trivially on the finite quotient `L / d L` form the principal congruence
subgroup of level `d`, which has finite index for `d ≠ 0`.

## Main definitions

* The `Group` instance on `Isometry L L`: composition, identity and inversion of self-isometries.
* `TauCeti.IntegralLattice.Isometry.carrierEquivHom`: restriction to the carrier as a group
  homomorphism `O(L) →* (L ≃ₗ[ℤ] L)`.
* `TauCeti.IntegralLattice.Isometry.det`: the determinant `O(L) →* ℤˣ`.
* `TauCeti.IntegralLattice.specialOrthogonalGroup`: the subgroup `SO(L)` of determinant one.
* `TauCeti.IntegralLattice.Isometry.neg`: negation, the element `-1` of `O(L)`.
* `TauCeti.IntegralLattice.specialOrthogonalGroup.toSpecialLinearGroup`: restriction to the
  carrier as a group homomorphism from `SO(L)` to the special linear group of the carrier.
* `TauCeti.IntegralLattice.specialOrthogonalGroup.toMatrix`: the matrix of a proper isometry in a
  finite carrier basis, as a group homomorphism into `Matrix.SpecialLinearGroup ι ℤ`.
* `TauCeti.IntegralLattice.Isometry.toIsometryGroup`: a self-isometry as an element of the isometry
  group of the rational form, with partial inverse
  `TauCeti.IntegralLattice.Isometry.ofIsometryGroup`.
* `TauCeti.IntegralLattice.Isometry.reductionHom`: the action of `O(L)` on `L / d L`, and
  `TauCeti.IntegralLattice.Isometry.congruenceSubgroup`: its kernel.
* `TauCeti.IntegralLattice.Isometry.conj`: conjugation by an isometry `L → M`, as a group
  isomorphism `O(L) ≃* O(M)`.

## Main results

* `TauCeti.IntegralLattice.Isometry.carrierEquivHom_injective`: a self-isometry is determined by
  its restriction to the carrier.
* `TauCeti.IntegralLattice.Isometry.coe_det_eq_det_toLinearMap`: the determinant of a
  self-isometry is that of its ambient rational linear equivalence.
* `TauCeti.IntegralLattice.Isometry.det_conj` and
  `TauCeti.IntegralLattice.map_conj_specialOrthogonalGroup`: conjugation preserves the determinant
  and carries `SO(L)` onto `SO(M)`.
* `TauCeti.IntegralLattice.Isometry.orientation_map_eq_iff` and
  `TauCeti.IntegralLattice.Isometry.orientation_map_eq_neg_iff`: the determinant detects whether
  a self-isometry preserves or reverses the orientation of any finite carrier basis.
* `TauCeti.IntegralLattice.index_specialOrthogonalGroup_le_two`: `SO(L)` has index at most two.
* `TauCeti.IntegralLattice.Isometry.det_neg`: the determinant of negation is `(-1) ^ rank L`.
* `TauCeti.IntegralLattice.specialOrthogonalGroup.toMatrix_injective`: a proper isometry is
  determined by its matrix in a finite carrier basis.
* `TauCeti.IntegralLattice.Isometry.mem_congruenceSubgroup_iff`: an isometry lies in the
  congruence subgroup of level `d` when it moves every lattice vector by `d` times a lattice
  vector, and `TauCeti.IntegralLattice.Isometry.finiteIndex_congruenceSubgroup`: for `d ≠ 0` this
  subgroup has finite index.
* `TauCeti.IntegralLattice.Isometry.mem_range_toIsometryGroup_iff`: a rational isometry comes from
  a self-isometry exactly when it preserves membership in the carrier.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 3, §4
-/

public section

namespace TauCeti

namespace IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

namespace Isometry

/-- The self-isometries of an integral lattice form a group under composition: `f * g` is `g`
followed by `f`, the identity is `refl` and the inverse is `symm`, as for
`LinearEquiv.automorphismGroup`. -/
instance : Group (Isometry L L) where
  mul f g := g.trans f
  one := refl L
  inv f := f.symm
  mul_assoc a b c := (trans_assoc c b a).symm
  one_mul f := trans_refl f
  mul_one f := refl_trans f
  inv_mul_cancel f := self_trans_symm f

theorem one_def : (1 : Isometry L L) = refl L := (rfl)

theorem mul_def (f g : Isometry L L) : f * g = g.trans f := (rfl)

theorem inv_def (f : Isometry L L) : f⁻¹ = f.symm := (rfl)

@[simp]
theorem one_apply (x : V) : (1 : Isometry L L) x = x := refl_apply L x

@[simp]
theorem mul_apply (f g : Isometry L L) (x : V) : (f * g) x = f (g x) := trans_apply g f x

@[simp]
theorem inv_apply (f : Isometry L L) (x : V) : f⁻¹ x = f.symm x := (rfl)

/-- Restriction of a self-isometry to the carrier, as a group homomorphism from `O(L)` to the
automorphism group of the carrier. -/
def carrierEquivHom (L : IntegralLattice V) : Isometry L L →* (L ≃ₗ[ℤ] L) where
  toFun e := e.carrierEquiv
  map_one' := carrierEquiv_refl L
  map_mul' f g := by rw [mul_def, carrierEquiv_trans, LinearEquiv.mul_eq_trans]

@[simp]
theorem carrierEquivHom_apply (e : Isometry L L) : carrierEquivHom L e = e.carrierEquiv := (rfl)

/-- A self-isometry is determined by its restriction to the carrier. -/
theorem carrierEquivHom_injective (L : IntegralLattice V) :
    Function.Injective (carrierEquivHom L) :=
  carrierEquiv_injective

/-- The determinant of a self-isometry of an integral lattice: the determinant of its restriction
to the carrier, a unit of `ℤ`. -/
noncomputable def det (L : IntegralLattice V) : Isometry L L →* ℤˣ :=
  LinearEquiv.det.comp (carrierEquivHom L)

theorem det_apply (e : Isometry L L) : det L e = LinearEquiv.det e.carrierEquiv := (rfl)

@[simp]
theorem coe_det (e : Isometry L L) :
    (det L e : ℤ) = LinearMap.det (e.carrierEquiv : L →ₗ[ℤ] L) :=
  LinearEquiv.coe_det e.carrierEquiv

/-- The determinant of a self-isometry is `1` or `-1`. -/
theorem det_eq_one_or_neg_one (e : Isometry L L) : det L e = 1 ∨ det L e = -1 :=
  Int.units_eq_one_or (det L e)

/-- A self-isometry preserves a finite carrier basis orientation exactly when its determinant
is one. -/
theorem orientation_map_eq_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ L) (e : Isometry L L) :
    (b.map e.carrierEquiv).orientation = b.orientation ↔ det L e = 1 := by
  rw [Module.Basis.orientation_comp_linearEquiv_eq_iff_det_pos, ← coe_det]
  rcases det_eq_one_or_neg_one e with h | h <;> simp [h]

/-- A self-isometry reverses a finite carrier basis orientation exactly when its determinant
is minus one. -/
theorem orientation_map_eq_neg_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ L) (e : Isometry L L) :
    (b.map e.carrierEquiv).orientation = -b.orientation ↔ det L e = -1 := by
  rw [Module.Basis.orientation_comp_linearEquiv_eq_neg_iff_det_neg, ← coe_det]
  rcases det_eq_one_or_neg_one e with h | h <;> simp [h]

/-- Negation is a self-isometry of every integral lattice: the element `-1` of `O(L)`. -/
def neg (L : IntegralLattice V) : Isometry L L where
  toIsometryEquiv :=
    { toLinearEquiv := LinearEquiv.neg ℚ
      map_app' x y := by simp }
  map_carrier := by
    have h : ((LinearEquiv.neg ℚ : V ≃ₗ[ℚ] V).restrictScalars ℤ).toLinearMap =
        -(LinearMap.id : V →ₗ[ℤ] V) := by
      ext x
      simp
    rw [h, Submodule.map_neg, Submodule.map_id]

@[simp]
theorem neg_apply (L : IntegralLattice V) (x : V) : neg L x = -x := (rfl)

/-- Negation restricts to negation of the carrier. -/
@[simp]
theorem carrierEquiv_neg (L : IntegralLattice V) : (neg L).carrierEquiv = LinearEquiv.neg ℤ := by
  ext x
  simp

/-- Negation is an involution of `O(L)`. -/
@[simp]
theorem neg_mul_neg (L : IntegralLattice V) : neg L * neg L = 1 := by
  ext x
  simp

/-- The determinant of negation is `(-1) ^ rank L`. -/
@[simp]
theorem det_neg (L : IntegralLattice V) : det L (neg L) = (-1) ^ Module.finrank ℤ L := by
  apply Units.ext
  rw [coe_det, carrierEquiv_neg, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  have h : ((LinearEquiv.neg ℤ : L ≃ₗ[ℤ] L) : L →ₗ[ℤ] L) = (-1 : ℤ) • LinearMap.id := by
    ext x
    simp
  rw [h, LinearMap.det_smul, LinearMap.det_id, mul_one]

/-- The determinant of a self-isometry is the determinant of its ambient rational linear
equivalence. -/
theorem coe_det_eq_det_toLinearMap (e : Isometry L L) :
    ((det L e : ℤ) : ℚ) = LinearMap.det ((e : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) := by
  rw [coe_det, LinearEquiv.eq_extendOfIsLattice e.carrierEquiv (e : V ≃ₗ[ℚ] V)
    fun x ↦ (e.coe_carrierEquiv_apply x).symm, LinearEquiv.det_extendOfIsLattice,
    algebraMap_int_eq, eq_intCast]

section Conj

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {M : IntegralLattice W}

/-- Conjugation by an isometry `e : L → M` identifies the isometry groups `O(L)` and `O(M)`: a
self-isometry `f` of `L` goes to `e ∘ f ∘ e⁻¹`. -/
def conj (e : Isometry L M) : Isometry L L ≃* Isometry M M where
  toFun f := (e.symm.trans f).trans e
  invFun g := (e.trans g).trans e.symm
  left_inv f := by ext; simp
  right_inv g := by ext; simp
  map_mul' f g := by ext; simp

@[simp]
theorem conj_apply (e : Isometry L M) (f : Isometry L L) (y : W) :
    conj e f y = e (f (e.symm y)) := by
  simp [conj]

@[simp]
theorem conj_symm_apply (e : Isometry L M) (g : Isometry M M) (x : V) :
    (conj e).symm g x = e.symm (g (e x)) := by
  simp [conj]

/-- Conjugation by an isometry preserves the determinant. -/
@[simp]
theorem det_conj (e : Isometry L M) (f : Isometry L L) : det M (conj e f) = det L f := by
  have h : (conj e f).carrierEquiv =
      (e.carrierEquiv.symm.trans f.carrierEquiv).trans e.carrierEquiv := by
    ext
    simp
  rw [det_apply, det_apply, h, LinearEquiv.det_conj]

end Conj

end Isometry

/-- The special isometry group `SO(L)`: the subgroup of the isometry group `O(L) = Isometry L L`
of self-isometries of determinant one. -/
noncomputable def specialOrthogonalGroup (L : IntegralLattice V) : Subgroup (Isometry L L) :=
  (Isometry.det L).ker

@[simp]
theorem mem_specialOrthogonalGroup_iff {e : Isometry L L} :
    e ∈ specialOrthogonalGroup L ↔ Isometry.det L e = 1 :=
  MonoidHom.mem_ker

/-- `SO(L)` has index at most two in `O(L)`, the determinant taking values in `ℤˣ = {±1}`. -/
theorem index_specialOrthogonalGroup_le_two (L : IntegralLattice V) :
    (specialOrthogonalGroup L).index ≤ 2 := by
  rw [specialOrthogonalGroup, Subgroup.index_ker]
  calc Nat.card (Isometry.det L).range ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _
        Subtype.val_injective
    _ = 2 := Nat.card_eq_fintype_card.trans Fintype.card_units_int

/-- The determinant-one subgroup has finite index, even when the isometry group is infinite. -/
instance (L : IntegralLattice V) : (specialOrthogonalGroup L).FiniteIndex :=
  Subgroup.finiteIndex_ker (Isometry.det L)

/-- The index of the special orthogonal group is one or two. -/
theorem index_specialOrthogonalGroup_eq_one_or_two (L : IntegralLattice V) :
    (specialOrthogonalGroup L).index = 1 ∨ (specialOrthogonalGroup L).index = 2 := by
  have h := index_specialOrthogonalGroup_le_two L
  have h₀ := (inferInstance : (specialOrthogonalGroup L).FiniteIndex).index_ne_zero
  omega

/-- The special orthogonal group has index two exactly when an improper isometry exists. -/
theorem index_specialOrthogonalGroup_eq_two_iff (L : IntegralLattice V) :
    (specialOrthogonalGroup L).index = 2 ↔ ∃ e : Isometry L L, Isometry.det L e = -1 := by
  constructor
  · intro h
    by_contra! hn
    have ht : specialOrthogonalGroup L = ⊤ := by
      apply top_unique
      intro e _
      exact mem_specialOrthogonalGroup_iff.mpr
        ((Isometry.det_eq_one_or_neg_one e).resolve_right (hn e))
    have h₁ := (Subgroup.index_eq_one.mpr ht)
    omega
  · rintro ⟨e, he⟩
    rcases index_specialOrthogonalGroup_eq_one_or_two L with h | h
    · have hm : e ∈ specialOrthogonalGroup L := by
        rw [Subgroup.index_eq_one.mp h]
        trivial
      have : (1 : ℤˣ) = -1 := (mem_specialOrthogonalGroup_iff.mp hm).symm.trans he
      have := congrArg Units.val this
      norm_num at this
    · exact h

/-- Negation lies in `SO(L)` exactly when the rank of `L` is even. -/
theorem neg_mem_specialOrthogonalGroup_iff (L : IntegralLattice V) :
    Isometry.neg L ∈ specialOrthogonalGroup L ↔ Even (Module.finrank ℤ L) := by
  rw [mem_specialOrthogonalGroup_iff, Isometry.det_neg, neg_one_pow_eq_one_iff_even]
  exact fun h ↦ by simpa using congrArg Units.val h

section Conj

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {M : IntegralLattice W}

/-- Isometric lattices have isometry groups of the same cardinality. -/
theorem Isometry.natCard_eq (e : Isometry L M) :
    Nat.card (Isometry L L) = Nat.card (Isometry M M) :=
  Nat.card_congr (Isometry.conj e).toEquiv

/-- Conjugation by an isometry `e : L → M` carries `SO(L)` onto `SO(M)`. -/
theorem map_conj_specialOrthogonalGroup (e : Isometry L M) :
    (specialOrthogonalGroup L).map (Isometry.conj e).toMonoidHom = specialOrthogonalGroup M := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_specialOrthogonalGroup_iff, mem_specialOrthogonalGroup_iff,
    ← Isometry.det_conj e, MulEquiv.apply_symm_apply]

/-- Isometric lattices have special isometry groups of the same cardinality. -/
theorem Isometry.natCard_specialOrthogonalGroup_eq (e : Isometry L M) :
    Nat.card (specialOrthogonalGroup L) = Nat.card (specialOrthogonalGroup M) := by
  rw [← map_conj_specialOrthogonalGroup e,
    Subgroup.card_map_of_injective (Isometry.conj e).injective]

end Conj

namespace specialOrthogonalGroup

/-- Restriction of a proper isometry to the carrier, as a group homomorphism from `SO(L)` to the
special linear group of the carrier. -/
def toSpecialLinearGroup (L : IntegralLattice V) :
    specialOrthogonalGroup L →* _root_.SpecialLinearGroup ℤ L where
  toFun g := ⟨(g : Isometry L L).carrierEquiv,
    (Isometry.det_apply _).symm.trans (mem_specialOrthogonalGroup_iff.mp g.prop)⟩
  map_one' := Subtype.ext (by simpa using map_one (Isometry.carrierEquivHom L))
  map_mul' g h :=
    Subtype.ext (by simpa using map_mul (Isometry.carrierEquivHom L) (g : Isometry L L) h)

@[simp]
theorem coe_toSpecialLinearGroup_apply (g : specialOrthogonalGroup L) :
    (toSpecialLinearGroup L g : L ≃ₗ[ℤ] L) = (g : Isometry L L).carrierEquiv := (rfl)

/-- A proper isometry is determined by its restriction to the carrier. -/
theorem toSpecialLinearGroup_injective (L : IntegralLattice V) :
    Function.Injective (toSpecialLinearGroup L) := fun _ _ h ↦
  Subtype.ext (Isometry.carrierEquiv_injective (congrArg Subtype.val h))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix of a proper isometry in a finite carrier basis `b`, as a group homomorphism from
`SO(L)` to `Matrix.SpecialLinearGroup ι ℤ`. -/
noncomputable def toMatrix (b : Module.Basis ι ℤ L) :
    specialOrthogonalGroup L →* Matrix.SpecialLinearGroup ι ℤ :=
  (Matrix.SpecialLinearGroup.toLin_equiv b).symm.toMonoidHom.comp (toSpecialLinearGroup L)

@[simp]
theorem coe_toMatrix_apply (b : Module.Basis ι ℤ L) (g : specialOrthogonalGroup L) :
    ((toMatrix b g : Matrix.SpecialLinearGroup ι ℤ) : Matrix ι ι ℤ) =
      LinearMap.toMatrix b b ((g : Isometry L L).carrierEquiv : L →ₗ[ℤ] L) :=
  Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq b _

/-- A proper isometry is determined by its matrix in a finite carrier basis. -/
theorem toMatrix_injective (b : Module.Basis ι ℤ L) : Function.Injective (toMatrix b) :=
  (Matrix.SpecialLinearGroup.toLin_equiv b).symm.injective.comp (toSpecialLinearGroup_injective L)

end specialOrthogonalGroup

namespace Isometry

open LinearMap (BilinForm)
open TauCeti.BilinForm
open scoped Pointwise

/-! ### Rational isometries preserving the carrier -/

/-- A self-isometry of a lattice, as an element of the isometry group of its rational form. -/
noncomputable def toIsometryGroup (L : IntegralLattice V) :
    Isometry L L →* isometryGroup L.form where
  toFun g := (isometryGroupEquivIsometryEquiv L.form).symm g.toIsometryEquiv
  map_one' := Subtype.ext (LinearEquiv.ext fun x ↦ by simp)
  map_mul' g h := Subtype.ext (LinearEquiv.ext fun x ↦ by simp)

@[simp]
theorem toIsometryGroup_apply (g : Isometry L L) (x : V) :
    (toIsometryGroup L g : V ≃ₗ[ℚ] V) x = g x := by
  simp [toIsometryGroup]

theorem toIsometryGroup_injective (L : IntegralLattice V) :
    Function.Injective (toIsometryGroup L) := fun g h hgh ↦
  Isometry.ext fun x ↦ by simpa using LinearEquiv.congr_fun (congrArg Subtype.val hgh) x

/-- A rational isometry of `L` which, together with its inverse, maps the carrier into itself is an
isometry of `L`. -/
noncomputable def ofIsometryGroup (G : isometryGroup L.form)
    (h : ∀ x ∈ L.carrier, (G : V ≃ₗ[ℚ] V) x ∈ L.carrier)
    (h' : ∀ x ∈ L.carrier, (G : V ≃ₗ[ℚ] V).symm x ∈ L.carrier) : Isometry L L where
  toIsometryEquiv := isometryGroupEquivIsometryEquiv L.form G
  map_carrier := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      simpa using h x hx
    · intro x hx
      exact ⟨_, h' x hx, by simp⟩

@[simp]
theorem ofIsometryGroup_apply (G : isometryGroup L.form) (h h') (x : V) :
    ofIsometryGroup G h h' x = (G : V ≃ₗ[ℚ] V) x := by
  simp [ofIsometryGroup, ← Isometry.coe_toIsometryEquiv]

@[simp]
theorem toIsometryGroup_ofIsometryGroup (G : isometryGroup L.form) (h h') :
    toIsometryGroup L (ofIsometryGroup G h h') = G :=
  Subtype.ext (LinearEquiv.ext fun x ↦ by simp)

@[simp]
theorem ofIsometryGroup_toIsometryGroup (g : Isometry L L) (h h') :
    ofIsometryGroup (toIsometryGroup L g) h h' = g :=
  Isometry.ext fun x ↦ by simp

/-- A rational isometry of `L` comes from a self-isometry of `L` exactly when it preserves
membership in the carrier. -/
theorem mem_range_toIsometryGroup_iff {G : isometryGroup L.form} :
    G ∈ (toIsometryGroup L).range ↔ ∀ x, (G : V ≃ₗ[ℚ] V) x ∈ L.carrier ↔ x ∈ L.carrier := by
  refine ⟨?_, fun h ↦ ⟨ofIsometryGroup G (fun x hx ↦ (h x).mpr hx) fun x hx ↦ (h _).mp ?_,
    toIsometryGroup_ofIsometryGroup G _ _⟩⟩
  · rintro ⟨g, rfl⟩ x
    simp
  · rwa [LinearEquiv.apply_symm_apply]

/-- A subgroup of rational isometries of `L` each mapping the carrier into itself consists of
self-isometries of `L`. -/
theorem le_range_toIsometryGroup {H : Subgroup (isometryGroup L.form)}
    (hH : ∀ G ∈ H, ∀ x ∈ L.carrier, (G : V ≃ₗ[ℚ] V) x ∈ L.carrier) :
    H ≤ (toIsometryGroup L).range := fun G hG ↦
  mem_range_toIsometryGroup_iff.mpr fun x ↦ ⟨fun hx ↦ by
    simpa using hH _ (inv_mem hG) _ hx, hH G hG x⟩

/-! ### Congruence subgroups -/

/-- The action of a self-isometry of `L` on the quotient `L / d L` of its carrier. -/
noncomputable def reductionHom (L : IntegralLattice V) (d : ℤ) :
    Isometry L L →* Module.End ℤ (QuotSMulTop d L) where
  toFun g := QuotSMulTop.map d (g.carrierEquiv : L →ₗ[ℤ] L)
  map_one' := by
    rw [one_def, carrierEquiv_refl]
    exact QuotSMulTop.map_id d L
  map_mul' g h := by
    rw [mul_def, carrierEquiv_trans, LinearEquiv.coe_trans, QuotSMulTop.map_comp,
      Module.End.mul_eq_comp]

@[simp]
theorem reductionHom_apply_mk (d : ℤ) (g : Isometry L L) (x : L) :
    reductionHom L d g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g.carrierEquiv x) :=
  QuotSMulTop.map_apply_mk ..

/-- The principal congruence subgroup of level `d`: the self-isometries of `L` acting trivially
on `L / d L`. -/
noncomputable def congruenceSubgroup (L : IntegralLattice V) (d : ℤ) : Subgroup (Isometry L L) :=
  (reductionHom L d).ker

/-- An isometry lies in the congruence subgroup of level `d` exactly when it moves every lattice
vector by `d` times a lattice vector. -/
theorem mem_congruenceSubgroup_iff {d : ℤ} {g : Isometry L L} :
    g ∈ congruenceSubgroup L d ↔ ∀ x : L, ∃ y : L, g.carrierEquiv x - x = d • y := by
  rw [congruenceSubgroup, MonoidHom.mem_ker]
  refine ⟨fun hg x ↦ ?_, fun hg ↦ Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)⟩
  · have h := LinearMap.congr_fun hg (Submodule.Quotient.mk x)
    rw [Module.End.one_apply, reductionHom_apply_mk, Submodule.Quotient.eq,
      Submodule.mem_smul_pointwise_iff_exists] at h
    obtain ⟨y, -, hy⟩ := h
    exact ⟨y, hy.symm⟩
  · obtain ⟨y, hy⟩ := hg x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Module.End.one_apply,
      reductionHom_apply_mk, Submodule.Quotient.eq, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨y, Submodule.mem_top, hy.symm⟩

/-- The congruence subgroups of levels `-d` and `d` coincide. -/
@[simp]
theorem congruenceSubgroup_neg (L : IntegralLattice V) (d : ℤ) :
    congruenceSubgroup L (-d) = congruenceSubgroup L d := by
  ext g
  simp only [mem_congruenceSubgroup_iff]
  exact forall_congr' fun x ↦ ⟨fun ⟨y, hy⟩ ↦ ⟨-y, by rw [hy, neg_smul, smul_neg]⟩,
    fun ⟨y, hy⟩ ↦ ⟨-y, by rw [hy, neg_smul_neg]⟩⟩

/-- For a positive level `d`, the congruence subgroup of level `d` has finite index in `O(L)`. -/
instance (L : IntegralLattice V) (d : ℕ) [NeZero d] : (congruenceSubgroup L d).FiniteIndex := by
  have : Finite (Module.End ℤ (QuotSMulTop (d : ℤ) L)) :=
    Finite.of_injective _ DFunLike.coe_injective
  rw [congruenceSubgroup, ← MonoidHom.ker_toHomUnits]
  infer_instance

/-- For `d ≠ 0`, the congruence subgroup of level `d` has finite index in `O(L)`. -/
theorem finiteIndex_congruenceSubgroup (L : IntegralLattice V) {d : ℤ} (hd : d ≠ 0) :
    (congruenceSubgroup L d).FiniteIndex := by
  have : NeZero d.natAbs := ⟨Int.natAbs_ne_zero.mpr hd⟩
  rcases Int.natAbs_eq d with h | h <;> rw [h]
  · infer_instance
  · rw [congruenceSubgroup_neg]
    infer_instance

end Isometry

end IntegralLattice

end TauCeti
