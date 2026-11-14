/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DieudonneDeterminant

/-!
# Determinant splittings and computations of algebraic `K₁`

This file constructs the canonical determinant homomorphisms out of `TauCeti.AlgebraicK1`,
establishes the determinant-scalar splitting over commutative rings, and computes `K₁` explicitly
for the integers, arbitrary division rings, and fields.

For any ring `A`, embedding `1 × 1` scalar matrices gives a group homomorphism
`TauCeti.AlgebraicK1.unitsHom : Aˣ →* AlgebraicK1 A`.

* **Commutative rings.** Stabilization preserves `Matrix.GeneralLinearGroup.det`, so the universal
  property of `AlgebraicK1` produces `TauCeti.AlgebraicK1.det : AlgebraicK1 A →* Aˣ` satisfying
  `det (unitsHom A u) = u`. Its kernel is the **special algebraic `K₁`** subgroup
  `TauCeti.specialAlgebraicK1 A : Subgroup (AlgebraicK1 A)`, and the section `unitsHom A` yields a
  canonical direct-product decomposition
  `TauCeti.AlgebraicK1.unitsProdSpecialEquiv : AlgebraicK1 A ≃* Aˣ × specialAlgebraicK1 A`.
  Whenever `ker det ≤ elementarySubgroup (Fin n) A` in every size `n`, `specialAlgebraicK1 A = ⊥`
  and `det` is an isomorphism `AlgebraicK1 A ≃* Aˣ`
  (`TauCeti.AlgebraicK1.detEquivOfKerDetLeElementary`).
* **The integers.** Since `elementarySubgroup (Fin n) ℤ = ker det` (Euclidean row reduction in
  `SL n ℤ`), `specialAlgebraicK1 ℤ = ⊥` and `TauCeti.AlgebraicK1.intDetEquiv : AlgebraicK1 ℤ ≃* ℤˣ`
  is an isomorphism sending `unitsHom ℤ (-1)` to `-1 ≠ 1`.
* **Division rings and fields.** Stabilization preserves `Matrix.GeneralLinearGroup.dieudonneDet`,
  inducing an isomorphism
  `TauCeti.AlgebraicK1.dieudonneDetEquiv : AlgebraicK1 D ≃* Group.Abelianization Dˣ`
  with inverse lifted from `unitsHom D`. Over a field `F`, `specialAlgebraicK1 F = ⊥` and
  `TauCeti.AlgebraicK1.fieldDetEquiv : AlgebraicK1 F ≃* Fˣ` agrees with `det`.

## Main definitions

* `TauCeti.AlgebraicK1.unitsHom`: the canonical map `Aˣ →* AlgebraicK1 A` sending `u` to the class
  of the `1 × 1` scalar matrix `[u]`.
* `TauCeti.AlgebraicK1.det`: the determinant `AlgebraicK1 A →* Aˣ` over a commutative ring `A`.
* `TauCeti.specialAlgebraicK1`: the subgroup `SK₁(A) = ker (AlgebraicK1.det)` of `AlgebraicK1 A`,
  together with `TauCeti.specialAlgebraicK1.projection` and `TauCeti.specialAlgebraicK1.map`.
* `TauCeti.AlgebraicK1.unitsProdSpecialEquiv`: the canonical decomposition
  `AlgebraicK1 A ≃* Aˣ × specialAlgebraicK1 A`.
* `TauCeti.AlgebraicK1.detEquivOfKerDetLeElementary`: the isomorphism `AlgebraicK1 A ≃* Aˣ` when
  every special linear matrix is elementary.
* `TauCeti.AlgebraicK1.intDetEquiv`: the determinant isomorphism `AlgebraicK1 ℤ ≃* ℤˣ`.
* `TauCeti.AlgebraicK1.dieudonneDet` and `TauCeti.AlgebraicK1.dieudonneDetEquiv`: the Dieudonné
  determinant isomorphism `AlgebraicK1 D ≃* Group.Abelianization Dˣ` over a division ring `D`.
* `TauCeti.AlgebraicK1.fieldDetEquiv`: the determinant isomorphism `AlgebraicK1 F ≃* Fˣ` over a
  field `F`.

## Main results

* `TauCeti.AlgebraicK1.det_unitsHom`: `unitsHom A` is a section of `AlgebraicK1.det`.
* `TauCeti.specialAlgebraicK1.int_eq_bot` and `TauCeti.AlgebraicK1.unitsHom_int_neg_one_ne_one`:
  `SK₁(ℤ) = ⊥` and `unitsHom ℤ (-1) ≠ 1` in `AlgebraicK1 ℤ`.
* `TauCeti.AlgebraicK1.unitsHom_surjective_of_divisionRing`: over a division ring `D`,
  `unitsHom D : Dˣ →* AlgebraicK1 D` is surjective.
* `TauCeti.specialAlgebraicK1.eq_bot_of_field` and `TauCeti.AlgebraicK1.dieudonneDet_eq_of_det`:
  `SK₁(F) = ⊥` over a field `F`, and the Dieudonné determinant on `AlgebraicK1 F` agrees with
  `Group.Abelianization.of ∘ AlgebraicK1.det`.

## References

* H. Bass, *Algebraic K-Theory*, W. A. Benjamin (1968), Chapter V, §1 and §9.
* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §3.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), §2.1–§2.2.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, GSM 145 (2013), Chapter III,
  §1.2–§1.4.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

/-! ## Scalar units in algebraic `K₁` -/

section Ring

variable {A : Type*} [Ring A]

/-- Stabilizing the `1 × 1` scalar matrix `[u]` to size `n ≥ 1` places `u` in the `(0, 0)` entry
and `1` along the remaining diagonal entries. -/
theorem stabilizeGL_scalar_one_eq_diagGL_mulSingle {n : ℕ} (hn : 1 ≤ n) (u : Aˣ) :
    stabilizeGL A hn (Matrix.GeneralLinearGroup.scalar (Fin 1) u) =
      diagGL (Pi.mulSingle ⟨0, hn⟩ u) := by
  ext i j
  rw [coe_stabilizeGL_apply, diagGL_apply]
  split_ifs with hlt hij hij
  · rw [← diagGL_const]
    change (diagGL fun _ : Fin 1 ↦ u) ⟨i, hlt.1⟩ ⟨j, hlt.2⟩ = _
    rw [diagGL_apply]
    have hi0 : i = ⟨0, hn⟩ := by
      ext
      simp only
      omega
    subst hij
    simp [hi0]
  · exfalso
    exact hij (Fin.ext (by omega))
  · subst hij
    have hi0 : i ≠ ⟨0, hn⟩ := by
      intro h
      exact hlt ⟨by simp [h], by simp [h]⟩
    simp [hi0]
  · simp [hij]

namespace AlgebraicK1

/-- Elementary matrices vanish in algebraic `K₁`. -/
@[simp]
theorem mk_eq_one_of_mem_elementarySubgroup {n : ℕ} {u : GL (Fin n) A}
    (hu : u ∈ TauCeti.elementarySubgroup (Fin n) A) : mk A n u = 1 :=
  mk_eq_one_iff.2 ⟨n, le_rfl, by simpa using hu⟩

variable (A) in
/-- The canonical homomorphism `Aˣ →* AlgebraicK1 A` sending a unit `u` to the class of the
`1 × 1` scalar matrix `[u]`. -/
def unitsHom : Aˣ →* AlgebraicK1 A :=
  (mk A 1).comp (Matrix.GeneralLinearGroup.scalar (Fin 1))

/-- Evaluating `unitsHom A` on `u` gives the `K₁`-class of `scalar (Fin 1) u`. -/
theorem unitsHom_apply (u : Aˣ) :
    unitsHom A u = mk A 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) u) :=
  (rfl)

/-- A single-coordinate diagonal matrix at index `0` represents `unitsHom A u` in
`AlgebraicK1 A`. -/
theorem mk_diagGL_mulSingle_zero {n : ℕ} (hn : 1 ≤ n) (u : Aˣ) :
    mk A n (diagGL (Pi.mulSingle ⟨0, hn⟩ u)) = unitsHom A u := by
  rw [← stabilizeGL_scalar_one_eq_diagGL_mulSingle hn u, mk_stabilizeGL, unitsHom_apply]

/-- `unitsHom` is natural with respect to ring homomorphisms. -/
@[simp]
theorem map_unitsHom {B : Type*} [Ring B] (f : A →+* B) (u : Aˣ) :
    map f (unitsHom A u) = unitsHom B (Units.map f.toMonoidHom u) := by
  simp only [unitsHom, MonoidHom.comp_apply, map_mk, ← diagGL_const]
  congr 1
  ext i j
  change f ((diagGL fun _ : Fin 1 ↦ u) i j) =
    (diagGL fun _ : Fin 1 ↦ Units.map f.toMonoidHom u) i j
  rw [diagGL_apply, diagGL_apply]
  fin_cases i
  fin_cases j
  simp

end AlgebraicK1

end Ring

/-! ## Determinant and `SK₁` over a commutative ring -/

section CommRing

variable {A : Type*} [CommRing A]

/-- Stabilization preserves the classical determinant of an invertible matrix. -/
@[simp]
theorem det_stabilizeGL {m n : ℕ} (h : m ≤ n) (u : GL (Fin m) A) :
    Matrix.GeneralLinearGroup.det (stabilizeGL A h u) = Matrix.GeneralLinearGroup.det u := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  ext
  rw [stabilizeGL_eq_reindexGL_fromBlocksGL]
  simp [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

namespace AlgebraicK1

/-- **The determinant on algebraic `K₁`** of a commutative ring `A`, induced via `AlgebraicK1.lift`
by `Matrix.GeneralLinearGroup.det` on each `GL (Fin n) A`. -/
def det : AlgebraicK1 A →* Aˣ :=
  lift (fun _ ↦ Matrix.GeneralLinearGroup.det) fun _ _ h u ↦ det_stabilizeGL h u

/-- On the class of an invertible matrix, `AlgebraicK1.det` agrees with
`Matrix.GeneralLinearGroup.det`. -/
@[simp]
theorem det_mk (n : ℕ) (u : GL (Fin n) A) :
    det (mk A n u) = Matrix.GeneralLinearGroup.det u :=
  lift_mk ..

/-- `unitsHom A` is a section of `AlgebraicK1.det`. -/
@[simp]
theorem det_unitsHom (u : Aˣ) : det (unitsHom A u) = u := by
  ext
  simp [unitsHom, ← diagGL_const]

/-- `AlgebraicK1.det` is surjective for every commutative ring. -/
theorem det_surjective : Function.Surjective (det (A := A)) :=
  fun u ↦ ⟨unitsHom A u, det_unitsHom u⟩

/-- `AlgebraicK1.det` is natural with respect to homomorphisms of commutative rings. -/
@[simp]
theorem det_map {B : Type*} [CommRing B] (f : A →+* B) (x : AlgebraicK1 A) :
    det (map f x) = Units.map f.toMonoidHom (det x) := by
  obtain ⟨n, u, rfl⟩ := exists_mk x
  ext
  simp [RingHom.map_det]

end AlgebraicK1

variable (A) in
/-- **Special algebraic `K₁`** (`SK₁(A)`) of a commutative ring `A`: the kernel of
`AlgebraicK1.det : AlgebraicK1 A →* Aˣ`. -/
def specialAlgebraicK1 : Subgroup (AlgebraicK1 A) :=
  (AlgebraicK1.det (A := A)).ker

/-- A class in `AlgebraicK1 A` belongs to `specialAlgebraicK1 A` precisely when its determinant is
`1`. -/
@[simp]
theorem mem_specialAlgebraicK1_iff {x : AlgebraicK1 A} :
    x ∈ specialAlgebraicK1 A ↔ AlgebraicK1.det x = 1 :=
  MonoidHom.mem_ker

namespace specialAlgebraicK1

variable (A) in
/-- The retraction `AlgebraicK1 A →* specialAlgebraicK1 A` onto `SK₁(A)` along `unitsHom A`,
sending `x` to `x * (unitsHom A (det x))⁻¹`. -/
def projection : AlgebraicK1 A →* specialAlgebraicK1 A :=
  (MonoidHom.id _ / (AlgebraicK1.unitsHom A).comp AlgebraicK1.det).codRestrict _
    fun x ↦ by simp

/-- The underlying `K₁`-class of `projection A x` is `x * (unitsHom A (det x))⁻¹`. -/
theorem coe_projection_apply (x : AlgebraicK1 A) :
    (projection A x : AlgebraicK1 A) = x * (AlgebraicK1.unitsHom A (AlgebraicK1.det x))⁻¹ := by
  simp [projection, div_eq_mul_inv]

/-- `projection A` is the identity on `specialAlgebraicK1 A`. -/
@[simp]
theorem projection_coe (x : specialAlgebraicK1 A) : projection A x = x := by
  ext
  simp [coe_projection_apply, mem_specialAlgebraicK1_iff.1 x.2]

/-- `projection A` kills scalar unit classes. -/
@[simp]
theorem projection_unitsHom (u : Aˣ) : projection A (AlgebraicK1.unitsHom A u) = 1 := by
  ext
  simp [coe_projection_apply]

/-- Every element of `AlgebraicK1 A` factors as its scalar determinant part times its `SK₁`
projection. -/
theorem unitsHom_det_mul_coe_projection (x : AlgebraicK1 A) :
    AlgebraicK1.unitsHom A (AlgebraicK1.det x) * (projection A x : AlgebraicK1 A) = x := by
  rw [coe_projection_apply, mul_comm, inv_mul_cancel_right]

/-- The homomorphism `SK₁(A) →* SK₁(B)` induced by a homomorphism of commutative rings. -/
def map {B : Type*} [CommRing B] (f : A →+* B) : specialAlgebraicK1 A →* specialAlgebraicK1 B :=
  ((AlgebraicK1.map f).comp (specialAlgebraicK1 A).subtype).codRestrict (specialAlgebraicK1 B)
    fun x ↦ by simp [mem_specialAlgebraicK1_iff.1 x.2]

/-- `specialAlgebraicK1.map` acts as `AlgebraicK1.map` on underlying classes. -/
@[simp]
theorem coe_map_apply {B : Type*} [CommRing B] (f : A →+* B) (x : specialAlgebraicK1 A) :
    (map f x : AlgebraicK1 B) = AlgebraicK1.map f x :=
  (rfl)

/-- `specialAlgebraicK1.projection` commutes with ring homomorphisms. -/
theorem map_projection {B : Type*} [CommRing B] (f : A →+* B) (x : AlgebraicK1 A) :
    map f (projection A x) = projection B (AlgebraicK1.map f x) := by
  ext
  simp [coe_projection_apply]

/-- `specialAlgebraicK1.map` sends the identity ring homomorphism to the identity. -/
@[simp]
theorem map_id : map (RingHom.id A) = MonoidHom.id (specialAlgebraicK1 A) := by
  ext x
  simp

/-- `specialAlgebraicK1.map` respects composition of ring homomorphisms. -/
theorem map_comp {B C : Type*} [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    map (g.comp f) = (map g).comp (map f) := by
  ext x
  simp

/-- If every matrix of determinant `1` in `GL (Fin n) A` is elementary for all `n`, then
`specialAlgebraicK1 A` is trivial. -/
theorem eq_bot_of_ker_det_le_elementarySubgroup
    (h : ∀ n : ℕ,
      (Matrix.GeneralLinearGroup.det (n := Fin n) (R := A)).ker ≤
        TauCeti.elementarySubgroup (Fin n) A) :
    specialAlgebraicK1 A = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨n, u, rfl⟩ := AlgebraicK1.exists_mk x
  rw [mem_specialAlgebraicK1_iff, AlgebraicK1.det_mk, ← MonoidHom.mem_ker] at hx
  exact Subgroup.mem_bot.2 (AlgebraicK1.mk_eq_one_of_mem_elementarySubgroup (h n hx))

end specialAlgebraicK1

namespace AlgebraicK1

variable (A) in
/-- **Determinant splitting of `AlgebraicK1`:** over any commutative ring `A`, `K₁(A)` decomposes
canonically as `Aˣ × SK₁(A)` via `x ↦ (det x, specialAlgebraicK1.projection A x)`. -/
def unitsProdSpecialEquiv : AlgebraicK1 A ≃* Aˣ × specialAlgebraicK1 A where
  toFun x := (det x, specialAlgebraicK1.projection A x)
  invFun p := unitsHom A p.1 * (p.2 : AlgebraicK1 A)
  left_inv := specialAlgebraicK1.unitsHom_det_mul_coe_projection
  right_inv := fun ⟨u, s⟩ ↦ Prod.ext (by simp [mem_specialAlgebraicK1_iff.1 s.2]) (by simp)
  map_mul' x y := Prod.ext (map_mul _ _ _) (map_mul _ _ _)

/-- First and second components of `unitsProdSpecialEquiv`. -/
@[simp]
theorem unitsProdSpecialEquiv_apply (x : AlgebraicK1 A) :
    unitsProdSpecialEquiv A x = (det x, specialAlgebraicK1.projection A x) :=
  (rfl)

/-- The inverse of `unitsProdSpecialEquiv` multiplies `unitsHom A u` by the `SK₁` element. -/
@[simp]
theorem unitsProdSpecialEquiv_symm_apply (p : Aˣ × specialAlgebraicK1 A) :
    (unitsProdSpecialEquiv A).symm p = unitsHom A p.1 * (p.2 : AlgebraicK1 A) :=
  (rfl)

/-- When every matrix of determinant `1` over `A` is elementary, `AlgebraicK1.det` is an
isomorphism `AlgebraicK1 A ≃* Aˣ` with inverse `unitsHom A`. -/
def detEquivOfKerDetLeElementary
    (h : ∀ n : ℕ,
      (Matrix.GeneralLinearGroup.det (n := Fin n) (R := A)).ker ≤
        TauCeti.elementarySubgroup (Fin n) A) :
    AlgebraicK1 A ≃* Aˣ where
  toFun := det
  invFun := unitsHom A
  left_inv x := by
    have hs : specialAlgebraicK1.projection A x = 1 := by
      have hmem : (specialAlgebraicK1.projection A x : AlgebraicK1 A) ∈
          (⊥ : Subgroup (AlgebraicK1 A)) :=
        specialAlgebraicK1.eq_bot_of_ker_det_le_elementarySubgroup h ▸
          (specialAlgebraicK1.projection A x).2
      ext
      exact Subgroup.mem_bot.1 hmem
    simpa [hs] using specialAlgebraicK1.unitsHom_det_mul_coe_projection x
  right_inv := det_unitsHom
  map_mul' := det.map_mul'

/-- Evaluating `detEquivOfKerDetLeElementary` gives `AlgebraicK1.det`. -/
@[simp]
theorem detEquivOfKerDetLeElementary_apply
    (h : ∀ n : ℕ,
      (Matrix.GeneralLinearGroup.det (n := Fin n) (R := A)).ker ≤
        TauCeti.elementarySubgroup (Fin n) A)
    (x : AlgebraicK1 A) :
    detEquivOfKerDetLeElementary h x = det x :=
  (rfl)

/-- The inverse of `detEquivOfKerDetLeElementary` is `unitsHom A`. -/
@[simp]
theorem detEquivOfKerDetLeElementary_symm_apply
    (h : ∀ n : ℕ,
      (Matrix.GeneralLinearGroup.det (n := Fin n) (R := A)).ker ≤
        TauCeti.elementarySubgroup (Fin n) A)
    (u : Aˣ) :
    (detEquivOfKerDetLeElementary h).symm u = unitsHom A u :=
  (rfl)

end AlgebraicK1

end CommRing

/-! ## Computation of `K₁(ℤ)` -/

/-- Over `ℤ`, special algebraic `K₁` is trivial: every integer matrix of determinant `1` is a
product of elementary transvections. -/
theorem specialAlgebraicK1.int_eq_bot : specialAlgebraicK1 ℤ = ⊥ :=
  specialAlgebraicK1.eq_bot_of_ker_det_le_elementarySubgroup
    fun n ↦ (elementarySubgroup_int_eq_ker_det (n := Fin n)).symm.le

namespace AlgebraicK1

/-- **Computation of `K₁(ℤ)`:** the determinant induces an isomorphism `AlgebraicK1 ℤ ≃* ℤˣ`. -/
def intDetEquiv : AlgebraicK1 ℤ ≃* ℤˣ :=
  detEquivOfKerDetLeElementary fun n ↦ (elementarySubgroup_int_eq_ker_det (n := Fin n)).symm.le

/-- `intDetEquiv` evaluates as `AlgebraicK1.det`. -/
@[simp]
theorem intDetEquiv_apply (x : AlgebraicK1 ℤ) : intDetEquiv x = det x :=
  (rfl)

/-- The inverse of `intDetEquiv` is `unitsHom ℤ`. -/
@[simp]
theorem intDetEquiv_symm_apply (u : ℤˣ) : intDetEquiv.symm u = unitsHom ℤ u :=
  (rfl)

/-- The `1 × 1` matrix `[-1]` represents a nontrivial element of `AlgebraicK1 ℤ`. -/
theorem unitsHom_int_neg_one_ne_one : unitsHom ℤ (-1 : ℤˣ) ≠ 1 := by
  intro h
  have hval : (-1 : ℤ) = 1 := by
    simpa using congrArg (fun x ↦ (det x : ℤ)) h
  omega

end AlgebraicK1

/-! ## Computation of `K₁(D)` over a division ring and `K₁(F)` over a field -/

section DivisionRing

variable {D : Type*} [DivisionRing D]

namespace AlgebraicK1

/-- **The Dieudonné determinant on algebraic `K₁`** of a division ring `D`, induced via
`AlgebraicK1.lift` by `Matrix.GeneralLinearGroup.dieudonneDet` on each `GL (Fin n) D`. -/
def dieudonneDet : AlgebraicK1 D →* Group.Abelianization Dˣ :=
  lift (fun _ ↦ Matrix.GeneralLinearGroup.dieudonneDet)
    fun _ _ h u ↦ Matrix.GeneralLinearGroup.dieudonneDet_stabilizeGL h u

/-- On the class of an invertible matrix, `AlgebraicK1.dieudonneDet` agrees with
`Matrix.GeneralLinearGroup.dieudonneDet`. -/
@[simp]
theorem dieudonneDet_mk (n : ℕ) (u : GL (Fin n) D) :
    dieudonneDet (mk D n u) = Matrix.GeneralLinearGroup.dieudonneDet u :=
  lift_mk ..

/-- On a scalar unit class `unitsHom D d`, the Dieudonné determinant is
`Group.Abelianization.of d`. -/
@[simp]
theorem dieudonneDet_unitsHom (d : Dˣ) :
    dieudonneDet (unitsHom D d) = Group.Abelianization.of d := by
  simp [unitsHom]

/-- Over a division ring `D`, every class in `AlgebraicK1 D` comes from a `1 × 1` unit via
`unitsHom D`. -/
theorem unitsHom_surjective_of_divisionRing : Function.Surjective (unitsHom D) := by
  intro x
  obtain ⟨n, g, rfl⟩ := exists_mk x
  have hn : 1 ≤ n + 2 := by omega
  rw [← mk_stabilizeGL (Nat.le_add_right n 2)]
  obtain ⟨e, he, d, hg⟩ :=
    exists_mem_elementarySubgroup_mul_diagGL_mulSingle
      (stabilizeGL D (Nat.le_add_right n 2) g) ⟨0, hn⟩
  refine ⟨d, ?_⟩
  rw [hg, map_mul, mk_eq_one_of_mem_elementarySubgroup he, one_mul,
    mk_diagGL_mulSingle_zero hn d]

variable (D) in
/-- **Computation of `K₁(D)` over a division ring:** the Dieudonné determinant is a canonical
group isomorphism `AlgebraicK1 D ≃* Group.Abelianization Dˣ` whose inverse lifts `unitsHom D`. -/
def dieudonneDetEquiv : AlgebraicK1 D ≃* Group.Abelianization Dˣ where
  toFun := dieudonneDet
  invFun := Group.Abelianization.lift (unitsHom D)
  left_inv x := by
    obtain ⟨d, rfl⟩ := unitsHom_surjective_of_divisionRing x
    simp
  right_inv y := by
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective _ y
    change dieudonneDet (Group.Abelianization.lift (unitsHom D) (Group.Abelianization.of d)) =
      Group.Abelianization.of d
    simp
  map_mul' := dieudonneDet.map_mul'

/-- `dieudonneDetEquiv D` evaluates as `AlgebraicK1.dieudonneDet`. -/
@[simp]
theorem dieudonneDetEquiv_apply (x : AlgebraicK1 D) :
    dieudonneDetEquiv D x = dieudonneDet x :=
  (rfl)

/-- The inverse of `dieudonneDetEquiv D` sends `Group.Abelianization.of d` to `unitsHom D d`. -/
@[simp]
theorem dieudonneDetEquiv_symm_of (d : Dˣ) :
    (dieudonneDetEquiv D).symm (Group.Abelianization.of d) = unitsHom D d := by
  simp [dieudonneDetEquiv]

/-- Naturality of `AlgebraicK1.dieudonneDet` with respect to homomorphisms of division rings. -/
theorem dieudonneDet_map {E : Type*} [DivisionRing E] (f : D →+* E) (x : AlgebraicK1 D) :
    dieudonneDet (map f x) =
      Group.Abelianization.map (Units.map f.toMonoidHom) (dieudonneDet x) := by
  obtain ⟨n, u, rfl⟩ := exists_mk x
  rw [map_mk, dieudonneDet_mk, dieudonneDet_mk, Matrix.GeneralLinearGroup.dieudonneDet_mapMatrix]

end AlgebraicK1

end DivisionRing

section Field

variable (F : Type*) [Field F]

/-- Over a field `F`, special algebraic `K₁` is trivial. -/
theorem specialAlgebraicK1.eq_bot_of_field : specialAlgebraicK1 F = ⊥ :=
  specialAlgebraicK1.eq_bot_of_ker_det_le_elementarySubgroup
    fun n ↦ (elementarySubgroup_eq_ker_det_of_field (n := Fin n)).symm.le

namespace AlgebraicK1

/-- **Computation of `K₁(F)` over a field:** the determinant is an isomorphism
`AlgebraicK1 F ≃* Fˣ` with inverse `unitsHom F`. -/
def fieldDetEquiv : AlgebraicK1 F ≃* Fˣ :=
  detEquivOfKerDetLeElementary fun n ↦ (elementarySubgroup_eq_ker_det_of_field (n := Fin n)).symm.le

/-- `fieldDetEquiv F` evaluates as `AlgebraicK1.det`. -/
@[simp]
theorem fieldDetEquiv_apply (x : AlgebraicK1 F) : fieldDetEquiv F x = det x :=
  (rfl)

/-- The inverse of `fieldDetEquiv F` is `unitsHom F`. -/
@[simp]
theorem fieldDetEquiv_symm_apply (u : Fˣ) : (fieldDetEquiv F).symm u = unitsHom F u :=
  (rfl)

variable {F} in
/-- Over a field `F`, the Dieudonné determinant on `AlgebraicK1 F` agrees with `AlgebraicK1.det`
followed by `Group.Abelianization.of`. -/
@[simp]
theorem dieudonneDet_eq_of_det (x : AlgebraicK1 F) :
    dieudonneDet x = Group.Abelianization.of (det x) := by
  obtain ⟨n, u, rfl⟩ := exists_mk x
  simp

/-- Over a field `F`, composing `dieudonneDetEquiv F` with `Group.Abelianization.equivOfComm.symm`
recovers `fieldDetEquiv F`. -/
theorem dieudonneDetEquiv_trans_equivOfComm_symm :
    (dieudonneDetEquiv F).trans Group.Abelianization.equivOfComm.symm = fieldDetEquiv F := by
  ext x
  simp

end AlgebraicK1

end Field

end TauCeti
