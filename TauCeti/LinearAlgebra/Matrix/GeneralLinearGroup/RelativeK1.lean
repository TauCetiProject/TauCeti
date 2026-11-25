/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Unitization
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitization

/-!
# Relative algebraic `K₁` of a nonunital algebra

Let `A` be a possibly nonunital algebra over a commutative ring `R`, and `A⁺ = Unitization R A`
its forced unitization, used even when `A` already has a unit. The augmentation
`A⁺ → R`, `(r, a) ↦ r`, induces a homomorphism `K₁(A⁺) → K₁(R)`, and the **relative `K₁`** of `A`
is its kernel. This is the `K₁`-group of a nonunital algebra; for a unital `A` it is computed with
the forced unitization all the same. The scalar inclusion `R → A⁺` splits the augmentation, so
every class of `A⁺` is the product of its relative part and the class of a scalar matrix.

Invertible matrices over `A⁺` whose scalar part is the identity, that is matrices `1 + a` with
entries of `a` in `A`, have relative classes, and every relative class is of this form. A
homomorphism of nonunital algebras induces a homomorphism of relative `K₁` through the induced map
of forced unitizations, which preserves the augmentation.

The matrices `1 + a` do not involve the scalar ring (`TauCeti.unitizationGLFstOneEquiv`). Hence,
for an algebra `R → S` and an `S`-algebra `A`, the change of scalars `Unitization.mapScalars`,
`(r, a) ↦ (algebraMap R S r, a)`, induces a surjection from the relative `K₁` of `A` over `R`
onto that over `S`; for `ℤ → ℂ` it compares the relative `K₁` of a nonunital complex algebra on
its integral and complex unitizations. No injectivity is claimed: relative `K₁` can depend on the
ambient ring (Swan's example, in the remark of Weibel cited below). When `A` is unital, the map
`Unitization R A → A`, `(r, a) ↦ r • 1 + a`, identifies the relative `K₁` of `A` with `K₁(A)`.

Relative `K₁` is the group paired with the relative cyclic cohomology of `A` by Connes' odd pairing
(`TauCeti.relativeAlgebraicK1.oddPairing`).

## Main definitions

* `TauCeti.relativeAlgebraicK1`: the kernel of `K₁(A⁺) → K₁(R)`.
* `TauCeti.relativeAlgebraicK1.projection`: the projection of `K₁(A⁺)` onto relative `K₁` along
  the classes of scalar matrices.
* `TauCeti.relativeAlgebraicK1.map`: the homomorphism induced by a homomorphism of nonunital
  algebras.
* `TauCeti.relativeAlgebraicK1.mapScalars`: change of the scalar ring along an algebra `R → S`.
* `TauCeti.relativeAlgebraicK1.equivAlgebraicK1`: for a unital algebra `A`, the isomorphism of
  its relative `K₁` with `K₁(A)`.

## Main results

* `TauCeti.AlgebraicK1.mk_mem_relativeAlgebraicK1`: an invertible matrix over `A⁺` with identity
  scalar part has a relative class.
* `TauCeti.relativeAlgebraicK1.projection_coe`,
  `TauCeti.relativeAlgebraicK1.projection_map_algebraMap`: the projection is the identity on
  relative classes and kills the classes of scalar matrices.
* `TauCeti.relativeAlgebraicK1.coe_projection_mul_map_algebraMap`: every class of `A⁺` is its
  relative part times the class of a scalar matrix.
* `TauCeti.relativeAlgebraicK1.map_projection`: the projection is natural.
* `TauCeti.relativeAlgebraicK1.map_id`, `TauCeti.relativeAlgebraicK1.map_comp`: functoriality.
* `TauCeti.relativeAlgebraicK1.exists_mk_eq`: every relative class is the class of a matrix with
  identity scalar part.
* `TauCeti.relativeAlgebraicK1.mapScalars_surjective`, `TauCeti.relativeAlgebraicK1.mapScalars_map`:
  change of scalars is surjective and natural.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), Chapters 1 and 2, for
  `K`-groups of nonunital rings through their unitization.
* A. Connes, *Noncommutative Geometry*, Chapter III, §3, for the `K`-theory of a nonunital algebra
  as a kernel on its unitization in the pairing with cyclic cohomology.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Remark 2.2.1, for relative `K₁` as a quotient of the
  matrices congruent to `1`, its dependence on the ambient ring (Swan's example), and Chapter II,
  Exercises 2.3 and 2.4, for the groups of a unital ring regarded as a nonunital one.
-/

public section

noncomputable section

namespace TauCeti

variable (R A : Type*) [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

/-- The **relative algebraic `K₁`** of a possibly nonunital algebra `A`: the kernel of the
homomorphism `K₁(A⁺) → K₁(R)` induced by the augmentation of the forced unitization
`A⁺ = Unitization R A`. -/
def relativeAlgebraicK1 : Subgroup (AlgebraicK1 (Unitization R A)) :=
  (AlgebraicK1.map (Unitization.fstHom R A : Unitization R A →+* R)).ker

variable {R A}

/-- A class of `A⁺` is relative exactly when the augmentation sends it to the trivial class. -/
@[simp]
theorem mem_relativeAlgebraicK1_iff {x : AlgebraicK1 (Unitization R A)} :
    x ∈ relativeAlgebraicK1 R A ↔
      AlgebraicK1.map (Unitization.fstHom R A : Unitization R A →+* R) x = 1 :=
  MonoidHom.mem_ker

/-- An invertible matrix over `A⁺` whose scalar part is the identity matrix has a relative
class. -/
theorem AlgebraicK1.mk_mem_relativeAlgebraicK1 {n : ℕ} {u : GL (Fin n) (Unitization R A)}
    (hu : (Unitization.fstHom R A : Unitization R A →+* R).mapMatrix
      (u : Matrix (Fin n) (Fin n) (Unitization R A)) = 1) :
    AlgebraicK1.mk (Unitization R A) n u ∈ relativeAlgebraicK1 R A := by
  rw [mem_relativeAlgebraicK1_iff, AlgebraicK1.map_mk]
  convert map_one (AlgebraicK1.mk R n)
  exact Units.ext hu

/-- The augmentation is a left inverse of the scalar inclusion on algebraic `K₁`. -/
theorem AlgebraicK1.map_fstHom_map_algebraMap (x : AlgebraicK1 R) :
    AlgebraicK1.map (Unitization.fstHom R A : Unitization R A →+* R)
      (AlgebraicK1.map (algebraMap R (Unitization R A)) x) = x := by
  rw [AlgebraicK1.map_map]
  convert DFunLike.congr_fun AlgebraicK1.map_id x
  ext r
  simp

namespace relativeAlgebraicK1

variable (R A) in
/-- The projection of `K₁(A⁺)` onto relative `K₁` along the classes of scalar matrices,
`x ↦ x · s(ε(x))⁻¹`, where `ε` is induced by the augmentation and `s` by the scalar inclusion. -/
def projection : AlgebraicK1 (Unitization R A) →* relativeAlgebraicK1 R A :=
  (MonoidHom.id _ / (AlgebraicK1.map (algebraMap R (Unitization R A))).comp
    (AlgebraicK1.map (Unitization.fstHom R A : Unitization R A →+* R))).codRestrict _
    fun x ↦ by simp [← RingHom.comp_assoc]

/-- The relative part of a class `x` of `A⁺` is `x · s(ε(x))⁻¹`. -/
theorem coe_projection_apply (x : AlgebraicK1 (Unitization R A)) :
    (projection R A x : AlgebraicK1 (Unitization R A)) =
      x * (AlgebraicK1.map (algebraMap R (Unitization R A))
        (AlgebraicK1.map (Unitization.fstHom R A : Unitization R A →+* R) x))⁻¹ := by
  simp [projection, div_eq_mul_inv]

/-- The projection is the identity on relative classes. -/
@[simp]
theorem projection_coe (x : relativeAlgebraicK1 R A) : projection R A x = x := by
  ext
  simp [coe_projection_apply, (mem_relativeAlgebraicK1_iff.1 x.property)]

/-- The projection kills the classes of scalar matrices. -/
@[simp]
theorem projection_map_algebraMap (y : AlgebraicK1 R) :
    projection R A (AlgebraicK1.map (algebraMap R (Unitization R A)) y) = 1 := by
  ext
  simp [coe_projection_apply]

/-- Every class of `A⁺` is the product of its relative part and the class of a scalar matrix,
the image of `x` under the map induced by `s ∘ ε`. -/
@[simp]
theorem coe_projection_mul_map_algebraMap (x : AlgebraicK1 (Unitization R A)) :
    (projection R A x : AlgebraicK1 (Unitization R A)) *
        AlgebraicK1.map ((algebraMap R (Unitization R A)).comp
          (Unitization.fstHom R A : Unitization R A →+* R)) x = x := by
  rw [← AlgebraicK1.map_map, coe_projection_apply, inv_mul_cancel_right]

/-- Every relative class is the class of an invertible matrix over `A⁺` whose scalar part is the
identity matrix. -/
theorem exists_mk_eq {x : AlgebraicK1 (Unitization R A)} (hx : x ∈ relativeAlgebraicK1 R A) :
    ∃ n, ∃ u ∈ unitizationGLFstOne R A (Fin n), AlgebraicK1.mk (Unitization R A) n u = x := by
  obtain ⟨n, u, rfl⟩ := AlgebraicK1.exists_mk x
  set s := Units.map ((Unitization.fstHom R A : Unitization R A →+* R).mapMatrix
    (m := Fin n)).toMonoidHom u
  set t := Units.map ((algebraMap R (Unitization R A)).mapMatrix (m := Fin n)).toMonoidHom s
  have hs : AlgebraicK1.mk R n s = 1 := by
    rw [← AlgebraicK1.map_mk]
    exact mem_relativeAlgebraicK1_iff.1 hx
  refine ⟨n, u * t⁻¹, ?_, ?_⟩
  · rw [unitizationGLFstOne_def, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
    ext i j
    simp [s, t]
  · rw [map_mul, map_inv, ← AlgebraicK1.map_mk, hs]
    simp

section Map

variable {B C : Type*} [NonUnitalRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]

/-- The homomorphism of relative `K₁` induced by a homomorphism of nonunital algebras, through the
induced map of forced unitizations. -/
def map (f : A →ₙₐ[R] B) : relativeAlgebraicK1 R A →* relativeAlgebraicK1 R B :=
  ((AlgebraicK1.map (Unitization.map f : Unitization R A →+* Unitization R B)).comp
    (relativeAlgebraicK1 R A).subtype).codRestrict _ fun x ↦ by
      rw [mem_relativeAlgebraicK1_iff, MonoidHom.comp_apply, AlgebraicK1.map_map,
        ← AlgHom.comp_toRingHom, Unitization.fstHom_comp_map]
      exact mem_relativeAlgebraicK1_iff.1 x.property

/-- The induced homomorphism of relative `K₁` is the induced homomorphism of `K₁(A⁺)`. -/
@[simp]
theorem coe_map_apply (f : A →ₙₐ[R] B) (x : relativeAlgebraicK1 R A) :
    (map f x : AlgebraicK1 (Unitization R B)) =
      AlgebraicK1.map (Unitization.map f : Unitization R A →+* Unitization R B) x :=
  (rfl)

/-- The projection onto relative `K₁` is natural for homomorphisms of nonunital algebras. -/
theorem map_projection (f : A →ₙₐ[R] B) (x : AlgebraicK1 (Unitization R A)) :
    map f (projection R A x) =
      projection R B
        (AlgebraicK1.map (Unitization.map f : Unitization R A →+* Unitization R B) x) := by
  ext
  simp only [coe_map_apply, coe_projection_apply, map_mul, map_inv]
  congr 2
  simp only [AlgebraicK1.map_map, ← AlgHom.comp_toRingHom, Unitization.fstHom_comp_map]
  rw [← RingHom.comp_assoc, AlgHom.comp_algebraMap]

/-- The identity homomorphism induces the identity of relative `K₁`. -/
@[simp]
theorem map_id : map (NonUnitalAlgHom.id R A) = MonoidHom.id (relativeAlgebraicK1 R A) := by
  ext x
  simp [Unitization.map_id]

/-- Relative `K₁` is functorial. -/
theorem map_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    map (g.comp f) = (map g).comp (map f) := by
  ext x
  simp only [coe_map_apply, MonoidHom.comp_apply, Unitization.map_comp, AlgHom.comp_toRingHom,
    AlgebraicK1.map_comp]

end Map

section ChangeOfScalars

variable {S : Type*} [CommRing S] [Algebra R S] [Module S A] [IsScalarTower S A A]
  [SMulCommClass S A A] [IsScalarTower R S A]

variable (S) in
/-- Change of the scalar ring of relative `K₁`: for an algebra `R → S` and an `S`-algebra `A`,
the homomorphism `K₁(A⁺_R) → K₁(A⁺_S)` induced by the change of scalars of forced unitizations
`Unitization.mapScalars`, `(r, a) ↦ (algebraMap R S r, a)`, restricted to relative classes.
This map is surjective (`relativeAlgebraicK1.mapScalars_surjective`); no injectivity is
claimed. -/
def mapScalars : relativeAlgebraicK1 R A →* relativeAlgebraicK1 S A :=
  ((AlgebraicK1.map (Unitization.mapScalars R S A : Unitization R A →+* Unitization S A)).comp
      (relativeAlgebraicK1 R A).subtype).codRestrict _
    fun x ↦ by
      simp [← AlgebraicK1.map_map _ (algebraMap R S), mem_relativeAlgebraicK1_iff.1 x.property]

/-- The change of scalars of relative `K₁` is the homomorphism of `K₁` induced by the map of
forced unitizations. -/
@[simp]
theorem coe_mapScalars_apply (x : relativeAlgebraicK1 R A) :
    (mapScalars S x : AlgebraicK1 (Unitization S A)) =
      AlgebraicK1.map (Unitization.mapScalars R S A : Unitization R A →+* Unitization S A) x :=
  (rfl)

/-- For an algebra `R → S` and an `S`-algebra `A`, every relative class over `Unitization S A`
comes from one over `Unitization R A`: the change of scalars of relative `K₁` is surjective. -/
theorem mapScalars_surjective :
    Function.Surjective (mapScalars S : relativeAlgebraicK1 R A →* relativeAlgebraicK1 S A) := by
  rintro ⟨x, hx⟩
  obtain ⟨n, u, hu, rfl⟩ := exists_mk_eq hx
  set v := (unitizationGLFstOneEquiv R A (Fin n)).symm
    (unitizationGLFstOneEquiv S A (Fin n) ⟨u, hu⟩)
  refine ⟨⟨_, AlgebraicK1.mk_mem_relativeAlgebraicK1 (mem_unitizationGLFstOne_iff.1 v.property)⟩,
    Subtype.ext ?_⟩
  rw [coe_mapScalars_apply, AlgebraicK1.map_mk, units_map_unitizationGLFstOneEquiv_symm,
    MulEquiv.symm_apply_apply]

/-- The change of scalars of relative `K₁` is natural for homomorphisms of nonunital
`S`-algebras. -/
theorem mapScalars_map {B : Type*} [NonUnitalRing B] [Module S B] [IsScalarTower S B B]
    [SMulCommClass S B B] [Module R B] [IsScalarTower R S B] [IsScalarTower R B B]
    [SMulCommClass R B B] (f : A →ₙₐ[S] B) (x : relativeAlgebraicK1 R A) :
    mapScalars S (map (f.restrictScalars R) x) = map f (mapScalars S x) := by
  have h : (Unitization.mapScalars R S B : Unitization R B →+* Unitization S B).comp
        (Unitization.map (f.restrictScalars R) : Unitization R A →+* Unitization R B) =
      (Unitization.map f : Unitization S A →+* Unitization S B).comp
        (Unitization.mapScalars R S A : Unitization R A →+* Unitization S A) :=
    RingHom.ext (Unitization.mapScalars_map f)
  apply Subtype.ext
  simp only [coe_mapScalars_apply, coe_map_apply, AlgebraicK1.map_map, h]

end ChangeOfScalars

section Unital

variable {B : Type*} [Ring B] [Algebra R B]

/-- The inverse of `unitizationGLFstOneEquivGL`, `u ↦ 1 + (u - 1)`, commutes with
stabilization. -/
private theorem coe_unitizationGLFstOneEquivGL_symm_stabilizeGL {m n : ℕ} (h : m ≤ n)
    (u : GL (Fin m) B) :
    ((unitizationGLFstOneEquivGL R B (Fin n)).symm (stabilizeGL B h u) :
        GL (Fin n) (Unitization R B)) =
      stabilizeGL (Unitization R B) h ((unitizationGLFstOneEquivGL R B (Fin m)).symm u) := by
  ext i j : 2
  simp only [coe_unitizationGLFstOneEquivGL_symm_apply, coe_stabilizeGL_apply, Matrix.add_apply,
    Matrix.map_apply, Matrix.sub_apply]
  split_ifs with hij <;> simp [Matrix.one_apply, Fin.ext_iff]

variable (R B) in
/-- The inverse of `relativeAlgebraicK1.equivAlgebraicK1`, `[u] ↦ [1 + (u - 1)]`. -/
private def ofAlgebraicK1 : AlgebraicK1 B →* relativeAlgebraicK1 R B :=
  (AlgebraicK1.lift (fun n ↦ (AlgebraicK1.mk (Unitization R B) n).comp
      ((unitizationGLFstOne R B (Fin n)).subtype.comp
        (unitizationGLFstOneEquivGL R B (Fin n)).symm.toMonoidHom))
    fun m n h u ↦ by
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom]
      rw [coe_unitizationGLFstOneEquivGL_symm_stabilizeGL,
        AlgebraicK1.mk_stabilizeGL]).codRestrict _
    fun x ↦ by
      obtain ⟨n, u, rfl⟩ := AlgebraicK1.exists_mk x
      simp only [AlgebraicK1.lift_mk]
      exact AlgebraicK1.mk_mem_relativeAlgebraicK1
        (mem_unitizationGLFstOne_iff.1 (SetLike.coe_mem _))

private theorem coe_ofAlgebraicK1_mk (n : ℕ) (u : GL (Fin n) B) :
    (ofAlgebraicK1 R B (AlgebraicK1.mk B n u) : AlgebraicK1 (Unitization R B)) =
      AlgebraicK1.mk (Unitization R B) n ((unitizationGLFstOneEquivGL R B (Fin n)).symm u) := by
  simp [ofAlgebraicK1]

variable (R B) in
/-- **Relative `K₁` of a unital algebra is its `K₁`.** For a unital `R`-algebra `B`, the
homomorphism induced by `Unitization R B → B`, `(r, b) ↦ r • 1 + b`, restricts to an
isomorphism from the relative `K₁` of `B`, computed on its forced unitization, onto `K₁(B)`. The
inverse sends the class of `u` to the class of `1 + (u - 1)`. -/
def equivAlgebraicK1 : relativeAlgebraicK1 R B ≃* AlgebraicK1 B :=
  MonoidHom.toMulEquiv
    ((AlgebraicK1.map (Unitization.lift (NonUnitalAlgHom.id R B) : Unitization R B →+* B)).comp
      (relativeAlgebraicK1 R B).subtype)
    (ofAlgebraicK1 R B)
    (by
      ext ⟨x, hx⟩
      obtain ⟨n, u, hu, rfl⟩ := exists_mk_eq hx
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, AlgebraicK1.map_mk,
        MonoidHom.id_apply]
      rw [← unitizationGLFstOneEquivGL_apply (u := ⟨u, hu⟩), coe_ofAlgebraicK1_mk,
        MulEquiv.symm_apply_apply])
    (by
      ext n u
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, coe_ofAlgebraicK1_mk,
        AlgebraicK1.map_mk, MonoidHom.id_apply]
      rw [← unitizationGLFstOneEquivGL_apply, MulEquiv.apply_symm_apply])

/-- `relativeAlgebraicK1.equivAlgebraicK1` is induced by `Unitization R B → B`,
`(r, b) ↦ r • 1 + b`. -/
@[simp]
theorem equivAlgebraicK1_apply (x : relativeAlgebraicK1 R B) :
    equivAlgebraicK1 R B x =
      AlgebraicK1.map (Unitization.lift (NonUnitalAlgHom.id R B) : Unitization R B →+* B) x :=
  (rfl)

/-- The inverse of `relativeAlgebraicK1.equivAlgebraicK1` sends the class of `u` to the class of
`1 + (u - 1)`. -/
@[simp]
theorem coe_equivAlgebraicK1_symm_mk (n : ℕ) (u : GL (Fin n) B) :
    ((equivAlgebraicK1 R B).symm (AlgebraicK1.mk B n u) : AlgebraicK1 (Unitization R B)) =
      AlgebraicK1.mk (Unitization R B) n ((unitizationGLFstOneEquivGL R B (Fin n)).symm u) :=
  coe_ofAlgebraicK1_mk n u

end Unital

end relativeAlgebraicK1

end TauCeti
