/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Dieudonne.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# Algebraic `K₁` of division rings and fields

Because `Matrix.GeneralLinearGroup.dieudonneDet` is invariant under stabilization `u ↦ u ⊕ 1`
(`Matrix.GeneralLinearGroup.dieudonneDet_stabilizeGL`), the universal property of algebraic `K₁`
descends it to a canonical group isomorphism
`TauCeti.AlgebraicK1.dieudonneDetEquiv : AlgebraicK1 D ≃* Group.Abelianization Dˣ` for every
division ring `D`, whose inverse sends `Group.Abelianization.of u` to the `1 × 1` scalar class
`mk D 1 (GeneralLinearGroup.scalar (Fin 1) u)`. In particular, in rank `2 ≤ n` an invertible matrix
over `D` represents `1` in `K₁(D)` if and only if it already lies in
`TauCeti.elementarySubgroup (Fin n) D` (`TauCeti.AlgebraicK1.mk_eq_one_iff_mem_elementarySubgroup`).

Specializing to a commutative field `F`, where `Group.Abelianization Fˣ ≃* Fˣ` and `dieudonneDet`
agrees with the polynomial determinant, yields the canonical isomorphism
`TauCeti.AlgebraicK1.detEquiv : AlgebraicK1 F ≃* Fˣ`.

## Main definitions

* `TauCeti.AlgebraicK1.dieudonneDetEquiv`: the canonical isomorphism
  `TauCeti.AlgebraicK1 D ≃* Group.Abelianization Dˣ` for a division ring `D`.
* `TauCeti.AlgebraicK1.detEquiv`: the canonical isomorphism `TauCeti.AlgebraicK1 F ≃* Fˣ` for a
  field `F`.

## Main results

* `Matrix.GeneralLinearGroup.dieudonneDet_stabilizeGL`: stabilization preserves the Dieudonné
  determinant.
* `TauCeti.AlgebraicK1.dieudonneDetEquiv_map`, `TauCeti.AlgebraicK1.detEquiv_map`: naturality with
  respect to ring homomorphisms of division rings and fields.
* `TauCeti.AlgebraicK1.mk_eq_one_iff_mem_elementarySubgroup`: over a division ring and for `2 ≤ n`,
  a matrix in `GL (Fin n) D` represents `1` in `K₁(D)` if and only if it already lies in `Eₙ(D)`.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), §2.2, Theorem 2.2.5 and
  Corollary 2.2.6.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, GSM 145 (2013), Chapter III,
  §1.2.4 and Example 1.3.5.
-/

public section

noncomputable section

open Matrix

namespace Matrix.GeneralLinearGroup

/-- Stabilization `u ↦ u ⊕ 1` preserves the Dieudonné determinant. -/
@[simp]
theorem dieudonneDet_stabilizeGL {D : Type*} [DivisionRing D] {a b : ℕ} (h : a ≤ b)
    (u : GL (Fin a) D) :
    dieudonneDet (TauCeti.stabilizeGL D h u) = dieudonneDet u := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Subsingleton.elim h (Nat.le_add_right a k), TauCeti.stabilizeGL_eq_reindexGL_fromBlocksGL,
    dieudonneDet_reindexGL, dieudonneDet_fromBlocksGL, map_one, mul_one]

end Matrix.GeneralLinearGroup

namespace TauCeti.AlgebraicK1

/-- **Algebraic `K₁` of a division ring.** The Dieudonné determinant induces a canonical
isomorphism `AlgebraicK1 D ≃* Group.Abelianization Dˣ`, with inverse sending
`Group.Abelianization.of u` to the `1 × 1` class `mk D 1 (GeneralLinearGroup.scalar (Fin 1) u)`. -/
def dieudonneDetEquiv (D : Type*) [DivisionRing D] :
    AlgebraicK1 D ≃* Group.Abelianization Dˣ where
  toFun := lift (fun _ ↦ GeneralLinearGroup.dieudonneDet)
    fun _ _ h u ↦ GeneralLinearGroup.dieudonneDet_stabilizeGL h u
  invFun := Group.Abelianization.lift ((mk D 1).comp (GeneralLinearGroup.scalar (Fin 1)))
  left_inv := by
    have hcomp :
        (Group.Abelianization.lift ((mk D 1).comp (GeneralLinearGroup.scalar (Fin 1)))).comp
          (lift (fun _ ↦ GeneralLinearGroup.dieudonneDet)
            fun _ _ h u ↦ GeneralLinearGroup.dieudonneDet_stabilizeGL h u) =
          MonoidHom.id (AlgebraicK1 D) := by
      refine hom_ext fun n ↦ MonoidHom.ext fun u ↦ ?_
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, lift_mk]
      rcases n with _ | m
      · rw [Subsingleton.elim u 1, map_one, map_one, map_one]
      · obtain ⟨e, he, d, rfl⟩ :=
          exists_mem_elementarySubgroup_mul_diagGL_mulSingle (Fin.last m) u
        have he1 : mk D (m + 1) e = 1 :=
          mk_eq_one_iff.2 ⟨m + 1, le_rfl, by simpa using he⟩
        rw [map_mul, GeneralLinearGroup.dieudonneDet_of_mem_elementarySubgroup he, one_mul,
          GeneralLinearGroup.dieudonneDet_diagGL_mulSingle, Group.Abelianization.lift_apply_of,
          MonoidHom.comp_apply, map_mul, he1, one_mul, mk_diagGL_mulSingle]
    exact DFunLike.congr_fun hcomp
  right_inv y := QuotientGroup.induction_on y fun u ↦ by
    have hy : (QuotientGroup.mk u : Group.Abelianization Dˣ) = Group.Abelianization.of u := rfl
    rw [hy, Group.Abelianization.lift_apply_of, MonoidHom.comp_apply, lift_mk,
      GeneralLinearGroup.dieudonneDet_scalar, Fintype.card_fin, pow_one]
  map_mul' := map_mul _

/-- `dieudonneDetEquiv` evaluates on the class of `u ∈ GL (Fin n) D` as `u.dieudonneDet`. -/
@[simp]
theorem dieudonneDetEquiv_mk {D : Type*} [DivisionRing D] (n : ℕ) (u : GL (Fin n) D) :
    dieudonneDetEquiv D (mk D n u) = GeneralLinearGroup.dieudonneDet u :=
  lift_mk ..

/-- The inverse of `dieudonneDetEquiv` sends `Group.Abelianization.of u` to
`[scalar (Fin 1) u]`. -/
@[simp]
theorem dieudonneDetEquiv_symm_of {D : Type*} [DivisionRing D] (u : Dˣ) :
    (dieudonneDetEquiv D).symm (Group.Abelianization.of u) =
      mk D 1 (GeneralLinearGroup.scalar (Fin 1) u) :=
  (rfl)

/-- Naturality of `dieudonneDetEquiv` with respect to ring homomorphisms of division rings. -/
@[simp]
theorem dieudonneDetEquiv_map {D E : Type*} [DivisionRing D] [DivisionRing E] (f : D →+* E)
    (x : AlgebraicK1 D) :
    dieudonneDetEquiv E (map f x) =
      Group.Abelianization.map (Units.map (f : D →* E)) (dieudonneDetEquiv D x) := by
  obtain ⟨n, u, rfl⟩ := exists_mk x
  rw [map_mk, dieudonneDetEquiv_mk, dieudonneDetEquiv_mk, RingHom.toMonoidHom_eq_coe,
    GeneralLinearGroup.dieudonneDet_unitsMap_mapMatrix]

/-- Over a division ring and in rank `2 ≤ n`, an invertible matrix represents `1` in
`AlgebraicK1 D` if and only if it already lies in `TauCeti.elementarySubgroup (Fin n) D`. -/
theorem mk_eq_one_iff_mem_elementarySubgroup {D : Type*} [DivisionRing D] {n : ℕ} (hn : 2 ≤ n)
    {u : GL (Fin n) D} :
    mk D n u = 1 ↔ u ∈ TauCeti.elementarySubgroup (Fin n) D := by
  calc
    mk D n u = 1 ↔ dieudonneDetEquiv D (mk D n u) = 1 :=
      ⟨fun h ↦ by rw [h, map_one],
        fun h ↦ (dieudonneDetEquiv D).injective (h.trans (map_one _).symm)⟩
    _ ↔ u ∈ TauCeti.elementarySubgroup (Fin n) D := by
      rw [dieudonneDetEquiv_mk,
        GeneralLinearGroup.dieudonneDet_eq_one_iff (by simpa [Fintype.card_fin] using hn)]

/-- **Algebraic `K₁` of a field.** The ordinary determinant induces a canonical isomorphism
`AlgebraicK1 F ≃* Fˣ`, sending `[u]` to `u.det` and `a : Fˣ` to `[scalar (Fin 1) a]`. -/
def detEquiv (F : Type*) [Field F] : AlgebraicK1 F ≃* Fˣ :=
  (dieudonneDetEquiv F).trans Group.Abelianization.equivOfComm.symm

/-- `detEquiv` evaluates on the class of `u ∈ GL (Fin n) F` as `u.det`. -/
@[simp]
theorem detEquiv_mk {F : Type*} [Field F] (n : ℕ) (u : GL (Fin n) F) :
    detEquiv F (mk F n u) = u.det := by
  simp [detEquiv, GeneralLinearGroup.dieudonneDet_eq_of_det]

/-- The inverse of `detEquiv` sends `a : Fˣ` to `[scalar (Fin 1) a]`. -/
@[simp]
theorem detEquiv_symm_apply {F : Type*} [Field F] (a : Fˣ) :
    (detEquiv F).symm a = mk F 1 (GeneralLinearGroup.scalar (Fin 1) a) := by
  simp [detEquiv]

/-- Naturality of `detEquiv` with respect to ring homomorphisms of fields. -/
@[simp]
theorem detEquiv_map {F K : Type*} [Field F] [Field K] (f : F →+* K) (x : AlgebraicK1 F) :
    detEquiv K (map f x) = Units.map (f : F →* K) (detEquiv F x) := by
  obtain ⟨n, u, rfl⟩ := exists_mk x
  rw [detEquiv, MulEquiv.trans_apply, dieudonneDetEquiv_map, dieudonneDetEquiv_mk,
    GeneralLinearGroup.dieudonneDet_eq_of_det, Group.Abelianization.map_of, detEquiv,
    MulEquiv.trans_apply, dieudonneDetEquiv_mk, GeneralLinearGroup.dieudonneDet_eq_of_det]
  simp

end TauCeti.AlgebraicK1

end
