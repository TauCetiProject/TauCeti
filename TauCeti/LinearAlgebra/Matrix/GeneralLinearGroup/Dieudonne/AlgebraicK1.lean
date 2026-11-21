/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Dieudonne.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DeterminantK1

/-!
# Algebraic `K₁` of division rings

Because `Matrix.GeneralLinearGroup.dieudonneDet` is invariant under stabilization `u ↦ u ⊕ 1`
(`Matrix.GeneralLinearGroup.dieudonneDet_stabilizeGL`), the universal property of algebraic `K₁`
descends it to a canonical group isomorphism
`TauCeti.AlgebraicK1.dieudonneDetEquiv : AlgebraicK1 D ≃* Group.Abelianization Dˣ` for every
division ring `D`, whose inverse sends `Group.Abelianization.of u` to
`TauCeti.AlgebraicK1.ofUnits D u`. In particular, in rank `2 ≤ n` an invertible matrix over `D`
represents `1` in `K₁(D)` if and only if it already lies in `TauCeti.elementarySubgroup (Fin n) D`
(`TauCeti.AlgebraicK1.mk_eq_one_iff_mem_elementarySubgroup`).

Over a commutative field `F`, `dieudonneDetEquiv F` agrees with `TauCeti.AlgebraicK1.det F` and
`TauCeti.AlgebraicK1.detEquiv (specialAlgebraicK1_eq_bot_of_euclideanDomain F)` (from
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DeterminantK1`) via
`Group.Abelianization.equivOfComm`.

## Main definitions

* `TauCeti.AlgebraicK1.dieudonneDetEquiv`: the canonical isomorphism
  `TauCeti.AlgebraicK1 D ≃* Group.Abelianization Dˣ` for a division ring `D`.

## Main results

* `Matrix.GeneralLinearGroup.dieudonneDet_stabilizeGL`: stabilization preserves the Dieudonné
  determinant.
* `TauCeti.AlgebraicK1.dieudonneDetEquiv_ofUnits`, `TauCeti.AlgebraicK1.dieudonneDetEquiv_symm_of`:
  compatibility of `dieudonneDetEquiv` with `TauCeti.AlgebraicK1.ofUnits`.
* `TauCeti.AlgebraicK1.dieudonneDetEquiv_map`: naturality with respect to ring homomorphisms of
  division rings.
* `TauCeti.AlgebraicK1.mk_eq_one_iff_mem_elementarySubgroup`: over a division ring and for `2 ≤ n`,
  a matrix in `GL (Fin n) D` represents `1` in `K₁(D)` if and only if it already lies in `Eₙ(D)`.
* `TauCeti.AlgebraicK1.dieudonneDetEquiv_eq_abelianizationOf_det`,
  `TauCeti.AlgebraicK1.dieudonneDetEquiv_trans_equivOfComm_symm`: over a field `F`,
  `dieudonneDetEquiv F` agrees with `TauCeti.AlgebraicK1.det F` and
  `TauCeti.AlgebraicK1.detEquiv`.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), §2.2, Theorem 2.2.5 and
  Corollary 2.2.6.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, GSM 145 (2013), Chapter III,
  1.2.4 and Example 1.3.5.
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
`Group.Abelianization.of u` to `ofUnits D u`. -/
def dieudonneDetEquiv (D : Type*) [DivisionRing D] :
    AlgebraicK1 D ≃* Group.Abelianization Dˣ :=
  MonoidHom.toMulEquiv
    (lift (fun _ ↦ GeneralLinearGroup.dieudonneDet)
      fun _ _ h u ↦ GeneralLinearGroup.dieudonneDet_stabilizeGL h u)
    (Group.Abelianization.lift (ofUnits D))
    (MonoidHom.ext fun x ↦ by
      obtain ⟨n, u, rfl⟩ := exists_mk x
      rcases n with _ | m
      · simp [Subsingleton.elim u 1]
      · obtain ⟨e, he, d, rfl⟩ :=
          exists_mem_elementarySubgroup_mul_diagGL_mulSingle (Fin.last m) u
        have he1 : mk D (m + 1) e = 1 :=
          mk_eq_one_iff.2 ⟨m + 1, le_rfl, by simpa using he⟩
        simp [he1, ofUnits_apply])
    (Group.Abelianization.hom_ext _ _ (MonoidHom.ext fun u ↦ by
      simp [ofUnits_apply]))

/-- `dieudonneDetEquiv` evaluates on the class of `u ∈ GL (Fin n) D` as `u.dieudonneDet`. -/
@[simp]
theorem dieudonneDetEquiv_mk {D : Type*} [DivisionRing D] (n : ℕ) (u : GL (Fin n) D) :
    dieudonneDetEquiv D (mk D n u) = GeneralLinearGroup.dieudonneDet u :=
  lift_mk ..

/-- `dieudonneDetEquiv` sends the `1 × 1` class `ofUnits D u` to `Group.Abelianization.of u`. -/
@[simp]
theorem dieudonneDetEquiv_ofUnits {D : Type*} [DivisionRing D] (u : Dˣ) :
    dieudonneDetEquiv D (ofUnits D u) = Group.Abelianization.of u := by
  simp [ofUnits_apply]

/-- The inverse of `dieudonneDetEquiv` sends `Group.Abelianization.of u` to `ofUnits D u`. -/
@[simp]
theorem dieudonneDetEquiv_symm_of {D : Type*} [DivisionRing D] (u : Dˣ) :
    (dieudonneDetEquiv D).symm (Group.Abelianization.of u) = ofUnits D u :=
  Group.Abelianization.lift_apply_of (ofUnits D) u

/-- Naturality of `dieudonneDetEquiv` with respect to ring homomorphisms of division rings. -/
@[simp]
theorem dieudonneDetEquiv_map {D E : Type*} [DivisionRing D] [DivisionRing E] (f : D →+* E)
    (x : AlgebraicK1 D) :
    dieudonneDetEquiv E (map f x) =
      Group.Abelianization.map (Units.map (f : D →* E)) (dieudonneDetEquiv D x) := by
  obtain ⟨n, u, rfl⟩ := exists_mk x
  simp [RingHom.toMonoidHom_eq_coe]

/-- Over a division ring and in rank `2 ≤ n`, an invertible matrix represents `1` in
`AlgebraicK1 D` if and only if it already lies in `TauCeti.elementarySubgroup (Fin n) D`. -/
theorem mk_eq_one_iff_mem_elementarySubgroup {D : Type*} [DivisionRing D] {n : ℕ} (hn : 2 ≤ n)
    {u : GL (Fin n) D} :
    mk D n u = 1 ↔ u ∈ TauCeti.elementarySubgroup (Fin n) D := by
  rw [← (dieudonneDetEquiv D).map_eq_one_iff, dieudonneDetEquiv_mk,
    GeneralLinearGroup.dieudonneDet_eq_one_iff (by simpa using hn)]

/-- Over a field `F`, `dieudonneDetEquiv F` agrees with `Group.Abelianization.of` composed with
`TauCeti.AlgebraicK1.det F`. -/
theorem dieudonneDetEquiv_eq_abelianizationOf_det {F : Type*} [Field F] (x : AlgebraicK1 F) :
    dieudonneDetEquiv F x = Group.Abelianization.of (det F x) := by
  obtain ⟨n, u, rfl⟩ := exists_mk x
  simp [GeneralLinearGroup.dieudonneDet_eq_abelianizationOf_det]

/-- Over a field `F`, composing `dieudonneDetEquiv F` with the abelianization equivalence recovers
`TauCeti.AlgebraicK1.detEquiv`. -/
theorem dieudonneDetEquiv_trans_equivOfComm_symm (F : Type*) [Field F] :
    (dieudonneDetEquiv F).trans Group.Abelianization.equivOfComm.symm =
      detEquiv (specialAlgebraicK1_eq_bot_of_euclideanDomain F) := by
  ext x
  simp [dieudonneDetEquiv_eq_abelianizationOf_det]

end TauCeti.AlgebraicK1

end
