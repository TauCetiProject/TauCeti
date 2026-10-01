/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleRing.Matrix
import TauCeti.Algebra.CentralSimple.SkolemNoether

/-!
# Inner automorphisms of a matrix algebra

An invertible matrix `g ∈ GL n R` over a commutative ring acts on the matrix algebra
`Matrix n n R` by the algebra automorphism `x ↦ g x g⁻¹`. This file packages that action as a
group homomorphism `GL n R →* (Matrix n n R ≃ₐ[R] Matrix n n R)` and proves:

* its kernel is the center of `GL n R`, the invertible scalar matrices;
* over a field it is surjective: every automorphism of a matrix algebra is inner
  (Skolem–Noether);
* hence it induces an injective homomorphism from Mathlib's projective general linear group
  `PGL(n, R) = GL n R / Z(GL n R)`, which is bijective over a field.

These are the pointwise facts behind the identification of the projective general linear group
scheme with the automorphism group scheme of the matrix algebra.

## Main declarations

* `Matrix.GeneralLinearGroup.innerAut`: conjugation as algebra automorphisms.
* `Matrix.GeneralLinearGroup.ker_innerAut`: its kernel is the center.
* `Matrix.GeneralLinearGroup.innerAut_surjective`: surjectivity over a field.
* `Matrix.ProjGenLinGroup.innerAut`: the induced homomorphism on `PGL(n, R)`, with
  `Matrix.ProjGenLinGroup.innerAut_injective` and `Matrix.ProjGenLinGroup.innerAut_bijective`.

## References

* R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 12, for the Skolem–Noether theorem; the
  form used is `TauCeti.exists_unit_conj_of_algEquiv`.
-/

public section

open Matrix

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Conjugation by an invertible matrix, `x ↦ g x g⁻¹`, as an algebra automorphism of the matrix
algebra. -/
noncomputable def innerAut : GL n R →* (Matrix n n R ≃ₐ[R] Matrix n n R) :=
  (MulSemiringAction.toAlgAut (ConjAct (GL n R)) R (Matrix n n R)).comp
    ConjAct.toConjAct.toMonoidHom

/-- The inner automorphism by `g` sends `x` to `g x g⁻¹`. -/
@[simp]
theorem innerAut_apply (g : GL n R) (x : Matrix n n R) :
    innerAut g x = (g : Matrix n n R) * x * (g : Matrix n n R)⁻¹ := by
  simp [innerAut, ConjAct.units_smul_def]

/-- **An inner automorphism of a matrix algebra is trivial exactly when the conjugating matrix is
central**, that is, an invertible scalar matrix. -/
theorem innerAut_eq_one_iff (g : GL n R) :
    innerAut g = 1 ↔ g ∈ Subgroup.center (GL n R) := by
  have key : innerAut g = 1 ↔ ∀ x : Matrix n n R, (g : Matrix n n R) * x = x * g := by
    rw [AlgEquiv.ext_iff]
    refine forall_congr' fun x => ?_
    rw [innerAut_apply, AlgEquiv.one_apply, ← Matrix.coe_units_inv]
    constructor
    · intro h
      calc (g : Matrix n n R) * x = g * x * ↑g⁻¹ * g := by
            rw [Matrix.mul_assoc _ (↑g⁻¹ : Matrix n n R), Units.inv_mul, Matrix.mul_one]
        _ = x * g := by rw [h]
    · intro h
      rw [h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [key]
  constructor
  · exact fun h => Subgroup.mem_center_iff.mpr fun h' => Units.ext (h h').symm
  · intro hg x
    obtain ⟨a, ha⟩ := mem_center_iff_val_mem_range_scalar.mp hg
    rw [← ha]
    exact (Matrix.scalar_commute a (fun _ => Commute.all _ _) x).eq

/-- The kernel of conjugation is the center of the general linear group. -/
@[simp]
theorem ker_innerAut : (innerAut (n := n) (R := R)).ker = Subgroup.center (GL n R) := by
  ext g
  exact innerAut_eq_one_iff g

/-- **Skolem–Noether for matrix algebras**: over a field, every algebra automorphism of a matrix
algebra is inner. -/
theorem innerAut_surjective (K : Type*) [Field K] :
    Function.Surjective (innerAut (n := n) (R := K)) := by
  intro e
  cases isEmpty_or_nonempty n
  · exact ⟨1, Subsingleton.elim _ _⟩
  · obtain ⟨u, hu⟩ := TauCeti.exists_unit_conj_of_algEquiv K e
    exact ⟨u, AlgEquiv.ext fun x => by rw [innerAut_apply, hu, Matrix.coe_units_inv]⟩

end Matrix.GeneralLinearGroup

namespace Matrix.ProjGenLinGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Conjugation induces a homomorphism from the projective general linear group
`PGL(n, R) = GL n R / Z(GL n R)` to the automorphism group of the matrix algebra. -/
noncomputable def innerAut : ProjGenLinGroup n R →* (Matrix n n R ≃ₐ[R] Matrix n n R) :=
  QuotientGroup.lift (Subgroup.center (GL n R)) GeneralLinearGroup.innerAut
    GeneralLinearGroup.ker_innerAut.ge

/-- On the class of `g`, the induced homomorphism is the inner automorphism by `g`. -/
@[simp]
theorem innerAut_mk (g : GL n R) : innerAut (mk g) = GeneralLinearGroup.innerAut g :=
  (rfl)

/-- `PGL(n, R)` acts faithfully on the matrix algebra by conjugation. -/
theorem innerAut_injective : Function.Injective (innerAut (n := n) (R := R)) := by
  refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
  obtain ⟨g, rfl⟩ := mk_surjective x
  rw [innerAut_mk, GeneralLinearGroup.innerAut_eq_one_iff] at hx
  exact mk_eq_one.mpr hx

/-- Over a field, `PGL(n, K)` is the automorphism group of the matrix algebra. -/
theorem innerAut_bijective (K : Type*) [Field K] :
    Function.Bijective (innerAut (n := n) (R := K)) := by
  refine ⟨innerAut_injective, fun e => ?_⟩
  obtain ⟨g, rfl⟩ := GeneralLinearGroup.innerAut_surjective K e
  exact ⟨mk g, innerAut_mk g⟩

end Matrix.ProjGenLinGroup
