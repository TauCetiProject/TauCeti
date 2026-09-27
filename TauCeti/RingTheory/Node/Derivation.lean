/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.RingTheory.Kaehler.Basic
public import TauCeti.RingTheory.Node.Basic

/-!
# Derivations of the nodal equation

For `B = R[x,y]/(xy-a)`, an `R`-derivation of `B` is determined by its values `u` and `v`
on `x` and `y`. The equation imposes precisely `yu+xv=0`. This calculation gives the
Jacobian relation used in the presentation of the relative differentials of a node.

The statement holds over any commutative coefficient ring and for any smoothing parameter.

## References

* Stacks Project, Section 10.131 (Differentials), Tag 00RM.
-/

public section

noncomputable section

namespace TauCeti.NodeAlgebra

open MvPolynomial

variable {R : Type*} [CommRing R] (a : R)

private abbrev polynomialRing := MvPolynomial (Fin 2) R

private local instance : Algebra (polynomialRing (R := R)) (NodeAlgebra R a) :=
  (mk a).toRingHom.toAlgebra

/-- The pairs of possible values of an `R`-derivation on the two coordinates of `xy=a`. -/
def DerivationValues : Submodule (NodeAlgebra R a) ((Fin 2) → NodeAlgebra R a) :=
  LinearMap.ker ({
      toFun := fun u ↦ coord a 1 * u 0 + coord a 0 * u 1
      map_add' := by intro u v; simp [mul_add, add_assoc, add_left_comm, add_comm]
      map_smul' := by intro c u; simp [smul_eq_mul, mul_add]; ring }
      : ((Fin 2) → NodeAlgebra R a) →ₗ[NodeAlgebra R a] NodeAlgebra R a)

/-- A pair belongs to `DerivationValues` exactly when it satisfies the differentiated
equation `yu+xv=0`. -/
@[simp]
lemma mem_derivationValues_iff (u : (Fin 2) → NodeAlgebra R a) :
    u ∈ DerivationValues a ↔ coord a 1 * u 0 + coord a 0 * u 1 = 0 :=
  Iff.rfl

private def derivationValues (D : Derivation R (NodeAlgebra R a) (NodeAlgebra R a)) :
    DerivationValues a := by
  refine ⟨fun i ↦ D (coord a i), ?_⟩
  apply (mem_derivationValues_iff a _).2
  calc
    _ = D (coord a 0 * coord a 1) := by rw [Derivation.leibniz]; ring
    _ = D (algebraMap R (NodeAlgebra R a) a) := congrArg D (coord_zero_mul_coord_one a)
    _ = 0 := D.map_algebraMap a

private def liftValues (u : DerivationValues a) (i : Fin 2) : polynomialRing (R := R) :=
  (mk_surjective a (u.1 i)).choose

private lemma mk_liftValues (u : DerivationValues a) (i : Fin 2) :
    mk a (liftValues a u i) = u.1 i :=
  (mk_surjective a (u.1 i)).choose_spec

private def polynomialDerivation (u : DerivationValues a) :
    Derivation R (polynomialRing (R := R)) (polynomialRing (R := R)) :=
  MvPolynomial.mkDerivation R (liftValues a u)

private lemma polynomialDerivation_relation (u : DerivationValues a) :
    mk a (polynomialDerivation a u (X 0 * X 1 - C a)) = 0 := by
  have hu : coord a 1 * u.1 0 + coord a 0 * u.1 1 = 0 :=
    (mem_derivationValues_iff a u.1).mp u.2
  simpa [polynomialDerivation, Derivation.leibniz, smul_eq_mul,
    mk_liftValues, mk_X, mul_comm, add_comm] using hu

private lemma polynomialDerivation_ker (u : DerivationValues a)
    (p : polynomialRing (R := R)) (hp : mk a p = 0) :
    mk a (polynomialDerivation a u p) = 0 := by
  have hp' : p ∈ Ideal.span {X 0 * X 1 - C a} := by
    rw [← ker_mk a]
    exact (RingHom.mem_ker (f := (mk a).toRingHom)).mpr hp
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp'
  rw [Derivation.leibniz]
  simp only [smul_eq_mul, map_add, map_mul, polynomialDerivation_relation,
    mul_zero, zero_add]
  have hr : mk a (X 0 * X 1 - C a) = 0 := by
    simp [map_sub, map_mul, mk_X, coord_zero_mul_coord_one]
  rw [hr, zero_mul]

private def derivationOfValues (u : DerivationValues a) :
    Derivation R (NodeAlgebra R a) (NodeAlgebra R a) :=
  Derivation.liftOfSurjective (mk_surjective a)
    (polynomialDerivation_ker a u)

private lemma derivationOfValues_coord (u : DerivationValues a) (i : Fin 2) :
    derivationOfValues a u (coord a i) = u.1 i := by
  rw [show coord a i = mk a (X i) from (mk_X a i).symm,
    derivationOfValues, Derivation.liftOfSurjective_apply]
  simp [polynomialDerivation, mk_liftValues]

/-- An `R`-derivation of the nodal algebra is uniquely determined by its values on the two
coordinates. -/
@[ext]
theorem derivation_ext {D E : Derivation R (NodeAlgebra R a) (NodeAlgebra R a)}
    (h : ∀ i, D (coord a i) = E (coord a i)) : D = E := by
  apply Derivation.ext
  intro b
  obtain ⟨p, rfl⟩ := mk_surjective a b
  have hpoly : D.compAlgebraMap (polynomialRing (R := R)) =
      E.compAlgebraMap (polynomialRing (R := R)) := by
    apply MvPolynomial.derivation_ext
    intro i
    simp only [Derivation.compAlgebraMap_apply, RingHom.algebraMap_toAlgebra,
      AlgHom.toRingHom_eq_coe]
    -- The locally chosen polynomial-algebra structure is induced by `mk`.
    change D (mk a (X i)) = E (mk a (X i))
    rw [mk_X]
    exact h i
  exact Derivation.congr_fun hpoly p

/-- Derivations of `R[x,y]/(xy-a)` are linearly equivalent to pairs of values satisfying
`yu+xv=0`. -/
def derivationEquivValues :
    Derivation R (NodeAlgebra R a) (NodeAlgebra R a) ≃ₗ[NodeAlgebra R a]
      DerivationValues a where
  toFun := derivationValues a
  invFun := derivationOfValues a
  left_inv D := derivation_ext a (by
    intro i
    simpa [derivationValues] using derivationOfValues_coord a (derivationValues a D) i)
  right_inv u := Subtype.ext (by funext i; exact derivationOfValues_coord a u i)
  map_add' D E := Subtype.ext (by funext i; rfl)
  map_smul' c D := Subtype.ext (by funext i; rfl)

/-- Evaluation of the derivation equivalence at a coordinate. -/
@[simp]
lemma derivationEquivValues_apply (D : Derivation R (NodeAlgebra R a) (NodeAlgebra R a))
    (i : Fin 2) : (derivationEquivValues a D).1 i = D (coord a i) := by
  rfl

/-- Evaluation of the inverse equivalence at a coordinate. -/
@[simp]
lemma derivationEquivValues_symm_apply (u : DerivationValues a) (i : Fin 2) :
    ((derivationEquivValues a).symm u) (coord a i) = u.1 i :=
  derivationOfValues_coord a u i

/-- The universal Kähler differentials of the two coordinates satisfy the Jacobian
relation of the nodal equation. -/
theorem differential_relation :
    coord a 1 • KaehlerDifferential.D R (NodeAlgebra R a) (coord a 0) +
      coord a 0 • KaehlerDifferential.D R (NodeAlgebra R a) (coord a 1) = 0 := by
  have h := congrArg (KaehlerDifferential.D R (NodeAlgebra R a))
    (coord_zero_mul_coord_one a)
  simpa only [Derivation.leibniz, Derivation.map_algebraMap, add_comm] using h

end TauCeti.NodeAlgebra
