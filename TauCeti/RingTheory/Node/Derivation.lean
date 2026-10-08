/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import TauCeti.RingTheory.Node.Basic

/-!
# Derivations of the nodal equation

For `B = R[x,y]/(xy-a)` and any `B`-module `M`, an `R`-derivation from `B` to `M` is
determined by its values `u` and `v` on `x` and `y`. The equation imposes precisely
`y • u + x • v = 0`. This calculation gives the
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
variable {M : Type*} [AddCommMonoid M] [Module (NodeAlgebra R a) M]
  [Module R M] [IsScalarTower R (NodeAlgebra R a) M]

private abbrev polynomialRing := MvPolynomial (Fin 2) R

private abbrev polynomialModule : Module (polynomialRing (R := R)) M :=
  Module.compHom M (mk a).toRingHom

private theorem polynomialScalarTower
    {M : Type*} [AddCommMonoid M] [Module (NodeAlgebra R a) M]
    [SMul R M] [IsScalarTower R (NodeAlgebra R a) M] :
    letI := polynomialModule (M := M) a
    IsScalarTower R (polynomialRing (R := R)) M := by
  let _ := polynomialModule (M := M) a
  constructor
  intro r p m
  -- The polynomial action on `M` is the action of its image under `mk`.
  change ((mk a) (r • p)) • m = r • ((mk a) p • m)
  rw [map_smul, smul_assoc]

/-- The pairs of possible values in `M` of an `R`-derivation on the two coordinates of
`xy=a`. -/
def DerivationValues : Submodule (NodeAlgebra R a) ((Fin 2) → M) :=
  LinearMap.ker ({
      toFun := fun u ↦ coord a 1 • u 0 + coord a 0 • u 1
      map_add' := by intro u v; simp [smul_add, add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro c u
        simp only [Pi.smul_apply, smul_add, RingHom.id_apply]
        rw [smul_comm (coord a 1) c, smul_comm (coord a 0) c] }
      : ((Fin 2) → M) →ₗ[NodeAlgebra R a] M)

omit [Module R M] [IsScalarTower R (NodeAlgebra R a) M] in
/-- A pair belongs to `DerivationValues` exactly when it satisfies the differentiated
equation `yu+xv=0`. -/
@[simp]
lemma mem_derivationValues_iff (u : (Fin 2) → M) :
    u ∈ DerivationValues a ↔ coord a 1 • u 0 + coord a 0 • u 1 = 0 :=
  Iff.rfl

omit [IsScalarTower R (NodeAlgebra R a) M] in
variable {a} in
/-- The coordinate values of any derivation satisfy the Jacobian relation of `xy = a`. -/
@[simp]
theorem _root_.Derivation.coord_one_smul_apply_coord_zero_add_coord_zero_smul_apply_coord_one
    (D : Derivation R (NodeAlgebra R a) M) :
    coord a 1 • D (coord a 0) + coord a 0 • D (coord a 1) = 0 := by
  have h := congrArg D (coord_zero_mul_coord_one a)
  simpa only [Derivation.leibniz, Derivation.map_algebraMap, add_comm] using h

private def derivationValues (D : Derivation R (NodeAlgebra R a) M) :
    DerivationValues (M := M) a :=
  ⟨fun i ↦ D (coord a i), (mem_derivationValues_iff a _).2
    D.coord_one_smul_apply_coord_zero_add_coord_zero_smul_apply_coord_one⟩

private def polynomialDerivation (u : DerivationValues (M := M) a) :
    letI := polynomialModule (M := M) a
    Derivation R (polynomialRing (R := R)) M := by
  letI := polynomialModule (M := M) a
  letI := polynomialScalarTower (M := M) a
  exact MvPolynomial.mkDerivation R u.1

private lemma polynomialDerivation_relation (u : DerivationValues (M := M) a) :
    polynomialDerivation a u (X 0 * X 1 - C a) = 0 := by
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup (NodeAlgebra R a)
  let _ := polynomialModule (M := M) a
  have hu : coord a 1 • u.1 0 + coord a 0 • u.1 1 = 0 :=
    (mem_derivationValues_iff a u.1).mp u.2
  rw [map_sub, Derivation.leibniz]
  simp only [polynomialDerivation, MvPolynomial.mkDerivation_X,
    MvPolynomial.derivation_C, sub_zero]
  -- Unfold the polynomial action to use the Jacobian relation in `M`.
  change (mk a (X 0)) • u.1 1 + (mk a (X 1)) • u.1 0 = 0
  simpa only [mk_X, add_comm] using hu

private lemma polynomialDerivation_ker (u : DerivationValues (M := M) a)
    (p : polynomialRing (R := R)) (hp : mk a p = 0) :
    polynomialDerivation a u p = 0 := by
  let _ := polynomialModule (M := M) a
  have hp' : p ∈ Ideal.span {X 0 * X 1 - C a} := by
    rw [← ker_mk a]
    exact (RingHom.mem_ker (f := (mk a).toRingHom)).mpr hp
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp'
  rw [Derivation.leibniz]
  simp only [polynomialDerivation_relation, smul_zero, zero_add]
  have hr : mk a (X 0 * X 1 - C a) = 0 := by
    simp [map_sub, map_mul, mk_X, coord_zero_mul_coord_one]
  -- The relation acts by zero on every `NodeAlgebra R a`-module.
  change (mk a (X 0 * X 1 - C a)) • polynomialDerivation a u q = 0
  rw [hr, zero_smul]

private def descendedLinearMap (u : DerivationValues (M := M) a) :
    NodeAlgebra R a →ₗ[R] M := by
  letI := polynomialModule (M := M) a
  let d := polynomialDerivation a u
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup (NodeAlgebra R a)
  exact (mk a).toLinearMap.liftOfSurjective (mk_surjective a) ⟨d.toLinearMap, by
    intro p hp
    apply LinearMap.mem_ker.mpr
    exact polynomialDerivation_ker a u p (LinearMap.mem_ker.mp hp)⟩

private lemma descendedLinearMap_mk (u : DerivationValues (M := M) a)
    (p : polynomialRing (R := R)) :
    descendedLinearMap a u (mk a p) = polynomialDerivation a u p := by
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup (NodeAlgebra R a)
  exact LinearMap.equivOfSurjective_apply (mk_surjective a) _

private def derivationOfValues (u : DerivationValues (M := M) a) :
    Derivation R (NodeAlgebra R a) M := by
  letI := polynomialModule (M := M) a
  let d := polynomialDerivation a u
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup (NodeAlgebra R a)
  let f := descendedLinearMap a u
  refine Derivation.mk' f ?_
  intro x y
  obtain ⟨p, rfl⟩ := mk_surjective a x
  obtain ⟨q, rfl⟩ := mk_surjective a y
  rw [← map_mul (mk a)]
  simp only [f, descendedLinearMap_mk]
  exact d.leibniz p q

private lemma derivationOfValues_coord (u : DerivationValues (M := M) a) (i : Fin 2) :
    derivationOfValues a u (coord a i) = u.1 i := by
  rw [← mk_X a i]
  simp only [derivationOfValues, Derivation.coe_mk', descendedLinearMap_mk]
  let _ := polynomialModule (M := M) a
  let _ := polynomialScalarTower (M := M) a
  exact MvPolynomial.mkDerivation_X R u.1 i

omit [IsScalarTower R (NodeAlgebra R a) M] in
/-- An `R`-derivation of the nodal algebra is uniquely determined by its values on the two
coordinates. -/
@[ext]
theorem derivation_ext {D E : Derivation R (NodeAlgebra R a) M}
    (h : ∀ i, D (coord a i) = E (coord a i)) : D = E := by
  apply Derivation.ext_of_adjoin_eq_top _ (adjoin_range_coord a)
  rintro _ ⟨i, rfl⟩
  exact h i

/-- Derivations of `R[x,y]/(xy-a)` into any module are linearly equivalent to pairs of
values satisfying `y • u + x • v = 0`. -/
def derivationEquivValues :
    Derivation R (NodeAlgebra R a) M ≃ₗ[NodeAlgebra R a]
      DerivationValues (M := M) a where
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
lemma derivationEquivValues_apply (D : Derivation R (NodeAlgebra R a) M)
    (i : Fin 2) : (derivationEquivValues a D).1 i = D (coord a i) := by
  rfl

/-- Evaluation of the inverse equivalence at a coordinate. -/
@[simp]
lemma derivationEquivValues_symm_apply (u : DerivationValues (M := M) a) (i : Fin 2) :
    ((derivationEquivValues a).symm u) (coord a i) = u.1 i :=
  derivationOfValues_coord a u i

end TauCeti.NodeAlgebra
