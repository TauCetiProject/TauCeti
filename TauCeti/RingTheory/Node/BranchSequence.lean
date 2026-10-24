/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.Flat
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.RingHom.Finite

/-!
# The branch exact sequence of a split node

The two branches of `R[x,y]/(xy)` give a map into `R[t] × R[t]`, taking `x` to `(t,0)`
and `y` to `(0,t)`. This map is injective, and its image consists of the pairs with the same
value at the origin. The difference of the two values is surjective onto `R`, identifying
the quotient of the branch algebra by the node algebra with `R` as an `R`-module.

This is the local algebra calculation underlying the normalization exact sequence at a split
node: a regular function on the two branches descends precisely when its values agree at the
two points above the node. The calculation works over every commutative ring; it does not
assert that the branch algebra is a normalization over a nonnormal base.

The sequence is also linear over the node algebra itself, with the action on `R` given by
`nodeValue`, evaluation at the singular section. `branchModuleSequence` records this stronger
scalar compatibility, allowing the associated-sheaf functor on the node to produce its
normalization sequence.

## References

* The Stacks Project, Section 53.19, *Nodal curves*, Tag 0C46.
-/

public section

noncomputable section

namespace TauCeti.NodeAlgebra

open Polynomial

variable (R : Type*) [CommRing R]

/-- Restriction to the two branches of the split nodal equation. -/
def branchMap : NodeAlgebra R 0 →ₐ[R] R[X] × R[X] :=
  lift 0 (X, 0) (0, X) (by simp)

/-- The first coordinate is the parameter on the first branch and zero on the second. -/
@[simp]
lemma branchMap_coord_zero : branchMap R (coord (0 : R) 0) = (X, 0) :=
  lift_coord_zero _ _ _ _

/-- The second coordinate is the parameter on the second branch and zero on the first. -/
@[simp]
lemma branchMap_coord_one : branchMap R (coord (0 : R) 1) = (0, X) :=
  lift_coord_one _ _ _ _

/-- The obstruction to descending a pair of branch functions is the difference of their values
at the origin. -/
def branchDifference : (R[X] × R[X]) →ₗ[R] R :=
  (Polynomial.lcoeff R 0).comp (LinearMap.fst R R[X] R[X]) -
    (Polynomial.lcoeff R 0).comp (LinearMap.snd R R[X] R[X])

@[simp]
lemma branchDifference_apply (p : R[X] × R[X]) :
    branchDifference R p = p.1.coeff 0 - p.2.coeff 0 := (rfl)

private lemma branchMap_aeval (i : Fin 2) (p : R[X]) :
    branchMap R (aeval (coord (0 : R) i) p) =
      if i = 0 then (p, C (p.coeff 0)) else (C (p.coeff 0), p) := by
  rw [← Polynomial.aeval_algHom_apply]
  fin_cases i <;> simp [Polynomial.aeval_prod_apply, ← Polynomial.coeff_zero_eq_aeval_zero',
    branchMap_coord_zero, branchMap_coord_one]

private lemma branchMap_aeval_sum (p : R[X]) :
    branchMap R (aeval (coord (0 : R) 0 + coord 0 1) p) = (p, p) := by
  rw [← Polynomial.aeval_algHom_apply]
  simp [Polynomial.aeval_prod_apply]

private lemma exists_eq_aeval_sum_add_mul [Nontrivial R] (z : NodeAlgebra R 0) :
    ∃ p q : R[X], z = aeval (coord (0 : R) 0 + coord 0 1) p +
      aeval (coord (0 : R) 0 + coord 0 1) q * coord 0 0 := by
  -- The existing monic quadratic presentation is free on `1,x` over `R[x+y]`.
  let e := adjoinRootEquiv (0 : R)
  have := e.symm.injective.nontrivial
  let pb := AdjoinRoot.powerBasis' (monic_quadratic (0 : R))
  obtain ⟨f, hf, he⟩ := pb.exists_eq_aeval (e.symm z)
  have hf2 : f.natDegree < 2 := by
    simpa only [pb, AdjoinRoot.powerBasis'_dim, natDegree_quadratic] using hf
  simp only [pb, AdjoinRoot.powerBasis'_gen] at he
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  have hz := congrArg (adjoinRootEquiv (0 : R)) he
  rw [AlgEquiv.apply_symm_apply] at hz
  rw [Polynomial.aeval_eq_sum_range' hf2] at hz
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    Algebra.smul_def, AdjoinRoot.algebraMap_eq, mul_one] at hz
  simpa only [map_add, map_mul, adjoinRootEquiv_of, adjoinRootEquiv_root] using hz

/-- Restriction to the two branches loses no regular functions, over any commutative base. -/
theorem branchMap_injective : Function.Injective (branchMap R) := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
    let := h
    have : Subsingleton (NodeAlgebra R 0) := Module.subsingleton R _
    exact fun _ _ _ ↦ Subsingleton.elim _ _
  | inr h =>
    let := h
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨p, q, rfl⟩ := exists_eq_aeval_sum_add_mul R z
    have hpair : (p + q * X, p) = (0, 0) := by
      simpa [branchMap_aeval_sum] using hz
    have hp : p = 0 := congrArg Prod.snd hpair
    have hq : q = 0 := Polynomial.isRegular_X.right.eq_iff.mp
      (by simpa [hp] using congrArg Prod.fst hpair)
    simp [hp, hq]

/-- A pair of branch functions descends to the node exactly when their constant terms agree. -/
theorem mem_range_branchMap_iff (p : R[X] × R[X]) :
    p ∈ (branchMap R).range ↔ p.1.coeff 0 = p.2.coeff 0 := by
  constructor
  · rintro ⟨z, rfl⟩
    have hhom :
        ((aeval (0 : R) : R[X] →ₐ[R] R).comp (AlgHom.fst R R[X] R[X])).comp (branchMap R) =
        ((aeval (0 : R) : R[X] →ₐ[R] R).comp (AlgHom.snd R R[X] R[X])).comp (branchMap R) := by
      ext <;> simp
    simpa [← Polynomial.coeff_zero_eq_eval_zero] using AlgHom.congr_fun hhom z
  · intro h
    refine ⟨aeval (coord (0 : R) 0) p.1 + aeval (coord (0 : R) 1) p.2 -
      algebraMap R (NodeAlgebra R 0) (p.1.coeff 0), ?_⟩
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [map_sub, map_add, branchMap_aeval R 0, branchMap_aeval R 1, AlgHom.commutes]
    simp [h]

/-- The difference of branch values is onto: every value is represented by `(C r, 0)`. -/
theorem branchDifference_surjective : Function.Surjective (branchDifference R) :=
  fun r ↦ ⟨(C r, 0), by simp⟩

/-- The branch sequence is exact: the functions descending to the node are precisely the
kernel of the difference of values at the origin. -/
theorem exact_branchMap_branchDifference :
    Function.Exact (branchMap R).toLinearMap (branchDifference R) := by
  rw [LinearMap.exact_iff]
  ext p
  simpa [LinearMap.mem_range, AlgHom.mem_range, LinearMap.mem_ker, sub_eq_zero] using
    (mem_range_branchMap_iff R p).symm

/-- The defect module of the branch inclusion is one copy of the base ring. -/
def branchQuotientEquiv :
    ((R[X] × R[X]) ⧸ LinearMap.range (branchMap R).toLinearMap) ≃ₗ[R] R :=
  (exact_branchMap_branchDifference R).linearEquivOfSurjective (branchDifference_surjective R)

/-- The quotient comparison takes a pair of branch functions to the difference at the origin. -/
@[simp]
lemma branchQuotientEquiv_mk (p : R[X] × R[X]) :
    branchQuotientEquiv R (Submodule.Quotient.mk p) = p.1.coeff 0 - p.2.coeff 0 := by
  rw [branchQuotientEquiv, Function.Exact.linearEquivOfSurjective_apply]
  exact (Submodule.liftQ_apply _ _ p).trans (branchDifference_apply R p)

/-- The inverse quotient comparison represents a value by the constant function on the first
branch and zero on the second. -/
@[simp]
lemma branchQuotientEquiv_symm_apply (r : R) :
    (branchQuotientEquiv R).symm r = Submodule.Quotient.mk (C r, 0) := by
  simpa [branchQuotientEquiv] using
    (exact_branchMap_branchDifference R).linearEquivOfSurjective_symm_apply
    (branchDifference_surjective R) (C r, 0)

/-- The branch algebra is finite over the node algebra, generated by `1` and `(1,0)`. -/
theorem finite_branchMap : (branchMap R).toRingHom.Finite := by
  let := (branchMap R).toRingHom.toAlgebra
  let f : (NodeAlgebra R 0 × NodeAlgebra R 0) →ₗ[NodeAlgebra R 0] (R[X] × R[X]) :=
    (LinearMap.toSpanSingleton (NodeAlgebra R 0) (R[X] × R[X]) 1).coprod
      (LinearMap.toSpanSingleton (NodeAlgebra R 0) (R[X] × R[X]) (1, 0))
  apply Module.Finite.of_surjective f
  intro p
  let r := p.1.coeff 0 - p.2.coeff 0
  obtain ⟨z, hz⟩ := (mem_range_branchMap_iff R (p - (C r, 0))).mpr (by simp [r])
  refine ⟨(z, algebraMap R (NodeAlgebra R 0) r), ?_⟩
  -- The local algebra structure is induced by `branchMap`; scalar multiplication is its
  -- image followed by multiplication in the branch algebra.
  simp only [f, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply, Algebra.smul_def,
    RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, mul_one]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hz
  rw [hz, (branchMap R).commutes]
  simp

/-! ### Linearity over the node algebra -/

open CategoryTheory

/-- Evaluation of a function on the split node at its singular section. -/
def nodeValue : NodeAlgebra R 0 →ₐ[R] R :=
  lift 0 0 0 (by simp)

@[simp]
theorem nodeValue_coord_zero : nodeValue R (coord (0 : R) 0) = 0 :=
  lift_coord_zero _ _ _ _

@[simp]
theorem nodeValue_coord_one : nodeValue R (coord (0 : R) 1) = 0 :=
  lift_coord_one _ _ _ _

/-- The value on the first branch at its origin is the value at the node. -/
@[simp]
theorem coeff_zero_branchMap_fst (z : NodeAlgebra R 0) :
    (branchMap R z).1.coeff 0 = nodeValue R z := by
  have h : ((aeval (0 : R)).comp ((AlgHom.fst R R[X] R[X]).comp (branchMap R))) =
      nodeValue R := by ext <;> simp
  simpa only [AlgHom.comp_apply, AlgHom.fst_apply, ← coeff_zero_eq_aeval_zero',
    Algebra.algebraMap_self, RingHom.id_apply] using
    AlgHom.congr_fun h z

/-- The value on the second branch at its origin is the value at the node. -/
@[simp]
theorem coeff_zero_branchMap_snd (z : NodeAlgebra R 0) :
    (branchMap R z).2.coeff 0 = nodeValue R z :=
  ((mem_range_branchMap_iff R _).mp ⟨z, rfl⟩).symm.trans (coeff_zero_branchMap_fst R z)

/-- The branch inclusion, linear over the node algebra via restriction of scalars. -/
def branchInclusion : ModuleCat.of (NodeAlgebra R 0) (NodeAlgebra R 0) ⟶
    (ModuleCat.restrictScalars (branchMap R : NodeAlgebra R 0 →+* R[X] × R[X])).obj
      (ModuleCat.of (R[X] × R[X]) (R[X] × R[X])) :=
  ModuleCat.ofHom (X := ModuleCat.of (NodeAlgebra R 0) (NodeAlgebra R 0))
    (Y := (ModuleCat.restrictScalars (branchMap R : NodeAlgebra R 0 →+* R[X] × R[X])).obj
      (ModuleCat.of (R[X] × R[X]) (R[X] × R[X])))
    { toFun := branchMap R
      map_add' := map_add _
      map_smul' := fun a z ↦ map_mul (branchMap R) a z }

@[simp]
theorem branchInclusion_apply (z : NodeAlgebra R 0) :
    branchInclusion R z = branchMap R z := (rfl)

/-- The difference of branch values is linear over the node algebra, acting on `R`
by evaluation at the node. -/
def branchDifferenceHom :
    (ModuleCat.restrictScalars (branchMap R : NodeAlgebra R 0 →+* R[X] × R[X])).obj
        (ModuleCat.of (R[X] × R[X]) (R[X] × R[X])) ⟶
      (ModuleCat.restrictScalars (nodeValue R : NodeAlgebra R 0 →+* R)).obj (ModuleCat.of R R) :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (branchMap R : NodeAlgebra R 0 →+* R[X] × R[X])).obj
      (ModuleCat.of (R[X] × R[X]) (R[X] × R[X])))
    (Y := (ModuleCat.restrictScalars (nodeValue R : NodeAlgebra R 0 →+* R)).obj (ModuleCat.of R R))
    { toFun := branchDifference R
      map_add' := map_add _
      map_smul' := fun a p ↦ by
        -- Reduce both the carrier of the restricted module and its scalar action;
        -- reducing only the goal leaves mismatched bundled additive structures.
        dsimp only [ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj'] at p ⊢
        simp only [branchDifference_apply]
        change ((branchMap R a).1 * p.1).coeff 0 -
            ((branchMap R a).2 * p.2).coeff 0 =
          nodeValue R a * (p.1.coeff 0 - p.2.coeff 0)
        simp [mul_coeff_zero, mul_sub] }

@[simp]
theorem branchDifferenceHom_apply (p : R[X] × R[X]) :
    branchDifferenceHom R p = p.1.coeff 0 - p.2.coeff 0 :=
  branchDifference_apply R p

/-- The branch sequence over the node algebra. Its last term is supported on the
singular section, and its last arrow measures failure of branch functions to descend.
The bundled objects and arrows remain transparent for applying exact functors. -/
abbrev branchModuleSequence : ShortComplex (ModuleCat (NodeAlgebra R 0)) :=
  ShortComplex.mk (branchInclusion R) (branchDifferenceHom R) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    -- Reduce the short-complex arrows through their bundled module homomorphisms.
    change branchDifference R (branchMap R z) = 0
    simp [branchDifference_apply])

/-- The normalization sequence of a split node is short exact as a sequence of
modules over the node algebra, over every commutative base ring. -/
theorem branchModuleSequence_shortExact : (branchModuleSequence R).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · exact exact_branchMap_branchDifference R
  · exact branchMap_injective R
  · exact branchDifference_surjective R

end TauCeti.NodeAlgebra
