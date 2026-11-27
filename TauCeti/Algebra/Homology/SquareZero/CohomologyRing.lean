/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import TauCeti.Algebra.DirectSum.Ring
public import TauCeti.Algebra.Homology.SquareZero.Graded

/-!
# The cohomology ring of a product that is associative and unital up to coboundaries

Let `D` be a linear endomorphism of a module `M` over a commutative ring `R`, with homogeneous
pieces `G : ℤ → Submodule R M`, and let `μ : M → M → M` be a bilinear map of degree zero obeying
the Leibniz rule `D (μ a b) = μ (D a) b + (-1)^i μ a (D b)` for `a` of degree `i`. Then `μ`
descends to products `H^i × H^j → H^(i + j)` on the degree-wise cohomology of `D`
(`LinearMap.cohomologyProduct`). Suppose moreover that

* `μ` is associative up to coboundaries on cocycles: `μ (μ a b) c - μ a (μ b c)` is a coboundary
  for all cocycles `a`, `b`, `c`;
* a cocycle `e` of degree zero is a two-sided unit up to coboundaries on cocycles: `μ e a - a`
  and `μ a e - a` are coboundaries for every cocycle `a`.

The chain-level product need not be associative or unital. Then the degree-wise cohomology groups
form a graded ring with unit the class of `e` (`LinearMap.cohomologyGRing`), and a graded
`R`-algebra (`LinearMap.cohomologyGAlgebra`), so that Mathlib's instances on direct sums make
`⨁ i, H^i` an `R`-algebra in which `of i [a] * of j [b] = of (i + j) [μ a b]`
(`LinearMap.cohomologyGRing_of_mk_mul_of_mk`) and `1 = of 0 [e]`
(`LinearMap.cohomologyGRing_one`). If `μ a b - (-1)^(i j) μ b a` is a coboundary for cocycles
`a` and `b` of degrees `i` and `j`, the ring is graded commutative
(`LinearMap.cohomologyGRing_of_mul_of_comm`).

A degree-preserving linear map `f` commuting with the endomorphisms, which intertwines two such
products up to coboundaries on cocycles and sends the unit to the unit up to a coboundary, induces
an `R`-algebra homomorphism of cohomology rings (`LinearMap.cohomologyAlgHom`), given in each
degree by the induced map `LinearMap.cohomologyMap`. If the induced map is bijective in every
degree, it is an isomorphism of `R`-algebras (`LinearMap.cohomologyAlgEquiv`), and then the
condition on the units is not needed: it is automatic once the induced map is onto in degree zero
(`LinearMap.sub_mem_coboundaries_of_surjective_cohomologyMap`), since a multiplicative map onto
the cohomology of a unital product sends the unit to the unit.

Two products `μ` and `ν` which differ by a coboundary on every pair of cocycles induce the same
product on cohomology (`LinearMap.cohomologyMul_eq_of_sub_mem_coboundaries`). Their units are then
cohomologous (`LinearMap.sub_mem_coboundaries_of_mul_sub_mem_coboundaries`), so the two cohomology
rings are the same graded ring structure (`LinearMap.cohomologyGRing_eq_of_sub_mem_coboundaries`):
the graded ring structure depends only on the product on cohomology and the unit class
(`LinearMap.cohomologyGRing_congr`), since it is built by `TauCeti.DirectSum.gRingOfMul` from
these alone.

The degree-wise cohomology is that of `TauCeti.Algebra.Homology.SquareZero.Graded`, where `M` need
not be the direct sum of the pieces `G i`; the ring is the direct sum of the cohomology groups of
the homogeneous pieces. This covers completed modules such as the completed Floer and Novikov
complexes of `TauCeti.RingTheory.NovikovModule`, whose chain-level operations are only associative,
unital and commutative up to explicit homotopies.

The construction follows `TauCeti.ModuleCat.gRingOfHomogeneous` and
`TauCeti.ModuleCat.gAlgebraOfHomogeneous`
(`TauCeti.Algebra.Category.ModuleCat.Monoidal.GradedRing`), with the laws holding only up to
coboundaries.

## Main definitions

* `LinearMap.cohomologyMul`: the product `H^i × H^j → H^(i + j)` induced by a product of degree
  zero.
* `LinearMap.cohomologyGRing`: the graded ring structure on degree-wise cohomology.
* `LinearMap.cohomologyGAlgebra`: its graded `R`-algebra structure.
* `LinearMap.cohomologyAlgHom`, `LinearMap.cohomologyAlgEquiv`: the algebra homomorphism, and
  isomorphism, of cohomology rings induced by a map intertwining the products.

## Main results

* `LinearMap.cohomologyGRing_eq_of_sub_mem_coboundaries`: products which differ by coboundaries on
  cocycles have the same cohomology ring.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the ring structure induced on Floer cohomology by the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 12.1, on the pair-of-pants product.
-/

public section

noncomputable section

open DirectSum TauCeti

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {D : M →ₗ[R] M} {G : ℤ → Submodule R M}

/-- Classes of cohomologous cocycles of equal degrees are equal as elements of the graded monoid
of cohomology classes, even when the two degrees are only propositionally equal. -/
theorem gradedMonoid_mk_cohomology_mk_eq {i j : ℤ} (h : i = j) {a : D.cocycles G i}
    {b : D.cocycles G j} (hab : (a : M) - b ∈ D.coboundaries G j) :
    GradedMonoid.mk (A := fun k ↦ D.cohomology G k) i (Submodule.Quotient.mk a) =
      GradedMonoid.mk j (Submodule.Quotient.mk b) := by
  subst h
  exact congrArg _ (cohomology_mk_eq_mk_iff.2 hab)

/-- A product of degree zero has degree shift `0`, in the form `LinearMap.cohomologyProduct`
expects. -/
private theorem apply_mem_add_zero {N : Type*} [AddCommGroup N] [Module R N]
    {H : ℤ → Submodule R N} (ν : N →ₗ[R] N →ₗ[R] N)
    (hdeg : ∀ {i j : ℤ} {a b : N}, a ∈ H i → b ∈ H j → ν a b ∈ H (i + j)) {i j : ℤ} {a b : N}
    (ha : a ∈ H i) (hb : b ∈ H j) : ν a b ∈ H (i + j + 0) := by
  rw [add_zero]
  exact hdeg ha hb

section Mul

variable (μ : M →ₗ[R] M →ₗ[R] M)
  (hdeg : ∀ {i j : ℤ} {a b : M}, a ∈ G i → b ∈ G j → μ a b ∈ G (i + j))
  (hL : ∀ {i : ℤ} {a : M}, a ∈ G i → ∀ b, D (μ a b) = μ (D a) b + negOnePowCast R i • μ a (D b))

include hdeg hL in
/-- The product of a cocycle of degree `i` and a cocycle of degree `j` is a cocycle of degree
`i + j`, for a product of degree zero obeying the Leibniz rule. -/
theorem apply_mem_cocycles_add {i j : ℤ} {a b : M} (ha : a ∈ D.cocycles G i)
    (hb : b ∈ D.cocycles G j) : μ a b ∈ D.cocycles G (i + j) :=
  apply_mem_cocycles μ (apply_mem_add_zero μ hdeg) hL (add_zero _) ha hb

/-- **The product on cohomology of a product of degree zero.** A bilinear map of degree zero
obeying the Leibniz rule induces a bilinear map `H^i × H^j → H^(i + j)` on degree-wise
cohomology. This is `LinearMap.cohomologyProduct` for the degree shift `0`. -/
def cohomologyMul {i j : ℤ} :
    D.cohomology G i →ₗ[R] D.cohomology G j →ₗ[R] D.cohomology G (i + j) :=
  cohomologyProduct μ (apply_mem_add_zero μ hdeg) hL (add_zero _)

/-- `LinearMap.cohomologyMul` is `LinearMap.cohomologyProduct` for the degree shift `0`. -/
private theorem cohomologyMul_eq_cohomologyProduct {i j : ℤ} :
    cohomologyMul μ hdeg hL (i := i) (j := j) =
      cohomologyProduct μ (apply_mem_add_zero μ hdeg) hL (add_zero _) :=
  rfl

/-- The product of the classes of two cocycles is the class of their product. -/
@[simp]
theorem cohomologyMul_mk {i j : ℤ} (a : D.cocycles G i) (b : D.cocycles G j) :
    cohomologyMul μ hdeg hL (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk ⟨μ a b, apply_mem_cocycles_add μ hdeg hL a.property b.property⟩ :=
  cohomologyProduct_mk μ (apply_mem_add_zero μ hdeg) hL (add_zero _) a b

end Mul

section GRing

variable (μ : M →ₗ[R] M →ₗ[R] M)
  (hdeg : ∀ {i j : ℤ} {a b : M}, a ∈ G i → b ∈ G j → μ a b ∈ G (i + j))
  (hL : ∀ {i : ℤ} {a : M}, a ∈ G i → ∀ b, D (μ a b) = μ (D a) b + negOnePowCast R i • μ a (D b))
  (e : M) (he : e ∈ D.cocycles G 0)
  (hone_mul : ∀ {i : ℤ} {a : M}, a ∈ D.cocycles G i → μ e a - a ∈ D.coboundaries G i)
  (hmul_one : ∀ {i : ℤ} {a : M}, a ∈ D.cocycles G i → μ a e - a ∈ D.coboundaries G i)
  (hassoc : ∀ {i j k : ℤ} {a b c : M}, a ∈ D.cocycles G i → b ∈ D.cocycles G j →
    c ∈ D.cocycles G k → μ (μ a b) c - μ a (μ b c) ∈ D.coboundaries G (i + j + k))

include hone_mul hmul_one hassoc

/-- **The cohomology ring.** Let `μ` be a bilinear map of degree zero obeying the Leibniz rule,
associative up to coboundaries on cocycles, with a cocycle `e` of degree zero which is a two-sided
unit up to coboundaries on cocycles. Then the degree-wise cohomology of `D` is a graded ring, with
product `LinearMap.cohomologyMul` and unit the class of `e`. -/
@[expose, instance_reducible]
def cohomologyGRing : DirectSum.GRing (fun i ↦ D.cohomology G i) :=
  TauCeti.DirectSum.gRingOfMul
    (fun _ _ ↦ toAddMonoidHom'.comp (cohomologyMul μ hdeg hL).toAddMonoidHom)
    (Submodule.Quotient.mk ⟨e, he⟩)
    (fun x ↦ by
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      exact (congrArg (GradedMonoid.mk _) (cohomologyMul_mk μ hdeg hL ⟨e, he⟩ a)).trans
        (gradedMonoid_mk_cohomology_mk_eq (zero_add _) (hone_mul a.property)))
    (fun x ↦ by
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      exact (congrArg (GradedMonoid.mk _) (cohomologyMul_mk μ hdeg hL a ⟨e, he⟩)).trans
        (gradedMonoid_mk_cohomology_mk_eq (add_zero _) (hmul_one a.property)))
    (fun x y z ↦ by
      -- Both sides are the classes of `μ (μ a b) c` and `μ a (μ b c)` for representatives `a`,
      -- `b`, `c`, in the degrees `i + j + k` and `i + (j + k)`.
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      induction y using Submodule.Quotient.induction_on with | H b => ?_
      induction z using Submodule.Quotient.induction_on with | H c => ?_
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, toAddMonoidHom'_apply,
        toAddMonoidHom_coe]
      rw [cohomologyMul_mk, cohomologyMul_mk, cohomologyMul_mk, cohomologyMul_mk]
      exact gradedMonoid_mk_cohomology_mk_eq (add_assoc _ _ _)
        (by simpa only [add_assoc] using hassoc a.property b.property c.property))

/-- In the cohomology ring, the product of homogeneous classes is `LinearMap.cohomologyMul`. -/
@[simp]
theorem cohomologyGRing_gMul {i j : ℤ} (x : D.cohomology G i) (y : D.cohomology G j) :
    letI := cohomologyGRing μ hdeg hL e he hone_mul hmul_one hassoc
    GradedMonoid.GMul.mul (A := fun i ↦ D.cohomology G i) x y = cohomologyMul μ hdeg hL x y :=
  TauCeti.DirectSum.gRingOfMul_gMul x y

/-- In the cohomology ring, the unit is the class of `e`. -/
@[simp]
theorem cohomologyGRing_gOne :
    letI := cohomologyGRing μ hdeg hL e he hone_mul hmul_one hassoc
    GradedMonoid.GOne.one (A := fun i ↦ D.cohomology G i) = Submodule.Quotient.mk ⟨e, he⟩ :=
  TauCeti.DirectSum.gRingOfMul_gOne

/-- In the cohomology ring, the product of the classes of two cocycles `a` and `b` is the class of
`μ a b`. -/
theorem cohomologyGRing_of_mk_mul_of_mk {i j : ℤ} (a : D.cocycles G i) (b : D.cocycles G j) :
    letI := cohomologyGRing μ hdeg hL e he hone_mul hmul_one hassoc
    of (fun i ↦ D.cohomology G i) i (Submodule.Quotient.mk a) * of _ j (Submodule.Quotient.mk b) =
      of (fun i ↦ D.cohomology G i) (i + j)
        (Submodule.Quotient.mk
          ⟨μ a b, apply_mem_cocycles_add μ hdeg hL a.property b.property⟩) := by
  let := cohomologyGRing μ hdeg hL e he hone_mul hmul_one hassoc
  rw [of_mul_of, cohomologyGRing_gMul, cohomologyMul_mk]

/-- The unit of the cohomology ring is the class of `e`, in degree zero. -/
theorem cohomologyGRing_one :
    letI := cohomologyGRing μ hdeg hL e he hone_mul hmul_one hassoc
    (1 : ⨁ i, D.cohomology G i) =
      of (fun i ↦ D.cohomology G i) 0 (Submodule.Quotient.mk ⟨e, he⟩) := by
  let := cohomologyGRing μ hdeg hL e he hone_mul hmul_one hassoc
  rw [one_def, cohomologyGRing_gOne]

/-- Multiplying on the left by a scalar multiple `r • [e]` of the unit is scalar multiplication by
`r`, as elements of the graded monoid of cohomology classes. -/
theorem cohomologyGRing_smul_one_mul (r : R) (x : GradedMonoid fun i ↦ D.cohomology G i) :
    letI := cohomologyGRing μ hdeg hL e he hone_mul hmul_one hassoc
    GradedMonoid.mk 0 (r • Submodule.Quotient.mk ⟨e, he⟩ : D.cohomology G 0) * x =
      ⟨x.1, r • x.2⟩ := by
  obtain ⟨i, x⟩ := x
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
  refine (congrArg (GradedMonoid.mk _) (cohomologyMul_mk μ hdeg hL _ a)).trans
    (gradedMonoid_mk_cohomology_mk_eq (zero_add i) ?_)
  simpa only [Submodule.coe_smul, map_smul, LinearMap.smul_apply, smul_sub] using
    Submodule.smul_mem _ r (hone_mul a.property)

/-- Multiplying on the right by a scalar multiple `r • [e]` of the unit is scalar multiplication
by `r`, as elements of the graded monoid of cohomology classes. -/
theorem cohomologyGRing_mul_smul_one (r : R) (x : GradedMonoid fun i ↦ D.cohomology G i) :
    letI := cohomologyGRing μ hdeg hL e he hone_mul hmul_one hassoc
    x * GradedMonoid.mk 0 (r • Submodule.Quotient.mk ⟨e, he⟩ : D.cohomology G 0) =
      ⟨x.1, r • x.2⟩ := by
  obtain ⟨i, x⟩ := x
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
  refine (congrArg (GradedMonoid.mk _) (cohomologyMul_mk μ hdeg hL a _)).trans
    (gradedMonoid_mk_cohomology_mk_eq (add_zero i) ?_)
  simpa only [Submodule.coe_smul, map_smul, smul_sub] using Submodule.smul_mem _ r
      (hmul_one a.property)

/-- **The cohomology algebra.** The graded ring `LinearMap.cohomologyGRing` is a graded
`R`-algebra, with structure map `r ↦ r • [e]` into degree zero. -/
@[expose, instance_reducible]
def cohomologyGAlgebra :
    @DirectSum.GAlgebra ℤ R (fun i ↦ D.cohomology G i) _ _ _ _
      (cohomologyGRing μ hdeg hL e he hone_mul hmul_one hassoc).toGSemiring :=
  letI := cohomologyGRing μ hdeg hL e he hone_mul hmul_one hassoc
  { toFun :=
      { toFun r := r • Submodule.Quotient.mk ⟨e, he⟩
        map_zero' := zero_smul R _
        map_add' r s := add_smul r s _ }
    map_one := one_smul R _
    map_mul r s := by
      refine (congrArg (GradedMonoid.mk 0) (mul_smul r s _)).trans ?_
      exact (cohomologyGRing_smul_one_mul μ hdeg hL e he hone_mul hmul_one hassoc r
        (GradedMonoid.mk 0 (s • Submodule.Quotient.mk ⟨e, he⟩))).symm
    commutes r x := (cohomologyGRing_smul_one_mul μ hdeg hL e he hone_mul hmul_one hassoc r x).trans
      (cohomologyGRing_mul_smul_one μ hdeg hL e he hone_mul hmul_one hassoc r x).symm
    smul_def r x :=
      (cohomologyGRing_smul_one_mul μ hdeg hL e he hone_mul hmul_one hassoc r x).symm }

/-- The structure map of `LinearMap.cohomologyGAlgebra` is `r ↦ r • [e]`. -/
@[simp]
theorem cohomologyGAlgebra_toFun (r : R) :
    letI := cohomologyGRing μ hdeg hL e he hone_mul hmul_one hassoc
    (cohomologyGAlgebra μ hdeg hL e he hone_mul hmul_one hassoc).toFun r =
      r • Submodule.Quotient.mk ⟨e, he⟩ :=
  rfl

/-- **Graded commutativity of the cohomology ring.** If `μ a b - (-1)^(i j) μ b a` is a coboundary
for all cocycles `a` and `b` of degrees `i` and `j`, then in the cohomology ring
`x y = (-1)^(i j) y x` for classes `x` and `y` of degrees `i` and `j`. -/
theorem cohomologyGRing_of_mul_of_comm
    (hcomm : ∀ {i j : ℤ} {a b : M}, a ∈ D.cocycles G i → b ∈ D.cocycles G j →
      μ a b - negOnePowCast R (i * j) • μ b a ∈ D.coboundaries G (i + j))
    {i j : ℤ} (x : D.cohomology G i) (y : D.cohomology G j) :
    letI := cohomologyGRing μ hdeg hL e he hone_mul hmul_one hassoc
    of (fun i ↦ D.cohomology G i) i x * of (fun i ↦ D.cohomology G i) j y =
      negOnePowCast R (i * j) •
        (of (fun i ↦ D.cohomology G i) j y * of (fun i ↦ D.cohomology G i) i x) := by
  let := cohomologyGRing μ hdeg hL e he hone_mul hmul_one hassoc
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  induction y using Submodule.Quotient.induction_on with | H b => ?_
  simp only [of_mul_of, ← of_smul, cohomologyGRing_gMul, cohomologyMul_mk,
    ← Submodule.Quotient.mk_smul]
  refine of_eq_of_gradedMonoid_eq (gradedMonoid_mk_cohomology_mk_eq (add_comm i j) ?_)
  simpa only [add_comm i j, SetLike.mk_smul_mk] using hcomm a.property b.property

end GRing

section AlgHom

variable {N : Type*} [AddCommGroup N] [Module R N] {E : N →ₗ[R] N} {H : ℤ → Submodule R N}
  (μ : M →ₗ[R] M →ₗ[R] M)
  (hμdeg : ∀ {i j : ℤ} {a b : M}, a ∈ G i → b ∈ G j → μ a b ∈ G (i + j))
  (hμL : ∀ {i : ℤ} {a : M}, a ∈ G i → ∀ b, D (μ a b) = μ (D a) b + negOnePowCast R i • μ a (D b))
  (e : M) (he : e ∈ D.cocycles G 0)
  (hμone_mul : ∀ {i : ℤ} {a : M}, a ∈ D.cocycles G i → μ e a - a ∈ D.coboundaries G i)
  (hμmul_one : ∀ {i : ℤ} {a : M}, a ∈ D.cocycles G i → μ a e - a ∈ D.coboundaries G i)
  (hμassoc : ∀ {i j k : ℤ} {a b c : M}, a ∈ D.cocycles G i → b ∈ D.cocycles G j →
    c ∈ D.cocycles G k → μ (μ a b) c - μ a (μ b c) ∈ D.coboundaries G (i + j + k))
  (ν : N →ₗ[R] N →ₗ[R] N)
  (hνdeg : ∀ {i j : ℤ} {a b : N}, a ∈ H i → b ∈ H j → ν a b ∈ H (i + j))
  (hνL : ∀ {i : ℤ} {a : N}, a ∈ H i → ∀ b, E (ν a b) = ν (E a) b + negOnePowCast R i • ν a (E b))
  (e' : N) (he' : e' ∈ E.cocycles H 0)
  (hνone_mul : ∀ {i : ℤ} {a : N}, a ∈ E.cocycles H i → ν e' a - a ∈ E.coboundaries H i)
  (hνmul_one : ∀ {i : ℤ} {a : N}, a ∈ E.cocycles H i → ν a e' - a ∈ E.coboundaries H i)
  (hνassoc : ∀ {i j k : ℤ} {a b c : N}, a ∈ E.cocycles H i → b ∈ E.cocycles H j →
    c ∈ E.cocycles H k → ν (ν a b) c - ν a (ν b c) ∈ E.coboundaries H (i + j + k))
  (f : M →ₗ[R] N) (hfdeg : ∀ {i : ℤ} {a : M}, a ∈ G i → f a ∈ H i)
  (hfD : ∀ {i : ℤ} {a : M}, a ∈ G i → E (f a) = f (D a))
  (hfmul : ∀ {i j : ℤ} {a b : M}, a ∈ D.cocycles G i → b ∈ D.cocycles G j →
    f (μ a b) - ν (f a) (f b) ∈ E.coboundaries H (i + j))
  (hfone : f e - e' ∈ E.coboundaries H 0)

include he he' hμone_mul hνdeg hνL hνmul_one hfmul in
/-- **A multiplicative map onto degree-zero cohomology preserves the unit.** Let `f` be a
degree-preserving linear map commuting with the endomorphisms such that `f (μ a b) - ν (f a) (f b)`
is a coboundary for all cocycles `a` and `b`, where `e` is a left unit of `μ` and `e'` a right unit
of `ν` up to coboundaries. If the map induced by `f` on degree-zero cohomology is onto, then
`f e - e'` is a coboundary: if `[f a] = [e']`, then
`[f e] = [f e] [e'] = [f e] [f a] = [f (μ e a)] = [f a] = [e']`. -/
theorem sub_mem_coboundaries_of_surjective_cohomologyMap
    (hsurj : Function.Surjective (cohomologyMap (G₁ := G) (G₀ := H) f hfdeg hfD 0)) :
    f e - e' ∈ E.coboundaries H 0 := by
  obtain ⟨x, hx⟩ := hsurj (Submodule.Quotient.mk ⟨e', he'⟩)
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  rw [cohomologyMap_mk, cohomology_mk_eq_mk_iff] at hx
  have hfe := apply_mem_cocycles_of_mem_cocycles f hfdeg hfD he
  -- `ν (f e) (f a - e')` is the product of a cocycle and a coboundary.
  have hprod : ν (f e) (f a - e') ∈ E.coboundaries H 0 :=
    apply_mem_coboundaries_of_right ν (apply_mem_add_zero ν hνdeg) hνL (by norm_num) hfe hx
  have hmul : f (μ e a) - ν (f e) (f a) ∈ E.coboundaries H 0 := by
    simpa only [add_zero] using hfmul he a.property
  have hone : f (μ e a - a) ∈ E.coboundaries H 0 :=
    apply_mem_coboundaries_of_mem_coboundaries f hfdeg hfD (hμone_mul a.property)
  have heq : f e - e' = -(ν (f e) e' - f e) - ν (f e) (f a - e') -
      (f (μ e a) - ν (f e) (f a)) + f (μ e a - a) + (f a - e') := by
    simp only [map_sub]
    abel
  rw [heq]
  exact add_mem (add_mem (sub_mem (sub_mem (neg_mem (hνmul_one hfe)) hprod) hmul) hone) hx

/-- **The algebra homomorphism of cohomology rings induced by a multiplicative map.** Let `f` be a
degree-preserving linear map commuting with the endomorphisms. If `f (μ a b) - ν (f a) (f b)` is a
coboundary for all cocycles `a` and `b`, and `f e - e'` is a coboundary, then the maps
`LinearMap.cohomologyMap f` induced in each degree form an `R`-algebra homomorphism between the
cohomology rings of `μ` and `ν`. -/
def cohomologyAlgHom :
    letI := cohomologyGRing μ hμdeg hμL e he hμone_mul hμmul_one hμassoc
    letI := cohomologyGAlgebra μ hμdeg hμL e he hμone_mul hμmul_one hμassoc
    letI := cohomologyGRing ν hνdeg hνL e' he' hνone_mul hνmul_one hνassoc
    letI := cohomologyGAlgebra ν hνdeg hνL e' he' hνone_mul hνmul_one hνassoc
    (⨁ i, D.cohomology G i) →ₐ[R] ⨁ i, E.cohomology H i :=
  letI := cohomologyGRing μ hμdeg hμL e he hμone_mul hμmul_one hμassoc
  letI := cohomologyGAlgebra μ hμdeg hμL e he hμone_mul hμmul_one hμassoc
  letI := cohomologyGRing ν hνdeg hνL e' he' hνone_mul hνmul_one hνassoc
  letI := cohomologyGAlgebra ν hνdeg hνL e' he' hνone_mul hνmul_one hνassoc
  toAlgebra R _ (fun i ↦ (lof R ℤ (fun i ↦ E.cohomology H i) i).comp (cohomologyMap f hfdeg hfD i))
    (by
      simp only [comp_apply, one_def, cohomologyGRing_gOne, cohomologyMap_mk, lof_eq_of]
      exact congrArg _ (cohomology_mk_eq_mk_iff.2 hfone))
    (fun {i j} x y ↦ by
      simp only [comp_apply, lof_eq_of, of_mul_of, cohomologyGRing_gMul,
        cohomologyMul_eq_cohomologyProduct]
      apply congrArg
      exact cohomologyMap_cohomologyProduct (hμdeg := apply_mem_add_zero μ hμdeg)
        (hνdeg := apply_mem_add_zero ν hνdeg) (add_zero (i + j)) (fun ha hb ↦ hfmul ha hb) x y)

/-- The algebra homomorphism of cohomology rings acts in each degree as the map induced by `f`. -/
@[simp]
theorem cohomologyAlgHom_of {i : ℤ} (x : D.cohomology G i) :
    cohomologyAlgHom μ hμdeg hμL e he hμone_mul hμmul_one hμassoc ν hνdeg hνL e' he' hνone_mul
        hνmul_one hνassoc f hfdeg hfD hfmul hfone (of _ i x) =
      of (fun i ↦ E.cohomology H i) i (cohomologyMap f hfdeg hfD i x) := by
  let := cohomologyGRing μ hμdeg hμL e he hμone_mul hμmul_one hμassoc
  let := cohomologyGRing ν hνdeg hνL e' he' hνone_mul hνmul_one hνassoc
  rw [cohomologyAlgHom, toAlgebra_apply]
  exact (toSemiring_of _ _ _ i x).trans (lof_eq_of R _ _ i _)

/-- As a linear map, the algebra homomorphism of cohomology rings is the direct sum of the maps
induced by `f` in each degree. -/
theorem cohomologyAlgHom_toLinearMap :
    letI := cohomologyGRing μ hμdeg hμL e he hμone_mul hμmul_one hμassoc
    letI := cohomologyGAlgebra μ hμdeg hμL e he hμone_mul hμmul_one hμassoc
    letI := cohomologyGRing ν hνdeg hνL e' he' hνone_mul hνmul_one hνassoc
    letI := cohomologyGAlgebra ν hνdeg hνL e' he' hνone_mul hνmul_one hνassoc
    (cohomologyAlgHom μ hμdeg hμL e he hμone_mul hμmul_one hμassoc ν hνdeg hνL e' he' hνone_mul
        hνmul_one hνassoc f hfdeg hfD hfmul hfone).toLinearMap =
      lmap fun i ↦ cohomologyMap (G₁ := G) (G₀ := H) f hfdeg hfD i :=
  linearMap_ext R fun i ↦ LinearMap.ext fun x ↦ by simp [lof_eq_of]

/-- **The algebra isomorphism of cohomology rings induced by a multiplicative map.** Let `f` be a
degree-preserving linear map commuting with the endomorphisms such that `f (μ a b) - ν (f a) (f b)`
is a coboundary for all cocycles `a` and `b`. If the map induced by `f` on cohomology is bijective
in every degree, then the maps it induces form an isomorphism of `R`-algebras between the
cohomology rings of `μ` and `ν`. No condition on the units is needed: it follows from
surjectivity in degree zero (`LinearMap.sub_mem_coboundaries_of_surjective_cohomologyMap`). -/
def cohomologyAlgEquiv
    (hbij : ∀ i, Function.Bijective (cohomologyMap (G₁ := G) (G₀ := H) f hfdeg hfD i)) :
    letI := cohomologyGRing μ hμdeg hμL e he hμone_mul hμmul_one hμassoc
    letI := cohomologyGAlgebra μ hμdeg hμL e he hμone_mul hμmul_one hμassoc
    letI := cohomologyGRing ν hνdeg hνL e' he' hνone_mul hνmul_one hνassoc
    letI := cohomologyGAlgebra ν hνdeg hνL e' he' hνone_mul hνmul_one hνassoc
    (⨁ i, D.cohomology G i) ≃ₐ[R] ⨁ i, E.cohomology H i :=
  letI := cohomologyGRing μ hμdeg hμL e he hμone_mul hμmul_one hμassoc
  letI := cohomologyGAlgebra μ hμdeg hμL e he hμone_mul hμmul_one hμassoc
  letI := cohomologyGRing ν hνdeg hνL e' he' hνone_mul hνmul_one hνassoc
  letI := cohomologyGAlgebra ν hνdeg hνL e' he' hνone_mul hνmul_one hνassoc
  AlgEquiv.ofBijective (cohomologyAlgHom μ hμdeg hμL e he hμone_mul hμmul_one hμassoc ν hνdeg hνL
    e' he' hνone_mul hνmul_one hνassoc f hfdeg hfD hfmul
    (sub_mem_coboundaries_of_surjective_cohomologyMap μ e he hμone_mul ν hνdeg hνL e' he' hνmul_one
      f hfdeg hfD hfmul (hbij 0).2)) <| by
    -- The homomorphism is the direct sum of the degreewise maps, which are bijective.
    rw [← AlgHom.coe_toLinearMap, cohomologyAlgHom_toLinearMap]
    exact ⟨lmap_injective _ |>.2 fun i ↦ (hbij i).1, lmap_surjective _ |>.2 fun i ↦ (hbij i).2⟩

/-- The algebra isomorphism of cohomology rings acts in each degree as the map induced by `f`. -/
@[simp]
theorem cohomologyAlgEquiv_of
    (hbij : ∀ i, Function.Bijective (cohomologyMap (G₁ := G) (G₀ := H) f hfdeg hfD i))
    {i : ℤ} (x : D.cohomology G i) :
    cohomologyAlgEquiv μ hμdeg hμL e he hμone_mul hμmul_one hμassoc ν hνdeg hνL e' he' hνone_mul
        hνmul_one hνassoc f hfdeg hfD hfmul hbij (of _ i x) =
      of (fun i ↦ E.cohomology H i) i (cohomologyMap f hfdeg hfD i x) :=
  cohomologyAlgHom_of μ hμdeg hμL e he hμone_mul hμmul_one hμassoc ν hνdeg hνL e' he' hνone_mul
    hνmul_one hνassoc f hfdeg hfD hfmul
    (sub_mem_coboundaries_of_surjective_cohomologyMap μ e he hμone_mul ν hνdeg hνL e' he' hνmul_one
      f hfdeg hfD hfmul (hbij 0).2) x

end AlgHom

section Homotopy

variable (μ : M →ₗ[R] M →ₗ[R] M)
  (hμdeg : ∀ {i j : ℤ} {a b : M}, a ∈ G i → b ∈ G j → μ a b ∈ G (i + j))
  (hμL : ∀ {i : ℤ} {a : M}, a ∈ G i → ∀ b, D (μ a b) = μ (D a) b + negOnePowCast R i • μ a (D b))
  (e : M) (he : e ∈ D.cocycles G 0)
  (hμone_mul : ∀ {i : ℤ} {a : M}, a ∈ D.cocycles G i → μ e a - a ∈ D.coboundaries G i)
  (hμmul_one : ∀ {i : ℤ} {a : M}, a ∈ D.cocycles G i → μ a e - a ∈ D.coboundaries G i)
  (hμassoc : ∀ {i j k : ℤ} {a b c : M}, a ∈ D.cocycles G i → b ∈ D.cocycles G j →
    c ∈ D.cocycles G k → μ (μ a b) c - μ a (μ b c) ∈ D.coboundaries G (i + j + k))
  (ν : M →ₗ[R] M →ₗ[R] M)
  (hνdeg : ∀ {i j : ℤ} {a b : M}, a ∈ G i → b ∈ G j → ν a b ∈ G (i + j))
  (hνL : ∀ {i : ℤ} {a : M}, a ∈ G i → ∀ b, D (ν a b) = ν (D a) b + negOnePowCast R i • ν a (D b))
  (e' : M) (he' : e' ∈ D.cocycles G 0)
  (hνone_mul : ∀ {i : ℤ} {a : M}, a ∈ D.cocycles G i → ν e' a - a ∈ D.coboundaries G i)
  (hνmul_one : ∀ {i : ℤ} {a : M}, a ∈ D.cocycles G i → ν a e' - a ∈ D.coboundaries G i)
  (hνassoc : ∀ {i j k : ℤ} {a b c : M}, a ∈ D.cocycles G i → b ∈ D.cocycles G j →
    c ∈ D.cocycles G k → ν (ν a b) c - ν a (ν b c) ∈ D.coboundaries G (i + j + k))
  (hμν : ∀ {i j : ℤ} {a b : M}, a ∈ D.cocycles G i → b ∈ D.cocycles G j →
    μ a b - ν a b ∈ D.coboundaries G (i + j))

include hμν in
/-- **Homotopic products induce the same product on cohomology.** If two products `μ` and `ν` of
degree zero obeying the Leibniz rule differ by a coboundary on every pair of cocycles, then they
induce the same product `H^i × H^j → H^(i + j)`. -/
theorem cohomologyMul_eq_of_sub_mem_coboundaries {i j : ℤ} (x : D.cohomology G i)
    (y : D.cohomology G j) :
    cohomologyMul μ hμdeg hμL x y = cohomologyMul ν hνdeg hνL x y := by
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  induction y using Submodule.Quotient.induction_on with | H b => ?_
  rw [cohomologyMul_mk, cohomologyMul_mk, cohomology_mk_eq_mk_iff]
  exact hμν a.property b.property

include he he' hμone_mul hνdeg hνL hνmul_one hμν in
/-- **Homotopic products have cohomologous units.** If `μ` and `ν` differ by a coboundary on every
pair of cocycles, `e` is a left unit of `μ` and `e'` a right unit of `ν` up to coboundaries, then
`e - e'` is a coboundary. -/
theorem sub_mem_coboundaries_of_mul_sub_mem_coboundaries : e - e' ∈ D.coboundaries G 0 :=
  sub_mem_coboundaries_of_surjective_cohomologyMap μ e he hμone_mul ν hνdeg hνL e' he' hνmul_one
    LinearMap.id (fun ha ↦ ha) (fun _ ↦ rfl) hμν
    (by rw [cohomologyMap_id]; exact Function.surjective_id)

/-- **The cohomology ring is determined by its product and unit.** If the products `μ` and `ν`
induce the same product on cohomology, and the units `e` and `e'` have the same class, then the
graded ring structures `LinearMap.cohomologyGRing` of `μ` and `ν` are equal. -/
theorem cohomologyGRing_congr
    (hmul : ∀ i j : ℤ, cohomologyMul μ hμdeg hμL (i := i) (j := j) = cohomologyMul ν hνdeg hνL)
    (hone : (Submodule.Quotient.mk ⟨e, he⟩ : D.cohomology G 0) = Submodule.Quotient.mk ⟨e', he'⟩) :
    cohomologyGRing μ hμdeg hμL e he hμone_mul hμmul_one hμassoc =
      cohomologyGRing ν hνdeg hνL e' he' hνone_mul hνmul_one hνassoc :=
  -- Both are `TauCeti.DirectSum.gRingOfMul` of the product and the unit class; the remaining
  -- arguments are proofs.
  TauCeti.DirectSum.gRingOfMul_congr (funext₂ fun i j ↦ by rw [hmul i j]) hone

include hμν in
/-- **Homotopic products give the same cohomology ring.** If two products `μ` and `ν` of degree
zero, each associative and unital up to coboundaries on cocycles, differ by a coboundary on every
pair of cocycles, then their cohomology rings are the same graded ring structure on the degree-wise
cohomology: the products agree (`LinearMap.cohomologyMul_eq_of_sub_mem_coboundaries`), and so do
the units, the classes of `e` and `e'`
(`LinearMap.sub_mem_coboundaries_of_mul_sub_mem_coboundaries`). -/
theorem cohomologyGRing_eq_of_sub_mem_coboundaries :
    cohomologyGRing μ hμdeg hμL e he hμone_mul hμmul_one hμassoc =
      cohomologyGRing ν hνdeg hνL e' he' hνone_mul hνmul_one hνassoc := by
  have hone : (Submodule.Quotient.mk ⟨e, he⟩ : D.cohomology G 0) =
      Submodule.Quotient.mk ⟨e', he'⟩ :=
    cohomology_mk_eq_mk_iff.2 (sub_mem_coboundaries_of_mul_sub_mem_coboundaries μ e he hμone_mul ν
      hνdeg hνL e' he' hνmul_one hμν)
  exact cohomologyGRing_congr μ hμdeg hμL e he hμone_mul hμmul_one hμassoc ν hνdeg hνL e' he'
    hνone_mul hνmul_one hνassoc
    (fun i j ↦ LinearMap.ext₂ fun x y ↦
      cohomologyMul_eq_of_sub_mem_coboundaries μ hμdeg hμL ν hνdeg hνL hμν x y) hone

end Homotopy

end LinearMap
