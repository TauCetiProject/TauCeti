/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Cohomology
public import TauCeti.Algebra.Homology.Ginzburg.LoopGrading

/-!
# The zeroth cohomology of the two-dimensional Ginzburg algebra

Let `Q` be a finite quiver and `Π₂(Q)` its non-completed two-dimensional Ginzburg differential
graded algebra (`TauCeti.isDGAlgebra_ginzburgTwoDifferential`).  This file proves

```text
H⁰(Π₂(Q)) ≅ Π_k(Q),
```

the zeroth cohomology algebra of `Π₂(Q)` is the additive preprojective algebra of `Q`, over every
commutative ring `k`.

The inclusion of the doubled path algebra gives a map `Π_k(Q) → H(Π₂(Q))`.  Killing adjoined loops
gives a map in the other direction, from cohomology to `Π_k(Q)`.  These maps identify `Π_k(Q)` with
the degree-zero cohomology.  The path-algebra retraction and its degree-zero characterization are
available in `TauCeti.Algebra.Homology.Ginzburg.LoopGrading`.

## Main definitions

* `TauCeti.preprojectiveToGinzburgTwoCohomology`: the algebra homomorphism `Π_k(Q) → H(Π₂(Q))`.
* `TauCeti.ginzburgTwoCohomologyToPreprojective`: the algebra homomorphism `H(Π₂(Q)) → Π_k(Q)`.
* `TauCeti.preprojectiveEquivGinzburgTwoCohomologyZero`: **the isomorphism
  `Π_k(Q) ≃ H⁰(Π₂(Q))`**.

## Main results

* `TauCeti.preprojectiveMk_ginzburgRetraction_ginzburgTwoDifferential`: every boundary of
  `Π₂(Q)` vanishes in `Π_k(Q)` once the loops are killed.
* `TauCeti.ginzburgTwoCohomologyToPreprojective_preprojectiveToGinzburgTwoCohomology`: the two maps
  compose to the identity of `Π_k(Q)`.
* `TauCeti.mem_range_preprojectiveToGinzburgTwoCohomology_iff`: the image of `Π_k(Q)` is the
  degree-zero cohomology.

## References

* V. Ginzburg, *Calabi--Yau algebras*, Section 4.2.
* B. Keller, *Deformed Calabi--Yau completions*, Section 6.5.
* T. Etgü and Y. Lekili, *Koszul duality patterns in Floer theory*, Section 4.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w



/-! ### Boundaries vanish in the preprojective algebra -/

section Boundaries

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- The prescribed differential of every Ginzburg arrow vanishes in `Π_k(Q)` once the loops are
killed: it is zero on a doubled arrow and the relator `ρ_i` on the loop `t_i`. -/
private theorem preprojectiveMk_ginzburgRetraction_ginzburgTwoArrowRelator
    {i j : Q} (e : GinzburgHom Q i j) :
    preprojectiveMk k Q (ginzburgRetraction k (ginzburgTwoArrowRelator k e)) = 0 := by
  cases e with
  | double a => rw [ginzburgTwoArrowRelator_double, map_zero, map_zero]
  | loop =>
    rw [ginzburgTwoArrowRelator_loop, ginzburgRetraction_ginzburgMap,
      preprojectiveMk_localPreprojectiveRelator]

/-- **Every boundary of `Π₂(Q)` vanishes in `Π_k(Q)` once the loops are killed.** -/
theorem preprojectiveMk_ginzburgRetraction_ginzburgTwoDifferential
    (x : pathAlgebra k (GinzburgQuiver Q)) :
    preprojectiveMk k Q (ginzburgRetraction k (ginzburgTwoDifferential k x)) = 0 := by
  have hpath : ∀ {a b : GinzburgQuiver Q} (p : Path a b),
      preprojectiveMk k Q (ginzburgRetraction k (ginzburgTwoDifferential k (ofPath ⟨a, b, p⟩))) =
        0 := by
    intro a b p
    induction p with
    | nil => rw [← vertexIdempotent_eq_ofPath, ginzburgTwoDifferential_vertexIdempotent,
        map_zero, map_zero]
    | cons p e ih =>
      have he := preprojectiveMk_ginzburgRetraction_ginzburgTwoArrowRelator k e
      rw [← ofArrow_mul_ofPath, ginzburgTwoDifferential_ofArrow_mul, map_add, map_add, map_mul,
        map_mul, he, zero_mul, zero_add, Units.smul_def, map_zsmul, map_zsmul, map_mul, map_mul,
        ih, mul_zero, smul_zero]
  induction x using induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, add_zero]
  | single y c =>
    obtain ⟨a, b, p⟩ := y
    rw [single_eq_smul_ofPath, map_smul, map_smul, map_smul, hpath, smul_zero]

end Boundaries

/-! ### The zeroth cohomology -/

section Cohomology

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- The inclusion of the doubled path algebra as an algebra homomorphism into the cycles of
`Π₂(Q)`, every doubled path being a cycle. -/
private noncomputable def ginzburgMapCycles :
    pathAlgebra k (Symmetrify Q) →ₐ[k] (isDGAlgebra_ginzburgTwoDifferential (Q := Q) k).cycles :=
  (ginzburgMap k).codRestrict _ fun x =>
    (isDGAlgebra_ginzburgTwoDifferential k).mem_cycles.mpr (ginzburgTwoDifferential_ginzburgMap k x)

/-- The algebra homomorphism `Π_k(Q) → H(Π₂(Q))` sending the class of a doubled path to the
cohomology class of the same path, a cycle of `Π₂(Q)`.  It is well defined because the relator
`ρ_i` is the boundary `d t_i`. -/
noncomputable def preprojectiveToGinzburgTwoCohomology :
    preprojectiveAlgebra k Q →ₐ[k] (isDGAlgebra_ginzburgTwoDifferential (Q := Q) k).Cohomology :=
  preprojectiveLiftOfForallLocalPreprojectiveRelator
    ((Ideal.Quotient.mkₐ k _).comp (ginzburgMapCycles k Q)) fun v => by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        ← (isDGAlgebra_ginzburgTwoDifferential k).quotientMk_map_eq_zero
          (ofArrow (GinzburgHom.loop v))]
      exact congrArg _ (Subtype.ext (ginzburgTwoDifferential_ofArrow_loop k v).symm)

/-- The map `Π_k(Q) → H(Π₂(Q))` sends the class of a doubled element to the cohomology class of
its image in the Ginzburg path algebra. -/
@[simp]
theorem preprojectiveToGinzburgTwoCohomology_preprojectiveMk (x : pathAlgebra k (Symmetrify Q)) :
    preprojectiveToGinzburgTwoCohomology k Q (preprojectiveMk k Q x) =
      Ideal.Quotient.mk (isDGAlgebra_ginzburgTwoDifferential k).boundaries.asIdeal
        ⟨ginzburgMap k x,
          (isDGAlgebra_ginzburgTwoDifferential k).mem_cycles.mpr
            (ginzburgTwoDifferential_ginzburgMap k x)⟩ := by
  rw [preprojectiveToGinzburgTwoCohomology,
    preprojectiveLift_of_forall_localPreprojectiveRelator_preprojectiveMk, AlgHom.comp_apply,
    Ideal.Quotient.mkₐ_eq_mk]
  exact congrArg _ (Subtype.ext (AlgHom.coe_codRestrict _ _ _ x))

/-- The algebra homomorphism `H(Π₂(Q)) → Π_k(Q)` sending the class of a cycle to the class of the
doubled element obtained by killing its adjoined loops.  It is well defined by
`TauCeti.preprojectiveMk_ginzburgRetraction_ginzburgTwoDifferential`. -/
noncomputable def ginzburgTwoCohomologyToPreprojective :
    (isDGAlgebra_ginzburgTwoDifferential (Q := Q) k).Cohomology →ₐ[k] preprojectiveAlgebra k Q :=
  Ideal.Quotient.liftₐ _
    (((preprojectiveMk k Q).comp (ginzburgRetraction k)).comp
      (isDGAlgebra_ginzburgTwoDifferential k).cycles.val) fun z hz => by
    obtain ⟨a, ha⟩ := (isDGAlgebra_ginzburgTwoDifferential k).mem_boundaries.mp
      (TwoSidedIdeal.mem_asIdeal.mp hz)
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Subalgebra.coe_val, ← ha]
    exact preprojectiveMk_ginzburgRetraction_ginzburgTwoDifferential k a

/-- The map `H(Π₂(Q)) → Π_k(Q)` sends the class of a cycle to the class of the doubled element
obtained by killing its loops. -/
@[simp]
theorem ginzburgTwoCohomologyToPreprojective_mk
    (z : (isDGAlgebra_ginzburgTwoDifferential (Q := Q) k).cycles) :
    ginzburgTwoCohomologyToPreprojective k Q
        (Ideal.Quotient.mk (isDGAlgebra_ginzburgTwoDifferential k).boundaries.asIdeal z) =
      preprojectiveMk k Q (ginzburgRetraction k z) :=
  Ideal.Quotient.liftₐ_apply _ _ _ _

/-- **`Π_k(Q)` is a retract of `H(Π₂(Q))`**: killing the loops undoes the map
`Π_k(Q) → H(Π₂(Q))`. -/
@[simp]
theorem ginzburgTwoCohomologyToPreprojective_preprojectiveToGinzburgTwoCohomology
    (x : preprojectiveAlgebra k Q) :
    ginzburgTwoCohomologyToPreprojective k Q (preprojectiveToGinzburgTwoCohomology k Q x) = x := by
  obtain ⟨x, rfl⟩ := preprojectiveMk_surjective k Q x
  rw [preprojectiveToGinzburgTwoCohomology_preprojectiveMk,
    ginzburgTwoCohomologyToPreprojective_mk, ginzburgRetraction_ginzburgMap]

/-- The map `Π_k(Q) → H(Π₂(Q))` is injective. -/
theorem preprojectiveToGinzburgTwoCohomology_injective :
    Function.Injective (preprojectiveToGinzburgTwoCohomology k Q) :=
  Function.LeftInverse.injective
    (ginzburgTwoCohomologyToPreprojective_preprojectiveToGinzburgTwoCohomology k Q)

/-- **The image of `Π_k(Q)` in `H(Π₂(Q))` is the degree-zero cohomology.** -/
theorem mem_range_preprojectiveToGinzburgTwoCohomology_iff
    {x : (isDGAlgebra_ginzburgTwoDifferential (Q := Q) k).Cohomology} :
    x ∈ (preprojectiveToGinzburgTwoCohomology k Q).range ↔
      x ∈ (isDGAlgebra_ginzburgTwoDifferential k).cohomologyGrading 0 := by
  rw [AlgHom.mem_range, IsDGAlgebra.mem_cohomologyGrading]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨y, rfl⟩ := preprojectiveMk_surjective k Q y
    exact ⟨_, ginzburgMap_mem_gradeBy_ginzburgTwoDegree k y,
      (preprojectiveToGinzburgTwoCohomology_preprojectiveMk k Q y).symm⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨preprojectiveMk k Q (ginzburgRetraction k z), ?_⟩
    rw [preprojectiveToGinzburgTwoCohomology_preprojectiveMk]
    exact congrArg _ (Subtype.ext (ginzburgMap_ginzburgRetraction_of_mem k hz))

/-- **The zeroth cohomology of the two-dimensional Ginzburg algebra is the preprojective algebra**:
`Π_k(Q) ≃ H⁰(Π₂(Q))` as `k`-algebras, the class of a doubled path going to the cohomology class of
the same path. -/
noncomputable def preprojectiveEquivGinzburgTwoCohomologyZero :
    preprojectiveAlgebra k Q ≃ₐ[k]
      (isDGAlgebra_ginzburgTwoDifferential (Q := Q) k).cohomologyGrading 0 :=
  AlgEquiv.ofBijective
    -- The graded-monoid structure of the cohomology grading is supplied by hand: typeclass search
    -- does not find it within its budget through the quotient grading.
    ((preprojectiveToGinzburgTwoCohomology k Q).codRestrict
      (@SetLike.GradeZero.subalgebra _ _ _ _ _ _ _
        (isDGAlgebra_ginzburgTwoDifferential k).cohomologyGrading
        (IsDGAlgebra.instGradedAlgebraCohomologyGrading _).toGradedMonoid)
      fun x => (mem_range_preprojectiveToGinzburgTwoCohomology_iff k Q).mp ⟨x, rfl⟩)
    ⟨fun _ _ h => preprojectiveToGinzburgTwoCohomology_injective k Q (congrArg Subtype.val h),
      fun z => by
        obtain ⟨x, hx⟩ :=
          (AlgHom.mem_range _).mp ((mem_range_preprojectiveToGinzburgTwoCohomology_iff k Q).mpr z.2)
        exact ⟨x, Subtype.ext hx⟩⟩

/-- The isomorphism `Π_k(Q) ≃ H⁰(Π₂(Q))` agrees with `TauCeti.preprojectiveToGinzburgTwoCohomology`
after forgetting the degree. -/
@[simp]
theorem coe_preprojectiveEquivGinzburgTwoCohomologyZero_apply (x : preprojectiveAlgebra k Q) :
    (preprojectiveEquivGinzburgTwoCohomologyZero k Q x :
        (isDGAlgebra_ginzburgTwoDifferential (Q := Q) k).Cohomology) =
      preprojectiveToGinzburgTwoCohomology k Q x := by
  -- `AlgEquiv.ofBijective` applies the homomorphism it is given, and `AlgHom.codRestrict` keeps the
  -- underlying element; `AlgEquiv.coe_ofBijective` cannot be used by rewriting, because the
  -- degree-zero piece and `SetLike.GradeZero.subalgebra` agree only up to unfolding.
  unfold preprojectiveEquivGinzburgTwoCohomologyZero
  rfl

/-- The inverse of `Π_k(Q) ≃ H⁰(Π₂(Q))` is
`TauCeti.ginzburgTwoCohomologyToPreprojective` on degree-zero classes. -/
theorem preprojectiveEquivGinzburgTwoCohomologyZero_symm_apply
    (z : (isDGAlgebra_ginzburgTwoDifferential (Q := Q) k).cohomologyGrading 0) :
    (preprojectiveEquivGinzburgTwoCohomologyZero k Q).symm z =
      ginzburgTwoCohomologyToPreprojective k Q z := by
  obtain ⟨x, rfl⟩ := (preprojectiveEquivGinzburgTwoCohomologyZero k Q).surjective z
  rw [AlgEquiv.symm_apply_apply, coe_preprojectiveEquivGinzburgTwoCohomologyZero_apply,
    ginzburgTwoCohomologyToPreprojective_preprojectiveToGinzburgTwoCohomology]

end Cohomology

end TauCeti
