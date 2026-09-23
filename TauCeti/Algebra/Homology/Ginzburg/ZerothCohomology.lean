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

The comparison is made by two algebra homomorphisms.  Killing every adjoined loop `t_i` is an
algebra homomorphism `TauCeti.ginzburgRetraction` from the Ginzburg path algebra onto the doubled
path algebra, a retraction of the inclusion `TauCeti.ginzburgMap`; on cohomological degree `0`,
which is spanned by the loop-free paths, it is inverse to that inclusion.  Composed with the
quotient map onto `Π_k(Q)` it kills every boundary, because the differential of a path is a sum
of terms each of which either contains a loop or contains a relator `d t_i = ρ_i`.  It therefore
descends to an algebra homomorphism `H(Π₂(Q)) → Π_k(Q)`.  In the other direction the inclusion
sends the relators `ρ_i = d t_i` to boundaries, so descends to an algebra homomorphism
`Π_k(Q) → H(Π₂(Q))`, whose image is the degree-zero part.  The first map is a left inverse of the
second, which gives the isomorphism onto `H⁰`.

The retraction is built through the universal property `TauCeti.PathAlgebra.liftAlgHom` in the same
way as `TauCeti.PathAlgebra.symmetrifyRetraction`, which kills the formal reverses of a doubled
quiver.

## Main definitions

* `TauCeti.ginzburgRetraction`: the algebra homomorphism from the Ginzburg path algebra to the
  doubled path algebra killing the adjoined loops.
* `TauCeti.preprojectiveToGinzburgTwoCohomology`: the algebra homomorphism `Π_k(Q) → H(Π₂(Q))`.
* `TauCeti.ginzburgTwoCohomologyToPreprojective`: the algebra homomorphism `H(Π₂(Q)) → Π_k(Q)`.
* `TauCeti.preprojectiveEquivGinzburgTwoCohomologyZero`: **the isomorphism
  `Π_k(Q) ≃ H⁰(Π₂(Q))`**.

## Main results

* `TauCeti.ginzburgRetraction_comp_ginzburgMap`: the retraction is a left inverse of the inclusion
  of the doubled path algebra, and `TauCeti.ginzburgMap_ginzburgRetraction_of_mem` says that it is
  a right inverse on cohomological degree `0`; so `TauCeti.mem_gradeBy_ginzburgTwoDegree_zero_iff`
  says that degree `0` is exactly the image of the doubled path algebra.
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

/-! ### Killing the adjoined loops -/

section Retraction

variable (k : Type w) {Q : Type u} [CommSemiring k] [Quiver.{v} Q]

/-- The image in the doubled path algebra of an arrow of the Ginzburg quiver: the same arrow when
it is a doubled arrow, and zero when it is an adjoined loop. -/
private noncomputable def ginzburgRetractArrow :
    {a b : Q} → GinzburgHom Q a b → pathAlgebra k (Symmetrify Q)
  | _, _, .double e => ofArrow (Q := Symmetrify Q) e
  | _, _, .loop _ => 0

/-- The image in the doubled path algebra of a path of the Ginzburg quiver: the same path when it
uses no adjoined loop, and zero once it does. -/
private noncomputable def ginzburgRetractPath :
    {a b : GinzburgQuiver Q} → Path a b → pathAlgebra k (Symmetrify Q)
  | a, _, .nil => vertexIdempotent (Q := Symmetrify Q) k a
  | _, _, .cons p e => ginzburgRetractArrow k e * ginzburgRetractPath p

-- The vertices of a Ginzburg arrow are terms of `Q`, which the doubled path algebra reads as
-- vertices of `Quiver.Symmetrify Q`; rewriting cannot see through that synonym, so the corner
-- identities of a doubled arrow are supplied below as terms with their quiver named.
/-- The image of a Ginzburg arrow lies in the corner of its target. -/
private theorem vertexIdempotent_mul_ginzburgRetractArrow {a b : Q} (e : GinzburgHom Q a b) :
    vertexIdempotent (Q := Symmetrify Q) k b * ginzburgRetractArrow k e =
      ginzburgRetractArrow k e := by
  cases e with
  | double e =>
    rw [ginzburgRetractArrow]
    exact (congrArg _ (ofArrow_eq_ofPath (Q := Symmetrify Q) e)).trans
      ((vertexIdempotent_mul_ofPath (k := k) (Q := Symmetrify Q)
        (Hom.toPath (V := Symmetrify Q) e)).trans (ofArrow_eq_ofPath (Q := Symmetrify Q) e).symm)
  | loop => rw [ginzburgRetractArrow, mul_zero]

/-- The image of a Ginzburg arrow lies in the corner of its source. -/
private theorem ginzburgRetractArrow_mul_vertexIdempotent {a b : Q} (e : GinzburgHom Q a b) :
    ginzburgRetractArrow k e * vertexIdempotent (Q := Symmetrify Q) k a =
      ginzburgRetractArrow k e := by
  cases e with
  | double e =>
    rw [ginzburgRetractArrow]
    exact (congrArg (· * _) (ofArrow_eq_ofPath (Q := Symmetrify Q) e)).trans
      ((ofPath_mul_vertexIdempotent (k := k) (Q := Symmetrify Q)
        (Hom.toPath (V := Symmetrify Q) e)).trans (ofArrow_eq_ofPath (Q := Symmetrify Q) e).symm)
  | loop => rw [ginzburgRetractArrow, zero_mul]

/-- The image of a Ginzburg path lies in the corner of its target. -/
private theorem vertexIdempotent_mul_ginzburgRetractPath {a b : GinzburgQuiver Q} (p : Path a b) :
    vertexIdempotent (Q := Symmetrify Q) k b * ginzburgRetractPath k p =
      ginzburgRetractPath k p := by
  cases p with
  | nil =>
    rw [ginzburgRetractPath]
    exact vertexIdempotent_mul_self (k := k) (Q := Symmetrify Q) _
  | cons p e =>
    rw [ginzburgRetractPath, ← mul_assoc]
    exact congrArg (· * _) (vertexIdempotent_mul_ginzburgRetractArrow k e)

/-- The image of a Ginzburg path lies in the corner of its source. -/
private theorem ginzburgRetractPath_mul_vertexIdempotent {a b : GinzburgQuiver Q} (p : Path a b) :
    ginzburgRetractPath k p * vertexIdempotent (Q := Symmetrify Q) k a =
      ginzburgRetractPath k p := by
  induction p with
  | nil =>
    rw [ginzburgRetractPath]
    exact vertexIdempotent_mul_self (k := k) (Q := Symmetrify Q) _
  | cons p e ih => rw [ginzburgRetractPath, mul_assoc, ih]

/-- Concatenation of Ginzburg paths becomes multiplication, later factor first. -/
private theorem ginzburgRetractPath_comp {a b c : GinzburgQuiver Q} (p : Path a b)
    (q : Path c a) :
    ginzburgRetractPath k p * ginzburgRetractPath k q = ginzburgRetractPath k (q.comp p) := by
  induction p with
  | nil => rw [Path.comp_nil, ginzburgRetractPath, vertexIdempotent_mul_ginzburgRetractPath]
  | cons p e ih => rw [Path.comp_cons, ginzburgRetractPath, ginzburgRetractPath, mul_assoc, ih]

/-- A doubled path, viewed in the Ginzburg quiver, goes back to itself. -/
private theorem ginzburgRetractPath_mapPath {a b : Symmetrify Q} (p : Path a b) :
    ginzburgRetractPath k (ginzburgOf.mapPath p) = ofPath ⟨a, b, p⟩ := by
  induction p with
  | nil =>
    rw [Prefunctor.mapPath_nil, ginzburgRetractPath]
    exact vertexIdempotent_eq_ofPath (Q := Symmetrify Q) k a
  | cons p e ih =>
    rw [Prefunctor.mapPath_cons, ginzburgRetractPath, ih]
    exact ofArrow_mul_ofPath e p

variable [Finite Q]

private theorem ginzburgRetractPath_hzero {x y : Quiver.TotalPath (GinzburgQuiver Q)}
    (h : y.2.1 ≠ x.1) :
    ginzburgRetractPath k x.2.2 * ginzburgRetractPath k y.2.2 = 0 := by
  rw [← ginzburgRetractPath_mul_vertexIdempotent k x.2.2,
    ← vertexIdempotent_mul_ginzburgRetractPath k y.2.2, mul_assoc,
    ← mul_assoc (vertexIdempotent (Q := Symmetrify Q) k x.1),
    vertexIdempotent_mul_vertexIdempotent_of_ne (Q := Symmetrify Q) (Ne.symm h), zero_mul,
    mul_zero]

private theorem ginzburgRetractPath_hone :
    letI := Fintype.ofFinite (GinzburgQuiver Q)
    ∑ v : GinzburgQuiver Q, ginzburgRetractPath k (Path.nil : Path v v) = 1 := by
  let _ := Fintype.ofFinite (Symmetrify Q)
  exact (Finset.sum_congr rfl fun v _ => by rw [ginzburgRetractPath]).trans
    (one_def (k := k) (Q := Symmetrify Q)).symm

/-- The algebra homomorphism from the Ginzburg path algebra to the doubled path algebra which fixes
the vertex idempotents and the doubled arrows and kills every adjoined loop `t_i`.  A Ginzburg path
goes to itself when it uses no loop, and to zero otherwise. -/
noncomputable def ginzburgRetraction :
    pathAlgebra k (GinzburgQuiver Q) →ₐ[k] pathAlgebra k (Symmetrify Q) :=
  liftAlgHom k (fun x => ginzburgRetractPath k x.2.2) (ginzburgRetractPath_comp k)
    (ginzburgRetractPath_hzero k) (ginzburgRetractPath_hone k)

/-- The retraction fixes every vertex idempotent. -/
@[simp]
theorem ginzburgRetraction_vertexIdempotent (v : GinzburgQuiver Q) :
    ginzburgRetraction k (vertexIdempotent k v) = vertexIdempotent (Q := Symmetrify Q) k v := by
  rw [vertexIdempotent_eq_ofPath, ginzburgRetraction, liftAlgHom_ofPath, ginzburgRetractPath]

/-- The retraction on an arrow of the Ginzburg quiver. -/
private theorem ginzburgRetraction_ofArrow {a b : GinzburgQuiver Q} (e : a ⟶ b) :
    ginzburgRetraction k (ofArrow e) = ginzburgRetractArrow k e := by
  rw [ofArrow_eq_ofPath, ginzburgRetraction, liftAlgHom_ofPath, ← Path.nil_comp (Hom.toPath e),
    Path.comp_toPath_eq_cons, ginzburgRetractPath, ginzburgRetractPath]
  exact ginzburgRetractArrow_mul_vertexIdempotent k e

/-- The retraction kills every adjoined loop. Deliberately not a `simp` lemma:
`TauCeti.PathAlgebra.ofArrow_eq_ofPath` already normalizes its left-hand side. -/
theorem ginzburgRetraction_ofArrow_loop (i : Q) :
    ginzburgRetraction k (ofArrow (GinzburgHom.loop i)) = 0 :=
  ginzburgRetraction_ofArrow k _

/-- **The retraction is a left inverse of the inclusion** of the doubled path algebra. -/
@[simp]
theorem ginzburgRetraction_comp_ginzburgMap :
    (ginzburgRetraction k).comp (ginzburgMap k) = AlgHom.id k (pathAlgebra k (Symmetrify Q)) :=
  algHom_ext k fun x => by
    obtain ⟨a, b, p⟩ := x
    rw [AlgHom.comp_apply, ginzburgMap_ofPath, Prefunctor.mapTotalPath_mk, ginzburgRetraction,
      liftAlgHom_ofPath, ginzburgRetractPath_mapPath, AlgHom.id_apply]

/-- The retraction undoes the inclusion of the doubled path algebra. -/
@[simp]
theorem ginzburgRetraction_ginzburgMap (x : pathAlgebra k (Symmetrify Q)) :
    ginzburgRetraction k (ginzburgMap k x) = x := by
  rw [← AlgHom.comp_apply, ginzburgRetraction_comp_ginzburgMap, AlgHom.id_apply]

/-- The retraction fixes every doubled arrow. Deliberately not a `simp` lemma:
`TauCeti.PathAlgebra.ofArrow_eq_ofPath` already normalizes its left-hand side. -/
theorem ginzburgRetraction_ofArrow_double {i j : Q} (a : (i ⟶ j) ⊕ (j ⟶ i)) :
    ginzburgRetraction k (ofArrow (GinzburgHom.double a)) =
      ofArrow (Q := Symmetrify Q) (a := i) (b := j) a :=
  (congrArg _ (ginzburgMap_ofArrow k a).symm).trans (ginzburgRetraction_ginzburgMap k _)

/-- The inclusion of the doubled path algebra in the Ginzburg path algebra is injective. -/
theorem ginzburgMap_injective : Function.Injective (ginzburgMap (Q := Q) k) :=
  Function.LeftInverse.injective (ginzburgRetraction_ginzburgMap k)

/-- A doubled Ginzburg arrow is the image of the doubled arrow it came from. -/
private theorem ginzburgMap_ginzburgRetractArrow {a b : Q} (e : GinzburgHom Q a b)
    (he : ginzburgLoopCount e = 0) :
    ginzburgMap k (ginzburgRetractArrow k e) = ofArrow e := by
  cases e with
  | double e => exact ginzburgMap_ofArrow k e
  | loop => simp at he

/-- A loop-free Ginzburg path is the image of the doubled path obtained by killing its loops. -/
private theorem ginzburgMap_ginzburgRetractPath {a b : GinzburgQuiver Q} (p : Path a b)
    (hp : p.addWeight ginzburgLoopCount = 0) :
    ginzburgMap k (ginzburgRetractPath k p) = ofPath ⟨a, b, p⟩ := by
  induction p with
  | nil =>
    rw [ginzburgRetractPath]
    exact (congrArg (ginzburgMap k) (doubledVertexIdempotent_def (Q := Q) k a).symm).trans
      ((ginzburgMap_doubledVertexIdempotent (Q := Q) k a).trans
        (vertexIdempotent_eq_ofPath (Q := GinzburgQuiver Q) k a))
  | cons p e ih =>
    rw [Path.addWeight_cons, Nat.add_eq_zero_iff] at hp
    rw [ginzburgRetractPath, map_mul, ih hp.1]
    exact (congrArg (· * _) (ginzburgMap_ginzburgRetractArrow k e hp.2)).trans
      (ofArrow_mul_ofPath e p)

/-- **The retraction is a right inverse of the inclusion on cohomological degree `0`**: an element
of degree `0` is a combination of loop-free paths, each of which is fixed by killing the loops and
including back. -/
theorem ginzburgMap_ginzburgRetraction_of_mem {x : pathAlgebra k (GinzburgQuiver Q)}
    (hx : x ∈ gradeBy k ginzburgTwoDegree 0) :
    ginzburgMap k (ginzburgRetraction k x) = x := by
  rw [gradeBy_ginzburgTwoDegree_zero_eq_gradeBy_ginzburgLoopCount_zero, gradeBy_eq_span_range]
    at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨⟨a, b, p⟩, hp⟩, rfl⟩ := hy
    rw [ginzburgRetraction, liftAlgHom_ofPath]
    exact ginzburgMap_ginzburgRetractPath k p hp
  | zero => rw [map_zero, map_zero]
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul c y _ hy => rw [map_smul, map_smul, hy]

/-- **Cohomological degree `0` of the Ginzburg path algebra is the doubled path algebra**: an
element has degree `0` exactly when it is the image of an element of the doubled path algebra. -/
theorem mem_gradeBy_ginzburgTwoDegree_zero_iff {x : pathAlgebra k (GinzburgQuiver Q)} :
    x ∈ gradeBy k ginzburgTwoDegree 0 ↔ ∃ y, ginzburgMap k y = x :=
  ⟨fun hx => ⟨_, ginzburgMap_ginzburgRetraction_of_mem k hx⟩,
    fun ⟨y, hy⟩ => hy ▸ ginzburgMap_mem_gradeBy_ginzburgTwoDegree k y⟩

end Retraction

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

/-- **Every boundary of `Π₂(Q)` vanishes in `Π_k(Q)` once the loops are killed.**  By the Leibniz
rule the differential of a path is a sum of terms, each of which contains either a relator
`d t_i = ρ_i` or an adjoined loop. -/
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

/-- The inverse of the isomorphism `Π_k(Q) ≃ H⁰(Π₂(Q))` kills the loops of a representing cycle:
it is `TauCeti.ginzburgTwoCohomologyToPreprojective` on the degree-zero classes.  Not a `simp`
lemma, as it would prevent `AlgEquiv.apply_symm_apply` from firing. -/
theorem preprojectiveEquivGinzburgTwoCohomologyZero_symm_apply
    (z : (isDGAlgebra_ginzburgTwoDifferential (Q := Q) k).cohomologyGrading 0) :
    (preprojectiveEquivGinzburgTwoCohomologyZero k Q).symm z =
      ginzburgTwoCohomologyToPreprojective k Q z := by
  obtain ⟨x, rfl⟩ := (preprojectiveEquivGinzburgTwoCohomologyZero k Q).surjective z
  rw [AlgEquiv.symm_apply_apply, coe_preprojectiveEquivGinzburgTwoCohomologyZero_apply,
    ginzburgTwoCohomologyToPreprojective_preprojectiveToGinzburgTwoCohomology]

end Cohomology

end TauCeti
