/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Norm.Basic
public import TauCeti.RepresentationTheory.Tensor.Induction.TrivialF2.Pairing
import TauCeti.RepresentationTheory.Tensor.Induction.Cup.DiagonalClass

/-!
# Multiplicativity of the Evens norm

For a compact open subgroup `U` of finite index `l`, the all-degree Evens norm preserves
cup products with trivial `𝔽₂` coefficients:
`N_U^G (x ⌣ y) = N_U^G x ⌣ N_U^G y`, with the degree transport
`l m + l n = l (m + n)` explicit. This holds in every bidegree, including degree zero.

The cocycle formula follows from the factorwise cup on the tensor-induced resolution.
The identification of tensor-induced trivial coefficients with trivial coefficients preserves
multiplication, so the resulting cup is the canonical mod-two cup, not a second product.
The statement is multiplicativity, not additivity: the norm is only a function on cohomology.

## Main results

* `OpenSubgroup.tensorNormCocycleClass_cupCochain`: the tensor norm preserves the cup of
  homogeneous cocycles, for any transversal.
* `OpenSubgroup.evensNorm_cup`: the Evens norm preserves the canonical cup product.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), §6, Proposition 1.
-/

public section

namespace OpenSubgroup

open TauCeti CategoryTheory

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : OpenSubgroup G) [U.toSubgroup.FiniteIndex] [CompactSpace U.toSubgroup]
  [Fintype (G ⧸ U.toSubgroup)]

open scoped TopRep.GradedResolution

/-- The tensor norm of the cup of two homogeneous cocycles is the canonical cup of their tensor
norms. The formula holds for every transversal, with the degree equality `l m + l n = l (m + n)`
read through `degreeCast`. -/
theorem tensorNormCocycleClass_cupCochain (t : U.toSubgroup.LeftTransversal) {m n : ℕ}
    (a : (TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).X m)
    (ha : ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).d m (m + 1)).hom a = 0)
    (b : (TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).X n)
    (hb : ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).d n (n + 1)).hom b = 0)
    (hab : ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).d (m + n) (m + n + 1)).hom
      ((trivialF2TopPairing U.toSubgroup).cupCochain m n a b) = 0) :
    tensorNormCocycleClass U t ((trivialF2TopPairing U.toSubgroup).cupCochain m n a b) hab =
      (ContinuousCohomology.degreeCast (trivialF2 G)
        (mul_add (Fintype.card (G ⧸ U.toSubgroup)) m n).symm).hom
        ((trivialF2TopPairing G).cup _ _
          (tensorNormCocycleClass U t a ha) (tensorNormCocycleClass U t b hb)) := by
  let A : SmoothDiscreteTopRep.{0, u, u} ℤ U.toSubgroup :=
    ⟨trivialF2 U.toSubgroup, isSmoothDiscrete_trivialF2 U.toSubgroup⟩
  let P := trivialF2TopPairing U.toSubgroup
  -- Give the coefficient morphism the same presentation as the diagonal-class theorem;
  -- the smooth tensor-induction functor preserves this carrier but is sealed.
  let e : ((toSmoothDiscrete ℤ G).obj
      (DiscreteRep.tensorInduced U.toSubgroup U.isOpen' t ((ofSmoothDiscrete ℤ U.toSubgroup).obj A))
      ).obj ⟶ trivialF2 G :=
    (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' t).hom.hom
  have hpair (x y) : e ((P.smoothTensorInduced U.toSubgroup U.isOpen' t).bil x y) =
      (trivialF2TopPairing G).bil (e x) (e y) := by
    rw [TopPairing.smoothTensorInduced_bil]
    exact smoothTensorInducedTrivialF2Iso_hom_apply_piTensorProduct_map₂ G _ _ _ x y
  have h := smoothTensorInducedDiagonalClass_gradedResolutionCupPairing
    U.toSubgroup U.isOpen' t (A := A) (B := A) (C := A) P
    (trivialF2_add_self U.toSubgroup) (trivialF2_add_self U.toSubgroup)
    (trivialF2_add_self U.toSubgroup)
    ((trivialF2 U.toSubgroup).cochainToGradedResolution_mem m a)
    ((trivialF2 U.toSubgroup).cochainToGradedResolution_invariant m a)
    (by rw [TopRep.gradedResolutionDifferential_cochainToGradedResolution, ha, map_zero])
    ((trivialF2 U.toSubgroup).cochainToGradedResolution_mem n b)
    ((trivialF2 U.toSubgroup).cochainToGradedResolution_invariant n b)
    (by rw [TopRep.gradedResolutionDifferential_cochainToGradedResolution, hb, map_zero])
  -- Apply the resolution identity as a term: its cocycle witnesses depend on the product,
  -- so rewriting that product inside the identity would leave an ill-typed motive.
  rw [tensorNormCocycleClass_def]
  refine (congrArg (ContinuousCohomology.coeffMap e _) (Eq.trans ?_ h)).trans ?_
  · congr 1
    exact (P.gradedResolutionCupPairing_cochainToGradedResolution m n a b).symm
  -- Move coefficient normalization past the degree transport, then use cup naturality.
  rw [← ConcreteCategory.comp_apply, ← ContinuousCohomology.degreeCast_naturality
    (ContinuousCohomology.coeffMap e), ConcreteCategory.comp_apply,
    (P.smoothTensorInduced U.toSubgroup U.isOpen' t).cup_coeffMap
      (trivialF2TopPairing G) e e e hpair]
  rw [tensorNormCocycleClass_def, tensorNormCocycleClass_def]
  -- Unfold the local coefficient object and map. The source is the object presentation from
  -- smoothTensorInductionFunctor_obj; the smooth/discrete dictionary preserves the carrier
  -- definitionally, so no transport lemma is needed. The cocycle witnesses are proof-irrelevant.
  rfl

/-- **The Evens norm is multiplicative** in every bidegree with trivial `𝔽₂` coefficients.
The cup of the norms has degree `l m + l n` and is transported to `l (m + n)`, the degree
of the norm of the cup. No additivity of the norm is asserted. -/
@[simp]
theorem evensNorm_cup {m n : ℕ}
    (x : continuousCohomology m (trivialF2 U.toSubgroup))
    (y : continuousCohomology n (trivialF2 U.toSubgroup)) :
    U.evensNorm ((trivialF2TopPairing U.toSubgroup).cup m n x y) =
      (ContinuousCohomology.degreeCast (trivialF2 G)
        (mul_add (Fintype.card (G ⧸ U.toSubgroup)) m n).symm).hom
        ((trivialF2TopPairing G).cup _ _ (U.evensNorm x) (U.evensNorm y)) := by
  obtain ⟨a, ha, rfl⟩ := TopRep.exists_cochainClass_eq x
  obtain ⟨b, hb, rfl⟩ := TopRep.exists_cochainClass_eq y
  have hab : ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).d (m + n) (m + n + 1)).hom
      ((trivialF2TopPairing U.toSubgroup).cupCochain m n a b) = 0 := by
    simp only [TopPairing.cupCochain_leibniz, ha, hb, map_zero, LinearMap.zero_apply,
      smul_zero, add_zero]
  rw [(trivialF2TopPairing U.toSubgroup).cup_cochainClass m n a ha b hb hab,
    evensNorm_cochainClass U default, evensNorm_cochainClass U default,
    evensNorm_cochainClass U default, tensorNormCocycleClass_cupCochain]

end OpenSubgroup
