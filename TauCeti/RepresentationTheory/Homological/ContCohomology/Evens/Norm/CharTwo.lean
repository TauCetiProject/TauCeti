/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Algebra.Discrete
public import TauCeti.RepresentationTheory.Tensor.Induction.Resolution
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Cochain
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero
import TauCeti.RepresentationTheory.Tensor.Induction.ChangeTransversal.Resolution
import TauCeti.RepresentationTheory.Tensor.Induction.Cochain
import TauCeti.RepresentationTheory.Tensor.Induction.Cup.DiagonalClass

/-!
# The Evens norm with coefficients in a discrete commutative ring of characteristic two

Let `U` be a compact open subgroup of finite index `l` in a topological group `G`, and let `A` be a
discrete commutative `G`-ring in which `2 = 0`, read as the coefficient object
`TauCeti.ofDiscreteModule ℤ G A`. Evens' norm, or multiplicative transfer, is the function

```
N_U^G : Hⁿ(U, A) → H^{l n}(G, A)
```

sending the class of a homogeneous cocycle `z` to the class of its diagonal tensor `z ⊗ ⋯ ⊗ z` in
the tensor-induced resolution (`TauCeti.smoothTensorInducedDiagonalClass`), a class with values in
the tensor-induced ring `⨂_{G ⧸ U} A`, pushed forward along Evens' twisted multiplication
`a₁ ⊗ ⋯ ⊗ a_l ↦ t₁a₁ ⋯ t_l a_l` (`TauCeti.smoothTensorInducedMulHom`). Because `2 = 0` in `A`, the
tensor-induced resolution is a complex and no sign enters, so the norm is defined in every degree.
The class depends only on the cohomology class of `z` and not on the transversal. The norm is not
additive, and its signature uses `→` between the underlying types.

With trivial `𝔽₂` coefficients, `OpenSubgroup.evensNorm` is defined by the same diagonal tensor,
normalized by multiplying the tensor factors. Here the coefficients carry an arbitrary continuous
action by ring automorphisms, which the twisted multiplication takes into account.

## Main definitions

* `OpenSubgroup.evensNormCharTwo`: the Evens norm `Hⁿ(U, A) → H^{l n}(G, A)`.

## Main results

* `OpenSubgroup.evensNormCharTwo_cochainClass`: the norm of the class of a homogeneous cocycle is
  the pushed-forward class of its diagonal tensor, computed with any transversal.
* `OpenSubgroup.evensNormCharTwo_gradedCohomologyClass`: the same for a cocycle of the total
  coinduced resolution.
* `OpenSubgroup.evensNormCharTwo_zero`: the norm of zero is zero.
* `OpenSubgroup.evensNormCharTwo_degreeZeroClass`: in degree zero the norm is the multiplicative
  norm `a ↦ ∏ x : G ⧸ U, t(x) • a` from `A^U` to `A^G`.
* `OpenSubgroup.evensNormCharTwo_degreeZeroClass_one`: the normalization `N_U^G 1 = 1`.
* `OpenSubgroup.evensNormCharTwo_cup`: the norm is multiplicative, `N(x ⌣ y) = N x ⌣ N y`, for the
  cup product of the multiplication of `A`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), §§5–6.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), §2, for the characteristic-two norm in every degree.
-/

public section

namespace OpenSubgroup

open TauCeti CategoryTheory
open scoped TopRep.GradedResolution

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : OpenSubgroup G) [U.toSubgroup.FiniteIndex] [CompactSpace U.toSubgroup]
  [Fintype (G ⧸ U.toSubgroup)]
  (A : Type u) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction G A] [ContinuousSMul G A] (hA : ∀ a : A, a + a = 0)

omit [IsTopologicalGroup G] [U.toSubgroup.FiniteIndex] [CompactSpace U.toSubgroup]
  [Fintype (G ⧸ U.toSubgroup)] [ContinuousSMul G A] in
include hA in
/-- Every element of the coefficient carrier `ofDiscreteModule ℤ U A`, whose additive group is that
of `A`, is its own negative. -/
private theorem add_self_eq_zero (a : (ofDiscreteModule ℤ U.toSubgroup A).V) : a + a = 0 :=
  hA a

/-- The class of the diagonal tensor of a homogeneous cocycle of `U` with values in `A`, pushed
forward to `A` along Evens's twisted multiplication for the transversal `t`. -/
private noncomputable def normCocycleClass (t : U.toSubgroup.LeftTransversal) {n : ℕ}
    (z : (TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).X n)
    (hz : ((TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).d n (n + 1)).hom z =
      0) :
    continuousCohomology (Fintype.card (G ⧸ U.toSubgroup) * n) (ofDiscreteModule ℤ G A) :=
  ContinuousCohomology.coeffMap
    (smoothTensorInducedMulHom.{0, u, 0} U.toSubgroup U.isOpen' A t).hom
    (Fintype.card (G ⧸ U.toSubgroup) * n)
    (smoothTensorInducedDiagonalClass.{0, u, u} U.toSubgroup U.isOpen' t
      ⟨ofDiscreteModule ℤ U.toSubgroup A, ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩
      (add_self_eq_zero U A hA)
      ((ofDiscreteModule ℤ U.toSubgroup A).cochainToGradedResolution n z)
      ((ofDiscreteModule ℤ U.toSubgroup A).cochainToGradedResolution_mem n z)
      ((ofDiscreteModule ℤ U.toSubgroup A).cochainToGradedResolution_invariant n z)
      (by rw [TopRep.gradedResolutionDifferential_cochainToGradedResolution, hz, map_zero]))

/-- The pushed-forward diagonal class of a cocycle does not depend on the transversal. -/
private theorem normCocycleClass_changeTransversal (s t : U.toSubgroup.LeftTransversal) {n : ℕ}
    (z : (TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).X n)
    (hz : ((TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).d n (n + 1)).hom z =
      0) :
    normCocycleClass U A hA t z hz = normCocycleClass U A hA s z hz := by
  rw [normCocycleClass, normCocycleClass,
    ← coeffMap_smoothTensorInducedDiagonalClass_changeTransversal.{0, u, u} U.toSubgroup U.isOpen'
      s t ⟨ofDiscreteModule ℤ U.toSubgroup A, ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩
      (add_self_eq_zero U A hA),
    ← ConcreteCategory.comp_apply, ← ContinuousCohomology.coeffMap_comp]
  rw [← ObjectProperty.FullSubcategory.comp_hom,
    smoothTensorInducedChangeTransversalIso_hom_smoothTensorInducedMulHom]

/-- Cocycles with equal classes have equal pushed-forward diagonal classes. -/
private theorem normCocycleClass_eq_of_cochainClass_eq (t : U.toSubgroup.LeftTransversal) {n : ℕ}
    (z z' : (TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).X n)
    (hz : ((TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).d n (n + 1)).hom z =
      0)
    (hz' : ((TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).d n (n + 1)).hom z' =
      0)
    (h : (ofDiscreteModule ℤ U.toSubgroup A).cochainClass n z hz =
      (ofDiscreteModule ℤ U.toSubgroup A).cochainClass n z' hz') :
    normCocycleClass U A hA t z hz = normCocycleClass U A hA t z' hz' :=
  congrArg (ContinuousCohomology.coeffMap
      (smoothTensorInducedMulHom.{0, u, 0} U.toSubgroup U.isOpen' A t).hom _)
    (smoothTensorInducedDiagonalClass_eq_of_cochainClass_eq U.toSubgroup U.isOpen' t
      ⟨ofDiscreteModule ℤ U.toSubgroup A, ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩
      (add_self_eq_zero U A hA) z z' hz hz' h)

/-- **The Evens norm in characteristic two** `N_U^G : Hⁿ(U, A) → H^{l n}(G, A)`, for a discrete
commutative `G`-ring `A` in which `2 = 0` and `l` the index of `U`: the class of the diagonal
tensor `z ⊗ ⋯ ⊗ z` of a homogeneous cocycle `z` representing the class, pushed forward along
Evens's twisted multiplication `a₁ ⊗ ⋯ ⊗ a_l ↦ t₁a₁ ⋯ t_l a_l`, computed with the default
transversal. By `OpenSubgroup.evensNormCharTwo_cochainClass` neither the representative nor the
transversal matters. It is a function and not an additive map. -/
noncomputable def evensNormCharTwo {n : ℕ}
    (x : continuousCohomology n (ofDiscreteModule ℤ U.toSubgroup A)) :
    continuousCohomology (Fintype.card (G ⧸ U.toSubgroup) * n) (ofDiscreteModule ℤ G A) :=
  normCocycleClass U A hA default (TopRep.exists_cochainClass_eq x).choose
    (TopRep.exists_cochainClass_eq x).choose_spec.choose

-- The `show` reads `hA` on the carrier of `ofDiscreteModule ℤ U A`, the form the diagonal class
-- takes; that carrier is `A` with its additive structure, but only up to unfolding.
/-- **The defining equation of the Evens norm in characteristic two:** the norm of the class of a
homogeneous cocycle `z` is the class of its diagonal tensor in the tensor-induced resolution,
pushed forward along Evens's twisted multiplication, computed with any transversal `t`. -/
theorem evensNormCharTwo_cochainClass (t : U.toSubgroup.LeftTransversal) {n : ℕ}
    (z : (TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).X n)
    (hz : ((TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).d n (n + 1)).hom z =
      0) :
    U.evensNormCharTwo A hA ((ofDiscreteModule ℤ U.toSubgroup A).cochainClass n z hz) =
      ContinuousCohomology.coeffMap
        (smoothTensorInducedMulHom.{0, u, 0} U.toSubgroup U.isOpen' A t).hom
        (Fintype.card (G ⧸ U.toSubgroup) * n)
        (smoothTensorInducedDiagonalClass.{0, u, u} U.toSubgroup U.isOpen' t
          ⟨ofDiscreteModule ℤ U.toSubgroup A, ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩
          (show ∀ a : (ofDiscreteModule ℤ U.toSubgroup A).V, a + a = 0 from hA)
          ((ofDiscreteModule ℤ U.toSubgroup A).cochainToGradedResolution n z)
          ((ofDiscreteModule ℤ U.toSubgroup A).cochainToGradedResolution_mem n z)
          ((ofDiscreteModule ℤ U.toSubgroup A).cochainToGradedResolution_invariant n z)
          (by rw [TopRep.gradedResolutionDifferential_cochainToGradedResolution, hz, map_zero])) :=
  (normCocycleClass_changeTransversal U A hA t default _ _).trans <|
    normCocycleClass_eq_of_cochainClass_eq U A hA t _ _ _ _
      (TopRep.exists_cochainClass_eq _).choose_spec.choose_spec

/-- The Evens norm in characteristic two of zero is zero, in every degree. -/
@[simp]
theorem evensNormCharTwo_zero (n : ℕ) :
    U.evensNormCharTwo A hA (0 : continuousCohomology n (ofDiscreteModule ℤ U.toSubgroup A)) =
      0 := by
  rw [← TopRep.cochainClass_zero (X := ofDiscreteModule ℤ U.toSubgroup A) (n := n),
    evensNormCharTwo_cochainClass U A hA default]
  exact (congrArg (ContinuousCohomology.coeffMap
      (smoothTensorInducedMulHom.{0, u, 0} U.toSubgroup U.isOpen' A default).hom _)
    (smoothTensorInducedDiagonalClass_cochainToGradedResolution_zero U.toSubgroup U.isOpen' default
      ⟨ofDiscreteModule ℤ U.toSubgroup A, ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩
      (add_self_eq_zero U A hA) n)).trans (map_zero _)

-- The `show` reads `hA` on the carrier of `ofDiscreteModule ℤ U A`, as in
-- `OpenSubgroup.evensNormCharTwo_cochainClass`.
/-- **The Evens norm in characteristic two of a cocycle of the total resolution.** For a
homogeneous cocycle `w` of degree `n` of the total coinduced resolution of `A`, fixed by `U`, the
norm of its class is the class of its diagonal tensor `w ⊗ ⋯ ⊗ w`, pushed forward along Evens's
twisted multiplication, computed with any transversal `t`. -/
theorem evensNormCharTwo_gradedCohomologyClass (t : U.toSubgroup.LeftTransversal) {n : ℕ}
    {w : (ofDiscreteModule ℤ U.toSubgroup A).gradedResolutionModule}
    (hw : w ∈ (ofDiscreteModule ℤ U.toSubgroup A).gradedResolutionPiece n)
    (hinv : ∀ u, (ofDiscreteModule ℤ U.toSubgroup A).gradedResolutionTopRep.ρ u w = w)
    (hdw : (ofDiscreteModule ℤ U.toSubgroup A).gradedResolutionDifferential w = 0) :
    U.evensNormCharTwo A hA ((TopRep.gradedResolutionContraction
        (ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A)).gradedCohomologyClass w hw hinv
        ((TopRep.gradedResolutionTopRepDifferential_apply _ w).trans hdw)) =
      ContinuousCohomology.coeffMap
        (smoothTensorInducedMulHom.{0, u, 0} U.toSubgroup U.isOpen' A t).hom
        (Fintype.card (G ⧸ U.toSubgroup) * n)
        (smoothTensorInducedDiagonalClass.{0, u, u} U.toSubgroup U.isOpen' t
          ⟨ofDiscreteModule ℤ U.toSubgroup A, ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩
          (show ∀ a : (ofDiscreteModule ℤ U.toSubgroup A).V, a + a = 0 from hA)
          w hw hinv hdw) := by
  -- A homogeneous invariant cocycle of the total resolution is an included homogeneous cocycle.
  obtain ⟨z, rfl⟩ := (ofDiscreteModule ℤ U.toSubgroup A).exists_cochainToGradedResolution_eq hw hinv
  have hz := (TopRep.gradedResolutionDifferential_cochainToGradedResolution_eq_zero_iff _ n z).1 hdw
  refine (congrArg (U.evensNormCharTwo A hA)
    (TopRep.gradedCohomologyClass_eq_degreeCast_cochainClass _ rfl z hz _ rfl _ _ _)).trans ?_
  rw [ContinuousCohomology.degreeCast_rfl, Iso.refl_hom, ConcreteCategory.id_apply,
    evensNormCharTwo_cochainClass U A hA t]

/-- **The Evens norm in characteristic two of a degree-zero class** is the multiplicative norm: for
`a ∈ A` fixed by `U`, the norm of its degree-zero class is the degree-zero class of the twisted
product `∏ x : G ⧸ U, t(x) • a` along any transversal `t`, in degree `0 = l · 0`. -/
theorem evensNormCharTwo_degreeZeroClass (t : U.toSubgroup.LeftTransversal) (a : A)
    (ha : ∀ u, (ofDiscreteModule ℤ U.toSubgroup A).ρ u a = a) :
    U.evensNormCharTwo A hA
        (ContinuousCohomology.degreeZeroClass (ofDiscreteModule ℤ U.toSubgroup A) a ha) =
      (ContinuousCohomology.degreeCast (ofDiscreteModule ℤ G A) (Nat.mul_zero _).symm).hom
        (ContinuousCohomology.degreeZeroClass (ofDiscreteModule ℤ G A)
          (∏ x, U.toSubgroup.leftTransversalRep t x • a : A)
          (U.toSubgroup.smul_prod_leftTransversalRep_smul (A := A) t ha)) := by
  obtain ⟨z, hz, hzx⟩ := TopRep.exists_cochainClass_eq
    (ContinuousCohomology.degreeZeroClass (ofDiscreteModule ℤ U.toSubgroup A) a ha)
  -- A homogeneous `0`-cocycle takes an invariant value at `1`, the image of its class in the
  -- invariants; representing the class of `a`, it takes the value `a`.
  have hu : ∀ u, (ofDiscreteModule ℤ U.toSubgroup A).ρ u (z.val 1) = z.val 1 := by
    have e := ContinuousCohomology.coe_zeroIso_hom_π (ofDiscreteModule ℤ U.toSubgroup A)
      ((TopRep.homogeneousCochains _).cyclesMkOfEq z (0 + 1) (CochainComplex.next ℕ 0) hz)
    rw [HomologicalComplex.iCycles_cyclesMkOfEq] at e
    rw [← e]
    exact (ContRepresentation.mem_invariants _).1 (Subtype.property _)
  have h1 : z.val 1 = a := (ContinuousCohomology.degreeZeroClass_inj hu ha).1
    ((TopRep.cochainClass_eq_degreeZeroClass _ z hz _ hu rfl).symm.trans hzx)
  rw [← hzx, evensNormCharTwo_cochainClass U A hA t]
  -- The cocycle-level computation lands in degree `l · 0`; compare it with the transported class
  -- heterogeneously, so that no unfolding of `l · 0` to `0` is needed.
  refine eq_of_heq ((heq_of_eq ?_).trans (ContinuousCohomology.degreeCast_hom_apply_heq _ _).symm)
  rw [Subgroup.smoothTensorInducedDiagonalClass_eq_degreeZeroClass,
    ContinuousCohomology.coeffMap_def]
  refine (ContinuousCohomology.map_degreeZeroClass (ContinuousMonoidHom.id G) _ _ _).trans ?_
  congr 1
  refine (smoothTensorInducedMulHom_hom_hom_apply_tprod (R := ℤ) U.toSubgroup U.isOpen' A t
    _).trans ?_
  rw [TopRep.cochainToGradedResolution_apply, TopRep.gradedResolutionProjection_lof_zero, h1]

/-- **The normalization of the Evens norm in characteristic two**: `N_U^G 1 = 1`, where `1` is the
degree-zero class of the unit of `A`, in degree `0 = l · 0`. -/
@[simp]
theorem evensNormCharTwo_degreeZeroClass_one :
    U.evensNormCharTwo A hA (ContinuousCohomology.degreeZeroClass
        (ofDiscreteModule ℤ U.toSubgroup A) 1 fun u ↦ (smul_one u : u • (1 : A) = 1)) =
      (ContinuousCohomology.degreeCast (ofDiscreteModule ℤ G A) (Nat.mul_zero _).symm).hom
        (ContinuousCohomology.degreeZeroClass (ofDiscreteModule ℤ G A) 1
          fun g ↦ (smul_one g : g • (1 : A) = 1)) := by
  refine (evensNormCharTwo_degreeZeroClass U A hA default 1 _).trans ?_
  simp only [smul_one, Finset.prod_const_one]
  -- The unit of `A` and the unit of the carrier `(ofDiscreteModule ℤ G A).V`, which is `A` with
  -- its monoid structure (`TauCeti.instMonoidOfDiscreteModuleV`), agree by definition.
  rfl

/-- The pushed-forward diagonal class of the cup of two cocycles, for the multiplication pairing of
`A`, is the cup of their pushed-forward diagonal classes, in degree `l m + l n = l (m + n)`. -/
private theorem normCocycleClass_cupCochain (t : U.toSubgroup.LeftTransversal) {m n : ℕ}
    (a : (TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).X m)
    (ha : ((TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).d m (m + 1)).hom a =
      0)
    (b : (TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).X n)
    (hb : ((TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).d n (n + 1)).hom b =
      0)
    (hab : ((TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).d (m + n)
      (m + n + 1)).hom ((ofDiscreteModuleMulPairing ℤ U.toSubgroup A).cupCochain m n a b) = 0) :
    normCocycleClass U A hA t ((ofDiscreteModuleMulPairing ℤ U.toSubgroup A).cupCochain m n a b)
        hab =
      (ContinuousCohomology.degreeCast (ofDiscreteModule ℤ G A)
        (mul_add (Fintype.card (G ⧸ U.toSubgroup)) m n).symm).hom
        ((ofDiscreteModuleMulPairing ℤ G A).cup _ _
          (normCocycleClass U A hA t a ha) (normCocycleClass U A hA t b hb)) := by
  let P := ofDiscreteModuleMulPairing ℤ U.toSubgroup A
  have h := smoothTensorInducedDiagonalClass_gradedResolutionCupPairing.{0, u, u}
    U.toSubgroup U.isOpen' t
    (A := ⟨ofDiscreteModule ℤ U.toSubgroup A, ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩)
    (B := ⟨ofDiscreteModule ℤ U.toSubgroup A, ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩)
    (C := ⟨ofDiscreteModule ℤ U.toSubgroup A, ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩)
    P (add_self_eq_zero U A hA) (add_self_eq_zero U A hA) (add_self_eq_zero U A hA)
    ((ofDiscreteModule ℤ U.toSubgroup A).cochainToGradedResolution_mem m a)
    ((ofDiscreteModule ℤ U.toSubgroup A).cochainToGradedResolution_invariant m a)
    (by rw [TopRep.gradedResolutionDifferential_cochainToGradedResolution, ha, map_zero])
    ((ofDiscreteModule ℤ U.toSubgroup A).cochainToGradedResolution_mem n b)
    ((ofDiscreteModule ℤ U.toSubgroup A).cochainToGradedResolution_invariant n b)
    (by rw [TopRep.gradedResolutionDifferential_cochainToGradedResolution, hb, map_zero])
  -- Apply the resolution identity as a term: its cocycle witnesses depend on the product,
  -- so rewriting that product inside the identity would leave an ill-typed motive.
  rw [normCocycleClass]
  refine (congrArg (ContinuousCohomology.coeffMap
    (smoothTensorInducedMulHom.{0, u, 0} U.toSubgroup U.isOpen' A t).hom _)
    (Eq.trans ?_ h)).trans ?_
  · congr 1
    exact (P.gradedResolutionCupPairing_cochainToGradedResolution m n a b).symm
  -- Move the twisted multiplication past the degree transport, then use its cup compatibility.
  rw [← ConcreteCategory.comp_apply, ← ContinuousCohomology.degreeCast_naturality
    (ContinuousCohomology.coeffMap _), ConcreteCategory.comp_apply,
    cup_coeffMap_smoothTensorInducedMulHom, normCocycleClass, normCocycleClass]

/-- **The Evens norm in characteristic two is multiplicative** in every bidegree, for the cup
product of the multiplication of `A`: `N(x ⌣ y) = N x ⌣ N y`. The cup of the norms has degree
`l m + l n` and is transported to `l (m + n)`, the degree of the norm of the cup. -/
@[simp]
theorem evensNormCharTwo_cup {m n : ℕ}
    (x : continuousCohomology m (ofDiscreteModule ℤ U.toSubgroup A))
    (y : continuousCohomology n (ofDiscreteModule ℤ U.toSubgroup A)) :
    U.evensNormCharTwo A hA ((ofDiscreteModuleMulPairing ℤ U.toSubgroup A).cup m n x y) =
      (ContinuousCohomology.degreeCast (ofDiscreteModule ℤ G A)
        (mul_add (Fintype.card (G ⧸ U.toSubgroup)) m n).symm).hom
        ((ofDiscreteModuleMulPairing ℤ G A).cup _ _
          (U.evensNormCharTwo A hA x) (U.evensNormCharTwo A hA y)) := by
  obtain ⟨a, ha, rfl⟩ := TopRep.exists_cochainClass_eq x
  obtain ⟨b, hb, rfl⟩ := TopRep.exists_cochainClass_eq y
  have hab : ((TopRep.homogeneousCochains (ofDiscreteModule ℤ U.toSubgroup A)).d (m + n)
      (m + n + 1)).hom ((ofDiscreteModuleMulPairing ℤ U.toSubgroup A).cupCochain m n a b) = 0 := by
    simp only [TopPairing.cupCochain_leibniz, ha, hb, map_zero, LinearMap.zero_apply,
      smul_zero, add_zero]
  rw [(ofDiscreteModuleMulPairing ℤ U.toSubgroup A).cup_cochainClass m n a ha b hb hab,
    evensNormCharTwo_cochainClass U A hA default, evensNormCharTwo_cochainClass U A hA default,
    evensNormCharTwo_cochainClass U A hA default]
  -- The three classes are `normCocycleClass` unfolded.
  exact normCocycleClass_cupCochain U A hA default a ha b hb hab

end OpenSubgroup
