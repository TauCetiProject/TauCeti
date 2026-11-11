/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Normalization.Finite
public import TauCeti.AlgebraicGeometry.Normalization.Regular
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness
import TauCeti.RingTheory.UniversallyJapanese

/-!
# The normalization genus of a curve

Let `X` be a curve over a field `k`: an integral scheme, proper of dimension one over `k`
(`AlgebraicGeometry.Scheme.IsCurveOver`). Its normalization `X^ν` is the normalization of `X` in its
function field, along `Spec k(X) ⟶ X`. This file shows that `X^ν` is again a curve over `k`, now
with discrete valuation rings as codimension-one local rings, so that `H¹(X^ν, 𝒪)` is
finite-dimensional, and defines the **normalization genus** of `X` as the genus of `X^ν`. It is the
genus attached to an irreducible component in the stability conditions for curves and stable maps.

The normalization is finite over `X`: the rings of sections of affine opens of `X` are domains of
finite type over `k`, hence Japanese. It is therefore proper over `k` and regular
(`TauCeti.AlgebraicGeometry.isRegular_normalization_fromSpecStalk_genericPoint`). It is surjective
onto `X`, being dominant and closed, so it has dimension exactly one: a proper specialization in `X`
lifts to one in `X^ν`.

## Main declarations

* `TauCeti.AlgebraicGeometry.isFinite_fromNormalization_of_locallyOfFiniteType`: the normalization
  of an integral scheme locally of finite type over a field is finite.
* `TauCeti.AlgebraicGeometry.isCurveOver_normalization`: the normalization of a curve is a curve.
* `AlgebraicGeometry.Scheme.normalizationGenus`: the genus of the normalization of a curve.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.3.8 (normalization) and Chapter IV, §1.
* The Stacks Project, Lemma 33.41.1 (0C45).
-/

public section

open CategoryTheory AlgebraicGeometry Topology

namespace TauCeti.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- **Finiteness of normalization over a field.** The normalization of an integral scheme locally of
finite type over a field, in its function field, is finite: the rings of sections of its affine
opens are domains of finite type over the field, hence Japanese. -/
theorem isFinite_fromNormalization_of_locallyOfFiniteType [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] :
    IsFinite (X.fromSpecStalk (genericPoint X)).fromNormalization := by
  refine isFinite_fromNormalization_fromSpecStalk_genericPoint_iff.mpr fun U hU _ ↦ ?_
  let φ := (Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ U le_top
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType k Γ(X, U) :=
    (X ↘ Spec (.of k)).finiteType_ΓSpecIso_inv_comp_appLE hU
  have := Ring.IsUniversallyJapanese.isJapanese k Γ(X, U)
  infer_instance

/-- The normalization of an integral scheme over `k` lies over `k` through the normalization
morphism. -/
noncomputable instance overNormalization [IsIntegral X] :
    (X.fromSpecStalk (genericPoint X)).normalization.Over (Spec (.of k)) where
  hom := (X.fromSpecStalk (genericPoint X)).fromNormalization ≫ X ↘ Spec (.of k)

/-- The structure morphism of the normalization is the normalization morphism followed by that of
`X`. -/
theorem normalization_over_hom [IsIntegral X] :
    (X.fromSpecStalk (genericPoint X)).normalization ↘ Spec (.of k) =
      (X.fromSpecStalk (genericPoint X)).fromNormalization ≫ X ↘ Spec (.of k) :=
  rfl

/-- In a T₀ space, a proper specialization gives a chain of two irreducible closed subsets. -/
private theorem one_le_topologicalKrullDim_of_specializes {α : Type*} [TopologicalSpace α]
    [T0Space α] {x y : α} (h : x ⤳ y) (hne : x ≠ y) : 1 ≤ topologicalKrullDim α := by
  let a : TopologicalSpace.IrreducibleCloseds α :=
    ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  let b : TopologicalSpace.IrreducibleCloseds α :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hab : a < b := lt_of_le_of_ne (specializes_iff_closure_subset.mp h) fun e ↦
    hne (h.antisymm (specializes_iff_closure_subset.mpr (congrArg SetLike.coe e).ge)).eq
  exact Order.one_le_krullDim_iff.mpr ⟨a, b, hab⟩

variable [X.IsCurveOver k]

/-- The normalization morphism of a curve is surjective: it is dominant and closed. -/
theorem surjective_fromNormalization_of_isCurveOver :
    Function.Surjective (X.fromSpecStalk (genericPoint X)).fromNormalization := by
  set f := X.fromSpecStalk (genericPoint X)
  have : IsFinite f.fromNormalization := isFinite_fromNormalization_of_locallyOfFiniteType k X
  have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
    rw [f.toNormalization_fromNormalization]
    infer_instance
  have : IsDominant f.fromNormalization := .of_comp f.toNormalization f.fromNormalization
  exact (surjective_of_isDominant_of_isClosed_range _
    (f.fromNormalization.isClosedMap.isClosed_range)).surj

/-- **The normalization of a curve is a curve.** The normalization of a curve over `k` in its
function field is integral, proper over `k` and of dimension one. -/
instance isCurveOver_normalization :
    (X.fromSpecStalk (genericPoint X)).normalization.IsCurveOver k := by
  set f := X.fromSpecStalk (genericPoint X)
  have : IsFinite f.fromNormalization := isFinite_fromNormalization_of_locallyOfFiniteType k X
  have hdimX := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k
  refine Scheme.isCurveOver_iff.mpr ⟨inferInstance, ?_, le_antisymm ?_ ?_⟩
  · rw [normalization_over_hom]
    infer_instance
  · exact f.fromNormalization.topologicalKrullDim_le.trans hdimX.le
  · -- `X` has a point other than its generic point, since it has dimension one
    obtain ⟨p, hp⟩ : ∃ p : X, p ≠ genericPoint X := by
      by_contra! h
      have : Subsingleton X := ⟨fun a b ↦ (h a).trans (h b).symm⟩
      have h0 : topologicalKrullDim X ≤ 0 := by
        rw [TauCeti.topologicalKrullDim_eq_iSup_coheight]
        refine iSup_le fun x ↦ ?_
        let := specializationPreorder X
        exact_mod_cast (Order.coheight_eq_zero.mpr fun y _ ↦ (Subsingleton.elim y x).le).le
      rw [hdimX] at h0
      exact absurd h0 (by norm_num)
    -- a preimage of `p` is a proper specialization of the generic point of the normalization
    obtain ⟨q, rfl⟩ := surjective_fromNormalization_of_isCurveOver k X p
    refine one_le_topologicalKrullDim_of_specializes
      ((genericPoint_spec f.normalization).specializes (Set.mem_univ q)) fun hq ↦ hp ?_
    refine IsGenericPoint.eq ?_ (genericPoint_spec X)
    refine isGenericPoint_iff_specializes.mpr fun x ↦ ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    obtain ⟨y, rfl⟩ := surjective_fromNormalization_of_isCurveOver k X x
    rw [← hq]
    exact ((genericPoint_spec f.normalization).specializes (Set.mem_univ y)).map
      f.fromNormalization.continuous

/-- The normalization of a curve is regular, so its codimension-one local rings are discrete
valuation rings. -/
instance isRegular_normalization_of_isCurveOver :
    IsRegular (X.fromSpecStalk (genericPoint X)).normalization := by
  have : IsFinite (X.fromSpecStalk (genericPoint X)).fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType k X
  have := Scheme.IsCurveOver.isNoetherian k X
  exact isRegular_normalization_fromSpecStalk_genericPoint
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k).le

/-- The first cohomology of the structure sheaf of the normalization of a curve is
finite-dimensional. -/
instance finiteDimensional_cohomology_one_normalization :
    FiniteDimensional k (Scheme.Modules.Cohomology
      (InvertibleSheaf.trivial (X.fromSpecStalk (genericPoint X)).normalization).obj 1) := by
  have : ∀ y : CodimensionOnePoint (X.fromSpecStalk (genericPoint X)).normalization,
      IsDiscreteValuationRing
        ((X.fromSpecStalk (genericPoint X)).normalization.presheaf.stalk (y : _)) :=
    fun _ ↦ inferInstance
  exact finiteDimensional_cohomology_one_trivial_of_isProper k
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one k)

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [X.IsCurveOver k]

/-- The **normalization genus** (geometric genus) of a curve `X` over a field `k`: the genus
`dim_k H¹(X^ν, 𝒪)` of its normalization `X^ν` in its function field. It is the genus of an
irreducible component used in stability conditions for curves and maps. -/
noncomputable def normalizationGenus : ℕ :=
  (X.fromSpecStalk (genericPoint X)).normalization.genus k

/-- The normalization genus is the genus of the normalization. -/
theorem normalizationGenus_def :
    X.normalizationGenus k = (X.fromSpecStalk (genericPoint X)).normalization.genus k :=
  normalizationGenus.eq_def k X

end AlgebraicGeometry.Scheme
