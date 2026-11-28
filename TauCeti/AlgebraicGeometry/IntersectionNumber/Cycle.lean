/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.TopDimension
public import TauCeti.AlgebraicGeometry.Chow.Pushforward
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
import TauCeti.AlgebraicGeometry.Curves.Normalization
import TauCeti.AlgebraicGeometry.IntersectionNumber.ProjectionFormula
import TauCeti.AlgebraicGeometry.LineBundle.BaseChange

/-!
# Intersection numbers with one-cycles

On a proper scheme `X` over a field `k`, a line-bundle class pairs with a one-cycle by
`(L · ∑ nᵢ [Cᵢ]) = ∑ nᵢ deg_k (L|_{Cᵢ})`. Here the cycles are the existing
`Chow.cyclesOfDimension X 1`, and each prime cycle is evaluated on the reduced closed
subscheme of its generic point. Thus the pairing includes negative coefficients and is
additive in the cycle as well as in the line bundle.

`LineBundleClass.cycleIntersectionNumber` bundles this bilinear pairing. Its value on a
prime cycle is the existing `LineBundleClass.intersectionNumber`, and the characterization
by integral closed curves makes it usable independently of the chosen presentation of a
curve as a reduced closed subscheme.

The pairing satisfies the **projection formula** for every morphism `f : Y ⟶ X` of proper
schemes over `k` (`LineBundleClass.cycleIntersectionNumber_cyclesMap`):

`(a · f_* α) = (f^* a · α)`,

where `f_*` is the pushforward of cycles `Chow.cyclesMap`. On a prime curve `C'` of `Y` it reduces
to two cases. If `f` maps `C'` onto a curve `C`, the induced morphism `C' ⟶ C` is finite, and
`(f^* a · C') = [κ(C') : κ(C)] · (a · C)` is the projection formula for finite dominant maps
(`LineBundleClass.intersectionNumber_pullback_eq_residueDegree_mul`); the degree is the residue
degree at the generic point that the pushforward of cycles uses. If `f` contracts `C'` to a closed
point, both sides vanish (`LineBundleClass.intersectionNumber_pullback_eq_zero_of_height_eq_zero`).
Restriction to a closed subscheme is the case of a closed immersion.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1, intersection numbers
  of line bundles with cycles of proper curves, and Section 9.2, the projection formula.
* W. Fulton, *Intersection Theory*, Proposition 2.5 (c), the projection formula for
  intersections of Cartier divisors with cycles under proper pushforward.
* The Stacks Project, Section 33.44 (Tag 0AYQ), degrees on proper curves.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Order
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry

open Chow

namespace LineBundleClass

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]

/-- The intersection pairing of line-bundle classes with one-cycles on a proper scheme
over a field. It extends the degree on integral closed curves by linearity, using the
existing group of algebraic one-cycles. -/
def cycleIntersectionNumber :
    Additive (LineBundleClass X) →+ (cyclesOfDimension X 1 →+ ℤ) := by
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  exact
    { toFun a := ((cyclesOfDimensionBasis X 1).constr ℤ fun x ↦
        intersectionNumber k
          (vanishingIdeal ⟨closure {(x : X)}, isClosed_closure⟩).subschemeι a.toMul).toAddMonoidHom
      map_zero' := by
        apply AddMonoidHom.toIntLinearMap_injective
        apply (cyclesOfDimensionBasis X 1).ext
        intro x
        simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.coe_toIntLinearMap,
          Module.Basis.constr_basis, toMul_zero, intersectionNumber_one,
          AddMonoidHom.zero_apply]
      map_add' a b := by
        apply AddMonoidHom.toIntLinearMap_injective
        apply (cyclesOfDimensionBasis X 1).ext
        intro x
        simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.coe_toIntLinearMap,
          Module.Basis.constr_basis, toMul_add, AddMonoidHom.add_apply]
        exact intersectionNumber_mul_of_isClosedImmersion k _ (comp_over _ _)
          (topologicalKrullDim_subscheme_vanishingIdeal_closure_of_mem_pointsOfDimension
            (d := 1) x.property) _ _ }

/-- The pairing on a prime one-cycle is the degree on the reduced closure of its point. -/
@[simp]
theorem cycleIntersectionNumber_basis [CompactSpace X] (a : LineBundleClass X)
    (x : pointsOfDimension X 1) :
    cycleIntersectionNumber k X (Additive.ofMul a) (cyclesOfDimensionBasis X 1 x) =
      intersectionNumber k
        (vanishingIdeal ⟨closure {(x : X)}, isClosed_closure⟩).subschemeι a :=
  (cyclesOfDimensionBasis X 1).constr_basis ℤ _ x

/-- A prime curve with any integer multiplicity pairs by multiplying its degree by
that multiplicity. -/
@[simp]
theorem cycleIntersectionNumber_single [DecidableEq X] (a : LineBundleClass X)
    (x : pointsOfDimension X 1) (n : ℤ) :
    cycleIntersectionNumber k X (Additive.ofMul a)
        ⟨Function.locallyFinsuppWithin.single (x : X) n,
          single_mem_cyclesOfDimension x.property n⟩ =
      n * intersectionNumber k
        (vanishingIdeal ⟨closure {(x : X)}, isClosed_closure⟩).subschemeι a := by
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have hs : (⟨Function.locallyFinsuppWithin.single (x : X) n,
      single_mem_cyclesOfDimension x.property n⟩ : cyclesOfDimension X 1) =
      n • cyclesOfDimensionBasis X 1 x := by
    apply Subtype.ext
    rw [AddSubgroup.coe_zsmul, coe_cyclesOfDimensionBasis]
    ext y
    simp [Function.locallyFinsuppWithin.single_apply, Pi.single_apply]
  rw [hs, map_zsmul, cycleIntersectionNumber_basis, zsmul_eq_mul]
  simp only [Int.cast_id]

/-- Intersection with a one-cycle is the finite sum of its coefficients times the
degrees on the corresponding integral closed curves. -/
theorem cycleIntersectionNumber_eq_sum [CompactSpace X] (a : LineBundleClass X)
    (α : cyclesOfDimension X 1) :
    cycleIntersectionNumber k X (Additive.ofMul a) α =
      ((cyclesOfDimensionBasis X 1).repr α).sum fun x n ↦
        n * intersectionNumber k
          (vanishingIdeal ⟨closure {(x : X)}, isClosed_closure⟩).subschemeι a := by
  exact (cyclesOfDimensionBasis X 1).constr_apply ℤ _ α

/-- The value on the prime cycle represented by an integral closed curve is its
intersection number, regardless of its presentation as a closed subscheme. -/
theorem cycleIntersectionNumber_basis_of_isClosedImmersion [CompactSpace X] {C : Scheme.{u}}
    [C.Over (Spec (.of k))] [IsIntegral C] (ι : C ⟶ X) [IsClosedImmersion ι]
    [ι.IsOver (Spec (.of k))] (x : pointsOfDimension X 1)
    (hx : ι (genericPoint C) = x) (a : LineBundleClass X) :
    cycleIntersectionNumber k X (Additive.ofMul a) (cyclesOfDimensionBasis X 1 x) =
      intersectionNumber k ι a := by
  let I := vanishingIdeal (⟨closure {(x : X)}, isClosed_closure⟩ : Closeds X)
  have hrange : Set.range ι = closure {(x : X)} := by
    rw [← hx, ← Set.image_singleton, ι.isClosedEmbedding.closure_image_eq,
      (genericPoint_spec C).def, Set.image_univ]
  have hI : I ≤ ι.ker := vanishingIdeal_le_ker_of_range_subset ι hrange.le
  let e := IsClosedImmersion.lift I.subschemeι ι (by simpa using hI)
  have he : e ≫ I.subschemeι = ι := IsClosedImmersion.lift_fac _ _ _
  have : IsIso e := ι.isIso_lift_subschemeι_vanishingIdeal hrange
  have heOver : e ≫ I.subscheme ↘ Spec (.of k) = C ↘ Spec (.of k) := by
    rw [← comp_over I.subschemeι (Spec (.of k)), ← Category.assoc, he, comp_over]
  rw [cycleIntersectionNumber_basis, ← he, intersectionNumber_def,
    intersectionNumber_def, ← pullback_comp, eulerDegree_pullback_of_isIso e heOver]

variable {X} {Y : Scheme.{u}} [Y.Over (Spec (.of k))]

omit [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
/-- **Contracted curves.** If a morphism `f : Y ⟶ X` sends a point `x` to a point of height zero,
then the pullback along `f` of every line-bundle class has degree zero on the reduced closure of
`x`: this curve maps into the closed point `f x`, on which every line bundle is trivial. -/
theorem intersectionNumber_pullback_eq_zero_of_height_eq_zero (f : Y ⟶ X) (x : Y)
    (hx : Order.height (f x) = 0) (a : LineBundleClass X) :
    intersectionNumber k (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subschemeι
      (pullback f a) = 0 := by
  set I := vanishingIdeal (⟨closure {x}, isClosed_closure⟩ : Closeds Y)
  set J := vanishingIdeal (⟨closure {f x}, isClosed_closure⟩ : Closeds X)
  have hle : J ≤ (I.subschemeι ≫ f).ker :=
    vanishingIdeal_le_ker_subschemeι_comp f ((Set.mapsTo_singleton.mpr rfl).closure f.continuous)
  rw [intersectionNumber_pullback]
  refine intersectionNumber_eq_zero_of_eq_comp k (I.subschemeι ≫ f)
    (IsClosedImmersion.lift J.subschemeι _ (by simpa using hle)) J.subschemeι
    (IsClosedImmersion.lift_fac _ _ _).symm (t := genericPoint J.subscheme) (fun z ↦ ?_) a
  -- A point of the reduced closure of `f x` is a specialization of `f x`; since `f x` has height
  -- zero, `f x` is in turn a specialization of it.
  rw [← J.subschemeι.isClosedEmbedding.isInducing.specializes_iff,
    subschemeι_genericPoint_vanishingIdeal_closure_singleton]
  have hz : J.subschemeι z ∈ closure {f x} := by
    have : J.subschemeι z ∈ Set.range J.subschemeι := ⟨z, rfl⟩
    rwa [range_subschemeι, coe_support_vanishingIdeal] at this
  exact (Order.height_eq_zero.mp hx) (specializes_iff_mem_closure.mpr hz)

variable [IsProper (Y ↘ Spec (.of k))]

/-- **The projection formula for a curve mapping onto a curve.** Let `f : Y ⟶ X` be a morphism of
proper schemes over `k`, and let `x` and `y = f x` be points of dimension one. Then the pullback
along `f` of a line-bundle class has degree `[κ(x) : κ(y)] · (a · C)` on the reduced closure of
`x`, where `C` is the reduced closure of `y`. -/
theorem intersectionNumber_pullback_eq_residueDegree_mul (f : Y ⟶ X) [f.IsOver (Spec (.of k))]
    (x : pointsOfDimension Y 1) (y : pointsOfDimension X 1) (hxy : f x = y)
    (a : LineBundleClass X) :
    intersectionNumber k (vanishingIdeal ⟨closure {(x : Y)}, isClosed_closure⟩).subschemeι
        (pullback f a) =
      f.residueDegree x *
        intersectionNumber k
          (vanishingIdeal ⟨closure {(y : X)}, isClosed_closure⟩).subschemeι a := by
  set I := vanishingIdeal (⟨closure {(x : Y)}, isClosed_closure⟩ : Closeds Y)
  set J := vanishingIdeal (⟨closure {(y : X)}, isClosed_closure⟩ : Closeds X)
  have hI :=
    topologicalKrullDim_subscheme_vanishingIdeal_closure_of_mem_pointsOfDimension x.property
  have hJ :=
    topologicalKrullDim_subscheme_vanishingIdeal_closure_of_mem_pointsOfDimension y.property
  -- `f` restricts to a morphism `g` from the reduced closure of `x` to that of `y`.
  have hle : J ≤ (I.subschemeι ≫ f).ker :=
    vanishingIdeal_le_ker_subschemeι_comp f ((Set.mapsTo_singleton.mpr hxy).closure f.continuous)
  let g := IsClosedImmersion.lift J.subschemeι (I.subschemeι ≫ f) (by simpa using hle)
  have hg : g ≫ J.subschemeι = I.subschemeι ≫ f := IsClosedImmersion.lift_fac _ _ _
  have : g.IsOver (Spec (.of k)) := ⟨by
    rw [over_eq_subschemeι_comp, over_eq_subschemeι_comp, ← Category.assoc, hg, Category.assoc,
      comp_over]⟩
  have : IsProper (I.subscheme ↘ Spec (.of k)) := by
    rw [over_eq_subschemeι_comp]; infer_instance
  have : IsProper (J.subscheme ↘ Spec (.of k)) := by
    rw [over_eq_subschemeι_comp]; infer_instance
  have : IsProper (g ≫ J.subscheme ↘ Spec (.of k)) := by
    rw [comp_over]; infer_instance
  have : IsProper g := .of_comp g (J.subscheme ↘ Spec (.of k))
  have hgen : g (genericPoint I.subscheme) = genericPoint J.subscheme := by
    apply J.subschemeι.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply,
      subschemeι_genericPoint_vanishingIdeal_closure_singleton,
      subschemeι_genericPoint_vanishingIdeal_closure_singleton, hxy]
  have : IsDominant g := isDominant_iff_genericPoint_eq.mpr hgen
  have : IsFinite g := isFinite_of_isDominant_of_topologicalKrullDim_eq_one k g
    (by exact_mod_cast hI) (by exact_mod_cast hJ)
  have : RelativeDimensionLE 1 (J.subscheme ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr hJ.le
  have := Scheme.Modules.finiteDimensional_cohomology_trivial_of_topologicalKrullDim_le_one k
    (X := I.subscheme) hI.le
  have := Scheme.Modules.finiteDimensional_cohomology_trivial_of_topologicalKrullDim_le_one k
    (X := J.subscheme) hJ.le
  -- The finite projection formula, with `[K(C') : K(C)]` the residue degree of `g`, hence of `f`.
  rw [intersectionNumber_pullback_of_isDominant k g J.subschemeι f hg.symm,
    g.finrank_fieldRange_functionFieldMap_eq_residueDegree]
  have hdeg := congrArg (fun φ ↦ φ.residueDegree (genericPoint I.subscheme)) hg
  simp only [Scheme.Hom.residueDegree_comp, Scheme.Hom.residueDegree_eq_one_of_surjectiveOnStalks,
    one_mul, mul_one] at hdeg
  rw [hdeg, subschemeι_genericPoint_vanishingIdeal_closure_singleton]

/-- **The projection formula for one-cycles.** For a morphism `f : Y ⟶ X` of proper schemes over
`k`, a line-bundle class `a` on `X` and a one-cycle `α` on `Y`, `(a · f_* α) = (f^* a · α)`, where
`f_*` is the pushforward of cycles: a prime curve `C'` on `Y` mapping onto a curve `C` is sent to
`[κ(C') : κ(C)] C`, and one contracted to a point is sent to zero. -/
theorem cycleIntersectionNumber_cyclesMap (f : Y ⟶ X) [f.IsOver (Spec (.of k))]
    (a : LineBundleClass X) (α : cyclesOfDimension Y 1) :
    letI : QuasiCompact f := by
      have : IsProper (f ≫ X ↘ Spec (.of k)) := by rw [comp_over]; infer_instance
      have : IsProper f := .of_comp f (X ↘ Spec (.of k))
      infer_instance
    cycleIntersectionNumber k X (Additive.ofMul a) (cyclesMap k f α) =
      cycleIntersectionNumber k Y (Additive.ofMul (pullback f a)) α := by
  have : IsProper (f ≫ X ↘ Spec (.of k)) := by rw [comp_over]; infer_instance
  have : IsProper f := .of_comp f (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  classical
  suffices h : (cycleIntersectionNumber k X (Additive.ofMul a)).comp (cyclesMap k f) =
      cycleIntersectionNumber k Y (Additive.ofMul (pullback f a)) from DFunLike.congr_fun h α
  apply AddMonoidHom.toIntLinearMap_injective
  apply (cyclesOfDimensionBasis Y 1).ext
  intro x
  simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.comp_apply]
  rw [cycleIntersectionNumber_basis]
  have hx : Order.height (x : Y) = 1 := by
    obtain ⟨n, hn, hn'⟩ := mem_pointsOfDimension.mp x.property
    rw [hn]; exact_mod_cast hn'
  have hmap : (cyclesMap k f (cyclesOfDimensionBasis Y 1 x) : AlgebraicCycle X ℤ) =
      Function.locallyFinsuppWithin.single (f x) (f.residueDegree x : ℤ) := by
    rw [coe_cyclesMap, coe_cyclesOfDimensionBasis, AlgebraicCycle.map_height_single k, one_mul]
  -- The proper map `f` does not raise heights, so the image of the curve is a point or a curve.
  rcases ((f.isClosedMap.specializingMap.height_apply_le_height (x : Y)).trans
    hx.le).lt_or_eq with h0 | h1
  · -- The curve is contracted to a closed point: both sides vanish.
    rw [Order.lt_one_iff] at h0
    have hdeg : f.residueDegree x = 0 := by
      by_contra hne
      have := height_apply_eq_height_of_residueDegree_ne_zero k f hne
      rw [h0, hx] at this
      exact zero_ne_one this
    have : cyclesMap k f (cyclesOfDimensionBasis Y 1 x) = 0 :=
      Subtype.ext (by rw [hmap, hdeg]; simp)
    rw [this, map_zero, intersectionNumber_pullback_eq_zero_of_height_eq_zero k f x h0]
  · -- The curve maps onto a curve, with degree the residue degree at its generic point.
    let y : pointsOfDimension X 1 := ⟨f x, mem_pointsOfDimension.mpr ⟨1, h1, rfl⟩⟩
    have : cyclesMap k f (cyclesOfDimensionBasis Y 1 x) =
        ⟨Function.locallyFinsuppWithin.single (y : X) (f.residueDegree x : ℤ),
          single_mem_cyclesOfDimension y.property _⟩ := Subtype.ext hmap
    rw [this, cycleIntersectionNumber_single,
      intersectionNumber_pullback_eq_residueDegree_mul k f x y rfl]

end LineBundleClass

end TauCeti.AlgebraicGeometry
