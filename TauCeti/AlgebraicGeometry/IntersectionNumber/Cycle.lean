/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.TopDimension
public import TauCeti.AlgebraicGeometry.Chow.Pushforward
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
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
curve as a reduced closed subscheme. This is the numerical pairing used in projection
formulas for pushforward of one-cycles.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1, intersection numbers
  of line bundles with cycles of proper curves.
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

/-- Restricting a line bundle to a closed subscheme and pairing with a one-cycle there
agrees with pairing the original line bundle with the pushforward cycle. -/
theorem cycleIntersectionNumber_cyclesMap_of_isClosedImmersion
    {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    (i : Y ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (a : LineBundleClass X) (α : cyclesOfDimension Y 1) :
    letI : IsProper (Y ↘ Spec (.of k)) := by
      rw [← comp_over i (Spec (.of k))]; infer_instance
    cycleIntersectionNumber k X (Additive.ofMul a) (cyclesMap k i α) =
      cycleIntersectionNumber k Y (Additive.ofMul (pullback i a)) α := by
  let : IsProper (Y ↘ Spec (.of k)) := by
    rw [← comp_over i (Spec (.of k))]; infer_instance
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  classical
  suffices h : (cycleIntersectionNumber k X (Additive.ofMul a)).comp (cyclesMap k i) =
      cycleIntersectionNumber k Y (Additive.ofMul (pullback i a)) from DFunLike.congr_fun h α
  apply AddMonoidHom.toIntLinearMap_injective
  apply (cyclesOfDimensionBasis Y 1).ext
  intro x
  let y : pointsOfDimension X 1 := ⟨i x, by
    simpa only [mem_pointsOfDimension, i.height_apply_eq_height] using x.property⟩
  have hmap : cyclesMap k i (cyclesOfDimensionBasis Y 1 x) = cyclesOfDimensionBasis X 1 y := by
    apply Subtype.ext
    rw [coe_cyclesMap, coe_cyclesOfDimensionBasis, coe_cyclesOfDimensionBasis,
      AlgebraicCycle.map_height_single k]
    simp only [Scheme.Hom.residueDegree_eq_one_of_surjectiveOnStalks, Nat.cast_one, mul_one, y]
  simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.comp_apply, hmap]
  rw [cycleIntersectionNumber_basis_of_isClosedImmersion k X
    ((vanishingIdeal ⟨closure {(x : Y)}, isClosed_closure⟩).subschemeι ≫ i) y
    (by simp [y]), cycleIntersectionNumber_basis, intersectionNumber_pullback]

end LineBundleClass

end TauCeti.AlgebraicGeometry
