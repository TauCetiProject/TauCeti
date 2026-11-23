/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Signed homological orientations in dimension zero

A smooth orientation of a zero-dimensional manifold selects the positive or negative class of
its point in integral local homology. The sign is that of the given tangent orientation, relative
to the canonical empty-basis orientation. Different components may carry different signs.

The signed point classes are compatible with local homology transport, restriction, and
orientation-preserving maps.

## Main results

* `TauCeti.Manifold.Orientation.toHomologicalOrientationOfZeroDim`: the signed native homological
  orientation determined by the given smooth orientation.
* `TauCeti.Manifold.Orientation.localOrientationOfZeroDim_coe` and
  `TauCeti.Manifold.Orientation.localOrientationOfZeroDim_eq_ite`: the intrinsic point class and
  its formula in every zero-dimensional chart.
* `TauCeti.Manifold.Orientation.toHomologicalOrientationOfZeroDim_restrict` and
  `TauCeti.Manifold.Orientation.toHomologicalOrientationOfZeroDim_pullback`: compatibility with
  native restriction and pullback by excision.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 15.
-/

public section

noncomputable section

open CategoryTheory Module Set Topology
open scoped Manifold

universe w v

namespace TauCeti.Manifold.Orientation

variable {M E : Type w} {H : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I 1 M]
  [ChartedSpace E M]

/-- The local integral orientation selected by a zero-dimensional smooth orientation. Its sign
is the actual sign of the tangent orientation relative to the canonical empty-basis orientation. -/
def localOrientationOfZeroDim (o : Manifold.Orientation I M (Fin 0)) (x : M) :
    LocalOrientation M x 0 := by
  classical
  have hE : finrank ℝ E = 0 := o.finrank_eq_zero
  let z := localOrientationOfZeroDimChart (chartAt E x) (mem_chart_source E x) hE
  exact if o.orientationAt x = positiveOrientation then z else -z

open Classical in
/-- The signed local orientation is the positive or negative native relative point class. -/
theorem localOrientationOfZeroDim_coe (o : Manifold.Orientation I M (Fin 0)) (x : M) :
    (o.localOrientationOfZeroDim x).val =
      if o.orientationAt x = positiveOrientation then
        localHomologyPointClass (ModuleCat.of ℤ (ULift.{w} ℤ)) {x} x 1
      else -(localHomologyPointClass (ModuleCat.of ℤ (ULift.{w} ℤ)) {x} x 1) := by
  classical
  unfold localOrientationOfZeroDim
  split_ifs <;>
    simp only [LocalOrientation.coe_neg,
      localOrientationOfZeroDimChart_coe]

open Classical in
/-- In every zero-dimensional chart, the selected local orientation is the chart's actual point
class with the sign of the original tangent orientation. -/
theorem localOrientationOfZeroDim_eq_ite {F : Type w} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (o : Manifold.Orientation I M (Fin 0))
    (φ : OpenPartialHomeomorph M F) {x : M} (hx : x ∈ φ.source) (hF : finrank ℝ F = 0) :
    o.localOrientationOfZeroDim x = if o.orientationAt x = positiveOrientation then
      localOrientationOfZeroDimChart φ hx hF else -localOrientationOfZeroDimChart φ hx hF := by
  classical
  have hE : finrank ℝ E = 0 := o.finrank_eq_zero
  have hz := localOrientationOfZeroDimChart_eq
    (chartAt E x) φ (mem_chart_source E x) hx hE hF
  unfold localOrientationOfZeroDim
  split_ifs
  · exact hz
  · exact congrArg Neg.neg hz

/-- A positive tangent orientation selects the positive point-chart generator. -/
theorem localOrientationOfZeroDim_eq_localOrientationOfZeroDimChart_of_orientationAt_eq
    (o : Manifold.Orientation I M (Fin 0)) (x : M)
    (hx : o.orientationAt x = positiveOrientation) :
    o.localOrientationOfZeroDim x = localOrientationOfZeroDimChart (chartAt E x)
      (mem_chart_source E x) (o.finrank_eq_zero) := by
  classical
  simp [localOrientationOfZeroDim, hx]

/-- A negative tangent orientation selects the negative point-chart generator. -/
theorem localOrientationOfZeroDim_eq_neg_localOrientationOfZeroDimChart_of_orientationAt_eq_neg
    (o : Manifold.Orientation I M (Fin 0)) (x : M)
    (hx : o.orientationAt x = -positiveOrientation) :
    o.localOrientationOfZeroDim x = -localOrientationOfZeroDimChart (chartAt E x)
      (mem_chart_source E x) (o.finrank_eq_zero) := by
  classical
  have hp : -(positiveOrientation : _root_.Orientation ℝ (TangentSpace I x) (Fin 0)) ≠
      positiveOrientation := (Module.Ray.ne_neg_self _).symm
  simp [localOrientationOfZeroDim, hx, hp]

/-- Reversing the smooth orientation reverses its signed local point class. -/
@[simp]
theorem localOrientationOfZeroDim_neg (o : Manifold.Orientation I M (Fin 0)) (x : M) :
    (-o).localOrientationOfZeroDim x = -o.localOrientationOfZeroDim x := by
  classical
  rw [localOrientationOfZeroDim_eq_ite (-o) (chartAt E x) (mem_chart_source E x)
      o.finrank_eq_zero,
    localOrientationOfZeroDim_eq_ite o (chartAt E x) (mem_chart_source E x) o.finrank_eq_zero]
  have hp : -(positiveOrientation : _root_.Orientation ℝ (TangentSpace I x) (Fin 0)) ≠
      positiveOrientation := (Module.Ray.ne_neg_self _).symm
  -- The ray negation instance needs the explicitly typed orientation here: generic `neg_neg`
  -- does not rewrite this double negation at implicit transparency.
  have hpp : - -(positiveOrientation : _root_.Orientation ℝ (TangentSpace I x) (Fin 0)) =
      positiveOrientation :=
    neg_neg (positiveOrientation : _root_.Orientation ℝ (TangentSpace I x) (Fin 0))
  rcases _root_.Orientation.eq_or_eq_neg_of_isEmpty (o.orientationAt x) with h | h <;>
    simp only [orientationAt_neg, h, hpp, hp, ↓reduceIte, neg_neg]

/-- The signed point class retains exactly the tangent orientation at the point. -/
theorem localOrientationOfZeroDim_eq_iff (o o' : Manifold.Orientation I M (Fin 0)) (x : M) :
    o.localOrientationOfZeroDim x = o'.localOrientationOfZeroDim x ↔
      o.orientationAt x = o'.orientationAt x := by
  classical
  have hE : finrank ℝ E = 0 := o.finrank_eq_zero
  let z := localOrientationOfZeroDimChart (chartAt E x) (mem_chart_source E x) hE
  have hz : -z ≠ z := fun h ↦ z.property.neg_ne
    (singularHomologyComplSingletonIsoOfFinrankEqZero (ModuleCat.of ℤ (ULift.{w} ℤ))
      (chartAt E x) (mem_chart_source E x) hE) (congrArg Subtype.val h)
  dsimp only [z] at hz
  have hp : (positiveOrientation : _root_.Orientation ℝ (TangentSpace I x) (Fin 0)) ≠
      -positiveOrientation := Module.Ray.ne_neg_self _
  rw [localOrientationOfZeroDim_eq_ite o (chartAt E x) (mem_chart_source E x) hE,
    localOrientationOfZeroDim_eq_ite o' (chartAt E x) (mem_chart_source E x) hE]
  rcases _root_.Orientation.eq_or_eq_neg_of_isEmpty (o.orientationAt x) with h | h <;>
    rcases _root_.Orientation.eq_or_eq_neg_of_isEmpty (o'.orientationAt x) with h' | h' <;>
      simp [h, h', hp, hp.symm, hz, hz.symm]

/-- A zero-dimensional smooth orientation supplies its signed native homological orientation.
Its value at a point is the relative point class in degree zero,
signed by the tangent orientation. -/
def toHomologicalOrientationOfZeroDim (o : Manifold.Orientation I M (Fin 0)) :
    HomologicalOrientation M E 0 where
  toFun := o.localOrientationOfZeroDim
  localOrientationTransport_toFun' {x y} f := by
    have hE : finrank ℝ E = 0 := o.finrank_eq_zero
    have : Subsingleton E := Module.finrank_zero_iff.1 hE
    have : DiscreteTopology M := ChartedSpace.discreteTopology (H := E) M
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    induction f using Path.Homotopic.Quotient.ind with
    | mk γ =>
      have hxy : x = y := by
        simpa only [Path.source, Path.target] using
          TotallyDisconnectedSpace.eq_of_continuous γ γ.continuous 0 1
      subst y
      have hγ : γ = Path.refl x := by
        apply Path.ext
        funext t
        exact (TotallyDisconnectedSpace.eq_of_continuous γ γ.continuous t 0).trans γ.source
      subst γ
      exact congrArg (fun e ↦ e (o.localOrientationOfZeroDim x))
        (localOrientationTransport_id M E 0 (FundamentalGroupoid.mk x))

/-- The homological orientation evaluates to the signed local point class. -/
@[simp]
theorem toHomologicalOrientationOfZeroDim_apply (o : Manifold.Orientation I M (Fin 0)) (x : M) :
    o.toHomologicalOrientationOfZeroDim x = o.localOrientationOfZeroDim x := by rfl

/-- Reversing a smooth orientation reverses its degree-zero homological orientation. -/
@[simp]
theorem toHomologicalOrientationOfZeroDim_neg (o : Manifold.Orientation I M (Fin 0)) :
    (-o).toHomologicalOrientationOfZeroDim = -o.toHomologicalOrientationOfZeroDim := by
  apply HomologicalOrientation.ext
  intro x
  exact localOrientationOfZeroDim_neg o x

/-- Distinct zero-dimensional smooth orientations have distinct signed homological orientations. -/
theorem toHomologicalOrientationOfZeroDim_injective :
    Function.Injective (toHomologicalOrientationOfZeroDim (I := I) (M := M)) := by
  intro o o' h
  apply Manifold.Orientation.ext
  intro x
  exact (localOrientationOfZeroDim_eq_iff o o' x).1 (DFunLike.congr_fun h x)

open Classical in
/-- Restricting the signed relative point class from any set containing the point gives the
local orientation chosen by the given smooth orientation. -/
theorem localHomologyRestriction_ite_localHomologyPointClass
    (o : Manifold.Orientation I M (Fin 0)) (x : M) {S : Set M} (hx : x ∈ S) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{w} ℤ)) (singleton_subset_iff.2 hx) 0
        (if o.orientationAt x = positiveOrientation then
          localHomologyPointClass (ModuleCat.of ℤ (ULift.{w} ℤ)) S x 1
        else -(localHomologyPointClass (ModuleCat.of ℤ (ULift.{w} ℤ)) S x 1)) =
      (o.localOrientationOfZeroDim x).val := by
  have hval := localHomologyPointClass_restriction_apply
    (ModuleCat.of ℤ (ULift.{w} ℤ)) (singleton_subset_iff.2 hx) x 1
  rw [localOrientationOfZeroDim_coe]
  split_ifs <;> simp only [map_neg, hval]

section Map

variable {N F : Type w} {H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
  [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold I' 1 N]
  [ChartedSpace F N]

/-- The map on native local homology carries the signed local point class to that of its image
for an orientation-preserving map whose point fibre is a singleton. -/
theorem IsOrientationPreservingAt.localHomologyMap_localOrientationOfZeroDim
    {o : Manifold.Orientation I M (Fin 0)} {o' : Manifold.Orientation I' N (Fin 0)}
    {j : C(M, N)} {x : M} (h : IsOrientationPreservingAt o o' j x)
    (hpre : j ⁻¹' {j x} ⊆ {x}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) j hpre 0
        (o.localOrientationOfZeroDim x).val = (o'.localOrientationOfZeroDim (j x)).val := by
  have hval := localHomologyPointClass_map_apply (ModuleCat.of ℤ (ULift.{w} ℤ)) j hpre x 1
  rw [localOrientationOfZeroDim_coe, localOrientationOfZeroDim_coe]
  by_cases hp : o.orientationAt x = positiveOrientation
  · simp only [hp, h.orientationAt_eq_positiveOrientation_iff.mp hp, ↓reduceIte, hval]
  · have hp' : o'.orientationAt (j x) ≠ positiveOrientation :=
      fun hx ↦ hp (h.orientationAt_eq_positiveOrientation_iff.mpr hx)
    simp only [hp, hp', ↓reduceIte, map_neg, hval]

end Map

section Comap

variable {N : Type w} {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold I' 1 N]
  [ChartedSpace E N]

/-- Smooth and homological orientation pullback agree for an orientation-preserving open
embedding, on the existing native orientation carriers. -/
theorem toHomologicalOrientationOfZeroDim_comap
    (o : Manifold.Orientation I M (Fin 0)) (o' : Manifold.Orientation I' N (Fin 0))
    {j : M → N} (hj : IsOpenEmbedding j) (ho : ∀ x, IsOrientationPreservingAt o o' j x) :
    o.toHomologicalOrientationOfZeroDim = o'.toHomologicalOrientationOfZeroDim.comap hj := by
  apply HomologicalOrientation.ext
  intro x
  apply (hj.localOrientationEquiv x 0).injective
  rw [HomologicalOrientation.localOrientationEquiv_comap_apply,
    toHomologicalOrientationOfZeroDim_apply, toHomologicalOrientationOfZeroDim_apply]
  apply Subtype.ext
  rw [IsOpenEmbedding.coe_localOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom]
  exact (ho x).localHomologyMap_localOrientationOfZeroDim _

/-- The construction commutes with the native smooth pullback along an open embedding. -/
theorem toHomologicalOrientationOfZeroDim_pullback
    (o' : Manifold.Orientation I' N (Fin 0)) {j : M → N} (hj : IsOpenEmbedding j)
    (hf : ContMDiff I I' 1 j) (hdf : ∀ x, (mfderiv I I' j x).IsInvertible)
    (hι : Fintype.card (Fin 0) = finrank ℝ E) :
    (o'.pullback hf hdf hι).toHomologicalOrientationOfZeroDim =
      o'.toHomologicalOrientationOfZeroDim.comap hj :=
  toHomologicalOrientationOfZeroDim_comap _ _ hj
    (fun x ↦ isOrientationPreservingAt_pullback _ _ _ _ x)

end Comap

/-- Restricting a smooth orientation to an open subset commutes with the existing homological
orientation restriction by excision. -/
@[simp]
theorem toHomologicalOrientationOfZeroDim_restrict (o : Manifold.Orientation I M (Fin 0))
    (U : TopologicalSpace.Opens M) :
    (o.restrict U).toHomologicalOrientationOfZeroDim (M := U) =
      o.toHomologicalOrientationOfZeroDim.comap (M := U) U.isOpen.isOpenEmbedding_subtypeVal :=
  toHomologicalOrientationOfZeroDim_comap (M := U) _ _ U.isOpen.isOpenEmbedding_subtypeVal
    (fun x ↦ isOrientationPreservingAt_restrict o U x)

end TauCeti.Manifold.Orientation
