/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import TauCeti.Analysis.Normed.Algebra.Logarithm.Inverse
public import TauCeti.Geometry.Lie.Exponential.Units.Basic
public import TauCeti.Topology.Algebra.Group.Connected
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Exponentials and the identity component of the unit group of a Banach algebra

Let `A` be a real Banach algebra; complex Banach algebras are included, through their underlying
real structure. Its unit group `Aˣ` is an open subset of `A`, so it is locally path connected, and
its identity component `Subgroup.connectedComponentOfOne Aˣ` is also the path component of `1`.
This file describes that component in two ways.

* **Products of exponentials.** For `x : A` the path `t ↦ exp (t • x)` joins `1` to `exp x`
  inside `Aˣ`, so every exponential lies in the identity component. Conversely every element
  near `1` is an exponential (`NormedSpace.range_exp_mem_nhds_one`, from the local logarithm), and
  a neighbourhood of `1` inside the identity component generates it. Since `(exp x)⁻¹ = exp (-x)`,
  the identity component consists exactly of the finite products `exp x₁ * ⋯ * exp xₖ`.
* **The unit ball about `1`.** Every `g` with `‖g - 1‖ < 1` is a unit, and the segment from `1`
  to `g` stays in that ball, so the ball is a connected neighbourhood of `1` in `Aˣ`. Hence it
  also generates the identity component. This part, and local path connectedness, only need a
  real normed algebra with summable geometric series.

Continuous ring homomorphisms commute with the exponential. Writing an element of the identity
component of the target as a product of exponentials and lifting each exponent shows that a
surjective continuous ring homomorphism `A →+* B` of real Banach algebras maps the identity
component of `Aˣ` onto that of `Bˣ`. Applied to matrix algebras this is the lifting statement used
to compare algebraic `K₁` of a Banach algebra with the stable group of components of its general
linear groups.

## Main results

* `Units.instLocallyPathConnectedSpace`: the unit group of a real normed algebra with summable
  geometric series is locally path connected, so its path components are its connected components.
* `TauCeti.closure_setOf_norm_sub_one_lt_eq_connectedComponentOfOne`: the unit ball about `1`
  generates the identity component.
* `TauCeti.expUnit_mem_connectedComponentOfOne`: exponentials lie in the identity component.
* `TauCeti.closure_range_expUnit_eq_connectedComponentOfOne`: the exponentials generate the
  identity component.
* `TauCeti.mem_connectedComponentOfOne_iff_exists_prod_exp`: the identity component consists of
  the finite products of exponentials.
* `RingHom.map_connectedComponentOfOne_units_eq_of_surjective`: a surjective continuous ring
  homomorphism maps the identity component onto the identity component.

## References

* G. Horváth and T. Kania, *Twisting exponential spectra*, Lemmas 2.1 and 2.2.
* S. Shirbisheh, *Lectures on C⋆-algebras*, Problem 2.8.
-/

public section

open NormedSpace Topology

/-- The unit group of a real normed algebra with summable geometric series, for instance of a
real or complex Banach algebra, is locally path connected: it is an open subset of a normed
space. Consequently its path components and connected components agree
(`pathComponent_eq_connectedComponent`). -/
instance Units.instLocallyPathConnectedSpace {A : Type*} [NormedRing A] [HasSummableGeomSeries A]
    [NormedSpace ℝ A] : LocallyPathConnectedSpace Aˣ :=
  Units.isOpenEmbedding_val.locallyPathConnectedSpace

namespace TauCeti

section UnitBall

variable {A : Type*} [NormedRing A]

private theorem one_mem_setOf_norm_sub_one_lt : (1 : Aˣ) ∈ {u : Aˣ | ‖(u : A) - 1‖ < 1} := by
  simp only [Set.mem_ofPred_eq, Units.val_one, sub_self, norm_zero, zero_lt_one]

variable [HasSummableGeomSeries A] [NormedSpace ℝ A]

/-- The units at distance less than one from `1` form a preconnected set. -/
private theorem isPreconnected_setOf_norm_sub_one_lt :
    IsPreconnected {u : Aˣ | ‖(u : A) - 1‖ < 1} := by
  -- The coercion is an embedding which maps this set onto the convex unit ball about `1`.
  have himage : (Units.val : Aˣ → A) '' {u | ‖(u : A) - 1‖ < 1} = Metric.ball 1 1 := by
    ext a
    refine ⟨fun ⟨u, hu, hua⟩ ↦ by simpa [← hua, dist_eq_norm] using hu, fun ha ↦ ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at ha
    refine ⟨Units.oneSub (1 - a) (by simpa [norm_sub_rev] using ha), ?_, by simp⟩
    simpa using ha
  rw [← Units.isOpenEmbedding_val.isEmbedding.isInducing.isPreconnected_image, himage]
  exact (convex_ball 1 1).isPreconnected

/-- **The unit ball about `1` generates the identity component of the unit group of a Banach
algebra.** More generally this holds for a real normed algebra with summable geometric series. -/
theorem closure_setOf_norm_sub_one_lt_eq_connectedComponentOfOne :
    Subgroup.closure {u : Aˣ | ‖(u : A) - 1‖ < 1} = Subgroup.connectedComponentOfOne Aˣ := by
  refine Subgroup.closure_eq_connectedComponentOfOne_of_mem_nhds_one_of_subset ?_
    (isPreconnected_setOf_norm_sub_one_lt.subset_connectedComponent one_mem_setOf_norm_sub_one_lt)
  have hopen : IsOpen {u : Aˣ | ‖(u : A) - 1‖ < 1} :=
    isOpen_lt (Units.continuous_val.sub continuous_const).norm continuous_const
  exact hopen.mem_nhds one_mem_setOf_norm_sub_one_lt

end UnitBall

section Exponential

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance] normedAlgebraRatOfReal

/-- An exponential lies in the identity component of the unit group: the path `t ↦ exp (t • x)`
joins `1` to `exp x`. -/
theorem expUnit_mem_connectedComponentOfOne (x : A) :
    expUnit x ∈ Subgroup.connectedComponentOfOne Aˣ := by
  have hg : Continuous fun t : ℝ ↦ expUnit (t • x) :=
    continuous_expUnit.comp (continuous_id.smul continuous_const)
  rw [Subgroup.mem_connectedComponentOfOne_iff]
  exact (isPreconnected_range hg).subset_connectedComponent ⟨0, by simp⟩ ⟨1, by simp⟩

/-- **The exponentials generate the identity component of the unit group of a Banach
algebra.** -/
theorem closure_range_expUnit_eq_connectedComponentOfOne :
    Subgroup.closure (Set.range (expUnit : A → Aˣ)) = Subgroup.connectedComponentOfOne Aˣ := by
  refine Subgroup.closure_eq_connectedComponentOfOne_of_mem_nhds_one_of_subset ?_
    (Set.range_subset_iff.2 expUnit_mem_connectedComponentOfOne)
  -- A unit close to `1` is close to `1` in `A`, where it is an exponential.
  have hnhds : (Units.val ⁻¹' Set.range exp : Set Aˣ) ∈ 𝓝 1 :=
    Units.continuous_val.continuousAt.preimage_mem_nhds (by simpa using range_exp_mem_nhds_one A)
  refine Filter.mem_of_superset hnhds fun u ⟨x, hx⟩ ↦ ⟨x, Units.ext ?_⟩
  simpa using hx

/-- The value of a product of exponential units is the product of the exponentials. -/
private theorem val_prod_map_expUnit (l : List A) :
    ((l.map expUnit).prod : A) = (l.map exp).prod := by
  rw [← Units.coeHom_apply, map_list_prod, List.map_map]
  simp [Function.comp_def]

/-- **The identity component of the unit group of a Banach algebra consists of the finite
products of exponentials.** A unit `u` lies in it exactly when `u = exp x₁ * ⋯ * exp xₖ` for some
list `[x₁, …, xₖ]` of elements of `A`. -/
theorem mem_connectedComponentOfOne_iff_exists_prod_exp {u : Aˣ} :
    u ∈ Subgroup.connectedComponentOfOne Aˣ ↔ ∃ l : List A, (l.map exp).prod = u := by
  refine ⟨fun hu ↦ ?_, fun ⟨l, hl⟩ ↦ ?_⟩
  · -- The exponential units are closed under inversion, so the subgroup they generate is the
    -- submonoid they generate, whose elements are finite products.
    rw [← closure_range_expUnit_eq_connectedComponentOfOne, ← Subgroup.mem_toSubmonoid,
      Subgroup.closure_toSubmonoid] at hu
    suffices ∃ l : List A, (l.map expUnit).prod = u from
      this.imp fun l hl ↦ by rw [← val_prod_map_expUnit, hl]
    induction hu using Submonoid.closure_induction with
    | mem v hv =>
      rcases hv with ⟨x, rfl⟩ | ⟨x, hx⟩
      · exact ⟨[x], by simp⟩
      · exact ⟨[-x], by simp [hx]⟩
    | one => exact ⟨[], by simp⟩
    | mul v w _ _ hv hw =>
      obtain ⟨l₁, rfl⟩ := hv
      obtain ⟨l₂, rfl⟩ := hw
      exact ⟨l₁ ++ l₂, by simp⟩
  · obtain rfl : (l.map expUnit).prod = u := Units.ext (by rw [val_prod_map_expUnit, hl])
    exact Subgroup.list_prod_mem _ (by simpa using fun x _ ↦ expUnit_mem_connectedComponentOfOne x)

end Exponential

end TauCeti

namespace RingHom

open TauCeti

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormedRing B]
  [NormedAlgebra ℝ B] [CompleteSpace B]

attribute [local instance] normedAlgebraRatOfReal

/-- **A surjective continuous ring homomorphism of Banach algebras maps the identity component of
the unit group onto the identity component.** Each factor of a product of exponentials in the
target lifts to an exponential in the source. -/
theorem map_connectedComponentOfOne_units_eq_of_surjective (f : A →+* B) (hf : Continuous f)
    (hsurj : Function.Surjective f) :
    (Subgroup.connectedComponentOfOne Aˣ).map (Units.map (f : A →* B)) =
      Subgroup.connectedComponentOfOne Bˣ := by
  refine le_antisymm (Subgroup.map_connectedComponentOfOne_le (Units.continuous_map hf))
    fun v hv ↦ ?_
  obtain ⟨l, hl⟩ := mem_connectedComponentOfOne_iff_exists_prod_exp.mp hv
  obtain rfl : (l.map expUnit).prod = v := Units.ext (by rw [val_prod_map_expUnit, hl])
  -- Lift the exponents through `f`; the product of their exponentials maps to `v`.
  refine ⟨((l.map (Function.surjInv hsurj)).map expUnit).prod,
    Subgroup.list_prod_mem _ (by simpa using fun b _ ↦ expUnit_mem_connectedComponentOfOne _), ?_⟩
  rw [map_list_prod, List.map_map, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun b _ ↦ Units.ext (by
    simp [map_exp f hf, Function.surjInv_eq hsurj]))

end RingHom
