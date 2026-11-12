/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sphere.StandardCircle
import Mathlib.Topology.Maps.Proper.Basic
import TauCeti.Topology.Homotopy.Path

/-!
# Families of loops as maps from the circle, and conjugate loops

The standard parametrization `circleLoop : I¹ → S¹` of the circle is a proper quotient map, so
for every space `P` the product `P × I¹ → P × S¹` is again a quotient map. A family of closed
paths parametrized by `P` therefore descends to a map `P × S¹ → Z`
(`TauCeti.circleFamilyLift`); in particular a continuous family of loops `ℓ a`, `a ∈ A`, is a map
`A × S¹ → Z` (`TauCeti.loopFamilyCircleMap`), with no compactness assumption on `A`. For a single
loop this is the identification of closed paths with maps from the circle
(`TauCeti.circleMapHomeomorphClosedUnitPath`, on the complex circle); without local compactness of
the parameter space, families cannot be obtained from it by currying. The circle here is `S¹ ⊆ ℝ²`
with `circleLoop`, the model of `TauCeti.BasedTopologicalSpace.basedMapCircleHomeomorph`.

The main result is that conjugating loops by paths does not change their free homotopy class, in
families: for continuous families of paths `χ a` and of loops `ℓ a` at the end points of the
`χ a`, the maps `A × S¹ → Z` given by `χ a · ℓ a · (χ a)⁻¹` and by `ℓ a` are homotopic
(`TauCeti.homotopic_loopFamilyCircleMap_trans_symm`). The homotopy is the explicit homotopy of
families of closed paths `Path.homotopicWith_uncurry_trans_trans_symm`, descended to the circle: at
time `r` it runs along `χ a` from `χ a r` to its end, along `ℓ a` on a middle interval which grows
to the whole interval as `r` tends to `1`, and back along `χ a`.

Such a conjugation is how a family of loops is moved to a fixed base point, for instance to turn a
family of loops of loops into a family of double loops, and this result compares the evaluation of
the conjugated family on the circle with that of the original one.

## Main declarations

* `TauCeti.isQuotientMap_prodMap_id_circleLoop`: `P × I¹ → P × S¹` is a quotient map.
* `TauCeti.circleFamilyLift`, `TauCeti.circleFamilyLift_apply_circleLoop`: a family of closed paths
  as a map `P × S¹ → Z`.
* `TauCeti.ext_circleLoop`: maps `P × S¹ → Z` agreeing along `circleLoop` are equal.
* `TauCeti.loopFamilyCircleMap`, `TauCeti.loopFamilyCircleMap_apply_circleLoop`: a continuous family
  of loops as a map `A × S¹ → Z`.
* `TauCeti.homotopic_loopFamilyCircleMap_trans_symm`: conjugate families of loops are homotopic as
  maps `A × S¹ → Z`.
-/

public section

noncomputable section

open Topology
open scoped unitInterval

namespace TauCeti

variable {P Z A : Type*} [TopologicalSpace P] [TopologicalSpace Z] [TopologicalSpace A]
  {x y : A → Z}

/-- The product of the identity of `P` with the standard parametrization `circleLoop` of the
circle is a quotient map `P × I¹ → P × S¹`, for every space `P`, since it is proper. -/
theorem isQuotientMap_prodMap_id_circleLoop :
    IsQuotientMap ((ContinuousMap.id P).prodMap circleLoop) :=
  (isProperMap_id.prodMap circleLoop.continuous.isProperMap).isClosedMap.isQuotientMap
    (continuous_id.prodMap circleLoop.continuous)
    (Function.surjective_id.prodMap circleLoop_surjective)

/-- The family `G` read on the cube `P × I¹`. -/
private def circleFamilyLiftAux (G : C(P × I, Z)) : C(P × (Fin 1 → I), Z) :=
  G.comp ⟨fun x => (x.1, x.2 0), by fun_prop⟩

private theorem factorsThrough_circleFamilyLiftAux (G : C(P × I, Z))
    (hG : ∀ p, G (p, 0) = G (p, 1)) :
    Function.FactorsThrough (circleFamilyLiftAux G) ((ContinuousMap.id P).prodMap circleLoop) := by
  rintro ⟨p, s⟩ ⟨p', s'⟩ h
  simp only [ContinuousMap.prodMap_apply, ContinuousMap.id_apply, Prod.map, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [circleFamilyLiftAux, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rcases eq_or_of_circleLoop_eq h with rfl | ⟨hs, hs'⟩
  · rfl
  · rw [Cube.boundary_fin_one_iff] at hs hs'
    rcases hs with hs | hs <;> rcases hs' with hs' | hs' <;> simp [hs, hs', hG]

/-- A family of closed paths `G (p, ·)` on the unit interval, parametrized by `p ∈ P`, descends
along the standard parametrization `circleLoop` of the circle to a map `P × S¹ → Z`. -/
def circleFamilyLift (G : C(P × I, Z)) (hG : ∀ p, G (p, 0) = G (p, 1)) : C(P × Sphere1, Z) :=
  isQuotientMap_prodMap_id_circleLoop.lift _ (factorsThrough_circleFamilyLiftAux G hG)

@[simp]
theorem circleFamilyLift_apply_circleLoop (G : C(P × I, Z)) (hG : ∀ p, G (p, 0) = G (p, 1))
    (p : P) (t : Fin 1 → I) : circleFamilyLift G hG (p, circleLoop t) = G (p, t 0) :=
  DFunLike.congr_fun (isQuotientMap_prodMap_id_circleLoop.lift_comp _
    (factorsThrough_circleFamilyLiftAux G hG)) (p, t)

/-- Maps `P × S¹ → Z` are determined by their values along `circleLoop`. -/
theorem ext_circleLoop {f g : C(P × Sphere1, Z)}
    (h : ∀ p t, f (p, circleLoop t) = g (p, circleLoop t)) : f = g := by
  ext ⟨p, z⟩
  obtain ⟨t, rfl⟩ := circleLoop_surjective z
  exact h p t

/-- A continuous family of loops `ℓ a`, `a ∈ A`, read as a map `A × S¹ → Z` through the
standard parametrization of the circle. -/
def loopFamilyCircleMap (ℓ : ∀ a, Path (y a) (y a)) (hℓ : Continuous ↿ℓ) :
    C(A × Sphere1, Z) :=
  circleFamilyLift ⟨↿ℓ, hℓ⟩ fun a => (ℓ a).source.trans (ℓ a).target.symm

@[simp]
theorem loopFamilyCircleMap_apply_circleLoop (ℓ : ∀ a, Path (y a) (y a))
    (hℓ : Continuous ↿ℓ) (a : A) (t : Fin 1 → I) :
    loopFamilyCircleMap ℓ hℓ (a, circleLoop t) = ℓ a (t 0) :=
  circleFamilyLift_apply_circleLoop _ _ a t

/-- **Conjugate loops are freely homotopic**, in families: for continuous families of paths
`χ a` from `x a` to `y a` and of loops `ℓ a` at `y a`, the family of loops `χ a · ℓ a · (χ a)⁻¹`
at `x a` and the family `ℓ a`, read as maps `A × S¹ → Z`, are homotopic. -/
theorem homotopic_loopFamilyCircleMap_trans_symm (χ : ∀ a, Path (x a) (y a)) (hχ : Continuous ↿χ)
    (ℓ : ∀ a, Path (y a) (y a)) (hℓ : Continuous ↿ℓ) :
    (loopFamilyCircleMap (fun a => ((χ a).trans (ℓ a)).trans (χ a).symm)
        (Path.trans_continuous_family _ (Path.trans_continuous_family _ hχ _ hℓ) _
          (Path.symm_continuous_family _ hχ))).Homotopic
      (loopFamilyCircleMap ℓ hℓ) := by
  obtain ⟨H⟩ := Path.homotopicWith_uncurry_trans_trans_symm χ hχ ℓ hℓ
  let K : C((I × A) × I, Z) :=
    H.toContinuousMap.comp ⟨fun q => (q.1.1, (q.1.2, q.2)), by fun_prop⟩
  have hK (q : I × A) : K (q, 0) = K (q, 1) := H.prop q.1 q.2
  refine ⟨{ toContinuousMap := (circleFamilyLift K hK).comp ⟨fun q : I × (A × Sphere1) =>
      ((q.1, q.2.1), q.2.2), by fun_prop⟩, map_zero_left := ?_, map_one_left := ?_ }⟩
  all_goals
    rintro ⟨a, z⟩
    obtain ⟨t, rfl⟩ := circleLoop_surjective z
    simp [K, Function.HasUncurry.uncurry]

end TauCeti
