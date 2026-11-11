/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sphere.StandardCircle
import Mathlib.Topology.Maps.Proper.Basic

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
(`TauCeti.homotopic_loopFamilyCircleMap_trans_symm`). The homotopy is explicit: at time `r` it
runs along `χ a` from `χ a r` to its end, along `ℓ a` on a middle interval which grows to the whole
interval as `r` tends to `1`, and back along `χ a`.

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
* `Path.homotopicWith_trans_trans_symm`: a conjugate loop is homotopic to the loop through closed
  paths `I → Z`.
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

/-- The explicit free homotopy from `χ · ℓ · χ⁻¹` to `ℓ`: at time `r` it runs along `χ` from
`χ r` to its end, along `ℓ` on a middle interval that grows to all of `I` as `r → 1`, and back
along `χ` to `χ r`. -/
private def conjHomotopyFun (χ : ∀ a, Path (x a) (y a)) (ℓ : ∀ a, Path (y a) (y a))
    (q : (I × A) × I) : Z :=
  if (q.2 : ℝ) ≤ (1 - q.1.1) / 4 then (χ q.1.2).extend (q.1.1 + 4 * q.2)
  else if (q.2 : ℝ) ≤ (1 + q.1.1) / 2 then
    (ℓ q.1.2).extend ((q.2 - (1 - q.1.1) / 4) / ((1 + 3 * q.1.1) / 4))
  else (χ q.1.2).extend (q.1.1 + 2 * (1 - q.2))

private theorem continuous_conjHomotopyFun (χ : ∀ a, Path (x a) (y a)) (hχ : Continuous ↿χ)
    (ℓ : ∀ a, Path (y a) (y a)) (hℓ : Continuous ↿ℓ) :
    Continuous (conjHomotopyFun χ ℓ) := by
  have hχe := Path.continuous_uncurry_extend_of_continuous_family χ hχ
  have hℓe := Path.continuous_uncurry_extend_of_continuous_family ℓ hℓ
  have hpos : ∀ r : I, (1 + 3 * (r : ℝ)) / 4 ≠ 0 := fun r => by
    have := r.2.1; positivity
  refine Continuous.if_le ?_ (Continuous.if_le ?_ ?_ (by fun_prop) (by fun_prop) ?_)
    (by fun_prop) (by fun_prop) ?_
  · exact hχe.comp ((by fun_prop : Continuous fun q : (I × A) × I => q.1.2).prodMk
      (by fun_prop : Continuous fun q : (I × A) × I => (q.1.1 : ℝ) + 4 * q.2))
  · exact hℓe.comp ((by fun_prop : Continuous fun q : (I × A) × I => q.1.2).prodMk
      ((by fun_prop : Continuous fun q : (I × A) × I => ((q.2 : ℝ) - (1 - q.1.1) / 4)).div
        (by fun_prop) fun q => hpos q.1.1))
  · exact hχe.comp ((by fun_prop : Continuous fun q : (I × A) × I => q.1.2).prodMk
      (by fun_prop : Continuous fun q : (I × A) × I => (q.1.1 : ℝ) + 2 * (1 - q.2)))
  · rintro ⟨⟨r, a⟩, t⟩ (h : (t : ℝ) = (1 + r) / 2)
    simp only [h]
    rw [show ((1 + (r : ℝ)) / 2 - (1 - r) / 4) / ((1 + 3 * r) / 4) = 1 by
        rw [div_eq_one_iff_eq (hpos r)]; ring,
      show (r : ℝ) + 2 * (1 - (1 + r) / 2) = 1 by ring, Path.extend_one, Path.extend_one]
  · rintro ⟨⟨r, a⟩, t⟩ (h : (t : ℝ) = (1 - r) / 4)
    have hle : (1 - (r : ℝ)) / 4 ≤ (1 + r) / 2 := by linarith [r.2.1]
    simp only [h, hle, ite_true]
    rw [show (r : ℝ) + 4 * ((1 - r) / 4) = 1 by ring, sub_self, zero_div, Path.extend_one,
      Path.extend_zero]

omit [TopologicalSpace A] in
private theorem conjHomotopyFun_zero_eq_one (χ : ∀ a, Path (x a) (y a))
    (ℓ : ∀ a, Path (y a) (y a)) (q : I × A) :
    conjHomotopyFun χ ℓ (q, 0) = conjHomotopyFun χ ℓ (q, 1) := by
  obtain ⟨⟨r, hr0, hr1⟩, a⟩ := q
  have h0 : (0 : ℝ) ≤ (1 - r) / 4 := by linarith
  have h1 : ¬ (1 : ℝ) ≤ (1 - r) / 4 := by linarith
  simp only [conjHomotopyFun, Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, add_zero, sub_self]
  simp only [h0, h1, ↓reduceIte]
  rcases hr1.lt_or_eq with hr1 | rfl
  · have h2 : ¬ (1 : ℝ) ≤ (1 + r) / 2 := by linarith
    simp [h2]
  · norm_num [Path.extend_one]

omit [TopologicalSpace A] in
private theorem conjHomotopyFun_zero (χ : ∀ a, Path (x a) (y a)) (ℓ : ∀ a, Path (y a) (y a))
    (a : A) (t : I) :
    conjHomotopyFun χ ℓ ((0, a), t) = (((χ a).trans (ℓ a)).trans (χ a).symm) t := by
  simp only [conjHomotopyFun, Set.Icc.coe_zero, sub_zero, zero_add, mul_zero, Path.trans_apply,
    Path.symm_apply]
  have ht0 := t.2.1
  have ht1 := t.2.2
  split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ <;> try (exfalso; linarith)
  · rw [Path.extend_apply _ ⟨by linarith, by linarith⟩]
    congr 1; ext; simp only; ring
  · rw [show ((t : ℝ) - 1 / 4) / ((1 + 0) / 4) = 2 * (2 * t) - 1 by ring,
      Path.extend_apply _ ⟨by linarith, by linarith⟩]
  · rw [Path.extend_apply _ ⟨by linarith, by linarith⟩]
    simp only [Function.comp_apply, unitInterval.symm]
    congr 1; ext; simp only; ring

omit [TopologicalSpace A] in
private theorem conjHomotopyFun_one (χ : ∀ a, Path (x a) (y a)) (ℓ : ∀ a, Path (y a) (y a))
    (a : A) (t : I) : conjHomotopyFun χ ℓ ((1, a), t) = ℓ a t := by
  have ht0 := t.2.1
  have ht1 := t.2.2
  simp only [conjHomotopyFun, Set.Icc.coe_one, sub_self, zero_div]
  split_ifs with h₁ h₂
  · have ht : t = 0 := Subtype.ext (le_antisymm h₁ ht0)
    subst ht
    simp
  · rw [show ((t : ℝ) - 0) / ((1 + 3 * 1) / 4) = t by ring, Path.extend_apply _ ⟨ht0, ht1⟩]
  · exfalso; linarith

/-- **Conjugate loops are freely homotopic**, in families: for continuous families of paths
`χ a` from `x a` to `y a` and of loops `ℓ a` at `y a`, the family of loops `χ a · ℓ a · (χ a)⁻¹`
at `x a` and the family `ℓ a`, read as maps `A × S¹ → Z`, are homotopic. -/
theorem homotopic_loopFamilyCircleMap_trans_symm (χ : ∀ a, Path (x a) (y a)) (hχ : Continuous ↿χ)
    (ℓ : ∀ a, Path (y a) (y a)) (hℓ : Continuous ↿ℓ) :
    (loopFamilyCircleMap (fun a => ((χ a).trans (ℓ a)).trans (χ a).symm)
        (Path.trans_continuous_family _ (Path.trans_continuous_family _ hχ _ hℓ) _
          (Path.symm_continuous_family _ hχ))).Homotopic
      (loopFamilyCircleMap ℓ hℓ) := by
  let H := circleFamilyLift ⟨conjHomotopyFun χ ℓ, continuous_conjHomotopyFun χ hχ ℓ hℓ⟩
    (conjHomotopyFun_zero_eq_one χ ℓ)
  refine ⟨{ toContinuousMap := H.comp ⟨fun q : I × (A × Sphere1) => ((q.1, q.2.1), q.2.2),
      by fun_prop⟩, map_zero_left := ?_, map_one_left := ?_ }⟩
  all_goals
    rintro ⟨a, z⟩
    obtain ⟨t, rfl⟩ := circleLoop_surjective z
    simp [H, conjHomotopyFun_zero, conjHomotopyFun_one]

/-- **A conjugate loop is homotopic through closed paths to the loop.** For a path `χ` from `a`
to `b` and a loop `ℓ` at `b`, the loop `χ · ℓ · χ⁻¹` at `a` and `ℓ` are homotopic as maps
`I → Z` through maps taking the same value at `0` and at `1`. This is the explicit homotopy of
`TauCeti.homotopic_loopFamilyCircleMap_trans_symm` for a single loop, before it descends to a
circle; through `TauCeti.circleMapHomeomorphClosedUnitPath` it gives the same statement on the
complex circle. -/
theorem _root_.Path.homotopicWith_trans_trans_symm {a b : Z} (χ : Path a b) (ℓ : Path b b) :
    ((((χ.trans ℓ).trans χ.symm : Path a a)) : C(I, Z)).HomotopicWith (ℓ : C(I, Z))
      fun p ↦ p 0 = p 1 :=
  ⟨{ toFun q := conjHomotopyFun (A := Unit) (fun _ ↦ χ) (fun _ ↦ ℓ) ((q.1, ()), q.2)
     continuous_toFun := (continuous_conjHomotopyFun (A := Unit) _
        (χ.continuous.comp continuous_snd) _ (ℓ.continuous.comp continuous_snd)).comp
          (by fun_prop)
     map_zero_left t := conjHomotopyFun_zero (A := Unit) (fun _ ↦ χ) (fun _ ↦ ℓ) () t
     map_one_left t := conjHomotopyFun_one (A := Unit) (fun _ ↦ χ) (fun _ ↦ ℓ) () t
     prop' s := conjHomotopyFun_zero_eq_one (A := Unit) (fun _ ↦ χ) (fun _ ↦ ℓ) (s, ()) }⟩

end TauCeti
