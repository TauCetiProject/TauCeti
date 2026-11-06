/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Normed.Group.AddCircle
public import TauCeti.Topology.Instances.AddCircle.UnitInterval
public import TauCeti.Topology.Homotopy.Path

/-!
# Null-homotopic maps from the circle

A continuous map `f : AddCircle p → X` (with `0 < p`) is read as the based loop
`t ↦ f (t * p)` on the unit interval (`ContinuousMap.addCircleLoop`). The map `f` is
null-homotopic exactly when this based loop is homotopic to the constant loop relative to its
endpoints (`ContinuousMap.nullhomotopic_iff_addCircleLoop_homotopic`): a free null-homotopy
collapses the image of the standard loop of the circle, and conversely a path homotopy descends
along the quotient map `I × I → I × AddCircle p`, `(s, t) ↦ (s, t * p)` (built from
`AddCircle.ofUnitInterval`), because it is constant on the two ends `t = 0` and `t = 1`, which are
the only points identified. When `X` is simply connected the based loop is homotopic to the
constant loop, so `f` is null-homotopic
(`ContinuousMap.nullhomotopic_addCircle_of_simplyConnectedSpace`).

Mathlib's `SimplyConnectedSpace` is phrased with based paths; this file supplies its consequence
for free loops parametrised by the circle, which is how circles are compared in conditions such as
simple connectivity at infinity.

Null-homotopy of a loop does not depend on its constant speed: a null-homotopic loop
`g : AddCircle T → X`, run at speed `a ≠ 0` (backwards when `a < 0`), is the null-homotopic loop
`t ↦ g (t * a)` on `AddCircle (T / |a|)` (`ContinuousMap.Nullhomotopic.exists_addCircle_comp_mul`).

## Main declarations

* `ContinuousMap.addCircleLoop`: a map from the circle read as a based loop.
* `ContinuousMap.nullhomotopic_iff_addCircleLoop_homotopic`: a map from the circle is
  null-homotopic exactly when its based loop is null-homotopic.
* `ContinuousMap.nullhomotopic_addCircle_of_simplyConnectedSpace`: every continuous map from a
  circle `AddCircle p` with `0 < p` into a simply connected space is null-homotopic.
* `ContinuousMap.Nullhomotopic.exists_addCircle_comp_mul`: a null-homotopic loop run at constant
  nonzero speed is null-homotopic.
-/

public section

noncomputable section

open Set Topology
open scoped unitInterval

namespace ContinuousMap

variable {p : ℝ} {X : Type*} [TopologicalSpace X]

/-- A map `f` from the circle `AddCircle p`, read as the based loop `t ↦ f (t * p)` at `f 0`. -/
def addCircleLoop (f : C(AddCircle p, X)) : Path (f 0) (f 0) where
  toContinuousMap := f.comp (AddCircle.ofUnitInterval p)
  source' := by simp
  target' := by simp [AddCircle.coe_period]

@[simp]
theorem addCircleLoop_apply (f : C(AddCircle p, X)) (t : I) :
    f.addCircleLoop t = f ((t * p : ℝ) : AddCircle p) :=
  congrArg f (AddCircle.ofUnitInterval_apply t)

/-- **Free and based null-homotopy of a loop.** A map `f` from a circle `AddCircle p` with
`0 < p` is null-homotopic exactly when the based loop `t ↦ f (t * p)` at `f 0` is homotopic to the
constant loop relative to its endpoints. -/
theorem nullhomotopic_iff_addCircleLoop_homotopic [Fact (0 < p)] (f : C(AddCircle p, X)) :
    f.Nullhomotopic ↔ f.addCircleLoop.Homotopic (Path.refl (f 0)) := by
  refine ⟨fun hf ↦ ?_, fun ⟨F⟩ ↦ ?_⟩
  · -- A null-homotopy collapses the image of the standard loop of the circle.
    let ℓ₀ : Path (0 : AddCircle p) 0 :=
      ⟨AddCircle.ofUnitInterval p, AddCircle.ofUnitInterval_zero, AddCircle.ofUnitInterval_one⟩
    exact Path.Homotopic.map_nullhomotopic_of_nullhomotopic hf ℓ₀
  -- Descend the path homotopy `F` along `(s, t) ↦ (s, t * p)`, which only glues the two ends of
  -- the loop parameter, where `F` takes the value `f 0`.
  let q : C(I × I, I × AddCircle p) := (ContinuousMap.id I).prodMap (AddCircle.ofUnitInterval p)
  have hsurj : Function.Surjective q :=
    Function.surjective_id.prodMap AddCircle.surjective_ofUnitInterval
  have hq : IsQuotientMap q := q.continuous.isClosedMap.isQuotientMap q.continuous hsurj
  have hF : Function.FactorsThrough (F.toContinuousMap : I × I → X) q := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ h
    obtain ⟨rfl, h⟩ := Prod.ext_iff.1 h
    obtain rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := AddCircle.ofUnitInterval_eq_ofUnitInterval_iff.1 h
    · rfl
    · exact (F.source s).trans (F.target s).symm
    · exact (F.target s).trans (F.source s).symm
  have hG (s t : I) : hq.lift F.toContinuousMap hF (s, AddCircle.ofUnitInterval p t) = F (s, t) :=
    DFunLike.congr_fun (hq.lift_comp F.toContinuousMap hF) (s, t)
  refine ⟨f 0, ⟨⟨hq.lift F.toContinuousMap hF, fun θ => ?_, fun θ => ?_⟩⟩⟩ <;>
    obtain ⟨t, rfl⟩ := AddCircle.surjective_ofUnitInterval (p := p) θ
  · exact (hG 0 t).trans (F.apply_zero t)
  · exact (hG 1 t).trans (F.apply_one t)

/-- **Every map from a circle into a simply connected space is null-homotopic.** -/
theorem nullhomotopic_addCircle_of_simplyConnectedSpace [Fact (0 < p)] [SimplyConnectedSpace X]
    (f : C(AddCircle p, X)) : f.Nullhomotopic :=
  (nullhomotopic_iff_addCircleLoop_homotopic f).2 (SimplyConnectedSpace.paths_homotopic _ _)

/-- **Constant-speed reparametrization of a null-homotopic loop.** If the loop
`g : AddCircle T → X` is null-homotopic and `a ≠ 0`, then `t ↦ g (t * a)`, a loop of period
`T / |a|` run backwards when `a < 0`, is null-homotopic. -/
theorem Nullhomotopic.exists_addCircle_comp_mul {T a : ℝ} (hT : T ≠ 0) (ha : a ≠ 0)
    {g : C(AddCircle T, X)} (hg : g.Nullhomotopic) :
    ∃ g' : C(AddCircle (T / |a|), X), g'.Nullhomotopic ∧
      ∀ t : ℝ, g' t = g ((t * a : ℝ) : AddCircle T) := by
  -- The reparametrization `ℝ/(T/|a|)ℤ → ℝ/Tℤ`, multiplication by `|a|`.
  let e : C(AddCircle (T / |a|), AddCircle T) :=
    ⟨_, (AddCircle.homeomorphAddCircle (T / |a|) T (div_ne_zero hT (abs_ne_zero.2 ha))
      hT).continuous⟩
  have he (t : ℝ) : e t = ((t * |a| : ℝ) : AddCircle T) := by
    rw [ContinuousMap.coe_mk, AddCircle.homeomorphAddCircle_apply_mk, inv_div,
      div_mul_cancel₀ _ hT]
  rcases ha.lt_or_gt with ha' | ha'
  · -- Backwards: compose further with the reflection of the circle.
    let n : C(AddCircle T, AddCircle T) := ⟨Neg.neg, continuous_neg⟩
    have hn (x : AddCircle T) : n x = -x := rfl
    refine ⟨g.comp (n.comp e), hg.comp_left _, fun t ↦ ?_⟩
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, he, hn, ← AddCircle.coe_neg,
      abs_of_neg ha', mul_neg, neg_neg]
  · refine ⟨g.comp e, hg.comp_left _, fun t ↦ ?_⟩
    rw [ContinuousMap.comp_apply, he, abs_of_pos ha']

end ContinuousMap
