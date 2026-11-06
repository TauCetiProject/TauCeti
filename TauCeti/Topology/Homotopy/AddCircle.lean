/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Normed.Group.AddCircle
public import TauCeti.Topology.Instances.AddCircle.UnitInterval

/-!
# Loops on the unit interval and maps from the circle

A path `c : I → X` with `c 0 = c 1` factors through the quotient map
`AddCircle.ofUnitInterval p : I → AddCircle p`, `t ↦ t * p`, for `0 < p`, which identifies only the
two endpoints (`ContinuousMap.exists_comp_ofUnitInterval_eq`). In the same way a family of loops
`G : I × I → X`, with `G (s, 0) = G (s, 1)` for every `s`, descends along
`I × I → I × AddCircle p`, `(s, t) ↦ (s, t * p)`, to a homotopy between the circle maps read off
its two end loops (`ContinuousMap.homotopic_of_forall_ofUnitInterval`). A family of paths
`L (s, ·)` need not consist of loops: if a family of arcs `C (s, ·)` runs back from the end of each
path to its start, and the arcs at `s = 0` and `s = 1` are constant, then the loops `L (s, ·)`
followed by `C (s, ·)` interpolate between the end loops, which are therefore freely homotopic
(`ContinuousMap.homotopic_of_forall_ofUnitInterval_of_closing`). Such arcs exist when the ends of
the paths lie in a convex set of a chart: take preimages of straight segments
(`ContinuousMap.homotopic_of_forall_ofUnitInterval_of_convex`). This is how a limit of periodic
orbits is compared with the orbits converging to it.

A continuous map `f : AddCircle p → X` (with `0 < p`) is read as the based loop
`t ↦ f (t * p)` on the unit interval. When `X` is simply connected this loop is homotopic to the
constant loop relative to its endpoints, and the descended homotopy is a free null-homotopy of `f`
(`ContinuousMap.nullhomotopic_addCircle_of_simplyConnectedSpace`). Mathlib's
`SimplyConnectedSpace` is phrased with based paths; this supplies its consequence for free loops
parametrised by the circle, which is how circles are compared in conditions such as simple
connectivity at infinity.

Null-homotopy of a loop does not depend on its constant speed: a null-homotopic loop
`g : AddCircle T → X`, run at speed `a ≠ 0` (backwards when `a < 0`), is the null-homotopic loop
`t ↦ g (t * a)` on `AddCircle (T / |a|)` (`ContinuousMap.Nullhomotopic.exists_addCircle_comp_mul`).

## Main declarations

* `ContinuousMap.exists_comp_ofUnitInterval_eq`: a loop on the unit interval is a map from the
  circle.
* `ContinuousMap.homotopic_of_forall_ofUnitInterval`: a closed family of loops is a homotopy of
  circle maps.
* `ContinuousMap.homotopic_of_forall_ofUnitInterval_of_closing`: the end loops of a family of
  paths closed up by a family of arcs, constant at both ends, are freely homotopic.
* `ContinuousMap.homotopic_of_forall_ofUnitInterval_of_convex`: the same, when the ends of the paths
  lie in a convex set of a chart, closed up by straight segments.
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

/-- **Loops on the unit interval are maps from the circle.** A path `c : I → X` with
`c 0 = c 1` factors through the quotient `AddCircle.ofUnitInterval p : I → AddCircle p`, for
`0 < p`. -/
theorem exists_comp_ofUnitInterval_eq [Fact (0 < p)] (c : C(I, X)) (hc : c 0 = c 1) :
    ∃ f : C(AddCircle p, X), ∀ t, f (AddCircle.ofUnitInterval p t) = c t := by
  have hq : IsQuotientMap (AddCircle.ofUnitInterval p) :=
    (AddCircle.ofUnitInterval p).continuous.isClosedMap.isQuotientMap
      (AddCircle.ofUnitInterval p).continuous AddCircle.surjective_ofUnitInterval
  have hc' : Function.FactorsThrough c (AddCircle.ofUnitInterval p) := by
    intro s t h
    obtain rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := AddCircle.ofUnitInterval_eq_ofUnitInterval_iff.1 h
    · rfl
    · exact hc
    · exact hc.symm
  exact ⟨hq.lift c hc', fun t ↦ DFunLike.congr_fun (hq.lift_comp c hc') t⟩

/-- **A closed family of loops is a homotopy of circle maps.** Let `G : I × I → X` be a family
of loops, `G (s, 0) = G (s, 1)` for every `s`. If `f₀` and `f₁` are the circle maps read off the
loops `G (0, ·)` and `G (1, ·)` through `AddCircle.ofUnitInterval p`, `0 < p`, then they are
homotopic. -/
theorem homotopic_of_forall_ofUnitInterval [Fact (0 < p)] {f₀ f₁ : C(AddCircle p, X)}
    (G : C(I × I, X)) (hG : ∀ s, G (s, 0) = G (s, 1))
    (h₀ : ∀ t, f₀ (AddCircle.ofUnitInterval p t) = G (0, t))
    (h₁ : ∀ t, f₁ (AddCircle.ofUnitInterval p t) = G (1, t)) : f₀.Homotopic f₁ := by
  -- Descend `G` along `(s, t) ↦ (s, t * p)`, which only glues the two ends of the loop
  -- parameter, where `G` takes the same value.
  let q : C(I × I, I × AddCircle p) := (ContinuousMap.id I).prodMap (AddCircle.ofUnitInterval p)
  have hsurj : Function.Surjective q :=
    Function.surjective_id.prodMap AddCircle.surjective_ofUnitInterval
  have hq : IsQuotientMap q := q.continuous.isClosedMap.isQuotientMap q.continuous hsurj
  have hG' : Function.FactorsThrough (G : I × I → X) q := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ h
    obtain ⟨rfl, h⟩ := Prod.ext_iff.1 h
    obtain rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := AddCircle.ofUnitInterval_eq_ofUnitInterval_iff.1 h
    · rfl
    · exact hG s
    · exact (hG s).symm
  have hlift (s t : I) : hq.lift G hG' (s, AddCircle.ofUnitInterval p t) = G (s, t) :=
    DFunLike.congr_fun (hq.lift_comp G hG') (s, t)
  refine ⟨⟨hq.lift G hG', fun θ ↦ ?_, fun θ ↦ ?_⟩⟩ <;>
    obtain ⟨t, rfl⟩ := AddCircle.surjective_ofUnitInterval (p := p) θ
  · exact (hlift 0 t).trans (h₀ t).symm
  · exact (hlift 1 t).trans (h₁ t).symm

/-- **Families of paths closed up by families of arcs.** Let `L : I × I → X` be a family of
paths and `C : I × I → X` a family of arcs running back from the end `L (s, 1)` of each path to
its start `L (s, 0)`, with `C (0, ·)` and `C (1, ·)` constant. Then the two end paths `L (0, ·)`
and `L (1, ·)` are loops, and the circle maps `f₀` and `f₁` read off them through
`AddCircle.ofUnitInterval p`, `0 < p`, are homotopic: the loops `L (s, ·)` followed by
`C (s, ·)` interpolate between them. -/
theorem homotopic_of_forall_ofUnitInterval_of_closing [Fact (0 < p)] {f₀ f₁ : C(AddCircle p, X)}
    (L C : C(I × I, X)) (hC₀ : ∀ s, C (s, 0) = L (s, 1)) (hC₁ : ∀ s, C (s, 1) = L (s, 0))
    (hl : ∀ t, C (0, t) = L (0, 0)) (hr : ∀ t, C (1, t) = L (1, 0))
    (h₀ : ∀ t, f₀ (AddCircle.ofUnitInterval p t) = L (0, t))
    (h₁ : ∀ t, f₁ (AddCircle.ofUnitInterval p t) = L (1, t)) : f₀.Homotopic f₁ := by
  let γ₁ (s : I) : Path (L (s, 0)) (L (s, 1)) := ⟨⟨fun t ↦ L (s, t), by fun_prop⟩, rfl, rfl⟩
  let γ₂ (s : I) : Path (L (s, 1)) (L (s, 0)) := ⟨⟨fun t ↦ C (s, t), by fun_prop⟩, hC₀ s, hC₁ s⟩
  -- The closed loops `L (s, ·)` followed by `C (s, ·)`.
  let K : C(I × I, X) := ⟨fun q ↦ ((γ₁ q.1).trans (γ₂ q.1)) q.2,
    Path.trans_continuous_family γ₁ L.continuous γ₂ C.continuous⟩
  have hK (s : I) : K (s, 0) = K (s, 1) := by
    simp only [K, ContinuousMap.coe_mk, Path.source, Path.target]
  -- At either end the arc is constant, so the closed loop is the path followed by a constant
  -- path, which is homotopic to the path relative to its endpoints.
  have hend (i : I) (hi : ∀ t, C (i, t) = L (i, 0)) :
      ∃ k : C(AddCircle p, X), (∀ t, k (AddCircle.ofUnitInterval p t) = K (i, t)) ∧
        ∀ f : C(AddCircle p, X), (∀ t, f (AddCircle.ofUnitInterval p t) = L (i, t)) →
          k.Homotopic f := by
    have hi₁ : L (i, 1) = L (i, 0) := (hC₀ i).symm.trans (hi 0)
    obtain ⟨k, hk⟩ := exists_comp_ofUnitInterval_eq (p := p)
      ⟨fun t ↦ K (i, t), by fun_prop⟩ (hK i)
    have hpt (t : I) : K (i, t) = ((γ₁ i).trans (Path.refl (L (i, 1)))) t := by
      simp only [K, ContinuousMap.coe_mk, Path.trans_apply, Path.refl_apply]
      split_ifs
      · rfl
      · exact (hi _).trans hi₁.symm
    let F := Path.Homotopy.transRefl (γ₁ i)
    refine ⟨k, hk, fun f hf ↦ homotopic_of_forall_ofUnitInterval F.toContinuousMap
      (fun s ↦ ?_) (fun t ↦ ?_) (fun t ↦ ?_)⟩
    · simp only [ContinuousMap.HomotopyWith.coe_toContinuousMap, Path.Homotopy.source,
        Path.Homotopy.target, hi₁]
    · simp only [ContinuousMap.HomotopyWith.coe_toContinuousMap,
        ContinuousMap.HomotopyWith.apply_zero, Path.coe_toContinuousMap, ← hpt]
      exact hk t
    · simp only [ContinuousMap.HomotopyWith.coe_toContinuousMap,
        ContinuousMap.HomotopyWith.apply_one, Path.coe_toContinuousMap]
      exact hf t
  obtain ⟨k₀, hk₀, hk₀f⟩ := hend 0 hl
  obtain ⟨k₁, hk₁, hk₁f⟩ := hend 1 hr
  exact ((hk₀f f₀ h₀).symm.trans (homotopic_of_forall_ofUnitInterval K hK hk₀ hk₁)).trans
    (hk₁f f₁ h₁)

/-- **Families of paths with ends in a convex chart.** Let `e` be a partial equivalence from `X`
to a real topological vector space, continuous on its source with inverse continuous on its
target, and let `B ⊆ e.target` be convex. Let `L : I × I → X` be a family of paths whose ends
`L (s, 0)` and `L (s, 1)` lie in the source of `e` and are sent into `B`, and whose end paths
`L (0, ·)` and `L (1, ·)` are loops. Then the circle maps `f₀` and `f₁` read off these loops
through `AddCircle.ofUnitInterval p`, `0 < p`, are homotopic: each path `L (s, ·)` is closed up by
the preimage of the straight segment in `B` from `e (L (s, 1))` back to `e (L (s, 0))`. -/
theorem homotopic_of_forall_ofUnitInterval_of_convex [Fact (0 < p)] {E : Type*} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {f₀ f₁ : C(AddCircle p, X)} (e : PartialEquiv X E) (he : ContinuousOn e e.source)
    (he' : ContinuousOn e.symm e.target) {B : Set E} (hB : Convex ℝ B) (hBt : B ⊆ e.target)
    (L : C(I × I, X)) (hL₀ : ∀ s, L (s, 0) ∈ e.source ∧ e (L (s, 0)) ∈ B)
    (hL₁ : ∀ s, L (s, 1) ∈ e.source ∧ e (L (s, 1)) ∈ B) (hl : L (0, 1) = L (0, 0))
    (hr : L (1, 1) = L (1, 0)) (h₀ : ∀ t, f₀ (AddCircle.ofUnitInterval p t) = L (0, t))
    (h₁ : ∀ t, f₁ (AddCircle.ofUnitInterval p t) = L (1, t)) : f₀.Homotopic f₁ := by
  have hc (i : I) (hi : ∀ s, L (s, i) ∈ e.source) : Continuous fun s : I ↦ e (L (s, i)) :=
    he.comp_continuous (L.continuous.comp (by fun_prop : Continuous fun s : I ↦ (s, i))) hi
  have hseg (z : I × I) : (1 - (z.2 : ℝ)) • e (L (z.1, 1)) + (z.2 : ℝ) • e (L (z.1, 0)) ∈ B :=
    hB (hL₁ z.1).2 (hL₀ z.1).2 (sub_nonneg.2 z.2.2.2) z.2.2.1 (by ring)
  -- The arcs closing up the paths: preimages of straight segments in `B`.
  let C : C(I × I, X) :=
    ⟨fun z ↦ e.symm ((1 - (z.2 : ℝ)) • e (L (z.1, 1)) + (z.2 : ℝ) • e (L (z.1, 0))),
      he'.comp_continuous (((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
        ((hc 1 fun s ↦ (hL₁ s).1).comp continuous_fst)).add
          ((continuous_subtype_val.comp continuous_snd).smul
            ((hc 0 fun s ↦ (hL₀ s).1).comp continuous_fst))) fun z ↦ hBt (hseg z)⟩
  have hC (s t : I) :
      C (s, t) = e.symm ((1 - (t : ℝ)) • e (L (s, 1)) + (t : ℝ) • e (L (s, 0))) := rfl
  refine homotopic_of_forall_ofUnitInterval_of_closing L C (fun s ↦ ?_) (fun s ↦ ?_)
    (fun t ↦ ?_) (fun t ↦ ?_) h₀ h₁
  · simp [hC, e.left_inv (hL₁ s).1]
  · simp [hC, e.left_inv (hL₀ s).1]
  · rw [hC, hl, ← add_smul, sub_add_cancel, one_smul, e.left_inv (hL₀ 0).1]
  · rw [hC, hr, ← add_smul, sub_add_cancel, one_smul, e.left_inv (hL₀ 1).1]

/-- A map from the circle read as a based loop at the image of `0`. -/
private def toLoop (f : C(AddCircle p, X)) : Path (f 0) (f 0) where
  toContinuousMap := f.comp (AddCircle.ofUnitInterval p)
  source' := by simp
  target' := by simp [AddCircle.coe_period]

/-- **Every map from a circle into a simply connected space is null-homotopic.** -/
theorem nullhomotopic_addCircle_of_simplyConnectedSpace [Fact (0 < p)] [SimplyConnectedSpace X]
    (f : C(AddCircle p, X)) : f.Nullhomotopic := by
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic (toLoop f) (Path.refl (f 0))
  refine ⟨f 0, homotopic_of_forall_ofUnitInterval F.toContinuousMap (fun s ↦ ?_) (fun t ↦ ?_)
    (fun t ↦ ?_)⟩
  · simp only [ContinuousMap.HomotopyWith.coe_toContinuousMap, Path.Homotopy.source,
      Path.Homotopy.target]
  · simp [toLoop]
  · simp

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
