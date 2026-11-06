/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Normed.Group.AddCircle
public import TauCeti.Topology.Homotopy.Path
public import TauCeti.Topology.Instances.AddCircle.UnitInterval

/-!
# Null-homotopy of maps from the circle

A continuous map `f : AddCircle p → X` (with `0 < p`) is read as the based loop
`t ↦ f (t * p)` on the unit interval. When `X` is simply connected this loop is homotopic to the
constant loop relative to its endpoints, and such a homotopy descends along the quotient map
`I × I → I × AddCircle p`, `(s, t) ↦ (s, t * p)` (built from `AddCircle.ofUnitInterval`),
because it is constant on the two ends `t = 0` and `t = 1`, which are the only points
identified. The descended map is a free null-homotopy of `f`
(`ContinuousMap.nullhomotopic_addCircle_of_simplyConnectedSpace`).

Mathlib's `SimplyConnectedSpace` is phrased with based paths; this file supplies its consequence
for free loops parametrised by the circle, which is how circles are compared in conditions such as
simple connectivity at infinity.

The same descent, together with the conjugation of a loop by a null homotopy at its basepoint
(`Path.Homotopic.map_trans_evalAt`), shows more generally that free and based null-homotopy agree:
`f` is null-homotopic exactly when its based loop is homotopic to the constant loop relative to
its endpoints (`ContinuousMap.nullhomotopic_iff_homotopic_refl`). Thus a continuous `p`-periodic
curve `γ : ℝ → X` is contractible, as a map `ℝ ⧸ pℤ → X`, exactly when the loop it traces over a
period `[s, s + p]` (`Function.Periodic.loop`) is null-homotopic
(`Function.Periodic.exists_nullhomotopic_iff_homotopic_loop`).

Null-homotopy of a loop does not depend on its constant speed: a null-homotopic loop
`g : AddCircle T → X`, run at speed `a ≠ 0` (backwards when `a < 0`), is the null-homotopic loop
`t ↦ g (t * a)` on `AddCircle (T / |a|)` (`ContinuousMap.Nullhomotopic.exists_addCircle_comp_mul`).

## Main declarations

* `ContinuousMap.nullhomotopic_addCircle_of_simplyConnectedSpace`: every continuous map from a
  circle `AddCircle p` with `0 < p` into a simply connected space is null-homotopic.
* `ContinuousMap.nullhomotopic_iff_homotopic_refl`: a map from the circle is null-homotopic exactly
  when its based loop is.
* `Function.Periodic.loop`: the loop traced by a continuous periodic curve over one period.
* `Function.Periodic.exists_nullhomotopic_iff_homotopic_loop`: a continuous periodic curve is
  contractible exactly when its loop over a period is null-homotopic.
* `ContinuousMap.Nullhomotopic.exists_addCircle_comp_mul`: a null-homotopic loop run at constant
  nonzero speed is null-homotopic.
-/

public section

noncomputable section

open Set Topology
open scoped unitInterval

namespace ContinuousMap

variable {p : ℝ} {X : Type*} [TopologicalSpace X]

/-- A map from the circle read as a based loop at the image of `0`. -/
private def toLoop (f : C(AddCircle p, X)) : Path (f 0) (f 0) where
  toContinuousMap := f.comp (AddCircle.ofUnitInterval p)
  source' := by simp
  target' := by simp [AddCircle.coe_period]

/-- A null-homotopic map from the circle is null-homotopic as a based loop: following the null
homotopy at `0` conjugates the loop into the constant loop. -/
private theorem Nullhomotopic.homotopic_toLoop {f : C(AddCircle p, X)} (hf : f.Nullhomotopic) :
    (toLoop f).Homotopic (Path.refl (f 0)) := by
  obtain ⟨y, ⟨F⟩⟩ := hf
  -- The circle itself, as a loop at `0`; its images under `f` and under the constant map.
  let c : Path (0 : AddCircle p) 0 :=
    ⟨AddCircle.ofUnitInterval p, AddCircle.ofUnitInterval_zero, AddCircle.ofUnitInterval_one⟩
  have hcf : c.map (map_continuous f) = toLoop f := Path.ext rfl
  have hc : (c.map (map_continuous (ContinuousMap.const (AddCircle p) y)) : Path y y) =
      Path.refl y :=
    Path.ext rfl
  have h := Path.Homotopic.map_trans_evalAt F c
  rw [hcf, hc] at h
  exact Path.Homotopic.trans_right_cancel <|
    h.trans ((Path.Homotopic.trans_refl _).trans (Path.Homotopic.refl_trans _).symm)

/-- A map from the circle whose based loop is null-homotopic is null-homotopic. -/
private theorem nullhomotopic_of_homotopic_toLoop [Fact (0 < p)] {f : C(AddCircle p, X)}
    (hf : (toLoop f).Homotopic (Path.refl (f 0))) : f.Nullhomotopic := by
  obtain ⟨F⟩ := hf
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

/-- **Free and based null-homotopy of loops agree.** For `0 < p`, a map `f : AddCircle p → X` is
null-homotopic exactly when a based loop `γ` tracing it, `γ t = f (t * p)` on the unit interval,
is homotopic to the constant loop relative to its endpoints. -/
theorem nullhomotopic_iff_homotopic_refl [Fact (0 < p)] {f : C(AddCircle p, X)} {x : X}
    (γ : Path x x) (hγ : ∀ t : I, γ t = f ((t * p : ℝ) : AddCircle p)) :
    f.Nullhomotopic ↔ γ.Homotopic (Path.refl x) := by
  obtain rfl : x = f 0 := by simpa using hγ 0
  obtain rfl : γ = toLoop f :=
    Path.ext (funext fun t ↦ (hγ t).trans (congrArg f (AddCircle.ofUnitInterval_apply t).symm))
  exact ⟨Nullhomotopic.homotopic_toLoop, nullhomotopic_of_homotopic_toLoop⟩

/-- **Every map from a circle into a simply connected space is null-homotopic.** -/
theorem nullhomotopic_addCircle_of_simplyConnectedSpace [Fact (0 < p)] [SimplyConnectedSpace X]
    (f : C(AddCircle p, X)) : f.Nullhomotopic :=
  nullhomotopic_of_homotopic_toLoop (SimplyConnectedSpace.paths_homotopic _ _)

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

namespace Function.Periodic

variable {p : ℝ} {X : Type*} [TopologicalSpace X] {γ : ℝ → X}

/-- The loop at `γ s` traced by a continuous `p`-periodic curve `γ` over the period `[s, s + p]`:
`t ↦ γ (s + t * p)` on the unit interval. -/
def loop (hp : Periodic γ p) (hγ : Continuous γ) (s : ℝ) : Path (γ s) (γ s) where
  toFun t := γ (s + t * p)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp [hp s]

@[simp]
theorem loop_apply (hp : Periodic γ p) (hγ : Continuous γ) (s : ℝ) (t : I) :
    hp.loop hγ s t = γ (s + t * p) :=
  (rfl)

/-- **A periodic curve is contractible exactly when its loop over a period is.** For `0 < p`, the
map `ℝ ⧸ pℤ → X` induced by a continuous `p`-periodic curve `γ` is null-homotopic exactly when
the loop traced by `γ` over the period `[s, s + p]` is null-homotopic relative to its endpoints,
for any initial time `s`. -/
theorem exists_nullhomotopic_iff_homotopic_loop [Fact (0 < p)] (hp : Periodic γ p)
    (hγ : Continuous γ) (s : ℝ) :
    (∃ g : C(AddCircle p, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t) ↔
      (hp.loop hγ s).Homotopic (Path.refl (γ s)) := by
  -- Rotating the circle by `s` turns `g` into a map whose based loop is `hp.loop hγ s`.
  let r (u : ℝ) : C(AddCircle p, AddCircle p) :=
    ⟨(· + (u : AddCircle p)), continuous_id.add continuous_const⟩
  have hr (u : ℝ) (θ : AddCircle p) : r u θ = θ + u := rfl
  have hrot (g : C(AddCircle p, X)) : (g.comp (r s)).Nullhomotopic → g.Nullhomotopic := by
    intro h
    have hg : (g.comp (r s)).comp (r (-s)) = g := by
      ext θ
      simp [r]
    exact hg ▸ h.comp_left (r (-s))
  have key (g : C(AddCircle p, X)) (hg : ∀ t : ℝ, g t = γ t) :
      (g.comp (r s)).Nullhomotopic ↔ (hp.loop hγ s).Homotopic (Path.refl (γ s)) :=
    ContinuousMap.nullhomotopic_iff_homotopic_refl _ fun t ↦ by
      rw [loop_apply, ContinuousMap.comp_apply, hr, ← AddCircle.coe_add, hg, add_comm]
  constructor
  · rintro ⟨g, hg, hgγ⟩
    exact (key g hgγ).1 (hg.comp_left (r s))
  · intro h
    let g : C(AddCircle p, X) := ⟨hp.lift, hγ.quotient_liftOn' _⟩
    have hgγ (t : ℝ) : g t = γ t := hp.lift_coe t
    exact ⟨g, hrot g ((key g hgγ).2 h), hgγ⟩

end Function.Periodic
