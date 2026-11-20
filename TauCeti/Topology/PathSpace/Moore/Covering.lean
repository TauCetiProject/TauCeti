/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Topology.PathSpace.Moore.Lifting

/-!
# Lifting Moore paths along a covering map

Let `p : E → B` be a covering map. A Moore path in `B` starting at `p e` lifts to a unique Moore
path in `E` starting at `e`, of the same length (`IsCoveringMap.moorePath_eq_of_map_eq` for
uniqueness). The lifts depend continuously on the point and the path, so they form a lifting
function for `p` on Moore paths (`IsCoveringMap.mooreLiftingFunction`), and by uniqueness every
lifting function of `p` is this one (`IsCoveringMap.subsingleton_mooreLiftingFunction`) and is
transitive (`IsCoveringMap.isTransitive`).

The lift of a Moore path `γ` from `e` is read off Mathlib's homotopy lifting for covering maps
(`IsCoveringMap.liftHomotopy`), applied to the family of paths `t ↦ γ (t m)` on the unit interval,
parametrized by the time `m ≥ 0` and the pair `(e, γ)`: the end points of these lifts, as `m`
varies, trace the lift of `γ`.

The Moore loop analogue of Mathlib's identification of the higher homotopy groups of a covering
space with those of the base holds on the nose for double loops. A Moore loop at the unit of
`Ω_{p e} B` is a family of Moore loops in `B` starting at the unit; lifting each of them from `e`
gives Moore paths whose end points lie in the discrete fibre and depend continuously on the
family's parameter, so they all end at `e`. Hence the double Moore loop map of `p` is a
homeomorphism `Ω_1 Ω_e E ≃ₜ Ω_1 Ω_{p e} B`
(`IsCoveringMap.doubleMooreLoopSpaceHomeomorph`). The single Moore loop map is not surjective
in general, since a loop in `B` whose lift from `e` does not close up has no preimage.

## Main results

* `IsCoveringMap.moorePath_eq_of_map_eq`: Moore paths in `E` with the same source and the same
  image under `p` are equal.
* `IsCoveringMap.mooreLiftingFunction`: the lifting function of a covering map on Moore paths.
* `IsCoveringMap.subsingleton_mooreLiftingFunction`, `IsCoveringMap.isTransitive`: it is the only
  lifting function of `p`, and every lifting function of `p` is transitive.
* `IsCoveringMap.doubleMooreLoopSpaceHomeomorph`: the double Moore loop map of a covering map is a
  homeomorphism.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Propositions 1.30 and 4.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1 (transitive lifting
  functions).
-/

public noncomputable section

open scoped NNReal unitInterval
open unitInterval

namespace IsCoveringMap

open TauCeti

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)}
  (hp : IsCoveringMap p)

include hp

/-- **Moore paths lift uniquely along a covering map**: two Moore paths in `E` with the same source
and the same image under `p` are equal. -/
theorem moorePath_eq_of_map_eq {δ₁ δ₂ : MoorePath E} (hs : δ₁.source = δ₂.source)
    (h : δ₁.map p = δ₂.map p) : δ₁ = δ₂ := by
  have hfun : ⇑δ₁ = ⇑δ₂ :=
    hp.eq_of_comp_eq δ₁.continuous δ₂.continuous
      (funext fun t ↦ by simpa using congr($h t)) 0 (by simpa only [MoorePath.source_def] using hs)
  exact MoorePath.ext (by rw [← MoorePath.length_map p, h, MoorePath.length_map])
    (congrFun hfun)

/-! ### The lifting function -/

/-- The family of paths `t ↦ γ (t m)` on the unit interval, parametrized by the time `m` and the
pair `(e, γ)`. -/
private def timeHomotopy (p : C(E, B)) : C(I × (ℝ≥0 × MooreReplacement p), B) :=
  ⟨fun q ↦ q.2.2.path (toNNReal q.1 * q.2.1), by fun_prop⟩

/-- The lift of `timeHomotopy` starting at the point `e` of each pair `(e, γ)`. -/
private def timeLift : C(I × (ℝ≥0 × MooreReplacement p), E) :=
  hp.liftHomotopy (timeHomotopy p) ⟨fun q ↦ q.2.point, by fun_prop⟩
    fun q ↦ by simp [timeHomotopy, ← MoorePath.source_def]

private theorem apply_timeLift (q : I × (ℝ≥0 × MooreReplacement p)) :
    p (timeLift hp q) = q.2.2.path (toNNReal q.1 * q.2.1) :=
  congrFun (hp.liftHomotopy_lifts _ _ _) q

private theorem timeLift_zero (q : ℝ≥0 × MooreReplacement p) : timeLift hp (0, q) = q.2.point :=
  hp.liftHomotopy_zero _ _ _ q

/-- At time `m = 0` the end point of the lifted path is the point of the pair: the lifted path lies
over a constant path, so it is constant. -/
private theorem timeLift_one_zero (x : MooreReplacement p) : timeLift hp (1, (0, x)) = x.point := by
  -- The lifted path at `m = 0` lies over the constant path at `γ 0`, so it is constant.
  have := hp.const_of_comp (g := fun t : I ↦ timeLift hp (t, (0, x))) (by fun_prop)
    (fun t t' ↦ by simp [apply_timeLift]) 1 0
  rw [this, timeLift_zero]

/-- Past the length of `γ`, the end point of the lift no longer moves. -/
private theorem timeLift_one_of_length_le (x : MooreReplacement p) {s : ℝ≥0}
    (hs : x.path.length ≤ s) :
    timeLift hp (1, (s, x)) = timeLift hp (1, (x.path.length, x)) := by
  -- The end points over the times between `length γ` and `s` lie over the stopped part of `γ`.
  have := hp.const_of_comp
    (g := fun t : I ↦ timeLift hp (1, (x.path.length + toNNReal t * (s - x.path.length), x)))
    (by fun_prop)
    (fun t t' ↦ by
      simp only [apply_timeLift, toNNReal_one, one_mul]
      rw [x.path.apply_of_length_le le_self_add, x.path.apply_of_length_le le_self_add])
    1 0
  simpa [add_tsub_cancel_of_le hs] using this

/-- The lift of the Moore path of a pair `(e, γ)` from `e`. -/
private def mooreLift (x : MooreReplacement p) : MoorePath E where
  toFun s := timeLift hp (1, (s, x))
  continuous_toFun := by fun_prop
  length := x.path.length
  apply_of_length_le' _ hs := timeLift_one_of_length_le hp x hs

private theorem mooreLift_apply (x : MooreReplacement p) (s : ℝ≥0) :
    mooreLift hp x s = timeLift hp (1, (s, x)) :=
  rfl

private theorem length_mooreLift (x : MooreReplacement p) :
    (mooreLift hp x).length = x.path.length :=
  rfl

private theorem continuous_mooreLift : Continuous (mooreLift hp) :=
  MoorePath.continuous_iff.2
    ⟨(MoorePath.continuous_length.comp MooreReplacement.continuous_path).congr fun x ↦
        (length_mooreLift hp x).symm,
      ((timeLift hp).continuous.comp (continuous_const.prodMk
        (continuous_snd.prodMk continuous_fst))).congr fun q ↦ (mooreLift_apply hp q.1 q.2).symm⟩

/-- **The lifting function of a covering map on Moore paths**: a Moore path `γ` in `B` starting at
`p e` lifts to the unique Moore path in `E` starting at `e` over `γ`, continuously in `(e, γ)`. -/
def mooreLiftingFunction : MooreLiftingFunction p where
  toContinuousMap := ⟨mooreLift hp, continuous_mooreLift hp⟩
  source_apply' x := by
    rw [ContinuousMap.coe_mk, MoorePath.source_def, mooreLift_apply, timeLift_one_zero]
  map_apply' x := MoorePath.ext (by simp [length_mooreLift]) fun s ↦ by
    simp [mooreLift_apply, apply_timeLift]

/-- **The lift is characterized by its start and its image**: a Moore path in `E` is the lift of
`γ` from `e` exactly when it starts at `e` and lies over `γ`. -/
theorem eq_mooreLiftingFunction_lift_iff {δ : MoorePath E} {e : E} {γ : MoorePath B}
    (h : γ.source = p e) :
    δ = hp.mooreLiftingFunction.lift e γ h ↔ δ.source = e ∧ δ.map p = γ := by
  refine ⟨?_, fun ⟨hs, hm⟩ ↦ hp.moorePath_eq_of_map_eq (by simp [hs]) (by simp [hm])⟩
  rintro rfl
  simp

/-- **A covering map has a unique lifting function on Moore paths.** -/
theorem subsingleton_mooreLiftingFunction : Subsingleton (MooreLiftingFunction p) :=
  ⟨fun Φ Ψ ↦ MooreLiftingFunction.ext <| ContinuousMap.ext fun x ↦
    hp.moorePath_eq_of_map_eq ((Φ.source_apply' x).trans (Ψ.source_apply' x).symm)
      ((Φ.map_apply' x).trans (Ψ.map_apply' x).symm)⟩

/-- **Every lifting function of a covering map is transitive**: the lift of a concatenation and the
concatenation of the lifts are both lifts from the same point, so they agree. -/
theorem isTransitive (Φ : MooreLiftingFunction p) : Φ.IsTransitive :=
  ⟨fun e γ δ hγ h ↦ hp.moorePath_eq_of_map_eq (by simp) (by simp)⟩

/-! ### Double Moore loops -/

variable (e : E)

/-- A Moore loop at `p e` in the family of a double Moore loop lifts to a Moore loop at `e`: the end
points of the lifts lie in the fibre over `p e` and vary continuously along the family, which
starts at the unit, so they stay at `e`. -/
private theorem target_lift_apply (Γ : MooreLoopSpace (MooreLoopSpace B (p e)) 1) (s : ℝ≥0) :
    (hp.mooreLiftingFunction.lift e (Γ.toMoorePath s).toMoorePath (by simp)).target = e := by
  have hconst := hp.const_of_comp
    (g := fun s ↦ (hp.mooreLiftingFunction.lift e (Γ.toMoorePath s).toMoorePath (by simp)).target)
    (MoorePath.continuous_target.comp <| hp.mooreLiftingFunction.continuous_lift continuous_const
      (MooreLoopSpace.continuous_toMoorePath.comp Γ.toMoorePath.continuous) fun _ ↦ by simp)
    (fun s s' ↦ by simp) s 0
  -- At time zero the family is at the unit, whose lift is the constant path at `e`.
  rw [hconst]
  simp

/-- The lift from `e` of the Moore loop at time `s` of a double Moore loop, as a Moore loop at
`e`. -/
private def liftLoop (Γ : MooreLoopSpace (MooreLoopSpace B (p e)) 1) (s : ℝ≥0) :
    MooreLoopSpace E e :=
  ⟨hp.mooreLiftingFunction.lift e (Γ.toMoorePath s).toMoorePath (by simp), by simp,
    target_lift_apply hp e Γ s⟩

private theorem continuous_liftLoop :
    Continuous fun q : MooreLoopSpace (MooreLoopSpace B (p e)) 1 × ℝ≥0 ↦ liftLoop hp e q.1 q.2 :=
  MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 <|
    hp.mooreLiftingFunction.continuous_lift continuous_const
      (MooreLoopSpace.continuous_toMoorePath.comp
        ((MooreLoopSpace.continuous_toMoorePath.comp continuous_fst).moorePath_eval
          continuous_snd)) fun _ ↦ by simp

/-- The lift of a double Moore loop in `B` at the unit to a double Moore loop in `E`. -/
private def doubleLift (Γ : MooreLoopSpace (MooreLoopSpace B (p e)) 1) :
    MooreLoopSpace (MooreLoopSpace E e) 1 where
  toMoorePath :=
    { toFun := liftLoop hp e Γ
      continuous_toFun := (continuous_liftLoop hp e).comp (continuous_const.prodMk continuous_id)
      length := Γ.toMoorePath.length
      apply_of_length_le' s hs := by
        have h : Γ.toMoorePath s = Γ.toMoorePath Γ.toMoorePath.length := by
          rw [Γ.toMoorePath.apply_of_length_le hs, MoorePath.target_def]
        exact MooreLoopSpace.ext (congrArg (fun γ : MooreLoopSpace B (p e) ↦
          hp.mooreLiftingFunction.lift e γ.toMoorePath (by simp)) h) }
  source_eq := MooreLoopSpace.ext <| by simp [MoorePath.source_def, liftLoop]
  target_eq := MooreLoopSpace.ext <| by simp [MoorePath.target_def, liftLoop]

private theorem doubleLift_apply (Γ : MooreLoopSpace (MooreLoopSpace B (p e)) 1) (s : ℝ≥0) :
    ((doubleLift hp e Γ).toMoorePath s).toMoorePath =
      hp.mooreLiftingFunction.lift e (Γ.toMoorePath s).toMoorePath (by simp) :=
  rfl

private theorem length_doubleLift (Γ : MooreLoopSpace (MooreLoopSpace B (p e)) 1) :
    (doubleLift hp e Γ).length = Γ.length := by
  rw [← MooreLoopSpace.length_toMoorePath, ← MooreLoopSpace.length_toMoorePath]
  rfl

private theorem continuous_doubleLift : Continuous (doubleLift hp e) :=
  MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 <| MoorePath.continuous_iff.2
    ⟨MooreLoopSpace.continuous_length.congr fun Γ ↦ by
        rw [Function.comp_apply, MooreLoopSpace.length_toMoorePath, length_doubleLift],
      continuous_liftLoop hp e⟩

/-- **The double Moore loop map of a covering map is a homeomorphism**: postcomposition with `p`
identifies the double Moore loops `Ω_1 Ω_e E` with `Ω_1 Ω_{p e} B`. Its inverse lifts each Moore
loop of a double Moore loop in `B` from `e`. -/
def doubleMooreLoopSpaceHomeomorph :
    MooreLoopSpace (MooreLoopSpace E e) 1 ≃ₜ MooreLoopSpace (MooreLoopSpace B (p e)) 1 where
  toFun := MooreLoopSpace.map
    (MooreLoopSpace.map p (rfl : p e = p e) : C(MooreLoopSpace E e, MooreLoopSpace B (p e)))
    (map_one (MooreLoopSpace.map p (rfl : p e = p e)))
  invFun := doubleLift hp e
  left_inv Δ := MooreLoopSpace.ext <| MoorePath.ext (by simp [length_doubleLift])
      fun s ↦ MooreLoopSpace.ext <| by
    rw [doubleLift_apply]
    exact hp.moorePath_eq_of_map_eq (by simp) (by simp)
  right_inv Γ := MooreLoopSpace.ext <| MoorePath.ext (by simp [length_doubleLift])
      fun s ↦ MooreLoopSpace.ext <| by
    simp [doubleLift_apply]
  continuous_toFun := map_continuous _
  continuous_invFun := continuous_doubleLift hp e

@[simp]
theorem doubleMooreLoopSpaceHomeomorph_apply (Δ : MooreLoopSpace (MooreLoopSpace E e) 1) :
    hp.doubleMooreLoopSpaceHomeomorph e Δ =
      MooreLoopSpace.map
        (MooreLoopSpace.map p (rfl : p e = p e) : C(MooreLoopSpace E e, MooreLoopSpace B (p e)))
        (map_one (MooreLoopSpace.map p (rfl : p e = p e))) Δ :=
  (rfl)

/-- The inverse of `doubleMooreLoopSpaceHomeomorph` lifts the Moore loop at each time from `e`. -/
@[simp]
theorem toMoorePath_doubleMooreLoopSpaceHomeomorph_symm_apply
    (Γ : MooreLoopSpace (MooreLoopSpace B (p e)) 1) (s : ℝ≥0) :
    (((hp.doubleMooreLoopSpaceHomeomorph e).symm Γ).toMoorePath s).toMoorePath =
      (hp.mooreLiftingFunction).lift e (Γ.toMoorePath s).toMoorePath (by simp) :=
  doubleLift_apply hp e Γ s

end IsCoveringMap
