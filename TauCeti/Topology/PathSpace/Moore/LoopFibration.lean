/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import TauCeti.Topology.Homotopy.LoopSpaceFibration
public import TauCeti.Topology.Homotopy.Path
public import TauCeti.Topology.PathSpace.Moore.Comparison.FundamentalGroup

/-!
# Moore loop maps of Hurewicz fibrations

For a Hurewicz fibration `p : E → B` and `e : E`, the induced map of fixed-interval loop spaces
`Ω E e → Ω B (p e)` is a Hurewicz fibration (`TauCeti.IsHurewiczFibration.loopMap`). This file
shows that the analogous statement for the Moore loop spaces fails, and that it fails only at the
loops of length zero.

The Moore loop map `MooreLoopSpace.map p` preserves lengths, and the only Moore loop of length
zero is the unit (`TauCeti.MooreLoopSpace.eq_one_of_length_eq_zero`). So the fibre of the Moore
loop map over the unit of `B` is a single point (`TauCeti.MooreLoopSpace.map_eq_one_iff`), while
over the constant loop of length `L > 0` it is the space of Moore loops of length `L` in the fibre
of `p`, a copy of its loop space (`TauCeti.MooreLoopSpace.fiberConstOfLengthHomeomorph`, for any
continuous map). In the
simplest case, the map from `X` to a point, the Moore loop map is the length
`MooreLoopSpace X x → [0, ∞)`. If the length has the homotopy lifting property for a single
point, lifting the path of lengths from `γ.length` down to `0` joins every Moore loop `γ` to the
unit, so the Moore loop space is path connected and the fundamental group of `X` at `x` is
trivial
(`TauCeti.MooreLoopSpace.subsingleton_fundamentalGroup_of_hasHomotopyLiftingProperty_length`).
For the circle, the map to a point is a Hurewicz fibration whose Moore loop map is not
(`TauCeti.MooreLoopSpace.not_forall_isHurewiczFibration_map`).

Away from length zero nothing goes wrong. A Moore loop of positive length is determined by its
length and its reparametrization to the unit interval
(`TauCeti.MooreLoopSpace.posLengthHomeomorph`), naturally in the space
(`TauCeti.MooreLoopSpace.posLengthHomeomorph_posLengthMap`). So on the Moore loops of positive
length, the Moore loop map of `p` (`TauCeti.MooreLoopSpace.posLengthMap`) is the product of the
identity of `(0, ∞)` with the fixed-interval loop map, and is therefore a Hurewicz fibration
(`TauCeti.IsHurewiczFibration.posLengthMap`). This map is again a Hurewicz fibration between
spaces of Moore loops, so the statement iterates: the induced map of positive-length Moore loops
of positive-length Moore loops, a Moore model of the double loop map, is a Hurewicz fibration
(`TauCeti.IsHurewiczFibration.posLengthMap_posLengthMap`).

## Main results

* `TauCeti.MooreLoopSpace.subsingleton_fundamentalGroup_of_hasHomotopyLiftingProperty_length`:
  if the length of Moore loops lifts paths, the fundamental group is trivial.
* `TauCeti.MooreLoopSpace.not_isHurewiczFibration_length`,
  `TauCeti.MooreLoopSpace.not_isHurewiczFibration_map_const`: when the fundamental group is
  nontrivial, neither the length nor the Moore loop map of the map to a point is a Hurewicz
  fibration.
* `TauCeti.MooreLoopSpace.not_forall_isHurewiczFibration_map`: the Moore loop map of a Hurewicz
  fibration need not be a Hurewicz fibration.
* `TauCeti.MooreLoopSpace.fiberConstOfLengthHomeomorph`: the fibre of the Moore loop map over a
  constant loop of positive length is the loop space of the fibre.
* `TauCeti.IsHurewiczFibration.posLengthMap`: on the Moore loops of positive length, the Moore
  loop map of a Hurewicz fibration is a Hurewicz fibration.
* `TauCeti.IsHurewiczFibration.posLengthMap_posLengthMap`: so is the induced map one level up, on
  positive-length Moore loops of positive-length Moore loops.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I.7 and III.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public noncomputable section

open unitInterval Topology.Homotopy
open scoped NNReal

universe w u v

namespace TauCeti

namespace MooreLoopSpace

variable {X : Type u} [TopologicalSpace X] {x : X}

/-! ### The length of Moore loops is not a fibration -/

/-- If the length of Moore loops at `x` has the homotopy lifting property with respect to a
nonempty space, then every Moore loop at `x` is joined to the unit: lift the path of lengths from
`γ.length` down to `0`, which ends at a loop of length zero. -/
theorem pathConnectedSpace_of_hasHomotopyLiftingProperty_length {A : Type w}
    [TopologicalSpace A] [Nonempty A]
    (h : HasHomotopyLiftingProperty (length : MooreLoopSpace X x → ℝ≥0) A) :
    PathConnectedSpace (MooreLoopSpace X x) := by
  have hjoined (γ : MooreLoopSpace X x) : Joined γ 1 := by
    let c : Path γ.length (0 : ℝ≥0) :=
      { toFun t := toNNReal (σ t) * γ.length
        continuous_toFun := by fun_prop
        source' := by simp
        target' := by simp }
    obtain ⟨Γ, hΓ₀, hΓ⟩ := h.exists_path_lift c
    have hΓ₁ : Γ 1 = 1 := eq_one_of_length_eq_zero <| by
      simpa only [Function.comp_apply, Path.target] using congrFun hΓ 1
    exact ⟨⟨Γ, hΓ₀, hΓ₁⟩⟩
  exact { nonempty := ⟨1⟩, joined := fun γ δ ↦ (hjoined γ).trans (hjoined δ).symm }

/-- If the length of Moore loops at `x` has the homotopy lifting property with respect to a
nonempty space, then the fundamental group of `X` at `x` is trivial. -/
theorem subsingleton_fundamentalGroup_of_hasHomotopyLiftingProperty_length {A : Type w}
    [TopologicalSpace A] [Nonempty A]
    (h : HasHomotopyLiftingProperty (length : MooreLoopSpace X x → ℝ≥0) A) :
    Subsingleton (FundamentalGroup X x) :=
  (pathConnectedSpace_iff x).1 (pathConnectedSpace_of_hasHomotopyLiftingProperty_length h)

/-- **The length of Moore loops is not a Hurewicz fibration** when the fundamental group is
nontrivial: its fibre over `0` is a single point. -/
theorem not_isHurewiczFibration_length [Nontrivial (FundamentalGroup X x)] :
    ¬ IsHurewiczFibration.{w} (length : MooreLoopSpace X x → ℝ≥0) := fun h ↦
  not_subsingleton (FundamentalGroup X x) <|
    subsingleton_fundamentalGroup_of_hasHomotopyLiftingProperty_length
      (h.hasHomotopyLiftingProperty PUnit)

/-- When the fundamental group of `X` at `x` is nontrivial, the Moore loop map of the map from `X`
to a point is not a Hurewicz fibration, although the map to a point is one
(`TauCeti.isHurewiczFibration_of_subsingleton`). -/
theorem not_isHurewiczFibration_map_const [Nontrivial (FundamentalGroup X x)] :
    ¬ IsHurewiczFibration.{w}
      (map (.const X ()) rfl : MooreLoopSpace X x → MooreLoopSpace Unit ()) := fun h ↦ by
  have hlength : lengthHomeomorph () ∘ map (.const X ()) rfl = (length : MooreLoopSpace X x → _) :=
    funext fun γ ↦ by simp
  exact not_isHurewiczFibration_length (hlength ▸ (lengthHomeomorph ()).isHurewiczFibration.comp h)

/-- **The Moore loop map of a Hurewicz fibration need not be a Hurewicz fibration.** The map from
the circle to a point is a Hurewicz fibration, but its Moore loop map is not. -/
theorem not_forall_isHurewiczFibration_map :
    ¬ ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e : E),
      IsHurewiczFibration.{w} p →
        IsHurewiczFibration.{w} (map p rfl : MooreLoopSpace E e → MooreLoopSpace B (p e)) := by
  intro h
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have := (AddCircle.windingNumberIso (0 : AddCircle (1 : ℝ))).toEquiv.nontrivial
  exact not_isHurewiczFibration_map_const
    (h (AddCircle (1 : ℝ)) Unit (.const _ ()) 0 isHurewiczFibration_of_subsingleton)

/-! ### Fibres of the Moore loop map over constant loops -/

section Fiber

variable {Y : Type v} [TopologicalSpace Y] {y : Y} (f : C(X, Y)) (hf : f x = y) {L : ℝ≥0}

/-- Every point of a Moore loop in the fibre of the Moore loop map over the constant loop of
length `L` lies in the fibre of `f`. -/
private theorem apply_toPath_mem_preimage_singleton
    (γ : (map f hf ⁻¹' {constOfLength y L} : Set (MooreLoopSpace X x))) (s : I) :
    γ.val.toPath s ∈ f ⁻¹' {y} := by
  subst hf
  have hγ : map f rfl γ.val = constOfLength (f x) L := γ.property
  have h := congrArg (fun δ : MooreLoopSpace Y (f x) ↦ δ.toPath s) hγ
  simpa [toPath_map] using h

/-- A loop in the fibre `f ⁻¹' {y}`, run in time `L > 0`, is a Moore loop in the fibre of the
Moore loop map of `f` over the constant loop of length `L`. -/
private theorem map_posLengthHomeomorph_symm_eq_constOfLength (hL : 0 < L)
    (c : Path (⟨x, hf⟩ : f ⁻¹' {y}) ⟨x, hf⟩) :
    map f hf ((posLengthHomeomorph x).symm (⟨L, hL⟩, c.map continuous_subtypeVal)).val =
      constOfLength y L := by
  -- every value of the extended loop lies in the fibre `f ⁻¹' {y}`
  have hmem (r : ℝ) : (c.map continuous_subtypeVal).extend r ∈ f ⁻¹' {y} := by
    obtain ⟨s, hs⟩ := (Path.extend_range (c.map continuous_subtypeVal)).subset
      (Set.mem_range_self r)
    exact hs ▸ (c s).property
  refine ext (MoorePath.ext (by simp) fun t ↦ ?_)
  simp only [toMoorePath_map, MoorePath.map_apply, toMoorePath_posLengthHomeomorph_symm_apply,
    MoorePath.rescale_apply, Path.toMoorePath_apply, toMoorePath_constOfLength,
    MoorePath.constOfLength_apply]
  exact hmem _

variable (x) in
/-- **The fibre of the Moore loop map over a constant loop of positive length is the loop space of
the fibre**: for `L > 0`, the Moore loops at `x` that `f` sends to the constant loop of length `L`
at `y = f x` are, through their reparametrization to the unit interval, the loops at `x` in the
fibre `f ⁻¹' {y}`. Over the unit, the fibre is a single point instead
(`TauCeti.MooreLoopSpace.map_eq_one_iff`). -/
def fiberConstOfLengthHomeomorph (hL : 0 < L) :
    (map f hf ⁻¹' {constOfLength y L} : Set (MooreLoopSpace X x)) ≃ₜ
      Path (⟨x, hf⟩ : f ⁻¹' {y}) ⟨x, hf⟩ where
  toFun γ := γ.val.toPath.codRestrict (x := ⟨x, hf⟩) (y := ⟨x, hf⟩)
    (apply_toPath_mem_preimage_singleton f hf γ)
  invFun c := ⟨((posLengthHomeomorph x).symm (⟨L, hL⟩, c.map continuous_subtypeVal)).val,
    map_posLengthHomeomorph_symm_eq_constOfLength f hf hL c⟩
  left_inv γ := by
    have hγ : map f hf γ.val = constOfLength y L := γ.property
    have hlen : γ.val.length = L := by simpa using congrArg length hγ
    refine Subtype.ext ((congrArg (fun c ↦ ((posLengthHomeomorph x).symm (⟨L, hL⟩, c)).val)
      ?_).trans (coe_posLengthHomeomorph_symm_mk_toPath γ.val hL hlen))
    exact Path.map_codRestrict _ _
  right_inv c := Path.ext <| funext fun s ↦ Subtype.ext <| by
    simp
  continuous_toFun := Path.continuous_uncurry_iff.1 <| continuous_induced_rng.2 <|
    ((Path.continuous_uncurry_iff.2 continuous_toPath).comp
      (continuous_subtypeVal.prodMap continuous_id)).congr fun γs ↦
        (Path.codRestrict_coe (x := ⟨x, hf⟩) (y := ⟨x, hf⟩) _
          (apply_toPath_mem_preimage_singleton f hf γs.1) γs.2).symm
  continuous_invFun := ((posLengthHomeomorph x).symm.continuous.comp
    (continuous_const.prodMk (continuous_loopMap continuous_subtypeVal _))).subtypeVal.subtype_mk
      _

/-- The loop of the fibre attached to a Moore loop `γ` by `fiberConstOfLengthHomeomorph` is the
reparametrization `toPath γ` of `γ` to the unit interval. -/
@[simp]
theorem coe_fiberConstOfLengthHomeomorph_apply (hL : 0 < L)
    (γ : (map f hf ⁻¹' {constOfLength y L} : Set (MooreLoopSpace X x))) (s : I) :
    (fiberConstOfLengthHomeomorph x f hf hL γ s : X) = γ.val.toPath s :=
  Path.codRestrict_coe (x := ⟨x, hf⟩) (y := ⟨x, hf⟩) _
    (apply_toPath_mem_preimage_singleton f hf γ) s

/-- The inverse of `fiberConstOfLengthHomeomorph` runs a loop of the fibre in time `L`, by the
inverse of `posLengthHomeomorph`. -/
@[simp]
theorem coe_fiberConstOfLengthHomeomorph_symm_apply (hL : 0 < L)
    (c : Path (⟨x, hf⟩ : f ⁻¹' {y}) ⟨x, hf⟩) :
    ((fiberConstOfLengthHomeomorph x f hf hL).symm c : MooreLoopSpace X x) =
      ((posLengthHomeomorph x).symm (⟨L, hL⟩, c.map continuous_subtypeVal)).val :=
  (rfl)

end Fiber

end MooreLoopSpace

open MooreLoopSpace

/-! ### The Moore loop map over positive lengths -/

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- **On the Moore loops of positive length, the Moore loop map of a Hurewicz fibration is a
Hurewicz fibration.** Under `MooreLoopSpace.posLengthHomeomorph` the map `posLengthMap p` is the
product of the identity of `(0, ∞)` with the fixed-interval loop map
(`MooreLoopSpace.posLengthHomeomorph_posLengthMap`), a Hurewicz fibration by
`TauCeti.IsHurewiczFibration.loopMap`. Without the restriction to positive lengths the statement
fails (`TauCeti.MooreLoopSpace.not_forall_isHurewiczFibration_map`). -/
theorem IsHurewiczFibration.posLengthMap (hp : IsHurewiczFibration.{w} p) (e : E) :
    IsHurewiczFibration.{w} (MooreLoopSpace.posLengthMap ⟨p, hp.continuous⟩ rfl (x := e)) := by
  have h : ⇑(MooreLoopSpace.posLengthMap ⟨p, hp.continuous⟩ rfl (x := e)) =
      (posLengthHomeomorph (p e)).symm ∘
        Prod.map (Homeomorph.refl _) (fun γ : Ω E e ↦ (γ.map hp.continuous : Ω B (p e))) ∘
          posLengthHomeomorph e := by
    funext γ
    rw [Function.comp_apply, Function.comp_apply, Homeomorph.eq_symm_apply,
      posLengthHomeomorph_posLengthMap, Homeomorph.refl_apply]
    -- at `rfl`, the loop map `ContinuousMap.loopMap` is pointwise `Path.map`
    exact Prod.ext rfl (Path.ext (funext fun s ↦ by simp))
  rw [h]
  exact (posLengthHomeomorph (p e)).symm.isHurewiczFibration.comp
    (((Homeomorph.refl (Set.Ioi (0 : ℝ≥0))).isHurewiczFibration.prodMap
      (hp.loopMap e)).comp_homeomorph _)

/-- **Double loops: the positive-length Moore loop map of a Hurewicz fibration is again a Hurewicz
fibration one level up.** For a Hurewicz fibration `p : E → B` and a Moore loop `c` of positive
length at `e`, for instance the constant loop of length `1`, the map induced by
`posLengthMap p : Ω^{>0}_e E → Ω^{>0}_{p e} B` on the Moore loops of positive length based at `c`
is a Hurewicz fibration. -/
theorem IsHurewiczFibration.posLengthMap_posLengthMap (hp : IsHurewiczFibration.{w} p) (e : E)
    (c : (length ⁻¹' Set.Ioi 0 : Set (MooreLoopSpace E e))) :
    IsHurewiczFibration.{w}
      (MooreLoopSpace.posLengthMap (MooreLoopSpace.posLengthMap ⟨p, hp.continuous⟩ rfl) rfl
        (x := c)) :=
  (hp.posLengthMap e).posLengthMap c

end TauCeti
