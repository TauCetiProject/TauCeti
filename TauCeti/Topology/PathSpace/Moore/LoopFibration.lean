/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import TauCeti.Topology.Homotopy.LoopSpaceFibration
public import TauCeti.Topology.PathSpace.Moore.Comparison.FundamentalGroup

/-!
# Moore loop maps of Hurewicz fibrations

For a Hurewicz fibration `p : E → B` and `e : E`, the induced map of fixed-interval loop spaces
`Ω E e → Ω B (p e)` is a Hurewicz fibration (`TauCeti.IsHurewiczFibration.loopMap`). This file
shows that the analogous statement for the Moore loop spaces fails, and that it fails only at the
loops of length zero.

The Moore loop map `MooreLoopSpace.map p` preserves lengths, and the only Moore loop of length
zero is the unit (`TauCeti.MooreLoopSpace.eq_one_of_length_eq_zero`). So the fibre of the Moore
loop map over the unit of `B` is a single point, while over the constant loop of length `L > 0` it
is the space of Moore loops of length `L` in the fibre of `p`, a copy of its loop space. In the
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
(`TauCeti.MooreLoopSpace.posLengthHomeomorph`), naturally in the space. So over the Moore loops
of positive length, the Moore loop map of `p` is the product of the identity of `(0, ∞)` with the
fixed-interval loop map, and is therefore a Hurewicz fibration
(`TauCeti.IsHurewiczFibration.restrictPreimage_mooreLoopMap`).

## Main results

* `TauCeti.MooreLoopSpace.subsingleton_fundamentalGroup_of_hasHomotopyLiftingProperty_length`:
  if the length of Moore loops lifts paths, the fundamental group is trivial.
* `TauCeti.MooreLoopSpace.not_isHurewiczFibration_length`,
  `TauCeti.MooreLoopSpace.not_isHurewiczFibration_map_const`: when the fundamental group is
  nontrivial, neither the length nor the Moore loop map of the map to a point is a Hurewicz
  fibration.
* `TauCeti.MooreLoopSpace.not_forall_isHurewiczFibration_map`: the Moore loop map of a Hurewicz
  fibration need not be a Hurewicz fibration.
* `TauCeti.MooreLoopSpace.posLengthHomeomorph`: Moore loops of positive length are pairs of a
  positive length and a loop on the unit interval.
* `TauCeti.IsHurewiczFibration.restrictPreimage_mooreLoopMap`: over the Moore loops of positive
  length, the Moore loop map of a Hurewicz fibration is a Hurewicz fibration.

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

end MooreLoopSpace

open MooreLoopSpace

/-! ### The Moore loop map over positive lengths -/

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- **Over the Moore loops of positive length, the Moore loop map of a Hurewicz fibration is a
Hurewicz fibration.** Under `MooreLoopSpace.posLengthHomeomorph` it is the product of the identity
of `(0, ∞)` with the fixed-interval loop map, a Hurewicz fibration by
`TauCeti.IsHurewiczFibration.loopMap`. Without the restriction to positive lengths the statement
fails (`TauCeti.MooreLoopSpace.not_forall_isHurewiczFibration_map`). -/
theorem IsHurewiczFibration.restrictPreimage_mooreLoopMap (hp : IsHurewiczFibration.{w} p)
    (e : E) :
    IsHurewiczFibration.{w} ((length ⁻¹' Set.Ioi 0 : Set (MooreLoopSpace B (p e))).restrictPreimage
      (map ⟨p, hp.continuous⟩ rfl)) := by
  -- the domain is the set of Moore loops of positive length, as the loop map preserves lengths
  have hdom : (map ⟨p, hp.continuous⟩ rfl) ⁻¹' (length ⁻¹' Set.Ioi 0 : Set (MooreLoopSpace B (p e)))
      = length ⁻¹' Set.Ioi 0 := by
    ext; simp
  have hset (γ : ↥((map ⟨p, hp.continuous⟩ rfl) ⁻¹'
      (length ⁻¹' Set.Ioi 0 : Set (MooreLoopSpace B (p e))))) :
      (Homeomorph.setCongr hdom γ : MooreLoopSpace E e) = γ :=
    (rfl) -- `Homeomorph.setCongr` does not change the underlying point
  let φ := (Homeomorph.setCongr hdom).trans (posLengthHomeomorph e)
  have hφ : (length ⁻¹' Set.Ioi 0 : Set (MooreLoopSpace B (p e))).restrictPreimage
      (map ⟨p, hp.continuous⟩ rfl) =
      (posLengthHomeomorph (p e)).symm ∘
        (Prod.map (Homeomorph.refl _) fun γ : Ω E e ↦ (γ.map hp.continuous : Ω B (p e))) ∘ φ := by
    funext γ
    simp only [Function.comp_apply]
    rw [Homeomorph.eq_symm_apply]
    refine Prod.ext (Subtype.ext ?_) ?_
    · simp [φ, hset]
    · simpa [φ, hset] using toPath_map ⟨p, hp.continuous⟩ γ.1
  rw [hφ]
  exact (posLengthHomeomorph (p e)).symm.isHurewiczFibration.comp
    (((Homeomorph.refl _).isHurewiczFibration.prodMap (hp.loopMap e)).comp_homeomorph φ)

end TauCeti
