/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.NotSimplyConnected
public import TauCeti.Topology.Homotopy.LoopSpaceFibration
public import TauCeti.Topology.PathSpace.Moore.Comparison.FundamentalGroup

/-!
# Moore loop maps of Hurewicz fibrations

For a Hurewicz fibration `p : E → B` and a point `e : E`, the induced map
`Ω p : Ω E e → Ω B (p e)` on fixed-interval loop spaces is a Hurewicz fibration
(`TauCeti.IsHurewiczFibration.loopMap`). This file compares the Moore loop map
`MooreLoopSpace.map p : Ωᴹ E e → Ωᴹ B (p e)` with it.

Away from length zero the two agree. A Moore loop of positive length `L` is determined by `L` and
its normalization `s ↦ γ (L s)` to the unit interval, and every pair of a positive length and a
fixed-interval loop arises, so the Moore loops of positive length are homeomorphic to
`(0, ∞) × Ω X x` (`TauCeti.MooreLoopSpace.positiveLengthHomeomorph`). Under these homeomorphisms
the Moore loop map becomes `id × Ω p`, hence the restriction of the Moore loop map over the Moore
loops of positive length is a Hurewicz fibration
(`TauCeti.IsHurewiczFibration.mooreLoopMap_restrictPreimage`).

At length zero the statement fails. The only Moore loop of length zero is the unit, so the fibre
of the Moore loop map over the unit of `Ωᴹ B (p e)` is a point, while over the constant loop of
length one it is the fixed-interval loop space of the fibre `p⁻¹(p e)`. Concretely, the constant
loops of lengths `1 - s` form a path from the constant loop of length one to the unit, so if the
Moore loop map lifts paths, every Moore loop at `e` in the fibre is joined to the unit
(`TauCeti.HasHomotopyLiftingProperty.joined_one_of_mooreLoopMap`) and is null-homotopic in `E`.
For the map from a space to a point, which is a Hurewicz fibration, this forces the fundamental
group of the space to be trivial
(`TauCeti.subsingleton_fundamentalGroup_of_hasHomotopyLiftingProperty_mooreLoopMap`). So the
Moore loop map of the Hurewicz fibration from the circle to a point is not a Hurewicz fibration
(`TauCeti.not_isHurewiczFibration_mooreLoopMap_circle`). Statements about fibrations of loop
spaces are therefore made for fixed-interval loops, and transported to Moore loops through the
homotopy equivalence `TauCeti.MooreLoopSpace.homotopyEquivPath`.

## Main definitions

* `TauCeti.MooreLoopSpace.positiveLengthHomeomorph`: the Moore loops of positive length are
  homeomorphic to `(0, ∞) × Ω X x`, by the length and the normalization to the unit interval.

## Main results

* `TauCeti.IsHurewiczFibration.mooreLoopMap_restrictPreimage`: over the Moore loops of positive
  length, the Moore loop map of a Hurewicz fibration is a Hurewicz fibration.
* `TauCeti.HasHomotopyLiftingProperty.joined_one_of_mooreLoopMap`: if the Moore loop map lifts
  paths, every Moore loop in the fibre is joined to the unit.
* `TauCeti.not_isHurewiczFibration_mooreLoopMap_circle`: the Moore loop map of the circle to a
  point is not a Hurewicz fibration, although the map itself is one.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.2.
-/

public section

noncomputable section

open scoped NNReal
open unitInterval

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace MooreLoopSpace

variable {X : Type*} [TopologicalSpace X] {x : X}

variable (X x) in
/-- The Moore loops of positive length are homeomorphic to the product of the positive reals and
the fixed-interval loops: a loop `γ` of length `L > 0` corresponds to `(L, s ↦ γ (L s))`, and a
pair `(L, σ)` to the loop `t ↦ σ (t / L)` of length `L`. -/
def positiveLengthHomeomorph :
    {γ : MooreLoopSpace X x // 0 < γ.length} ≃ₜ {L : ℝ≥0 // 0 < L} × Path x x where
  toFun γ := (⟨γ.1.length, γ.2⟩, γ.1.toPath)
  invFun q := ⟨⟨q.2.toMoorePath.rescale q.1, by simp,
    by rw [MoorePath.target_rescale _ q.1.2.ne', Path.target_toMoorePath]⟩, by
    rw [← length_toMoorePath, MoorePath.length_rescale]
    exact q.1.2⟩
  left_inv γ := Subtype.ext <| ext <| by
    dsimp only
    rw [toMoorePath_toPath, MoorePath.rescale_rescale _ one_ne_zero, ← length_toMoorePath,
      MoorePath.rescale_length]
  right_inv q := Prod.ext (Subtype.ext <| by
      dsimp only
      rw [← length_toMoorePath, MoorePath.length_rescale]) <|
    Path.ext <| funext fun s ↦ by
      dsimp only
      rw [toPath_apply, MoorePath.rescale_apply, MoorePath.length_rescale,
        Path.length_toMoorePath, one_mul, mul_div_cancel_left₀ _ q.1.2.ne',
        Path.toMoorePath_apply]
      exact q.2.extend_extends' s
  continuous_toFun := by fun_prop
  continuous_invFun := by
    refine Continuous.subtype_mk (isEmbedding_toMoorePath.continuous_iff.2 ?_) _
    exact (Path.continuous_toMoorePath.comp continuous_snd).moorePath_rescale
      (continuous_subtype_val.comp continuous_fst) fun q ↦ q.1.2.ne'

@[simp]
theorem coe_fst_positiveLengthHomeomorph (γ : {γ : MooreLoopSpace X x // 0 < γ.length}) :
    ((positiveLengthHomeomorph X x γ).1 : ℝ≥0) = γ.1.length :=
  (rfl)

@[simp]
theorem snd_positiveLengthHomeomorph (γ : {γ : MooreLoopSpace X x // 0 < γ.length}) :
    (positiveLengthHomeomorph X x γ).2 = γ.1.toPath :=
  (rfl)

@[simp]
theorem toMoorePath_positiveLengthHomeomorph_symm_apply (q : {L : ℝ≥0 // 0 < L} × Path x x) :
    ((positiveLengthHomeomorph X x).symm q).1.toMoorePath = q.2.toMoorePath.rescale q.1 :=
  (rfl)

end MooreLoopSpace

open MooreLoopSpace

/-- **The Moore loop map of a Hurewicz fibration is a Hurewicz fibration away from length zero**:
for a Hurewicz fibration `p : E → B` and `e : E`, the restriction of the Moore loop map
`Ωᴹ E e → Ωᴹ B (p e)` over the Moore loops of positive length is a Hurewicz fibration. Over the
whole Moore loop space this fails (`TauCeti.not_isHurewiczFibration_mooreLoopMap_circle`). -/
theorem IsHurewiczFibration.mooreLoopMap_restrictPreimage {p : E → B}
    (hp : IsHurewiczFibration.{w} p) (e : E) :
    IsHurewiczFibration.{w}
      ({β : MooreLoopSpace B (p e) | 0 < β.length}.restrictPreimage
        (MooreLoopSpace.map ⟨p, hp.continuous⟩ rfl)) := by
  -- In the coordinates of `positiveLengthHomeomorph` the map is `id × Ω p`.
  have hq : IsHurewiczFibration.{w}
      (Prod.map id fun γ : Path e e ↦ (γ.map hp.continuous : Path (p e) (p e))) :=
    (Homeomorph.refl {L : ℝ≥0 // 0 < L}).isHurewiczFibration.prodMap (hp.loopMap e)
  convert ((positiveLengthHomeomorph B (p e)).symm.isHurewiczFibration.comp hq).comp_homeomorph
    (((Homeomorph.refl _).subtype
      (p := (· ∈ MooreLoopSpace.map ⟨p, hp.continuous⟩ rfl ⁻¹' {β | 0 < β.length}))
      (q := fun γ : MooreLoopSpace E e ↦ 0 < γ.length) fun γ ↦ by simp).trans
      (positiveLengthHomeomorph E e)) using 1
  funext ⟨γ, hγ⟩
  refine (positiveLengthHomeomorph B (p e)).injective (Prod.ext (Subtype.ext ?_) ?_) <;> simp

/-! ### Failure at length zero -/

/-- If the Moore loop map of `p` lifts homotopies parametrized by a nonempty space, then every Moore
loop at `e` lying in the fibre `p⁻¹(p e)` is joined to the unit in the Moore loop space of `E`:
the constant loops of lengths `(1 - s) L` shrink its image to the unit, and a lift of this path
ends at a loop of length zero. -/
theorem HasHomotopyLiftingProperty.joined_one_of_mooreLoopMap {A : Type w} [TopologicalSpace A]
    [Nonempty A] {p : C(E, B)} {e : E}
    (h : HasHomotopyLiftingProperty (MooreLoopSpace.map p rfl : MooreLoopSpace E e → _) A)
    {γ : MooreLoopSpace E e} (hγ : MooreLoopSpace.map p rfl γ = constOfLength (p e) γ.length) :
    Joined γ 1 := by
  let δ : Path (MooreLoopSpace.map p rfl γ) 1 :=
    { toFun s := constOfLength (p e) (γ.length * toNNReal (σ s))
      continuous_toFun := by fun_prop
      source' := by simp [hγ]
      target' := by simp }
  obtain ⟨Γ, hΓ₀, hΓ⟩ := h.exists_path_lift δ
  have hΓ₁ : Γ 1 = 1 := by
    rw [← length_eq_zero_iff]
    simpa [δ] using congrArg MooreLoopSpace.length (congrFun hΓ 1)
  exact ⟨⟨Γ, hΓ₀, hΓ₁⟩⟩

/-- If the Moore loop map of a map `E → B` to a subsingleton lifts homotopies parametrized by a
nonempty space, then the fundamental group of `E` is trivial: every Moore loop lies in the fibre,
so it is joined to the unit. Maps to a point are Hurewicz fibrations
(`TauCeti.isHurewiczFibration_of_subsingleton`), so this is an obstruction to the Moore loop map of
a Hurewicz fibration being one. -/
theorem subsingleton_fundamentalGroup_of_hasHomotopyLiftingProperty_mooreLoopMap
    [Subsingleton B] {A : Type w} [TopologicalSpace A] [Nonempty A] {p : C(E, B)} {e : E}
    (h : HasHomotopyLiftingProperty (MooreLoopSpace.map p rfl : MooreLoopSpace E e → _) A) :
    Subsingleton (FundamentalGroup E e) := by
  have hone (γ : MooreLoopSpace E e) : fundamentalGroupHom e γ = 1 := by
    have hγ := h.joined_one_of_mooreLoopMap (γ := γ) <| ext <| MoorePath.ext (by simp) fun _ ↦
      Subsingleton.elim _ _
    rw [← zerothHomotopyEquivFundamentalGroup_mk, ← map_one (fundamentalGroupHom e),
      ← zerothHomotopyEquivFundamentalGroup_mk]
    exact congrArg _ (ZerothHomotopy.sound hγ.somePath)
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨γ, rfl⟩ := fundamentalGroupHom_surjective e a
  obtain ⟨δ, rfl⟩ := fundamentalGroupHom_surjective e b
  rw [hone, hone]

/-- **The Moore loop map of a Hurewicz fibration need not be a Hurewicz fibration.** The map from
the circle to a point is a Hurewicz fibration (`TauCeti.isHurewiczFibration_of_subsingleton`), but
its Moore loop map `Ωᴹ S¹ → Ωᴹ pt ≅ [0, ∞)` is not one: the fibre over length zero is a point,
while the fibre over length one is the fixed-interval loop space of the circle. -/
theorem not_isHurewiczFibration_mooreLoopMap_circle :
    ¬ IsHurewiczFibration.{w}
      (MooreLoopSpace.map (ContinuousMap.const Circle ()) rfl : MooreLoopSpace Circle 1 → _) :=
  fun h ↦ by
    have := Circle.nontrivial_fundamentalGroup 1
    exact not_subsingleton _
      (subsingleton_fundamentalGroup_of_hasHomotopyLiftingProperty_mooreLoopMap
        (h.hasHomotopyLiftingProperty PUnit))

end TauCeti
