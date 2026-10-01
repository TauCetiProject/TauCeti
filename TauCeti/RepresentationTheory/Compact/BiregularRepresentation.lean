/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.RegularRepresentation

/-!
# The biregular representation of a compact group on `L²(G)`

A compact group `G` acts on `L²(G)` from both sides, by `TauCeti.leftRegularLp` and
`TauCeti.rightRegularLp`. The two actions commute, and this file bundles them into the **biregular
representation** of `G × G`,

`((g, h) · f) x = f (g⁻¹ * x * h)`.

Bi-translation preserves normalized Haar measure, so the action is unitary. It is also strongly
continuous: the orbit map is continuous at every `L²` function, although for an infinite compact
group the representation need not be continuous in the operator norm. This is the `G × G`-action
used by the equivariant form of the Peter-Weyl decomposition.

## Main definitions

* `TauCeti.biRegularLp`: the biregular representation of `G × G` on `L²(G)`.

## Main statements

* `TauCeti.biRegularLp_apply`: unfolds the action to `Lp.compMeasurePreserving`; the body of
  `biRegularLp` is not exposed, so this is the interface to its raw form.
* `TauCeti.biRegularLp_toLp`: computes the action on continuous representatives.
* `TauCeti.biRegularLp_apply_mk_one` and `TauCeti.biRegularLp_apply_one_mk`: the two factors are
  the left and the right regular representation.
* `TauCeti.biRegularLp_apply_eq_left_right` and `TauCeti.biRegularLp_apply_eq_right_left`: the
  action is the composite of the two translations, in either order.
* `TauCeti.isUnitary_biRegularLp`: the representation is unitary.
* `TauCeti.continuous_biRegularLp_apply`: the action is strongly continuous.
-/

public section

open MeasureTheory

namespace TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Bi-translation `x ↦ g⁻¹ * x * h` preserves normalized Haar measure. -/
theorem measurePreserving_biTranslate (g h : G) :
    MeasurePreserving (fun x : G => g⁻¹ * x * h) (haarProb G) (haarProb G) :=
  (measurePreserving_mul_right (haarProb G) h).comp
    (measurePreserving_mul_left (haarProb G) g⁻¹)

variable (𝕜 G) in
/-- **The biregular representation** of `G × G` on `L²(G)`: `(g, h)` acts by
`f ↦ (x ↦ f (g⁻¹ * x * h))`.

The two factors are ordered so that restricting along `g ↦ (g, 1)` gives
`TauCeti.leftRegularLp`, while restricting along `h ↦ (1, h)` gives
`TauCeti.rightRegularLp`. -/
noncomputable def biRegularLp : ContRepresentation 𝕜 (G × G) (Lp 𝕜 2 (haarProb G)) :=
  .ofMonoidHom
    { toFun p := (Lp.compMeasurePreservingₗᵢ 𝕜 (fun x => p.1⁻¹ * x * p.2)
        (measurePreserving_biTranslate p.1 p.2)).toContinuousLinearMap
      map_one' := ContinuousLinearMap.ext fun f => by
        simp only [one_apply_eq_self, LinearIsometry.coe_toContinuousLinearMap,
          Lp.compMeasurePreservingₗᵢ_apply, Prod.fst_one, Prod.snd_one, inv_one, one_mul, mul_one,
          ← Function.id_def]
        exact Lp.compMeasurePreserving_id_apply f
      map_mul' p q := ContinuousLinearMap.ext fun f => by
        have hfun : (fun x : G => (p * q).1⁻¹ * x * (p * q).2) =
            (fun x : G => q.1⁻¹ * x * q.2) ∘ (fun x : G => p.1⁻¹ * x * p.2) := by
          funext x
          simp only [Function.comp_apply, Prod.fst_mul, Prod.snd_mul, mul_inv_rev]
          simp [mul_assoc]
        simp only [mul_apply_eq_comp, hfun]
        exact Lp.compMeasurePreserving_comp_apply f
          (measurePreserving_biTranslate q.1 q.2)
          (measurePreserving_biTranslate p.1 p.2) }

/-- **Bi-translation on `L²(G)`, unfolded to the underlying `Lp.compMeasurePreserving`.** The body
of `biRegularLp` is not exposed, so this is the lemma that moves a statement between the
representation and its raw `Lp.compMeasurePreserving` form. -/
theorem biRegularLp_apply (p : G × G) (f : Lp 𝕜 2 (haarProb G)) :
    biRegularLp 𝕜 G p f =
      Lp.compMeasurePreserving (fun x => p.1⁻¹ * x * p.2)
        (measurePreserving_biTranslate p.1 p.2) f :=
  (rfl)

/-- Bi-translation on `L²(G)` is represented by bi-translation of functions. -/
theorem coeFn_biRegularLp (p : G × G) (f : Lp 𝕜 2 (haarProb G)) :
    biRegularLp 𝕜 G p f =ᵐ[haarProb G] fun x => f (p.1⁻¹ * x * p.2) := by
  rw [biRegularLp_apply]
  exact Lp.coeFn_compMeasurePreserving f _

/-- **On a continuous function, the biregular representation is bi-translation.** -/
@[simp]
theorem biRegularLp_toLp (F : C(G, 𝕜)) (p : G × G) :
    biRegularLp 𝕜 G p (ContinuousMap.toLp 2 (haarProb G) 𝕜 F) =
      ContinuousMap.toLp 2 (haarProb G) 𝕜
        (F.comp ⟨fun x => p.1⁻¹ * x * p.2,
          continuous_const.mul continuous_id |>.mul continuous_const⟩) := by
  rw [biRegularLp_apply]
  exact Lp.compMeasurePreserving_toLp 𝕜 F
    ⟨fun x => p.1⁻¹ * x * p.2, continuous_const.mul continuous_id |>.mul continuous_const⟩
    (measurePreserving_biTranslate p.1 p.2)

/-- The first factor of the biregular representation is the left regular representation. -/
@[simp]
theorem biRegularLp_apply_mk_one (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    biRegularLp 𝕜 G (g, 1) f = leftRegularLp 𝕜 G g f := by
  rw [biRegularLp_apply, leftRegularLp_apply]
  congr
  funext x
  simp

/-- The second factor of the biregular representation is the right regular representation. -/
@[simp]
theorem biRegularLp_apply_one_mk (h : G) (f : Lp 𝕜 2 (haarProb G)) :
    biRegularLp 𝕜 G (1, h) f = rightRegularLp 𝕜 G h f := by
  rw [biRegularLp_apply, rightRegularLp_apply]
  congr
  funext x
  simp

/-- The biregular action is left translation after right translation. -/
theorem biRegularLp_apply_eq_left_right (p : G × G) (f : Lp 𝕜 2 (haarProb G)) :
    biRegularLp 𝕜 G p f =
      leftRegularLp 𝕜 G p.1 (rightRegularLp 𝕜 G p.2 f) := by
  calc
    biRegularLp 𝕜 G p f = biRegularLp 𝕜 G ((p.1, 1) * (1, p.2)) f := by simp
    _ = biRegularLp 𝕜 G (p.1, 1) (biRegularLp 𝕜 G (1, p.2) f) := by
      rw [map_mul]
      rfl
    _ = leftRegularLp 𝕜 G p.1 (rightRegularLp 𝕜 G p.2 f) := by simp

/-- The biregular action is also right translation after left translation; in particular, its two
factors commute. -/
theorem biRegularLp_apply_eq_right_left (p : G × G) (f : Lp 𝕜 2 (haarProb G)) :
    biRegularLp 𝕜 G p f =
      rightRegularLp 𝕜 G p.2 (leftRegularLp 𝕜 G p.1 f) := by
  calc
    biRegularLp 𝕜 G p f = biRegularLp 𝕜 G ((1, p.2) * (p.1, 1)) f := by simp
    _ = biRegularLp 𝕜 G (1, p.2) (biRegularLp 𝕜 G (p.1, 1) f) := by
      rw [map_mul]
      rfl
    _ = rightRegularLp 𝕜 G p.2 (leftRegularLp 𝕜 G p.1 f) := by simp

variable (𝕜 G) in
/-- **The biregular representation is unitary**, because every bi-translation preserves normalized
Haar measure. -/
theorem isUnitary_biRegularLp : ContRepresentation.IsUnitary (biRegularLp 𝕜 G) := by
  rw [ContRepresentation.isUnitary_iff_norm_map]
  intro p f
  rw [biRegularLp_apply]
  exact Lp.norm_compMeasurePreserving f _

/-- **The biregular representation is strongly continuous:** every orbit map
`(g, h) ↦ (g, h) · f` is continuous. -/
theorem continuous_biRegularLp_apply (f : Lp 𝕜 2 (haarProb G)) :
    Continuous fun p : G × G => biRegularLp 𝕜 G p f := by
  have hp : Continuous fun p : G × G =>
      (⟨fun x : G => p.1⁻¹ * x * p.2,
        continuous_const.mul continuous_id |>.mul continuous_const⟩ : C(G, G)) :=
    (ContinuousMap.curry
      ⟨fun q : (G × G) × G => q.1.1⁻¹ * q.2 * q.1.2,
        (continuous_fst.fst.inv.mul continuous_snd).mul continuous_fst.snd⟩).continuous
  simp only [biRegularLp_apply]
  exact continuous_const.compMeasurePreservingLp hp _ (by simp)

end CompactGroup

end TauCeti
