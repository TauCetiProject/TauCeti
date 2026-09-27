/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.RegularRepresentation

/-!
# The biregular representation of a compact group on `L²(G)`

A compact group `G` acts on `L²(G)` from both sides. This file bundles the left action
`(g · f) x = f (g⁻¹ * x)` as `TauCeti.leftRegularLp`, and the commuting left and right actions
together as the **biregular representation**

`((g, h) · f) x = f (g⁻¹ * x * h)`.

Both actions preserve normalized Haar measure and are therefore unitary. They are also strongly
continuous: the orbit map is continuous at every `L²` function, although for an infinite compact
group the representation need not be continuous in the operator norm. The biregular action is the
`G × G`-action used by the equivariant form of the Peter-Weyl decomposition.

## Main definitions

* `TauCeti.leftRegularLp`: the left regular representation of `G` on `L²(G)`.
* `TauCeti.biRegularLp`: the biregular representation of `G × G` on `L²(G)`.

## Main statements

* `TauCeti.leftRegularLp_apply`, `TauCeti.biRegularLp_apply`: unfold the actions to
  `Lp.compMeasurePreserving`.
* `TauCeti.leftRegularLp_toLp`, `TauCeti.biRegularLp_toLp`: compute the actions on continuous
  representatives.
* `TauCeti.isUnitary_leftRegularLp`, `TauCeti.isUnitary_biRegularLp`: both representations are
  unitary.
* `TauCeti.continuous_leftRegularLp_apply`, `TauCeti.continuous_biRegularLp_apply`: both actions are
  strongly continuous.
-/

@[expose] public section

open MeasureTheory

namespace TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (𝕜 G) in
/-- **The left regular representation** of a compact group on `L²(G)`: the element `g` acts by
`f ↦ (x ↦ f (g⁻¹ * x))`. The inverse makes this a representation rather than an
antirepresentation.

As for `TauCeti.rightRegularLp`, only strong continuity is asserted; operator-norm continuity is
not needed and generally fails for infinite compact groups. -/
noncomputable def leftRegularLp : ContRepresentation 𝕜 G (Lp 𝕜 2 (haarProb G)) :=
  .ofMonoidHom
    { toFun g := (Lp.compMeasurePreservingₗᵢ 𝕜 (g⁻¹ * ·)
        (measurePreserving_mul_left (haarProb G) g⁻¹)).toContinuousLinearMap
      map_one' := ContinuousLinearMap.ext fun f => by
        change Lp.compMeasurePreserving (fun x : G => (1 : G)⁻¹ * x)
            (measurePreserving_mul_left (haarProb G) (1 : G)⁻¹) f = f
        simpa only [inv_one, one_mul, Function.id_def] using
          (Lp.compMeasurePreserving_id_apply (E := 𝕜) (p := 2) f)
      map_mul' g h := ContinuousLinearMap.ext fun f => by
        have hfun : (fun x : G => (g * h)⁻¹ * x) =
            (fun x : G => h⁻¹ * x) ∘ (fun x : G => g⁻¹ * x) := by
          funext x
          simp only [Function.comp_apply, mul_inv_rev, mul_assoc]
        simp only [mul_apply_eq_comp, hfun]
        exact Lp.compMeasurePreserving_comp_apply f
          (measurePreserving_mul_left (haarProb G) h⁻¹)
          (measurePreserving_mul_left (haarProb G) g⁻¹) }

/-- **Left translation on `L²(G)`, unfolded to `Lp.compMeasurePreserving`.** -/
theorem leftRegularLp_apply (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    leftRegularLp 𝕜 G g f =
      Lp.compMeasurePreserving (g⁻¹ * ·) (measurePreserving_mul_left (haarProb G) g⁻¹) f :=
  rfl

/-- Left translation on `L²(G)` is represented by left translation of functions. -/
theorem coeFn_leftRegularLp (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    leftRegularLp 𝕜 G g f =ᵐ[haarProb G] fun x => f (g⁻¹ * x) := by
  rw [leftRegularLp_apply]
  exact Lp.coeFn_compMeasurePreserving f _

/-- **On a continuous function, the left regular representation is left translation by the
inverse.** -/
@[simp]
theorem leftRegularLp_toLp (F : C(G, 𝕜)) (g : G) :
    leftRegularLp 𝕜 G g (ContinuousMap.toLp 2 (haarProb G) 𝕜 F) =
      ContinuousMap.toLp 2 (haarProb G) 𝕜 (F.comp (.mulLeft g⁻¹)) := by
  rw [leftRegularLp_apply]
  exact Lp.compMeasurePreserving_toLp 𝕜 F (.mulLeft g⁻¹)
    (measurePreserving_mul_left (haarProb G) g⁻¹)

variable (𝕜 G) in
/-- **The left regular representation is unitary**, because left translation preserves normalized
Haar measure. -/
theorem isUnitary_leftRegularLp : ContRepresentation.IsUnitary (leftRegularLp 𝕜 G) := by
  rw [ContRepresentation.isUnitary_iff_norm_map]
  intro g f
  rw [leftRegularLp_apply]
  exact Lp.norm_compMeasurePreserving f _

/-- **The left regular representation is strongly continuous:** every orbit map `g ↦ g · f` is
continuous. -/
theorem continuous_leftRegularLp_apply (f : Lp 𝕜 2 (haarProb G)) :
    Continuous fun g : G => leftRegularLp 𝕜 G g f := by
  have hg : Continuous fun g : G => ContinuousMap.mulLeft (X := G) g⁻¹ :=
    (ContinuousMap.curry
      ⟨fun p : G × G => p.1⁻¹ * p.2, continuous_fst.inv.mul continuous_snd⟩).continuous
  simp only [leftRegularLp_apply]
  exact continuous_const.compMeasurePreservingLp hg _ (by simp)

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
        change Lp.compMeasurePreserving (fun x : G => (1 : G)⁻¹ * x * 1)
            (measurePreserving_biTranslate (1 : G) 1) f = f
        simpa only [Prod.fst_one, Prod.snd_one, inv_one, one_mul, mul_one, Function.id_def] using
          (Lp.compMeasurePreserving_id_apply (E := 𝕜) (p := 2) f)
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

/-- **Bi-translation on `L²(G)`, unfolded to `Lp.compMeasurePreserving`.** -/
theorem biRegularLp_apply (p : G × G) (f : Lp 𝕜 2 (haarProb G)) :
    biRegularLp 𝕜 G p f =
      Lp.compMeasurePreserving (fun x => p.1⁻¹ * x * p.2)
        (measurePreserving_biTranslate p.1 p.2) f :=
  rfl

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
