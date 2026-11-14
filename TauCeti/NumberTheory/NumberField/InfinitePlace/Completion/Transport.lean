/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.WithAbs
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Real
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Transport
import Mathlib.Analysis.Complex.Basic

/-!
# Transporting archimedean completions along an isomorphism of fields

A ring isomorphism `e : K ≃+* L` of fields that intertwines infinite places `w` of `K` and `w'` of
`L` (`∀ x, w' (e x) = w x`) extends by continuity to the isometric ring isomorphism
`AbsoluteValue.Completion.congr e hw : w.Completion ≃+* w'.Completion`. Specializing `w'` to
`NumberField.InfinitePlace.equivOfRingEquiv e w` gives the canonical completion isomorphism
`NumberField.InfinitePlace.Completion.ringEquivOfRingEquiv e w :
w.Completion ≃+* (equivOfRingEquiv e w).Completion`.

Because `w'` and `w` have the same multiplicity, `AbsoluteValue.Completion.congr` preserves the
normalized archimedean absolute value `completionNormalizedAbsValue`. At a real place it commutes on
the nose with `extensionEmbeddingOfIsReal`; at every infinite place it commutes with the canonical
real inclusion `Completion.ofReal` and the norm-section homomorphism `completionNormSection`, while
`extensionEmbedding` into `ℂ` commutes up to complex conjugation.

No `NumberField` hypothesis is needed on `K` or `L`.

## Main definitions

* `NumberField.InfinitePlace.Completion.ringEquivOfRingEquiv`: the ring isomorphism
  `w.Completion ≃+* (equivOfRingEquiv e w).Completion` induced by `e : K ≃+* L`.

## Main results

* `NumberField.InfinitePlace.Completion.congr_coe`: `AbsoluteValue.Completion.congr` extends `e` on
  coercions from `K` into `w.Completion`.
* `NumberField.InfinitePlace.completionNormalizedAbsValue_congr`: `AbsoluteValue.Completion.congr`
  preserves `completionNormalizedAbsValue`.
* `NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_congr`: at real places,
  `AbsoluteValue.Completion.congr` commutes with `extensionEmbeddingOfIsReal`.
* `NumberField.InfinitePlace.Completion.extensionEmbedding_congr_eq_or_eq_conj`: on `w.Completion`,
  `extensionEmbedding w'` composed with `congr` is either `extensionEmbedding w` or its complex
  conjugate.
* `NumberField.InfinitePlace.Completion.congr_ofReal`,
  `NumberField.InfinitePlace.units_map_congr_completionNormSection`:
  `AbsoluteValue.Completion.congr` commutes with `Completion.ofReal` and `completionNormSection`.
* `NumberField.InfinitePlace.Completion.ringEquivOfRingEquiv_algebraMap`,
  `NumberField.InfinitePlace.Completion.norm_ringEquivOfRingEquiv`,
  `NumberField.InfinitePlace.completionNormalizedAbsValue_ringEquivOfRingEquiv`: specializations to
  `equivOfRingEquiv e w`.

## Implementation notes

The primary lemmas take an arbitrary target place `w'` together with `hw : ∀ x, w' (e x) = w x`
rather than fixing `w' = equivOfRingEquiv e w`. Call sites holding an independently given place
need no cast along an equality of places, and functoriality (`congr_refl`, `congr_symm`,
`congr_trans`) lives directly on `AbsoluteValue.Completion.congr` without heterogeneous casts.
`eq_equivOfRingEquiv_iff` specializes `hw` immediately when `w'` is `equivOfRingEquiv e w`.
-/

public section
noncomputable section

open scoped NNReal ComplexConjugate

namespace NumberField.InfinitePlace

variable {K L : Type*} [Field K] [Field L]

section ApplyEq

variable {e : K ≃+* L} {w : InfinitePlace K} {w' : InfinitePlace L}

-- Not `@[simp]`: `AbsoluteValue.Completion.congr_coe` and `WithAbs.congr_apply` already prove this.
/-- `AbsoluteValue.Completion.congr` sends the coercion of `x : K` in `w.Completion` to the
coercion of `e x` in `w'.Completion`. -/
theorem Completion.congr_coe (hw : ∀ x, w' (e x) = w x) (x : K) :
    AbsoluteValue.Completion.congr e hw (x : w.Completion) = (e x : w'.Completion) := by
  rw [← Completion.algebraMap_apply_eq_coe, ← Completion.algebraMap_apply_eq_coe,
    AbsoluteValue.Completion.congr_algebraMap]

-- Not `@[simp]`: `completionNormalizedAbsValue_apply` already simplifies the left-hand side.
/-- `AbsoluteValue.Completion.congr` preserves the normalized archimedean absolute value. -/
theorem completionNormalizedAbsValue_congr (hw : ∀ x, w' (e x) = w x) (z : w.Completion) :
    completionNormalizedAbsValue w' (AbsoluteValue.Completion.congr e hw z) =
      completionNormalizedAbsValue w z := by
  rw [completionNormalizedAbsValue_apply, AbsoluteValue.Completion.norm_congr,
    mult_eq_of_apply_eq hw, completionNormalizedAbsValue_apply]

/-- At real places intertwined by `e : K ≃+* L`, `AbsoluteValue.Completion.congr` commutes with the
real extension embeddings into `ℝ`. -/
@[simp]
theorem Completion.extensionEmbeddingOfIsReal_congr (hw : ∀ x, w' (e x) = w x) (hw' : w'.IsReal)
    (z : w.Completion) :
    Completion.extensionEmbeddingOfIsReal hw' (AbsoluteValue.Completion.congr e hw z) =
      Completion.extensionEmbeddingOfIsReal ((isReal_iff_of_apply_eq hw).mp hw') z := by
  refine congrFun (Completion.funext_of_continuous
    ((Completion.isometry_extensionEmbeddingOfIsReal hw').continuous.comp
      (AbsoluteValue.Completion.continuous_congr hw))
    (Completion.isometry_extensionEmbeddingOfIsReal ((isReal_iff_of_apply_eq hw).mp hw')).continuous
    fun x ↦ ?_) z
  rw [Function.comp_apply, AbsoluteValue.Completion.congr_algebraMap,
    Completion.algebraMap_apply_eq_coe, Completion.algebraMap_apply_eq_coe,
    Completion.extensionEmbeddingOfIsReal_coe, Completion.extensionEmbeddingOfIsReal_coe,
    WithAbs.equiv_apply, WithAbs.equiv_apply, WithAbs.ofAbs_toAbs, WithAbs.ofAbs_toAbs,
    embedding_of_isReal_apply_of_apply_eq hw hw']

/-- Composing `extensionEmbedding w'` with `AbsoluteValue.Completion.congr e hw` gives either
`extensionEmbedding w` everywhere or its complex conjugate everywhere. -/
theorem Completion.extensionEmbedding_congr_eq_or_eq_conj (hw : ∀ x, w' (e x) = w x) :
    (∀ z : w.Completion,
        Completion.extensionEmbedding w' (AbsoluteValue.Completion.congr e hw z) =
          Completion.extensionEmbedding w z) ∨
      ∀ z : w.Completion,
        Completion.extensionEmbedding w' (AbsoluteValue.Completion.congr e hw z) =
          conj (Completion.extensionEmbedding w z) := by
  have hmk : mk (w'.embedding.comp (e : K →+* L)) = mk w.embedding := by
    rw [mk_embedding]
    exact InfinitePlace.ext _ _ fun x ↦ by
      rw [apply, RingHom.comp_apply, RingHom.coe_coe, norm_embedding_eq, hw]
  rcases mk_eq_iff.mp hmk with hemb | hemb
  · left
    intro z
    refine congrFun (Completion.funext_of_continuous
      ((Completion.isometry_extensionEmbedding w').continuous.comp
        (AbsoluteValue.Completion.continuous_congr hw))
      (Completion.isometry_extensionEmbedding w).continuous fun x ↦ ?_) z
    rw [Function.comp_apply, AbsoluteValue.Completion.congr_algebraMap,
      Completion.algebraMap_apply_eq_coe, Completion.algebraMap_apply_eq_coe]
    simpa using RingHom.congr_fun hemb x
  · right
    intro z
    refine congrFun (Completion.funext_of_continuous
      ((Completion.isometry_extensionEmbedding w').continuous.comp
        (AbsoluteValue.Completion.continuous_congr hw))
      (Complex.continuous_conj.comp (Completion.isometry_extensionEmbedding w).continuous)
      fun x ↦ ?_) z
    rw [Function.comp_apply, Function.comp_apply, AbsoluteValue.Completion.congr_algebraMap,
      Completion.algebraMap_apply_eq_coe, Completion.algebraMap_apply_eq_coe]
    have hx : conj (w'.embedding (e x)) = w.embedding x := by
      simpa [ComplexEmbedding.conjugate_coe_eq] using RingHom.congr_fun hemb x
    simp [← hx]

/-- `AbsoluteValue.Completion.congr` commutes with the canonical inclusion `Completion.ofReal` of
`ℝ` at every infinite place, real or complex. -/
@[simp]
theorem Completion.congr_ofReal (hw : ∀ x, w' (e x) = w x) (r : ℝ) :
    AbsoluteValue.Completion.congr e hw (Completion.ofReal w r) = Completion.ofReal w' r := by
  rw [Completion.eq_ofReal_iff]
  let f : ℝ →+* ℂ :=
    (Completion.extensionEmbedding w').comp
      ((AbsoluteValue.Completion.congr e hw).toRingHom.comp (Completion.ofReal w))
  have hf : f = Complex.ofRealHom :=
    Complex.ringHom_eq_ofReal_of_continuous <|
      (Completion.isometry_extensionEmbedding w').continuous.comp <|
        (AbsoluteValue.Completion.continuous_congr hw).comp (Completion.continuous_ofReal w)
  exact RingHom.congr_fun hf r

/-- `AbsoluteValue.Completion.congr` commutes with the positive-real norm section
`completionNormSection`. -/
@[simp]
theorem units_map_congr_completionNormSection (hw : ∀ x, w' (e x) = w x) (t : ℝ≥0ˣ) :
    Units.map (AbsoluteValue.Completion.congr e hw : w.Completion →* w'.Completion)
        (completionNormSection w t) =
      completionNormSection w' t := by
  ext
  simp [mult_eq_of_apply_eq hw]

end ApplyEq

section EquivOfRingEquiv

/-- The ring isomorphism `w.Completion ≃+* (equivOfRingEquiv e w).Completion` of archimedean
completions induced by a field isomorphism `e : K ≃+* L`. -/
def Completion.ringEquivOfRingEquiv (e : K ≃+* L) (w : InfinitePlace K) :
    w.Completion ≃+* (equivOfRingEquiv e w).Completion :=
  AbsoluteValue.Completion.congr e (eq_equivOfRingEquiv_iff.mp rfl)

-- Not `@[simp]`: unfolding `ringEquivOfRingEquiv` to `AbsoluteValue.Completion.congr` would take
-- the `ringEquivOfRingEquiv_*` lemmas out of simp normal form.
/-- `Completion.ringEquivOfRingEquiv e w` is `AbsoluteValue.Completion.congr` for
`equivOfRingEquiv e w`. -/
theorem Completion.ringEquivOfRingEquiv_eq_congr (e : K ≃+* L) (w : InfinitePlace K) :
    Completion.ringEquivOfRingEquiv e w =
      AbsoluteValue.Completion.congr (w := (equivOfRingEquiv e w).1) e
        (eq_equivOfRingEquiv_iff.mp rfl) :=
  (rfl)

/-- `Completion.ringEquivOfRingEquiv` intertwines `algebraMap` from `K` and `L`. -/
@[simp]
theorem Completion.ringEquivOfRingEquiv_algebraMap (e : K ≃+* L) (w : InfinitePlace K) (x : K) :
    Completion.ringEquivOfRingEquiv e w (algebraMap K w.Completion x) =
      algebraMap L (equivOfRingEquiv e w).Completion (e x) :=
  AbsoluteValue.Completion.congr_algebraMap _ x

/-- `Completion.ringEquivOfRingEquiv` sends `(x : w.Completion)` to
`(e x : (equivOfRingEquiv e w).Completion)`. -/
@[simp]
theorem Completion.ringEquivOfRingEquiv_coe (e : K ≃+* L) (w : InfinitePlace K) (x : K) :
    Completion.ringEquivOfRingEquiv e w (x : w.Completion) =
      (e x : (equivOfRingEquiv e w).Completion) :=
  Completion.congr_coe _ x

/-- `Completion.ringEquivOfRingEquiv` is an isometry. -/
theorem Completion.isometry_ringEquivOfRingEquiv (e : K ≃+* L) (w : InfinitePlace K) :
    Isometry (Completion.ringEquivOfRingEquiv e w) :=
  AbsoluteValue.Completion.isometry_congr _

/-- `Completion.ringEquivOfRingEquiv` preserves the norm. -/
@[simp]
theorem Completion.norm_ringEquivOfRingEquiv (e : K ≃+* L) (w : InfinitePlace K)
    (z : w.Completion) :
    ‖Completion.ringEquivOfRingEquiv e w z‖ = ‖z‖ :=
  AbsoluteValue.Completion.norm_congr _ z

/-- `Completion.ringEquivOfRingEquiv` is continuous. -/
@[continuity, fun_prop]
theorem Completion.continuous_ringEquivOfRingEquiv (e : K ≃+* L) (w : InfinitePlace K) :
    Continuous (Completion.ringEquivOfRingEquiv e w) :=
  AbsoluteValue.Completion.continuous_congr _

/-- `Completion.ringEquivOfRingEquiv` is the unique continuous ring homomorphism extending `e`. -/
theorem Completion.eq_ringEquivOfRingEquiv_of_continuous (e : K ≃+* L) (w : InfinitePlace K)
    {f : w.Completion →+* (equivOfRingEquiv e w).Completion} (hf : Continuous f)
    (hfK : ∀ x : K, f (algebraMap K w.Completion x) =
      algebraMap L (equivOfRingEquiv e w).Completion (e x)) :
    f = (Completion.ringEquivOfRingEquiv e w).toRingHom :=
  AbsoluteValue.Completion.eq_congr_of_continuous _ hf hfK

-- Not `@[simp]`: `completionNormalizedAbsValue_apply`, `norm_ringEquivOfRingEquiv`, and
-- `mult_equivOfRingEquiv` already prove this.
/-- `Completion.ringEquivOfRingEquiv` preserves `completionNormalizedAbsValue`. -/
theorem completionNormalizedAbsValue_ringEquivOfRingEquiv (e : K ≃+* L) (w : InfinitePlace K)
    (z : w.Completion) :
    completionNormalizedAbsValue (equivOfRingEquiv e w)
        (Completion.ringEquivOfRingEquiv e w z) =
      completionNormalizedAbsValue w z :=
  completionNormalizedAbsValue_congr _ z

/-- At a real place, `Completion.ringEquivOfRingEquiv` commutes with `extensionEmbeddingOfIsReal`.
-/
@[simp]
theorem Completion.extensionEmbeddingOfIsReal_ringEquivOfRingEquiv (e : K ≃+* L)
    {w : InfinitePlace K} (hw : (equivOfRingEquiv e w).IsReal) (z : w.Completion) :
    Completion.extensionEmbeddingOfIsReal hw (Completion.ringEquivOfRingEquiv e w z) =
      Completion.extensionEmbeddingOfIsReal ((isReal_equivOfRingEquiv_iff e w).mp hw) z :=
  Completion.extensionEmbeddingOfIsReal_congr _ hw z

/-- `Completion.ringEquivOfRingEquiv` commutes with `Completion.ofReal`. -/
@[simp]
theorem Completion.ringEquivOfRingEquiv_ofReal (e : K ≃+* L) (w : InfinitePlace K) (r : ℝ) :
    Completion.ringEquivOfRingEquiv e w (Completion.ofReal w r) =
      Completion.ofReal (equivOfRingEquiv e w) r :=
  Completion.congr_ofReal _ r

/-- `Completion.ringEquivOfRingEquiv` commutes with `completionNormSection`. -/
@[simp]
theorem units_map_ringEquivOfRingEquiv_completionNormSection (e : K ≃+* L) (w : InfinitePlace K)
    (t : ℝ≥0ˣ) :
    Units.map (Completion.ringEquivOfRingEquiv e w :
        w.Completion →* (equivOfRingEquiv e w).Completion) (completionNormSection w t) =
      completionNormSection (equivOfRingEquiv e w) t :=
  units_map_congr_completionNormSection _ t

end EquivOfRingEquiv

end NumberField.InfinitePlace
