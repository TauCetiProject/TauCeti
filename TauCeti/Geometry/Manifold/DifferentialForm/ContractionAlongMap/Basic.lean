/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.ContractionAlongMap
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Interior

/-!
# Contraction of differential forms along a map

Let `p : M → N` be a map between manifolds (possibly with boundary or corners) and
`V : (x : M) → TangentSpace I' (p x)` be a section of the pulled-back tangent bundle `p^* TN`,
which need not factor through a vector field on `N`. For a fixed-coefficient differential
`(k + 1)`-form `ω : RoughForm I' N F (k + 1)` with values in a real normed space `F`, its
*contraction along `(p, V)`* (`TauCeti.mcontractionAlongMap`) inserts `V x` into the first slot of
`ω (p x)` via `ContinuousAlternatingMap.curryLeft` and pulls the remaining `k` slots back along
`mfderiv I I' p x`:

`C_(p, V)(ω)_x (v₁, …, vₖ) = ω (p x) (V x, dpₓ v₁, …, dpₓ vₖ)`.

Differentiating or integrating a pulled-back form `p_t^* ω` along a moving family of maps
`P : M × T → N` whose slices `p_t x = P (x, t)` are not invertible (for example, a homotopy or a
non-immersive deformation) naturally produces a contraction along `(p_t, ∂_t P)` whose velocity
section `∂_t P` lies in `p_t^* TN` and generally does not descend to a vector field on `N`. This
module develops the general contraction operator along `(p, V)` that feeds family contraction in
`TauCeti.Geometry.Manifold.DifferentialForm.ContractionAlongMap.Family`, Cartan's variation formula
in `TauCeti.Geometry.Manifold.DifferentialForm.ContractionAlongMap.MovingPullback`, and the
moving-pullback homotopy operator in
`TauCeti.Geometry.Manifold.DifferentialForm.ContractionAlongMap.Homotopy`.

The relative counterpart `TauCeti.mcontractionAlongMapWithin` uses `mfderivWithin I I' p s x` so
that regularity and chain-rule statements hold on subsets with unique derivatives, including
boundary and corner domains.

## Main declarations

* `TauCeti.mcontractionAlongMapWithin`, `TauCeti.mcontractionAlongMap`: contraction of a rough
  `(k + 1)`-form along `(p, V)` within a set and on the whole manifold.
* `TauCeti.mcontractionAlongMap_id`, `TauCeti.mcontractionAlongMap_comp_field`: for `p = id`,
  `C_(id, V) ω` is `RoughForm.interior V ω`; when `V = Y ∘ p` comes from a field `Y` on `N`,
  `C_(p, Y ∘ p) ω = p^* (ω.interior Y)`.
* `TauCeti.mcontractionAlongMap_comp_right`, `TauCeti.mcontractionAlongMap_mpullback`: source
  naturality `C_(p ∘ h, V ∘ h) ω = h^* (C_(p, V) ω)` and target naturality
  `C_(p, V)(q^* η) = C_(q ∘ p, dq ∘ V) η`, which together recover `TauCeti.mpullback_interior` for
  related fields.
* `TauCeti.mpullback_subtype_val_mcontractionAlongMap`,
  `TauCeti.mpullback_inclusion_mcontractionAlongMap`,
  `TauCeti.mcontractionAlongMap_mpullback_subtype_val`,
  `TauCeti.mcontractionAlongMap_mpullback_inclusion`: source and target restriction to open
  submanifolds.
* `TauCeti.mcontractionAlongMap_wedgeWith_apply`,
  `TauCeti.mcontractionAlongMap_wedgeWith_zero_right`,
  `TauCeti.mcontractionAlongMap_wedgeWith_zero_left` (and their `Within` and real-valued `wedge`
  counterparts): the graded antiderivation law for paired and real wedges across all positive-sum
  degree pairs, specializing at `p = id` to `TauCeti.RoughForm.interior_wedgeWith_apply`.
* `ContMDiffWithinAt.mcontractionAlongMapWithin`, `ContMDiffAt.mcontractionAlongMap_family`,
  `TauCeti.IsSmoothForm.mcontractionAlongMap`, `TauCeti.SmoothForm.mcontractionAlongMap`: `C^m`
  regularity, joint smoothness in parameters, and the bundled `ℝ`-linear map on `SmoothForm`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapters 14 and 17.
-/

public section

noncomputable section

open Bundle Set Filter TopologicalSpace ContinuousAlternatingMap
open scoped Manifold Topology

namespace TauCeti

variable {E H M E' H' N E'' H'' L F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace N] [ChartedSpace H' N] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  [TopologicalSpace L] [ChartedSpace H'' L] {I'' : ModelWithCorners ℝ E'' H''}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ}

/-! ### Definitions and basic properties -/

/-- **Contraction along a map within a set.** Insert the tangent vector `V x` along `p : M → N`
into the first slot of `ω (p x)` by `ContinuousAlternatingMap.curryLeft`, and pull the remaining
`k` slots back along `mfderivWithin I I' p s x`. -/
def mcontractionAlongMapWithin (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (p : M → N) (V : (x : M) → TangentSpace I' (p x)) (s : Set M)
    (ω : RoughForm I' N F (k + 1)) : RoughForm I M F k :=
  fun x ↦ (ContinuousAlternatingMap.curryLeft (E := E') (ω (p x)) (V x)).compContinuousLinearMap
    (mfderivWithin I I' p s x)

/-- **Contraction along a map.** Insert the tangent vector `V x` along `p : M → N` into the first
slot of `ω (p x)` by `ContinuousAlternatingMap.curryLeft`, and pull the remaining `k` slots back
along `mfderiv I I' p x`. -/
def mcontractionAlongMap (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (ω : RoughForm I' N F (k + 1)) : RoughForm I M F k :=
  fun x ↦ (ContinuousAlternatingMap.curryLeft (E := E') (ω (p x)) (V x)).compContinuousLinearMap
    (mfderiv I I' p x)

theorem mcontractionAlongMapWithin_def (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (s : Set M) (ω : RoughForm I' N F (k + 1)) (x : M) :
    mcontractionAlongMapWithin I I' p V s ω x =
      (ContinuousAlternatingMap.curryLeft (E := E') (ω (p x)) (V x)).compContinuousLinearMap
        (mfderivWithin I I' p s x) :=
  (rfl)

theorem mcontractionAlongMap_def (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (ω : RoughForm I' N F (k + 1)) (x : M) :
    mcontractionAlongMap I I' p V ω x =
      (ContinuousAlternatingMap.curryLeft (E := E') (ω (p x)) (V x)).compContinuousLinearMap
        (mfderiv I I' p x) :=
  (rfl)

@[simp]
theorem mcontractionAlongMapWithin_apply (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (s : Set M) (ω : RoughForm I' N F (k + 1)) (x : M) (v : Fin k → TangentSpace I x) :
    mcontractionAlongMapWithin I I' p V s ω x v =
      ω (p x) (Matrix.vecCons (V x) fun i ↦ mfderivWithin I I' p s x (v i)) :=
  (rfl)

@[simp]
theorem mcontractionAlongMap_apply (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (ω : RoughForm I' N F (k + 1)) (x : M) (v : Fin k → TangentSpace I x) :
    mcontractionAlongMap I I' p V ω x v =
      ω (p x) (Matrix.vecCons (V x) fun i ↦ mfderiv I I' p x (v i)) :=
  (rfl)

@[simp]
theorem mcontractionAlongMapWithin_univ (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMapWithin I I' p V univ ω = mcontractionAlongMap I I' p V ω := by
  ext x v
  simp

theorem mcontractionAlongMapWithin_eq_mcontractionAlongMap {p : M → N}
    {V : (x : M) → TangentSpace I' (p x)} {s : Set M} {x : M}
    (hs : UniqueMDiffWithinAt I s x) (hp : MDifferentiableAt I I' p x)
    (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMapWithin I I' p V s ω x = mcontractionAlongMap I I' p V ω x := by
  ext v
  simp [mfderivWithin_eq_mfderiv hs hp]

theorem mcontractionAlongMapWithin_of_isOpen {p : M → N} {V : (x : M) → TangentSpace I' (p x)}
    {s : Set M} (hs : IsOpen s) {x : M} (hx : x ∈ s) (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMapWithin I I' p V s ω x = mcontractionAlongMap I I' p V ω x := by
  ext v
  simp [mfderivWithin_of_isOpen hs hx]

theorem mcontractionAlongMapWithin_congr_field_at {p : M → N}
    {V W : (x : M) → TangentSpace I' (p x)} (s : Set M) (ω : RoughForm I' N F (k + 1))
    {x : M} (hVW : V x = W x) :
    mcontractionAlongMapWithin I I' p V s ω x = mcontractionAlongMapWithin I I' p W s ω x := by
  ext v
  simp [hVW]

theorem mcontractionAlongMap_congr_field_at {p : M → N}
    {V W : (x : M) → TangentSpace I' (p x)} (ω : RoughForm I' N F (k + 1))
    {x : M} (hVW : V x = W x) :
    mcontractionAlongMap I I' p V ω x = mcontractionAlongMap I I' p W ω x := by
  ext v
  simp [hVW]

/-- On normed model spaces, `mcontractionAlongMapWithin` is the flat-space
`TauCeti.contractionAlongMapWithin`. -/
theorem mcontractionAlongMapWithin_modelSpace (p : E → E') (V : E → E') (s : Set E)
    (ω : RoughForm 𝓘(ℝ, E') E' F (k + 1)) :
    mcontractionAlongMapWithin 𝓘(ℝ, E) 𝓘(ℝ, E') p V s ω =
      contractionAlongMapWithin p V ω s := by
  ext x v
  refine (mcontractionAlongMapWithin_apply p V s ω x v).trans
    (Eq.trans ?_ (contractionAlongMapWithin_apply p V ω s x v).symm)
  rw [mfderivWithin_eq_fderivWithin]
  rfl

/-- On normed model spaces, `mcontractionAlongMap` is the flat-space
`TauCeti.contractionAlongMap`. -/
theorem mcontractionAlongMap_modelSpace (p : E → E') (V : E → E')
    (ω : RoughForm 𝓘(ℝ, E') E' F (k + 1)) :
    mcontractionAlongMap 𝓘(ℝ, E) 𝓘(ℝ, E') p V ω = contractionAlongMap p V ω := by
  ext x v
  refine (mcontractionAlongMap_apply p V ω x v).trans
    (Eq.trans ?_ (contractionAlongMap_apply p V ω x v).symm)
  rw [mfderiv_eq_fderiv]
  rfl

/-! ### Linearity in the vector field and the form -/

@[simp]
theorem mcontractionAlongMapWithin_zero_field (p : M → N) (s : Set M)
    (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMapWithin I I' p 0 s ω = 0 := by
  ext x v
  rw [mcontractionAlongMapWithin_apply]
  exact (ω (p x)).map_coord_zero 0 (by simp)

@[simp]
theorem mcontractionAlongMap_zero_field (p : M → N) (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMap I I' p 0 ω = 0 := by
  rw [← mcontractionAlongMapWithin_univ, mcontractionAlongMapWithin_zero_field]

@[simp]
theorem mcontractionAlongMapWithin_zero (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (s : Set M) :
    mcontractionAlongMapWithin I I' p V s (0 : RoughForm I' N F (k + 1)) = 0 := by
  ext x v
  simp

@[simp]
theorem mcontractionAlongMap_zero (p : M → N) (V : (x : M) → TangentSpace I' (p x)) :
    mcontractionAlongMap I I' p V (0 : RoughForm I' N F (k + 1)) = 0 := by
  rw [← mcontractionAlongMapWithin_univ, mcontractionAlongMapWithin_zero]

@[simp]
theorem mcontractionAlongMapWithin_add_field (p : M → N)
    (V W : (x : M) → TangentSpace I' (p x)) (s : Set M) (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMapWithin I I' p (V + W) s ω =
      mcontractionAlongMapWithin I I' p V s ω + mcontractionAlongMapWithin I I' p W s ω := by
  ext x v
  simp only [mcontractionAlongMapWithin_apply, Pi.add_apply, ContinuousAlternatingMap.add_apply]
  exact (ω (p x)).toAlternatingMap.map_vecCons_add _ (V x) (W x)

@[simp]
theorem mcontractionAlongMap_add_field (p : M → N) (V W : (x : M) → TangentSpace I' (p x))
    (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMap I I' p (V + W) ω =
      mcontractionAlongMap I I' p V ω + mcontractionAlongMap I I' p W ω := by
  simpa only [mcontractionAlongMapWithin_univ] using
    mcontractionAlongMapWithin_add_field (I := I) (I' := I') p V W univ ω

@[simp]
theorem mcontractionAlongMapWithin_smul_field (p : M → N) (a : M → ℝ)
    (V : (x : M) → TangentSpace I' (p x)) (s : Set M) (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMapWithin I I' p (fun x ↦ a x • V x) s ω =
      fun x ↦ a x • mcontractionAlongMapWithin I I' p V s ω x := by
  ext x v
  simp only [mcontractionAlongMapWithin_apply, ContinuousAlternatingMap.smul_apply]
  exact (ω (p x)).toAlternatingMap.map_vecCons_smul _ (a x) (V x)

@[simp]
theorem mcontractionAlongMap_smul_field (p : M → N) (a : M → ℝ)
    (V : (x : M) → TangentSpace I' (p x)) (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMap I I' p (fun x ↦ a x • V x) ω =
      fun x ↦ a x • mcontractionAlongMap I I' p V ω x := by
  simpa only [mcontractionAlongMapWithin_univ] using
    mcontractionAlongMapWithin_smul_field (I := I) (I' := I') p a V univ ω

@[simp]
theorem mcontractionAlongMapWithin_neg_field (p : M → N)
    (V : (x : M) → TangentSpace I' (p x)) (s : Set M) (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMapWithin I I' p (-V) s ω = -mcontractionAlongMapWithin I I' p V s ω := by
  ext x v
  simp only [mcontractionAlongMapWithin_apply, Pi.neg_apply, ContinuousAlternatingMap.neg_apply]
  rw [← neg_one_smul ℝ (V x)]
  exact ((ω (p x)).toAlternatingMap.map_vecCons_smul _ (-1 : ℝ) (V x)).trans (neg_one_smul ℝ _)

@[simp]
theorem mcontractionAlongMap_neg_field (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMap I I' p (-V) ω = -mcontractionAlongMap I I' p V ω := by
  simpa only [mcontractionAlongMapWithin_univ] using
    mcontractionAlongMapWithin_neg_field (I := I) (I' := I') p V univ ω

@[simp]
theorem mcontractionAlongMapWithin_sub_field (p : M → N)
    (V W : (x : M) → TangentSpace I' (p x)) (s : Set M) (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMapWithin I I' p (V - W) s ω =
      mcontractionAlongMapWithin I I' p V s ω - mcontractionAlongMapWithin I I' p W s ω := by
  rw [sub_eq_add_neg, mcontractionAlongMapWithin_add_field, mcontractionAlongMapWithin_neg_field,
    sub_eq_add_neg]

@[simp]
theorem mcontractionAlongMap_sub_field (p : M → N) (V W : (x : M) → TangentSpace I' (p x))
    (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMap I I' p (V - W) ω =
      mcontractionAlongMap I I' p V ω - mcontractionAlongMap I I' p W ω := by
  rw [sub_eq_add_neg, mcontractionAlongMap_add_field, mcontractionAlongMap_neg_field,
    sub_eq_add_neg]

@[simp]
theorem mcontractionAlongMapWithin_add (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (s : Set M) (ω η : RoughForm I' N F (k + 1)) :
    mcontractionAlongMapWithin I I' p V s (ω + η) =
      mcontractionAlongMapWithin I I' p V s ω + mcontractionAlongMapWithin I I' p V s η := by
  ext x v
  simp

@[simp]
theorem mcontractionAlongMap_add (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (ω η : RoughForm I' N F (k + 1)) :
    mcontractionAlongMap I I' p V (ω + η) =
      mcontractionAlongMap I I' p V ω + mcontractionAlongMap I I' p V η := by
  simpa only [mcontractionAlongMapWithin_univ] using
    mcontractionAlongMapWithin_add (I := I) (I' := I') p V univ ω η

@[simp]
theorem mcontractionAlongMapWithin_smul (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (s : Set M) (c : ℝ) (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMapWithin I I' p V s (c • ω) =
      c • mcontractionAlongMapWithin I I' p V s ω := by
  ext x v
  simp

@[simp]
theorem mcontractionAlongMap_smul (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (c : ℝ) (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMap I I' p V (c • ω) = c • mcontractionAlongMap I I' p V ω := by
  simpa only [mcontractionAlongMapWithin_univ] using
    mcontractionAlongMapWithin_smul (I := I) (I' := I') p V univ c ω

@[simp]
theorem mcontractionAlongMapWithin_neg (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (s : Set M) (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMapWithin I I' p V s (-ω) = -mcontractionAlongMapWithin I I' p V s ω := by
  ext x v
  simp

@[simp]
theorem mcontractionAlongMap_neg (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMap I I' p V (-ω) = -mcontractionAlongMap I I' p V ω := by
  simpa only [mcontractionAlongMapWithin_univ] using
    mcontractionAlongMapWithin_neg (I := I) (I' := I') p V univ ω

@[simp]
theorem mcontractionAlongMapWithin_sub (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (s : Set M) (ω η : RoughForm I' N F (k + 1)) :
    mcontractionAlongMapWithin I I' p V s (ω - η) =
      mcontractionAlongMapWithin I I' p V s ω - mcontractionAlongMapWithin I I' p V s η := by
  ext x v
  simp

@[simp]
theorem mcontractionAlongMap_sub (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (ω η : RoughForm I' N F (k + 1)) :
    mcontractionAlongMap I I' p V (ω - η) =
      mcontractionAlongMap I I' p V ω - mcontractionAlongMap I I' p V η := by
  simpa only [mcontractionAlongMapWithin_univ] using
    mcontractionAlongMapWithin_sub (I := I) (I' := I') p V univ ω η

/-! ### Specializations to interior product and naturality -/

/-- **Identity specialization.** Contracting along the identity map `id : M → M` is the interior
product `RoughForm.interior`. -/
@[simp]
theorem mcontractionAlongMap_id (V : (x : M) → TangentSpace I x) (ω : RoughForm I M F (k + 1)) :
    mcontractionAlongMap I I id V ω = ω.interior V := by
  ext x v
  simp only [mcontractionAlongMap_apply, RoughForm.interior_apply, mfderiv_id,
    ContinuousLinearMap.id_apply]
  rfl

/-- When the section along `p` comes from a vector field `Y` on `N`, contracting along `(p, Y ∘ p)`
is pulling back `ω.interior Y` along `p`. -/
theorem mcontractionAlongMapWithin_comp_field (p : M → N) (Y : (y : N) → TangentSpace I' y)
    (s : Set M) (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMapWithin I I' p (fun x ↦ Y (p x)) s ω =
      mpullbackWithin I I' p s (ω.interior Y) := by
  ext x v
  simp [mcontractionAlongMapWithin_apply, mpullbackWithin_apply, RoughForm.interior_apply]

/-- When the section along `p` comes from a vector field `Y` on `N`, contracting along `(p, Y ∘ p)`
is pulling back `ω.interior Y` along `p`. -/
theorem mcontractionAlongMap_comp_field (p : M → N) (Y : (y : N) → TangentSpace I' y)
    (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMap I I' p (fun x ↦ Y (p x)) ω = mpullback I I' p (ω.interior Y) := by
  ext x v
  simp [mcontractionAlongMap_apply, mpullback_apply, RoughForm.interior_apply]

/-- **Source naturality within sets (pointwise).** Precomposing `(p, V)` with `h : L → M` pulls
the contraction back along `h`. -/
theorem mcontractionAlongMapWithin_comp_right_at {h : L → M} {p : M → N}
    {V : (x : M) → TangentSpace I' (p x)} {ω : RoughForm I' N F (k + 1)}
    {s : Set L} {t : Set M} {z : L}
    (hh : MDifferentiableWithinAt I'' I h s z) (hp : MDifferentiableWithinAt I I' p t (h z))
    (hst : MapsTo h s t) (hs : UniqueMDiffWithinAt I'' s z) :
    mcontractionAlongMapWithin I'' I' (p ∘ h) (fun y ↦ V (h y)) s ω z =
      mpullbackWithin I'' I h s (mcontractionAlongMapWithin I I' p V t ω) z := by
  have hchain : mfderivWithin I'' I' (p ∘ h) s z =
      (mfderivWithin I I' p t (h z)).comp (mfderivWithin I'' I h s z) :=
    mfderivWithin_comp z hp hh hst hs
  ext v
  simp only [mcontractionAlongMapWithin_apply, mpullbackWithin_apply, hchain,
    ContinuousLinearMap.comp_apply, Function.comp_apply]

/-- **Source naturality (pointwise).** Precomposing `(p, V)` with `h : L → M` pulls the contraction
back along `h`: `C_(p ∘ h, V ∘ h) ω = h^* (C_(p, V) ω)`. -/
theorem mcontractionAlongMap_comp_right_at {h : L → M} {p : M → N}
    {V : (x : M) → TangentSpace I' (p x)} {ω : RoughForm I' N F (k + 1)} {z : L}
    (hh : MDifferentiableAt I'' I h z) (hp : MDifferentiableAt I I' p (h z)) :
    mcontractionAlongMap I'' I' (p ∘ h) (fun y ↦ V (h y)) ω z =
      mpullback I'' I h (mcontractionAlongMap I I' p V ω) z := by
  simpa only [mcontractionAlongMapWithin_univ, mpullbackWithin_univ] using
    mcontractionAlongMapWithin_comp_right_at (s := univ) (t := univ) (V := V) (ω := ω)
      hh.mdifferentiableWithinAt hp.mdifferentiableWithinAt (mapsTo_univ _ _)
      (uniqueMDiffWithinAt_univ I'')

/-- **Source naturality.** If `h : L → M` and `p : M → N` are differentiable, then
`C_(p ∘ h, V ∘ h) ω = h^* (C_(p, V) ω)`. -/
theorem mcontractionAlongMap_comp_right {h : L → M} {p : M → N}
    (V : (x : M) → TangentSpace I' (p x)) (ω : RoughForm I' N F (k + 1))
    (hh : MDifferentiable I'' I h) (hp : MDifferentiable I I' p) :
    mcontractionAlongMap I'' I' (p ∘ h) (fun y ↦ V (h y)) ω =
      mpullback I'' I h (mcontractionAlongMap I I' p V ω) :=
  funext fun z ↦ mcontractionAlongMap_comp_right_at (hh z) (hp (h z))

section TargetNaturality

variable {E''' H''' Q : Type*} [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H'''] [TopologicalSpace Q] [ChartedSpace H''' Q]
  {I''' : ModelWithCorners ℝ E''' H'''}

/-- **Target naturality within sets (pointwise).** Contracting a pulled-back form `q^* η` along
`(p, V)` is contracting `η` along `(q ∘ p, dq ∘ V)`. -/
theorem mcontractionAlongMapWithin_mpullbackWithin_at {p : M → N} {q : N → Q}
    {V : (x : M) → TangentSpace I' (p x)} {η : RoughForm I''' Q F (k + 1)}
    {s : Set M} {t : Set N} {x : M}
    (hp : MDifferentiableWithinAt I I' p s x) (hq : MDifferentiableWithinAt I' I''' q t (p x))
    (hst : MapsTo p s t) (hs : UniqueMDiffWithinAt I s x) :
    mcontractionAlongMapWithin I I' p V s (mpullbackWithin I' I''' q t η) x =
      mcontractionAlongMapWithin I I''' (q ∘ p)
        (fun y ↦ mfderivWithin I' I''' q t (p y) (V y)) s η x := by
  have hchain : mfderivWithin I I''' (q ∘ p) s x =
      (mfderivWithin I' I''' q t (p x)).comp (mfderivWithin I I' p s x) :=
    mfderivWithin_comp x hq hp hst hs
  ext v
  simp only [mcontractionAlongMapWithin_apply, mpullbackWithin_apply, hchain,
    ContinuousLinearMap.comp_apply, Function.comp_apply]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

/-- **Target naturality (pointwise).** Contracting a pulled-back form `q^* η` along `(p, V)` is
contracting `η` along `(q ∘ p, dq ∘ V)`: `C_(p, V)(q^* η) = C_(q ∘ p, dq ∘ V) η`. -/
theorem mcontractionAlongMap_mpullback_at {p : M → N} {q : N → Q}
    {V : (x : M) → TangentSpace I' (p x)} {η : RoughForm I''' Q F (k + 1)} {x : M}
    (hp : MDifferentiableAt I I' p x) (hq : MDifferentiableAt I' I''' q (p x)) :
    mcontractionAlongMap I I' p V (mpullback I' I''' q η) x =
      mcontractionAlongMap I I''' (q ∘ p) (fun y ↦ mfderiv I' I''' q (p y) (V y)) η x := by
  simpa only [mcontractionAlongMapWithin_univ, mpullbackWithin_univ, mfderivWithin_univ] using
    mcontractionAlongMapWithin_mpullbackWithin_at (s := univ) (t := univ) (V := V) (η := η)
      hp.mdifferentiableWithinAt hq.mdifferentiableWithinAt (mapsTo_univ _ _)
      (uniqueMDiffWithinAt_univ I)

/-- **Target naturality.** If `p : M → N` and `q : N → Q` are differentiable, then
`C_(p, V)(q^* η) = C_(q ∘ p, dq ∘ V) η`. -/
theorem mcontractionAlongMap_mpullback {p : M → N} {q : N → Q}
    (V : (x : M) → TangentSpace I' (p x)) (η : RoughForm I''' Q F (k + 1))
    (hp : MDifferentiable I I' p) (hq : MDifferentiable I' I''' q) :
    mcontractionAlongMap I I' p V (mpullback I' I''' q η) =
      mcontractionAlongMap I I''' (q ∘ p) (fun y ↦ mfderiv I' I''' q (p y) (V y)) η :=
  funext fun x ↦ mcontractionAlongMap_mpullback_at (hp x) (hq (p x))

end TargetNaturality

/-! ### Open restriction -/

/-- Restricting `mcontractionAlongMap` to an open submanifold `U : Opens M` along `Subtype.val`
contracts along `p ∘ Subtype.val` and `V ∘ Subtype.val`, with no regularity hypothesis. -/
@[simp]
theorem mpullback_subtype_val_mcontractionAlongMap (U : Opens M) (p : M → N)
    (V : (x : M) → TangentSpace I' (p x)) (ω : RoughForm I' N F (k + 1)) :
    mpullback I I (Subtype.val : U → M) (mcontractionAlongMap I I' p V ω) =
      mcontractionAlongMap I I' (p ∘ (Subtype.val : U → M)) (fun x : U ↦ V x) ω := by
  ext x v
  rw [mpullback_apply, mcontractionAlongMap_apply]
  refine Eq.trans ?_
    (mcontractionAlongMap_apply (I := I) (I' := I') (p ∘ (Subtype.val : U → M))
      (fun x : U ↦ V x) ω x v).symm
  refine congrArg (ω (p x)) (funext fun i ↦ ?_)
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [Matrix.cons_val_succ, Manifold.mfderiv_comp_subtype_val_apply,
      Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      Manifold.tangentSpaceOpenEquiv_apply]

/-- Restricting `mcontractionAlongMap` along the inclusion `Opens.inclusion h` of nested open
subsets `U ≤ W` contracts along `p ∘ Opens.inclusion h`, with no regularity hypothesis. -/
@[simp]
theorem mpullback_inclusion_mcontractionAlongMap {U W : Opens M} (h : U ≤ W) (p : W → N)
    (V : (x : W) → TangentSpace I' (p x)) (ω : RoughForm I' N F (k + 1)) :
    mpullback I I (Opens.inclusion h) (mcontractionAlongMap I I' p V ω) =
      mcontractionAlongMap I I' (p ∘ Opens.inclusion h)
        (fun x : U ↦ V (Opens.inclusion h x)) ω := by
  ext x v
  classical
  let p' : M → N := fun y ↦ if hy : y ∈ W then p ⟨y, hy⟩ else p (Opens.inclusion h x)
  have hpW : p' ∘ (Subtype.val : W → M) = p := funext fun y ↦ dite_eq_left y.property
  have hpU : p' ∘ (Subtype.val : U → M) = p ∘ Opens.inclusion h :=
    funext fun y ↦ dite_eq_left (h y.property)
  rw [mpullback_inclusion_apply, mcontractionAlongMap_apply]
  refine Eq.trans ?_
    (mcontractionAlongMap_apply (I := I) (I' := I') (p ∘ Opens.inclusion h)
      (fun x : U ↦ V (Opens.inclusion h x)) ω x v).symm
  refine congrArg (ω (p (Opens.inclusion h x))) (funext fun i ↦ ?_)
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    have h1 : mfderiv I I' p (Opens.inclusion h x) (v i) =
        mfderiv I I' p' (x : M) (v i) := by
      rw [← hpW]
      exact Manifold.mfderiv_comp_subtype_val_apply (J := I) (I := I') (U := W) (f := p')
        (x := Opens.inclusion h x) (v i)
    have h2 : mfderiv I I' (p ∘ Opens.inclusion h) x (v i) =
        mfderiv I I' p' (x : M) (v i) := by
      rw [← hpU]
      exact Manifold.mfderiv_comp_subtype_val_apply (J := I) (I := I') (U := U) (f := p')
        (x := x) (v i)
    exact h1.trans h2.symm

/-- Contracting a form restricted to an open target `U' : Opens N` along `p : M → U'` agrees with
contracting the ambient form along `Subtype.val ∘ p`, with no regularity hypothesis. -/
@[simp]
theorem mcontractionAlongMap_mpullback_subtype_val (U' : Opens N) (p : M → U')
    (V : (x : M) → TangentSpace I' (p x)) (ω : RoughForm I' N F (k + 1)) :
    mcontractionAlongMap I I' p V (mpullback I' I' (Subtype.val : U' → N) ω) =
      mcontractionAlongMap I I' ((Subtype.val : U' → N) ∘ p) (fun x ↦ V x) ω := by
  ext x v
  rw [mcontractionAlongMap_apply, mpullback_apply]
  refine Eq.trans ?_
    (mcontractionAlongMap_apply (I := I) (I' := I') ((Subtype.val : U' → N) ∘ p)
      (fun x ↦ V x) ω x v).symm
  refine congrArg (ω (p x)) (funext fun i ↦ ?_)
  cases i using Fin.cases with
  | zero =>
    simp only [Matrix.cons_val_zero, Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      Manifold.tangentSpaceOpenEquiv_apply]
    rfl
  | succ i =>
    simp only [Matrix.cons_val_succ, Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      Manifold.tangentSpaceOpenEquiv_apply, Manifold.mfderiv_subtype_val_comp_apply]
    rfl

/-- Contracting a form restricted along `Opens.inclusion h` for nested open target subsets
`U' ≤ W'` along `p : M → U'` agrees with contracting along `Opens.inclusion h ∘ p`, with no
regularity hypothesis. -/
@[simp]
theorem mcontractionAlongMap_mpullback_inclusion {U' W' : Opens N} (h : U' ≤ W') (p : M → U')
    (V : (x : M) → TangentSpace I' (p x)) (ω : RoughForm I' W' F (k + 1)) :
    mcontractionAlongMap I I' p V (mpullback I' I' (Opens.inclusion h) ω) =
      mcontractionAlongMap I I' (Opens.inclusion h ∘ p) (fun x ↦ V x) ω := by
  ext x v
  rw [mcontractionAlongMap_apply, mpullback_inclusion_apply]
  refine Eq.trans ?_
    (mcontractionAlongMap_apply (I := I) (I' := I') (Opens.inclusion h ∘ p)
      (fun x ↦ V x) ω x v).symm
  refine congrArg (ω (Opens.inclusion h (p x))) (funext fun i ↦ ?_)
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [Matrix.cons_val_succ]
    have h1 := Manifold.mfderiv_subtype_val_comp_apply (J := I) (I := I') (U := U') (f := p)
      (x := x) (v i)
    have h2 := Manifold.mfderiv_subtype_val_comp_apply (J := I) (I := I') (U := W')
      (f := Opens.inclusion h ∘ p) (x := x) (v i)
    exact h1.symm.trans h2

/-! ### Antiderivation law for paired wedges -/

section Wedge

variable {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]

/-- **Paired-wedge antiderivation within a set (both degrees positive).** For `φ` of degree `k + 1`
and `ψ` of degree `l + 1`, contraction along `(p, V)` satisfies
`C_(p, V)(φ ∧_μ ψ) = C_(p, V) φ ∧_μ p^* ψ + (-1)^(k + 1) • (p^* φ ∧_μ C_(p, V) ψ)`. -/
theorem mcontractionAlongMapWithin_wedgeWith_apply {l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (p : M → N) (V : (x : M) → TangentSpace I' (p x)) (s : Set M)
    (φ : RoughForm I' N F₁ (k + 1)) (ψ : RoughForm I' N F₂ (l + 1))
    (x : M) (v : Fin (k + 1 + l) → TangentSpace I x) :
    mcontractionAlongMapWithin (k := k + 1 + l) I I' p V s (φ.wedgeWith μ ψ) x v =
      (mcontractionAlongMapWithin I I' p V s φ).wedgeWith μ (mpullbackWithin I I' p s ψ) x
          (v ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) •
          (mpullbackWithin I I' p s φ).wedgeWith μ
            (mcontractionAlongMapWithin I I' p V s ψ) x v := by
  have h := ContinuousAlternatingMap.curryLeftTopological_pairedWedge
    (E := TangentSpace I' (p x)) μ μ.continuous₂ (φ (p x)) (ψ (p x)) (V x)
    (fun i ↦ mfderivWithin I I' p s x (v i))
  have h1 : mcontractionAlongMapWithin I I' p V s φ x =
      ((φ (p x)).curryLeftTopological (V x)).compContinuousLinearMap
        (mfderivWithin I I' p s x) := by
    ext w
    simp [mcontractionAlongMapWithin_apply,
      ContinuousAlternatingMap.curryLeftTopological_apply_apply, Function.comp_def]
  have h2 : mcontractionAlongMapWithin I I' p V s ψ x =
      ((ψ (p x)).curryLeftTopological (V x)).compContinuousLinearMap
        (mfderivWithin I I' p s x) := by
    ext w
    simp [mcontractionAlongMapWithin_apply,
      ContinuousAlternatingMap.curryLeftTopological_apply_apply, Function.comp_def]
  have hp1 : mpullbackWithin I I' p s φ x =
      (φ (p x)).compContinuousLinearMap (mfderivWithin I I' p s x) := by
    ext w
    simp [mpullbackWithin_apply, Function.comp_def]
  have hp2 : mpullbackWithin I I' p s ψ x =
      (ψ (p x)).compContinuousLinearMap (mfderivWithin I I' p s x) := by
    ext w
    simp [mpullbackWithin_apply, Function.comp_def]
  rw [mcontractionAlongMapWithin_apply, RoughForm.wedgeWith_apply', RoughForm.wedgeWith_apply',
    RoughForm.wedgeWith_apply', h1, h2, hp1, hp2,
    ← ContinuousAlternatingMap.pairedWedge_compContinuousLinearMap,
    ← ContinuousAlternatingMap.pairedWedge_compContinuousLinearMap]
  simpa only [ContinuousAlternatingMap.curryLeftTopological_apply_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def] using h

/-- **Paired-wedge antiderivation (both degrees positive).** At `p = id` this specializes to
`TauCeti.RoughForm.interior_wedgeWith_apply`. -/
theorem mcontractionAlongMap_wedgeWith_apply {l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (φ : RoughForm I' N F₁ (k + 1)) (ψ : RoughForm I' N F₂ (l + 1))
    (x : M) (v : Fin (k + 1 + l) → TangentSpace I x) :
    mcontractionAlongMap (k := k + 1 + l) I I' p V (φ.wedgeWith μ ψ) x v =
      (mcontractionAlongMap I I' p V φ).wedgeWith μ (mpullback I I' p ψ) x
          (v ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) •
          (mpullback I I' p φ).wedgeWith μ (mcontractionAlongMap I I' p V ψ) x v := by
  simpa only [mcontractionAlongMapWithin_univ, mpullbackWithin_univ] using
    mcontractionAlongMapWithin_wedgeWith_apply (I := I) (I' := I') μ p V univ φ ψ x v

/-- **Real-valued wedge antiderivation within a set (both degrees positive).** -/
theorem mcontractionAlongMapWithin_wedge_apply {l : ℕ}
    (p : M → N) (V : (x : M) → TangentSpace I' (p x)) (s : Set M)
    (φ : RoughForm I' N ℝ (k + 1)) (ψ : RoughForm I' N ℝ (l + 1))
    (x : M) (v : Fin (k + 1 + l) → TangentSpace I x) :
    mcontractionAlongMapWithin (k := k + 1 + l) I I' p V s (φ.wedge ψ) x v =
      (mcontractionAlongMapWithin I I' p V s φ).wedge (mpullbackWithin I I' p s ψ) x
          (v ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) •
          (mpullbackWithin I I' p s φ).wedge
            (mcontractionAlongMapWithin I I' p V s ψ) x v := by
  simpa only [RoughForm.wedge_def] using
    mcontractionAlongMapWithin_wedgeWith_apply (I := I) (I' := I') (ContinuousLinearMap.mul ℝ ℝ)
      p V s φ ψ x v

/-- **Real-valued wedge antiderivation (both degrees positive).** -/
theorem mcontractionAlongMap_wedge_apply {l : ℕ}
    (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (φ : RoughForm I' N ℝ (k + 1)) (ψ : RoughForm I' N ℝ (l + 1))
    (x : M) (v : Fin (k + 1 + l) → TangentSpace I x) :
    mcontractionAlongMap (k := k + 1 + l) I I' p V (φ.wedge ψ) x v =
      (mcontractionAlongMap I I' p V φ).wedge (mpullback I I' p ψ) x
          (v ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) •
          (mpullback I I' p φ).wedge (mcontractionAlongMap I I' p V ψ) x v := by
  simpa only [RoughForm.wedge_def] using
    mcontractionAlongMap_wedgeWith_apply (I := I) (I' := I') (ContinuousLinearMap.mul ℝ ℝ)
      p V φ ψ x v

/-- **Paired-wedge law when the right factor has degree zero (within a set).** The zero-form
contraction term is omitted: `C_(p, V)(φ ∧_μ ψ) = C_(p, V) φ ∧_μ p^* ψ`. -/
@[simp]
theorem mcontractionAlongMapWithin_wedgeWith_zero_right (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (p : M → N) (V : (x : M) → TangentSpace I' (p x)) (s : Set M)
    (φ : RoughForm I' N F₁ (k + 1)) (ψ : RoughForm I' N F₂ 0) :
    mcontractionAlongMapWithin (k := k) I I' p V s (φ.wedgeWith μ ψ) =
      (mcontractionAlongMapWithin I I' p V s φ).wedgeWith μ (mpullbackWithin I I' p s ψ) := by
  ext x v
  rw [mcontractionAlongMapWithin_apply, RoughForm.wedgeWith_apply_zero_right,
    RoughForm.wedgeWith_apply_zero_right, mcontractionAlongMapWithin_apply, mpullbackWithin_apply]
  exact congrArg₂ (fun a b ↦ μ a b) rfl (congrArg (ψ (p x)) (Subsingleton.elim _ _))

/-- **Paired-wedge law when the right factor has degree zero:**
`C_(p, V)(φ ∧_μ ψ) = C_(p, V) φ ∧_μ p^* ψ`. -/
@[simp]
theorem mcontractionAlongMap_wedgeWith_zero_right (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (φ : RoughForm I' N F₁ (k + 1)) (ψ : RoughForm I' N F₂ 0) :
    mcontractionAlongMap (k := k) I I' p V (φ.wedgeWith μ ψ) =
      (mcontractionAlongMap I I' p V φ).wedgeWith μ (mpullback I I' p ψ) := by
  simpa only [mcontractionAlongMapWithin_univ, mpullbackWithin_univ] using
    mcontractionAlongMapWithin_wedgeWith_zero_right (I := I) (I' := I') μ p V univ φ ψ

/-- **Real-valued wedge law when the right factor has degree zero (within a set).** -/
@[simp]
theorem mcontractionAlongMapWithin_wedge_zero_right
    (p : M → N) (V : (x : M) → TangentSpace I' (p x)) (s : Set M)
    (φ : RoughForm I' N ℝ (k + 1)) (ψ : RoughForm I' N ℝ 0) :
    mcontractionAlongMapWithin (k := k) I I' p V s (φ.wedge ψ) =
      (mcontractionAlongMapWithin I I' p V s φ).wedge (mpullbackWithin I I' p s ψ) := by
  simpa only [RoughForm.wedge_def] using
    mcontractionAlongMapWithin_wedgeWith_zero_right (I := I) (I' := I')
      (ContinuousLinearMap.mul ℝ ℝ) p V s φ ψ

/-- **Real-valued wedge law when the right factor has degree zero.** -/
@[simp]
theorem mcontractionAlongMap_wedge_zero_right
    (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (φ : RoughForm I' N ℝ (k + 1)) (ψ : RoughForm I' N ℝ 0) :
    mcontractionAlongMap (k := k) I I' p V (φ.wedge ψ) =
      (mcontractionAlongMap I I' p V φ).wedge (mpullback I I' p ψ) := by
  simpa only [RoughForm.wedge_def] using
    mcontractionAlongMap_wedgeWith_zero_right (I := I) (I' := I')
      (ContinuousLinearMap.mul ℝ ℝ) p V φ ψ

/-- **Paired-wedge law when the left factor has degree zero (within a set).** The zero-form
contraction term is omitted and `(-1)^0 = 1`: `C_(p, V)(φ ∧_μ ψ) = p^* φ ∧_μ C_(p, V) ψ`. -/
@[simp]
theorem mcontractionAlongMapWithin_wedgeWith_zero_left {l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (p : M → N) (V : (x : M) → TangentSpace I' (p x)) (s : Set M)
    (φ : RoughForm I' N F₁ 0) (ψ : RoughForm I' N F₂ (l + 1)) :
    mcontractionAlongMapWithin (k := 0 + l) I I' p V s (φ.wedgeWith μ ψ) =
      (mpullbackWithin I I' p s φ).wedgeWith μ (mcontractionAlongMapWithin I I' p V s ψ) := by
  ext x v
  rw [mcontractionAlongMapWithin_apply, RoughForm.wedgeWith_apply', RoughForm.wedgeWith_apply',
    ContinuousAlternatingMap.pairedWedge_apply_zero_left,
    ContinuousAlternatingMap.pairedWedge_apply_zero_left,
    mpullbackWithin_apply, mcontractionAlongMapWithin_apply]
  refine congrArg₂ (fun a b ↦ μ a b) (congrArg (φ (p x)) (Subsingleton.elim _ _))
    (congrArg (ψ (p x)) (funext fun j ↦ ?_))
  cases j using Fin.cases <;> rfl

/-- **Paired-wedge law when the left factor has degree zero:**
`C_(p, V)(φ ∧_μ ψ) = p^* φ ∧_μ C_(p, V) ψ`. -/
@[simp]
theorem mcontractionAlongMap_wedgeWith_zero_left {l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (φ : RoughForm I' N F₁ 0) (ψ : RoughForm I' N F₂ (l + 1)) :
    mcontractionAlongMap (k := 0 + l) I I' p V (φ.wedgeWith μ ψ) =
      (mpullback I I' p φ).wedgeWith μ (mcontractionAlongMap I I' p V ψ) := by
  simpa only [mcontractionAlongMapWithin_univ, mpullbackWithin_univ] using
    mcontractionAlongMapWithin_wedgeWith_zero_left (I := I) (I' := I') μ p V univ φ ψ

/-- **Real-valued wedge law when the left factor has degree zero (within a set).** -/
@[simp]
theorem mcontractionAlongMapWithin_wedge_zero_left {l : ℕ}
    (p : M → N) (V : (x : M) → TangentSpace I' (p x)) (s : Set M)
    (φ : RoughForm I' N ℝ 0) (ψ : RoughForm I' N ℝ (l + 1)) :
    mcontractionAlongMapWithin (k := 0 + l) I I' p V s (φ.wedge ψ) =
      (mpullbackWithin I I' p s φ).wedge (mcontractionAlongMapWithin I I' p V s ψ) := by
  simpa only [RoughForm.wedge_def] using
    mcontractionAlongMapWithin_wedgeWith_zero_left (I := I) (I' := I')
      (ContinuousLinearMap.mul ℝ ℝ) p V s φ ψ

/-- **Real-valued wedge law when the left factor has degree zero.** -/
@[simp]
theorem mcontractionAlongMap_wedge_zero_left {l : ℕ}
    (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (φ : RoughForm I' N ℝ 0) (ψ : RoughForm I' N ℝ (l + 1)) :
    mcontractionAlongMap (k := 0 + l) I I' p V (φ.wedge ψ) =
      (mpullback I I' p φ).wedge (mcontractionAlongMap I I' p V ψ) := by
  simpa only [RoughForm.wedge_def] using
    mcontractionAlongMap_wedgeWith_zero_left (I := I) (I' := I')
      (ContinuousLinearMap.mul ℝ ℝ) p V φ ψ

end Wedge

/-! ### Fibre coordinates, regularity, and smooth families -/

section Smooth

variable [IsManifold I 1 M] [IsManifold I' 1 N]

/-- In fibre coordinates centred at `x₀ : M` and `y₀ : N`, `mcontractionAlongMapWithin` inserts the
tangent-bundle fibre coordinate of `V x` into the fibre coordinate of `ω (p x)` and precomposes
with the tangent coordinates of `mfderivWithin I I' p s x`. The target tangent trivialization at
`y₀` must be valid at `p x`. -/
theorem RoughForm.inCoordinates_mcontractionAlongMapWithin (ω : RoughForm I' N F (k + 1))
    (p : M → N) (V : (x : M) → TangentSpace I' (p x)) (s : Set M) (x₀ x : M) (y₀ : N)
    (hx : p x ∈ (trivializationAt E' (TangentSpace I') y₀).baseSet) :
    ContinuousAlternatingMap.inCoordinates E F x₀ x x₀ x
        (mcontractionAlongMapWithin I I' p V s ω x) =
      ((ContinuousAlternatingMap.inCoordinates E' F y₀ (p x) y₀ (p x)
        (ω (p x))).curryLeft
          ((trivializationAt E' (TangentSpace I') y₀ ⟨p x, V x⟩).2)).compContinuousLinearMap
        (ContinuousLinearMap.inCoordinates E (TangentSpace I) E' (TangentSpace I')
          x₀ x y₀ (p x) (mfderivWithin I I' p s x)) := by
  let c : TangentSpace I' (p x) [⋀^Fin k]→L[ℝ] Trivial N F (p x) :=
    ContinuousAlternatingMap.curryLeft (E := E') (ω (p x)) (V x)
  have h := ContinuousAlternatingMap.inCoordinates_compContinuousLinearMap
    (F₁ := E) (F₂ := E') (F₃ := F) (V₁ := TangentSpace I) (V₂ := TangentSpace I')
    (V₃ := Trivial N F) (x₀ := x₀) (y₀ := y₀) (z₀ := y₀)
    c (mfderivWithin I I' p s x) hx
  set e' := trivializationAt E' (TangentSpace I') y₀
  have hcur : ContinuousAlternatingMap.inCoordinates E' F y₀ (p x) y₀ (p x) c =
      (ContinuousAlternatingMap.inCoordinates E' F y₀ (p x) y₀ (p x) (ω (p x))).curryLeft
        (e' ⟨p x, V x⟩).2 := by
    ext v
    simp only [c, ContinuousAlternatingMap.inCoordinates,
      Bundle.Trivial.eq_trivialization N F (trivializationAt F (Trivial N F) y₀),
      Bundle.Trivial.continuousLinearMapAt_trivialization,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_def,
      ContinuousLinearMap.id_apply, ContinuousAlternatingMap.curryLeft_apply_apply]
    refine congrArg (ω (p x)) (funext fun i ↦ ?_)
    cases i using Fin.cases with
    | zero =>
      simp only [Matrix.cons_val_zero]
      rw [e'.symmL_apply hx, e'.symm_apply_apply_mk hx]
      rfl
    | succ i =>
      simp only [Matrix.cons_val_succ]
      rfl
  rw [hcur] at h
  ext v
  have hv := congrArg (fun a ↦ a v) h
  simp only [ContinuousAlternatingMap.inCoordinates,
    Bundle.Trivial.eq_trivialization M F (trivializationAt F (Trivial M F) x₀),
    Bundle.Trivial.eq_trivialization N F (trivializationAt F (Trivial N F) y₀),
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_def,
    ContinuousLinearMap.id_apply, mcontractionAlongMapWithin_apply] at hv ⊢
  exact hv

/-- **Within-set `C^m` regularity of contraction along a map.** If `ω` is `C^m` within `t` at
`p x`, `p` is `C^n` within `s` at `x` with `m + 1 ≤ n`, and `y ↦ (p y, V y)` is `C^m` into `TN`
within `s` at `x`, then `mcontractionAlongMapWithin I I' p V s ω` is `C^m` within `s` at `x`. -/
theorem _root_.ContMDiffWithinAt.mcontractionAlongMapWithin {m n : WithTop ℕ∞}
    {p : M → N} {V : (x : M) → TangentSpace I' (p x)}
    {ω : RoughForm I' N F (k + 1)} {s : Set M} {t : Set N} {x : M}
    (hω : ContMDiffWithinAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) y (ω y)) t (p x))
    (hp : ContMDiffWithinAt I I' n p s x)
    (hV : ContMDiffWithinAt I I'.tangent m
      (fun y ↦ TotalSpace.mk' E' (p y) (V y)) s x)
    (hmn : m + 1 ≤ n) (hst : MapsTo p s t) (hx : x ∈ s) (hs : UniqueMDiffOn I s) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y
        (TauCeti.mcontractionAlongMapWithin I I' p V s ω y)) s x := by
  have hpm : ContMDiffWithinAt I I' m p s x :=
    hp.of_le ((le_add_of_nonneg_right zero_le_one).trans hmn)
  have hω_coord := ((contMDiffWithinAt_continuousAlternatingMap_bundle _).mp hω).2.comp x hpm hst
  have hV_coord := (Bundle.contMDiffWithinAt_totalSpace_iff.mp hV).2
  have hcur := ((curryLeftLI (𝕜 := ℝ) (E := E') (F := F) (n := k)).toContinuousLinearMap.contDiff
    |>.comp_contMDiffWithinAt hω_coord).clm_apply hV_coord
  have hdp := hp.mfderivWithin_const hmn hx hs
  have hpre := ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := ℝ) (E := E) (F := E') (G := F) (ι := Fin k) m
  have hp_all := (hpre.comp_contMDiffWithinAt hdp).clm_apply hcur
  apply (contMDiffWithinAt_continuousAlternatingMap_bundle _).mpr
  refine ⟨contMDiffWithinAt_id, hp_all.congr_of_eventuallyEq_of_mem ?_ hx⟩
  have hmem : p ⁻¹' (trivializationAt E' (TangentSpace I') (p x)).baseSet ∈ 𝓝[s] x :=
    hp.continuousWithinAt.preimage_mem_nhdsWithin
      ((trivializationAt E' (TangentSpace I') (p x)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (p x)))
  filter_upwards [hmem] with y hy
  simpa only [Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    LinearIsometry.coe_toContinuousLinearMap, curryLeftLI_apply, inTangentCoordinates, id_eq]
    using ω.inCoordinates_mcontractionAlongMapWithin (I := I) p V s x y (p x) hy

/-- `C^m` regularity of `mcontractionAlongMapWithin` on a unique-differentiability set `s`. -/
theorem _root_.ContMDiffOn.mcontractionAlongMapWithin {m n : WithTop ℕ∞}
    {p : M → N} {V : (x : M) → TangentSpace I' (p x)}
    {ω : RoughForm I' N F (k + 1)} {s : Set M} {t : Set N}
    (hω : ContMDiffOn I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) y (ω y)) t)
    (hp : ContMDiffOn I I' n p s)
    (hV : ContMDiffOn I I'.tangent m (fun y ↦ TotalSpace.mk' E' (p y) (V y)) s)
    (hmn : m + 1 ≤ n) (hst : MapsTo p s t) (hs : UniqueMDiffOn I s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y
        (TauCeti.mcontractionAlongMapWithin I I' p V s ω y)) s :=
  fun x hx ↦ (hω (p x) (hst hx)).mcontractionAlongMapWithin (hp x hx) (hV x hx) hmn hst hx hs

/-- Pointwise `C^m` regularity of `mcontractionAlongMap`. -/
theorem _root_.ContMDiffAt.mcontractionAlongMap {m n : WithTop ℕ∞}
    {p : M → N} {V : (x : M) → TangentSpace I' (p x)}
    {ω : RoughForm I' N F (k + 1)} {x : M}
    (hω : ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) y (ω y)) (p x))
    (hp : ContMDiffAt I I' n p x)
    (hV : ContMDiffAt I I'.tangent m (fun y ↦ TotalSpace.mk' E' (p y) (V y)) x)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y
        (TauCeti.mcontractionAlongMap I I' p V ω y)) x := by
  simpa only [← contMDiffWithinAt_univ, mcontractionAlongMapWithin_univ] using
    hω.contMDiffWithinAt.mcontractionAlongMapWithin hp.contMDiffWithinAt hV.contMDiffWithinAt
      hmn (mapsTo_univ _ _) (mem_univ x) uniqueMDiffOn_univ

/-- **Contraction along a smooth family of maps.** Let `p : L → M → N` be jointly `C^n` at
`(q₀, g q₀)`, `g : L → M` be `C^m` at `q₀` (`m + 1 ≤ n`), and `V q` be a section along `p q`
such that `q ↦ (p q (g q), V q (g q))` is `C^m` into `TN` at `q₀`. For a form `ω` that is `C^m`
at `p q₀ (g q₀)`, the contractions `C_(p q, V q) ω` at `g q` form a `C^m` section along `g` at
`q₀`. -/
theorem _root_.ContMDiffAt.mcontractionAlongMap_family [IsManifold I'' 1 L] {m n : WithTop ℕ∞}
    {ω : RoughForm I' N F (k + 1)} {p : L → M → N} {g : L → M}
    {V : (q : L) → (y : M) → TangentSpace I' (p q y)} {q₀ : L}
    (hω : ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) y (ω y)) (p q₀ (g q₀)))
    (hp : ContMDiffAt (I''.prod I) I' n (Function.uncurry p) (q₀, g q₀))
    (hg : ContMDiffAt I'' I m g q₀)
    (hV : ContMDiffAt I'' I'.tangent m
      (fun q ↦ TotalSpace.mk' E' (p q (g q)) (V q (g q))) q₀)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt I'' (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun q ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) (g q)
        (TauCeti.mcontractionAlongMap I I' (p q) (V q) ω (g q))) q₀ := by
  have hpg : ContMDiffAt I'' I' m (fun q ↦ p q (g q)) q₀ :=
    (hp.of_le ((le_add_of_nonneg_right zero_le_one).trans hmn)).comp q₀
      (contMDiffAt_id.prodMk hg)
  have hω_coord := ((contMDiffAt_continuousAlternatingMap_bundle _).mp hω).2.comp q₀ hpg
  have hV_coord := (Bundle.contMDiffAt_totalSpace_iff.mp hV).2
  have hcur := ((curryLeftLI (𝕜 := ℝ) (E := E') (F := F) (n := k)).toContinuousLinearMap.contDiff
    |>.comp_contMDiffAt hω_coord).clm_apply hV_coord
  have hdp := hp.mfderiv p g hg hmn
  have hpre := ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := ℝ) (E := E) (F := E') (G := F) (ι := Fin k) m
  have hp_all := (hpre.comp_contMDiffAt hdp).clm_apply hcur
  apply (contMDiffAt_continuousAlternatingMap_bundle _).mpr
  refine ⟨hg, hp_all.congr_of_eventuallyEq ?_⟩
  have hmem : (fun q ↦ p q (g q)) ⁻¹'
      (trivializationAt E' (TangentSpace I') (p q₀ (g q₀))).baseSet ∈ 𝓝 q₀ :=
    hpg.continuousAt.preimage_mem_nhds
      ((trivializationAt E' (TangentSpace I') (p q₀ (g q₀))).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (p q₀ (g q₀))))
  filter_upwards [hmem] with q hq
  simpa only [Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    LinearIsometry.coe_toContinuousLinearMap, curryLeftLI_apply,
    mcontractionAlongMapWithin_univ, mfderivWithin_univ, inTangentCoordinates]
    using ω.inCoordinates_mcontractionAlongMapWithin (I := I) (p q) (V q) univ (g q₀) (g q)
      (p q₀ (g q₀)) hq

/-- Contracting a `C^m` fixed-coefficient form along a `C^(m + 1)` map `p` and a `C^m` section
`V` of `p^* TN` produces a `C^m` form. -/
theorem IsSmoothForm.mcontractionAlongMap {m : WithTop ℕ∞} {p : M → N}
    {V : (x : M) → TangentSpace I' (p x)} {ω : RoughForm I' N F (k + 1)}
    (hω : IsSmoothForm I' m ω) (hp : ContMDiff I I' (m + 1) p)
    (hV : ContMDiff I I'.tangent m (fun x ↦ TotalSpace.mk' E' (p x) (V x))) :
    IsSmoothForm I m (TauCeti.mcontractionAlongMap I I' p V ω) :=
  (isSmoothForm_def m _).mpr fun x ↦
    ((isSmoothForm_def m ω).mp hω (p x)).mcontractionAlongMap (hp x) (hV x) le_rfl

namespace SmoothForm

open scoped ContDiff

/-- **Bundled contraction along a smooth map** as a linear map on smooth fixed-coefficient forms. -/
def mcontractionAlongMap (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (hp : ContMDiff I I' ∞ p)
    (hV : ContMDiff I I'.tangent ∞ (fun x ↦ TotalSpace.mk' E' (p x) (V x))) :
    SmoothForm I' N F (k + 1) →ₗ[ℝ] SmoothForm I M F k where
  toFun φ := ⟨TauCeti.mcontractionAlongMap I I' p V φ.val,
    mem_smoothBundleForms.mpr
      ((isSmoothBundleForm_def ∞ _).mpr
        (φ.isSmoothForm.mcontractionAlongMap (by simpa using hp) hV).contMDiff)⟩
  map_add' φ η := Subtype.ext (TauCeti.mcontractionAlongMap_add p V φ.val η.val)
  map_smul' c φ := Subtype.ext (TauCeti.mcontractionAlongMap_smul p V c φ.val)

@[simp]
theorem coe_mcontractionAlongMap (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (hp : ContMDiff I I' ∞ p)
    (hV : ContMDiff I I'.tangent ∞ (fun x ↦ TotalSpace.mk' E' (p x) (V x)))
    (φ : SmoothForm I' N F (k + 1)) :
    (mcontractionAlongMap p V hp hV φ).val = TauCeti.mcontractionAlongMap I I' p V φ.val :=
  (rfl)

theorem mcontractionAlongMap_apply (p : M → N) (V : (x : M) → TangentSpace I' (p x))
    (hp : ContMDiff I I' ∞ p)
    (hV : ContMDiff I I'.tangent ∞ (fun x ↦ TotalSpace.mk' E' (p x) (V x)))
    (φ : SmoothForm I' N F (k + 1)) (x : M) (v : Fin k → TangentSpace I x) :
    (mcontractionAlongMap p V hp hV φ).val x v =
      φ.val (p x) (Matrix.vecCons (V x) fun i ↦ mfderiv I I' p x (v i)) :=
  (rfl)

end SmoothForm

end Smooth

end TauCeti
