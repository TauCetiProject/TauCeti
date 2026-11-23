/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.CylinderHomotopy
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Calculus.TangentCone.Prod
import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.Fin

/-!
# Contraction along a map and differentiation of moving pullbacks on normed spaces

Let `p : E → F` be a map between real normed spaces and `V : E → F` be a vector field along `p`,
which need not factor through a vector field on `F`. For a differential `(k + 1)`-form
`form : F → F [⋀^Fin (k + 1)]→L[ℝ] G`, its *contraction along `(p, V)`*
(`TauCeti.contractionAlongMap`) inserts `V x` into the first slot of `form (p x)` by
`ContinuousAlternatingMap.curryLeft` and pulls the remaining `k` slots back along `fderiv ℝ p x`:

`C_(p, V)(form)_x (v₁, …, vₖ) = form (p x) (V x, Dp(x) v₁, …, Dp(x) vₖ)`.

The relative version `TauCeti.contractionAlongMapWithin` uses `fderivWithin ℝ p s x` so that it
applies directly on chart domains with boundary or corners.

For a one-parameter family `P : E × ℝ → F`, with spatial slice `pₜ x = P (x, t)` and parameter
velocity `Vₜ x = DP(x, t)(0, 1)`, the *family contraction* `TauCeti.familyContraction P t form` is
`C_(pₜ, Vₜ)(form)`. Differentiating the pulled-back form `s ↦ pₛ^* form` in time at a fixed point
`x` gives the Cartan-type variation formula
(`TauCeti.hasDerivAt_compContinuousLinearMap_fderiv_family`)

`∂ₜ (pₜ^* form)ₓ = d (C_(pₜ, Vₜ) form)ₓ + (C_(pₜ, Vₜ) (d form))ₓ`,

requiring neither invertibility of the slices `pₜ` nor completeness of the coefficient space `G`.
The proof pulls `form` back to `E × ℝ` along `P`, applies the pointwise Cartan identity
`ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft_comp_add_curryLeft` in the parameter
direction `(0, 1)`, and restricts along the inclusion `inl : E →L[ℝ] E × ℝ`. Integrating over
`t ∈ [0, 1]` when `G` is complete identifies `∫₀¹ C_(pₜ, Vₜ) form dt` with the cylinder homotopy
operator `TauCeti.cylinderHomotopy` applied to `P^* form`
(`TauCeti.intervalIntegral_familyContraction_eq_cylinderHomotopy`).

## Main declarations

* `TauCeti.contractionAlongMapWithin`, `TauCeti.contractionAlongMap`: contraction of a differential
  form along a map and a vector field along that map.
* `TauCeti.contractionAlongMap_comp_right`,
  `TauCeti.contractionAlongMap_compContinuousLinearMap_fderiv`: naturality under precomposition on
  the source and pullback on the target.
* `ContDiffWithinAt.contractionAlongMapWithin`, `ContDiff.contractionAlongMap`: `C^m` regularity.
* `TauCeti.familyContractionWithin`, `TauCeti.familyContraction`: contraction of a form along a
  one-parameter family `P : E × ℝ → F` and its time velocity, with linearity, naturality, and
  `C^m` regularity.
* `TauCeti.hasDerivAt_compContinuousLinearMap_fderivWithin_family`,
  `TauCeti.hasDerivAt_compContinuousLinearMap_fderiv_family`: differentiation of moving pullbacks
  within a set and on the whole space.
* `TauCeti.hasDerivAt_comp_familyContractionWithin_extDerivWithin`,
  `TauCeti.hasDerivAt_comp_familyContraction_extDeriv`: the degree-zero specialization
  `∂ₜ (f ∘ pₜ)ₓ = C_(pₜ, Vₜ)(df)ₓ 0`.
* `TauCeti.intervalIntegral_familyContraction_eq_cylinderHomotopy`: agreement of the time integral
  of `familyContraction` over `[0, 1]` with `cylinderHomotopy` of the product pullback.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapters 14 and 17.
* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., §3.2.
-/

public section

noncomputable section

open Set Filter MeasureTheory ContinuousAlternatingMap
open scoped Topology ContDiff

namespace TauCeti

variable {E E' F F' G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {k : ℕ}

/-! ### Contraction along a map -/

/-- **Contraction along a map within a set.** Insert the vector `V x` along `p : E → F` into the
first slot of `form (p x)`, and pull the remaining `k` slots back by `fderivWithin ℝ p s x`. -/
def contractionAlongMapWithin (p : E → F) (V : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (s : Set E) (x : E) : E [⋀^Fin k]→L[ℝ] G :=
  ((form (p x)).curryLeft (V x)).compContinuousLinearMap (fderivWithin ℝ p s x)

/-- **Contraction along a map.** Insert the vector `V x` along `p : E → F` into the first slot of
`form (p x)`, and pull the remaining `k` slots back by `fderiv ℝ p x`. -/
def contractionAlongMap (p : E → F) (V : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (x : E) : E [⋀^Fin k]→L[ℝ] G :=
  ((form (p x)).curryLeft (V x)).compContinuousLinearMap (fderiv ℝ p x)

theorem contractionAlongMapWithin_def (p : E → F) (V : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (s : Set E) (x : E) :
    contractionAlongMapWithin p V form s x =
      ((form (p x)).curryLeft (V x)).compContinuousLinearMap (fderivWithin ℝ p s x) :=
  (rfl)

theorem contractionAlongMap_def (p : E → F) (V : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (x : E) :
    contractionAlongMap p V form x =
      ((form (p x)).curryLeft (V x)).compContinuousLinearMap (fderiv ℝ p x) :=
  (rfl)

@[simp]
theorem contractionAlongMapWithin_univ (p : E → F) (V : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    contractionAlongMapWithin p V form univ = contractionAlongMap p V form := by
  ext x v
  simp [contractionAlongMapWithin_def, contractionAlongMap_def]

theorem contractionAlongMapWithin_eq_contractionAlongMap {p : E → F} {V : E → F}
    {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G} {s : Set E} {x : E}
    (hs : UniqueDiffWithinAt ℝ s x) (hp : DifferentiableAt ℝ p x) :
    contractionAlongMapWithin p V form s x = contractionAlongMap p V form x := by
  rw [contractionAlongMapWithin_def, contractionAlongMap_def, fderivWithin_eq_fderiv hs hp]

@[simp]
theorem contractionAlongMapWithin_apply (p : E → F) (V : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (s : Set E) (x : E) (v : Fin k → E) :
    contractionAlongMapWithin p V form s x v =
      form (p x) (Matrix.vecCons (V x) fun i ↦ fderivWithin ℝ p s x (v i)) :=
  (rfl)

@[simp]
theorem contractionAlongMap_apply (p : E → F) (V : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (x : E) (v : Fin k → E) :
    contractionAlongMap p V form x v =
      form (p x) (Matrix.vecCons (V x) fun i ↦ fderiv ℝ p x (v i)) :=
  (rfl)

@[simp]
theorem contractionAlongMapWithin_zero_field (p : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (s : Set E) :
    contractionAlongMapWithin p 0 form s = 0 := by
  ext x v
  simp [contractionAlongMapWithin_def]

@[simp]
theorem contractionAlongMap_zero_field (p : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    contractionAlongMap p 0 form = 0 := by
  rw [← contractionAlongMapWithin_univ]
  exact contractionAlongMapWithin_zero_field p form univ

@[simp]
theorem contractionAlongMapWithin_zero (p : E → F) (V : E → F) (s : Set E) :
    contractionAlongMapWithin p V (0 : F → F [⋀^Fin (k + 1)]→L[ℝ] G) s = 0 := by
  ext x v
  simp

@[simp]
theorem contractionAlongMap_zero (p : E → F) (V : E → F) :
    contractionAlongMap p V (0 : F → F [⋀^Fin (k + 1)]→L[ℝ] G) = 0 := by
  ext x v
  simp

@[simp]
theorem contractionAlongMapWithin_add_field (p : E → F) (V W : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (s : Set E) :
    contractionAlongMapWithin p (V + W) form s =
      contractionAlongMapWithin p V form s + contractionAlongMapWithin p W form s := by
  ext x v
  simp [contractionAlongMapWithin_def, map_add]

@[simp]
theorem contractionAlongMap_add_field (p : E → F) (V W : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    contractionAlongMap p (V + W) form =
      contractionAlongMap p V form + contractionAlongMap p W form := by
  rw [← contractionAlongMapWithin_univ, ← contractionAlongMapWithin_univ,
    ← contractionAlongMapWithin_univ]
  exact contractionAlongMapWithin_add_field p V W form univ

@[simp]
theorem contractionAlongMapWithin_smul_field (p : E → F) (a : E → ℝ) (V : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (s : Set E) :
    contractionAlongMapWithin p (fun x ↦ a x • V x) form s =
      fun x ↦ a x • contractionAlongMapWithin p V form s x := by
  ext x v
  simp [contractionAlongMapWithin_def]

@[simp]
theorem contractionAlongMap_smul_field (p : E → F) (a : E → ℝ) (V : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    contractionAlongMap p (fun x ↦ a x • V x) form =
      fun x ↦ a x • contractionAlongMap p V form x := by
  ext x v
  simp [contractionAlongMap_def]

@[simp]
theorem contractionAlongMapWithin_add (p : E → F) (V : E → F)
    (form₁ form₂ : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (s : Set E) :
    contractionAlongMapWithin p V (form₁ + form₂) s =
      contractionAlongMapWithin p V form₁ s + contractionAlongMapWithin p V form₂ s := by
  ext x v
  simp

@[simp]
theorem contractionAlongMap_add (p : E → F) (V : E → F)
    (form₁ form₂ : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    contractionAlongMap p V (form₁ + form₂) =
      contractionAlongMap p V form₁ + contractionAlongMap p V form₂ := by
  ext x v
  simp

@[simp]
theorem contractionAlongMapWithin_smul (c : ℝ) (p : E → F) (V : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (s : Set E) :
    contractionAlongMapWithin p V (c • form) s = c • contractionAlongMapWithin p V form s := by
  ext x v
  simp

@[simp]
theorem contractionAlongMap_smul (c : ℝ) (p : E → F) (V : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    contractionAlongMap p V (c • form) = c • contractionAlongMap p V form := by
  ext x v
  simp

@[simp]
theorem contractionAlongMapWithin_neg (p : E → F) (V : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (s : Set E) :
    contractionAlongMapWithin p V (-form) s = -contractionAlongMapWithin p V form s := by
  ext x v
  simp

@[simp]
theorem contractionAlongMap_neg (p : E → F) (V : E → F)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    contractionAlongMap p V (-form) = -contractionAlongMap p V form := by
  ext x v
  simp

@[simp]
theorem contractionAlongMapWithin_sub (p : E → F) (V : E → F)
    (form₁ form₂ : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (s : Set E) :
    contractionAlongMapWithin p V (form₁ - form₂) s =
      contractionAlongMapWithin p V form₁ s - contractionAlongMapWithin p V form₂ s := by
  ext x v
  simp

@[simp]
theorem contractionAlongMap_sub (p : E → F) (V : E → F)
    (form₁ form₂ : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    contractionAlongMap p V (form₁ - form₂) =
      contractionAlongMap p V form₁ - contractionAlongMap p V form₂ := by
  ext x v
  simp

/-- Along the identity map, `contractionAlongMap` is the interior product `curryLeft`. -/
@[simp]
theorem contractionAlongMap_id (V : E → E) (form : E → E [⋀^Fin (k + 1)]→L[ℝ] G) (x : E) :
    contractionAlongMap id V form x = (form x).curryLeft (V x) := by
  ext v
  simp [contractionAlongMap_def]

/-- **Source naturality within a set.** Precomposing `(p, V)` with `h : E' → E` pulls back the
contraction along `h`. -/
theorem contractionAlongMapWithin_comp_right {h : E' → E} {p : E → F} {V : E → F}
    {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G} {s' : Set E'} {s : Set E} {z : E'}
    (hh : DifferentiableWithinAt ℝ h s' z) (hp : DifferentiableWithinAt ℝ p s (h z))
    (hst : MapsTo h s' s) (hs' : UniqueDiffWithinAt ℝ s' z) :
    contractionAlongMapWithin (p ∘ h) (V ∘ h) form s' z =
      (contractionAlongMapWithin p V form s (h z)).compContinuousLinearMap
        (fderivWithin ℝ h s' z) := by
  rw [contractionAlongMapWithin_def, contractionAlongMapWithin_def,
    fderivWithin_comp z hp hh hst hs']
  ext v
  rfl

/-- **Source naturality.** If `h : E' → E` is differentiable at `z` and `p : E → F` is
differentiable at `h z`, then precomposing `(p, V)` with `h` pulls back the contraction along `h`.
-/
theorem contractionAlongMap_comp_right {h : E' → E} {p : E → F} {V : E → F}
    {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G} {z : E'}
    (hh : DifferentiableAt ℝ h z) (hp : DifferentiableAt ℝ p (h z)) :
    contractionAlongMap (p ∘ h) (V ∘ h) form z =
      (contractionAlongMap p V form (h z)).compContinuousLinearMap (fderiv ℝ h z) := by
  simpa only [contractionAlongMapWithin_univ, fderivWithin_univ] using
    contractionAlongMapWithin_comp_right (s' := univ) (s := univ)
      hh.differentiableWithinAt hp.differentiableWithinAt (mapsTo_univ _ _) uniqueDiffWithinAt_univ

/-- **Target naturality within sets.** Contracting a pulled-back form `q^* η` along `(p, V)` is
contracting `η` along `(q ∘ p, Dq ∘ V)`. -/
theorem contractionAlongMapWithin_compContinuousLinearMap_fderivWithin {p : E → F} {q : F → F'}
    {V : E → F} {η : F' → F' [⋀^Fin (k + 1)]→L[ℝ] G} {s : Set E} {t : Set F} {x : E}
    (hp : DifferentiableWithinAt ℝ p s x) (hq : DifferentiableWithinAt ℝ q t (p x))
    (hst : MapsTo p s t) (hs : UniqueDiffWithinAt ℝ s x) :
    contractionAlongMapWithin p V
        (fun y ↦ (η (q y)).compContinuousLinearMap (fderivWithin ℝ q t y)) s x =
      contractionAlongMapWithin (q ∘ p) (fun y ↦ fderivWithin ℝ q t (p y) (V y)) η s x := by
  ext v
  rw [contractionAlongMapWithin_apply, contractionAlongMapWithin_apply,
    compContinuousLinearMap_apply, fderivWithin_comp x hq hp hst hs]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

/-- **Target naturality.** Contracting a pulled-back form `q^* η` along `(p, V)` is contracting `η`
along `(q ∘ p, Dq ∘ V)`. -/
theorem contractionAlongMap_compContinuousLinearMap_fderiv {p : E → F} {q : F → F'} {V : E → F}
    {η : F' → F' [⋀^Fin (k + 1)]→L[ℝ] G} {x : E}
    (hp : DifferentiableAt ℝ p x) (hq : DifferentiableAt ℝ q (p x)) :
    contractionAlongMap p V
        (fun y ↦ (η (q y)).compContinuousLinearMap (fderiv ℝ q y)) x =
      contractionAlongMap (q ∘ p) (fun y ↦ fderiv ℝ q (p y) (V y)) η x := by
  simpa only [contractionAlongMapWithin_univ, fderivWithin_univ] using
    contractionAlongMapWithin_compContinuousLinearMap_fderivWithin (s := univ) (t := univ)
      (V := V) (η := η) hp.differentiableWithinAt hq.differentiableWithinAt
      (mapsTo_univ _ _) uniqueDiffWithinAt_univ

/-! ### Regularity -/

/-- A `C^m` form contracted along a `C^n` map (`m + 1 ≤ n`) and a `C^m` vector field along it is
`C^m` within a unique-differentiability set. -/
theorem _root_.ContDiffWithinAt.contractionAlongMapWithin {m n : WithTop ℕ∞}
    {p : E → F} {V : E → F} {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G} {s : Set E} {t : Set F} {x : E}
    (hform : ContDiffWithinAt ℝ m form t (p x))
    (hp : ContDiffWithinAt ℝ n p s x) (hV : ContDiffWithinAt ℝ m V s x)
    (hmn : m + 1 ≤ n) (hst : MapsTo p s t) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    ContDiffWithinAt ℝ m (contractionAlongMapWithin p V form s) s x := by
  have hpm : ContDiffWithinAt ℝ m p s x :=
    hp.of_le ((le_add_of_nonneg_right zero_le_one).trans hmn)
  have hcur : ContDiffWithinAt ℝ m (fun y ↦ (form (p y)).curryLeft (V y)) s x := by
    simpa only [Function.comp_def, LinearIsometry.coe_toContinuousLinearMap, curryLeftLI_apply]
      using ((curryLeftLI (𝕜 := ℝ) (E := F) (F := G) (n := k)).toContinuousLinearMap.contDiff
        |>.comp_contDiffWithinAt (hform.comp x hpm hst)).clm_apply hV
  have hdp : ContDiffWithinAt ℝ m (fderivWithin ℝ p s) s x :=
    hp.fderivWithin_right hs hmn hx
  simpa only [Function.comp_def, compContinuousLinearMapCLM_apply, ← contractionAlongMapWithin_def]
    using (ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
      (𝕜 := ℝ) (E := E) (F := F) (G := G) (ι := Fin k) m |>.comp_contDiffWithinAt hdp).clm_apply
      hcur

/-- On a unique-differentiability set, contracting a `C^m` form along a `C^n` map (`m + 1 ≤ n`) and
a `C^m` vector field along it gives a `C^m` form. -/
theorem _root_.ContDiffOn.contractionAlongMapWithin {m n : WithTop ℕ∞}
    {p : E → F} {V : E → F} {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G} {s : Set E} {t : Set F}
    (hform : ContDiffOn ℝ m form t) (hp : ContDiffOn ℝ n p s) (hV : ContDiffOn ℝ m V s)
    (hmn : m + 1 ≤ n) (hst : MapsTo p s t) (hs : UniqueDiffOn ℝ s) :
    ContDiffOn ℝ m (TauCeti.contractionAlongMapWithin p V form s) s :=
  fun x hx ↦ (hform (p x) (hst hx)).contractionAlongMapWithin (hp x hx) (hV x hx) hmn hst hs hx

/-- Pointwise `C^m` regularity of `contractionAlongMap` when `m + 1 ≤ n`. -/
theorem _root_.ContDiffAt.contractionAlongMap {m n : WithTop ℕ∞}
    {p : E → F} {V : E → F} {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G} {x : E}
    (hform : ContDiffAt ℝ m form (p x)) (hp : ContDiffAt ℝ n p x) (hV : ContDiffAt ℝ m V x)
    (hmn : m + 1 ≤ n) :
    ContDiffAt ℝ m (TauCeti.contractionAlongMap p V form) x := by
  simpa only [← contDiffWithinAt_univ, contractionAlongMapWithin_univ] using
    hform.contDiffWithinAt.contractionAlongMapWithin hp.contDiffWithinAt hV.contDiffWithinAt hmn
      (mapsTo_univ _ _) uniqueDiffOn_univ (mem_univ x)

/-- Global `C^m` regularity of `contractionAlongMap` when `m + 1 ≤ n`. -/
theorem _root_.ContDiff.contractionAlongMap {m n : WithTop ℕ∞}
    {p : E → F} {V : E → F} {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G}
    (hform : ContDiff ℝ m form) (hp : ContDiff ℝ n p) (hV : ContDiff ℝ m V) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (TauCeti.contractionAlongMap p V form) :=
  contDiff_iff_contDiffAt.mpr fun _ ↦
    hform.contDiffAt.contractionAlongMap hp.contDiffAt hV.contDiffAt hmn

/-! ### Family contraction and differentiation of moving pullbacks -/

/-- **Family contraction within a set.** Contraction of `form` at time `t` along the spatial slice
`y ↦ P (y, t)` of `P : E × ℝ → F` and its parameter velocity `y ↦ deriv (fun u ↦ P (y, u)) t`,
using derivatives within `s`. -/
def familyContractionWithin (P : E × ℝ → F) (s : Set E) (t : ℝ)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (x : E) : E [⋀^Fin k]→L[ℝ] G :=
  contractionAlongMapWithin (fun y ↦ P (y, t)) (fun y ↦ deriv (fun u ↦ P (y, u)) t) form s x

/-- **Family contraction.** Contraction of `form` at time `t` along the spatial slice
`x ↦ P (x, t)` of `P : E × ℝ → F` and its parameter velocity `x ↦ fderiv ℝ P (x, t) (0, 1)`. -/
def familyContraction (P : E × ℝ → F) (t : ℝ)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) : E → E [⋀^Fin k]→L[ℝ] G :=
  contractionAlongMap (fun x ↦ P (x, t)) (fun x ↦ fderiv ℝ P (x, t) (0, 1)) form

theorem familyContractionWithin_def (P : E × ℝ → F) (s : Set E) (t : ℝ)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (x : E) :
    familyContractionWithin P s t form x =
      contractionAlongMapWithin (fun y ↦ P (y, t))
        (fun y ↦ deriv (fun u ↦ P (y, u)) t) form s x :=
  (rfl)

theorem familyContraction_def (P : E × ℝ → F) (t : ℝ)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    familyContraction P t form =
      contractionAlongMap (fun x ↦ P (x, t)) (fun x ↦ fderiv ℝ P (x, t) (0, 1)) form :=
  (rfl)

@[simp]
theorem familyContractionWithin_apply (P : E × ℝ → F) (s : Set E) (t : ℝ)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (x : E) (v : Fin k → E) :
    familyContractionWithin P s t form x v =
      form (P (x, t)) (Matrix.vecCons (deriv (fun u ↦ P (x, u)) t)
        fun i ↦ fderivWithin ℝ (fun y ↦ P (y, t)) s x (v i)) :=
  (rfl)

@[simp]
theorem familyContraction_apply (P : E × ℝ → F) (t : ℝ)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) (x : E) (v : Fin k → E) :
    familyContraction P t form x v =
      form (P (x, t)) (Matrix.vecCons (fderiv ℝ P (x, t) (0, 1))
        fun i ↦ fderiv ℝ (fun y ↦ P (y, t)) x (v i)) :=
  (rfl)

@[simp]
theorem familyContractionWithin_zero (P : E × ℝ → F) (s : Set E) (t : ℝ) :
    familyContractionWithin P s t (0 : F → F [⋀^Fin (k + 1)]→L[ℝ] G) = 0 :=
  contractionAlongMapWithin_zero _ _ _

@[simp]
theorem familyContraction_zero (P : E × ℝ → F) (t : ℝ) :
    familyContraction P t (0 : F → F [⋀^Fin (k + 1)]→L[ℝ] G) = 0 :=
  contractionAlongMap_zero _ _

@[simp]
theorem familyContractionWithin_add (P : E × ℝ → F) (s : Set E) (t : ℝ)
    (form₁ form₂ : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    familyContractionWithin P s t (form₁ + form₂) =
      familyContractionWithin P s t form₁ + familyContractionWithin P s t form₂ :=
  contractionAlongMapWithin_add _ _ form₁ form₂ _

@[simp]
theorem familyContraction_add (P : E × ℝ → F) (t : ℝ)
    (form₁ form₂ : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    familyContraction P t (form₁ + form₂) =
      familyContraction P t form₁ + familyContraction P t form₂ :=
  contractionAlongMap_add _ _ form₁ form₂

@[simp]
theorem familyContractionWithin_smul (c : ℝ) (P : E × ℝ → F) (s : Set E) (t : ℝ)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    familyContractionWithin P s t (c • form) = c • familyContractionWithin P s t form :=
  contractionAlongMapWithin_smul c _ _ form _

@[simp]
theorem familyContraction_smul (c : ℝ) (P : E × ℝ → F) (t : ℝ)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    familyContraction P t (c • form) = c • familyContraction P t form :=
  contractionAlongMap_smul c _ _ form

@[simp]
theorem familyContractionWithin_neg (P : E × ℝ → F) (s : Set E) (t : ℝ)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    familyContractionWithin P s t (-form) = -familyContractionWithin P s t form :=
  contractionAlongMapWithin_neg _ _ form _

@[simp]
theorem familyContraction_neg (P : E × ℝ → F) (t : ℝ)
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    familyContraction P t (-form) = -familyContraction P t form :=
  contractionAlongMap_neg _ _ form

@[simp]
theorem familyContractionWithin_sub (P : E × ℝ → F) (s : Set E) (t : ℝ)
    (form₁ form₂ : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    familyContractionWithin P s t (form₁ - form₂) =
      familyContractionWithin P s t form₁ - familyContractionWithin P s t form₂ :=
  contractionAlongMapWithin_sub _ _ form₁ form₂ _

@[simp]
theorem familyContraction_sub (P : E × ℝ → F) (t : ℝ)
    (form₁ form₂ : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    familyContraction P t (form₁ - form₂) =
      familyContraction P t form₁ - familyContraction P t form₂ :=
  contractionAlongMap_sub _ _ form₁ form₂

/-- **Source naturality of `familyContractionWithin`.** Precomposing a moving family `P : E × ℝ → F`
in its spatial argument with `h : E' → E` pulls back `familyContractionWithin` along `h`. -/
theorem familyContractionWithin_comp_prodMap_id {h : E' → E} {P : E × ℝ → F}
    {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G} {s' : Set E'} {s : Set E} {t : ℝ} {z : E'}
    (hh : DifferentiableWithinAt ℝ h s' z)
    (hP : DifferentiableWithinAt ℝ (fun y ↦ P (y, t)) s (h z))
    (hst : MapsTo h s' s) (hs' : UniqueDiffWithinAt ℝ s' z) :
    familyContractionWithin (P ∘ Prod.map h id) s' t form z =
      (familyContractionWithin P s t form (h z)).compContinuousLinearMap
        (fderivWithin ℝ h s' z) := by
  have hbase := contractionAlongMapWithin_comp_right (h := h) (p := fun y ↦ P (y, t))
    (V := fun y ↦ deriv (fun u ↦ P (y, u)) t) (form := form) hh hP hst hs'
  simpa only [familyContractionWithin_def, Function.comp_def, Prod.map_apply, id_eq] using hbase

/-- **Source naturality of `familyContraction`.** If `h : E' → E` is differentiable at `z` and
`P : E × ℝ → F` is differentiable at `(h z, t)`, precomposing `P` in its spatial argument with `h`
pulls back `familyContraction` along `h`. -/
theorem familyContraction_comp_prodMap_id {h : E' → E} {P : E × ℝ → F}
    {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G} {t : ℝ} {z : E'}
    (hh : DifferentiableAt ℝ h z) (hP : DifferentiableAt ℝ P (h z, t)) :
    familyContraction (P ∘ Prod.map h id) t form z =
      (familyContraction P t form (h z)).compContinuousLinearMap (fderiv ℝ h z) := by
  have hP_slice : DifferentiableAt ℝ (fun y ↦ P (y, t)) (h z) :=
    hP.comp (h z) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (h z) t).differentiableAt
  have hvel : fderiv ℝ (P ∘ Prod.map h id) (z, t) (0, 1) = fderiv ℝ P (h z, t) (0, 1) := by
    have hmap : HasFDerivAt (Prod.map h (id : ℝ → ℝ))
        ((fderiv ℝ h z).prodMap (ContinuousLinearMap.id ℝ ℝ)) (z, t) :=
      hh.hasFDerivAt.prodMap (z, t) (hasFDerivAt_id t)
    rw [fderiv_comp (z, t) hP hmap.differentiableAt, hmap.fderiv]
    simp
  have hbase := contractionAlongMap_comp_right (h := h) (p := fun y ↦ P (y, t))
    (V := fun y ↦ fderiv ℝ P (y, t) (0, 1)) (form := form) hh hP_slice
  ext v
  rw [familyContraction_apply, compContinuousLinearMap_apply, familyContraction_apply, hvel]
  simpa only [contractionAlongMap_apply, compContinuousLinearMap_apply, Function.comp_def,
    Prod.map_apply, id_eq] using DFunLike.congr_fun hbase v

/-- **Target naturality of `familyContractionWithin`.** Contracting a pulled-back form `q^* η`
along a moving family `P` equals contracting `η` along `q ∘ P`. -/
theorem familyContractionWithin_compContinuousLinearMap_fderivWithin {P : E × ℝ → F} {q : F → F'}
    {η : F' → F' [⋀^Fin (k + 1)]→L[ℝ] G} {s : Set E} {t_set : Set F} {x : E} {t : ℝ}
    (hPs : DifferentiableWithinAt ℝ (fun y ↦ P (y, t)) s x)
    (hPt : DifferentiableAt ℝ (fun u ↦ P (x, u)) t)
    (hq : DifferentiableWithinAt ℝ q t_set (P (x, t)))
    (hst : MapsTo (fun y ↦ P (y, t)) s t_set) (hs : UniqueDiffWithinAt ℝ s x)
    (hmaps_t : (fun u ↦ P (x, u)) ⁻¹' t_set ∈ 𝓝 t) :
    familyContractionWithin P s t
        (fun y ↦ (η (q y)).compContinuousLinearMap (fderivWithin ℝ q t_set y)) x =
      familyContractionWithin (q ∘ P) s t η x := by
  have hvel : deriv (fun u ↦ q (P (x, u))) t =
      fderivWithin ℝ q t_set (P (x, t)) (deriv (fun u ↦ P (x, u)) t) := by
    obtain ⟨U, hUsub, hUopen, htU⟩ := mem_nhds_iff.mp hmaps_t
    have hc : HasDerivWithinAt (fun u ↦ q (P (x, u)))
        (fderivWithin ℝ q t_set (P (x, t)) (deriv (fun u ↦ P (x, u)) t)) U t :=
      hq.hasFDerivWithinAt.comp_hasDerivWithinAt t hPt.hasDerivAt.hasDerivWithinAt
        (fun _ hu ↦ hUsub hu)
    exact (hc.hasDerivAt (hUopen.mem_nhds htU)).deriv
  have hbase := contractionAlongMapWithin_compContinuousLinearMap_fderivWithin
    (p := fun y ↦ P (y, t)) (q := q) (V := fun y ↦ deriv (fun u ↦ P (y, u)) t) (η := η)
    hPs hq hst hs
  ext v
  simpa only [familyContractionWithin_apply, contractionAlongMapWithin_apply, Function.comp_def,
    hvel] using DFunLike.congr_fun hbase v

/-- **Target naturality of `familyContraction`.** Contracting a pulled-back form `q^* η` along a
moving family `P` equals contracting `η` along `q ∘ P`. -/
theorem familyContraction_compContinuousLinearMap_fderiv {P : E × ℝ → F} {q : F → F'}
    {η : F' → F' [⋀^Fin (k + 1)]→L[ℝ] G} {x : E} {t : ℝ}
    (hP : DifferentiableAt ℝ P (x, t)) (hq : DifferentiableAt ℝ q (P (x, t))) :
    familyContraction P t (fun y ↦ (η (q y)).compContinuousLinearMap (fderiv ℝ q y)) x =
      familyContraction (q ∘ P) t η x := by
  have hPs : DifferentiableAt ℝ (fun y ↦ P (y, t)) x :=
    hP.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t).differentiableAt
  have hvel : fderiv ℝ (q ∘ P) (x, t) (0, 1) =
      fderiv ℝ q (P (x, t)) (fderiv ℝ P (x, t) (0, 1)) := by
    rw [fderiv_comp (x, t) hq hP, ContinuousLinearMap.comp_apply]
  have hbase := contractionAlongMap_compContinuousLinearMap_fderiv
    (p := fun y ↦ P (y, t)) (q := q) (V := fun y ↦ fderiv ℝ P (y, t) (0, 1)) (η := η) hPs hq
  ext v
  rw [familyContraction_apply, familyContraction_apply, hvel]
  simpa only [contractionAlongMap_apply, Function.comp_def] using DFunLike.congr_fun hbase v

/-- Pointwise `C^m` regularity of `familyContractionWithin` within a unique-differentiability set
when `m + 1 ≤ n`. -/
theorem _root_.ContDiffWithinAt.familyContractionWithin {m n : WithTop ℕ∞}
    {P : E × ℝ → F} {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G}
    {s : Set E} {U : Set ℝ} {t_set : Set F} {x : E} {t : ℝ}
    (hform : ContDiffWithinAt ℝ m form t_set (P (x, t)))
    (hP : ContDiffWithinAt ℝ n P (s ×ˢ U) (x, t)) (hmn : m + 1 ≤ n)
    (hst : MapsTo (fun y ↦ P (y, t)) s t_set) (hs : UniqueDiffOn ℝ s) (hxs : x ∈ s)
    (hU : IsOpen U) (htU : t ∈ U) :
    ContDiffWithinAt ℝ m (familyContractionWithin P s t form) s x := by
  have hmaps_slice : MapsTo (fun y : E ↦ (y, t)) s (s ×ˢ U) := fun _ hy ↦ Set.mk_mem_prod hy htU
  have hslice_n : ContDiffWithinAt ℝ n (fun y ↦ P (y, t)) s x :=
    hP.comp x ((contDiff_id.prodMk contDiff_const).contDiffWithinAt (s := s)) hmaps_slice
  have h1n : (1 : WithTop ℕ∞) ≤ n := (le_add_of_nonneg_left bot_le).trans hmn
  have hP1 : ContDiffWithinAt ℝ (1 : ℕ) P (s ×ˢ U) (x, t) := hP.of_le (by exact_mod_cast h1n)
  obtain ⟨W, hWmem, -, hP1on⟩ := hP1.contDiffOn (le_refl (1 : WithTop ℕ∞)) (by simp)
  rw [insert_eq_of_mem (Set.mk_mem_prod hxs htU)] at hWmem
  obtain ⟨W₀, hW₀open, hxW₀, hW₀sub⟩ := mem_nhdsWithin.mp hWmem
  have hV_eq : (fun y ↦ fderivWithin ℝ P (s ×ˢ U) (y, t) (0, 1)) =ᶠ[𝓝[s] x]
      (fun y ↦ deriv (fun u ↦ P (y, u)) t) := by
    have hpre : (fun y : E ↦ (y, t)) ⁻¹' W₀ ∈ 𝓝 x :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hW₀open.mem_nhds hxW₀)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hpre] with y hy hyW₀
    have hWmem_y : W ∈ 𝓝[s ×ˢ U] (y, t) :=
      Filter.mem_of_superset
        (Filter.inter_mem (nhdsWithin_le_nhds (hW₀open.mem_nhds hyW₀)) self_mem_nhdsWithin) hW₀sub
    have hdPy : DifferentiableWithinAt ℝ P (s ×ˢ U) (y, t) :=
      ((hP1on (y, t) (hW₀sub ⟨hyW₀, Set.mk_mem_prod hy htU⟩)).mono_of_mem_nhdsWithin
        hWmem_y).differentiableWithinAt one_ne_zero
    exact fderivWithin_apply_mk_zero_one hdPy hy (hU.mem_nhds htU)
  have hV_m : ContDiffWithinAt ℝ m (fun y ↦ deriv (fun u ↦ P (y, u)) t) s x := by
    have hdf : ContDiffWithinAt ℝ m (fun y ↦ fderivWithin ℝ P (s ×ˢ U) (y, t) (0, 1)) s x :=
      ((hP.fderivWithin_right (hs.prod hU.uniqueDiffOn) hmn ⟨hxs, htU⟩).comp x
        ((contDiff_id.prodMk contDiff_const).contDiffWithinAt (s := s))
        hmaps_slice).clm_apply contDiffWithinAt_const
    exact hdf.congr_of_eventuallyEq hV_eq.symm
      (fderivWithin_apply_mk_zero_one (hP1.differentiableWithinAt one_ne_zero) hxs
        (hU.mem_nhds htU)).symm
  exact hform.contractionAlongMapWithin (p := fun y ↦ P (y, t)) hslice_n hV_m hmn hst hs hxs

/-- `C^m` regularity of `familyContractionWithin` on a unique-differentiability set when
`m + 1 ≤ n`. -/
theorem _root_.ContDiffOn.familyContractionWithin {m n : WithTop ℕ∞}
    {P : E × ℝ → F} {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G}
    {s : Set E} {U : Set ℝ} {t_set : Set F} {t : ℝ}
    (hform : ContDiffOn ℝ m form t_set) (hP : ContDiffOn ℝ n P (s ×ˢ U)) (hmn : m + 1 ≤ n)
    (hst : MapsTo (fun y ↦ P (y, t)) s t_set) (hs : UniqueDiffOn ℝ s)
    (hU : IsOpen U) (htU : t ∈ U) :
    ContDiffOn ℝ m (familyContractionWithin P s t form) s :=
  fun x hx ↦ (hform (P (x, t)) (hst hx)).familyContractionWithin (hP (x, t) ⟨hx, htU⟩)
    hmn hst hs hx hU htU

/-- Pointwise `C^m` regularity of `familyContraction` when `m + 1 ≤ n`. -/
theorem _root_.ContDiffAt.familyContraction {m n : WithTop ℕ∞}
    {P : E × ℝ → F} {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G} {x : E} {t : ℝ}
    (hform : ContDiffAt ℝ m form (P (x, t))) (hP : ContDiffAt ℝ n P (x, t)) (hmn : m + 1 ≤ n) :
    ContDiffAt ℝ m (familyContraction P t form) x := by
  have hslice_n : ContDiffAt ℝ n (fun y ↦ P (y, t)) x :=
    hP.comp x (contDiff_id.prodMk contDiff_const).contDiffAt
  have hV_m : ContDiffAt ℝ m (fun y ↦ fderiv ℝ P (y, t) (0, 1)) x :=
    ((hP.fderiv_right hmn).comp x (contDiff_id.prodMk contDiff_const).contDiffAt).clm_apply
      contDiffAt_const
  exact hform.contractionAlongMap (p := fun y ↦ P (y, t)) hslice_n hV_m hmn

/-- Global `C^m` regularity of `familyContraction` when `m + 1 ≤ n`. -/
theorem _root_.ContDiff.familyContraction {m n : WithTop ℕ∞}
    {P : E × ℝ → F} {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G} {t : ℝ}
    (hform : ContDiff ℝ m form) (hP : ContDiff ℝ n P) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (familyContraction P t form) :=
  contDiff_iff_contDiffAt.mpr fun _ ↦ hform.contDiffAt.familyContraction hP.contDiffAt hmn

theorem familyContractionWithin_univ_eq_of_differentiableAt {P : E × ℝ → F} {t : ℝ} {x : E}
    (hP : DifferentiableAt ℝ P (x, t)) (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    familyContractionWithin P univ t form x = familyContraction P t form x := by
  have hvel : deriv (fun u ↦ P (x, u)) t = fderiv ℝ P (x, t) (0, 1) :=
    (hasDerivAt_slice_right hP).deriv
  ext v
  simp [familyContractionWithin_apply, familyContraction_apply, hvel]

/-- Contracting the product pullback `(η ∘ P)^*` along `(0, 1)` and restricting to `E × {0}` via
`ContinuousLinearMap.inl` recovers `familyContractionWithin`. -/
private theorem compContinuousLinearMap_inl_curryLeft_pullback_eq_familyContractionWithin
    {P : E × ℝ → F} {s s' : Set E} {U' : Set ℝ} {y : E} {t : ℝ}
    (hs'eq : s' =ᶠ[𝓝 y] s) (hs' : UniqueDiffWithinAt ℝ s' y) (hy : y ∈ s')
    (hU' : U' ∈ 𝓝 t) (hP : DifferentiableWithinAt ℝ P (s' ×ˢ U') (y, t))
    (η : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    (((η (P (y, t))).compContinuousLinearMap
      (fderivWithin ℝ P (s' ×ˢ U') (y, t))).curryLeft (0, 1)).compContinuousLinearMap
      (.inl ℝ E ℝ) = familyContractionWithin P s t η y := by
  have hfderiv_s' : fderivWithin ℝ (fun z ↦ P (z, t)) s' y =
      fderivWithin ℝ (fun z ↦ P (z, t)) s y :=
    fderivWithin_congr_set hs'eq
  have hinl := fderivWithin_slice_left hP hs' (mem_of_mem_nhds hU')
  have hvel := fderivWithin_apply_mk_zero_one hP hy hU'
  ext v
  simp only [familyContractionWithin_apply, compContinuousLinearMap_apply, curryLeft_apply_apply,
    ← hfderiv_s', hinl, ← hvel, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

/-- Core of `hasDerivAt_compContinuousLinearMap_fderivWithin_family` once `P` has been restricted
to a rectangular neighbourhood `(s ∩ O₁) ×ˢ U'` on which it is `C²` and maps into `t_set`. -/
private theorem hasDerivAt_compContinuousLinearMap_fderivWithin_family_of_contDiffOn
    {P : E × ℝ → F} {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G}
    {s O₁ : Set E} {U' : Set ℝ} {t_set : Set F} {x : E} {t : ℝ}
    (hs : UniqueDiffOn ℝ s) (hxc : x ∈ closure (interior s)) (hxs : x ∈ s)
    (hO₁open : IsOpen O₁) (hxO₁ : x ∈ O₁) (hU'open : IsOpen U') (htU' : t ∈ U')
    (hPon : ContDiffOn ℝ (2 : ℕ) P ((s ∩ O₁) ×ˢ U'))
    (hst' : MapsTo P ((s ∩ O₁) ×ˢ U') t_set)
    (hform : DifferentiableWithinAt ℝ form t_set (P (x, t))) :
    HasDerivAt
      (fun u ↦ (form (P (x, u))).compContinuousLinearMap
        (fderivWithin ℝ (fun y ↦ P (y, u)) s x))
      (extDerivWithin (familyContractionWithin P s t form) s x +
        familyContractionWithin P s t (extDerivWithin form t_set) x) t := by
  set s' := s ∩ O₁
  have hxs' : x ∈ s' := ⟨hxs, hxO₁⟩
  have hs'u : UniqueDiffOn ℝ s' := hs.inter hO₁open
  have hWu : UniqueDiffOn ℝ (s' ×ˢ U') := UniqueDiffOn.prod hs'u hU'open.uniqueDiffOn
  have hxc' : x ∈ closure (interior s') := by
    rw [mem_closure_iff_nhds] at hxc ⊢
    intro V₀ hV₀
    obtain ⟨y, ⟨hyV₀, hyO₁⟩, hys⟩ := hxc (V₀ ∩ O₁) (inter_mem hV₀ (hO₁open.mem_nhds hxO₁))
    exact ⟨y, hyV₀, by simpa only [s', interior_inter, hO₁open.interior_eq] using ⟨hys, hyO₁⟩⟩
  have hxtc' : (x, t) ∈ closure (interior (s' ×ˢ U')) := by
    rw [interior_prod_eq, hU'open.interior_eq, closure_prod_eq]
    exact ⟨hxc', subset_closure htU'⟩
  have hxt' : (x, t) ∈ s' ×ˢ U' := ⟨hxs', htU'⟩
  have hs'eq_at : ∀ y ∈ O₁, s' =ᶠ[𝓝 y] s := fun y hy ↦ by
    filter_upwards [hO₁open.mem_nhds hy] with z hz
    simp [s', hz]
  -- Pull `form` back to the product `s' ×ˢ U'`.
  let Ω : E × ℝ → (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] G :=
    fun q ↦ (form (P q)).compContinuousLinearMap (fderivWithin ℝ P (s' ×ˢ U') q)
  let contractInl : ((E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] G) →L[ℝ] E [⋀^Fin k]→L[ℝ] G :=
    compContinuousLinearMapCLM (.inl ℝ E ℝ) ∘L
      curryLeftFlipL (𝕜 := ℝ) (E := E × ℝ) (F := G) (n := k) (0, 1)
  have hdP : DifferentiableWithinAt ℝ P (s' ×ˢ U') (x, t) :=
    (hPon (x, t) hxt').differentiableWithinAt (by norm_num)
  have hd2P : DifferentiableWithinAt ℝ (fderivWithin ℝ P (s' ×ˢ U')) (s' ×ˢ U') (x, t) :=
    ((hPon (x, t) hxt').fderivWithin_right hWu (by norm_num) hxt').differentiableWithinAt
      one_ne_zero
  have hdΩ : DifferentiableWithinAt ℝ Ω (s' ×ˢ U') (x, t) :=
    (hform.comp (x, t) hdP hst').continuousAlternatingMapCompContinuousLinearMap hd2P
  set A := fderivWithin ℝ Ω (s' ×ˢ U') (x, t)
  -- Identify `contractInl (Ω (y, t))` with `familyContractionWithin` on `s'`.
  have hslice_eq : ∀ y ∈ s', contractInl (Ω (y, t)) = familyContractionWithin P s t form y := by
    intro y hy
    have hdPy : DifferentiableWithinAt ℝ P (s' ×ˢ U') (y, t) :=
      (hPon (y, t) ⟨hy, htU'⟩).differentiableWithinAt (by norm_num)
    simpa only [contractInl, Ω, ContinuousLinearMap.comp_apply, compContinuousLinearMapCLM_apply,
      curryLeftFlipL_apply_apply]
      using compContinuousLinearMap_inl_curryLeft_pullback_eq_familyContractionWithin
        (hs'eq_at y hy.2) (hs'u y hy) hy (hU'open.mem_nhds htU') hdPy form
  -- Compute `extDerivWithin (familyContractionWithin P s t form) s x` via `s'`.
  have hd_contr : extDerivWithin (familyContractionWithin P s t form) s x =
      alternatizeUncurryFin (contractInl ∘L A ∘L .inl ℝ E ℝ) := by
    have hev : (fun y ↦ contractInl (Ω (y, t))) =ᶠ[𝓝[s'] x]
        familyContractionWithin P s t form := by
      filter_upwards [self_mem_nhdsWithin] with y hy using hslice_eq y hy
    have hm_left : MapsTo (fun y ↦ (y, t)) s' (s' ×ˢ U') := fun _ hy ↦ ⟨hy, htU'⟩
    have hslice_d : HasFDerivWithinAt (fun y ↦ Ω (y, t)) (A ∘L .inl ℝ E ℝ) s' x := by
      simpa only [Function.comp_def] using
        hdΩ.hasFDerivWithinAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t).hasFDerivWithinAt
          hm_left
    have hfderiv_slice : fderivWithin ℝ (fun y ↦ contractInl (Ω (y, t))) s' x =
        contractInl ∘L (A ∘L .inl ℝ E ℝ) :=
      (contractInl.hasFDerivAt.comp_hasFDerivWithinAt x hslice_d).fderivWithin (hs'u x hxs')
    rw [← extDerivWithin_congr_set (hs'eq_at x hxO₁), ← hev.extDerivWithin_eq (hslice_eq x hxs'),
      extDerivWithin, hfderiv_slice, ContinuousLinearMap.comp_assoc]
  -- Compute `familyContractionWithin P s t (extDerivWithin form t_set) x` via pullback of `d form`.
  have hcontr_d : familyContractionWithin P s t (extDerivWithin form t_set) x =
      ((alternatizeUncurryFin A).curryLeft (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ) := by
    have hpull_d := extDerivWithin_pullback hform (hPon (x, t) hxt') (by norm_num)
      hWu hxtc' hxt' hst'
    dsimp only [A]
    rw [← extDerivWithin, hpull_d]
    exact (compContinuousLinearMap_inl_curryLeft_pullback_eq_familyContractionWithin
      (hs'eq_at x hxO₁) (hs'u x hxs') hxs' (hU'open.mem_nhds htU') hdP
      (extDerivWithin form t_set)).symm
  -- Combine both terms through the constant-coefficient Cartan identity for `(0, 1)`.
  have hcartan : extDerivWithin (familyContractionWithin P s t form) s x +
      familyContractionWithin P s t (extDerivWithin form t_set) x =
      (A (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ) := by
    have key := congrArg (compContinuousLinearMapCLM (.inl ℝ E ℝ))
      (alternatizeUncurryFin_curryLeft_comp_add_curryLeft A (0, 1))
    rw [map_add, compContinuousLinearMapCLM_apply, compContinuousLinearMapCLM_apply,
      compContinuousLinearMapCLM_apply, alternatizeUncurryFin_compContinuousLinearMap] at key
    rw [hd_contr, hcontr_d]
    simpa only [contractInl, ContinuousLinearMap.comp_assoc] using key
  rw [hcartan]
  -- Differentiate `u ↦ (Ω (x, u)).compContinuousLinearMap (.inl ℝ E ℝ)` at `t`.
  let C := compContinuousLinearMapCLM (𝕜 := ℝ) (F := G) (ι := Fin (k + 1)) (.inl ℝ E ℝ)
  have hderivΩ : HasDerivAt (fun u ↦ C (Ω (x, u))) (C (A (0, 1))) t := by
    have hw : HasDerivWithinAt (fun u ↦ Ω (x, u)) (A (0, 1)) U' t :=
      hasDerivWithinAt_slice_right hdΩ hxs'
    exact C.hasFDerivAt.comp_hasDerivAt t (hw.hasDerivAt (hU'open.mem_nhds htU'))
  refine hderivΩ.congr_of_eventuallyEq ?_
  filter_upwards [hU'open.mem_nhds htU'] with u hu
  have hdPu : DifferentiableWithinAt ℝ P (s' ×ˢ U') (x, u) :=
    (hPon (x, u) ⟨hxs', hu⟩).differentiableWithinAt (by norm_num)
  have hfderiv_s' : fderivWithin ℝ (fun y ↦ P (y, u)) s' x =
      fderivWithin ℝ (fun y ↦ P (y, u)) s x :=
    fderivWithin_inter (hO₁open.mem_nhds hxO₁)
  have hinl := fderivWithin_slice_left hdPu (hs'u x hxs') hu
  ext v
  simp only [C, Ω, compContinuousLinearMapCLM_apply, compContinuousLinearMap_apply, ← hfderiv_s',
    hinl, ContinuousLinearMap.coe_comp, Function.comp_assoc]

/-- **Differentiation of moving pullbacks within a set.** Let `P : E × ℝ → F` be `C²` within
`s ×ˢ U` at `(x, t)`, where `s` has unique derivatives with `x ∈ s ∩ closure (interior s)` and `U`
is an open neighbourhood of `t` in `ℝ`. If `P` maps `s ×ˢ U` into `t_set` near `(x, t)` and `form`
is differentiable within `t_set` at `P (x, t)`, then the pulled-back forms `pᵤ^* form` at `x` have
time derivative `d(C_(pₜ, Vₜ) form)ₓ + C_(pₜ, Vₜ)(d form)ₓ`. Neither completeness of `G` nor
invertibility of the slices `pᵤ` is required. -/
theorem hasDerivAt_compContinuousLinearMap_fderivWithin_family {r : WithTop ℕ∞}
    {P : E × ℝ → F} {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G}
    {s : Set E} {U : Set ℝ} {t_set : Set F} {x : E} {t : ℝ}
    (hs : UniqueDiffOn ℝ s) (hxc : x ∈ closure (interior s)) (hxs : x ∈ s)
    (hU : IsOpen U) (htU : t ∈ U)
    (hP : ContDiffWithinAt ℝ r P (s ×ˢ U) (x, t)) (hr : 2 ≤ r)
    (hmaps : P ⁻¹' t_set ∈ 𝓝[s ×ˢ U] (x, t))
    (hform : DifferentiableWithinAt ℝ form t_set (P (x, t))) :
    HasDerivAt
      (fun u ↦ (form (P (x, u))).compContinuousLinearMap
        (fderivWithin ℝ (fun y ↦ P (y, u)) s x))
      (extDerivWithin (familyContractionWithin P s t form) s x +
        familyContractionWithin P s t (extDerivWithin form t_set) x) t := by
  have hP2 : ContDiffWithinAt ℝ (2 : ℕ) P (s ×ˢ U) (x, t) := hP.of_le (by exact_mod_cast hr)
  -- Shrink to open rectangular neighbourhoods `O₁` of `x` and `O₂ ⊆ U` of `t` on which `P` is
  -- `C²` within `(s ∩ O₁) ×ˢ O₂` and maps into `t_set`.
  obtain ⟨W₀, hW₀open, hxW₀, hW₀maps⟩ := mem_nhdsWithin.mp hmaps
  obtain ⟨W₁, hW₁mem, -, hP2on⟩ := hP2.contDiffOn (le_refl (2 : WithTop ℕ∞)) (by simp)
  rw [insert_eq_of_mem (⟨hxs, htU⟩ : (x, t) ∈ s ×ˢ U)] at hW₁mem
  obtain ⟨W₂, hW₂open, hxW₂, hW₂sub⟩ := mem_nhdsWithin.mp hW₁mem
  obtain ⟨O₁, O₂, hO₁open, hO₂open, hxO₁, htO₂, hOprod⟩ :=
    isOpen_prod_iff.mp (hW₀open.inter (hW₂open.inter (isOpen_univ.prod hU))) x t
      ⟨hxW₀, hxW₂, mem_univ x, htU⟩
  have hsubSU : (s ∩ O₁) ×ˢ O₂ ⊆ s ×ˢ U :=
    prod_mono inter_subset_left fun u hu ↦ (@hOprod (x, u) ⟨hxO₁, hu⟩).2.2.2
  have hPon : ContDiffOn ℝ (2 : ℕ) P ((s ∩ O₁) ×ˢ O₂) :=
    hP2on.mono fun q hq ↦ hW₂sub ⟨(hOprod ⟨hq.1.2, hq.2⟩).2.1, hsubSU hq⟩
  have hst' : MapsTo P ((s ∩ O₁) ×ˢ O₂) t_set :=
    fun q hq ↦ hW₀maps ⟨(hOprod ⟨hq.1.2, hq.2⟩).1, hsubSU hq⟩
  exact hasDerivAt_compContinuousLinearMap_fderivWithin_family_of_contDiffOn hs hxc hxs
    hO₁open hxO₁ hO₂open htO₂ hPon hst' hform

/-- **Differentiation of moving pullbacks** on normed spaces:
`∂ₜ(pₜ^* form)ₓ = d(C_(pₜ, Vₜ) form)ₓ + C_(pₜ, Vₜ)(d form)ₓ`. Neither invertibility of the slices
`pₜ` nor completeness of `G` is required. -/
theorem hasDerivAt_compContinuousLinearMap_fderiv_family {r : WithTop ℕ∞}
    {P : E × ℝ → F} {form : F → F [⋀^Fin (k + 1)]→L[ℝ] G} {x : E} {t : ℝ}
    (hP : ContDiffAt ℝ r P (x, t)) (hr : 2 ≤ r)
    (hform : DifferentiableAt ℝ form (P (x, t))) :
    HasDerivAt
      (fun s ↦ (form (P (x, s))).compContinuousLinearMap
        (fderiv ℝ (fun y ↦ P (y, s)) x))
      (extDeriv (familyContraction P t form) x +
        familyContraction P t (extDeriv form) x) t := by
  have hP2 : ContDiffAt ℝ (2 : ℕ) P (x, t) := hP.of_le (by exact_mod_cast hr)
  have hevP : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ P (y, t) :=
    ((continuous_id.prodMk continuous_const).continuousAt.tendsto.eventually
      (hP2.eventually (by simp))).mono fun _ hy ↦ hy.differentiableAt (by norm_num)
  have hev_fam : familyContractionWithin P univ t form =ᶠ[𝓝 x] familyContraction P t form :=
    hevP.mono fun _ hy ↦ familyContractionWithin_univ_eq_of_differentiableAt hy form
  have hwithin := hasDerivAt_compContinuousLinearMap_fderivWithin_family
    (s := univ) (U := univ) (t_set := univ) uniqueDiffOn_univ
    (by simp) (mem_univ x) isOpen_univ (mem_univ t)
    (by simpa only [univ_prod_univ, contDiffWithinAt_univ] using hP) hr
    univ_mem hform.differentiableWithinAt
  simp only [fderivWithin_univ, extDerivWithin_univ] at hwithin
  rwa [hev_fam.extDeriv_eq,
    familyContractionWithin_univ_eq_of_differentiableAt (hP2.differentiableAt (by norm_num)) _]
    at hwithin

/-- **Differentiation of moving pullbacks in degree zero** within a set:
`∂ₜ(f ∘ pₜ)ₓ = C_(pₜ, Vₜ)(df)ₓ 0`. Only differentiability of `P` and `f` is needed. -/
theorem hasDerivAt_comp_familyContractionWithin_extDerivWithin
    {P : E × ℝ → F} {f : F → G} {s : Set E} {U : Set ℝ} {t_set : Set F} {x : E} {t : ℝ}
    (hxs : x ∈ s) (hU : IsOpen U) (htU : t ∈ U)
    (ht : UniqueDiffWithinAt ℝ t_set (P (x, t)))
    (hP : DifferentiableWithinAt ℝ P (s ×ˢ U) (x, t))
    (hmaps : P ⁻¹' t_set ∈ 𝓝[s ×ˢ U] (x, t))
    (hf : DifferentiableWithinAt ℝ f t_set (P (x, t))) :
    HasDerivAt (fun u ↦ f (P (x, u)))
      (familyContractionWithin P s t
        (extDerivWithin (fun y ↦ constOfIsEmpty ℝ F (Fin 0) (f y)) t_set) x 0) t := by
  obtain ⟨W₀, hW₀open, hxW₀, hW₀maps⟩ := mem_nhdsWithin.mp hmaps
  have hO : U ∩ (fun u ↦ (x, u)) ⁻¹' W₀ ∈ 𝓝 t :=
    Filter.inter_mem (hU.mem_nhds htU)
      (((continuous_const.prodMk continuous_id).continuousAt).preimage_mem_nhds
        (hW₀open.mem_nhds hxW₀))
  have hcurve : HasDerivWithinAt (fun u ↦ P (x, u))
      (fderivWithin ℝ P (s ×ˢ U) (x, t) (0, 1)) (U ∩ (fun u ↦ (x, u)) ⁻¹' W₀) t :=
    (hasDerivWithinAt_slice_right hP hxs).mono inter_subset_left
  have hcomp : HasDerivWithinAt (fun u ↦ f (P (x, u)))
      (fderivWithin ℝ f t_set (P (x, t)) (fderivWithin ℝ P (s ×ˢ U) (x, t) (0, 1)))
      (U ∩ (fun u ↦ (x, u)) ⁻¹' W₀) t :=
    hf.hasFDerivWithinAt.comp_hasDerivWithinAt t hcurve
      fun _ hu ↦ hW₀maps ⟨hu.2, hxs, hu.1⟩
  have hvel := fderivWithin_apply_mk_zero_one hP hxs (hU.mem_nhds htU)
  refine (hcomp.hasDerivAt hO).congr_deriv ?_
  rw [familyContractionWithin_apply, extDerivWithin_constOfIsEmpty f ht, hvel]
  simp

/-- **Differentiation of moving pullbacks in degree zero** on normed spaces:
`∂ₜ(f ∘ pₜ)ₓ = C_(pₜ, Vₜ)(df)ₓ 0`. -/
theorem hasDerivAt_comp_familyContraction_extDeriv
    {P : E × ℝ → F} {f : F → G} {x : E} {t : ℝ}
    (hP : DifferentiableAt ℝ P (x, t)) (hf : DifferentiableAt ℝ f (P (x, t))) :
    HasDerivAt (fun u ↦ f (P (x, u)))
      (familyContraction P t (extDeriv fun y ↦ constOfIsEmpty ℝ F (Fin 0) (f y)) x 0) t := by
  have h := hasDerivAt_comp_familyContractionWithin_extDerivWithin
    (s := univ) (U := univ) (t_set := univ) (mem_univ x) isOpen_univ (mem_univ t)
    uniqueDiffWithinAt_univ
    (by simpa only [univ_prod_univ, differentiableWithinAt_univ] using hP)
    univ_mem hf.differentiableWithinAt
  simpa only [extDerivWithin_univ,
    familyContractionWithin_univ_eq_of_differentiableAt hP _] using h

/-- Integrating `familyContraction P t form` over `t ∈ [0, 1]` agrees with the cylinder homotopy
operator `TauCeti.cylinderHomotopy` applied to the product pullback `P^* form`, assuming only
differentiability of `P` at `(x, t)` for `t ∈ (0, 1)`. -/
theorem intervalIntegral_familyContraction_eq_cylinderHomotopy
    {P : E × ℝ → F} {x : E} (hP : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ P (x, t))
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    (∫ t in (0 : ℝ)..1, familyContraction P t form x) =
      cylinderHomotopy (fun q ↦ (form (P q)).compContinuousLinearMap (fderiv ℝ P q)) x := by
  rw [cylinderHomotopy_apply]
  refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht ↦ ?_
  have hPt : DifferentiableAt ℝ P (x, t) := hP t ht
  rw [← familyContractionWithin_univ_eq_of_differentiableAt hPt form]
  simpa only [univ_prod_univ, fderivWithin_univ] using
    (compContinuousLinearMap_inl_curryLeft_pullback_eq_familyContractionWithin (s := univ)
      (s' := univ) (U' := univ) (Filter.Eventually.of_forall fun _ ↦ Iff.rfl)
      uniqueDiffWithinAt_univ (mem_univ x) univ_mem
      (by simpa only [univ_prod_univ, differentiableWithinAt_univ] using hPt) form).symm

end TauCeti
