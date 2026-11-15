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
import TauCeti.Analysis.Calculus.DifferentialForm.Pullback
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
* `TauCeti.contractionAlongMap_comp_right`, `TauCeti.contractionAlongMap_compContinuousLinearMap`:
  naturality under precomposition on the source and pullback on the target.
* `ContDiffWithinAt.contractionAlongMapWithin`, `ContDiff.contractionAlongMap`: `C^m` regularity.
* `TauCeti.familyContractionWithin`, `TauCeti.familyContraction`: contraction of a form along a
  one-parameter family `P : E × ℝ → F` and its time velocity.
* `TauCeti.hasDerivAt_compContinuousLinearMap_fderivWithin_family`,
  `TauCeti.hasDerivAt_compContinuousLinearMap_fderiv_family`: differentiation of moving pullbacks
  within a set and on the whole space.
* `TauCeti.hasDerivAt_comp_eq_familyContraction_extDeriv`: the degree-zero specialization
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

/-- **Source naturality.** Precomposing `(p, V)` with a differentiable map `h : E' → E` pulls back
the contraction along `h`. -/
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
theorem contractionAlongMapWithin_compContinuousLinearMap {p : E → F} {q : F → F'} {V : E → F}
    {η : F' → F' [⋀^Fin (k + 1)]→L[ℝ] G} {s : Set E} {t : Set F} {x : E}
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
theorem contractionAlongMap_compContinuousLinearMap {p : E → F} {q : F → F'} {V : E → F}
    {η : F' → F' [⋀^Fin (k + 1)]→L[ℝ] G} {x : E}
    (hp : DifferentiableAt ℝ p x) (hq : DifferentiableAt ℝ q (p x)) :
    contractionAlongMap p V
        (fun y ↦ (η (q y)).compContinuousLinearMap (fderiv ℝ q y)) x =
      contractionAlongMap (q ∘ p) (fun y ↦ fderiv ℝ q (p y) (V y)) η x := by
  simpa only [contractionAlongMapWithin_univ, fderivWithin_univ] using
    contractionAlongMapWithin_compContinuousLinearMap (s := univ) (t := univ) (V := V) (η := η)
      hp.differentiableWithinAt hq.differentiableWithinAt (mapsTo_univ _ _) uniqueDiffWithinAt_univ

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
  change ContDiffWithinAt ℝ m
    (fun y ↦ ((form (p y)).curryLeft (V y)).compContinuousLinearMap (fderivWithin ℝ p s y)) s x
  simpa only [Function.comp_def, compContinuousLinearMapCLM_apply]
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

theorem familyContractionWithin_univ_eq_of_differentiableAt {P : E × ℝ → F} {t : ℝ} {x : E}
    (hP : DifferentiableAt ℝ P (x, t)) (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    familyContractionWithin P univ t form x = familyContraction P t form x := by
  have hvel : deriv (fun u ↦ P (x, u)) t = fderiv ℝ P (x, t) (0, 1) :=
    (hP.hasFDerivAt.comp_hasDerivAt t (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t).hasDerivAt).deriv
  ext v
  simp [familyContractionWithin_apply, familyContraction_apply, hvel]

private theorem fderivWithin_prod_comp_inl {P : E × ℝ → F} {s : Set E} {U : Set ℝ}
    {y : E} {u : ℝ} (hs : UniqueDiffWithinAt ℝ s y) (hu : u ∈ U)
    (hP : DifferentiableWithinAt ℝ P (s ×ˢ U) (y, u)) :
    fderivWithin ℝ P (s ×ˢ U) (y, u) ∘L .inl ℝ E ℝ =
      fderivWithin ℝ (fun z ↦ P (z, u)) s y := by
  symm
  have hm : MapsTo (fun z ↦ (z, u)) s (s ×ˢ U) := fun _ hz ↦ ⟨hz, hu⟩
  exact (hP.hasFDerivWithinAt.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y u).hasFDerivWithinAt
    hm).fderivWithin hs

private theorem fderivWithin_prod_zero_one {P : E × ℝ → F} {s : Set E} {U : Set ℝ}
    {y : E} {u : ℝ} (hy : y ∈ s) (hU : IsOpen U) (hu : u ∈ U)
    (hP : DifferentiableWithinAt ℝ P (s ×ˢ U) (y, u)) :
    fderivWithin ℝ P (s ×ˢ U) (y, u) (0, 1) = deriv (fun w ↦ P (y, w)) u := by
  symm
  have hw : HasDerivWithinAt (fun w ↦ P (y, w))
      (fderivWithin ℝ P (s ×ˢ U) (y, u) (0, 1)) U u :=
    hP.hasFDerivWithinAt.comp_hasDerivWithinAt u
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) y u).hasDerivAt.hasDerivWithinAt
      (fun _ hw ↦ ⟨hy, hw⟩)
  exact (hw.hasDerivAt (hU.mem_nhds hu)).deriv

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
  obtain ⟨W₁, hW₁mem, hW₁sub, hP2on⟩ :=
    hP2.contDiffOn (le_refl (2 : WithTop ℕ∞)) (by simp)
  have hxt_mem : (x, t) ∈ s ×ˢ U := ⟨hxs, htU⟩
  rw [insert_eq_of_mem hxt_mem] at hW₁mem hW₁sub
  obtain ⟨W₂, hW₂open, hxW₂, hW₂sub⟩ := mem_nhdsWithin.mp hW₁mem
  obtain ⟨O₁, O₂, hO₁open, hO₂open, hxO₁, htO₂, hOprod⟩ :=
    isOpen_prod_iff.mp (hW₀open.inter (hW₂open.inter (isOpen_univ.prod hU))) x t
      ⟨hxW₀, hxW₂, mem_univ x, htU⟩
  set s' := s ∩ O₁
  set U' := O₂
  have hU'sub : U' ⊆ U := fun u hu ↦ (@hOprod (x, u) ⟨hxO₁, hu⟩).2.2.2
  have htU' : t ∈ U' := htO₂
  have hxs' : x ∈ s' := ⟨hxs, hxO₁⟩
  have hs'u : UniqueDiffOn ℝ s' := hs.inter hO₁open
  have hWu : UniqueDiffOn ℝ (s' ×ˢ U') := UniqueDiffOn.prod hs'u hO₂open.uniqueDiffOn
  have hsubSU : s' ×ˢ U' ⊆ s ×ˢ U := prod_mono inter_subset_left hU'sub
  have hsubW₁ : s' ×ˢ U' ⊆ W₁ := fun q hq ↦
    hW₂sub ⟨(hOprod ⟨hq.1.2, hq.2⟩).2.1, hsubSU hq⟩
  have hPon : ContDiffOn ℝ (2 : ℕ) P (s' ×ˢ U') := hP2on.mono hsubW₁
  have hst' : MapsTo P (s' ×ˢ U') t_set := fun q hq ↦
    hW₀maps ⟨(hOprod ⟨hq.1.2, hq.2⟩).1, hsubSU hq⟩
  have hxc' : x ∈ closure (interior s') := by
    rw [mem_closure_iff_nhds] at hxc ⊢
    intro V₀ hV₀
    obtain ⟨y, ⟨hyV₀, hyO₁⟩, hys⟩ := hxc (V₀ ∩ O₁) (inter_mem hV₀ (hO₁open.mem_nhds hxO₁))
    exact ⟨y, hyV₀, by simpa only [s', interior_inter, hO₁open.interior_eq] using ⟨hys, hyO₁⟩⟩
  have hxtc' : (x, t) ∈ closure (interior (s' ×ˢ U')) := by
    rw [interior_prod_eq, hO₂open.interior_eq, closure_prod_eq]
    exact ⟨hxc', subset_closure htU'⟩
  have hxt' : (x, t) ∈ s' ×ˢ U' := ⟨hxs', htU'⟩
  -- Pull `form` back to the product `s' ×ˢ U'`.
  let Ω : E × ℝ → (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] G :=
    fun q ↦ (form (P q)).compContinuousLinearMap (fderivWithin ℝ P (s' ×ˢ U') q)
  let contractInl : ((E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] G) →L[ℝ] E [⋀^Fin k]→L[ℝ] G :=
    compContinuousLinearMapCLM (.inl ℝ E ℝ) ∘L
      (curryLeftLI (𝕜 := ℝ) (E := E × ℝ) (F := G) (n := k)).toContinuousLinearMap.flip (0, 1)
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
    have hyt' : (y, t) ∈ s' ×ˢ U' := ⟨hy, htU'⟩
    have hdPy : DifferentiableWithinAt ℝ P (s' ×ˢ U') (y, t) :=
      (hPon (y, t) hyt').differentiableWithinAt (by norm_num)
    have hfderiv_s' : fderivWithin ℝ (fun z ↦ P (z, t)) s' y =
        fderivWithin ℝ (fun z ↦ P (z, t)) s y :=
      fderivWithin_inter (hO₁open.mem_nhds hy.2)
    have hinl := fderivWithin_prod_comp_inl (hs'u y hy) htU' hdPy
    have hvel := fderivWithin_prod_zero_one hy hO₂open htU' hdPy
    ext v
    change Ω (y, t) (Matrix.vecCons (0, 1) fun i ↦ (v i, 0)) = _
    rw [familyContractionWithin_apply, ← hfderiv_s', ← hinl, ← hvel]
    simp only [Ω, compContinuousLinearMap_apply]
    congr 1
    funext i
    cases i using Fin.cases <;> rfl
  -- Compute `extDerivWithin (familyContractionWithin P s t form) s x` via `s'`.
  have hs'eq : s' =ᶠ[𝓝 x] s := by
    filter_upwards [hO₁open.mem_nhds hxO₁] with y hy
    simp [s', hy]
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
    rw [← extDerivWithin_congr_set hs'eq, ← hev.extDerivWithin_eq (hslice_eq x hxs'),
      extDerivWithin, hfderiv_slice, ContinuousLinearMap.comp_assoc]
  -- Compute `familyContractionWithin P s t (extDerivWithin form t_set) x` via pullback of `d form`.
  have hcontr_d : familyContractionWithin P s t (extDerivWithin form t_set) x =
      ((alternatizeUncurryFin A).curryLeft (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ) := by
    have hpull_d := extDerivWithin_pullback hform (hPon (x, t) hxt') (by norm_num)
      hWu hxtc' hxt' hst'
    change _ = ((extDerivWithin Ω (s' ×ˢ U') (x, t)).curryLeft (0, 1)).compContinuousLinearMap
      (.inl ℝ E ℝ)
    rw [hpull_d]
    have hfderiv_s' : fderivWithin ℝ (fun z ↦ P (z, t)) s' x =
        fderivWithin ℝ (fun z ↦ P (z, t)) s x :=
      fderivWithin_inter (hO₁open.mem_nhds hxO₁)
    have hinl := fderivWithin_prod_comp_inl (hs'u x hxs') htU' hdP
    have hvel := fderivWithin_prod_zero_one hxs' hO₂open htU' hdP
    ext v
    change _ = (extDerivWithin form t_set (P (x, t))).compContinuousLinearMap
      (fderivWithin ℝ P (s' ×ˢ U') (x, t)) (Matrix.vecCons (0, 1) fun i ↦ (v i, 0))
    rw [familyContractionWithin_apply, ← hfderiv_s', ← hinl, ← hvel,
      compContinuousLinearMap_apply]
    congr 1
    funext i
    cases i using Fin.cases <;> rfl
  -- Combine both terms through the constant-coefficient Cartan identity for `(0, 1)`.
  have hcartan : extDerivWithin (familyContractionWithin P s t form) s x +
      familyContractionWithin P s t (extDerivWithin form t_set) x =
      (A (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ) := by
    have key := congrArg (compContinuousLinearMapCLM (.inl ℝ E ℝ))
      (alternatizeUncurryFin_curryLeft_comp_add_curryLeft A (0, 1))
    rw [map_add, compContinuousLinearMapCLM_apply, compContinuousLinearMapCLM_apply,
      compContinuousLinearMapCLM_apply, alternatizeUncurryFin_compContinuousLinearMap] at key
    rw [hd_contr, hcontr_d]
    exact key
  rw [hcartan]
  -- Differentiate `u ↦ (Ω (x, u)).compContinuousLinearMap (.inl ℝ E ℝ)` at `t`.
  let C := compContinuousLinearMapCLM (𝕜 := ℝ) (F := G) (ι := Fin (k + 1)) (.inl ℝ E ℝ)
  have hderivΩ : HasDerivAt (fun u ↦ C (Ω (x, u))) (C (A (0, 1))) t := by
    have hm_right : MapsTo (fun u ↦ (x, u)) U' (s' ×ˢ U') := fun _ hu ↦ ⟨hxs', hu⟩
    have hw : HasDerivWithinAt (fun u ↦ Ω (x, u)) (A (0, 1)) U' t :=
      hdΩ.hasFDerivWithinAt.comp_hasDerivWithinAt t
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t).hasDerivAt.hasDerivWithinAt hm_right
    exact C.hasFDerivAt.comp_hasDerivAt t (hw.hasDerivAt (hO₂open.mem_nhds htU'))
  refine hderivΩ.congr_of_eventuallyEq ?_
  filter_upwards [hO₂open.mem_nhds htU'] with u hu
  have hxu' : (x, u) ∈ s' ×ˢ U' := ⟨hxs', hu⟩
  have hdPu : DifferentiableWithinAt ℝ P (s' ×ˢ U') (x, u) :=
    (hPon (x, u) hxu').differentiableWithinAt (by norm_num)
  have hfderiv_s' : fderivWithin ℝ (fun y ↦ P (y, u)) s' x =
      fderivWithin ℝ (fun y ↦ P (y, u)) s x :=
    fderivWithin_inter (hO₁open.mem_nhds hxO₁)
  have hinl := fderivWithin_prod_comp_inl (hs'u x hxs') hu hdPu
  ext v
  simp only [C, Ω, compContinuousLinearMapCLM_apply, compContinuousLinearMap_apply, ← hfderiv_s',
    ← hinl, ContinuousLinearMap.coe_comp, Function.comp_assoc]

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
theorem hasDerivAt_comp_eq_familyContractionWithin_extDerivWithin
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
    hP.hasFDerivWithinAt.comp_hasDerivWithinAt t
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t).hasDerivAt.hasDerivWithinAt
      fun _ hu ↦ ⟨hxs, hu.1⟩
  have hcomp : HasDerivWithinAt (fun u ↦ f (P (x, u)))
      (fderivWithin ℝ f t_set (P (x, t)) (fderivWithin ℝ P (s ×ˢ U) (x, t) (0, 1)))
      (U ∩ (fun u ↦ (x, u)) ⁻¹' W₀) t :=
    hf.hasFDerivWithinAt.comp_hasDerivWithinAt t hcurve
      fun _ hu ↦ hW₀maps ⟨hu.2, hxs, hu.1⟩
  have hvel := fderivWithin_prod_zero_one hxs hU htU hP
  refine (hcomp.hasDerivAt hO).congr_deriv ?_
  rw [familyContractionWithin_apply, extDerivWithin_constOfIsEmpty f ht, hvel]
  simp

/-- **Differentiation of moving pullbacks in degree zero** on normed spaces:
`∂ₜ(f ∘ pₜ)ₓ = C_(pₜ, Vₜ)(df)ₓ 0`. -/
theorem hasDerivAt_comp_eq_familyContraction_extDeriv
    {P : E × ℝ → F} {f : F → G} {x : E} {t : ℝ}
    (hP : DifferentiableAt ℝ P (x, t)) (hf : DifferentiableAt ℝ f (P (x, t))) :
    HasDerivAt (fun u ↦ f (P (x, u)))
      (familyContraction P t (extDeriv fun y ↦ constOfIsEmpty ℝ F (Fin 0) (f y)) x 0) t := by
  have h := hasDerivAt_comp_eq_familyContractionWithin_extDerivWithin
    (s := univ) (U := univ) (t_set := univ) (mem_univ x) isOpen_univ (mem_univ t)
    uniqueDiffWithinAt_univ
    (by simpa only [univ_prod_univ, differentiableWithinAt_univ] using hP)
    univ_mem hf.differentiableWithinAt
  simpa only [extDerivWithin_univ,
    familyContractionWithin_univ_eq_of_differentiableAt hP _] using h

/-- Integrating `familyContraction P t form` over `t ∈ [0, 1]` agrees with the cylinder homotopy
operator `TauCeti.cylinderHomotopy` applied to the product pullback `P^* form`. -/
theorem intervalIntegral_familyContraction_eq_cylinderHomotopy
    {P : E × ℝ → F} {x : E} (hP : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ P (x, t))
    (form : F → F [⋀^Fin (k + 1)]→L[ℝ] G) :
    (∫ t in (0 : ℝ)..1, familyContraction P t form x) =
      cylinderHomotopy (fun q ↦ (form (P q)).compContinuousLinearMap (fderiv ℝ P q)) x := by
  rw [cylinderHomotopy_apply]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  have hinl : fderiv ℝ P (x, t) ∘L .inl ℝ E ℝ = fderiv ℝ (fun y ↦ P (y, t)) x := by
    simpa only [univ_prod_univ, fderivWithin_univ] using
      fderivWithin_prod_comp_inl (s := univ) (U := univ) uniqueDiffWithinAt_univ (mem_univ t)
        (by simpa only [univ_prod_univ, differentiableWithinAt_univ] using hP t ht)
  ext v
  simp only [familyContraction_apply, compContinuousLinearMap_apply, curryLeft_apply_apply,
    ← hinl, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

end TauCeti
