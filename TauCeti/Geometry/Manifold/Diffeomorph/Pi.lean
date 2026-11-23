/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.IsManifold.Pi

/-!
# Diffeomorphisms of finite products and dimension-cast charted spaces

This file provides general manifold infrastructure for `Fin`-indexed finite products and
dimension-cast charted spaces:

* `TauCeti.castFinChartedSpace`, `TauCeti.castFinChartedSpace_isManifold`,
  `TauCeti.castFinDiffeomorph`: transporting a `Fin d₁ → 𝕜` charted-space structure, manifold
  structure, and identity diffeomorphism across a propositional dimension equality `d₁ = d₂`.
* `Diffeomorph.finOneDiffeomorph`: the canonical `C^n` diffeomorphism `Y ≃ₘ^n (Fin 1 → Y)`.
* `Diffeomorph.snocDiffeomorph`: the canonical `C^n` diffeomorphism
  `(Fin (k + 1) → Y) × Y ≃ₘ^n (Fin (k + 2) → Y)` via `Fin.snoc`.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

section CastFin

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X : Type*} [TopologicalSpace X] {d₁ d₂ : ℕ}

/-- Transport a charted-space structure along an equality of model dimensions. -/
@[instance_reducible]
def castFinChartedSpace (h : d₁ = d₂) (cs : ChartedSpace (Fin d₁ → 𝕜) X) :
    ChartedSpace (Fin d₂ → 𝕜) X :=
  h ▸ cs

/-- Transport an `IsManifold` structure along an equality of model dimensions. -/
theorem castFinChartedSpace_isManifold {n : ℕ∞ω} (h : d₁ = d₂) (cs : ChartedSpace (Fin d₁ → 𝕜) X)
    (hM : letI := cs; IsManifold 𝓘(𝕜, Fin d₁ → 𝕜) n X) :
    letI := castFinChartedSpace h cs
    IsManifold 𝓘(𝕜, Fin d₂ → 𝕜) n X := by
  subst h
  exact hM

/-- The identity map as a `C^n` diffeomorphism between a charted space and its dimension-cast
copy. -/
noncomputable def castFinDiffeomorph {n : ℕ∞ω} (h : d₁ = d₂) (cs : ChartedSpace (Fin d₁ → 𝕜) X) :
    letI := cs
    letI : ChartedSpace (Fin d₂ → 𝕜) X := castFinChartedSpace h cs
    X ≃ₘ^n⟮𝓘(𝕜, Fin d₁ → 𝕜), 𝓘(𝕜, Fin d₂ → 𝕜)⟯ X := by
  subst h
  letI := cs
  exact Diffeomorph.refl 𝓘(𝕜, Fin d₁ → 𝕜) X n

/-- The dimension-cast diffeomorphism acts as the identity. -/
@[simp]
theorem castFinDiffeomorph_apply {n : ℕ∞ω} (h : d₁ = d₂) (cs : ChartedSpace (Fin d₁ → 𝕜) X)
    (x : X) :
    castFinDiffeomorph (n := n) h cs x = x := by
  subst h
  rfl

/-- The inverse of the dimension-cast diffeomorphism acts as the identity. -/
@[simp]
theorem castFinDiffeomorph_symm_apply {n : ℕ∞ω} (h : d₁ = d₂) (cs : ChartedSpace (Fin d₁ → 𝕜) X)
    (x : X) :
    letI := cs
    letI : ChartedSpace (Fin d₂ → 𝕜) X := castFinChartedSpace h cs
    (castFinDiffeomorph (n := n) h cs).symm x = x := by
  subst h
  rfl

end CastFin

end TauCeti

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] {n : ℕ∞ω}

/-- Canonical `C^n` diffeomorphism `Y ≃ₘ^n (Fin 1 → Y)` sending `y` to `fun _ ↦ y`. -/
def finOneDiffeomorph : Y ≃ₘ^n⟮I, ModelWithCorners.pi (fun _ : Fin 1 ↦ I)⟯ (Fin 1 → Y) where
  toFun y := fun _ ↦ y
  invFun w := w 0
  left_inv _ := rfl
  right_inv w := funext fun i ↦ congrArg w (Subsingleton.elim 0 i)
  contMDiff_toFun := contMDiff_pi_iff.2 fun _ ↦ contMDiff_id
  contMDiff_invFun := contMDiff_apply

/-- Applying `finOneDiffeomorph` gives the constant `Fin 1`-tuple. -/
@[simp]
theorem finOneDiffeomorph_apply (y : Y) :
    finOneDiffeomorph (I := I) (n := n) y = fun _ ↦ y := (rfl)

/-- The inverse of `finOneDiffeomorph` evaluates at index `0`. -/
@[simp]
theorem finOneDiffeomorph_symm_apply (w : Fin 1 → Y) :
    (finOneDiffeomorph (I := I) (n := n)).symm w = w 0 := (rfl)

/-- Canonical `C^n` diffeomorphism `(Fin (k + 1) → Y) × Y ≃ₘ^n (Fin (k + 2) → Y)` via
`Fin.snoc`. -/
def snocDiffeomorph (k : ℕ) :
    ((Fin (k + 1) → Y) × Y) ≃ₘ^n⟮
      (ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ I)).prod I,
      ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ I)⟯ (Fin (k + 2) → Y) where
  toFun p := Fin.snoc p.1 p.2
  invFun w := (Fin.init w, w (Fin.last (k + 1)))
  left_inv p := Prod.ext (by simp) (by simp)
  right_inv w := Fin.snoc_init_self w
  contMDiff_toFun := by
    refine contMDiff_pi_iff.2 fun i ↦ ?_
    refine Fin.lastCases
      (motive := fun i ↦ ContMDiff ((ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ I)).prod I)
        I n (fun p : (Fin (k + 1) → Y) × Y ↦ Fin.snoc (α := fun _ ↦ Y) p.1 p.2 i)) ?_ ?_ i
    · simp only [Fin.snoc_last]
      exact contMDiff_snd
    · intro j
      simp only [Fin.snoc_castSucc]
      exact (contMDiff_apply (i := j)).comp contMDiff_fst
  contMDiff_invFun :=
    (contMDiff_pi_iff.2 fun j ↦ contMDiff_apply (i := j.castSucc)).prodMk
      (contMDiff_apply (i := Fin.last (k + 1)))

/-- Applying `snocDiffeomorph` appends the second factor with `Fin.snoc`. -/
@[simp]
theorem snocDiffeomorph_apply (k : ℕ) (p : (Fin (k + 1) → Y) × Y) :
    snocDiffeomorph (I := I) (n := n) k p = Fin.snoc p.1 p.2 := (rfl)

/-- The inverse of `snocDiffeomorph` splits into `Fin.init` and the last coordinate. -/
@[simp]
theorem snocDiffeomorph_symm_apply (k : ℕ) (w : Fin (k + 2) → Y) :
    (snocDiffeomorph (I := I) (n := n) k).symm w = (Fin.init w, w (Fin.last (k + 1))) := (rfl)

end Diffeomorph
