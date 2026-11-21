/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# Separation of real spectral sets for partial operators

For partial linear maps on real or complex inner product spaces, `realSpectrum`
selects the real points of the partial-operator spectrum. `SpectralSetsSeparated`
records a uniform lower bound on distances between selected real spectral
sets, allowing different operators and underlying spaces.

Separation is symmetric, remains valid with a weaker distance bound, and is
preserved when either selected set is restricted. These properties provide
hypotheses for perturbation bounds between spectral subspaces.

Adapted from the Kitware DKPS formalization,
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean`.
-/

public section

namespace LinearPMap

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The real points of a partial linear map's spectrum, viewed as a subset of `ℝ`. -/
def realSpectrum (A : E →ₗ.[𝕜] E) : Set ℝ :=
  (fun x : ℝ => (x : 𝕜)) ⁻¹' A.spectrum

/-- A real scalar is in `realSpectrum` exactly when its image in the scalar field
belongs to the partial-operator spectrum. -/
@[simp] theorem mem_realSpectrum_iff {A : E →ₗ.[𝕜] E} {a : ℝ} :
    a ∈ realSpectrum A ↔ (a : 𝕜) ∈ A.spectrum :=
  Iff.rfl

/-- A uniform lower bound on the distance between selected parts of the real
spectra of two partial linear maps. A strictly positive bound witnesses
spectral separation. -/
def SpectralSetsSeparated (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (s t : Set ℝ) (d : ℝ) : Prop :=
  ∀ a ∈ realSpectrum A, a ∈ s →
    ∀ b ∈ realSpectrum B, b ∈ t → d ≤ |a - b|

/-- Characterization of separation by a distance bound on every selected
pair of real spectral points. -/
theorem spectralSetsSeparated_iff
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {s t : Set ℝ} {d : ℝ} :
    SpectralSetsSeparated A B s t d ↔
      ∀ a ∈ realSpectrum A, a ∈ s →
        ∀ b ∈ realSpectrum B, b ∈ t → d ≤ |a - b| :=
  Iff.rfl

/-- Establish spectral-set separation from a uniform distance bound. -/
theorem SpectralSetsSeparated.of_forall
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {s t : Set ℝ} {d : ℝ}
    (h : ∀ a ∈ realSpectrum A, a ∈ s →
      ∀ b ∈ realSpectrum B, b ∈ t → d ≤ |a - b|) :
    SpectralSetsSeparated A B s t d :=
  spectralSetsSeparated_iff.mpr h

/-- Extract the separation bound for two selected real spectral points. -/
theorem SpectralSetsSeparated.bound
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {s t : Set ℝ} {d : ℝ}
    (h : SpectralSetsSeparated A B s t d)
    {a b : ℝ} (ha : a ∈ realSpectrum A) (has : a ∈ s)
    (hb : b ∈ realSpectrum B) (hbt : b ∈ t) :
    d ≤ |a - b| :=
  (spectralSetsSeparated_iff.mp h) a ha has b hb hbt

/-- Exchanging both operators and their selected spectral sets preserves
spectral separation. -/
theorem SpectralSetsSeparated.symm
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {s t : Set ℝ} {d : ℝ}
    (h : SpectralSetsSeparated A B s t d) :
    SpectralSetsSeparated B A t s d := by
  apply SpectralSetsSeparated.of_forall
  intro b hb ht a ha hs
  simpa [abs_sub_comm] using h.bound ha hs hb ht

/-- A smaller lower bound still separates the selected spectral sets. -/
theorem SpectralSetsSeparated.mono_gap
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {s t : Set ℝ} {d e : ℝ}
    (h : SpectralSetsSeparated A B s t d) (hed : e ≤ d) :
    SpectralSetsSeparated A B s t e := by
  apply SpectralSetsSeparated.of_forall
  intro a ha hs b hb ht
  exact hed.trans (h.bound ha hs hb ht)

/-- Restricting either selected real spectral set preserves separation. -/
theorem SpectralSetsSeparated.mono_sets
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {s s' t t' : Set ℝ} {d : ℝ}
    (h : SpectralSetsSeparated A B s t d)
    (hs : s' ⊆ s) (ht : t' ⊆ t) :
    SpectralSetsSeparated A B s' t' d := by
  apply SpectralSetsSeparated.of_forall
  intro a ha has' b hb hbt'
  exact h.bound ha (hs has') hb (ht hbt')

end LinearPMap
