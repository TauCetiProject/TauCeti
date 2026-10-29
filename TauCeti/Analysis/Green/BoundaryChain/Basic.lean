/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoxIntegral.IntervalIntegral
public import Mathlib.Topology.Path
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Integer chains of planar paths

An arc is an existing `Path` with its endpoints retained. Chains are finitely supported
integer coefficients on these arcs. The endpoint boundary is terminal minus initial endpoint.
The coordinate integral is the integer-linear extension of the actual Henstock integral.
`Integrable` records genuine gauge integrability on every arc with nonzero coefficient.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- Existing planar paths, with their endpoints. -/
abbrev Arc := Σ p : ℂ, Σ q : ℂ, Path p q

/-- Finite integer-weighted sums of parameterized planar arcs. -/
abbrev BoundaryChain := Arc →₀ ℤ

namespace BoundaryChain

/-- A path with coefficient one. -/
def ofPath {p q : ℂ} (γ : Path p q) : BoundaryChain := Finsupp.single ⟨p, q, γ⟩ 1

/-- A path generator is the singleton coefficient function on its endpoint-indexed path. -/
theorem ofPath_def {p q : ℂ} (γ : Path p q) :
    ofPath γ = Finsupp.single ⟨p, q, γ⟩ 1 := (rfl)

/-- Pointwise equal paths give the same generator, even when their endpoint indices differ. -/
theorem ofPath_congr {p q p' q' : ℂ} (γ : Path p q) (δ : Path p' q')
    (h : ∀ t, γ t = δ t) : ofPath γ = ofPath δ := by
  have hp : p = p' := by simpa using h 0
  have hq : q = q' := by simpa using h 1
  subst p'
  subst q'
  congr 1
  exact Path.ext (funext h)

@[simp]
theorem support_ofPath {p q : ℂ} (γ : Path p q) :
    (ofPath γ).support = {⟨p, q, γ⟩} := by
  simp [ofPath]

/-- The endpoint boundary of a chain: terminal endpoint minus initial endpoint. -/
def boundary : BoundaryChain →ₗ[ℤ] (ℂ →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun γ : Arc ↦ Finsupp.single γ.2.1 1 - Finsupp.single γ.1 1)

/-- The endpoint boundary is the finite weighted sum of the endpoint differences. -/
theorem boundary_apply (c : BoundaryChain) :
    boundary c = c.sum (fun γ n ↦ n • (Finsupp.single γ.2.1 1 - Finsupp.single γ.1 1)) :=
  Finsupp.linearCombination_apply ℤ c

@[simp]
theorem boundary_ofPath {p q : ℂ} (γ : Path p q) :
    boundary (ofPath γ) = Finsupp.single q 1 - Finsupp.single p 1 := by
  simp [boundary, ofPath]

/-- Four edges with the lower and right edges positive and the upper and left edges negative. -/
def quadrilateral {p₀ p₁ p₂ p₃ : ℂ}
    (bottom : Path p₀ p₁) (right : Path p₁ p₂) (top : Path p₃ p₂) (left : Path p₀ p₃) :
    BoundaryChain := ofPath bottom + ofPath right - ofPath top - ofPath left

/-- The four signed edges of a quadrilateral. -/
theorem quadrilateral_def {p₀ p₁ p₂ p₃ : ℂ}
    (bottom : Path p₀ p₁) (right : Path p₁ p₂) (top : Path p₃ p₂) (left : Path p₀ p₃) :
    quadrilateral bottom right top left = ofPath bottom + ofPath right - ofPath top -
      ofPath left := (rfl)

/-- Every such four-edge boundary is an endpoint cycle, including degenerate edges. -/
@[simp]
theorem boundary_quadrilateral {p₀ p₁ p₂ p₃ : ℂ}
    (bottom : Path p₀ p₁) (right : Path p₁ p₂) (top : Path p₃ p₂) (left : Path p₀ p₃) :
    boundary (quadrilateral bottom right top left) = 0 := by
  simp only [quadrilateral, map_sub, map_add, boundary_ofPath]
  abel

/-- Gauge integral of a coordinate one-form along one arc. -/
def arcIntegral (L : ℂ →L[ℝ] ℝ) (P : ℂ → ℝ) (γ : Arc) : ℝ :=
  BoxIntegral.integral (TauCeti.BoxIntegral.intervalBox 0 1 zero_lt_one)
    BoxIntegral.IntegrationParams.Henstock
    (fun t ↦ P (γ.2.2.extend (t 0)) * L (deriv γ.2.2.extend (t 0)))
    BoxIntegral.BoxAdditiveMap.volume

/-- The arc integral uses the canonical constant extension of the existing path. -/
theorem arcIntegral_def (L : ℂ →L[ℝ] ℝ) (P : ℂ → ℝ) (γ : Arc) :
    arcIntegral L P γ = BoxIntegral.integral (TauCeti.BoxIntegral.intervalBox 0 1 zero_lt_one)
      BoxIntegral.IntegrationParams.Henstock
      (fun t ↦ P (γ.2.2.extend (t 0)) * L (deriv γ.2.2.extend (t 0)))
      BoxIntegral.BoxAdditiveMap.volume := (rfl)

/-- Integer-linear extension of the gauge coordinate integral to finite chains. -/
def integral (L : ℂ →L[ℝ] ℝ) (P : ℂ → ℝ) : BoundaryChain →ₗ[ℤ] ℝ :=
  Finsupp.linearCombination ℤ (arcIntegral L P)

/-- Evaluation of the chain integral as a finite integer-weighted sum. -/
theorem integral_apply (L : ℂ →L[ℝ] ℝ) (P : ℂ → ℝ) (c : BoundaryChain) :
    integral L P c = c.sum (fun γ n ↦ n • arcIntegral L P γ) :=
  Finsupp.linearCombination_apply ℤ c

@[simp]
theorem integral_ofPath (L : ℂ →L[ℝ] ℝ) (P : ℂ → ℝ) {p q : ℂ} (γ : Path p q) :
    integral L P (ofPath γ) = arcIntegral L P ⟨p, q, γ⟩ := by
  simp [integral, ofPath]

/-- Every nonzero arc coefficient has an actual Henstock-integrable coordinate integrand. -/
def Integrable (L : ℂ →L[ℝ] ℝ) (P : ℂ → ℝ) (c : BoundaryChain) : Prop :=
  ∀ γ ∈ c.support, BoxIntegral.Integrable (TauCeti.BoxIntegral.intervalBox 0 1 zero_lt_one)
    BoxIntegral.IntegrationParams.Henstock
    (fun t ↦ P (γ.2.2.extend (t 0)) * L (deriv γ.2.2.extend (t 0)))
    BoxIntegral.BoxAdditiveMap.volume

/-- Integrability is checked exactly on the finite support of a chain. -/
theorem integrable_iff (L : ℂ →L[ℝ] ℝ) (P : ℂ → ℝ) (c : BoundaryChain) :
    Integrable L P c ↔ ∀ γ ∈ c.support,
      BoxIntegral.Integrable (TauCeti.BoxIntegral.intervalBox 0 1 zero_lt_one)
        BoxIntegral.IntegrationParams.Henstock
        (fun t ↦ P (γ.2.2.extend (t 0)) * L (deriv γ.2.2.extend (t 0)))
        BoxIntegral.BoxAdditiveMap.volume := Iff.rfl

@[simp]
theorem integrable_zero (L : ℂ →L[ℝ] ℝ) (P : ℂ → ℝ) : Integrable L P 0 := by
  simp [Integrable]

@[simp]
theorem integrable_ofPath_iff (L : ℂ →L[ℝ] ℝ) (P : ℂ → ℝ) {p q : ℂ} (γ : Path p q) :
    Integrable L P (ofPath γ) ↔
      BoxIntegral.Integrable (TauCeti.BoxIntegral.intervalBox 0 1 zero_lt_one)
        BoxIntegral.IntegrationParams.Henstock
        (fun t ↦ P (γ.extend (t 0)) * L (deriv γ.extend (t 0)))
        BoxIntegral.BoxAdditiveMap.volume := by
  simp [Integrable, ofPath]

/-- Finite chain addition preserves gauge integrability, including cancellation. -/
theorem Integrable.add {L : ℂ →L[ℝ] ℝ} {P : ℂ → ℝ} {c d : BoundaryChain}
    (hc : Integrable L P c) (hd : Integrable L P d) : Integrable L P (c + d) := by
  classical
  intro γ hγ
  rcases Finset.mem_union.mp (Finsupp.support_add hγ) with h | h
  · exact hc γ h
  · exact hd γ h

@[simp]
theorem integrable_neg_iff {L : ℂ →L[ℝ] ℝ} {P : ℂ → ℝ} {c : BoundaryChain} :
    Integrable L P (-c) ↔ Integrable L P c := by
  simp [Integrable]

/-- Chain subtraction preserves gauge integrability. -/
theorem Integrable.sub {L : ℂ →L[ℝ] ℝ} {P : ℂ → ℝ} {c d : BoundaryChain}
    (hc : Integrable L P c) (hd : Integrable L P d) : Integrable L P (c - d) := by
  rw [sub_eq_add_neg]
  exact hc.add (integrable_neg_iff.mpr hd)

/-- Integrability of a finite family of chains gives integrability of their sum. -/
theorem Integrable.sum {L : ℂ →L[ℝ] ℝ} {P : ℂ → ℝ} {ι : Type*} (s : Finset ι)
    (c : ι → BoundaryChain) (h : ∀ i ∈ s, Integrable L P (c i)) :
    Integrable L P (∑ i ∈ s, c i) :=
  Finset.sum_induction _ _ (fun _ _ h₁ h₂ ↦ h₁.add h₂) (integrable_zero _ _) h

/-- Gauge integrability is stable under integer coefficients. -/
theorem Integrable.zsmul {L : ℂ →L[ℝ] ℝ} {P : ℂ → ℝ} {c : BoundaryChain}
    (hc : Integrable L P c) (n : ℤ) : Integrable L P (n • c) := by
  intro γ hγ
  exact hc γ (Finsupp.support_smul hγ)

/-- Every supported arc has the gauge integral used by the chain integral. -/
theorem Integrable.hasIntegral {L : ℂ →L[ℝ] ℝ} {P : ℂ → ℝ} {c : BoundaryChain}
    (hc : Integrable L P c) {γ : Arc} (hγ : γ ∈ c.support) :
    BoxIntegral.HasIntegral (TauCeti.BoxIntegral.intervalBox 0 1 zero_lt_one)
      BoxIntegral.IntegrationParams.Henstock
      (fun t ↦ P (γ.2.2.extend (t 0)) * L (deriv γ.2.2.extend (t 0)))
      BoxIntegral.BoxAdditiveMap.volume (arcIntegral L P γ) :=
  (hc γ hγ).hasIntegral

end BoundaryChain
end TauCeti.Green
