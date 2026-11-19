/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.StandardFrame
public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation
import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Comparison
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# The similarity principle for weak solutions of linear Cauchy–Riemann equations

Let `V` be a finite-dimensional complex normed space, `Ω ⊆ ℂ` open and `p > 2`. Let
`J ∈ W^{1,p}_loc(Ω; End_ℝ V)` be a continuous field of complex structures, `J² = -1`, and
`C ∈ Lᵖ_loc(Ω; End_ℝ V)` a field of real-linear endomorphisms. Let `ξ : ℂ → V` be a weak solution
of the linear Cauchy–Riemann equation

`∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0`

on `Ω` in the sense of `TauCeti.IsWeakLinearCauchyRiemannOn`: `ξ` is continuous, with a weak
derivative in `Lᵖ_loc`, and the equation holds almost everywhere. The **vector similarity
principle** (Carleman; McDuff–Salamon, Theorem 2.3.5) says that near every point `z₀ ∈ Ω` the
solution factors as `ξ = Φ σ`, with `Φ` a continuous `W^{1,p}_loc` family of invertible
real-linear maps satisfying `J Φ = Φ i` and `σ` holomorphic
(`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn_of_complexStructure`). Consequently a
weak solution has the zero structure of a holomorphic map: it has a similarity factorization at
every point, it vanishes on a connected open set as soon as it vanishes to infinite order at one
point or on a nonempty open subset, and otherwise its zeros are isolated.
These are the statements used for the local theory of pseudoholomorphic curves of finite
regularity, whose linearized equations have Sobolev coefficients.

The proof reduces to the standard structure `i`. The standard frame of
`TauCeti.standardFrame` turns the equation for `J` into an equation for `i` with a new coefficient
in `Lᵖ_loc` (`TauCeti.isWeakLinearCauchyRiemannOn_iff_standardFrame`), whose solutions factor by
the similarity principle for the standard structure,
`TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivOn_of_ne_top`, with a `W^{1,p}_loc` factor.
Composing that factor with the standard frame gives `Φ`.

## Main results

* `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn_of_complexStructure`: the
  factorization for a continuous `W^{1,p}_loc` field of complex structures `J`, with
  `J Φ = Φ i`.
* `TauCeti.hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_of_complexStructure`: the
  factorization in the form consumed by `TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation`.
* `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_forall_isBigO_of_complexStructure` and
  `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eqOn_zero_of_complexStructure`: unique
  continuation.
* `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn_of_complexStructure`:
  isolated zeros.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the Carleman similarity principle) and its proof.
* T. Carleman, *Sur les systèmes linéaires aux dérivées partielles du premier ordre à deux
  variables*, C. R. Acad. Sci. Paris **197** (1933), 471–474.
-/

public noncomputable section

open Asymptotics Complex Filter Function MeasureTheory Metric Set Topology TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] {p : ℝ≥0}
  {Ω : Opens ℂ} {J C : ℂ → V →L[ℝ] V} {ξ : ℂ → V}

/-- **The similarity principle for weak solutions** (Carleman; McDuff–Salamon, Theorem 2.3.5).
Let `p > 2`, let `J` be a continuous field of complex structures, `J² = -1`, on a
finite-dimensional complex normed space `V`, of class `W^{1,p}_loc` on an open set `Ω`, let `C` be
a locally `Lᵖ` field of real-linear endomorphisms of `V`, and let `ξ` be a weak solution of
`∂ₛξ + J ∂ₜξ + C ξ = 0` on `Ω`. Then every point `z₀ ∈ Ω` is the centre of a disc in `Ω` on which
`ξ = Φ σ`, with `Φ` a continuous `W^{1,p}_loc` family of invertible real-linear maps satisfying
`J Φ = Φ i` and `σ` holomorphic. -/
theorem exists_similarity_of_isWeakLinearCauchyRiemannOn_of_complexStructure (hp : 2 < p)
    (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (h : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hC : MemLpLoc p Ω C) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V),
      ContinuousOn Φ (ball z₀ r) ∧ MemWkpLoc p (ball z₀ r) 1 Φ ∧
      (∀ z ∈ ball z₀ r,
        IsUnit (Φ z) ∧ J z ∘L Φ z = Φ z ∘L (I • ContinuousLinearMap.id ℝ V)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ V
  have h₀ := hJJ z₀ hz₀
  -- reduce to the standard structure with the standard frame `S` on a disc `B₁`
  obtain ⟨Φ₁, hΦ₁⟩ :=
    ContinuousLinearMap.exists_continuousLinearEquiv_comp_eq_comp_I_smul (J z₀) h₀
  obtain ⟨r₁, hr₁, hr₁Ω, hu⟩ :=
    exists_ball_isUnit_standardFrame (Φ₁ := Φ₁) Ω.isOpen hz₀ hJc h₀
  let B₁ : Opens ℂ := ⟨ball z₀ r₁, isOpen_ball⟩
  set S := standardFrame J z₀ Φ₁
  have hSw : MemWkpLoc p B₁ 1 S := (memWkpLoc_standardFrame hJ).mono hr₁Ω
  obtain ⟨DS, hDS, hDSp⟩ := hSw.exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hDSp
  have hJc₁ : ContinuousOn J B₁ := hJc.mono hr₁Ω
  have hη := (isWeakLinearCauchyRiemannOn_iff_standardFrame hp hJc₁
    (fun z hz ↦ hJJ z (hr₁Ω hz)) h₀ hΦ₁ hu hDS hDSp).1 (h.mono hr₁Ω)
  have hC₁ : MemLpLoc p B₁ (frameCoeff J C S DS) :=
    (memLpLoc_frameCoeff_iff isOpen_ball.measurableSet (continuousOn_standardFrame hJc₁) hDSp hu
      hJc₁).2 (hC.mono_set hr₁Ω)
  -- and factor the solution of the reduced equation
  obtain ⟨r, hr, hrB, Ψ, σ, hΨc, hΨw, hΨu, hσ, hησ⟩ :=
    exists_similarity_of_hasWeakConjWirtingerDerivOn_of_ne_top (by exact_mod_cast hp)
      ENNReal.coe_ne_top hC₁ hη.continuousOn hη.hasWeakConjWirtingerDerivOn (mem_ball_self hr₁)
  have hrr₁ : ball z₀ r ⊆ ball z₀ r₁ := hrB
  let L : (V →L[ℂ] V) →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ
  refine ⟨r, hr, hrr₁.trans hr₁Ω, fun z ↦ S z ∘L L (Ψ z), σ, ?_, ?_, fun z hz ↦ ⟨?_, ?_⟩, hσ,
    fun z hz ↦ ?_⟩
  · exact ((continuousOn_standardFrame hJc₁).mono hrr₁).clm_comp
      (L.continuous.comp_continuousOn hΨc)
  · let Br : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
    have hp1 : (1 : ℝ≥0) < p := one_lt_two.trans hp
    exact (hSw.mono hrr₁ : MemWkpLoc p Br 1 S).bilin (ContinuousLinearMap.compL ℝ V V V) hp hp1
      le_rfl (hΨw.clm_comp L : MemWkpLoc p Br 1 fun z ↦ L (Ψ z))
  · exact (hu z (hrr₁ hz)).mul (ContinuousLinearMap.isUnit_restrictScalars (hΨu z hz))
  · rw [← ContinuousLinearMap.comp_assoc, comp_standardFrame (hJJ z (hr₁Ω (hrr₁ hz))) h₀ hΦ₁,
      ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
    congr 1
    ext v
    simp [L]
  · have hinv : S z (Ring.inverse (S z) (ξ z)) = ξ z := by
      simpa using congr($(Ring.mul_inverse_cancel _ (hu z (hrr₁ hz))) (ξ z))
    have hη : Ring.inverse (S z) (ξ z) = Ψ z (σ z) := hησ hz
    rw [← hinv, hη]
    simp [L]

/-- A weak solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` on an open set `Ω`, with `J` a continuous
`W^{1,p}_loc` field of complex structures and `C` locally `Lᵖ`, `p > 2`, has a similarity
factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_of_complexStructure (hp : 2 < p)
    (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (h : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hC : MemLpLoc p Ω C) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) : HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨r, hr, -, Φ, σ, hΦ, -, hΦu, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn_of_complexStructure hp hJc hJ hJJ h hC hz₀
  exact .of_eqOn_ball hr hΦ (hΦu z₀ (mem_ball_self hr)).1 hσ hξσ

/-- **Unique continuation** for weak solutions. On a connected open set `Ω`, a weak solution of
`∂ₛξ + J ∂ₜξ + C ξ = 0`, with `J` a continuous `W^{1,p}_loc` field of complex structures and `C`
locally `Lᵖ`, `p > 2`, that vanishes to infinite order at one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_forall_isBigO_of_complexStructure (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (h : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hC : MemLpLoc p Ω C) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO Ω.isOpen hΩc h.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_of_complexStructure
      hp hJc hJ hJJ h hC hz) hz₀ h₀

/-- **Unique continuation** for weak solutions. On a connected open set `Ω`, a weak solution of
`∂ₛξ + J ∂ₜξ + C ξ = 0`, with `J` a continuous `W^{1,p}_loc` field of complex structures and `C`
locally `Lᵖ`, `p > 2`, that vanishes on a nonempty open subset of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eqOn_zero_of_complexStructure (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (h : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hC : MemLpLoc p Ω C) {U : Set ℂ}
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_eqOn_zero Ω.isOpen hΩc h.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_of_complexStructure
      hp hJc hJ hJJ h hC hz) hU hUne hUΩ h₀

/-- **Isolated zeros** of weak solutions. On a connected open set `Ω`, the zeros of a weak
solution of `∂ₛξ + J ∂ₜξ + C ξ = 0`, with `J` a continuous `W^{1,p}_loc` field of complex
structures and `C` locally `Lᵖ`, `p > 2`, that is not identically zero on `Ω` form a discrete
subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn_of_complexStructure
    (hp : 2 < p) (hΩc : IsPreconnected (Ω : Set ℂ)) (hJc : ContinuousOn J Ω)
    (hJ : MemWkpLoc p Ω 1 J) (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (h : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hC : MemLpLoc p Ω C)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) : {z | ξ z ≠ 0} ∈ codiscreteWithin (Ω : Set ℂ) := by
  have := FiniteDimensional.completeSpace ℂ V
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt Ω.isOpen hΩc
    h.continuousOn (fun _ hz _ ↦
      hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_of_complexStructure hp hJc hJ hJJ
        h hC hz) hne

end TauCeti
