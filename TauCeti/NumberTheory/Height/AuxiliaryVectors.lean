/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.PowerModulus
public import TauCeti.NumberTheory.GeometryOfNumbers.Covolume.Basic
public import TauCeti.NumberTheory.Height.LatticeOverPairs
import TauCeti.NumberTheory.GeometryOfNumbers.Covolume.Completion

/-!
# Auxiliary vectors of a twisted lattice

Auxiliary vectors have a common scalar clearing their denominators at the allowed twists and
have bounded conjugate norms at the reference twist. A surjective projection of a spanning
family supplies auxiliary vectors once its effects on denominators and sizes are controlled.
One can then complete an independent family to a basis using only these auxiliary vectors,
without losing the common scalar in the completion.

The auxiliary vectors, their normalized spanning set, and their use in basis completion are
those of `New.Data.IsAuxiliaryForm`, `New.Data.exists_span_isAuxiliaryForm_eq_top`, and
`New.Data.integral_forms_long` in `grh/src/New/Determinant/Twist/LongForms.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

open Matrix Set Submodule
open scoped ComplexOrder

namespace TauCeti.TwistedLattice

variable {T C V : Type*} [One T] [Fintype C] [AddCommMonoid V] [Module ℂ V]
variable {S : T → Type*} [∀ t, NormedAddCommGroup (S t)] [∀ t, InnerProductSpace ℂ (S t)]

/-- Vectors whose lifts become integral after multiplication by the common scalar `γ` at
all allowed twists, and whose conjugated squared norms at the reference twist are at most
`exp h`. -/
def auxiliaryVectors (L : TwistedLattice S C V) (γ : T → ℂ) (h : ℝ) : Set V :=
  {v | (∀ t ι (ht : L.allowed t ι.primeIndex), γ t • L.lift t v ∈ L.integral t ι ht) ∧
    ∀ σ : ℂ ≃+* ℂ, L.normSqAt σ v ≤ Real.exp h}

/-- The denominator and size conditions for an auxiliary vector. -/
@[simp] theorem mem_auxiliaryVectors_iff (L : TwistedLattice S C V) {γ : T → ℂ} {h : ℝ} {v : V} :
    v ∈ L.auxiliaryVectors γ h ↔
      (∀ t ι (ht : L.allowed t ι.primeIndex), γ t • L.lift t v ∈ L.integral t ι ht) ∧
        ∀ σ : ℂ ≃+* ℂ, L.normSqAt σ v ≤ Real.exp h := Iff.rfl

/-- Suppose a surjection sends a spanning set to vectors with a common clearing scalar
`c(t) / c(1)` and bounded conjugate lengths. Then the auxiliary vectors span, with a scalar
of value `1` at the reference twist and modulus given by a single power of the twisting norms
times `F`. Here `F` is positive even away from the reference twist, so the scalar never vanishes. -/
theorem exists_span_auxiliaryVectors_eq_top (L : TwistedLattice S C V)
    {U : Type*} [AddCommMonoid U] [Module ℂ U] (p : U →ₗ[ℂ] V) (hp : Function.Surjective p)
    {A : Set U} (hA : span ℂ A = ⊤) {c : T → ℂ} {N : T → ℕ+} {F : T → ℝ}
    (hc : HasNormUpToPower N c F) (hc₁ : c 1 ≠ 0) (hN₁ : N 1 = 1) (hF₁ : F 1 = 1)
    (hF : ∀ t, 0 < F t) {h : ℝ}
    (hint : ∀ v ∈ A, ∀ t ι (ht : L.allowed t ι.primeIndex),
      (c t / c 1) • L.lift t (p v) ∈ L.integral t ι ht)
    (hshort : ∀ v ∈ A, ∀ σ : ℂ ≃+* ℂ, L.normSqAt σ (p v) ≤ Real.exp h) :
    ∃ (e : ℤ) (γ : T → ℂ), γ 1 = 1 ∧ (∀ t, γ t ≠ 0) ∧
      (∀ t, ‖γ t‖ = ((N t : ℕ) : ℝ) ^ ((e : ℝ) / 2) * F t) ∧
      span ℂ (L.auxiliaryVectors γ h) = ⊤ := by
  obtain ⟨e, he⟩ := hc.exists_norm_div_eq hN₁ hF₁ hc₁
  let γ : T → ℂ := fun t ↦ c t / c 1
  have hγ (t : T) : ‖γ t‖ = ((N t : ℕ) : ℝ) ^ ((e : ℝ) / 2) * F t :=
    (he t).trans (by rw [abs_of_pos (hF t)])
  refine ⟨e, γ, div_self hc₁, fun t ↦ norm_ne_zero_iff.mp ?_, hγ, ?_⟩
  · rw [hγ]
    exact (mul_pos (Real.rpow_pos_of_pos (by positivity) _) (hF t)).ne'
  apply top_unique
  rw [← LinearMap.range_eq_top.mpr hp, ← Submodule.map_top, ← hA, Submodule.map_span]
  exact span_mono (image_subset_iff.mpr fun v hv ↦
    (L.mem_auxiliaryVectors_iff).mpr ⟨hint v hv, hshort v hv⟩)

/-- Complete an independent family to a basis using auxiliary vectors. The new vectors use the
same clearing scalar at every allowed twist, while the logarithmic squared covolume increases
by at most the codimension times the common size bound. Only spanning modulo the original
family is needed. -/
theorem exists_basis_completion_of_auxiliary_vectors {U : Type*} [AddCommGroup U]
    [Module ℂ U] [FiniteDimensional ℂ U] (L : TwistedLattice S C U)
    {I : Type*} [Fintype I] [DecidableEq I] {v : I → U} (hv : LinearIndependent ℂ v)
    {γ : T → ℂ} {h c : ℝ}
    (hspan : span ℂ (range v ∪ L.auxiliaryVectors γ h) = ⊤)
    (hc : (of fun j i ↦ L.coord (L.lift 1 (v i)) j).CovolumeLE L.gram c) :
    let k := Module.finrank ℂ U - Fintype.card I
    ∃ b : Module.Basis (I ⊕ Fin k) ℂ U,
      (∀ i, b (.inl i) = v i) ∧ (∀ j, b (.inr j) ∈ L.auxiliaryVectors γ h) ∧
      (of fun j i ↦ L.coord (L.lift 1 (b i)) j).CovolumeLE L.gram (c + k * h) := by
  dsimp only
  refine hv.exists_basis_completion_of_covolumeLE hspan
    (fun x ↦ L.coord (L.lift 1 x)) L.posDef_gram.posSemidef hc ?_
  intro x hx σ
  let w : C → ℂ := fun j ↦ σ (L.coord (L.lift 1 x) j)
  have hnonneg := L.posDef_gram.posSemidef.dotProduct_mulVec_nonneg w
  have heq : ‖star w ⬝ᵥ (L.gram.map (algebraMap ℚ ℂ) *ᵥ w)‖ = L.normSqAt σ x := by
    rw [L.normSqAt_def]
    simpa only [Complex.ofReal_re] using congrArg Complex.re (Complex.norm_of_nonneg' hnonneg)
  exact heq.trans_le ((L.mem_auxiliaryVectors_iff.mp hx).2 σ)

end TauCeti.TwistedLattice
