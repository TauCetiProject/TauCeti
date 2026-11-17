/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Relative.FirstJet
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart

/-!
# The relative Poincaré lemma on a tube

Let `Φ` be a diffeomorphism from the total space of a vector bundle `V → B` onto a manifold `M`,
such as a tubular neighbourhood of an embedded submanifold, with zero-section inclusion
`i = Φ ∘ 0` and retraction `ρ = Φ ∘ 0 ∘ π ∘ Φ⁻¹` onto its image. Transporting the relative
Poincaré operator `P` of the bundle (`TauCeti.vectorBundlePoincareHomotopy`) along `Φ` gives, for
every closed `C^r` form `η` of positive degree on `M` with `r ≥ 1`, the form
`β = (Φ⁻¹)^* P (Φ^* η)`. It satisfies `d β = η - ρ^* η` and vanishes along `i` as a full ambient
tensor (`Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback`), and `d β = η` when
`i^* η = 0` (`Diffeomorph.exists_isSmoothForm_relative_primitive`).

At every point `Φ(0_b)` where `η` vanishes as a full ambient tensor, `β` moreover has zero first
jet: the coordinate expression of `β` in the preferred chart at `Φ(0_b)` has zero derivative
there, within the range of the model. On the total space this is the first-jet property of `P`
(`TauCeti.hasFDerivWithinAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection`), and pulling a
form back along the `C¹` map `Φ⁻¹` preserves zero first jets
(`TauCeti.RoughForm.hasFDerivWithinAt_inChartAt_mpullback_of_apply_eq_zero`). For two symplectic
forms agreeing on the full ambient tangent spaces along a submanifold, a primitive of their
difference with zero first jet there makes the Moser vector field vanish to first order along the
submanifold, so that the Moser diffeomorphism has differential the identity along it.

## Main results

* `Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback`: the relative homotopy formula on a
  tube, with the first-jet property.
* `Diffeomorph.exists_isSmoothForm_relative_primitive`: the relative Poincaré lemma on a tube, with
  the first-jet property.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, §6.2 (the relative Poincaré lemma by fibre scaling) and Theorem 7.4 (the
  relative Moser theorem).
-/

public section

noncomputable section

open Set Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {B FV : Type*} {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V]
  [VectorBundle ℝ FV V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {n : WithTop ℕ∞} [IsManifold IB n B] [ContMDiffVectorBundle n FV V IB]

/-- **The relative Poincaré lemma on a tube.** Let `Φ` be a `C^n` diffeomorphism from the total
space of a `C^n` vector bundle onto `M`, such as a tubular neighbourhood, with zero-section
inclusion `i = Φ ∘ 0` and retraction `ρ = Φ ∘ 0 ∘ π ∘ Φ⁻¹` onto its image. Every closed `C^r`
form `η` of positive degree on `M`, with `1 ≤ r` and `r + 1 ≤ n`, has a `C^r` form `β` with
`d β = η - ρ^* η` that vanishes along `i` as a full ambient tensor. At every point of the image of
`i` where `η` vanishes as a full ambient tensor, `β` moreover has zero first jet: its coordinate
expression in the preferred chart there has zero derivative, within the range of the model. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0) :
    ∃ β : RoughForm I M F k, IsSmoothForm I r β ∧
      mextDeriv β = η - mpullback I I (Φ ∘ zeroSection FV V ∘ π FV V ∘ Φ.symm) η ∧
      (∀ b, β (Φ (zeroSection FV V b)) = 0) ∧
      ∀ b, η (Φ (zeroSection FV V b)) = 0 →
        HasFDerivWithinAt (β.inChartAt (Φ (zeroSection FV V b)))
          (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) (range I)
          (extChartAt I (Φ (zeroSection FV V b)) (Φ (zeroSection FV V b))) := by
  have hr' : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  have h2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by rw [← one_add_one_eq_two]; gcongr) hn
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (by norm_num) h2).ne'
  have : IsManifold IB ((r : WithTop ℕ∞) + 1) B := .of_le hn
  have : ContMDiffVectorBundle ((r : WithTop ℕ∞) + 1) FV V IB := .of_le hn
  have : IsManifold IB 2 B := .of_le h2
  have : ContMDiffVectorBundle 2 FV V IB := .of_le h2
  have hη₀ := hη.mpullback (Φ.contMDiff.of_le hn)
  have hβ₀ := hη₀.vectorBundlePoincareHomotopy
  refine ⟨mpullback I (IB.prod 𝓘(ℝ, FV)) Φ.symm (vectorBundlePoincareHomotopy
    (mpullback (IB.prod 𝓘(ℝ, FV)) I Φ η)), hβ₀.mpullback (Φ.symm.contMDiff.of_le hn), ?_,
    fun b ↦ ?_, fun b hb ↦ ?_⟩
  · have hd := Φ.mdifferentiable hn0
    have hds := Φ.symm.mdifferentiable hn0
    have hZ := (contMDiff_zeroSection ℝ V (IB := IB) (F := FV) (n := 1)).mdifferentiable one_ne_zero
    have hp := (Bundle.contMDiff_proj (IB := IB) (n := 1) (F := FV) V).mdifferentiable one_ne_zero
    rw [← mpullback_mextDeriv (Φ.symm.contMDiff.of_le h2)
        ((isSmoothBundleForm_def 1 _).mpr (hβ₀.of_le hr').contMDiff),
      mextDeriv_vectorBundlePoincareHomotopy (hη₀.of_le hr')
        (hη.of_le hr' |>.mextDeriv_mpullback_eq_zero hclosed (Φ.contMDiff.of_le h2)),
      mpullback_sub, mpullback_symm_mpullback hn0, ← mpullback_comp (hZ.comp hp) hd,
      ← mpullback_comp hds (hd.comp (hZ.comp hp))]
    -- Both retractions are `Φ ∘ 0 ∘ π ∘ Φ⁻¹`, associated differently.
    simp only [Function.comp_assoc]
  · exact mpullback_apply_eq_zero ((congrArg _ (Φ.symm_apply_apply _)).trans
      (vectorBundlePoincareHomotopy_zeroSection _ b))
  · -- The primitive on the total space has zero first jet at `0_b`, and pulling back along the
    -- `C¹` map `Φ⁻¹` preserves this.
    have h1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) h2
    have : IsManifold IB 1 B := .of_le h1
    have : ContMDiffVectorBundle 1 FV V IB := .of_le h1
    exact RoughForm.hasFDerivWithinAt_inChartAt_mpullback_of_apply_eq_zero _
      (Φ.symm.contMDiff.of_le h1).contMDiffAt (Φ.symm_apply_apply _)
      (vectorBundlePoincareHomotopy_zeroSection _ b)
      (hasFDerivWithinAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection
        (hη₀.of_le zero_le) (mpullback_apply_eq_zero hb))

/-- **The relative Poincaré lemma on a tube**, for forms restricting to zero on the core. Let `Φ`
be a `C^n` diffeomorphism from the total space of a `C^n` vector bundle onto `M`, such as a
tubular neighbourhood, with zero-section inclusion `i = Φ ∘ 0`. Every closed `C^r` form `η` of
positive degree on `M` with `i^* η = 0`, where `1 ≤ r` and `r + 1 ≤ n`, is the exterior
derivative of a `C^r` form `β` that vanishes along `i` as a full ambient tensor, and which has zero
first jet at every point of the image of `i` where `η` vanishes as a full ambient tensor. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_relative_primitive
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0)
    (hi : mpullback IB I (Φ ∘ zeroSection FV V) η = 0) :
    ∃ β : RoughForm I M F k, IsSmoothForm I r β ∧ mextDeriv β = η ∧
      (∀ b, β (Φ (zeroSection FV V b)) = 0) ∧
      ∀ b, η (Φ (zeroSection FV V b)) = 0 →
        HasFDerivWithinAt (β.inChartAt (Φ (zeroSection FV V b)))
          (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) (range I)
          (extChartAt I (Φ (zeroSection FV V b)) (Φ (zeroSection FV V b))) := by
  obtain ⟨β, hβ, hdβ, hβ₀, hβ₁⟩ :=
    Φ.exists_isSmoothForm_mextDeriv_eq_sub_mpullback hr hn hη hclosed
  refine ⟨β, hβ, ?_, hβ₀, hβ₁⟩
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (by simp) hn).ne'
  have hp := (Bundle.contMDiff_proj (IB := IB) (n := 1) (F := FV) V).mdifferentiable one_ne_zero
  have hiΦ := (Φ.contMDiff.comp (contMDiff_zeroSection ℝ V (IB := IB) (F := FV))).mdifferentiable
    hn0
  rw [hdβ, ← Function.comp_assoc (Φ : TotalSpace FV V → M) (zeroSection FV V),
    mpullback_comp (hp.comp (Φ.symm.mdifferentiable hn0)) hiΦ, hi, mpullback_zero, sub_zero]

end TauCeti
