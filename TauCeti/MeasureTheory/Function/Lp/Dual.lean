/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.UniformConvex
import TauCeti.Analysis.Normed.Module.Annihilator
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Representation of continuous functionals on `Lᵖ`

On a σ-finite measure space, the integral pairing identifies the continuous dual of `Lᵠ`
with `Lᵖ` for conjugate exponents `1 < p, q < ∞`. The isometric embedding is supplied by
`MeasureTheory.Lp.toDual`. Surjectivity follows from reflexivity of `Lᵠ`: a functional
annihilating the closed range is evaluation at an `Lᵠ` function, which must vanish by the
injectivity of the reversed integral pairing.

This representation passes distributional test-function bounds to actual `Lᵖ` weak derivatives.

For a real inner product space `E` with a finite orthonormal basis `b`, the dual of the product
`(Lᵠ)ᶥ` is represented by `Lᵖ(α; E)`: a functional `Λ` is `g ↦ ∑ᵢ ∫ ⟪H, bᵢ⟫ gᵢ` for a field
`H ∈ Lᵖ` with `‖H‖_{Lᵖ} ≤ |ι| ‖Λ‖` (`MeasureTheory.Lp.exists_memLp_forall_dual_pi_apply_eq`).

## References

* G. B. Folland, *Real Analysis*, second edition, Theorem 6.16.
-/

public section

open scoped ENNReal InnerProductSpace

namespace MeasureTheory.Lp

variable {α 𝕜 : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {μ : Measure α}
  [SigmaFinite μ] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Every continuous scalar functional on `Lᵠ` is integration against an `Lᵖ` function,
for conjugate exponents strictly between one and infinity. -/
theorem toDual_surjective (hq : 1 < q) (hq_top : q ≠ ∞) :
    Function.Surjective (toDual 𝕜 μ p q) := by
  let S := (toDual 𝕜 μ p q).toLinearMap.range
  have hS : IsClosed (S : Set (StrongDual 𝕜 (Lp 𝕜 q μ))) :=
    (toDual 𝕜 μ p q).isometry.isClosedEmbedding.isClosed_range
  intro Λ
  suffices Λ ∈ S.topologicalClosure by
    rw [hS.submodule_topologicalClosure_eq] at this
    exact this
  apply (S.mem_topologicalClosure_iff_forall_dual_eq_zero Λ).2
  intro Ψ hΨ
  obtain ⟨f, rfl⟩ := surjective_inclusionInDoubleDual (𝕜 := 𝕜) (E := 𝕜) hq hq_top Ψ
  have hf : f = 0 := by
    apply (toDual 𝕜 μ q p).injective
    apply ContinuousLinearMap.ext
    intro g
    have hzero := hΨ (toDual 𝕜 μ p q g)
      (LinearMap.mem_range_self (toDual 𝕜 μ p q).toLinearMap g)
    rw [NormedSpace.dual_def, toDual_apply] at hzero
    rw [map_zero, zero_apply, toDual_apply]
    simpa only [mul_comm] using hzero
  simp [hf]

variable (𝕜 μ p q) in
/-- The norm-preserving integral representation of the continuous dual of `Lᵠ` by `Lᵖ`. -/
noncomputable def dualEquiv (hq : 1 < q) (hq_top : q ≠ ∞) :
    Lp 𝕜 p μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 q μ) :=
  LinearIsometryEquiv.ofSurjective (toDual 𝕜 μ p q) (toDual_surjective hq hq_top)

/-- Evaluation of the integral representation equivalence. -/
theorem dualEquiv_apply (hq : 1 < q) (hq_top : q ≠ ∞) (g : Lp 𝕜 p μ) (f : Lp 𝕜 q μ) :
    dualEquiv 𝕜 μ p q hq hq_top g f = ∫ x, g x * f x ∂μ :=
  toDual_apply g f

@[simp]
theorem coe_dualEquiv (hq : 1 < q) (hq_top : q ≠ ∞) :
    ⇑(dualEquiv 𝕜 μ p q hq hq_top) = toDual 𝕜 μ p q := by
  funext g
  ext f
  exact (dualEquiv_apply hq hq_top g f).trans (toDual_apply g f).symm

/-- The representing density of a functional integrates to its value on every `Lᵠ` function. -/
@[simp]
theorem integral_dualEquiv_symm_mul (hq : 1 < q) (hq_top : q ≠ ∞)
    (Λ : StrongDual 𝕜 (Lp 𝕜 q μ)) (f : Lp 𝕜 q μ) :
    ∫ x, (dualEquiv 𝕜 μ p q hq hq_top).symm Λ x * f x ∂μ = Λ f := by
  rw [← dualEquiv_apply hq hq_top, LinearIsometryEquiv.apply_symm_apply]

/-- **Representation of functionals on `(Lᵠ)ᶥ`.** Let `b` be a finite orthonormal basis of a real
inner product space `E`. A continuous functional `Λ` on `(Lᵠ)ᶥ` is `g ↦ ∑ᵢ ∫ ⟪H, bᵢ⟫ gᵢ` for a
field `H ∈ Lᵖ(α; E)` with `‖H‖_{Lᵖ} ≤ |ι| ‖Λ‖`. -/
theorem exists_memLp_forall_dual_pi_apply_eq {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (hq : 1 < q) (hq_top : q ≠ ∞) (b : OrthonormalBasis ι ℝ E)
    (Λ : StrongDual ℝ (ι → Lp ℝ q μ)) :
    ∃ H : α → E, MemLp H p μ ∧ eLpNorm H p μ ≤ Fintype.card ι * ENNReal.ofReal ‖Λ‖ ∧
      ∀ g, Λ g = ∑ i, ∫ x, ⟪H x, b i⟫_ℝ * g i x ∂μ := by
  classical
  let Λc : ι → StrongDual ℝ (Lp ℝ q μ) := fun i =>
    Λ.comp (ContinuousLinearMap.single ℝ (fun _ : ι => Lp ℝ q μ) i)
  let Hc : ι → Lp ℝ p μ := fun i => (dualEquiv ℝ μ p q hq hq_top).symm (Λc i)
  have hHc (i : ι) : ‖Hc i‖ ≤ ‖Λ‖ := by
    simp only [Hc, LinearIsometryEquiv.norm_map]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun g => ?_
    calc ‖Λc i g‖ ≤ ‖Λ‖ * ‖Pi.single (M := fun _ : ι => Lp ℝ q μ) i g‖ := Λ.le_opNorm _
      _ = ‖Λ‖ * ‖g‖ := by rw [Pi.norm_single]
  have hHi (i : ι) : MemLp (fun x => (Hc i : α → ℝ) x • b i) p μ :=
    (Lp.memLp (Hc i)).smul (memLp_top_const (b i))
  have hsum : (fun x => ∑ i, (Hc i : α → ℝ) x • b i) = ∑ i, fun x => (Hc i : α → ℝ) x • b i :=
    (Finset.sum_fn _ _).symm
  have hinner (x : α) (i : ι) : ⟪∑ j, (Hc j : α → ℝ) x • b j, b i⟫_ℝ = Hc i x := by
    simp [sum_inner, real_inner_smul_left, b.inner_eq_ite]
  refine ⟨fun x => ∑ i, (Hc i : α → ℝ) x • b i, ?_, ?_, fun g => ?_⟩
  · rw [hsum]
    exact memLp_finsetSum' Finset.univ fun i _ => hHi i
  · calc eLpNorm (fun x => ∑ i, (Hc i : α → ℝ) x • b i) p μ
        ≤ ∑ i, eLpNorm (fun x => (Hc i : α → ℝ) x • b i) p μ := by
          rw [hsum]
          exact eLpNorm_sum_le Fact.out
      _ ≤ ∑ _i : ι, ENNReal.ofReal ‖Λ‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [eLpNorm_congr_norm_ae (hHi i).aestronglyMeasurable (Lp.aestronglyMeasurable (Hc i))
            (ae_of_all _ fun x => by rw [norm_smul, b.orthonormal.1 i, mul_one]), ← Lp.eNorm_def,
            ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hHc i)
      _ = Fintype.card ι * ENNReal.ofReal ‖Λ‖ := by simp
  · conv_lhs => rw [← Finset.univ_sum_single g]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [hinner]
    exact (integral_dualEquiv_symm_mul (p := p) hq hq_top (Λc i) (g i)).symm

end MeasureTheory.Lp
