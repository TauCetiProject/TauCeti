/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Basic
-- Private: used only inside proofs.
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Sobolev.SmoothCutoff
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Smooth compactly supported fields are dense in vector-valued `W^{1,p}(ℝⁿ)`

For a real Banach space `F` and `1 ≤ p < ∞`, every element of the first-order weak-derivative
graph over `Lᵖ(ℝⁿ, F)` is a limit of the graph elements of smooth compactly supported fields
`ℝⁿ → F` (`TauCeti.WeakDerivStep.dense_setOf_exists_contDiff_hasCompactSupport`). A priori
estimates proved for smooth compactly supported fields therefore extend to the whole Sobolev space
by continuity. No finite dimensionality of `F` is assumed, so this applies to paths in an
infinite-dimensional Hilbert space, the setting of the linearized operators `d/ds + A(s)` on a
strip.

The proof mollifies, then cuts off. Convolving a field `u` with weak derivative `Du` against a
normalized smooth bump gives a smooth field whose classical derivative is the mollification of
`Du` (`TauCeti.HasWeakFDerivOn.hasFDerivAt_convolution_right`), and the mollifications converge to
`u` and `Du` in `Lᵖ` (`TauCeti.tendsto_eLpNorm_normed_convolution_sub`). A smooth field with
derivative in `Lᵖ` is in turn the limit of its products with the expanding cutoffs `χ (x / n)`
(`TauCeti.exists_contDiff_hasCompactSupport_tendsto_eLpNorm_sub_fderiv_sub`), and a smooth
compactly supported field has its classical derivative as weak derivative
(`TauCeti.WeakDerivStep.exists_prev_ae_eq_and_weakFDeriv_ae_eq_of_differentiableOn`).

## Main declarations

* `TauCeti.WeakDerivStep.dense_setOf_exists_contDiff_hasCompactSupport`: the fields with a smooth
  compactly supported representative are dense.

## References

L. C. Evans, *Partial Differential Equations*, §5.3.1; H. Brezis, *Functional Analysis, Sobolev
Spaces and Partial Differential Equations*, Theorem 9.2 (mollification and cutoff, in the scalar
case).
-/

public section

noncomputable section

open Filter MeasureTheory TopologicalSpace Set
open scoped Convolution ENNReal Topology

namespace TauCeti.WeakDerivStep

section Density

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

/-- **Cutting off a smooth field.** An element of the weak-derivative graph over `Lᵖ(ℝⁿ, F)`
represented by a smooth field `g` whose derivative lies in `Lᵖ` is a limit of elements represented
by smooth compactly supported fields: the expanding cutoffs `χ (x / (n + 1)) • g x`. -/
private theorem mem_closure_setOf_exists_contDiff_hasCompactSupport (hp : p ≠ ∞)
    {v : WeakDerivStep mu ⊤ p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E))))}
    {g : E → F} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hvg : ⇑(prev _ v) =ᵐ[mu.restrict (⊤ : Opens E)] g)
    (hdg : MemLp (fderiv ℝ g) p (mu.restrict (⊤ : Opens E))) :
    v ∈ closure {u : WeakDerivStep mu ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E)))) |
      ∃ φ : E → F, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
        ⇑(prev _ u) =ᵐ[mu.restrict (⊤ : Opens E)] φ} := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
  have hgp : MemLp g p (mu.restrict (⊤ : Opens E)) := (Lp.memLp (prev _ v)).ae_eq hvg
  obtain ⟨h, hh, hconv, hdconv⟩ :=
    exists_contDiff_hasCompactSupport_tendsto_eLpNorm_sub_fderiv_sub hp hg le_top hgp hdg
  have hh1 (n : ℕ) : ContDiff ℝ 1 (h n) := (hh n).1.of_le (by exact_mod_cast le_top)
  have hhp (n : ℕ) : MemLp (h n) p (mu.restrict (⊤ : Opens E)) :=
    (hh1 n).continuous.memLp_of_hasCompactSupport (hh n).2
  have hdhp (n : ℕ) : MemLp (fderiv ℝ (h n)) p (mu.restrict (⊤ : Opens E)) :=
    ((hh1 n).continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport ((hh n).2.fderiv ℝ)
  -- The weak derivative of `v` is the classical derivative of its smooth representative.
  have hdv : ⇑(weakFDeriv _ v) =ᵐ[mu.restrict (⊤ : Opens E)] fderiv ℝ g :=
    ((hasWeakFDerivOn_base_prev _ v).congr_ae hvg).ae_eq_fderiv
      ((hg1.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
      fun x _ ↦ hg1.differentiable one_ne_zero x
  choose w hw hdw using fun n ↦ exists_prev_ae_eq_and_weakFDeriv_ae_eq_of_differentiableOn
    (fun x _ ↦ (hh1 n).differentiable one_ne_zero x) (hhp n) (hdhp n)
  exact mem_closure_of_tendsto (tendsto_of_tendsto_eLpNorm hw hdw hvg hdv hconv hdconv)
    (.of_forall fun n ↦ ⟨h n, (hh n).1, (hh n).2, hw n⟩)

open ContinuousLinearMap in
/-- **Mollifying a field.** Every element of the weak-derivative graph over `Lᵖ(ℝⁿ, F)` is a limit
of elements represented by smooth fields whose derivatives lie in `Lᵖ`: its convolutions with
normalized smooth bumps of shrinking radii. -/
private theorem exists_tendsto_of_contDiff (hp : p ≠ ∞)
    (u : WeakDerivStep mu ⊤ p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E))))) :
    ∃ v : ℕ → WeakDerivStep mu ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E)))),
      Tendsto v atTop (𝓝 u) ∧ ∀ k, ∃ g : E → F, ContDiff ℝ (⊤ : ℕ∞) g ∧
        ⇑(prev _ (v k)) =ᵐ[mu.restrict (⊤ : Opens E)] g ∧
        MemLp (fderiv ℝ g) p (mu.restrict (⊤ : Opens E)) := by
  have hν : mu.restrict ((⊤ : Opens E) : Set E) = mu := by simp
  set f : E → F := ⇑(prev _ u)
  set D : E → E →L[ℝ] F := ⇑(weakFDeriv _ u)
  have hf : MemLp f p mu := by rw [← hν]; exact Lp.memLp _
  have hD : MemLp D p mu := by rw [← hν]; exact Lp.memLp _
  let phi : ℕ → ContDiffBump (0 : E) := fun k ↦
    ⟨1 / ((k : ℝ) + 1) / 2, 1 / ((k : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩
  have hphi : Tendsto (fun k ↦ (phi k).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- The mollified field `g k` is smooth, and its classical derivative is the mollified weak
  -- derivative.
  let g : ℕ → E → F := fun k ↦ (phi k).normed mu ⋆[lsmul ℝ ℝ, mu] f
  have hg (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (g k) :=
    (phi k).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (phi k).contDiff_normed (hf.locallyIntegrable Fact.out)
  have hg1 (k : ℕ) : ContDiff ℝ 1 (g k) := (hg k).of_le (by exact_mod_cast le_top)
  have hfd (k : ℕ) : fderiv ℝ (g k) = (phi k).normed mu ⋆[lsmul ℝ ℝ, mu] D := funext fun x ↦ by
    have h := (hasWeakFDerivOn_base_prev _ u).hasFDerivAt_convolution_right
      (hf.locallyIntegrable Fact.out) (hD.locallyIntegrable Fact.out) ((phi k).normed mu)
      (phi k).contDiff_normed (phi k).hasCompactSupport_normed x (fun _ _ ↦ trivial)
    rw [convolution_flip, convolution_flip] at h
    exact h.fderiv
  have hgp (k : ℕ) : MemLp (g k) p (mu.restrict (⊤ : Opens E)) := by
    rw [hν]; exact (Lp.memLp _).ae_eq (normedBumpLp_ae_eq_convolution hp (phi k) hf)
  have hdgp (k : ℕ) : MemLp (fderiv ℝ (g k)) p (mu.restrict (⊤ : Opens E)) := by
    rw [hν, hfd]; exact (Lp.memLp _).ae_eq (normedBumpLp_ae_eq_convolution hp (phi k) hD)
  choose v hv hdv using fun k ↦ exists_prev_ae_eq_and_weakFDeriv_ae_eq_of_differentiableOn
    (fun x _ ↦ (hg1 k).differentiable one_ne_zero x) (hgp k) (hdgp k)
  refine ⟨v, tendsto_of_tendsto_eLpNorm (g₀ := f) (D₀ := D) hv hdv .rfl .rfl ?_ ?_,
    fun k ↦ ⟨g k, hg k, hv k, hdgp k⟩⟩
  · rw [hν]; exact tendsto_eLpNorm_normed_convolution_sub hp hphi hf
  · rw [hν]; simpa only [hfd] using tendsto_eLpNorm_normed_convolution_sub hp hphi hD

/-- **Density of smooth compactly supported fields.** For a real Banach space `F` and
`1 ≤ p < ∞`, the elements of the weak-derivative graph over `Lᵖ(ℝⁿ, F)` represented by a smooth
compactly supported field are dense. -/
theorem dense_setOf_exists_contDiff_hasCompactSupport (hp : p ≠ ∞) :
    Dense {u : WeakDerivStep mu ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E)))) |
      ∃ φ : E → F, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
        ⇑(prev _ u) =ᵐ[mu.restrict (⊤ : Opens E)] φ} := fun u ↦ by
  obtain ⟨v, hv, hsmooth⟩ := exists_tendsto_of_contDiff hp u
  refine closure_closure.subset (mem_closure_of_tendsto hv (Eventually.of_forall fun k ↦ ?_))
  obtain ⟨g, hg, hvg, hdg⟩ := hsmooth k
  exact mem_closure_setOf_exists_contDiff_hasCompactSupport hp hg hvg hdg

end Density

end TauCeti.WeakDerivStep
