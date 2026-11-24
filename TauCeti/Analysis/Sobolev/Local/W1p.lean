/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.Local.FirstOrder
public import TauCeti.Analysis.Sobolev.Local.Norm
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Local

/-!
# Order-one local Sobolev functions and `W1p`

Let `Ω` be an open subset of a finite-dimensional real inner product space `E` carrying a Borel
additive Haar measure `μ`. This file compares the first-order local Sobolev class
`TauCeti.MemW1pLoc p Ω` of real-valued functions with `TauCeti.W1p`: a real function lies in
`MemW1pLoc p Ω u μ` exactly when its restriction to every open `W` with compact closure contained in
`Ω` is represented by an element of `W1p μ W p`. The weak gradient of that element is dual, through
`InnerProductSpace.toDual`, to the weak derivative of the function on `Ω`. On `ℂ`, the planar
order-one class `TauCeti.MemWkpLoc p Ω 1` agrees with `MemW1pLoc p Ω`
(`TauCeti.memWkpLoc_one_iff_memW1pLoc`), and a real function of finite `W^{1,p}(Ω)` norm
`TauCeti.eLpNormWkp p Ω 1` is represented by an element of `W1p volume Ω p` whose norm is at most
that size.

## Main declarations

* `TauCeti.MemW1pLoc.exists_w1p`: a real member of `MemW1pLoc p Ω` is represented by an element of
  `W1p` on every relatively compact open subset of `Ω`, with the dual weak gradient.
* `TauCeti.memW1pLoc_iff_forall_w1p`: characterization of real-valued `MemW1pLoc p Ω` by
  `W1p μ W p` on relatively compact open subsets `W` of `Ω`.
* `TauCeti.memWkpLoc_one_iff_memW1pLoc`: on open subsets of `ℂ`, `MemWkpLoc p Ω 1` agrees with
  `MemW1pLoc p Ω`.
* `TauCeti.exists_w1p_enorm_le_eLpNormWkp`: a real function on `Ω ⊆ ℂ` of finite `W^{1,p}(Ω)` norm
  is represented in `W1p volume Ω p` with no larger norm.

## References

* W. P. Ziemer, *Weakly Differentiable Functions*, Graduate Texts in Mathematics 120, Springer,
  1989, §2.1.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces).
-/

public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E}

/-- **Local Sobolev functions are Sobolev on relatively compact subdomains.** Let
`u ∈ MemW1pLoc p Ω` be real-valued, with weak derivative `D` on `Ω`. On every open `W` whose
closure is compact and contained in `Ω`, `u` is represented by an element of `W1p μ W p`
whose weak gradient is dual to `D`. -/
theorem MemW1pLoc.exists_w1p {u : E → ℝ} (hu : MemW1pLoc p Ω u μ)
    {D : E → E →L[ℝ] ℝ} (hD : HasWeakFDerivOn μ Ω u D) {W : Opens E}
    (hWc : IsCompact (closure (W : Set E))) (hWΩ : closure (W : Set E) ⊆ Ω) :
    ∃ v : W1p μ W p, W1p.value v =ᵐ[μ.restrict W] u ∧
      W1p.gradient v =ᵐ[μ.restrict W]
        fun x => (InnerProductSpace.toDual ℝ E).symm (D x) :=
  W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn
    (hu.memLpLoc.memLp_restrict_of_isCompact_closure hWc hWΩ)
    ((hu.memLpLoc_of_hasWeakFDerivOn hD).memLp_restrict_of_isCompact_closure hWc hWΩ)
    (hD.mono (SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ)))

/-- **Comparison of `MemW1pLoc` with `W1p`.** A real-valued function on `Ω ⊆ E` lies in
`MemW1pLoc p Ω` if and only if its restriction to every open `W` with compact closure contained in
`Ω` is represented by an element of `W1p μ W p`. The weak gradients then correspond to the
weak derivative of `u` on `Ω` through `InnerProductSpace.toDual`, by
`TauCeti.MemW1pLoc.exists_w1p`. -/
theorem memW1pLoc_iff_forall_w1p {u : E → ℝ} :
    MemW1pLoc p Ω u μ ↔ ∀ W : Opens E, IsCompact (closure (W : Set E)) →
      closure (W : Set E) ⊆ Ω → ∃ v : W1p μ W p, W1p.value v =ᵐ[μ.restrict W] u := by
  constructor
  · intro hu W hWc hWΩ
    obtain ⟨D, hD, -⟩ := hu.exists_hasWeakFDerivOn
    obtain ⟨v, hv, -⟩ := hu.exists_w1p hD hWc hWΩ
    exact ⟨v, hv⟩
  · intro h
    have hcover : ∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ W : Opens E, K ⊆ W ∧ W ≤ Ω ∧
        ∃ v : W1p μ W p, W1p.value v =ᵐ[μ.restrict W] u := by
      intro K hK hKΩ
      obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
      exact ⟨W, hKW, SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ), h W hWc hWΩ⟩
    obtain ⟨D, hD⟩ : ∃ D : E → E →L[ℝ] ℝ, HasWeakFDerivOn μ Ω u D := by
      refine exists_hasWeakFDerivOn_iff_locally.2 fun x hx => ?_
      obtain ⟨W, hxW, -, v, hv⟩ := hcover {x} isCompact_singleton (singleton_subset_iff.2 hx)
      exact ⟨W, hxW rfl, _, (W1p.hasWeakFDerivOn v).congr_ae hv⟩
    refine memW1pLoc_iff.2
      ⟨memLpLoc_iff.2 fun K hKΩ hK => ?_, D, hD, memLpLoc_iff.2 fun K hKΩ hK => ?_⟩
    · obtain ⟨W, hKW, -, v, hv⟩ := hcover K hK hKΩ
      have hmono : μ.restrict K ≤ μ.restrict (W : Set E) := Measure.restrict_mono hKW le_rfl
      exact ((Lp.memLp (W1p.value v)).mono_measure hmono).ae_eq (ae_mono hmono hv)
    · obtain ⟨W, hKW, hWΩ, v, hv⟩ := hcover K hK hKΩ
      have hmono : μ.restrict K ≤ μ.restrict (W : Set E) := Measure.restrict_mono hKW le_rfl
      have hae : (fun x => innerSL ℝ (W1p.gradient v x)) =ᵐ[μ.restrict W] D :=
        ((W1p.hasWeakFDerivOn v).congr_ae hv).ae_eq (hD.mono hWΩ)
      exact (((innerSL ℝ).comp_memLp' (Lp.memLp (W1p.gradient v))).mono_measure hmono).ae_eq
        (ae_mono hmono hae)

end InnerProduct

section Planar

/-- On open subsets of `ℂ`, the order-one planar class `MemWkpLoc p Ω 1` is `MemW1pLoc p Ω`. -/
@[simp]
theorem memWkpLoc_one_iff_memW1pLoc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} {Ω : Opens ℂ} {u : ℂ → F} :
    MemWkpLoc p Ω 1 u ↔ MemW1pLoc p Ω u := by
  simp only [memWkpLoc_succ_iff_of_isOpen, memWkpLoc_zero_iff, memW1pLoc_iff]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℂ}

/-- **The `W1p` norm is bounded by the `W^{1,p}` norm.** A real function `u` whose `W^{1,p}(Ω)`
norm `TauCeti.eLpNormWkp p Ω 1 u` is finite is represented by an element of `W1p volume Ω p` whose
extended norm is at most `eLpNormWkp p Ω 1 u`. -/
theorem exists_w1p_enorm_le_eLpNormWkp {u : ℂ → ℝ} (hu : eLpNormWkp p Ω 1 u ≠ ∞) :
    ∃ v : W1p volume Ω p, W1p.value v =ᵐ[volume.restrict Ω] u ∧ ‖v‖ₑ ≤ eLpNormWkp p Ω 1 u := by
  obtain ⟨D, hD, hDfin⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hu
  rw [Opens.interior_coe] at hD
  rw [eLpNormWkp_zero, ← lt_top_iff_ne_top] at hDfin
  have hu1 : MemLp u p (volume.restrict Ω) :=
    memLp_iff.2 (lt_top_iff_ne_top.2 (ne_top_of_le_ne_top hu eLpNorm_le_eLpNormWkp))
  obtain ⟨v, hv, hg⟩ :=
    W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn hu1 (memLp_iff.2 hDfin) hD
  rw [eLpNormWkp_succ_eq_of_hasWeakFDerivOn hD, eLpNormWkp_zero]
  exact ⟨v, hv, W1p.enorm_le_eLpNorm_add_eLpNorm_of_ae_eq hv hg⟩

end Planar

end TauCeti
