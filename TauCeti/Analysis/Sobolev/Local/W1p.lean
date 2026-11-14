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
additive Haar measure. This file compares the first-order local Sobolev class
`TauCeti.MemW1pLoc p Ω` of real-valued functions (and, on `ℂ`, the order-one planar class
`TauCeti.MemWkpLoc p Ω 1`) with `TauCeti.W1p`: a real function lies in `MemW1pLoc p Ω` exactly when
its restriction to every open `W` with compact closure contained in `Ω` is represented by an element
of `W1p volume W p`. The weak gradient of that element is dual, through
`InnerProductSpace.toDual`, to the weak derivative of the function on `Ω`. On `ℂ`, a real function
of finite `W^{1,p}(Ω)` norm `TauCeti.eLpNormWkp p Ω 1` is represented by an element of
`W1p volume Ω p` whose norm is at most that size.

## Main declarations

* `TauCeti.MemW1pLoc.exists_w1p`: a real member of `MemW1pLoc p Ω` is represented by an element of
  `W1p` on every relatively compact open subset of `Ω`, with the dual weak gradient.
* `TauCeti.memW1pLoc_iff_forall_w1p`: characterization of real-valued `MemW1pLoc p Ω` by
  `W1p volume W p` on relatively compact open subsets `W` of `Ω`.
* `TauCeti.MemWkpLoc.exists_w1p`, `TauCeti.memWkpLoc_one_iff_forall_w1p`: the planar
  specializations for `MemWkpLoc p Ω 1`.
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
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E}

/-- **Local Sobolev functions are Sobolev on relatively compact subdomains.** Let
`u ∈ MemW1pLoc p Ω` be real-valued, with weak derivative `D` on `Ω`. On every open `W` whose
closure is compact and contained in `Ω`, `u` is represented by an element of `W1p volume W p`
whose weak gradient is dual to `D`. -/
theorem MemW1pLoc.exists_w1p {u : E → ℝ} (hu : MemW1pLoc p Ω u)
    {D : E → E →L[ℝ] ℝ} (hD : HasWeakFDerivOn volume Ω u D) {W : Opens E}
    (hWc : IsCompact (closure (W : Set E))) (hWΩ : closure (W : Set E) ⊆ Ω) :
    ∃ v : W1p volume W p, W1p.value v =ᵐ[volume.restrict W] u ∧
      W1p.gradient v =ᵐ[volume.restrict W]
        fun x => (InnerProductSpace.toDual ℝ E).symm (D x) := by
  have hmono : volume.restrict (W : Set E) ≤ volume.restrict (closure (W : Set E)) :=
    Measure.restrict_mono subset_closure le_rfl
  exact W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn
    ((memLpLoc_iff.1 hu.memLpLoc _ hWΩ hWc).mono_measure hmono)
    ((memLpLoc_iff.1 (hu.memLpLoc_of_hasWeakFDerivOn hD) _ hWΩ hWc).mono_measure hmono)
    (hD.mono (SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ)))

/-- **Comparison of `MemW1pLoc` with `W1p`.** A real-valued function on `Ω ⊆ E` lies in
`MemW1pLoc p Ω` if and only if its restriction to every open `W` with compact closure contained in
`Ω` is represented by an element of `W1p volume W p`. The weak gradients then correspond to the
weak derivative of `u` on `Ω` through `InnerProductSpace.toDual`, by
`TauCeti.MemW1pLoc.exists_w1p`. -/
theorem memW1pLoc_iff_forall_w1p {u : E → ℝ} :
    MemW1pLoc p Ω u ↔ ∀ W : Opens E, IsCompact (closure (W : Set E)) →
      closure (W : Set E) ⊆ Ω → ∃ v : W1p volume W p, W1p.value v =ᵐ[volume.restrict W] u := by
  constructor
  · intro hu W hWc hWΩ
    obtain ⟨D, hD, -⟩ := hu.exists_hasWeakFDerivOn
    obtain ⟨v, hv, -⟩ := hu.exists_w1p hD hWc hWΩ
    exact ⟨v, hv⟩
  · intro h
    have hcover : ∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ W : Opens E, K ⊆ W ∧ W ≤ Ω ∧
        ∃ v : W1p volume W p, W1p.value v =ᵐ[volume.restrict W] u := by
      intro K hK hKΩ
      obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
      exact ⟨W, hKW, SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ), h W hWc hWΩ⟩
    obtain ⟨D, hD⟩ : ∃ D : E → E →L[ℝ] ℝ, HasWeakFDerivOn volume Ω u D := by
      refine exists_hasWeakFDerivOn_iff_locally.2 fun x hx => ?_
      obtain ⟨W, hxW, -, v, hv⟩ := hcover {x} isCompact_singleton (singleton_subset_iff.2 hx)
      exact ⟨W, hxW rfl, _, (W1p.hasWeakFDerivOn v).congr_ae hv⟩
    refine memW1pLoc_iff.2
      ⟨memLpLoc_iff.2 fun K hKΩ hK => ?_, D, hD, memLpLoc_iff.2 fun K hKΩ hK => ?_⟩
    · obtain ⟨W, hKW, -, v, hv⟩ := hcover K hK hKΩ
      have hmono : volume.restrict K ≤ volume.restrict (W : Set E) :=
        Measure.restrict_mono hKW le_rfl
      exact ((Lp.memLp (W1p.value v)).mono_measure hmono).ae_eq (ae_mono hmono hv)
    · obtain ⟨W, hKW, hWΩ, v, hv⟩ := hcover K hK hKΩ
      have hmono : volume.restrict K ≤ volume.restrict (W : Set E) :=
        Measure.restrict_mono hKW le_rfl
      have hae : (fun x => innerSL ℝ (W1p.gradient v x)) =ᵐ[volume.restrict W] D :=
        ((W1p.hasWeakFDerivOn v).congr_ae hv).ae_eq (hD.mono hWΩ)
      exact (((innerSL ℝ).comp_memLp' (Lp.memLp (W1p.gradient v))).mono_measure hmono).ae_eq
        (ae_mono hmono hae)

end InnerProduct

section Planar

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℂ}

/-- **Local Sobolev functions on `ℂ` are Sobolev on relatively compact subdomains.** Let
`u ∈ MemWkpLoc p Ω 1` be real-valued, with weak derivative `D` on `Ω`. On every open `W` whose
closure is compact and contained in `Ω`, `u` is represented by an element of `W1p volume W p`
whose weak gradient is dual to `D`. -/
theorem MemWkpLoc.exists_w1p {u : ℂ → ℝ} (hu : MemWkpLoc p Ω 1 u)
    {D : ℂ → ℂ →L[ℝ] ℝ} (hD : HasWeakFDerivOn volume Ω u D) {W : Opens ℂ}
    (hWc : IsCompact (closure (W : Set ℂ))) (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    ∃ v : W1p volume W p, W1p.value v =ᵐ[volume.restrict W] u ∧
      W1p.gradient v =ᵐ[volume.restrict W]
        fun z => (InnerProductSpace.toDual ℝ ℂ).symm (D z) :=
  (memWkpLoc_one_iff_memW1pLoc.1 hu).exists_w1p hD hWc hWΩ

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

/-- **Comparison with `W1p` at order one.** A real function lies in `MemWkpLoc p Ω 1` exactly when
its restriction to every open `W` with compact closure contained in `Ω` is represented by an element
of `W1p volume W p`. The weak gradients then correspond to the weak derivative of `u` on `Ω`
through `InnerProductSpace.toDual`, by `TauCeti.MemWkpLoc.exists_w1p`. -/
theorem memWkpLoc_one_iff_forall_w1p {u : ℂ → ℝ} :
    MemWkpLoc p Ω 1 u ↔ ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) →
      closure (W : Set ℂ) ⊆ Ω → ∃ v : W1p volume W p, W1p.value v =ᵐ[volume.restrict W] u :=
  memWkpLoc_one_iff_memW1pLoc.trans memW1pLoc_iff_forall_w1p

end Planar

end TauCeti
