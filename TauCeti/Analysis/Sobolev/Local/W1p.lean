/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.Local.Norm
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Local

/-!
# Order-one local Sobolev functions and `W1p`

Let `Ω ⊆ ℂ` be open. This file compares the order-one local Sobolev class `TauCeti.MemWkpLoc p Ω 1`
of real functions with the library's `TauCeti.W1p`: a real function lies in `MemWkpLoc p Ω 1`
exactly when its restriction to every open `W` with compact closure contained in `Ω` is represented
by an element of `W1p volume W p`. The weak gradient of that element is dual, through
`InnerProductSpace.toDual`, to the weak derivative of the function on `Ω`. A real function of
finite `W^{1,p}(Ω)` norm `TauCeti.eLpNormWkp p Ω 1` is represented by an element of
`W1p volume Ω p` whose norm is at most that size.

## Main declarations

* `TauCeti.MemWkpLoc.exists_w1p`: a real member of `MemWkpLoc p Ω 1` is represented by an element
  of `W1p` on every relatively compact open subset of `Ω`, with the dual weak gradient.
* `TauCeti.exists_w1p_enorm_le_eLpNormWkp`: a real function of finite `W^{1,p}(Ω)` norm is
  represented in `W1p volume Ω p` with no larger norm.
* `TauCeti.memWkpLoc_one_iff_forall_w1p`: the order-one comparison with `W1p`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces).
-/

public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℂ}

/-- **Local Sobolev functions are Sobolev on relatively compact subdomains.** Let
`u ∈ MemWkpLoc p Ω 1` be real-valued, with weak derivative `D` on `Ω`. On every open `W` whose
closure is compact and contained in `Ω`, `u` is represented by an element of `W1p volume W p`
whose weak gradient is dual to `D`. -/
theorem MemWkpLoc.exists_w1p {u : ℂ → ℝ} (hu : MemWkpLoc p Ω 1 u)
    {D : ℂ → ℂ →L[ℝ] ℝ} (hD : HasWeakFDerivOn volume Ω u D) {W : Opens ℂ}
    (hWc : IsCompact (closure (W : Set ℂ))) (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    ∃ v : W1p volume W p, W1p.value v =ᵐ[volume.restrict W] u ∧
      W1p.gradient v =ᵐ[volume.restrict W]
        fun z => (InnerProductSpace.toDual ℝ ℂ).symm (D z) := by
  have hmono : volume.restrict (W : Set ℂ) ≤ volume.restrict (closure (W : Set ℂ)) :=
    Measure.restrict_mono subset_closure le_rfl
  exact W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn
    ((memLpLoc_iff.1 hu.memLpLoc _ hWΩ hWc).mono_measure hmono)
    ((memLpLoc_iff.1 (hu.memLpLoc_of_hasWeakFDerivOn hD) _ hWΩ hWc).mono_measure hmono)
    (hD.mono (SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ)))

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
      closure (W : Set ℂ) ⊆ Ω → ∃ v : W1p volume W p, W1p.value v =ᵐ[volume.restrict W] u := by
  constructor
  · intro hu W hWc hWΩ
    obtain ⟨D, hD, -⟩ := hu.exists_weakFDeriv_of_isOpen
    obtain ⟨v, hv, -⟩ := hu.exists_w1p hD hWc hWΩ
    exact ⟨v, hv⟩
  · intro h
    have hcover : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ W : Opens ℂ, K ⊆ W ∧ W ≤ Ω ∧
        ∃ v : W1p volume W p, W1p.value v =ᵐ[volume.restrict W] u := by
      intro K hK hKΩ
      obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
      exact ⟨W, hKW, SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ), h W hWc hWΩ⟩
    obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ →L[ℝ] ℝ, HasWeakFDerivOn volume Ω u D := by
      refine exists_hasWeakFDerivOn_iff_locally.2 fun x hx => ?_
      obtain ⟨W, hxW, -, v, hv⟩ := hcover {x} isCompact_singleton (singleton_subset_iff.2 hx)
      exact ⟨W, hxW rfl, _, (W1p.hasWeakFDerivOn v).congr_ae hv⟩
    refine memWkpLoc_succ_iff_of_isOpen.2 ⟨memLpLoc_iff.2 fun K hKΩ hK => ?_, D, hD,
      memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hKΩ hK => ?_)⟩
    · obtain ⟨W, hKW, -, v, hv⟩ := hcover K hK hKΩ
      have hmono : volume.restrict K ≤ volume.restrict (W : Set ℂ) :=
        Measure.restrict_mono hKW le_rfl
      exact ((Lp.memLp (W1p.value v)).mono_measure hmono).ae_eq (ae_mono hmono hv)
    · obtain ⟨W, hKW, hWΩ, v, hv⟩ := hcover K hK hKΩ
      have hmono : volume.restrict K ≤ volume.restrict (W : Set ℂ) :=
        Measure.restrict_mono hKW le_rfl
      have hae : (fun z => innerSL ℝ (W1p.gradient v z)) =ᵐ[volume.restrict W] D :=
        ((W1p.hasWeakFDerivOn v).congr_ae hv).ae_eq (hD.mono hWΩ)
      exact (((innerSL ℝ).comp_memLp' (Lp.memLp (W1p.gradient v))).mono_measure hmono).ae_eq
        (ae_mono hmono hae)

end TauCeti
