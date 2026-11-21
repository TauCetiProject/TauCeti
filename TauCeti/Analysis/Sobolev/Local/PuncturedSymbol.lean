/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.SymbolClass
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Sobolev.Local.Lipschitz

/-!
# Punctured symbols of order at least two are locally `W^{2,∞}`

A punctured symbol of order `ℓ` on the plane (`TauCeti.IsPuncturedSymbol`) is smooth on a
punctured disc about `0`, with `j`-th derivative `O(|z| ^ (ℓ - j))`. Nothing is asked at `0`, so a
priori its classical derivatives only live on the punctured disc. When `ℓ ≥ 2` and the symbol
vanishes at `0`, it is `C¹` on a disc about `0` with Lipschitz derivative
(`TauCeti.IsPuncturedSymbol.exists_contDiffOn_holderOnWith_fderiv`), and this file deduces that it
lies in the local Sobolev class `W^{2,∞}` on that disc
(`TauCeti.IsPuncturedSymbol.exists_memWkpLoc_two`). The value at `0` is irrelevant there, since
changing it alters the symbol only on a null set. Its first weak derivative is its classical
derivative, which exists at `0` as well, and its second weak derivative is the classical second
derivative on the punctured disc: the Lipschitz first derivative is weakly differentiable across
the origin, with weak derivative its almost-everywhere derivative, bounded by the Lipschitz
constant. So the derivative bounds of a symbol of order `ℓ ≥ 2` survive at the puncture in the
Sobolev sense, as needed to use such a symbol as a coefficient in elliptic estimates.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix E (the Micallef–White theorem, whose proof uses
  symbols of order at least two on the punctured disc as `C^{1,α}` elliptic coefficients).
-/

public section

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ℓ : ℝ}
  {f : ℂ → F}

/-- **A punctured symbol of order at least two is locally `W^{2,∞}`.** A punctured symbol on the
plane of order `ℓ ≥ 2`, with values in a finite-dimensional space, lies in the local Sobolev class
`W^{2,∞}` on a disc about `0`, whatever its value at `0`. -/
theorem IsPuncturedSymbol.exists_memWkpLoc_two (hf : IsPuncturedSymbol ℓ f) (hℓ : 2 ≤ ℓ) :
    ∃ r > 0, MemWkpLoc ⊤ (Metric.ball (0 : ℂ) r) 2 f := by
  -- vanish at `0` first: this changes `f` only on a null set, invisible to `MemWkpLoc`
  set g := Function.update f 0 0
  have hg : IsPuncturedSymbol ℓ g :=
    hf.congr (eventually_nhdsWithin_of_forall fun _ hz ↦ (Function.update_of_ne hz _ _).symm)
  obtain ⟨r, hr, hC1, C, hC⟩ := hg.exists_contDiffOn_holderOnWith_fderiv (α := 1) one_pos
    (by push_cast; linarith) le_rfl (Function.update_self _ _ _)
  refine ⟨r, hr, MemWkpLoc.congr_ae (f := g) ?_ ?_⟩
  · -- read the ball as an open set, as `memWkpLoc_two_of_locallyLipschitzOn_fderiv` needs
    rw [← TopologicalSpace.Opens.coe_mk (hU := Metric.isOpen_ball (x := (0 : ℂ)) (ε := r))]
      at hC1 hC ⊢
    exact (hC1.differentiableOn one_ne_zero).memWkpLoc_two_of_locallyLipschitzOn_fderiv
      fun _ _ ↦ ⟨C, _, self_mem_nhdsWithin, holderOnWith_one.1 hC⟩
  · filter_upwards [MeasureTheory.ae_restrict_of_ae
      (MeasureTheory.compl_mem_ae_iff.2 (MeasureTheory.measure_singleton (0 : ℂ)))] with z hz
    exact Function.update_of_ne hz _ _

end TauCeti
