/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Trace.Domain
public import TauCeti.Analysis.CStarAlgebra.Trace.LowerSemicontinuous
public import TauCeti.Analysis.CStarAlgebra.Trace.Matrix

/-!
# The matrix amplification of a densely defined trace

A trace `τ` on a C⋆-algebra `B` (`TauCeti.IsTrace`) is densely defined when its finite part
`𝔪_τ⁺` is dense in `B₊` (`TauCeti.IsDenselyDefined`). Then the domain `𝔪_τ`, a subspace
containing `𝔪_τ⁺`, has closure containing `B₊`, which spans `B`, so `𝔪_τ` is dense in `B`; since
`𝔪_τ ⊆ 𝔫_τ`, the square-integrable elements are dense too
(`TauCeti.IsTrace.dense_domain_of_isDenselyDefined`,
`TauCeti.IsTrace.dense_sqIntegrable_of_isDenselyDefined`).

The **matrix amplification** `τ_n(x) = Σᵢ τ(xᵢᵢ)` of a densely defined trace is densely defined
(`TauCeti.IsTrace.isDenselyDefined_matrixTrace`), one clause of TracesOnCStarAlgebras Tr1.3: write
a positive matrix as `R⋆R` and approximate `R` entrywise by matrices over `𝔫_τ`, which lie in
`𝔫_{τ_n}` (`TauCeti.IsTrace.mem_sqIntegrable_matrixTrace_iff`); their products `R_k⋆R_k` lie in
`𝔪_{τ_n}⁺` and converge to `R⋆R`.

## Main results

* `TauCeti.IsTrace.dense_domain_of_isDenselyDefined`: `𝔪_τ` is dense in `B`.
* `TauCeti.IsTrace.dense_sqIntegrable_of_isDenselyDefined`: `𝔫_τ` is dense in `B`.
* `TauCeti.IsTrace.isDenselyDefined_matrixTrace`: `τ_n` is densely defined when `τ` is.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {τ : B → ℝ≥0∞}

namespace IsTrace

/-- **The domain of a densely defined trace is dense.** -/
theorem dense_domain_of_isDenselyDefined (hd : IsDenselyDefined τ) :
    Dense (domain τ : Set B) := by
  -- The closure of `𝔪_τ` is a subspace containing `B₊`, which spans `B`.
  have h : {x : B | 0 ≤ x} ⊆ (domain τ).topologicalClosure :=
    (isDenselyDefined_iff.1 hd).trans (closure_mono finitePart_subset_domain)
  have htop : (domain τ).topologicalClosure = ⊤ :=
    eq_top_iff.2 (CStarAlgebra.span_nonneg (A := B) ▸ Submodule.span_le.2 h)
  rw [← Submodule.dense_iff_topologicalClosure_eq_top] at htop
  exact htop

/-- **The square-integrable elements of a densely defined trace are dense.** -/
theorem dense_sqIntegrable_of_isDenselyDefined (hτ : IsTrace τ) (hd : IsDenselyDefined τ) :
    Dense (sqIntegrable τ) :=
  (dense_domain_of_isDenselyDefined hd).mono hτ.domain_subset_sqIntegrable

variable {n : Type*} [Fintype n]

/-- **The matrix amplification of a densely defined trace is densely defined.** -/
theorem isDenselyDefined_matrixTrace (hτ : IsTrace τ) (hd : IsDenselyDefined τ) :
    IsDenselyDefined (matrixTrace τ n) := by
  refine isDenselyDefined_iff.2 fun x hx ↦ ?_
  obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (show 0 ≤ x from hx)
  -- Matrices over `𝔫_τ` are dense in `M_n(B)`, whose topology is the entrywise one.
  have hS : Dense (Set.univ.pi fun _ : n ↦ Set.univ.pi fun _ : n ↦ sqIntegrable τ :
      Set (CStarMatrix n n B)) :=
    dense_pi Set.univ fun _ _ ↦
      dense_pi Set.univ fun _ _ ↦ hτ.dense_sqIntegrable_of_isDenselyDefined hd
  have hcont : Continuous fun S : CStarMatrix n n B ↦ star S * S :=
    continuous_star.mul continuous_id
  refine map_mem_closure (f := fun S : CStarMatrix n n B ↦ star S * S) hcont (hS R)
    fun S hSmem ↦ ?_
  refine star_mul_self_mem_finitePart_iff.2 (hτ.mem_sqIntegrable_matrixTrace_iff.2 fun i j ↦ ?_)
  exact hSmem i (Set.mem_univ i) j (Set.mem_univ j)

end IsTrace

end TauCeti
