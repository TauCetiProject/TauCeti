/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Nondegenerate

import TauCeti.Geometry.Symplectic.Darboux.SkewAdjoint
import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Toral

/-!
# Williamson's classification of split Cartan subalgebras of `sp(V, ω)`

Let `(V, ω)` be a finite-dimensional real symplectic vector space. A family `Q` of quadratic forms
is nondegenerate (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily`) when the Hamiltonian
endomorphisms `A_{Q i}` generate a Cartan subalgebra `𝔥` of `sp(V, ω)`; these are the Hessian data
of the nondegenerate rank-zero singular points of integrable systems. Williamson's theorem sorts
such subalgebras into elliptic, hyperbolic and focus-focus blocks. This file proves the
classification in the **split** case, where every `A_{Q i}` has real spectrum (its generalized
eigenspaces span `V`): such a family spans the same space of quadratic forms as the hyperbolic
blocks `Hₖ = xₖ yₖ` (`TauCeti.SymplecticForm.hyperbolic`) of some Darboux basis
`(q₁, p₁, …, qₙ, pₙ)`
(`IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_hyperbolic`).
Conversely the span of the hyperbolic blocks of a Darboux basis is nondegenerate and split, so this
characterizes the split nondegenerate families
(`TauCeti.SymplecticForm.exists_isDarbouxBasis_span_eq_span_hyperbolic_iff`).

The linear algebra behind it is the simultaneous hyperbolic normal form
(`TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq_smul_of_skewAdjoint`): a pairwise
commuting family `f` of semisimple elements of `sp(V, ω)` with real spectra is diagonal in a
Darboux basis, with opposite eigenvalues on each pair, `f i qₖ = c i k • qₖ` and
`f i pₖ = -c i k • pₖ`.

For a nondegenerate family the members are semisimple and commute
(`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.isSemisimple_hamiltonianEnd`), so in such
a basis every `A_{Q i}` is `∑ₖ c i k A_{Hₖ}`, that is `Q i = ∑ₖ c i k Hₖ`. The hyperbolic blocks
Poisson-commute with these, and the span of a nondegenerate family is its own Poisson centralizer
(`IsNondegenerateQuadraticFamily.mem_span_of_forall_quadraticPoissonBracket_eq_zero`), so the two
spans agree. All names are in the namespace `TauCeti.SymplecticForm`.

## Main results

* `IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_hyperbolic`: a nondegenerate
  family with real spectra spans the hyperbolic blocks of a Darboux basis.
* `TauCeti.SymplecticForm.exists_isDarbouxBasis_span_eq_span_hyperbolic_iff`: a family spans the
  hyperbolic blocks of some Darboux basis exactly when it is nondegenerate with real spectra.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
-/

public section

open Module

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V}

/-! ### Split nondegenerate families -/

section Split

variable [FiniteDimensional ℝ V] {ι : Type*} {Q : ι → QuadraticForm ℝ V}

/-- **Williamson's theorem for split Cartan subalgebras.** A nondegenerate family of quadratic
forms whose Hamiltonian endomorphisms have real spectra (their generalized eigenspaces span `V`)
spans the same space of quadratic forms as the hyperbolic blocks `Hₖ = xₖ yₖ` of some Darboux
basis. -/
theorem IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_hyperbolic
    (h : ω.IsNondegenerateQuadraticFamily Q)
    (hsplit : ∀ i, ⨆ μ, (ω.hamiltonianEnd (Q i)).maxGenEigenspace μ = ⊤) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
      Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (hyperbolic b)) := by
  obtain ⟨n, b, c, hb, hc⟩ := exists_isDarbouxBasis_forall_apply_eq_smul_of_skewAdjoint
    (fun i ↦ ω.hamiltonianEnd (Q i)) (fun i ↦ ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra _)
    (fun i j _ ↦ (quadraticPoissonBracket_eq_zero_iff (ω := ω)).1
      (h.quadraticPoissonBracket_eq_zero i j))
    (fun i ↦ h.isSemisimple_hamiltonianEnd (Submodule.subset_span ⟨i, rfl⟩)) hsplit
  -- Each `Q i` is the combination `∑ₖ c i k Hₖ` of the hyperbolic blocks.
  have hQ (i : ι) : Q i ∈ Submodule.span ℝ (Set.range (hyperbolic b)) := by
    rw [hb.eq_sum_smul_ellipticHyperbolic_of_hamiltonianEnd_apply ∅ (R := Q i) (c := c i)
      (by simpa using hc i), ellipticHyperbolic_empty]
    exact Submodule.sum_mem _ fun k _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))
  refine ⟨n, b, hb, le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 hQ))
    (Submodule.span_le.2 (Set.range_subset_iff.2 fun k ↦ ?_))⟩
  -- Conversely each `Hₖ` Poisson-commutes with the `Q i`, so it lies in their span.
  exact h.mem_span_of_forall_quadraticPoissonBracket_eq_zero fun i ↦
    hb.isNondegenerateQuadraticFamily_hyperbolic.quadraticPoissonBracket_eq_zero_of_mem_span
      (Submodule.subset_span (Set.mem_range_self k)) (hQ i)

/-- **Classification of split nondegenerate families.** A family of quadratic forms spans the same
space as the hyperbolic blocks `Hₖ = xₖ yₖ` of some Darboux basis exactly when it is nondegenerate
and the Hamiltonian endomorphisms of its members have real spectra. -/
theorem exists_isDarbouxBasis_span_eq_span_hyperbolic_iff :
    (∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
      Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (hyperbolic b))) ↔
      ω.IsNondegenerateQuadraticFamily Q ∧
        ∀ i, ⨆ μ, (ω.hamiltonianEnd (Q i)).maxGenEigenspace μ = ⊤ := by
  refine ⟨?_, fun ⟨h, hsplit⟩ ↦ h.exists_isDarbouxBasis_span_eq_span_hyperbolic hsplit⟩
  rintro ⟨n, b, hb, hspan⟩
  refine ⟨(isNondegenerateQuadraticFamily_iff_of_span_eq hspan).2
    hb.isNondegenerateQuadraticFamily_hyperbolic, fun i ↦ ?_⟩
  -- Each `Q i` is a combination `∑ₖ cₖ Hₖ` of the hyperbolic blocks, hence diagonal in `b`.
  have hQ : Q i ∈ Submodule.span ℝ (Set.range (hyperbolic b)) := by
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hQ
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨⟨k, a⟩, rfl⟩
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · refine Submodule.mem_iSup_of_mem (c k) (Module.End.eigenspace_le_maxGenEigenspace
      (Module.End.mem_eigenspace_iff.2 ?_))
    simpa [← hc] using hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_fst ∅ c k
  · refine Submodule.mem_iSup_of_mem (-c k) (Module.End.eigenspace_le_maxGenEigenspace
      (Module.End.mem_eigenspace_iff.2 ?_))
    simpa [← hc] using hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_snd ∅ c k

end Split

end TauCeti.SymplecticForm
