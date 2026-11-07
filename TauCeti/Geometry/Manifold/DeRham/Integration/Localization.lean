/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Euclidean
import TauCeti.Geometry.Manifold.DeRham.Integration.Surjective

/-!
# Localization of compactly supported top-degree cohomology

Using the finite open-cover decomposition in
`TauCeti.compactlySupportedDeRhamCohomology.exists_sum_extendByZero`, this file expresses top-degree
classes as linear combinations of normalized coordinate-domain classes. On a domain diffeomorphic
to the model space, integration identifies compactly supported top-degree cohomology with the
scalars. Consequently a class coming from such a domain is zero if its integral is zero.

These statements isolate the local ingredients in the computation of top compactly supported
cohomology on connected oriented manifolds. They do not assert that integration is injective on
an arbitrary manifold: comparing normalized generators on different coordinate domains requires
connectedness.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17,
  the proof of the integration theorem for compactly supported top-degree cohomology.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public noncomputable section

open Set TopologicalSpace Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {n : ℕ}

namespace compactlySupportedDeRhamCohomology

variable [BoundarylessManifold I M]

/-- On a manifold diffeomorphic to its finite-dimensional model space, integration on top
compactly supported cohomology is bijective, for any orientation, including in dimension zero. -/
theorem bijective_integral_of_diffeomorph_normedSpace [SigmaCompactSpace M]
    (o : Manifold.Orientation I M (Fin n)) (Φ : E ≃ₘ⟮𝓘(ℝ, E), I⟯ M) :
    Function.Bijective (integral o) := by
  -- `H^n_c(M) ≅ H^n_c(E)` is a line, and integration onto `ℝ` is surjective.
  have : Nonempty M := ⟨Φ 0⟩
  have hfin : finrank ℝ (compactlySupportedDeRhamCohomology I M n) = finrank ℝ ℝ := by
    rw [(equivOfDiffeomorph Φ n).finrank_eq, finrank_self]
    exact finrank_compactlySupportedDeRhamCohomology_normedSpace E (by simpa using o.card_eq.symm)
  have : FiniteDimensional ℝ (compactlySupportedDeRhamCohomology I M n) :=
    Module.finite_of_finrank_eq_succ (hfin.trans (finrank_self ℝ))
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr
    (surjective_integral o), surjective_integral o⟩

/-- A class extended by zero from a Euclidean coordinate domain vanishes if its integral
vanishes. No connectedness of the ambient manifold or of the larger open subset is required. -/
theorem eq_zero_of_integral_eq_zero_of_mem_range_extendByZero
    (o : Manifold.Orientation I M (Fin n)) {U W : Opens M}
    [SigmaCompactSpace W] (h : U ≤ W)
    (Φ : E ≃ₘ⟮𝓘(ℝ, E), I⟯ U) {c : compactlySupportedDeRhamCohomology I W n}
    (hc : c ∈ LinearMap.range (extendByZero h n))
    (hzero : integral (o.restrict W) c = 0) : c = 0 := by
  have : SigmaCompactSpace U :=
    ⟨Φ.toHomeomorph.surjective.range_eq ▸ isSigmaCompact_range Φ.continuous⟩
  obtain ⟨d, rfl⟩ := hc
  rw [integral_extendByZero] at hzero
  have hd : d = 0 := (bijective_integral_of_diffeomorph_normedSpace (o.restrict U) Φ).injective
    (hzero.trans (map_zero _).symm)
  simp [hd]

/-- Normalized top-degree classes on a cover by Euclidean coordinate domains generate the
compactly supported top-degree cohomology of their union. The coefficients are finite in number,
even when the cover is infinite. -/
theorem exists_sum_smul_extendByZero (o : Manifold.Orientation I M (Fin n))
    {W : Opens M} [SigmaCompactSpace W] {ι : Type*} (U : ι → Opens M)
    [∀ i, SigmaCompactSpace (U i)] (hU : ∀ i, U i ≤ W) (hcover : W ≤ iSup U)
    (Φ : ∀ i, E ≃ₘ⟮𝓘(ℝ, E), I⟯ U i)
    (b : ∀ i, compactlySupportedDeRhamCohomology I (U i) n)
    (hb : ∀ i, integral (o.restrict (U i)) (b i) = 1)
    (c : compactlySupportedDeRhamCohomology I W n) :
    ∃ s : Finset ι, ∃ a : ι → ℝ,
      c = ∑ i ∈ s, a i • extendByZero (hU i) n (b i) := by
  obtain ⟨s, d, hd⟩ := exists_sum_extendByZero U hU hcover
    (by simpa using o.card_eq.ge) c
  let a (i : ι) := integral (o.restrict (U i)) (d i)
  have hdb (i : ι) : d i = a i • b i :=
    (bijective_integral_of_diffeomorph_normedSpace (o.restrict (U i)) (Φ i)).injective
      (by simp [a, hb])
  refine ⟨s, a, ?_⟩
  simpa only [hdb, map_smul] using hd

end compactlySupportedDeRhamCohomology

/-- A compactly supported smooth top form supported inside a Euclidean coordinate domain is
compactly supported exact in any larger open subset if and only if its integral is zero. -/
theorem mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero_of_tsupport_subset
    [BoundarylessManifold I M] (o : Manifold.Orientation I M (Fin n)) {U W : Opens M}
    [SigmaCompactSpace W] (h : U ≤ W)
    (Φ : E ≃ₘ⟮𝓘(ℝ, E), I⟯ U) {φ : SmoothForm I W ℝ n}
    (hφ : φ ∈ compactlySupportedForms I W n)
    (hs : _root_.tsupport (α := E [⋀^Fin n]→L[ℝ] ℝ) φ.1 ⊆ {x | (x : M) ∈ U}) :
    φ ∈ exactCompactlySupportedForms I W n ↔ integralTopForm (o.restrict W) φ.1 = 0 := by
  refine ⟨integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms (o.restrict W), fun hz ↦ ?_⟩
  have hn : finrank ℝ E ≤ n := by simpa using o.card_eq.ge
  let φd := compactlySupportedForms.toClosedOfFinrankLe I hn ⟨φ, hφ⟩
  obtain ⟨ψ, hψ⟩ := (compactlySupportedForms.mem_range_extendByZero_iff h
    (φ := ⟨φ, hφ⟩)).mpr hs
  let ψd := compactlySupportedForms.toClosedOfFinrankLe I hn ψ
  have hext : compactlySupportedClosedForms.extendByZero h n ψd = φd := by
    simpa only [compactlySupportedForms.toClosedOfFinrankLe_extendByZero] using
      congrArg (compactlySupportedForms.toClosedOfFinrankLe I hn) hψ
  have hcoe : (φd : SmoothForm I W ℝ n) = φ :=
    compactlySupportedForms.coe_toClosedOfFinrankLe I hn ⟨φ, hφ⟩
  rw [← hcoe]
  apply (compactlySupportedDeRhamCohomology.mk_eq_zero_iff I n φd).mp
  apply compactlySupportedDeRhamCohomology.eq_zero_of_integral_eq_zero_of_mem_range_extendByZero
    o h Φ
  · exact ⟨compactlySupportedDeRhamCohomology.mk I n ψd, by
      rw [compactlySupportedDeRhamCohomology.extendByZero_mk, hext]⟩
  · simpa only [compactlySupportedDeRhamCohomology.integral_mk, φd,
      compactlySupportedForms.coe_toClosedOfFinrankLe] using hz

end TauCeti
