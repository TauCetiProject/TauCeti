/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.ApproximationDomain
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.SuccessiveMinima

/-!
# Basic properties of successive minima of an approximation domain

For independent forms and positive level, the successive minima over the number field are
positive below the ambient dimension and are realized by one linearly independent family.
-/

public section

open Module NumberField NumberField.mixedEmbedding

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

open scoped Pointwise in
/-- **A family realizing the successive minima of an approximation domain.** For forms
independent at the infinite places and at `S₀` and a level `Q > 0`, there are `card ι` linearly
independent vectors `x l` of the lattice `approxModule S₀ L c Q` whose mixed embeddings lie in the
dilate of `approxBody L c Q` by the `l`-th successive minimum over `K`. Read at the infinite places
with `TauCeti.NumberField.mixedEmbedding_mem_smul_approxBody_iff`, this is
`v (L v i (x l)) ≤ μ l · Q ^ c v i`. -/
theorem exists_linearIndependent_mem_smul_successiveMinimum_approx
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    ∃ x : Fin (Fintype.card ι) → ι → K, LinearIndependent K x ∧
      ∀ l, x l ∈ approxModule S₀ L c Q ∧ (fun j ↦ mixedEmbedding K (x l j)) ∈
        (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l • approxBody L c Q := by
  let _ := discreteTopology_mixedImage_approxModule hLfin c Q
  let _ := isZLattice_mixedImage_approxModule hLfin c hQ.ne'
  obtain ⟨B, hcoe, hB⟩ := exists_convexBody_eq_approxBody hLinf c hQ
  obtain ⟨x, hx, hxB⟩ :=
    (approxModule S₀ L c Q).exists_linearIndependent_mem_smul_successiveMinimum hB
  rw [hcoe] at hxB
  exact ⟨x, hx, hxB⟩

/-- Below `card ι`, the successive minima over `K` of an approximation domain of positive level,
with forms independent at the infinite places and at `S₀`, are positive. -/
theorem successiveMinimum_approx_pos {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) {l : ℕ} (hl : l < Fintype.card ι) :
    0 < (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l := by
  let _ := discreteTopology_mixedImage_approxModule hLFin c Q
  let _ := isZLattice_mixedImage_approxModule hLFin c hQ.ne'
  obtain ⟨B, hcoe, hB⟩ := exists_convexBody_eq_approxBody hLInf c hQ
  simpa only [hcoe] using (approxModule S₀ L c Q).successiveMinimum_pos hB hl

end TauCeti.NumberField
