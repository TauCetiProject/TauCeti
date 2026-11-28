/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.LinearForms
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Rank

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Ranks of approximation domains in Plücker coordinates

If a domain contains the Plücker vectors of the `p`-subfamilies meeting the first `k` indices
of a family, its span contains their wedge span. For an independent family of length `k + p`,
this bounds the rank from below. For a full basis, a proper domain span is exactly that wedge
span. The same containment bounds the first `N.choose p - 1` minima by one, where `N = k + p`,
leaving only the last minimum to estimate for the wedge domain.
-/

public section

open Module NumberField Set.powersetCard

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [LinearOrder ι]

/-- If the Plücker vectors of the `p`-subfamilies of `y` meeting the first `k` indices lie in an
approximation domain, their span `wedgeSpan k p y` lies in the span of the domain. -/
theorem wedgeSpan_le_approxSpan_of_forall_plucker_mem {N p k : ℕ}
    {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → Set.powersetCard ι p → Dual K (Set.powersetCard ι p → K)}
    {c : AbsoluteValue K ℝ → Set.powersetCard ι p → ℝ} {Q : ℝ}
    {y : Fin N → ι → K}
    (hyD : ∀ J : Set.powersetCard (Fin N) p, (∃ j ∈ J, (j : ℕ) < k) →
      plucker (y ∘ ofFinEmbEquiv.symm J) ∈ approxDomain S₀ L c Q) :
    wedgeSpan k p y ≤ approxSpan S₀ L c Q :=
  wedgeSpan_le_iff.2 fun J hJ ↦ mem_approxSpan_of_mem (hyD J hJ)

/-- If an approximation domain contains the Plücker vectors of the `p`-subfamilies of an
independent family of length `N = k + p` meeting the first `k` indices, its span has dimension
at least `N.choose p - 1`. -/
theorem choose_sub_one_le_finrank_approxSpan_of_forall_plucker_mem [Finite ι] {N p k : ℕ}
    {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → Set.powersetCard ι p → Dual K (Set.powersetCard ι p → K)}
    {c : AbsoluteValue K ℝ → Set.powersetCard ι p → ℝ} {Q : ℝ}
    (hkp : k + p = N) {y : Fin N → ι → K}
    (hy : LinearIndependent K y)
    (hyD : ∀ J : Set.powersetCard (Fin N) p, (∃ j ∈ J, (j : ℕ) < k) →
      plucker (y ∘ ofFinEmbEquiv.symm J) ∈ approxDomain S₀ L c Q) :
    N.choose p - 1 ≤ finrank K (approxSpan S₀ L c Q) := by
  let _ := Fintype.ofFinite ι
  have hW := wedgeSpan_le_approxSpan_of_forall_plucker_mem hyD
  have hrank := finrank_wedgeSpan_add_one hy hkp
  have hle : N.choose p - 1 ≤ finrank K (wedgeSpan k p y) := by omega
  exact hle.trans (Submodule.finrank_mono hW)

variable [Fintype ι]

/-- A proper approximation-domain span containing all Plücker vectors of the `p`-subfamilies of
a basis meeting the first `k` indices is their wedge span when `k + p = card ι`. -/
theorem approxSpan_eq_wedgeSpan_of_forall_plucker_mem {p k : ℕ}
    {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → Set.powersetCard ι p → Dual K (Set.powersetCard ι p → K)}
    {c : AbsoluteValue K ℝ → Set.powersetCard ι p → ℝ} {Q : ℝ}
    (hkp : k + p = Fintype.card ι) {y : Fin (Fintype.card ι) → ι → K}
    (hy : LinearIndependent K y)
    (hyD : ∀ J : Set.powersetCard (Fin (Fintype.card ι)) p, (∃ j ∈ J, (j : ℕ) < k) →
      plucker (y ∘ ofFinEmbEquiv.symm J) ∈ approxDomain S₀ L c Q)
    (hproper : approxSpan S₀ L c Q ≠ ⊤) :
    approxSpan S₀ L c Q = wedgeSpan k p y := by
  have hle := wedgeSpan_le_approxSpan_of_forall_plucker_mem hyD
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  have hrank := Submodule.finrank_lt hproper
  rw [finrank_fintype_fun_eq_card, Set.powersetCard.fintypeCard] at hrank
  have hwedge := finrank_wedgeSpan_add_one hy hkp
  omega

/-- If an approximation domain contains the Plücker vectors of the `p`-subfamilies of an
independent family of length `N = k + p` meeting the first `k` indices, its first
`N.choose p - 1` successive minima over `K` are at most `1`. -/
theorem successiveMinimum_le_one_of_forall_plucker_mem {N p k : ℕ} {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → Set.powersetCard ι p → Dual K (Set.powersetCard ι p → K)}
    {c : AbsoluteValue K ℝ → Set.powersetCard ι p → ℝ} {Q : ℝ}
    (hkp : k + p = N) {y : Fin N → ι → K}
    (hy : LinearIndependent K y)
    (hyD : ∀ J : Set.powersetCard (Fin N) p, (∃ j ∈ J, (j : ℕ) < k) →
      plucker (y ∘ ofFinEmbEquiv.symm J) ∈ approxDomain S₀ L c Q)
    {l : ℕ} (hl : l < N.choose p - 1) :
    (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ≤ 1 := by
  have := choose_sub_one_le_finrank_approxSpan_of_forall_plucker_mem hkp hy hyD
  exact successiveMinimum_le_one_of_lt_finrank_approxSpan (by omega)

end TauCeti.NumberField
