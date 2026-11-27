/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Filtration

/-!
# The index filtration of the Bott complex

Suppose that every nonzero pushforward of Bott chain data strictly lowers the negative-normal rank,
`λ_C ≤ λ_D → P_CD = 0`: every nonconstant trajectory between distinct critical components lowers
the Morse index along the critical set. Then the Bott complex is filtered by the negative-normal
rank: the `q`th stage consists of the chains on the components with `λ_C ≤ q`. This is the
critical-value filtration of `TauCeti.BottChainData.filtration` for the value `v C = λ_C` and the
integer cut values `q ↦ q` (`TauCeti.BottChainData.indexSpectralSequence`).

Its bands contain the components of a single rank, so there are no trajectories inside a band. The
first page therefore has at `(p, q)`, with `p + q = -n`, the direct sum `⊕ H_(n - λ_C)(C)` of the
homology of the chains on the components `C` with `λ_C = q + 1`
(`TauCeti.BottChainData.indexSpectralSequenceFirstPageXIso`). In the homological indexing of a
filtered complex this is `E¹_(λ, m) = ⊕_(λ_C = λ) H_m(C)`, in total degree `λ + m`. Two adjacent
bands differ in rank by one, so the correspondences between them preserve the chain degree
(`TauCeti.bottDegreeShift_eq_zero_of_eq_add_one`), and by
`TauCeti.BottChainData.spectralSequence_first_page_d_homologyπ` the first differential is induced
by these correspondences `F_CD` with `λ_C - λ_D = 1`.

## Main definitions

* `TauCeti.BottChainData.indexSpectralSequence`: the spectral sequence of the index filtration.
* `TauCeti.BottChainData.indexSpectralSequenceFirstPageXIso`: its first page.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.4 (the filtrations of the Morse–Bott complex and their
  spectral sequences).
-/

public section

open CategoryTheory Limits Set

namespace TauCeti

namespace BottChainData

variable {R : Type*} [Ring R] {ι : Type*} {M : ι → Type*} [∀ C, AddCommGroup (M C)]
  [∀ C, Module R (M C)] [Fintype ι] (B : BottChainData R ι M)
  {S : ∀ C, ℤ → Submodule R (M C)}
  (hboundary : ∀ C j, ∀ x ∈ S C j, B.boundary C x ∈ S C (j - 1))
  (hpushforward : ∀ C D j, ∀ x ∈ S C j,
    B.pushforward C D x ∈ S D (j + bottDegreeShift B.rank C D))
  (hrank : ∀ C D, B.rank C ≤ B.rank D → B.pushforward C D = 0)

include hrank in
/-- If every nonzero pushforward strictly lowers the negative-normal rank, it strictly lowers the
rank as a real value. -/
theorem pushforward_eq_zero_of_natCast_rank_le (C D : ι) (h : (B.rank C : ℝ) ≤ B.rank D) :
    B.pushforward C D = 0 :=
  hrank C D (by exact_mod_cast h)

/-- **The index spectral sequence of the Bott complex.** If every nonzero pushforward strictly
lowers the negative-normal rank, the spectral sequence of the filtration of the Bott complex by
the components of rank at most `q`, in the cohomological indexing of
`CochainComplex.spectralSequence`: chains of total degree `n` sit in degree `-n`. -/
noncomputable abbrev indexSpectralSequence :=
  B.spectralSequence (fun C ↦ (B.rank C : ℝ)) (B.pushforward_eq_zero_of_natCast_rank_le hrank)
    hboundary hpushforward (a := fun q : ℤ ↦ (q : ℝ)) Int.cast_mono

/-- A natural number lies in the band `Ioc q (q + 1)` of the index filtration exactly when it
is `q + 1`. -/
private theorem natCast_mem_Ioc_intCast_iff (m : ℕ) (q : ℤ) :
    (m : ℝ) ∈ Ioc (q : ℝ) ((q + 1 : ℤ) : ℝ) ↔ (m : ℤ) = q + 1 := by
  rw [mem_Ioc, show (m : ℝ) = ((m : ℤ) : ℝ) by norm_cast, Int.cast_lt, Int.cast_le]
  lia

/-- **The first page of the index spectral sequence.** The object at `(p, q)` on the first page
(numbered `2`, as in `CochainComplex.spectralSequence`), with `p + q = -n`, is the direct sum
`⊕ H_(n - λ_C)(C)` over the components `C` of negative-normal rank `λ_C = q + 1` of the homology
of the chains on `C` (`TauCeti.BottChainData.componentChains`), lifted to the universe of the Bott
complex. -/
noncomputable def indexSpectralSequenceFirstPageXIso [DecidableEq ι] (pq : ℤ × ℤ) (n : ℤ)
    (hn : pq.1 + pq.2 = -n) :
    ((B.indexSpectralSequence hboundary hpushforward hrank).page 2).X pq ≅
      ⨁ fun C : {C // (B.rank C : ℤ) = pq.2 + 1} ↦ (ModuleCat.uliftFunctor R).obj
        ((B.componentChains hboundary C.val).homology (n - B.rank C.val)) :=
  B.spectralSequenceFirstPageXIsoBiproduct _ _ hboundary hpushforward Int.cast_mono pq n hn
      (fun C D hC hD ↦ by
        rw [natCast_mem_Ioc_intCast_iff] at hC hD
        exact_mod_cast hC.trans hD.symm) ≪≫
    biproduct.whiskerEquiv
      (g := fun C : {C // (B.rank C : ℤ) = pq.2 + 1} ↦ (ModuleCat.uliftFunctor R).obj
        ((B.componentChains hboundary C.val).homology (n - B.rank C.val)))
      (Equiv.subtypeEquivRight fun C ↦ natCast_mem_Ioc_intCast_iff (B.rank C) pq.2)
      fun _ ↦ Iso.refl _

/-- The identification of the first page of the index spectral sequence is that of the
critical-value spectral sequence for a single value per band
(`TauCeti.BottChainData.spectralSequenceFirstPageXIsoBiproduct`), followed by the reindexing of
the components of rank `q + 1` as those with value in `Ioc q (q + 1)`. -/
theorem indexSpectralSequenceFirstPageXIso_def [DecidableEq ι] (pq : ℤ × ℤ) (n : ℤ)
    (hn : pq.1 + pq.2 = -n) :
    B.indexSpectralSequenceFirstPageXIso hboundary hpushforward hrank pq n hn =
      B.spectralSequenceFirstPageXIsoBiproduct _ _ hboundary hpushforward Int.cast_mono pq n hn
          (fun C D hC hD ↦ by
            simp only [mem_Ioc] at hC hD
            norm_cast at hC hD ⊢
            lia) ≪≫
        biproduct.whiskerEquiv
          (g := fun C : {C // (B.rank C : ℤ) = pq.2 + 1} ↦ (ModuleCat.uliftFunctor R).obj
            ((B.componentChains hboundary C.val).homology (n - B.rank C.val)))
          (Equiv.subtypeEquivRight fun C ↦ by
            rw [mem_Ioc]
            norm_cast
            lia)
          fun _ ↦ Iso.refl _ :=
  (rfl)

end BottChainData

end TauCeti
