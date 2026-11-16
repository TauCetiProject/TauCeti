/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Basic
public import TauCeti.Analysis.Complex.Rectangle

/-!
# Certified lists of zeros in a rectangle

A numerical verification of the zeros of a meromorphic function in a rectangle `R` usually
produces a finite list of small rectangles `B₁, …, Bₖ` inside `R` together with multiplicities
`m₁, …, mₖ`, and checks by contour integration that `Bᵢ` contains exactly `mᵢ` zeros and `R`
exactly `m₁ + ⋯ + mₖ`. `TauCeti.HasZerosInRects f U z w Bs ms` is the statement that such a
certificate is correct for the closed rectangle `Complex.Rectangle z w`, with rectangles given by
pairs of opposite corners. Nothing here proves a numerical fact: the predicate is the meaning
of a certificate, and its consequences are what a numerical certificate buys.

Multiplicities are natural numbers, the function has no pole in `R`, and it has neither a zero
nor a pole on the frontier of `R` or of any `Bᵢ`. These conditions are what make the certificate
informative: with signed counts an omitted zero could cancel an omitted pole, and a zero on a
shared edge of two rectangles would be counted twice.

## Main results

* `TauCeti.HasZerosInRects.exists_mem_interior`: every zero of `f` in `R` lies in the interior
  of some rectangle of the certificate.
* `TauCeti.HasZerosInRects.divisorCount_eq_sum`: the signed count of `R`, which a contour
  integral computes, is the sum of the multiplicities.
* `TauCeti.HasZerosInRects.of_rectangle_subset`, `TauCeti.HasZerosInRects.of_forall₂_subset`:
  the outer rectangle may be shrunk, and each certified rectangle replaced by a smaller one with
  the same count.
* `TauCeti.not_hasZerosInRects_of_meromorphicOrderAt_ne_zero`: no certificate exists for a
  rectangle with a zero or a pole on its frontier.
-/

public section

open Set Complex

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {U : Set ℂ} {z w z' w' ρ : ℂ} {Bs Bs' : List (ℂ × ℂ)} {ms : List ℕ}

/-- The certified rectangles `Bs`, with multiplicities `ms`, account for all zeros of `f` in the
closed rectangle `Rectangle z w`. Each rectangle is given by a pair of opposite corners. The
conditions are: `f` is meromorphic on `U ⊇ Rectangle z w` without poles in the rectangle; each
`Bᵢ` lies in the rectangle and their interiors are pairwise disjoint; `f` has order `0` on the
frontier of the rectangle and of each `Bᵢ`; the zero count of `Bᵢ` is `mᵢ`; and the zero count of
the rectangle is the sum of the `mᵢ`. -/
structure HasZerosInRects (f : ℂ → E) (U : Set ℂ) (z w : ℂ) (Bs : List (ℂ × ℂ))
    (ms : List ℕ) : Prop where
  meromorphicOn : MeromorphicOn f U
  rectangle_subset : Rectangle z w ⊆ U
  divisor_nonneg : ∀ s ∈ Rectangle z w, 0 ≤ MeromorphicOn.divisor f U s
  subset_rectangle : ∀ B ∈ Bs, Rectangle B.1 B.2 ⊆ Rectangle z w
  pairwise_disjoint_interior :
    Bs.Pairwise fun B B' ↦ Disjoint (interior (Rectangle B.1 B.2)) (interior (Rectangle B'.1 B'.2))
  meromorphicOrderAt_frontier : ∀ s ∈ frontier (Rectangle z w), meromorphicOrderAt f s = 0
  meromorphicOrderAt_frontier_of_mem :
    ∀ B ∈ Bs, ∀ s ∈ frontier (Rectangle B.1 B.2), meromorphicOrderAt f s = 0
  map_zeroCount : Bs.map (fun B ↦ zeroCount f U (Rectangle B.1 B.2)) = ms
  zeroCount_eq_sum : zeroCount f U (Rectangle z w) = ms.sum

/-- A rectangle with a zero or a pole on its frontier admits no certificate. -/
theorem not_hasZerosInRects_of_meromorphicOrderAt_ne_zero (hρ : ρ ∈ frontier (Rectangle z w))
    (hord : meromorphicOrderAt f ρ ≠ 0) : ¬HasZerosInRects f U z w Bs ms :=
  fun h ↦ hord (h.meromorphicOrderAt_frontier ρ hρ)

namespace HasZerosInRects

variable (h : HasZerosInRects f U z w Bs ms)
include h

/-- The divisor of `f` has finite support in a subset of the certified rectangle. -/
private theorem finite_support {S : Set ℂ} (hS : S ⊆ Rectangle z w) :
    (S ∩ Function.support (fun s ↦ (MeromorphicOn.divisor f U s).toNat)).Finite :=
  zeroCount_support_finite <| MeromorphicOn.divisor_finite_inter_support_of_isCompact
    (isCompact_rectangle z w) h.rectangle_subset hS

/-- A certified rectangle has the same zero count as its interior. -/
private theorem zeroCount_interior_of_mem {B : ℂ × ℂ} (hB : B ∈ Bs) :
    zeroCount f U (interior (Rectangle B.1 B.2)) = zeroCount f U (Rectangle B.1 B.2) := by
  have hBR := h.subset_rectangle B hB
  refine zeroCount_interior fun s hs ↦ ?_
  have hsB : s ∈ Rectangle B.1 B.2 := (isClosed_rectangle _ _).frontier_subset hs
  rw [h.meromorphicOn.divisor_apply (h.rectangle_subset (hBR hsB)),
    h.meromorphicOrderAt_frontier_of_mem B hB s hs, WithTop.untop₀_zero]

/-- The interiors of the certified rectangles carry the full count of the rectangle. -/
private theorem sum_zeroCount_interior :
    (Bs.map fun B ↦ zeroCount f U (interior (Rectangle B.1 B.2))).sum = ms.sum := by
  rw [← h.map_zeroCount]
  congr 1
  exact List.map_congr_left fun B hB ↦ h.zeroCount_interior_of_mem hB

/-- **Coverage.** Every zero of `f` in the rectangle lies in the interior of a certified
rectangle. -/
theorem exists_mem_interior (hρ : ρ ∈ Rectangle z w)
    (hpos : 0 < MeromorphicOn.divisor f U ρ) :
    ∃ B ∈ Bs, ρ ∈ interior (Rectangle B.1 B.2) := by
  by_contra hcon
  push Not at hcon
  -- The interiors are disjoint subsets of the rectangle minus `ρ`, whose count is too small.
  have hsub : ∀ S ∈ Bs.map (fun B ↦ interior (Rectangle B.1 B.2)), S ⊆ Rectangle z w \ {ρ} := by
    simp only [List.mem_map]
    rintro S ⟨B, hB, rfl⟩ s hs
    exact ⟨h.subset_rectangle B hB (interior_subset hs), fun hsρ ↦ hcon B hB (hsρ ▸ hs)⟩
  have hle := sum_zeroCount_le (f := f) (U := U)
    (h.pairwise_disjoint_interior.map _ fun _ _ ↦ id) hsub (h.finite_support sdiff_subset)
  rw [List.map_map] at hle
  have hsplit := zeroCount_add_sdiff (f := f) (U := U) (singleton_subset_iff.2 hρ)
    (h.finite_support subset_rfl)
  rw [zeroCount_def (R := {ρ}), finsum_mem_singleton, h.zeroCount_eq_sum] at hsplit
  have := h.sum_zeroCount_interior
  simp only [Function.comp_def] at hle
  omega

/-- Without poles in the rectangle, the signed count of the rectangle, which a contour integral
computes, is the sum of the certified multiplicities. -/
theorem divisorCount_eq_sum : divisorCount f U (Rectangle z w) = ms.sum := by
  rw [divisorCount_eq_zeroCount h.divisor_nonneg, h.zeroCount_eq_sum]

/-- **Stability under shrinking the rectangle.** The certificate remains valid on a smaller
rectangle containing all certified rectangles, provided `f` has order `0` on its frontier. -/
theorem of_rectangle_subset (hsub : Rectangle z' w' ⊆ Rectangle z w)
    (hBs : ∀ B ∈ Bs, Rectangle B.1 B.2 ⊆ Rectangle z' w')
    (hfr : ∀ s ∈ frontier (Rectangle z' w'), meromorphicOrderAt f s = 0) :
    HasZerosInRects f U z' w' Bs ms where
  meromorphicOn := h.meromorphicOn
  rectangle_subset := hsub.trans h.rectangle_subset
  divisor_nonneg s hs := h.divisor_nonneg s (hsub hs)
  subset_rectangle := hBs
  pairwise_disjoint_interior := h.pairwise_disjoint_interior
  meromorphicOrderAt_frontier := hfr
  meromorphicOrderAt_frontier_of_mem := h.meromorphicOrderAt_frontier_of_mem
  map_zeroCount := h.map_zeroCount
  zeroCount_eq_sum := by
    rw [← h.zeroCount_eq_sum]
    refine (zeroCount_eq_iff_of_subset hsub (h.finite_support subset_rfl)).2 fun s hs ↦ ?_
    by_contra hne
    obtain ⟨B, hB, hsB⟩ := h.exists_mem_interior hs.1 (by omega)
    exact hs.2 (hBs B hB (interior_subset hsB))

/-- **Stability under shrinking the certified rectangles.** Each certified rectangle may be
replaced by a smaller one with the same zero count, provided `f` has order `0` on the frontiers
of the new rectangles. -/
theorem of_forall₂_subset
    (hBs : List.Forall₂ (fun B' B ↦ Rectangle B'.1 B'.2 ⊆ Rectangle B.1 B.2) Bs' Bs)
    (hfr : ∀ B ∈ Bs', ∀ s ∈ frontier (Rectangle B.1 B.2), meromorphicOrderAt f s = 0)
    (hcount : Bs'.map (fun B ↦ zeroCount f U (Rectangle B.1 B.2)) = ms) :
    HasZerosInRects f U z w Bs' ms where
  meromorphicOn := h.meromorphicOn
  rectangle_subset := h.rectangle_subset
  divisor_nonneg := h.divisor_nonneg
  subset_rectangle B' hB' := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB'
    have hlen := hBs.length_eq
    exact (hBs.get hi (hlen ▸ hi)).trans
      (h.subset_rectangle _ (List.getElem_mem (hlen ▸ hi)))
  pairwise_disjoint_interior := by
    have hlen := hBs.length_eq
    have hpw := List.pairwise_iff_getElem.1 h.pairwise_disjoint_interior
    refine List.pairwise_iff_getElem.2 fun i j hi hj hij ↦ ?_
    exact (hpw i j (hlen ▸ hi) (hlen ▸ hj) hij).mono
      (interior_mono (hBs.get hi (hlen ▸ hi))) (interior_mono (hBs.get hj (hlen ▸ hj)))
  meromorphicOrderAt_frontier := h.meromorphicOrderAt_frontier
  meromorphicOrderAt_frontier_of_mem := hfr
  map_zeroCount := hcount
  zeroCount_eq_sum := h.zeroCount_eq_sum

end HasZerosInRects

end TauCeti
