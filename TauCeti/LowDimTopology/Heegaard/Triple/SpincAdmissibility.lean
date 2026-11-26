/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.Triple.MaslovIndex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Admissibility of Heegaard triples for a fixed spin^c structure

A holomorphic triangle `ψ` in a pointed Heegaard triple diagram `(Σ, α, β, γ, z)` determines a
spin^c structure `s_z(ψ)` on the four-manifold `X_{αβγ}`, and the triangles in one spin^c
structure with the same corners and basepoint multiplicity differ by sums of doubly periodic
domains `P`. Their Maslov indices differ by the pairing `⟨c₁(s_z(ψ)), H(P)⟩`. Ozsváth and Szabó
call the triple *strongly admissible* for `s` when every nonzero sum of doubly periodic domains
`P` with `⟨c₁(s), H(P)⟩ = 2m ≥ 0` has a coefficient greater than `m`. This is the condition
under which the nonnegative triangle classes in `s` of each Maslov index are finitely many, so
that the triangle maps on the minus and plus flavors are finite sums. The weaker condition
needed with the basepoint multiplicity fixed only concerns the `P` with `⟨c₁(s), H(P)⟩ = 0`:
they must have coefficients of both signs.

This file develops both conditions for the incidence data `TauCeti.HeegaardTripleRegionSystem`,
with the region Euler characteristics `χ`, at the class of a triangle domain `E` with corners
`x`, `y`, `w`. The role of the Chern class pairing is played by Sarkar's Maslov index
(`TauCeti.HeegaardTripleRegionSystem.maslovIndex`): the change `μ(E + P) - μ(E)` of the Maslov
index when a domain `P` is added to `E` (`TauCeti.HeegaardTripleRegionSystem.periodicMaslovIndex`).
For a sum `P = P₁ + P₂ + P₃` of periodic domains of the diagrams `(α, β)`, `(β, γ)` and `(α, γ)`,
additivity of the Maslov index at the three corners gives

`μ(E + P) - μ(E) = (e(P₁) + 2 n_x(P₁)) + (e(P₂) + 2 n_y(P₂)) + (e(P₃) + 2 n_w(P₃))`,

the sum of the Maslov indices of the three periodic domains at the corners. So the change is
additive on the sums of doubly periodic domains, and it does not change when `E` is replaced by
another triangle domain in its class, or juxtaposed with a disk domain at one of its corners. On a
geometric triple it is `⟨c₁(s_z(ψ)), H(P)⟩` for a triangle `ψ` with domain `E`, by the
triangle analogue of Ozsváth–Szabó, Theorem 4.9; that identification, like the one of domains
with Whitney triangles, is geometric and is not formalized here.

Weak admissibility of the triple (`TauCeti.HeegaardTripleRegionSystem.WeaklyAdmissible`)
quantifies over all sums of doubly periodic domains, so it implies weak admissibility at every
triangle domain, and the two agree when no sum of doubly periodic domains changes the Maslov
index, as for a torsion spin^c structure. Strong admissibility at a triangle domain also implies
weak admissibility there.

## Main definitions

In the namespace `TauCeti.HeegaardTripleRegionSystem`:

* `periodicMaslovIndex`: the change `μ(E + P) - μ(E)` of the Maslov index of a triangle domain
  `E` when `P` is added to it.
* `WeaklyAdmissibleAt`: every nonzero sum of doubly periodic domains `P` with `μ(E + P) = μ(E)`
  has positive and negative coefficients.
* `StronglyAdmissible`: every nonzero sum of doubly periodic domains `P` with
  `μ(E + P) - μ(E) = 2m ≥ 0` has a coefficient greater than `m`.

## Main results

In the namespace `TauCeti.HeegaardTripleRegionSystem`:

* `IsTriangleDomain.periodicMaslovIndex_add_add_eq`: the formula above.
* `IsTriangleDomain.periodicMaslovIndex_add`: additivity on sums of doubly periodic domains, and
  `IsTriangleDomain.periodicMaslovIndex_add_zsmul_one`: adding `k` copies of the whole surface
  adds `2 k` on a closed surface of genus `n`.
* `IsTriangleDomain.periodicMaslovIndex_of_sub_mem` and
  `IsAlphaBetaDomainBetween.periodicMaslovIndex_add` with its two counterparts: the change
  depends only on the class of `E`, and is unchanged by juxtaposition with disk domains at the
  corners. So are both admissibility conditions, for instance
  `IsTriangleDomain.weaklyAdmissibleAt_iff_of_sub_mem` and
  `IsAlphaBetaDomainBetween.stronglyAdmissible_add_iff`. By
  `IsTriangleDomain.periodicMaslovIndex_eq_of_isTriangleDomain` it is even the same at all
  triangle domains with the same corners.
* `WeaklyAdmissible.weaklyAdmissibleAt`, `StronglyAdmissible.weaklyAdmissibleAt` and
  `weaklyAdmissibleAt_iff_weaklyAdmissible`: the comparisons between the conditions.
* `IsTriangleDomain.weaklyAdmissibleAt_iff_exists_pos_forall_sum_mul_eq_zero` and
  `IsTriangleDomain.sum_mul_eq_of_maslovIndex_eq`: weak admissibility at `E` is the existence of
  a strictly positive area form for which the domains in the class of `E` with the same Maslov
  index have the same area.
* `WeaklyAdmissibleAt.finite_setOf_nonneg_sub_mem_maslovIndex_eq`: weak admissibility at `E`
  makes the nonnegative domains in the class of `E` with a given Maslov index finitely many.
* `StronglyAdmissible.finite_setOf_nonneg_sub_mem_maslovIndex_eq`: strong admissibility at `E`
  makes the nonnegative domains with a given Maslov index which differ from `E` by a sum of
  doubly periodic domains and copies of the whole surface finitely many, whatever their
  basepoint multiplicity.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §8: Definition 8.8 (admissibility of
  triples) and Lemmas 8.9–8.11 (finiteness of the nonnegative triangle classes); Definition 4.10
  and Remark 4.11 (admissibility of diagrams for a spin^c structure) and Theorem 4.9 (the Maslov
  index of a periodic class).
* S. Sarkar, *Maslov index formulas for Whitney n-gons*, J. Symplectic Geom. **9** (2011),
  [arXiv:math/0609673](https://arxiv.org/abs/math/0609673), Theorem 3.3 (additivity of the
  Maslov index of triangle domains).
-/

public section

open Finset

namespace TauCeti

namespace HeegaardTripleRegionSystem

variable {n : ℕ} {PointAB PointBC PointAC Region Basepoint : Type*}
  {T : HeegaardTripleRegionSystem n PointAB PointBC PointAC Region Basepoint}
  [Fintype PointAB] [Fintype PointBC] [Fintype PointAC] [Fintype Region]

section PeriodicMaslovIndex

variable (T) in
/-- The change `μ(E + P) - μ(E)` of Sarkar's Maslov index with corners `x` and `w` when the domain
`P` is added to the domain `E`. For a triangle domain `E` and a sum `P` of doubly periodic domains
this is additive in `P` (`IsTriangleDomain.periodicMaslovIndex_add`) and depends only on the
class of `E`; it is the combinatorial counterpart of the pairing of the first Chern class of the
spin^c structure of a triangle with domain `E` with the class of `P`. -/
def periodicMaslovIndex (χ : Region → ℤ) (x : T.alphaBeta.Generator)
    (w : T.alphaGamma.Generator) (E P : Region → ℤ) : ℚ :=
  T.maslovIndex χ x w (E + P) - T.maslovIndex χ x w E

variable {χ : Region → ℤ} {x x' : T.alphaBeta.Generator} {y y' : T.betaGamma.Generator}
  {w w' : T.alphaGamma.Generator} {D E E' P Q : Region → ℤ}

theorem periodicMaslovIndex_def :
    T.periodicMaslovIndex χ x w E P = T.maslovIndex χ x w (E + P) - T.maslovIndex χ x w E :=
  (rfl)

@[simp]
theorem periodicMaslovIndex_zero : T.periodicMaslovIndex χ x w E 0 = 0 := by
  simp [periodicMaslovIndex_def]

omit [Fintype PointAB] [Fintype PointBC] [Fintype PointAC] [Fintype Region] in
/-- Adding a sum of doubly periodic domains to a triangle domain gives a triangle domain with the
same corners. -/
private theorem IsTriangleDomain.add_of_mem (hE : T.IsTriangleDomain x y w E)
    (hP : P ∈ T.doublyPeriodicDomains) : T.IsTriangleDomain x y w (E + P) :=
  (hE.of_sub_mem_doublyPeriodicDomains (by rwa [add_sub_cancel_left])).1

/-- **The Maslov index of a sum of doubly periodic domains.** Adding to a triangle domain `E` with
corners `x`, `y`, `w` periodic domains `P₁`, `P₂`, `P₃` of the diagrams `(α, β)`, `(β, γ)` and
`(α, γ)` adds the Maslov indices `e(P₁) + 2 n_x(P₁)`, `e(P₂) + 2 n_y(P₂)` and `e(P₃) + 2 n_w(P₃)`
of the three periodic domains at the corners. -/
theorem IsTriangleDomain.periodicMaslovIndex_add_add_eq (χ : Region → ℤ)
    (hE : T.IsTriangleDomain x y w E) {P₁ P₂ P₃ : Region → ℤ}
    (h₁ : P₁ ∈ T.alphaBetaPeriodicDomains) (h₂ : P₂ ∈ T.betaGammaPeriodicDomains)
    (h₃ : P₃ ∈ T.alphaGammaPeriodicDomains) :
    T.periodicMaslovIndex χ x w E (P₁ + P₂ + P₃) =
      (T.eulerMeasure χ P₁ + 2 * T.alphaBetaGeneratorPointMeasure x P₁) +
        (T.eulerMeasure χ P₂ + 2 * T.betaGammaGeneratorPointMeasure y P₂) +
        (T.eulerMeasure χ P₃ + 2 * T.alphaGammaGeneratorPointMeasure w P₃) := by
  have hD₁ := ((isAlphaBetaDomainBetween_self_iff (x := x)).mpr h₁).1
  have hD₂ := ((isBetaGammaDomainBetween_self_iff (y := y)).mpr h₂).1
  have hD₃ := ((isAlphaGammaDomainBetween_self_iff (w := w)).mpr h₃).1
  have hE₃ := hE.add_isAlphaGammaDomainBetween hD₃
  rw [periodicMaslovIndex_def, show E + (P₁ + P₂ + P₃) = P₁ + (P₂ + (E + P₃)) by abel,
    hD₁.maslovIndex_add χ (hD₂.add_isTriangleDomain hE₃), hD₂.maslovIndex_add χ hE₃,
    hE.maslovIndex_add χ hD₃]
  ring

/-- The change of the Maslov index of a triangle domain is additive on sums of doubly periodic
domains. -/
theorem IsTriangleDomain.periodicMaslovIndex_add (χ : Region → ℤ)
    (hE : T.IsTriangleDomain x y w E) (hP : P ∈ T.doublyPeriodicDomains)
    (hQ : Q ∈ T.doublyPeriodicDomains) :
    T.periodicMaslovIndex χ x w E (P + Q) =
      T.periodicMaslovIndex χ x w E P + T.periodicMaslovIndex χ x w E Q := by
  obtain ⟨P₁, h₁, P₂, h₂, P₃, h₃, rfl⟩ := mem_doublyPeriodicDomains_iff.mp hP
  obtain ⟨Q₁, k₁, Q₂, k₂, Q₃, k₃, rfl⟩ := mem_doublyPeriodicDomains_iff.mp hQ
  rw [show P₁ + P₂ + P₃ + (Q₁ + Q₂ + Q₃) = (P₁ + Q₁) + (P₂ + Q₂) + (P₃ + Q₃) by abel,
    hE.periodicMaslovIndex_add_add_eq χ (add_mem h₁ k₁) (add_mem h₂ k₂) (add_mem h₃ k₃),
    hE.periodicMaslovIndex_add_add_eq χ h₁ h₂ h₃, hE.periodicMaslovIndex_add_add_eq χ k₁ k₂ k₃]
  simp only [map_add]
  ring

theorem IsTriangleDomain.periodicMaslovIndex_neg (χ : Region → ℤ)
    (hE : T.IsTriangleDomain x y w E) (hP : P ∈ T.doublyPeriodicDomains) :
    T.periodicMaslovIndex χ x w E (-P) = -T.periodicMaslovIndex χ x w E P := by
  have h := hE.periodicMaslovIndex_add χ hP (neg_mem hP)
  rw [add_neg_cancel, periodicMaslovIndex_zero] at h
  linarith

theorem IsTriangleDomain.periodicMaslovIndex_sub (χ : Region → ℤ)
    (hE : T.IsTriangleDomain x y w E) (hP : P ∈ T.doublyPeriodicDomains)
    (hQ : Q ∈ T.doublyPeriodicDomains) :
    T.periodicMaslovIndex χ x w E (P - Q) =
      T.periodicMaslovIndex χ x w E P - T.periodicMaslovIndex χ x w E Q := by
  rw [sub_eq_add_neg, hE.periodicMaslovIndex_add χ hP (neg_mem hQ),
    hE.periodicMaslovIndex_neg χ hQ, sub_eq_add_neg]

/-- Adding `k` copies of the whole surface to a domain adds `2 k` to the change of the Maslov
index of a triangle domain, on a closed surface of genus `n`. -/
theorem IsTriangleDomain.periodicMaslovIndex_add_zsmul_one
    (hχ : ∑ r, χ r - Fintype.card PointAB - Fintype.card PointBC - Fintype.card PointAC =
      2 - 2 * (n : ℤ))
    (hE : T.IsTriangleDomain x y w E) (hP : P ∈ T.doublyPeriodicDomains) (k : ℤ) :
    T.periodicMaslovIndex χ x w E (P + k • 1) = T.periodicMaslovIndex χ x w E P + 2 * k := by
  rw [periodicMaslovIndex_def, periodicMaslovIndex_def,
    show E + (P + k • 1) = k • 1 + (E + P) by abel,
    (hE.add_of_mem hP).maslovIndex_zsmul_one_add hχ k]
  ring

/-- The change of the Maslov index by a sum of doubly periodic domains `P` is the same at any two
triangle domains with the same corners `x`, `y`, `w`, whether or not they lie in one class: by
`IsTriangleDomain.periodicMaslovIndex_add_add_eq` it only depends on the corners. -/
theorem IsTriangleDomain.periodicMaslovIndex_eq_of_isTriangleDomain (χ : Region → ℤ)
    (hE : T.IsTriangleDomain x y w E) (hE' : T.IsTriangleDomain x y w E')
    (hP : P ∈ T.doublyPeriodicDomains) :
    T.periodicMaslovIndex χ x w E' P = T.periodicMaslovIndex χ x w E P := by
  obtain ⟨P₁, h₁, P₂, h₂, P₃, h₃, rfl⟩ := mem_doublyPeriodicDomains_iff.mp hP
  rw [hE.periodicMaslovIndex_add_add_eq χ h₁ h₂ h₃, hE'.periodicMaslovIndex_add_add_eq χ h₁ h₂ h₃]

/-- The change of the Maslov index by a sum of doubly periodic domains `P` is the same at two
triangle domains in one class, that is, when `E' - E` is a sum of doubly periodic domains. -/
theorem IsTriangleDomain.periodicMaslovIndex_of_sub_mem (χ : Region → ℤ)
    (hE : T.IsTriangleDomain x y w E) (h : E' - E ∈ T.doublyPeriodicDomains)
    (hP : P ∈ T.doublyPeriodicDomains) :
    T.periodicMaslovIndex χ x w E' P = T.periodicMaslovIndex χ x w E P :=
  hE.periodicMaslovIndex_eq_of_isTriangleDomain χ (hE.of_sub_mem_doublyPeriodicDomains h).1 hP

/-- Juxtaposing a disk domain from `x'` to `x` in `(Σ, α, β)` with a triangle domain `E` leaves the
change `μ(E + P) - μ(E)` unchanged for every sum `P` of doubly periodic domains. -/
theorem IsAlphaBetaDomainBetween.periodicMaslovIndex_add (χ : Region → ℤ)
    (hD : T.IsAlphaBetaDomainBetween x' x D) (hE : T.IsTriangleDomain x y w E)
    (hP : P ∈ T.doublyPeriodicDomains) :
    T.periodicMaslovIndex χ x' w (D + E) P = T.periodicMaslovIndex χ x w E P := by
  rw [periodicMaslovIndex_def, periodicMaslovIndex_def, add_assoc,
    hD.maslovIndex_add χ (hE.add_of_mem hP), hD.maslovIndex_add χ hE]
  ring

/-- Juxtaposing a disk domain from `y'` to `y` in `(Σ, β, γ)` with a triangle domain `E` leaves the
change `μ(E + P) - μ(E)` unchanged for every sum `P` of doubly periodic domains. -/
theorem IsBetaGammaDomainBetween.periodicMaslovIndex_add (χ : Region → ℤ)
    (hD : T.IsBetaGammaDomainBetween y' y D) (hE : T.IsTriangleDomain x y w E)
    (hP : P ∈ T.doublyPeriodicDomains) :
    T.periodicMaslovIndex χ x w (D + E) P = T.periodicMaslovIndex χ x w E P := by
  rw [periodicMaslovIndex_def, periodicMaslovIndex_def, add_assoc,
    hD.maslovIndex_add χ (hE.add_of_mem hP), hD.maslovIndex_add χ hE]
  ring

/-- Juxtaposing a triangle domain `E` with a disk domain from `w` to `w'` in `(Σ, α, γ)` leaves the
change `μ(E + P) - μ(E)` unchanged for every sum `P` of doubly periodic domains. -/
theorem IsAlphaGammaDomainBetween.periodicMaslovIndex_add (χ : Region → ℤ)
    (hD : T.IsAlphaGammaDomainBetween w w' D) (hE : T.IsTriangleDomain x y w E)
    (hP : P ∈ T.doublyPeriodicDomains) :
    T.periodicMaslovIndex χ x w' (E + D) P = T.periodicMaslovIndex χ x w E P := by
  rw [periodicMaslovIndex_def, periodicMaslovIndex_def, show E + D + P = E + P + D by abel,
    (hE.add_of_mem hP).maslovIndex_add χ hD, hE.maslovIndex_add χ hD]
  ring

end PeriodicMaslovIndex

section Admissible

variable (T) in
/-- Weak admissibility at the class of a triangle domain `E` with corners `x`, `w`, for the region
Euler characteristics `χ`: every nonzero sum of doubly periodic domains which does not change the
Maslov index of `E` has positive and negative coefficients. On a geometric triple this is the
condition of Ozsváth–Szabó's Definition 8.8 restricted, as their Definition 4.10 does for
diagrams, to the doubly periodic sums whose Chern class pairing with the spin^c structure of a
triangle with domain `E` vanishes. -/
def WeaklyAdmissibleAt (χ : Region → ℤ) (x : T.alphaBeta.Generator) (w : T.alphaGamma.Generator)
    (E : Region → ℤ) : Prop :=
  ∀ P ∈ T.doublyPeriodicDomains, T.periodicMaslovIndex χ x w E P = 0 → P ≠ 0 →
    (∃ r, 0 < P r) ∧ ∃ r, P r < 0

variable (T) in
/-- Strong admissibility at the class of a triangle domain `E` with corners `x`, `w`, for the
region Euler characteristics `χ`: every nonzero sum of doubly periodic domains `P` which raises
the Maslov index of `E` by `2m ≥ 0` has a coefficient greater than `m`. On a geometric triple
this is strong admissibility for the spin^c structure of a triangle with domain `E`
(Ozsváth–Szabó, Definition 8.8). The rational half-index is used because the region Euler
characteristics are an arbitrary argument. -/
def StronglyAdmissible (χ : Region → ℤ) (x : T.alphaBeta.Generator) (w : T.alphaGamma.Generator)
    (E : Region → ℤ) : Prop :=
  ∀ P ∈ T.doublyPeriodicDomains, P ≠ 0 → 0 ≤ T.periodicMaslovIndex χ x w E P →
    ∃ r, T.periodicMaslovIndex χ x w E P / 2 < (P r : ℚ)

variable {χ : Region → ℤ} {x x' : T.alphaBeta.Generator} {y y' : T.betaGamma.Generator}
  {w w' : T.alphaGamma.Generator} {D E E' : Region → ℤ}

theorem weaklyAdmissibleAt_def :
    T.WeaklyAdmissibleAt χ x w E ↔ ∀ P ∈ T.doublyPeriodicDomains,
      T.periodicMaslovIndex χ x w E P = 0 → P ≠ 0 → (∃ r, 0 < P r) ∧ ∃ r, P r < 0 :=
  Iff.rfl

theorem stronglyAdmissible_iff :
    T.StronglyAdmissible χ x w E ↔ ∀ P ∈ T.doublyPeriodicDomains, P ≠ 0 →
      0 ≤ T.periodicMaslovIndex χ x w E P →
        ∃ r, T.periodicMaslovIndex χ x w E P / 2 < (P r : ℚ) :=
  Iff.rfl

/-- The two conditions only depend on the changes of the Maslov index by sums of doubly periodic
domains. -/
private theorem weaklyAdmissibleAt_iff_of_forall {x' w' E'}
    (h : ∀ P ∈ T.doublyPeriodicDomains,
      T.periodicMaslovIndex χ x' w' E' P = T.periodicMaslovIndex χ x w E P) :
    T.WeaklyAdmissibleAt χ x' w' E' ↔ T.WeaklyAdmissibleAt χ x w E :=
  forall₂_congr fun P hP => by rw [h P hP]

private theorem stronglyAdmissible_iff_of_forall {x' w' E'}
    (h : ∀ P ∈ T.doublyPeriodicDomains,
      T.periodicMaslovIndex χ x' w' E' P = T.periodicMaslovIndex χ x w E P) :
    T.StronglyAdmissible χ x' w' E' ↔ T.StronglyAdmissible χ x w E :=
  forall₂_congr fun P hP => by rw [h P hP]

/-- Weak admissibility at a triangle domain only depends on its class. -/
theorem IsTriangleDomain.weaklyAdmissibleAt_iff_of_sub_mem (hE : T.IsTriangleDomain x y w E)
    (h : E' - E ∈ T.doublyPeriodicDomains) :
    T.WeaklyAdmissibleAt χ x w E' ↔ T.WeaklyAdmissibleAt χ x w E :=
  weaklyAdmissibleAt_iff_of_forall fun _ hP => hE.periodicMaslovIndex_of_sub_mem χ h hP

/-- Strong admissibility at a triangle domain only depends on its class. -/
theorem IsTriangleDomain.stronglyAdmissible_iff_of_sub_mem (hE : T.IsTriangleDomain x y w E)
    (h : E' - E ∈ T.doublyPeriodicDomains) :
    T.StronglyAdmissible χ x w E' ↔ T.StronglyAdmissible χ x w E :=
  stronglyAdmissible_iff_of_forall fun _ hP => hE.periodicMaslovIndex_of_sub_mem χ h hP

/-- Weak admissibility at a triangle domain is unchanged by juxtaposition with a disk domain of
`(Σ, α, β)` at its corner `x`. -/
theorem IsAlphaBetaDomainBetween.weaklyAdmissibleAt_add_iff
    (hD : T.IsAlphaBetaDomainBetween x' x D) (hE : T.IsTriangleDomain x y w E) :
    T.WeaklyAdmissibleAt χ x' w (D + E) ↔ T.WeaklyAdmissibleAt χ x w E :=
  weaklyAdmissibleAt_iff_of_forall fun _ hP => hD.periodicMaslovIndex_add χ hE hP

/-- Strong admissibility at a triangle domain is unchanged by juxtaposition with a disk domain of
`(Σ, α, β)` at its corner `x`. -/
theorem IsAlphaBetaDomainBetween.stronglyAdmissible_add_iff
    (hD : T.IsAlphaBetaDomainBetween x' x D) (hE : T.IsTriangleDomain x y w E) :
    T.StronglyAdmissible χ x' w (D + E) ↔ T.StronglyAdmissible χ x w E :=
  stronglyAdmissible_iff_of_forall fun _ hP => hD.periodicMaslovIndex_add χ hE hP

/-- Weak admissibility at a triangle domain is unchanged by juxtaposition with a disk domain of
`(Σ, β, γ)` at its corner `y`. -/
theorem IsBetaGammaDomainBetween.weaklyAdmissibleAt_add_iff
    (hD : T.IsBetaGammaDomainBetween y' y D) (hE : T.IsTriangleDomain x y w E) :
    T.WeaklyAdmissibleAt χ x w (D + E) ↔ T.WeaklyAdmissibleAt χ x w E :=
  weaklyAdmissibleAt_iff_of_forall fun _ hP => hD.periodicMaslovIndex_add χ hE hP

/-- Strong admissibility at a triangle domain is unchanged by juxtaposition with a disk domain of
`(Σ, β, γ)` at its corner `y`. -/
theorem IsBetaGammaDomainBetween.stronglyAdmissible_add_iff
    (hD : T.IsBetaGammaDomainBetween y' y D) (hE : T.IsTriangleDomain x y w E) :
    T.StronglyAdmissible χ x w (D + E) ↔ T.StronglyAdmissible χ x w E :=
  stronglyAdmissible_iff_of_forall fun _ hP => hD.periodicMaslovIndex_add χ hE hP

/-- Weak admissibility at a triangle domain is unchanged by juxtaposition with a disk domain of
`(Σ, α, γ)` at its corner `w`. -/
theorem IsAlphaGammaDomainBetween.weaklyAdmissibleAt_add_iff
    (hD : T.IsAlphaGammaDomainBetween w w' D) (hE : T.IsTriangleDomain x y w E) :
    T.WeaklyAdmissibleAt χ x w' (E + D) ↔ T.WeaklyAdmissibleAt χ x w E :=
  weaklyAdmissibleAt_iff_of_forall fun _ hP => hD.periodicMaslovIndex_add χ hE hP

/-- Strong admissibility at a triangle domain is unchanged by juxtaposition with a disk domain of
`(Σ, α, γ)` at its corner `w`. -/
theorem IsAlphaGammaDomainBetween.stronglyAdmissible_add_iff
    (hD : T.IsAlphaGammaDomainBetween w w' D) (hE : T.IsTriangleDomain x y w E) :
    T.StronglyAdmissible χ x w' (E + D) ↔ T.StronglyAdmissible χ x w E :=
  stronglyAdmissible_iff_of_forall fun _ hP => hD.periodicMaslovIndex_add χ hE hP

/-- A weakly admissible triple is weakly admissible at every triangle domain. -/
theorem WeaklyAdmissible.weaklyAdmissibleAt (hT : T.WeaklyAdmissible) (χ : Region → ℤ)
    (x : T.alphaBeta.Generator) (w : T.alphaGamma.Generator) (E : Region → ℤ) :
    T.WeaklyAdmissibleAt χ x w E := fun P hP _ =>
  (AddSubgroup.forall_exists_pos_and_neg_iff_forall_nonneg_eq_zero _).mpr
    (weaklyAdmissible_iff.mp hT) P hP

/-- If no sum of doubly periodic domains changes the Maslov index of `E`, as for a torsion spin^c
structure, then weak admissibility at `E` is weak admissibility. -/
theorem weaklyAdmissibleAt_iff_weaklyAdmissible
    (h : ∀ P ∈ T.doublyPeriodicDomains, T.periodicMaslovIndex χ x w E P = 0) :
    T.WeaklyAdmissibleAt χ x w E ↔ T.WeaklyAdmissible :=
  ⟨fun hT => weaklyAdmissible_iff.mpr <|
    (AddSubgroup.forall_exists_pos_and_neg_iff_forall_nonneg_eq_zero _).mp
      fun P hP => hT P hP (h P hP), fun hT => hT.weaklyAdmissibleAt χ x w E⟩

/-- Strong admissibility at a triangle domain implies weak admissibility there: a sum of doubly
periodic domains `P` not changing the Maslov index has a positive coefficient, and so has `-P`. -/
theorem StronglyAdmissible.weaklyAdmissibleAt (hT : T.StronglyAdmissible χ x w E)
    (hE : T.IsTriangleDomain x y w E) : T.WeaklyAdmissibleAt χ x w E := by
  intro P hP hμ hne
  have hμ' : T.periodicMaslovIndex χ x w E (-P) = 0 := by
    rw [hE.periodicMaslovIndex_neg χ hP, hμ, neg_zero]
  obtain ⟨r, hr⟩ := hT P hP hne hμ.ge
  obtain ⟨s, hs⟩ := hT (-P) (neg_mem hP) (neg_ne_zero.mpr hne) hμ'.ge
  rw [hμ, zero_div] at hr
  rw [hμ', zero_div] at hs
  refine ⟨⟨r, by exact_mod_cast hr⟩, ⟨s, ?_⟩⟩
  have hs' : (0 : ℤ) < -P s := by exact_mod_cast hs
  exact neg_pos.mp hs'

section Weak

variable (hE : T.IsTriangleDomain x y w E)
include hE

variable (χ) in
/-- The sums of doubly periodic domains which do not change the Maslov index of `E`. -/
private def indexZero : AddSubgroup (Region → ℤ) where
  carrier := {P | P ∈ T.doublyPeriodicDomains ∧ T.periodicMaslovIndex χ x w E P = 0}
  add_mem' {P Q} hP hQ :=
    ⟨add_mem hP.1 hQ.1, by rw [hE.periodicMaslovIndex_add χ hP.1 hQ.1, hP.2, hQ.2, add_zero]⟩
  zero_mem' := ⟨zero_mem _, periodicMaslovIndex_zero⟩
  neg_mem' {P} hP := ⟨neg_mem hP.1, by rw [hE.periodicMaslovIndex_neg χ hP.1, hP.2, neg_zero]⟩

private theorem mem_indexZero {P : Region → ℤ} :
    P ∈ indexZero χ hE ↔
      P ∈ T.doublyPeriodicDomains ∧ T.periodicMaslovIndex χ x w E P = 0 :=
  Iff.rfl

/-- Two domains in the class of `E` with the same Maslov index differ by a sum of doubly periodic
domains not changing the Maslov index of `E`. -/
private theorem sub_mem_indexZero {D D' : Region → ℤ} (hD : D - E ∈ T.doublyPeriodicDomains)
    (hD' : D' - E ∈ T.doublyPeriodicDomains)
    (hμ : T.maslovIndex χ x w D' = T.maslovIndex χ x w D) : D' - D ∈ indexZero χ hE := by
  refine ⟨by simpa using sub_mem hD' hD, ?_⟩
  rw [show D' - D = (D' - E) - (D - E) by abel, hE.periodicMaslovIndex_sub χ hD' hD,
    periodicMaslovIndex_def, periodicMaslovIndex_def, add_sub_cancel, add_sub_cancel, hμ,
    sub_self]

/-- Weak admissibility at a triangle domain `E` means that the only nonnegative sum of doubly
periodic domains not changing the Maslov index of `E` is zero. -/
theorem IsTriangleDomain.weaklyAdmissibleAt_iff :
    T.WeaklyAdmissibleAt χ x w E ↔ ∀ P ∈ T.doublyPeriodicDomains,
      T.periodicMaslovIndex χ x w E P = 0 → 0 ≤ P → P = 0 := by
  have := AddSubgroup.forall_exists_pos_and_neg_iff_forall_nonneg_eq_zero (indexZero χ hE)
  simp only [mem_indexZero, and_imp] at this
  exact this

/-- Weak admissibility at a triangle domain `E` is the existence of strictly positive region areas
`A` for which every sum of doubly periodic domains not changing the Maslov index of `E` has signed
area zero. -/
theorem IsTriangleDomain.weaklyAdmissibleAt_iff_exists_pos_forall_sum_mul_eq_zero :
    T.WeaklyAdmissibleAt χ x w E ↔ ∃ A : Region → ℝ, (∀ r, 0 < A r) ∧
      ∀ P ∈ T.doublyPeriodicDomains, T.periodicMaslovIndex χ x w E P = 0 →
        ∑ r, A r * P r = 0 := by
  have := (indexZero χ hE).exists_pos_sum_mul_intCast_eq_zero_iff (K := ℝ)
  simp only [mem_indexZero, and_imp] at this
  rw [hE.weaklyAdmissibleAt_iff, this]

/-- If an area form `A` vanishes on the sums of doubly periodic domains not changing the Maslov
index of the triangle domain `E`, then all domains in the class of `E` with the same Maslov index
have the same area: the energy bound for holomorphic triangles in a fixed spin^c structure, once
their energy is identified with the area of their domain. -/
theorem IsTriangleDomain.sum_mul_eq_of_maslovIndex_eq {A : Region → ℝ}
    (hA : ∀ P ∈ T.doublyPeriodicDomains, T.periodicMaslovIndex χ x w E P = 0 →
      ∑ r, A r * P r = 0)
    {D D' : Region → ℤ} (hD : D - E ∈ T.doublyPeriodicDomains)
    (hD' : D' - E ∈ T.doublyPeriodicDomains)
    (hμ : T.maslovIndex χ x w D' = T.maslovIndex χ x w D) :
    ∑ r, A r * D' r = ∑ r, A r * D r :=
  sum_mul_intCast_eq_of_sub_mem (P := indexZero χ hE) (fun P hP => hA P hP.1 hP.2)
    (sub_mem_indexZero hE hD hD' hμ)

omit hE in
/-- **Finiteness for weak admissibility.** If the triple is weakly admissible at the triangle
domain `E`, then only finitely many nonnegative domains with a given Maslov index differ from `E`
by a sum of doubly periodic domains. These are triangle domains with the corners and basepoint
multiplicities of `E` (`IsTriangleDomain.of_sub_mem_doublyPeriodicDomains`). -/
theorem WeaklyAdmissibleAt.finite_setOf_nonneg_sub_mem_maslovIndex_eq
    (hT : T.WeaklyAdmissibleAt χ x w E) (hE : T.IsTriangleDomain x y w E) (m : ℚ) :
    {D : Region → ℤ | 0 ≤ D ∧ D - E ∈ T.doublyPeriodicDomains ∧
      T.maslovIndex χ x w D = m}.Finite :=
  AddSubgroup.finite_of_forall_sub_mem (P := indexZero χ hE)
    (fun P hP => hE.weaklyAdmissibleAt_iff.mp hT P hP.1 hP.2) (fun _ hD => hD.1)
    fun _ ⟨_, hD, hDm⟩ _ ⟨_, hD', hD'm⟩ => sub_mem_indexZero hE hD hD' (hD'm.trans hDm.symm)

end Weak

section Strong

variable (hχ : ∑ r, χ r - Fintype.card PointAB - Fintype.card PointBC - Fintype.card PointAC =
  2 - 2 * (n : ℤ)) (hE : T.IsTriangleDomain x y w E)
include hE

/-- The sums of doubly periodic domains and copies of the whole surface which do not change the
Maslov index of `E`, recorded by a decomposition `F = P + k Σ` with `μ(E + P) - μ(E) + 2 k = 0`;
on a closed surface of genus `n` this is `μ(E + F) = μ(E)`. -/
private def classIndexZero (χ : Region → ℤ) : AddSubgroup (Region → ℤ) where
  carrier := {F | ∃ P ∈ T.doublyPeriodicDomains, ∃ k : ℤ,
    F = P + k • 1 ∧ T.periodicMaslovIndex χ x w E P + 2 * k = 0}
  add_mem' := by
    rintro _ _ ⟨P, hP, k, rfl, hk⟩ ⟨Q, hQ, l, rfl, hl⟩
    refine ⟨P + Q, add_mem hP hQ, k + l, by rw [add_zsmul]; abel, ?_⟩
    rw [hE.periodicMaslovIndex_add χ hP hQ]
    push_cast
    linarith
  zero_mem' := ⟨0, zero_mem _, 0, by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨P, hP, k, rfl, hk⟩
    refine ⟨-P, neg_mem hP, -k, by rw [neg_zsmul]; abel, ?_⟩
    rw [hE.periodicMaslovIndex_neg χ hP]
    push_cast
    linarith

include hχ in
/-- Two domains differing from `E` by sums of doubly periodic domains and copies of the whole
surface, with the same Maslov index, differ by an element of `classIndexZero`. -/
private theorem sub_mem_classIndexZero {D D' : Region → ℤ}
    (hD : D - E ∈ T.doublyPeriodicDomains ⊔ AddSubgroup.zmultiples 1)
    (hD' : D' - E ∈ T.doublyPeriodicDomains ⊔ AddSubgroup.zmultiples 1)
    (hμ : T.maslovIndex χ x w D' = T.maslovIndex χ x w D) :
    D' - D ∈ classIndexZero hE χ := by
  obtain ⟨P, hP, _, ⟨k, rfl⟩, hPk⟩ := AddSubgroup.mem_sup.mp hD
  obtain ⟨Q, hQ, _, ⟨l, rfl⟩, hQl⟩ := AddSubgroup.mem_sup.mp hD'
  -- The two indices are `μ(E) + μ(E + P) - μ(E) + 2 k` and the same with `Q` and `l`.
  have hDμ := hE.periodicMaslovIndex_add_zsmul_one hχ hP k
  have hD'μ := hE.periodicMaslovIndex_add_zsmul_one hχ hQ l
  rw [hPk, periodicMaslovIndex_def, add_sub_cancel] at hDμ
  rw [hQl, periodicMaslovIndex_def, add_sub_cancel] at hD'μ
  refine ⟨Q - P, sub_mem hQ hP, l - k, ?_, ?_⟩
  · rw [show D' - D = (D' - E) - (D - E) by abel, ← hPk, ← hQl, sub_zsmul]
    abel
  · rw [hE.periodicMaslovIndex_sub χ hQ hP]
    push_cast
    linarith

include hχ in
/-- Strong admissibility at `E` forces a basepoint when some region exists: otherwise the whole
surface is a periodic domain raising the Maslov index of `E` by two with all coefficients one. -/
private theorem StronglyAdmissible.nonempty_basepoint (hT : T.StronglyAdmissible χ x w E)
    [Nonempty Region] : Nonempty Basepoint := by
  by_contra hB
  rw [not_nonempty_iff] at hB
  have h₁ : (1 : Region → ℤ) ∈ T.doublyPeriodicDomains :=
    alphaBetaPeriodicDomains_le_doublyPeriodicDomains (by simp)
  have hμ := hE.periodicMaslovIndex_add_zsmul_one hχ (zero_mem _) 1
  rw [zero_add, one_zsmul, periodicMaslovIndex_zero] at hμ
  obtain ⟨r, hr⟩ := hT 1 h₁ one_ne_zero (by rw [hμ]; norm_num)
  rw [hμ] at hr
  norm_num at hr

include hχ in
/-- Under strong admissibility at `E`, on a closed surface of genus `n`, the only nonnegative
element of `classIndexZero` is zero. -/
private theorem StronglyAdmissible.eq_zero_of_mem_classIndexZero
    (hT : T.StronglyAdmissible χ x w E) {F : Region → ℤ} (hF : F ∈ classIndexZero hE χ)
    (hF₀ : 0 ≤ F) : F = 0 := by
  cases isEmpty_or_nonempty Region
  · exact funext fun r => isEmptyElim r
  obtain ⟨P, hP, k, rfl, hk⟩ := hF
  -- At a basepoint `P` vanishes, so `k ≥ 0`.
  obtain ⟨z⟩ := hT.nonempty_basepoint hχ hE
  have hPz : P (T.basepoint z) = 0 :=
    ((mem_triplyPeriodicDomains_iff.mp (doublyPeriodicDomains_le_triplyPeriodicDomains hP)).1 z)
  have hk₀ : 0 ≤ k := by simpa [hPz] using hF₀ (T.basepoint z)
  -- `-P` raises the index by `2 k ≥ 0` but has every coefficient at most `k`, so `P = 0`.
  have hμ : T.periodicMaslovIndex χ x w E (-P) = 2 * k := by
    rw [hE.periodicMaslovIndex_neg χ hP]
    linarith
  have hP₀ : P = 0 := by
    by_contra hne
    obtain ⟨r, hr⟩ := hT (-P) (neg_mem hP) (neg_ne_zero.mpr hne) (by rw [hμ]; positivity)
    have hFr : (0 : ℚ) ≤ P r + k := by exact_mod_cast (by simpa using hF₀ r : 0 ≤ P r + k)
    rw [hμ] at hr
    simp only [Pi.neg_apply, Int.cast_neg] at hr
    linarith
  subst hP₀
  rw [periodicMaslovIndex_zero, zero_add] at hk
  have hk' : k = 0 := by exact_mod_cast (by linarith : (k : ℚ) = 0)
  simp [hk']

omit hE in
include hχ in
/-- **Finiteness for strong admissibility.** If the triple, on a closed surface of genus `n`, is
strongly admissible at the triangle domain `E`, then only finitely many nonnegative domains with a
given Maslov index differ from `E` by a sum of doubly periodic domains and copies of the whole
surface. Unlike `WeaklyAdmissibleAt.finite_setOf_nonneg_sub_mem_maslovIndex_eq`, the basepoint
multiplicities of these domains are not prescribed; this is the finiteness behind the triangle
maps on the flavors recording every basepoint multiplicity by a power of a formal variable. -/
theorem StronglyAdmissible.finite_setOf_nonneg_sub_mem_maslovIndex_eq
    (hT : T.StronglyAdmissible χ x w E) (hE : T.IsTriangleDomain x y w E) (m : ℚ) :
    {D : Region → ℤ | 0 ≤ D ∧ D - E ∈ T.doublyPeriodicDomains ⊔ AddSubgroup.zmultiples 1 ∧
      T.maslovIndex χ x w D = m}.Finite :=
  AddSubgroup.finite_of_forall_sub_mem (P := classIndexZero hE χ)
    (fun _ hF hF₀ => hT.eq_zero_of_mem_classIndexZero hχ hE hF hF₀) (fun _ hD => hD.1)
    fun _ ⟨_, hD, hDm⟩ _ ⟨_, hD', hD'm⟩ =>
      sub_mem_classIndexZero hχ hE hD hD' (hD'm.trans hDm.symm)

end Strong

end Admissible

end HeegaardTripleRegionSystem

end TauCeti
