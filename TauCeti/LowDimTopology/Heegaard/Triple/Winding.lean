/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.Triple.SpincAdmissibility
public import TauCeti.LowDimTopology.Heegaard.Winding

/-!
# Admissibility of Heegaard triples by winding

Ozsváth and Szabó make a pointed Heegaard diagram weakly or strongly admissible by winding its
attaching curves along dual curves, away from the basepoint, and the triangle maps need the same
for Heegaard triple diagrams `(Σ, α, β, γ, z)`: the sums of doubly periodic domains must have
coefficients of both signs, or a coefficient larger than half the change `μ(E + P) - μ(E)` of the
Maslov index of a triangle domain `E`
(`TauCeti.HeegaardTripleRegionSystem.WeaklyAdmissibleAt` and
`TauCeti.HeegaardTripleRegionSystem.StronglyAdmissible`). This file is the triangle version of
`TauCeti.LowDimTopology.Heegaard.Winding`.

The lattice `L` stands for the sums of doubly periodic domains of the original triple, transported
to the wound triple `T` by an additive map `e : L →+ (Region → ℤ)` onto the sums of doubly periodic
domains of `T`. Coordinates `aᵢ : L →+ ℤ` detecting the elements of `L`, such as the multiplicities
of the attaching curves in the boundary, are wound `N` times: for each `i` there are regions of
`T` on which `e P` has the multiplicities `p_i(P) + N aᵢ(P)` and `q_i(P) - N aᵢ(P)`, with additive
`p_i`, `q_i`. The uniform winding estimate
`AddMonoidHom.exists_forall_exists_lt_add_mul_or_lt_sub_mul` then gives one `N₀`, depending only
on `L`, the `aᵢ`, `p_i`, `q_i` and the Maslov functional, such that every wound triple with
`N ≥ N₀` is admissible. The weak admissibility at a triangle domain only needs the `aᵢ` to detect
the elements of Maslov index zero. The arguments are those for diagrams, stated in
`TauCeti.LowDimTopology.Heegaard.Winding` for any subgroup of `Region → ℤ`
(`TauCeti.exists_forall_nonneg_eq_zero_of_winding`,
`TauCeti.exists_forall_exists_pos_and_neg_of_winding` and
`TauCeti.exists_forall_exists_half_lt_of_winding`), applied here to the sums of doubly periodic
domains.

The triples are abstract incidence data (`TauCeti.HeegaardTripleRegionSystem`), and the winding
regions and the transport `e` are hypotheses: constructing the wound triples of an actual Heegaard
triple diagram, and identifying the Maslov indices of transported domains with the Chern class
pairings of the spin^c structures of triangles, are separate geometric steps.

## Main results

* `TauCeti.HeegaardTripleRegionSystem.exists_forall_weaklyAdmissible_of_winding`: sufficiently
  wound triples are weakly admissible.
* `TauCeti.HeegaardTripleRegionSystem.exists_forall_weaklyAdmissibleAt_of_winding`: sufficiently
  wound triples are weakly admissible at a triangle domain, when the `aᵢ` only detect the elements
  of Maslov index zero there.
* `TauCeti.HeegaardTripleRegionSystem.exists_forall_stronglyAdmissible_of_winding`: sufficiently
  wound triples are strongly admissible at a triangle domain.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §5, Lemmas 5.2 and 5.4 (admissibility
  by winding), and §8, Definition 8.8 (admissibility of triples).
-/

public section

namespace TauCeti

universe u₁ u₂ u₃ v w

namespace HeegaardTripleRegionSystem

variable {L ι : Type*} [AddCommGroup L] [Finite ι]

/-- **Weak admissibility of triples by winding.** Let the coordinates `aᵢ` detect the elements of
`L`. Then there is `N₀` such that, for every `N ≥ N₀`, a Heegaard triple is weakly admissible as
soon as an additive map `e : L →+ (Region → ℤ)` reaches all its sums of doubly periodic domains
and, for each `i`, there are regions on which `e P` has multiplicities `p_i(P) + N aᵢ(P)` and
`q_i(P) - N aᵢ(P)`. -/
theorem exists_forall_weaklyAdmissible_of_winding {a : ι → L →+ ℤ}
    (ha : ∀ P, (∀ i, a i P = 0) → P = 0) (p q : ι → L →+ ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ {n : ℕ} {PointAB : Type u₁} {PointBC : Type u₂}
      {PointAC : Type u₃} {Region : Type v} {Basepoint : Type w}
      (T : HeegaardTripleRegionSystem n PointAB PointBC PointAC Region Basepoint)
      (e : L →+ (Region → ℤ)), (∀ D ∈ T.doublyPeriodicDomains, ∃ P, e P = D) →
      (∀ i, ∃ r, ∀ P, e P r = p i P + N * a i P) →
      (∀ i, ∃ r, ∀ P, e P r = q i P - N * a i P) → T.WeaklyAdmissible := by
  obtain ⟨N₀, hN₀⟩ := exists_forall_nonneg_eq_zero_of_winding ha p q
  exact ⟨N₀, fun N hN n PointAB PointBC PointAC Region Basepoint T e he hp hq =>
    weaklyAdmissible_iff.mpr (hN₀ N hN T.doublyPeriodicDomains e he hp hq)⟩

/-- **Weak admissibility of triples at a triangle domain by winding.** Let `c : L →+ ℚ` give the
changes of the Maslov index of a triangle domain `E` by the transported sums of doubly periodic
domains, and let the coordinates `aᵢ` detect the elements of `L` with `c P = 0`. Then there is
`N₀` such that, for every `N ≥ N₀`, a Heegaard triple is weakly admissible at `E` as soon as an
additive map `e : L →+ (Region → ℤ)` reaches all its sums of doubly periodic domains,
`μ(E + e P) - μ(E) = c P`, and, for each `i`, there are regions on which `e P` has multiplicities
`p_i(P) + N aᵢ(P)` and `q_i(P) - N aᵢ(P)`. -/
theorem exists_forall_weaklyAdmissibleAt_of_winding (c : L →+ ℚ) {a : ι → L →+ ℤ}
    (ha : ∀ P, c P = 0 → (∀ i, a i P = 0) → P = 0) (p q : ι → L →+ ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ {n : ℕ} {PointAB : Type u₁} {PointBC : Type u₂}
      {PointAC : Type u₃} {Region : Type v} {Basepoint : Type w} [Fintype PointAB]
      [Fintype PointBC] [Fintype PointAC] [Fintype Region]
      (T : HeegaardTripleRegionSystem n PointAB PointBC PointAC Region Basepoint)
      (χ : Region → ℤ) (x : T.alphaBeta.Generator) (w : T.alphaGamma.Generator)
      (E : Region → ℤ) (e : L →+ (Region → ℤ)),
      (∀ D ∈ T.doublyPeriodicDomains, ∃ P, e P = D) →
      (∀ P, T.periodicMaslovIndex χ x w E (e P) = c P) →
      (∀ i, ∃ r, ∀ P, e P r = p i P + N * a i P) →
      (∀ i, ∃ r, ∀ P, e P r = q i P - N * a i P) → T.WeaklyAdmissibleAt χ x w E := by
  obtain ⟨N₀, hN₀⟩ := exists_forall_exists_pos_and_neg_of_winding c ha p q
  exact ⟨N₀, fun N hN n PointAB PointBC PointAC Region Basepoint _ _ _ _ T χ x w E e he hc hp hq =>
    weaklyAdmissibleAt_def.mpr
      (hN₀ N hN T.doublyPeriodicDomains (T.periodicMaslovIndex χ x w E) e he hc hp hq)⟩

/-- **Strong admissibility of triples at a triangle domain by winding.** Let `c : L →+ ℚ` give the
changes of the Maslov index of a triangle domain `E` by the transported sums of doubly periodic
domains, and let the coordinates `aᵢ` detect the elements of `L`. Then there is `N₀` such that,
for every `N ≥ N₀`, a Heegaard triple is strongly admissible at `E` as soon as an additive map
`e : L →+ (Region → ℤ)` reaches all its sums of doubly periodic domains,
`μ(E + e P) - μ(E) = c P`, and, for each `i`, there are regions on which `e P` has multiplicities
`p_i(P) + N aᵢ(P)` and `q_i(P) - N aᵢ(P)`. -/
theorem exists_forall_stronglyAdmissible_of_winding (c : L →+ ℚ) {a : ι → L →+ ℤ}
    (ha : ∀ P, (∀ i, a i P = 0) → P = 0) (p q : ι → L →+ ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ {n : ℕ} {PointAB : Type u₁} {PointBC : Type u₂}
      {PointAC : Type u₃} {Region : Type v} {Basepoint : Type w} [Fintype PointAB]
      [Fintype PointBC] [Fintype PointAC] [Fintype Region]
      (T : HeegaardTripleRegionSystem n PointAB PointBC PointAC Region Basepoint)
      (χ : Region → ℤ) (x : T.alphaBeta.Generator) (w : T.alphaGamma.Generator)
      (E : Region → ℤ) (e : L →+ (Region → ℤ)),
      (∀ D ∈ T.doublyPeriodicDomains, ∃ P, e P = D) →
      (∀ P, T.periodicMaslovIndex χ x w E (e P) = c P) →
      (∀ i, ∃ r, ∀ P, e P r = p i P + N * a i P) →
      (∀ i, ∃ r, ∀ P, e P r = q i P - N * a i P) → T.StronglyAdmissible χ x w E := by
  obtain ⟨N₀, hN₀⟩ := exists_forall_exists_half_lt_of_winding c ha p q
  exact ⟨N₀, fun N hN n PointAB PointBC PointAC Region Basepoint _ _ _ _ T χ x w E e he hc hp hq =>
    stronglyAdmissible_iff.mpr fun D hD hD₀ _ =>
      hN₀ N hN T.doublyPeriodicDomains (T.periodicMaslovIndex χ x w E) e he hc hp hq D hD hD₀⟩

end HeegaardTripleRegionSystem

end TauCeti
