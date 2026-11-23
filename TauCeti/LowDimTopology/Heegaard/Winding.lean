/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.StrongAdmissibility
import TauCeti.Algebra.Order.Field.IntLattice

/-!
# Admissibility by winding: the uniform coefficient estimate

Ozsváth and Szabó make a pointed Heegaard diagram weakly or strongly admissible by *winding*:
an `α`-curve `αᵢ` is isotoped `N` times around a curve `γᵢ` dual to it, away from the basepoint.
The periodic domains of the wound diagram correspond to those of the original one. Crossing
`αᵢ` changes the multiplicity of a periodic domain `P` by the multiplicity `aᵢ(P)` of `αᵢ` in
its boundary, so in the winding region along `γᵢ` the domain `P` has regions with multiplicities
`p_i(P) + N aᵢ(P)` on one side and `q_i(P) - N aᵢ(P)` on the other, where `p_i(P)` and `q_i(P)`
are multiplicities of `P` next to the winding region; all of these are additive in `P`. On a
Heegaard diagram the `aᵢ` together detect the periodic domains: a periodic domain with no
`α`-boundary has boundary a combination of the `β`-curves, which are linearly independent in
the homology of the surface, so it is a multiple of the whole surface and vanishes at the
basepoint. For large `N` the wound multiplicities then exceed any prescribed additive
functional, such as half the Maslov index, `⟨c₁(s), H(P)⟩ / 2`.

This file proves that estimate, uniformly in `P` and with a single `N₀` for all `N ≥ N₀`, and
deduces weak and strong admissibility of every region system in which such winding regions
appear. Checking the elements of a basis of the periodic domains would not suffice: the
estimate has to hold for every lattice element, including those with arbitrarily large
coefficients. The uniformity comes from bounding every additive functional on the lattice by
the `ℓ¹`-norm `∑ i, |aᵢ(P)|` of the detecting coordinates
(`AddMonoidHom.exists_abs_le_mul_sum_abs`): at a coordinate `i` where `|aᵢ(P)|` is largest,
the term `N |aᵢ(P)|` dominates all the others once `N` exceeds a constant independent of `P`.

The lattice `L` stands for the periodic domains of the original diagram, transported to the
wound diagram `H` by an additive map `e : L →+ (Region → ℤ)` onto the periodic domains of `H`.
The region systems are abstract incidence data
(`TauCeti.HeegaardRegionSystem`), and the theorems below take the winding regions and the
transport as hypotheses: constructing the wound diagrams of an actual Heegaard diagram, and
identifying the Maslov index of transported periodic domains with the Chern class pairing, are
separate geometric steps.

## Main results

* `AddMonoidHom.exists_forall_exists_lt_add_mul_or_lt_sub_mul`: the uniform estimate. For every
  additive functional `c` there is `N₀` such that for `N ≥ N₀` every nonzero `P` has an index
  `i` with `c P < p_i(P) + N aᵢ(P)` or `c P < q_i(P) - N aᵢ(P)`.
* `TauCeti.HeegaardRegionSystem.exists_forall_weaklyAdmissible_of_winding`: sufficiently wound
  diagrams are weakly admissible.
* `TauCeti.HeegaardRegionSystem.exists_forall_weaklyAdmissibleAt_of_winding`: sufficiently wound
  diagrams are weakly admissible at a generator, when the `aᵢ` only detect the periodic domains
  of Maslov index zero there.
* `TauCeti.HeegaardRegionSystem.exists_forall_stronglyAdmissible_of_winding`: sufficiently wound
  diagrams are strongly admissible at a generator.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §5: Lemma 5.2 (weakly admissible
  diagrams by winding) and Lemma 5.4 (strongly admissible diagrams by winding).
-/

public section

namespace TauCeti

universe u v w

namespace HeegaardRegionSystem

variable {L ι : Type*} [AddCommGroup L] [Finite ι]

omit [Finite ι] in
/-- A region realizing a winding multiplicity of `e P` above `t` gives a region of `e P` above
`t`. -/
private theorem exists_lt_of_winding {Region : Type*} {a p q : ι → L →+ ℤ}
    {e : L →+ (Region → ℤ)} {N : ℕ}
    (hp : ∀ i, ∃ r, ∀ P, e P r = p i P + N * a i P)
    (hq : ∀ i, ∃ r, ∀ P, e P r = q i P - N * a i P) {P : L} {t : ℚ}
    (h : ∃ i, t < ((p i P + N * a i P : ℤ) : ℚ) ∨ t < ((q i P - N * a i P : ℤ) : ℚ)) :
    ∃ r, t < (e P r : ℚ) := by
  obtain ⟨i, h | h⟩ := h
  · obtain ⟨r, hr⟩ := hp i
    exact ⟨r, by rwa [hr]⟩
  · obtain ⟨r, hr⟩ := hq i
    exact ⟨r, by rwa [hr]⟩

omit [Finite ι] in
/-- If the winding estimate with `c = 0` holds for `P` and `-P`, then `e P` has a positive and a
negative coefficient. -/
private theorem exists_pos_and_neg_of_winding {Region : Type*} {a p q : ι → L →+ ℤ}
    {e : L →+ (Region → ℤ)} {N : ℕ}
    (hp : ∀ i, ∃ r, ∀ P, e P r = p i P + N * a i P)
    (hq : ∀ i, ∃ r, ∀ P, e P r = q i P - N * a i P)
    (hest : ∀ P, P ≠ 0 → ∃ i, (0 : L →+ ℚ) P < ((p i P + N * a i P : ℤ) : ℚ) ∨
      (0 : L →+ ℚ) P < ((q i P - N * a i P : ℤ) : ℚ))
    {P : L} (hP : P ≠ 0) : (∃ r, 0 < e P r) ∧ ∃ r, e P r < 0 := by
  obtain ⟨r, hr⟩ := exists_lt_of_winding hp hq (hest P hP)
  obtain ⟨s, hs⟩ := exists_lt_of_winding hp hq (hest (-P) (neg_ne_zero.mpr hP))
  exact ⟨⟨r, by simpa using hr⟩, ⟨s, by simpa using hs⟩⟩

/-- **Weak admissibility by winding.** Let the coordinates `aᵢ` detect the elements of `L`.
Then there is `N₀` such that, for every `N ≥ N₀`, a region system is weakly admissible as soon
as an additive map `e : L →+ (Region → ℤ)` reaches all its periodic domains and, for each `i`,
there are regions on which `e P` has multiplicities `p_i(P) + N aᵢ(P)` and `q_i(P) - N aᵢ(P)`. -/
theorem exists_forall_weaklyAdmissible_of_winding {a : ι → L →+ ℤ}
    (ha : ∀ P, (∀ i, a i P = 0) → P = 0) (p q : ι → L →+ ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ {n : ℕ} {Point : Type u} {Region : Type v}
      {Basepoint : Type w} (H : HeegaardRegionSystem n Point Region Basepoint)
      (e : L →+ (Region → ℤ)), (∀ D ∈ H.periodicDomains, ∃ P, e P = D) →
      (∀ i, ∃ r, ∀ P, e P r = p i P + N * a i P) →
      (∀ i, ∃ r, ∀ P, e P r = q i P - N * a i P) → H.WeaklyAdmissible := by
  obtain ⟨N₀, hN₀⟩ :=
    AddMonoidHom.exists_forall_exists_lt_add_mul_or_lt_sub_mul ha p q (0 : L →+ ℚ)
  refine ⟨N₀, fun N hN n Point Region Basepoint H e he hp hq =>
    weaklyAdmissible_iff.mpr fun D hD hD₀ => ?_⟩
  obtain ⟨P, rfl⟩ := he D hD
  by_contra hne
  obtain ⟨-, r, hr⟩ := exists_pos_and_neg_of_winding (P := P) hp hq (hN₀ N hN)
    (by rintro rfl; exact hne (map_zero e))
  exact (hD₀ r).not_gt hr

/-- **Weak admissibility at a generator by winding.** Let `c : L →+ ℚ` give the Maslov indices
of the transported periodic domains at a generator `x`, and let the coordinates `aᵢ` detect the
elements of `L` with `c P = 0`. Then there is `N₀` such that, for every `N ≥ N₀`, a region
system is weakly admissible at `x` as soon as an additive map `e : L →+ (Region → ℤ)` reaches
all its periodic domains, `H.maslovIndex χ x x (e P) = c P`, and, for each `i`, there are
regions on which `e P` has multiplicities `p_i(P) + N aᵢ(P)` and `q_i(P) - N aᵢ(P)`. -/
theorem exists_forall_weaklyAdmissibleAt_of_winding (c : L →+ ℚ) {a : ι → L →+ ℤ}
    (ha : ∀ P, c P = 0 → (∀ i, a i P = 0) → P = 0) (p q : ι → L →+ ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ {n : ℕ} {Point : Type u} {Region : Type v}
      {Basepoint : Type w} [Fintype Point] [Fintype Region] [DecidableEq Region]
      (H : HeegaardRegionSystem n Point Region Basepoint) (χ : Region → ℤ) (x : H.Generator)
      (e : L →+ (Region → ℤ)), (∀ D ∈ H.periodicDomains, ∃ P, e P = D) →
      (∀ P, H.maslovIndex χ x x (e P) = c P) →
      (∀ i, ∃ r, ∀ P, e P r = p i P + N * a i P) →
      (∀ i, ∃ r, ∀ P, e P r = q i P - N * a i P) → H.WeaklyAdmissibleAt χ x := by
  -- Apply the estimate on the lattice `ker c` of elements of Maslov index zero.
  let incl := c.ker.subtype
  obtain ⟨N₀, hN₀⟩ := AddMonoidHom.exists_forall_exists_lt_add_mul_or_lt_sub_mul
    (a := fun i => (a i).comp incl)
    (fun P hP => Subtype.ext (ha P P.2 (by simpa using hP)))
    (fun i => (p i).comp incl) (fun i => (q i).comp incl)
    (0 : c.ker →+ ℚ)
  refine ⟨N₀, fun N hN n Point Region Basepoint _ _ _ H χ x e he hc hp hq =>
    weaklyAdmissibleAt_def.mpr fun D hD hD0 hD₀ => ?_⟩
  obtain ⟨P, rfl⟩ := he D hD
  have hP : P ∈ c.ker := by rw [AddMonoidHom.mem_ker, ← hc]; exact hD0
  exact exists_pos_and_neg_of_winding (e := e.comp incl) (P := ⟨P, hP⟩)
    (fun i => (hp i).imp fun _ hr P => by simpa using hr P)
    (fun i => (hq i).imp fun _ hr P => by simpa using hr P)
    (hN₀ N hN) (by rintro ⟨⟩; exact hD₀ (map_zero e))

/-- **Strong admissibility by winding.** Let `c : L →+ ℚ` give the Maslov indices of the
transported periodic domains at a generator `x`, and let the coordinates `aᵢ` detect the
elements of `L`. Then there is `N₀` such that, for every `N ≥ N₀`, a region system is strongly
admissible at `x` as soon as an additive map `e : L →+ (Region → ℤ)` reaches all its periodic
domains, `H.maslovIndex χ x x (e P) = c P`, and, for each `i`, there are regions on which `e P`
has multiplicities `p_i(P) + N aᵢ(P)` and `q_i(P) - N aᵢ(P)`. -/
theorem exists_forall_stronglyAdmissible_of_winding (c : L →+ ℚ) {a : ι → L →+ ℤ}
    (ha : ∀ P, (∀ i, a i P = 0) → P = 0) (p q : ι → L →+ ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ {n : ℕ} {Point : Type u} {Region : Type v}
      {Basepoint : Type w} [Fintype Point] [Fintype Region] [DecidableEq Region]
      (H : HeegaardRegionSystem n Point Region Basepoint) (χ : Region → ℤ) (x : H.Generator)
      (e : L →+ (Region → ℤ)), (∀ D ∈ H.periodicDomains, ∃ P, e P = D) →
      (∀ P, H.maslovIndex χ x x (e P) = c P) →
      (∀ i, ∃ r, ∀ P, e P r = p i P + N * a i P) →
      (∀ i, ∃ r, ∀ P, e P r = q i P - N * a i P) → H.StronglyAdmissible χ x := by
  obtain ⟨N₀, hN₀⟩ := AddMonoidHom.exists_forall_exists_lt_add_mul_or_lt_sub_mul ha p q
    ((AddMonoidHom.mulLeft (2⁻¹ : ℚ)).comp c)
  refine ⟨N₀, fun N hN n Point Region Basepoint _ _ _ H χ x e he hc hp hq =>
    stronglyAdmissible_iff.mpr fun D hD hD₀ _ => ?_⟩
  obtain ⟨P, rfl⟩ := he D hD
  have hP : P ≠ 0 := by rintro rfl; exact hD₀ (map_zero e)
  obtain ⟨r, hr⟩ := exists_lt_of_winding hp hq (hN₀ N hN P hP)
  refine ⟨r, ?_⟩
  rw [hc, div_eq_inv_mul]
  simpa using hr

end HeegaardRegionSystem

end TauCeti
