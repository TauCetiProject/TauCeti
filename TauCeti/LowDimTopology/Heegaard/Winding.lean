/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.StrongAdmissibility
import TauCeti.Analysis.Normed.Group.LatticeBound

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

That estimate holds uniformly in `P`, with a single `N₀` for all `N ≥ N₀`
(`AddMonoidHom.exists_forall_exists_lt_add_mul_or_lt_sub_mul`), and this file deduces weak and
strong admissibility of every region system in which such winding regions
appear. Checking the elements of a basis of the periodic domains would not suffice: the
estimate has to hold for every lattice element, including those with arbitrarily large
coefficients. The uniformity comes from bounding every additive functional on the lattice by
the sup norm of the detecting coordinates `aᵢ(P)`
(`AddMonoidHom.exists_norm_le_mul_norm_of_injective`): at a coordinate `i` where `|aᵢ(P)|` is
largest, the term `N |aᵢ(P)|` dominates all the others once `N` exceeds a constant independent of
`P`.

The lattice `L` stands for the periodic domains of the original diagram, transported to the
wound diagram `H` by an additive map `e : L →+ (Region → ℤ)` onto the periodic domains of `H`.
The region systems are abstract incidence data
(`TauCeti.HeegaardRegionSystem`), and the theorems below take the winding regions and the
transport as hypotheses: constructing the wound diagrams of an actual Heegaard diagram, and
identifying the Maslov index of transported periodic domains with the Chern class pairing, are
separate geometric steps.

The criteria of `TauCeti.LowDimTopology.Heegaard.PeriodicNorm` start instead from regions whose
multiplicities dominate a norm of the periodic domains of one fixed region system, with a
threshold depending on that system. Here the winding regions are hypotheses about the transport
`e`, so one `N₀`, depending only on `L`, the `aᵢ`, `p_i`, `q_i` and the Maslov functional, serves
every wound region system; and the weak admissibility at a generator needs the `aᵢ` to detect only
the periodic domains of Maslov index zero.

## Main results

* `TauCeti.exists_lt_of_winding` and `TauCeti.exists_pos_and_neg_of_winding`: the coefficients of
  `e P` in the winding regions, for an additive map `e` into the domains of any region system.
* `TauCeti.exists_forall_nonneg_eq_zero_of_winding`,
  `TauCeti.exists_forall_exists_pos_and_neg_of_winding` and
  `TauCeti.exists_forall_exists_half_lt_of_winding`: the three admissibility conditions below for
  any subgroup `S` of `Region → ℤ` reached by `e`, and any functional `m` with `m (e P) = c P` in
  place of the Maslov index; the versions for Heegaard triples in
  `TauCeti.LowDimTopology.Heegaard.Triple.Winding` use them too.
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

variable {L ι : Type*} [AddCommGroup L]

/-- Let `e : L →+ (Region → ℤ)` have, for each `i`, a region on which `e P` has multiplicity
`p_i(P) + N aᵢ(P)` and a region on which it has multiplicity `q_i(P) - N aᵢ(P)`, for all `P`. If one
of these winding multiplicities of `P` exceeds `t`, then some coefficient of `e P` exceeds `t`. -/
theorem exists_lt_of_winding {Region : Type*} {a p q : ι → L →+ ℤ}
    {e : L →+ (Region → ℤ)} {N : ℕ}
    (hp : ∀ i, ∃ r, ∀ P, e P r = p i P + N * a i P)
    (hq : ∀ i, ∃ r, ∀ P, e P r = q i P - N * a i P) {P : L} {t : ℝ}
    (h : ∃ i, t < ((p i P + N * a i P : ℤ) : ℝ) ∨ t < ((q i P - N * a i P : ℤ) : ℝ)) :
    ∃ r, t < (e P r : ℝ) := by
  obtain ⟨i, h | h⟩ := h
  · obtain ⟨r, hr⟩ := hp i
    exact ⟨r, by rwa [hr]⟩
  · obtain ⟨r, hr⟩ := hq i
    exact ⟨r, by rwa [hr]⟩

/-- Let `e : L →+ (Region → ℤ)` have the winding regions of `exists_lt_of_winding`. If the winding
estimate `AddMonoidHom.exists_forall_exists_lt_add_mul_or_lt_sub_mul` with the functional `0` holds
at `N`, then `e P` has a positive and a negative coefficient for every `P ≠ 0`. -/
theorem exists_pos_and_neg_of_winding {Region : Type*} {a p q : ι → L →+ ℤ}
    {e : L →+ (Region → ℤ)} {N : ℕ}
    (hp : ∀ i, ∃ r, ∀ P, e P r = p i P + N * a i P)
    (hq : ∀ i, ∃ r, ∀ P, e P r = q i P - N * a i P)
    (hest : ∀ P, P ≠ 0 → ∃ i, (0 : L →+ ℝ) P < ((p i P + N * a i P : ℤ) : ℝ) ∨
      (0 : L →+ ℝ) P < ((q i P - N * a i P : ℤ) : ℝ))
    {P : L} (hP : P ≠ 0) : (∃ r, 0 < e P r) ∧ ∃ r, e P r < 0 := by
  obtain ⟨r, hr⟩ := exists_lt_of_winding hp hq (hest P hP)
  obtain ⟨s, hs⟩ := exists_lt_of_winding hp hq (hest (-P) (neg_ne_zero.mpr hP))
  exact ⟨⟨r, by simpa using hr⟩, ⟨s, by simpa using hs⟩⟩

variable [Finite ι]

/-- **Nonnegative domains vanish after winding.** Let the coordinates `aᵢ` detect the elements of
`L`. Then there is `N₀` such that, for every `N ≥ N₀`, the only nonnegative element of a subgroup
`S` of domains is `0`, as soon as an additive map `e : L →+ (Region → ℤ)` reaches all of `S` and,
for each `i`, there are regions on which `e P` has multiplicities `p_i(P) + N aᵢ(P)` and
`q_i(P) - N aᵢ(P)`. This is weak admissibility by winding, for diagrams and for triples. -/
theorem exists_forall_nonneg_eq_zero_of_winding {a : ι → L →+ ℤ}
    (ha : ∀ P, (∀ i, a i P = 0) → P = 0) (p q : ι → L →+ ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ {Region : Type v} (S : AddSubgroup (Region → ℤ))
      (e : L →+ (Region → ℤ)), (∀ D ∈ S, ∃ P, e P = D) →
      (∀ i, ∃ r, ∀ P, e P r = p i P + N * a i P) →
      (∀ i, ∃ r, ∀ P, e P r = q i P - N * a i P) → ∀ D ∈ S, 0 ≤ D → D = 0 := by
  obtain ⟨N₀, hN₀⟩ :=
    AddMonoidHom.exists_forall_exists_lt_add_mul_or_lt_sub_mul ha p q (0 : L →+ ℝ)
  refine ⟨N₀, fun N hN Region S e he hp hq D hD hD₀ => ?_⟩
  obtain ⟨P, rfl⟩ := he D hD
  by_contra hne
  obtain ⟨-, r, hr⟩ := exists_pos_and_neg_of_winding (P := P) hp hq (hN₀ N hN)
    (by rintro rfl; exact hne (map_zero e))
  exact (hD₀ r).not_gt hr

/-- **Domains of index zero have coefficients of both signs after winding.** Let `c : L →+ ℚ` and
let the coordinates `aᵢ` detect the elements of `L` with `c P = 0`. Then there is `N₀` such that,
for every `N ≥ N₀`, every nonzero element `D` of a subgroup `S` of domains with `m D = 0` has a
positive and a negative coefficient, as soon as an additive map `e : L →+ (Region → ℤ)` reaches
all of `S`, `m (e P) = c P`, and, for each `i`, there are regions on which `e P` has multiplicities
`p_i(P) + N aᵢ(P)` and `q_i(P) - N aᵢ(P)`. This is weak admissibility at a generator or a
triangle domain by winding, for `m` the Maslov index. -/
theorem exists_forall_exists_pos_and_neg_of_winding (c : L →+ ℚ) {a : ι → L →+ ℤ}
    (ha : ∀ P, c P = 0 → (∀ i, a i P = 0) → P = 0) (p q : ι → L →+ ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ {Region : Type v} (S : AddSubgroup (Region → ℤ))
      (m : (Region → ℤ) → ℚ) (e : L →+ (Region → ℤ)), (∀ D ∈ S, ∃ P, e P = D) →
      (∀ P, m (e P) = c P) →
      (∀ i, ∃ r, ∀ P, e P r = p i P + N * a i P) →
      (∀ i, ∃ r, ∀ P, e P r = q i P - N * a i P) →
      ∀ D ∈ S, m D = 0 → D ≠ 0 → (∃ r, 0 < D r) ∧ ∃ r, D r < 0 := by
  -- Apply the estimate on the lattice `ker c` of elements of Maslov index zero.
  let incl := c.ker.subtype
  obtain ⟨N₀, hN₀⟩ := AddMonoidHom.exists_forall_exists_lt_add_mul_or_lt_sub_mul
    (a := fun i => (a i).comp incl)
    (fun P hP => Subtype.ext (ha P P.property (by simpa [incl] using hP)))
    (fun i => (p i).comp incl) (fun i => (q i).comp incl)
    (0 : c.ker →+ ℝ)
  refine ⟨N₀, fun N hN Region S m e he hc hp hq D hD hD0 hD₀ => ?_⟩
  obtain ⟨P, rfl⟩ := he D hD
  have hP : P ∈ c.ker := by rw [AddMonoidHom.mem_ker, ← hc]; exact hD0
  exact exists_pos_and_neg_of_winding (e := e.comp incl) (P := ⟨P, hP⟩)
    (fun i => (hp i).imp fun _ hr P => by simpa [incl] using hr P)
    (fun i => (hq i).imp fun _ hr P => by simpa [incl] using hr P)
    (hN₀ N hN) fun h => hD₀ (by rw [(AddSubgroup.mk_eq_zero _).mp h, map_zero])

/-- **Large coefficients after winding.** Let `c : L →+ ℚ` and let the coordinates `aᵢ` detect the
elements of `L`. Then there is `N₀` such that, for every `N ≥ N₀`, every nonzero element `D` of a
subgroup `S` of domains has a coefficient larger than `m D / 2`, as soon as an additive map
`e : L →+ (Region → ℤ)` reaches all of `S`, `m (e P) = c P`, and, for each `i`, there are regions on
which `e P` has multiplicities `p_i(P) + N aᵢ(P)` and `q_i(P) - N aᵢ(P)`. This is strong
admissibility by winding, for `m` the Maslov index. -/
theorem exists_forall_exists_half_lt_of_winding (c : L →+ ℚ) {a : ι → L →+ ℤ}
    (ha : ∀ P, (∀ i, a i P = 0) → P = 0) (p q : ι → L →+ ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ {Region : Type v} (S : AddSubgroup (Region → ℤ))
      (m : (Region → ℤ) → ℚ) (e : L →+ (Region → ℤ)), (∀ D ∈ S, ∃ P, e P = D) →
      (∀ P, m (e P) = c P) →
      (∀ i, ∃ r, ∀ P, e P r = p i P + N * a i P) →
      (∀ i, ∃ r, ∀ P, e P r = q i P - N * a i P) →
      ∀ D ∈ S, D ≠ 0 → ∃ r, m D / 2 < D r := by
  obtain ⟨N₀, hN₀⟩ := AddMonoidHom.exists_forall_exists_lt_add_mul_or_lt_sub_mul ha p q
    ((Rat.castHom ℝ).toAddMonoidHom.comp ((AddMonoidHom.mulLeft (2⁻¹ : ℚ)).comp c))
  refine ⟨N₀, fun N hN Region S m e he hc hp hq D hD hD₀ => ?_⟩
  obtain ⟨P, rfl⟩ := he D hD
  have hP : P ≠ 0 := by rintro rfl; exact hD₀ (map_zero e)
  obtain ⟨r, hr⟩ := exists_lt_of_winding hp hq (hN₀ N hN P hP)
  refine ⟨r, ?_⟩
  rw [hc, div_eq_inv_mul, ← Rat.cast_lt (K := ℝ)]
  simpa using hr

namespace HeegaardRegionSystem

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
  obtain ⟨N₀, hN₀⟩ := exists_forall_nonneg_eq_zero_of_winding ha p q
  exact ⟨N₀, fun N hN n Point Region Basepoint H e he hp hq =>
    weaklyAdmissible_iff.mpr (hN₀ N hN H.periodicDomains e he hp hq)⟩

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
  obtain ⟨N₀, hN₀⟩ := exists_forall_exists_pos_and_neg_of_winding c ha p q
  exact ⟨N₀, fun N hN n Point Region Basepoint _ _ _ H χ x e he hc hp hq =>
    weaklyAdmissibleAt_def.mpr (hN₀ N hN H.periodicDomains _ e he hc hp hq)⟩

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
  obtain ⟨N₀, hN₀⟩ := exists_forall_exists_half_lt_of_winding c ha p q
  exact ⟨N₀, fun N hN n Point Region Basepoint _ _ _ H χ x e he hc hp hq =>
    stronglyAdmissible_iff.mpr fun D hD hD₀ _ =>
      hN₀ N hN H.periodicDomains _ e he hc hp hq D hD hD₀⟩

end HeegaardRegionSystem

end TauCeti
