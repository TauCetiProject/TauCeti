/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.Subgroup

import TauCeti.NumberTheory.NumberField.Global.Places.Connected
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic
import TauCeti.Topology.Algebra.Group.Units

/-!
# Every open subgroup of the idele class group contains a ray subgroup

Let `K` be a number field.  The ray subgroups `raySubgroup 𝔪`, indexed by the moduli `𝔪` of `K`,
are open subgroups of the idele class group `C_K`.  This file proves that they are cofinal among
all open subgroups: every open subgroup of `C_K` contains `raySubgroup 𝔪` for some modulus `𝔪`.
Consequently the finite quotients `C_K / raySubgroup 𝔪 ≅ Cl_𝔪` see every open subgroup, which is
what identifies the continuous finite-order characters of `C_K` with the ray class characters.

The proof works in the idele group.  An open subgroup `V` of the ideles is a neighbourhood of `1`,
so it contains all ideles `x` with `x` and `x⁻¹` in a neighbourhood `W` of `1` in the adele ring.
The finite part of `W` contains a basic congruence neighbourhood: integrality at every finite
place and a congruence `x_v ≡ 1` to some level `n v` at finitely many places `v`.  The modulus `𝔪`
with exponent `n v` at those places and every real place in its infinite part therefore has
`ideleCongruenceSubgroup 𝔪 ≤ V`, once the archimedean components are handled: an open subgroup is
closed, so `V` contains every connected set of ideles through `1`, hence all ideles concentrated at
a complex place and all positive ideles concentrated at a real place.  The finite and archimedean
components of a congruence idele are then separately in `V`.

Since the ray subgroups and the idele congruence subgroups are themselves open, a subgroup of the
idele class group or of the idele group is open exactly when it contains one of them.

## Main results

* `TauCeti.GlobalNumberFields.ofCompletion_mem_of_isOpen`: an open subgroup of the idele group
  contains every idele concentrated at a complex place and every positive idele concentrated at a
  real place.
* `TauCeti.GlobalNumberFields.exists_ideleCongruenceSubgroup_le_of_isOpen`: every open subgroup
  of the idele group contains an idele congruence subgroup.
* `TauCeti.GlobalNumberFields.isOpen_iff_exists_ideleCongruenceSubgroup_le`: a subgroup of the
  idele group is open exactly when it contains an idele congruence subgroup.
* `TauCeti.GlobalNumberFields.exists_raySubgroup_le_of_isOpen`: every open subgroup of the idele
  class group contains a ray subgroup.
* `TauCeti.GlobalNumberFields.isOpen_iff_exists_raySubgroup_le`: a subgroup of the idele class
  group is open exactly when it contains a ray subgroup.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §17.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Filter Topology
open scoped NumberField NumberField.AdeleRing WithZero

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K]

section

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]

/-- **An open subgroup of the idele group contains the archimedean identity component**: it
contains every idele concentrated at a complex place and every positive idele concentrated at a real
place.  Membership of an idele in an open subgroup therefore depends on its archimedean components
only through their signs at the real places. -/
theorem ofCompletion_mem_of_isOpen {V : Subgroup (IdeleGroup R K)}
    (hV : IsOpen (V : Set (IdeleGroup R K))) (w : InfinitePlace K) (u : w.Completionˣ)
    (hu : ∀ hw : w.IsReal, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw u) :
    IdeleGroup.ofCompletion R K w u ∈ V := by
  have hopen : IsOpen ((V.comap (IdeleGroup.ofCompletion R K w) : Subgroup w.Completionˣ) :
      Set w.Completionˣ) := by
    rw [Subgroup.coe_comap]
    exact hV.preimage (IdeleGroup.continuous_ofCompletion R K w)
  have hclopen : IsClopen ((V.comap (IdeleGroup.ofCompletion R K w) : Subgroup w.Completionˣ) :
      Set w.Completionˣ) :=
    ⟨Subgroup.isClosed_of_isOpen _ hopen, hopen⟩
  rw [← Subgroup.mem_comap]
  rcases w.isReal_or_isComplex with hw | hw
  · exact (InfinitePlace.Completion.isPreconnected_setOf_extensionEmbeddingOfIsReal_pos
      hw).subset_isClopen hclopen ⟨1, by simp, one_mem _⟩ (hu hw)
  · have := InfinitePlace.Completion.connectedSpace_units_of_isComplex hw
    exact Set.eq_univ_iff_forall.mp (hclopen.eq_univ ⟨1, one_mem _⟩) u

end

variable [NumberField K]

/-- **Every open subgroup of the idele group contains an idele congruence subgroup.**  The idele
congruence subgroups are therefore cofinal among the open subgroups of the idele group; see
`isOpen_iff_exists_ideleCongruenceSubgroup_le` for the resulting characterisation of openness. -/
theorem exists_ideleCongruenceSubgroup_le_of_isOpen (V : Subgroup (IdeleGroup (𝓞 K) K))
    (hV : IsOpen (V : Set (IdeleGroup (𝓞 K) K))) :
    ∃ 𝔪 : Modulus K, ideleCongruenceSubgroup 𝔪 ≤ V := by
  classical
  -- Neighbourhoods `W₁` of `1` and `W₂` of `1⁻¹ = 1` in the adele ring controlling membership in
  -- `V` through `x` and `x⁻¹`.
  obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := Units.mem_nhds_iff.mp (hV.mem_nhds V.one_mem)
  have hW₁' : W₁ ∈ 𝓝 (1 : 𝔸[K]) := by simpa using hW₁
  have hW₂' : W₂ ∈ 𝓝 (1 : 𝔸[K]) := by simpa using hW₂
  -- The adele ring is the product of the infinite and the finite adeles.
  obtain ⟨Winf, hWinf, Wf, hWf, hWprod⟩ := mem_nhds_prod_iff.mp (inter_mem hW₁' hW₂' :
    W₁ ∩ W₂ ∈ 𝓝 ((1 : InfiniteAdeleRing K), (1 : FiniteAdeleRing (𝓞 K) K)))
  -- The finite part contains a basic congruence neighbourhood of `1`.
  have hWf0 : (fun a ↦ 1 + a) ⁻¹' Wf ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) :=
    (continuous_const_add 1).continuousAt.preimage_mem_nhds (by rwa [add_zero])
  obtain ⟨I, n, hIn⟩ := FiniteAdeleRing.exists_finset_forall_mem_of_mem_nhds_zero hWf0
  -- The modulus: exponent `n v` at each place of `I`, and every real place.
  obtain ⟨𝔪, h𝔪f, h𝔪i⟩ : ∃ 𝔪 : Modulus K,
      𝔪.finitePart = ∏ v ∈ I, v.asIdeal ^ n v ∧ 𝔪.infinitePart = Finset.univ :=
    ⟨⟨∏ v ∈ I, v.asIdeal ^ n v, by
      rw [ne_eq, ← Ideal.zero_eq_bot]
      exact Finset.prod_ne_zero_iff.mpr fun v _ ↦
        pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot), Finset.univ⟩, rfl, rfl⟩
  refine ⟨𝔪, fun x hx ↦ ?_⟩
  -- The finite component of a congruence idele lies in `W₁ ∩ W₂`: it is integral at every finite
  -- place and congruent to `1` to level `n v` at each `v ∈ I`.
  have hfin : ∀ y ∈ ideleCongruenceSubgroup 𝔪,
      ((IdeleGroup.ofFiniteIdele (𝓞 K) K (IdeleGroup.toFiniteIdele (𝓞 K) K y) :
        IdeleGroup (𝓞 K) K) : 𝔸[K]) ∈ W₁ ∩ W₂ := by
    intro y hy
    rw [IdeleGroup.coe_ofFiniteIdele, IdeleGroup.coe_toFiniteIdele]
    refine hWprod ⟨mem_of_mem_nhds hWinf, ?_⟩
    have h := hIn ((y : 𝔸[K]).2 - 1)
      (fun v ↦ by
        rw [FiniteAdeleRing.sub_apply, FiniteAdeleRing.one_apply]
        exact sub_mem (ideleCongruenceSubgroup.snd_mem_adicCompletionIntegers hy v) (one_mem _))
      (fun v hv ↦ by
        have hdvd : v.asIdeal ^ n v ∣ 𝔪.finitePart := h𝔪f ▸ Finset.dvd_prod_of_mem _ hv
        rw [FiniteAdeleRing.sub_apply, FiniteAdeleRing.one_apply]
        exact ideleCongruenceSubgroup.valued_snd_sub_one_le_of_pow_dvd hy hdvd)
    rwa [Set.mem_preimage, add_sub_cancel] at h
  -- Decompose `x` into its archimedean components, which lie in `V` by connectedness, and its
  -- finite component, which lies in `V` by the choice of `W₁` and `W₂`.
  rw [← IdeleGroup.prod_ofCompletion_mul_ofFiniteIdele x]
  refine V.mul_mem (V.prod_mem fun w _ ↦ ofCompletion_mem_of_isOpen hV w _ fun hw ↦ ?_) ?_
  · exact ideleCongruenceSubgroup.extensionEmbeddingOfIsReal_pos hx (w := ⟨w, hw⟩)
      (h𝔪i ▸ Finset.mem_univ _)
  · refine hW _ (hfin x hx).1 ?_
    rw [← map_inv, ← map_inv]
    exact (hfin x⁻¹ ((ideleCongruenceSubgroup 𝔪).inv_mem hx)).2

/-- **A subgroup of the idele group is open exactly when it contains an idele congruence
subgroup.** -/
theorem isOpen_iff_exists_ideleCongruenceSubgroup_le (V : Subgroup (IdeleGroup (𝓞 K) K)) :
    IsOpen (V : Set (IdeleGroup (𝓞 K) K)) ↔ ∃ 𝔪 : Modulus K, ideleCongruenceSubgroup 𝔪 ≤ V :=
  ⟨exists_ideleCongruenceSubgroup_le_of_isOpen V,
    fun ⟨𝔪, h⟩ ↦ Subgroup.isOpen_mono h (isOpen_ideleCongruenceSubgroup 𝔪)⟩

/-- **Every open subgroup of the idele class group contains a ray subgroup.**  The ray subgroups
are therefore cofinal among the open subgroups of the idele class group, so that the finite
quotients `C_K / raySubgroup 𝔪` see every open subgroup; see `isOpen_iff_exists_raySubgroup_le` for
the resulting characterisation of openness. -/
theorem exists_raySubgroup_le_of_isOpen (U : Subgroup (IdeleClassGroup (𝓞 K) K))
    (hU : IsOpen (U : Set (IdeleClassGroup (𝓞 K) K))) :
    ∃ 𝔪 : Modulus K, raySubgroup 𝔪 ≤ U := by
  obtain ⟨𝔪, h𝔪⟩ := exists_ideleCongruenceSubgroup_le_of_isOpen
    (U.comap (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))) (by
      rw [Subgroup.coe_comap]
      exact hU.preimage QuotientGroup.continuous_mk)
  refine ⟨𝔪, fun c hc ↦ ?_⟩
  obtain ⟨x, hx, rfl⟩ := mem_raySubgroup_iff.mp hc
  exact h𝔪 hx

/-- **A subgroup of the idele class group is open exactly when it contains a ray subgroup.** -/
theorem isOpen_iff_exists_raySubgroup_le (U : Subgroup (IdeleClassGroup (𝓞 K) K)) :
    IsOpen (U : Set (IdeleClassGroup (𝓞 K) K)) ↔ ∃ 𝔪 : Modulus K, raySubgroup 𝔪 ≤ U :=
  ⟨exists_raySubgroup_le_of_isOpen U, fun ⟨𝔪, h⟩ ↦ Subgroup.isOpen_mono h (isOpen_raySubgroup 𝔪)⟩

end TauCeti.GlobalNumberFields
