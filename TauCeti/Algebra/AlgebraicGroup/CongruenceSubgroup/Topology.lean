/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Compact
public import TauCeti.Algebra.AlgebraicGroup.CongruenceSubgroup.Basic
public import TauCeti.Topology.Algebra.PointTopology.Basic
public import TauCeti.Topology.Algebra.Ring.Compact

/-!
# Congruence subgroups are open and form a neighbourhood basis

For a Hopf algebra `H` of finite type over `k` and a topological `k`-algebra `R`, the group of
points `WithConv (H →ₐ[k] R)` carries the point topology, the coarsest topology making every
evaluation continuous. Membership in a congruence subgroup is a congruence condition on the values
of a point at finitely many generators of `H`, so the congruence subgroup of an open level is
open. Over a compact Hausdorff noetherian local ring, such as the valuation ring `O` of a
nonarchimedean local field, every power of the maximal ideal is open, so all the congruence
subgroups `𝒢(O)ₙ` of an affine group `𝒢` of finite type over `O` are open in `𝒢(O)`.

Conversely, a neighbourhood of the identity constrains only finitely many values of a point, and
a point of the congruence subgroup of level `J` agrees with the identity modulo `J` at every
element of `H`. So when ideals `J i` form a basis of neighbourhoods of `0` in `R`, the congruence
subgroups of the levels `J i` form a basis of neighbourhoods of the identity. Since the topology of
a compact Hausdorff noetherian local ring is its `m`-adic topology
(`IsLocalRing.isAdic_maximalIdeal`), the subgroups `𝒢(O)ₙ` form a basis of neighbourhoods of the
identity in `𝒢(O)`.

## Main declarations

* `TauCeti.HopfAlgebra.isOpen_congruenceSubgroup`: the congruence subgroup of an open level is
  open when `H` is of finite type.
* `TauCeti.HopfAlgebra.isOpen_congruenceSubgroup_maximalIdeal_pow`: over a compact Hausdorff
  noetherian local ring, the congruence subgroups of the levels `m ^ n` are open.
* `TauCeti.HopfAlgebra.hasBasis_nhds_one_congruenceSubgroup`: congruence subgroups of the levels of
  an ideal basis of neighbourhoods of `0` form a basis of neighbourhoods of the identity, when `H`
  is of finite type; `hasBasis_nhds_one_congruenceSubgroup_pow` is the case of an `I`-adic
  topology.
* `TauCeti.HopfAlgebra.hasBasis_nhds_one_congruenceSubgroup_maximalIdeal_pow`: over a compact
  Hausdorff noetherian local ring, the congruence subgroups of the levels `m ^ n` form a basis of
  neighbourhoods of the identity.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1 and Ex. 2.3, pp. 2–3.
* V. Platonov, A. Rapinchuk, I. Rapinchuk, *Algebraic groups and number theory*, vol. 1,
  2nd ed. (2023), §3.1, p. 126.
-/

public section

open Coalgebra WithConv Topology

namespace TauCeti

namespace HopfAlgebra

variable {k H R : Type*} [CommSemiring k] [Semiring H] [_root_.HopfAlgebra k H]
  [CommRing R] [Algebra k R] [TopologicalSpace R]

/-- The congruence subgroup of an open level `I` is open in the point topology, when `H` is of
finite type over `k`. -/
theorem isOpen_congruenceSubgroup [ContinuousSub R] [Algebra.FiniteType k H] {I : Ideal R}
    (hI : IsOpen (I : Set R)) :
    IsOpen (congruenceSubgroup k H I : Set (WithConv (H →ₐ[k] R))) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := H)
  have hset : (congruenceSubgroup k H I : Set (WithConv (H →ₐ[k] R))) =
      ⋂ h ∈ (s : Set H), (fun x : WithConv (H →ₐ[k] R) ↦
        x.ofConv h - algebraMap k R (counit h)) ⁻¹' I := by
    ext x
    simp only [SetLike.mem_coe, mem_congruenceSubgroup_iff_of_adjoin_eq_top hs, Set.mem_iInter,
      Set.mem_preimage]
  rw [hset]
  exact s.finite_toSet.isOpen_biInter fun h _ ↦
    hI.preimage (((PointTopology.continuous_withConv_iff.1 continuous_id) h).sub continuous_const)

open scoped PointTopology in
/-- **Congruence subgroups form a neighbourhood basis of the identity.** If ideals `J i` of `R`
form a basis of neighbourhoods of `0`, then for `H` of finite type over `k` the congruence
subgroups of the levels `J i` form a basis of neighbourhoods of the identity point in the point
topology. -/
theorem hasBasis_nhds_one_congruenceSubgroup [IsTopologicalAddGroup R] [Algebra.FiniteType k H]
    {ι : Sort*} {p : ι → Prop} {J : ι → Ideal R}
    (hJ : (𝓝 (0 : R)).HasBasis p fun i ↦ (J i : Set R)) :
    (𝓝 (1 : WithConv (H →ₐ[k] R))).HasBasis p
      fun i ↦ (congruenceSubgroup k H (J i) : Set (WithConv (H →ₐ[k] R))) := by
  refine ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨i, _, hiU⟩ ↦ Filter.mem_of_superset ?_ hiU⟩⟩
  · -- The point topology is induced from `H → R`, so `U` contains a box around the identity
    -- constrained at finitely many coordinates `h ∈ s`; a level `J i` small enough at each of
    -- these coordinates gives a congruence subgroup inside the box.
    have hind : Topology.IsInducing fun x : WithConv (H →ₐ[k] R) ↦ ⇑x.ofConv :=
      PointTopology.isEmbedding_coeFn.isInducing.comp
        PointTopology.isHomeomorph_ofConv.isEmbedding.isInducing
    obtain ⟨W, hW, hWU⟩ := (hind.nhds_eq_comap 1 ▸ hU : U ∈ Filter.comap _ _)
    rw [nhds_pi, Filter.mem_pi] at hW
    obtain ⟨s, hs, t, ht, hst⟩ := hW
    have hshift : ∀ h, (fun r ↦ r + algebraMap k R (counit h)) ⁻¹' t h ∈ 𝓝 (0 : R) := fun h ↦
      (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using ht h)
    obtain ⟨i, hi, hiJ⟩ := hJ.mem_iff.mp ((Filter.biInter_mem hs).2 fun h _ ↦ hshift h)
    refine ⟨i, hi, fun x hx ↦ hWU (hst fun h hh ↦ ?_)⟩
    simpa using Set.mem_iInter₂.mp (hiJ (mem_congruenceSubgroup_iff.1 hx h)) h hh
  · -- Membership is a congruence on finitely many generators `h ∈ s`, each an open condition
    -- around the identity.
    obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := H)
    have hmem : ∀ h, (fun x : WithConv (H →ₐ[k] R) ↦ x.ofConv h - algebraMap k R (counit h)) ⁻¹'
        (J i : Set R) ∈ 𝓝 1 := fun h ↦
      (((PointTopology.continuous_withConv_iff.1 continuous_id) h).sub
        continuous_const).continuousAt.preimage_mem_nhds (by simpa using hJ.mem_of_mem ‹_›)
    refine Filter.mem_of_superset ((Filter.biInter_finset_mem s).2 fun h _ ↦ hmem h) ?_
    intro x hx
    exact (mem_congruenceSubgroup_iff_of_adjoin_eq_top hs).2 fun h hh ↦ Set.mem_iInter₂.mp hx h hh

/-- For an `I`-adic topology on `R` and `H` of finite type over `k`, the congruence subgroups of
the levels `I ^ n` form a basis of neighbourhoods of the identity point. -/
theorem hasBasis_nhds_one_congruenceSubgroup_pow [IsTopologicalRing R] [Algebra.FiniteType k H]
    {I : Ideal R} (hI : IsAdic I) :
    (𝓝 (1 : WithConv (H →ₐ[k] R))).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (congruenceSubgroup k H (I ^ n) : Set (WithConv (H →ₐ[k] R))) :=
  hasBasis_nhds_one_congruenceSubgroup hI.hasBasis_nhds_zero

variable (k H R) in
/-- Over a compact Hausdorff noetherian local ring `R`, for instance the valuation ring of a
nonarchimedean local field, the congruence subgroup of level `m ^ n` of an affine group of finite
type is open in the point topology. -/
theorem isOpen_congruenceSubgroup_maximalIdeal_pow [IsTopologicalRing R] [CompactSpace R]
    [T2Space R] [IsNoetherianRing R] [IsLocalRing R] [Algebra.FiniteType k H] (n : ℕ) :
    IsOpen (congruenceSubgroup k H (IsLocalRing.maximalIdeal R ^ n) :
      Set (WithConv (H →ₐ[k] R))) :=
  isOpen_congruenceSubgroup (IsLocalRing.isOpen_maximalIdeal_pow R n)

variable (k H R) in
/-- Over a compact Hausdorff noetherian local ring `R`, for instance the valuation ring `O` of a
nonarchimedean local field, the congruence subgroups `𝒢(O)ₙ` of the levels `m ^ n` of an affine
group of finite type form a basis of neighbourhoods of the identity in the point topology. -/
theorem hasBasis_nhds_one_congruenceSubgroup_maximalIdeal_pow [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] [IsNoetherianRing R] [IsLocalRing R] [Algebra.FiniteType k H] :
    (𝓝 (1 : WithConv (H →ₐ[k] R))).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (congruenceSubgroup k H (IsLocalRing.maximalIdeal R ^ n) :
        Set (WithConv (H →ₐ[k] R))) :=
  hasBasis_nhds_one_congruenceSubgroup_pow (IsLocalRing.isAdic_maximalIdeal R)

end HopfAlgebra

end TauCeti
