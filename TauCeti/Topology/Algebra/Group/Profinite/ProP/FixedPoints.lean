/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.QuotientAddGroup
public import TauCeti.GroupTheory.PGroup.Additive
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.GroupAction.Discrete

/-!
# Fixed points of pro-`p` groups on finite `p`-primary modules

Let `G` be a pro-`p` group acting continuously on a finite discrete additive group `M` in which
every element has `p`-power order. This file proves the fixed-point input to the
**trivial-filtration theorem** for such coefficients. If `M` is nontrivial then `G` fixes a
nonzero element of `M`, which may be taken of order `p`, so `M` contains a copy of `𝔽_p` with
trivial action. Applied to the quotient of `M` by a `G`-stable subgroup `N ≠ ⊤`, this gives an
element `x ∉ N` with `p • x ∈ N` that is fixed modulo `N`. Iterating this relative form builds
the `G`-stable chain of subgroups from `⊥` to `⊤` with `𝔽_p`-factors and trivial action; the
iteration is carried out in `TauCeti.Topology.Algebra.Group.Profinite.ProP.Filtration`.

These statements are the dévissage input for the cohomology of pro-`p` groups: a property of
finite discrete `p`-primary coefficient modules that holds for `𝔽_p` with trivial action and is
stable under extensions, such as the vanishing of a cohomological functor in a fixed degree,
holds for every such module.

The finite case, a `p`-group acting on a nonzero finite `p`-group fixes a nonzero element, is
Mathlib's `IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point`; this file extends it to
pro-`p` groups. The order computations for `p`-primary additive groups are in
`TauCeti.GroupTheory.PGroup.Additive`, and the induced action on the quotient by a `G`-stable
subgroup, `AddSubgroup.quotientDistribMulAction`, is in
`TauCeti.Algebra.GroupAction.QuotientAddGroup`.

## Main results

* `TauCeti.exists_ne_zero_invariant_of_isProP`: a pro-`p` group acting continuously on a
  nontrivial finite discrete `p`-primary additive group fixes a nonzero element.
* `TauCeti.exists_ne_zero_nsmul_eq_zero_invariant_of_isProP`: the fixed element may be taken of
  order `p`; `TauCeti.exists_addSubgroup_natCard_eq_invariant_of_isProP` packages it as a
  `G`-stable subgroup of order `p` with trivial action.
* `TauCeti.exists_notMem_nsmul_mem_smul_sub_mem_of_isProP`: the relative form, a fixed element
  of order `p` modulo a `G`-stable subgroup `N ≠ ⊤`.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.1.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 7.7.
-/

public section

namespace TauCeti

universe u v

variable {p : ℕ} [hp : Fact p.Prime]

section FixedPoints

variable {G : Type u} [Group G] [TopologicalSpace G]
  {M : Type v} [AddGroup M] [DistribMulAction G M] [Finite M]

/-- **Nonzero fixed points, open-kernel form.** A pro-`p` group acting on a nontrivial finite
`p`-primary additive group `M` with open kernel fixes a nonzero element. This form asks for no
topology on `M`, only that the kernel of the action be open in `G`, and so applies to quotients
`M ⧸ N` by `G`-stable subgroups. -/
theorem exists_ne_zero_invariant_of_isProP_of_isOpen_ker (hG : IsProP p G) [Nontrivial M]
    (hK : IsOpen ((MulAction.toPermHom G M).ker : Set G))
    (htors : ∀ m : M, ∃ k : ℕ, p ^ k • m = 0) : ∃ m : M, m ≠ 0 ∧ ∀ g : G, g • m = m := by
  -- the action factors through the finite `p`-group `G ⧸ K`, `K` the open kernel of the action
  let K : OpenNormalSubgroup G :=
    { toOpenSubgroup := { toSubgroup := (MulAction.toPermHom G M).ker, isOpen' := hK }
      isNormal' := (MulAction.toPermHom G M).normal_ker }
  have hQ : IsPGroup p (MulAction.toPermHom G M).range :=
    (isProP_iff.mp hG K).of_equiv (QuotientGroup.quotientKerEquivRange _)
  have h0 : (0 : M) ∈ MulAction.fixedPoints (MulAction.toPermHom G M).range M := by
    rintro ⟨_, g, rfl⟩
    simp [Subgroup.smul_def, Equiv.Perm.smul_def]
  obtain ⟨m, hm, hne⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point M
    (prime_dvd_natCard_of_forall_exists_nsmul_eq_zero htors) h0
  refine ⟨m, hne.symm, fun g ↦ ?_⟩
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hm ⟨MulAction.toPermHom G M g, g, rfl⟩

/-- **Fixed points of order `p`, open-kernel form.** The nonzero fixed element can be taken to
have order `p`. -/
theorem exists_ne_zero_nsmul_eq_zero_invariant_of_isProP_of_isOpen_ker (hG : IsProP p G)
    [Nontrivial M] (hK : IsOpen ((MulAction.toPermHom G M).ker : Set G))
    (htors : ∀ m : M, ∃ k : ℕ, p ^ k • m = 0) :
    ∃ m : M, m ≠ 0 ∧ p • m = 0 ∧ ∀ g : G, g • m = m := by
  obtain ⟨m, hm0, hm⟩ := exists_ne_zero_invariant_of_isProP_of_isOpen_ker hG hK htors
  obtain ⟨k, hk⟩ := htors m
  obtain ⟨n, hn0, hn⟩ := exists_nsmul_pow_ne_zero_nsmul_nsmul_pow_eq_zero hm0 hk
  exact ⟨p ^ n • m, hn0, hn, fun g ↦ by rw [smul_comm, hm g]⟩

variable [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- **The trivial-filtration theorem, first form.** A pro-`p` group acting continuously on a
nontrivial finite discrete `p`-primary additive group fixes a nonzero element. -/
theorem exists_ne_zero_invariant_of_isProP (hG : IsProP p G) [Nontrivial M]
    (htors : ∀ m : M, ∃ k : ℕ, p ^ k • m = 0) : ∃ m : M, m ≠ 0 ∧ ∀ g : G, g • m = m :=
  exists_ne_zero_invariant_of_isProP_of_isOpen_ker hG (isOpen_toPermHom_ker G M) htors

/-- A pro-`p` group acting continuously on a nontrivial finite discrete `p`-primary additive
group fixes a nonzero element of order `p`. -/
theorem exists_ne_zero_nsmul_eq_zero_invariant_of_isProP (hG : IsProP p G) [Nontrivial M]
    (htors : ∀ m : M, ∃ k : ℕ, p ^ k • m = 0) :
    ∃ m : M, m ≠ 0 ∧ p • m = 0 ∧ ∀ g : G, g • m = m :=
  exists_ne_zero_nsmul_eq_zero_invariant_of_isProP_of_isOpen_ker hG
    (isOpen_toPermHom_ker G M) htors

/-- A nontrivial finite discrete `p`-primary additive group with a continuous action of a
pro-`p` group contains a `G`-stable subgroup of order `p` on which `G` acts trivially: a copy of
`𝔽_p` with trivial action. -/
theorem exists_addSubgroup_natCard_eq_invariant_of_isProP (hG : IsProP p G) [Nontrivial M]
    (htors : ∀ m : M, ∃ k : ℕ, p ^ k • m = 0) :
    ∃ N : AddSubgroup M, Nat.card N = p ∧ ∀ g : G, ∀ x ∈ N, g • x = x := by
  obtain ⟨m, hm0, hpm, hm⟩ := exists_ne_zero_nsmul_eq_zero_invariant_of_isProP hG htors
  refine ⟨AddSubgroup.zmultiples m, ?_, fun g x hx ↦ ?_⟩
  · rw [Nat.card_zmultiples, addOrderOf_eq_prime hpm hm0]
  · obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [smul_comm, hm g]

end FixedPoints

section Quotient

variable {G : Type u} [Group G] [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [Finite M]

/-- **The trivial-filtration theorem, relative form.** For a `G`-stable subgroup `N ≠ ⊤` of a
finite discrete `p`-primary additive group `M` with a continuous action of a pro-`p` group `G`,
there is `x ∉ N` with `p • x ∈ N` whose class modulo `N` is fixed by `G`: the quotient `M ⧸ N`,
with the induced action `AddSubgroup.quotientDistribMulAction`, contains a copy of `𝔽_p` with
trivial action. -/
theorem exists_notMem_nsmul_mem_smul_sub_mem_of_isProP (hG : IsProP p G)
    (htors : ∀ m : M, ∃ k : ℕ, p ^ k • m = 0) {N : AddSubgroup M}
    (hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N) (hN' : N ≠ ⊤) :
    ∃ x : M, x ∉ N ∧ p • x ∈ N ∧ ∀ g : G, g • x - x ∈ N := by
  let _ := N.quotientDistribMulAction hN
  -- the stabilizer of a class is the preimage of the open set `N`, so the kernel is open
  have hK : IsOpen ((MulAction.toPermHom G (M ⧸ N)).ker : Set G) := by
    rw [toPermHom_ker_eq_iInf_stabilizer, Subgroup.coe_iInf]
    refine isOpen_iInter_of_finite fun y ↦ ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    have : (MulAction.stabilizer G (x : M ⧸ N) : Set G) = (fun g : G ↦ g • x - x) ⁻¹' N := by
      ext g
      simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage,
        AddSubgroup.quotientDistribMulAction_smul_mk, QuotientAddGroup.eq_iff_sub_mem]
    rw [this]
    exact (isOpen_discrete _).preimage
      ((continuous_of_discreteTopology (f := fun m : M ↦ m - x)).comp
        (continuous_id.smul continuous_const))
  have : Nontrivial (M ⧸ N) := QuotientAddGroup.nontrivial_iff.mpr hN'
  have htors' : ∀ y : M ⧸ N, ∃ k : ℕ, p ^ k • y = 0 := fun y ↦ by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨k, hk⟩ := htors x
    exact ⟨k, by rw [← QuotientAddGroup.mk_nsmul, hk, QuotientAddGroup.mk_zero]⟩
  obtain ⟨y, hy0, hpy, hy⟩ :=
    exists_ne_zero_nsmul_eq_zero_invariant_of_isProP_of_isOpen_ker hG hK htors'
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  refine ⟨x, fun hx ↦ hy0 ((QuotientAddGroup.eq_zero_iff x).mpr hx), ?_, fun g ↦ ?_⟩
  · rwa [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at hpy
  · have := hy g
    rwa [AddSubgroup.quotientDistribMulAction_smul_mk, QuotientAddGroup.eq_iff_sub_mem] at this

end Quotient

end TauCeti
