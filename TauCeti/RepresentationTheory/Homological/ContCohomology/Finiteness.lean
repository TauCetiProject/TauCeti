/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Index.Exact
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Devissage
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.AllDegrees

/-!
# Finiteness of continuous cohomology with finite coefficients, from an open normal subgroup

Let `G` be a profinite group, `V` an open normal subgroup of `G` and `N` a natural number. This
file reduces the finiteness of the continuous cohomology `Hⁱ(G, A)` of the finite discrete
`G`-modules `A` killed by `N` on which `V` acts trivially to the finiteness of `Hʲ(V, M)`, for
`0 < j ≤ i`, on the trivial `V`-modules `M` of prime order dividing `N`. Over a field this is the
step from an absolute Galois group to that of a finite Galois extension over which the
coefficients become constant and which contains the relevant roots of unity; this is how the
finiteness of the local Galois cohomology of a finite module is proved.

There are two steps.

* **Coinduction.** The unit `A ↪ Coind_V^G A` of coinduction embeds `A` into a finite module with
  `Hʲ(G, Coind_V^G A) ≅ Hʲ(V, A)` by Shapiro's lemma, and the cokernel `C` of the short exact
  sequence `TauCeti.ContCohomology.coindShortExact` is again a finite module killed by `N` on which
  `V` acts trivially, because `V` is normal
  (`TauCeti.DiscreteCoind.smul_eq_self_of_forall_smul_eq_self`).
  Exactness of `Hⁱ(G, C) → Hⁱ⁺¹(G, A) → Hⁱ⁺¹(G, Coind_V^G A)` then gives finiteness of
  `Hⁱ⁺¹(G, A)` by induction on the degree, starting from `H⁰(G, A) ⊆ A`
  (`TauCeti.ContCohomology.finite_continuousCohomology_zero`,
  `TauCeti.ContinuousCohomology.finite_continuousCohomology_of_isOpen_of_normal`).
* **Dévissage of trivial modules.** A finite trivial module killed by `N` is an iterated extension
  of trivial modules of prime order dividing `N`, by Cauchy's theorem and the dévissage induction
  principle `TauCeti.ContCohomology.finite_induction_of_exists_addSubgroup`; exactness of
  `Hʲ(V, P) → Hʲ(V, M) → Hʲ(V, M ⧸ P)` passes finiteness along each extension
  (`TauCeti.ContinuousCohomology.finite_continuousCohomology_of_forall_natCard_prime`).

## Main results

* `TauCeti.ContinuousCohomology.finite_continuousCohomology_of_forall_natCard_prime`: finiteness of
  `Hⁿ` on the trivial modules of prime order dividing `N` gives finiteness on every finite trivial
  module killed by `N`.
* `TauCeti.ContinuousCohomology.finite_continuousCohomology_of_isOpen_of_normal`: finiteness of
  `Hʲ(V, -)`, `0 < j ≤ i`, on the finite trivial modules killed by `N` gives finiteness of
  `Hⁱ(G, A)` for every finite discrete `A` killed by `N` on which `V` acts trivially.
* `TauCeti.ContinuousCohomology.finite_continuousCohomology_of_isOpen_of_normal_of_prime`: the
  same, with the trivial modules of prime order dividing `N` as test class.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. II, §5.2, proof of Proposition 14.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.4) for
  Shapiro's lemma and Ch. VII, §1 for the local finiteness theorem.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

open TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Dévissage of finite trivial coefficients.** Let `G` be a locally compact group, `n` a degree
and `N` a natural number. If `Hⁿ(G, A)` is finite for every discrete `G`-module `A` of prime order
dividing `N` on which `G` acts trivially, then `Hⁿ(G, M)` is finite for every finite discrete
`G`-module `M` killed by `N` on which `G` acts trivially. -/
theorem finite_continuousCohomology_of_forall_natCard_prime [LocallyCompactSpace G] {N n : ℕ}
    (h : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A] [Finite A], (Nat.card A).Prime →
      Nat.card A ∣ N → (∀ (g : G) (a : A), g • a = a) →
      Finite (continuousCohomology n (ofDiscreteModule ℤ G A)))
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M] (hN : ∀ m : M, N • m = 0)
    (htriv : ∀ (g : G) (m : M), g • m = m) :
    Finite (continuousCohomology n (ofDiscreteModule ℤ G M)) := by
  -- dévissage along subgroups of prime order dividing `N`, inside the trivial modules killed by `N`
  -- (elaborated before unifying with the goal, which otherwise unfolds `ofDiscreteModule`)
  refine (finite_induction_of_exists_addSubgroup
    (motive := fun M _ _ _ _ _ ↦ Finite (continuousCohomology n (ofDiscreteModule ℤ G M)))
    (fun M [AddCommGroup M] [DistribMulAction G M] ↦
      (∀ m : M, N • m = 0) ∧ ∀ (g : G) (m : M), g • m = m) (fun k ↦ k.Prime ∧ k ∣ N)
    (fun _ hk ↦ hk.1.one_lt) (fun _ _ _ _ _ _ f hf hM ↦ ⟨fun m ↦ ?_, fun g m ↦ ?_⟩)
    (fun M _ _ _ _ _ _ _ hM ↦ ?_) (fun M _ _ _ _ _ _ ↦ ?_)
    (fun A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S hA hAtriv _ _ hC ↦ ?_) M ⟨hN, htriv⟩ :)
  -- the class is closed under equivariant surjections
  · obtain ⟨m, rfl⟩ := hf m
    rw [← map_nsmul, hM.1, _root_.map_zero]
  · obtain ⟨m, rfl⟩ := hf m
    rw [← _root_.map_smul, hM.2]
  -- Cauchy's theorem: an element `x` of prime order `ℓ`, which divides `N`
  · obtain ⟨ℓ, hℓ, hℓM⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := M)).ne'
    have := Fact.mk hℓ
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' ℓ hℓM
    refine ⟨AddSubgroup.zmultiples x, ?_, fun g y _ ↦ hM.2 g y⟩
    rw [Nat.card_zmultiples, hx]
    exact ⟨hℓ, hx ▸ addOrderOf_dvd_of_nsmul_eq_zero (hM.1 x)⟩
  · have := subsingleton_continuousCohomology_ofDiscreteModule_of_subsingleton (R := ℤ) (G := G) M n
    exact Finite.of_subsingleton
  -- exactness in the middle of `Hⁿ(G, A) → Hⁿ(G, B) → Hⁿ(G, C)`, with finite outer terms
  · have := h A hA.1 hA.2 hAtriv
    exact (S.longExact_exact₂ n).finite

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Finiteness through an open normal subgroup.** Let `G` be a profinite group, `V` an open
normal subgroup, `N` a natural number and `i` a degree. Suppose that for every `0 < j ≤ i`,
`Hʲ(V, M)` is finite for every finite discrete `V`-module `M` killed by `N` on which `V` acts
trivially. Then `Hⁱ(G, A)` is finite for every finite discrete `G`-module `A` killed by `N` on which
`V` acts trivially. Degree zero needs no hypothesis, `H⁰(G, A)` being a subgroup of `A`. -/
theorem finite_continuousCohomology_of_isOpen_of_normal (V : Subgroup G) [V.Normal]
    (hV : IsOpen (V : Set G)) {N : ℕ} (i : ℕ)
    (h : ∀ j, 0 < j → j ≤ i → ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M]
      [DiscreteTopology M] [DistribMulAction V M] [ContinuousSMul V M] [Finite M],
      (∀ m : M, N • m = 0) → (∀ (v : V) (m : M), v • m = m) →
      Finite (continuousCohomology j (ofDiscreteModule ℤ V M)))
    (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A] (hN : ∀ a : A, N • a = 0)
    (htriv : ∀ v ∈ V, ∀ a : A, v • a = a) :
    Finite (continuousCohomology i (ofDiscreteModule ℤ G A)) := by
  have : Finite (G ⧸ V) := V.quotient_finite_of_isOpen hV
  have : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  induction i generalizing A with
  | zero => exact finite_continuousCohomology_zero A
  | succ i ih =>
  -- the short exact sequence `0 → A → Coind_V^G A → C → 0` of the unit of coinduction
  set S := coindShortExact G V A
  -- `C` is killed by `N`, and `V` acts trivially on it, because it acts trivially on
  -- `Coind_V^G A` by normality
  have : Finite (continuousCohomology i (ofDiscreteModule ℤ G (CoindQuotient G V A))) := by
    refine ih (fun j hj₀ hj ↦ h j hj₀ (hj.trans i.le_succ)) (CoindQuotient G V A)
      (S.nsmul_eq_zero_right (DiscreteCoind.nsmul_eq_zero hN)) (fun v hv c ↦ ?_)
    induction c using CoindQuotient.induction_on with
    | h f => rw [← CoindQuotient.mk_smul,
        DiscreteCoind.smul_eq_self_of_forall_smul_eq_self (fun u a ↦ htriv u u.2 a) hv f]
  -- Shapiro's lemma: `Hⁱ⁺¹(G, Coind_V^G A) ≅ Hⁱ⁺¹(V, A)`
  have := h (i + 1) i.succ_pos le_rfl A hN fun v a ↦ htriv v v.2 a
  have : Finite (continuousCohomology (i + 1) (ofDiscreteModule ℤ G (DiscreteCoind G V A))) :=
    Finite.of_equiv _
      (shapiroIso V (V.isClosed_of_isOpen hV) A (i + 1)).symm.toContinuousLinearEquiv.toEquiv
  exact (S.longExact_exact₁ i).finite

/-- **Finiteness through an open normal subgroup, prime test class.** Let `G` be a profinite
group, `V` an open normal subgroup, `N` a natural number and `i` a degree. Suppose that for every
`0 < j ≤ i`, `Hʲ(V, M)` is finite for every discrete `V`-module `M` of prime order dividing `N` on
which `V` acts trivially. Then `Hⁱ(G, A)` is finite for every finite discrete `G`-module `A` killed
by `N` on which `V` acts trivially. -/
theorem finite_continuousCohomology_of_isOpen_of_normal_of_prime (V : Subgroup G) [V.Normal]
    (hV : IsOpen (V : Set G)) {N : ℕ} (i : ℕ)
    (h : ∀ j, 0 < j → j ≤ i → ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M]
      [DiscreteTopology M] [DistribMulAction V M] [ContinuousSMul V M] [Finite M],
      (Nat.card M).Prime → Nat.card M ∣ N → (∀ (v : V) (m : M), v • m = m) →
      Finite (continuousCohomology j (ofDiscreteModule ℤ V M)))
    (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A] (hN : ∀ a : A, N • a = 0)
    (htriv : ∀ v ∈ V, ∀ a : A, v • a = a) :
    Finite (continuousCohomology i (ofDiscreteModule ℤ G A)) :=
  have : CompactSpace V := isCompact_iff_compactSpace.mp (V.isClosed_of_isOpen hV).isCompact
  finite_continuousCohomology_of_isOpen_of_normal V hV i
    (fun j hj₀ hj M _ _ _ _ _ _ hM hMtriv ↦
      finite_continuousCohomology_of_forall_natCard_prime (h j hj₀ hj) M hM hMtriv) A hN htriv

end TauCeti.ContinuousCohomology
