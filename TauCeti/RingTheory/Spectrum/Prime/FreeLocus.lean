/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Flat.Localization
public import TauCeti.LinearAlgebra.FreeModule.Filtration

import Mathlib.RingTheory.Flat.Rank
import TauCeti.RingTheory.Flat.Pi
import TauCeti.RingTheory.Ideal.Pure

/-!
# The free locus over a reduced ring, and of a filtered module

Every module over a reduced ring is free at each minimal prime. For a finitely presented
module, Mathlib's openness of the free locus therefore gives an open neighbourhood of the
minimal primes where it is locally free.

A module with an exhaustive increasing filtration is free at every prime where all the
subquotients of the filtration are free. No finiteness is assumed, so this applies to modules
that are not finitely generated over the base, as in the proof of generic freeness in
`TauCeti.RingTheory.Spectrum.Prime.GenericFreeness`.

The rank of `R^k` at every prime is `k`, with no nontriviality hypothesis on `R`: a ring with a
prime ideal is nontrivial.
Every locus where the rank of a finitely presented flat module `M` lies in a given set is the
basic open set of an idempotent. In particular its support is the basic open set of an idempotent
`e`, and `M × R ⧸ (e)` has positive rank at every prime. If the rank of `M` is at most `n`, adding
`n` factors `R ⧸ (1 - e j)` of rank `0` or `1` pads `M` to constant rank `n`. The rank of a base
change of a finite flat module is constant when the base change sees the elements cutting out the
rank loci uniformly.
At a maximal ideal `P`, the rank of a finite flat module is the dimension of its reduction modulo
`P`, the form in which Mathlib's freeness criterion over semilocal rings,
`Module.free_of_flat_of_finrank_eq`, takes its hypothesis.

## Main declarations

* `Module.mem_freeLocus_of_mem_minimalPrimes`: over a reduced ring, every module is free at the
  minimal primes.
* `Module.iInter_freeLocus_subquotient_subset_freeLocus`: a filtered module is free wherever all
  subquotients of the filtration are.
* `Module.rankAtStalk_fin_fun`: the free module `R^k` has rank `k` at every prime.
* `Module.exists_isIdempotentElem_basicOpen_eq_rankAtStalk_preimage`: the locus where the rank of
  a finitely presented flat module lies in a given set is the basic open set of an idempotent.
* `Module.exists_isIdempotentElem_basicOpen_eq_support`: the support of a finitely presented flat
  module is the basic open set of an idempotent.
* `Module.rankAtStalk_quotient_span_one_sub`: for an idempotent `e`, `R ⧸ (1 - e)` has rank `1`
  on the basic open set of `e` and rank `0` off it.
* `Module.exists_rankAtStalk_prod_quotient_eq_max`: adding the complement of the support of a
  finitely presented flat module gives a module of positive rank at every prime.
* `Module.exists_rankAtStalk_prod_pi_quotient_eq`: a finitely presented flat module of rank at
  most `n` is a direct factor of a module of constant rank `n`.
* `Module.finrank_quotient_tensorProduct_eq_rankAtStalk`: the rank of a finite flat module at a
  maximal ideal `P` is the dimension of its reduction modulo `P`.
* `TauCeti.Module.exists_rankAtStalk_tensorProduct_eq`: a finite flat module whose rank is
  constant on the primes under a base change acquires constant rank after that base change.

## References

* The Stacks Project, Tags 051R and 051Z, for generic freeness.
-/

public section

namespace Module

section Reduced

variable {R : Type*} (M : Type*) [CommRing R] [IsReduced R] [AddCommGroup M] [Module R M]

/-- Over a reduced ring, every module is free at each minimal prime, where the localization of
the ring is a field. -/
theorem mem_freeLocus_of_mem_minimalPrimes {p : Ideal R} (hp : p ∈ minimalPrimes R) :
    ⟨p, hp.1.1⟩ ∈ freeLocus R M := by
  have := hp.1.1
  have : Ring.KrullDimLE 0 (Localization.AtPrime p) := .of_isLocalization p hp _
  let : Field (Localization.AtPrime p) := Ring.KrullDimLE.isField_of_isReduced.toField
  exact Module.Free.of_divisionRing _ _

variable (R) [Nontrivial R]

/-- A module over a nonzero reduced ring has nonempty free locus. -/
theorem freeLocus_nonempty : (freeLocus R M).Nonempty := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (R := R) (I := ⊥) bot_ne_top
  exact ⟨_, mem_freeLocus_of_mem_minimalPrimes M hp⟩

end Reduced

section Filtration

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A module is free at every prime at which all subquotients `N (j + 1) ⧸ N j` of an exhaustive
increasing filtration `⊥ = N 0 ≤ N 1 ≤ ⋯` are free.

No finiteness is assumed, so this applies to filtrations of modules that are not finitely
generated over the base ring. -/
theorem iInter_freeLocus_subquotient_subset_freeLocus (N : ℕ → Submodule R M)
    (hN : Monotone N) (h0 : N 0 = ⊥) (htop : ⨆ j, N j = ⊤) :
    ⋂ j, freeLocus R (N (j + 1) ⧸ (N j).submoduleOf (N (j + 1))) ⊆ freeLocus R M := by
  intro p hp
  rw [Set.mem_iInter] at hp
  let S := p.asIdeal.primeCompl
  let Rp := Localization.AtPrime p.asIdeal
  let L : ℕ → Submodule Rp (LocalizedModule S M) := fun j ↦ (N j).localized S
  have hL : Monotone L := fun _ _ hij ↦
    (Submodule.localized'gi Rp S (LocalizedModule.mkLinearMap S M)).gc.monotone_l (hN hij)
  have hL0 : L 0 = ⊥ := by simp [L, h0]
  refine Module.Free.of_filtration L hL (by rw [hL0]; infer_instance)
    (by simp only [L]; rw [← Submodule.localized'_iSup, htop, Submodule.localized'_top])
    fun j ↦ ?_
  -- Localize the subquotient through the localization of `N (j + 1)`.
  let g := (N (j + 1)).toLocalized' Rp S (LocalizedModule.mkLinearMap S M)
  let W := (N j).submoduleOf (N (j + 1))
  have hcoe (m : N (j + 1)) (s : S) :
      ((IsLocalizedModule.mk' g m s : L (j + 1)) : LocalizedModule S M) =
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) (m : M) s := by
    rw [eq_comm, IsLocalizedModule.mk'_eq_iff, ← Submodule.coe_smul_of_tower,
      IsLocalizedModule.mk'_cancel', Submodule.toLocalized'_apply_coe]
  have heq : W.localized' Rp S g = (L j).submoduleOf (L (j + 1)) := by
    ext x
    rw [Submodule.mem_localized']
    constructor
    · rintro ⟨m, hm, s, rfl⟩
      exact ⟨m, hm, s, (hcoe m s).symm⟩
    · rintro ⟨m, hm, s, hx⟩
      exact ⟨⟨m, hN j.le_succ hm⟩, hm, s, Subtype.ext ((hcoe _ s).trans hx)⟩
  have hfree : Module.Free Rp (L (j + 1) ⧸ W.localized' Rp S g) :=
    (mem_freeLocus_of_isLocalization p Rp _ (W.toLocalizedQuotient' Rp S g)).mp (hp j)
  exact Module.Free.of_equiv (Submodule.quotEquivOfEq _ _ heq)

end Filtration

/-- The free module `R^k` has rank `k` at every prime of `R`. -/
theorem rankAtStalk_fin_fun {R : Type*} [CommRing R] (k : ℕ) (p : PrimeSpectrum R) :
    rankAtStalk (R := R) (Fin k → R) p = k := by
  have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨p⟩
  simp

/-- The locus where the rank of a finitely presented flat module lies in a given set of ranks is
cut out by an idempotent: it is a preimage under the locally constant rank function, hence
clopen. -/
theorem exists_isIdempotentElem_basicOpen_eq_rankAtStalk_preimage {R : Type*} (M : Type*)
    [CommRing R] [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M]
    (s : Set ℕ) : ∃ e : R, IsIdempotentElem e ∧
      (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) = rankAtStalk (R := R) M ⁻¹' s := by
  have hloc := isLocallyConstant_rankAtStalk (R := R) (M := M)
  exact (PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    ⟨isOpen_compl_iff.mp (hloc sᶜ), hloc s⟩).imp fun e h ↦ ⟨h.1, h.2.symm⟩

/-- The support of a finitely presented flat module is cut out by an idempotent: it is the locus
where the locally constant rank function is positive, hence clopen. -/
theorem exists_isIdempotentElem_basicOpen_eq_support {R : Type*} (M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M] :
    ∃ e : R, IsIdempotentElem e ∧
      (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) = Module.support R M := by
  obtain ⟨e, he, hU⟩ := exists_isIdempotentElem_basicOpen_eq_rankAtStalk_preimage (R := R) M
    {n | 0 < n}
  exact ⟨e, he, hU.trans (Set.ext fun p ↦ rankAtStalk_pos_iff_mem_support p)⟩

open scoped Classical in
/-- For an idempotent `e`, the quotient `R ⧸ (1 - e)`, the localization away from `e`, has rank `1`
at the primes in the basic open set of `e` and rank `0` at the others. -/
theorem rankAtStalk_quotient_span_one_sub {R : Type*} [CommRing R] {e : R}
    (he : IsIdempotentElem e) (p : PrimeSpectrum R) :
    rankAtStalk (R := R) (R ⧸ Ideal.span {1 - e}) p = if e ∈ p.asIdeal then 0 else 1 := by
  have := Flat.quotient_span_singleton_of_isIdempotentElem he.one_sub
  have h₁ : rankAtStalk (R := R) (R ⧸ Ideal.span {1 - e}) p ≤ 1 :=
    rankAtStalk_le_one_iff_surjective.mpr Ideal.Quotient.mk_surjective p
  have h₀ : 0 < rankAtStalk (R := R) (R ⧸ Ideal.span {1 - e}) p ↔ e ∉ p.asIdeal := by
    -- `R ⧸ (1 - e)` sees exactly the primes of `V(1 - e) = D(e)`.
    simp [PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap,
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      ← PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]
  split_ifs with hp
  · exact Nat.eq_zero_of_not_pos (h₀.not.mpr (not_not.mpr hp))
  · have := h₀.mpr hp
    omega

/-- **Padding to constant rank.** A finitely presented flat module `M` of rank at most `n` is a
direct factor of a module of constant rank `n`: for suitable idempotents `e j`, `j < n`, the module
`M × ∏_{j < n} R ⧸ (1 - e j)` has rank `n` at every prime. -/
theorem exists_rankAtStalk_prod_pi_quotient_eq {R : Type*} (M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M] {n : ℕ}
    (hn : ∀ p : PrimeSpectrum R, rankAtStalk (R := R) M p ≤ n) :
    ∃ e : Fin n → R, (∀ j, IsIdempotentElem (e j)) ∧
      rankAtStalk (R := R) (M × Π j, R ⧸ Ideal.span {1 - e j}) = n := by
  choose e he hU using fun j : Fin n ↦
    exists_isIdempotentElem_basicOpen_eq_rankAtStalk_preimage (R := R) M {k | (j : ℕ) + k < n}
  refine ⟨e, he, funext fun p ↦ ?_⟩
  have (j : Fin n) := Flat.quotient_span_singleton_of_isIdempotentElem (he j).one_sub
  have hmem (j : Fin n) : e j ∉ p.asIdeal ↔ (j : ℕ) < n - rankAtStalk (R := R) M p := by
    rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, hU j, Set.mem_preimage,
      Set.mem_ofPred_eq]
    have := hn p
    omega
  have hsum : ∑ j : Fin n, rankAtStalk (R := R) (R ⧸ Ideal.span {1 - e j}) p =
      n - rankAtStalk (R := R) M p := by
    calc ∑ j : Fin n, rankAtStalk (R := R) (R ⧸ Ideal.span {1 - e j}) p
        = ∑ j : Fin n, if (j : ℕ) < n - rankAtStalk (R := R) M p then 1 else 0 :=
          Finset.sum_congr rfl fun j _ ↦ by
            have := hmem j
            rw [rankAtStalk_quotient_span_one_sub (he j)]
            split_ifs <;> simp_all
      _ = n - rankAtStalk (R := R) M p := by
          rw [Finset.sum_boole, Nat.cast_id, Fin.card_filter_val_lt]
          omega
  simp only [rankAtStalk_prod, rankAtStalk_pi, finsum_eq_sum_of_fintype, Pi.add_apply,
    Pi.natCast_apply, Nat.cast_id, hsum]
  have := hn p
  omega

/-- Adding the complement `R ⧸ (e)` of the support of a finitely presented flat module `M` gives
a module of rank `max 1 (rank M)` at every prime, hence one of positive rank everywhere. -/
theorem exists_rankAtStalk_prod_quotient_eq_max {R : Type*} (M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M] :
    ∃ e : R, IsIdempotentElem e ∧ ∀ p : PrimeSpectrum R,
      rankAtStalk (R := R) (M × R ⧸ Ideal.span {e}) p = max 1 (rankAtStalk (R := R) M p) := by
  obtain ⟨e, he, hsupp⟩ := exists_isIdempotentElem_basicOpen_eq_support (R := R) M
  have := Flat.quotient_span_singleton_of_isIdempotentElem he
  refine ⟨e, he, fun p ↦ ?_⟩
  -- `R ⧸ (e) = R ⧸ (1 - (1 - e))` has rank `1` off `D(e)` and rank `0` on it.
  have hU := rankAtStalk_quotient_span_one_sub he.one_sub p
  rw [sub_sub_cancel] at hU
  -- The support `D(e)` of `M` is `V(1 - e)`.
  have hM : 0 < rankAtStalk (R := R) M p ↔ 1 - e ∈ p.asIdeal := by
    rw [rankAtStalk_pos_iff_mem_support, ← hsupp,
      PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he, PrimeSpectrum.mem_zeroLocus,
      Set.singleton_subset_iff, SetLike.mem_coe]
  rw [rankAtStalk_prod, Pi.add_apply, hU]
  split_ifs with hp
  · have := hM.mpr hp
    omega
  · have := hM.not.mpr hp
    omega

open scoped TensorProduct in
/-- The rank of a finite flat module at a maximal ideal `P` is the dimension of its reduction
modulo `P` over the field `R ⧸ P`. -/
theorem finrank_quotient_tensorProduct_eq_rankAtStalk {R : Type*} (M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (P : MaximalSpectrum R) :
    finrank (R ⧸ P.asIdeal) ((R ⧸ P.asIdeal) ⊗[R] M) = rankAtStalk M P.toPrimeSpectrum := by
  let := Ideal.Quotient.field P.asIdeal
  -- the unique point of `Spec (R ⧸ P)` lies over `P`
  have hP : (⊤ : PrimeSpectrum (R ⧸ P.asIdeal)).comap (algebraMap R (R ⧸ P.asIdeal)) =
      P.toPrimeSpectrum := by
    ext1
    simp only [PrimeSpectrum.comap_asIdeal, IsLocalRing.PrimeSpectrum.asIdeal_top,
      IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, Ideal.Quotient.algebraMap_eq,
      Ideal.mk_ker]
    -- `P.toPrimeSpectrum` is `P.asIdeal` viewed as a prime ideal
    rfl
  rw [← hP, ← rankAtStalk_baseChange, rankAtStalk_eq_finrank_of_free, Pi.natCast_apply,
    Nat.cast_id]

end Module

namespace TauCeti.Module

open _root_.Module

open scoped TensorProduct in
/-- If a finite flat module `M` has the same rank at all primes of `R` lying under primes of `T'`,
then the base change of `M` to `T'` has constant rank. -/
theorem exists_rankAtStalk_tensorProduct_eq {R T' M : Type*} [CommRing R] [CommRing T']
    [Algebra R T'] [AddCommGroup M] [Module R M] [Module.Flat R M] [Module.Finite R M]
    (h : ∀ q q' : PrimeSpectrum T', rankAtStalk (R := R) M (q.comap (algebraMap R T')) =
      rankAtStalk (R := R) M (q'.comap (algebraMap R T'))) :
    ∃ m : ℕ, rankAtStalk (R := T') (T' ⊗[R] M) = m := by
  by_cases hne : Nonempty (PrimeSpectrum T')
  · obtain ⟨q₀⟩ := hne
    exact ⟨rankAtStalk M (q₀.comap (algebraMap R T')), funext fun q ↦ by
      rw [rankAtStalk_baseChange, Pi.natCast_apply, h q₀ q, Nat.cast_id]⟩
  · exact ⟨0, funext fun q ↦ (hne ⟨q⟩).elim⟩

end TauCeti.Module

namespace PrimeSpectrum

open Module

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If a base prime belongs to the free locus of an algebra, that algebra is flat
over the base after localizing at any prime above it. -/
theorem flat_localization_of_comap_mem_freeLocus (q : PrimeSpectrum S)
    (hq : q.comap (algebraMap R S) ∈ freeLocus R S) :
    Flat R (Localization.AtPrime q.asIdeal) := by
  let p := q.comap (algebraMap R S)
  let U := Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl
  let B := Localization U
  have hU : U ≤ q.asIdeal.primeCompl := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  let : Algebra B (Localization.AtPrime q.asIdeal) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ U q.asIdeal.primeCompl hU
  have : IsScalarTower S B (Localization.AtPrime q.asIdeal) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ U q.asIdeal.primeCompl hU
  have : IsScalarTower R B (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [IsScalarTower.algebraMap_eq R S B, ← RingHom.comp_assoc,
        ← IsScalarTower.algebraMap_eq S B (Localization.AtPrime q.asIdeal),
        ← IsScalarTower.algebraMap_eq R S (Localization.AtPrime q.asIdeal)])
  have : Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl S) := hq
  have : Flat R (Localization.AtPrime p.asIdeal) :=
    IsLocalization.flat _ p.asIdeal.primeCompl
  have : Flat R (LocalizedModule p.asIdeal.primeCompl S) :=
    Flat.trans R (Localization.AtPrime p.asIdeal) _
  have : Flat R B := Flat.of_linearEquiv
    (IsLocalizedModule.iso p.asIdeal.primeCompl (IsScalarTower.toAlgHom R S B).toLinearMap).symm
  have : IsLocalization (q.asIdeal.primeCompl.map (algebraMap S B))
      (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isLocalization_of_submonoid_le B _ U q.asIdeal.primeCompl hU
  have : Flat B (Localization.AtPrime q.asIdeal) :=
    IsLocalization.flat _ (q.asIdeal.primeCompl.map (algebraMap S B))
  exact Flat.trans R B _

end PrimeSpectrum

namespace Ideal

/-- A finitely presented flat module over a ring with connected spectrum vanishes if its fibre at
one maximal ideal vanishes, since its rank is locally constant. -/
theorem subsingleton_of_subsingleton_fiber {R M : Type*} [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M] (p : Ideal R) [p.IsMaximal]
    (h : Subsingleton (p.Fiber M)) : Subsingleton M := by
  have hrank_identity : Module.rankAtStalk (R := R) M
      ⟨p, (inferInstance : p.IsMaximal).isPrime⟩ = 0 := by
    rw [Module.rankAtStalk_eq]
    exact Module.finrank_zero_of_subsingleton
  have hrank : Module.rankAtStalk (R := R) M = 0 := by
    apply funext
    intro q
    simp only [Pi.zero_apply]
    calc
      Module.rankAtStalk M q =
          Module.rankAtStalk M ⟨p, (inferInstance : p.IsMaximal).isPrime⟩ :=
        IsLocallyConstant.apply_eq_of_preconnectedSpace
          (Module.isLocallyConstant_rankAtStalk (R := R) (M := M)) _ _
      _ = 0 := hrank_identity
  exact (Module.rankAtStalk_eq_zero_iff_subsingleton (R := R) (M := M)).mp hrank

end Ideal
