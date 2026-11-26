/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.DedekindDomain.Factorization
import TauCeti.Data.ZMod.Divisibility
import TauCeti.RingTheory.Norm.Congruence

/-!
# The absolute ideal norm under ring isomorphisms, prime factorizations, and congruences

Identifying two rings along an isomorphism identifies their ideals, and the absolute norm is
insensitive to that identification. In a Dedekind domain with finite quotients, the absolute
norm of a nonzero ideal stays nonzero when cast into characteristic zero. A proper ideal
contains no natural number prime to its absolute norm, and for any nonzero ideal of a Dedekind
domain its absolute norm factors as the product over all height-one primes of the residue
cardinality raised to the prime multiplicity. Over `ℤ` itself, the absolute norm of the ideal
`(n)` is `|n|`.

The cardinality of the quotient of a submodule `p` by a submodule `N` of `p` is the index of the
image of `N` in `p`, as additive subgroups of the ambient module.
A submodule with finite quotient has nonzero index, and the index of the image of a submodule
under an injective linear map is its index times the index of the range. Preimages under a
surjective linear map keep the index, so a linear equivalence matches the submodules of a given
index.

In a Dedekind domain that is free of finite rank over `ℤ`, congruent elements whose norms
have nonnegative product generate principal ideals with congruent absolute norms.

In a torsion-free module, the multiples of `a • s` have index `#(R ⧸ (a))` in the multiples of a
nonzero `s`, so the index `Submodule.cardQuot` is multiplicative along this chain.

## Main results

* `Submodule.cardQuot_eq_relIndex_map_subtype`: for a submodule `N` of a submodule `p`,
  `#(p ⧸ N)` is the index of the image of `N` in `p`.
* `Submodule.cardQuot_ne_zero`: a submodule with finite quotient has nonzero index.
* `Submodule.finite_quotient_of_cardQuot_ne_zero`: conversely, a submodule with nonzero index has
  finite quotient.
* `Submodule.cardQuot_map_of_injective`: for an injective linear map `f`,
  `#(N ⧸ f P) = #(M ⧸ P) * #(N ⧸ range f)`.
* `Submodule.cardQuot_comap_of_surjective`: preimages under a surjective linear map keep the
  index.
* `Submodule.subtypeCardQuotEquiv`: a linear equivalence matches the submodules of a given index,
  by images (`Submodule.coe_subtypeCardQuotEquiv_apply`) and preimages
  (`Submodule.coe_subtypeCardQuotEquiv_symm_apply`).
* `Ideal.absNorm_comap_of_ringEquiv`, `Ideal.absNorm_map_of_ringEquiv`: the absolute norm of an
  ideal is unchanged by transporting it along a ring isomorphism, in either direction.
* `Ideal.absNorm_map_of_ringEquiv_eq_natCard`: the absolute norm of an ideal transported from an
  arbitrary commutative ring is the cardinality of the original quotient.
* `Ideal.natCast_absNorm_ne_zero`, `IsDedekindDomain.HeightOneSpectrum.natCast_absNorm_ne_zero`:
  in a Dedekind domain with finite quotients, the absolute norm of a nonzero ideal, in particular
  of a height-one prime, stays nonzero when cast into characteristic zero.
* `Ideal.natCast_notMem_of_coprime_absNorm`: a natural number prime to the absolute norm of a
  proper ideal does not lie in it.
* `Ideal.finprod_pow_count_eq_absNorm`: for a nonzero ideal `J` of a Dedekind domain `R`, the
  absolute norm equals `∏ᶠ v, (#(R ⧸ v)) ^ count v J`.
* `Int.absNorm_span_singleton`, `Int.absNorm_le_natAbs_of_dvd_span_singleton`: the absolute norm
  of the ideal `(n)` of `ℤ` is `|n|`, and that of an ideal dividing `(n)`, for `n ≠ 0`, is at most
  `|n|`.
* `Ideal.natCast_absNorm_span_singleton_eq_of_sub_mem`: congruent elements whose norms have
  nonnegative product generate ideals with absolute norms congruent modulo `m`.
* `Submodule.cardQuot_span_singleton_smul`: `#(M ⧸ R • (a • s)) = #(R ⧸ (a)) * #(M ⧸ R • s)` for
  `s ≠ 0` in a torsion-free module `M`.
-/

public section

namespace Submodule

/-- The cardinality of the quotient of `p` by a submodule `N` of `p` is the index of the image of
`N` in `p`, as additive subgroups of the ambient module. -/
theorem cardQuot_eq_relIndex_map_subtype {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) (N : Submodule R p) :
    N.cardQuot = (N.map p.subtype).toAddSubgroup.relIndex p.toAddSubgroup := by
  have hp : (⊤ : AddSubgroup p).map (p.subtype : p →+ M) = p.toAddSubgroup := by
    rw [← AddMonoidHom.range_eq_map]
    ext x
    simp
  rw [cardQuot, ← AddSubgroup.relIndex_top_right, map_toAddSubgroup, ← hp,
    AddSubgroup.relIndex_map_map_of_injective _ _ p.injective_subtype]

/-- A submodule with finite quotient has nonzero index. -/
theorem cardQuot_ne_zero {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (S : Submodule R M) [Finite (M ⧸ S)] : S.cardQuot ≠ 0 := by
  rw [cardQuot_apply]
  exact Nat.card_pos.ne'

/-- A submodule with nonzero index has finite quotient. -/
theorem finite_quotient_of_cardQuot_ne_zero {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {S : Submodule R M} (hS : S.cardQuot ≠ 0) : Finite (M ⧸ S) :=
  Nat.finite_of_card_ne_zero (by rwa [← cardQuot_apply])

/-- **The index of an injective image**: for an injective linear map `f : M → N`, the index of
`f P` in `N` is the index of `P` in `M` times the index of the range of `f`. Both sides are `0`
when an index is infinite. -/
theorem cardQuot_map_of_injective {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {f : M →ₗ[R] N} (hf : Function.Injective f)
    (P : Submodule R M) : (P.map f).cardQuot = P.cardQuot * (LinearMap.range f).cardQuot := by
  rw [cardQuot, cardQuot, cardQuot, map_toAddSubgroup, LinearMap.range_toAddSubgroup]
  exact AddSubgroup.index_map_of_injective _ hf

/-- Pulling a submodule back along a surjective linear map preserves its index. Adapted from
`cardQuot_comap_of_surjective` in `src/New/Spanning/RemainingTerms/Discriminants.lean` of
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). -/
theorem cardQuot_comap_of_surjective {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {f : M →ₗ[R] N} (hf : Function.Surjective f)
    (P : Submodule R N) : (P.comap f).cardQuot = P.cardQuot :=
  P.toAddSubgroup.index_comap_of_surjective (f := f.toAddMonoidHom) hf

/-- A linear equivalence `M ≃ N` matches the submodules of `M` of index `n` with those of `N`,
by taking images. -/
noncomputable def subtypeCardQuotEquiv {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (n : ℕ) :
    {P : Submodule R M // P.cardQuot = n} ≃ {P : Submodule R N // P.cardQuot = n} :=
  (orderIsoMapComap e).toEquiv.subtypeEquiv fun P ↦ by
    rw [RelIso.coe_fn_toEquiv, orderIsoMapComap_apply, cardQuot_map_of_injective e.injective,
      LinearEquiv.range, cardQuot_top, mul_one]

@[simp]
theorem coe_subtypeCardQuotEquiv_apply {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (n : ℕ)
    (P : {P : Submodule R M // P.cardQuot = n}) :
    (subtypeCardQuotEquiv e n P : Submodule R N) = P.val.map (e : M →ₗ[R] N) :=
  by
  simp [subtypeCardQuotEquiv]

@[simp]
theorem coe_subtypeCardQuotEquiv_symm_apply {R M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (n : ℕ)
    (P : {P : Submodule R N // P.cardQuot = n}) :
    ((subtypeCardQuotEquiv e n).symm P : Submodule R M) = P.val.comap (e : M →ₗ[R] N) :=
  by
  simp [subtypeCardQuotEquiv]

end Submodule

namespace Ideal

variable {R R' : Type*} [CommRing R] [CommRing R'] [IsDedekindDomain R] [IsDedekindDomain R']

/-- The absolute norm is invariant under transporting an ideal backwards along an isomorphism of
Dedekind domains.  Use this to move a norm computation to whichever of two identified rings it is
easier to carry out in. -/
@[simp]
theorem absNorm_comap_of_ringEquiv (e : R ≃+* R') (I : Ideal R') :
    absNorm (Ideal.comap e I) = absNorm I := by
  obtain rfl | hI := eq_or_ne I ⊥
  · simp [Ideal.comap_bot_of_injective _ e.injective]
  have hI' : Ideal.comap e I ≠ ⊥ :=
    fun h ↦ hI (Ideal.eq_bot_of_comap_eq_bot' (f := e.toRingHom) e.surjective h)
  rw [absNorm_of_ne_bot hI', absNorm_of_ne_bot hI,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ e (Ideal.map_comap_eq_self_of_equiv e I).symm)

/-- The absolute norm is invariant under transporting an ideal forwards along an isomorphism of
Dedekind domains.  This is the form to use when the ideal is given on the source side. -/
@[simp]
theorem absNorm_map_of_ringEquiv (e : R ≃+* R') (I : Ideal R) :
    absNorm (I.map e) = absNorm I := by
  rw [← Ideal.comap_symm]
  exact absNorm_comap_of_ringEquiv e.symm I

/-- The absolute norm of an ideal transported along an isomorphism from an arbitrary commutative
ring `A` is the cardinality of the quotient of `A` by the original ideal. Use this to compute the
norm of an ideal in coordinates where the absolute norm itself is not available, for instance in a
concrete model of a ring of integers that is not known to be a Dedekind domain. -/
theorem absNorm_map_of_ringEquiv_eq_natCard {A : Type*} [CommRing A] [Infinite R']
    {F : Type*} [EquivLike F A R'] [RingEquivClass F A R'] (e : F) (I : Ideal A) :
    absNorm (I.map e) = Nat.card (A ⧸ I) := by
  rw [absNorm_eq_natCard]
  exact Nat.card_congr (Ideal.quotientEquiv I _ (RingEquivClass.toRingEquiv e) rfl).toEquiv.symm

/-- In a Dedekind domain with finite quotients, the absolute norm of a nonzero ideal stays
nonzero when cast into any `AddMonoidWithOne` of characteristic zero, such as `ℝ` or `ℂ`. -/
theorem natCast_absNorm_ne_zero [Ring.HasFiniteQuotients R] {α : Type*} [AddMonoidWithOne α]
    [CharZero α] {I : Ideal R} (hI : I ≠ ⊥) : (absNorm I : α) ≠ 0 :=
  Nat.cast_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr hI)

/-- A natural number prime to the absolute norm of a proper ideal `I` does not lie in `I`, since
`I` contains its norm (`Ideal.absNorm_mem`). -/
theorem natCast_notMem_of_coprime_absNorm {I : Ideal R} (hI : I ≠ ⊤) {a : ℕ}
    (ha : a.Coprime (absNorm I)) : (a : R) ∉ I := fun h ↦ hI <| by
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr ha).map (Int.castRingHom R)
  rw [eq_top_iff_one, ← huv]
  simpa using I.add_mem (I.mul_mem_left u h) (I.mul_mem_left v (absNorm_mem I))

open _root_.IsDedekindDomain in
/-- **Prime-factorization formula for the absolute norm of a nonzero ideal.** -/
theorem finprod_pow_count_eq_absNorm {J : Ideal R} (hJ : J ≠ ⊥) :
    (∏ᶠ v : HeightOneSpectrum R,
        Nat.card (R ⧸ v.asIdeal) ^ (Associates.mk v.asIdeal).count (Associates.mk J).factors) =
      Ideal.absNorm J := by
  have hJ0 : J ≠ 0 := by rwa [Ideal.zero_eq_bot]
  have hfact := congrArg Ideal.absNorm.toMonoidHom
    (Ideal.finprod_heightOneSpectrum_factorization hJ0)
  rw [MonoidHom.map_finprod _ (Ideal.hasFiniteMulSupport hJ0)] at hfact
  refine Eq.trans ?_ hfact
  refine finprod_congr fun v ↦ ?_
  simp [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, Ideal.absNorm_of_ne_bot v.ne_bot,
    Submodule.cardQuot_apply]

end Ideal

namespace IsDedekindDomain.HeightOneSpectrum

/-- The absolute norm of a height-one prime of a Dedekind domain with finite quotients stays
nonzero when cast into any `AddMonoidWithOne` of characteristic zero. This is
`Ideal.natCast_absNorm_ne_zero` for `P.asIdeal`, stated for use with dot notation. -/
theorem natCast_absNorm_ne_zero {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Ring.HasFiniteQuotients R] {α : Type*} [AddMonoidWithOne α] [CharZero α]
    (P : HeightOneSpectrum R) : (Ideal.absNorm P.asIdeal : α) ≠ 0 :=
  Ideal.natCast_absNorm_ne_zero P.ne_bot

end IsDedekindDomain.HeightOneSpectrum

namespace Int

/-- The absolute norm of the ideal of `ℤ` generated by `n` is `|n|`. -/
theorem absNorm_span_singleton (n : ℤ) : Ideal.absNorm (Ideal.span {n}) = n.natAbs := by
  rw [Ideal.absNorm_span_singleton, Algebra.norm_self, MonoidHom.id_apply]

/-- An ideal of `ℤ` dividing the ideal generated by a nonzero `n` has absolute norm at most
`|n|`. -/
theorem absNorm_le_natAbs_of_dvd_span_singleton {I : Ideal ℤ} {n : ℤ} (hn : n ≠ 0)
    (h : I ∣ Ideal.span {n}) : Ideal.absNorm I ≤ n.natAbs := by
  rw [← absNorm_span_singleton]
  exact Nat.le_of_dvd (by simpa [absNorm_span_singleton] using hn)
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd h))

end Int

section AbsNormCongruence

variable {S : Type*} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S]

/-- Coprimality of an ideal to the ideal generated by a natural number implies coprimality of
its absolute norm to that number. -/
theorem Ideal.absNorm_coprime_of_isCoprime_span_natCast [IsDedekindDomain S]
    {I : Ideal S} {n : ℕ} (hcop : IsCoprime I (Ideal.span {(n : S)})) :
    (Ideal.absNorm I).Coprime n := by
  by_contra h
  obtain ⟨p, hp, hpI, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  obtain ⟨P, hPmax, hPunder, hPI⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hpI
  have hIle : I ≤ P := Ideal.dvd_iff_le.mp hPI
  have hnmem : (n : S) ∈ P := by
    have hnunder : (n : ℤ) ∈ P.under ℤ := by
      rw [hPunder, Ideal.mem_span_singleton]
      exact_mod_cast hpn
    have hnmap : algebraMap ℤ S (n : ℤ) ∈ P := by
      rw [← Ideal.mem_under]
      exact hnunder
    simpa using hnmap
  have hnle : Ideal.span {(n : S)} ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hnmem
  have htop : (⊤ : Ideal S) ≤ P := by
    rw [← hcop.sup_eq]
    exact sup_le hIle hnle
  exact hPmax.ne_top (top_unique htop)

/-- **Congruent elements with norms of nonnegative product generate ideals of congruent norms.**
If `a ≡ b` modulo the ideal `(m)` of a Dedekind domain `S` that is free of finite rank over `ℤ`,
and `N(a) N(b) ≥ 0`, then the absolute norms of `(a)` and `(b)` are congruent modulo `m`. -/
theorem Ideal.natCast_absNorm_span_singleton_eq_of_sub_mem [IsDedekindDomain S]
    {m : ℕ}
    {a b : S} (hab : 0 ≤ Algebra.norm ℤ a * Algebra.norm ℤ b)
    (h : a - b ∈ Ideal.span {(m : S)}) :
    (Ideal.absNorm (Ideal.span {a}) : ZMod m) = Ideal.absNorm (Ideal.span {b}) := by
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
  exact ZMod.natCast_natAbs_eq_of_mul_nonneg hab (Algebra.intCast_norm_eq_of_sub_mem_span_natCast h)

end AbsNormCongruence

namespace Submodule

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Module.IsTorsionFree R M]

/-- **The index of the multiples of `a • s`** in a torsion-free module is the index of `(a)` in `R`
times the index of the multiples of `s`, for `s ≠ 0`: the multiples of `s` form a copy of `R` in
which those of `a • s` are the ideal `(a)`. Both sides are `0` when an index is infinite. -/
theorem cardQuot_span_singleton_smul (a : R) {s : M} (hs : s ≠ 0) :
    (span R {a • s}).cardQuot = (Ideal.span {a}).cardQuot * (span R {s}).cardQuot := by
  let f := LinearMap.toSpanSingleton R M s
  have hmap : span R {a • s} = Submodule.map f (Ideal.span {a}) := by
    rw [← Ideal.submodule_span_eq, map_span, Set.image_singleton, LinearMap.toSpanSingleton_apply]
  rw [hmap, cardQuot_map_of_injective (smul_left_injective R hs), LinearMap.range_toSpanSingleton]

end Submodule
