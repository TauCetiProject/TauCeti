/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# The monic irreducible factors of a polynomial over a field

For a polynomial `f` over a field `K`, `Polynomial.Factors f` is the type of its distinct monic
irreducible factors: the subtype of `K[X]` cut out by `Irreducible p ∧ p.Monic ∧ p ∣ f`. Working
with this subtype rather than with `normalizedFactors f` keeps `DecidableEq K` out of the
statements; the two are compared by Mathlib's `Polynomial.mem_normalizedFactors_iff`, whose
conjunct order the predicate above follows.

The factors are pairwise coprime, and when `f` is nonzero and squarefree their product is
associated to `f`, so the ideal `(f)` is the intersection of the ideals `(p)`. That is the input
for the Chinese Remainder decomposition of `K[X] ⧸ (f)` into the fields `K[X] ⧸ (p)`.

## Main definitions

* `Polynomial.Factors`: the distinct monic irreducible factors of `f`, as a type.
* `Polynomial.Factors.linearEquivRoots`: the linear factors correspond to the roots of `f`, with
  `linearEquivRoots_apply` and `linearEquivRoots_symm_apply` computing both directions.

## Main results

* `Polynomial.Factors.finite`: a nonzero polynomial has finitely many factors.
* `Polynomial.Factors.infinite_zero`, `Polynomial.Factors.finite_iff`: the zero polynomial has
  infinitely many factors (an instance), so finiteness characterizes nonzero polynomials.
* `Polynomial.Factors.normalizedFactors_eq_map_univ_val`: for a nonzero squarefree polynomial,
  its normalized factors are precisely the distinct monic irreducible factors.
* `Polynomial.Factors.subsingleton_iff_exists_associated_pow`: a polynomial has at most one factor
  exactly when it is a unit times a power of an irreducible polynomial.
* `Polynomial.Factors.isCoprime`: distinct factors are coprime.
* `Polynomial.Factors.span_eq_iInf_span`: for `f` nonzero and squarefree,
  `(f) = ⨅ p, (p)`.
* `Polynomial.sum_natDegree_normalizedFactors`: the degrees of the normalized irreducible
  factors, counted with multiplicity, sum to the degree.
* `Polynomial.map_natDegree_normalizedFactors_eq_singleton_iff`: those degrees form a singleton
  exactly when the polynomial is irreducible.
* `Polynomial.count_one_map_natDegree_normalizedFactors`: a nonzero squarefree polynomial has as
  many linear normalized factors as distinct roots.
* `Polynomial.monic_squarefree_normalizedFactors_prod`: a product of distinct monic irreducible
  polynomials is monic and squarefree, and its normalized factors are those polynomials.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, commit `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`, section `EtaleDecomposition`. The source is written against
Lean `v4.32.0`; this is a forward port.
-/

public section

namespace Polynomial

open UniqueFactorizationMonoid

variable {K : Type*} [Field K] {f : K[X]}

/-- The distinct monic irreducible factors of `f`, as an index type.

This is *not* defined via `normalizedFactors` (which would require `DecidableEq K`); the
predicate is spelled in the order of `Polynomial.mem_normalizedFactors_iff`, which is therefore
the characterization of membership in `normalizedFactors f`. -/
abbrev Factors (f : K[X]) : Type _ := {p : K[X] // Irreducible p ∧ p.Monic ∧ p ∣ f}

namespace Factors

lemma irreducible (p : f.Factors) : Irreducible (p : K[X]) := p.2.1

lemma monic (p : f.Factors) : (p : K[X]).Monic := p.2.2.1

lemma dvd (p : f.Factors) : (p : K[X]) ∣ f := p.2.2.2

lemma ne_zero (p : f.Factors) : (p : K[X]) ≠ 0 := p.irreducible.ne_zero

lemma prime (p : f.Factors) : Prime (p : K[X]) := p.irreducible.prime

lemma separable (hf : f.Separable) (p : f.Factors) : (p : K[X]).Separable :=
  hf.of_dvd p.dvd

lemma finite (hf : f ≠ 0) : Finite f.Factors := by
  classical
  have h : Finite {p : K[X] // p ∈ normalizedFactors f} :=
    (normalizedFactors f).finite_toSet.to_subtype
  exact .of_injective _
    (Subtype.impEmbedding _ (· ∈ normalizedFactors f)
      fun p hp ↦ (Polynomial.mem_normalizedFactors_iff hf).mpr hp).injective

/-- For a nonzero squarefree polynomial, its normalized factors list its distinct monic
irreducible factors exactly once. -/
lemma normalizedFactors_eq_map_univ_val [Fintype f.Factors] [DecidableEq K]
    (hsq : Squarefree f) :
    normalizedFactors f = Finset.univ.val.map (Subtype.val : f.Factors → K[X]) := by
  have hf := hsq.ne_zero
  refine (Multiset.Nodup.ext
    ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hf).1 hsq)
    (Finset.univ.nodup.map Subtype.val_injective)).2 fun p => ?_
  rw [Polynomial.mem_normalizedFactors_iff hf, Multiset.mem_map]
  exact ⟨fun hp => ⟨⟨p, hp⟩, Finset.mem_univ _, rfl⟩, fun ⟨q, _, hq⟩ => hq ▸ q.2⟩

/-- The zero polynomial has infinitely many distinct monic irreducible factors, since every monic
irreducible polynomial divides it. -/
instance infinite_zero : Infinite (0 : K[X]).Factors := by
  classical
  refine Infinite.of_not_fintype fun hfin : Fintype (0 : K[X]).Factors ↦ ?_
  -- Euclid's argument: `X` times the product of the factors, plus one, has a new factor.
  set S : Finset K[X] := (Finset.univ : Finset (0 : K[X]).Factors).image Subtype.val
  have hSm : ∀ q ∈ S, q.Monic := fun q hq ↦ by
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hq
    exact Factors.monic q
  have hPdeg : 0 < (X * ∏ q ∈ S, q).natDegree := by
    rw [monic_X.natDegree_mul (monic_prod_of_monic _ _ hSm), natDegree_X]
    omega
  have hN := not_isUnit_of_natDegree_pos (X * ∏ q ∈ S, q + 1)
    (by rwa [natDegree_add_eq_left_of_natDegree_lt (by simpa using hPdeg)])
  obtain ⟨q, hqm, hqirr, hqdvd⟩ := exists_monic_irreducible_factor _ hN
  have hqS : q ∈ S := Finset.mem_image.mpr ⟨⟨q, hqirr, hqm, dvd_zero q⟩, Finset.mem_univ _, rfl⟩
  have h1 : q ∣ X * ∏ q ∈ S, q := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hqS) X
  exact hqirr.not_isUnit (isUnit_of_dvd_one ((dvd_add_right h1).mp hqdvd))

/-- A polynomial has finitely many distinct monic irreducible factors exactly when it is nonzero. -/
lemma finite_iff : Finite f.Factors ↔ f ≠ 0 :=
  ⟨fun h hf ↦ by
    subst hf
    exact _root_.not_finite (Factors (0 : K[X])), finite⟩

lemma nonempty (hu : ¬ IsUnit f) : Nonempty f.Factors :=
  let ⟨p, hmonic, hirr, hdvd⟩ := f.exists_monic_irreducible_factor hu
  ⟨⟨p, hirr, hmonic, hdvd⟩⟩

/-- A polynomial has at most one monic irreducible factor exactly when it is a unit times a power
of one irreducible polynomial. -/
lemma subsingleton_iff_exists_associated_pow :
    Subsingleton f.Factors ↔ ∃ q : K[X], Irreducible q ∧ ∃ n : ℕ, Associated (q ^ n) f := by
  classical
  by_cases hf : f = 0
  · -- Both sides fail: `0` has infinitely many factors and is not associated to a power of an
    -- irreducible polynomial.
    subst f
    exact iff_of_false (not_subsingleton _) fun ⟨q, hq, n, hq0⟩ ↦
      pow_ne_zero n hq.ne_zero (hq0.eq_zero_iff.mpr rfl)
  refine ⟨fun h ↦ ?_, fun ⟨q, hq, n, hqf⟩ ↦ ⟨fun a b ↦ Subtype.ext ?_⟩⟩
  · by_cases hu : IsUnit f
    · exact ⟨X, irreducible_X, 0, by rw [pow_zero]; exact (associated_one_iff_isUnit.mpr hu).symm⟩
    obtain ⟨q⟩ := nonempty hu
    refine ⟨q, q.irreducible, exists_associated_prime_pow_of_unique_normalized_factor
      (fun {m} hm ↦ ?_) hf⟩
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨m, (Polynomial.mem_normalizedFactors_iff hf).mp hm⟩ : f.Factors) q)
  · -- Every factor divides `q ^ n`, hence `q`, so all of them are associated to `q`.
    have key (r : f.Factors) : Associated (r : K[X]) q :=
      r.irreducible.associated_of_dvd hq (r.prime.dvd_of_dvd_pow (r.dvd.trans hqf.symm.dvd))
    exact eq_of_monic_of_associated a.monic b.monic ((key a).trans (key b).symm)

/-- The monic linear factors of `f` correspond to the roots of `f`. -/
noncomputable def linearEquivRoots :
    {p : f.Factors // (p : K[X]).natDegree = 1} ≃ {x : K // f.eval x = 0} where
  toFun p := ⟨-((p : f.Factors) : K[X]).coeff 0,
    eval_eq_zero_of_dvd_of_eval_eq_zero (p : f.Factors).dvd <| by
      conv_lhs => rw [(p : f.Factors).monic.eq_X_add_C p.2]
      simp⟩
  invFun x := ⟨⟨X - C (x : K), irreducible_X_sub_C _, monic_X_sub_C _,
    dvd_iff_isRoot.mpr x.2⟩, natDegree_X_sub_C _⟩
  left_inv p := Subtype.ext <| Subtype.ext <| by
    simpa using ((p : f.Factors).monic.eq_X_add_C p.2).symm
  right_inv x := Subtype.ext <| by simp

/-- `linearEquivRoots` sends a monic linear factor to the root it records, the negated constant
coefficient. -/
@[simp]
lemma linearEquivRoots_apply (p : {p : f.Factors // (p : K[X]).natDegree = 1}) :
    (linearEquivRoots p : K) = -((p : f.Factors) : K[X]).coeff 0 :=
  (rfl)

/-- `linearEquivRoots.symm` sends a root `x` to the monic linear factor `X - C x`. -/
@[simp]
lemma linearEquivRoots_symm_apply (x : {x : K // f.eval x = 0}) :
    ((linearEquivRoots.symm x : f.Factors) : K[X]) = X - C (x : K) :=
  (rfl)

/-- Distinct monic irreducible factors of `f` are coprime. -/
lemma isCoprime {p q : f.Factors} (hne : p ≠ q) : IsCoprime (p : K[X]) (q : K[X]) :=
  p.irreducible.coprime_iff_not_dvd.mpr fun h ↦ hne <| Subtype.ext <|
    eq_of_monic_of_associated p.monic q.monic (p.irreducible.associated_of_dvd q.irreducible h)

/-- Distinct monic irreducible factors of `f` span coprime ideals. -/
lemma isCoprime_span {p q : f.Factors} (hne : p ≠ q) :
    IsCoprime (Ideal.span {(p : K[X])}) (Ideal.span {(q : K[X])}) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mpr (isCoprime hne)

/-- A nonzero squarefree polynomial is associated to the product of its distinct monic
irreducible factors. -/
lemma associated_prod [Fintype f.Factors] (hsq : Squarefree f) :
    Associated (∏ p : f.Factors, (p : K[X])) f := by
  classical
  rw [Finset.prod_eq_multiset_prod, ← normalizedFactors_eq_map_univ_val hsq]
  exact prod_normalizedFactors hsq.ne_zero

/-- The degrees of the distinct monic irreducible factors of `f` sum to at most the degree of
`f`. The `Fintype` instance forces `f ≠ 0`, by `finite_iff`. -/
lemma sum_natDegree_le [Fintype f.Factors] :
    ∑ p : f.Factors, (p : K[X]).natDegree ≤ f.natDegree := by
  rw [← natDegree_prod _ _ fun p _ ↦ p.ne_zero]
  exact natDegree_le_of_dvd
    (Fintype.prod_dvd_of_coprime (fun p q hpq ↦ isCoprime hpq) fun p ↦ p.dvd)
    (finite_iff.mp inferInstance)

/-- For `f` nonzero and squarefree, the ideal `(f)` is the intersection of the ideals `(p)` over
the monic irreducible factors `p` of `f`. This is the input for the Chinese Remainder
decomposition of `K[X] ⧸ (f)`. -/
lemma span_eq_iInf_span (hsq : Squarefree f) :
    Ideal.span {f} = ⨅ p : f.Factors, Ideal.span {(p : K[X])} := by
  have hf := hsq.ne_zero
  have : Fintype f.Factors := @Fintype.ofFinite _ (finite hf)
  rw [Ideal.iInf_span_singleton fun _ _ hpq ↦ isCoprime hpq]
  exact (Ideal.span_singleton_eq_span_singleton.mpr (associated_prod hsq)).symm

/-- A prime factor of the image of `f` under a ring homomorphism to a commutative semiring
divides the image of one of the monic irreducible factors of `f`.

This lets computations after changing coefficients be indexed by the factors over the base
field, including when the target is a nonfield ring such as a product of fields. -/
lemma exists_dvd_map {L : Type*} [CommSemiring L] (σ : K →+* L) (hf : f ≠ 0) {q : L[X]}
    (hq : Prime q) (hdvd : q ∣ f.map σ) : ∃ p : f.Factors, q ∣ (p : K[X]).map σ := by
  classical
  have h1 : Associated ((normalizedFactors f).map (Polynomial.map σ)).prod (f.map σ) := by
    have h2 := (prod_normalizedFactors hf).map (mapRingHom σ)
    rwa [map_multiset_prod, coe_mapRingHom] at h2
  obtain ⟨g, hgmem, hgdvd⟩ := hq.exists_mem_multiset_dvd (hdvd.trans h1.symm.dvd)
  obtain ⟨p₀, hp₀, rfl⟩ := Multiset.mem_map.mp hgmem
  exact ⟨⟨p₀, (Polynomial.mem_normalizedFactors_iff hf).mp hp₀⟩, hgdvd⟩

end Factors

/-! ### Degrees of the normalized irreducible factors

`Polynomial.Factors` keeps `DecidableEq K` out of its statements by working with a subtype, at
the cost of forgetting multiplicities. The lemmas below are the counterparts for
`normalizedFactors`, which does record them.
-/

variable [DecidableEq K]

/-- The degrees of the normalized irreducible factors of a polynomial over a field, counted with
multiplicity, sum to its degree. -/
lemma sum_natDegree_normalizedFactors (g : K[X]) :
    ((normalizedFactors g).map natDegree).sum = g.natDegree := by
  by_cases hg : g = 0
  · simp [hg]
  · rw [← natDegree_multiset_prod _ (zero_notMem_normalizedFactors g)]
    exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hg))

/-- The degrees of the normalized irreducible factors of a polynomial over a field form the
singleton `{g.natDegree}` exactly when the polynomial is irreducible. -/
@[simp]
lemma map_natDegree_normalizedFactors_eq_singleton_iff {g : K[X]} :
    (normalizedFactors g).map natDegree = {g.natDegree} ↔ Irreducible g := by
  refine ⟨fun h ↦ card_normalizedFactors_eq_one_iff.mp ?_, fun h ↦ ?_⟩
  · simpa using congrArg Multiset.card h
  · rw [normalizedFactors_irreducible h, Multiset.map_singleton, natDegree_normalize]

/-- For a nonzero squarefree polynomial over a field, the number of linear factors among its
normalized irreducible factors is the number of its distinct roots. Over a finite field this
bounds the number of linear factors by the number of elements of the field. -/
lemma count_one_map_natDegree_normalizedFactors {g : K[X]} (hsq : Squarefree g) :
    ((normalizedFactors g).map natDegree).count 1 = g.roots.toFinset.card := by
  have hg := hsq.ne_zero
  have := Factors.finite hg
  let _ : Fintype g.Factors := Fintype.ofFinite _
  -- Squarefreeness lists the normalized factors as the distinct factors `g.Factors`; the linear
  -- ones correspond to the roots through `Factors.linearEquivRoots`.
  have hlin : ((normalizedFactors g).map natDegree).count 1 =
      Nat.card {p : g.Factors // (p : K[X]).natDegree = 1} := by
    simp [Multiset.count_map, Factors.normalizedFactors_eq_map_univ_val hsq, eq_comm (a := 1),
      Fintype.card_subtype, Finset.card_def]
  rw [hlin, Nat.card_congr Factors.linearEquivRoots, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by simp [hg])

/-- The product of a duplicate-free multiset of monic irreducible polynomials is monic and
squarefree, and its normalized factors are the multiset itself. -/
theorem monic_squarefree_normalizedFactors_prod {s : Multiset K[X]}
    (smonic : ∀ p ∈ s, p.Monic) (sirr : ∀ p ∈ s, Irreducible p) (snodup : s.Nodup) :
    s.prod.Monic ∧ Squarefree s.prod ∧ normalizedFactors s.prod = s := by
  have hfac : normalizedFactors s.prod = s := by
    rw [normalizedFactors_prod_eq s sirr]
    exact (Multiset.map_congr rfl fun p hp ↦ (smonic p hp).normalize_eq_self).trans s.map_id'
  refine ⟨by simpa using monic_multiset_prod_of_monic s id smonic, ?_, hfac⟩
  rw [squarefree_iff_nodup_normalizedFactors
    (Multiset.prod_ne_zero fun hp ↦ (sirr 0 hp).ne_zero rfl), hfac]
  exact snodup

end Polynomial

end
