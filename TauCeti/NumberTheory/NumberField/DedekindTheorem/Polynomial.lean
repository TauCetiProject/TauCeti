/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.NumberTheory.NumberField.DedekindTheorem
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import TauCeti.GroupTheory.Perm.SumCongr
import TauCeti.NumberTheory.NumberField.Frobenius
import TauCeti.NumberTheory.NumberField.Minpoly
import TauCeti.NumberTheory.NumberField.SplittingField
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Roots

/-!
# Dedekind's theorem for an integer polynomial

Let `f` be a monic polynomial over `ℤ` and let `p` be a prime not dividing the discriminant of
`f`, equivalently a prime such that `f mod p` is squarefree. Dedekind's theorem says that the
Galois group of `f` contains a permutation of the roots of `f` whose cycle type, with fixed points
counted as cycles of length `1`, is the multiset of degrees of the irreducible factors of
`f mod p`. This file derives that statement from the field-theoretic form
`TauCeti.NumberField.fullCycleType_galActionHom_restrict_eq_map_natDegree_monicFactorsMod`
proved in `TauCeti.NumberTheory.NumberField.DedekindTheorem`.

Throughout, the permutation is the action of a Frobenius element `σ` at a prime above `p` of a
Galois number field `M` in which `f` splits, acting on the roots of `f` in `M`. For an
irreducible `f`, the root field `ℚ[X]/(f)` has the class of `X` as an integral primitive element
with minimal polynomial `f` over `ℤ` (Gauss's lemma supplies the irreducibility of `f` over `ℚ`),
and the field-theoretic theorem applies directly. For a reducible `f`, the root set of `f` is
the disjoint union of the root sets of the monic irreducible factors of `f` over `ℤ` (two such
factors sharing a root would share the minimal polynomial of that root, whose square would then
divide `f mod p`), the action of `σ` respects that decomposition, and both the full cycle type and
the factor-degree multiset are additive along it; the same `σ` serves for every factor.

Finally the permutation is transported along `Polynomial.Gal.rootsEquivRoots` to the roots of
`f` in an arbitrary field `E` over `ℚ` in which `f` splits, and produced as an element of
`Polynomial.Gal (f.map (Int.castRingHom ℚ))`, so that the statement does not mention `M`.

## Main results

* `exists_gal_fullCycleType_eq_map_natDegree_normalizedFactors`: Dedekind's theorem for a monic
  `f : ℤ[X]` squarefree modulo `p`, in any field `E` over `ℚ` where `f` splits.
* `exists_gal_fullCycleType_eq_factorizationType`: the same in `ℂ`, hypothesised on
  `p ∤ f.discr`, with the full cycle type written out as the cycle type plus one part `1` for
  each fixed point. This is the form consumed by name by the polynomial Galois groups roadmap.
* `fullCycleType_galActionHom_restrict_eq_map_natDegree_normalizedFactors`: the statement for a
  fixed Frobenius element of a fixed Galois number field.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §8, Exercise 4.
-/

public section

open Polynomial UniqueFactorizationMonoid

open scoped NumberField

namespace TauCeti.NumberField

variable {p : ℕ} [Fact p.Prime]

/-! ### Disjointness of the root sets of coprime factors -/

/-- Two monic integer polynomials whose product is squarefree modulo `p` have no common root in
any field of characteristic zero: a common root would have a minimal polynomial over `ℤ`
dividing both, whose square would divide the product modulo `p`. -/
theorem disjoint_rootSet_of_squarefree_map_mul {a b : ℤ[X]} (ha : a.Monic)
    (hsq : Squarefree ((a * b).map (Int.castRingHom (ZMod p)))) (E : Type*) [Field E]
    [Algebra ℚ E] :
    Disjoint ((a.map (Int.castRingHom ℚ)).rootSet E) ((b.map (Int.castRingHom ℚ)).rootSet E) := by
  rw [Set.disjoint_left]
  intro β hβa hβb
  rw [mem_rootSet, ← algebraMap_int_eq, aeval_map_algebraMap] at hβa hβb
  have : CharZero E := ((algebraMap ℚ E).charZero_iff (algebraMap ℚ E).injective).mp inferInstance
  have hint : IsIntegral ℤ β := ⟨a, ha, by rw [← aeval_def]; exact hβa.2⟩
  have hdvd : (minpoly ℤ β).map (Int.castRingHom (ZMod p)) *
      (minpoly ℤ β).map (Int.castRingHom (ZMod p)) ∣ (a * b).map (Int.castRingHom (ZMod p)) := by
    rw [← Polynomial.map_mul]
    exact Polynomial.map_dvd _ (mul_dvd_mul (minpoly.isIntegrallyClosed_dvd hint hβa.2)
      (minpoly.isIntegrallyClosed_dvd hint hβb.2))
  have h1 := ((minpoly.monic hint).map (Int.castRingHom (ZMod p))).isUnit_iff.mp (hsq _ hdvd)
  have h2 := (minpoly.monic hint).natDegree_map (Int.castRingHom (ZMod p))
  rw [h1, natDegree_one] at h2
  exact (minpoly.natDegree_pos hint).ne h2

/-! ### Additivity of the full cycle type along a factorisation -/

section Product

variable {E : Type*} [Field E] [Algebra ℚ E]

open scoped Classical in
/-- The full cycle type of the action of `σ` on the roots of `a * b` is the sum of the full
cycle types of its actions on the roots of `a` and of `b`, when the root sets are disjoint. -/
theorem fullCycleType_galActionHom_restrict_map_mul {a b : ℤ[X]} (ha : a.Monic) (hb : b.Monic)
    (hsq : Squarefree ((a * b).map (Int.castRingHom (ZMod p))))
    [Fact (((a * b).map (Int.castRingHom ℚ)).map (algebraMap ℚ E)).Splits]
    [Fact ((a.map (Int.castRingHom ℚ)).map (algebraMap ℚ E)).Splits]
    [Fact ((b.map (Int.castRingHom ℚ)).map (algebraMap ℚ E)).Splits] (σ : E ≃ₐ[ℚ] E) :
    Equiv.Perm.fullCycleType (Gal.galActionHom ((a * b).map (Int.castRingHom ℚ)) E
        (Gal.restrict ((a * b).map (Int.castRingHom ℚ)) E σ)) =
      Equiv.Perm.fullCycleType (Gal.galActionHom (a.map (Int.castRingHom ℚ)) E
          (Gal.restrict (a.map (Int.castRingHom ℚ)) E σ)) +
        Equiv.Perm.fullCycleType (Gal.galActionHom (b.map (Int.castRingHom ℚ)) E
          (Gal.restrict (b.map (Int.castRingHom ℚ)) E σ)) := by
  have hdisj := disjoint_rootSet_of_squarefree_map_mul ha hsq E
  have hunion : ((a * b).map (Int.castRingHom ℚ)).rootSet E =
      (a.map (Int.castRingHom ℚ)).rootSet E ∪ (b.map (Int.castRingHom ℚ)).rootSet E := by
    rw [Polynomial.map_mul]
    exact rootSet_mul ((ha.map _).map _).ne_zero ((hb.map _).map _).ne_zero
  let e : ((a * b).map (Int.castRingHom ℚ)).rootSet E ≃
      (a.map (Int.castRingHom ℚ)).rootSet E ⊕ (b.map (Int.castRingHom ℚ)).rootSet E :=
    (Equiv.subtypeEquivRight (Set.ext_iff.mp hunion)).trans (Equiv.Set.union hdisj)
  have hl : ∀ (y : ((a * b).map (Int.castRingHom ℚ)).rootSet E)
      (h : (y : E) ∈ (a.map (Int.castRingHom ℚ)).rootSet E), e y = Sum.inl ⟨y, h⟩ := fun y h =>
    Equiv.Set.union_apply_left hdisj (a := Equiv.subtypeEquivRight (Set.ext_iff.mp hunion) y) h
  have hr : ∀ (y : ((a * b).map (Int.castRingHom ℚ)).rootSet E)
      (h : (y : E) ∈ (b.map (Int.castRingHom ℚ)).rootSet E), e y = Sum.inr ⟨y, h⟩ := fun y h =>
    Equiv.Set.union_apply_right hdisj (a := Equiv.subtypeEquivRight (Set.ext_iff.mp hunion) y) h
  have hsl : ∀ z : (a.map (Int.castRingHom ℚ)).rootSet E, ((e.symm (Sum.inl z) : _) : E) = z :=
    fun _ => rfl
  have hsr : ∀ z : (b.map (Int.castRingHom ℚ)).rootSet E, ((e.symm (Sum.inr z) : _) : E) = z :=
    fun _ => rfl
  have hcoe : ∀ (g : ℚ[X]) [Fact (g.map (algebraMap ℚ E)).Splits] (y : g.rootSet E),
      ((Gal.galActionHom g E (Gal.restrict g E σ) y : g.rootSet E) : E) = σ y :=
    fun g _ y => Gal.restrict_smul σ y
  -- Along `e`, the permutation of the roots of `a * b` is the sum of the two permutations.
  have hperm : e.permCongr (Gal.galActionHom ((a * b).map (Int.castRingHom ℚ)) E
      (Gal.restrict ((a * b).map (Int.castRingHom ℚ)) E σ)) =
      Equiv.Perm.sumCongr (Gal.galActionHom (a.map (Int.castRingHom ℚ)) E
        (Gal.restrict (a.map (Int.castRingHom ℚ)) E σ))
        (Gal.galActionHom (b.map (Int.castRingHom ℚ)) E
          (Gal.restrict (b.map (Int.castRingHom ℚ)) E σ)) := by
    ext z
    rcases z with z | z
    · have hz : ((Gal.galActionHom _ E (Gal.restrict _ E σ) (e.symm (Sum.inl z)) : _) : E) ∈
          (a.map (Int.castRingHom ℚ)).rootSet E := by
        rw [hcoe, hsl, ← hcoe (a.map (Int.castRingHom ℚ))]
        exact (Gal.galActionHom _ E (Gal.restrict _ E σ) z).2
      rw [Equiv.permCongr_apply, Equiv.Perm.sumCongr_apply, Sum.map_inl, hl _ hz]
      congr 1
      exact Subtype.ext ((hcoe _ _).trans ((congrArg σ (hsl z)).trans (hcoe _ z).symm))
    · have hz : ((Gal.galActionHom _ E (Gal.restrict _ E σ) (e.symm (Sum.inr z)) : _) : E) ∈
          (b.map (Int.castRingHom ℚ)).rootSet E := by
        rw [hcoe, hsr, ← hcoe (b.map (Int.castRingHom ℚ))]
        exact (Gal.galActionHom _ E (Gal.restrict _ E σ) z).2
      rw [Equiv.permCongr_apply, Equiv.Perm.sumCongr_apply, Sum.map_inr, hr _ hz]
      congr 1
      exact Subtype.ext ((hcoe _ _).trans ((congrArg σ (hsr z)).trans (hcoe _ z).symm))
  simp only [Equiv.Perm.fullCycleType_def]
  rw [← Equiv.Perm.parts_partition_permCongr e, hperm, Equiv.Perm.parts_partition_sumCongr]

end Product

/-! ### Dedekind's theorem at a fixed Frobenius element -/

section Frobenius

variable {M : Type*} [Field M] [NumberField M] [IsGalois ℚ M]

open scoped Classical in
/-- Dedekind's theorem for a monic irreducible `f : ℤ[X]` squarefree modulo `p`, at a Frobenius
element `σ` of a Galois number field `M` in which `f` splits: `σ` permutes the roots of `f` in
`M` with full cycle type the degrees of the irreducible factors of `f mod p`. -/
theorem fullCycleType_galActionHom_restrict_eq_map_natDegree_normalizedFactors_of_irreducible
    {f : ℤ[X]} (hf : f.Monic) (hirr : Irreducible f)
    (hsq : Squarefree (f.map (Int.castRingHom (ZMod p))))
    [Fact ((f.map (Int.castRingHom ℚ)).map (algebraMap ℚ M)).Splits]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(p : ℤ)})]
    {σ : M ≃ₐ[ℚ] M} (hσ : IsArithFrobAt ℤ σ Q) :
    Equiv.Perm.fullCycleType (Gal.galActionHom (f.map (Int.castRingHom ℚ)) M
        (Gal.restrict (f.map (Int.castRingHom ℚ)) M σ)) =
      (normalizedFactors (f.map (Int.castRingHom (ZMod p)))).map natDegree := by
  set g : ℚ[X] := f.map (Int.castRingHom ℚ) with hg
  have hgirr : Irreducible g := by
    rw [hg, ← algebraMap_int_eq]
    exact (hf.irreducible_iff_irreducible_map_fraction_map).mp hirr
  have hgmonic : g.Monic := hf.map _
  have : Fact (Irreducible g) := ⟨hgirr⟩
  -- The root field `K = ℚ[X]/(g)` and its generator as an algebraic integer.
  set K := AdjoinRoot g
  have hθint : IsIntegral ℤ (AdjoinRoot.root g) :=
    ⟨f, hf, by
      rw [show algebraMap ℤ K = (AdjoinRoot.of g).comp (Int.castRingHom ℚ) from
        (RingHom.eq_intCast' _).trans (RingHom.eq_intCast' _).symm, ← eval₂_map, ← hg]
      exact AdjoinRoot.eval₂_root g⟩
  set θ : 𝓞 K := ⟨AdjoinRoot.root g, hθint⟩ with hθ
  have hminQ : minpoly ℚ (θ : K) = g := by
    have h1 := AdjoinRoot.minpoly_root (K := ℚ) hgirr.ne_zero
    rw [hgmonic.leadingCoeff, inv_one, C_1, mul_one] at h1
    convert h1 using 2 <;> rfl
  have hminZ : minpoly ℤ θ = f := by
    apply Polynomial.map_injective _ (algebraMap ℤ ℚ).injective_int
    rw [← _root_.NumberField.RingOfIntegers.minpoly_rat_coe, hminQ, hg, algebraMap_int_eq]
  have hsq' : Squarefree ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by rwa [hminZ]
  -- Dedekind's theorem for `θ`, transported to the given polynomial `g = minpoly ℚ θ`.
  have key : ∀ (g' : ℚ[X]) [Fact (g'.map (algebraMap ℚ M)).Splits], minpoly ℚ (θ : K) = g' →
      Equiv.Perm.fullCycleType (Gal.galActionHom g' M (Gal.restrict g' M σ)) =
        (RingOfIntegers.monicFactorsMod θ p).val.map natDegree := by
    intro g' _ hg'
    subst hg'
    exact fullCycleType_galActionHom_restrict_eq_map_natDegree_monicFactorsMod hsq' Q hσ
  rw [key g hminQ, RingOfIntegers.monicFactorsMod, hminZ, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr]
  exact (squarefree_iff_nodup_normalizedFactors (hf.map _).ne_zero).mp hsq

open scoped Classical in
/-- **Dedekind's theorem** at a Frobenius element. Let `f` be a monic integer polynomial
squarefree modulo the prime `p`, and let `σ` be a Frobenius element at a prime above `p` of a
Galois number field `M` in which `f` splits. Then `σ` permutes the roots of `f` in `M` with full
cycle type the multiset of degrees of the irreducible factors of `f mod p`. -/
theorem fullCycleType_galActionHom_restrict_eq_map_natDegree_normalizedFactors
    {f : ℤ[X]} (hf : f.Monic) (hsq : Squarefree (f.map (Int.castRingHom (ZMod p))))
    [Fact ((f.map (Int.castRingHom ℚ)).map (algebraMap ℚ M)).Splits]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(p : ℤ)})]
    {σ : M ≃ₐ[ℚ] M} (hσ : IsArithFrobAt ℤ σ Q) :
    Equiv.Perm.fullCycleType (Gal.galActionHom (f.map (Int.castRingHom ℚ)) M
        (Gal.restrict (f.map (Int.castRingHom ℚ)) M σ)) =
      (normalizedFactors (f.map (Int.castRingHom (ZMod p)))).map natDegree := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hu : IsUnit f
    · obtain rfl := hf.eq_one_of_isUnit hu
      have : IsEmpty (((1 : ℤ[X]).map (Int.castRingHom ℚ)).rootSet M) :=
        Set.isEmpty_coe_sort.mpr (by rw [Polynomial.map_one, rootSet_one])
      rw [Equiv.Perm.fullCycleType_of_isEmpty, Polynomial.map_one, normalizedFactors_one,
        Multiset.map_zero]
    -- Split off a monic irreducible factor `q'` of `f`, leaving a monic cofactor `r'`.
    obtain ⟨q, hq, r, hr⟩ := WfDvdMonoid.exists_irreducible_factor hu hf.ne_zero
    have hlc : q.leadingCoeff * r.leadingCoeff = 1 := by
      rw [← leadingCoeff_mul, ← hr, hf.leadingCoeff]
    have hqu : IsUnit q.leadingCoeff := ⟨⟨_, _, hlc, (mul_comm _ _).trans hlc⟩, rfl⟩
    have hq'm : (q * C q.leadingCoeff).Monic := by
      rw [Monic.def, leadingCoeff_mul, leadingCoeff_C, Int.isUnit_mul_self hqu]
    have hfeq : f = q * C q.leadingCoeff * (r * C q.leadingCoeff) := by
      rw [mul_mul_mul_comm, ← C_mul, Int.isUnit_mul_self hqu, C_1, mul_one, hr]
    have hr'm : (r * C q.leadingCoeff).Monic := hq'm.of_mul_monic_left (hfeq ▸ hf)
    have hq'irr : Irreducible (q * C q.leadingCoeff) :=
      (irreducible_mul_isUnit (isUnit_C.mpr hqu)).mpr hq
    have hlt : (r * C q.leadingCoeff).natDegree < n := by
      rw [← hn, hfeq, hq'm.natDegree_mul hr'm]
      exact Nat.lt_add_of_pos_left (hq'm.natDegree_pos.mpr hq'irr.ne_one)
    subst hfeq
    have hsplit : ((q * C q.leadingCoeff * (r * C q.leadingCoeff)).map (Int.castRingHom ℚ)).map
        (algebraMap ℚ M) ≠ 0 := (((hq'm.mul hr'm).map _).map _).ne_zero
    have hs : (((q * C q.leadingCoeff * (r * C q.leadingCoeff)).map (Int.castRingHom ℚ)).map
        (algebraMap ℚ M)).Splits := Fact.out
    have : Fact (((q * C q.leadingCoeff).map (Int.castRingHom ℚ)).map (algebraMap ℚ M)).Splits :=
      ⟨hs.of_dvd hsplit (Polynomial.map_dvd _ (Polynomial.map_dvd _ (dvd_mul_right _ _)))⟩
    have : Fact (((r * C q.leadingCoeff).map (Int.castRingHom ℚ)).map (algebraMap ℚ M)).Splits :=
      ⟨hs.of_dvd hsplit (Polynomial.map_dvd _ (Polynomial.map_dvd _ (dvd_mul_left _ _)))⟩
    have hsq' := hsq
    rw [Polynomial.map_mul] at hsq'
    rw [fullCycleType_galActionHom_restrict_map_mul hq'm hr'm hsq σ,
      fullCycleType_galActionHom_restrict_eq_map_natDegree_normalizedFactors_of_irreducible hq'm
        hq'irr hsq'.of_mul_left Q hσ,
      ih _ hlt hr'm hsq'.of_mul_right rfl,
      Polynomial.map_mul (p := q * C q.leadingCoeff) (q := r * C q.leadingCoeff),
      normalizedFactors_mul (hq'm.map _).ne_zero (hr'm.map _).ne_zero, Multiset.map_add]

end Frobenius

/-! ### Dedekind's theorem in the Galois group of the polynomial -/

open scoped Classical in
/-- **Dedekind's theorem.** Let `f` be a monic integer polynomial squarefree modulo the prime
`p`, and let `E` be a field over `ℚ` in which `f` splits. Then some element of the Galois group
of `f` acts on the roots of `f` in `E` with full cycle type the multiset of degrees of the
irreducible factors of `f` modulo `p`. -/
theorem exists_gal_fullCycleType_eq_map_natDegree_normalizedFactors
    (f : ℤ[X]) (hf : f.Monic) (p : ℕ) [Fact p.Prime]
    (hsq : Squarefree (f.map (Int.castRingHom (ZMod p))))
    (E : Type*) [Field E] [Algebra ℚ E]
    [Fact ((f.map (Int.castRingHom ℚ)).map (algebraMap ℚ E)).Splits] :
    ∃ σ : (f.map (Int.castRingHom ℚ)).Gal,
      Equiv.Perm.fullCycleType (Gal.galActionHom (f.map (Int.castRingHom ℚ)) E σ) =
        (normalizedFactors (f.map (Int.castRingHom (ZMod p)))).map natDegree := by
  set g : ℚ[X] := f.map (Int.castRingHom ℚ) with hg
  -- `f` is separable over `ℚ`, since its discriminant is prime to `p`.
  have hsep : g.Separable := by
    rw [hg, ← algebraMap_int_eq, ← hf.discr_ne_zero_iff_separable_map ℚ]
    rintro h
    exact (hf.separable_map_zmod_iff_not_dvd_discr p).mp
      (PerfectField.separable_iff_squarefree.mpr hsq) (h ▸ dvd_zero _)
  -- The splitting field, a prime above `p` and a Frobenius at it.
  set M := g.SplittingField
  have : IsGalois ℚ M := IsGalois.of_separable_splitting_field hsep
  have : Fact (g.map (algebraMap ℚ M)).Splits := ⟨SplittingField.splits g⟩
  have hpprime : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp Fact.out)
  obtain ⟨⟨Q, hQ, hQo⟩⟩ := (Ideal.span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 M)
  obtain ⟨σ, hσ⟩ := _root_.NumberField.exists_isArithFrobAt_int_of_liesOver (p := p) Q
  refine ⟨Gal.restrict g M σ, ?_⟩
  -- Transport the permutation from the splitting field to `E`.
  have hperm : Gal.galActionHom g E (Gal.restrict g M σ) =
      (Gal.rootsEquivRoots g M E).permCongr (Gal.galActionHom g M (Gal.restrict g M σ)) := by
    ext x
    rw [Equiv.permCongr_apply]
    change ((Gal.restrict g M σ • x : g.rootSet E) : E) = ((Gal.rootsEquivRoots g M E
      (Gal.restrict g M σ • (Gal.rootsEquivRoots g M E).symm x) : g.rootSet E) : E)
    rw [← Gal.smul_rootsEquivRoots, Equiv.apply_symm_apply]
  rw [hperm, Equiv.Perm.fullCycleType_permCongr]
  exact fullCycleType_galActionHom_restrict_eq_map_natDegree_normalizedFactors hf hsq Q hσ

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ in
/-- **Dedekind's theorem**, in the form consumed by the polynomial Galois groups roadmap. Let `f`
be a monic integer polynomial and `p` a prime not dividing its discriminant. Then the Galois
group of `f` contains an element whose cycle type on the complex roots of `f`, completed by one
part `1` for each fixed root, is the multiset of degrees of the irreducible factors of `f`
modulo `p`.

The completed cycle type is `Equiv.Perm.fullCycleType`; it is written out here because the
consumer's contract fixes this signature. -/
theorem exists_gal_fullCycleType_eq_factorizationType
    (f : ℤ[X]) (hf : f.Monic) (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ f.discr) :
    ∃ σ : (f.map (Int.castRingHom ℚ)).Gal,
      (Gal.galActionHom (f.map (Int.castRingHom ℚ)) ℂ σ).cycleType +
          Multiset.replicate (Fintype.card ((f.map (Int.castRingHom ℚ)).rootSet ℂ) -
            (Gal.galActionHom (f.map (Int.castRingHom ℚ)) ℂ σ).support.card) 1 =
        (normalizedFactors (f.map (Int.castRingHom (ZMod p)))).map natDegree := by
  obtain ⟨σ, hσ⟩ := exists_gal_fullCycleType_eq_map_natDegree_normalizedFactors f hf p
    (PerfectField.separable_iff_squarefree.mp
      ((hf.separable_map_zmod_iff_not_dvd_discr p).mpr hp)) ℂ
  refine ⟨σ, ?_⟩
  rw [Equiv.Perm.fullCycleType_def, Equiv.Perm.parts_partition] at hσ
  exact hσ

end TauCeti.NumberField
