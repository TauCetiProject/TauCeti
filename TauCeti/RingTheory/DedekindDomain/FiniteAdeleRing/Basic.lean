/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Algebra
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Approximation

/-!
# The finite adele ring: separation, integral elements, and strong approximation

Mathlib's `IsDedekindDomain.FiniteAdeleRing R K` is the restricted product of the completions
`v.adicCompletion K` over the height one primes `v` of a Dedekind domain `R` with fraction field
`K`, with respect to the integer rings `v.adicCompletionIntegers K`.  This file records basic facts
about it that are not stated in Mathlib:

* the finite adele ring is Hausdorff, since each completion is;
* subtraction, multiplication, and the multiplicative unit are computed place by place;
* the product of the local integer rings embeds continuously as the integral finite adeles;
* an element of `K` is integral at every finite place exactly when it lies in `R`, so the integral
  finite adeles meet the diagonal copy of `K` in `R`;
* **strong approximation**: `K` is dense in the finite adele ring.

The third fact is the finite half of the discreteness of a number field in its adele ring.  The
fourth says that an element of `K` can be made close to a given finite adele `a` at finitely many
places while differing from `a` by an integral element at every other place.  Since the integral
finite adeles are open, it implies that `K` and the integral finite adeles together span the finite
adele ring additively.  For a number field the infinite places are what is omitted here: `K` is
discrete, not dense, in the full adele ring.

The proof clears denominators: a finite adele `a` has a common denominator `d ∈ R`, and the
integral adele `a * d` is approximated by an element `r ∈ R` at finitely many places by the Chinese
remainder theorem, with enough extra precision at the primes dividing `d` that `r / d`
approximates `a`.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.integralEmbedding`: the continuous embedding of the product of
  the local integer rings into the finite adeles.
* `IsDedekindDomain.FiniteAdeleRing.one_apply`, `sub_apply`, and `mul_apply`: the corresponding
  operations are computed place by place.
* `IsDedekindDomain.FiniteAdeleRing.forall_algebraMap_mem_adicCompletionIntegers_iff`: the diagonal
  image of `x : K` is integral at every finite place if and only if `x` lies in `R`.
* `IsDedekindDomain.FiniteAdeleRing.mul_nonZeroDivisor_mem_adicCompletionIntegers`: a finite adele
  has a common denominator in `R`.
* `IsDedekindDomain.FiniteAdeleRing.exists_forall_valued_sub_le_and_forall_valued_sub_le_one`:
  strong approximation with explicit precision at finitely many places and integrality everywhere.
* `IsDedekindDomain.FiniteAdeleRing.denseRange_algebraMap`: `K` is dense in the finite adele ring.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §§14–15.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §3 (the Chinese remainder theorem).
-/

public section

namespace IsDedekindDomain.FiniteAdeleRing

open HeightOneSpectrum

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

instance : T2Space (FiniteAdeleRing R K) :=
  inferInstanceAs <| T2Space <|
    RestrictedProduct (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
      (fun v ↦ v.adicCompletionIntegers K) Filter.cofinite

variable {R K}

-- `FiniteAdeleRing R K` is a `def` wrapping the restricted product, so
-- the corresponding `RestrictedProduct` lemmas do not apply to it directly;
-- these are their restatements, and like them they hold by `rfl`.
/-- The value of `1 : 𝔸ᶠ[R, K]` at a finite place is `1`. -/
@[simp] theorem one_apply (v : HeightOneSpectrum R) : (1 : FiniteAdeleRing R K) v = 1 := rfl

/-- Subtraction of finite adeles is computed place by place. -/
@[simp] theorem sub_apply (a b : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (a - b) v = a v - b v := rfl

/-- Multiplication of finite adeles is computed place by place. -/
@[simp] theorem mul_apply (a b : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (a * b) v = a v * b v := rfl

/-- The product of the local integer rings embedded continuously in the finite adele ring. Its
range is the set of finite adeles integral at every finite place. -/
noncomputable def integralEmbedding :
    (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) →A[ℤ] FiniteAdeleRing R K where
  toFun := RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
    (fun v ↦ (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  cont := RestrictedProduct.isEmbedding_structureMap.continuous

/-- The integral embedding is evaluated place by place. -/
@[simp]
theorem integralEmbedding_apply
    (x : ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) (v : HeightOneSpectrum R) :
    integralEmbedding (R := R) (K := K) x v = x v :=
  RestrictedProduct.structureMap_apply _ _ v

/-- The product of the local integer rings embeds into the finite adele ring. -/
theorem isEmbedding_integralEmbedding :
    Topology.IsEmbedding (integralEmbedding (R := R) (K := K)) :=
  RestrictedProduct.isEmbedding_structureMap

/-- The embedding of the product of the local integer rings into the finite adeles is continuous. -/
@[continuity, fun_prop]
theorem continuous_integralEmbedding :
    Continuous (integralEmbedding (R := R) (K := K)) :=
  map_continuous (integralEmbedding (R := R) (K := K))

/-- The range of the integral embedding is the set of finite adeles integral at every place. -/
theorem range_integralEmbedding :
    Set.range (integralEmbedding (R := R) (K := K)) =
      {a : FiniteAdeleRing R K | ∀ v, a v ∈ v.adicCompletionIntegers K} := by
  exact RestrictedProduct.range_structureMap _ _

/-- The integral finite adeles are compact when every local integer ring is compact. -/
theorem isCompact_integralFiniteAdeles
    [∀ v : HeightOneSpectrum R, CompactSpace (v.adicCompletionIntegers K)] :
    IsCompact {a : FiniteAdeleRing R K | ∀ v, a v ∈ v.adicCompletionIntegers K} := by
  rw [← range_integralEmbedding]
  exact isCompact_range (continuous_integralEmbedding (R := R) (K := K))

/-- The diagonal image of an element of `K` in the finite adele ring is integral at every finite
place exactly when the element lies in `R`. -/
theorem forall_algebraMap_mem_adicCompletionIntegers_iff (x : K) :
    (∀ v : HeightOneSpectrum R,
        algebraMap K (FiniteAdeleRing R K) x v ∈ v.adicCompletionIntegers K) ↔
      x ∈ (algebraMap R K).range := by
  simp only [algebraMap_apply, mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation']
  refine ⟨mem_integers_of_valuation_le_one K x, ?_⟩
  rintro ⟨r, rfl⟩ v
  exact v.valuation_le_one r

end IsDedekindDomain.FiniteAdeleRing

/-! ### Strong approximation -/

namespace IsDedekindDomain

open HeightOneSpectrum WithZero Topology

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

namespace FiniteAdeleRing

/-- **A finite adele has a common denominator**: some nonzero divisor `b` of `R` makes `a * b`
integral at every place. -/
theorem mul_nonZeroDivisor_mem_adicCompletionIntegers (a : FiniteAdeleRing R K) :
    ∃ b ∈ nonZeroDivisors R,
      ∀ v, a v * algebraMap R (v.adicCompletion K) b ∈ v.adicCompletionIntegers K := by
  classical
  -- `a` is integral outside a finite set of places, and each of those has its own denominator
  have hT : {v | a v ∉ v.adicCompletionIntegers K}.Finite := Filter.eventually_cofinite.mp a.2
  choose b hb0 hb using fun v ↦
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
  refine ⟨∏ v ∈ hT.toFinset, b v, prod_mem fun v _ ↦ hb0 v, fun v ↦ ?_⟩
  by_cases hv : v ∈ hT.toFinset
  · rw [← Finset.mul_prod_erase _ _ hv, map_mul, ← mul_assoc]
    exact mul_mem (hb v) (v.coe_mem_adicCompletionIntegers _)
  · exact mul_mem (by simpa using hv) (v.coe_mem_adicCompletionIntegers _)

/-- **Strong approximation for the finite adeles, in explicit form.** Every finite adele `a` is
approximated by an element `x` of `K` to any prescribed precision at finitely many places, while
`x - a` is integral at every place. -/
theorem exists_forall_valued_sub_le_and_forall_valued_sub_le_one (a : FiniteAdeleRing R K)
    (s : Finset (HeightOneSpectrum R))
    (n : HeightOneSpectrum R → ℕ) :
    ∃ x : K, (∀ v ∈ s, Valued.v (algebraMap K (v.adicCompletion K) x - a v) ≤ exp (-(n v : ℤ))) ∧
      ∀ v, Valued.v (algebraMap K (v.adicCompletion K) x - a v) ≤ 1 := by
  classical
  -- `a` has a common denominator `d`
  obtain ⟨d, hd0, hda⟩ := mul_nonZeroDivisor_mem_adicCompletionIntegers a
  replace hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd0
  -- `d` is a unit outside the finite set `D` of primes dividing it
  have hD : {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  set N : HeightOneSpectrum R → ℕ := fun v ↦ multiplicity v.asIdeal (Ideal.span {d})
  have hvd (v : HeightOneSpectrum R) :
      Valued.v (algebraMap R (v.adicCompletion K) d) = exp (-(N v : ℤ)) := by
    rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap,
      v.intValuation_eq_exp_neg_multiplicity hd0]
  -- approximate `a * d` by `r ∈ R` on `s ∪ D`, with the extra precision `N` absorbing `d`
  obtain ⟨r, hr⟩ := HeightOneSpectrum.exists_forall_valued_sub_le (s ∪ hD.toFinset)
    (fun v ↦ ⟨a v * algebraMap R (v.adicCompletion K) d, hda v⟩) (fun v ↦ n v + N v)
  refine ⟨algebraMap R K r / algebraMap R K d, ?_⟩
  have key (v : HeightOneSpectrum R) :
      Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r / algebraMap R K d) - a v) *
        exp (-(N v : ℤ)) =
      Valued.v (a v * algebraMap R (v.adicCompletion K) d -
        algebraMap R (v.adicCompletion K) r) := by
    have hd : algebraMap R (v.adicCompletion K) d ≠ 0 := fun h ↦
      exp_ne_zero (by rw [← hvd v, h, map_zero])
    rw [← hvd v, ← map_mul, map_div₀, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, sub_mul, div_mul_cancel₀ _ hd, Valuation.map_sub_swap]
  have hS : ∀ v ∈ s ∪ hD.toFinset,
      Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r / algebraMap R K d) - a v) ≤
        exp (-(n v : ℤ)) := fun v hv ↦ by
    have hrv := hr v hv
    rw [← key v, Nat.cast_add, neg_add, exp_add] at hrv
    exact le_of_mul_le_mul_right hrv exp_pos
  refine ⟨fun v hv ↦ hS v (Finset.mem_union_left _ hv), fun v ↦ ?_⟩
  by_cases hv : v ∈ s ∪ hD.toFinset
  · exact (hS v hv).trans (exp_le_one_iff.mpr (by omega))
  · have hN : N v = 0 := multiplicity_eq_zero_of_not_dvd fun h ↦
      hv (Finset.mem_union_right _ (hD.mem_toFinset.mpr h))
    have hkey := key v
    rw [hN, Nat.cast_zero, neg_zero, exp_zero, mul_one] at hkey
    rw [hkey]
    exact Valuation.map_sub_le _ (hda v) (v.coe_mem_adicCompletionIntegers r)

/-- Every finite adele differs from a diagonal element by an integral finite adele. -/
theorem exists_forall_sub_algebraMap_mem_adicCompletionIntegers (a : FiniteAdeleRing R K) :
    ∃ x : K, ∀ v, a v - algebraMap K (v.adicCompletion K) x ∈
      v.adicCompletionIntegers K := by
  obtain ⟨x, -, hx⟩ :=
    exists_forall_valued_sub_le_and_forall_valued_sub_le_one a ∅ (fun _ ↦ 0)
  refine ⟨x, fun v ↦ ?_⟩
  have hxa : algebraMap K (v.adicCompletion K) x - a v ∈
      v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers]
    exact hx v
  simpa only [neg_sub] using neg_mem hxa

/-- **Every neighbourhood of `0` in the finite adele ring contains a basic congruence
neighbourhood.**  There are a finite set `I` of places and exponents `n` such that every finite
adele integral at every place, with `v`-adic valuation at most `exp (-n v)` at each `v ∈ I`, lies in
the neighbourhood. -/
theorem exists_finset_forall_mem_of_mem_nhds_zero {U : Set (FiniteAdeleRing R K)} (hU : U ∈ 𝓝 0) :
    ∃ (I : Finset (HeightOneSpectrum R)) (n : HeightOneSpectrum R → ℕ),
      ∀ a : FiniteAdeleRing R K, (∀ v, a v ∈ v.adicCompletionIntegers K) →
        (∀ v ∈ I, Valued.v (a v) ≤ exp (-(n v : ℤ))) → a ∈ U := by
  have hopen (v : HeightOneSpectrum R) :
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Valued.isOpen_valuationSubring _
  -- `FiniteAdeleRing R K` is by definition the restricted product, so its neighbourhoods of `0`
  -- are images of neighbourhoods of `0` in the product of the `𝒪_v`
  have hU1 : integralEmbedding (R := R) (K := K) ⁻¹' U ∈ 𝓝 0 :=
    (RestrictedProduct.nhds_zero_eq_map_structureMap (fun v : HeightOneSpectrum R ↦
      v.adicCompletion K) (B := fun v ↦ v.adicCompletionIntegers K) hopen).ge hU
  rw [nhds_pi, Filter.mem_pi] at hU1
  obtain ⟨I, hI, t, ht, hIt⟩ := hU1
  choose n hn using fun v ↦ exists_maximalIdeal_pow_subset_of_mem_nhds v (ht v)
  refine ⟨hI.toFinset, n, fun a ha hav ↦ ?_⟩
  let w : ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K := fun v ↦ ⟨a v, ha v⟩
  have hw : w ∈ I.pi t := fun v hv ↦
    hn v ((mem_maximalIdeal_pow_iff v).mpr (hav v (hI.mem_toFinset.mpr hv)))
  have heq : integralEmbedding (R := R) (K := K) w = a := by
    apply RestrictedProduct.ext
    intro v
    exact integralEmbedding_apply w v
  rw [← heq]
  exact hIt hw

variable (R K) in
/-- **Strong approximation**: `K` is dense in the finite adele ring of `R`. -/
theorem denseRange_algebraMap : DenseRange (algebraMap K (FiniteAdeleRing R K)) := by
  intro a
  refine mem_closure_iff_nhds.mpr fun U hU ↦ ?_
  -- translate to a neighbourhood of `0`, which contains a basic congruence neighbourhood
  have hU0 : (a + ·) ⁻¹' U ∈ 𝓝 (0 : FiniteAdeleRing R K) :=
    (continuous_const_add a).continuousAt.preimage_mem_nhds (by rwa [add_zero])
  obtain ⟨I, n, hIn⟩ := exists_finset_forall_mem_of_mem_nhds_zero hU0
  obtain ⟨x, hxI, hx⟩ := exists_forall_valued_sub_le_and_forall_valued_sub_le_one a I n
  refine ⟨algebraMap K _ x, ?_, x, rfl⟩
  have h := hIn (algebraMap K (FiniteAdeleRing R K) x - a)
    (fun v ↦ by rw [mem_adicCompletionIntegers, sub_apply, algebraMap_apply]; exact hx v)
    (fun v hv ↦ by rw [sub_apply, algebraMap_apply]; exact hxI v hv)
  rwa [Set.mem_preimage, add_sub_cancel] at h

end FiniteAdeleRing

end IsDedekindDomain
