/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.Topology.PureDimension
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import TauCeti.RingTheory.Catenary

/-!
# Krull dimension and heights under quotients

For an ideal `I` of a commutative ring `R`, the quotient map `R → R ⧸ I` identifies
`Spec (R ⧸ I)` homeomorphically with the closed subset `V(I)` of `Spec R`. So the topological Krull
dimension of `V(I)` is the Krull dimension of `R ⧸ I`.
Quotienting by the nilradical preserves the entire prime spectrum, hence its Krull dimension and
the height of each prime ideal. Conversely, quotients by nonzero principal ideals bound the Krull
dimension from above: the second prime of a chain contains a nonzero element, and the rest of the
chain lies over it. This is the upper-bound step of dimension counts by induction on the number of
variables.

Quotienting by a non-zero-divisor `r` lowers the height of every prime `p` containing `r` by at
least one: a chain of primes of `R ⧸ (r)` ending at the image of `p` pulls back to a chain ending
at `p` whose first prime contains `r`, hence is not minimal and extends by a minimal prime below
it. This is the height form of Mathlib's `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`, and
the lower-bound step of height counts by induction on the number of variables. In a noetherian
ring Krull's principal ideal theorem gives the reverse inequality, so the height drops by exactly
one.

Quotienting by an ideal `q ≤ p` does not increase the height of the prime `p`. If `p` has finite
height, a chain of primes of length `ht p` ending at `p` starts above some minimal prime `q`, and
it lies in the interval `[q, p]` of `Spec R`, whose dimension is `ht (p ⧸ q)`; so the height of
`p` is attained on an irreducible component of `Spec R` through `p`.

The spectrum of a ring is pure-dimensional of dimension `d` exactly when every quotient by a
minimal prime has Krull dimension `d`: the irreducible components are the closed subsets `V(P)`
for minimal primes `P`. This gives a componentwise criterion using only quotient dimensions.

## Main results

* `Ideal.topologicalKrullDim_zeroLocus`: the closed subset `V(I)` of `Spec R` has the Krull
  dimension of `R ⧸ I`.
* `TauCeti.isPureDimensional_primeSpectrum_iff`: the spectrum is pure-dimensional exactly when
  every minimal-prime quotient has the prescribed dimension.
* `TauCeti.ringKrullDim_quotient_nilradical`: reduction preserves Krull dimension.
* `TauCeti.ringKrullDim_le_add_one_of_forall_ringKrullDim_quotient_le`: if every quotient by a
  nonzero principal ideal has Krull dimension at most `n`, the ring has Krull dimension at most
  `n + 1`.
* `TauCeti.ringKrullDim_quotient_add_one_le_of_lt`: for a prime `p` strictly contained in an ideal
  `q`, `ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p)`.
* `Ideal.height_map_quotientMk_nilradical`: reduction preserves the height of a prime ideal.
* `Ideal.height_map_quotientMk_span_singleton_add_one`: in a noetherian ring, quotienting by a
  non-zero-divisor in a prime `p` lowers the height of `p` by one.
* `Ideal.height_map_quotientMk_le`: quotienting by an ideal contained in a prime `p` does not
  increase the height of `p`.
* `Ideal.exists_mem_minimalPrimes_height_map_quotientMk_eq`: a prime `p` of finite height has the
  height of its image modulo some minimal prime `q ≤ p`.
-/

public section

namespace Ideal

open PrimeSpectrum

variable {R : Type*} [CommRing R]

/-- The closed subset `V(I)` of `Spec R` has the Krull dimension of `R ⧸ I`. -/
@[simp]
theorem topologicalKrullDim_zeroLocus (I : Ideal R) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set R)) = ringKrullDim (R ⧸ I) := by
  have hi := isClosedEmbedding_comap_of_surjective _ _ (Quotient.mk_surjective (I := I))
  have hrange :
      Set.range (PrimeSpectrum.comap (Quotient.mk I)) = PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [range_comap_of_surjective _ _ Quotient.mk_surjective, mk_ker]
  rw [← topologicalKrullDim_eq_ringKrullDim]
  exact ((hi.isEmbedding.toHomeomorph).trans (Homeomorph.setCongr hrange)).symm.isHomeomorph
    |>.topologicalKrullDim_eq

end Ideal

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- The spectrum of a ring `R` is pure-dimensional of dimension `d` if and only if `R ⧸ P` has
Krull dimension `d` for every minimal prime `P` of `R`. -/
theorem isPureDimensional_primeSpectrum_iff {d : ℕ} :
    IsPureDimensional d (PrimeSpectrum R) ↔ ∀ P ∈ minimalPrimes R, ringKrullDim (R ⧸ P) = d := by
  simp_rw [isPureDimensional_iff, ← PrimeSpectrum.zeroLocus_minimalPrimes, Set.forall_mem_image,
    Function.comp_apply, Ideal.topologicalKrullDim_zeroLocus]

variable (R)

/-- Passing to the quotient by the nilradical preserves Krull dimension. -/
@[simp]
theorem ringKrullDim_quotient_nilradical :
    ringKrullDim (R ⧸ nilradical R) = ringKrullDim R := by
  rw [ringKrullDim_quotient, PrimeSpectrum.zeroLocus_nilradical, ringKrullDim]
  exact Order.krullDim_eq_of_orderIso OrderIso.Set.univ

variable {R}

/-- If the quotient of `R` by every nonzero principal ideal has Krull dimension at most `n`, then
`R` has Krull dimension at most `n + 1`. -/
theorem ringKrullDim_le_add_one_of_forall_ringKrullDim_quotient_le {n : ℕ∞}
    (h : ∀ f : R, f ≠ 0 → ringKrullDim (R ⧸ Ideal.span {f}) ≤ n) :
    ringKrullDim R ≤ n + 1 := by
  refine iSup_le fun l ↦ ?_
  obtain hl | hl := eq_or_ne l.length 0
  · rw [hl, Nat.cast_zero]
    exact_mod_cast (zero_le : (0 : ℕ∞) ≤ n + 1)
  -- The second prime `l 1` contains some `f ∉ l 0`; then `f ≠ 0`, and the tail of `l` is a
  -- chain in `V(f)`.
  let t : LTSeries (PrimeSpectrum R) := l.tail hl
  have h₀₁ : l.head.asIdeal < t.head.asIdeal := by
    rw [PrimeSpectrum.asIdeal_lt_asIdeal, RelSeries.head_tail, ← RelSeries.apply_zero]
    exact l.strictMono (Fin.pos_iff_ne_zero.mpr (by simpa [Fin.ext_iff] using hl))
  obtain ⟨f, hf₁, hf₀⟩ := IsConcreteLE.exists_of_lt h₀₁
  have hf : f ≠ 0 := by
    rintro rfl
    exact hf₀ (zero_mem _)
  let q : LTSeries (PrimeSpectrum.zeroLocus (R := R) (Ideal.span {f})) :=
    .mk t.length (fun i ↦ ⟨t i, by
      rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem]
      exact LTSeries.head_le t i hf₁⟩) fun _ _ hij ↦ Subtype.mk_lt_mk.mpr (t.strictMono hij)
  have hq : (t.length : WithBot ℕ∞) ≤ n := (Order.LTSeries.length_le_krullDim q).trans
    ((ringKrullDim_quotient _).symm.le.trans (h f hf))
  rw [show l.length = t.length + 1 by rw [RelSeries.tail_length]; omega]
  simpa using add_le_add_left hq 1

/-- If `p ⊊ q` with `p` prime, then `ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p)`. -/
theorem ringKrullDim_quotient_add_one_le_of_lt {p q : Ideal R} [p.IsPrime] (h : p < q) :
    ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨x, hxq, hxp⟩ := IsConcreteLE.exists_of_lt h
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor h.le)
    (Ideal.Quotient.factor_surjective h.le) (r := Ideal.Quotient.mk p x)
    (mem_nonZeroDivisors_of_ne_zero ?_) ?_
  · rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
  · rwa [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]

end TauCeti

namespace Ideal

variable {R : Type*} [CommRing R]

/-- Passing to the quotient by the nilradical preserves the height of a prime ideal. -/
@[simp]
theorem height_map_quotientMk_nilradical (p : Ideal R) [p.IsPrime] :
    (p.map (Ideal.Quotient.mk (nilradical R))).height = p.height := by
  let I : Ideal R := nilradical R
  let e : PrimeSpectrum (R ⧸ I) ≃o PrimeSpectrum R :=
    (I.primeSpectrumQuotientOrderIsoZeroLocus).trans
      ((Set.orderIsoOfEq _ _ PrimeSpectrum.zeroLocus_nilradical).trans OrderIso.Set.univ)
  have hIp : I ≤ p := nilradical_le_prime p
  let q : Ideal (R ⧸ I) := p.map (Ideal.Quotient.mk I)
  have : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa [Ideal.mk_ker] using hIp)
  have he : e ⟨q, inferInstance⟩ = (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    -- The composite `e` is definitionally contraction by `Quotient.mk I` on underlying ideals.
    -- Mathlib provides no apply lemma for this composite of the quotient-spectrum equivalence,
    -- `Set.orderIsoOfEq`, and `OrderIso.Set.univ`.
    change (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = p
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_of_le_left hIp
  calc
    q.height = Order.height (⟨q, inferInstance⟩ : PrimeSpectrum (R ⧸ I)) :=
      PrimeSpectrum.height_eq_orderHeight (⟨q, inferInstance⟩ : PrimeSpectrum (R ⧸ I))
    _ = Order.height (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
      rw [← he, Order.height_orderIso]
    _ = p.height :=
      (PrimeSpectrum.height_eq_orderHeight (⟨p, inferInstance⟩ : PrimeSpectrum R)).symm

open scoped nonZeroDivisors in
/-- Quotienting by a non-zero-divisor `r` in a prime `p` lowers the height of `p` by at least one.
The reverse inequality holds in noetherian rings, by Krull's principal ideal theorem; see
`Ideal.height_map_quotientMk_span_singleton_add_one`. -/
theorem height_map_quotientMk_span_singleton_add_one_le {r : R} (hr : r ∈ R⁰) (p : Ideal R)
    [p.IsPrime] (hrp : r ∈ p) : (p.map (Quotient.mk (span {r}))).height + 1 ≤ p.height := by
  have hle : span {r} ≤ p := (span_singleton_le_iff_mem p).mpr hrp
  have : (p.map (Quotient.mk (span {r}))).IsPrime := isPrime_map_quotientMk_of_isPrime hle
  let q : PrimeSpectrum (R ⧸ span {r}) := ⟨_, this⟩
  let P : PrimeSpectrum R := ⟨p, ‹_›⟩
  -- A chain ending at `q` pulls back to a chain ending at `p` whose head contains `r`; since
  -- `r` lies in no minimal prime, a minimal prime strictly below the head extends it by one.
  have key (l : LTSeries (PrimeSpectrum (R ⧸ span {r}))) (hl : l.last = q) :
      ∃ l' : LTSeries (PrimeSpectrum R), l'.last = P ∧ l'.length = l.length + 1 := by
    let l₁ := l.map (PrimeSpectrum.comap (Quotient.mk (span {r})))
      (RingHom.strictMono_comap_of_surjective Quotient.mk_surjective)
    obtain ⟨m, hm, hm'⟩ := exists_minimalPrimes_le (J := l₁.head.asIdeal) bot_le
    have hlt : (⟨m, hm.1.1⟩ : PrimeSpectrum R) < l₁.head := by
      refine lt_of_le_of_ne hm' fun h ↦ Set.disjoint_iff.mp
        (disjoint_nonZeroDivisors_of_mem_minimalPrimes hm) ⟨?_, hr⟩
      have : r ∈ l₁.head.asIdeal := by simp [l₁, PrimeSpectrum.comap_asIdeal]
      simpa [← h] using this
    refine ⟨l₁.cons _ hlt, ?_, by simp [l₁]⟩
    rw [RelSeries.last_cons]
    ext1
    simp [l₁, hl, q, P, comap_map_mk hle]
  rw [P.height_eq_orderHeight, q.height_eq_orderHeight]
  cases h : Order.height q using ENat.recTopCoe with
  | top =>
    rw [top_add, top_le_iff, Order.height_eq_top_iff]
    intro n
    rcases n with _ | n
    · exact ⟨RelSeries.singleton _ P, rfl, rfl⟩
    · obtain ⟨l, hl, hn⟩ := Order.height_eq_top_iff.mp h n
      obtain ⟨l', hl', hn'⟩ := key l hl
      exact ⟨l', hl', hn' ▸ hn ▸ rfl⟩
  | coe n =>
    obtain ⟨l, hl, hn⟩ := Order.exists_series_of_height_eq_coe q h
    obtain ⟨l', hl', hn'⟩ := key l hl
    have := Order.length_le_height_last (p := l')
    rw [hl', hn', hn] at this
    exact_mod_cast this

open scoped nonZeroDivisors in
/-- In a noetherian ring, quotienting by a non-zero-divisor `r` in a prime `p` lowers the height of
`p` by exactly one. -/
theorem height_map_quotientMk_span_singleton_add_one [IsNoetherianRing R] {r : R} (hr : r ∈ R⁰)
    (p : Ideal R) [p.IsPrime] (hrp : r ∈ p) :
    (p.map (Quotient.mk (span {r}))).height + 1 = p.height :=
  (height_map_quotientMk_span_singleton_add_one_le hr p hrp).antisymm
    (height_le_height_add_one_of_mem hrp)

/-- Passing to the quotient by an ideal `q ≤ p` does not increase the height of the prime `p`: a
chain of primes of `R ⧸ q` ending at the image of `p` pulls back to a chain ending at `p`. -/
theorem height_map_quotientMk_le {p q : Ideal R} [p.IsPrime] (hqp : q ≤ p) :
    (p.map (Quotient.mk q)).height ≤ p.height := by
  have : (p.map (Quotient.mk q)).IsPrime := isPrime_map_quotientMk_of_isPrime hqp
  let P : PrimeSpectrum (R ⧸ q) := ⟨_, this⟩
  have hP : PrimeSpectrum.comap (Quotient.mk q) P = (⟨p, ‹_›⟩ : PrimeSpectrum R) :=
    PrimeSpectrum.ext (comap_map_mk hqp)
  calc (p.map (Quotient.mk q)).height = Order.height P := P.height_eq_orderHeight
    _ ≤ Order.height (PrimeSpectrum.comap (Quotient.mk q) P) :=
        Order.height_le_height_apply_of_strictMono _
          (RingHom.strictMono_comap_of_surjective Quotient.mk_surjective) P
    _ = p.height := by rw [hP]; exact (PrimeSpectrum.height_eq_orderHeight _).symm

/-- If the prime `p` has finite height, then some minimal prime `q ≤ p` satisfies
`ht (p ⧸ q) = ht p`: the height of `p` is attained on an irreducible component of `Spec R`
through `p`. -/
theorem exists_mem_minimalPrimes_height_map_quotientMk_eq (p : Ideal R) [p.IsPrime]
    [p.FiniteHeight] :
    ∃ q ∈ minimalPrimes R, q ≤ p ∧ (p.map (Quotient.mk q)).height = p.height := by
  -- Take a chain of length `ht p` ending at `p` and a minimal prime below its first prime.
  obtain ⟨l, hl, hlen⟩ := p.exists_ltSeries_length_eq_height
  obtain ⟨q, hq, hqh⟩ := exists_minimalPrimes_le (J := l.head.asIdeal) bot_le
  let Q : PrimeSpectrum R := ⟨q, hq.1.1⟩
  have hQ : Q ≤ l.head := hqh
  have hQP : Q ≤ ⟨p, ‹_›⟩ := hl ▸ hQ.trans l.head_le_last
  refine ⟨q, hq, hQP, (height_map_quotientMk_le hQP).antisymm ?_⟩
  -- The chain `l` lies in the interval `[q, p]` of `Spec R`, whose dimension is `ht (p ⧸ q)`.
  let l' : LTSeries (Set.Icc Q ⟨p, ‹_›⟩) :=
    .mk l.length (fun i ↦ ⟨l i, hQ.trans (l.head_le i), hl ▸ l.monotone (Fin.le_last i)⟩)
      fun _ _ hij ↦ Subtype.mk_lt_mk.mpr (l.strictMono hij)
  rw [← hlen, ← WithBot.coe_le_coe, ← PrimeSpectrum.krullDim_Icc hQP]
  exact Order.LTSeries.length_le_krullDim l'

end Ideal
