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
* `Ideal.height_map_quotientMk_nilradical`: reduction preserves the height of a prime ideal.
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

end Ideal
