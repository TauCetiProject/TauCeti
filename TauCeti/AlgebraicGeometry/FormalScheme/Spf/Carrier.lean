/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Spectrum.Prime.Topology
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology

import TauCeti.Topology.Homeomorph.SetCongr

/-!
# The underlying space of the formal spectrum

Let `A` be a topological ring. The underlying space of the formal spectrum `Spf A` is the set of
open prime ideals of `A`, with the subspace topology of `Spec A` (EGA I, Ch. I, 10.1.1–10.1.2).
The structure sheaf of `Spf A` is a sheaf on this space: the limit of the structure sheaves of
the spectra `Spec (A ⧸ I ^ (n + 1))`, transported along the homeomorphisms below.

If an ideal `I` defines the topology of `A`, a prime ideal is open exactly when it contains `I`,
so the underlying space is the Zariski closed set `V(I)`, and the quotient map `A → A ⧸ J`
identifies it with `Spec (A ⧸ J)` for every ideal of definition `J`, in particular for every power
`I ^ (n + 1)`. Since the set of open primes is defined from the topology alone, it does not depend
on the choice of an ideal of definition.

For `f ∈ A`, the basic open set `D(f)` of `Spf A` consists of the open primes not containing `f`.
These form a basis of the topology; `D(g) ⊆ D(f)` holds exactly when `g` lies in the radical of
`f A + I`, which is the condition under which the completed localisations of an adic ring have a
restriction map `A_{f} → A_{g}` (`TauCeti.AdicRing.CompletedAway.restrict`), and `D(f)` is empty
exactly when `f` is nilpotent modulo `I`.

## Main definitions

* `TauCeti.FormalScheme.Spf.carrier A`: the open prime ideals of `A`, as a subset of `Spec A`.
* `TauCeti.FormalScheme.Spf.homeomorphSpecQuotient`: for an ideal of definition `J`, the
  homeomorphism of the underlying space of `Spf A` with `Spec (A ⧸ J)`.
* `TauCeti.FormalScheme.Spf.basicOpen f`: the basic open set `D(f)` of the underlying space.
* `TauCeti.FormalScheme.Spf.comap`: the continuous map of underlying spaces induced by a
  continuous ring homomorphism.

## Main results

* `TauCeti.FormalScheme.Spf.mem_carrier_iff_le`: for an ideal of definition `I`, a prime is open
  if and only if it contains `I`.
* `TauCeti.FormalScheme.Spf.carrier_eq_zeroLocus`, `TauCeti.FormalScheme.Spf.isClosed_carrier`:
  the underlying space is the Zariski closed set `V(I)`.
* `TauCeti.FormalScheme.Spf.carrier_eq_empty_iff_subsingleton`: the formal spectrum of a
  separated ring with an ideal of definition is empty exactly when the ring is zero.
* `TauCeti.FormalScheme.Spf.isBasis_basicOpen`: the basic open sets form a basis.
* `TauCeti.FormalScheme.Spf.basicOpen_le_basicOpen_iff`: `D(g) ⊆ D(f)` if and only if `g` lies
  in the radical of `f A + I`.
* `TauCeti.FormalScheme.Spf.basicOpen_eq_bot_iff`: `D(f)` is empty if and only if `f` lies in
  the radical of `I`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, §10.1
  (10.1.1, 10.1.2) and §10.2 (10.2.1).
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open TopologicalSpace Topology PrimeSpectrum

namespace TauCeti.FormalScheme.Spf

variable (A : Type*) [CommRing A] [TopologicalSpace A]

/-- The underlying set of the formal spectrum `Spf A`: the prime ideals of `A` that are open. It
carries the subspace topology of `Spec A`. -/
def carrier : Set (PrimeSpectrum A) :=
  {p | IsOpen (p.asIdeal : Set A)}

variable {A}

@[simp]
theorem mem_carrier {p : PrimeSpectrum A} : p ∈ carrier A ↔ IsOpen (p.asIdeal : Set A) :=
  Iff.rfl

variable {I J : Ideal A}

/-- If `I` defines the topology of `A`, a prime ideal of `A` is open if and only if it contains
`I`. -/
theorem mem_carrier_iff_le (hI : IsAdic I) {p : PrimeSpectrum A} :
    p ∈ carrier A ↔ I ≤ p.asIdeal :=
  hI.isOpen_iff_le_of_isRadical p.isPrime.isRadical

/-- If `I` defines the topology of `A`, the underlying set of `Spf A` is the zero locus `V(I)`.
In particular it is the same for all ideals of definition. -/
theorem carrier_eq_zeroLocus (hI : IsAdic I) : carrier A = zeroLocus I := by
  ext p
  rw [mem_carrier_iff_le hI, mem_zeroLocus, SetLike.coe_subset_coe]

/-- The underlying set of the formal spectrum is Zariski closed in `Spec A`. -/
theorem isClosed_carrier (hI : IsAdic I) : IsClosed (carrier A) :=
  carrier_eq_zeroLocus hI ▸ isClosed_zeroLocus _

/-- For a discrete ring every prime is open, so the formal spectrum has the same points as the
spectrum. -/
@[simp]
theorem carrier_eq_univ [DiscreteTopology A] : carrier A = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ isOpen_discrete _

/-- The formal spectrum is empty if and only if an ideal of definition is the unit ideal. -/
theorem carrier_eq_empty_iff (hI : IsAdic I) : carrier A = ∅ ↔ I = ⊤ := by
  rw [carrier_eq_zeroLocus hI, zeroLocus_empty_iff_eq_top]

/-- If `I` defines the topology of `A` and `A` is separated, the formal spectrum is empty if and
only if `A` is zero: if `I` is the unit ideal, every neighbourhood of `0` is all of `A`, so
separation forces `A` to be zero. -/
theorem carrier_eq_empty_iff_subsingleton [T1Space A] (hI : IsAdic I) :
    carrier A = ∅ ↔ Subsingleton A := by
  rw [carrier_eq_empty_iff hI]
  refine ⟨fun h ↦ ⟨fun a b ↦ ?_⟩, fun _ ↦ Subsingleton.elim _ _⟩
  have hnhds (x : A) : x = 0 := by
    by_contra hx
    obtain ⟨n, -, hn⟩ := hI.hasBasis_nhds_zero.mem_iff.mp (isOpen_ne.mem_nhds (Ne.symm hx))
    exact hn (by simp [h, Ideal.top_pow]) rfl
  rw [hnhds a, hnhds b]

/-- If `I` defines the topology of `A` and `A` is separated and nonzero, the formal spectrum is
nonempty. -/
theorem carrier_nonempty [T1Space A] [Nontrivial A] (hI : IsAdic I) : (carrier A).Nonempty :=
  Set.nonempty_iff_ne_empty.mpr fun h ↦
    not_subsingleton A ((carrier_eq_empty_iff_subsingleton hI).mp h)

section Quotient

/-- For an ideal of definition `J` of `A`, the quotient map `A → A ⧸ J` identifies the underlying
space of `Spf A` with `Spec (A ⧸ J)` (EGA I, Ch. I, 10.1.2). For an ideal of definition `I`, this
applies to every power `J = I ^ (n + 1)`, by `is_ideal_adic_pow`. The inverse sends a prime of
`A ⧸ J` to its preimage in `A`. -/
noncomputable def homeomorphSpecQuotient (hJ : IsAdic J) :
    carrier A ≃ₜ PrimeSpectrum (A ⧸ J) :=
  (Homeomorph.setCongr (carrier_eq_zeroLocus hJ)).trans (quotientHomeomorphZeroLocus J).symm

/-- The inverse of `homeomorphSpecQuotient` sends a prime of `A ⧸ J` to its preimage in `A`. -/
@[simp]
theorem coe_homeomorphSpecQuotient_symm_apply (hJ : IsAdic J) (q : PrimeSpectrum (A ⧸ J)) :
    ((homeomorphSpecQuotient hJ).symm q : PrimeSpectrum A) =
      PrimeSpectrum.comap (Ideal.Quotient.mk J) q := by
  simp [homeomorphSpecQuotient]

/-- `homeomorphSpecQuotient` sends an open prime of `A` to its image in `A ⧸ J`. -/
@[simp]
theorem homeomorphSpecQuotient_apply_asIdeal (hJ : IsAdic J) (p : carrier A) :
    (homeomorphSpecQuotient hJ p).asIdeal = (p : PrimeSpectrum A).asIdeal.map
      (Ideal.Quotient.mk J) := by
  conv_rhs => rw [← (homeomorphSpecQuotient hJ).symm_apply_apply p]
  rw [coe_homeomorphSpecQuotient_symm_apply, comap_asIdeal,
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

/-- The identifications of `Spf A` with the spectra of two quotients `A ⧸ J` and `A ⧸ K`, for
ideals of definition `J ≤ K`, are compatible with the closed immersion
`Spec (A ⧸ K) → Spec (A ⧸ J)`. -/
theorem homeomorphSpecQuotient_symm_comap_factor (hJ : IsAdic J) {K : Ideal A} (hK : IsAdic K)
    (hJK : J ≤ K) (q : PrimeSpectrum (A ⧸ K)) :
    (homeomorphSpecQuotient hJ).symm (PrimeSpectrum.comap (Ideal.Quotient.factor hJK) q) =
      (homeomorphSpecQuotient hK).symm q := by
  ext1
  rw [coe_homeomorphSpecQuotient_symm_apply, coe_homeomorphSpecQuotient_symm_apply,
    ← comap_comp_apply, Ideal.Quotient.factor_comp_mk]

end Quotient

section BasicOpen

/-- The basic open set `D(f)` of the underlying space of `Spf A`: the open primes of `A` not
containing `f`. -/
def basicOpen (f : A) : Opens (carrier A) :=
  (PrimeSpectrum.basicOpen f).comap ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem mem_basicOpen {f : A} {p : carrier A} :
    p ∈ basicOpen f ↔ f ∉ (p : PrimeSpectrum A).asIdeal :=
  Iff.rfl

@[simp]
theorem basicOpen_one : basicOpen (1 : A) = ⊤ := by
  ext p
  simpa using (Ideal.ne_top_iff_one _).mp p.1.isPrime.ne_top

@[simp]
theorem basicOpen_zero : basicOpen (0 : A) = ⊥ := by
  ext p
  simp

theorem basicOpen_mul (f g : A) : basicOpen (f * g) = basicOpen f ⊓ basicOpen g := by
  ext p
  simp [p.1.isPrime.mul_mem_iff_mem_or_mem, not_or]

/-- The basic open sets `D(f)` form a basis of the topology of the underlying space of `Spf A`. -/
theorem isBasis_basicOpen : Opens.IsBasis (Set.range (basicOpen (A := A))) := by
  rw [Opens.IsBasis, ← Set.range_comp]
  convert IsInducing.subtypeVal.isTopologicalBasis (isTopologicalBasis_basic_opens (R := A))
  ext
  simp [basicOpen, Function.comp_def]

/-- If `I` defines the topology of `A`, then `D(g) ⊆ D(f)` in `Spf A` if and only if `g` lies in
the radical of `f A + I`, that is, if and only if `f` divides a power of `g` modulo `I`. -/
theorem basicOpen_le_basicOpen_iff (hI : IsAdic I) {f g : A} :
    basicOpen g ≤ basicOpen f ↔ g ∈ (Ideal.span {f} ⊔ I).radical := by
  rw [← Ideal.span_singleton_le_iff_mem, ← zeroLocus_subset_zeroLocus_iff, zeroLocus_sup,
    zeroLocus_span, zeroLocus_span]
  refine ⟨fun h p ⟨hf, hp⟩ ↦ ?_, fun h p hg hf ↦ hg ?_⟩
  · rw [mem_zeroLocus, Set.singleton_subset_iff] at hf ⊢
    rw [mem_zeroLocus, SetLike.coe_subset_coe] at hp
    by_contra hg
    exact h (x := ⟨p, (mem_carrier_iff_le hI).mpr hp⟩) hg hf
  · exact Set.singleton_subset_iff.mp
      (h ⟨Set.singleton_subset_iff.mpr hf, (mem_carrier_iff_le hI).mp p.2⟩)

/-- If `I` defines the topology of `A`, then `D(f)` is empty if and only if `f` lies in the
radical of `I`, that is, if and only if `f` is nilpotent modulo `I`. -/
theorem basicOpen_eq_bot_iff (hI : IsAdic I) {f : A} :
    basicOpen f = ⊥ ↔ f ∈ I.radical := by
  rw [← le_bot_iff, ← basicOpen_zero, basicOpen_le_basicOpen_iff hI,
    Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq]

end BasicOpen

section Comap

variable {B : Type*} [CommRing B] [TopologicalSpace B] {C : Type*} [CommRing C]
  [TopologicalSpace C]

/-- A continuous ring homomorphism `φ : B → A` pulls open primes of `A` back to open primes of
`B`, so it induces a continuous map from the underlying space of `Spf A` to that of `Spf B`
(EGA I, Ch. I, 10.2.1). -/
def comap (φ : B →+* A) (hφ : Continuous φ) : C(carrier A, carrier B) where
  toFun p := ⟨PrimeSpectrum.comap φ p, p.2.preimage hφ⟩
  continuous_toFun := ((continuous_comap φ).comp continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_comap_apply (φ : B →+* A) (hφ : Continuous φ) (p : carrier A) :
    (comap φ hφ p : PrimeSpectrum B) = PrimeSpectrum.comap φ p :=
  (rfl)

@[simp]
theorem comap_id : comap (RingHom.id A) continuous_id = ContinuousMap.id (carrier A) :=
  (rfl)

theorem comap_comp (φ : B →+* A) (hφ : Continuous φ) (ψ : C →+* B) (hψ : Continuous ψ) :
    comap (φ.comp ψ) (hφ.comp hψ) = (comap ψ hψ).comp (comap φ hφ) :=
  (rfl)

/-- The preimage of `D(b)` under the map induced by `φ : B → A` is `D(φ b)`. -/
@[simp]
theorem comap_basicOpen (φ : B →+* A) (hφ : Continuous φ) (b : B) :
    (basicOpen b).comap (comap φ hφ) = basicOpen (φ b) :=
  (rfl)

end Comap

end TauCeti.FormalScheme.Spf
