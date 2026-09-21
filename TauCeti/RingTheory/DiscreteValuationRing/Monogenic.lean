/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Nakayama
-- for `UniqueFactorizationMonoid.instIsIntegrallyClosed`, which `PowerBasis.ofAdjoinEqTop'` needs
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Monogenicity of a finite extension of discrete valuation rings

Let `S` be a discrete valuation ring, finite over a discrete valuation subring `R`, and assume
the residue extension `𝓀(S)/𝓀(R)` is separable.  This file proves that `S = R[β]` for a single
`β : S`.  Both the ramified and the unramified case are covered; Mathlib's
`IsLocalRing.exists_adjoin_eq_top` covers only the unramified (finite étale) case, where the
generator may be taken to be any lift of a primitive element of the residue extension.

The proof is Serre's: pick a lift `a` of a primitive element of the residue extension and a
polynomial `g : R[X]` lifting its minimal polynomial.  Then `g(a)` lies in the maximal ideal and
`g'(a)` is a unit, so one Newton step, replacing `a` by `a + π` for a uniformizer `π` when it is
needed, arranges
that `g(β)` *generates* the maximal ideal.  The subring `R[β]` then meets every residue class
modulo `𝓂(S)` and contains a uniformizer, hence meets every residue class modulo `𝓂(S) ^ n`;
taking `n` large enough that `𝓂(S) ^ n ⊆ 𝓂(R) S`, Nakayama's lemma gives `R[β] = S`.

Only the existence of the generator needs the two rings to be discrete valuation rings: the
generation criterion and the steps it is assembled from hold for a module-finite extension of
local rings, and are stated there.

## Main results

* `TauCeti.IsLocalRing.exists_span_eval_eq_maximalIdeal`: the Newton step.
* `TauCeti.IsLocalRing.adjoin_eq_top_of_span_eval_eq_maximalIdeal`: the criterion for a single
  element to generate `S` over `R`.
* `TauCeti.IsLocalRing.adjoin_eq_top_of_residue_surjective_of_span_eq_maximalIdeal`: in the
  totally ramified case every generator of the maximal ideal of `S` generates `S` over `R`.
* `TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top`: a finite extension of discrete
  valuation rings with separable residue extension is monogenic.
* `TauCeti.IsDiscreteValuationRing.nonempty_powerBasis`: the integral basis a generator produces,
  via Mathlib's `PowerBasis.ofAdjoinEqTop'`.
* `TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top_and_intermediateField_adjoin_eq_top`: a
  generator of `S` over `R` also generates the fraction field of `S` over that of `R`.

## References

* [J.-P. Serre, *Corps locaux*][serre1968], Chapter III, §6, Proposition 12.
-/

public section

open IsLocalRing Polynomial

namespace TauCeti

namespace Subalgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If a subalgebra `T` meets every residue class of `S` modulo a principal ideal `I` and contains
a generator of `I`, then it meets every residue class modulo any power of `I`. -/
theorem sup_pow_eq_top {T : Subalgebra R S} {I : Ideal S} {π : S}
    (hπ : Ideal.span {π} = I) (hπT : π ∈ T)
    (h : T.toSubmodule ⊔ I.restrictScalars R = ⊤) (n : ℕ) :
    T.toSubmodule ⊔ (I ^ n).restrictScalars R = ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : I ^ n = Ideal.span {π ^ n} := by
      rw [← hπ, Ideal.span_singleton_pow]
    refine eq_top_iff.mpr fun s _ => ?_
    obtain ⟨t, ht, m, hm, rfl⟩ := Submodule.mem_sup.mp (ih.ge Submodule.mem_top : s ∈ _)
    obtain ⟨u, rfl⟩ : ∃ u, m = π ^ n * u := by
      rw [Submodule.restrictScalars_mem, hpow, Ideal.mem_span_singleton] at hm
      exact hm
    obtain ⟨t', ht', m', hm', rfl⟩ := Submodule.mem_sup.mp (h.ge Submodule.mem_top : u ∈ _)
    refine Submodule.mem_sup.mpr ⟨t + π ^ n * t', ?_, π ^ n * m', ?_, by ring⟩
    · rw [Subalgebra.mem_toSubmodule] at ht ht' ⊢
      exact add_mem ht (mul_mem (pow_mem hπT n) ht')
    · rw [Submodule.restrictScalars_mem, pow_succ]
      exact Ideal.mul_mem_mul (hpow ▸ Ideal.mem_span_singleton_self _) hm'

end Subalgebra

namespace IsLocalRing

section Newton

variable {S : Type*} [CommRing S] [IsLocalRing S]

/-- **Newton step at a principal maximal ideal.**  If `π` generates the maximal ideal of a local
ring `S`, and `f : S[X]` has a simple root at `a` modulo `𝓂(S)`, then `f` takes a value generating
`𝓂(S)` at some `b` congruent to `a` modulo `𝓂(S)`: either `a` itself works, or `a + π` does. -/
theorem exists_span_eval_eq_maximalIdeal {f : S[X]} {a π : S}
    (hπ : Ideal.span {π} = maximalIdeal S) (ha : f.eval a ∈ maximalIdeal S)
    (ha' : IsUnit ((derivative f).eval a)) :
    ∃ b : S, b - a ∈ maximalIdeal S ∧ Ideal.span {f.eval b} = maximalIdeal S := by
  have hπmem : π ∈ maximalIdeal S := hπ ▸ Ideal.mem_span_singleton_self π
  by_cases h : Ideal.span {f.eval a} = maximalIdeal S
  · exact ⟨a, by simp, h⟩
  refine ⟨a + π, by simpa using hπmem, ?_⟩
  -- The failure of `a` forces `f.eval a ∈ 𝓂(S) ^ 2`, say `f.eval a = π ^ 2 * d`.
  obtain ⟨u, hu⟩ : ∃ u, f.eval a = π * u :=
    Ideal.mem_span_singleton.mp (hπ ▸ ha)
  have hu' : u ∈ maximalIdeal S := by
    by_contra hu'
    exact h (by rw [hu, Ideal.span_singleton_mul_right_unit (notMem_maximalIdeal.mp hu'), hπ])
  obtain ⟨d, hd⟩ : ∃ d, u = π * d := Ideal.mem_span_singleton.mp (hπ ▸ hu')
  obtain ⟨k, hk⟩ := binomExpansion f a π
  -- Now `f.eval (a + π) = π * ((derivative f).eval a + π * (d + k))`, with a unit on the right.
  have hfac : f.eval (a + π) = π * ((derivative f).eval a + π * (d + k)) := by
    rw [hk, hu, hd]; ring
  have hunit : IsUnit ((derivative f).eval a + π * (d + k)) := by
    refine notMem_maximalIdeal.mp fun hmem => notMem_maximalIdeal.mpr ha' ?_
    simpa using sub_mem hmem (Ideal.mul_mem_right (d + k) _ hπmem)
  rw [hfac, Ideal.span_singleton_mul_right_unit hunit, hπ]

end Newton

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- Reduction modulo the maximal ideals commutes with `algebraMap`, as a square of ring
homomorphisms.  This is Mathlib's `IsLocalRing.ResidueField.algebraMap_residue` in the form
`Polynomial.map_aeval_eq_aeval_map` takes. -/
private theorem residue_comp_algebraMap :
    (algebraMap (ResidueField R) (ResidueField S)).comp (residue R) =
      (residue S).comp (algebraMap R S) :=
  RingHom.ext fun x => ResidueField.algebraMap_residue x

/-- If the residue of `β` generates the residue field extension, then `R[β]` meets every residue
class of `S` modulo the maximal ideal: `R[β]` and `𝓂(S)` together span `S` over `R`.  This is the
residue-class step of the generation criterion
`TauCeti.IsLocalRing.adjoin_eq_top_of_span_eval_eq_maximalIdeal`.  It is the ramified counterpart
of the forward half of Mathlib's `IsLocalRing.adjoin_residue_eq_top_iff_adjoin_eq_top`, which
spans modulo `𝓂(R) S` instead and so is available only when the two ideals agree. -/
theorem sup_maximalIdeal_eq_top_of_adjoin_residue_eq_top {β : S}
    (hβ : Algebra.adjoin (ResidueField R) {residue S β} = ⊤) :
    (Algebra.adjoin R {β}).toSubmodule ⊔ (maximalIdeal S).restrictScalars R = ⊤ := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hβ
  refine eq_top_iff.mpr fun s _ => ?_
  obtain ⟨p, hp⟩ := hβ (residue S s)
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective _ residue_surjective p
  rw [← map_aeval_eq_aeval_map residue_comp_algebraMap] at hp
  refine Submodule.mem_sup.mpr ⟨aeval β q, ?_, s - aeval β q, ?_, by ring⟩
  · rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨q, rfl⟩
  · rw [Submodule.restrictScalars_mem, ← Ideal.Quotient.eq]
    exact hp.symm

variable [Module.Finite R S]

omit [IsLocalHom (algebraMap R S)] in
/-- The maximal ideal of `S` is nilpotent modulo the ideal generated by the maximal ideal of `R`:
some power of `𝓂(S)` lies in `𝓂(R) S`.  For discrete valuation rings the exponent that works is
the ramification index. -/
theorem exists_maximalIdeal_pow_le_map :
    ∃ n : ℕ, maximalIdeal S ^ n ≤ (maximalIdeal R).map (algebraMap R S) := by
  have : Module.Finite R (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R _).toLinearMap Ideal.Quotient.mk_surjective
  have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (R ⧸ maximalIdeal R) :=
    letI := Ideal.Quotient.field (maximalIdeal R)
    inferInstance
  have : IsArtinianRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    IsArtinianRing.of_finite (R ⧸ maximalIdeal R) _
  exact _root_.IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient _

/-- **The generation criterion.**  An element `β` of `S` generates `S` as an `R`-algebra as soon as
its residue generates the residue field extension and some polynomial in `β` with coefficients in
`R` generates the maximal ideal of `S`. -/
theorem adjoin_eq_top_of_span_eval_eq_maximalIdeal {β : S} {g : R[X]}
    (hres : Algebra.adjoin (ResidueField R) {residue S β} = ⊤)
    (hgen : Ideal.span {aeval β g} = maximalIdeal S) :
    Algebra.adjoin R {β} = ⊤ := by
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_map (R := R) (S := S)
  have hmem : aeval β g ∈ Algebra.adjoin R {β} := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨g, rfl⟩
  have hsup := TauCeti.Subalgebra.sup_pow_eq_top hgen hmem
    (sup_maximalIdeal_eq_top_of_adjoin_residue_eq_top hres) n
  rw [← Algebra.toSubmodule_eq_top]
  refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.mp inferInstance) (maximalIdeal_le_jacobson ⊥) ?_)
  rw [Ideal.smul_top_eq_map]
  exact hsup.ge.trans (sup_le_sup_left (Submodule.restrictScalars_mono R hn) _)

/-- **The totally ramified case.**  If the residue extension is trivial, every generator of the
maximal ideal of `S` generates `S` over `R`.  This is the direction of the Eisenstein description
of a totally ramified extension that produces an integral power basis. -/
theorem adjoin_eq_top_of_residue_surjective_of_span_eq_maximalIdeal
    (hsurj : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)))
    {π : S} (hπ : Ideal.span {π} = maximalIdeal S) : Algebra.adjoin R {π} = ⊤ := by
  refine adjoin_eq_top_of_span_eval_eq_maximalIdeal (g := X) ?_ (by simpa using hπ)
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := hsurj x
  exact _root_.Subalgebra.algebraMap_mem _ y

end IsLocalRing

namespace IntermediateField

variable {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L] [Algebra R S]
  [Algebra R K] [Algebra R L] [Algebra S L] [Algebra K L] [IsScalarTower R S L]
  [IsScalarTower R K L] [IsFractionRing S L]

/-- If `S` is generated as an `R`-algebra by a single element `β`, then the fraction field `L` of
`S` is generated by the image of `β` over any field `K` sitting between `R` and `L`: every element
of `L` is a ratio of two elements of `R[β]`. -/
theorem adjoin_eq_top_of_algebra_adjoin_eq_top {β : S} (h : Algebra.adjoin R {β} = ⊤) :
    IntermediateField.adjoin K {algebraMap S L β} = ⊤ := by
  have key : ∀ s : S, algebraMap S L s ∈ IntermediateField.adjoin K {algebraMap S L β} := by
    intro s
    have hs : s ∈ Algebra.adjoin R {β} := h.ge Algebra.mem_top
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      obtain rfl : x = β := hx
      exact IntermediateField.subset_adjoin K _ rfl
    | algebraMap r =>
      rw [← IsScalarTower.algebraMap_apply R S L, IsScalarTower.algebraMap_apply R K L]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨s, t, -, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  exact div_mem (key s) (key t)

end IntermediateField

namespace IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [Module.Finite R S]
  [FaithfulSMul R S]

/-- **Local monogenicity.**  A finite extension of discrete valuation rings whose residue
extension is separable is generated by a single element.  Completeness of `R` is not needed: it
enters the classical statement only to guarantee that the integral closure of `R` in a finite
field extension is again a discrete valuation ring, which is here a hypothesis on `S`. -/
theorem exists_adjoin_eq_top [Algebra.IsSeparable (ResidueField R) (ResidueField S)] :
    ∃ β : S, Algebra.adjoin R {β} = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField R) (ResidueField S)
  obtain ⟨a, rfl⟩ := residue_surjective (R := S) α
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  -- A lift `g : R[X]` of the minimal polynomial of the residue of `a`.
  obtain ⟨g, hg⟩ := (mem_lifts _).mp
    (mem_lifts_of_surjective residue_surjective (minpoly (ResidueField R) (residue S a)))
  have hbridge : ∀ x : S, residue S (aeval x g) =
      aeval (residue S x) (minpoly (ResidueField R) (residue S a)) := fun x => by
    rw [map_aeval_eq_aeval_map TauCeti.IsLocalRing.residue_comp_algebraMap, hg]
  have hbridge' : ∀ x : S, residue S (aeval x (derivative g)) =
      aeval (residue S x) (derivative (minpoly (ResidueField R) (residue S a))) := fun x => by
    rw [map_aeval_eq_aeval_map TauCeti.IsLocalRing.residue_comp_algebraMap, ← derivative_map, hg]
  -- `g` has a simple root at `a` modulo the maximal ideal, so a Newton step applies.
  have hval : (g.map (algebraMap R S)).eval a ∈ maximalIdeal S := by
    rw [eval_map, ← aeval_def, ← residue_eq_zero_iff]
    exact (hbridge a).trans (minpoly.aeval _ _)
  have hder : IsUnit ((derivative (g.map (algebraMap R S))).eval a) := by
    rw [derivative_map, eval_map, ← aeval_def, ← residue_ne_zero_iff_isUnit, hbridge' a]
    exact (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨β, hβa, hβ⟩ := TauCeti.IsLocalRing.exists_span_eval_eq_maximalIdeal
    hπ.maximalIdeal_eq.symm hval hder
  have hres : residue S β = residue S a := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hβa
  refine ⟨β, TauCeti.IsLocalRing.adjoin_eq_top_of_span_eval_eq_maximalIdeal (g := g) ?_ ?_⟩
  · exact hres ▸ Algebra.adjoin_eq_top_of_primitive_element (IsAlgebraic.of_finite _ _) hα
  · rwa [aeval_def, ← eval_map]

/-- A finite extension of discrete valuation rings with separable residue extension admits a
power basis: the integral basis `1, β, …, β ^ (n - 1)` attached to a generator `β`. -/
theorem nonempty_powerBasis [Algebra.IsSeparable (ResidueField R) (ResidueField S)] :
    Nonempty (PowerBasis R S) :=
  let ⟨β, h⟩ := exists_adjoin_eq_top (R := R) (S := S)
  ⟨PowerBasis.ofAdjoinEqTop' (IsIntegral.of_finite R β) h⟩

/-- A generator of `S` over `R` also generates the fraction field of `S` over that of `R`, so the
power basis of `TauCeti.IsDiscreteValuationRing.nonempty_powerBasis` is built from a primitive
element of the extension of fraction fields. -/
theorem exists_adjoin_eq_top_and_intermediateField_adjoin_eq_top
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] (K L : Type*) [Field K] [Field L]
    [Algebra R K] [Algebra R L] [Algebra S L] [Algebra K L] [IsScalarTower R S L]
    [IsScalarTower R K L] [IsFractionRing S L] :
    ∃ β : S, Algebra.adjoin R {β} = ⊤ ∧ IntermediateField.adjoin K {algebraMap S L β} = ⊤ :=
  let ⟨β, h⟩ := exists_adjoin_eq_top (R := R) (S := S)
  ⟨β, h, TauCeti.IntermediateField.adjoin_eq_top_of_algebra_adjoin_eq_top h⟩

/-- **The totally ramified case.**  If the residue extension is trivial, every uniformizer of `S`
generates `S` over `R`.  This is the direction of the Eisenstein description of a totally ramified
extension that produces an integral power basis. -/
theorem adjoin_eq_top_of_residue_surjective_of_irreducible
    (hsurj : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)))
    {π : S} (hπ : Irreducible π) : Algebra.adjoin R {π} = ⊤ :=
  TauCeti.IsLocalRing.adjoin_eq_top_of_residue_surjective_of_span_eq_maximalIdeal hsurj
    hπ.maximalIdeal_eq.symm

end IsDiscreteValuationRing

end TauCeti
