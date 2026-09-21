/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Nakayama
import Mathlib.Tactic.Ring

/-!
# Monogenicity criteria for finite extensions of local rings

This file develops the local-ring steps in the monogenicity argument for finite extensions of
discrete valuation rings. The Newton step produces an element whose polynomial value generates a
principal maximal ideal. A residue-field generator then meets every residue class, and propagation
through powers of the maximal ideal lets Nakayama's lemma prove algebra generation.

## Main results

* `TauCeti.IsLocalRing.exists_span_eval_eq_maximalIdeal`: the Newton step at a principal maximal
  ideal.
* `TauCeti.IsLocalRing.sup_maximalIdeal_eq_top_of_adjoin_residue_eq_top`: a lift of a residue-field
  generator meets every residue class.
* `TauCeti.IsLocalRing.adjoin_eq_top_of_span_eval_eq_maximalIdeal`: the generation criterion.
* `TauCeti.IsLocalRing.adjoin_eq_top_of_residue_surjective_of_span_eq_maximalIdeal`: the criterion
  for a generator of the maximal ideal when the residue map is surjective.
-/

public section

open IsLocalRing Polynomial

namespace TauCeti.IsLocalRing

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

end TauCeti.IsLocalRing
