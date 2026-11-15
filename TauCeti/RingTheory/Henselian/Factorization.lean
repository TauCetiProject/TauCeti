/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.RingTheory.Henselian.Section
import TauCeti.RingTheory.Jacobson.Basic
import TauCeti.RingTheory.Polynomial.UniversalFactorizationRing
import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Lifting coprime factorizations along a Henselian pair

Let `(R, I)` be a Henselian pair and let `p` be a monic polynomial over `R`. Every factorization
`p ≡ g₀ h₀ (mod I)` into coprime monic polynomials over `R ⧸ I` lifts to a factorization
`p = g h` into monic polynomials over `R` with `g ≡ g₀` and `h ≡ h₀`, and this lift is unique.
Existence of such lifts, together with `I` lying in the Jacobson radical, is the definition of a
Henselian pair in the Stacks Project; uniqueness is a consequence. Mathlib's `HenselianRing`
instead asks for lifts of simple roots, which are the factorizations with `g₀` linear. The two
agree (`TauCeti.henselianRing_iff_forall_exists_monic_mul_eq`).

## Main results

* `Ideal.existsUnique_monic_mul_eq`: over a Henselian pair, a factorization into coprime monic
  polynomials modulo `I` lifts uniquely to a factorization into monic polynomials.
* `TauCeti.henselianRing_of_forall_exists_monic_mul_eq`: if `I` lies in the Jacobson radical and
  coprime monic factorizations modulo `I` lift, then `(R, I)` is Henselian.
* `TauCeti.henselianRing_iff_forall_exists_monic_mul_eq`: a pair `(R, I)` is Henselian if and only
  if `I` lies in the Jacobson radical and coprime monic factorizations modulo `I` lift.

## Implementation notes

Factorizations of `p` into coprime monic factors of given degrees are the points of Mathlib's
`Polynomial.UniversalCoprimeFactorizationRing` (Andrew Yang), an étale `R`-algebra. Sections of an
étale algebra lift uniquely along a Henselian pair (`TauCeti.HenselianRing.comp_bijective`), and
this is the lift of factorizations. Coprimality of the lifted factors comes from
`Polynomial.isCoprime_of_isCoprime_map`.

## References

* [Stacks Project, Definition 15.11.1](https://stacks.math.columbia.edu/tag/09XE).
* [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI).
-/

public section

open Polynomial

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R) [HenselianRing R I]

/-- **Coprime factorizations lift along a Henselian pair.** If `(R, I)` is Henselian and the
reduction of a monic polynomial `p` modulo `I` is a product `g₀ h₀` of coprime monic polynomials,
then there is exactly one pair of monic polynomials `g`, `h` over `R` with `p = g h`, `g ≡ g₀` and
`h ≡ h₀` modulo `I`. -/
@[stacks 09XE "the factorizations of Definition 15.11.1 lift, uniquely"]
theorem existsUnique_monic_mul_eq {p : R[X]} (hp : p.Monic) {g₀ h₀ : (R ⧸ I)[X]}
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hgh₀ : IsCoprime g₀ h₀)
    (hp₀ : p.map (Ideal.Quotient.mk I) = g₀ * h₀) :
    ∃! gh : R[X] × R[X], gh.1.Monic ∧ gh.2.Monic ∧ gh.1 * gh.2 = p ∧
      gh.1.map (Ideal.Quotient.mk I) = g₀ ∧ gh.2.map (Ideal.Quotient.mk I) = h₀ := by
  have hjac : I ≤ Ring.jacobson R := HenselianRing.jac
  cases subsingleton_or_nontrivial (R ⧸ I) with
  | inl _ =>
    have := Ideal.subsingleton_of_le_jacobson hjac
    exact ⟨(1, 1), ⟨monic_of_subsingleton _, monic_of_subsingleton _, Subsingleton.elim _ _,
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩, fun _ _ ↦ Subsingleton.elim _ _⟩
  | inr _ =>
  set m := g₀.natDegree
  set k := h₀.natDegree
  have hn : p.natDegree = m + k := by
    rw [← hp.natDegree_map (Ideal.Quotient.mk I), hp₀, hg₀.natDegree_mul hh₀]
  let P : MonicDegreeEq R p.natDegree := .mk p hp rfl
  let A := UniversalCoprimeFactorizationRing m k hn P
  -- The given factorization modulo `I` is a point of `A` with values in `R ⧸ I`.
  let ψ : A →ₐ[R] R ⧸ I := (UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I) m k hn P).symm
    ⟨(.mk g₀ hg₀ rfl, .mk h₀ hh₀ rfl), by simpa [P] using hp₀.symm, hgh₀⟩
  -- A factorization over `R` with the given reductions is a point of `A` lifting `ψ`.
  have hpoint : ∀ gh : R[X] × R[X], gh.1.Monic → gh.2.Monic → gh.1 * gh.2 = p →
      gh.1.map (Ideal.Quotient.mk I) = g₀ → gh.2.map (Ideal.Quotient.mk I) = h₀ →
      ∃ φ : A →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp φ = ψ ∧
        ((UniversalCoprimeFactorizationRing.homEquiv R m k hn P φ).1.1.1,
          (UniversalCoprimeFactorizationRing.homEquiv R m k hn P φ).1.2.1) = gh := by
    rintro ⟨g, h⟩ hg hh hgh hgmap hhmap
    have hgdeg : g.natDegree = m := by rw [← hg.natDegree_map (Ideal.Quotient.mk I), hgmap]
    have hhdeg : h.natDegree = k := by rw [← hh.natDegree_map (Ideal.Quotient.mk I), hhmap]
    have hcop : IsCoprime g h :=
      Polynomial.isCoprime_of_isCoprime_map hjac hg (by rwa [hgmap, hhmap])
    refine ⟨(UniversalCoprimeFactorizationRing.homEquiv R m k hn P).symm
      ⟨(.mk g hg hgdeg, .mk h hh hhdeg), by simpa [P] using hgh, hcop⟩, ?_, by simp⟩
    apply (UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I) m k hn P).injective
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · simp [UniversalCoprimeFactorizationRing.homEquiv_mkₐ_comp_fst I m k hn P _, ψ,
        hgmap]
    · simp [UniversalCoprimeFactorizationRing.homEquiv_mkₐ_comp_snd I m k hn P _, ψ,
        hhmap]
  obtain ⟨φ, hφ⟩ := (TauCeti.HenselianRing.comp_bijective I (A := A)).2 ψ
  set q := UniversalCoprimeFactorizationRing.homEquiv R m k hn P φ
  have hq₀ := congrArg (fun φ ↦ (UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I) m k hn P φ).1)
    hφ
  simp only [ψ, Equiv.apply_symm_apply] at hq₀
  refine ⟨(q.1.1.1, q.1.2.1), ⟨q.1.1.monic, q.1.2.monic, by simpa [P] using q.2.1, ?_, ?_⟩, ?_⟩
  · simpa [q, UniversalCoprimeFactorizationRing.homEquiv_mkₐ_comp_fst I m k hn P φ]
      using congr(($hq₀).1.1)
  · simpa [q, UniversalCoprimeFactorizationRing.homEquiv_mkₐ_comp_snd I m k hn P φ]
      using congr(($hq₀).2.1)
  · rintro gh ⟨hg, hh, hgh, hgmap, hhmap⟩
    obtain ⟨φ', hφ', rfl⟩ := hpoint gh hg hh hgh hgmap hhmap
    rw [(TauCeti.HenselianRing.comp_bijective I (A := A)).1 (hφ'.trans hφ.symm)]

/-- **Coprime factorizations lift along a Henselian pair.** The existence half of
`Ideal.existsUnique_monic_mul_eq`, recording that the lifted factors are again
coprime. -/
theorem exists_monic_mul_eq {p : R[X]} (hp : p.Monic) {g₀ h₀ : (R ⧸ I)[X]}
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hgh₀ : IsCoprime g₀ h₀)
    (hp₀ : p.map (Ideal.Quotient.mk I) = g₀ * h₀) :
    ∃ g h : R[X], g.Monic ∧ h.Monic ∧ g * h = p ∧ IsCoprime g h ∧
      g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀ := by
  obtain ⟨⟨g, h⟩, ⟨hg, hh, hgh, hgmap, hhmap⟩, -⟩ :=
    I.existsUnique_monic_mul_eq hp hg₀ hh₀ hgh₀ hp₀
  exact ⟨g, h, hg, hh, hgh, Polynomial.isCoprime_of_isCoprime_map HenselianRing.jac hg
    (by rwa [hgmap, hhmap]), hgmap, hhmap⟩

end Ideal

namespace TauCeti

/-- **Henselian pairs from lifted factorizations.** If `I` lies in the Jacobson radical of `R` and
every factorization of a monic polynomial modulo `I` into coprime monic polynomials lifts to a
factorization over `R`, then `(R, I)` is Henselian: a simple root `a₀` modulo `I` of `p` splits off
the coprime factor `X - a₀`, whose lift is `X - a` for a root `a ≡ a₀` of `p`. -/
theorem henselianRing_of_forall_exists_monic_mul_eq {R : Type*} [CommRing R] {I : Ideal R}
    (hjac : I ≤ Ring.jacobson R)
    (H : ∀ p : R[X], p.Monic → ∀ g₀ h₀ : (R ⧸ I)[X], g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ →
      p.map (Ideal.Quotient.mk I) = g₀ * h₀ →
      ∃ g h : R[X], g.Monic ∧ h.Monic ∧ g * h = p ∧
        g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀) :
    HenselianRing R I where
  jac := hjac
  is_henselian p hp a₀ hpa₀ hunit := by
    cases subsingleton_or_nontrivial (R ⧸ I) with
    | inl _ =>
      have := Ideal.subsingleton_of_le_jacobson hjac
      exact ⟨a₀, Subsingleton.elim _ _, Subsingleton.elim (a₀ - a₀) 0 ▸ I.zero_mem⟩
    | inr _ =>
    -- Modulo `I`, the simple root `a₀` splits off the coprime factor `X - a₀`.
    set π := Ideal.Quotient.mk I
    set q₀ := p.map π /ₘ (X - C (π a₀))
    have hroot : (p.map π).IsRoot (π a₀) := by
      rw [IsRoot, eval_map_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hpa₀
    have hfac : p.map π = (X - C (π a₀)) * q₀ := (mul_divByMonic_eq_iff_isRoot.mpr hroot).symm
    have hcop : IsCoprime (X - C (π a₀)) q₀ := isCoprime_X_sub_C_of_isUnit_eval <| by
      rwa [eval_divByMonic_X_sub_C_self, derivative_map, eval_map_apply]
    obtain ⟨g, h, hg, -, hgh, hgmap, -⟩ := H p hp _ q₀ (monic_X_sub_C _)
      ((monic_X_sub_C _).of_mul_monic_left (hfac ▸ hp.map π)) hcop hfac
    -- The lift of `X - a₀` is `X - a` for a root `a ≡ a₀` of `p`.
    have hgdeg : g.natDegree = 1 := by
      rw [← hg.natDegree_map π, hgmap, natDegree_X_sub_C]
    have hga : g = X - C (-g.coeff 0) := by
      rw [map_neg, sub_neg_eq_add]
      exact hg.eq_X_add_C hgdeg
    refine ⟨-g.coeff 0, ?_, ?_⟩
    · rw [IsRoot, ← hgh, eval_mul, hga]
      simp
    · rw [← Ideal.Quotient.eq, map_neg]
      have := congrArg (fun r : (R ⧸ I)[X] ↦ r.coeff 0) hgmap
      simp only [coeff_map, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub] at this
      rw [this, neg_neg]

/-- **Henselian pairs lift coprime factorizations.** A pair `(R, I)` is Henselian if and only if
`I` lies in the Jacobson radical and every factorization of a monic polynomial modulo `I` into
coprime monic polynomials lifts to a factorization over `R`. The right-hand side is the definition
of a Henselian pair in the Stacks Project. -/
@[stacks 09XE "agrees with Mathlib's `HenselianRing`"]
theorem henselianRing_iff_forall_exists_monic_mul_eq {R : Type*} [CommRing R] {I : Ideal R} :
    HenselianRing R I ↔ I ≤ Ring.jacobson R ∧
      ∀ p : R[X], p.Monic → ∀ g₀ h₀ : (R ⧸ I)[X], g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ →
        p.map (Ideal.Quotient.mk I) = g₀ * h₀ →
        ∃ g h : R[X], g.Monic ∧ h.Monic ∧ g * h = p ∧
          g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀ := by
  refine ⟨fun _ ↦ ⟨HenselianRing.jac, fun p hp g₀ h₀ hg₀ hh₀ hgh₀ hp₀ ↦ ?_⟩,
    fun ⟨hjac, H⟩ ↦ henselianRing_of_forall_exists_monic_mul_eq hjac H⟩
  obtain ⟨g, h, hg, hh, hgh, -, hgmap, hhmap⟩ :=
    I.exists_monic_mul_eq hp hg₀ hh₀ hgh₀ hp₀
  exact ⟨g, h, hg, hh, hgh, hgmap, hhmap⟩

end TauCeti
