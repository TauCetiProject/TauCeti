/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Unramified.LocalStructure
public import TauCeti.RingTheory.Etale.FiniteEtaleSplit

import TauCeti.RingTheory.Unramified.Diagonal

/-!
# Sections of étale algebras over a Henselian local ring

Let `R` be a Henselian local ring with residue field `k`, and let `S` be an étale `R`-algebra.
Reducing modulo the maximal ideal is a bijection from `R`-algebra maps `S → R` to `R`-algebra maps
`S → k` (`TauCeti.HenselianLocalRing.comp_bijective`): every `k`-point of `S` lifts uniquely to an
`R`-point. This is one of the equivalent characterisations of Henselian local rings, and the
analogue for the maximal ideal of `Algebra.FormallyEtale.comp_bijective`, where the ideal is
square-zero.

For a standard étale algebra `R[X]_g ⧸ (f)` an `R`-point is a root `a` of `f` with `g(a)` a unit,
so this is Hensel's lemma: `f'(a)` is a unit at such a root. A general étale algebra is standard
étale after inverting an element `g` outside the kernel of a given `k`-point
(`Algebra.IsEtaleAt.exists_isStandardEtale`), and both `k`-points and their lifts extend
uniquely to the localisation.

Consequently a *strictly Henselian* local ring, one whose residue field is separably closed, has
no nonsplit finite étale covers (`TauCeti.IsFiniteEtaleSplit.of_henselianLocalRing`): a faithfully
flat finite étale algebra has a `k`-point because `k` is separably closed, and this lifts to a
section. Such rings need be neither fields nor reduced.

## Main results

* `TauCeti.HenselianLocalRing.comp_bijective`: over a Henselian local ring, `R`-points of an étale
  algebra are in bijection with its points over the residue field.
* `TauCeti.IsFiniteEtaleSplit.of_henselianLocalRing`: a Henselian local ring with separably
  closed residue field has no nonsplit finite étale covers.

## References

* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG), characterisations of
  Henselian local rings by sections of étale algebras.
* P. Scholze, *Étale cohomology of diamonds*, Lemma 15.3, for rings without nonsplit finite étale
  covers.
-/

public section

open IsLocalRing Polynomial

universe u

namespace TauCeti

namespace HenselianLocalRing

variable {R S : Type*} [CommRing R] [HenselianLocalRing R] [CommRing S] [Algebra R S]

/-- The surjectivity half of `HenselianLocalRing.comp_bijective` for a standard étale algebra
`R[X]_g ⧸ (f)`: its `R`-points are the roots of `f` at which `g` is a unit, and such a root over the
residue field lifts by Hensel's lemma, because `f'` is a unit there. -/
private theorem comp_surjective_of_isStandardEtale [Algebra.IsStandardEtale R S] :
    Function.Surjective
      ((Algebra.ofId R (ResidueField R)).comp : (S →ₐ[R] R) → S →ₐ[R] ResidueField R) := by
  intro ψ
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := R) (S := S)
  -- Reduction commutes with evaluating polynomials over `R`.
  have hres (a : R) (p : R[X]) : residue R (aeval a p) = aeval (residue R a) p := by
    rw [← ResidueField.algebraMap_eq, aeval_algebraMap_apply]
  have hy := P.hasMap.map ψ
  obtain ⟨a₀, ha₀⟩ := residue_surjective (ψ P.x)
  obtain ⟨a, ha, haa₀⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a₀
    (by rw [← residue_eq_zero_iff, ← coe_aeval_eq_eval, hres, ha₀]; exact hy.1)
    (by
      rw [← residue_ne_zero_iff_isUnit, ← coe_aeval_eq_eval, hres, ha₀]
      exact hy.isUnit_derivative_f.ne_zero)
  have hra : residue R a = ψ P.x := by
    rw [← ha₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact haa₀
  have hP : P.HasMap a := by
    refine ⟨ha, ?_⟩
    rw [← residue_ne_zero_iff_isUnit, hres, hra]
    exact hy.2.ne_zero
  refine ⟨(P.lift a hP).comp P.equivRing.toAlgHom, P.hom_ext ?_⟩
  simp [hra]

/-- Over a Henselian local ring `R`, reduction modulo the maximal ideal is a bijection from the
`R`-points of an étale `R`-algebra `S` to its points over the residue field: every `R`-algebra map
`S → k` lifts uniquely to an `R`-algebra map `S → R`. Compare
`Algebra.FormallyEtale.comp_bijective`, the same statement for square-zero ideals over an
arbitrary base. -/
@[stacks 04GG "sections of étale algebras through a residue field point"]
theorem comp_bijective [Algebra.Etale R S] :
    Function.Bijective
      ((Algebra.ofId R (ResidueField R)).comp : (S →ₐ[R] R) → S →ₐ[R] ResidueField R) := by
  -- Uniqueness holds for unramified algebras, as the maximal ideal is the Jacobson radical.
  refine ⟨fun φ₁ φ₂ h ↦ Algebra.FormallyUnramified.ext_of_quotient_eq R S
    (maximalIdeal R) (maximalIdeal_le_jacobson ⊥) (AlgHom.ext fun s ↦ ?_), fun ψ ↦ ?_⟩
  · simpa [Ideal.Quotient.eq, ← residue_ne_zero_iff_isUnit, sub_eq_zero] using AlgHom.congr_fun h s
  -- Invert some `g ∉ ker ψ` to make `S` standard étale, and extend `ψ` to `S[1/g]`.
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨g, hg, _⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (RingHom.ker ψ)
  have hg : IsUnit (ψ g) := isUnit_iff_ne_zero.mpr fun h ↦ hg (RingHom.mem_ker.mpr h)
  let ψ' : Localization.Away g →ₐ[R] ResidueField R :=
    IsLocalization.liftAlgHom (M := .powers g) (f := ψ) fun ⟨_, n, hn⟩ ↦ hn ▸ by
      simpa using hg.pow n
  obtain ⟨φ, hφ⟩ := comp_surjective_of_isStandardEtale ψ'
  refine ⟨φ.comp (IsScalarTower.toAlgHom R S _), AlgHom.ext fun s ↦ ?_⟩
  simpa [ψ'] using AlgHom.congr_fun hφ (algebraMap S _ s)

end HenselianLocalRing

/-- A Henselian local ring with separably closed residue field, that is, a strictly Henselian local
ring, has no nonsplit finite étale covers: a faithfully flat finite étale algebra has a point over
the separably closed residue field, which lifts to a section. -/
instance IsFiniteEtaleSplit.of_henselianLocalRing (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)] : IsFiniteEtaleSplit R :=
  isFiniteEtaleSplit_iff_exists_section.mpr fun T _ _ _ _ _ ↦
    have ⟨ψ⟩ := IsFiniteEtaleSplit.nonempty_algHom (ResidueField R) T
    have ⟨φ, _⟩ := (HenselianLocalRing.comp_bijective (R := R) (S := T)).2 ψ
    ⟨φ⟩

end TauCeti
