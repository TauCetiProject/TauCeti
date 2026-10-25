/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Unramified.LocalStructure
public import TauCeti.RingTheory.Etale.FiniteEtaleSplit

import TauCeti.RingTheory.Henselization.Section
import TauCeti.RingTheory.Unramified.Diagonal

/-!
# Étale sections over henselian pairs

For a henselian pair `(R, I)`, reduction induces a bijection from the `R`-points of every étale
`R`-algebra to its points over `R ⧸ I`. Conversely, this lifting property characterizes henselian
pairs, including the requirement that `I` lie in the Jacobson radical. The ring need not be
local, noetherian, complete, or reduced, and the étale algebra need not be finite as a module.

The maximal-ideal specialization gives sections over henselian local rings and their relative
form. A henselian local ring with separably closed residue field consequently has no nonsplit
finite étale covers (`TauCeti.IsFiniteEtaleSplit.of_henselianLocalRing`).

The relative form allows an arbitrary base ring and a henselian pair in the target. These
section-lifting results are the étale input to lifting smooth sections and to comparing finite
étale algebras across a henselian reduction.

## Implementation notes

`Henselization.exists_isNeighbourhood_localization` isolates the specified residue section as an
étale neighbourhood. `Henselization.nonempty_algHom_of_bijective_reducedMap` then supplies a
section over the henselian pair. Uniqueness follows from the unramified diagonal and the
Jacobson radical, via `Algebra.FormallyUnramified.ext_of_quotient_eq`.

## References

* [Stacks Project, Lemma 15.11.6, Tag 09XI](https://stacks.math.columbia.edu/tag/09XI),
  equivalence of henselianity and lifting sections of étale algebras.
* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG), characterisations of
  henselian local rings by sections of étale algebras.
* [Stacks Project, Tag 08HQ](https://stacks.math.columbia.edu/tag/08HQ), the relative local form.
* P. Scholze, *Étale cohomology of diamonds*, Lemma 15.3, for rings without nonsplit finite
  étale covers.
-/

public section

universe u

open scoped TensorProduct

namespace TauCeti

namespace HenselianRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Over a henselian pair `(R, I)`, every point of an étale `R`-algebra over `R ⧸ I` lifts
uniquely to an `R`-point. -/
@[stacks 09XI "(1) ⇒ (2), with uniqueness"]
theorem comp_bijective (I : Ideal R) [HenselianRing R I] [Algebra.Etale R S] :
    Function.Bijective
      ((Ideal.Quotient.mkₐ R I).comp : (S →ₐ[R] R) → S →ₐ[R] R ⧸ I) := by
  refine ⟨fun f g h ↦ Algebra.FormallyUnramified.ext_of_quotient_eq R S I
    HenselianRing.jac h, fun ψ ↦ ?_⟩
  obtain ⟨x, hx, hC⟩ := Henselization.exists_isNeighbourhood_localization I ψ
  let C := Localization.Away x
  let ψ' : C →ₐ[R] R ⧸ I := IsLocalization.liftAlgHom (M := Submonoid.powers x)
    (f := ψ) fun ⟨_, n, hn⟩ ↦ hn ▸ by simp [hx]
  have hψ' (s : S) : ψ' (algebraMap S C s) = ψ s := IsLocalization.lift_eq _ s
  obtain ⟨hEtale, hBij⟩ := (Henselization.isNeighbourhood_iff I _).mp hC
  have : Algebra.Etale R C := hEtale
  obtain ⟨σ⟩ := Henselization.nonempty_algHom_of_bijective_reducedMap I (C := C) hBij
  have heq : (Ideal.Quotient.mkₐ R I).comp σ = ψ' := hC.algHom_ext (by simp)
  refine ⟨σ.comp (IsScalarTower.toAlgHom R S C), AlgHom.ext fun s ↦ ?_⟩
  exact (AlgHom.congr_fun heq (algebraMap S C s)).trans (hψ' s)

section Relative

variable {A : Type*} [CommRing A] [Algebra R A] [Algebra.Etale R A]

/-- For a henselian `R`-algebra pair `(S, J)`, reduction is a bijection from `R`-algebra maps
from an étale `R`-algebra to `S` to such maps into `S ⧸ J`. -/
theorem comp_bijective_of_algebra (J : Ideal S) [HenselianRing S J] :
    Function.Bijective
      ((Ideal.Quotient.mkₐ R J).comp : (A →ₐ[R] S) → A →ₐ[R] S ⧸ J) := by
  have h := comp_bijective (R := S) (S := S ⊗[R] A) J
  have hcomp : ((Ideal.Quotient.mkₐ R J).comp : (A →ₐ[R] S) → A →ₐ[R] S ⧸ J) =
      (AlgHom.liftEquiv R S A (S ⧸ J)).symm ∘
        (Ideal.Quotient.mkₐ S J).comp ∘ AlgHom.liftEquiv R S A S := by
    ext f a
    simp
  rw [hcomp]
  exact (AlgHom.liftEquiv R S A (S ⧸ J)).symm.bijective.comp
    (h.comp (AlgHom.liftEquiv R S A S).bijective)

end Relative

end HenselianRing

open Polynomial

/-- A pair is henselian if and only if every section of an étale algebra modulo its ideal
lifts to a section over the ring. The lifting property itself forces the ideal into the
Jacobson radical. It suffices to test algebras in the universe of the base ring. -/
@[stacks 09XI "(1) ⇔ (2)"]
theorem henselianRing_iff_etale_comp_surjective (R : Type u) [CommRing R] (I : Ideal R) :
    HenselianRing R I ↔ ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S],
      Function.Surjective
        ((Ideal.Quotient.mkₐ R I).comp : (S →ₐ[R] R) → S →ₐ[R] R ⧸ I) := by
  refine ⟨fun _ S _ _ _ ↦ (HenselianRing.comp_bijective I).2, fun H ↦ ?_⟩
  refine ⟨?_, fun f hf a₀ ha₀ hd ↦ ?_⟩
  · -- Localizations at elements congruent to one force the Jacobson-radical condition.
    intro r hr
    rw [Ideal.mem_jacobson_bot]
    intro y
    let x := r * y + 1
    have hx : Ideal.Quotient.mk I x = 1 := by
      simp [x, Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right y hr)]
    let ψ : Localization.Away x →ₐ[R] R ⧸ I :=
      IsLocalization.liftAlgHom (M := Submonoid.powers x) (f := Ideal.Quotient.mkₐ R I)
        fun ⟨_, n, hn⟩ ↦ hn ▸ by simpa only [Ideal.Quotient.mkₐ_eq_mk, map_pow, hx, one_pow]
          using isUnit_one
    obtain ⟨φ, _⟩ := H (Localization.Away x) ψ
    simpa using (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x).map φ
  · -- A simple root is a point of the standard étale algebra with the derivative inverted.
    let P : StandardEtalePair R := ⟨f, hf, f.derivative, 1, 0, 1, by simp⟩
    have hP : P.HasMap (Ideal.Quotient.mk I a₀) := by
      constructor
      · simp only [P, ← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply,
          coe_aeval_eq_eval]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr ha₀
      · simp only [P, ← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply,
          coe_aeval_eq_eval]
        exact hd
    obtain ⟨φ, hφ⟩ := H P.Ring (P.lift _ hP)
    refine ⟨φ P.X, ?_, ?_⟩
    · have := (P.hasMap_X.map φ).1
      simpa [P, coe_aeval_eq_eval] using this
    · rw [← Ideal.Quotient.eq]
      simpa using AlgHom.congr_fun hφ P.X

open IsLocalRing

namespace HenselianLocalRing

variable {R S : Type*} [CommRing R] [HenselianLocalRing R] [CommRing S] [Algebra R S]

/-- Over a Henselian local ring `R`, reduction modulo the maximal ideal is a bijection from the
`R`-points of an étale `R`-algebra `S` to its points over the residue field: every `R`-algebra map
`S → k` lifts uniquely to an `R`-algebra map `S → R`. Compare
`Algebra.FormallyEtale.comp_bijective`, the same statement for square-zero ideals over an
arbitrary base. -/
@[stacks 04GG "sections of étale algebras through a residue field point"]
theorem comp_bijective [Algebra.Etale R S] :
    Function.Bijective
      ((Algebra.ofId R (ResidueField R)).comp : (S →ₐ[R] R) → S →ₐ[R] ResidueField R) := by
  -- The residue field is the quotient by the maximal ideal, with the same scalar map.
  convert HenselianRing.comp_bijective (R := R) (S := S) (maximalIdeal R) using 1 <;> rfl

section Relative

variable {R S A : Type*} [CommRing R] [CommRing S] [HenselianLocalRing S] [Algebra R S]
  [CommRing A] [Algebra R A] [Algebra.Etale R A]

/-- The relative form of `comp_bijective`: for a Henselian local `R`-algebra `S` and an étale
`R`-algebra `A`, reduction modulo the maximal ideal of `S` is a bijection from `R`-algebra maps
`A → S` to `R`-algebra maps `A → κ(S)`. The base is arbitrary; `comp_bijective` is the case
`S = R`. -/
@[stacks 08HQ "relative form, over an arbitrary base"]
theorem comp_bijective_of_algebra :
    Function.Bijective
      ((IsScalarTower.toAlgHom R S (ResidueField S)).comp :
        (A →ₐ[R] S) → A →ₐ[R] ResidueField S) := by
  -- The residue field is the quotient by the maximal ideal, with the same scalar map.
  convert HenselianRing.comp_bijective_of_algebra (R := R) (S := S) (A := A)
    (maximalIdeal S) using 1 <;> rfl

end Relative

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
