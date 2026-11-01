/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Unramified.LocalStructure
import TauCeti.RingTheory.Henselization.Section
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.TensorProduct.LiftEquiv
import TauCeti.RingTheory.Unramified.Diagonal
import TauCeti.RingTheory.Unramified.Section.Idempotent

/-!
# Sections of étale algebras over a Henselian pair

Let `(S, J)` be a Henselian pair and let `A` be an étale `S`-algebra. Reducing modulo `J` is a
bijection from `S`-algebra maps `A → S` to `S`-algebra maps `A → S ⧸ J`
(`TauCeti.HenselianRing.comp_bijective`): every section of `Spec A → Spec S` over the closed
subscheme `V(J)` extends uniquely to a section over `Spec S`. More generally, for an étale algebra
`A` over an arbitrary base `R` and a Henselian pair `(S, J)` under `R`, every `R`-algebra map
`A → S ⧸ J` lifts uniquely to an `R`-algebra map `A → S`
(`TauCeti.HenselianRing.comp_bijective_of_algebra`).

Conversely, this lifting property characterises Henselian pairs: if every `R`-algebra map from an
étale `R`-algebra to `R ⧸ I` lifts to `R`, then `(R, I)` is Henselian
(`TauCeti.henselianRing_iff_forall_comp_surjective`). Lifting along localizations `R[1/u]` with
`u ≡ 1 mod I` puts `I` in the Jacobson radical, and lifting along the standard étale algebras
`R[X]_{f'} ⧸ (f)` lifts simple roots of monic polynomials.

The local case `J = 𝔪` is `TauCeti.HenselianLocalRing.comp_bijective`, which has an elementary
proof by Hensel's lemma for standard étale algebras. These lifts are one input for comparing
finite étale algebras over `S` with finite étale algebras over `S ⧸ J`.

## Main results

* `TauCeti.HenselianRing.comp_bijective`: over a Henselian pair `(S, J)`, sections of an étale
  `S`-algebra are in bijection with its sections modulo `J`.
* `TauCeti.HenselianRing.comp_bijective_of_algebra`: the same for an étale algebra over an
  arbitrary base `R` and a Henselian pair `(S, J)` under `R`.
* `TauCeti.henselianRing_iff_forall_comp_surjective`: a pair `(R, I)` is Henselian if and only if
  every section modulo `I` of an étale `R`-algebra lifts to a section.

## Implementation notes

Existence of lifts over a general pair reduces to étale neighbourhoods, whose sections are
`TauCeti.Henselization.nonempty_algHom_of_bijective_reducedMap`. Over `S ⧸ J`, a section of the
étale algebra `(S ⧸ J) ⊗[S] A` is localization at an idempotent `e`; inverting a lift `g ∈ A` of
`e` (`TauCeti.Algebra.FormallyUnramified.exists_mul_mem_map_of_eq_zero`) gives an étale
`S`-algebra `A[1/g]` with `A[1/g] ⧸ J A[1/g] ≅ S ⧸ J`. Uniqueness holds because
`J` lies in the Jacobson radical (`TauCeti.Algebra.FormallyUnramified.ext_of_quotient_eq`).

## References

* [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI), the equivalence of
  conditions (1) and (2).
* The Stacks Project, Lemma 15.11.5 (uniqueness of sections over a Henselian pair).
-/

public section

open TensorProduct Polynomial

universe u v

namespace TauCeti

namespace HenselianRing

section Absolute

variable {S : Type u} [CommRing S] (J : Ideal S)
  {A : Type v} [CommRing A] [Algebra S A] [Algebra.Etale S A]

variable [HenselianRing S J]

/-- **Sections of étale algebras over a Henselian pair.** Over a Henselian pair `(S, J)`,
reduction modulo `J` is a bijection from the `S`-algebra maps `A → S` out of an étale `S`-algebra
`A` to the `S`-algebra maps `A → S ⧸ J`. -/
@[stacks 09XI "(1) ⇒ (2), with uniqueness of the lift"]
theorem comp_bijective :
    Function.Bijective ((Ideal.Quotient.mkₐ S J).comp : (A →ₐ[S] S) → A →ₐ[S] S ⧸ J) := by
  refine ⟨fun _ _ h ↦ Algebra.FormallyUnramified.ext_of_quotient_eq S A J HenselianRing.jac h,
    fun ψ ↦ ?_⟩
  -- Invert some `g` with `ψ g = 1` that kills the kernel of `ψ` modulo `JA`.
  obtain ⟨g, hψg, hg⟩ := Algebra.FormallyUnramified.exists_mul_mem_map_of_eq_zero J ψ
  let C := Localization.Away g
  let ψC : C →ₐ[S] S ⧸ J := IsLocalization.Away.liftAlgHom g (f := ψ) (by simp [hψg])
  have hψC (a : A) : ψC (algebraMap A C a) = ψ a := by
    simp [ψC, IsLocalization.Away.lift_eq]
  have hJC : J.map (algebraMap S C) = (J.map (algebraMap S A)).map (algebraMap A C) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  -- The kernel of `ψC` is `J C`.
  have hker (c : C) (hc : ψC c = 0) : c ∈ J.map (algebraMap S C) := by
    obtain ⟨n, a, hca⟩ := IsLocalization.Away.surj g c
    have ha : ψ a = 0 := by
      rw [← hψC, ← hca, map_mul, hc, zero_mul]
    rw [← Ideal.unit_mul_mem_iff_mem _ ((IsLocalization.Away.algebraMap_isUnit g).pow (n + 1)),
      pow_succ', mul_assoc, mul_comm _ c, hca, ← map_mul, hJC]
    exact Ideal.mem_map_of_mem _ (hg a ha)
  have hbij : Function.Bijective (Henselization.reducedMap J C) := by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Henselization.reducedMap_mk, Ideal.Quotient.eq_zero_iff_mem, hJC] at hx
      -- `ψC` kills `J C`, and restricts to the quotient map on `S`.
      have hle : (J.map (algebraMap S A)).map (algebraMap A C) ≤ RingHom.ker ψC := by
        rw [← hJC, Ideal.map_le_iff_le_comap]
        intro j hj
        simpa [Ideal.Quotient.eq_zero_iff_mem] using hj
      simpa using hle hx
    · obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (ψC c)
      refine ⟨Ideal.Quotient.mk J s, ?_⟩
      rw [Henselization.reducedMap_mk, Ideal.Quotient.eq]
      exact hker _ (by simp [hs])
  -- `C` is an étale neighbourhood of `(S, J)`, so it has a section `τ`.
  obtain ⟨τ⟩ := Henselization.nonempty_algHom_of_bijective_reducedMap J hbij
  -- Maps out of `C` to `S ⧸ J` are unique, so `τ` reduces to `ψC` modulo `J`.
  have hsurj : Function.Surjective (algebraMap (S ⧸ J) (C ⧸ J.map (algebraMap S C))) :=
    fun y ↦ by
      obtain ⟨x, rfl⟩ := hbij.2 y
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨Ideal.Quotient.mk J s, by simp⟩
  have hτ : (Ideal.Quotient.mkₐ S J).comp τ = ψC :=
    Ideal.algHom_ext_of_surjective_algebraMap_quotient J C hsurj (by simp) _ _
  exact ⟨τ.comp (IsScalarTower.toAlgHom S A C), AlgHom.ext fun a ↦ by
    simpa [hψC] using AlgHom.congr_fun hτ (algebraMap A C a)⟩

end Absolute

section Relative

variable {R : Type*} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] (J : Ideal S)
  [HenselianRing S J] {A : Type v} [CommRing A] [Algebra R A] [Algebra.Etale R A]

/-- The relative form of `comp_bijective`: for a Henselian pair `(S, J)` with `S` an `R`-algebra
and an étale `R`-algebra `A`, reduction modulo `J` is a bijection from `R`-algebra maps `A → S` to
`R`-algebra maps `A → S ⧸ J`. The base is arbitrary; `comp_bijective` is the case `R = S`. -/
@[stacks 09XI "(1) ⇒ (2), relative form over an arbitrary base"]
theorem comp_bijective_of_algebra :
    Function.Bijective ((Ideal.Quotient.mkₐ R J).comp : (A →ₐ[R] S) → A →ₐ[R] S ⧸ J) :=
  -- Base change `A` to the étale `S`-algebra `S ⊗[R] A` and apply `comp_bijective` over `S`.
  (AlgHom.restrictScalars_comp_bijective_iff R A (Ideal.Quotient.mkₐ S J)).mpr
    (comp_bijective J)

end Relative

end HenselianRing

/-- **Henselian pairs are characterised by lifting sections of étale algebras.** A pair `(R, I)`
is Henselian if and only if every `R`-algebra map from an étale `R`-algebra to `R ⧸ I` lifts to an
`R`-algebra map to `R`. The condition does not assume that `I` lies in the Jacobson radical. -/
@[stacks 09XI "(1) ⇔ (2)"]
theorem henselianRing_iff_forall_comp_surjective {R : Type u} [CommRing R] {I : Ideal R} :
    HenselianRing R I ↔ ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A],
      Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] R) → A →ₐ[R] R ⧸ I) := by
  refine ⟨fun _ A _ _ _ ↦ (HenselianRing.comp_bijective I).2, fun h ↦ ⟨fun x hx ↦ ?_, ?_⟩⟩
  · -- A unit `u ≡ 1 mod I` of `R ⧸ I` lifts along `R → R[1/u]`, so `u` is a unit of `R`.
    refine Ideal.mem_jacobson_bot.mpr fun y ↦ ?_
    have hu : Ideal.Quotient.mk I (x * y + 1) = 1 := by
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right y hx)]
    have := Algebra.Etale.of_isLocalizationAway (A := Localization.Away (x * y + 1)) (x * y + 1)
    obtain ⟨φ, -⟩ := h (Localization.Away (x * y + 1))
      (IsLocalization.Away.liftAlgHom (x * y + 1) (f := Algebra.ofId R (R ⧸ I)) (by simp [hu]))
    simpa using (IsLocalization.Away.algebraMap_isUnit (x * y + 1)).map φ
  · -- A simple root modulo `I` of a monic `f` is a section modulo `I` of `R[X]_{f'} ⧸ (f)`.
    intro f hf a₀ hfa₀ hf'a₀
    let P : StandardEtalePair R := ⟨f, hf, derivative f, 1, 0, 1, by ring⟩
    have hev (p : R[X]) : aeval (Ideal.Quotient.mk I a₀) p = Ideal.Quotient.mk I (p.eval a₀) := by
      rw [← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply, coe_aeval_eq_eval]
    have hP : P.HasMap (Ideal.Quotient.mk I a₀) :=
      ⟨(hev f).trans (Ideal.Quotient.eq_zero_iff_mem.mpr hfa₀), (hev (derivative f)) ▸ hf'a₀⟩
    obtain ⟨φ, hφ⟩ := h P.Ring (P.lift _ hP)
    refine ⟨φ P.X, ?_, Ideal.Quotient.eq.mp ?_⟩
    · simpa [coe_aeval_eq_eval] using (StandardEtalePair.hasMap_X.map φ).1
    · simpa using AlgHom.congr_fun hφ P.X

end TauCeti
