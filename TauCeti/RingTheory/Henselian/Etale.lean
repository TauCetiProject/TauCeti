/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Unramified.LocalStructure

import TauCeti.RingTheory.Henselian.Basic
import TauCeti.RingTheory.Henselian.Section
import TauCeti.RingTheory.LocalRing.ResidueField.Ideal
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient
import TauCeti.RingTheory.TensorProduct.LiftEquiv
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

In terms of prime ideals, an `R`-algebra retraction `τ : S → R` cuts out the prime `𝔮 = τ⁻¹(𝔪_R)`
lying over `𝔪_R` with `κ(𝔪_R) → κ(𝔮)` bijective; conversely, over a Henselian local ring every
such prime of an étale `R`-algebra comes from a unique `R`-algebra retraction
(`TauCeti.HenselianLocalRing.existsUnique_algHom_comap_maximalIdeal_of_residueFieldMap_surjective`),
and this property characterises Henselian local rings (`TauCeti.HenselianLocalRing.tfae_etale`).

## Main results

* `TauCeti.HenselianLocalRing.comp_bijective`: over a Henselian local ring, `R`-points of an étale
  algebra are in bijection with its points over the residue field.
* `TauCeti.HenselianLocalRing.existsUnique_algHom_comap_maximalIdeal_of_residueFieldMap_surjective`:
  for a prime `𝔮` of an étale `R`-algebra over `𝔪_R` with `κ(𝔪_R) → κ(𝔮)` surjective, there is a
  unique `R`-algebra retraction `τ : S → R` with `τ⁻¹(𝔪_R) = 𝔮`.
* `TauCeti.HenselianLocalRing.tfae_etale`: equivalence of `HenselianLocalRing R`,
  `HenselianRing R (maximalIdeal R)`, lifting of residue-field points of étale `R`-algebras, and
  unique retractions at primes over `𝔪_R` with trivial residue field extension (Stacks, Tag 04GG).
* `TauCeti.HenselianLocalRing.comp_bijective_of_algebra`: the relative form for an étale algebra
  over an arbitrary base `R` and a Henselian local `R`-algebra `S`.

## References

* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG), characterisations of
  Henselian local rings by sections of étale algebras.
* [Stacks Project, Lemma 10.153.11, Tag 08HQ](https://stacks.math.columbia.edu/tag/08HQ), unique
  lifting of residue field points of an étale algebra to a Henselian local algebra over an
  arbitrary base.
-/

public section

open _root_.IsLocalRing TauCeti.IsLocalRing Polynomial TensorProduct

universe u

namespace TauCeti

namespace HenselianLocalRing

section Henselian

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

/-- Every residue-field point `ψ : S →ₐ[R] ResidueField R` of an étale `R`-algebra over a
Henselian local ring `R` lifts to a unique `R`-algebra retraction `φ : S →ₐ[R] R`. -/
@[stacks 04GG "unique lift of a residue field point"]
theorem existsUnique_algHom_comp_eq [Algebra.Etale R S] (ψ : S →ₐ[R] ResidueField R) :
    ∃! φ : S →ₐ[R] R, (Algebra.ofId R (ResidueField R)).comp φ = ψ :=
  comp_bijective.existsUnique ψ

/-- Over a Henselian local ring `R`, every prime `𝔮` of an étale `R`-algebra `S` lying over `𝔪_R`
such that `κ(𝔪_R) → κ(𝔮)` is surjective is the preimage of `𝔪_R` under a unique `R`-algebra
retraction `τ : S →ₐ[R] R`. -/
@[stacks 04GG "(1) ⇒ (8)"]
theorem existsUnique_algHom_comap_maximalIdeal_of_residueFieldMap_surjective [Algebra.Etale R S]
    {𝔮 : Ideal S} [𝔮.IsPrime] (h𝔮 : 𝔮.comap (algebraMap R S) = maximalIdeal R)
    (hκ : Function.Surjective
      (Ideal.ResidueField.map (maximalIdeal R) 𝔮 (algebraMap R S) h𝔮.symm)) :
    ∃! τ : S →ₐ[R] R, (maximalIdeal R).comap τ = 𝔮 := by
  obtain ⟨ψ, hψ⟩ := exists_algHom_residueField_ker_eq h𝔮 hκ
  obtain ⟨τ, hτ, _⟩ := existsUnique_algHom_comp_eq ψ
  have hτ_comap : (maximalIdeal R).comap τ = 𝔮 := by
    rw [← τ.ker_residue_comp_eq_comap_maximalIdeal, hτ, hψ]
  refine ⟨τ, hτ_comap, fun τ' hτ' ↦ comp_bijective.1 (algHom_residueField_eq_of_ker_eq ?_)⟩
  rw [τ'.ker_residue_comp_eq_comap_maximalIdeal, τ.ker_residue_comp_eq_comap_maximalIdeal,
    hτ', hτ_comap]

/-- Over a Henselian local ring `R`, a prime `𝔮` of an étale `R`-algebra `S` lying over `𝔪_R`
is cut out by an `R`-algebra retraction `τ : S →ₐ[R] R` if and only if `κ(𝔪_R) → κ(𝔮)` is
bijective. -/
@[stacks 04GG "(8)"]
theorem exists_algHom_comap_maximalIdeal_iff [Algebra.Etale R S] {𝔮 : Ideal S} [𝔮.IsPrime]
    (h𝔮 : 𝔮.comap (algebraMap R S) = maximalIdeal R) :
    (∃ τ : S →ₐ[R] R, (maximalIdeal R).comap τ = 𝔮) ↔
      Function.Bijective
        (Ideal.ResidueField.map (maximalIdeal R) 𝔮 (algebraMap R S) h𝔮.symm) :=
  ⟨fun ⟨_, hτ⟩ ↦ Ideal.ResidueField.map_bijective_of_comap hτ h𝔮,
    fun hκ ↦
      (existsUnique_algHom_comap_maximalIdeal_of_residueFieldMap_surjective h𝔮
        hκ.surjective).exists⟩

end Henselian

/-- **Étale retraction characterisations of Henselian local rings.** For a local ring `R`, the
following are equivalent:
1. `R` is a Henselian local ring;
2. `(R, 𝔪_R)` is a Henselian pair;
3. for every étale `R`-algebra `S`, reduction modulo `𝔪_R` is a bijection
   `(S →ₐ[R] R) → (S →ₐ[R] ResidueField R)`;
4. for every étale `R`-algebra `S`, every `R`-algebra map `S →ₐ[R] ResidueField R` lifts to
   `S →ₐ[R] R`;
5. for every étale `R`-algebra `S` and prime `𝔮` over `𝔪_R` with `κ(𝔪_R) → κ(𝔮)` bijective,
   there is a unique `R`-algebra retraction `τ : S →ₐ[R] R` with `τ⁻¹(𝔪_R) = 𝔮`. -/
@[stacks 04GG]
theorem tfae_etale (R : Type u) [CommRing R] [_root_.IsLocalRing R] :
    List.TFAE
      [HenselianLocalRing R,
        HenselianRing R (maximalIdeal R),
        ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S],
          Function.Bijective
            ((Algebra.ofId R (ResidueField R)).comp : (S →ₐ[R] R) → S →ₐ[R] ResidueField R),
        ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S],
          Function.Surjective
            ((Algebra.ofId R (ResidueField R)).comp : (S →ₐ[R] R) → S →ₐ[R] ResidueField R),
        ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S] (𝔮 : Ideal S) [𝔮.IsPrime]
          (h𝔮 : 𝔮.comap (algebraMap R S) = maximalIdeal R),
          Function.Bijective
            (Ideal.ResidueField.map (maximalIdeal R) 𝔮 (algebraMap R S) h𝔮.symm) →
            ∃! τ : S →ₐ[R] R, (maximalIdeal R).comap τ = 𝔮] := by
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 → 1 := fun _ ↦ HenselianRing.henselianLocalRing R
  tfae_have 1 → 3 := fun _ _ _ _ _ ↦ comp_bijective
  tfae_have 3 → 4 := fun h S _ _ _ ↦ (h S).surjective
  tfae_have 1 → 5 := fun _ _ _ _ _ _ _ h𝔮 hκ ↦
    existsUnique_algHom_comap_maximalIdeal_of_residueFieldMap_surjective h𝔮 hκ.surjective
  tfae_have 5 → 4 := by
    intro h S _ _ _ ψ
    have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
    have h𝔮 := ψ.comap_ker_residueField
    obtain ⟨τ, hτ, -⟩ := h S (RingHom.ker ψ) h𝔮 (ψ.residueFieldMap_bijective_of_ker_eq rfl h𝔮)
    refine ⟨τ, algHom_residueField_eq_of_ker_eq ?_⟩
    rw [τ.ker_residue_comp_eq_comap_maximalIdeal, hτ]
  tfae_have 4 → 2 := by
    intro h
    let := Ideal.Quotient.field (maximalIdeal R)
    let e : (R ⧸ maximalIdeal R) ≃ₐ[R] ResidueField R :=
      (residueFieldAlgEquivOfSurjective (Ideal.Quotient.mkₐ_surjective R (maximalIdeal R))).symm
    refine henselianRing_iff_forall_comp_surjective.mpr fun A _ _ _ ψ ↦ ?_
    obtain ⟨φ, hφ⟩ := h A (e.toAlgHom.comp ψ)
    refine ⟨φ, AlgHom.ext fun a ↦ e.injective ?_⟩
    rw [AlgHom.comp_apply,
      residueFieldAlgEquivOfSurjective_symm_apply
        (Ideal.Quotient.mkₐ_surjective R (maximalIdeal R)),
      ← ResidueField.algebraMap_eq]
    exact AlgHom.congr_fun hφ a
  tfae_finish

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
        (A →ₐ[R] S) → A →ₐ[R] ResidueField S) :=
  -- Base change `A` to the étale `S`-algebra `S ⊗[R] A` and apply `comp_bijective` over `S`.
  (AlgHom.restrictScalars_comp_bijective_iff R A (Algebra.ofId S (ResidueField S))).mpr
    (comp_bijective (R := S) (S := S ⊗[R] A))

end Relative

end HenselianLocalRing

end TauCeti
