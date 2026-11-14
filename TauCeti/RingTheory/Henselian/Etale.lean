/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Unramified.LocalStructure
public import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Basic

import TauCeti.RingTheory.Henselian.Basic
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
(`TauCeti.HenselianLocalRing.existsUnique_algHom_of_surjective_residueField_map`), and this
property characterises Henselian local rings (`TauCeti.HenselianLocalRing.tfae_etale`).

Consequently a *strictly Henselian* local ring, one whose residue field is separably closed, has
no nonsplit finite étale covers (`TauCeti.IsFiniteEtaleSplit.of_henselianLocalRing`): a faithfully
flat finite étale algebra has a `k`-point because `k` is separably closed, and this lifts to a
section. Such rings need be neither fields nor reduced. As the spectrum of a local ring is
connected, every finite étale algebra over a strictly Henselian local ring is moreover a finite
product of copies of the base (`Algebra.IsFiniteSplit.of_henselianLocalRing`).

## Main results

* `TauCeti.HenselianLocalRing.comp_bijective`: over a Henselian local ring, `R`-points of an étale
  algebra are in bijection with its points over the residue field.
* `TauCeti.HenselianLocalRing.existsUnique_algHom_of_surjective_residueField_map`: for a prime `𝔮`
  of an étale `R`-algebra over `𝔪_R` with `κ(𝔪_R) → κ(𝔮)` surjective, there is a unique
  `R`-algebra retraction `τ : S → R` with `τ⁻¹(𝔪_R) = 𝔮`.
* `TauCeti.HenselianLocalRing.tfae_etale`: equivalence of `HenselianLocalRing R`,
  `HenselianRing R (maximalIdeal R)`, lifting of residue-field points of étale `R`-algebras, and
  unique retractions at primes over `𝔪_R` with trivial residue field extension (Stacks, Tag 04GG).
* `TauCeti.HenselianLocalRing.comp_bijective_of_algebra`: the relative form for an étale algebra
  over an arbitrary base `R` and a Henselian local `R`-algebra `S`.
* `TauCeti.IsFiniteEtaleSplit.of_henselianLocalRing`: a Henselian local ring with separably
  closed residue field has no nonsplit finite étale covers.
* `Algebra.IsFiniteSplit.of_henselianLocalRing`: over such a ring every finite étale algebra is a
  finite product of copies of the base.

## References

* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG), characterisations of
  Henselian local rings by sections of étale algebras.
* [Stacks Project, Lemma 10.153.11, Tag 08HQ](https://stacks.math.columbia.edu/tag/08HQ), unique
  lifting of residue field points of an étale algebra to a Henselian local algebra over an
  arbitrary base.
* P. Scholze, *Étale cohomology of diamonds*, Lemma 15.3, for rings without nonsplit finite étale
  covers.
-/

public section

open IsLocalRing Polynomial TensorProduct

universe u

namespace TauCeti

namespace HenselianLocalRing

section Local

variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]

/-- Two `R`-algebra maps `S →ₐ[R] ResidueField R` with the same kernel coincide, because
`R → ResidueField R` is surjective. -/
private theorem algHom_residueField_eq_of_ker_eq {ψ₁ ψ₂ : S →ₐ[R] ResidueField R}
    (hker : RingHom.ker ψ₁ = RingHom.ker ψ₂) : ψ₁ = ψ₂ := by
  ext s
  obtain ⟨r, hr⟩ := residue_surjective (ψ₁ s)
  have hmem : s - algebraMap R S r ∈ RingHom.ker ψ₁ := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, ResidueField.algebraMap_eq, hr, sub_self]
  have hmem₂ : s - algebraMap R S r ∈ RingHom.ker ψ₂ := hker ▸ hmem
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero, ResidueField.algebraMap_eq, hr]
    at hmem₂
  exact hmem₂.symm

/-- The kernel of the reduction `S → R → ResidueField R` of an `R`-algebra retraction `τ : S → R`
is `τ⁻¹(𝔪_R)`. -/
private theorem ker_residue_comp_eq_comap_maximalIdeal (τ : S →ₐ[R] R) :
    RingHom.ker ((Algebra.ofId R (ResidueField R)).comp τ) = (maximalIdeal R).comap τ := by
  ext s
  simp [RingHom.mem_ker, ResidueField.algebraMap_eq]

/-- The kernel of an `R`-algebra map `S →ₐ[R] ResidueField R` lies over `𝔪_R`. -/
private theorem comap_ker_algHom_residueField (ψ : S →ₐ[R] ResidueField R) :
    (RingHom.ker ψ).comap (algebraMap R S) = maximalIdeal R := by
  ext r
  simp [Ideal.mem_comap, RingHom.mem_ker, ResidueField.algebraMap_eq]

/-- If `𝔮` is the kernel of an `R`-algebra map `ψ : S →ₐ[R] ResidueField R`, then the induced map
`κ(𝔪_R) → κ(𝔮)` on residue fields is bijective. -/
private theorem bijective_residueField_map_of_ker_eq (ψ : S →ₐ[R] ResidueField R) {𝔮 : Ideal S}
    [𝔮.IsPrime] (hker : RingHom.ker ψ = 𝔮)
    (h𝔮 : 𝔮.comap (algebraMap R S) = maximalIdeal R := hker ▸ comap_ker_algHom_residueField ψ) :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) 𝔮 (algebraMap R S) h𝔮.symm) := by
  let liftψ : 𝔮.ResidueField →ₐ[R] ResidueField R :=
    Ideal.ResidueField.liftₐ 𝔮 ψ hker.symm.le fun s hs ↦ by
      rw [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
      intro h0
      exact hs (hker ▸ RingHom.mem_ker.mpr h0)
  refine ⟨RingHom.injective _, fun y ↦ ?_⟩
  obtain ⟨r, hr⟩ := residue_surjective (liftψ y)
  refine ⟨algebraMap R (maximalIdeal R).ResidueField r, liftψ.toRingHom.injective ?_⟩
  change liftψ (Ideal.ResidueField.map (maximalIdeal R) 𝔮 (algebraMap R S) h𝔮.symm
    (algebraMap R (maximalIdeal R).ResidueField r)) = liftψ y
  rw [Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.liftₐ_algebraMap,
    AlgHom.commutes, ResidueField.algebraMap_eq, hr]

/-- If `τ : S →ₐ[R] R` satisfies `τ⁻¹(𝔪_R) = 𝔮`, then `𝔮` lies over `𝔪_R` and `κ(𝔪_R) → κ(𝔮)`
is bijective. -/
private theorem bijective_residueField_map_of_comap_maximalIdeal {τ : S →ₐ[R] R} {𝔮 : Ideal S}
    [𝔮.IsPrime] (hτ : (maximalIdeal R).comap τ = 𝔮)
    (h𝔮 : 𝔮.comap (algebraMap R S) = maximalIdeal R := by
      rw [← hτ, Ideal.comap_comap]
      simpa [RingHom.ext_iff] using congrArg (maximalIdeal R).comap τ.comp_algebraMap) :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) 𝔮 (algebraMap R S) h𝔮.symm) :=
  bijective_residueField_map_of_ker_eq ((Algebra.ofId R (ResidueField R)).comp τ)
    ((ker_residue_comp_eq_comap_maximalIdeal τ).trans hτ) h𝔮

/-- A prime `𝔮` of `S` over `𝔪_R` with `κ(𝔪_R) → κ(𝔮)` surjective is the kernel of an
`R`-algebra map `S →ₐ[R] ResidueField R`. -/
private theorem exists_algHom_residueField_ker_eq {𝔮 : Ideal S} [𝔮.IsPrime]
    (h𝔮 : 𝔮.comap (algebraMap R S) = maximalIdeal R)
    (hκ : Function.Surjective
      (Ideal.ResidueField.map (maximalIdeal R) 𝔮 (algebraMap R S) h𝔮.symm)) :
    ∃ ψ : S →ₐ[R] ResidueField R, RingHom.ker ψ = 𝔮 := by
  let f := Ideal.ResidueField.mapₐ (maximalIdeal R) 𝔮 (Algebra.ofId R S) h𝔮.symm
  let e : (maximalIdeal R).ResidueField ≃ₐ[R] 𝔮.ResidueField :=
    AlgEquiv.ofBijective f ⟨f.toRingHom.injective, hκ⟩
  let g : (maximalIdeal R).ResidueField →ₐ[R] ResidueField R :=
    Ideal.ResidueField.liftₐ (maximalIdeal R) (Algebra.ofId R (ResidueField R))
      (by
        intro r hr
        rwa [RingHom.mem_ker, Algebra.ofId_apply, ResidueField.algebraMap_eq, residue_eq_zero_iff])
      fun r hr ↦ by
        rw [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, Algebra.ofId_apply,
          ResidueField.algebraMap_eq, isUnit_iff_ne_zero, ne_eq, residue_eq_zero_iff]
        exact hr
  refine ⟨(g.comp e.symm.toAlgHom).comp (IsScalarTower.toAlgHom R S 𝔮.ResidueField), ?_⟩
  ext s
  change g (e.symm (algebraMap S 𝔮.ResidueField s)) = 0 ↔ s ∈ 𝔮
  rw [map_eq_zero_iff g g.toRingHom.injective, map_eq_zero_iff e.symm e.symm.injective,
    Ideal.algebraMap_residueField_eq_zero]

end Local

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
theorem existsUnique_algHom_of_etale [Algebra.Etale R S] (ψ : S →ₐ[R] ResidueField R) :
    ∃! φ : S →ₐ[R] R, (Algebra.ofId R (ResidueField R)).comp φ = ψ :=
  comp_bijective.existsUnique ψ

/-- Over a Henselian local ring `R`, every prime `𝔮` of an étale `R`-algebra `S` lying over `𝔪_R`
such that `κ(𝔪_R) → κ(𝔮)` is surjective is the preimage of `𝔪_R` under a unique `R`-algebra
retraction `τ : S →ₐ[R] R`. -/
@[stacks 04GG "(1) ⇒ (8)"]
theorem existsUnique_algHom_of_surjective_residueField_map [Algebra.Etale R S] {𝔮 : Ideal S}
    [𝔮.IsPrime] (h𝔮 : 𝔮.comap (algebraMap R S) = maximalIdeal R)
    (hκ : Function.Surjective
      (Ideal.ResidueField.map (maximalIdeal R) 𝔮 (algebraMap R S) h𝔮.symm)) :
    ∃! τ : S →ₐ[R] R, (maximalIdeal R).comap τ = 𝔮 := by
  obtain ⟨ψ, hψ⟩ := exists_algHom_residueField_ker_eq h𝔮 hκ
  obtain ⟨τ, hτ, _⟩ := existsUnique_algHom_of_etale ψ
  refine ⟨τ, ?_, fun τ' hτ' ↦ comp_bijective.1 (algHom_residueField_eq_of_ker_eq ?_)⟩
  · dsimp only
    rw [← ker_residue_comp_eq_comap_maximalIdeal, hτ, hψ]
  · rw [ker_residue_comp_eq_comap_maximalIdeal, ker_residue_comp_eq_comap_maximalIdeal,
      hτ', ← ker_residue_comp_eq_comap_maximalIdeal, hτ, hψ]

/-- Over a Henselian local ring `R`, a prime `𝔮` of an étale `R`-algebra `S` lying over `𝔪_R`
is cut out by an `R`-algebra retraction `τ : S →ₐ[R] R` if and only if `κ(𝔪_R) → κ(𝔮)` is
bijective. -/
@[stacks 04GG "(8)"]
theorem exists_algHom_comap_maximalIdeal_iff [Algebra.Etale R S] {𝔮 : Ideal S} [𝔮.IsPrime]
    (h𝔮 : 𝔮.comap (algebraMap R S) = maximalIdeal R) :
    (∃ τ : S →ₐ[R] R, (maximalIdeal R).comap τ = 𝔮) ↔
      Function.Bijective
        (Ideal.ResidueField.map (maximalIdeal R) 𝔮 (algebraMap R S) h𝔮.symm) :=
  ⟨fun ⟨_, hτ⟩ ↦ bijective_residueField_map_of_comap_maximalIdeal hτ h𝔮,
    fun hκ ↦ (existsUnique_algHom_of_surjective_residueField_map h𝔮 hκ.surjective).exists⟩

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
theorem tfae_etale (R : Type u) [CommRing R] [IsLocalRing R] :
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
    existsUnique_algHom_of_surjective_residueField_map h𝔮 hκ.surjective
  tfae_have 5 → 4 := by
    intro h S _ _ _ ψ
    have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
    have h𝔮 := comap_ker_algHom_residueField ψ
    obtain ⟨τ, hτ, -⟩ := h S (RingHom.ker ψ) h𝔮 (bijective_residueField_map_of_ker_eq ψ rfl h𝔮)
    refine ⟨τ, algHom_residueField_eq_of_ker_eq ?_⟩
    rw [ker_residue_comp_eq_comap_maximalIdeal, hτ]
  tfae_have 4 → 1 := by
    intro h
    refine ⟨fun f hf a₀ hfa₀ hf'a₀ ↦ ?_⟩
    let P : StandardEtalePair R := ⟨f, hf, derivative f, 1, 0, 1, by ring⟩
    have hev (p : R[X]) : aeval (residue R a₀) p = residue R (p.eval a₀) := by
      rw [← ResidueField.algebraMap_eq, aeval_algebraMap_apply, coe_aeval_eq_eval]
    have hP : P.HasMap (residue R a₀) :=
      ⟨(hev f).trans ((residue_eq_zero_iff _).mpr hfa₀),
        (hev (derivative f)) ▸ hf'a₀.map (residue R)⟩
    obtain ⟨φ, hφ⟩ := h P.Ring (P.lift _ hP)
    refine ⟨φ P.X, ?_, ?_⟩
    · simpa [coe_aeval_eq_eval] using (StandardEtalePair.hasMap_X.map φ).1
    · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
      simpa [ResidueField.algebraMap_eq] using AlgHom.congr_fun hφ P.X
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

/-- A Henselian local ring with separably closed residue field, that is, a strictly Henselian local
ring, has no nonsplit finite étale covers: a faithfully flat finite étale algebra has a point over
the separably closed residue field, which lifts to a section. -/
instance IsFiniteEtaleSplit.of_henselianLocalRing (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)] : IsFiniteEtaleSplit R :=
  isFiniteEtaleSplit_iff_exists_section.mpr fun T _ _ _ _ _ ↦
    have ⟨ψ⟩ := IsFiniteEtaleSplit.nonempty_algHom (ResidueField R) T
    have ⟨φ, _⟩ := (HenselianLocalRing.comp_bijective (R := R) (S := T)).2 ψ
    ⟨φ⟩

/-- **Finite étale algebras over a strictly Henselian local ring split**: over a Henselian local
ring `R` with separably closed residue field, every finite étale `R`-algebra is `R`-isomorphic to
a finite product `Fin n → R` of copies of `R`. -/
theorem _root_.Algebra.IsFiniteSplit.of_henselianLocalRing (R : Type u) [CommRing R]
    [HenselianLocalRing R] [IsSepClosed (ResidueField R)] (T : Type*) [CommRing T] [Algebra R T]
    [Algebra.Etale R T] [Module.Finite R T] : Algebra.IsFiniteSplit R T :=
  .of_isFiniteEtaleSplit T

end TauCeti
