/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.RingTheory.Henselian.Section
import TauCeti.RingTheory.Kaehler.Conormal
import TauCeti.RingTheory.Kaehler.FormallyEtale
import TauCeti.RingTheory.Kaehler.Localization

/-!
# Sections of smooth algebras over a Henselian pair

Let `(R, I)` be a Henselian pair and `A` a smooth `R`-algebra. An `R`-algebra map
`σ : A → R ⧸ I` is a section of `Spec A → Spec R` over the closed subscheme `V(I)`. Elkik's
theorem says that every such section extends to a section `A → R` over all of `Spec R`. This file
proves it when the differentials of `A` restricted to the section, the `A ⧸ ker σ`-module
`Ω[A⁄R] ⧸ (ker σ) • Ω[A⁄R]`, are free (`TauCeti.HenselianRing.exists_comp_eq_of_free`). This
holds when `R ⧸ I` is local (`TauCeti.HenselianRing.comp_surjective_of_isLocalRing`), and in
particular for a Henselian local ring and its residue field
(`TauCeti.HenselianLocalRing.comp_surjective_of_smooth`). The general case reduces to the free
one after adjoining the symmetric algebra of a finite projective complement of that module.

The proof follows the Stacks Project. Lift a basis of `Ω[A⁄R] ⧸ J Ω[A⁄R]`, with `J = ker σ`, to
differentials `D xᵢ` of elements `xᵢ ∈ J`. By Nakayama's lemma, after inverting some
`g ≡ 1 (mod J)` the `D xᵢ` form a basis of `Ω[A[1/g]⁄R]`, so `A[1/g] ⧸ (xᵢ)` is étale over `R`.
The section `σ` factors through it, and sections of étale algebras lift over a Henselian pair
(`TauCeti.HenselianRing.comp_bijective`).

## Main results

* `TauCeti.HenselianRing.exists_comp_eq_of_free`: over a Henselian pair `(R, I)`, a section
  `σ : A →ₐ[R] R ⧸ I` of a smooth `R`-algebra lifts to `A →ₐ[R] R` when the differentials of `A`
  restricted to the section are free.
* `TauCeti.HenselianRing.comp_surjective_of_isLocalRing`: the same for every section, when
  `R ⧸ I` is local.
* `TauCeti.HenselianLocalRing.comp_surjective_of_smooth`: over a Henselian local ring, every
  residue-field point of a smooth algebra lifts to an `R`-point.

## References

* [Stacks Project, Lemma 15.13.3](https://stacks.math.columbia.edu/tag/0H74), via Lemma 15.9.14
  ([Tag 07M7](https://stacks.math.columbia.edu/tag/07M7)), whose proof in the free case is
  followed here.
* R. Elkik, *Solutions d'équations à coefficients dans un anneau hensélien*, Ann. Sci. École
  Norm. Sup. (4) 6 (1973), 553–603.
-/

public section

open KaehlerDifferential

universe u v

namespace TauCeti.HenselianRing

variable {R : Type u} [CommRing R] (I : Ideal R) [HenselianRing R I]
  {A : Type v} [CommRing A] [Algebra R A]

/-- If `A ⧸ ker σ` is trivial, then so is `R ⧸ I`, so `I = ⊤`; as `I` lies in the Jacobson radical,
`R` and `A` are trivial and any map is a lift. -/
private theorem exists_comp_eq_of_subsingleton (σ : A →ₐ[R] R ⧸ I)
    (hσ : Subsingleton (A ⧸ RingHom.ker σ)) :
    ∃ φ : A →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp φ = σ := by
  have hI : I = ⊤ := by
    -- `1 ∈ ker σ`, so `1 = σ 1 = 0` in `R ⧸ I`.
    have h1 : (1 : A) ∈ RingHom.ker σ := Ideal.Quotient.subsingleton_iff.mp hσ ▸ trivial
    have h10 : (1 : R ⧸ I) = 0 := by simpa using RingHom.mem_ker.mp h1
    rw [← Ideal.Quotient.subsingleton_iff]
    exact subsingleton_of_zero_eq_one h10.symm
  have : Subsingleton R := by
    have := Ring.mem_jacobson_iff.mp
      (HenselianRing.jac (I := I) (hI ▸ Submodule.mem_top (x := (1 : R)))) (-1)
    exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp (by simpa using this))
  have : Subsingleton A := subsingleton_of_zero_eq_one (by
    rw [← map_zero (algebraMap R A), ← map_one (algebraMap R A), Subsingleton.elim (0 : R) 1])
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId R A) ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
    fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩).symm.toAlgHom, AlgHom.ext fun _ ↦ Subsingleton.elim _ _⟩

/-- **Elkik's lifting, for free differentials along the section.** Let `(R, I)` be a Henselian
pair, `A` a smooth `R`-algebra and `σ : A →ₐ[R] R ⧸ I`. If the differentials of `A` restricted to
the section, the `A ⧸ ker σ`-module `Ω[A⁄R] ⧸ (ker σ) • Ω[A⁄R]`, are free, then `σ` lifts to an
`R`-algebra map `A →ₐ[R] R`. -/
@[stacks 0H74 "when the differentials restricted to the section are free"]
theorem exists_comp_eq_of_free [Algebra.Smooth R A] (σ : A →ₐ[R] R ⧸ I)
    [Module.Free (A ⧸ RingHom.ker σ) (Ω[A⁄R] ⧸ RingHom.ker σ • (⊤ : Submodule A Ω[A⁄R]))] :
    ∃ φ : A →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp φ = σ := by
  set J := RingHom.ker σ
  by_cases hJ : Subsingleton (A ⧸ J)
  · exact exists_comp_eq_of_subsingleton I σ hJ
  have : Nontrivial (A ⧸ J) := not_subsingleton_iff_nontrivial.mp hJ
  -- `R → A ⧸ J` is surjective, as `A ⧸ J ≅ R ⧸ I`.
  have hR : Function.Surjective (algebraMap R (A ⧸ J)) := fun y ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (σ a)
    exact ⟨r, (Ideal.Quotient.eq.mpr (by simp [J, RingHom.mem_ker, ← hr])).symm⟩
  -- Lift a basis of `Ω ⧸ J Ω` to differentials `D xᵢ` with `xᵢ ∈ J`; they form a basis of
  -- `Ω[W⁄R]` for `W = A[1/g]` with `g ≡ 1 (mod J)`.
  let b := Module.Free.chooseBasis (A ⧸ J) (Ω[A⁄R] ⧸ J • (⊤ : Submodule A Ω[A⁄R]))
  have : Finite (Module.Free.ChooseBasisIndex (A ⧸ J) _) := Module.Finite.finite_basis b
  have : Algebra.FormallyUnramified R (A ⧸ J) := .of_surjective (Algebra.ofId R (A ⧸ J)) hR
  choose x hxJ hxb using fun i ↦ KaehlerDifferential.exists_mem_and_mk_D_eq J (b i)
  obtain ⟨g, hgJ, bW, hbW⟩ :=
    KaehlerDifferential.exists_sub_one_mem_and_basis_localizationAway J b fun i ↦ (hxb i).symm
  let W := Localization.Away g
  have : Algebra.Smooth A W := .of_isLocalization_Away g
  have : Algebra.Smooth R W := .comp R A W
  -- So `W ⧸ (xᵢ)` is étale over `R`, and `σ` factors through it.
  let K : Ideal W := Ideal.span (Set.range fun i ↦ algebraMap A W (x i))
  have : Algebra.Etale R (W ⧸ K) := bW.etale_quotient_span_range hbW
  let σW : W →ₐ[R] R ⧸ I := IsLocalization.Away.liftAlgHom g (f := σ)
    (by simp [show σ g = 1 by simpa [J, sub_eq_zero] using hgJ])
  have hσW (a : A) : σW (algebraMap A W a) = σ a := by
    simp [σW, IsLocalization.Away.liftAlgHom_apply]
  have hK : ∀ w ∈ K, σW w = 0 := fun w hw ↦ by
    refine (Ideal.span_le (I := RingHom.ker σW)).mpr ?_ hw
    rintro _ ⟨i, rfl⟩
    simpa [hσW] using RingHom.mem_ker.mp (hxJ i)
  have hτ (a : A) : Ideal.Quotient.liftₐ K σW hK (Ideal.Quotient.mk _ (algebraMap A W a)) = σ a :=
    (AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp K σW hK) (algebraMap A W a)).trans (hσW a)
  -- Sections of étale algebras lift over the Henselian pair `(R, I)`.
  obtain ⟨ρ, hρ⟩ := (HenselianRing.comp_bijective I).2 (Ideal.Quotient.liftₐ K σW hK)
  refine ⟨ρ.comp ((Ideal.Quotient.mkₐ R K).comp (IsScalarTower.toAlgHom R A W)),
    AlgHom.ext fun a ↦ ?_⟩
  rw [← hτ]
  exact AlgHom.congr_fun hρ (Ideal.Quotient.mk _ (algebraMap A W a))

/-- Over a Henselian pair `(R, I)` with `R ⧸ I` local, for instance a Henselian pair with `R`
local, every `R`-algebra map from a smooth `R`-algebra to `R ⧸ I` lifts to `R`. -/
theorem comp_surjective_of_isLocalRing [Algebra.Smooth R A] [IsLocalRing (R ⧸ I)] :
    Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] R) → A →ₐ[R] R ⧸ I) := by
  intro σ
  have hσ : Function.Surjective σ := fun y ↦ by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨algebraMap R A r, by simp⟩
  -- `A ⧸ ker σ ≅ R ⧸ I` is local, and `Ω ⧸ (ker σ) Ω` is finite and flat over it, hence free.
  let e := Ideal.quotientKerAlgEquivOfSurjective hσ
  have := e.toEquiv.nontrivial
  have := IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  have : Module.Flat (A ⧸ RingHom.ker σ) (Ω[A⁄R] ⧸ RingHom.ker σ • (⊤ : Submodule A Ω[A⁄R])) :=
    .of_linearEquiv ((TensorProduct.quotTensorEquivQuotSMul _ _).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective).symm
  have := Module.free_of_flat_of_isLocalRing (R := A ⧸ RingHom.ker σ)
    (P := Ω[A⁄R] ⧸ RingHom.ker σ • (⊤ : Submodule A Ω[A⁄R]))
  exact exists_comp_eq_of_free I σ

end TauCeti.HenselianRing

namespace TauCeti.HenselianLocalRing

open IsLocalRing

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {A : Type v} [CommRing A] [Algebra R A] [Algebra.Smooth R A]

/-- Over a Henselian local ring `R`, every `R`-algebra map from a smooth `R`-algebra to the residue
field lifts to an `R`-algebra map to `R`. -/
theorem comp_surjective_of_smooth :
    Function.Surjective
      ((Algebra.ofId R (ResidueField R)).comp : (A →ₐ[R] R) → A →ₐ[R] ResidueField R) := by
  intro ψ
  -- Identify the residue field with `R ⧸ 𝔪`, where the Henselian pair `(R, 𝔪)` applies.
  let e : ResidueField R ≃ₐ[R] R ⧸ maximalIdeal R :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R (ResidueField R))
      residue_surjective).symm.trans (Ideal.quotientEquivAlgOfEq R ker_residue)
  have : IsLocalRing (R ⧸ maximalIdeal R) := .of_surjective' (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective
  obtain ⟨φ, hφ⟩ := HenselianRing.comp_surjective_of_isLocalRing (maximalIdeal R)
    (e.toAlgHom.comp ψ)
  refine ⟨φ, AlgHom.ext fun a ↦ e.injective ?_⟩
  rw [AlgHom.comp_apply, Algebra.ofId_apply, AlgEquiv.commutes, Ideal.Quotient.algebraMap_eq]
  simpa using AlgHom.congr_fun hφ a

end TauCeti.HenselianLocalRing


