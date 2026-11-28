/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Algebra.Module.Projective.FreeComplement
import TauCeti.LinearAlgebra.SymmetricAlgebra.Kaehler
import TauCeti.LinearAlgebra.SymmetricAlgebra.Smooth
import TauCeti.RingTheory.Kaehler.BaseChange
import TauCeti.RingTheory.Kaehler.Conormal
import TauCeti.RingTheory.Kaehler.FormallyEtale
import TauCeti.RingTheory.Kaehler.Localization

/-!
# Factoring closed-fibre points of smooth algebras through étale slices

Let `R → T` be a surjective commutative algebra map (typically `T = R ⧸ I`) and let `A` be a smooth
`R`-algebra together with an `R`-algebra map `ψ : A →ₐ[R] T`. Even when `Spec T` is disconnected or
`Ω[A⁄R]` does not have constant rank along `Spec T`, `ψ` factors through an étale `R`-algebra `C`:
there exist an étale `R`-algebra `C` (either in the universe of `A` or in the universe of `R`), an
`R`-algebra map `f : A →ₐ[R] C`, and an `R`-algebra map `ψC : C →ₐ[R] T` with `ψC ∘ f = ψ`
(`Algebra.Smooth.exists_etale_algHom_comp_eq`).

Geometrically, a smooth morphism `Spec A → Spec R` equipped with a section over a closed subscheme
`Spec T ↪ Spec R` admits an étale `R`-scheme ("étale slice") mapping to `Spec A` through which that
closed-fibre section factors. No Henselian or Noetherian hypothesis on `R` is required; when
`(R, I)` is a Henselian pair, lifting the induced `T`-point of the étale slice `C` immediately
yields Elkik's smooth lifting theorem (`TauCeti.HenselianRing.comp_surjective`).

The construction has two steps, following Stacks Project Lemma 15.13.3 (Tag 0H74):
1. **Free-cotangent retract** (`Algebra.Smooth.exists_retract_basis_kaehlerDifferential`): because
   `Ω[A⁄R]` is finitely generated projective over `A`, it admits a finite projective complement `K`
   with `Ω[A⁄R] × K ≃ₗ[A] (Fin n → A)` (`Module.Projective.exists_prod_linearEquiv_fin`). Passing to
   `B := SymmetricAlgebra A K` makes `A` an `R`-algebra retract of a smooth `R`-algebra `B` whose
   Jacobi–Zariski sequence splits globally, giving a global `B`-basis of `Ω[B⁄R]` of rank `n`.
2. **Transverse coordinates along `ker ψ`**
   (`Module.Basis.exists_etale_quotient_localizationAway`): reducing the basis of `Ω[B⁄R]` modulo
   `J • Ω[B⁄R]` (`J = ker ψ`), lifting its vectors via the conormal surjection
   (`KaehlerDifferential.exists_mem_and_mk_D_eq`) to elements `x : ι → B` in `J`, and localizing via
   `TauCeti.KaehlerDifferential.exists_sub_one_mem_and_basis_localizationAway` gives `d ≡ 1 (mod J)`
   such that the differentials `D xᵢ` form a basis of `Ω[B[1/d]⁄R]`. Quotienting `B[1/d]` by `(xᵢ)`
   then cuts out an étale `R`-algebra (`Module.Basis.etale_quotient_span_range`) through which `ψ`
   factors.

## Main results

* `Module.Basis.exists_etale_quotient_localizationAway`: when `B` is smooth over `R` with free
  differentials indexed by `ι`, `ψ` factors through an explicit étale quotient `B[1/d] ⧸ (xᵢ)`.
* `Algebra.Smooth.exists_retract_basis_kaehlerDifferential`: every smooth `R`-algebra `A` is an
  `R`-algebra retract of a smooth `R`-algebra `B` in the same universe with globally finite free
  `Ω[B⁄R]`.
* `Algebra.Smooth.exists_etale_algHom_comp_eq'` and `Algebra.Smooth.exists_etale_algHom_comp_eq`:
  every `R`-algebra map `A →ₐ[R] T` out of a smooth `R`-algebra along a surjective base map `R → T`
  factors through an étale `R`-algebra (in the universe of `A`, or in the universe of `R`).

## References

* [Stacks Project, Lemma 15.13.3](https://stacks.math.columbia.edu/tag/0H74).
-/

public section

noncomputable section

open KaehlerDifferential TensorProduct

universe u v

namespace Module.Basis

/-- When `B` is smooth over `R` and `Ω[B⁄R]` admits a `B`-basis `b` indexed by `ι`, any `R`-algebra
map `ψ : B →ₐ[R] T` with `algebraMap R T` surjective factors through an étale quotient
`Localization.Away d ⧸ (xᵢ)` with `ψ d = 1` and `ψ (x i) = 0` for all `i : ι`. -/
theorem exists_etale_quotient_localizationAway {R B T ι : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.Smooth R B] [CommRing T] [Algebra R T]
    (b : Module.Basis ι B Ω[B⁄R]) (hsurj : Function.Surjective (algebraMap R T)) (ψ : B →ₐ[R] T) :
    ∃ (d : B) (x : ι → B)
      (ψC : (Localization.Away d ⧸
        Ideal.span (Set.range (algebraMap B (Localization.Away d) ∘ x))) →ₐ[R] T),
      ψ d = 1 ∧ (∀ i, ψ (x i) = 0) ∧
      Algebra.Etale R (Localization.Away d ⧸
        Ideal.span (Set.range (algebraMap B (Localization.Away d) ∘ x))) ∧
      ψC.comp ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R B _)) = ψ := by
  by_cases hB : Subsingleton B
  · -- When `B` is subsingleton, `T` and `B[1/0] ⧸ (0)` are subsingleton and hence étale over `R`.
    have : Subsingleton T := ψ.toRingHom.codomain_trivial
    let C := Localization.Away (0 : B) ⧸
      Ideal.span (Set.range (algebraMap B (Localization.Away (0 : B)) ∘ (0 : ι → B)))
    have : Subsingleton C := (algebraMap B C).codomain_trivial
    let ψC : C →ₐ[R] T :=
      { toFun := 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ ↦ Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ ↦ Subsingleton.elim _ _
        commutes' := fun _ ↦ Subsingleton.elim _ _ }
    exact ⟨0, 0, ψC, Subsingleton.elim _ _, fun _ ↦ Subsingleton.elim _ _, inferInstance,
      Subsingleton.elim _ _⟩
  · have : Nontrivial B := not_subsingleton_iff_nontrivial.mp hB
    have : Finite ι := Module.Finite.finite_basis b
    set J : Ideal B := RingHom.ker ψ
    -- `R → B ⧸ J` is surjective since `R → T` is surjective, so `B ⧸ J` is formally unramified.
    have hRJ : Function.Surjective (algebraMap R (B ⧸ J)) := fun z ↦ by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨r, hr⟩ := hsurj (ψ y)
      exact ⟨r, (Ideal.Quotient.eq.mpr (by simp [J, RingHom.mem_ker, ← hr])).symm⟩
    have : Algebra.FormallyUnramified R (B ⧸ J) := .of_surjective (Algebra.ofId R (B ⧸ J)) hRJ
    -- Reduce `b` modulo `J • Ω[B⁄R]`, lift to differentials of elements of `J`, and localize.
    let bJ : Module.Basis ι (B ⧸ J) (Ω[B⁄R] ⧸ J • (⊤ : Submodule B Ω[B⁄R])) :=
      (b.baseChange (B ⧸ J)).map
        ((TensorProduct.quotTensorEquivQuotSMul Ω[B⁄R] J).extendScalarsOfSurjective
          Ideal.Quotient.mk_surjective)
    choose x hxJ hxb using fun i ↦ KaehlerDifferential.exists_mem_and_mk_D_eq J (bJ i)
    obtain ⟨d, hdJ, bx, hbx⟩ :=
      TauCeti.KaehlerDifferential.exists_sub_one_mem_and_basis_localizationAway J bJ
        fun i ↦ (hxb i).symm
    have hψd : ψ d = 1 :=
      sub_eq_zero.mp (by rw [← map_one ψ, ← map_sub]; exact RingHom.mem_ker.mp hdJ)
    have hψx (i : ι) : ψ (x i) = 0 := RingHom.mem_ker.mp (hxJ i)
    let W := Localization.Away d
    have : Algebra.Smooth R W := .comp R B W
    let xW : ι → W := algebraMap B W ∘ x
    have het : Algebra.Etale R (W ⧸ Ideal.span (Set.range xW)) := bx.etale_quotient_span_range hbx
    -- `ψ` inverts `d` (`ψ d = 1`) and vanishes on every `x i`, so it factors through `W ⧸ (xW)`.
    let ψW : W →ₐ[R] T := IsLocalization.Away.liftAlgHom d (f := ψ) (by simp [hψd])
    have hψW (a : B) : ψW (algebraMap B W a) = ψ a := by
      simp [ψW, IsLocalization.Away.lift_eq]
    have hker (w : W) (hw : w ∈ Ideal.span (Set.range xW)) : ψW w = 0 := by
      rw [← RingHom.mem_ker]
      refine Ideal.span_le.mpr ?_ hw
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker, xW, hψW, hψx i]
    exact ⟨d, x, Ideal.Quotient.liftₐ (Ideal.span (Set.range xW)) ψW hker, hψd, hψx, het,
      AlgHom.ext hψW⟩

end Module.Basis

namespace Algebra.Smooth

/-- **Every smooth algebra is a retract of a smooth algebra with globally free differentials.**
Every smooth `R`-algebra `A` is an `R`-algebra retract (`β.comp α = AlgHom.id R A`) of a smooth
`R`-algebra `B` in the same universe whose module of Kähler differentials `Ω[B⁄R]` is finite free
(with a `B`-basis indexed by `Fin n`). -/
theorem exists_retract_basis_kaehlerDifferential (R : Type u) (A : Type v) [CommRing R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] :
    ∃ (n : ℕ) (B : Type v) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra.Smooth R B)
      (α : A →ₐ[R] B) (β : B →ₐ[R] A),
      β.comp α = AlgHom.id R A ∧ Nonempty (Module.Basis (Fin n) B Ω[B⁄R]) := by
  -- Choose a finite projective complement `K` with `Ω[A⁄R] × K ≃ₗ[A] (Fin n → A)`, and set
  -- `B := SymmetricAlgebra A K` with augmentation retract `SymmetricAlgebra.algebraMapInv`.
  obtain ⟨K, _, _, _, _, n, ⟨e⟩⟩ := Module.Projective.exists_prod_linearEquiv_fin A Ω[A⁄R]
  let : Module R K := Module.compHom K (algebraMap R A)
  have : IsScalarTower R A K := .of_algebraMap_smul fun _ _ ↦ rfl
  let B := SymmetricAlgebra A K
  have : Algebra.Smooth R B := .comp R A B
  obtain ⟨eB, -⟩ := TauCeti.exists_kaehlerDifferentialProdEquiv R A B
  -- Transport `Pi.basisFun A (Fin n)` along `B ⊗[A] (Fin n → A) ≃ B ⊗[A] (Ω[A⁄R] × K) ≃ Ω[B⁄R]`.
  let bAK : Module.Basis (Fin n) B (B ⊗[A] (Ω[A⁄R] × K)) :=
    Algebra.TensorProduct.basis B ((Pi.basisFun A (Fin n)).map e.symm)
  let eTot : (B ⊗[A] (Ω[A⁄R] × K)) ≃ₗ[B] Ω[B⁄R] :=
    TensorProduct.prodRight A B B Ω[A⁄R] K ≪≫ₗ
      LinearEquiv.prodCongr (LinearEquiv.refl B (B ⊗[A] Ω[A⁄R]))
        (SymmetricAlgebra.kaehlerDifferentialEquiv A K).symm ≪≫ₗ
      eB.symm
  refine ⟨n, B, inferInstance, inferInstance, inferInstance,
    IsScalarTower.toAlgHom R A B,
    (SymmetricAlgebra.algebraMapInv (R := A) (M := K)).restrictScalars R, ?_, ⟨bAK.map eTot⟩⟩
  ext a
  exact SymmetricAlgebra.algebraMap_leftInverse K a

/-- **Étale slice factorization (in the universe of `A`).** Every `R`-algebra homomorphism
`ψ : A →ₐ[R] T` out of a smooth `R`-algebra `A` along a surjective base map `R → T` factors through
an étale `R`-algebra `C` in the universe of `A`. -/
@[stacks 0H74 "étale factorization step"]
theorem exists_etale_algHom_comp_eq' {R : Type u} {A : Type v} {T : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] [CommRing T] [Algebra R T]
    (hsurj : Function.Surjective (algebraMap R T)) (ψ : A →ₐ[R] T) :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra.Etale R C)
      (f : A →ₐ[R] C) (ψC : C →ₐ[R] T), ψC.comp f = ψ := by
  obtain ⟨n, B, _, _, _, α, β, hβα, ⟨b⟩⟩ := exists_retract_basis_kaehlerDifferential R A
  obtain ⟨d, x, ψC, -, -, het, hψC⟩ := b.exists_etale_quotient_localizationAway hsurj (ψ.comp β)
  refine ⟨_, inferInstance, inferInstance, het,
    ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R B _)).comp α, ψC, ?_⟩
  rw [← AlgHom.comp_assoc, hψC, AlgHom.comp_assoc, hβα, AlgHom.comp_id]

/-- **Étale slice factorization (in the universe of `R`).** Every `R`-algebra homomorphism
`ψ : A →ₐ[R] T` out of a smooth `R`-algebra `A` along a surjective base map `R → T` factors through
an étale `R`-algebra `C : Type u` in the universe of the base ring `R`. -/
@[stacks 0H74 "small-universe étale factorization"]
theorem exists_etale_algHom_comp_eq {R : Type u} {A T : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.Smooth R A] [CommRing T] [Algebra R T]
    (hsurj : Function.Surjective (algebraMap R T)) (ψ : A →ₐ[R] T) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra.Etale R C)
      (f : A →ₐ[R] C) (ψC : C →ₐ[R] T), ψC.comp f = ψ := by
  obtain ⟨C₀, _, _, _, f₀, ψ₀, h₀⟩ := exists_etale_algHom_comp_eq' hsurj ψ
  have : Small.{u} C₀ := Algebra.FiniteType.small (R := R) (S := C₀)
  let e : Shrink.{u} C₀ ≃ₐ[R] C₀ := Shrink.algEquiv R C₀
  have : Algebra.Etale R (Shrink.{u} C₀) := .of_equiv e.symm
  refine ⟨Shrink.{u} C₀, inferInstance, inferInstance, inferInstance,
    e.symm.toAlgHom.comp f₀, ψ₀.comp e.toAlgHom, ?_⟩
  rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc e.toAlgHom, AlgEquiv.comp_symm, AlgHom.id_comp, h₀]

end Algebra.Smooth
