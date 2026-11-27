/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import TauCeti.RingTheory.Flat.QuotientRegular
import TauCeti.RingTheory.Extension.Presentation.Models
import TauCeti.Algebra.TensorProduct.BaseChange
import TauCeti.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps
import TauCeti.Algebra.Regular.SMul
import TauCeti.RingTheory.Flat.Fiber.Regular
import TauCeti.RingTheory.Flat.LocalCriterion
import TauCeti.RingTheory.Flat.TensorProduct
import TauCeti.RingTheory.Localization.Module.TensorProduct
/-!
# Fibrewise regular equations in flat finitely presented algebras

An element of a flat finitely presented algebra is a nonzerodivisor, with flat quotient,
when it is a nonzerodivisor on every residue-field fibre. Neither ring is assumed Noetherian.

The proof spreads a finite P and the equation to a Noetherian model. At each point,
flatness descends to a finitely generated intermediate base by the finite tensor relations.
The Noetherian local criterion then makes the equation universally regular near that point.

## References

* The Stacks Project, Tags 00MD and 00ME.
-/

public section

open TensorProduct LinearMap
open scoped Pointwise

namespace Module

variable {R₀ A S₀ : Type*} [CommRing R₀] [CommRing A] [Algebra R₀ A]
    [CommRing S₀]
  [Algebra R₀ S₀]

private theorem exists_fg_idealMap_tensor_eq_zero
    [Flat A (A ⊗[R₀] S₀)] (I : Ideal R₀) [Module.Finite R₀ I]
    (ξ : S₀ ⊗[R₀] I)
    (hξ : TensorProduct.rid R₀ S₀ (I.subtype.lTensor S₀ ξ) = 0) :
    let τ := Algebra.idealMap A I
    ∃ (Q : Submodule R₀ (I.map (algebraMap R₀ A))) (hPQ : LinearMap.range τ ≤ Q),
      Q.FG ∧ (Submodule.inclusion hPQ).rTensor S₀
        (τ.rangeRestrict.rTensor S₀ (TensorProduct.comm R₀ S₀ I ξ)) = 0 := by
  classical
  let τ := Algebra.idealMap A I
  have himage : ∀ x : S₀ ⊗[R₀] I,
      AlgebraTensorModule.rTensor R₀ S₀ (I.map (algebraMap R₀ A)).subtype
        (τ.rTensor S₀ (TensorProduct.comm R₀ S₀ I x)) =
          (1 : A) ⊗ₜ TensorProduct.rid R₀ S₀ (I.subtype.lTensor S₀ x) := by
    intro x
    induction x with
    | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy, map_add, map_add, tmul_add]
    | tmul s a =>
      rw [TensorProduct.comm_tmul, LinearMap.rTensor_tmul, AlgebraTensorModule.rTensor_tmul]
      simp only [τ, Submodule.subtype_apply, Algebra.idealMap_apply_coe]
      rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
      simp
  have hPfg : (LinearMap.range τ).FG := by
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map τ
  have ht : (LinearMap.range τ).subtype.rTensor S₀
      (τ.rangeRestrict.rTensor S₀ (TensorProduct.comm R₀ S₀ I ξ)) = 0 := by
    apply rTensor_ideal_subtype_injective_of_flat_baseChange
      (I.map (algebraMap R₀ A))
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    -- The restricted tensor of the ideal inclusion is its algebra-linear tensor map.
    change AlgebraTensorModule.rTensor R₀ S₀ (I.map (algebraMap R₀ A)).subtype
      (τ.rTensor S₀ (TensorProduct.comm R₀ S₀ I ξ)) = 0
    rw [himage, hξ, tmul_zero]
  exact TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hPfg ht

private theorem exists_finset_idealMap_submodule (I : Ideal R₀)
    (Q : Submodule R₀ (I.map (algebraMap R₀ A))) (hQ : Q.FG) :
    ∃ T : Finset A, ∀ R₁ : Subalgebra R₀ A, (T : Set A) ⊆ R₁ →
      ∃ κ : I.map (algebraMap R₀ R₁) →ₗ[R₀] I.map (algebraMap R₀ A),
        Function.Injective κ ∧ Q ≤ LinearMap.range κ ∧
          κ ∘ₗ Algebra.idealMap R₁ I = Algebra.idealMap A I := by
  classical
  obtain ⟨generators, hG⟩ := hQ
  have hrep : ∀ a : I.map (algebraMap R₀ A),
      ∃ (n : ℕ) (c : Fin n → A) (x : Fin n → I),
        ∑ i, c i * algebraMap R₀ A (x i) = a := by
    intro a
    obtain ⟨n, c, x, hcx⟩ := Submodule.mem_span_set'.mp a.property
    choose y hy hxy using fun i ↦ (x i).property
    exact ⟨n, c, fun i ↦ ⟨y i, hy i⟩, by rw [← hcx]; simp [hxy, smul_eq_mul]⟩
  choose n c x hcx using hrep
  refine ⟨generators.biUnion fun a ↦ Finset.univ.image (c a), fun R₁ hT ↦ ?_⟩
  let J := I.map (algebraMap R₀ R₁)
  have hmem : ∀ a ∈ J, ((a : R₁) : A) ∈ I.map (algebraMap R₀ A) := by
    intro a ha
    have := Ideal.mem_map_of_mem R₁.val.toRingHom ha
    have hcomp : R₁.val.toRingHom.comp (algebraMap R₀ R₁) = algebraMap R₀ A :=
      IsScalarTower.algebraMap_eq R₀ R₁ A
    rwa [Ideal.map_map, hcomp] at this
  let κ : J →ₗ[R₀] I.map (algebraMap R₀ A) :=
    { toFun := fun a ↦ ⟨((a : R₁) : A), hmem a a.property⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ Subtype.ext (by simp [Algebra.smul_def]) }
  refine ⟨κ, fun a b hab ↦ Subtype.ext (Subtype.ext congr(($hab : A))), ?_, ?_⟩
  · rw [← hG, Submodule.span_le]
    intro a ha
    have hc : ∀ i, c a i ∈ R₁ := fun i ↦
      hT (Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
    refine ⟨⟨∑ i, ⟨c a i, hc i⟩ * algebraMap R₀ R₁ (x a i), ?_⟩, Subtype.ext ?_⟩
    · exact Submodule.sum_mem _ fun i _ ↦
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (x a i).property)
    · simp [κ, ← hcx a]
  · ext a
    rfl

private theorem exists_finset_lTensor_eq_zero
    [Flat A (A ⊗[R₀] S₀)] (I : Ideal R₀)
    (ξ : S₀ ⊗[R₀] I) (hξ : TensorProduct.rid R₀ S₀ (I.subtype.lTensor S₀ ξ) = 0) :
    ∃ T : Finset A, ∀ R₁ : Subalgebra R₀ A, (T
        : Set A) ⊆ R₁ →
      (((Algebra.linearMap R₀ R₁) ∘ₗ I.subtype).codRestrict
        ((I.map (algebraMap R₀ R₁)).restrictScalars R₀)
        (fun a ↦ Ideal.mem_map_of_mem _ a.property)).lTensor S₀ ξ = 0 := by
  classical
  obtain ⟨J, hJ, hJI, ξJ, hinc, hξJ⟩ := exists_fg_ideal_tensor_kernel I ξ hξ
  have : Module.Finite R₀ J := Module.Finite.of_fg hJ
  let τ := Algebra.idealMap A J
  obtain ⟨Q, hPQ, hQfg, hQ⟩ :=
    exists_fg_idealMap_tensor_eq_zero (A := A) J ξJ hξJ
  obtain ⟨T, hT⟩ := exists_finset_idealMap_submodule J Q hQfg
  refine ⟨T, fun R₁ hTR ↦ ?_⟩
  obtain ⟨κ, hκ, hQκ, hκτ⟩ := hT R₁ hTR
  let ψ := (LinearEquiv.ofInjective κ hκ).symm.toLinearMap ∘ₗ Submodule.inclusion hQκ
  have hψ : ψ ∘ₗ Submodule.inclusion hPQ ∘ₗ τ.rangeRestrict =
      Algebra.idealMap R₁ J := by
    refine LinearMap.ext fun a ↦ hκ ?_
    -- Evaluate the composed restricted-range maps before applying the inverse computation law.
    change κ ((LinearEquiv.ofInjective κ hκ).symm _) = _
    rw [LinearEquiv.ofInjective_symm_apply]
    exact (LinearMap.congr_fun hκτ a).symm
  have key : (ψ ∘ₗ Submodule.inclusion hPQ ∘ₗ τ.rangeRestrict).rTensor S₀
      (TensorProduct.comm R₀ S₀ J ξJ) = ψ.rTensor S₀ ((Submodule.inclusion hPQ).rTensor S₀
        (τ.rangeRestrict.rTensor S₀ (TensorProduct.comm R₀ S₀ J ξJ))) := by
    simp only [LinearMap.rTensor_comp, LinearMap.comp_apply]
  have hzero : (Algebra.idealMap R₁ J).rTensor S₀
      (TensorProduct.comm R₀ S₀ J ξJ) = 0 := by
    rw [← hψ, key, hQ, map_zero]
  have hzeroJ : (Algebra.idealMap R₁ J).lTensor S₀ ξJ = 0 := by
    apply (TensorProduct.comm R₀ S₀ (J.map (algebraMap R₀ R₁))).injective
    exact (LinearMap.rTensor_comm (Algebra.idealMap R₁ J) ξJ).symm.trans
      (hzero.trans (TensorProduct.comm R₀ S₀ (J.map (algebraMap R₀ R₁))).map_zero.symm)
  let inclusion : J.map (algebraMap R₀ R₁) →ₗ[R₀] I.map (algebraMap R₀ R₁) :=
    (Submodule.inclusion (Ideal.map_mono (f := algebraMap R₀ R₁) hJI)).restrictScalars R₀
  have hmap : inclusion ∘ₗ Algebra.idealMap R₁ J =
      Algebra.idealMap R₁ I ∘ₗ Submodule.inclusion hJI := by
    ext a
    rfl
  -- The codomain restriction and restriction of scalars describe the same ideal carrier.
  change (Algebra.idealMap R₁ I).lTensor S₀ ξ = 0
  rw [← hinc, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← hmap,
    LinearMap.lTensor_comp, LinearMap.comp_apply, hzeroJ, map_zero]

end Module

namespace Module

universe u

variable {R₀ R₁ S₀ : Type u} [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀]

private lemma rid_lTensor_ideal_subtype (I : Ideal R₀) (ξ : S₀ ⊗[R₀] I) :
    ((AlgebraTensorModule.rid R₀ S₀ S₀).toLinearMap ∘ₗ
      AlgebraTensorModule.lTensor S₀ S₀ I.subtype) ξ =
      TensorProduct.rid R₀ S₀ (I.subtype.lTensor S₀ ξ) := rfl

private theorem lTensor_mapIdeal_subtype_injective (p : Ideal R₀)
    {M : Type*} [AddCommGroup M] [Module R₀ M]
    (hbij : ∀ r ∉ p, Function.Bijective (fun m : M ↦ r • m))
    (hker : ∀ ξ : M ⊗[R₀] p,
      TensorProduct.rid R₀ M (p.subtype.lTensor M ξ) = 0 →
        (((Algebra.linearMap R₀ R₁) ∘ₗ p.subtype).codRestrict
          ((p.map (algebraMap R₀ R₁)).restrictScalars R₀)
          (fun a ↦ Ideal.mem_map_of_mem _ a.property)).lTensor M ξ = 0) :
    Function.Injective (((p.map (algebraMap R₀ R₁)).restrictScalars R₀).subtype.lTensor M) := by
  let J := (p.map (algebraMap R₀ R₁)).restrictScalars R₀
  let σ := ((Algebra.linearMap R₀ R₁) ∘ₗ p.subtype).codRestrict J
    (fun a ↦ Ideal.mem_map_of_mem _ a.property)
  have hL : p • (⊤ : Submodule R₀ R₁) ≤ J := by
    rw [Submodule.smul_le]
    intro r hr m _
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr)
  refine Ideal.lTensor_subtype_injective_of_forall_ker p
    (fun N _ _ hN N' ↦ Ideal.lTensor_subtype_injective_of_bijective_smul p hbij hN N')
    J hL fun ξ hξ r ↦ ?_
  let μr : J →ₗ[R₀] J := (DistribSMul.toLinearMap R₁ (p.map (algebraMap R₀ R₁))
    r).restrictScalars R₀
  have : ((LinearMap.toSpanSingleton R₀ R₁ r) ∘ₗ p.subtype).codRestrict J
      (fun a ↦ hL (Submodule.smul_mem_smul a.property trivial)) =
        μr ∘ₗ σ := by
    ext a
    -- The two restricted ideal maps act by base scalars and by multiplication in `R₁`.
    change (a : R₀) • r = r • algebraMap R₀ R₁ a
    rw [Algebra.smul_def, smul_eq_mul, mul_comm]
  rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply, hker ξ hξ, map_zero]

private theorem flat_localization_tensor_of_forall [IsNoetherianRing R₁]
    [Algebra.FiniteType R₀ S₀] (q₁ : Ideal (R₁ ⊗[R₀] S₀)) [q₁.IsPrime]
    (h : ∀ ξ : S₀ ⊗[R₀] ((q₁.comap Algebra.TensorProduct.includeRight.toRingHom).comap
        (algebraMap R₀ S₀)),
      TensorProduct.rid R₀ S₀ (Submodule.subtype _ |>.lTensor S₀ ξ) = 0 →
      (((Algebra.linearMap R₀ R₁) ∘ₗ Submodule.subtype _).codRestrict
        ((((q₁.comap Algebra.TensorProduct.includeRight.toRingHom).comap
          (algebraMap R₀ S₀)).map (algebraMap R₀ R₁)).restrictScalars R₀)
        (fun a ↦ Ideal.mem_map_of_mem _ a.property)).lTensor S₀ ξ = 0) :
    Flat R₁ (Localization.AtPrime q₁) := by
  classical
  set q₀ := q₁.comap (Algebra.TensorProduct.includeRight.toRingHom : S₀ →+* R₁ ⊗[R₀] S₀)
  set p₀ := q₀.comap (algebraMap R₀ S₀)
  set I₁ : Ideal R₁ := p₀.map (algebraMap R₀ R₁)
  set M₀ := Localization.AtPrime q₀
  set M₁ := Localization.AtPrime q₁
  have : IsNoetherianRing (R₁ ⊗[R₀] S₀) := Algebra.FiniteType.isNoetherianRing R₁ _
  have hbij : ∀ r ∉ p₀, Function.Bijective (fun m : M₀ ↦ r • m) := by
    intro r hr
    have hu : IsUnit (algebraMap R₀ M₀ r) := by
      rw [IsScalarTower.algebraMap_apply R₀ S₀ M₀]
      exact IsLocalization.map_units M₀ (⟨algebraMap R₀ S₀ r, hr⟩ : q₀.primeCompl)
    simp_rw [Algebra.smul_def]
    exact ⟨fun x y hxy ↦ hu.mul_left_cancel hxy, fun y ↦ ⟨hu.unit⁻¹ * y, by
      simp only
      rw [← mul_assoc, hu.mul_val_inv, one_mul]⟩⟩
  have hQ₀ : ∀ (N : Type u) [AddCommGroup N] [Module R₀ N],
      (∀ r ∈ p₀, ∀ n : N, r • n = 0) →
        ∀ N' : Submodule R₀ N, Function.Injective (N'.subtype.lTensor M₀) :=
    fun N _ _ hN N' ↦ Ideal.lTensor_subtype_injective_of_bijective_smul p₀ hbij hN N'
  have hI₀ := lTensor_mapIdeal_subtype_injective (R₁ := R₁) p₀ hbij
    (lTensor_eq_zero_of_localization q₀ p₀ _ h)
  have hQ (N : Type u) [AddCommGroup N] [Module R₁ N]
      (hN : ∀ r ∈ I₁, ∀ n : N, r • n = 0) (N' : Submodule R₁ N) :
      Function.Injective (N'.subtype.lTensor M₁) := by
    let : Module R₀ N := Module.compHom N (algebraMap R₀ R₁)
    have : IsScalarTower R₀ R₁ N := ⟨fun r s n ↦ by
      -- Both base actions on the restricted module are induced through the intermediate ring.
      change (r • s) • n = algebraMap R₀ R₁ r • s • n
      rw [Algebra.smul_def, mul_smul]⟩
    apply lTensor_injective_localization_tensor q₁ N'.subtype
    exact hQ₀ N (fun r hr n ↦ hN _ (Ideal.mem_map_of_mem _ hr) n) (N'.restrictScalars R₀)
  have := Flat.quotient_of_lTensor_injective I₁ hQ
  apply Flat.of_subtype_rTensor_injective (S := M₁) (mapIdeal_le_jacobson_localization_tensor q₁)
  exact (I₁.subtype.lTensor_inj_iff_rTensor_inj _).mp
    (lTensor_injective_localization_tensor q₁ I₁.subtype hI₀)

private theorem exists_fg_flat_localization_tensor {A : Type u} [CommRing
    A] [Algebra R₀ A]
    [IsNoetherianRing R₀] [Algebra.FiniteType R₀ S₀] [Flat A (A ⊗[R₀] S₀)]
    (prime : Ideal (A ⊗[R₀] S₀)) [prime.IsPrime] :
    ∃ R₁ : Subalgebra R₀ A, R₁.FG ∧ IsNoetherianRing R₁ ∧
      Flat R₁ (Localization.AtPrime
        (prime.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ S₀)).toRingHom)) := by
  classical
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing R₀ S₀
  set q₀ : Ideal S₀ := prime.comap (Algebra.TensorProduct.includeRight.toRingHom)
  set p₀ : Ideal R₀ := q₀.comap (algebraMap R₀ S₀)
  let μ' : S₀ ⊗[R₀] p₀ →ₗ[S₀] S₀ := (AlgebraTensorModule.rid R₀ S₀ S₀).toLinearMap ∘ₗ
    AlgebraTensorModule.lTensor S₀ S₀ p₀.subtype
  have hμ' (x) : μ' x = TensorProduct.rid R₀ S₀ (p₀.subtype.lTensor S₀ x) :=
    rid_lTensor_ideal_subtype p₀ x
  obtain ⟨Ξ, hΞ⟩ : (LinearMap.ker μ').FG := IsNoetherian.noetherian _
  have hV : ∀ ξ ∈ Ξ, ∃ T : Finset A, ∀ R₁ : Subalgebra R₀ A,
      (T : Set A) ⊆ R₁ →
      (((Algebra.linearMap R₀ R₁) ∘ₗ p₀.subtype).codRestrict
        ((p₀.map (algebraMap R₀ R₁)).restrictScalars R₀)
        (fun a ↦ Ideal.mem_map_of_mem _ a.property)).lTensor S₀ ξ = 0 := fun ξ hξ ↦
    exists_finset_lTensor_eq_zero p₀ ξ (by
      have h : ξ ∈ LinearMap.ker μ' := hΞ ▸ Submodule.subset_span hξ
      rw [LinearMap.mem_ker, hμ'] at h
      exact h)
  choose! T hT using hV
  set R₁ := Algebra.adjoin R₀ ((Ξ.biUnion T : Finset A) : Set A)
  have : Algebra.FiniteType R₀ R₁ := Algebra.FiniteType.adjoin_of_finite (Finset.finite_toSet _)
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R₀ R₁
  refine ⟨R₁, Subalgebra.fg_adjoin_finset _, this, ?_⟩
  set q₁ := prime.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ S₀)).toRingHom
  have hq : q₁.comap (Algebra.TensorProduct.includeRight.toRingHom) = q₀ := by
    rw [Ideal.comap_comap]
    congr 1
  apply flat_localization_tensor_of_forall q₁
  rw [hq]
  intro ξ hξ
  have hμ : μ' ξ = 0 := by
    rw [hμ']
    exact hξ
  have hξ' : ξ ∈ Submodule.span S₀ (Ξ : Set (S₀ ⊗[R₀] p₀)) :=
    hΞ ▸ LinearMap.mem_ker.mpr hμ
  set σ := ((Algebra.linearMap R₀ R₁) ∘ₗ p₀.subtype).codRestrict
    ((p₀.map (algebraMap R₀ R₁)).restrictScalars R₀)
      (fun a ↦ Ideal.mem_map_of_mem _ a.property)
  -- The scalar extension of the restricted ideal map has the same underlying tensor map.
  change AlgebraTensorModule.lTensor S₀ S₀ σ ξ = 0
  clear hξ hμ
  induction hξ' using Submodule.span_induction with
  | zero => exact map_zero _
  | mem x hx =>
    exact hT x hx R₁ (subset_trans (Finset.subset_biUnion_of_mem T hx)
        Algebra.subset_adjoin)
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

end Module

namespace Algebra

universe u

private lemma mem_map_of_mul_mem_map_of_tensor {R B K : Type*} [CommRing
  R] [CommRing B] [CommRing K]
    [Algebra R B] [Algebra R K] (prime : Ideal B)
      [prime.IsPrime]
    (hflat : Module.Flat R (Localization.AtPrime prime))
    (hker : ∀ r : R, algebraMap R K r = 0 ↔ r
      ∈ prime.comap (algebraMap R B)) (f t : B) (ht :
      t ∉ prime)
    (htensor : ∀ y : B ⊗[R] K, f • y
      = 0 → t • y = 0) :
    ∀ x : Localization.AtPrime prime, algebraMap B _ f * x
      ∈
        (prime.comap (algebraMap R B)).map (algebraMap R
          (Localization.AtPrime prime)) →
      x ∈ (prime.comap (algebraMap R B)).map (algebraMap R
        (Localization.AtPrime prime)) := by
  set I := prime.comap (algebraMap R B)
  set M₁ := Localization.AtPrime prime
  have Hloc := isSMulRegular_localized_tensor_of_kernel (N := K)
    prime f t ht htensor
  intro x hm
  have : Module.Flat R M₁ := hflat
  let ψ : (R ⧸ I) →ₗ[R] K :=
    (Ideal.Quotient.liftₐ I (Algebra.ofId R K) fun r hr ↦ (hker
      r).mpr hr).toLinearMap
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hker r]
    exact hx
  have hzero (x : M₁) : x ⊗ₜ[R] (1 : R ⧸ I) = 0 ↔
      x ∈ I.map (algebraMap R M₁) := tmul_one_quotient_eq_zero_iff I x
  have hmap (x : M₁) : ψ.lTensor M₁ (x ⊗ₜ[R] 1) = x ⊗ₜ[R] 1 := by
    simp [ψ]
  have h1 : algebraMap B M₁ f • (x ⊗ₜ[R]
      (1 : K)) = 0 := by
    rw [smul_tmul', smul_eq_mul, ← hmap]
    rw [(hzero _).mpr hm, map_zero]
  have h2 := Hloc.right_eq_zero_of_smul h1
  apply (hzero _).mp
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := M₁) ψ hψ
  rw [hmap, map_zero, h2]

private theorem exists_notMem_forall_mul_mem_map_of_universal_kernel
    {R₀ R₁ S₀ : Type*} {A : Type u} [CommRing R₀] [CommRing R₁]
    [CommRing A] [CommRing S₀] [Algebra R₀ R₁] [Algebra R₀ A]
    [Algebra R₁ A] [IsScalarTower R₀ R₁ A] [Algebra R₀ S₀]
    (prime : Ideal (A ⊗[R₀] S₀)) (f : S₀)
    (g : R₁ ⊗[R₀] S₀)
    (hg : Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ R₁ A)
      (AlgHom.id R₀ S₀) g ∉ prime)
    (hP : ∀ (N : Type u) [AddCommGroup N] [Module R₁ N]
      (x : (R₁ ⊗[R₀] S₀) ⊗[R₁] N),
      (1 ⊗ₜ f : R₁ ⊗[R₀] S₀) • x = 0 → ∃ n : ℕ, g ^ n • x = 0) :
    ∃ g ∉ prime, ∀ (I : Ideal A) (x : A ⊗[R₀] S₀),
      (1 ⊗ₜ f) * x ∈ I.map (algebraMap A _) →
      ∃ n : ℕ, g ^ n * x ∈ I.map (algebraMap A _) := by
  let B := A ⊗[R₀] S₀
  let ι : R₁ ⊗[R₀] S₀ →ₐ[R₀] B :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ R₁ A) (AlgHom.id R₀ S₀)
  let f₁ : R₁ ⊗[R₀] S₀ := 1 ⊗ₜ f
  have hιf : ι f₁ = 1 ⊗ₜ f := by
    exact Algebra.TensorProduct.map_toAlgHom_one_tmul _ f
  have hz (I : Ideal A) (x : B) :
      x ⊗ₜ[A] (1 : A ⧸ I) = 0 ↔ x ∈ I.map (algebraMap A B) :=
    tmul_one_quotient_eq_zero_iff I x
  refine ⟨ι g, hg, fun I x hx ↦ ?_⟩
  let e := Algebra.TensorProduct.baseChangeTensorEquiv
    (R₀ := R₀) (A := A) (S₀ := S₀) (R₁ := R₁)
    (A ⧸ I)
  set y := e.symm (x ⊗ₜ[A] (1 : A ⧸ I))
  have hy : f₁ • y = 0 := by
    apply e.injective
    rw [Algebra.TensorProduct.baseChangeTensorEquiv_smul, LinearEquiv.apply_symm_apply,
      LinearEquiv.map_zero, hιf, smul_tmul', smul_eq_mul, hz]
    exact hx
  obtain ⟨n, hn⟩ := hP (A ⧸ I) y hy
  refine ⟨n, (hz I _).mp ?_⟩
  have := congr(e $hn)
  rw [Algebra.TensorProduct.baseChangeTensorEquiv_smul, LinearEquiv.apply_symm_apply,
    LinearEquiv.map_zero, map_pow, smul_tmul', smul_eq_mul] at this
  exact this

private theorem exists_notMem_forall_mul_mem_map_of_tensor {R₀ A S₀ : Type u}
  [CommRing R₀]
    [CommRing A] [CommRing S₀] [Algebra R₀ A] [Algebra R₀ S₀] [IsNoetherianRing
      R₀]
    [Algebra.FiniteType R₀ S₀] [Module.Flat A (A ⊗[R₀] S₀)] (prime : Ideal
      (A ⊗[R₀] S₀))
    [prime.IsPrime] (f t : S₀) (ht : (1 ⊗ₜ t : A ⊗[R₀] S₀) ∉
      prime) {K : Type*} [CommRing K]
    [Algebra A K] (hK : RingHom.ker (algebraMap A K) =
      prime.comap (algebraMap A (A ⊗[R₀] S₀)))
    (hfib : ∀ x : (A ⊗[R₀] S₀) ⊗[A] K,
      (1 ⊗ₜ f : A ⊗[R₀] S₀) • x = 0 → (1 ⊗ₜ t : A ⊗[R₀] S₀)
        • x = 0) :
    ∃ g ∉ prime, ∀ (I : Ideal A) (x : A ⊗[R₀] S₀), (1 ⊗ₜ
      f) * x ∈ I.map (algebraMap A _) →
      ∃ n : ℕ, g ^ n * x ∈ I.map (algebraMap A _) := by
  classical
  obtain ⟨R₁, -, hR₁, hflat⟩ := Module.exists_fg_flat_localization_tensor (S₀ := S₀) prime
  set B := A ⊗[R₀] S₀
  set S₁ := R₁ ⊗[R₀] S₀
  let ι : S₁ →ₐ[R₀] B :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ R₁ A) (AlgHom.id R₀ S₀)
  have hι : Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ S₀) = ι := rfl
  rw [hι] at hflat
  set q₁ := prime.comap ι.toRingHom
  set f₁ : S₁ := 1 ⊗ₜ f
  set t₁ : S₁ := 1 ⊗ₜ t
  have hιf : ι f₁ = 1 ⊗ₜ f := by
    exact Algebra.TensorProduct.map_toAlgHom_one_tmul _ f
  have hιt : ι t₁ = 1 ⊗ₜ t := by
    exact Algebra.TensorProduct.map_toAlgHom_one_tmul _ t
  have ht₁ : t₁ ∉ q₁ := by
    -- Membership in the inverse-image prime is membership after the tensor map.
    change ι t₁ ∉ prime
    rw [hιt]
    exact ht
  let : Algebra R₀ K := ((algebraMap A K).comp (algebraMap R₀
    A)).toAlgebra
  have : IsScalarTower R₀ A K := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R₀ R₁ K := ⟨fun r a z ↦ by
    -- The intermediate-subalgebra action is the restriction of the ambient algebra action.
    change (r • (a : A)) • z = r • ((a : A) • z)
    exact smul_assoc r (a : A) z⟩
  have H₁ := Algebra.TensorProduct.smul_eq_zero_imp_of_baseChange
    (A := A) K f₁ t₁ (by
      -- The tensor base-change map is the local abbreviation `ι`.
      change ∀ x : B ⊗[A] K,
        ι f₁ • x = 0 → ι t₁ • x = 0
      simpa only [hιf, hιt] using hfib)
  set p₁ := q₁.comap (algebraMap R₁ S₁)
  have hker : ∀ r : R₁, algebraMap R₁ K r = 0 ↔ r ∈ p₁ := by
    intro r
    rw [← RingHom.mem_ker, ker_algebraMap_comap_tensor_subalgebra R₁ prime hK]
    rfl
  have hfib₁ := mem_map_of_mul_mem_map_of_tensor q₁ hflat hker f₁ t₁ ht₁ H₁
  obtain ⟨g, hg, hP⟩ := Ideal.exists_notMem_forall_pow_smul_eq_zero q₁ f₁ hfib₁
  exact exists_notMem_forall_mul_mem_map_of_universal_kernel prime f g hg hP

/-- Fibrewise injectivity of multiplication spreads to all ideal quotients near the given prime. -/
private theorem exists_notMem_forall_mul_mem_map {A : Type u}
    {B : Type*}
  [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B]
      [Algebra.FinitePresentation A B] (prime : Ideal B)
      [prime.IsPrime]
    (f t : B) (ht : t ∉ prime) {K : Type*} [CommRing
      K] [Algebra A K]
    (hK : RingHom.ker (algebraMap A K) = prime.comap (algebraMap A
      B))
    (hfib : ∀ x : B ⊗[A] K, f • x = 0 → t •
      x = 0) :
    ∃ g ∉ prime, ∀ (I : Ideal A) (x : B), f *
      x ∈ I.map (algebraMap A B) →
      ∃ n : ℕ, g ^ n * x ∈ I.map (algebraMap A
        B) := by
  obtain ⟨R₀, _, _, _, S₀, _, _, _, e, f₀, t₀, hf₀, ht₀⟩ :=
    Algebra.FinitePresentation.exists_noetherian_model (A := A) f t
  have : Module.Flat A (A ⊗[R₀] S₀) := Module.Flat.of_linearEquiv
    e.toLinearEquiv
  have he : (e : A ⊗[R₀] S₀ →+* B).comp (algebraMap A _)
    = algebraMap A B :=
    RingHom.ext fun a ↦ e.commutes a
  set q' := prime.comap (e : A ⊗[R₀] S₀ →+* B)
  let eK : (A ⊗[R₀] S₀) ⊗[A] K ≃ₐ[A]
    B ⊗[A] K := Algebra.TensorProduct.congr e
    AlgEquiv.refl
  have hE (b : A ⊗[R₀] S₀) (x : (A ⊗[R₀] S₀) ⊗[A]
    K) : eK (b • x) = e b • eK
    x := by
    rw [← smul_one_mul b x,
      ← smul_one_mul (e b) (eK x), map_mul]
    congr 1
    have hone : e (1 ⊗ₜ[R₀] (1 : S₀)) = 1 := by
      rw [← Algebra.TensorProduct.one_def]
      exact e.map_one
    simp [eK, Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, hone]
  obtain ⟨g, hg, hP⟩ := exists_notMem_forall_mul_mem_map_of_tensor q' f₀ t₀
    (by
      -- The model prime is the inverse image under the presentation equivalence.
      change e (1 ⊗ₜ t₀) ∉ prime
      rw [ht₀]
      exact ht)
    (by rw [hK, Ideal.comap_comap, he])
    (fun x hx ↦ by
      apply eK.injective
      rw [hE, map_zero, ht₀]
      apply hfib
      rw [← hf₀, ← hE, hx, map_zero])
  have hmap (I : Ideal A) (y : A ⊗[R₀] S₀) : e
    y ∈ I.map (algebraMap A B) ↔
      y ∈ I.map (algebraMap A (A ⊗[R₀] S₀)) := by
    have he' : (e.toRingEquiv : A ⊗[R₀] S₀ →+* B).comp (algebraMap
      A _) = algebraMap A B := he
    rw [← he', ← Ideal.map_map, Ideal.map_comap_of_equiv, Ideal.mem_comap]
    simp
  refine ⟨e g, hg, fun I x hx ↦ ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨n, hn⟩ := hP I x (by
    rw [← hmap, map_mul, hf₀]
    exact hx)
  exact ⟨n, by rw [← map_pow, ← map_mul, hmap]; exact hn⟩

end Algebra
namespace Module.Flat

/-- An element of a flat finitely presented algebra is regular if it is regular on all fibres. -/
theorem isSMulRegular_of_forall_isSMulRegular_fiber {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [Flat R B] [Algebra.FinitePresentation R B] {b : B}
    (h : ∀ (p : Ideal R) [p.IsPrime],
      IsSMulRegular (p.Fiber B) ((1 : p.ResidueField) ⊗ₜ[R] b)) : IsSMulRegular B b := by
  refine IsSMulRegular.of_right_eq_zero_of_smul fun x hx ↦ ?_
  by_contra hne
  have hann : (Submodule.span B {x}).annihilator ≠ ⊤ := by
    intro htop
    apply hne
    have : (1 : B) ∈ (Submodule.span B {x}).annihilator := htop ▸ Submodule.mem_top
    simpa using (Submodule.mem_annihilator_span_singleton _ _).mp this
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hann
  have := hq.isPrime
  let p := q.comap (algebraMap R B)
  let e := Algebra.TensorProduct.comm R B p.ResidueField
  have hfib : IsSMulRegular (B ⊗[R] p.ResidueField) (b ⊗ₜ[R] (1 : p.ResidueField)) :=
    (TauCeti.isSMulRegular_map_iff e _).mp (by simpa [e] using h p)
  obtain ⟨g, hg, hP⟩ := Algebra.exists_notMem_forall_mul_mem_map q b 1
    ((Ideal.ne_top_iff_one q).mp hq.ne_top) p.ker_algebraMap_residueField
    (fun y hy ↦ by
      rw [one_smul]
      rw [← smul_one_mul b y, Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul,
        mul_one] at hy
      exact hfib.right_eq_zero_of_smul hy)
  obtain ⟨n, hn⟩ := hP ⊥ x (by
    simpa only [Ideal.map_bot, Submodule.mem_bot, smul_eq_mul] using hx)
  apply hg
  exact hq.isPrime.mem_of_pow_mem n
    (hle ((Submodule.mem_annihilator_span_singleton _ _).mpr (by
      simpa only [Ideal.map_bot, Submodule.mem_bot, smul_eq_mul] using hn)))

/-- A principal quotient of a flat finitely presented algebra is flat when its equation is
regular on every residue-field fibre. -/
theorem quotient_span_singleton_of_forall_isSMulRegular_fiber {R B : Type*}
    [CommRing R] [CommRing B] [Algebra R B] [Flat R B] [Algebra.FinitePresentation R B] {b : B}
    (h : ∀ (p : Ideal R) [p.IsPrime],
      IsSMulRegular (p.Fiber B) ((1 : p.ResidueField) ⊗ₜ[R] b)) :
    Flat R (B ⧸ Ideal.span {b}) := by
  apply quotient_span_singleton_of_lTensor_mulLeft_injective b
  intro I _
  have hregular : IsSMulRegular ((R ⧸ I) ⊗[R] B) ((1 : R ⧸ I) ⊗ₜ[R] b) :=
    isSMulRegular_of_forall_isSMulRegular_fiber fun p _ ↦
      p.isSMulRegular_fiber_baseChange (h _)
  simpa only [IsSMulRegular, smul_eq_mul, ← LinearMap.mulLeft_apply (R := R),
    LinearMap.mulLeft_tmul, LinearMap.mulLeft_one, ← LinearMap.lTensor_def] using hregular

end Module.Flat
