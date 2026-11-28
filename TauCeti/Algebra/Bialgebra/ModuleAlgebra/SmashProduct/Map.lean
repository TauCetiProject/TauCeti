/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv
public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.SmashProduct

/-!
# Functoriality of the smash product along bialgebra maps

While `TauCeti.LeftModuleAlgebra.SmashProduct.map` gives functoriality in equivariant algebra
homomorphisms over a fixed bialgebra `H`, the smash product `A # H` is jointly functorial in a
bialgebra homomorphism `g : K →ₐc[R] H` and an equivariant algebra homomorphism
`f : Hom μ (ν.restrict g)`.

## Main definitions

* `TauCeti.LeftModuleAlgebra.SmashProduct.mapBialg`: joint functoriality `A # K →ₐ[R] B # H`
  sending `a # k` to `f a # g k`.
* `TauCeti.LeftModuleAlgebra.SmashProduct.congr`: algebra equivalence `A # K ≃ₐ[R] B # H` induced
  by a bialgebra equivalence `K ≃ₐc[R] H` and an equivariant algebra equivalence `A ≃ₐ[R] B`.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, §4.1.
* Y. Qi, *Hopfological algebra*, Example 2.8.
-/

public section

open scoped TensorProduct Coalgebra
open Coalgebra

namespace TauCeti

namespace LeftModuleAlgebra

namespace SmashProduct

section Functoriality

variable {R : Type*} [CommSemiring R]
  {K : Type*} [Semiring K] [Bialgebra R K]
  {H : Type*} [Semiring H] [Bialgebra R H]
  {L : Type*} [Semiring L] [Bialgebra R L]
  {A : Type*} [Semiring A] [Algebra R A]
  {B : Type*} [Semiring B] [Algebra R B]
  {C : Type*} [Semiring C] [Algebra R C]

/-- Joint functoriality of the smash product: a bialgebra homomorphism `g : K →ₐc[R] H` and an
equivariant algebra homomorphism `f : Hom μ (ν.restrict g)` induce an `R`-algebra homomorphism
`A # K →ₐ[R] B # H` sending `a # k` to `f a # g k`. -/
noncomputable def mapBialg {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) :
    SmashProduct μ →ₐ[R] SmashProduct ν :=
  lift (includeA.comp f.toAlgHom) (includeH.comp g.toAlgHom) <|
    (smashCompatible_iff (ℛ R)).mpr fun k a => by
      have hcomul : Coalgebra.comul (R := R) (g k) =
          ∑ i ∈ (ℛ R k).index, g ((ℛ R k).left i) ⊗ₜ[R] g ((ℛ R k).right i) := by
        simpa [← (ℛ R k).eq, map_sum] using (CoalgHomClass.map_comp_comul_apply g k).symm
      let rg : Coalgebra.Repr R (g k) _ :=
        ⟨(ℛ R k).index, fun i => g ((ℛ R k).left i), fun i => g ((ℛ R k).right i), hcomul.symm⟩
      simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, Hom.coe_toAlgHom,
        includeH_mul_includeA (μ := ν) rg]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [rg, ← ν.restrict_action g, ← f.map_action]

@[simp]
theorem mapBialg_pure {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) (a : A) (k : K) :
    mapBialg g f (pure a k) = pure (f a) (g k) := by
  simp [mapBialg]

@[simp]
theorem mapBialg_includeA {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) (a : A) :
    mapBialg g f (includeA a) = includeA (f a) := by
  simp [mapBialg]

@[simp]
theorem mapBialg_includeH {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) (k : K) :
    mapBialg g f (includeH k) = includeH (g k) := by
  simp [mapBialg]

@[simp]
theorem mapBialg_comp_includeA {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) :
    (mapBialg g f).comp includeA = includeA.comp f.toAlgHom :=
  lift_comp_includeA ..

@[simp]
theorem mapBialg_comp_includeH {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) :
    (mapBialg g f).comp includeH = includeH.comp g.toAlgHom :=
  lift_comp_includeH ..

theorem toLinearMap_mapBialg {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) :
    (mapBialg g f).toLinearMap =
      (linearEquivTensor ν).symm.toLinearMap ∘ₗ
        TensorProduct.map f.toAlgHom.toLinearMap g.toAlgHom.toLinearMap ∘ₗ
        (linearEquivTensor μ).toLinearMap :=
  lhom_ext fun a k => by simp [AlgHom.toLinearMap_apply]

@[simp]
theorem mapBialg_comp {μ : LeftModuleAlgebra R L A} {ν : LeftModuleAlgebra R K B}
    {ξ : LeftModuleAlgebra R H C} (g₂ : K →ₐc[R] H) (g₁ : L →ₐc[R] K)
    (f₂ : Hom ν (ξ.restrict g₂)) (f₁ : Hom μ (ν.restrict g₁)) :
    (mapBialg g₂ f₂).comp (mapBialg g₁ f₁) =
      mapBialg (g₂.comp g₁) ⟨f₂.toAlgHom.comp f₁.toAlgHom, fun _ _ => by simp⟩ := by
  ext <;> simp

/-- Algebra equivalence `A # K ≃ₐ[R] B # H` induced by a bialgebra equivalence `g : K ≃ₐc[R] H`
and an equivariant algebra equivalence `f : A ≃ₐ[R] B`. -/
noncomputable def congr {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K ≃ₐc[R] H) (f : A ≃ₐ[R] B) (hf : ∀ k a, f (μ.action k a) = ν.action (g k) (f a)) :
    SmashProduct μ ≃ₐ[R] SmashProduct ν :=
  AlgEquiv.ofAlgHom
    (mapBialg (g : K →ₐc[R] H) ⟨f.toAlgHom, fun k a => by simp [hf]⟩)
    (mapBialg (g.symm : H →ₐc[R] K) ⟨f.symm.toAlgHom, fun _ _ => f.injective (by simp [hf])⟩)
    (by ext <;> simp)
    (by ext <;> simp)

@[simp]
theorem congr_pure {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K ≃ₐc[R] H) (f : A ≃ₐ[R] B) (hf : ∀ k a, f (μ.action k a) = ν.action (g k) (f a))
    (a : A) (k : K) :
    congr g f hf (pure a k) = pure (f a) (g k) :=
  mapBialg_pure (g : K →ₐc[R] H) ⟨f.toAlgHom, fun k' a' => by simp [hf]⟩ a k

@[simp]
theorem congr_includeA {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K ≃ₐc[R] H) (f : A ≃ₐ[R] B) (hf : ∀ k a, f (μ.action k a) = ν.action (g k) (f a))
    (a : A) :
    congr g f hf (includeA a) = includeA (f a) := by
  simp [includeA_eq_pure]

@[simp]
theorem congr_includeH {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K ≃ₐc[R] H) (f : A ≃ₐ[R] B) (hf : ∀ k a, f (μ.action k a) = ν.action (g k) (f a))
    (k : K) :
    congr g f hf (includeH k) = includeH (g k) := by
  simp [includeH_eq_pure]

@[simp]
theorem congr_symm_pure {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K ≃ₐc[R] H) (f : A ≃ₐ[R] B) (hf : ∀ k a, f (μ.action k a) = ν.action (g k) (f a))
    (b : B) (h : H) :
    (congr g f hf).symm (pure b h) = pure (f.symm b) (g.symm h) :=
  mapBialg_pure (g.symm : H →ₐc[R] K) ⟨f.symm.toAlgHom, fun _ _ => f.injective (by simp [hf])⟩ b h

@[simp]
theorem congr_symm_includeA {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K ≃ₐc[R] H) (f : A ≃ₐ[R] B) (hf : ∀ k a, f (μ.action k a) = ν.action (g k) (f a))
    (b : B) :
    (congr g f hf).symm (includeA b) = includeA (f.symm b) := by
  simp [includeA_eq_pure]

@[simp]
theorem congr_symm_includeH {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K ≃ₐc[R] H) (f : A ≃ₐ[R] B) (hf : ∀ k a, f (μ.action k a) = ν.action (g k) (f a))
    (h : H) :
    (congr g f hf).symm (includeH h) = includeH (g.symm h) := by
  simp [includeH_eq_pure]

/-- The inverse of `SmashProduct.congr` is `SmashProduct.congr` of the inverse equivalences. -/
theorem congr_symm {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K ≃ₐc[R] H) (f : A ≃ₐ[R] B) (hf : ∀ k a, f (μ.action k a) = ν.action (g k) (f a)) :
    (congr g f hf).symm = congr g.symm f.symm (fun _ _ => f.injective (by simp [hf])) := by
  apply AlgEquiv.coe_toAlgHom_injective
  ext <;> simp

/-- `SmashProduct.congr` of identity equivalences is the identity algebra equivalence. -/
@[simp]
theorem congr_refl (μ : LeftModuleAlgebra R H A) :
    congr (BialgEquiv.refl R H) (AlgEquiv.refl : A ≃ₐ[R] A) (fun _ _ => by simp) =
      (AlgEquiv.refl : SmashProduct μ ≃ₐ[R] SmashProduct μ) := by
  apply AlgEquiv.coe_toAlgHom_injective
  ext <;> simp

end Functoriality

end SmashProduct

end LeftModuleAlgebra

end TauCeti
