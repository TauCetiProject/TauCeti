/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.SmashProduct.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Transport

/-!
# Right comodule algebra structure on the smash product

Let `H` be an `R`-bialgebra and `A` a left `H`-module algebra (`TauCeti.LeftModuleAlgebra R H A`).
Transporting the cofree right `H`-comodule structure on `A ⊗[R] H` along `μ.tensorEquiv.symm`
equips the smash product `A # H` (`μ.SmashProduct`) with the right `H`-coaction

`coact (a # h) = ∑ (a # h₁) ⊗ h₂`.

This coaction is unital and multiplicative for the smash-product algebra structure, making
`μ.SmashProduct` a right `H`-comodule algebra (`TauCeti.ComoduleAlgebra R H μ.SmashProduct`).
Moreover, without any flatness, commutativity, or antipode hypotheses, the coinvariant subalgebra
`ComoduleAlgebra.coinvariants R H μ.SmashProduct` coincides with the image of `μ.includeA` and is
canonically isomorphic as an `R`-algebra to `A`.

## Main definitions

* `TauCeti.LeftModuleAlgebra.SmashProduct.instComodule`: the right `H`-comodule structure on
  `μ.SmashProduct` transported from `Comodule.cofree R H A`.
* `TauCeti.LeftModuleAlgebra.SmashProduct.instComoduleAlgebra`: the right `H`-comodule algebra
  structure on `μ.SmashProduct`.
* `TauCeti.LeftModuleAlgebra.includeACoinvariantsEquiv`: the unconditional `R`-algebra isomorphism
  `A ≃ₐ[R] ComoduleAlgebra.coinvariants R H μ.SmashProduct`.
* `TauCeti.LeftModuleAlgebra.SmashProduct.mapHomComoduleHom`: `SmashProduct.mapHom f` bundled as a
  right `H`-comodule morphism.

## Main results

* `TauCeti.LeftModuleAlgebra.SmashProduct.coact_smash_eq_sum`: Sweedler formula
  `coact (a # h) = ∑ (a # h₁) ⊗ h₂` in any `Coalgebra.Repr`.
* `TauCeti.LeftModuleAlgebra.coinvariants_eq_includeA_range`: the coinvariants of `A # H` are
  precisely `μ.includeA.range`.
* `TauCeti.LeftModuleAlgebra.SmashProduct.coactAlgHom_comp_map`: naturality of the coaction with
  respect to `SmashProduct.map`.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, §4.1.
* Y. Qi, *Hopfological algebra*, Definition 2.4 and Example 2.8.
-/

public section

open scoped TensorProduct Coalgebra
open Coalgebra

namespace TauCeti

namespace LeftModuleAlgebra

universe u v w

variable {R : Type u} {H : Type v} {A : Type w}
  [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A]

namespace SmashProduct

section Coaction

variable (μ : LeftModuleAlgebra R H A)

section CofreeTransport

attribute [local instance] Comodule.cofree

/-- The `R`-linear right `H`-coaction `A # H →ₗ[R] (A # H) ⊗[R] H` obtained by transporting the
cofree coaction on `A ⊗[R] H` along `μ.tensorEquiv.symm`. -/
noncomputable def smashCoact : μ.SmashProduct →ₗ[R] μ.SmashProduct ⊗[R] H :=
  Comodule.transportCoact (R := R) (C := H) μ.tensorEquiv.symm

private theorem smashCoact_eq :
    smashCoact μ =
      (Comodule.Transport (R := R) (C := H) (M := A ⊗[R] H) (N := μ.SmashProduct)
        μ.tensorEquiv.symm).coact :=
  (Comodule.transport_coact (R := R) (C := H) μ.tensorEquiv.symm).symm

/-- Right `H`-comodule structure on `A # H` obtained by transporting the cofree right `H`-comodule
on `A ⊗[R] H` along `μ.tensorEquiv.symm`. -/
noncomputable instance instComodule : Comodule R H μ.SmashProduct where
  coact := smashCoact μ
  coassoc := by
    rw [smashCoact_eq]
    exact (Comodule.Transport (R := R) (C := H) μ.tensorEquiv.symm).coassoc
  lTensor_counit_comp_coact := by
    rw [smashCoact_eq]
    exact (Comodule.Transport (R := R) (C := H) μ.tensorEquiv.symm).lTensor_counit_comp_coact

variable {μ}

/-- Representation-free formula for the right `H`-coaction on a pure smash element `a # h`. -/
theorem coact_smash (a : A) (h : H) :
    Comodule.coact (R := R) (C := H) (μ.smash a h) =
      μ.tensorEquiv.symm.toLinearMap.rTensor H
        ((TensorProduct.assoc R A H H).symm (a ⊗ₜ[R] Coalgebra.comul (R := R) h)) := by
  change smashCoact μ (μ.smash a h) = _
  simp [smashCoact, LinearMap.rTensor_def]

end CofreeTransport

variable {μ}

/-- Sweedler formula for the right `H`-coaction on `a # h` in any finite representation of
`comul h`. -/
theorem coact_smash_eq_sum {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (a : A) :
    Comodule.coact (R := R) (C := H) (μ.smash a h) =
      ∑ i ∈ r.index, μ.smash a (r.left i) ⊗ₜ[R] r.right i := by
  rw [coact_smash, ← r.eq, TensorProduct.tmul_sum, map_sum, map_sum]
  rfl

/-- Applying `μ.retractA` to the left factor of `coact x` recovers `μ.tensorEquiv x`. -/
@[simp]
theorem retractA_rTensor_coact (x : μ.SmashProduct) :
    μ.retractA.rTensor H (Comodule.coact (R := R) (C := H) x) = μ.tensorEquiv x := by
  have h : μ.retractA.rTensor H ∘ₗ Comodule.coact (R := R) (C := H) =
      μ.tensorEquiv.toLinearMap := by
    refine lhom_ext fun a h => ?_
    simp only [LinearMap.comp_apply, coact_smash_eq_sum (ℛ R h), map_sum,
      LinearMap.rTensor_tmul, retractA_smash, TensorProduct.smul_tmul, ← TensorProduct.tmul_sum,
      sum_counit_smul, LinearEquiv.coe_coe, tensorEquiv_smash]
  exact LinearMap.congr_fun h x

private noncomputable def coactIncludeA (μ : LeftModuleAlgebra R H A) :
    A →ₐ[R] μ.SmashProduct ⊗[R] H :=
  Algebra.TensorProduct.includeLeft.comp μ.includeA

private noncomputable def coactIncludeH (μ : LeftModuleAlgebra R H A) :
    H →ₐ[R] μ.SmashProduct ⊗[R] H :=
  (Algebra.TensorProduct.map μ.includeH (AlgHom.id R H)).comp (Bialgebra.comulAlgHom R H)

private theorem smashCompatible_coactInclude (μ : LeftModuleAlgebra R H A) :
    μ.SmashCompatible (coactIncludeA μ) (coactIncludeH μ) := by
  rw [μ.smashCompatible_iff_sum _ _ (ℛ R)]
  intro h a
  let r := ℛ R h
  let r₁ := fun i => ℛ R (r.left i)
  let r₂ := fun i => ℛ R (r.right i)
  have hco := congrArg
    (μ.tensorEquiv.symm.toLinearMap.rTensor H ∘ₗ
      (TensorProduct.assoc R A H H).symm.toLinearMap ∘ₗ
      TensorProduct.map (μ.action.toLinearMap.flip a) LinearMap.id)
    (Coalgebra.sum_tmul_tmul_eq r r₁ r₂)
  simp only [map_sum, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.flip_apply,
    AlgHom.toLinearMap_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
    TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, tensorEquiv_symm_tmul] at hco
  calc coactIncludeH μ h * coactIncludeA μ a
      = (∑ i ∈ r.index, μ.includeH (r.left i) ⊗ₜ[R] r.right i) * (μ.includeA a ⊗ₜ[R] 1) := by
          simp [coactIncludeH, coactIncludeA, Bialgebra.comulAlgHom_apply, ← r.eq, map_sum]
    _ = ∑ i ∈ r.index, ∑ j ∈ (r₁ i).index,
          μ.smash (μ.action ((r₁ i).left j) a) ((r₁ i).right j) ⊗ₜ[R] r.right i := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one,
            μ.includeH_mul_includeA_eq_sum (r₁ i) a, TensorProduct.sum_tmul]
          simp only [includeA_mul_includeH]
    _ = ∑ i ∈ r.index, ∑ j ∈ (r₂ i).index,
          μ.smash (μ.action (r.left i) a) ((r₂ i).left j) ⊗ₜ[R] (r₂ i).right j := hco
    _ = ∑ i ∈ r.index, coactIncludeA μ (μ.action (r.left i) a) * coactIncludeH μ (r.right i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hr₂ : coactIncludeH μ (r.right i) =
              ∑ j ∈ (r₂ i).index, μ.includeH ((r₂ i).left j) ⊗ₜ[R] (r₂ i).right j := by
            simp [coactIncludeH, Bialgebra.comulAlgHom_apply, ← (r₂ i).eq, map_sum]
          rw [hr₂, coactIncludeA, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, includeA_mul_includeH]

private noncomputable def coactLift (μ : LeftModuleAlgebra R H A) :
    μ.SmashProduct →ₐ[R] μ.SmashProduct ⊗[R] H :=
  lift (coactIncludeA μ) (coactIncludeH μ) (smashCompatible_coactInclude μ)

private theorem toLinearMap_coactLift (μ : LeftModuleAlgebra R H A) :
    (coactLift μ).toLinearMap = Comodule.coact (R := R) (C := H) (M := μ.SmashProduct) := by
  refine lhom_ext fun a h => ?_
  simp only [AlgHom.toLinearMap_apply, coactLift, lift_smash, coactIncludeA, coactIncludeH,
    AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply, Bialgebra.comulAlgHom_apply,
    ← (ℛ R h).eq, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Finset.mul_sum,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, includeA_mul_includeH,
    coact_smash_eq_sum (ℛ R h)]

/-- The smash product `A # H` is a right `H`-comodule algebra under
`coact (a # h) = ∑ (a # h₁) ⊗ h₂`. -/
noncomputable instance instComoduleAlgebra (μ : LeftModuleAlgebra R H A) :
    ComoduleAlgebra R H μ.SmashProduct where
  toComodule := instComodule μ
  coact_one := by
    rw [← toLinearMap_coactLift μ]
    exact (coactLift μ).map_one
  coact_mul x y := by
    rw [← toLinearMap_coactLift μ]
    exact (coactLift μ).map_mul x y

@[simp]
theorem coact_smash_one (a : A) :
    Comodule.coact (R := R) (C := H) (μ.smash a 1) = μ.smash a 1 ⊗ₜ[R] 1 := by
  rw [← includeA_apply, ← toLinearMap_coactLift μ]
  simp [coactLift, coactIncludeA]

@[simp]
theorem coact_one_smash (h : H) :
    Comodule.coact (R := R) (C := H) (μ.smash 1 h) =
      Algebra.TensorProduct.map μ.includeH (AlgHom.id R H) (Coalgebra.comul (R := R) h) := by
  rw [← includeH_apply, ← toLinearMap_coactLift μ]
  simp [coactLift, coactIncludeH, Bialgebra.comulAlgHom_apply]

theorem coact_includeA (a : A) :
    Comodule.coact (R := R) (C := H) (μ.includeA a) = μ.includeA a ⊗ₜ[R] 1 := by
  simp

theorem coact_includeH (h : H) :
    Comodule.coact (R := R) (C := H) (μ.includeH h) =
      Algebra.TensorProduct.map μ.includeH (AlgHom.id R H) (Coalgebra.comul (R := R) h) := by
  simp

@[simp]
theorem coactAlgHom_comp_includeA (μ : LeftModuleAlgebra R H A) :
    (ComoduleAlgebra.coactAlgHom R H μ.SmashProduct).comp μ.includeA =
      Algebra.TensorProduct.includeLeft.comp μ.includeA :=
  AlgHom.ext fun a => by simp

@[simp]
theorem coactAlgHom_comp_includeH (μ : LeftModuleAlgebra R H A) :
    (ComoduleAlgebra.coactAlgHom R H μ.SmashProduct).comp μ.includeH =
      (Algebra.TensorProduct.map μ.includeH (AlgHom.id R H)).comp (Bialgebra.comulAlgHom R H) :=
  AlgHom.ext fun h => by simp [Bialgebra.comulAlgHom_apply]

end Coaction

end SmashProduct

/-! ### Coinvariants of the smash product -/

section Coinvariants

variable (μ : LeftModuleAlgebra R H A)

/-- For every `a : A`, `μ.includeA a` is `H`-coinvariant in `A # H`. -/
theorem includeA_mem_coinvariants (a : A) :
    μ.includeA a ∈ ComoduleAlgebra.coinvariants R H μ.SmashProduct := by
  simp

/-- The coinvariant subalgebra `(A # H)^{co H}` equals the image `μ.includeA.range` of `A`,
unconditionally over any commutative semiring `R` and any `R`-bialgebra `H`. -/
theorem coinvariants_eq_includeA_range :
    ComoduleAlgebra.coinvariants R H μ.SmashProduct = μ.includeA.range := by
  refine le_antisymm (fun x hx => ?_) ?_
  · refine ⟨μ.retractA x, μ.tensorEquiv.injective ?_⟩
    have hco : μ.retractA.rTensor H (Comodule.coact (R := R) (C := H) x) =
        μ.retractA.rTensor H (x ⊗ₜ[R] 1) :=
      congrArg (μ.retractA.rTensor H) (ComoduleAlgebra.mem_coinvariants.1 hx)
    simpa using hco.symm
  · rintro _ ⟨a, rfl⟩
    exact μ.includeA_mem_coinvariants a

/-- Unconditional `R`-algebra isomorphism `A ≃ₐ[R] (A # H)^{co H}` induced by `μ.includeA`. -/
noncomputable def includeACoinvariantsEquiv :
    A ≃ₐ[R] ComoduleAlgebra.coinvariants R H μ.SmashProduct :=
  (AlgEquiv.ofInjective μ.includeA μ.includeA_injective).trans
    (Subalgebra.equivOfEq _ _ μ.coinvariants_eq_includeA_range.symm)

@[simp]
theorem coe_includeACoinvariantsEquiv_apply (a : A) :
    (μ.includeACoinvariantsEquiv a : μ.SmashProduct) = μ.includeA a :=
  (rfl)

@[simp]
theorem includeACoinvariantsEquiv_symm_apply
    (x : ComoduleAlgebra.coinvariants R H μ.SmashProduct) :
    μ.includeACoinvariantsEquiv.symm x = μ.retractA x := by
  apply μ.includeA_injective
  have hx : (x : μ.SmashProduct) ∈ μ.includeA.range := by
    rw [← μ.coinvariants_eq_includeA_range]
    exact x.2
  rw [AlgHom.mem_range] at hx
  obtain ⟨a, ha⟩ := hx
  have hsymm : μ.includeA (μ.includeACoinvariantsEquiv.symm x) = (x : μ.SmashProduct) := by
    rw [← μ.coe_includeACoinvariantsEquiv_apply, AlgEquiv.apply_symm_apply]
  rw [hsymm, ← ha, μ.retractA_includeA]

end Coinvariants

/-! ### Functoriality of the coaction -/

namespace SmashProduct

section Functoriality

variable {K : Type*} [Semiring K] [Bialgebra R K]
  {B : Type*} [Semiring B] [Algebra R B]

/-- Naturality of the smash-product coaction with respect to `SmashProduct.map`. -/
theorem coactAlgHom_comp_map {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) :
    (ComoduleAlgebra.coactAlgHom R H ν.SmashProduct).comp (map g f) =
      (Algebra.TensorProduct.map (map g f) g.toAlgHom).comp
        (ComoduleAlgebra.coactAlgHom R K μ.SmashProduct) := by
  refine algHom_ext (AlgHom.ext fun a => by simp) ?_
  calc ((ComoduleAlgebra.coactAlgHom R H ν.SmashProduct).comp (map g f)).comp μ.includeH
      = ((Algebra.TensorProduct.map ν.includeH (AlgHom.id R H)).comp
          (Bialgebra.comulAlgHom R H)).comp g.toAlgHom := by
          rw [AlgHom.comp_assoc, map_comp_includeH, ← AlgHom.comp_assoc, coactAlgHom_comp_includeH]
    _ = (Algebra.TensorProduct.map ν.includeH (AlgHom.id R H)).comp
          ((Algebra.TensorProduct.map g.toAlgHom g.toAlgHom).comp
            (Bialgebra.comulAlgHom R K)) := by
          rw [AlgHom.comp_assoc, ← g.map_comp_comulAlgHom]
    _ = (Algebra.TensorProduct.map ((map g f).comp μ.includeH) g.toAlgHom).comp
          (Bialgebra.comulAlgHom R K) := by
          rw [← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp,
            map_comp_includeH]
    _ = ((Algebra.TensorProduct.map (map g f) g.toAlgHom).comp
          (ComoduleAlgebra.coactAlgHom R K μ.SmashProduct)).comp μ.includeH := by
          rw [AlgHom.comp_assoc, coactAlgHom_comp_includeH, ← AlgHom.comp_assoc,
            ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]

/-- Pointwise form of `coactAlgHom_comp_map`. -/
theorem coact_map {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) (x : μ.SmashProduct) :
    Comodule.coact (R := R) (C := H) (map g f x) =
      Algebra.TensorProduct.map (map g f) g.toAlgHom
        (Comodule.coact (R := R) (C := K) x) := by
  simpa only [AlgHom.comp_apply, ComoduleAlgebra.coactAlgHom_apply] using
    AlgHom.congr_fun (coactAlgHom_comp_map g f) x

/-- `SmashProduct.mapHom f` bundled as a right `H`-comodule morphism `A # H → B # H`. -/
noncomputable def mapHomComoduleHom {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}
    (f : Hom μ ν) : Comodule.Hom R H μ.SmashProduct ν.SmashProduct where
  toLinearMap := (mapHom f).toLinearMap
  map_coact := by
    refine lhom_ext fun a h => ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, mapHom_smash,
      coact_smash_eq_sum (ℛ R h), map_sum, TensorProduct.map_tmul, LinearMap.id_apply]

@[simp]
theorem mapHomComoduleHom_apply {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}
    (f : Hom μ ν) (x : μ.SmashProduct) :
    mapHomComoduleHom f x = mapHom f x :=
  (rfl)

end Functoriality

end SmashProduct

end LeftModuleAlgebra

end TauCeti
