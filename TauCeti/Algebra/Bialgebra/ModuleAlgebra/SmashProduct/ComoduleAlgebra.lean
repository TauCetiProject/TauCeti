/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra.Basic
public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.SmashProduct.Map
public import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Transport

import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Fixed

/-!
# Right comodule algebra structure on the smash product

Let `H` be an `R`-bialgebra and `A` a left `H`-module algebra (`TauCeti.LeftModuleAlgebra R H A`).
Transporting the cofree right `H`-comodule structure on `A ⊗[R] H` along
`(linearEquivTensor μ).symm` equips the smash product `A # H` (`SmashProduct μ`) with the right
`H`-coaction

`coact (a # h) = ∑ (a # h₁) ⊗ h₂`.

This coaction is unital and multiplicative for the smash-product algebra structure, making
`SmashProduct μ` a right `H`-comodule algebra (`TauCeti.ComoduleAlgebra R H (SmashProduct μ)`).
Moreover, without any flatness, commutativity, or antipode hypotheses, the coinvariant subalgebra
`ComoduleAlgebra.coinvariants R H (SmashProduct μ)` coincides with the image of `includeA` and is
canonically isomorphic as an `R`-algebra to `A`.

## Main definitions

* `TauCeti.LeftModuleAlgebra.SmashProduct.instComodule`: the right `H`-comodule structure on
  `SmashProduct μ` transported from `Comodule.cofree R H A`.
* `TauCeti.LeftModuleAlgebra.SmashProduct.instComoduleAlgebra`: the right `H`-comodule algebra
  structure on `SmashProduct μ`.
* `TauCeti.LeftModuleAlgebra.SmashProduct.includeACoinvariantsEquiv`: the unconditional `R`-algebra
  isomorphism `A ≃ₐ[R] ComoduleAlgebra.coinvariants R H (SmashProduct μ)`.
* `TauCeti.LeftModuleAlgebra.SmashProduct.mapComoduleHom`: `SmashProduct.map f` bundled as a right
  `H`-comodule morphism.

## Main results

* `TauCeti.LeftModuleAlgebra.SmashProduct.coact_pure_eq_sum`: Sweedler formula
  `coact (a # h) = ∑ (a # h₁) ⊗ h₂` in any `Coalgebra.Repr`.
* `TauCeti.LeftModuleAlgebra.SmashProduct.coinvariants_eq_includeA_range`: the coinvariants of
  `A # H` are precisely `(includeA (μ := μ)).range`.
* `TauCeti.LeftModuleAlgebra.SmashProduct.coactAlgHom_comp_mapBialg`: naturality of the coaction
  with respect to `SmashProduct.mapBialg`.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, §4.1.
* Y. Qi, *Hopfological algebra*, Definition 2.4 and Example 2.8.
-/

public section

open scoped TensorProduct Coalgebra
open Coalgebra

namespace TauCeti

namespace LeftModuleAlgebra

variable {R H A : Type*}
  [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A]

namespace SmashProduct

section Coaction

variable (μ : LeftModuleAlgebra R H A)

section CofreeTransport

attribute [local instance] Comodule.cofree

/-- Right `H`-comodule structure on `A # H` obtained by transporting the cofree right `H`-comodule
on `A ⊗[R] H` along `(linearEquivTensor μ).symm`. -/
noncomputable instance instComodule : Comodule R H (SmashProduct μ) :=
  Comodule.Transport (R := R) (C := H) (linearEquivTensor μ).symm

variable {μ}

/-- Representation-free formula for the right `H`-coaction on a pure smash element `a # h`. -/
theorem coact_pure (a : A) (h : H) :
    Comodule.coact (R := R) (C := H) (pure (μ := μ) a h) =
      (linearEquivTensor μ).symm.toLinearMap.rTensor H
        ((TensorProduct.assoc R A H H).symm (a ⊗ₜ[R] Coalgebra.comul (R := R) h)) := by
  rw [Comodule.transport_coact (R := R) (C := H) (linearEquivTensor μ).symm,
    Comodule.transportCoact_apply]
  simp [LinearMap.rTensor_def]

end CofreeTransport

variable {μ}

/-- Sweedler formula for the right `H`-coaction on `a # h` in any finite representation of
`comul h`. -/
theorem coact_pure_eq_sum {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (a : A) :
    Comodule.coact (R := R) (C := H) (pure (μ := μ) a h) =
      ∑ i ∈ r.index, pure a (r.left i) ⊗ₜ[R] r.right i := by
  rw [coact_pure, ← r.eq, TensorProduct.tmul_sum, map_sum, map_sum]
  simp only [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
    linearEquivTensor_symm_tmul]

private noncomputable def coactIncludeA (μ : LeftModuleAlgebra R H A) :
    A →ₐ[R] SmashProduct μ ⊗[R] H :=
  Algebra.TensorProduct.includeLeft.comp includeA

private noncomputable def coactIncludeH (μ : LeftModuleAlgebra R H A) :
    H →ₐ[R] SmashProduct μ ⊗[R] H :=
  (Algebra.TensorProduct.map (includeH (μ := μ)) (AlgHom.id R H)).comp (Bialgebra.comulAlgHom R H)

private theorem smashCompatible_coactInclude (μ : LeftModuleAlgebra R H A) :
    μ.SmashCompatible (coactIncludeA μ) (coactIncludeH μ) :=
  (smashCompatible_includeA_includeH (μ := μ)).includeLeft_map_comul (AlgHom.id R H)

private noncomputable def coactLift (μ : LeftModuleAlgebra R H A) :
    SmashProduct μ →ₐ[R] SmashProduct μ ⊗[R] H :=
  lift (coactIncludeA μ) (coactIncludeH μ) (smashCompatible_coactInclude μ)

private theorem coactLift_pure (μ : LeftModuleAlgebra R H A) (a : A) (h : H) :
    coactLift μ (pure a h) = Comodule.coact (R := R) (C := H) (pure (μ := μ) a h) := by
  rw [coact_pure_eq_sum (ℛ R h)]
  simp [coactLift, coactIncludeA, coactIncludeH, ← (ℛ R h).eq, Finset.mul_sum]

private theorem toLinearMap_coactLift (μ : LeftModuleAlgebra R H A) :
    (coactLift μ).toLinearMap = Comodule.coact (R := R) (C := H) (M := SmashProduct μ) :=
  lhom_ext fun a h => coactLift_pure μ a h

/-- The smash product `A # H` is a right `H`-comodule algebra under
`coact (a # h) = ∑ (a # h₁) ⊗ h₂`. -/
noncomputable instance instComoduleAlgebra (μ : LeftModuleAlgebra R H A) :
    ComoduleAlgebra R H (SmashProduct μ) where
  toComodule := instComodule μ
  coact_one := by
    rw [← toLinearMap_coactLift μ]
    exact (coactLift μ).map_one
  coact_mul x y := by
    rw [← toLinearMap_coactLift μ]
    exact (coactLift μ).map_mul x y

@[simp↓]
theorem coact_pure_one (a : A) :
    Comodule.coact (R := R) (C := H) (pure (μ := μ) a 1) = pure (μ := μ) a 1 ⊗ₜ[R] 1 := by
  rw [← includeA_eq_pure, ← toLinearMap_coactLift μ]
  simp [coactLift, coactIncludeA]

@[simp↓]
theorem coact_one_pure (h : H) :
    Comodule.coact (R := R) (C := H) (pure (μ := μ) 1 h) =
      Algebra.TensorProduct.map (includeH (μ := μ)) (AlgHom.id R H)
        (Coalgebra.comul (R := R) h) := by
  rw [← includeH_eq_pure, ← toLinearMap_coactLift μ]
  simp [coactLift, coactIncludeH, Bialgebra.comulAlgHom_apply]

@[simp↓]
theorem coact_includeA (a : A) :
    Comodule.coact (R := R) (C := H) (includeA (μ := μ) a) = includeA a ⊗ₜ[R] 1 := by
  rw [includeA_eq_pure, coact_pure_one, ← includeA_eq_pure]

@[simp↓]
theorem coact_includeH (h : H) :
    Comodule.coact (R := R) (C := H) (includeH (μ := μ) h) =
      Algebra.TensorProduct.map (includeH (μ := μ)) (AlgHom.id R H)
        (Coalgebra.comul (R := R) h) := by
  rw [includeH_eq_pure, coact_one_pure]

@[simp]
theorem coactAlgHom_comp_includeA (μ : LeftModuleAlgebra R H A) :
    (ComoduleAlgebra.coactAlgHom R H (SmashProduct μ)).comp includeA =
      Algebra.TensorProduct.includeLeft.comp includeA :=
  AlgHom.ext fun a => by simp

@[simp]
theorem coactAlgHom_comp_includeH (μ : LeftModuleAlgebra R H A) :
    (ComoduleAlgebra.coactAlgHom R H (SmashProduct μ)).comp includeH =
      (Algebra.TensorProduct.map (includeH (μ := μ)) (AlgHom.id R H)).comp
        (Bialgebra.comulAlgHom R H) :=
  AlgHom.ext fun h => by simp [Bialgebra.comulAlgHom_apply]

end Coaction

/-! ### Coinvariants of the smash product -/

section Coinvariants

variable (μ : LeftModuleAlgebra R H A)

/-- For every `a : A`, `includeA a` is `H`-coinvariant in `A # H`. -/
theorem includeA_mem_coinvariants (a : A) :
    includeA (μ := μ) a ∈ ComoduleAlgebra.coinvariants R H (SmashProduct μ) := by
  simp

/-- Every `H`-coinvariant element of `A # H` is recovered from `retractA μ` via `includeA`. -/
theorem includeA_retractA_of_mem_coinvariants {x : SmashProduct μ}
    (hx : x ∈ ComoduleAlgebra.coinvariants R H (SmashProduct μ)) :
    includeA (retractA μ x) = x := by
  let _ := Comodule.cofree R H A
  have hmem : linearEquivTensor μ x ∈ Comodule.fixedSubcomodule R H (A ⊗[R] H) := by
    simpa using (Comodule.transportInvHom (R := R) (C := H)
      (linearEquivTensor μ).symm).mem_fixedSubcomodule
        (Comodule.mem_fixedSubcomodule.2 (ComoduleAlgebra.mem_coinvariants.1 hx))
  refine (linearEquivTensor μ).injective ?_
  rw [linearEquivTensor_includeA]
  exact (Comodule.mem_fixedSubcomodule_cofree_iff (linearEquivTensor μ x)).1 hmem

/-- The coinvariant subalgebra `(A # H)^{co H}` equals the image `(includeA (μ := μ)).range` of
`A`, unconditionally over any commutative semiring `R` and any `R`-bialgebra `H`. -/
theorem coinvariants_eq_includeA_range :
    ComoduleAlgebra.coinvariants R H (SmashProduct μ) = (includeA (μ := μ)).range := by
  refine le_antisymm (fun x hx => ⟨retractA μ x, includeA_retractA_of_mem_coinvariants μ hx⟩) ?_
  rintro _ ⟨a, rfl⟩
  exact includeA_mem_coinvariants μ a

/-- Unconditional `R`-algebra isomorphism `A ≃ₐ[R] (A # H)^{co H}` induced by `includeA`. -/
noncomputable def includeACoinvariantsEquiv :
    A ≃ₐ[R] ComoduleAlgebra.coinvariants R H (SmashProduct μ) :=
  (AlgEquiv.ofInjective (includeA (μ := μ)) includeA_injective).trans
    (Subalgebra.equivOfEq _ _ (coinvariants_eq_includeA_range μ).symm)

@[simp]
theorem coe_includeACoinvariantsEquiv_apply (a : A) :
    (includeACoinvariantsEquiv μ a : SmashProduct μ) = includeA a :=
  (rfl)

@[simp]
theorem includeACoinvariantsEquiv_symm_apply
    (x : ComoduleAlgebra.coinvariants R H (SmashProduct μ)) :
    (includeACoinvariantsEquiv μ).symm x = retractA μ x :=
  (AlgEquiv.symm_apply_eq _).2
    (Subtype.ext (includeA_retractA_of_mem_coinvariants μ x.property).symm)

end Coinvariants

/-! ### Functoriality of the coaction -/

section Functoriality

variable {K : Type*} [Semiring K] [Bialgebra R K]
  {B : Type*} [Semiring B] [Algebra R B]

/-- Naturality of the smash-product coaction with respect to `SmashProduct.mapBialg`. -/
theorem coactAlgHom_comp_mapBialg {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) :
    (ComoduleAlgebra.coactAlgHom R H (SmashProduct ν)).comp (mapBialg g f) =
      (Algebra.TensorProduct.map (mapBialg g f) g.toAlgHom).comp
        (ComoduleAlgebra.coactAlgHom R K (SmashProduct μ)) := by
  let _ := Comodule.cofree R K A
  let _ := Comodule.cofree R H A
  let _ := Comodule.cofree R H B
  have hν : (linearEquivTensor ν).toLinearMap ∘ₗ (linearEquivTensor ν).symm.toLinearMap =
      LinearMap.id := LinearMap.ext fun y => (linearEquivTensor ν).apply_symm_apply y
  have hμ : (linearEquivTensor μ).toLinearMap ∘ₗ (linearEquivTensor μ).symm.toLinearMap =
      LinearMap.id := LinearMap.ext fun y => (linearEquivTensor μ).apply_symm_apply y
  have htrν :
      Comodule.transportCoact (R := R) (C := H) (linearEquivTensor ν).symm =
        TensorProduct.map (linearEquivTensor ν).symm.toLinearMap (LinearMap.id : H →ₗ[R] H) ∘ₗ
          Comodule.coact (R := R) (C := H) (M := B ⊗[R] H) ∘ₗ
          (linearEquivTensor ν).toLinearMap :=
    LinearMap.ext fun y => by
      simp [Comodule.transportCoact_apply]
  have htrμ :
      Comodule.transportCoact (R := R) (C := K) (linearEquivTensor μ).symm =
        TensorProduct.map (linearEquivTensor μ).symm.toLinearMap (LinearMap.id : K →ₗ[R] K) ∘ₗ
          Comodule.coact (R := R) (C := K) (M := A ⊗[R] K) ∘ₗ
          (linearEquivTensor μ).toLinearMap :=
    LinearMap.ext fun y => by
      simp [Comodule.transportCoact_apply]
  have hlin :
      Comodule.coact (R := R) (C := H) (M := SmashProduct ν) ∘ₗ (mapBialg g f).toLinearMap =
        TensorProduct.map (mapBialg g f).toLinearMap g.toAlgHom.toLinearMap ∘ₗ
          Comodule.coact (R := R) (C := K) (M := SmashProduct μ) := by
    rw [Comodule.transport_coact (R := R) (C := H) (linearEquivTensor ν).symm,
      Comodule.transport_coact (R := R) (C := K) (linearEquivTensor μ).symm,
      htrν, htrμ, toLinearMap_mapBialg]
    calc
      (TensorProduct.map (linearEquivTensor ν).symm.toLinearMap (LinearMap.id : H →ₗ[R] H) ∘ₗ
          Comodule.coact (R := R) (C := H) (M := B ⊗[R] H) ∘ₗ
          (linearEquivTensor ν).toLinearMap) ∘ₗ
          ((linearEquivTensor ν).symm.toLinearMap ∘ₗ
            TensorProduct.map f.toAlgHom.toLinearMap g.toAlgHom.toLinearMap ∘ₗ
            (linearEquivTensor μ).toLinearMap)
        = TensorProduct.map (linearEquivTensor ν).symm.toLinearMap (LinearMap.id : H →ₗ[R] H) ∘ₗ
            (Comodule.coact (R := R) (C := H) (M := B ⊗[R] H) ∘ₗ
              f.toAlgHom.toLinearMap.rTensor H) ∘ₗ
            (g.toCoalgHom : K →ₗc[R] H).toLinearMap.lTensor A ∘ₗ
            (linearEquivTensor μ).toLinearMap := by
          simp only [LinearMap.comp_assoc]
          rw [show (linearEquivTensor ν).toLinearMap ∘ₗ ((linearEquivTensor ν).symm.toLinearMap ∘ₗ
              (TensorProduct.map f.toAlgHom.toLinearMap g.toAlgHom.toLinearMap ∘ₗ
                (linearEquivTensor μ).toLinearMap)) =
              TensorProduct.map f.toAlgHom.toLinearMap g.toAlgHom.toLinearMap ∘ₗ
                (linearEquivTensor μ).toLinearMap by
            rw [← LinearMap.comp_assoc, hν, LinearMap.id_comp]]
          rw [← LinearMap.rTensor_comp_lTensor (f := f.toAlgHom.toLinearMap)
            (g := g.toAlgHom.toLinearMap)]
          simp only [LinearMap.comp_assoc]
          rfl
      _ = TensorProduct.map (linearEquivTensor ν).symm.toLinearMap (LinearMap.id : H →ₗ[R] H) ∘ₗ
            ((f.toAlgHom.toLinearMap.rTensor H).rTensor H ∘ₗ
              (Comodule.coact (R := R) (C := H) (M := A ⊗[R] H) ∘ₗ
                (g.toCoalgHom : K →ₗc[R] H).toLinearMap.lTensor A)) ∘ₗ
            (linearEquivTensor μ).toLinearMap := by
          rw [Comodule.cofree_coact, ← Comodule.cofreeCoact_def,
            Comodule.cofreeCoact_comp_rTensor, Comodule.cofreeCoact_def, ← Comodule.cofree_coact]
          simp only [LinearMap.comp_assoc]
      _ = (TensorProduct.map (linearEquivTensor ν).symm.toLinearMap (LinearMap.id : H →ₗ[R] H) ∘ₗ
            (f.toAlgHom.toLinearMap.rTensor H).rTensor H ∘ₗ
            TensorProduct.map ((g.toCoalgHom : K →ₗc[R] H).toLinearMap.lTensor A)
              (g.toCoalgHom : K →ₗc[R] H).toLinearMap) ∘ₗ
            Comodule.coact (R := R) (C := K) (M := A ⊗[R] K) ∘ₗ
            (linearEquivTensor μ).toLinearMap := by
          rw [show (g.toCoalgHom : K →ₗc[R] H).toLinearMap = (g.toCoalgHom : K →ₗc[R] H) from rfl,
            Comodule.coact_comp_lTensor_coalgHom]
          simp only [LinearMap.comp_assoc]
      _ = TensorProduct.map
            ((linearEquivTensor ν).symm.toLinearMap ∘ₗ
              TensorProduct.map f.toAlgHom.toLinearMap g.toAlgHom.toLinearMap ∘ₗ
              (linearEquivTensor μ).toLinearMap)
            g.toAlgHom.toLinearMap ∘ₗ
            (TensorProduct.map (linearEquivTensor μ).symm.toLinearMap (LinearMap.id : K →ₗ[R] K) ∘ₗ
              Comodule.coact (R := R) (C := K) (M := A ⊗[R] K) ∘ₗ
              (linearEquivTensor μ).toLinearMap) := by
          simp only [← LinearMap.comp_assoc]
          congr 2
          rw [LinearMap.rTensor_def, LinearMap.comp_assoc (TensorProduct.map _ _),
            ← TensorProduct.map_comp, ← TensorProduct.map_comp,
            LinearMap.id_comp, LinearMap.id_comp, LinearMap.rTensor_comp_lTensor]
          symm
          rw [← TensorProduct.map_comp, LinearMap.comp_assoc _ (linearEquivTensor μ).toLinearMap,
            hμ, LinearMap.comp_id, LinearMap.comp_id]
          rfl
  exact AlgHom.ext fun x => by
    have h := LinearMap.congr_fun hlin x
    simpa only [AlgHom.comp_apply, ComoduleAlgebra.coactAlgHom_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply] using
      h.trans (congr_arg (· (Comodule.coact (R := R) (C := K) x))
        (Algebra.TensorProduct.toLinearMap_map (mapBialg g f) g.toAlgHom).symm)

/-- Pointwise form of `coactAlgHom_comp_mapBialg`. -/
theorem coact_mapBialg {μ : LeftModuleAlgebra R K A} {ν : LeftModuleAlgebra R H B}
    (g : K →ₐc[R] H) (f : Hom μ (ν.restrict g)) (x : SmashProduct μ) :
    Comodule.coact (R := R) (C := H) (mapBialg g f x) =
      Algebra.TensorProduct.map (mapBialg g f) g.toAlgHom
        (Comodule.coact (R := R) (C := K) x) := by
  simpa only [AlgHom.comp_apply, ComoduleAlgebra.coactAlgHom_apply] using
    AlgHom.congr_fun (coactAlgHom_comp_mapBialg g f) x

/-- `SmashProduct.map f` bundled as a right `H`-comodule morphism `A # H → B # H`. -/
noncomputable def mapComoduleHom {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}
    (f : Hom μ ν) : Comodule.Hom R H (SmashProduct μ) (SmashProduct ν) :=
  letI := Comodule.cofree R H A
  letI := Comodule.cofree R H B
  Comodule.transportHom (linearEquivTensor μ).symm (linearEquivTensor ν).symm
    (Comodule.Hom.cofreeMap f.toAlgHom.toLinearMap)

@[simp]
theorem mapComoduleHom_apply {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}
    (f : Hom μ ν) (x : SmashProduct μ) :
    mapComoduleHom f x = map f x := by
  let _ := Comodule.cofree R H A
  let _ := Comodule.cofree R H B
  exact LinearMap.congr_fun
    (lhom_ext (f := (mapComoduleHom f).toLinearMap) (g := (map f).toLinearMap) fun a h => by
      simp [mapComoduleHom]) x

end Functoriality

end SmashProduct

end LeftModuleAlgebra

end TauCeti
