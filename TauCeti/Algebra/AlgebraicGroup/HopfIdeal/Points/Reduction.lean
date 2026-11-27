/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Reduction

/-!
# Points of the reduction of a commutative Hopf algebra

Every algebra-valued point of a commutative Hopf algebra `H` valued in a reduced algebra `A`
kills all nilpotent elements, and hence factors uniquely through the reduced quotient
`H ⧸ (TauCeti.HopfIdeal.reduction R H).toIdeal`. This identification is a group isomorphism on
convolution groups (`TauCeti.HopfIdeal.reductionPointsMulEquiv`) and is natural with respect to
the induced map on reduced quotients (`TauCeti.HopfIdeal.reductionBialgHom`).

## Main declarations

* `TauCeti.HopfIdeal.reductionPointsMulEquiv`: the multiplicative equivalence between reduced-valued
  points of the reduced quotient and of `H`.
* `TauCeti.HopfIdeal.reductionPointsMulEquiv_apply`: evaluation as `BialgHom.mapDomain` along the
  quotient morphism.
* `TauCeti.HopfIdeal.reductionPointsMulEquiv_symm_apply`: inverse evaluation via
  `Ideal.Quotient.liftₐ`.
* `TauCeti.HopfIdeal.reductionPointsMulEquiv_mapDomain_reductionBialgHom`: naturality with respect
  to `TauCeti.HopfIdeal.reductionBialgHom`.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u v w x

variable (R : Type u) [CommRing R] [IsReduced R]
variable (H : Type v) [CommRing H] [_root_.HopfAlgebra R H]
variable [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))]
variable (A : Type w) [CommSemiring A] [IsReduced A] [Algebra R A]

/-- Every point of `H` valued in a reduced `R`-algebra factors uniquely through the reduced
quotient `H ⧸ (HopfIdeal.reduction R H).toIdeal`. -/
noncomputable def reductionPointsMulEquiv :
    WithConv ((H ⧸ (reduction R H).toIdeal) →ₐ[R] A) ≃* WithConv (H →ₐ[R] A) :=
  let I := reduction R H
  let q := Bialgebra.Quotient.mkBialgHom I.toIdeal
  MulEquiv.ofBijective (BialgHom.mapDomain (A := A) q)
    ⟨BialgHom.mapDomain_injective_of_surjective q (Bialgebra.Quotient.mkBialgHom_surjective _),
      fun a => by
        have ha_ker : ∀ x ∈ I.toIdeal, a.ofConv x = 0 := fun x hx =>
          ((mem_nilradical.mp (reduction_toIdeal R H ▸ hx)).map
            a.ofConv.toRingHom).eq_zero
        refine ⟨toConv (Ideal.Quotient.liftₐ I.toIdeal a.ofConv ha_ker), ?_⟩
        rw [BialgHom.mapDomain_apply, ofConv_toConv, Bialgebra.Quotient.mkBialgHom_toAlgHom,
          Ideal.Quotient.liftₐ_comp, toConv_ofConv]⟩

/-- `reductionPointsMulEquiv` acts by precomposition with the quotient bialgebra morphism. -/
@[simp]
theorem reductionPointsMulEquiv_apply
    (g : WithConv ((H ⧸ (reduction R H).toIdeal) →ₐ[R] A)) :
    reductionPointsMulEquiv R H A g =
      BialgHom.mapDomain (A := A) (Bialgebra.Quotient.mkBialgHom (reduction R H).toIdeal) g :=
  (rfl)

/-- The inverse of `reductionPointsMulEquiv` lifts a reduced-valued point of `H` through the
reduced quotient `H ⧸ (HopfIdeal.reduction R H).toIdeal`. -/
@[simp]
theorem reductionPointsMulEquiv_symm_apply (a : WithConv (H →ₐ[R] A)) :
    (reductionPointsMulEquiv R H A).symm a =
      toConv (Ideal.Quotient.liftₐ (reduction R H).toIdeal a.ofConv fun x hx =>
        ((mem_nilradical.mp (reduction_toIdeal R H ▸ hx)).map a.ofConv.toRingHom).eq_zero) := by
  apply (reductionPointsMulEquiv R H A).injective
  rw [MulEquiv.apply_symm_apply, reductionPointsMulEquiv_apply, BialgHom.mapDomain_apply,
    ofConv_toConv, Bialgebra.Quotient.mkBialgHom_toAlgHom, Ideal.Quotient.liftₐ_comp,
    toConv_ofConv]

variable {R H A}

/-- Naturality of `reductionPointsMulEquiv` with respect to `reductionBialgHom`. -/
theorem reductionPointsMulEquiv_mapDomain_reductionBialgHom
    {H' : Type x} [CommRing H'] [_root_.HopfAlgebra R H']
    [IsReduced ((H' ⧸ nilradical H') ⊗[R] (H' ⧸ nilradical H'))]
    (φ : H →ₐc[R] H')
    (g : WithConv ((H' ⧸ (reduction R H').toIdeal) →ₐ[R] A)) :
    reductionPointsMulEquiv R H A (BialgHom.mapDomain (reductionBialgHom φ) g) =
      BialgHom.mapDomain φ (reductionPointsMulEquiv R H' A g) := by
  rw [reductionPointsMulEquiv_apply, reductionPointsMulEquiv_apply, ← MonoidHom.comp_apply,
    ← BialgHom.mapDomain_comp, reductionBialgHom_comp_mkBialgHom, BialgHom.mapDomain_comp,
    MonoidHom.comp_apply]

end TauCeti.HopfIdeal
