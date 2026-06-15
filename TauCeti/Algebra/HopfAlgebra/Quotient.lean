/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.Algebra.HopfAlgebra.HopfIdeal

/-!
# The quotient Hopf algebra of a Hopf ideal

For a commutative Hopf algebra `H` over a commutative ring `R` and a Hopf ideal `I` of `H`,
this file equips the quotient ring `H ⧸ I` with the structure of a Hopf algebra over `R`,
descending the comultiplication, counit and antipode from `H`. The quotient map
`H →ₐ[R] H ⧸ I` is then a Hopf algebra morphism by construction.

This is the Layer 3 milestone "the quotient Hopf algebra `A/I`" of the reductive-groups
roadmap: closed subgroup schemes of an affine group scheme are represented on coordinate
rings by exactly these quotient Hopf algebras, and the three Hopf-ideal closure conditions
(`comul (I) ⊆ I ⊗ H + H ⊗ I`, `counit (I) = 0`, `S(I) ⊆ I`) are precisely what is needed for
the structure maps to descend.

The construction only uses the *easy* direction of the kernel computation for tensor products:
the comultiplication descends because `comul x` lands in `I ⊗ H + H ⊗ I`, which the quotient
map kills. No exactness or flatness input is needed; that is what the Hopf-ideal axioms buy.

## Main definitions

* `TauCeti.HopfIdeal.quotientComulAlgHom`, `TauCeti.HopfIdeal.quotientCounitAlgHom`: the
  comultiplication and counit of the quotient, as `R`-algebra homomorphisms descended from `H`.
* `TauCeti.HopfIdeal.instCoalgebraQuotient`, `instBialgebraQuotient`,
  `instHopfAlgebraQuotient`: the coalgebra, bialgebra and Hopf algebra structures on `H ⧸ I`.
* `TauCeti.HopfIdeal.mkBialgHom`: the quotient map `H →ₐc[R] H ⧸ I` as a bialgebra morphism.

## References

This follows the standard construction of the quotient Hopf algebra; see Sweedler,
*Hopf Algebras*, Chapter 4, and Waterhouse, *Introduction to Affine Group Schemes*, §16. It
builds on the `TauCeti.HopfIdeal` API and Mathlib's algebra-quotient lift `Ideal.Quotient.liftₐ`,
the tensor-product algebra map `Algebra.TensorProduct.map`, and the bialgebra/Hopf-algebra
constructors `Bialgebra.mk'` and the `HopfAlgebra` axioms.
-/

open scoped TensorProduct

namespace TauCeti

namespace HopfIdeal

universe u v

variable {R : Type u} {H : Type v}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable (I : HopfIdeal R H)

/-- The tensor square of the quotient map, `H ⊗ H →ₐ[R] (H ⧸ I) ⊗ (H ⧸ I)`. -/
private noncomputable abbrev mkₐ₂ :
    H ⊗[R] H →ₐ[R] (H ⧸ I.toIdeal) ⊗[R] (H ⧸ I.toIdeal) :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal) (Ideal.Quotient.mkₐ R I.toIdeal)

/-- The tensor square of the quotient map kills `I ⊗ H + H ⊗ I`. -/
private theorem leSup_le_ker_mkₐ₂ :
    leftTensorIdeal (R := R) (H := H) I.toIdeal ⊔ rightTensorIdeal (R := R) (H := H) I.toIdeal ≤
      RingHom.ker (mkₐ₂ I).toRingHom := by
  apply sup_le
  · rw [leftTensorIdeal_le_iff]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change mkₐ₂ I (Algebra.TensorProduct.includeLeft y) = 0
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul, map_one,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hy, TensorProduct.zero_tmul]
  · rw [rightTensorIdeal_le_iff]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change mkₐ₂ I (Algebra.TensorProduct.includeRight y) = 0
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hy, TensorProduct.tmul_zero]

/-- The comultiplication of the quotient, as an `R`-algebra homomorphism descended from `H`. -/
noncomputable def quotientComulAlgHom :
    (H ⧸ I.toIdeal) →ₐ[R] (H ⧸ I.toIdeal) ⊗[R] (H ⧸ I.toIdeal) :=
  Ideal.Quotient.liftₐ I.toIdeal ((mkₐ₂ I).comp (Bialgebra.comulAlgHom R H)) <| by
    intro x hx
    rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
    exact RingHom.mem_ker.mp (leSup_le_ker_mkₐ₂ I (I.comul_mem (mem_toIdeal.mp hx)))

/-- The counit of the quotient, as an `R`-algebra homomorphism descended from `H`. -/
noncomputable def quotientCounitAlgHom : (H ⧸ I.toIdeal) →ₐ[R] R :=
  Ideal.Quotient.liftₐ I.toIdeal (Bialgebra.counitAlgHom R H) <| by
    intro x hx
    rw [Bialgebra.counitAlgHom_apply]
    exact I.counit_eq_zero (mem_toIdeal.mp hx)

@[simp]
theorem quotientComulAlgHom_mk (h : H) :
    quotientComulAlgHom I (Ideal.Quotient.mkₐ R I.toIdeal h)
      = Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal)
        (Ideal.Quotient.mkₐ R I.toIdeal) (Coalgebra.comul h) := by
  rw [quotientComulAlgHom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]

@[simp]
theorem quotientCounitAlgHom_mk (h : H) :
    quotientCounitAlgHom I (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Coalgebra.counit (R := R) h := by
  rw [quotientCounitAlgHom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom, Bialgebra.counitAlgHom_apply]

/-- The underlying linear quotient map `H →ₗ[R] H ⧸ I`. -/
private noncomputable abbrev mkL : H →ₗ[R] H ⧸ I.toIdeal :=
  (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap

private theorem mkL_surjective : Function.Surjective (mkL I) :=
  Ideal.Quotient.mkₐ_surjective R I.toIdeal

private theorem comul_mkL_apply (h : H) :
    (quotientComulAlgHom I).toLinearMap (mkL I h)
      = TensorProduct.map (mkL I) (mkL I) (Coalgebra.comul h) := by
  change quotientComulAlgHom I (Ideal.Quotient.mkₐ R I.toIdeal h) = _
  rw [quotientComulAlgHom_mk]
  exact LinearMap.congr_fun
    (Algebra.TensorProduct.toLinearMap_map (Ideal.Quotient.mkₐ R I.toIdeal)
      (Ideal.Quotient.mkₐ R I.toIdeal)) _

/-- The quotient comultiplication intertwines `mkL` with the comultiplication of `H`. -/
private theorem comul_comp_mkL :
    (quotientComulAlgHom I).toLinearMap ∘ₗ mkL I
      = TensorProduct.map (mkL I) (mkL I) ∘ₗ Coalgebra.comul := by
  ext h
  simpa only [LinearMap.comp_apply] using comul_mkL_apply I h

/-- The quotient counit intertwines `mkL` with the counit of `H`. -/
private theorem counit_comp_mkL :
    (quotientCounitAlgHom I).toLinearMap ∘ₗ mkL I = Coalgebra.counit (R := R) := by
  ext h
  change quotientCounitAlgHom I (Ideal.Quotient.mkₐ R I.toIdeal h) = _
  rw [quotientCounitAlgHom_mk]

/-- A linear map out of the quotient is determined by its precomposition with `mkL`. -/
private theorem linearMap_ext {N : Type*} [AddCommMonoid N] [Module R N]
    {f g : (H ⧸ I.toIdeal) →ₗ[R] N} (hfg : f ∘ₗ mkL I = g ∘ₗ mkL I) : f = g := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨a, rfl⟩ := mkL_surjective I q
  exact LinearMap.congr_fun hfg a

/-- The coalgebra structure on the quotient, descended from `H`. The coalgebra laws are proved
by transporting `H`'s own laws along the surjective quotient map, using the naturality of the
tensor-product constructions (`LinearMap.rTensor_map` and friends) to avoid tensor inductions. -/
noncomputable instance instCoalgebraQuotient : Coalgebra R (H ⧸ I.toIdeal) where
  comul := (quotientComulAlgHom I).toLinearMap
  counit := (quotientCounitAlgHom I).toLinearMap
  coassoc := by
    refine linearMap_ext I (LinearMap.ext fun h => ?_)
    simp only [LinearMap.comp_apply, comul_mkL_apply, LinearMap.rTensor_map, LinearMap.lTensor_map,
      comul_comp_mkL, ← LinearMap.map_rTensor, ← LinearMap.map_lTensor]
    exact (TensorProduct.map_map_assoc (mkL I) (mkL I) (mkL I) _).symm.trans
      (congrArg _ (Coalgebra.coassoc_apply h))
  rTensor_counit_comp_comul := by
    refine linearMap_ext I ?_
    rw [LinearMap.comp_assoc, comul_comp_mkL, ← LinearMap.comp_assoc, LinearMap.rTensor_comp_map,
      counit_comp_mkL, ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_assoc,
      Coalgebra.rTensor_counit_comp_comul]
    ext h
    simp only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.lTensor_tmul]
  lTensor_counit_comp_comul := by
    refine linearMap_ext I ?_
    rw [LinearMap.comp_assoc, comul_comp_mkL, ← LinearMap.comp_assoc, LinearMap.lTensor_comp_map,
      counit_comp_mkL, ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_assoc,
      Coalgebra.lTensor_counit_comp_comul]
    ext h
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      LinearMap.rTensor_tmul]

/-- The comultiplication on the quotient, evaluated on a quotient class. -/
@[simp]
theorem comul_mk (h : H) :
    Coalgebra.comul (R := R) (Ideal.Quotient.mkₐ R I.toIdeal h)
      = TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap
        (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap (Coalgebra.comul h) :=
  comul_mkL_apply I h

/-- The counit on the quotient, evaluated on a quotient class. -/
@[simp]
theorem counit_mk (h : H) :
    Coalgebra.counit (R := R) (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Coalgebra.counit (R := R) h :=
  quotientCounitAlgHom_mk I h

/-- The bialgebra structure on the quotient: the descended comultiplication and counit are
algebra homomorphisms, so they preserve `1` and products. -/
noncomputable instance instBialgebraQuotient : Bialgebra R (H ⧸ I.toIdeal) :=
  Bialgebra.mk' R (H ⧸ I.toIdeal)
    (map_one (quotientCounitAlgHom I))
    (fun {a b} => map_mul (quotientCounitAlgHom I) a b)
    (map_one (quotientComulAlgHom I))
    (fun {a b} => map_mul (quotientComulAlgHom I) a b)

/-- The antipode of the quotient, as an `R`-algebra homomorphism descended from `H` (valid since
`H` is commutative, where the antipode is an algebra homomorphism). -/
noncomputable def quotientAntipodeAlgHom : (H ⧸ I.toIdeal) →ₐ[R] H ⧸ I.toIdeal :=
  Ideal.Quotient.liftₐ I.toIdeal
    ((Ideal.Quotient.mkₐ R I.toIdeal).comp (HopfAlgebra.antipodeAlgHom R H)) <| by
    intro x hx
    rw [AlgHom.comp_apply, HopfAlgebra.antipodeAlgHom_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.antipode_mem (mem_toIdeal.mp hx))

@[simp]
theorem quotientAntipodeAlgHom_mk (h : H) :
    quotientAntipodeAlgHom I (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R h) := by
  simp only [quotientAntipodeAlgHom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom, AlgHom.comp_apply,
    HopfAlgebra.antipodeAlgHom_apply]

@[simp]
private theorem antipode_comp_mkL :
    (quotientAntipodeAlgHom I).toLinearMap ∘ₗ mkL I = mkL I ∘ₗ HopfAlgebra.antipode R := by
  ext h
  exact quotientAntipodeAlgHom_mk I h

/-- Multiplication on the quotient is the transport of multiplication on `H`: this is the
naturality of `LinearMap.mul'` along the algebra homomorphism `mkL`. -/
private theorem mul'_comp_map_mkL :
    LinearMap.mul' R (H ⧸ I.toIdeal) ∘ₗ TensorProduct.map (mkL I) (mkL I)
      = mkL I ∘ₗ LinearMap.mul' R H := by
  refine TensorProduct.ext' fun a b => ?_
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
    AlgHom.toLinearMap_apply, map_mul]

private theorem mul'_map_mkL_apply (x : H ⊗[R] H) :
    LinearMap.mul' R (H ⧸ I.toIdeal) (TensorProduct.map (mkL I) (mkL I) x)
      = mkL I (LinearMap.mul' R H x) :=
  LinearMap.congr_fun (mul'_comp_map_mkL I) x

/-- The Hopf algebra structure on the quotient, descended from `H`. The antipode axioms are
transported from `H` along the surjective quotient map (valid since `H` is commutative). -/
noncomputable instance instHopfAlgebraQuotient : HopfAlgebra R (H ⧸ I.toIdeal) where
  antipode := (quotientAntipodeAlgHom I).toLinearMap
  mul_antipode_rTensor_comul := by
    refine linearMap_ext I (LinearMap.ext fun h => ?_)
    simp only [LinearMap.comp_apply, comul_mk, LinearMap.rTensor_map, antipode_comp_mkL,
      ← LinearMap.map_rTensor, mul'_map_mkL_apply, HopfAlgebra.mul_antipode_rTensor_comul_apply,
      AlgHom.toLinearMap_apply, AlgHom.commutes, Algebra.linearMap_apply, counit_mk]
  mul_antipode_lTensor_comul := by
    refine linearMap_ext I (LinearMap.ext fun h => ?_)
    simp only [LinearMap.comp_apply, comul_mk, LinearMap.lTensor_map, antipode_comp_mkL,
      ← LinearMap.map_lTensor, mul'_map_mkL_apply, HopfAlgebra.mul_antipode_lTensor_comul_apply,
      AlgHom.toLinearMap_apply, AlgHom.commutes, Algebra.linearMap_apply, counit_mk]

/-- The quotient map `H →ₐ[R] H ⧸ I` as a bialgebra morphism: it is an algebra homomorphism
respecting the counit and comultiplication by construction. -/
noncomputable def mkBialgHom : H →ₐc[R] H ⧸ I.toIdeal :=
  BialgHom.ofAlgHom (Ideal.Quotient.mkₐ R I.toIdeal)
    (by ext h; simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, counit_mk])
    (by
      ext h
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, comul_mk]
      exact LinearMap.congr_fun
        (Algebra.TensorProduct.toLinearMap_map (Ideal.Quotient.mkₐ R I.toIdeal)
          (Ideal.Quotient.mkₐ R I.toIdeal)) _)

@[simp]
theorem mkBialgHom_apply (h : H) : mkBialgHom I h = Ideal.Quotient.mkₐ R I.toIdeal h := rfl

end HopfIdeal

end TauCeti
