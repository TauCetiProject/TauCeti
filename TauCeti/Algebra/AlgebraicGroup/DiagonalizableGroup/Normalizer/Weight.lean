/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction

/-!
# Normalizers transport weight spaces

Suppose a rational point `g` normalizes a homomorphism `D(X) → G`, with inverse conjugation
inducing the automorphism `w` of the character group `X`. In every rational representation of
`G`, the action of `g` carries the weight space of `x` onto that of `w x`.

Normalization is expressed by an equality of coordinate morphisms valid over every value
algebra, including nonreduced ones. No smoothness, reducedness, finite type, or field
hypothesis is needed. For the adjoint representation and a split maximal torus, this is the
transport of root spaces underlying the Weyl action on roots.
The same transport statement holds for commutative monoid algebras.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.DiagonalizableGroup

noncomputable section

variable {R H X V : Type*} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
  [CommMonoid X] [AddCommMonoid V] [Module R V] [Comodule R H V]

/-- A normalizing rational point sends weight vectors to the weights obtained by pullback
along inverse conjugation. -/
theorem basePointsRepresentation_mem_weightSpace
    (π : H →ₐc[R] MonoidAlgebra R X) (g : WithConv (H →ₐ[R] R)) (w : X ≃* X)
    (hg : π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹) =
      (MonoidAlgebra.domCongr R R w).toAlgHom.comp π.toAlgHom)
    {x : X} {v : V} (hv : v ∈ weightSpace V π.toCoalgHom x) :
    Comodule.basePointsRepresentation (H := H) V g v ∈ weightSpace V π.toCoalgHom (w x) := by
  rw [mem_weightSpace_iff_endOfPoint]
  let c := AlgHom.mapValue (H := H) (Algebra.ofId R (MonoidAlgebra R X)) g
  let t := toConv π.toAlgHom
  have hconj : toConv (π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹)) =
      c⁻¹ * t * c := by
    simpa only [c, t, map_inv, inv_inv] using
      HopfAlgebra.comp_pointConjugationAlgHom g⁻¹ t
  have he := LinearMap.congr_fun
    (Comodule.endOfPoint_convMul V t c) (1 ⊗ₜ[R] v)
  have he' := LinearMap.congr_fun
    (Comodule.endOfPoint_convMul V c (c⁻¹ * t * c)) (1 ⊗ₜ[R] v)
  have hw := endOfPoint_tmul_of_mem_weightSpace V π
    (MonoidAlgebra.domCongr R R w).toAlgHom 1 hv
  have hconj' : π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹) =
      (c⁻¹ * t * c).ofConv := congrArg ofConv hconj
  rw [← hg, hconj'] at hw
  simp only [AlgEquiv.coe_toAlgHom,
    MonoidAlgebra.domCongr_single, one_mul] at hw
  simp only [LinearMap.comp_apply] at he he'
  simp only [← mul_assoc, mul_inv_cancel, one_mul] at he'
  rw [← Comodule.endOfPoint_mapValue_algebraOfId_tmul g 1 v, ← he, he', hw]
  exact Comodule.endOfPoint_mapValue_algebraOfId_tmul g _ v

/-- The normalization equation for inverse conjugation also gives its inverse equation. -/
private theorem inverse_normalization
    (π : H →ₐc[R] MonoidAlgebra R X) (g : WithConv (H →ₐ[R] R)) (w : X ≃* X)
    (hg : π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹) =
      (MonoidAlgebra.domCongr R R w).toAlgHom.comp π.toAlgHom) :
    π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g) =
      (MonoidAlgebra.domCongr R R w.symm).toAlgHom.comp π.toAlgHom := by
  apply AlgHom.ext
  intro h
  have hc := AlgHom.congr_fun (HopfAlgebra.pointConjugationAlgHom_mul g g⁻¹) h
  simp only [mul_inv_cancel, HopfAlgebra.pointConjugationAlgHom_one,
    AlgHom.id_apply, AlgHom.comp_apply] at hc
  have he := AlgHom.congr_fun hg (HopfAlgebra.pointConjugationAlgHom g h)
  simp only [AlgHom.comp_apply] at he
  rw [← hc] at he
  apply (MonoidAlgebra.domCongr R R w).injective
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, ← MonoidAlgebra.domCongr_symm,
    AlgEquiv.apply_symm_apply] using he.symm

/-- A normalizing point carries a weight space onto the permuted weight space. -/
theorem map_weightSpace_basePointsRepresentation
    (π : H →ₐc[R] MonoidAlgebra R X) (g : WithConv (H →ₐ[R] R)) (w : X ≃* X)
    (hg : π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹) =
      (MonoidAlgebra.domCongr R R w).toAlgHom.comp π.toAlgHom) (x : X) :
    (weightSpace V π.toCoalgHom x).map (Comodule.basePointsRepresentation (H := H) V g) =
      weightSpace V π.toCoalgHom (w x) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact basePointsRepresentation_mem_weightSpace π g w hg hv
  · intro v hv
    apply Submodule.mem_map.mpr
    refine ⟨Comodule.basePointsRepresentation (H := H) V g⁻¹ v, ?_, ?_⟩
    · have hv' := basePointsRepresentation_mem_weightSpace π g⁻¹ w.symm
          (by simpa only [inv_inv] using inverse_normalization π g w hg) hv
      rw [MulEquiv.symm_apply_apply] at hv'
      exact hv'
    · exact Representation.self_inv_apply _ g v

/-- Normalization preserves whether a weight space is nonzero. -/
theorem weightSpace_apply_ne_bot_iff
    (π : H →ₐc[R] MonoidAlgebra R X) (g : WithConv (H →ₐ[R] R)) (w : X ≃* X)
    (hg : π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹) =
      (MonoidAlgebra.domCongr R R w).toAlgHom.comp π.toAlgHom) (x : X) :
    weightSpace V π.toCoalgHom (w x) ≠ ⊥ ↔ weightSpace V π.toCoalgHom x ≠ ⊥ := by
  rw [← map_weightSpace_basePointsRepresentation π g w hg x]
  have hi := Submodule.map_injective_of_injective
    (Representation.apply_bijective (Comodule.basePointsRepresentation (H := H) V) g).1
  have hb : (weightSpace V π.toCoalgHom x).map
        (Comodule.basePointsRepresentation (H := H) V g) =
      (⊥ : Submodule R V).map (Comodule.basePointsRepresentation (H := H) V g) ↔
      weightSpace V π.toCoalgHom x = ⊥ := hi.eq_iff
  simpa only [Submodule.map_bot] using not_congr hb

end

end TauCeti.DiagonalizableGroup
