/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Finite
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central
import TauCeti.RingTheory.FiniteType.FiniteRange
import TauCeti.LinearAlgebra.TensorProduct.Basis
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints

/-!
# Normal diagonalizable subgroups are central

A normal diagonalizable closed subgroup of a reduced connected affine group of finite type
over an algebraically closed field is central. The diagonalizable subgroup need not be reduced:
the conclusion concerns its full scheme structure, including infinitesimal subgroups.

The normalizer acts through a finite group of character automorphisms. Conjugation coefficients
are regular functions on the ambient group, so connectedness makes them constant. Specializing
at the identity makes the restricted conjugation trivial. Point separation is used only on the
reduced ambient coordinate ring, never on the diagonalizable subgroup.

## References

* J. S. Milne, *Algebraic Groups* (2017), Corollary 12.38.

The finite character action is `BialgHom.finite_range_normalizerCharacterHom`. The constancy
argument follows `TauCeti.Comodule.nonzeroJointWeightAction_basePointsRepresentation_eq_one`.
-/

public section

open TauCeti WithConv
open scoped TensorProduct

namespace BialgHom

noncomputable section

variable {k H X : Type*} [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X]

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
  [ConnectedSpace (PrimeSpectrum H)]

private theorem conjugation_tensor_eq_of_isNormal
    (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (hN : (HopfIdeal.kerOfSurjective π hπ).IsNormal) (x : H) :
    TensorProduct.map LinearMap.id π.toAlgHom.toLinearMap
      (HopfAlgebra.conjugationAlgHom (R := k) (H := H) x) = (1 : H) ⊗ₜ[k] π x := by
  classical
  have hnormalizer (g : WithConv (H →ₐ[k] k)) : g ∈ normalizerPoints π hπ := by
    rw [mem_normalizerPoints]
    apply le_antisymm
    · have h := hN.le_conjugate g⁻¹
      exact (HopfIdeal.conjugate_mono g h).trans_eq
        (HopfIdeal.conjugate_conjugate_inv _ g)
    · exact hN.le_conjugate g
  have hfinite (x : H) : (Set.range fun g : WithConv (H →ₐ[k] k) ↦
      π (HopfAlgebra.pointConjugationAlgHom g x)).Finite := by
    apply ((finite_range_normalizerCharacterHom π hπ).image
      (fun w ↦ MonoidAlgebra.domCongr k k w (π x))).subset
    rintro _ ⟨g, rfl⟩
    refine ⟨normalizerCharacterHom π hπ ⟨g⁻¹, hnormalizer g⁻¹⟩,
      ⟨⟨g⁻¹, hnormalizer g⁻¹⟩, rfl⟩, ?_⟩
    simpa using (AlgHom.congr_fun
      (normalizerCharacterHom_comp π hπ ⟨g⁻¹, hnormalizer g⁻¹⟩) x).symm
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  let z := TensorProduct.map LinearMap.id π.toAlgHom.toLinearMap
    (HopfAlgebra.conjugationAlgHom (R := k) (H := H) x)
  let a := LinearMap.tensorComponent φ z
  have heval (f : H →ₐ[k] k) : f a = φ (π (HopfAlgebra.pointConjugationAlgHom (toConv f) x)) := by
    have h := (π.toAlgHom.apply_pointConjugationAlgHom (toConv f) x).symm
    have hc := congrArg φ h
    have hcontract := LinearMap.congr_fun (f.toLinearMap.comp_tensorComponent φ) z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_def,
      AlgHom.toLinearMap_apply] at hcontract
    rw [hcontract]
    simpa only [z, TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp,
      ofConv_toConv, BialgHom.coe_toAlgHom] using hc
  have ha : (Set.range fun f : H →ₐ[k] k ↦ f a).Finite := by
    apply ((hfinite x).image φ).subset
    rintro _ ⟨f, rfl⟩
    exact ⟨π (HopfAlgebra.pointConjugationAlgHom (toConv f) x),
      ⟨toConv f, rfl⟩, (heval f).symm⟩
  have hconstant := eq_algebraMap_of_finite_range_eval a ha
    (1 : WithConv (H →ₐ[k] k)).ofConv
  rw [heval] at hconstant
  simpa [a, z, Algebra.algebraMap_eq_smul_one] using hconstant

private theorem commute_mapDomain_of_isNormal
    (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (hN : (HopfIdeal.kerOfSurjective π hπ).IsNormal)
    {A : Type*} [CommRing A] [Algebra k A]
    (g : WithConv (H →ₐ[k] A)) (t : WithConv (MonoidAlgebra k X →ₐ[k] A)) :
    Commute g (AlgHom.mapDomain π t) := by
  have hconj : g * AlgHom.mapDomain π t * g⁻¹ = AlgHom.mapDomain π t := by
    apply ofConv_injective
    apply AlgHom.ext
    intro x
    have h := congrArg (Algebra.TensorProduct.productMap g.ofConv t.ofConv)
      (conjugation_tensor_eq_of_isNormal π hπ hN x)
    have hmap (z : H ⊗[k] H) :
        Algebra.TensorProduct.productMap g.ofConv t.ofConv
          (TensorProduct.map LinearMap.id π.toAlgHom.toLinearMap z) =
        Algebra.TensorProduct.productMap g.ofConv (t.ofConv.comp π.toAlgHom) z := by
      induction z using TensorProduct.inductionOn with
      | add a b ha hb => simp_all
      | tmul a b => simp
    rw [hmap] at h
    rw [← AlgHom.comp_apply, HopfAlgebra.productMap_comp_conjugationAlgHom] at h
    simpa [AlgHom.mapDomain_apply] using h
  exact (commute_iff_eq _ _).mpr (mul_inv_eq_iff_eq_mul.mp hconj)

/-- A normal diagonalizable closed subgroup of a reduced connected finite-type affine group
over an algebraically closed field is central as a subgroup scheme. No smoothness or
reducedness of the diagonalizable subgroup is assumed. -/
theorem isCentral_kerOfSurjective_of_isNormal
    (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (hN : (HopfIdeal.kerOfSurjective π hπ).IsNormal) :
    (HopfIdeal.kerOfSurjective π hπ).IsCentral := by
  apply (CommHopfAlgCat.isCentral_iff_forall_isCentralPoint
    (_root_.CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ)).mpr
  intro A g hg
  rw [HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range] at hg
  obtain ⟨t, rfl⟩ := hg
  rw [HopfAlgebra.isCentralPoint_def]
  intro B _ _ φ h
  have hnat := DFunLike.congr_fun (AlgHom.mapValue_mapDomain π φ).symm t
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hnat
  rw [hnat]
  exact (commute_mapDomain_of_isNormal π hπ hN h (AlgHom.mapValue φ t)).symm

end

end BialgHom
