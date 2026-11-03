/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Finite
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Normal
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
import TauCeti.RingTheory.FiniteType.FiniteRange
import TauCeti.LinearAlgebra.TensorProduct.Basis
import TauCeti.Algebra.TensorProduct.MapLinear
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Connected subgroups of a diagonalizable subgroup's normalizer

A morphism from a reduced connected affine group into the normalizer of a closed
diagonalizable subgroup factors through its centralizer. Both groups are of finite type
over an algebraically closed field, but the ambient group and the diagonalizable subgroup
may be nonreduced. The conclusion is scheme-theoretic and controls every value algebra.

This is the connectedness step in comparing normalizer quotients with Weyl groups.
The finite character action from `BialgHom.finite_range_normalizerCharacterHom` makes
conjugation coefficients constant on the connected source. Their values at the identity
then force the restricted conjugation to be trivial.

The coefficient argument also gives centrality of normal diagonalizable subgroups,
as recorded in `TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normal`.
The final results identify the normalizer and centralizer tangent Lie algebras when
the normalizer is reduced; no reducedness of the diagonalizable subgroup is required.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12 and §21.1.
* T. A. Springer, *Linear Algebraic Groups*, §7.1.
-/

public section

open TauCeti WithConv
open scoped TensorProduct

namespace BialgHom

noncomputable section

variable {k H K X : Type*} [Field k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [CommGroup X]
  [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K] [IsReduced K]
  [ConnectedSpace (PrimeSpectrum K)]

private theorem map_conjugation_tensor_eq
    (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (φ : H →ₐc[k] K)
    (hnorm : ∀ g : WithConv (K →ₐ[k] k), mapDomain φ g ∈ normalizerPoints π hπ)
    (x : H) :
    TensorProduct.map φ.toAlgHom.toLinearMap π.toAlgHom.toLinearMap
      (HopfAlgebra.conjugationAlgHom (R := k) (H := H) x) = (1 : K) ⊗ₜ[k] π x := by
  classical
  have hfinite (x : H) : (Set.range fun g : WithConv (K →ₐ[k] k) ↦
      π (HopfAlgebra.pointConjugationAlgHom (mapDomain φ g) x)).Finite := by
    apply ((finite_range_normalizerCharacterHom π hπ).image
      (fun w ↦ MonoidAlgebra.domCongr k k w (π x))).subset
    rintro _ ⟨g, rfl⟩
    refine ⟨normalizerCharacterHom π hπ ⟨mapDomain φ g⁻¹, hnorm g⁻¹⟩,
      ⟨⟨mapDomain φ g⁻¹, hnorm g⁻¹⟩, rfl⟩, ?_⟩
    have he := (AlgHom.congr_fun
      (normalizerCharacterHom_comp π hπ ⟨mapDomain φ g⁻¹, hnorm g⁻¹⟩) x).symm
    simp only [AlgHom.comp_apply] at he
    conv_rhs at he => simp only [Subtype.coe_mk, map_inv, inv_inv]
    simpa using he
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro ψ
  let z := TensorProduct.map φ.toAlgHom.toLinearMap π.toAlgHom.toLinearMap
    (HopfAlgebra.conjugationAlgHom (R := k) (H := H) x)
  let a := LinearMap.tensorComponent ψ z
  have heval (f : K →ₐ[k] k) :
      f a = ψ (π (HopfAlgebra.pointConjugationAlgHom (mapDomain φ (toConv f)) x)) := by
    have h := (π.toAlgHom.toLinearMap.apply_pointConjugationAlgHom
      (mapDomain φ (toConv f)) x).symm
    have hc := congrArg ψ h
    have hcontract := LinearMap.congr_fun (f.toLinearMap.comp_tensorComponent ψ) z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_def,
      AlgHom.toLinearMap_apply] at hcontract
    rw [hcontract]
    simpa only [z, TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp,
      mapDomain_apply, ofConv_toConv, AlgHom.comp_toLinearMap, AlgHom.toLinearMap_apply,
      BialgHom.coe_toAlgHom] using hc
  have ha : (Set.range fun f : K →ₐ[k] k ↦ f a).Finite := by
    apply ((hfinite x).image ψ).subset
    rintro _ ⟨f, rfl⟩
    exact ⟨π (HopfAlgebra.pointConjugationAlgHom (mapDomain φ (toConv f)) x),
      ⟨toConv f, rfl⟩, (heval f).symm⟩
  have hconstant := eq_algebraMap_of_finite_range_eval a ha
    (1 : WithConv (K →ₐ[k] k)).ofConv
  rw [heval, map_one, HopfAlgebra.pointConjugationAlgHom_one, AlgHom.id_apply] at hconstant
  simpa [a, z, Algebra.algebraMap_eq_smul_one] using hconstant

/-- A morphism from a reduced connected affine group of finite type whose rational points
normalize a closed diagonalizable subgroup factors through its scheme-theoretic centralizer.
Neither the ambient group nor the diagonalizable subgroup needs to be reduced. -/
theorem centralizerHopfIdeal_le_ker_of_forall_mapDomain_mem_normalizerPoints
    (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (φ : H →ₐc[k] K)
    (hnorm : ∀ g : WithConv (K →ₐ[k] k), mapDomain φ g ∈ normalizerPoints π hπ) :
    (centralizerHopfIdeal π).toIdeal ≤ RingHom.ker φ := by
  rw [centralizerHopfIdeal_toIdeal, Ideal.span_le]
  rintro _ ⟨⟨x, χ⟩, rfl⟩
  apply RingHom.mem_ker.mpr
  dsimp only
  have h := map_conjugation_tensor_eq π hπ φ hnorm x
  have hz : TensorProduct.map φ.toAlgHom.toLinearMap LinearMap.id
      (centralizerDefect π x) = 0 := by
    simp only [centralizerDefect_def, map_sub, TensorProduct.map_algebraTensorProduct_map,
      AlgHom.toLinearMap_id, LinearMap.comp_id, LinearMap.id_comp, TensorProduct.map_tmul,
      AlgHom.toLinearMap_apply, map_one, LinearMap.id_apply, h, sub_self]
  simpa only [AlgHom.toLinearMap_apply, BialgHom.coe_toAlgHom] using
    (map_centralizerDefect_eq_zero_iff π φ.toAlgHom.toLinearMap x).mp hz χ

end

section ClosedSubgroup

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k} {X : Type u} [CommGroup X]
  (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)

/-- A reduced connected closed subgroup of the scheme-theoretic normalizer of a closed
diagonalizable subgroup lies in its scheme-theoretic centralizer. Ideal inclusions reverse
the inclusions of subgroup schemes. -/
theorem centralizerHopfIdeal_le_of_le_normalizerHopfIdeal (I : HopfIdeal k H)
    [IsReduced (FiniteTypeCommHopfAlgCat.quotient H I)]
    [ConnectedSpace (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient H I))]
    (hI : normalizerHopfIdeal π hπ ≤ I) : centralizerHopfIdeal π ≤ I := by
  let q := CommHopfAlgCat.mkQuotient H.obj I
  have hnorm (g : WithConv ((FiniteTypeCommHopfAlgCat.quotient H I) →ₐ[k] k)) :
      mapDomain q.hom g ∈ normalizerPoints π hπ := by
    rw [← universalNormalizerPoints_base_eq_normalizerPoints π hπ,
      ← quotientPointsSubgroup_normalizerHopfIdeal π hπ]
    apply TauCeti.CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj hI (CommAlgCat.of k k)
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro x hx
    have hx0 : q.hom x = 0 := (CommHopfAlgCat.mkQuotient_eq_zero_iff H.obj I x).mpr hx
    rw [mapDomain_apply_apply, hx0, map_zero]
  have hker := centralizerHopfIdeal_le_ker_of_forall_mapDomain_mem_normalizerPoints
    π hπ q.hom hnorm
  intro x hx
  exact (CommHopfAlgCat.mkQuotient_eq_zero_iff H.obj I x).mp
    (hker (HopfIdeal.mem_toIdeal.mpr hx))

/-- If the scheme normalizer is reduced, its identity component centralizes the entire
diagonalizable subgroup, including any infinitesimal structure in that subgroup. -/
theorem centralizerHopfIdeal_le_identityComponent_normalizerHopfIdeal
    [IsReduced (FiniteTypeCommHopfAlgCat.quotient H (normalizerHopfIdeal π hπ))] :
    centralizerHopfIdeal π ≤ (normalizerHopfIdeal π hπ).identityComponent := by
  let N := normalizerHopfIdeal π hπ
  let _ : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H N) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k _)
  let _ := N.smooth_identityComponent
  let _ : IsReduced (FiniteTypeCommHopfAlgCat.quotient H N.identityComponent) :=
    isReduced_of_smooth k _
  let _ : ConnectedSpace
      (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient H N.identityComponent)) :=
    N.geometricallyConnected_identityComponent.connectedSpace k _
  exact centralizerHopfIdeal_le_of_le_normalizerHopfIdeal π hπ _ N.le_identityComponent

/-- A reduced scheme normalizer and the scheme centralizer of a closed diagonalizable
subgroup have the same tangent Lie algebra. This holds in every characteristic; in
characteristic zero the reducedness hypothesis follows from Cartier's theorem. -/
@[simp]
theorem lieSubalgebra_normalizerHopfIdeal_eq_centralizerHopfIdeal
    [IsReduced (FiniteTypeCommHopfAlgCat.quotient H (normalizerHopfIdeal π hπ))] :
    (normalizerHopfIdeal π hπ).lieSubalgebra (B := k) =
      (centralizerHopfIdeal π).lieSubalgebra (B := k) := by
  have hC := centralizerHopfIdeal_le_identityComponent_normalizerHopfIdeal π hπ
  have hN := normalizerHopfIdeal_le_centralizerHopfIdeal π hπ
  apply le_antisymm
  · rw [← HopfIdeal.lieSubalgebra_identityComponent (normalizerHopfIdeal π hπ)]
    intro d hd
    rw [HopfIdeal.mem_lieSubalgebra_iff] at hd ⊢
    exact fun x hx ↦ hd x (hC hx)
  · intro d hd
    rw [HopfIdeal.mem_lieSubalgebra_iff] at hd ⊢
    exact fun x hx ↦ hd x (hN hx)

end ClosedSubgroup

end BialgHom
