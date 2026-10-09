/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Algebra.HopfAlgebra.TensorShear

/-!
# Finite locally free commutative group schemes are killed by their rank

Let `H` be a commutative and cocommutative Hopf algebra over a commutative ring `R`, so that
`Spec H` is a commutative affine group scheme over `R` whose group of `A`-valued points is the
convolution group `WithConv (H →ₐ[R] A)`. If `H` is finite projective over `R` of constant rank
`n`, that is, `Spec H` is a finite locally free commutative group scheme of rank `n`, then every
point is killed by `n`: `x ^ n = 1` for every commutative `R`-algebra `A` and every
`x : WithConv (H →ₐ[R] A)`. This is Deligne's theorem. It is the input which turns a point of
exact order `n` of an elliptic curve into an `n`-torsion point, and which makes the
factorisation construction of dual isogenies possible.

## Main results

* `TauCeti.AlgHom.convPow_finrank_eq_one`: when `H` is free of finite rank over `R`, every point
  is killed by `Module.finrank R H`.
* `TauCeti.AlgHom.convPow_eq_one_of_rankAtStalk`: when `H` is finite projective over `R` and its
  rank at every prime is `n`, every point is killed by `n`.

## Implementation notes

The free case is the norm argument of Deligne, as presented by Tate and Oort. The convolution
algebra of linear maps `H →ₗ[R] B` plays the role of the coordinate ring of the Cartier dual with
coefficients in `B`. For `B = H` and `B' = H ⊗[R] H`, a basis of `H` over `R` makes the
convolution algebra of `H →ₗ[R] B'` free of rank `n` over that of `H →ₗ[R] B`, so it has a norm.
Write `ι₁` and `ι₂` for the two inclusions `H → H ⊗[R] H`. The shear automorphism
`a ⊗ b ↦ (a ⊗ 1) Δ b` of `H ⊗[R] H` over its left factor preserves norms and sends `ι₂` to
`Δ = ι₁ * ι₂`, where `ι₁` comes from the identity of `H`. Taking norms gives
`N(ι₂) = id ^ n * N(ι₂)`, and `ι₂` is a unit, so `id ^ n = 1`. The universal point `id` then
controls every point. The locally free case follows by checking the resulting identity of
elements of `H` after localizing at every maximal ideal of `R`.

## References

* J. Tate and F. Oort, *Group schemes of prime order*, Ann. Sci. École Norm. Sup. (4) 3 (1970),
  1–21, §1.
* J. Tate, *Finite flat group schemes*, in *Modular Forms and Fermat's Last Theorem*, Springer,
  1997.
-/

public section

open WithConv TensorProduct

namespace TauCeti.AlgHom

variable {R H : Type*} [CommRing R] [CommRing H] [_root_.HopfAlgebra R H]
  [Coalgebra.IsCocomm R H]

section Free

/-- The convolution algebra of linear maps `H → H ⊗[R] H` as an algebra over the convolution
algebra of linear maps `H → H`, through the left tensor factor. -/
private noncomputable abbrev convTensorAlgebra :
    Algebra (WithConv (H →ₗ[R] H)) (WithConv (H →ₗ[R] H ⊗[R] H)) :=
  ((IsScalarTower.toAlgHom R H (H ⊗[R] H)).convCompLeft H).toRingHom.toAlgebra

attribute [local instance] convTensorAlgebra

/-- The structure map of `convTensorAlgebra` is post-composition with the left inclusion. -/
private theorem algebraMap_convTensor (f : WithConv (H →ₗ[R] H)) :
    algebraMap (WithConv (H →ₗ[R] H)) (WithConv (H →ₗ[R] H ⊗[R] H)) f =
      (IsScalarTower.toAlgHom R H (H ⊗[R] H)).convCompLeft H f :=
  rfl

/-- A basis of `H` over `R` gives a basis of the convolution algebra of `H → H ⊗[R] H` over the
convolution algebra of `H → H`, by taking coordinates in the right tensor factor. -/
private noncomputable def convTensorBasis {ι : Type*} [Finite ι] (b : Module.Basis ι R H) :
    Module.Basis ι (WithConv (H →ₗ[R] H)) (WithConv (H →ₗ[R] H ⊗[R] H)) :=
  .ofEquivFun
    { (Algebra.TensorProduct.basis H b).convCoordEquiv R H with
      map_smul' := fun f φ => funext fun i => by
        simpa [Algebra.smul_def, algebraMap_convTensor] using
          (Algebra.TensorProduct.basis H b).convCoordEquiv_convCompLeft_mul f φ i }

/-- Post-composition with the shear automorphism `a ⊗ b ↦ (a ⊗ 1) Δ b` of `H ⊗[R] H`, as an
automorphism of the convolution algebra of `H → H ⊗[R] H` over that of `H → H`. -/
private noncomputable def convTensorShear :
    WithConv (H →ₗ[R] H ⊗[R] H) ≃ₐ[WithConv (H →ₗ[R] H)] WithConv (H →ₗ[R] H ⊗[R] H) where
  toFun := (HopfAlgebra.tensorShearMulRight (R := R) (H := H) :
    H ⊗[R] H →ₐ[R] H ⊗[R] H).convCompLeft H
  invFun := (HopfAlgebra.tensorShearMulRight (R := R) (H := H)).symm.toAlgHom.convCompLeft H
  left_inv φ := by ext; simp
  right_inv φ := by ext; simp
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' f := by
    ext c
    simp [algebraMap_convTensor, Algebra.TensorProduct.algebraMap_apply]

/-- The shear sends the right tensor inclusion to the comultiplication, which is the convolution
product of the two tensor inclusions. -/
private theorem convTensorShear_includeRight :
    convTensorShear (toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H).toLinearMap) =
      algebraMap (WithConv (H →ₗ[R] H)) (WithConv (H →ₗ[R] H ⊗[R] H))
          (toConv _root_.LinearMap.id) *
        toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H).toLinearMap := by
  have hτ : (HopfAlgebra.tensorShearMulRight (R := R) (H := H) :
      H ⊗[R] H →ₐ[R] H ⊗[R] H).toLinearMap ∘ₗ
        (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H).toLinearMap =
      CoalgebraStruct.comul := by
    ext a
    simp [← Algebra.TensorProduct.one_def]
  have hι : (IsScalarTower.toAlgHom R H (H ⊗[R] H)).toLinearMap ∘ₗ _root_.LinearMap.id =
      (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H).toLinearMap := by
    ext a
    simp [Algebra.TensorProduct.algebraMap_apply]
  simp only [convTensorShear, algebraMap_convTensor, AlgEquiv.coe_mk, Equiv.coe_fn_mk,
    _root_.AlgHom.convCompLeft_apply, hτ, hι]
  exact Coalgebra.comul_eq_convMul_includeLeft_includeRight

omit [Coalgebra.IsCocomm R H] in
/-- The right tensor inclusion is a convolution unit, being an algebra-homomorphism point. -/
private theorem isUnit_includeRight :
    IsUnit (toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H).toLinearMap) := by
  let toLinear : WithConv (H →ₐ[R] H ⊗[R] H) →* WithConv (H →ₗ[R] H ⊗[R] H) :=
    { toFun f := toConv f.ofConv.toLinearMap
      map_one' := _root_.AlgHom.toLinearMap_convOne
      map_mul' := _root_.AlgHom.toLinearMap_convMul }
  exact (Group.isUnit (toConv Algebra.TensorProduct.includeRight)).map toLinear

/-- The convolution power of the identity of a free Hopf algebra by its rank is the unit. -/
private theorem convPow_id_eq_one [Module.Free R H] [Module.Finite R H] :
    toConv (_root_.LinearMap.id : H →ₗ[R] H) ^ Module.finrank R H = 1 := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · have : Subsingleton H := Module.subsingleton R H
    exact Subsingleton.elim _ _
  have hnorm := Algebra.norm_eq_of_algEquiv convTensorShear
    (toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H).toLinearMap)
  rw [convTensorShear_includeRight, map_mul,
    Algebra.norm_algebraMap_of_basis (convTensorBasis (Module.Free.chooseBasis R H)),
    ((isUnit_includeRight (R := R) (H := H)).map
      (Algebra.norm (WithConv (H →ₗ[R] H)))).mul_eq_right] at hnorm
  rwa [Module.finrank_eq_card_chooseBasisIndex]

/-- **Deligne's theorem, free case.** Every point of a commutative and cocommutative Hopf algebra
which is free of finite rank `n` over `R` is killed by `n`. -/
theorem convPow_finrank_eq_one [Module.Free R H] [Module.Finite R H] {A : Type*}
    [CommSemiring A] [Algebra R A] (x : WithConv (H →ₐ[R] A)) :
    x ^ Module.finrank R H = 1 := by
  have hid : toConv (_root_.AlgHom.id R H) ^ Module.finrank R H = 1 := by
    apply ofConv_injective
    apply _root_.AlgHom.toLinearMap_injective
    apply toConv_injective
    rw [_root_.AlgHom.toLinearMap_convPow, _root_.AlgHom.toLinearMap_convOne]
    exact convPow_id_eq_one
  have hx : x = mapValue x.ofConv (toConv (_root_.AlgHom.id R H)) := by simp
  rw [hx, ← map_pow, hid, map_one]

end Free

/-- If `H` becomes free after base change to `S`, then every point of `H` with values in an
`S`-algebra is killed by the rank of `S ⊗[R] H` over `S`. -/
private theorem convPow_eq_one_of_baseChange {S : Type*} [CommRing S] [Algebra R S]
    [Module.Free S (S ⊗[R] H)] [Module.Finite S (S ⊗[R] H)] {A : Type*} [CommSemiring A]
    [Algebra S A] [Algebra R A] [IsScalarTower R S A] (x : WithConv (H →ₐ[R] A)) :
    x ^ Module.finrank S (S ⊗[R] H) = 1 := by
  let e := baseChangePointsMulEquiv (k := R) (K := S) (A := H) (R := A)
  rw [← e.symm_apply_apply x, ← map_pow, convPow_finrank_eq_one, map_one]

/-- **Deligne's theorem.** Every point of a commutative and cocommutative Hopf algebra which is
finite projective of constant rank `n` over `R` is killed by `n`. -/
theorem convPow_eq_one_of_rankAtStalk [Module.Finite R H] [Module.Projective R H] {n : ℕ}
    (hn : ∀ p, Module.rankAtStalk (R := R) H p = n) {A : Type*} [CommSemiring A] [Algebra R A]
    (x : WithConv (H →ₐ[R] A)) : x ^ n = 1 := by
  -- It suffices to treat the universal point, the identity of `H`. Its `n`-th power and the
  -- unit are compared as elements of `H` after localizing at each maximal ideal `P`, where `H`
  -- becomes free of rank `n`.
  have hid : toConv (_root_.AlgHom.id R H) ^ n = 1 := by
    apply ofConv_injective
    ext h
    refine Module.eq_of_localization_maximal (fun P _ => Localization.AtPrime P ⊗[R] H)
      (fun P _ => TensorProduct.mk R (Localization.AtPrime P) H 1) _ _ fun P _ => ?_
    let j : H →ₐ[R] Localization.AtPrime P ⊗[R] H := Algebra.TensorProduct.includeRight
    have := Module.free_of_flat_of_isLocalRing (R := Localization.AtPrime P)
      (P := Localization.AtPrime P ⊗[R] H)
    have hP := hn ⟨P, inferInstance⟩
    rw [Module.rankAtStalk_eq_finrank_tensorProduct] at hP
    have hj := convPow_eq_one_of_baseChange (S := Localization.AtPrime P) (toConv j)
    rw [hP] at hj
    have key : mapValue j (toConv (_root_.AlgHom.id R H) ^ n) = 1 := by
      rw [map_pow]
      simpa using hj
    have := congrArg (fun y => y.ofConv h) key
    simp only [mapValue_apply, ofConv_toConv, _root_.AlgHom.comp_apply,
      _root_.AlgHom.convOne_apply, j, Algebra.TensorProduct.includeRight_apply] at this
    simp [this, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]
  have hx : x = mapValue x.ofConv (toConv (_root_.AlgHom.id R H)) := by simp
  rw [hx, ← map_pow, hid, map_one]

end TauCeti.AlgHom
