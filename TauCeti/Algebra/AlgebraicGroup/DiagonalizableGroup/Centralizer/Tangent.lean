/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace
import TauCeti.Algebra.DualNumber.Convolution

/-!
# The Lie algebra of the centralizer of a diagonalizable subgroup

Let `G = Spec H` be an affine group scheme over a commutative ring `R` and `D(X) → G` a closed
diagonalizable subgroup with coordinate map `π : H →ₐc[R] R[X]`. The centralizer `Z_G(D(X))` is
the closed subgroup scheme cut out by `BialgHom.centralizerHopfIdeal π`. This file identifies its
Lie algebra inside the Lie algebra of `G`: it is the subspace fixed by the adjoint action of
`D(X)`, that is, the weight space of the trivial character in the weight decomposition of `Lie G`
under `D(X)`.

Both sides are conditions on a tangent vector `d` at the identity of `G`, viewed as a counit-valued
derivation of `H`. The tangent vector lies in the Lie algebra of the centralizer when it kills the
coefficients of the conjugation defects; evaluating a derivation on the conjugation defect is
differentiating the conjugating variable, and this yields the convolution commutator of `d` with
the universal point of `D(X)`. The adjoint action of the universal point of `D(X)` on `d`, which
differentiates the conjugated variable, is the convolution conjugate `π ⋆ d ⋆ π⁻¹`. Both
conditions therefore say that `d` and `π` commute in the convolution algebra. The convolution
commutator is computed on dual-number points, as the infinitesimal coefficient of the conjugate of
`π` by the tangent point of `d`.

The hypotheses are those needed to speak of the adjoint representation on the single module
`Lie G = Module.Dual R (Bialgebra.CotangentSpace R H)`: the augmentation cotangent space of `H`
is finite projective. No smoothness, reducedness or field hypothesis enters. The base ring, the
Hopf algebra and the character group are taken in a common universe because the universal-point
criterion `Derivation.mem_adjointWeightSpace_iff_universalPointAction` is stated that way.

## Main declarations

* `BialgHom.cotangentLinearEquiv_mem_lieSubalgebra_centralizerHopfIdeal_iff`: **a tangent vector
  lies in the Lie algebra of the centralizer of `D(X)` exactly when it has trivial weight under
  `D(X)`.**
* `BialgHom.lieSubalgebra_centralizerHopfIdeal_toSubmodule`: the Lie algebra of the centralizer
  is the trivial weight space, transported along cotangent duality.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a (the Lie algebra of a closed subgroup) and §13
  (tori acting on schemes).
* SGA 3, Exposé XI, Corollaire 5.3.
-/

public section

open TensorProduct TrivSqZeroExt WithConv

namespace BialgHom

open TauCeti

universe u

variable {R H X : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]

/-- Conjugating a point by the dual-number tangent point of a tangent vector: the infinitesimal
coefficient of the conjugate is the convolution commutator of the tangent vector with the point.
This mirrors `Derivation.snd_conjugate_tangentPoint`, which conjugates the tangent point by the
point instead. -/
private theorem snd_tangentPoint_conjugate {B : Type*} [CommRing B] [Algebra R B]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B))
    (g : WithConv (H →ₐ[R] Bialgebra.CounitAlgebra R H B)) (a : H) :
    snd (((derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val *
        AlgHom.mapValue (H := H) (inlAlgHom R (Bialgebra.CounitAlgebra R H B)
          (Bialgebra.CounitAlgebra R H B)) g *
        (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val⁻¹).ofConv a) =
      (toConv (↑d : H →ₗ[R] Bialgebra.CounitAlgebra R H B) * toConv g.ofConv.toLinearMap -
        toConv g.ofConv.toLinearMap *
          toConv (↑d : H →ₗ[R] Bialgebra.CounitAlgebra R H B)).ofConv a := by
  let q := AlgHom.mapValue (H := H) (inlAlgHom R (Bialgebra.CounitAlgebra R H B)
    (Bialgebra.CounitAlgebra R H B)) g
  let p := (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val
  let F := (fstHom R (Bialgebra.CounitAlgebra R H B) (Bialgebra.CounitAlgebra R H B)).toLinearMap
  let S := (sndHom (Bialgebra.CounitAlgebra R H B)
    (Bialgebra.CounitAlgebra R H B)).restrictScalars R
  let D := toConv (↑d : H →ₗ[R] Bialgebra.CounitAlgebra R H B)
  let G := toConv g.ofConv.toLinearMap
  have hqF : F ∘ₗ q.ofConv.toLinearMap = g.ofConv.toLinearMap := by
    ext x
    simp [F, q, AlgHom.mapValue_apply]
  have hqS : S ∘ₗ q.ofConv.toLinearMap = 0 := by
    ext x
    simp [S, q, AlgHom.mapValue_apply]
  have hpF : F ∘ₗ p.ofConv.toLinearMap = (1 : WithConv (H →ₗ[R] _)).ofConv := by
    ext x
    exact fst_apply_of_mem_tangentKer
      (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).2 x
  have hpS : S ∘ₗ p.ofConv.toLinearMap = D.ofConv := by
    ext x
    exact derivationMulEquivTangentKer_apply_snd (Multiplicative.ofAdd d) x
  have hpinv : p⁻¹ = (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd (-d))).val := by
    rw [ofAdd_neg, map_inv, Subgroup.coe_inv]
  have hpinvF : F ∘ₗ (p⁻¹).ofConv.toLinearMap = (1 : WithConv (H →ₗ[R] _)).ofConv := by
    rw [hpinv]
    ext x
    exact fst_apply_of_mem_tangentKer
      (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd (-d))).2 x
  have hpinvS : S ∘ₗ (p⁻¹).ofConv.toLinearMap = -D.ofConv := by
    rw [hpinv]
    ext x
    exact derivationMulEquivTangentKer_apply_snd (Multiplicative.ofAdd (-d)) x
  -- Negation passes through convolution; `mul_neg` does not apply because the convolution ring
  -- and the pointwise additive group of `WithConv` expose different negation instances.
  have hneg : G * -D = -(G * D) := by
    apply ofConv_injective
    ext c
    simp [(Coalgebra.Repr.arbitrary R c).convMul_apply]
  have hpqF : F ∘ₗ (p * q).ofConv.toLinearMap = g.ofConv.toLinearMap := by
    rw [← ofConv_toConv ((p * q).ofConv.toLinearMap), AlgHom.toLinearMap_convMul]
    dsimp only [F]
    rw [LinearMap.algHom_comp_convMul_distrib]
    rw [hpF, hqF]
    simp only [toConv_ofConv, one_mul, ofConv_toConv]
  have hpqS : S ∘ₗ (p * q).ofConv.toLinearMap = (D * G).ofConv := by
    rw [← ofConv_toConv ((p * q).ofConv.toLinearMap), AlgHom.toLinearMap_convMul]
    dsimp only [S]
    rw [WithConv.snd_comp_convMul]
    rw [hpF, hqS, hpS, hqF]
    simp only [toConv_ofConv, toConv_zero, mul_zero, zero_add]
    rfl
  have hc : S ∘ₗ (p * q * p⁻¹).ofConv.toLinearMap = (D * G - G * D).ofConv := by
    rw [← ofConv_toConv ((p * q * p⁻¹).ofConv.toLinearMap), AlgHom.toLinearMap_convMul]
    dsimp only [S]
    rw [WithConv.snd_comp_convMul]
    rw [hpqF, hpinvS, hpqS, hpinvF]
    simp only [toConv_ofConv, toConv_neg, mul_one]
    rw [hneg, sub_eq_add_neg, add_comm]
  have ha := LinearMap.congr_fun hc a
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, sndHom_apply,
    AlgHom.toLinearMap_apply, S, q, p, D, G] using ha

variable (π : H →ₐc[R] MonoidAlgebra R X)

/-- Tensoring a linear map with the identity after applying `π` to the second factor is tensoring
it with `π`. -/
private theorem map_id_algebraTensorProduct_map_id {A : Type*} [AddCommMonoid A] [Module R A]
    (f : H →ₗ[R] A) (z : H ⊗[R] H) :
    TensorProduct.map f LinearMap.id (Algebra.TensorProduct.map (AlgHom.id R H) π.toAlgHom z) =
      TensorProduct.map f π.toAlgHom.toLinearMap z := by
  induction z with
  | tmul a b => simp
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- Evaluating a tangent vector of `G` on the conjugation of a coordinate, in the conjugating
variable, with the universal point of `D(X)` in the conjugated variable, computes the convolution
commutator of the tangent vector with that point. -/
private theorem lid_map_conjugationAlgHom (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (h : H) :
    TensorProduct.lid R (MonoidAlgebra R X)
        (TensorProduct.map ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ
            (d : H →ₗ[R] Bialgebra.CounitAlgebra R H R)) π.toAlgHom.toLinearMap
          (HopfAlgebra.conjugationAlgHom (R := R) (H := H) h)) =
      Bialgebra.CounitAlgebra.algEquivSelf R H (CommAlgCat.of R (MonoidAlgebra R X))
        ((toConv (↑(Derivation.mapValue (Algebra.ofId R (MonoidAlgebra R X)) d) :
              H →ₗ[R] Bialgebra.CounitAlgebra R H (CommAlgCat.of R (MonoidAlgebra R X))) *
            toConv (Derivation.pointInCounitAlgebra (CommAlgCat.of R (MonoidAlgebra R X))
              (toConv π.toAlgHom)).ofConv.toLinearMap -
          toConv (Derivation.pointInCounitAlgebra (CommAlgCat.of R (MonoidAlgebra R X))
              (toConv π.toAlgHom)).ofConv.toLinearMap *
            toConv (↑(Derivation.mapValue (Algebra.ofId R (MonoidAlgebra R X)) d) :
              H →ₗ[R] Bialgebra.CounitAlgebra R H (CommAlgCat.of R (MonoidAlgebra R X)))).ofConv
          h) := by
  let A := CommAlgCat.of R (MonoidAlgebra R X)
  let d' := Derivation.mapValue (Algebra.ofId R A) d
  let p := Derivation.pointInCounitAlgebra A (toConv π.toAlgHom)
  let T := (derivationMulEquivTangentKer R H A (Multiplicative.ofAdd d')).val
  let Q := AlgHom.mapValue (H := H)
    (inlAlgHom R (Bialgebra.CounitAlgebra R H A) (Bialgebra.CounitAlgebra R H A)) p
  have hconj := AlgHom.congr_fun
    (HopfAlgebra.productMap_comp_conjugationAlgHom (R := R) (H := H) T Q) h
  rw [AlgHom.comp_apply] at hconj
  rw [← snd_tangentPoint_conjugate d' p h, ← hconj]
  have hmaps : (TensorProduct.lid R (MonoidAlgebra R X)).toLinearMap ∘ₗ
      TensorProduct.map ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ
        (d : H →ₗ[R] Bialgebra.CounitAlgebra R H R)) π.toAlgHom.toLinearMap =
      (Bialgebra.CounitAlgebra.algEquivSelf R H A).toLinearMap ∘ₗ
        (sndHom (Bialgebra.CounitAlgebra R H A) (Bialgebra.CounitAlgebra R H A)).restrictScalars R
          ∘ₗ (Algebra.TensorProduct.productMap T.ofConv Q.ofConv).toLinearMap := by
    -- The universal point and the tangent vector are rewritten through the well-typed
    -- identifications of the counit algebra with its coefficient ring.
    have hpdef : p = AlgHom.mapValue (H := H)
        (Bialgebra.CounitAlgebra.algEquivSelf R H A).symm.toAlgHom (toConv π.toAlgHom) := by
      apply ofConv_injective
      ext h
      rw [Derivation.pointInCounitAlgebra_apply, AlgHom.mapValue_apply, ofConv_toConv,
        ofConv_toConv, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
      exact (Bialgebra.CounitAlgebra.algEquivSelf_symm_apply R H A _).symm
    apply TensorProduct.ext'
    intro a b
    have hQ : Q.ofConv b = inl (p.ofConv b) := by
      simp only [Q, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, inlAlgHom_apply]
    have hT : snd (T.ofConv a) = d' a :=
      derivationMulEquivTangentKer_apply_snd (Multiplicative.ofAdd d') a
    have hd' : d' a = Bialgebra.CounitAlgebra.mapAlgHom (A := H) (Algebra.ofId R A) (d a) := by
      have h := LinearMap.congr_fun (Derivation.coe_mapValue_linearMap (Algebra.ofId R A) d) a
      simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Derivation.coeFn_coe] using h
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
    rw [LinearMap.restrictScalars_apply, sndHom_apply,
      AlgHom.toLinearMap_apply, Algebra.TensorProduct.productMap_apply_tmul, snd_mul,
      op_smul_eq_mul, hQ, fst_inl, snd_inl, smul_zero, zero_add, hT, hd', hpdef,
      AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, TensorProduct.map_tmul,
      LinearEquiv.coe_coe, TensorProduct.lid_tmul, map_mul]
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe, AlgHom.toLinearMap_apply,
      AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply, Bialgebra.CounitAlgebra.mapAlgHom_apply,
      Bialgebra.CounitAlgebra.algEquivSelf_map, Algebra.ofId_apply, Algebra.smul_def,
      BialgHom.coe_toAlgHom]
    rfl
  exact LinearMap.congr_fun hmaps _

variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

/-- **The Lie algebra of the centralizer of a diagonalizable subgroup is the fixed part of the
adjoint action of that subgroup.** A tangent vector of `G` at the identity, viewed as a
counit-valued derivation through `Derivation.cotangentLinearEquiv`, lies in the Lie algebra of
`Z_G(D(X))` exactly when it has trivial weight under `D(X)`. -/
theorem cotangentLinearEquiv_mem_lieSubalgebra_centralizerHopfIdeal_iff
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    Derivation.cotangentLinearEquiv (B := R) x ∈
        (centralizerHopfIdeal π).lieSubalgebra (B := R) ↔
      x ∈ Derivation.adjointWeightSpace π 1 := by
  -- Weight-space membership becomes invariance under the adjoint action of the universal point,
  -- and Lie-algebra membership becomes vanishing on the generators of the centralizer ideal.
  rw [Derivation.mem_adjointWeightSpace_iff_universalPointAction,
    ← (Derivation.tangentScalarExtensionEquiv (R := R) (A := H)
      (B := MonoidAlgebra R X)).injective.eq_iff,
    Derivation.tangentScalarExtensionEquiv_adjointAction (CommAlgCat.of R (MonoidAlgebra R X))
      (toConv π.toAlgHom),
    Derivation.tangentScalarExtensionEquiv_tmul, one_smul,
    Derivation.tangentScalarExtensionEquiv_tmul, ← MonoidAlgebra.one_def, one_smul,
    HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _ (centralizerHopfIdeal_toIdeal π)]
  simp only [Set.forall_mem_range, Prod.forall]
  set d := Derivation.cotangentLinearEquiv (B := R) x
  set A := CommAlgCat.of R (MonoidAlgebra R X)
  set d' := Derivation.mapValue (Algebra.ofId R A) d
  set p := Derivation.pointInCounitAlgebra A (toConv π.toAlgHom)
  set D : WithConv (H →ₗ[R] Bialgebra.CounitAlgebra R H A) :=
    toConv (↑d' : H →ₗ[R] Bialgebra.CounitAlgebra R H A)
  set P : WithConv (H →ₗ[R] Bialgebra.CounitAlgebra R H A) := toConv p.ofConv.toLinearMap
  set P' : WithConv (H →ₗ[R] Bialgebra.CounitAlgebra R H A) :=
    toConv (p⁻¹).ofConv.toLinearMap
  -- Killing the coefficients of the conjugation defect is vanishing of the commutator of `d`
  -- with the universal point of `D(X)`.
  have hgen (h : H) :
      (∀ χ, d (centralizerCoefficient π h χ) = 0) ↔ (D * P - P * D).ofConv h = 0 := by
    have hcoeff : (∀ χ, d (centralizerCoefficient π h χ) = 0) ↔
        TensorProduct.map ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ
            (d : H →ₗ[R] Bialgebra.CounitAlgebra R H R)) LinearMap.id
          (centralizerDefect π h) = 0 := by
      rw [map_centralizerDefect_eq_zero_iff]
      simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe,
        EmbeddingLike.map_eq_zero_iff]
    rw [hcoeff, ← (TensorProduct.lid R (MonoidAlgebra R X)).map_eq_zero_iff,
      centralizerDefect_def, map_sub, map_sub, map_id_algebraTensorProduct_map_id,
      lid_map_conjugationAlgHom, TensorProduct.map_tmul]
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe, Derivation.map_one_eq_zero, map_zero,
      TensorProduct.zero_tmul, sub_zero, EmbeddingLike.map_eq_zero_iff, D, P, d', p, A]
  rw [forall_congr' hgen]
  have hPP' : P * P' = 1 := by
    rw [← AlgHom.toLinearMap_convMul, mul_inv_cancel, AlgHom.toLinearMap_convOne]
  have hP'P : P' * P = 1 := by
    rw [← AlgHom.toLinearMap_convMul, inv_mul_cancel, AlgHom.toLinearMap_convOne]
  -- The adjoint action of the universal point is convolution conjugation.
  have had : Derivation.adDerivation A p d' = d' ↔ P * D * P' = D := by
    constructor
    · intro he
      rw [← Derivation.toConv_coe_adDerivation, he]
    · intro he
      ext a
      rw [Derivation.adDerivation_apply]
      exact DFunLike.congr_fun (congrArg ofConv he) a
  rw [had]
  constructor
  · intro hcomm
    have hDP : D * P = P * D := by
      rw [← sub_eq_zero]
      apply ofConv_injective
      rw [ofConv_zero]
      exact LinearMap.ext hcomm
    rw [← hDP, mul_assoc, hPP', mul_one]
  · intro he h
    have hPD : P * D = D * P := by
      calc P * D = P * D * P' * P := by rw [mul_assoc (P * D), hP'P, mul_one]
        _ = D * P := by rw [he]
    rw [hPD, sub_self, ofConv_zero, LinearMap.zero_apply]

/-- The Lie algebra of the centralizer of a diagonalizable subgroup is the trivial weight space of
the adjoint action of that subgroup, transported along cotangent duality. -/
theorem lieSubalgebra_centralizerHopfIdeal_toSubmodule :
    ((centralizerHopfIdeal π).lieSubalgebra (B := R)).toSubmodule =
      (Derivation.adjointWeightSpace π 1).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R) :
          Module.Dual R (Bialgebra.CotangentSpace R H) →ₗ[R]
            Derivation R H (Bialgebra.CounitAlgebra R H R)) := by
  ext d
  rw [LieSubalgebra.mem_toSubmodule, Submodule.mem_map_equiv,
    ← cotangentLinearEquiv_mem_lieSubalgebra_centralizerHopfIdeal_iff,
    LinearEquiv.apply_symm_apply]

end BialgHom
