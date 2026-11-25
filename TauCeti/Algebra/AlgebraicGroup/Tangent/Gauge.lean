/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.CounitPoints
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Naturality
public import TauCeti.RingTheory.Derivation.Convolution

/-!
# Logarithmic derivatives of points and the gauge action

Let `H` be a commutative Hopf algebra over `R`, the coordinate ring of an affine group `G`, and
let `D` be an `R`-derivation of a commutative `R`-algebra `B`. A point `g ∈ G(B)`, an algebra map
`H → B`, can be differentiated along `D`: the composite `D ∘ g` is a derivation of `H` at the
point `g`. Translating it back to the identity by the convolution inverse gives the **right
logarithmic derivative**

`dlog g = (D ∘ g) ⋆ g⁻¹`,

a derivation of `H` at the counit, that is, a tangent vector in `Lie(G) (B)`
(`Derivation.pointRightLogDeriv`). For `G = GLₙ` this is the matrix `(Dg) g⁻¹`
(`TauCeti.GeneralLinear.tangentMatrix_pointRightLogDeriv`), and for `G = 𝔾ₘ` it is `Du / u`
(`TauCeti.MultiplicativeGroup.tangentLinearEquiv_pointRightLogDeriv`).

The logarithmic derivative is a crossed homomorphism for the adjoint action,
`dlog (g h) = dlog g + Ad g (dlog h)`, and it vanishes exactly on the horizontal points, those
with `D ∘ g = 0`. Twisting the adjoint action by it gives the **gauge action**

`gauge g A = Ad g A - dlog g`

of `G(B)` on tangent vectors `A`, which read as the connections `D + A` on the trivial
`G`-torsor over `B` (`Derivation.pointGauge`). It is a left action,
`gauge (g h) A = gauge g (gauge h A)`, and `g` carries `A` to `A'` exactly when `g` solves the
linear differential equation `D ∘ g = g ⋆ A - A' ⋆ g`. Both constructions are natural in `B`
along algebra maps intertwining the derivations.

For `B = R⸨t⸩` and `D = d/dt`, this is the gauge action of the formal loop group `G(R⸨t⸩)` on
connections `d + A dt` on the punctured formal disc, over every coefficient algebra `R`,
nonreduced ones included.

## Main definitions

* `Derivation.pointRightLogDeriv D g`: the right logarithmic derivative `(D ∘ g) ⋆ g⁻¹`.
* `Derivation.pointGauge D g A`: the gauge action `Ad g A - dlog g`.

## Main results

* `Derivation.pointRightLogDeriv_mul`: the crossed-homomorphism law.
* `Derivation.pointRightLogDeriv_eq_zero_iff`: `dlog g = 0` exactly when `D ∘ g = 0`.
* `Derivation.mapValue_pointRightLogDeriv`, `Derivation.mapValue_pointGauge`: naturality in
  the coefficient algebra.
* `Derivation.pointGauge_one`, `Derivation.pointGauge_mul`: the gauge action is a left action.
* `Derivation.pointGauge_eq_iff`: gauge transformations are the solutions of a linear
  differential equation.
* `Derivation.pointGauge_of_isCocomm`: for a commutative group the gauge action is translation
  by `-dlog g`.

## References

* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge Stud. Adv. Math. 103 (2007),
  §1.2.4, (1.2-4), and §1.2.6, (1.2-7).
* E. Frenkel and D. Gaitsgory, *Local geometric Langlands correspondence and affine Kac–Moody
  algebras*, §1.1, (1.2).
-/

public section

open TauCeti WithConv

namespace Derivation

section CommSemiring

variable {R H B : Type*} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
  [CommSemiring B] [Algebra R B] (D : Derivation R B B)

/-- The derivative `D ∘ g` of a point is a derivation at `g`: composed with the multiplication of
`H` it is `g ⊠ (D ∘ g) + (D ∘ g) ⊠ g`. -/
private lemma toConv_comp_comp_mul' (g : WithConv (H →ₐ[R] B)) :
    toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap ∘ₗ LinearMap.mul' R H) =
      mulTensor (toConv g.ofConv.toLinearMap)
          (toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap)) +
        mulTensor (toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap))
          (toConv g.ofConv.toLinearMap) := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp [D.leibniz, mul_comm]

/-- The convolution `(D ∘ g) ⋆ g⁻¹` satisfies the Leibniz rule at the counit:
composed with the multiplication of `H` it is `1 ⊠ δ + δ ⊠ 1`. -/
private lemma toConv_dlog_comp_mul' (g : WithConv (H →ₐ[R] B)) :
    toConv ((toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap) *
        toConv (g⁻¹).ofConv.toLinearMap).ofConv ∘ₗ LinearMap.mul' R H) =
      mulTensor 1 (toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap) *
          toConv (g⁻¹).ofConv.toLinearMap) +
        mulTensor (toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap) *
          toConv (g⁻¹).ofConv.toLinearMap) 1 := by
  have h := LinearMap.convMul_comp_coalgHom_distrib
    (toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap)) (toConv ((g⁻¹).ofConv.toLinearMap))
    (_root_.Bialgebra.mulCoalgHom R H)
  -- The `toLinearMap` field of `mulCoalgHom` is definitionally `mul'`; the library
  -- states this only for the coercion, whose pattern does not match the field
  -- projection, so the identification is by `rfl`.
  rw [show (_root_.Bialgebra.mulCoalgHom R H).toLinearMap = LinearMap.mul' R H from rfl] at h
  rw [h, toConv_ofConv, ofConv_toConv, LinearMap.comp_assoc, toConv_comp_comp_mul' D g,
    ofConv_toConv, AlgHom.toConv_toLinearMap_comp_mul' (g⁻¹).ofConv, add_mul,
    WithConv.mulTensor_convMul, WithConv.mulTensor_convMul, algHom_toConv_mul_toConv_inv]

/-- **The right logarithmic derivative of a point** `g ∈ G(B)` along a derivation `D` of `B`:
the tangent vector `dlog g = (D ∘ g) ⋆ g⁻¹` at the identity, obtained by translating the
derivative `D ∘ g` of `g` back to the identity by the convolution inverse of `g`. -/
noncomputable def pointRightLogDeriv (g : WithConv (H →ₐ[R] B)) :
    Derivation R H (Bialgebra.CounitAlgebra R H B) where
  toLinearMap := (Bialgebra.CounitAlgebra.algEquivSelf R H B).symm.toLinearMap ∘ₗ
    (toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap) *
      toConv (g⁻¹).ofConv.toLinearMap).ofConv
  map_one_eq_zero' := by
    -- Both factors evaluate at `1` factorwise since `comul 1 = 1 ⊗ 1`, and `D 1 = 0`.
    rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, EmbeddingLike.map_eq_zero_iff]
    simp [LinearMap.convMul_apply, Algebra.TensorProduct.one_def]
  leibniz' a b := by
    have h := congrArg (fun F => F.ofConv (a ⊗ₜ[R] b)) (toConv_dlog_comp_mul' D g)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mul'_apply,
      ofConv_add, LinearMap.add_apply, WithConv.mulTensor_apply_tmul,
      LinearMap.convOne_apply] at h
    apply (Bialgebra.CounitAlgebra.algEquivSelf R H B).injective
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply, map_add,
      Bialgebra.CounitAlgebra.algEquivSelf_smul, AlgEquiv.apply_symm_apply, h]
    ring

/-- The right logarithmic derivative is the convolution `(D ∘ g) ⋆ g⁻¹`, transported into the
counit algebra. -/
theorem pointRightLogDeriv_apply (g : WithConv (H →ₐ[R] B)) (a : H) :
    D.pointRightLogDeriv g a = (Bialgebra.CounitAlgebra.algEquivSelf R H B).symm
      ((toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap) *
        toConv (g⁻¹).ofConv.toLinearMap).ofConv a) :=
  (rfl)

/-- The right logarithmic derivative, valuewise in the coefficient algebra. -/
theorem algEquivSelf_pointRightLogDeriv_apply (g : WithConv (H →ₐ[R] B)) (a : H) :
    Bialgebra.CounitAlgebra.algEquivSelf R H B (D.pointRightLogDeriv g a) =
      (toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap) *
        toConv (g⁻¹).ofConv.toLinearMap).ofConv a := by
  rw [pointRightLogDeriv_apply, AlgEquiv.apply_symm_apply]

/-- The right logarithmic derivative, read in the coefficient algebra, is the convolution
`(D ∘ g) ⋆ g⁻¹`. -/
theorem toConv_algEquivSelf_comp_pointRightLogDeriv (g : WithConv (H →ₐ[R] B)) :
    toConv ((Bialgebra.CounitAlgebra.algEquivSelf R H B).toLinearMap ∘ₗ
        ↑(D.pointRightLogDeriv g)) =
      toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap) * toConv (g⁻¹).ofConv.toLinearMap := by
  refine ofConv_injective (LinearMap.ext fun a => ?_)
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe,
    algEquivSelf_pointRightLogDeriv_apply]

/-- Two tangent vectors agree exactly when they agree after identifying the counit algebra with
the coefficient algebra. -/
private lemma toConv_algEquivSelf_comp_inj
    {d d' : Derivation R H (Bialgebra.CounitAlgebra R H B)} :
    toConv ((Bialgebra.CounitAlgebra.algEquivSelf R H B).toLinearMap ∘ₗ
        (d : H →ₗ[R] Bialgebra.CounitAlgebra R H B)) =
      toConv ((Bialgebra.CounitAlgebra.algEquivSelf R H B).toLinearMap ∘ₗ
        (d' : H →ₗ[R] Bialgebra.CounitAlgebra R H B)) ↔ d = d' :=
  ⟨fun h => Derivation.ext fun a => (Bialgebra.CounitAlgebra.algEquivSelf R H B).injective
    (LinearMap.congr_fun (congrArg ofConv h) a), fun h => h ▸ rfl⟩

/-- The adjoint action of a point `g ∈ G(B)`, read in the coefficient algebra, is the
convolution conjugation `g ⋆ d ⋆ g⁻¹`. -/
theorem toConv_algEquivSelf_comp_adDerivation (g : WithConv (H →ₐ[R] B))
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    toConv ((Bialgebra.CounitAlgebra.algEquivSelf R H B).toLinearMap ∘ₗ
        ↑(adDerivation B ((Bialgebra.CounitAlgebra.pointsMulEquiv R H B).symm g) d)) =
      toConv g.ofConv.toLinearMap *
        toConv ((Bialgebra.CounitAlgebra.algEquivSelf R H B).toLinearMap ∘ₗ ↑d) *
          toConv (g⁻¹).ofConv.toLinearMap := by
  -- The distributivity lemma is stated for the linear map of an `AlgHom`, so first
  -- rewrite the linear map of the `AlgEquiv` as that of its underlying `AlgHom`.
  rw [coe_adDerivation_linearMap, ← map_inv, ← AlgEquiv.toLinearEquiv_toLinearMap,
    ← AlgEquiv.toAlgHom_toLinearMap, LinearMap.algHom_comp_convMul_distrib, ofConv_toConv,
    LinearMap.algHom_comp_convMul_distrib, ofConv_toConv, toConv_ofConv]
  simp only [AlgEquiv.toAlgHom_toLinearMap, WithConv.algEquivSelf_comp_pointsMulEquiv_symm]

/-- The identity point has zero logarithmic derivative. -/
@[simp]
theorem pointRightLogDeriv_one : D.pointRightLogDeriv (1 : WithConv (H →ₐ[R] B)) = 0 := by
  have h : toConv ((D : B →ₗ[R] B) ∘ₗ (1 : WithConv (H →ₐ[R] B)).ofConv.toLinearMap) = 0 := by
    refine ofConv_injective (LinearMap.ext fun a => ?_)
    simp [AlgHom.convOne_apply]
  apply toConv_algEquivSelf_comp_inj.mp
  rw [toConv_algEquivSelf_comp_pointRightLogDeriv, h, zero_mul]
  simp

/-- **The logarithmic derivative is a crossed homomorphism** for the adjoint action:
`dlog (g h) = dlog g + Ad g (dlog h)`. -/
theorem pointRightLogDeriv_mul (g h : WithConv (H →ₐ[R] B)) :
    D.pointRightLogDeriv (g * h) =
      D.pointRightLogDeriv g +
        adDerivation B ((Bialgebra.CounitAlgebra.pointsMulEquiv R H B).symm g)
          (D.pointRightLogDeriv h) := by
  apply toConv_algEquivSelf_comp_inj.mp
  have hgh : (g * h).ofConv.toLinearMap =
      (toConv g.ofConv.toLinearMap * toConv h.ofConv.toLinearMap).ofConv := by
    rw [← AlgHom.toLinearMap_convMul, ofConv_toConv]
  rw [Derivation.coe_add_linearMap, LinearMap.comp_add, toConv_add,
    toConv_algEquivSelf_comp_adDerivation, toConv_algEquivSelf_comp_pointRightLogDeriv,
    toConv_algEquivSelf_comp_pointRightLogDeriv, toConv_algEquivSelf_comp_pointRightLogDeriv,
    hgh, Derivation.toConv_comp_convMul, toConv_ofConv, toConv_ofConv, mul_inv_rev,
    AlgHom.toLinearMap_convMul]
  set tg := toConv g.ofConv.toLinearMap
  set th := toConv h.ofConv.toLinearMap
  calc (toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap) * th +
          tg * toConv ((D : B →ₗ[R] B) ∘ₗ h.ofConv.toLinearMap)) *
        (toConv (h⁻¹).ofConv.toLinearMap * toConv (g⁻¹).ofConv.toLinearMap)
      = toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap) *
            (th * toConv (h⁻¹).ofConv.toLinearMap) * toConv (g⁻¹).ofConv.toLinearMap +
          tg * (toConv ((D : B →ₗ[R] B) ∘ₗ h.ofConv.toLinearMap) *
            toConv (h⁻¹).ofConv.toLinearMap) * toConv (g⁻¹).ofConv.toLinearMap := by
        simp only [add_mul, mul_assoc]
    _ = _ := by rw [algHom_toConv_mul_toConv_inv, mul_one]

/-- **Horizontal points**: the logarithmic derivative of `g` vanishes exactly when `g` is
killed by `D`, that is, when every coordinate of `g` is a constant for `D`. -/
theorem pointRightLogDeriv_eq_zero_iff (g : WithConv (H →ₐ[R] B)) :
    D.pointRightLogDeriv g = 0 ↔ (D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap = 0 := by
  constructor
  · intro h0
    have h := toConv_algEquivSelf_comp_pointRightLogDeriv D g
    rw [h0, Derivation.coe_zero_linearMap, LinearMap.comp_zero, toConv_zero] at h
    apply toConv_injective
    calc toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap)
        = toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap) * toConv (g⁻¹).ofConv.toLinearMap *
            toConv g.ofConv.toLinearMap := by
          rw [mul_assoc, algHom_toConv_inv_mul_toConv, mul_one]
      _ = 0 := by rw [← h, zero_mul]
  · intro h0
    apply toConv_algEquivSelf_comp_inj.mp
    rw [toConv_algEquivSelf_comp_pointRightLogDeriv, h0, toConv_zero, zero_mul,
      Derivation.coe_zero_linearMap, LinearMap.comp_zero, toConv_zero]

section Naturality

variable {C : Type*} [CommSemiring C] [Algebra R C]

/-- The convolution `(D ∘ g) ⋆ g⁻¹` is natural in the coefficient algebra, along an algebra map
`φ : B → C` intertwining the derivations `D` of `B` and `D'` of `C`. -/
private lemma toConv_comp_convMul_inv (φ : B →ₐ[R] C) (D' : Derivation R C C)
    (hφ : ∀ b, D' (φ b) = φ (D b)) (g : WithConv (H →ₐ[R] B)) :
    toConv (φ.toLinearMap ∘ₗ (toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap) *
        toConv (g⁻¹).ofConv.toLinearMap).ofConv) =
      toConv ((D' : C →ₗ[R] C) ∘ₗ (AlgHom.mapValue φ g).ofConv.toLinearMap) *
        toConv ((AlgHom.mapValue φ g)⁻¹).ofConv.toLinearMap := by
  rw [LinearMap.algHom_comp_convMul_distrib, toConv_ofConv, ← map_inv]
  exact congrArg₂ (· * ·) (congrArg toConv (LinearMap.ext fun x => by simp [hφ]))
    (congrArg toConv (LinearMap.ext fun x => by simp))

/-- **Naturality of the logarithmic derivative** in the coefficient algebra: along an algebra
map `φ : B → C` intertwining the derivations `D` of `B` and `D'` of `C`, the logarithmic
derivative of the image of `g` is the image of the logarithmic derivative of `g`. -/
theorem mapValue_pointRightLogDeriv (φ : B →ₐ[R] C) (D' : Derivation R C C)
    (hφ : ∀ b, D' (φ b) = φ (D b)) (g : WithConv (H →ₐ[R] B)) :
    mapValue φ (D.pointRightLogDeriv g) = D'.pointRightLogDeriv (AlgHom.mapValue φ g) := by
  ext a
  have h := LinearMap.congr_fun (congrArg ofConv (toConv_comp_convMul_inv D φ D' hφ g)) a
  rw [ofConv_toConv, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H C).injective
  rw [algEquivSelf_pointRightLogDeriv_apply, mapValue_apply,
    Bialgebra.CounitAlgebra.algEquivSelf_map, algEquivSelf_pointRightLogDeriv_apply, h]

end Naturality

end CommSemiring

section CommRing

variable {R H B : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [CommRing B] [Algebra R B] (D : Derivation R B B)

/-- The logarithmic derivative of an inverse: `dlog g⁻¹ = -Ad g⁻¹ (dlog g)`. -/
theorem pointRightLogDeriv_inv (g : WithConv (H →ₐ[R] B)) :
    D.pointRightLogDeriv g⁻¹ =
      -adDerivation B ((Bialgebra.CounitAlgebra.pointsMulEquiv R H B).symm g⁻¹)
        (D.pointRightLogDeriv g) := by
  have h := D.pointRightLogDeriv_mul g⁻¹ g
  rw [inv_mul_cancel, pointRightLogDeriv_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- **The gauge action** of a point `g ∈ G(B)` on a tangent vector `A`, read as the connection
`D + A` on the trivial `G`-torsor over `B`: `gauge g A = Ad g A - dlog g`. -/
noncomputable def pointGauge (g : WithConv (H →ₐ[R] B))
    (A : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    Derivation R H (Bialgebra.CounitAlgebra R H B) :=
  adDerivation B ((Bialgebra.CounitAlgebra.pointsMulEquiv R H B).symm g) A -
    D.pointRightLogDeriv g

theorem pointGauge_def (g : WithConv (H →ₐ[R] B))
    (A : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    D.pointGauge g A =
      adDerivation B ((Bialgebra.CounitAlgebra.pointsMulEquiv R H B).symm g) A -
        D.pointRightLogDeriv g :=
  (rfl)

/-- The gauge transform of the trivial connection `D` by `g` is `D - dlog g`. -/
@[simp]
theorem pointGauge_zero (g : WithConv (H →ₐ[R] B)) :
    D.pointGauge g 0 = -D.pointRightLogDeriv g := by
  rw [pointGauge_def, ← adRepresentation_apply, map_zero, zero_sub]

/-- For a cocommutative Hopf algebra the adjoint action is trivial, so the gauge action is the
translation `A ↦ A - dlog g`. -/
theorem pointGauge_of_isCocomm [_root_.Coalgebra.IsCocomm R H] (g : WithConv (H →ₐ[R] B))
    (A : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    D.pointGauge g A = A - D.pointRightLogDeriv g := by
  rw [pointGauge_def, adDerivation_eq_self_of_isCocomm]

/-- The identity point acts trivially by gauge transformations. -/
@[simp]
theorem pointGauge_one (A : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    D.pointGauge 1 A = A := by
  rw [pointGauge_def, map_one, ← adRepresentation_apply, map_one, pointRightLogDeriv_one,
    sub_zero, one_apply_eq_self]

/-- **The gauge action is a left action**: `gauge (g h) A = gauge g (gauge h A)`. -/
theorem pointGauge_mul (g h : WithConv (H →ₐ[R] B))
    (A : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    D.pointGauge (g * h) A = D.pointGauge g (D.pointGauge h A) := by
  simp only [pointGauge_def, ← adRepresentation_apply, map_mul, pointRightLogDeriv_mul,
    mul_apply_eq_comp, map_sub]
  abel

@[simp]
theorem pointGauge_inv_pointGauge (g : WithConv (H →ₐ[R] B))
    (A : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    D.pointGauge g⁻¹ (D.pointGauge g A) = A := by
  rw [← pointGauge_mul, inv_mul_cancel, pointGauge_one]

@[simp]
theorem pointGauge_pointGauge_inv (g : WithConv (H →ₐ[R] B))
    (A : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    D.pointGauge g (D.pointGauge g⁻¹ A) = A := by
  rw [← pointGauge_mul, mul_inv_cancel, pointGauge_one]

/-- **Gauge transformations solve a linear differential equation**: `g` carries `A` to `A'`
exactly when `D ∘ g = g ⋆ A - A' ⋆ g`, with `A` and `A'` read in the coefficient algebra. -/
theorem pointGauge_eq_iff {g : WithConv (H →ₐ[R] B)}
    {A A' : Derivation R H (Bialgebra.CounitAlgebra R H B)} :
    D.pointGauge g A = A' ↔
      toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap) =
        toConv g.ofConv.toLinearMap *
            toConv ((Bialgebra.CounitAlgebra.algEquivSelf R H B).toLinearMap ∘ₗ
              (A : H →ₗ[R] Bialgebra.CounitAlgebra R H B)) -
          toConv ((Bialgebra.CounitAlgebra.algEquivSelf R H B).toLinearMap ∘ₗ
              (A' : H →ₗ[R] Bialgebra.CounitAlgebra R H B)) *
            toConv g.ofConv.toLinearMap := by
  rw [← toConv_algEquivSelf_comp_inj, pointGauge_def, Derivation.coe_sub_linearMap,
    LinearMap.comp_sub, toConv_sub, toConv_algEquivSelf_comp_adDerivation,
    toConv_algEquivSelf_comp_pointRightLogDeriv]
  set tg := toConv g.ofConv.toLinearMap
  set tgi := toConv (g⁻¹).ofConv.toLinearMap
  set Dg := toConv ((D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap)
  constructor
  · intro h
    rw [← h, sub_mul, mul_assoc (tg * _), algHom_toConv_inv_mul_toConv, mul_one, mul_assoc Dg,
      algHom_toConv_inv_mul_toConv, mul_one, sub_sub_cancel]
  · intro h
    rw [h, sub_mul, mul_assoc _ tg, algHom_toConv_mul_toConv_inv, mul_one, sub_sub_cancel]

/-- **Naturality of the gauge action** in the coefficient algebra, along an algebra map
`φ : B → C` intertwining the derivations `D` of `B` and `D'` of `C`. -/
theorem mapValue_pointGauge {C : Type*} [CommRing C] [Algebra R C] (φ : B →ₐ[R] C)
    (D' : Derivation R C C) (hφ : ∀ b, D' (φ b) = φ (D b)) (g : WithConv (H →ₐ[R] B))
    (A : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    mapValue φ (D.pointGauge g A) = D'.pointGauge (AlgHom.mapValue φ g) (mapValue φ A) := by
  rw [pointGauge_def, pointGauge_def, map_sub, mapValue_adDerivation,
    Bialgebra.CounitAlgebra.mapValue_pointsMulEquiv_symm_apply,
    mapValue_pointRightLogDeriv D φ D' hφ]

/-- The stabilizer of the connection `D + A` under the gauge action: its automorphisms as a
connection on the trivial torsor. -/
noncomputable def pointGaugeStabilizer (A : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    Subgroup (WithConv (H →ₐ[R] B)) where
  carrier := {g | D.pointGauge g A = A}
  one_mem' := D.pointGauge_one A
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [pointGauge_mul, hh, hg]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    conv_lhs => rw [← hg]
    exact D.pointGauge_inv_pointGauge g A

@[simp]
theorem mem_pointGaugeStabilizer_iff {A : Derivation R H (Bialgebra.CounitAlgebra R H B)}
    {g : WithConv (H →ₐ[R] B)} : g ∈ D.pointGaugeStabilizer A ↔ D.pointGauge g A = A :=
  Iff.rfl

/-- The automorphisms of the trivial connection `D` are the horizontal points, those killed
by `D`. -/
theorem mem_pointGaugeStabilizer_zero_iff {g : WithConv (H →ₐ[R] B)} :
    g ∈ D.pointGaugeStabilizer 0 ↔ (D : B →ₗ[R] B) ∘ₗ g.ofConv.toLinearMap = 0 := by
  rw [mem_pointGaugeStabilizer_iff, pointGauge_zero, neg_eq_zero, pointRightLogDeriv_eq_zero_iff]

end CommRing

end Derivation
