/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Star
public import TauCeti.Analysis.Complex.Circle.Conj
public import TauCeti.Topology.FiberBundle.Principal.Tensor
public import TauCeti.Topology.VectorBundle.Associated.Extension
public import TauCeti.Topology.VectorBundle.TensorProduct.Basic

/-!
# The Hermitian lines of the inverse and the tensor product of circle bundles

A principal `U(1)`-bundle `P` has the Hermitian line `P ×_{U(1)} ℂ`
(`TauCeti.AssociatedBundle Circle P ℂ`), on which `U(1)` acts on `ℂ` by multiplication. The inverse
`P⁻¹ = P ×_{z ↦ z⁻¹} U(1)` (`TauCeti.PrincipalBundle.Inverse`) and the tensor product
`P ⊗ Q = (P ×_B Q) ×_{(z, w) ↦ z w} U(1)` (`TauCeti.PrincipalBundle.Tensor`) of principal
`U(1)`-bundles are defined by extending the structure group. This file identifies their lines with
the conjugate line and the tensor product of lines:

* **The inverse.** Complex conjugation intertwines `z` with `z⁻¹ = conj z` on `ℂ`, so
  `[p, w] ↦ [[p, 1], conj w]` is a fibrewise conjugate-linear isomorphism
  `P ×_{U(1)} ℂ ≃ P⁻¹ ×_{U(1)} ℂ` (`TauCeti.PrincipalBundle.inverseLineEquiv`, by
  `Circle.starRingEnd_smul`), continuous on total spaces in both directions. The line of `P⁻¹` is
  the conjugate of the line of `P`, which for a Hermitian line is its dual.
* **The tensor product.** `[[(p, q), h], w] ↦ [p, h w] ⊗ [q, 1]` is a fibrewise continuous linear
  isomorphism `(P ⊗ Q) ×_{U(1)} ℂ ≃ (P ×_{U(1)} ℂ) ⊗ (Q ×_{U(1)} ℂ)`
  (`TauCeti.PrincipalBundle.tensorLineEquiv`), continuous on total spaces in both directions.
  It is well defined because `[(p z, q w), h] = [(p, q), z w h]` and `[q w, 1] = w [q, 1]`. In
  fixed frames, `[p, a] ⊗ [q, c] = (a c) ([p, 1] ⊗ [q, 1])`
  (`TauCeti.AssociatedBundle.mk_tmul_mk_eq_smul`).

These are the statements that `P⁻¹` and `P ⊗ Q` are the circle bundles of the inverse and the
tensor product of the Hermitian lines, which is how twisting lines of `Spinᶜ` structures built from
these operations are recognised.

## Main definitions

* `TauCeti.PrincipalBundle.inverseLineEquiv`: the conjugate-linear isomorphism from the line of `P`
  to the line of `P⁻¹`.
* `TauCeti.PrincipalBundle.tensorLineEquiv`: the linear isomorphism from the line of `P ⊗ Q` to the
  tensor product of the lines of `P` and `Q`.

## Main results

* `TauCeti.PrincipalBundle.inverseLineEquiv_mk`, `TauCeti.PrincipalBundle.inverseLineEquiv_symm_mk`:
  the formulas `[p, w] ↦ [[p, 1], conj w]` and `[[p, h], w] ↦ [p, conj (h w)]`.
* `TauCeti.PrincipalBundle.tensorLineEquiv_mk`, `TauCeti.PrincipalBundle.tensorLineEquiv_symm_tmul`:
  the formulas `[[(p, q), h], w] ↦ [p, h w] ⊗ [q, 1]` and `[p, a] ⊗ [q, c] ↦ [[(p, q), 1], a c]`.
* `TauCeti.PrincipalBundle.continuous_inverseLineEquiv`,
  `TauCeti.PrincipalBundle.continuous_inverseLineEquiv_symm`,
  `TauCeti.PrincipalBundle.continuous_tensorLineEquiv`,
  `TauCeti.PrincipalBundle.continuous_tensorLineEquiv_symm`: continuity on total spaces.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 6, §§2–3.
-/

public section

noncomputable section

open Bundle MulOpposite
open scoped TensorProduct TauCeti.ModuleTopology

namespace TauCeti.PrincipalBundle

variable {B : Type*} [TopologicalSpace B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P]
  {Q : B → Type*} [TopologicalSpace (TotalSpace Circle Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle Circle Q] [∀ b, MulAction Circleᵐᵒᵖ (Q b)] [PrincipalBundle Circle Q]

/-- Inversion of the circle, along which a principal `U(1)`-bundle extends to its inverse. -/
local notation "ν" => (ContinuousMonoidHom.inv Circle : Circle →* Circle)

/-- Inversion of the circle is continuous. -/
local notation "hν" => map_continuous (ContinuousMonoidHom.inv Circle)

/-- Multiplication of the circle, along which the fibre product of two principal `U(1)`-bundles
extends to their tensor product. -/
local notation "τ" => (ContinuousMonoidHom.mul Circle : Circle × Circle →* Circle)

/-- Multiplication of the circle is continuous. -/
local notation "hτ" => map_continuous (ContinuousMonoidHom.mul Circle)

/-! ### The line of the inverse -/

section Inverse

variable (P) in
/-- **The line of the inverse circle bundle** is the conjugate line: for a principal `U(1)`-bundle
`P`, the map `[p, w] ↦ [[p, 1], conj w]` is a fibrewise conjugate-linear isomorphism from the
Hermitian line `P ×_{U(1)} ℂ` to the Hermitian line of the inverse bundle
`P⁻¹ = P ×_{z ↦ z⁻¹} U(1)` (`TauCeti.PrincipalBundle.inverseLineEquiv_mk`). -/
def inverseLineEquiv (b : B) :
    AssociatedBundle Circle P ℂ b ≃L⋆[ℂ] AssociatedBundle Circle (Inverse Circle P) ℂ b :=
  Extend.associatedEquivOfEquivariant ν hν (starL ℂ) Circle.starRingEnd_smul b

/-- **The line of the inverse in a frame**: `[p, w] ↦ [[p, 1], conj w]`. -/
@[simp]
theorem inverseLineEquiv_mk {b : B} (p : P b) (w : ℂ) :
    inverseLineEquiv P b (AssociatedBundle.mk Circle p w) =
      AssociatedBundle.mk Circle (Extend.inl ν hν p) (starRingEnd ℂ w) :=
  Extend.associatedEquivOfEquivariant_mk ν hν (starL ℂ) Circle.starRingEnd_smul p w

/-- **The inverse identification in a frame**: `[[p, h], w] ↦ [p, conj (h w)]`. -/
@[simp]
theorem inverseLineEquiv_symm_mk {b : B} (p : P b) (h : Circle) (w : ℂ) :
    (inverseLineEquiv P b).symm (AssociatedBundle.mk Circle (Extend.mk ν hν p h) w) =
      AssociatedBundle.mk Circle p (starRingEnd ℂ (h * w)) :=
  (Extend.associatedEquivOfEquivariant_symm_mk ν hν (starL ℂ) Circle.starRingEnd_smul p h w).trans
    (by simp [Circle.smul_def])

variable (P) in
/-- **The line of the inverse is identified continuously** on total spaces. -/
theorem continuous_inverseLineEquiv :
    Continuous fun z : TotalSpace ℂ (AssociatedBundle Circle P ℂ) ↦
      TotalSpace.mk' ℂ (E := AssociatedBundle Circle (Inverse Circle P) ℂ) z.proj
        (inverseLineEquiv P z.proj z.snd) :=
  Extend.continuous_associatedEquivOfEquivariant ν hν (starL ℂ) Circle.starRingEnd_smul

variable (P) in
/-- **The inverse identification is continuous** on total spaces. -/
theorem continuous_inverseLineEquiv_symm :
    Continuous fun z : TotalSpace ℂ (AssociatedBundle Circle (Inverse Circle P) ℂ) ↦
      TotalSpace.mk' ℂ (E := AssociatedBundle Circle P ℂ) z.proj
        ((inverseLineEquiv P z.proj).symm z.snd) :=
  Extend.continuous_associatedEquivOfEquivariant_symm ν hν (starL ℂ) Circle.starRingEnd_smul

end Inverse

/-! ### The line of the tensor product -/

/-- **Pure tensors of lines in fixed frames**: for associated bundles with scalar model fibre,
`[p, a] ⊗ [q, c] = (a c) ([p, 1] ⊗ [q, 1])`. -/
theorem _root_.TauCeti.AssociatedBundle.mk_tmul_mk_eq_smul {𝕜 G G' : Type*}
    [NontriviallyNormedField 𝕜] [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
    [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
    {Q : B → Type*} [TopologicalSpace (TotalSpace G' Q)] [∀ b, TopologicalSpace (Q b)]
    [FiberBundle G' Q] [∀ b, MulAction G'ᵐᵒᵖ (Q b)] [PrincipalBundle G' Q]
    [DistribMulAction G 𝕜] [SMulCommClass G 𝕜 𝕜] [ContinuousSMul G 𝕜]
    [DistribMulAction G' 𝕜] [SMulCommClass G' 𝕜 𝕜] [ContinuousSMul G' 𝕜]
    {b : B} (p : P b) (q : Q b) (a c : 𝕜) :
    AssociatedBundle.mk G p a ⊗ₜ[𝕜] AssociatedBundle.mk G' q c =
      (a * c) • (AssociatedBundle.mk G p (1 : 𝕜) ⊗ₜ[𝕜] AssociatedBundle.mk G' q (1 : 𝕜)) := by
  rw [AssociatedBundle.mk_eq_smul_mk_one p a, AssociatedBundle.mk_eq_smul_mk_one q c,
    TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, mul_comm c a]

section Tensor

/-- The identification of lines read in the frames `[(p₀, q₀), 1]`, `p₀` and `q₀`:
`[[(p₀, q₀), 1], w] ↦ [p₀, w] ⊗ [q₀, 1]`. -/
private def tensorLineLinearEquiv {b : B} (p₀ : P b) (q₀ : Q b) :
    AssociatedBundle Circle (Tensor Circle P Q) ℂ b ≃ₗ[ℂ]
      AssociatedBundle Circle P ℂ b ⊗[ℂ] AssociatedBundle Circle Q ℂ b :=
  (AssociatedBundle.mkContinuousLinearEquiv ℂ Circle (F := ℂ) (P := Tensor Circle P Q)
      (Extend.inl τ hτ (FiberProd.mk p₀ q₀))).symm.toLinearEquiv ≪≫ₗ
    (TensorProduct.rid ℂ ℂ).symm ≪≫ₗ
    TensorProduct.congr (AssociatedBundle.mkContinuousLinearEquiv ℂ Circle p₀).toLinearEquiv
      (AssociatedBundle.mkContinuousLinearEquiv ℂ Circle q₀).toLinearEquiv

/-- The identification of lines in every frame, whatever its reference frames:
`[[(p, q), h], w] ↦ [p, h w] ⊗ [q, 1]`. -/
private theorem tensorLineLinearEquiv_mk {b : B} (p₀ p : P b) (q₀ q : Q b) (h : Circle)
    (w : ℂ) :
    tensorLineLinearEquiv p₀ q₀
        (AssociatedBundle.mk Circle (Extend.mk τ hτ (FiberProd.mk p q) h) w) =
      AssociatedBundle.mk Circle p (h • w) ⊗ₜ[ℂ] AssociatedBundle.mk Circle q (1 : ℂ) := by
  -- Write `(p, q) = (p₀, q₀) • (z, u)`; then `[[(p, q), h], w] = [[(p₀, q₀), 1], z u h w]`.
  obtain ⟨z, rfl⟩ : ∃ z, op z • p₀ = p := ⟨_, smul_division (G := Circle) p₀ p⟩
  obtain ⟨u, rfl⟩ : ∃ u, op u • q₀ = q := ⟨_, smul_division (G := Circle) q₀ q⟩
  rw [← FiberProd.op_smul_mk, Extend.mk_smul, ← Extend.smul_inl, AssociatedBundle.mk_smul]
  simp only [tensorLineLinearEquiv, LinearEquiv.trans_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv,
    AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk, division_self, one_smul,
    TensorProduct.rid_symm_apply, TensorProduct.congr_tmul,
    AssociatedBundle.mkContinuousLinearEquiv_apply, AssociatedBundle.mk_smul]
  rw [AssociatedBundle.mk_tmul_mk_eq_smul p₀ q₀ _ 1,
    AssociatedBundle.mk_tmul_mk_eq_smul p₀ q₀ _ (u • (1 : ℂ))]
  congr 1
  -- `τ (z, u) = z u` holds by definition of `ContinuousMonoidHom.mul` (Mathlib states no apply
  -- lemma for it), and the scalars are multiplications in `ℂ`.
  have hτzu : (τ (z, u) : Circle) = z * u := rfl
  rw [hτzu]
  simp only [Circle.smul_def, Circle.coe_mul, smul_eq_mul, mul_one]
  ring

variable (P Q) in
/-- **The line of the tensor product of circle bundles** is the tensor product of their lines: for
principal `U(1)`-bundles `P` and `Q`, the map `[[(p, q), h], w] ↦ [p, h w] ⊗ [q, 1]` is a fibrewise
continuous linear isomorphism from the Hermitian line of `P ⊗ Q` to the tensor product of the
Hermitian lines of `P` and `Q` (`TauCeti.PrincipalBundle.tensorLineEquiv_mk`). -/
def tensorLineEquiv (b : B) :
    AssociatedBundle Circle (Tensor Circle P Q) ℂ b ≃L[ℂ]
      AssociatedBundle Circle P ℂ b ⊗[ℂ] AssociatedBundle Circle Q ℂ b :=
  (tensorLineLinearEquiv ((FiberBundle.homeomorphAt Circle P b).symm 1)
    ((FiberBundle.homeomorphAt Circle Q b).symm 1)).toContinuousLinearEquivOfIsModuleTopology

/-- **The line of the tensor product in a frame**: `[[(p, q), h], w] ↦ [p, h w] ⊗ [q, 1]`. -/
@[simp]
theorem tensorLineEquiv_mk {b : B} (p : P b) (q : Q b) (h : Circle) (w : ℂ) :
    tensorLineEquiv P Q b
        (AssociatedBundle.mk Circle (Extend.mk τ hτ (FiberProd.mk p q) h) w) =
      AssociatedBundle.mk Circle p (h • w) ⊗ₜ[ℂ] AssociatedBundle.mk Circle q (1 : ℂ) :=
  (congrFun (LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology _) _).trans
    (tensorLineLinearEquiv_mk _ p _ q h w)

/-- **The line of the tensor product at `[(p, q), 1]`**: `[[(p, q), 1], w] ↦ [p, w] ⊗ [q, 1]`. -/
@[simp]
theorem tensorLineEquiv_inl {b : B} (p : P b) (q : Q b) (w : ℂ) :
    tensorLineEquiv P Q b
        (AssociatedBundle.mk Circle (Extend.inl τ hτ (FiberProd.mk p q)) w) =
      AssociatedBundle.mk Circle p w ⊗ₜ[ℂ] AssociatedBundle.mk Circle q (1 : ℂ) := by
  rw [Extend.inl_def, tensorLineEquiv_mk, one_smul]

/-- **The inverse identification on pure tensors**: `[p, a] ⊗ [q, c] ↦ [[(p, q), 1], a c]`. -/
@[simp]
theorem tensorLineEquiv_symm_tmul {b : B} (p : P b) (q : Q b) (a c : ℂ) :
    (tensorLineEquiv P Q b).symm
        (AssociatedBundle.mk Circle p a ⊗ₜ[ℂ] AssociatedBundle.mk Circle q c) =
      AssociatedBundle.mk Circle (Extend.inl τ hτ (FiberProd.mk p q)) (a * c) := by
  refine (ContinuousLinearEquiv.symm_apply_eq _).2
    ((?_ : _ = _).trans (tensorLineEquiv_inl p q _).symm)
  rw [AssociatedBundle.mk_tmul_mk_eq_smul p q (a * c), mul_one]
  exact AssociatedBundle.mk_tmul_mk_eq_smul p q a c

variable (P Q) in
/-- **The line of the tensor product is identified continuously** on total spaces. -/
theorem continuous_tensorLineEquiv :
    Continuous fun v : TotalSpace ℂ (AssociatedBundle Circle (Tensor Circle P Q) ℂ) ↦
      TotalSpace.mk' (ProjectiveTensor ℂ ℂ ℂ)
        (E := fun b ↦ AssociatedBundle Circle P ℂ b ⊗[ℂ] AssociatedBundle Circle Q ℂ b)
        v.proj (tensorLineEquiv P Q v.proj v.snd) := by
  -- The total space is an open quotient of `((P ×_B Q) × U(1)) × ℂ`, on which the identification
  -- is `(((p, q), h), w) ↦ [p, h w] ⊗ [q, 1]`.
  refine ((AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk Circle (Tensor Circle P Q) ℂ).comp
    ((Extend.isOpenQuotientMap_totalSpaceMk_mk (FiberProd P Q) τ hτ).prodMap
      IsOpenQuotientMap.id)).continuous_comp_iff.1 ?_
  have hc : Continuous fun y : (TotalSpace (Circle × Circle) (FiberProd P Q) × Circle) × ℂ ↦
      TotalSpace.mk' (ProjectiveTensor ℂ ℂ ℂ)
        (E := fun b ↦ AssociatedBundle Circle P ℂ b ⊗[ℂ] AssociatedBundle Circle Q ℂ b)
        y.1.1.proj
        (AssociatedBundle.mk Circle y.1.1.snd.fst (y.1.2 • y.2) ⊗ₜ[ℂ]
          AssociatedBundle.mk Circle y.1.1.snd.snd (1 : ℂ)) :=
    ((FiberProd.continuous_totalSpaceMk_fst.comp (continuous_fst.comp continuous_fst))
        |>.totalSpaceMk_associatedBundleMk
          ((continuous_snd.comp continuous_fst).smul continuous_snd)).tmul_section
      ((FiberProd.continuous_totalSpaceMk_snd.comp (continuous_fst.comp continuous_fst))
        |>.totalSpaceMk_associatedBundleMk continuous_const)
  exact hc.congr fun y ↦ congrArg (TotalSpace.mk _) (tensorLineEquiv_mk ..).symm

variable (P Q) in
/-- **The tensor identification is continuous** on total spaces: the inverse of a continuous
fibrewise linear equivalence of finite-rank bundles is continuous. -/
theorem continuous_tensorLineEquiv_symm :
    Continuous fun v : TotalSpace (ProjectiveTensor ℂ ℂ ℂ)
        (fun b ↦ AssociatedBundle Circle P ℂ b ⊗[ℂ] AssociatedBundle Circle Q ℂ b) ↦
      TotalSpace.mk' ℂ (E := AssociatedBundle Circle (Tensor Circle P Q) ℂ) v.proj
        ((tensorLineEquiv P Q v.proj).symm v.snd) :=
  continuous_bundle_symm (tensorLineEquiv P Q) (continuous_tensorLineEquiv P Q)

end Tensor

end TauCeti.PrincipalBundle
