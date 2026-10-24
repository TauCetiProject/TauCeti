/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.UniformSpace.Real
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Pairing
public import TauCeti.Data.Fin.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.Curry
import Mathlib.Tactic.Module
import TauCeti.GroupTheory.Perm.Inversion
import TauCeti.GroupTheory.Perm.Basic

/-!
# Paired wedges of continuous alternating maps

This file constructs the paired wedge of continuous alternating maps on real modules with a
topology. Its determinant normalization is the signed-permutation sum divided by the two input
factorials. It provides bilinearity and pullback compatibility for general topological coefficient
spaces, including the flip law. A pairing that turns multiplication by one scalar into
multiplication by another, such as a complex-bilinear pairing, makes the paired wedge semilinear
in the same way, and the paired wedge is natural for coefficient maps intertwining two pairings.
Joint continuity of each pairing is supplied explicitly; no norm is required on the domain or
coefficients. The output coefficients require only continuity of multiplication by each fixed
scalar. The flip law assumes this property for the second input coefficient space as well.

It also proves the norm-free interior-product antiderivation law
`ι_v (φ ∧ ψ) = ι_v φ ∧ ψ + (-1) ^ (deg φ) • φ ∧ ι_v ψ`, using
`ContinuousAlternatingMap.curryLeftTopological` from the accompanying Curry module.
The normed counterpart is `ContinuousAlternatingMap.curryLeft_pairedWedge`.

The alternating-map API follows Mathlib's `AlternatingMap.curryLeft` and `map_insertNth`, and the
paired-wedge design follows Yury Kudryashov's `DeRhamCohomology` project.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Lemma 14.13.
* Yury Kudryashov's `DeRhamCohomology` project.
-/

public section

open TensorProduct TauCeti

namespace ContinuousAlternatingMap

variable {E F₁ F₂ F₃ : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
  [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
  [AddCommGroup F₃] [Module ℝ F₃] [TopologicalSpace F₃]
  [IsTopologicalAddGroup F₃] [ContinuousConstSMul ℝ F₃]

/-- The linear map induced by a continuous bilinear pairing on the tensor product. -/
noncomputable def pairingLinear (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) :
    F₁ ⊗[ℝ] F₂ →ₗ[ℝ] F₃ :=
  TensorProduct.lift ((ContinuousLinearMap.coeLM ℝ).comp μ.toLinearMap)

/-- The pairing-induced linear map evaluates pure tensors by the original pairing. -/
@[simp]
theorem pairingLinear_tmul (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (x : F₁) (y : F₂) :
    pairingLinear μ (x ⊗ₜ[ℝ] y) = μ x y := by
  simp [pairingLinear]

/-- The unalternated multilinear pairing underlying the paired wedge. -/
noncomputable def wedgeWithUnalternated {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    MultilinearMap ℝ (fun _ : Fin (k + l) => E) F₃ :=
  (pairingLinear μ).compMultilinearMap <|
    (MultilinearMap.domCoprod φ.toAlternatingMap.toMultilinearMap
      ψ.toAlternatingMap.toMultilinearMap).domDomCongr finSumFinEquiv

/-- The tensor-product construction of the unalternated paired wedge. -/
theorem wedgeWithUnalternated_def {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    wedgeWithUnalternated μ φ ψ =
      (pairingLinear μ).compMultilinearMap
        ((MultilinearMap.domCoprod φ.toAlternatingMap.toMultilinearMap
          ψ.toAlternatingMap.toMultilinearMap).domDomCongr finSumFinEquiv) := (rfl)

/-- Evaluation of the unalternated pairing on concatenated vectors. -/
@[simp]
theorem wedgeWithUnalternated_apply {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    wedgeWithUnalternated μ φ ψ v =
      μ (φ (fun i => v (Fin.castAdd l i))) (ψ (fun j => v (Fin.natAdd k j))) := by
  simp [wedgeWithUnalternated, pairingLinear]

/-- The continuous multilinear map associated to the unalternated paired product. -/
noncomputable def wedgeWithUnalternatedContinuous {k l : ℕ}
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k + l) => E) F₃ :=
  { toMultilinearMap := wedgeWithUnalternated μ φ ψ
    cont := by
      have hfun : (wedgeWithUnalternated μ φ ψ).toFun =
          (fun v ↦ μ (φ (fun i ↦ v (Fin.castAdd l i)))
            (ψ (fun j ↦ v (Fin.natAdd k j)))) :=
        funext (wedgeWithUnalternated_apply μ φ ψ)
      rw [hfun]
      fun_prop }

/-- Evaluation of the continuous unalternated pairing on concatenated vectors. -/
@[simp]
theorem wedgeWithUnalternatedContinuous_apply {k l : ℕ}
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    wedgeWithUnalternatedContinuous μ hμ φ ψ v =
      μ (φ (fun i ↦ v (Fin.castAdd l i))) (ψ (fun j ↦ v (Fin.natAdd k j))) := by
  exact wedgeWithUnalternated_apply μ φ ψ v

/-- The paired wedge of continuous alternating maps, normalized by the two input factorials. -/
noncomputable def pairedWedge {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    E [⋀^Fin (k + l)]→L[ℝ] F₃ :=
  (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
    (wedgeWithUnalternatedContinuous μ hμ φ ψ).alternatization

/-- The pointwise formula for the paired wedge in all degrees. -/
theorem pairedWedge_apply {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    pairedWedge μ hμ φ ψ v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          μ (φ (fun i ↦ v (σ (Fin.castAdd l i))))
            (ψ (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  simp only [pairedWedge, ContinuousAlternatingMap.smul_apply,
    ContinuousMultilinearMap.alternatization_apply_apply,
    wedgeWithUnalternatedContinuous_apply]
  simp only [Function.comp_apply]

/-- Wedge with a degree-zero form is the coefficient pairing with its value on the empty tuple. -/
@[simp]
theorem pairedWedge_apply_zero_right {k : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin 0]→L[ℝ] F₂) (v : Fin k → E) :
    pairedWedge μ hμ φ ψ v = μ (φ v) (ψ 0) := by
  let L : F₁ →L[ℝ] F₃ :=
    { toFun := fun a ↦ μ a (ψ 0)
      map_add' := fun a b ↦ by simp
      map_smul' := fun c a ↦ by simp
      cont := hμ.comp (continuous_id.prodMk continuous_const) }
  have h : wedgeWithUnalternatedContinuous μ hμ φ ψ =
      (L.compContinuousAlternatingMap φ).toContinuousMultilinearMap := by
    ext w
    rw [wedgeWithUnalternatedContinuous_apply]
    have hw : (fun j : Fin 0 ↦ w (Fin.natAdd k j)) = 0 := Subsingleton.elim _ _
    simp [L, hw]
  rw [pairedWedge, h, alternatization_toContinuousMultilinearMap]
  simp [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.factorial_ne_zero, L]

/-- On one-forms, the paired wedge is the usual two-term alternating product. -/
@[simp]
theorem pairedWedge_apply_one_one {μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃}
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin 1]→L[ℝ] F₁) (ψ : E [⋀^Fin 1]→L[ℝ] F₂) (v w : E) :
    pairedWedge μ hμ φ ψ ![v, w] = μ (φ ![v]) (ψ ![w]) - μ (φ ![w]) (ψ ![v]) := by
  classical
  rw [pairedWedge_apply]
  rw [Equiv.Perm.univ_fin_two, Finset.sum_insert (by decide), Finset.sum_singleton,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  simp [Fin.fin_one_eq_zero, Matrix.cons_fin_one, sub_eq_add_neg]

/-- The underlying alternating map of the paired wedge is the alternatization of its unalternated
multilinear pairing, divided by `k! l!`. -/
@[simp]
theorem pairedWedge_toAlternatingMap {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hmu : Continuous (Function.uncurry fun x y ↦ mu x y))
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    (pairedWedge mu hmu phi psi).toAlternatingMap =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        (ContinuousAlternatingMap.wedgeWithUnalternated mu phi psi).alternatization := by
  ext v
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap, pairedWedge_apply,
    _root_.smul_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply, ContinuousAlternatingMap.wedgeWithUnalternated_apply]

/-- Precomposing both inputs of a paired wedge by a continuous linear map is the same as
precomposing the resulting wedge. -/
@[simp]
theorem pairedWedge_compContinuousLinearMap {E' : Type*} [AddCommGroup E'] [Module ℝ E']
    [TopologicalSpace E'] {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂)
    (f : E' →L[ℝ] E) :
    (pairedWedge μ hμ φ ψ).compContinuousLinearMap f =
      pairedWedge μ hμ (φ.compContinuousLinearMap f) (ψ.compContinuousLinearMap f) := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, pairedWedge_apply,
    Function.comp_def]

/-- The paired wedge is additive in its first alternating map. -/
@[simp]
theorem pairedWedge_add_left [ContinuousAdd F₁] {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ φ' : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge μ hμ (φ + φ') ψ = pairedWedge μ hμ φ ψ + pairedWedge μ hμ φ' ψ := by
  ext v
  simp only [pairedWedge_apply, ContinuousAlternatingMap.add_apply, map_add, _root_.add_apply,
    smul_add, Finset.sum_add_distrib]

/-- The paired wedge is additive in its second alternating map. -/
@[simp]
theorem pairedWedge_add_right [ContinuousAdd F₂] {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ ψ' : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge μ hμ φ (ψ + ψ') = pairedWedge μ hμ φ ψ + pairedWedge μ hμ φ ψ' := by
  ext v
  simp only [pairedWedge_apply, ContinuousAlternatingMap.add_apply, map_add,
    smul_add, Finset.sum_add_distrib]

/-- If the pairing turns multiplication by `c` in its first argument into multiplication by `d`,
then so does the paired wedge in its first alternating map. For a complex-bilinear pairing this is
complex-linearity in the first factor; it also covers pairings that are conjugate-linear in the
first argument. -/
theorem pairedWedge_smul_left_of_map_smul {S S' : Type*} [Monoid S] [DistribMulAction S F₁]
    [ContinuousConstSMul S F₁] [SMulCommClass ℝ S F₁] [Monoid S'] [DistribMulAction S' F₃]
    [ContinuousConstSMul S' F₃] [SMulCommClass ℝ S' F₃] {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) {c : S} {d : S'}
    (hcd : ∀ a b, μ (c • a) b = d • μ a b)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge μ hμ (c • φ) ψ = d • pairedWedge μ hμ φ ψ := by
  ext v
  simp only [pairedWedge_apply, ContinuousAlternatingMap.smul_apply, hcd, Finset.smul_sum,
    smul_comm _ d]

/-- If the pairing turns multiplication by `c` in its second argument into multiplication by
`d`, then so does the paired wedge in its second alternating map. For a complex-bilinear pairing
this is complex-linearity in the second factor. -/
theorem pairedWedge_smul_right_of_map_smul {S S' : Type*} [Monoid S] [DistribMulAction S F₂]
    [ContinuousConstSMul S F₂] [SMulCommClass ℝ S F₂] [Monoid S'] [DistribMulAction S' F₃]
    [ContinuousConstSMul S' F₃] [SMulCommClass ℝ S' F₃] {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) {c : S} {d : S'}
    (hcd : ∀ a b, μ a (c • b) = d • μ a b)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge μ hμ φ (c • ψ) = d • pairedWedge μ hμ φ ψ := by
  ext v
  simp only [pairedWedge_apply, ContinuousAlternatingMap.smul_apply, hcd, Finset.smul_sum,
    smul_comm _ d]

/-- The paired wedge respects scalar multiplication in its first alternating map. -/
@[simp]
theorem pairedWedge_smul_left [ContinuousConstSMul ℝ F₁] {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) (c : ℝ)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge μ hμ (c • φ) ψ = c • pairedWedge μ hμ φ ψ :=
  pairedWedge_smul_left_of_map_smul μ hμ (fun a b ↦ by simp) φ ψ

/-- The paired wedge respects scalar multiplication in its second alternating map. -/
@[simp]
theorem pairedWedge_smul_right [ContinuousConstSMul ℝ F₂] {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) (c : ℝ)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge μ hμ φ (c • ψ) = c • pairedWedge μ hμ φ ψ :=
  pairedWedge_smul_right_of_map_smul μ hμ (fun a b ↦ by simp) φ ψ

/-- The paired wedge is natural in the coefficients: if continuous linear maps `L₁`, `L₂`, `L`
of the coefficient spaces intertwine the pairings `μ` and `μ'`, then applying `L` to the paired
wedge of `φ` and `ψ` gives the paired wedge of `L₁ ∘ φ` and `L₂ ∘ ψ`. -/
theorem compContinuousAlternatingMap_pairedWedge {G₁ G₂ G₃ : Type*}
    [AddCommGroup G₁] [Module ℝ G₁] [TopologicalSpace G₁]
    [AddCommGroup G₂] [Module ℝ G₂] [TopologicalSpace G₂]
    [AddCommGroup G₃] [Module ℝ G₃] [TopologicalSpace G₃]
    [IsTopologicalAddGroup G₃] [ContinuousConstSMul ℝ G₃] {k l : ℕ}
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (μ' : G₁ →L[ℝ] G₂ →L[ℝ] G₃) (hμ' : Continuous (Function.uncurry fun x y ↦ μ' x y))
    (L₁ : F₁ →L[ℝ] G₁) (L₂ : F₂ →L[ℝ] G₂) (L : F₃ →L[ℝ] G₃)
    (hL : ∀ a b, L (μ a b) = μ' (L₁ a) (L₂ b))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    L.compContinuousAlternatingMap (pairedWedge μ hμ φ ψ) =
      pairedWedge μ' hμ' (L₁.compContinuousAlternatingMap φ)
        (L₂.compContinuousAlternatingMap ψ) := by
  ext v
  simp only [pairedWedge_apply, ContinuousLinearMap.compContinuousAlternatingMap_coe,
    Function.comp_apply, _root_.map_smul, _root_.map_sum, map_zsmul_unit, hL]

/-- Postcomposing the pairing postcomposes the paired wedge. -/
@[simp]
theorem pairedWedge_postcomp {F₄ : Type*} [AddCommGroup F₄] [Module ℝ F₄]
    [TopologicalSpace F₄] [IsTopologicalAddGroup F₄] [ContinuousConstSMul ℝ F₄]
    {k l : ℕ} (nu : F₃ →L[ℝ] F₄) (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hmu : Continuous (Function.uncurry fun x y ↦ mu x y))
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge ((ContinuousLinearMap.postcomp F₂ nu).comp mu)
        (by
          simpa only [Function.uncurry_def, Function.comp_def, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.postcomp_apply] using nu.continuous.comp hmu) phi psi =
      nu.compContinuousAlternatingMap (pairedWedge mu hmu phi psi) := by
  rw [compContinuousAlternatingMap_pairedWedge mu hmu ((ContinuousLinearMap.postcomp F₂ nu).comp mu)
    _ (.id ℝ F₁) (.id ℝ F₂) nu (fun _ _ ↦ by simp) phi psi,
    ContinuousLinearMap.id_compContinuousAlternatingMap,
    ContinuousLinearMap.id_compContinuousAlternatingMap]

/-- The paired wedge is additive in the pairing. -/
@[simp]
theorem pairedWedge_add_pairing {k l : ℕ} (mu nu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hmu : Continuous (Function.uncurry fun x y ↦ mu x y))
    (hnu : Continuous (Function.uncurry fun x y ↦ nu x y))
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge (mu + nu) (by
        convert hmu.add hnu using 1
        ext p
        simp only [Function.uncurry_def, _root_.add_apply, Pi.add_apply]) phi psi =
      pairedWedge mu hmu phi psi + pairedWedge nu hnu phi psi := by
  ext v
  simp only [pairedWedge_apply, _root_.add_apply, ContinuousAlternatingMap.add_apply,
    Finset.smul_sum, smul_add]
  rw [Finset.sum_add_distrib]

/-- The paired wedge respects scalar multiplication of the pairing. -/
@[simp]
theorem pairedWedge_smul_pairing {k l : ℕ} (c : ℝ) (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hmu : Continuous (Function.uncurry fun x y ↦ mu x y))
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge (c • mu) (by
        convert hmu.const_smul c using 1
        ext p
        simp only [Function.uncurry_def, _root_.smul_apply, Pi.smul_apply]) phi psi =
      c • pairedWedge mu hmu phi psi := by
  ext v
  simp only [pairedWedge_apply, ContinuousAlternatingMap.smul_apply, _root_.smul_apply,
    Finset.smul_sum, smul_comm _ c]

/-- Negating the pairing negates the paired wedge. -/
@[simp]
theorem pairedWedge_neg_pairing {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hmu : Continuous (Function.uncurry fun x y ↦ mu x y))
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge (-mu) (by
        convert hmu.neg using 1
        ext p
        simp only [Function.uncurry_def, _root_.neg_apply, Pi.neg_apply])
      phi psi = -pairedWedge mu hmu phi psi := by
  ext v
  simp only [pairedWedge_apply, _root_.neg_apply, ContinuousAlternatingMap.neg_apply,
    smul_neg, Finset.sum_neg_distrib]

/-- The paired wedge for the zero pairing is zero. -/
@[simp]
theorem pairedWedge_zero_pairing {k l : ℕ} (phi : E [⋀^Fin k]→L[ℝ] F₁)
    (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge (0 : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (by
        simpa only [Function.uncurry_def, _root_.zero_apply] using
          (continuous_const : Continuous (fun _ : F₁ × F₂ ↦ (0 : F₃))))
      phi psi = 0 := by
  ext v
  simp only [pairedWedge_apply, _root_.zero_apply, smul_zero, Finset.sum_const_zero,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

/-- Wedge with the zero form on the left is zero. -/
@[simp]
theorem pairedWedge_zero_left {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hmu : Continuous (Function.uncurry fun x y ↦ mu x y))
    (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge mu hmu (0 : E [⋀^Fin k]→L[ℝ] F₁) psi = 0 := by
  ext v
  simp only [pairedWedge_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply, _root_.map_zero,
    _root_.zero_apply, smul_zero, Finset.sum_const_zero]

/-- Wedge with the zero form on the right is zero. -/
@[simp]
theorem pairedWedge_zero_right {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hmu : Continuous (Function.uncurry fun x y ↦ mu x y))
    (phi : E [⋀^Fin k]→L[ℝ] F₁) :
    pairedWedge mu hmu phi (0 : E [⋀^Fin l]→L[ℝ] F₂) = 0 := by
  ext v
  simp only [pairedWedge_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply, _root_.map_zero,
    smul_zero, Finset.sum_const_zero]

/-- The flip identity: swapping the two forms of a paired wedge flips the pairing and costs the
graded sign `(-1) ^ (k * l)`. This holds for every pairing. -/
theorem pairedWedge_flip [IsTopologicalAddGroup F₂] [ContinuousConstSMul ℝ F₂]
    {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hmu : Continuous (Function.uncurry fun x y ↦ mu x y))
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) (v : Fin (k + l) → E) :
    pairedWedge mu hmu phi psi v =
      (-1 : ℝ) ^ (k * l) • pairedWedge (mu.pairingFlip hmu)
        (mu.pairingFlip_continuous hmu) psi phi (v ∘ Fin.cast (Nat.add_comm l k)) := by
  -- Reindex the permutation sum on the right by composing with the block swap `B`, which
  -- exchanges the first `k` and the last `l` indices and has sign `(-1) ^ (k * l)`.
  set c : Fin (l + k) ≃ Fin (k + l) := finCongr (Nat.add_comm l k)
  set B : Equiv.Perm (Fin (k + l)) := finAddFlip.trans c
  have hsum : ∑ tau : Equiv.Perm (Fin (l + k)), Equiv.Perm.sign tau •
        mu.pairingFlip hmu
          (psi (fun i => (v ∘ Fin.cast (Nat.add_comm l k)) (tau (Fin.castAdd k i))))
          (phi (fun j => (v ∘ Fin.cast (Nat.add_comm l k)) (tau (Fin.natAdd l j)))) =
      Equiv.Perm.sign B • ∑ sigma : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign sigma •
        mu (phi (fun i => v (sigma (Fin.castAdd l i))))
          (psi (fun j => v (sigma (Fin.natAdd k j)))) := by
    let f : Equiv.Perm (Fin (k + l)) → F₃ := fun sigma =>
      mu (phi (fun i => v (sigma (Fin.castAdd l i))))
        (psi (fun j => v (sigma (Fin.natAdd k j))))
    calc
      _ = ∑ tau : Equiv.Perm (Fin (l + k)), Equiv.Perm.sign tau •
          f (c.permCongr tau * B) := by
        apply Finset.sum_congr rfl
        intro tau _
        have hleft : (fun i => v ((c.permCongr tau * B) (Fin.castAdd l i))) =
            fun j => v (Fin.cast (Nat.add_comm l k) (tau (Fin.natAdd l j))) := by
          funext i
          simp [B, c, finAddFlip_apply_castAdd]
        have hright : (fun j => v ((c.permCongr tau * B) (Fin.natAdd k j))) =
            fun i => v (Fin.cast (Nat.add_comm l k) (tau (Fin.castAdd k i))) := by
          funext j
          simp [B, c, finAddFlip_apply_natAdd]
        simp only [f, Function.comp_apply, ContinuousLinearMap.pairingFlip_apply]
        rw [← hright, ← hleft]
      _ = _ := sum_sign_smul_permCongr_mul c B f
  rw [pairedWedge_apply, pairedWedge_apply, hsum, sign_finAddFlip_trans_finCongr]
  generalize (∑ sigma : Equiv.Perm (Fin (k + l)), (_ : F₃)) = S
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ]
  match_scalars
  ring_nf
  simp

/-- Anticommutation of a paired wedge along a skew-symmetric pairing. -/
theorem pairedWedge_anticomm [IsTopologicalAddGroup F₁] [ContinuousConstSMul ℝ F₁]
    {k l : ℕ} {mu : F₁ →L[ℝ] F₁ →L[ℝ] F₃}
    (hmu : Continuous (Function.uncurry fun x y ↦ mu x y))
    (hskew : ∀ a b, mu a b = -mu b a)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₁)
    (v : Fin (k + l) → E) :
    pairedWedge mu hmu phi psi v =
      -((-1 : ℝ) ^ (k * l) • pairedWedge mu hmu psi phi (v ∘ Fin.cast (Nat.add_comm l
    k))) := by
  have hflip : (mu.pairingFlip hmu) = -mu := by
    ext a b
    simpa only [ContinuousLinearMap.pairingFlip_apply, _root_.neg_apply] using hskew b a
  rw [pairedWedge_flip]
  simp only [hflip, pairedWedge_neg_pairing mu hmu, ContinuousAlternatingMap.neg_apply,
    smul_neg]

/-- Graded commutativity of the paired wedge along a symmetric pairing. -/
theorem pairedWedge_comm [IsTopologicalAddGroup F₁] [ContinuousConstSMul ℝ F₁]
    {k l : ℕ} {mu : F₁ →L[ℝ] F₁ →L[ℝ] F₃}
    (hmu : Continuous (Function.uncurry fun x y ↦ mu x y))
    (hsymm : ∀ a b, mu a b = mu b a)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₁) (v : Fin (k + l) → E) :
    pairedWedge mu hmu phi psi v =
      (-1 : ℝ) ^ (k * l) • pairedWedge mu hmu psi phi (v ∘ Fin.cast (Nat.add_comm l k))
    := by
  have hflip : (mu.pairingFlip hmu) = mu := by
    ext a b
    simpa only [ContinuousLinearMap.pairingFlip_apply] using hsymm b a
  rw [pairedWedge_flip]
  simp only [hflip]

section InteriorProduct

open Equiv

variable {k l : ℕ}

private lemma sum_sign_smul_insertNth_castAdd [ContinuousAdd F₁] [ContinuousConstSMul ℝ F₁]
    (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin (k + 1)]→L[ℝ] F₁) (psi : E [⋀^Fin (l + 1)]→L[ℝ] F₂) (v : E)
    (w : Fin (k + 1 + l) → E) (i : Fin (k + 1)) :
    (-1 : ℤ) ^ (Fin.castAdd (l + 1) i : ℕ) • ∑ τ : Perm (Fin (k + 1 + l)), Perm.sign τ •
      mu (phi fun a => Fin.insertNth (α := fun _ => E)
          (Fin.castAdd (l + 1) i : Fin (k + 1 + l + 1)) v (w ∘ τ) (Fin.castAdd (l + 1) a))
        (psi fun b => Fin.insertNth (α := fun _ => E)
          (Fin.castAdd (l + 1) i : Fin (k + 1 + l + 1)) v (w ∘ τ) (Fin.natAdd (k + 1) b)) =
      ∑ sigma : Perm (Fin (k + (l + 1))), Perm.sign sigma •
        mu (phi.curryLeftTopological v fun a =>
            (w ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) (sigma (Fin.castAdd (l + 1) a)))
          (psi fun b =>
            (w ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) (sigma (Fin.natAdd k b))) := by
  have hsign : (-1 : ℤ) ^ (Fin.castAdd (l + 1) i : ℕ) * (-1) ^ (i : ℕ) = 1 := by
    simp [← mul_pow]
  simp_rw [Fin.insertNth_castAdd_comp_castAdd, Fin.insertNth_castAdd_apply_natAdd,
    ContinuousAlternatingMap.map_insertNth', ← curryLeftTopological_apply_apply]
  simp only [map_zsmul, FunLike.coe_smul, Pi.smul_apply, smul_comm (Perm.sign _),
    ← Finset.smul_sum, smul_smul, hsign, one_smul]
  symm
  refine Fintype.sum_equiv (finCongr (show k + (l + 1) = k + 1 + l by omega)).permCongr _ _
    fun sigma => ?_
  simp [Perm.sign_permCongr]

private lemma sum_sign_smul_insertNth_natAdd [ContinuousAdd F₂] [ContinuousConstSMul ℝ F₂]
    (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin (k + 1)]→L[ℝ] F₁) (psi : E [⋀^Fin (l + 1)]→L[ℝ] F₂) (v : E)
    (w : Fin (k + 1 + l) → E) (i : Fin (l + 1)) :
    (-1 : ℤ) ^ (Fin.natAdd (k + 1) i : ℕ) • ∑ τ : Perm (Fin (k + 1 + l)), Perm.sign τ •
      mu (phi fun a => Fin.insertNth (α := fun _ => E)
          (Fin.natAdd (k + 1) i : Fin (k + 1 + l + 1)) v (w ∘ τ) (Fin.castAdd (l + 1) a))
        (psi fun b => Fin.insertNth (α := fun _ => E)
          (Fin.natAdd (k + 1) i : Fin (k + 1 + l + 1)) v (w ∘ τ) (Fin.natAdd (k + 1) b)) =
      (-1 : ℝ) ^ (k + 1) • ∑ sigma : Perm (Fin (k + 1 + l)), Perm.sign sigma •
        mu (phi fun a => w (sigma (Fin.castAdd l a)))
          (psi.curryLeftTopological v fun b => w (sigma (Fin.natAdd (k + 1) b))) := by
  have hsign : (-1 : ℤ) ^ (Fin.natAdd (k + 1) i : ℕ) * (-1 : ℤ) ^ (i : ℕ) = (-1 : ℤ) ^ (k + 1) := by
    simp [pow_add, mul_assoc, ← mul_pow]
  simp_rw [Fin.insertNth_natAdd_apply_castAdd, Fin.insertNth_natAdd_comp_natAdd,
    ContinuousAlternatingMap.map_insertNth', ← curryLeftTopological_apply_apply]
  simp only [map_zsmul, smul_comm (Perm.sign _), ← Finset.smul_sum, smul_smul, hsign,
    Function.comp_apply]
  rw [← Int.cast_smul_eq_zsmul ℝ]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The interior product is an antiderivation of degree `-1` for the paired wedge:
`ι_v (φ ∧ ψ) = ι_v φ ∧ ψ + (-1) ^ (k + 1) • φ ∧ ι_v ψ` for a `(k + 1)`-form `φ`.
This is the topological counterpart of `ContinuousAlternatingMap.curryLeft_pairedWedge` and the
formula of Lee, *Introduction to Smooth Manifolds*, 2nd ed., Lemma 14.13. -/
theorem curryLeftTopological_pairedWedge
    [ContinuousAdd F₁] [ContinuousConstSMul ℝ F₁]
    [ContinuousAdd F₂] [ContinuousConstSMul ℝ F₂]
    (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hmu : Continuous (Function.uncurry fun x y ↦ mu x y))
    (phi : E [⋀^Fin (k + 1)]→L[ℝ] F₁)
    (psi : E [⋀^Fin (l + 1)]→L[ℝ] F₂) (v : E)
    (w : Fin (k + 1 + l) → E) :
    curryLeftTopological (n := k + 1 + l)
      (pairedWedge (k := k + 1) (l := l + 1) mu hmu phi psi) v w =
      pairedWedge (k := k) (l := l + 1) mu hmu (curryLeftTopological (n := k) phi v) psi
        (w ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) •
          pairedWedge (k := k + 1) (l := l) mu hmu phi (curryLeftTopological (n := l) psi v) w := by
  rw [curryLeftTopological_apply_apply, pairedWedge_apply, pairedWedge_apply, pairedWedge_apply]
  let g : (Fin (k + 1 + l + 1) → E) → F₃ := fun y =>
    mu (phi fun i => y (Fin.castAdd (l + 1) i))
      (psi fun j => y (Fin.natAdd (k + 1) j))
  have hexp := TauCeti.sum_sign_smul_cons_comp_eq_sum_insertNth
    (n := k + 1 + l) g v w
  simp only [g, Function.comp_apply] at hexp
  have hexp' : (∑ sigma : Perm (Fin (k + 1 + (l + 1))), Perm.sign sigma •
      mu (phi fun i =>
        Fin.cons (α := fun _ : Fin (k + 1 + l + 1) => E) v w
          (sigma (Fin.castAdd (l + 1) i)))
        (psi fun j =>
          Fin.cons (α := fun _ : Fin (k + 1 + l + 1) => E) v w
            (sigma (Fin.natAdd (k + 1) j)))) =
      ∑ j : Fin (k + 1 + l + 1), (-1 : ℤ) ^ (j : ℕ) •
        ∑ tau : Perm (Fin (k + 1 + l)), Perm.sign tau •
          mu (phi fun i => Fin.insertNth (α := fun _ => E) j v (w ∘ tau)
              (Fin.castAdd (l + 1) i))
            (psi fun q => Fin.insertNth (α := fun _ => E) j v (w ∘ tau)
              (Fin.natAdd (k + 1) q)) := by
    -- The paired-wedge expression uses the other parenthesization of the sum of degrees;
    -- `convert` transports the expansion across that definitional equality.
    convert hexp using 1
  have hsplit (f : Fin (k + 1 + l + 1) → F₃) :
      ∑ j, f j = ∑ i : Fin (k + 1), f (Fin.castAdd (l + 1) i) +
        ∑ i : Fin (l + 1), f (Fin.natAdd (k + 1) i) :=
    Fin.sum_univ_add (a := k + 1) (b := l + 1) f
  have hvecCons (x : E) (y : Fin (k + 1 + l) → E) :
      Matrix.vecCons x y = Fin.cons x y := rfl
  rw [hvecCons]
  rw [hexp', hsplit]
  simp only [sum_sign_smul_insertNth_castAdd, sum_sign_smul_insertNth_natAdd, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Nat.factorial_succ k, Nat.factorial_succ l]
  match_scalars <;> field_simp
end InteriorProduct

end ContinuousAlternatingMap
