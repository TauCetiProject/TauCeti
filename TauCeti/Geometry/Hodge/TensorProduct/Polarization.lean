/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.HodgeForm
public import TauCeti.Geometry.Hodge.TensorProduct.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.Analysis.InnerProductSpace.TensorProduct
import TauCeti.LinearAlgebra.SesquilinearForm.TorsionFree

/-!
# Tensor products of polarized Hodge structures

If `Q` polarizes an integral pure Hodge structure `V` of weight `n` and `Q'` polarizes `V'` of
weight `n'`, then the tensor product form `Q ⊗ Q'` polarizes the tensor product `V ⊗ V'` of weight
`n + n'` (`TauCeti.Hodge.HodgeStructure.tensorProduct`, carried by the tensor product of the
lattices).

The Weil operator of the tensor product is the tensor product of the Weil operators, so the Hodge
form of `Q ⊗ Q'` is the tensor product of the Hodge forms of `Q` and `Q'`; as a tensor product of
positive definite Hermitian forms it is positive definite, which is the second Hodge–Riemann
relation. The first Hodge–Riemann relation holds because the Hodge component `H^{p,q}` of the
tensor product is spanned by the products of the components of `V` and `V'` whose bidegrees add
up to `(p,q)`. Positivity also gives nondegeneracy, which descends to the integral form because a
lattice carrying a nondegenerate form is torsion-free, hence flat over `ℤ`.

Consequently polarizable Hodge structures are closed under tensor products.

## Main declarations

* `TauCeti.Hodge.IsPolarization.tensorProduct`: the tensor product of two polarizing forms
  polarizes the tensor product.
* `TauCeti.Hodge.Polarization.tensorProduct`: the tensor product of two polarizations.
* `TauCeti.Hodge.Polarization.tensorProduct_hodgeForm_tmul_tmul`: the Hodge form on pure tensors.
* `TauCeti.Hodge.IsPolarizable.tensorProduct`: a tensor product of polarizable pure Hodge
  structures is polarizable.

## References

Deligne, *Théorie de Hodge II*, §2.1; Peters–Steenbrink, *Mixed Hodge Structures*, §2.1.
-/

public section

open scoped TensorProduct ComplexOrder

namespace TauCeti.Hodge

variable {V : Type*} {V' : Type*} {Vℂ : Type*} {V'ℂ : Type*}
variable [AddCommGroup V] [AddCommGroup V'] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} {ι'ℂ : V' →ₗ[ℤ] V'ℂ}
variable {hℂ : IsBaseChange ℂ ιℂ} {h'ℂ : IsBaseChange ℂ ι'ℂ} {n n' : ℤ}

/-! ### The tensor product of two polarizations -/

namespace IsPolarization

variable {hs : HodgeStructure hℂ n} {hs' : HodgeStructure h'ℂ n'}
variable {Q : LinearMap.BilinForm ℤ V} {Q' : LinearMap.BilinForm ℤ V'}

/-- The complexified tensor product form has the weight symmetry of weight `n + n'`. -/
private theorem tmul_symm_weight (h : IsPolarization hℂ hs Q) (h' : IsPolarization h'ℂ hs' Q')
    (x y : Vℂ ⊗[ℂ] V'ℂ) :
    (integralFormBaseChange hℂ Q).tmul (integralFormBaseChange h'ℂ Q') y x =
      ((n + n').negOnePow : ℤ) *
        (integralFormBaseChange hℂ Q).tmul (integralFormBaseChange h'ℂ Q') x y := by
  induction x with
  | tmul a b =>
    induction y with
    | tmul c d =>
      rw [LinearMap.BilinForm.tensorDistrib_tmul, LinearMap.BilinForm.tensorDistrib_tmul,
        smul_eq_mul, smul_eq_mul, h.complex_symm_weight a c, h'.complex_symm_weight b d,
        Int.negOnePow_add, Units.val_mul, Int.cast_mul]
      ring
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy', mul_add]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', mul_add]

/-- Two Hodge components of the tensor product pair to zero under the complexified tensor product
form unless their degrees add up to the weight. -/
private theorem tmul_eq_zero_of_mem_piece (h : IsPolarization hℂ hs Q)
    (h' : IsPolarization h'ℂ hs' Q') {q s : ℤ} (hqs : q + s ≠ n + n') {x y : Vℂ ⊗[ℂ] V'ℂ}
    (hx : x ∈ (HodgeStructureOn.tensorProduct hs hs').piece q)
    (hy : y ∈ (HodgeStructureOn.tensorProduct hs hs').piece s) :
    (integralFormBaseChange hℂ Q).tmul (integralFormBaseChange h'ℂ Q') x y = 0 := by
  rw [HodgeStructureOn.tensorProduct_piece_eq_iSup] at hx hy
  have hle : (⨆ r, Submodule.map₂ (TensorProduct.mk ℂ Vℂ V'ℂ) (hs.piece r)
      (hs'.piece (q - r))) ≤
      (⨆ t, Submodule.map₂ (TensorProduct.mk ℂ Vℂ V'ℂ) (hs.piece t)
        (hs'.piece (s - t))).dualAnnihilator.comap
          ((integralFormBaseChange hℂ Q).tmul (integralFormBaseChange h'ℂ Q')) := by
    refine iSup_le fun r ↦ Submodule.map₂_le.mpr fun a ha b hb ↦ ?_
    rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
    refine fun w hw ↦ LinearMap.mem_ker.mp ((iSup_le fun t ↦
      Submodule.map₂_le.mpr fun c hc d hd ↦ ?_ : _ ≤ LinearMap.ker _) hw)
    rw [LinearMap.mem_ker, TensorProduct.mk_apply, TensorProduct.mk_apply,
      LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul]
    by_cases hrt : r + t = n
    · rw [h'.orthogonal_piece (by omega) hb hd, zero_mul]
    · rw [h.orthogonal_piece hrt ha hc, mul_zero]
  exact (Submodule.mem_dualAnnihilator _).mp (Submodule.mem_comap.mp (hle hx)) y hy

/-- The Hodge form of the tensor product form is positive definite: it is the tensor product of
the Hodge forms of the two polarizations. -/
private theorem tmul_weilOperator_conj_self_pos (h : IsPolarization hℂ hs Q)
    (h' : IsPolarization h'ℂ hs' Q') {x : Vℂ ⊗[ℂ] V'ℂ} (hx : x ≠ 0) :
    0 < (integralFormBaseChange hℂ Q).tmul (integralFormBaseChange h'ℂ Q')
      ((HodgeStructureOn.tensorProduct hs hs').weilOperator
        (((latticeConjugation hℂ).tensorProduct (latticeConjugation h'ℂ)).toEquiv x)) x := by
  let P : Polarization hℂ hs := ⟨Q, h⟩
  let P' : Polarization h'ℂ hs' := ⟨Q', h'⟩
  -- `H u v = B (C (conj u)) v`, so the goal is `0 < H x x`.
  refine apply_self_pos_of_apply_tmul_tmul
    (H := ((integralFormBaseChange hℂ Q).tmul (integralFormBaseChange h'ℂ Q') ∘ₗ
      (HodgeStructureOn.tensorProduct hs hs').weilOperator) ∘ₛₗ
        ((latticeConjugation hℂ).tensorProduct (latticeConjugation h'ℂ)).toEquiv.toLinearMap)
    (fun a b c d ↦ ?_) P.isSymm_hodgeForm P'.isSymm_hodgeForm (fun _ ↦ P.hodgeForm_self_pos)
    (fun _ ↦ P'.hodgeForm_self_pos) hx
  rw [Polarization.hodgeForm_apply, Polarization.hodgeForm_apply, Polarization.Q_def,
    Polarization.Q_def, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Conjugation.tensorProduct_toEquiv_tmul, HodgeStructureOn.weilOperator_tensorProduct,
    TensorProduct.map_tmul, LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul,
    latticeConjugation_toEquiv_apply, latticeConjugation_toEquiv_apply, mul_comm]

/-- **The tensor product of two polarizing forms polarizes the tensor product.** If `Q`
polarizes a Hodge structure of weight `n` and `Q'` one of weight `n'`, then `Q ⊗ Q'` polarizes
their tensor product, of weight `n + n'`. -/
theorem tensorProduct (h : IsPolarization hℂ hs Q) (h' : IsPolarization h'ℂ hs' Q') :
    IsPolarization (isBaseChange_tensorLatticeMap hℂ h'ℂ) (hs.tensorProduct hs') (Q.tmul Q') := by
  -- Read `Q ⊗ Q'` through the canonical `ℤ`-module structure of `V ⊗[ℤ] V'`, the one the fields of
  -- `IsPolarization` are stated for; Mathlib's `tmul` uses the tensor-product one.
  set B : LinearMap.BilinForm ℤ (V ⊗[ℤ] V') := Q.tmul Q'
  have hBℂ : integralFormBaseChange (isBaseChange_tensorLatticeMap hℂ h'ℂ) B =
      (integralFormBaseChange hℂ Q).tmul (integralFormBaseChange h'ℂ Q') :=
    integralFormBaseChange_tmul hℂ h'ℂ Q Q'
  have hsymm : ∀ x y, B y x = ((n + n').negOnePow : ℤ) * B x y := by
    intro x y
    apply Int.cast_injective (α := ℂ)
    rw [Int.cast_mul, ← integralFormBaseChange_ι (isBaseChange_tensorLatticeMap hℂ h'ℂ) B,
      ← integralFormBaseChange_ι (isBaseChange_tensorLatticeMap hℂ h'ℂ) B, hBℂ]
    exact tmul_symm_weight h h' _ _
  refine ⟨hsymm, ?_, fun p x hx y hy ↦ ?_, fun p x hx hx0 ↦ ?_⟩
  · refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft fun x y hxy ↦ by
      rw [hsymm, hxy, mul_zero]).mpr fun v hv ↦ ?_
    -- The complexification of `v` pairs to zero with everything, hence with the conjugate of its
    -- Weil transform, so it vanishes by positivity of the Hodge form.
    have hzero : ∀ z, (integralFormBaseChange hℂ Q).tmul (integralFormBaseChange h'ℂ Q')
        (tensorLatticeMap ιℂ ι'ℂ v) z = 0 := by
      intro z
      induction z using (isBaseChange_tensorLatticeMap hℂ h'ℂ).inductionOn with
      | tmul w => rw [← hBℂ, integralFormBaseChange_ι, hv w, Int.cast_zero]
      | smul c z hz => rw [map_smul, hz, smul_zero]
      | add z z' hz hz' => rw [map_add, hz, hz', add_zero]
    have hι : tensorLatticeMap ιℂ ι'ℂ v = 0 := by
      by_contra hne
      have hpos := tmul_weilOperator_conj_self_pos h h' hne
      rw [tmul_symm_weight h h', hzero, mul_zero] at hpos
      exact lt_irrefl 0 hpos
    -- A lattice carrying a nondegenerate form is torsion-free, hence flat, so its
    -- complexification is injective.
    have := h.nondegenerate.1.isTorsionFree
    have := h'.nondegenerate.1.isTorsionFree
    exact tensorLatticeMap_injective hℂ h'ℂ (hι.trans (map_zero _).symm)
  · rw [HodgeStructure.tensorProduct_F, HodgeStructureOn.F_eq_iSup_piece] at hx hy
    rw [hBℂ]
    have hle : (⨆ q, ⨆ (_ : p ≤ q), (HodgeStructureOn.tensorProduct hs hs').piece q) ≤
        (⨆ s, ⨆ (_ : n + n' + 1 - p ≤ s),
          (HodgeStructureOn.tensorProduct hs hs').piece s).dualAnnihilator.comap
            ((integralFormBaseChange hℂ Q).tmul (integralFormBaseChange h'ℂ Q')) := by
      refine iSup_le fun q ↦ iSup_le fun hq x hx ↦ ?_
      rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
      exact fun w hw ↦ LinearMap.mem_ker.mp ((iSup_le fun s ↦ iSup_le fun hs y hy ↦
        tmul_eq_zero_of_mem_piece h h' (by omega) hx hy : _ ≤ LinearMap.ker _) hw)
    exact (Submodule.mem_dualAnnihilator _).mp (Submodule.mem_comap.mp (hle hx)) y hy
  · rw [HodgeStructure.tensorProduct_piece] at hx
    rw [hBℂ, ← latticeConjugation_toEquiv_apply (isBaseChange_tensorLatticeMap hℂ h'ℂ),
      latticeConjugation_tensorProduct hℂ h'ℂ,
      ← (HodgeStructureOn.tensorProduct hs hs').apply_weilOperator_conj_self_of_mem_piece _
        (tmul_symm_weight h h') hx]
    exact tmul_weilOperator_conj_self_pos h h' hx0

end IsPolarization

variable {hs : HodgeStructure hℂ n} {hs' : HodgeStructure h'ℂ n'}

/-- The tensor product of two polarizations of pure Hodge structures. -/
noncomputable def Polarization.tensorProduct (P : Polarization hℂ hs)
    (P' : Polarization h'ℂ hs') :
    Polarization (isBaseChange_tensorLatticeMap hℂ h'ℂ) (hs.tensorProduct hs') where
  Qint := P.Qint.tmul P'.Qint
  isPolarization := P.isPolarization.tensorProduct P'.isPolarization

/-- The integral form of a tensor product of polarizations is the tensor product form. -/
@[simp]
theorem Polarization.tensorProduct_Qint (P : Polarization hℂ hs) (P' : Polarization h'ℂ hs') :
    (P.tensorProduct P').Qint = P.Qint.tmul P'.Qint :=
  (rfl)

/-- The complex form of a tensor product of polarizations is the tensor product form. -/
@[simp]
theorem Polarization.tensorProduct_Q (P : Polarization hℂ hs) (P' : Polarization h'ℂ hs') :
    (P.tensorProduct P').Q = P.Q.tmul P'.Q := by
  rw [Polarization.Q_def, Polarization.Q_def, Polarization.Q_def, Polarization.tensorProduct_Qint,
    integralFormBaseChange_tmul]

/-- The Hodge form of a tensor product of polarizations is the product of their Hodge forms on
pure tensors. -/
@[simp]
theorem Polarization.tensorProduct_hodgeForm_tmul_tmul (P : Polarization hℂ hs)
    (P' : Polarization h'ℂ hs') (a c : Vℂ) (b d : V'ℂ) :
    (P.tensorProduct P').hodgeForm (a ⊗ₜ[ℂ] b) (c ⊗ₜ[ℂ] d) =
      P.hodgeForm a c * P'.hodgeForm b d := by
  have hweil : (hs.tensorProduct hs').weilOperator =
      TensorProduct.map hs.weilOperator hs'.weilOperator := by
    refine ((hs.tensorProduct hs').weilOperator_unique _ fun p x hx ↦ ?_).symm
    rw [← HodgeStructureOn.weilOperator_tensorProduct hs hs']
    rw [HodgeStructure.tensorProduct_piece] at hx
    exact (HodgeStructureOn.tensorProduct hs hs').weilOperator_apply_of_mem hx
  rw [Polarization.hodgeForm_apply, Polarization.hodgeForm_apply,
    Polarization.hodgeForm_apply, Polarization.tensorProduct_Q,
    latticeConj_tensorLatticeMap_tmul hℂ h'ℂ, hweil,
    TensorProduct.map_tmul, LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul]
  exact mul_comm _ _

/-- **Polarizable Hodge structures are closed under tensor products.** -/
theorem IsPolarizable.tensorProduct (h : IsPolarizable hℂ hs) (h' : IsPolarizable h'ℂ hs') :
    IsPolarizable (isBaseChange_tensorLatticeMap hℂ h'ℂ) (hs.tensorProduct hs') := by
  obtain ⟨P⟩ := isPolarizable_iff_nonempty.1 h
  obtain ⟨P'⟩ := isPolarizable_iff_nonempty.1 h'
  exact (P.tensorProduct P').isPolarizable

end TauCeti.Hodge
