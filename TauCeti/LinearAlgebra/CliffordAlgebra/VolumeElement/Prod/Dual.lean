/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Dual
public import TauCeti.LinearAlgebra.TensorProduct.Dual
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Dual

/-!
# Reverse duality of graded tensor products of complex Clifford modules

On the reverse-dual module `E*` (`AlgHom.cliffordReverseDual`), `Γ_V` acts by
`(-1) ^ (n / 2) • Γ_Eᵀ`. Comparing `complexProdTensor` of the reverse duals with the reverse dual
of `complexProdTensor` along `TensorProduct.dualDistrib ℂ E F` splits by the parity of `n / 2`:

* For `Even (n / 2)`, `dualDistrib ℂ E F` directly intertwines the two actions (with
  `dualDistribEquiv ℂ E F` conjugating them for finite-dimensional `E`, `F`).
* For `Odd (n / 2)`, `dualDistrib ℂ E F` intertwines the `-o₁`-graded product on `E* ⊗ F*` with
  the reverse dual of the `+o₁`-graded product; for even-dimensional `(W, o₂)`, precomposing with
  `1 ⊗ Γ_(F*)` restores `+o₁` (giving `lTensorComplexVolumeDualDistribEquiv` when `Q₂ w = -‖w‖²`
  and `E`, `F` are finite-dimensional).

## Main definitions and results

* `CliffordAlgebra.lTensorComplexVolumeDualDistribEquiv`: `E* ⊗ F* ≃ₗ[ℂ] (E ⊗ F)*` given by
  `1 ⊗ Γ_(F*)` followed by `dualDistribEquiv ℂ E F`.
* `CliffordAlgebra.dualDistrib_comp_complexProdTensor_of_even_div_two` and
  `CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_of_even_div_two`: the
  `Even (n / 2)` duality intertwining and conjugation laws.
* `CliffordAlgebra.dualDistrib_comp_complexProdTensor_neg_orientation_of_odd_div_two`,
  `CliffordAlgebra.dualDistrib_comp_lTensor_complexVolume_comp_complexProdTensor_of_odd_div_two`,
  and `CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_of_odd_div_two`: the
  `Odd (n / 2)` duality intertwining and conjugation laws.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module TensorProduct
open scoped TensorProduct

namespace CliffordAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- Common generator check: whenever `Γ_V` for an orientation `o₁'` acts on `E*` by `(ρ₁ Γ_V)ᵀ`,
`dualDistrib ℂ E F` intertwines `complexProdTensor` for `o₁'` on `E* ⊗ F*` with the reverse dual of
`complexProdTensor` for `o₁` on `(E ⊗ F)*`. -/
private theorem dualDistrib_comp_complexProdTensor_of_dualMap
    (o₁' : Orientation ℝ V (Fin n))
    (hdual : ρ₁.cliffordReverseDual (complexVolume Q₁ o₁') = (ρ₁ (complexVolume Q₁ o₁)).dualMap)
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    dualDistrib ℂ E F ∘ₗ
        complexProdTensor hQ o₁' hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a ∘ₗ dualDistrib ℂ E F := by
  rw [complexProdTensor_eq_comp, complexProdTensor_eq_comp,
    AlgHom.cliffordReverseDual_comp_map, AlgHom.comp_apply, AlgHom.comp_apply,
    ← AlgHom.dualDistrib_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂]
  congr 2
  exact AlgHom.cliffordProdTensor_congr rfl hdual rfl

/-! ### Even half-dimension (`n = 2ℓ`, `ℓ` even) -/

/-- **Reverse duality of `complexProdTensor` when `Even (n / 2)`.** Because `Γ_(E*) = Γ_Eᵀ`,
`TensorProduct.dualDistrib ℂ E F` intertwines the graded product of the reverse duals with the
reverse dual of the graded product on every Clifford element. -/
theorem dualDistrib_comp_complexProdTensor_of_even_div_two (heven : Even (n / 2))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    dualDistrib ℂ E F ∘ₗ
        complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a ∘ₗ dualDistrib ℂ E F :=
  dualDistrib_comp_complexProdTensor_of_dualMap hQ o₁ hQ₁ hn ρ₁ ρ₂ o₁
    (by rw [AlgHom.cliffordReverseDual_complexVolume, heven.neg_one_pow, one_smul]) a

/-- For finite-dimensional `E` and `F` and `Even (n / 2)`, `TensorProduct.dualDistribEquiv ℂ E F`
conjugates `complexProdTensor` of the reverse duals into the reverse dual of `complexProdTensor`. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj_of_even_div_two
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (heven : Even (n / 2))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a =
      (dualDistribEquiv ℂ E F).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a) := by
  refine LinearMap.ext fun Φ ↦ ?_
  obtain ⟨z, rfl⟩ := (dualDistribEquiv ℂ E F).surjective Φ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simpa only [← toLinearMap_dualDistribEquiv, LinearEquiv.coe_toLinearMap, LinearMap.comp_apply]
    using (LinearMap.congr_fun
      (dualDistrib_comp_complexProdTensor_of_even_div_two hQ o₁ hQ₁ hn ρ₁ ρ₂ heven a) z).symm

/-! ### Odd half-dimension (`n = 2ℓ`, `ℓ` odd) -/

/-- When `Odd (n / 2)` (for example a plane `n = 2`), `Γ_(E*) = -Γ_Eᵀ`, so `dualDistrib ℂ E F`
intertwines the `-o₁`-graded product of the reverse duals with the reverse dual of the `+o₁`-graded
product, for arbitrary `(W, Q₂)`. -/
theorem dualDistrib_comp_complexProdTensor_neg_orientation_of_odd_div_two (hodd : Odd (n / 2))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    dualDistrib ℂ E F ∘ₗ
        complexProdTensor hQ (-o₁) hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a ∘ₗ dualDistrib ℂ E F :=
  dualDistrib_comp_complexProdTensor_of_dualMap hQ o₁ hQ₁ hn ρ₁ ρ₂ (-o₁)
    (by
      rw [AlgHom.cliffordReverseDual_complexVolume, hodd.neg_one_pow,
        complexVolume_neg_orientation, map_neg]
      ext φ e; simp) a

section EvenSecondFactor

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))

/-- **Reverse duality of `complexProdTensor` when `Odd (n / 2)`.** When `W` is also oriented of
even dimension `m`, precomposing `dualDistrib ℂ E F` with `1 ⊗ Γ_(F*)` intertwines the `+o₁`-graded
product of the reverse duals with the reverse dual of the `+o₁`-graded product. -/
theorem dualDistrib_comp_lTensor_complexVolume_comp_complexProdTensor_of_odd_div_two
    (hodd : Odd (n / 2)) (hm : Even m) (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (dualDistrib ℂ E F ∘ₗ (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)) ∘ₗ
        complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a ∘ₗ
        (dualDistrib ℂ E F ∘ₗ
          (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)) := by
  have hflip : (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E) ∘ₗ
      complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a =
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a ∘ₗ
      (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E) := by
    simpa only [Module.End.mul_eq_comp] using
      lTensor_complexVolume_mul_complexProdTensor hQ o₁ hQ₁ hn
        ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual o₂ hm a
  rw [LinearMap.comp_assoc, hflip, ← LinearMap.comp_assoc,
    dualDistrib_comp_complexProdTensor_neg_orientation_of_odd_div_two hQ o₁ hQ₁ hn ρ₁ ρ₂ hodd a,
    LinearMap.comp_assoc]

variable (E) in
/-- For finite-dimensional `E` and `F` and `Q₂ w = -‖w‖²`, the twisted tensor-duality equivalence
`E* ⊗ F* ≃ₗ[ℂ] (E ⊗ F)*` given by `1 ⊗ Γ_(F*)` followed by `dualDistribEquiv ℂ E F`. -/
def lTensorComplexVolumeDualDistribEquiv [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) :
    (Dual ℂ E ⊗[ℂ] Dual ℂ F) ≃ₗ[ℂ] Dual ℂ (E ⊗[ℂ] F) :=
  ((LinearEquiv.ofInvolutive (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂))
      (ρ₂.cliffordReverseDual.involutive_complexVolume o₂ hQ₂)).lTensor (Dual ℂ E)).trans
    (dualDistribEquiv ℂ E F)

variable (E) in
/-- Underlying linear map of `lTensorComplexVolumeDualDistribEquiv`. -/
@[simp]
theorem toLinearMap_lTensorComplexVolumeDualDistribEquiv
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) :
    (lTensorComplexVolumeDualDistribEquiv E ρ₂ o₂ hQ₂).toLinearMap =
      dualDistrib ℂ E F ∘ₗ
        (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E) := by
  rw [lTensorComplexVolumeDualDistribEquiv, ← LinearEquiv.comp_coe,
    LinearEquiv.coe_lTensor, toLinearMap_dualDistribEquiv]
  refine congrArg (dualDistrib ℂ E F ∘ₗ ·) (congrArg (LinearMap.lTensor (Dual ℂ E)) ?_)
  exact LinearMap.ext fun x ↦ by rw [LinearEquiv.coe_toLinearMap, LinearEquiv.coe_ofInvolutive]

variable (E) in
/-- Forward evaluation of `lTensorComplexVolumeDualDistribEquiv`: applies `1 ⊗ Γ_(F*)`
followed by `TensorProduct.dualDistrib ℂ E F`. -/
@[simp]
theorem lTensorComplexVolumeDualDistribEquiv_apply
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (z : Dual ℂ E ⊗[ℂ] Dual ℂ F) :
    lTensorComplexVolumeDualDistribEquiv E ρ₂ o₂ hQ₂ z =
      dualDistrib ℂ E F
        ((ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E) z) := by
  rw [← LinearEquiv.coe_toLinearMap, toLinearMap_lTensorComplexVolumeDualDistribEquiv,
    LinearMap.comp_apply]

variable (E) in
/-- Inverse evaluation of `lTensorComplexVolumeDualDistribEquiv`: applies
`(TensorProduct.dualDistribEquiv ℂ E F).symm` followed by `1 ⊗ Γ_(F*)`. -/
@[simp]
theorem lTensorComplexVolumeDualDistribEquiv_symm_apply
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (Φ : Dual ℂ (E ⊗[ℂ] F)) :
    (lTensorComplexVolumeDualDistribEquiv E ρ₂ o₂ hQ₂).symm Φ =
      (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)
        ((dualDistribEquiv ℂ E F).symm Φ) := by
  rw [LinearEquiv.symm_apply_eq, lTensorComplexVolumeDualDistribEquiv_apply,
    ← LinearMap.lTensor_comp_apply]
  have hid : ρ₂.cliffordReverseDual (complexVolume Q₂ o₂) ∘ₗ
      ρ₂.cliffordReverseDual (complexVolume Q₂ o₂) = LinearMap.id :=
    LinearMap.ext (ρ₂.cliffordReverseDual.involutive_complexVolume o₂ hQ₂)
  rw [hid, LinearMap.lTensor_id, LinearMap.id_apply, ← toLinearMap_dualDistribEquiv]
  exact ((dualDistribEquiv ℂ E F).apply_symm_apply Φ).symm

variable (E) in
/-- Underlying linear map of `(lTensorComplexVolumeDualDistribEquiv E ρ₂ o₂ hQ₂).symm`. -/
@[simp]
theorem toLinearMap_lTensorComplexVolumeDualDistribEquiv_symm
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) :
    (lTensorComplexVolumeDualDistribEquiv E ρ₂ o₂ hQ₂).symm.toLinearMap =
      (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E) ∘ₗ
        (dualDistribEquiv ℂ E F).symm.toLinearMap :=
  LinearMap.ext (lTensorComplexVolumeDualDistribEquiv_symm_apply E ρ₂ o₂ hQ₂)

/-- For finite-dimensional `E` and `F`, `Odd (n / 2)`, `Even m`, and `Q₂ w = -‖w‖²`,
`lTensorComplexVolumeDualDistribEquiv` conjugates `complexProdTensor` of the reverse duals into
the reverse dual of `complexProdTensor`. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj_of_odd_div_two
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (hodd : Odd (n / 2)) (hm : Even m) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a =
      (lTensorComplexVolumeDualDistribEquiv E ρ₂ o₂ hQ₂).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a) := by
  refine LinearMap.ext fun Φ ↦ ?_
  obtain ⟨z, rfl⟩ := (lTensorComplexVolumeDualDistribEquiv E ρ₂ o₂ hQ₂).surjective Φ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simpa only [lTensorComplexVolumeDualDistribEquiv_apply, LinearMap.comp_apply] using
    (LinearMap.congr_fun
      (dualDistrib_comp_lTensor_complexVolume_comp_complexProdTensor_of_odd_div_two hQ o₁ hQ₁ hn
        ρ₁ ρ₂ o₂ hodd hm a) z).symm

end EvenSecondFactor

end CliffordAlgebra
