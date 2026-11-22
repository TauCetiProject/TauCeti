/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Dual
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.ProdEquiv
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Dual
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Unit

/-!
# Reverse duality of `CliffordAlgebra.complexProdTensor`

For an even-dimensional oriented real inner product space `V` of dimension `n = 2ℓ` with
`Q₁ v = -‖v‖²`, the intrinsic chirality of the reverse dual `E*` is `Γ_(E*) = (-1) ^ (n / 2) Γ_Eᵀ`:

* **Unified reverse duality**: `TensorProduct.dualDistrib ℂ E F` intertwines `complexProdTensor`
  of `(E*, F*)` for `if Even (n / 2) then o₁ else -o₁` with
  `(complexProdTensor ρ₁ ρ₂).cliffordReverseDual` (`CliffordAlgebra.dualDistrib_complexProdTensor`,
  `CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj`).
* **When `Odd (n / 2)` (`n ≡ 2 (mod 4)`) and `W` is even-dimensional**: precomposing
  `TensorProduct.dualDistrib` with `1 ⊗ Γ_(F*)` restores `o₁`
  (`CliffordAlgebra.dualDistrib_comp_lTensor_complexProdTensor_of_odd_div_two`,
  `CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_of_odd_div_two`).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module TensorProduct

namespace CliffordAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] {n : ℕ} [Fact (finrank ℝ V = n)]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (o₁ : Orientation ℝ V (Fin n)) (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

private theorem cliffordReverseDual_complexVolume_if_even :
    ρ₁.cliffordReverseDual (complexVolume Q₁ (if Even (n / 2) then o₁ else -o₁)) =
      (ρ₁ (complexVolume Q₁ o₁)).dualMap := by
  split_ifs with h
  · rw [AlgHom.cliffordReverseDual_complexVolume, h.neg_one_pow, one_smul]
  · have ho : Odd (n / 2) := Nat.not_even_iff_odd.mp h
    rw [complexVolume_neg_orientation, map_neg, AlgHom.cliffordReverseDual_complexVolume,
      ho.neg_one_pow]
    ext φ; simp

/-- **Unified reverse duality of `CliffordAlgebra.complexProdTensor`**:
`TensorProduct.dualDistrib ℂ E F` intertwines `complexProdTensor` of `(E*, F*)` for
`if Even (n / 2) then o₁ else -o₁` with `(complexProdTensor hQ o₁ ...).cliffordReverseDual`,
without finiteness assumptions on `E`, `F`, or `W`. -/
theorem dualDistrib_complexProdTensor (x : CliffordAlgebra (Q.baseChange ℂ)) :
    dualDistrib ℂ E F ∘ₗ
        complexProdTensor hQ (if Even (n / 2) then o₁ else -o₁) hQ₁ hn
          ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual x =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual x ∘ₗ dualDistrib ℂ E F := by
  have hγ := cliffordReverseDual_complexVolume_if_even o₁ ρ₁
  have hmap :
      (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).toAlgHom =
        map ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ).toIsometry :=
    AlgHom.ext (equivOfIsometry_apply _)
  rw [complexProdTensor_eq_comp, complexProdTensor_eq_comp, hmap,
    AlgHom.cliffordReverseDual_comp_map, AlgHom.comp_apply, AlgHom.comp_apply]
  simpa only [hγ] using
    AlgHom.dualDistrib_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁)
      ρ₂ (map ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ).toIsometry x)

/-- **Unified reverse-dual isomorphism**: for finite-dimensional `E` and `F`,
`TensorProduct.dualDistribEquiv ℂ E F` conjugates `complexProdTensor` of `(E*, F*)` for
`if Even (n / 2) then o₁ else -o₁` to the reverse dual of `complexProdTensor`. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (x : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual x =
      (dualDistribEquiv ℂ E F).conj
        (complexProdTensor hQ (if Even (n / 2) then o₁ else -o₁) hQ₁ hn
          ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual x) := by
  have hγ := cliffordReverseDual_complexVolume_if_even o₁ ρ₁
  have hmap :
      (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).toAlgHom =
        map ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ).toIsometry :=
    AlgHom.ext (equivOfIsometry_apply _)
  rw [complexProdTensor_eq_comp, complexProdTensor_eq_comp, hmap,
    AlgHom.cliffordReverseDual_comp_map, AlgHom.comp_apply, AlgHom.comp_apply]
  simpa only [hγ] using
    AlgHom.cliffordReverseDual_cliffordProdTensor_eq_conj ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁)
      ρ₂ (map ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ).toIsometry x)

/-- **Restoring `o₁` when `Odd (n / 2)` and `W` is even-dimensional**: precomposing
`TensorProduct.dualDistrib ℂ E F` with `1 ⊗ Γ_(F*)` intertwines `complexProdTensor` of `(E*, F*)`
for `o₁` with the reverse dual of `complexProdTensor` for `o₁`. -/
theorem dualDistrib_comp_lTensor_complexProdTensor_of_odd_div_two
    [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
    (o₂ : Orientation ℝ W (Fin m)) (hm : Even m) (hndiv : Odd (n / 2))
    (x : CliffordAlgebra (Q.baseChange ℂ)) :
    (dualDistrib ℂ E F ∘ₗ
        (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)) ∘ₗ
        complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual x =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual x ∘ₗ
        (dualDistrib ℂ E F ∘ₗ
          (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)) := by
  have hdual := dualDistrib_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ x
  simp only [Nat.not_even_iff_odd.mpr hndiv, ↓reduceIte] at hdual
  rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp,
    lTensor_complexVolume_mul_complexProdTensor hQ o₁ hQ₁ hn
      ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual o₂ hm x,
    Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hdual, LinearMap.comp_assoc]

/-- **Reverse-dual isomorphism for `o₁` when `Odd (n / 2)` and `Even m`**: when also
`Q₂ w = -‖w‖²` and `E`, `F` are finite-dimensional, `(1 ⊗ Γ_(F*)) ≪≫ₗ dualDistribEquiv ℂ E F`
conjugates `complexProdTensor` of `(E*, F*)` for `o₁` to the reverse dual of `complexProdTensor`. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj_of_odd_div_two
    [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (o₂ : Orientation ℝ W (Fin m)) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m)
    (hndiv : Odd (n / 2)) (x : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual x =
      (((LinearEquiv.ofInvolutive (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂))
          (ρ₂.cliffordReverseDual.involutive_complexVolume o₂ hQ₂)).lTensor
            (Dual ℂ E)).trans (dualDistribEquiv ℂ E F)).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual x) := by
  have hconj := cliffordReverseDual_complexProdTensor_eq_conj hQ o₁ hQ₁ hn ρ₁ ρ₂ x
  simp only [Nat.not_even_iff_odd.mpr hndiv, ↓reduceIte] at hconj
  rw [← LinearEquiv.conj_trans, LinearEquiv.trans_apply, hconj]
  congr 1
  have h := AlgHom.congr_fun (conjAlgEquiv_lTensor_complexVolume_complexProdTensor hQ o₁ hQ₁ hn
    ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual o₂ hQ₂ hm) x
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, LinearEquiv.conjAlgEquiv_apply] at h
  exact h.symm

end CliffordAlgebra
