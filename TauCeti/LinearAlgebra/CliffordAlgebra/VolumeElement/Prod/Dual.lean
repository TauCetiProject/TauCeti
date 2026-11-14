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

* **When `Even (n / 2)` (`n ≡ 0 (mod 4)`)**: `TensorProduct.dualDistrib ℂ E F` intertwines
  `complexProdTensor` of `(E*, F*)` with `(complexProdTensor ρ₁ ρ₂).cliffordReverseDual` for the
  same orientation `o₁` (`CliffordAlgebra.dualDistrib_complexProdTensor_of_even_div_two`,
  `CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_of_even_div_two`).
* **When `Odd (n / 2)` (`n ≡ 2 (mod 4)`)**: `dualDistrib ℂ E F` intertwines `complexProdTensor` of
  `(E*, F*)` for `-o₁` with the reverse dual for `o₁`
  (`CliffordAlgebra.dualDistrib_complexProdTensor_neg_orientation_of_odd_div_two`,
  `CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_neg_orientation_of_odd_div_two`),
  and precomposing with `1 ⊗ Γ_(F*)` when `W` is even-dimensional restores `o₁`
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

private theorem cliffordReverseDual_equivOfIsometry_apply
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    {Qₐ : QuadraticForm ℂ M₁} {Qᵦ : QuadraticForm ℂ M₂} {S : Type*} [AddCommGroup S] [Module ℂ S]
    (ρ : CliffordAlgebra Qᵦ →ₐ[ℂ] Module.End ℂ S) (f : Qₐ.IsometryEquiv Qᵦ)
    (x : CliffordAlgebra Qₐ) :
    (ρ.comp (equivOfIsometry f).toAlgHom).cliffordReverseDual x =
      ρ.cliffordReverseDual (equivOfIsometry f x) := by
  have hcomp : ρ.cliffordReverseDual.comp (equivOfIsometry f).toAlgHom =
      (ρ.comp (equivOfIsometry f).toAlgHom).cliffordReverseDual :=
    AlgHom.cliffordReverseDual_unique _ _ fun v ↦ by simp [equivOfIsometry_apply]
  exact (AlgHom.congr_fun hcomp x).symm

/-- **Reverse duality when `n ≡ 0 (mod 4)` (`Even (n / 2)`)**: `TensorProduct.dualDistrib ℂ E F`
intertwines `complexProdTensor` of the reverse duals `(E*, F*)` with the reverse dual of
`complexProdTensor`, with no finiteness assumptions on `E`, `F`, or `W`. -/
theorem dualDistrib_complexProdTensor_of_even_div_two (hndiv : Even (n / 2))
    (x : CliffordAlgebra (Q.baseChange ℂ)) :
    dualDistrib ℂ E F ∘ₗ
        complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual x =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual x ∘ₗ dualDistrib ℂ E F := by
  have hγ : ρ₁.cliffordReverseDual (complexVolume Q₁ o₁) =
      (ρ₁ (complexVolume Q₁ o₁)).dualMap := by
    rw [AlgHom.cliffordReverseDual_complexVolume, hndiv.neg_one_pow, one_smul]
  rw [complexProdTensor_eq_cliffordProdTensor, complexProdTensor_eq_comp,
    cliffordReverseDual_equivOfIsometry_apply]
  simpa only [hγ] using
    AlgHom.dualDistrib_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (by rw [← map_mul, complexVolume_mul_self o₁ hQ₁, map_one])
      (fun v ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg])
      ρ₂ (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ) x)

/-- **Reverse-dual isomorphism when `Even (n / 2)`**: for finite-dimensional `E` and `F`,
`TensorProduct.dualDistribEquiv ℂ E F` conjugates `complexProdTensor` of `(E*, F*)` to the reverse
dual of `complexProdTensor`. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj_of_even_div_two
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (hndiv : Even (n / 2))
    (x : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual x =
      (dualDistribEquiv ℂ E F).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual x) := by
  refine LinearMap.ext fun Φ ↦ ?_
  obtain ⟨z, rfl⟩ := (dualDistribEquiv ℂ E F).surjective Φ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simpa only [LinearMap.comp_apply, ← toLinearMap_dualDistribEquiv, LinearEquiv.coe_coe] using
    (LinearMap.congr_fun
      (dualDistrib_complexProdTensor_of_even_div_two hQ o₁ hQ₁ hn ρ₁ ρ₂ hndiv x) z).symm

/-- **Reverse duality when `n ≡ 2 (mod 4)` (`Odd (n / 2)`)**: because `Γ_(E*) = -Γ_Eᵀ`,
`TensorProduct.dualDistrib ℂ E F` intertwines `complexProdTensor` of `(E*, F*)` for `-o₁` with the
reverse dual of `complexProdTensor` for `o₁`. -/
theorem dualDistrib_complexProdTensor_neg_orientation_of_odd_div_two (hndiv : Odd (n / 2))
    (x : CliffordAlgebra (Q.baseChange ℂ)) :
    dualDistrib ℂ E F ∘ₗ
        complexProdTensor hQ (-o₁) hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual x =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual x ∘ₗ dualDistrib ℂ E F := by
  have hγ : ρ₁.cliffordReverseDual (complexVolume Q₁ (-o₁)) =
      (ρ₁ (complexVolume Q₁ o₁)).dualMap := by
    rw [complexVolume_neg_orientation, map_neg, AlgHom.cliffordReverseDual_complexVolume,
      hndiv.neg_one_pow]; ext φ e; simp
  rw [complexProdTensor_eq_cliffordProdTensor, complexProdTensor_eq_comp,
    cliffordReverseDual_equivOfIsometry_apply]
  simpa only [hγ] using
    AlgHom.dualDistrib_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (by rw [← map_mul, complexVolume_mul_self o₁ hQ₁, map_one])
      (fun v ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg])
      ρ₂ (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ) x)

/-- **Reverse-dual isomorphism with `-o₁` when `Odd (n / 2)`**: for finite-dimensional `E` and `F`,
`TensorProduct.dualDistribEquiv ℂ E F` conjugates `complexProdTensor` of `(E*, F*)` for `-o₁` to the
reverse dual of `complexProdTensor` for `o₁`. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj_neg_orientation_of_odd_div_two
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (hndiv : Odd (n / 2))
    (x : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual x =
      (dualDistribEquiv ℂ E F).conj
        (complexProdTensor hQ (-o₁) hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual x) := by
  refine LinearMap.ext fun Φ ↦ ?_
  obtain ⟨z, rfl⟩ := (dualDistribEquiv ℂ E F).surjective Φ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simpa only [LinearMap.comp_apply, ← toLinearMap_dualDistribEquiv, LinearEquiv.coe_coe] using
    (LinearMap.congr_fun
      (dualDistrib_complexProdTensor_neg_orientation_of_odd_div_two hQ o₁ hQ₁ hn ρ₁ ρ₂ hndiv x)
      z).symm

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
  rw [LinearMap.comp_assoc,
    lTensor_complexVolume_comp_complexProdTensor hQ o₁ hQ₁ hn
      ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual o₂ hm x,
    ← LinearMap.comp_assoc,
    dualDistrib_complexProdTensor_neg_orientation_of_odd_div_two hQ o₁ hQ₁ hn ρ₁ ρ₂ hndiv x,
    LinearMap.comp_assoc]

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
          (map_complexVolume_involutive o₂ hQ₂ ρ₂.cliffordReverseDual)).lTensor
            (Dual ℂ E)).trans (dualDistribEquiv ℂ E F)).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual x) := by
  rw [← LinearEquiv.conj_trans, LinearEquiv.trans_apply,
    cliffordReverseDual_complexProdTensor_eq_conj_neg_orientation_of_odd_div_two
      hQ o₁ hQ₁ hn ρ₁ ρ₂ hndiv x]
  congr 1
  have h := AlgHom.congr_fun (conjAlgEquiv_lTensor_complexVolume_complexProdTensor hQ o₁ hQ₁ hn
    ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual o₂ hQ₂ hm) x
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, LinearEquiv.conjAlgEquiv_apply] at h
  refine LinearMap.ext fun z ↦ ?_
  rw [LinearEquiv.conj_apply_apply, ← h]; rfl

end CliffordAlgebra
