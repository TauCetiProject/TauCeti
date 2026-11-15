/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Dual
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Neg
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Dual
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic

/-!
# Reverse duality of the graded tensor product of complex Clifford modules

Let `V` be an oriented real inner product space of even dimension `n = 2ℓ` with `Q₁ v = -‖v‖²`. By
`AlgHom.cliffordReverseDual_complexVolume`, `Γ_V` acts on the reverse dual `E*` by
`(-1) ^ ℓ Γ_Eᵀ` (`ℓ = n / 2`), whereas `AlgHom.dualDistrib_cliffordProdTensor` uses `Γ_Eᵀ`. The
comparison between `E* ⊗ F*` and `(E ⊗ F)*` therefore splits by the parity of `ℓ = n / 2`:

* **`Even (n / 2)`**: `Γ_(E*) = Γ_Eᵀ`, so `TensorProduct.dualDistrib ℂ E F` intertwines the two
  actions directly (and `dualDistribEquiv` conjugates them when `E`, `F` are finite-dimensional).
* **`Odd (n / 2)`**: `Γ_(E*) = -Γ_Eᵀ`, negating `(0, w)`; when `W` is even-dimensional, composing
  on the right with `1 ⊗ Γ_(F*)` restores the sign on the entire Clifford algebra.

## Main results

* `CliffordAlgebra.dualDistrib_complexProdTensor_of_even` and
  `CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_of_even`: `Even (n / 2)` case.
* `CliffordAlgebra.dualDistrib_complexProdTensor_ι_inr_of_odd`,
  `CliffordAlgebra.dualDistrib_comp_lTensor_complexProdTensor_of_odd`, and
  `CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_of_odd`: `Odd (n / 2)` case.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module TensorProduct

namespace CliffordAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {n : ℕ} [Fact (finrank ℝ V = n)]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (o₁ : Orientation ℝ V (Fin n)) (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

section EvenHalfRank

/-- **Reverse duality for `Even (n / 2)`**: when `n / 2` is even, `TensorProduct.dualDistrib ℂ E F`
intertwines the graded product of the reverse duals with the reverse dual of the graded product,
without finiteness of `E`, `F` or assumptions on `W`. -/
theorem dualDistrib_complexProdTensor_of_even (hℓ : Even (n / 2))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    dualDistrib ℂ E F ∘ₗ
        complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a ∘ₗ dualDistrib ℂ E F := by
  have hγ := map_complexVolume_mul_self o₁ hQ₁ ρ₁
  have hγρ := map_complexVolume_mul_map_ι o₁ hn ρ₁
  have hdual : ρ₁.cliffordReverseDual (complexVolume Q₁ o₁) =
      (ρ₁ (complexVolume Q₁ o₁)).dualMap := by
    rw [AlgHom.cliffordReverseDual_complexVolume, hℓ.neg_one_pow, one_smul]
  rw [complexProdTensor_def, complexProdTensor_def, AlgHom.cliffordReverseDual_comp_equivOfIsometry,
    AlgHom.comp_apply, AlgHom.comp_apply,
    AlgHom.cliffordProdTensor_congr_grading ρ₁.cliffordReverseDual _ _ _ ρ₂.cliffordReverseDual
      hdual (by rw [Module.End.mul_eq_comp, LinearMap.dualMap_comp_dualMap,
          ← Module.End.mul_eq_comp, hγ]; exact LinearMap.dualMap_id)
      (AlgHom.dualMap_mul_cliffordReverseDual_ι ρ₁ _ hγρ)]
  exact AlgHom.dualDistrib_cliffordProdTensor ρ₁ _ hγ hγρ ρ₂ _

/-- For finite-dimensional `E` and `F` and `Even (n / 2)`, `TensorProduct.dualDistribEquiv ℂ E F`
conjugates the graded product of the reverse duals into the reverse dual of the graded product. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj_of_even [Module.Finite ℂ E]
    [Module.Finite ℂ F] (hℓ : Even (n / 2)) (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a =
      (dualDistribEquiv ℂ E F).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a) := by
  refine LinearMap.ext fun Φ ↦ ?_
  obtain ⟨z, rfl⟩ := (dualDistribEquiv ℂ E F).surjective Φ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simpa only [LinearMap.comp_apply, ← toLinearMap_dualDistribEquiv, LinearEquiv.coe_coe] using
    (LinearMap.congr_fun (dualDistrib_complexProdTensor_of_even hQ o₁ hQ₁ hn ρ₁ ρ₂ hℓ a) z).symm

end EvenHalfRank

section OddHalfRank

/-- When `n / 2` is odd (for instance `n = 2`), `Γ_(E*) = -Γ_Eᵀ`, so the unadjusted pairing
`TensorProduct.dualDistrib ℂ E F` carries the generator `(0, w)` on `E* ⊗ F*` to minus its
reverse-dual action on `(E ⊗ F)*`. -/
theorem dualDistrib_complexProdTensor_ι_inr_of_odd (hℓ : Odd (n / 2)) (w : W)
    (z : Dual ℂ E ⊗[ℂ] Dual ℂ F) :
    dualDistrib ℂ E F
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual
          (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) z) =
      -((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual
        (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) (dualDistrib ℂ E F z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul φ ψ =>
    exact TensorProduct.ext' fun _ _ ↦ by
      simp [AlgHom.cliffordReverseDual_complexVolume, hℓ.neg_one_pow]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, neg_add]

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
  (o₂ : Orientation ℝ W (Fin m)) (hm : Even m)

include hm in
/-- **Reverse duality for `Odd (n / 2)`**: when `n / 2` is odd and `W` is even-dimensional,
composing `TensorProduct.dualDistrib ℂ E F` with `1 ⊗ Γ_(F*)` intertwines the graded product of the
reverse duals with the reverse dual of the graded product on the entire Clifford algebra. -/
theorem dualDistrib_comp_lTensor_complexProdTensor_of_odd (hℓ : Odd (n / 2))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (dualDistrib ℂ E F ∘ₗ
        (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)) ∘ₗ
        complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a ∘ₗ
        (dualDistrib ℂ E F ∘ₗ
          (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)) := by
  have hγ := map_complexVolume_mul_self o₁ hQ₁ ρ₁
  have hγρ := map_complexVolume_mul_map_ι o₁ hn ρ₁
  let γ' : Module.End ℂ (Dual ℂ E) := (ρ₁ (complexVolume Q₁ o₁)).dualMap
  have hγ' : γ' * γ' = 1 := by
    rw [Module.End.mul_eq_comp, LinearMap.dualMap_comp_dualMap, ← Module.End.mul_eq_comp, hγ]
    exact LinearMap.dualMap_id
  have hγ'ρ := AlgHom.dualMap_mul_cliffordReverseDual_ι ρ₁ _ hγρ
  have hdual : ρ₁.cliffordReverseDual (complexVolume Q₁ o₁) = -γ' := by
    ext φ; simp [AlgHom.cliffordReverseDual_complexVolume, hℓ.neg_one_pow, γ']
  rw [complexProdTensor_def, complexProdTensor_def, AlgHom.cliffordReverseDual_comp_equivOfIsometry,
    AlgHom.comp_apply, AlgHom.comp_apply,
    AlgHom.cliffordProdTensor_congr_grading ρ₁.cliffordReverseDual _ _ _ ρ₂.cliffordReverseDual
      hdual (LinearMap.ext fun φ ↦ by simpa using DFunLike.congr_fun hγ' φ)
      (fun v ↦ LinearMap.ext fun φ ↦ by
        simpa [neg_eq_iff_eq_neg] using DFunLike.congr_fun (hγ'ρ v) φ),
    LinearMap.comp_assoc,
    AlgHom.lTensor_comp_cliffordProdTensor_neg _ _ hγ' hγ'ρ _
      (map_complexVolume_mul_map_ι o₂ hm ρ₂.cliffordReverseDual),
    ← LinearMap.comp_assoc, AlgHom.dualDistrib_cliffordProdTensor ρ₁ _ hγ hγρ ρ₂,
    LinearMap.comp_assoc]

include hm in
/-- For finite-dimensional `E` and `F`, `Odd (n / 2)`, `Even m`, and `Q₂ w = -‖w‖²`, composing
`1 ⊗ Γ_(F*)` with `TensorProduct.dualDistribEquiv ℂ E F` conjugates the graded product of the
reverse duals into the reverse dual of the graded product. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj_of_odd [Module.Finite ℂ E]
    [Module.Finite ℂ F] (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hℓ : Odd (n / 2))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a =
      (((LinearEquiv.ofInvolutive (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂))
          (map_complexVolume_involutive o₂ hQ₂ ρ₂.cliffordReverseDual)).lTensor (Dual ℂ E)).trans
        (dualDistribEquiv ℂ E F)).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a) := by
  let e := ((LinearEquiv.ofInvolutive (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂))
    (map_complexVolume_involutive o₂ hQ₂ ρ₂.cliffordReverseDual)).lTensor (Dual ℂ E)).trans
    (dualDistribEquiv ℂ E F)
  refine LinearMap.ext fun Φ ↦ ?_
  obtain ⟨z, rfl⟩ := e.surjective Φ
  have hl (u : Dual ℂ E ⊗[ℂ] Dual ℂ F) : e u = (dualDistrib ℂ E F ∘ₗ
      (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)) u := by
    induction u using TensorProduct.inductionOn with
    | tmul x y => simp [e, ← toLinearMap_dualDistribEquiv]
    | add x y hx hy => simp [hx, hy]
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, hl, hl]
  exact (LinearMap.congr_fun
    (dualDistrib_comp_lTensor_complexProdTensor_of_odd hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm hℓ a) z).symm

end OddHalfRank

end CliffordAlgebra
