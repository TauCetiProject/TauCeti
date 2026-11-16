/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Dual
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.TensorProduct.Dual
-- Private: ring-generic reverse duality of `cliffordProdTensor` is used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Dual

/-!
# Reverse duality of `complexProdTensor`

Let `V` be an even-dimensional oriented real inner product space of dimension `n = 2ℓ` with
`Q₁ v = -‖v‖²`, let `(W, Q₂)` be any real quadratic space, and let `E`, `F` be complex Clifford
modules given by `ρ₁` and `ρ₂`. Their reverse duals `E*` and `F*` carry `ρ₁.cliffordReverseDual`
and `ρ₂.cliffordReverseDual` (`TauCeti/LinearAlgebra/CliffordAlgebra/Dual.lean`).

In `CliffordAlgebra.complexProdTensor`, the reverse-dual action `(E ⊗ F)*` uses the transposed
chirality `Γ_Eᵀ` (`AlgHom.dualDistrib_cliffordProdTensor` and
`AlgHom.cliffordReverseDual_cliffordProdTensor_eq_conj` in
`TauCeti/LinearAlgebra/CliffordAlgebra/Prod/Dual.lean`), whereas `complexProdTensor` of `E*` and
`F*` uses the intrinsic chirality `Γ_(E*) = (-1) ^ (n / 2) • Γ_Eᵀ`
(`AlgHom.cliffordReverseDual_complexVolume`):

* **Parity-uniform reverse duality**: scaling the orientation of `V` by `(-1 : ℝˣ) ^ (n / 2)`
  cancels `(-1) ^ (n / 2)` in all even dimensions, so `TensorProduct.dualDistrib ℂ E F` intertwines
  the `((-1 : ℝˣ) ^ (n / 2) • o₁)`-graded product of `E*` and `F*` with `(E ⊗ F)*` on every
  Clifford element (`CliffordAlgebra.dualDistrib_complexProdTensor`), and
  `TensorProduct.dualDistribEquiv ℂ E F` conjugates them when `E` and `F` are finite-dimensional
  (`CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj`).
* **When `Even (n / 2)` (`n ≡ 0 (mod 4)`)**: `(-1 : ℝˣ) ^ (n / 2) = 1`, so `dualDistrib ℂ E F`
  intertwines the `o₁`-graded actions directly
  (`CliffordAlgebra.dualDistrib_complexProdTensor_of_even` and
  `CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_of_even`).
* **When `Odd (n / 2)` (`n ≡ 2 (mod 4)`, e.g. a plane `n = 2`)**: `Γ_(E*) = -Γ_Eᵀ`.
  - Using `-o₁` on `E* ⊗ F*` restores `-Γ_(E*) = Γ_Eᵀ`
    (`CliffordAlgebra.dualDistrib_complexProdTensor_neg_orientation_of_odd`), while for the same
    orientation `o₁` a vector `(0, w)` of `W` acquires a minus sign
    (`CliffordAlgebra.dualDistrib_complexProdTensor_ι_inr_of_odd`).
  - When `W` is an oriented real inner product space of even dimension `m`, precomposing
    `dualDistrib ℂ E F` with `1 ⊗ Γ_(F*)` (`(ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor`)
    restores intertwining for `o₁` on every Clifford element
    (`CliffordAlgebra.dualDistrib_comp_lTensor_complexProdTensor_of_odd`), and gives a conjugation
    equivalence when `Q₂ w = -‖w‖²` and `E`, `F` are finite-dimensional
    (`CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_of_odd`).

## Main results

* `CliffordAlgebra.dualDistrib_complexProdTensor` and
  `CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj`: parity-uniform reverse duality
  with orientation `(-1 : ℝˣ) ^ (n / 2) • o₁`.
* `CliffordAlgebra.dualDistrib_complexProdTensor_of_even` and
  `CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_of_even`: `n ≡ 0 (mod 4)` case.
* `CliffordAlgebra.dualDistrib_complexProdTensor_neg_orientation_of_odd` and
  `CliffordAlgebra.dualDistrib_complexProdTensor_ι_inr_of_odd`: `n ≡ 2 (mod 4)` sign analysis.
* `CliffordAlgebra.dualDistrib_comp_lTensor_complexProdTensor_of_odd` and
  `CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_of_odd`: restoration by
  `1 ⊗ Γ_(F*)` when `Even m`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

noncomputable section

open Module TensorProduct

namespace CliffordAlgebra

section FirstFactor

private theorem cliffordReverseDual_comp_equivOfIsometry
    {M₁ M₂ S : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    {Q₁ : QuadraticForm ℂ M₁} {Q₂ : QuadraticForm ℂ M₂}
    [AddCommGroup S] [Module ℂ S] (e : Q₁.IsometryEquiv Q₂)
    (σ : CliffordAlgebra Q₂ →ₐ[ℂ] Module.End ℂ S) :
    (σ.comp (equivOfIsometry e).toAlgHom).cliffordReverseDual =
      σ.cliffordReverseDual.comp (equivOfIsometry e).toAlgHom :=
  (AlgHom.cliffordReverseDual_unique (σ.comp (equivOfIsometry e).toAlgHom)
    (σ.cliffordReverseDual.comp (equivOfIsometry e).toAlgHom) fun v ↦ by
      simp [equivOfIsometry_apply]).symm

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [AddCommGroup W] [Module ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

private theorem cliffordReverseDual_complexVolume_signed_orientation :
    ρ₁.cliffordReverseDual (complexVolume Q₁ ((-1 : ℝˣ) ^ (n / 2) • o₁)) =
      (ρ₁ (complexVolume Q₁ o₁)).dualMap := by
  ext φ e
  rcases Nat.even_or_odd (n / 2) with hn2 | hn2 <;>
    simp [hn2.neg_one_pow, Module.Ray.neg_units_smul]

/-! ### Parity-uniform reverse duality -/

private theorem complexProdTensor_signed_orientation_cliffordReverseDual :
    complexProdTensor hQ ((-1 : ℝˣ) ^ (n / 2) • o₁) hQ₁ hn
      ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual =
      (AlgHom.cliffordProdTensor ρ₁.cliffordReverseDual (ρ₁ (complexVolume Q₁ o₁)).dualMap
          (by
            rw [Module.End.mul_eq_comp, LinearMap.dualMap_comp_dualMap,
              ← Module.End.mul_eq_comp, map_complexVolume_mul_self o₁ hQ₁ ρ₁]
            exact LinearMap.dualMap_id)
          (AlgHom.dualMap_mul_cliffordReverseDual_ι ρ₁ _
            (map_complexVolume_mul_map_ι o₁ hn ρ₁)) ρ₂.cliffordReverseDual).comp
        (equivOfIsometry (TauCeti.baseChangeWithLpProdIsometryEquiv hQ ℂ)).toAlgHom := by
  rw [complexProdTensor_def]
  congr 1
  exact AlgHom.cliffordProdTensor_congr_grading ρ₁.cliffordReverseDual _ _ _
    ρ₂.cliffordReverseDual (cliffordReverseDual_complexVolume_signed_orientation o₁ ρ₁) _ _

/-- **Parity-uniform reverse duality of `complexProdTensor`**: scaling `o₁` by `(-1 : ℝˣ) ^ (n / 2)`
aligns `Γ_(E*)` with `Γ_Eᵀ` in every even dimension `n`, so `TensorProduct.dualDistrib ℂ E F`
intertwines `complexProdTensor` of the reverse duals with the reverse dual of `complexProdTensor`
on every Clifford element, with no finiteness assumption on `E`, `F`, or `W`. -/
theorem dualDistrib_complexProdTensor (a : CliffordAlgebra (Q.baseChange ℂ)) :
    dualDistrib ℂ E F ∘ₗ
        complexProdTensor hQ ((-1 : ℝˣ) ^ (n / 2) • o₁) hQ₁ hn
          ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a ∘ₗ dualDistrib ℂ E F := by
  rw [complexProdTensor_signed_orientation_cliffordReverseDual, complexProdTensor_def,
    cliffordReverseDual_comp_equivOfIsometry, AlgHom.comp_apply, AlgHom.comp_apply]
  exact AlgHom.dualDistrib_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
    (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂ _

/-- For finite-dimensional `E` and `F`, `TensorProduct.dualDistribEquiv ℂ E F` conjugates the
`((-1 : ℝˣ) ^ (n / 2) • o₁)`-graded product of `E*` and `F*` into the reverse dual of
`complexProdTensor`. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a =
      (dualDistribEquiv ℂ E F).conj
        (complexProdTensor hQ ((-1 : ℝˣ) ^ (n / 2) • o₁) hQ₁ hn
          ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a) := by
  rw [complexProdTensor_signed_orientation_cliffordReverseDual, complexProdTensor_def,
    cliffordReverseDual_comp_equivOfIsometry, AlgHom.comp_apply, AlgHom.comp_apply]
  exact AlgHom.cliffordReverseDual_cliffordProdTensor_eq_conj ρ₁ (ρ₁ (complexVolume Q₁ o₁))
    (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂ _

/-! ### `Even (n / 2)` (`n ≡ 0 (mod 4)`) -/

/-- **Reverse duality of `complexProdTensor` when `Even (n / 2)`**: because `Γ_(E*) = Γ_Eᵀ`,
`TensorProduct.dualDistrib ℂ E F` intertwines `complexProdTensor` of the reverse duals with the
reverse dual of `complexProdTensor` on every Clifford element, with no finiteness assumption on `E`
or `F`. -/
theorem dualDistrib_complexProdTensor_of_even (hn2 : Even (n / 2))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    dualDistrib ℂ E F ∘ₗ
        complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a ∘ₗ dualDistrib ℂ E F := by
  simpa [hn2.neg_one_pow] using dualDistrib_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a

/-- For finite-dimensional `E` and `F` and `Even (n / 2)`, `TensorProduct.dualDistribEquiv ℂ E F`
conjugates `complexProdTensor` of the reverse duals into the reverse dual of `complexProdTensor`. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj_of_even
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (hn2 : Even (n / 2))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a =
      (dualDistribEquiv ℂ E F).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a) := by
  simpa [hn2.neg_one_pow] using
    cliffordReverseDual_complexProdTensor_eq_conj hQ o₁ hQ₁ hn ρ₁ ρ₂ a

/-! ### `Odd (n / 2)` (`n ≡ 2 (mod 4)`) -/

/-- **Sign flip on `W`-vectors when `Odd (n / 2)`**: because `Γ_(E*) = -Γ_Eᵀ`, for the same
orientation `o₁` on both sides, `TensorProduct.dualDistrib ℂ E F` carries the `(0, w)` action on
`E* ⊗ F*` to minus the reverse-dual `(0, w)` action on `(E ⊗ F)*`. -/
theorem dualDistrib_complexProdTensor_ι_inr_of_odd (hn2 : Odd (n / 2)) (w : W) :
    dualDistrib ℂ E F ∘ₗ
        complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual
          (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) =
      -((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual
          (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) ∘ₗ dualDistrib ℂ E F) := by
  rw [AlgHom.cliffordReverseDual_ι, complexProdTensor_ι_one_tmul_toLp_inr,
    complexProdTensor_ι_one_tmul_toLp_inr]
  ext φ ψ e f
  simp [AlgHom.cliffordReverseDual_complexVolume, hn2.neg_one_pow]

/-- **Reverse duality with `-o₁` when `Odd (n / 2)`**: reversing `o₁` to `-o₁` on `E* ⊗ F*` cancels
`(-1) ^ (n / 2) = -1`, so `TensorProduct.dualDistrib ℂ E F` intertwines the `-o₁`-graded product of
`E*` and `F*` with `(E ⊗ F)*` for arbitrary `W`. -/
theorem dualDistrib_complexProdTensor_neg_orientation_of_odd (hn2 : Odd (n / 2))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    dualDistrib ℂ E F ∘ₗ
        complexProdTensor hQ (-o₁) hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a ∘ₗ dualDistrib ℂ E F := by
  simpa [hn2.neg_one_pow, Module.Ray.neg_units_smul] using
    dualDistrib_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a

end FirstFactor

section EvenSecondFactor

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
  [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))

/-- **Restoration of `o₁`-reverse duality by `1 ⊗ Γ_(F*)` when `Odd (n / 2)` and `Even m`**:
precomposing `TensorProduct.dualDistrib ℂ E F` with `1 ⊗ Γ_(F*)` intertwines `complexProdTensor`
of `E*` and `F*` (for `o₁`) with `(complexProdTensor ... ρ₁ ρ₂).cliffordReverseDual` on every
Clifford element. -/
theorem dualDistrib_comp_lTensor_complexProdTensor_of_odd (hn2 : Odd (n / 2)) (hm : Even m)
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (dualDistrib ℂ E F ∘ₗ
        (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)) ∘ₗ
        complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a ∘ₗ
        (dualDistrib ℂ E F ∘ₗ
          (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)) := by
  have hflip :=
    lTensor_complexVolume_comp_complexProdTensor_neg_orientation hQ (-o₁) hQ₁ hn
      ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual o₂ hm a
  rw [neg_neg o₁] at hflip
  rw [LinearMap.comp_assoc, hflip, ← LinearMap.comp_assoc,
    dualDistrib_complexProdTensor_neg_orientation_of_odd hQ o₁ hQ₁ hn ρ₁ ρ₂ hn2 a,
    LinearMap.comp_assoc]

/-- For finite-dimensional `E` and `F`, `Odd (n / 2)`, `Even m`, and `Q₂ w = -‖w‖²`, conjugating
`complexProdTensor` of the reverse duals by `(1 ⊗ Γ_(F*))` followed by `dualDistribEquiv ℂ E F`
recovers the reverse dual of `complexProdTensor`. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj_of_odd
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (hn2 : Odd (n / 2)) (hm : Even m)
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a =
      (((LinearEquiv.ofInvolutive (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂))
          (map_complexVolume_involutive o₂ hQ₂ ρ₂.cliffordReverseDual)).lTensor
            (Dual ℂ E)).trans (dualDistribEquiv ℂ E F)).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a) := by
  let e := ((LinearEquiv.ofInvolutive (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂))
      (map_complexVolume_involutive o₂ hQ₂ ρ₂.cliffordReverseDual)).lTensor
        (Dual ℂ E)).trans (dualDistribEquiv ℂ E F)
  have he : e.toLinearMap =
      dualDistrib ℂ E F ∘ₗ
        (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E) := by
    have hinv_coe :
        (LinearEquiv.ofInvolutive (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂))
          (map_complexVolume_involutive o₂ hQ₂ ρ₂.cliffordReverseDual)).toLinearMap =
        ρ₂.cliffordReverseDual (complexVolume Q₂ o₂) :=
      LinearMap.ext (congrFun (LinearEquiv.coe_ofInvolutive _ _))
    rw [LinearEquiv.coe_trans, toLinearMap_dualDistribEquiv, LinearEquiv.coe_lTensor, hinv_coe]
  apply LinearMap.ext
  intro Φ
  obtain ⟨z, rfl⟩ := e.surjective Φ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simpa only [LinearMap.comp_apply, ← he, LinearEquiv.coe_coe] using
    (LinearMap.congr_fun
      (dualDistrib_comp_lTensor_complexProdTensor_of_odd hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hn2 hm a) z).symm

end EvenSecondFactor

end CliffordAlgebra
