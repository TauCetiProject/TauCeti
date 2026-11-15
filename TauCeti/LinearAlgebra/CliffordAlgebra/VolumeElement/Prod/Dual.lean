/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Dual
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Eigenspace
public import TauCeti.LinearAlgebra.TensorProduct.Dual

/-!
# Reverse duality of `complexProdTensor`

Let `V` be an even-dimensional oriented real inner product space of dimension `n = 2ℓ` with
`Q₁ v = -‖v‖²`, let `(W, Q₂)` be any real inner product space, and let `E`, `F` be complex Clifford
modules given by `ρ₁` and `ρ₂`. Their reverse duals `E*` and `F*` carry `ρ₁.cliffordReverseDual`
and `ρ₂.cliffordReverseDual` (`TauCeti/LinearAlgebra/CliffordAlgebra/Dual.lean`).

In `CliffordAlgebra.complexProdTensor`, the reverse-dual action `(E ⊗ F)*` uses the transposed
chirality `Γ_Eᵀ`, whereas `complexProdTensor` of `E*` and `F*` uses the intrinsic chirality
`Γ_(E*) = (-1) ^ (n / 2) • Γ_Eᵀ` (`AlgHom.cliffordReverseDual_complexVolume`):

* **When `Even (n / 2)` (`n ≡ 0 (mod 4)`)**: `Γ_(E*) = Γ_Eᵀ`, so the canonical pairing
  `TensorProduct.dualDistrib ℂ E F : E* ⊗ F* →ₗ[ℂ] (E ⊗ F)*` intertwines the two actions directly
  on every Clifford element (`CliffordAlgebra.dualDistrib_complexProdTensor_of_even`), without any
  finiteness assumption. For finite-dimensional `E` and `F`, `TensorProduct.dualDistribEquiv ℂ E F`
  identifies the two actions by conjugation
  (`CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_of_even`).
* **When `Odd (n / 2)` (`n ≡ 2 (mod 4)`, e.g. a plane `n = 2`)**: `Γ_(E*) = -Γ_Eᵀ`.
  - Using `-o₁` on `E* ⊗ F*` restores `-Γ_(E*) = Γ_Eᵀ`, so `dualDistrib ℂ E F` intertwines the
    `-o₁`-graded product of `E*` and `F*` with `(E ⊗ F)*` for arbitrary `W`
    (`CliffordAlgebra.dualDistrib_complexProdTensor_neg_orientation_of_odd`), while for the same
    orientation `o₁` a vector `(0, w)` of `W` acquires a minus sign
    (`CliffordAlgebra.dualDistrib_complexProdTensor_ι_inr_of_odd`).
  - When `W` also has even dimension `m` (`o₂ : Orientation ℝ W (Fin m)`), precomposing
    `dualDistrib ℂ E F` with `1 ⊗ Γ_(F*)` (`(ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor`)
    restores intertwining for `o₁` on every Clifford element
    (`CliffordAlgebra.dualDistrib_comp_lTensor_complexProdTensor_of_odd`), and gives a conjugation
    equivalence when `Q₂ w = -‖w‖²` and `E`, `F` are finite-dimensional
    (`CliffordAlgebra.cliffordReverseDual_complexProdTensor_eq_conj_of_odd`).

## Main results

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

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

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
  induction a using CliffordAlgebra.induction with
  | algebraMap z =>
    ext φ ψ e f
    simp [Algebra.algebraMap_eq_smul_one]
  | ι z =>
    induction z using TensorProduct.inductionOn with
    | tmul c x =>
      let v := (WithLp.ofLp x).1
      let w := (WithLp.ofLp x).2
      have hcx : c ⊗ₜ[ℝ] x = c • ((1 : ℂ) ⊗ₜ[ℝ] WithLp.toLp 2 (v, w)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hcx, map_smul, map_smul, map_smul, LinearMap.comp_smul, LinearMap.smul_comp]
      congr 1
      rw [AlgHom.cliffordReverseDual_ι, complexProdTensor_ι_one_tmul_toLp,
        complexProdTensor_ι_one_tmul_toLp]
      ext φ ψ e f
      simp [AlgHom.cliffordReverseDual_complexVolume, hn2.neg_one_pow, LinearMap.rTensor]
    | add y z hy hz =>
      simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hy, hz]
  | add a b ha hb =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, ha, hb]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha]
    rw [LinearMap.comp_assoc, hb, ← LinearMap.comp_assoc]

/-- For finite-dimensional `E` and `F` and `Even (n / 2)`, `TensorProduct.dualDistribEquiv ℂ E F`
conjugates `complexProdTensor` of the reverse duals into the reverse dual of `complexProdTensor`. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj_of_even
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (hn2 : Even (n / 2))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a =
      (dualDistribEquiv ℂ E F).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a) := by
  apply LinearMap.ext
  intro Φ
  obtain ⟨z, rfl⟩ := (dualDistribEquiv ℂ E F).surjective Φ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simpa only [LinearMap.comp_apply, ← toLinearMap_dualDistribEquiv, LinearEquiv.coe_coe] using
    (LinearMap.congr_fun (dualDistrib_complexProdTensor_of_even hQ o₁ hQ₁ hn ρ₁ ρ₂ hn2 a) z).symm

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
  induction a using CliffordAlgebra.induction with
  | algebraMap z =>
    ext φ ψ e f
    simp [Algebra.algebraMap_eq_smul_one]
  | ι z =>
    induction z using TensorProduct.inductionOn with
    | tmul c x =>
      let v := (WithLp.ofLp x).1
      let w := (WithLp.ofLp x).2
      have hcx : c ⊗ₜ[ℝ] x = c • ((1 : ℂ) ⊗ₜ[ℝ] WithLp.toLp 2 (v, w)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hcx, map_smul, map_smul, map_smul, LinearMap.comp_smul, LinearMap.smul_comp]
      congr 1
      rw [AlgHom.cliffordReverseDual_ι, complexProdTensor_ι_one_tmul_toLp,
        complexProdTensor_ι_one_tmul_toLp]
      ext φ ψ e f
      simp [AlgHom.cliffordReverseDual_complexVolume, hn2.neg_one_pow, LinearMap.rTensor]
    | add y z hy hz =>
      simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hy, hz]
  | add a b ha hb =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, ha, hb]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha]
    rw [LinearMap.comp_assoc, hb, ← LinearMap.comp_assoc]

section EvenSecondFactor

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))

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
          (involutive_apply_complexVolume o₂ hQ₂ ρ₂.cliffordReverseDual)).lTensor
            (Dual ℂ E)).trans (dualDistribEquiv ℂ E F)).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a) := by
  let e := ((LinearEquiv.ofInvolutive (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂))
      (involutive_apply_complexVolume o₂ hQ₂ ρ₂.cliffordReverseDual)).lTensor
        (Dual ℂ E)).trans (dualDistribEquiv ℂ E F)
  have he : e.toLinearMap =
      dualDistrib ℂ E F ∘ₗ
        (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E) := by
    ext φ ψ x y
    simp [e, LinearEquiv.lTensor, mul_comm]
  apply LinearMap.ext
  intro Φ
  obtain ⟨z, rfl⟩ := e.surjective Φ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simpa only [LinearMap.comp_apply, ← he, LinearEquiv.coe_coe] using
    (LinearMap.congr_fun
      (dualDistrib_comp_lTensor_complexProdTensor_of_odd hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hn2 hm a) z).symm

end EvenSecondFactor

end CliffordAlgebra
