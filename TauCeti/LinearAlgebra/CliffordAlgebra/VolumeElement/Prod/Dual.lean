/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Dual
public import TauCeti.LinearAlgebra.TensorProduct.Dual
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality

/-!
# Reverse duality of graded tensor products of complex Clifford modules

Let `V` and `W` be real inner product spaces with `(V, o₁)` oriented of even dimension `n = 2ℓ`,
`Q₁ v = -‖v‖²`, and `Q (v, w) = Q₁ v + Q₂ w` on `WithLp 2 (V × W)`, and let `E` and `F` be complex
Clifford modules over `Q₁` and `Q₂`.

On the reverse-dual module `E*` (`AlgHom.cliffordReverseDual`), the normalized complex volume
element `Γ_V` acts by `(-1) ^ (n / 2) • Γ_Eᵀ` (`AlgHom.cliffordReverseDual_complexVolume`), while
in the reverse dual `(E ⊗ F)*` of the graded product `complexProdTensor`, the vector `(0, w)` acts
by `(Γ_E ⊗ c_F(w))ᵀ`. Comparing the two through the canonical pairing
`TensorProduct.dualDistrib ℂ E F : E* ⊗ F* →ₗ[ℂ] (E ⊗ F)*` splits by the parity of `ℓ = n / 2`:

* When `Even (n / 2)` (`n ≡ 0 [MOD 4]`), `Γ_(E*) = Γ_Eᵀ`, so `dualDistrib ℂ E F` directly
  intertwines `complexProdTensor` of the reverse duals with the reverse dual of `complexProdTensor`,
  with no assumptions on `W`, `Q₂`, or the dimensions of `E` and `F`. For finite-dimensional `E` and
  `F`, `TensorProduct.dualDistribEquiv ℂ E F` conjugates one action into the other.
* When `Odd (n / 2)` (`n ≡ 2 [MOD 4]`, for example a negative-metric plane `n = 2`),
  `Γ_(E*) = -Γ_Eᵀ`, so `dualDistrib ℂ E F` intertwines the `-o₁`-graded product on `E* ⊗ F*` with
  the reverse dual of the `+o₁`-graded product on `(E ⊗ F)*`. When `W` is also oriented of even
  dimension `m`, precomposing with `1 ⊗ Γ_(F*)` restores the `+o₁`-graded product
  (`lTensor_complexVolume_comp_complexProdTensor_neg_orientation`), giving the intertwiner
  `dualDistrib ℂ E F ∘ₗ (1 ⊗ Γ_(F*))` — an equivalence for finite-dimensional `E`, `F` when
  `Q₂ w = -‖w‖²`.

## Main definitions

* `CliffordAlgebra.cliffordReverseDualProdEquivOfOddDivTwo`: the linear equivalence
  `E* ⊗ F* ≃ₗ[ℂ] (E ⊗ F)*` given by `(1 ⊗ Γ_(F*))` followed by `dualDistribEquiv ℂ E F` when
  `Q₂ w = -‖w‖²` and `E`, `F` are finite-dimensional.

## Main results

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
  have hgen (z : ℂ ⊗[ℝ] WithLp 2 (V × W)) :
      dualDistrib ℂ E F ∘ₗ
          complexProdTensor hQ o₁' hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual
            (ι (Q.baseChange ℂ) z) =
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual
            (ι (Q.baseChange ℂ) (QuadraticMap.Isometry.id (Q.baseChange ℂ) z)) ∘ₗ
          dualDistrib ℂ E F := by
    induction z using TensorProduct.inductionOn with
    | tmul c x =>
      obtain ⟨⟨v, w⟩, rfl⟩ : ∃ p : V × W, WithLp.toLp 2 p = x :=
        ⟨WithLp.ofLp x, by simp⟩
      have hc : c ⊗ₜ[ℝ] WithLp.toLp 2 (v, w) =
          c • ((1 : ℂ) ⊗ₜ[ℝ] WithLp.toLp 2 (v, w)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp only [QuadraticMap.Isometry.id_apply, hc, map_smul, LinearMap.comp_smul,
        LinearMap.smul_comp]
      congr 1
      apply TensorProduct.ext'
      intro φ ψ
      apply TensorProduct.ext'
      intro e f
      simp [complexProdTensor_ι_one_tmul_toLp, hdual, LinearMap.rTensor]
    | add x y hx hy =>
      simp only [QuadraticMap.Isometry.id_apply] at hx hy ⊢
      simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hx, hy]
  simpa [CliffordAlgebra.map_id] using comp_eq_map_comp_of_forall_ι hgen a

/-! ### Even half-dimension (`n = 2ℓ`, `ℓ` even) -/

/-- **Reverse duality of `complexProdTensor` when `Even (n / 2)`.** Because `(-1) ^ (n / 2) = 1`,
`Γ_(E*) = Γ_Eᵀ`, and `TensorProduct.dualDistrib ℂ E F` intertwines the graded product of the
reverse duals with the reverse dual of the graded product on every Clifford element, with no
finiteness or metric assumption on `W`, `E`, or `F`. -/
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
  apply LinearMap.ext
  intro Φ
  obtain ⟨z, rfl⟩ := (dualDistribEquiv ℂ E F).surjective Φ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simpa only [LinearMap.comp_apply, ← toLinearMap_dualDistribEquiv, LinearEquiv.coe_coe] using
    (LinearMap.congr_fun
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
      ext φ e
      simp) a

section EvenSecondFactor

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))

/-- **Reverse duality of `complexProdTensor` when `Odd (n / 2)`.** When `W` is also oriented of
even dimension `m`, precomposing `dualDistrib ℂ E F` with `1 ⊗ Γ_(F*)`
(`(ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)`) intertwines the `+o₁`-graded
product of the reverse duals with the reverse dual of the `+o₁`-graded product. No finiteness on
`E`, `F` and no metric hypothesis on `Q₂` are needed. -/
theorem dualDistrib_comp_lTensor_complexVolume_comp_complexProdTensor_of_odd_div_two
    (hodd : Odd (n / 2)) (hm : Even m) (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (dualDistrib ℂ E F ∘ₗ (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)) ∘ₗ
        complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a =
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a ∘ₗ
        (dualDistrib ℂ E F ∘ₗ
          (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E)) := by
  have hflip := lTensor_complexVolume_comp_complexProdTensor_neg_orientation hQ (-o₁) hQ₁ hn
    ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual o₂ hm a
  rw [_root_.neg_neg o₁] at hflip
  rw [LinearMap.comp_assoc, hflip, ← LinearMap.comp_assoc,
    dualDistrib_comp_complexProdTensor_neg_orientation_of_odd_div_two hQ o₁ hQ₁ hn ρ₁ ρ₂ hodd a,
    LinearMap.comp_assoc]

variable (E) in
/-- For finite-dimensional `E` and `F` and `Q₂ w = -‖w‖²`, the twisted tensor-duality equivalence
`E* ⊗ F* ≃ₗ[ℂ] (E ⊗ F)*` given by `1 ⊗ Γ_(F*)` followed by `dualDistribEquiv ℂ E F`. -/
def cliffordReverseDualProdEquivOfOddDivTwo [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) :
    (Dual ℂ E ⊗[ℂ] Dual ℂ F) ≃ₗ[ℂ] Dual ℂ (E ⊗[ℂ] F) :=
  have hγF : ρ₂.cliffordReverseDual (complexVolume Q₂ o₂) ∘ₗ
      ρ₂.cliffordReverseDual (complexVolume Q₂ o₂) = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, complexVolume_mul_self o₂ hQ₂, map_one,
      Module.End.one_eq_id]
  ((LinearEquiv.ofLinearMap _ _ hγF hγF).lTensor (Dual ℂ E)).trans (dualDistribEquiv ℂ E F)

variable (E) in
/-- Underlying linear map of `cliffordReverseDualProdEquivOfOddDivTwo`. -/
@[simp]
theorem toLinearMap_cliffordReverseDualProdEquivOfOddDivTwo
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) :
    (cliffordReverseDualProdEquivOfOddDivTwo E ρ₂ o₂ hQ₂).toLinearMap =
      dualDistrib ℂ E F ∘ₗ
        (ρ₂.cliffordReverseDual (complexVolume Q₂ o₂)).lTensor (Dual ℂ E) := by
  ext φ ψ
  simp [cliffordReverseDualProdEquivOfOddDivTwo, mul_comm]

/-- For finite-dimensional `E` and `F`, `Odd (n / 2)`, `Even m`, and `Q₂ w = -‖w‖²`,
`cliffordReverseDualProdEquivOfOddDivTwo` conjugates `complexProdTensor` of the reverse duals into
the reverse dual of `complexProdTensor`. -/
theorem cliffordReverseDual_complexProdTensor_eq_conj_of_odd_div_two
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (hodd : Odd (n / 2)) (hm : Even m) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).cliffordReverseDual a =
      (cliffordReverseDualProdEquivOfOddDivTwo E ρ₂ o₂ hQ₂).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁.cliffordReverseDual ρ₂.cliffordReverseDual a) := by
  let U := cliffordReverseDualProdEquivOfOddDivTwo E ρ₂ o₂ hQ₂
  apply LinearMap.ext
  intro Φ
  obtain ⟨z, rfl⟩ := U.surjective Φ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  have hint := LinearMap.congr_fun
    (dualDistrib_comp_lTensor_complexVolume_comp_complexProdTensor_of_odd_div_two hQ o₁ hQ₁ hn
      ρ₁ ρ₂ o₂ hodd hm a) z
  simpa only [U, LinearMap.comp_apply,
    ← toLinearMap_cliffordReverseDualProdEquivOfOddDivTwo E ρ₂ o₂ hQ₂, LinearEquiv.coe_coe] using
    hint.symm

end EvenSecondFactor

end CliffordAlgebra
