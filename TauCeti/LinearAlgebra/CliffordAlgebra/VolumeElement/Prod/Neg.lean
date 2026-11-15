/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Neg
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic

/-!
# Orientation reversal in the graded tensor product of complex Clifford modules

Reversing the orientation `o₁` of the even-dimensional space `V` negates its chirality `Γ_V`, so
in `CliffordAlgebra.complexProdTensor` the vector action `c(0, w) = Γ_V ⊗ c_W(w)` becomes
`-Γ_V ⊗ c_W(w)` (`CliffordAlgebra.complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr`).

When `W` is also even-dimensional, its normalized complex volume element `Γ_W` anticommutes with
every vector of `W` (for any quadratic form `Q₂`), so `1 ⊗ Γ_W` (`LinearMap.lTensor E`) intertwines
the `-o₁` product action with the `o₁` product action on the entire complexified Clifford algebra
(`CliffordAlgebra.lTensor_complexVolume_comp_complexProdTensor_neg`). When moreover
`Q₂ w = -‖w‖²`, `1 ⊗ Γ_W` is an involution conjugating one action into the other
(`CliffordAlgebra.conjAlgEquiv_complexProdTensor_neg`). Reversing either `o₁` or `o₂` reverses the
ordered product orientation of `V ⊕ W` and negates the product chirality `Γ_V ⊗ Γ_W`
(`CliffordAlgebra.complexProdTensor_neg_orientation_complexVolume`,
`CliffordAlgebra.complexProdTensor_complexVolume_neg_right`).

## Main results

* `CliffordAlgebra.complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr`: for `-o₁`, a vector
  `(0, w)` acts by `-(Γ_V ⊗ c_W(w))`.
* `CliffordAlgebra.lTensor_complexVolume_comp_complexProdTensor_neg` and
  `CliffordAlgebra.conjAlgEquiv_complexProdTensor_neg`: `1 ⊗ Γ_W` intertwines (and, for
  `Q₂ w = -‖w‖²`, conjugates) the `-o₁` and `o₁` product actions.
* `CliffordAlgebra.complexProdTensor_neg_orientation_complexVolume` and
  `CliffordAlgebra.complexProdTensor_complexVolume_neg_right`: reversing `o₁` or `o₂` negates the
  product chirality.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, the chapter on Clifford modules.
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

/-- Reversing the orientation `o₁` of `V` negates the action of every vector `(0, w)` of `W` in
`CliffordAlgebra.complexProdTensor`. -/
theorem complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr (w : W) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) =
      -TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) := by
  apply TensorProduct.ext'
  intro e f
  simp [neg_tmul]

section EvenRight

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
  (o₂ : Orientation ℝ W (Fin m)) (hm : Even m)

include hm in
/-- **Intertwining under orientation reversal**: when `W` is even-dimensional, `1 ⊗ Γ_W`
intertwines `complexProdTensor` for `-o₁` with `complexProdTensor` for `o₁` on the entire
complexified Clifford algebra of `V ⊕ W`. No metric hypothesis on `Q₂` is required. -/
theorem lTensor_complexVolume_comp_complexProdTensor_neg
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (ρ₂ (complexVolume Q₂ o₂)).lTensor E ∘ₗ
        complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ a =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a ∘ₗ
        (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  have hneg : ρ₁ (complexVolume Q₁ (-o₁)) = -ρ₁ (complexVolume Q₁ o₁) := by
    rw [complexVolume_neg_orientation, map_neg]
  have hγ := map_complexVolume_mul_self o₁ hQ₁ ρ₁
  have hγρ := map_complexVolume_mul_map_ι o₁ hn ρ₁
  have hδρ := map_complexVolume_mul_map_ι o₂ hm ρ₂
  rw [complexProdTensor_def, complexProdTensor_def, AlgHom.comp_apply, AlgHom.comp_apply,
    AlgHom.cliffordProdTensor_congr_grading ρ₁ _ _ _ ρ₂ hneg (by rw [neg_mul_neg, hγ])
      (fun v ↦ by rw [neg_mul, mul_neg, neg_neg, hγρ, neg_neg])]
  exact AlgHom.lTensor_comp_cliffordProdTensor_neg ρ₁ (ρ₁ (complexVolume Q₁ o₁)) hγ hγρ ρ₂ hδρ _

include hm in
/-- When `Q₂ w = -‖w‖²` and `W` is even-dimensional, conjugating by the involution `1 ⊗ Γ_W`
carries `complexProdTensor` for `-o₁` to `complexProdTensor` for `o₁`. -/
theorem conjAlgEquiv_complexProdTensor_neg (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) :
    ((((LinearEquiv.ofInvolutive (ρ₂ (complexVolume Q₂ o₂))
        (map_complexVolume_involutive o₂ hQ₂ ρ₂)).lTensor E).conjAlgEquiv ℂ).toAlgHom).comp
      (complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂) =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ := by
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, LinearEquiv.conjAlgEquiv_apply,
    ← LinearMap.comp_assoc, eq_comm, LinearEquiv.eq_comp_toLinearMap_symm, eq_comm]
  have he : ((LinearEquiv.ofInvolutive (ρ₂ (complexVolume Q₂ o₂))
      (map_complexVolume_involutive o₂ hQ₂ ρ₂)).lTensor E).toLinearMap =
      (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
    apply TensorProduct.ext'
    intro e f
    rfl
  rw [he]
  exact lTensor_complexVolume_comp_complexProdTensor_neg hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm a

variable [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
include hm

/-- Reversing `o₁` reverses the ordered product orientation `(-o₁) × o₂` and negates the product
chirality action `Γ_V ⊗ Γ_W`. -/
theorem complexProdTensor_neg_orientation_complexVolume
    (o' : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (ho' : o'.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)) =
      (-o₁).prod o₂ Fact.out Fact.out) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (complexVolume Q o') =
      -TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  rw [complexProdTensor_complexVolume_of_map_eq_prod hQ (-o₁) hQ₁ hn ρ₁ ρ₂ o₂ o' hm ho']
  apply TensorProduct.ext'
  intro e f
  simp [neg_tmul]

/-- Reversing `o₂` reverses the ordered product orientation `o₁ × (-o₂)` and negates the product
chirality action `Γ_V ⊗ Γ_W`. -/
theorem complexProdTensor_complexVolume_neg_right
    (o' : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (ho' : o'.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)) =
      o₁.prod (-o₂) Fact.out Fact.out) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o') =
      -TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  rw [complexProdTensor_complexVolume_of_map_eq_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ (-o₂) o' hm ho']
  apply TensorProduct.ext'
  intro e f
  simp [tmul_neg]

end EvenRight

end CliffordAlgebra
