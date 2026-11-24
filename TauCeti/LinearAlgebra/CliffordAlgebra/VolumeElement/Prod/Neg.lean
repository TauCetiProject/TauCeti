/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Neg

/-!
# Orientation reversal in the graded tensor product of complex Clifford modules

Reversing the orientation `o₁` of the even-dimensional space `V` negates `Γ_V`, so in
`CliffordAlgebra.complexProdTensor` the vector action `c(0, w) = Γ_V ⊗ c_W(w)` becomes
`-Γ_V ⊗ c_W(w)`. When `W` is also even-dimensional, `1 ⊗ Γ_W` intertwines the `o₁` product action
with the `-o₁` product action on the entire complexified Clifford algebra (and conjugates one into
the other when `Q₂ w = -‖w‖²`), while reversing `o₁` or `o₂` negates the product chirality
`Γ_V ⊗ Γ_W`.

## Main results

* `CliffordAlgebra.complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr`: for `-o₁`, `(0, w)` acts
  by `-(Γ_V ⊗ c_W(w))`.
* `CliffordAlgebra.lTensor_complexVolume_mul_complexProdTensor` and
  `CliffordAlgebra.complexProdTensor_neg_orientation`: `1 ⊗ Γ_W` intertwines (and, for
  `Q₂ w = -‖w‖²`, conjugates) the `o₁` and `-o₁` product actions.
* `CliffordAlgebra.complexProdTensor_neg_orientation_complexVolume` and
  `CliffordAlgebra.complexProdTensor_complexVolume_neg_right`: reversing `o₁` or `o₂` negates the
  product chirality `Γ_V ⊗ Γ_W` (covering rank zero as well).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed. (2007), Definition 2.2.42.
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
      -TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) :=
  TensorProduct.ext' fun _ _ ↦ by simp [neg_tmul]

section EvenRight

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
  (o₂ : Orientation ℝ W (Fin m))

/-- **Reversing the orientation of `V`**: for `W` of even dimension, `1 ⊗ Γ_W` intertwines the
graded tensor product for `o₁` with that for `-o₁`, on which a vector of `W` acts by
`c(0, w) = -Γ_V ⊗ c_W(w)`. No metric hypothesis on `Q₂` is required. -/
theorem lTensor_complexVolume_mul_complexProdTensor (hm : Even m)
    (x : CliffordAlgebra (Q.baseChange ℂ)) :
    (ρ₂ (complexVolume Q₂ o₂)).lTensor E * complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ x =
      complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ x * (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  rw [complexProdTensor_def, complexProdTensor_def, AlgHom.comp_apply, AlgHom.comp_apply]
  exact AlgHom.lTensor_mul_cliffordProdTensor_of_eq_neg _ _ _ _ _ _ _ ρ₂
    (map_complexVolume_mul_map_ι o₂ hm ρ₂) (by rw [complexVolume_neg_orientation, map_neg]) _

/-- **Reversing the orientation of `V` is a conjugation**: for `W` of even dimension with
`Q₂ w = -‖w‖²`, the graded tensor product for `-o₁` is the conjugate of that for `o₁` by the
involution `1 ⊗ Γ_W`. -/
theorem complexProdTensor_neg_orientation (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m)
    (x : CliffordAlgebra (Q.baseChange ℂ)) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ x =
      (ρ₂ (complexVolume Q₂ o₂)).lTensor E * complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ x *
        (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  rw [complexProdTensor_def, complexProdTensor_def, AlgHom.comp_apply, AlgHom.comp_apply]
  exact AlgHom.cliffordProdTensor_of_eq_neg _ _ _ _ _ _ _ ρ₂
    (map_complexVolume_mul_map_ι o₂ hm ρ₂) (map_complexVolume_mul_self o₂ hQ₂ ρ₂)
    (by rw [complexVolume_neg_orientation, map_neg]) _

variable [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]

/-- Reversing `o₁` reverses the ordered product orientation `(-o₁) × o₂` and negates the product
chirality action `Γ_V ⊗ Γ_W` (equivalently leaving it equal to `Γ_(V, -o₁) ⊗ Γ_W`), including in
dimension zero. -/
theorem complexProdTensor_neg_orientation_complexVolume (hm : Even m)
    (o' : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (ho' : o'.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)) =
      (-o₁).prod o₂ Fact.out Fact.out) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (complexVolume Q o') =
      -TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  rw [complexProdTensor_complexVolume_of_map_eq_prod hQ (-o₁) hQ₁ hn ρ₁ ρ₂ o₂ o' hm ho']
  exact TensorProduct.ext' fun _ _ ↦ by simp [neg_tmul]

/-- Reversing `o₂` reverses the ordered product orientation `o₁ × (-o₂)` and negates the product
chirality action `Γ_V ⊗ Γ_W`. -/
theorem complexProdTensor_complexVolume_neg_right (hm : Even m)
    (o' : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (ho' : o'.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)) =
      o₁.prod (-o₂) Fact.out Fact.out) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o') =
      -TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  rw [complexProdTensor_complexVolume_of_map_eq_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ (-o₂) o' hm ho']
  exact TensorProduct.ext' fun _ _ ↦ by simp [tmul_neg]

end EvenRight

end CliffordAlgebra
