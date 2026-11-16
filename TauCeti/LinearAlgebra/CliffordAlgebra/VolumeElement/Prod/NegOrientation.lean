/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.NegGrading

/-!
# Orientation reversal of the first factor in a graded complex Clifford tensor product

Reversing the orientation `o₁` of the first even-dimensional factor `V` negates its chirality
`Γ_V` (`CliffordAlgebra.complexVolume_neg_orientation`). Thus `complexProdTensor` formed with
`-o₁` leaves the action of `V` unchanged and negates the action of `W`:
`c_{-o₁}(v, w) = c₁(v) ⊗ 1 - Γ_V ⊗ c₂(w)`.

When the second factor `W` is also finite-dimensional, oriented, and even-dimensional, its complex
volume element `Γ_W` anticommutes with every vector of `W`. Therefore `1 ⊗ Γ_W` intertwines
`complexProdTensor` formed with `-o₁` and `complexProdTensor` formed with `o₁` for an arbitrary
quadratic form `Q₂` on `W`
(`CliffordAlgebra.lTensor_complexVolume_complexProdTensor_neg_orientation`).
When moreover `Q₂ w = -‖w‖²`, `Γ_W` is an involution and `1 ⊗ Γ_W` conjugates the two actions
(`CliffordAlgebra.conjAlgEquiv_complexProdTensor_neg_orientation`).

On the product volume element for the unreversed orientation `o₁ × o₂`, the `m` minus signs from
`W` cancel when `m` is even, so `c_{-o₁}(Γ_(o₁ × o₂)) = Γ_V ⊗ Γ_W`, whereas on the reversed
product orientation `(-o₁) × o₂` the sign flips to `-(Γ_V ⊗ Γ_W)`.

## Main results

* `CliffordAlgebra.complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr`: reversing `o₁` negates
  the action of vectors in `W`.
* `CliffordAlgebra.lTensor_complexVolume_complexProdTensor_neg_orientation`,
  `CliffordAlgebra.lTensor_complexVolume_complexProdTensor_neg_orientation_apply`: for even `m` and
  any `Q₂`, `1 ⊗ Γ_W` intertwines the `-o₁`-graded and `o₁`-graded actions.
* `CliffordAlgebra.conjAlgEquiv_complexProdTensor_neg_orientation`: when `Q₂ w = -‖w‖²`,
  conjugation by `1 ⊗ Γ_W` carries the `-o₁`-graded action to the `o₁`-graded action.
* `CliffordAlgebra.complexProdTensor_neg_orientation_complexVolume_prod`: action on `Γ_(o₁ × o₂)`
  for even `m`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module TensorProduct
open scoped TensorProduct

namespace CliffordAlgebra

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W}
  {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- Reversing the orientation `o₁` of the first factor negates the action of vectors in `W`. -/
theorem complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr (w : W) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂
        (ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ[ℝ] WithLp.toLp 2 ((0 : V), w))) =
      -TensorProduct.map (ρ₁ (complexVolume Q₁ o₁))
        (ρ₂ (ι (Q₂.baseChange ℂ) ((1 : ℂ) ⊗ₜ[ℝ] w))) := by
  ext e f
  simp [complexVolume_neg_orientation, neg_tmul]

section EvenSecond

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
  (o₂ : Orientation ℝ W (Fin m))

/-- **Orientation reversal intertwining**: when `W` is even-dimensional, `1 ⊗ Γ_W` intertwines
`complexProdTensor` formed with `-o₁` and `complexProdTensor` formed with `o₁`, for an arbitrary
quadratic form `Q₂` on `W`. -/
theorem lTensor_complexVolume_complexProdTensor_neg_orientation (hm : Even m)
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (ρ₂ (complexVolume Q₂ o₂)).lTensor E ∘ₗ complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ a =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a ∘ₗ (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  let e : Q.IsometryEquiv (Q₁.prod Q₂) :=
    { toLinearEquiv := WithLp.linearEquiv 2 ℝ (V × W), map_app' := fun x ↦ (hQ x).symm }
  rw [complexProdTensor_eq_cliffordProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ e (fun _ ↦ rfl),
    complexProdTensor_eq_cliffordProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ e (fun _ ↦ rfl)]
  exact AlgHom.lTensor_cliffordProdTensor_of_eq_neg ρ₁ (ρ₁ (complexVolume Q₁ o₁)) _ _ ρ₂ _ _
    (by rw [complexVolume_neg_orientation, map_neg])
    (ρ₂ (complexVolume Q₂ o₂))
    (fun w ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₂ hm, map_neg])
    (equivOfIsometry (e.baseChangeProd ℂ) a)

/-- Pointwise form of
`CliffordAlgebra.lTensor_complexVolume_complexProdTensor_neg_orientation`. -/
theorem lTensor_complexVolume_complexProdTensor_neg_orientation_apply (hm : Even m)
    (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] F) :
    (ρ₂ (complexVolume Q₂ o₂)).lTensor E (complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ a z) =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a ((ρ₂ (complexVolume Q₂ o₂)).lTensor E z) :=
  LinearMap.congr_fun
    (lTensor_complexVolume_complexProdTensor_neg_orientation hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm a) z

/-- **Orientation reversal equivalence**: when `W` is even-dimensional with `Q₂ w = -‖w‖²`,
conjugation by the involution `1 ⊗ Γ_W` carries `complexProdTensor` formed with `-o₁` to
`complexProdTensor` formed with `o₁`. -/
theorem conjAlgEquiv_complexProdTensor_neg_orientation (hm : Even m)
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) :
    (((LinearEquiv.ofInvolutive (ρ₂ (complexVolume Q₂ o₂))
          (involutive_apply_complexVolume o₂ hQ₂ ρ₂)).lTensor E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂) =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ := by
  let e : Q.IsometryEquiv (Q₁.prod Q₂) :=
    { toLinearEquiv := WithLp.linearEquiv 2 ℝ (V × W), map_app' := fun x ↦ (hQ x).symm }
  rw [complexProdTensor_eq_cliffordProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ e (fun _ ↦ rfl),
    complexProdTensor_eq_cliffordProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ e (fun _ ↦ rfl),
    ← AlgHom.comp_assoc,
    AlgHom.conjAlgEquiv_cliffordProdTensor_lTensor_of_eq_neg ρ₁ (ρ₁ (complexVolume Q₁ o₁)) _ _ ρ₂
      _ _ (by rw [complexVolume_neg_orientation, map_neg])
      (ρ₂ (complexVolume Q₂ o₂)) (involutive_apply_complexVolume o₂ hQ₂ ρ₂)
      (fun w ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₂ hm, map_neg])]

/-- For even `m`, the `-o₁`-graded action sends the unreversed product volume element `Γ_(o₁ × o₂)`
to `Γ_V ⊗ Γ_W`, because the `m` sign flips on `W` cancel. On the reversed product orientation
`(-o₁) × o₂`, `CliffordAlgebra.complexProdTensor_complexVolume_prod` gives `-(Γ_V ⊗ Γ_W)`. -/
theorem complexProdTensor_neg_orientation_complexVolume_prod (hm : Even m)
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)] :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂
        (complexVolume Q (Orientation.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm
          (o₁.prod o₂ Fact.out Fact.out))) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  have h := complexProdTensor_complexVolume_prod hQ (-o₁) hQ₁ hn ρ₁ ρ₂ o₂ hm
  rw [Orientation.prod_neg_left, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
    complexVolume_neg_orientation, map_neg] at h
  apply TensorProduct.ext'
  intro e f
  exact neg_inj.mp (by simpa [neg_tmul] using LinearMap.congr_fun h (e ⊗ₜ f))

end EvenSecond

end CliffordAlgebra
