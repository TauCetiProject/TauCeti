/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Involution
public import TauCeti.LinearAlgebra.QuadraticForm.WithLp
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Graded-algebra comparison and half-spin decomposition of Clifford tensor products

Let `V` and `W` be real inner product spaces with `V` oriented of even dimension `n`,
`Q₁ v = -‖v‖²`, `Q (v, w) = Q₁ v + Q₂ w` on `WithLp 2 (V × W)`, and let `E` and `F` be complex
Clifford modules over `Q₁` and `Q₂`.

First, `CliffordAlgebra.complexWithLpProdEquiv` identifies the complexified Clifford algebra of
`WithLp 2 (V × W)` with the graded tensor product
`evenOdd (Q₁.baseChange ℂ) ᵍ⊗[ℂ] evenOdd (Q₂.baseChange ℂ)` via `CliffordAlgebra.prodEquiv`, and
shows that `CliffordAlgebra.complexProdTensor` is the composite of this equivalence with the
Koszul-signed tensor action: for `b` of parity `j` and `e` in the `(-1) ^ i`-eigenspace of the
chirality `Γ_V`, the pure tensor `a ᵍ⊗ b` sends `e ⊗ f` to `(-1) ^ (i * j) • (ρ₁ a e ⊗ ρ₂ b f)`.
When `W` is finite-dimensional and `ρ₁`, `ρ₂` are spinor modules (bijective onto `End_ℂ E` and
`End_ℂ F`), `complexProdTensor` is bijective onto `End_ℂ (E ⊗ F)`.

Second, when `W` is also oriented of even dimension `m` with `Q₂ w = -‖w‖²`, the product chirality
`Γ_(V ⊕ W)` acts on `E ⊗ F` by `Γ_V ⊗ Γ_W`
(`CliffordAlgebra.complexProdTensor_complexVolume_of_map_prod`). Combining this with
`Module.End.eigenspaceTensorMapEquiv` decomposes the `μ`-eigenspace (`μ² = 1`) of `E ⊗ F` as

  `(E ⊗ F)^μ ≃ (E⁺ ⊗ F^μ) × (E⁻ ⊗ F^(-μ))`,

so `(E ⊗ F)⁺ ≃ (E⁺ ⊗ F⁺) × (E⁻ ⊗ F⁻)` and `(E ⊗ F)⁻ ≃ (E⁺ ⊗ F⁻) × (E⁻ ⊗ F⁺)`. For spinor modules
`S_V` and `S_W` with `n + m ≠ 0`, each half-spin space of `S_V ⊗ S_W` has complex dimension
`2 ^ ((n + m) / 2 - 1)` — for two negative-metric planes (`n = m = 2`), rank `2` out of `4`.

## Main definitions

* `CliffordAlgebra.complexWithLpProdEquiv`: the graded-algebra equivalence
  `CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ]`
  `evenOdd (Q₁.baseChange ℂ) ᵍ⊗[ℂ] evenOdd (Q₂.baseChange ℂ)`.
* `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv`: the half-spin linear equivalence
  `(E ⊗ F)^μ ≃ (E⁺ ⊗ F^μ) × (E⁻ ⊗ F^(-μ))` for `μ * μ = 1`.

## Main results

* `CliffordAlgebra.complexProdTensor_complexWithLpProdEquiv_symm_tmul` and
  `CliffordAlgebra.complexProdTensor_complexWithLpProdEquiv_symm_tmul_apply_tmul`: the Koszul-signed
  action of homogeneous graded tensors on `E ⊗ F`.
* `CliffordAlgebra.complexProdTensor_bijective`: tensor product of spinor modules is a spinor
  module.
* `CliffordAlgebra.finrank_eigenspace_complexProdTensor_complexVolume` and
  `CliffordAlgebra.finrank_eigenspace_complexProdTensor_complexVolume_of_bijective`: dimension
  formulas for the half-spin spaces of `E ⊗ F`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Chapter 2, §2.2.
-/

public section

noncomputable section

open Module
open scoped TensorProduct

namespace CliffordAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

/-! ### Comparison with `CliffordAlgebra.prodEquiv` -/

include hQ in
/-- The complexified Clifford algebra of `WithLp 2 (V × W)` is isomorphic to the graded tensor
product `evenOdd (Q₁.baseChange ℂ) ᵍ⊗[ℂ] evenOdd (Q₂.baseChange ℂ)`, composing
`QuadraticMap.IsometryEquiv.baseChangeProd` of `QuadraticMap.IsometryEquiv.withLpProd` with
`CliffordAlgebra.prodEquiv`. -/
def complexWithLpProdEquiv :
    CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ]
      evenOdd (Q₁.baseChange ℂ) ᵍ⊗[ℂ] evenOdd (Q₂.baseChange ℂ) :=
  (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).trans
    (prodEquiv (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))

/-- On a real vector `(v, w)`, `complexWithLpProdEquiv` sends `ι (1 ⊗ (v, w))` to
`ι (1 ⊗ v) ᵍ⊗ 1 + 1 ᵍ⊗ ι (1 ⊗ w)`. -/
@[simp]
theorem complexWithLpProdEquiv_ι_one_tmul_toLp (v : V) (w : W) :
    complexWithLpProdEquiv hQ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, w))) =
      ι (Q₁.baseChange ℂ) (1 ⊗ₜ v) ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ ι (Q₂.baseChange ℂ) (1 ⊗ₜ w) := by
  simp [complexWithLpProdEquiv, equivOfIsometry_apply,
    QuadraticMap.IsometryEquiv.baseChangeProd_tmul]

/-- The inverse of `complexWithLpProdEquiv` sends `ι u ᵍ⊗ 1` to the left-summand vector. -/
@[simp]
theorem complexWithLpProdEquiv_symm_ι_tmul_one (v : V) :
    (complexWithLpProdEquiv hQ).symm (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v) ᵍ⊗ₜ 1) =
      ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, 0)) := by
  apply (complexWithLpProdEquiv hQ).injective
  simp [complexWithLpProdEquiv_ι_one_tmul_toLp]

/-- The inverse of `complexWithLpProdEquiv` sends `1 ᵍ⊗ ι w` to the right-summand vector. -/
@[simp]
theorem complexWithLpProdEquiv_symm_one_tmul_ι (w : W) :
    (complexWithLpProdEquiv hQ).symm (1 ᵍ⊗ₜ ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)) =
      ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w)) := by
  apply (complexWithLpProdEquiv hQ).injective
  simp [complexWithLpProdEquiv_ι_one_tmul_toLp]

variable [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

include hQ₁ in
private theorem map_complexVolume_mul_self' :
    ρ₁ (complexVolume Q₁ o₁) * ρ₁ (complexVolume Q₁ o₁) = 1 := by
  rw [← map_mul, complexVolume_mul_self o₁ hQ₁, map_one]

include hn in
private theorem map_complexVolume_mul_map_ι' (w : ℂ ⊗[ℝ] V) :
    ρ₁ (complexVolume Q₁ o₁) * ρ₁ (ι (Q₁.baseChange ℂ) w) =
      -(ρ₁ (ι (Q₁.baseChange ℂ) w) * ρ₁ (complexVolume Q₁ o₁)) := by
  rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg]

/-- `complexProdTensor` transported along `(complexWithLpProdEquiv hQ).symm` is
`AlgHom.cliffordProdTensor ∘ toProd`. -/
private theorem complexProdTensor_comp_complexWithLpProdEquiv_symm :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).comp (complexWithLpProdEquiv hQ).symm.toAlgHom =
      (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
        (map_complexVolume_mul_self' o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι' o₁ hn ρ₁) ρ₂).comp
        (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)) := by
  have h : complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ =
      ((AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
        (map_complexVolume_mul_self' o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι' o₁ hn ρ₁) ρ₂).comp
        (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))).comp
        (complexWithLpProdEquiv hQ).toAlgHom := by
    refine AlgHom.toRingHom_injective <| baseChange_ringHom_ext Q (fun _ ↦ by simp) fun x' ↦ ?_
    obtain ⟨⟨v, w⟩, rfl⟩ : ∃ p : V × W, WithLp.toLp 2 p = x' :=
      ⟨WithLp.ofLp x', by simp⟩
    simp [complexProdTensor_ι_one_tmul_toLp, complexWithLpProdEquiv_ι_one_tmul_toLp]
  apply AlgHom.ext
  intro x
  rw [h]
  simp

/-- **Comparison with Mathlib's `CliffordAlgebra.prodEquiv`.** Under `complexWithLpProdEquiv`, a
pure tensor `a ᵍ⊗ b` with `b` of parity `j` in `CliffordAlgebra (Q₂.baseChange ℂ)` acts on `E ⊗ F`
by `ρ₁ a Γ_V ^ j ⊗ ρ₂ b`. -/
theorem complexProdTensor_complexWithLpProdEquiv_symm_tmul
    (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ ((complexWithLpProdEquiv hQ).symm (a ᵍ⊗ₜ b)) =
      TensorProduct.map (ρ₁ a * ρ₁ (complexVolume Q₁ o₁) ^ j.val) (ρ₂ b) := by
  have h := AlgHom.congr_fun
    (complexProdTensor_comp_complexWithLpProdEquiv_symm hQ o₁ hQ₁ hn ρ₁ ρ₂) (a ᵍ⊗ₜ b)
  exact h.trans (AlgHom.cliffordProdTensor_toProd_tmul ρ₁ (ρ₁ (complexVolume Q₁ o₁))
    (map_complexVolume_mul_self' o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι' o₁ hn ρ₁) ρ₂ a hb)

/-- **Koszul-signed evaluation on homogeneous spinors.** If `b` has parity `j` in
`CliffordAlgebra (Q₂.baseChange ℂ)` and `e` lies in the `(-1) ^ i`-eigenspace of the chirality
`Γ_V` (`i = 0` on `E⁺`, `i = 1` on `E⁻`), then `(complexWithLpProdEquiv hQ).symm (a ᵍ⊗ b)` sends
`e ⊗ f` to `(-1) ^ (i * j.val) • (ρ₁ a e ⊗ ρ₂ b f)`. -/
theorem complexProdTensor_complexWithLpProdEquiv_symm_tmul_apply_tmul
    (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j)
    {i : ℕ} {e : E} (he : e ∈ (ρ₁ (complexVolume Q₁ o₁)).eigenspace ((-1 : ℂ) ^ i)) (f : F) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ ((complexWithLpProdEquiv hQ).symm (a ᵍ⊗ₜ b)) (e ⊗ₜ f) =
      (-1 : ℂ) ^ (i * j.val) • (ρ₁ a e ⊗ₜ ρ₂ b f) := by
  have h := LinearMap.congr_fun (AlgHom.congr_fun
    (complexProdTensor_comp_complexWithLpProdEquiv_symm hQ o₁ hQ₁ hn ρ₁ ρ₂) (a ᵍ⊗ₜ b)) (e ⊗ₜ f)
  exact h.trans (AlgHom.cliffordProdTensor_toProd_tmul_apply_tmul ρ₁ (ρ₁ (complexVolume Q₁ o₁))
    (map_complexVolume_mul_self' o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι' o₁ hn ρ₁) ρ₂ a hb he f)

/-- **The graded tensor product of spinor modules is a spinor module.** When `W` is
finite-dimensional and `ρ₁`, `ρ₂` are bijective onto `End_ℂ E` and `End_ℂ F`, the graded product
action `complexProdTensor` is bijective onto `End_ℂ (E ⊗ F)`. -/
theorem complexProdTensor_bijective [FiniteDimensional ℝ W]
    (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂) :
    Function.Bijective (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) := by
  have : Module.Finite ℂ (ℂ ⊗[ℝ] V) := inferInstance
  have : Module.Finite ℂ (ℂ ⊗[ℝ] W) := inferInstance
  have : Module.Finite ℂ E := Module.Finite.of_surjective_end ρ₁ hρ₁.2
  have : Module.Finite ℂ F := Module.Finite.of_surjective_end ρ₂ hρ₂.2
  have hbij : Function.Bijective
      ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).comp (complexWithLpProdEquiv hQ).symm.toAlgHom) := by
    rw [complexProdTensor_comp_complexWithLpProdEquiv_symm hQ o₁ hQ₁ hn ρ₁ ρ₂]
    exact (AlgHom.cliffordProdTensor_bijective ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self' o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι' o₁ hn ρ₁) ρ₂
      hρ₁ hρ₂).comp (prodEquiv (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).symm.bijective
  have heq : (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ : _ → _) =
      ⇑((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).comp (complexWithLpProdEquiv hQ).symm.toAlgHom) ∘
        ⇑(complexWithLpProdEquiv hQ) := by
    ext a z
    simp
  rw [heq]
  exact hbij.comp (complexWithLpProdEquiv hQ).bijective

/-! ### Half-spin eigenspace decomposition -/

section HalfSpin

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))
  [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
  (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))

/-- **Half-spin decomposition of the graded tensor product.** For even-dimensional oriented
inner product spaces `(V, o₁)` and `(W, o₂)` with `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, and `V ⊕ W`
oriented by `o₁.prod o₂`, the `μ`-eigenspace (`μ * μ = 1`) of the product chirality `Γ_(V ⊕ W)` on
`E ⊗ F` is linearly isomorphic to `(E⁺ ⊗ F^μ) × (E⁻ ⊗ F^(-μ))`:

* for `μ = 1`: `(E ⊗ F)⁺ ≃ (E⁺ ⊗ F⁺) × (E⁻ ⊗ F⁻)`;
* for `μ = -1`: `(E ⊗ F)⁻ ≃ (E⁺ ⊗ F⁻) × (E⁻ ⊗ F⁺)`. -/
def complexProdTensorComplexVolumeEigenspaceEquiv (hm : Even m) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (ho : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) {μ : ℂ} (hμ : μ * μ = 1) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ ≃ₗ[ℂ]
      ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1 ⊗[ℂ]
          (ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) ×
        ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1) ⊗[ℂ]
          (ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) :=
  (LinearEquiv.ofEq _ _
      (congrArg (fun f ↦ Module.End.eigenspace f μ)
        (complexProdTensor_complexVolume_of_map_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hm hQ₂ ho))).trans
    (Module.End.eigenspaceTensorMapEquiv
      (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
      (involutive_apply_complexVolume o₁ hQ₁ ρ₁) (involutive_apply_complexVolume o₂ hQ₂ ρ₂) hμ)

/-- The forward map of `complexProdTensorComplexVolumeEigenspaceEquiv` applies the tensor products
of the chirality projections `½ (1 ± Γ_V)` and `½ (1 ± μ Γ_W)`. -/
@[simp]
theorem complexProdTensorComplexVolumeEigenspaceEquiv_apply (hm : Even m)
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (ho : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) {μ : ℂ} (hμ : μ * μ = 1)
    (z : (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) :
    complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hm hQ₂ ho hμ z =
      (TensorProduct.map
          (Module.End.eigenProjOfInvolutive (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
            (one_mul 1))
          (Module.End.eigenProjOfInvolutive (involutive_apply_complexVolume o₂ hQ₂ ρ₂) hμ) z.1,
        TensorProduct.map
          (Module.End.eigenProjOfInvolutive (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
            ((neg_mul_neg (1 : ℂ) 1).trans (one_mul 1)))
          (Module.End.eigenProjOfInvolutive (involutive_apply_complexVolume o₂ hQ₂ ρ₂)
            ((neg_mul_neg μ μ).trans hμ)) z.1) := by
  rw [complexProdTensorComplexVolumeEigenspaceEquiv, LinearEquiv.trans_apply,
    Module.End.eigenspaceTensorMapEquiv_apply, LinearEquiv.coe_ofEq_apply]

/-- The inverse of `complexProdTensorComplexVolumeEigenspaceEquiv` adds the two tensor products of
the chirality-eigenspace inclusions. -/
@[simp]
theorem coe_complexProdTensorComplexVolumeEigenspaceEquiv_symm_apply (hm : Even m)
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (ho : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) {μ : ℂ} (hμ : μ * μ = 1)
    (p : ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1 ⊗[ℂ]
            (ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) ×
          ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1) ⊗[ℂ]
            (ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ))) :
    ((complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hm hQ₂ ho hμ).symm p :
        E ⊗[ℂ] F) =
      TensorProduct.map ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1).subtype
          ((ρ₂ (complexVolume Q₂ o₂)).eigenspace μ).subtype p.1 +
        TensorProduct.map ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1)).subtype
          ((ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)).subtype p.2 := by
  rw [complexProdTensorComplexVolumeEigenspaceEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply,
    Module.End.coe_eigenspaceTensorMapEquiv_symm_apply]

/-- Dimension of the `μ`-eigenspace (`μ * μ = 1`) of `Γ_(V ⊕ W)` on `E ⊗ F`:
`dim (E ⊗ F)^μ = dim E⁺ · dim F^μ + dim E⁻ · dim F^(-μ)`. -/
theorem finrank_eigenspace_complexProdTensor_complexVolume
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (hm : Even m)
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (ho : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) {μ : ℂ} (hμ : μ * μ = 1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) =
      finrank ℂ ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1) *
          finrank ℂ ((ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) +
        finrank ℂ ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1)) *
          finrank ℂ ((ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) := by
  rw [(complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hm hQ₂ ho
      hμ).finrank_eq,
    Module.finrank_prod, Module.finrank_tensorProduct, Module.finrank_tensorProduct]

omit [Fact (finrank ℝ W = m)] in
/-- **Half-spin dimension of `S_V ⊗ S_W`.** When `E` and `F` are spinor modules over `V` and `W`
(`ρ₁`, `ρ₂` bijective) and `n + m ≠ 0`, both the `+1`- and `-1`-eigenspaces of `Γ_(V ⊕ W)` on
`E ⊗ F` have complex dimension `2 ^ ((n + m) / 2 - 1)`. For two negative-metric planes
(`n = m = 2`), this is `2` out of `4`. -/
theorem finrank_eigenspace_complexProdTensor_complexVolume_of_bijective
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hnm : n + m ≠ 0)
    (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂)
    {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) =
      2 ^ ((n + m) / 2 - 1) := by
  -- Equip `E ⊗ F` locally with the module structure induced by `complexProdTensor` so
  -- `finrank_eigenspace_complexVolume_of_bijective_lsmul` applies directly.
  let : Module (CliffordAlgebra (Q.baseChange ℂ)) (E ⊗[ℂ] F) :=
    Module.compHom (E ⊗[ℂ] F) (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).toRingHom
  have : IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) (E ⊗[ℂ] F) :=
    ⟨fun c a z ↦ by
      -- Unfold the pulled-back Clifford scalar action to `complexProdTensor`.
      change complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (c • a) z =
        c • complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z
      rw [map_smul, LinearMap.smul_apply]⟩
  have hQ_norm (x : WithLp 2 (V × W)) : Q x = -‖x‖ ^ 2 := by
    rw [hQ x, hQ₁, hQ₂, WithLp.prod_norm_sq_eq_of_L2]
    dsimp only [WithLp.fst, WithLp.snd]
    ring
  have hlsmul : (Algebra.lsmul ℂ ℂ (E ⊗[ℂ] F) :
      CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (E ⊗[ℂ] F)) =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ := by
    ext a z
    rfl
  rw [← hlsmul]
  exact finrank_eigenspace_complexVolume_of_bijective_lsmul o hQ_norm
    (hlsmul.symm ▸ complexProdTensor_bijective hQ o₁ hQ₁ hn ρ₁ ρ₂ hρ₁ hρ₂) hnm hμ

end HalfSpin

end CliffordAlgebra
