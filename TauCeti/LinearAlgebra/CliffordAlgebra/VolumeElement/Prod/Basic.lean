/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
public import TauCeti.LinearAlgebra.Dimension.FactFinrank
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.WithLp
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Prod
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Neg

/-!
# Chirality of the graded tensor product of Clifford modules

Let `V` and `W` be oriented real inner product spaces of dimensions `n` and `m`, with quadratic
forms `Q₁` and `Q₂`, and let `V ⊕ W` be the `L²` product `WithLp 2 (V × W)` with a form `Q`
satisfying `Q (v, w) = Q₁ v + Q₂ w`. For the negative-metric convention `Q₁ v = -‖v‖²` and
`Q₂ w = -‖w‖²` this is `Q x = -‖x‖²`. Let `E` and `F` be modules over the complexified Clifford
algebras of `Q₁` and `Q₂`, given by algebra maps `ρ₁` and `ρ₂`.

When `n` is even and `Q₁ v = -‖v‖²`, the normalized complex volume element `Γ_V`
(`CliffordAlgebra.complexVolume`) is an involution anticommuting with every vector of `V`, so it
grades `E`. The graded tensor product from
`TauCeti/LinearAlgebra/CliffordAlgebra/Prod/Basic.lean` then
makes `E ⊗ F` a module over the complexified Clifford algebra of `V ⊕ W`
(`CliffordAlgebra.complexProdTensor`), on which

  `c(v, 0) = c_V(v) ⊗ 1`,  `c(0, w) = Γ_V ⊗ c_W(w)`.

The vectors are moved from `ℂ ⊗ (V ⊕ W)` to `(ℂ ⊗ V) × (ℂ ⊗ W)` by the quadratic isometry
`QuadraticMap.IsometryEquiv.baseChangeProd` of `QuadraticMap.IsometryEquiv.withLpProd`.

On an adapted orthonormal product frame `(e₁, …, eₙ, f₁, …, fₘ)`, the normalized volume element of
`V ⊕ W` acts on `E ⊗ F` by `i ^ ⌊(n + m + 1) / 2⌋ (c(e₁) ⋯ c(eₙ) Γ_V ^ m ⊗ c(f₁) ⋯ c(fₘ))`
(`CliffordAlgebra.complexProdTensor_complexVolume_eq_smul_map`). Basis-free product volume
formulas and their even/odd specializations are developed in
`TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement/Prod/ProdEquiv.lean`.

**Orientation reversal.** Reversing the orientation of `V` negates `Γ_V`, so on the graded tensor
product for `-o₁` a vector of `W` acts by `c(0, w) = -Γ_V ⊗ c_W(w)`. For `m` even, `1 ⊗ Γ_W`
anticommutes with every `c_W(w)` and so intertwines the two graded tensor products
(`CliffordAlgebra.lTensor_complexVolume_mul_complexProdTensor`); for `Q₂ w = -‖w‖²` it is an
involution, and the product for `-o₁` is the conjugate of that for `o₁`
(`CliffordAlgebra.complexProdTensor_neg_orientation`).

## Main definitions

* `CliffordAlgebra.complexProdTensor`: the graded tensor product action of the complexified
  Clifford algebra of `V ⊕ W` on `E ⊗ F`, graded by the chirality of `V`.

## Main results

* `CliffordAlgebra.complexProdTensor_eq_comp`: `complexProdTensor` factors as
  `AlgHom.cliffordProdTensor` precomposed with `(withLpProd hQ).baseChangeProd ℂ`.
* `CliffordAlgebra.complexProdTensor_ι_one_tmul_toLp`: `c(v, w) = c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)`.
* `CliffordAlgebra.complexProdTensor_complexVolume_eq_smul_map`: ordered-frame product action of
  `complexVolume Q o`.
* `CliffordAlgebra.lTensor_complexVolume_mul_complexProdTensor`: `1 ⊗ Γ_W` intertwines the graded
  tensor products for `o₁` and `-o₁`.
* `CliffordAlgebra.complexProdTensor_neg_orientation`: the graded tensor product for `-o₁` is the
  conjugate of that for `o₁` by `1 ⊗ Γ_W`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed. (2007), Definition 2.2.42.
-/

public section

noncomputable section

open Module
open scoped TensorProduct

namespace CliffordAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}

variable (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

include hQ₁ in
/-- For even `k`, `ρ₁(Γ_V) ^ k = 1` when `Q₁ v = -‖v‖²`. -/
theorem map_complexVolume_pow_of_even {k : ℕ} (hk : Even k) :
    ρ₁ (complexVolume Q₁ o₁) ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [← two_mul, pow_mul, sq, map_complexVolume_mul_self o₁ hQ₁ ρ₁, one_pow]

include hQ in
/-- **The graded tensor product of Clifford modules of `V` and `W`.** For `V` of even dimension
with `Q₁ v = -‖v‖²`, the chirality operator `Γ_V` grades `E`, and the complexified Clifford algebra
of `V ⊕ W` acts on `E ⊗ F` by `c(v, w) = c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)`
(`CliffordAlgebra.complexProdTensor_ι_one_tmul_toLp`). -/
def complexProdTensor : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (E ⊗[ℂ] F) :=
  (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂).comp
    (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).toAlgHom

include hQ in
/-- `CliffordAlgebra.complexProdTensor` is `AlgHom.cliffordProdTensor` graded by `Γ_V`, composed
with the complexified product quadratic isometry. -/
theorem complexProdTensor_eq_comp :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ =
      (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
          (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂).comp
        (equivOfIsometry
          ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).toAlgHom :=
  (rfl)

/-- A real vector `(v, w)` of `V ⊕ W` acts on `E ⊗ F` by `c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)`. -/
@[simp]
theorem complexProdTensor_ι_one_tmul_toLp (v : V) (w : W) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, w))) =
      (ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v))).rTensor F +
        TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) := by
  rw [complexProdTensor_eq_comp, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  simp [equivOfIsometry_apply, QuadraticMap.IsometryEquiv.toIsometry_apply,
    AlgHom.cliffordProdTensor_ι]

/-- A vector of `V` acts through the first factor: `c(v, 0) = c_V(v) ⊗ 1`. -/
theorem complexProdTensor_ι_one_tmul_toLp_inl (v : V) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, 0))) =
      (ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v))).rTensor F := by
  simp [complexProdTensor_ι_one_tmul_toLp]

/-- A vector of `W` acts through the chirality of `V`: `c(0, w) = Γ_V ⊗ c_W(w)`. -/
theorem complexProdTensor_ι_one_tmul_toLp_inr (w : W) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) := by
  simp [complexProdTensor_ι_one_tmul_toLp]

/-- The ordered frame product of `V ⊕ W` acts by
`i ^ ⌊(n + m + 1) / 2⌋ (c(e₁) ⋯ c(eₙ) Γ_V ^ m ⊗ c(f₁) ⋯ c(fₘ))`. -/
theorem complexProdTensor_complexVolume_eq_smul_map {m : ℕ}
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))) (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (b₂ : OrthonormalBasis (Fin m) ℝ W) (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
    (ho : ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        (@complexVolume (WithLp 2 (V × W)) _ _
          (Module.Finite.of_basis ((b₁.prod b₂).reindex finSumFinEquiv).toBasis) (n + m)
          (by have := Module.Finite.of_basis b₂.toBasis
              have : Fact (finrank ℝ W = m) :=
                ⟨by rw [Module.finrank_eq_card_basis b₂.toBasis, Fintype.card_fin]⟩
              exact TauCeti.instFactFinrankWithLpProd) Q o) =
      Complex.I ^ ((n + m + 1) / 2) • TensorProduct.map
        (ρ₁ (((List.finRange n).map b₁).map fun v ↦ ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)).prod *
          ρ₁ (complexVolume Q₁ o₁) ^ m)
        (ρ₂ (((List.finRange m).map b₂).map fun w ↦ ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)).prod) := by
  have : FiniteDimensional ℝ W := Module.Finite.of_basis b₂.toBasis
  have : Fact (finrank ℝ W = m) :=
    ⟨by rw [Module.finrank_eq_card_basis b₂.toBasis, Fintype.card_fin]⟩
  have hQb₁ := b₁.isOrthoᵢ_associated hQ₁
  have hl : (List.finRange (n + m)).map ((b₁.prod b₂).reindex finSumFinEquiv) =
      ((List.finRange n).map fun i ↦ WithLp.toLp 2 (b₁ i, 0)) ++
        (List.finRange m).map fun j ↦ WithLp.toLp 2 (0, b₂ j) := by
    rw [← List.ofFn_eq_map, List.ofFn_add, ← List.ofFn_eq_map, ← List.ofFn_eq_map]
    congr 2 <;> ext i
    · have hcast : Fin.castLE (Nat.le_add_right n m) i = Fin.castAdd m i := by ext; simp
      simp [OrthonormalBasis.reindex_apply, hcast]
    · simp [OrthonormalBasis.reindex_apply]
  have h₁ : equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)
      ((((List.finRange n).map fun i ↦ WithLp.toLp 2 (b₁ i, 0)).map
        fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ v)).prod) =
        map (QuadraticMap.Isometry.inl (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
          (((List.finRange n).map b₁).map fun v ↦ ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)).prod := by
    simp [equivOfIsometry_apply, QuadraticMap.IsometryEquiv.toIsometry_apply, map_list_prod,
      List.map_map, Function.comp_def]
  have h₂ : equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)
      ((((List.finRange m).map fun j ↦ WithLp.toLp 2 (0, b₂ j)).map
        fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ v)).prod) =
        map (QuadraticMap.Isometry.inr (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
          ((((List.finRange m).map b₂).map ((1 : ℂ) ⊗ₜ[ℝ] ·)).map
            (ι (Q₂.baseChange ℂ))).prod := by
    simp [equivOfIsometry_apply, QuadraticMap.IsometryEquiv.toIsometry_apply, map_list_prod,
      List.map_map, Function.comp_def]
  have hQb :
      (QuadraticMap.associated Q).IsOrthoᵢ ((b₁.prod b₂).reindex finSumFinEquiv).toBasis := by
    have h := OrthonormalBasis.isOrthoᵢ_associated_prod hQ hQb₁ hQb₂
    rw [LinearMap.isOrthoᵢ_def] at h ⊢
    intro i j hij
    simpa [OrthonormalBasis.reindex_apply] using h _ _ (finSumFinEquiv.symm.injective.ne hij)
  -- Split the frame product of `V ⊕ W` into its `V` block and its `W` block.
  rw [complexVolume_eq o _ ho hQb, hl, List.map_append, List.prod_append]
  -- Move each block into its summand, where the two Clifford algebras act.
  rw [map_smul, complexProdTensor_eq_comp, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, map_mul,
    h₁, h₂]
  simp only [map_mul, AlgHom.cliffordProdTensor_map_inl, AlgHom.cliffordProdTensor_map_inr_prod,
    LinearMap.rTensor, ← Module.End.one_eq_id, ← TensorProduct.map_mul, one_mul]
  simp [List.map_map, Function.comp_def]

/-! ### Orientation reversal -/

section NegOrientation

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))

/-- **Reversing the orientation of `V`**: for `W` of even dimension, `1 ⊗ Γ_W` intertwines the
graded tensor product for `o₁` with that for `-o₁`, on which a vector of `W` acts by
`c(0, w) = -Γ_V ⊗ c_W(w)`. -/
theorem lTensor_complexVolume_mul_complexProdTensor (hm : Even m)
    (x : CliffordAlgebra (Q.baseChange ℂ)) :
    (ρ₂ (complexVolume Q₂ o₂)).lTensor E * complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ x =
      complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ x * (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  rw [complexProdTensor_eq_comp, complexProdTensor_eq_comp, AlgHom.comp_apply, AlgHom.comp_apply]
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
  rw [complexProdTensor_eq_comp, complexProdTensor_eq_comp, AlgHom.comp_apply, AlgHom.comp_apply]
  exact AlgHom.cliffordProdTensor_of_eq_neg _ _ _ _ _ _ _ ρ₂
    (map_complexVolume_mul_map_ι o₂ hm ρ₂) (map_complexVolume_mul_self o₂ hQ₂ ρ₂)
    (by rw [complexVolume_neg_orientation, map_neg]) _

end NegOrientation

end CliffordAlgebra
