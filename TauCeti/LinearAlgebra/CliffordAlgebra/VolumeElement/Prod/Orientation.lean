/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic
public import TauCeti.LinearAlgebra.Orientation.Prod
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Prod
import TauCeti.Analysis.InnerProductSpace.QuadraticForm.OrthonormalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Neg
import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Orientation reversal and product orientations for graded Clifford tensor products

Let `V` and `W` be real inner product spaces with `V` oriented of even dimension `n`,
`Q₁ v = -‖v‖²`, `Q (v, w) = Q₁ v + Q₂ w` on `WithLp 2 (V × W)`, and let `E`, `F` be complex
Clifford modules over `Q₁`, `Q₂`. Reversing `o₁` negates `Γ_V`, replacing `c(0, w) = Γ_V ⊗ c_W(w)`
by `-Γ_V ⊗ c_W(w)` (equivalently twisting `ρ₂` by `CliffordAlgebra.involute`). For `W` of even
dimension `m`, `1 ⊗ Γ_W` intertwines the two graded tensor products (and conjugates them when
`Q₂ w = -‖w‖²`). This file also computes the normalized volume element of `V ⊕ W` on `E ⊗ F`
first for concatenated orthonormal frames (`CliffordAlgebra.complexProdTensor_complexVolume` and
`CliffordAlgebra.complexProdTensor_complexVolume_of_odd`), and then upgrades those formulas to the
frame-free product orientation `Orientation.prod o₁ o₂` for all orientations (including
`-positiveOrientation` in dimension zero).

## Main results

* `CliffordAlgebra.complexProdTensor_neg_orientation_ι_one_tmul_toLp`: reversing `o₁` negates the
  action of `(0, w)`.
* `CliffordAlgebra.complexProdTensor_neg_orientation_eq_involute`: reversing `o₁` twists `ρ₂` by
  `CliffordAlgebra.involute`.
* `CliffordAlgebra.lTensor_complexVolume_mul_complexProdTensor`: `1 ⊗ Γ_W` intertwines the graded
  tensor products for `o₁` and `-o₁`.
* `CliffordAlgebra.complexProdTensor_neg_orientation`: the graded tensor product for `-o₁` is the
  conjugate of that for `o₁` by `1 ⊗ Γ_W`.
* `CliffordAlgebra.complexProdTensor_complexVolume` and
  `CliffordAlgebra.complexProdTensor_complexVolume_of_odd`: ordered-frame product-volume formulas.
* `CliffordAlgebra.complexProdTensor_complexVolume_of_map_prod` and
  `CliffordAlgebra.complexProdTensor_complexVolume_of_odd_of_map_prod`: frame-free product-volume
  formulas for `(o₁.prod o₂).map _ (WithLp.linearEquiv 2 ℝ (V × W)).symm`.
* `CliffordAlgebra.complexProdTensor_neg_orientation_complexVolume_neg_of_map_prod`: reversing
  `o₁` reverses the product orientation `o` and negates the product chirality.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Chapter 2, §2.2, and Chapter 12, §12.1.
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
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-! ### Orientation reversal of the first summand -/

/-- Reversing the orientation of `V` replaces `c(v, w) = c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)` by
`c_V(v) ⊗ 1 - Γ_V ⊗ c_W(w)`. -/
theorem complexProdTensor_neg_orientation_ι_one_tmul_toLp (v : V) (w : W) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, w))) =
      (ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v))).rTensor F -
        TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) := by
  simp [TensorProduct.map_neg_left, sub_eq_add_neg]

/-- Reversing the orientation of `V` in `complexProdTensor` is equivalent to twisting the second
representation `ρ₂` by `CliffordAlgebra.involute`. -/
theorem complexProdTensor_neg_orientation_eq_involute :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ (ρ₂.comp involute) := by
  refine AlgHom.toRingHom_injective <| baseChange_ringHom_ext Q (fun _ ↦ by simp) fun x ↦ ?_
  obtain ⟨⟨v, w⟩, rfl⟩ := WithLp.toLp_surjective 2 x
  simp [TensorProduct.map_neg_left, TensorProduct.map_neg_right]

section SecondFactor

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

/-! ### Ordered-frame product volume formulas -/

variable [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
  (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))

omit [Fact (finrank ℝ W = m)] in
/-- The ordered frame product of `V ⊕ W` acts by `c(e₁) ⋯ c(eₙ) Γ_V ^ m ⊗ c(f₁) ⋯ c(fₘ)`. -/
private theorem complexProdTensor_complexVolume_eq_map (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (hQb₁ : (QuadraticMap.associated Q₁).IsOrthoᵢ b₁.toBasis) (b₂ : OrthonormalBasis (Fin m) ℝ W)
    (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
    (ho : ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      Complex.I ^ ((n + m + 1) / 2) • TensorProduct.map
        (ρ₁ (((List.finRange n).map b₁).map fun v ↦ ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)).prod *
          ρ₁ (complexVolume Q₁ o₁) ^ m)
        (ρ₂ (((List.finRange m).map b₂).map fun w ↦ ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)).prod) := by
  have hl : (List.finRange (n + m)).map ((b₁.prod b₂).reindex finSumFinEquiv) =
      ((List.finRange n).map fun i ↦ WithLp.toLp 2 (b₁ i, 0)) ++
        (List.finRange m).map fun j ↦ WithLp.toLp 2 (0, b₂ j) := by
    rw [← List.ofFn_eq_map, List.ofFn_add, ← List.ofFn_eq_map, ← List.ofFn_eq_map]
    congr 2 <;> ext i
    · have hcast : Fin.castLE (Nat.le_add_right n m) i = Fin.castAdd m i := by ext; simp
      simp [OrthonormalBasis.reindex_apply, hcast]
    · simp [OrthonormalBasis.reindex_apply]
  have h₁ : map ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ).toIsometry
      ((((List.finRange n).map fun i ↦ WithLp.toLp 2 (b₁ i, 0)).map
        fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ v)).prod) =
        map (QuadraticMap.Isometry.inl (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
          (((List.finRange n).map b₁).map fun v ↦ ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)).prod := by
    simp [QuadraticMap.IsometryEquiv.baseChangeProd_tmul, map_list_prod, List.map_map,
      Function.comp_def]
  have h₂ : map ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ).toIsometry
      ((((List.finRange m).map fun j ↦ WithLp.toLp 2 (0, b₂ j)).map
        fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ v)).prod) =
        map (QuadraticMap.Isometry.inr (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))
          ((((List.finRange m).map b₂).map ((1 : ℂ) ⊗ₜ[ℝ] ·)).map
            (ι (Q₂.baseChange ℂ))).prod := by
    simp [QuadraticMap.IsometryEquiv.baseChangeProd_tmul, map_list_prod, List.map_map,
      Function.comp_def]
  have hQb :
      (QuadraticMap.associated Q).IsOrthoᵢ ((b₁.prod b₂).reindex finSumFinEquiv).toBasis := by
    have h := OrthonormalBasis.isOrthoᵢ_associated_prod hQ hQb₁ hQb₂
    rw [LinearMap.isOrthoᵢ_def] at h ⊢
    intro i j hij
    simpa [OrthonormalBasis.reindex_apply] using h _ _ (finSumFinEquiv.symm.injective.ne hij)
  -- Split the frame product of `V ⊕ W` into its `V` block and its `W` block.
  rw [complexVolume_eq o _ ho hQb, hl, List.map_append, List.prod_append]
  -- Move each block into its summand, where the two Clifford algebras act.
  rw [map_smul, complexProdTensor_eq_comp, AlgHom.comp_apply, map_mul, map_mul, h₁, h₂]
  simp only [AlgHom.cliffordProdTensor_map_inl, AlgHom.cliffordProdTensor_map_inr_prod,
    LinearMap.rTensor, ← Module.End.one_eq_id, ← TensorProduct.map_mul, one_mul]
  simp [List.map_map, Function.comp_def]

include hQ₁ in
/-- The normalized volume element of `V ⊕ W` acts by `Γ_V ^ (m + 1) ⊗ Γ_W`. -/
private theorem complexProdTensor_complexVolume_eq_map_pow (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (hb₁ : b₁.toBasis.orientation = o₁) (b₂ : OrthonormalBasis (Fin m) ℝ W)
    (hb₂ : b₂.toBasis.orientation = o₂) (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
    (ho : ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁) ^ (m + 1)) (ρ₂ (complexVolume Q₂ o₂)) := by
  have hQb₁ := b₁.isOrthoᵢ_associated hQ₁
  rw [complexProdTensor_complexVolume_eq_map hQ o₁ hQ₁ hn ρ₁ ρ₂ o b₁ hQb₁ b₂ hQb₂ ho, pow_succ']
  -- Only the first factor `Γ_V` of `Γ_V ^ (m + 1) = Γ_V * Γ_V ^ m` is expanded in the frame.
  generalize ρ₁ (complexVolume Q₁ o₁) ^ m = g
  rw [complexVolume_eq o₁ b₁ hb₁ hQb₁, complexVolume_eq o₂ b₂ hb₂ hQb₂]
  simp only [map_smul, smul_mul_assoc, TensorProduct.map_smul_left, TensorProduct.map_smul_right,
    smul_smul, ← pow_add]
  congr 2
  obtain ⟨j, hj⟩ := hn
  omega

/-- **Volume elements of `V ⊕ W` compare as a tensor product**: for `V` and `W` of even dimension
with `Q₁ v = -‖v‖²`, and `V ⊕ W` oriented by the concatenation `(e₁, …, eₙ, f₁, …, fₘ)` of a
positively oriented orthonormal frame of `V` and a positively oriented orthonormal frame of `W`
orthogonal for `Q₂`, the normalized volume element of `V ⊕ W` acts on the graded tensor product
`E ⊗ F` by `Γ_V ⊗ Γ_W`. When also `Q₂ w = -‖w‖²`, so that `Γ_W` is the chirality of `W`, this says
the chirality of `V ⊕ W` is the tensor grading. -/
theorem complexProdTensor_complexVolume (hm : Even m) (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (hb₁ : b₁.toBasis.orientation = o₁) (b₂ : OrthonormalBasis (Fin m) ℝ W)
    (hb₂ : b₂.toBasis.orientation = o₂) (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
    (ho : ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  rw [complexProdTensor_complexVolume_eq_map_pow hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o b₁ hb₁ b₂ hb₂ hQb₂ ho,
    pow_succ, map_complexVolume_pow_of_even o₁ hQ₁ ρ₁ hm, one_mul]

/-- **For odd `W` the volume element of `V ⊕ W` acts through `W` alone**: for `V` of even and `W`
of odd dimension, with `Q₁ v = -‖v‖²` and the ordered product orientation, the normalized volume
element of `V ⊕ W` acts on the graded tensor product `E ⊗ F` by `1 ⊗ ω_W`. -/
theorem complexProdTensor_complexVolume_of_odd (hm : Odd m) (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (hb₁ : b₁.toBasis.orientation = o₁) (b₂ : OrthonormalBasis (Fin m) ℝ W)
    (hb₂ : b₂.toBasis.orientation = o₂) (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
    (ho : ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  rw [complexProdTensor_complexVolume_eq_map_pow hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o b₁ hb₁ b₂ hb₂ hQb₂ ho,
    map_complexVolume_pow_of_even o₁ hQ₁ ρ₁ hm.add_one, LinearMap.lTensor, Module.End.one_eq_id]

/-! ### Frame-free product orientations -/

/-- Reduction of frame-free product-volume formulas from arbitrary orientations `(o₁, o₂)` to
the standard-basis orientations `(b₁.toBasis.orientation, b₂.toBasis.orientation)` via
`orientation_eq_or_eq_neg`. -/
private theorem complexProdTensor_complexVolume_of_map_prod_aux
    (Rhs : (CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F) →
      Orientation ℝ V (Fin n) → Orientation ℝ W (Fin m) → Module.End ℂ (E ⊗[ℂ] F))
    (hbase : ∀ (b₁ : OrthonormalBasis (Fin n) ℝ V) (b₂ : OrthonormalBasis (Fin m) ℝ W)
      (_hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
      (ρ₂' : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F),
      complexProdTensor hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂'
          (complexVolume Q
            ((b₁.toBasis.orientation.prod b₂.toBasis.orientation Fact.out Fact.out).map
              (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
        Rhs ρ₂' b₁.toBasis.orientation b₂.toBasis.orientation)
    (hneg_right : ∀ ρ₂' o₁' o₂', Rhs ρ₂' o₁' (-o₂') = -Rhs ρ₂' o₁' o₂')
    (hneg_left : ∀ ρ₂' o₁' o₂', Rhs ρ₂' (-o₁') o₂' = -Rhs (ρ₂'.comp involute) o₁' o₂')
    (ho : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) = Rhs ρ₂ o₁ o₂ := by
  let b₁ : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  obtain ⟨b₂, hQb₂⟩ := Q₂.exists_orthonormalBasis_isOrthoᵢ_associated (Fact.out : finrank ℝ W = m)
  have hpos (ρ₂' : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
      (o₂' : Orientation ℝ W (Fin m)) :
      complexProdTensor hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂'
          (complexVolume Q ((b₁.toBasis.orientation.prod o₂' Fact.out Fact.out).map (Fin (n + m))
            (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
        Rhs ρ₂' b₁.toBasis.orientation o₂' := by
    rcases b₂.toBasis.orientation_eq_or_eq_neg o₂' with rfl | rfl
    · exact hbase b₁ b₂ hQb₂ ρ₂'
    · rw [Orientation.map_prod_neg_right, complexVolume_neg_orientation, map_neg,
        hbase b₁ b₂ hQb₂ ρ₂', hneg_right]
  subst ho
  rcases b₁.toBasis.orientation_eq_or_eq_neg o₁ with rfl | rfl
  · exact hpos ρ₂ o₂
  · rw [Orientation.map_prod_neg_left, complexVolume_neg_orientation, map_neg,
      complexProdTensor_neg_orientation_eq_involute, hpos (ρ₂.comp involute) o₂, hneg_left]

/-- **Frame-free product chirality**: for even `n` and `m`, `Q₁ v = -‖v‖²`, any quadratic form
`Q₂` on `W`, and `V ⊕ W` oriented by transporting `o₁.prod o₂` along
`(WithLp.linearEquiv 2 ℝ (V × W)).symm`, the normalized complex volume element of `V ⊕ W` acts on
`E ⊗ F` by `Γ_V ⊗ Γ_W`. This holds for every pair of orientations `(o₁, o₂)`, including
`-positiveOrientation` in dimension zero. -/
theorem complexProdTensor_complexVolume_of_map_prod (hm : Even m)
    (ho : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) :=
  complexProdTensor_complexVolume_of_map_prod_aux hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o
    (fun ρ₂' o₁' o₂' ↦ TensorProduct.map (ρ₁ (complexVolume Q₁ o₁')) (ρ₂' (complexVolume Q₂ o₂')))
    (fun b₁ b₂ hQb₂ ρ₂' ↦ complexProdTensor_complexVolume hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂'
      b₂.toBasis.orientation _ hm b₁ rfl b₂ rfl hQb₂
      (b₁.orientation_reindex_prod b₂ Fact.out Fact.out))
    (fun ρ₂' o₁' o₂' ↦ by simp)
    (fun ρ₂' o₁' o₂' ↦ by simp [hm.neg_one_pow])
    ho

/-- **Frame-free odd product volume**: for even `n` and odd `m`, `Q₁ v = -‖v‖²`, any quadratic form
`Q₂` on `W`, and `V ⊕ W` oriented by `o₁.prod o₂`, the normalized complex volume element of
`V ⊕ W` acts on `E ⊗ F` by `1 ⊗ ω_W`, for every orientation `o₁` of `V` (including in rank zero). -/
theorem complexProdTensor_complexVolume_of_odd_of_map_prod (hm : Odd m)
    (ho : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      (ρ₂ (complexVolume Q₂ o₂)).lTensor E :=
  complexProdTensor_complexVolume_of_map_prod_aux hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o
    (fun ρ₂' _ o₂' ↦ (ρ₂' (complexVolume Q₂ o₂')).lTensor E)
    (fun b₁ b₂ hQb₂ ρ₂' ↦ complexProdTensor_complexVolume_of_odd hQ b₁.toBasis.orientation hQ₁ hn ρ₁
      ρ₂' b₂.toBasis.orientation _ hm b₁ rfl b₂ rfl hQb₂
      (b₁.orientation_reindex_prod b₂ Fact.out Fact.out))
    (fun ρ₂' _ o₂' ↦ by simp)
    (fun ρ₂' _ o₂' ↦ by simp [hm.neg_one_pow])
    ho

/-- **Product chirality under orientation reversal (frame-free)**: for even `n` and `m`, reversing
`o₁` to `-o₁` reverses the product orientation `o` to `-o` (`Orientation.prod_neg_left`) and
negates the action of the product chirality on `E ⊗ F`. -/
theorem complexProdTensor_neg_orientation_complexVolume_neg_of_map_prod (hm : Even m)
    (ho : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (complexVolume Q (-o)) =
      -complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) := by
  have ho' : ((-o₁).prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = -o := by
    rw [Orientation.map_prod_neg_left, ho]
  rw [complexProdTensor_complexVolume_of_map_prod hQ (-o₁) hQ₁ hn ρ₁ ρ₂ o₂ (-o) hm ho',
    complexProdTensor_complexVolume_of_map_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hm ho]
  simp [TensorProduct.map_neg_left]

end SecondFactor

end CliffordAlgebra
