/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod
public import TauCeti.LinearAlgebra.Orientation.Prod
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Prod
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# Orientation reversal and product orientations for graded Clifford tensor products

Let `V` and `W` be real inner product spaces with `V` oriented of even dimension `n`,
`Q₁ v = -‖v‖²`, `Q (v, w) = Q₁ v + Q₂ w` on `WithLp 2 (V × W)`, and let `E`, `F` be complex
Clifford modules over `Q₁`, `Q₂`. Reversing `o₁` negates `Γ_V`, replacing `c(0, w) = Γ_V ⊗ c_W(w)`
by `-Γ_V ⊗ c_W(w)` (equivalently twisting `ρ₂` by `CliffordAlgebra.involute`). This file upgrades
the product-volume formulas of `VolumeElement/Prod.lean` to the frame-free product orientation
`Orientation.prod o₁ o₂` for all orientations (including `-positiveOrientation` in dimension zero).

## Main results

* `CliffordAlgebra.complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr` and
  `CliffordAlgebra.complexProdTensor_neg_orientation_ι_one_tmul_toLp`: reversing `o₁` negates the
  action of `(0, w)`.
* `CliffordAlgebra.complexProdTensor_complexVolume_of_map_prod` and
  `CliffordAlgebra.complexProdTensor_complexVolume_of_odd_of_map_prod`: frame-free product-volume
  formulas for `(o₁.prod o₂).map _ (WithLp.linearEquiv 2 ℝ (V × W)).symm`.
* `CliffordAlgebra.complexProdTensor_neg_orientation_complexVolume_neg_of_map_prod`: frame-free
  version of `complexProdTensor_neg_orientation_complexVolume_neg`.

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

private theorem map_neg_left (f : Module.End ℂ E) (g : Module.End ℂ F) :
    TensorProduct.map (-f) g = -TensorProduct.map f g := by ext; simp [TensorProduct.neg_tmul]

private theorem map_neg_right (f : Module.End ℂ E) (g : Module.End ℂ F) :
    TensorProduct.map f (-g) = -TensorProduct.map f g := by ext; simp [TensorProduct.tmul_neg]

/-- Reversing the orientation of `V` negates the action of `(0, w)` on `E ⊗ F`:
`c_{-o₁}(0, w) = -Γ_V ⊗ c_W(w)`. -/
theorem complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr (w : W) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) =
      -TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) := by
  rw [complexProdTensor_ι_one_tmul_toLp_inr, complexVolume_neg_orientation, map_neg, map_neg_left]

/-- Reversing the orientation of `V` replaces `c(v, w) = c_V(v) ⊗ 1 + Γ_V ⊗ c_W(w)` by
`c_V(v) ⊗ 1 - Γ_V ⊗ c_W(w)`. -/
theorem complexProdTensor_neg_orientation_ι_one_tmul_toLp (v : V) (w : W) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, w))) =
      (ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v))).rTensor F -
        TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) := by
  rw [complexProdTensor_ι_one_tmul_toLp, complexVolume_neg_orientation, map_neg, map_neg_left,
    sub_eq_add_neg]

private theorem complexProdTensor_neg_orientation_eq_involute :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ (ρ₂.comp involute) := by
  refine AlgHom.toRingHom_injective <| baseChange_ringHom_ext Q (fun _ ↦ by simp) fun x ↦ ?_
  rcases x with ⟨⟨v, w⟩⟩
  simp [map_neg_left, map_neg_right]

section SecondFactor

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))

/-! ### Frame-free product orientations -/

variable [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
  (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))

/-- **Frame-free product chirality**: for even `n` and `m`, `Q₁ v = -‖v‖²`, `Q₂ w = -‖w‖²`, and
`V ⊕ W` oriented by transporting `o₁.prod o₂` along `(WithLp.linearEquiv 2 ℝ (V × W)).symm`, the
normalized complex volume element of `V ⊕ W` acts on `E ⊗ F` by `Γ_V ⊗ Γ_W`. This holds for every
pair of orientations `(o₁, o₂)`, including `-positiveOrientation` in dimension zero. -/
theorem complexProdTensor_complexVolume_of_map_prod (hm : Even m) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (ho : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  let b₁ : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  let b₂ : OrthonormalBasis (Fin m) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr Fact.out)
  have hpos (ρ₂' : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
      (o₂' : Orientation ℝ W (Fin m)) :
      complexProdTensor hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂'
          (complexVolume Q ((b₁.toBasis.orientation.prod o₂' Fact.out Fact.out).map (Fin (n + m))
            (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
        TensorProduct.map (ρ₁ (complexVolume Q₁ b₁.toBasis.orientation))
          (ρ₂' (complexVolume Q₂ o₂')) := by
    have hbase := complexProdTensor_complexVolume hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂'
      b₂.toBasis.orientation _ hm b₁ rfl b₂ rfl (b₂.isOrthoᵢ_associated hQ₂)
      (b₁.orientation_reindex_prod b₂ Fact.out Fact.out)
    rcases b₂.toBasis.orientation_eq_or_eq_neg o₂' with rfl | rfl
    · exact hbase
    · rw [Orientation.prod_neg_right, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
        complexVolume_neg_orientation, map_neg, map_neg_right, hbase]
  subst ho
  rcases b₁.toBasis.orientation_eq_or_eq_neg o₁ with rfl | rfl
  · exact hpos ρ₂ o₂
  · rw [Orientation.prod_neg_left, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
      complexVolume_neg_orientation, map_neg, map_neg_left,
      complexProdTensor_neg_orientation_eq_involute, hpos (ρ₂.comp involute) o₂,
      AlgHom.comp_apply, involute_complexVolume, hm.neg_one_pow, one_smul]

/-- **Frame-free odd product volume**: for even `n` and odd `m`, `Q₁ v = -‖v‖²`, `Q₂ w = -‖w‖²`,
and `V ⊕ W` oriented by `o₁.prod o₂`, the normalized complex volume element of `V ⊕ W` acts on
`E ⊗ F` by `1 ⊗ ω_W`, for every orientation `o₁` of `V` (including in rank zero). -/
theorem complexProdTensor_complexVolume_of_odd_of_map_prod (hm : Odd m)
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (ho : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  let b₁ : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  let b₂ : OrthonormalBasis (Fin m) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr Fact.out)
  have hpos (ρ₂' : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
      (o₂' : Orientation ℝ W (Fin m)) :
      complexProdTensor hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂'
          (complexVolume Q ((b₁.toBasis.orientation.prod o₂' Fact.out Fact.out).map (Fin (n + m))
            (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
        (ρ₂' (complexVolume Q₂ o₂')).lTensor E := by
    have hbase := complexProdTensor_complexVolume_of_odd hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂'
      b₂.toBasis.orientation _ hm b₁ rfl b₂ rfl (b₂.isOrthoᵢ_associated hQ₂)
      (b₁.orientation_reindex_prod b₂ Fact.out Fact.out)
    rcases b₂.toBasis.orientation_eq_or_eq_neg o₂' with rfl | rfl
    · exact hbase
    · rw [Orientation.prod_neg_right, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
        complexVolume_neg_orientation, map_neg, LinearMap.lTensor_neg, hbase]
  subst ho
  rcases b₁.toBasis.orientation_eq_or_eq_neg o₁ with rfl | rfl
  · exact hpos ρ₂ o₂
  · rw [Orientation.prod_neg_left, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
      complexProdTensor_neg_orientation_eq_involute, hpos (ρ₂.comp involute) o₂,
      AlgHom.comp_apply, involute_complexVolume, hm.neg_one_pow, neg_one_smul, map_neg,
      LinearMap.lTensor_neg, neg_neg]

/-- **Product chirality under orientation reversal (frame-free)**: for even `n` and `m`, reversing
`o₁` to `-o₁` reverses the product orientation `o` to `-o` (`Orientation.prod_neg_left`) and
negates the action of the product chirality on `E ⊗ F`. -/
theorem complexProdTensor_neg_orientation_complexVolume_neg_of_map_prod (hm : Even m)
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (ho : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (complexVolume Q (-o)) =
      -complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) := by
  have ho' : ((-o₁).prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = -o := by
    rw [Orientation.prod_neg_left, Orientation.map_neg, ho]
  rw [complexProdTensor_complexVolume_of_map_prod hQ (-o₁) hQ₁ hn ρ₁ ρ₂ o₂ (-o) hm hQ₂ ho',
    complexProdTensor_complexVolume_of_map_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hm hQ₂ ho,
    complexVolume_neg_orientation, map_neg, map_neg_left]

end SecondFactor

end CliffordAlgebra
