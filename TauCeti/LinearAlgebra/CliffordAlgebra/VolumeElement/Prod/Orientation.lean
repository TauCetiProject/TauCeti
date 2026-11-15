/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic
public import TauCeti.LinearAlgebra.Orientation.Prod
-- Private: negated-grading intertwining and orthonormal-basis polar orthogonality are proof-only.
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Neg

/-!
# Orientation reversal and frame-free product orientations for `complexProdTensor`

Let `V` and `W` be oriented real inner product spaces of dimensions `n` and `m`, with `n` even and
`Q₁ v = -‖v‖²`. Reversing the orientation of `V` from `o₁` to `-o₁` negates its chirality `Γ_V`
(`CliffordAlgebra.complexVolume_neg_orientation`). In the graded tensor product
`CliffordAlgebra.complexProdTensor` on `E ⊗ F`:

* Vectors `(v, 0)` of `V` still act by `c_V(v) ⊗ 1`, while vectors `(0, w)` of `W` act by
  `-Γ_V ⊗ c_W(w)`: as an algebra homomorphism, `complexProdTensor` for `-o₁` equals
  `complexProdTensor` for `o₁` with `ρ₂` precomposed with the grade involution
  `CliffordAlgebra.involute` (`CliffordAlgebra.complexProdTensor_neg_orientation_eq_comp_involute`).
* When `m` is even, `Γ_W` anticommutes with every vector of `W`, so `1 ⊗ Γ_W` intertwines the
  `-o₁` and `o₁` product actions on the entire complexified Clifford algebra
  (`CliffordAlgebra.lTensor_complexVolume_comp_complexProdTensor_neg_orientation`). When moreover
  `Q₂ w = -‖w‖²`, conjugation by `1 ⊗ Γ_W` identifies the two algebra maps
  (`CliffordAlgebra.conjAlgEquiv_complexProdTensor_neg_orientation`).

Using the canonical frame-free product orientation `Orientation.prod o₁ o₂` transported along
`(WithLp.linearEquiv 2 ℝ (V × W)).symm`, the volume formulas of
`TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement/Prod/Basic.lean` hold without choosing frames,
including in rank zero and for negative orientations
(`CliffordAlgebra.complexProdTensor_complexVolume_of_prod` and
`CliffordAlgebra.complexProdTensor_complexVolume_of_odd_of_prod`). Reversing `o₁` to `-o₁`
reverses the product orientation `o` to `-o` (`Orientation.prod_neg_left`), so the product chirality
changes sign (`CliffordAlgebra.complexProdTensor_neg_orientation_complexVolume_neg`).

## Main results

* `CliffordAlgebra.complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr`: reversing `o₁` replaces
  `c(0, w)` by `-Γ_V ⊗ c_W(w)`.
* `CliffordAlgebra.complexProdTensor_neg_orientation_eq_comp_involute`: reversing `o₁` twists `ρ₂`
  by `CliffordAlgebra.involute`.
* `CliffordAlgebra.lTensor_complexVolume_comp_complexProdTensor_neg_orientation` and
  `CliffordAlgebra.conjAlgEquiv_complexProdTensor_neg_orientation`: for `m` even, `1 ⊗ Γ_W`
  intertwines the `-o₁` and `o₁` product actions.
* `CliffordAlgebra.complexProdTensor_complexVolume_of_prod` and
  `CliffordAlgebra.complexProdTensor_complexVolume_of_odd_of_prod`: frame-free product volume
  formulas for `Orientation.prod o₁ o₂`.
* `CliffordAlgebra.complexProdTensor_neg_orientation_complexVolume_neg`: reversing `o₁` (and thus
  the product orientation) negates the product chirality `Γ_V ⊗ Γ_W`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
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

/-! ### Reversing the orientation of the first factor -/

/-- Reversing the orientation of `V` negates the second summand's term in `c(v, w)`:
`c_{-o₁}(v, w) = c_V(v) ⊗ 1 - Γ_V ⊗ c_W(w)`. -/
theorem complexProdTensor_neg_orientation_ι_one_tmul_toLp (v : V) (w : W) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, w))) =
      (ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v))).rTensor F -
        TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) := by
  apply TensorProduct.ext'
  intro e f
  simp [complexProdTensor_ι_one_tmul_toLp, sub_eq_add_neg, TensorProduct.neg_tmul]

/-- **Orientation reversal on vectors of `W`**: reversing the orientation of `V` replaces `c(0, w)`
by `-Γ_V ⊗ c_W(w)`. -/
theorem complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr (w : W) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) =
      -TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) := by
  apply TensorProduct.ext'
  intro e f
  simp [TensorProduct.neg_tmul]

/-- **Orientation reversal twists the second factor by the grade involution**: `complexProdTensor`
for `-o₁` coincides with `complexProdTensor` for `o₁` applied to `ρ₂ ∘ involute`. -/
theorem complexProdTensor_neg_orientation_eq_comp_involute :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ (ρ₂.comp (involute (Q := Q₂.baseChange ℂ))) := by
  refine baseChange_algHom_ext Q fun x ↦ ?_
  apply TensorProduct.ext'
  intro e f
  have hx : x = WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2) := rfl
  rw [hx]
  simp [complexProdTensor_ι_one_tmul_toLp, TensorProduct.neg_tmul, TensorProduct.tmul_neg]

section EvenSecondFactor

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))

/-- **Intertwining orientation reversal by `1 ⊗ Γ_W`**: when `W` has even dimension `m`, the
operator `1 ⊗ Γ_W` (`(ρ₂ (complexVolume Q₂ o₂)).lTensor E`) intertwines `complexProdTensor` for
`-o₁` with `complexProdTensor` for `o₁` on every element of `CliffordAlgebra (Q.baseChange ℂ)`. No
metric assumption on `Q₂` is required. -/
theorem lTensor_complexVolume_comp_complexProdTensor_neg_orientation (hm : Even m)
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (ρ₂ (complexVolume Q₂ o₂)).lTensor E ∘ₗ complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ a =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a ∘ₗ (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  induction a using CliffordAlgebra.induction with
  | algebraMap z =>
    ext t
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
      apply TensorProduct.ext'
      intro e f
      have hanti : ρ₂ (complexVolume Q₂ o₂) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)) f) =
          -ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)) (ρ₂ (complexVolume Q₂ o₂) f) := by
        rw [← mul_apply_eq_comp, ← map_mul, complexVolume_mul_ι_of_even o₂ hm, map_neg, map_mul,
          LinearMap.neg_apply, mul_apply_eq_comp]
      rw [LinearMap.comp_apply, LinearMap.comp_apply, complexProdTensor_ι_one_tmul_toLp,
        complexProdTensor_ι_one_tmul_toLp]
      simp [hanti, TensorProduct.tmul_neg, TensorProduct.neg_tmul]
    | add y z hy hz =>
      simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hy, hz]
  | add a b ha hb =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, ha, hb]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha]
    rw [LinearMap.comp_assoc, hb, ← LinearMap.comp_assoc]

/-- Pointwise form of
`CliffordAlgebra.lTensor_complexVolume_comp_complexProdTensor_neg_orientation`. -/
theorem lTensor_complexVolume_complexProdTensor_neg_orientation (hm : Even m)
    (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] F) :
    (ρ₂ (complexVolume Q₂ o₂)).lTensor E (complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ a z) =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a ((ρ₂ (complexVolume Q₂ o₂)).lTensor E z) :=
  LinearMap.congr_fun
    (lTensor_complexVolume_comp_complexProdTensor_neg_orientation hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm a) z

/-- When `m` is even and `Q₂ w = -‖w‖²`, conjugating `complexProdTensor` for `-o₁` by the linear
involution `1 ⊗ Γ_W` yields `complexProdTensor` for `o₁`. -/
theorem conjAlgEquiv_complexProdTensor_neg_orientation (hm : Even m)
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) :
    (((LinearEquiv.ofInvolutive (ρ₂ (complexVolume Q₂ o₂))
        (involutive_apply_complexVolume o₂ hQ₂ ρ₂)).lTensor E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂) =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ := by
  let hinv := involutive_apply_complexVolume o₂ hQ₂ ρ₂
  refine baseChange_algHom_ext Q fun x ↦ ?_
  apply TensorProduct.ext'
  intro e f
  let v := (WithLp.ofLp x).1
  let w := (WithLp.ofLp x).2
  have hx : x = WithLp.toLp 2 (v, w) := rfl
  have hsymm : (LinearEquiv.ofInvolutive (ρ₂ (complexVolume Q₂ o₂)) hinv).symm f =
      ρ₂ (complexVolume Q₂ o₂) f := rfl
  have hanti : ρ₂ (complexVolume Q₂ o₂)
      (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)) (ρ₂ (complexVolume Q₂ o₂) f)) =
        -ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)) f := by
    rw [← mul_apply_eq_comp, ← map_mul, complexVolume_mul_ι_of_even o₂ hm, map_neg, map_mul,
      LinearMap.neg_apply, mul_apply_eq_comp, hinv f]
  rw [hx, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, complexProdTensor_ι_one_tmul_toLp]
  simp [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.lTensor, hsymm, hinv f, hanti,
    TensorProduct.tmul_neg, TensorProduct.neg_tmul]

/-! ### Frame-free product orientation formulas -/

/-- The orientation of the reindexed `L²` product of two orthonormal bases is the canonical
`Orientation.prod` of their orientations transported along
`(WithLp.linearEquiv 2 ℝ (V × W)).symm`. -/
private theorem orientation_reindex_prod_orthonormalBasis (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (b₂ : OrthonormalBasis (Fin m) ℝ W) :
    ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation =
      (Orientation.prod b₁.toBasis.orientation b₂.toBasis.orientation
        Fact.out Fact.out).map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm := by
  rw [Orientation.prod_basis_orientation, ← Basis.orientation_map]
  congr 1
  refine Basis.eq_of_apply_eq (Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_)) <;>
    simp [Basis.prod_apply]

variable [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]

/-- **Frame-free chirality of `V ⊕ W` for even `W`**: when `V` and `W` have even dimensions `n` and
`m` with `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, and `o` is the canonical product orientation
`Orientation.prod o₁ o₂` transported to `WithLp 2 (V × W)`, the normalized volume element of
`V ⊕ W` acts on `E ⊗ F` by `Γ_V ⊗ Γ_W`. This holds for all even `n` and `m`, including rank zero
and negative orientations. -/
theorem complexProdTensor_complexVolume_of_prod (hm : Even m) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    {o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))}
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  subst ho
  let b₁ : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  let b₂ : OrthonormalBasis (Fin m) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr Fact.out)
  have hbase (ρ₂' : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F) :
      complexProdTensor hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂'
        (complexVolume Q ((Orientation.prod b₁.toBasis.orientation b₂.toBasis.orientation
          Fact.out Fact.out).map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
        TensorProduct.map (ρ₁ (complexVolume Q₁ b₁.toBasis.orientation))
          (ρ₂' (complexVolume Q₂ b₂.toBasis.orientation)) :=
    complexProdTensor_complexVolume hQ _ hQ₁ hn ρ₁ ρ₂' _ _ hm b₁ rfl b₂ rfl
      (b₂.isOrthoᵢ_associated hQ₂) (orientation_reindex_prod_orthonormalBasis b₁ b₂)
  have hneg_map (u : Module.End ℂ E) (v : Module.End ℂ F) :
      TensorProduct.map (-u) v = -TensorProduct.map u v ∧
        TensorProduct.map u (-v) = -TensorProduct.map u v :=
    ⟨TensorProduct.ext' fun e f ↦ by simp [TensorProduct.neg_tmul],
      TensorProduct.ext' fun e f ↦ by simp [TensorProduct.tmul_neg]⟩
  rcases b₁.toBasis.orientation_eq_or_eq_neg o₁ with rfl | rfl <;>
    rcases b₂.toBasis.orientation_eq_or_eq_neg o₂ with rfl | rfl
  · exact hbase ρ₂
  · simp only [Orientation.prod_neg_right, Orientation.map_neg, complexVolume_neg_orientation,
      map_neg, hbase ρ₂, (hneg_map _ _).2]
  · simp only [Orientation.prod_neg_left, Orientation.map_neg, complexVolume_neg_orientation,
      map_neg, complexProdTensor_neg_orientation_eq_comp_involute, hbase, AlgHom.comp_apply,
      involute_complexVolume, hm.neg_one_pow, one_smul, (hneg_map _ _).1]
  · simp only [Orientation.prod_neg_neg, complexVolume_neg_orientation, map_neg,
      complexProdTensor_neg_orientation_eq_comp_involute, hbase, AlgHom.comp_apply,
      involute_complexVolume, hm.neg_one_pow, one_smul, (hneg_map _ _).1, (hneg_map _ _).2,
      neg_neg]

/-- **Frame-free volume element of `V ⊕ W` for odd `W`**: when `V` has even dimension `n` with
`Q₁ v = -‖v‖²`, `W` has odd dimension `m` with `Q₂ w = -‖w‖²`, and `o` is the canonical product
orientation `Orientation.prod o₁ o₂` transported to `WithLp 2 (V × W)`, the normalized volume
element of `V ⊕ W` acts on `E ⊗ F` by `1 ⊗ ω_W`, for all orientations `o₁` and `o₂` (including
`n = 0`). -/
theorem complexProdTensor_complexVolume_of_odd_of_prod (hm : Odd m) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    {o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))}
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  subst ho
  let b₁ : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  let b₂ : OrthonormalBasis (Fin m) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr Fact.out)
  have hbase (ρ₂' : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F) :
      complexProdTensor hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂'
        (complexVolume Q ((Orientation.prod b₁.toBasis.orientation b₂.toBasis.orientation
          Fact.out Fact.out).map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
        (ρ₂' (complexVolume Q₂ b₂.toBasis.orientation)).lTensor E :=
    complexProdTensor_complexVolume_of_odd hQ _ hQ₁ hn ρ₁ ρ₂' _ _ hm b₁ rfl b₂ rfl
      (b₂.isOrthoᵢ_associated hQ₂) (orientation_reindex_prod_orthonormalBasis b₁ b₂)
  rcases b₁.toBasis.orientation_eq_or_eq_neg o₁ with rfl | rfl <;>
    rcases b₂.toBasis.orientation_eq_or_eq_neg o₂ with rfl | rfl
  · exact hbase ρ₂
  · simp only [Orientation.prod_neg_right, Orientation.map_neg, complexVolume_neg_orientation,
      map_neg, hbase ρ₂, LinearMap.lTensor_neg]
  · simp only [Orientation.prod_neg_left, Orientation.map_neg, complexVolume_neg_orientation,
      map_neg, complexProdTensor_neg_orientation_eq_comp_involute, hbase, AlgHom.comp_apply,
      involute_complexVolume, hm.neg_one_pow, neg_one_smul, LinearMap.lTensor_neg, neg_neg]
  · simp only [Orientation.prod_neg_neg, complexVolume_neg_orientation, map_neg,
      complexProdTensor_neg_orientation_eq_comp_involute, hbase, AlgHom.comp_apply,
      involute_complexVolume, hm.neg_one_pow, neg_one_smul]

/-- **Orientation reversal negates the product chirality**: when `V` and `W` are even-dimensional
with `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, reversing `o₁` to `-o₁` reverses the product orientation
`o` to `-o`, and the action of the product chirality `complexVolume Q (-o)` in the `-o₁`-graded
tensor product is `-(Γ_V ⊗ Γ_W)`. -/
theorem complexProdTensor_neg_orientation_complexVolume_neg (hm : Even m)
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) {o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))}
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (complexVolume Q (-o)) =
      -TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  have ho' : (Orientation.prod (-o₁) o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = -o := by
    rw [Orientation.prod_neg_left, Orientation.map_neg, ho]
  rw [complexProdTensor_complexVolume_of_prod hQ (-o₁) hQ₁ hn ρ₁ ρ₂ o₂ hm hQ₂ ho',
    complexVolume_neg_orientation, map_neg]
  exact TensorProduct.ext' fun e f ↦ by simp [TensorProduct.neg_tmul]

end EvenSecondFactor

end CliffordAlgebra
