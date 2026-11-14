/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic
public import TauCeti.LinearAlgebra.Orientation.Prod
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Prod
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# Orientation reversal and product orientations for graded Clifford tensor products

Let `V` and `W` be real inner product spaces with `V` oriented and of even dimension `n`,
`Q₁ v = -‖v‖²`, `Q (v, w) = Q₁ v + Q₂ w` on `WithLp 2 (V × W)`, and let `E` and `F` be complex
Clifford modules over `Q₁` and `Q₂`.

Reversing the orientation `o₁` of `V` negates its chirality operator `Γ_V`
(`CliffordAlgebra.complexVolume_neg_orientation`), so `CliffordAlgebra.complexProdTensor` replaces
`c(0, w) = Γ_V ⊗ c_W(w)` by `-Γ_V ⊗ c_W(w)` while leaving `c(v, 0) = c_V(v) ⊗ 1` unchanged. When
`W` is also oriented and of even dimension `m`, its volume element `Γ_W` anticommutes with every
vector of `W`, so the operator `1 ⊗ Γ_W` (`(ρ₂ (complexVolume Q₂ o₂)).lTensor E`) intertwines the
two product actions on all of `CliffordAlgebra (Q.baseChange ℂ)`.

This file also upgrades the volume-element comparison formulas of
`TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement/Prod/Basic.lean` from explicit positively
oriented frames to the canonical product orientation `Orientation.prod o₁ o₂` transported to
`WithLp 2 (V × W)`. Because `Orientation.prod` retains both signs in dimension zero, these
frame-free formulas hold unconditionally for every pair of orientations `(o₁, o₂)`, including the
negative orientation of a zero-dimensional summand; reversing `o₁` reverses the product orientation
and negates the product chirality `-Γ_V ⊗ Γ_W`.

## Main results

* `CliffordAlgebra.complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr` and
  `CliffordAlgebra.complexProdTensor_neg_orientation_ι_one_tmul_toLp`: reversing `o₁` negates the
  action of `(0, w)`.
* `CliffordAlgebra.lTensor_complexVolume_comp_complexProdTensor_neg_orientation`: for even `m`,
  `1 ⊗ Γ_W` intertwines `complexProdTensor` for `-o₁` and `o₁`.
* `CliffordAlgebra.complexProdTensor_complexVolume_of_map_prod` and
  `CliffordAlgebra.complexProdTensor_complexVolume_of_odd_of_map_prod`: frame-free product-volume
  formulas for `(o₁.prod o₂).map _ (WithLp.linearEquiv 2 ℝ (V × W)).symm`.
* `CliffordAlgebra.complexProdTensor_neg_orientation_complexVolume_neg`: reversing `o₁` and the
  product orientation negates the product chirality.

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
    TensorProduct.map (-f) g = -TensorProduct.map f g := by
  ext; simp [TensorProduct.neg_tmul]

private theorem map_neg_right (f : Module.End ℂ E) (g : Module.End ℂ F) :
    TensorProduct.map f (-g) = -TensorProduct.map f g := by
  ext; simp [TensorProduct.tmul_neg]

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

section SecondFactor

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))

/-- **Intertwining under orientation reversal of `V`.** When `W` is also oriented of even dimension
`m`, the operator `1 ⊗ Γ_W` (`(ρ₂ (complexVolume Q₂ o₂)).lTensor E`) intertwines the graded tensor
product actions for `-o₁` and `o₁` on every element of `CliffordAlgebra (Q.baseChange ℂ)`. No
assumption on `Q₂` is needed. -/
theorem lTensor_complexVolume_comp_complexProdTensor_neg_orientation (hm : Even m)
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (ρ₂ (complexVolume Q₂ o₂)).lTensor E ∘ₗ complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ a =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a ∘ₗ (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  have hgen (z : ℂ ⊗[ℝ] WithLp 2 (V × W)) :
      (ρ₂ (complexVolume Q₂ o₂)).lTensor E ∘ₗ
          complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (ι (Q.baseChange ℂ) z) =
        complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
            (ι (Q.baseChange ℂ) (QuadraticMap.Isometry.id (Q.baseChange ℂ) z)) ∘ₗ
          (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
    induction z using TensorProduct.inductionOn with
    | tmul c x =>
      have hc : c ⊗ₜ[ℝ] x = c • ((1 : ℂ) ⊗ₜ[ℝ] WithLp.toLp 2 (WithLp.ofLp x)) := by
        rw [WithLp.toLp_ofLp, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hanti : ρ₂ (complexVolume Q₂ o₂) * ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ (WithLp.ofLp x).2)) =
          -(ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ (WithLp.ofLp x).2)) * ρ₂ (complexVolume Q₂ o₂)) := by
        rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₂ hm, map_neg]
      simp only [QuadraticMap.Isometry.id_apply, hc, map_smul, LinearMap.comp_smul,
        LinearMap.smul_comp]
      congr 1
      rw [complexProdTensor_neg_orientation_ι_one_tmul_toLp, complexProdTensor_ι_one_tmul_toLp]
      simp only [LinearMap.lTensor, LinearMap.rTensor, ← Module.End.mul_eq_comp,
        ← Module.End.one_eq_id, mul_sub, add_mul, ← TensorProduct.map_mul,
        one_mul, mul_one, hanti, map_neg_right, sub_neg_eq_add]
    | add x y hx hy =>
      simp only [QuadraticMap.Isometry.id_apply] at hx hy ⊢
      simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hx, hy]
  simpa [CliffordAlgebra.map_id] using comp_eq_map_comp_of_forall_ι hgen a

/-- Pointwise form of
`CliffordAlgebra.lTensor_complexVolume_comp_complexProdTensor_neg_orientation`. -/
theorem lTensor_complexVolume_complexProdTensor_neg_orientation_apply (hm : Even m)
    (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] F) :
    (ρ₂ (complexVolume Q₂ o₂)).lTensor E (complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ a z) =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a ((ρ₂ (complexVolume Q₂ o₂)).lTensor E z) :=
  LinearMap.congr_fun
    (lTensor_complexVolume_comp_complexProdTensor_neg_orientation hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm a) z

/-! ### Frame-free product orientations -/

variable [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
  (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))

/-- **Frame-free product chirality**: for even `n` and `m`, `Q₁ v = -‖v‖²`, `Q₂ w = -‖w‖²`, and
`V ⊕ W` oriented by transporting `o₁.prod o₂` along `(WithLp.linearEquiv 2 ℝ (V × W)).symm`, the
normalized complex volume element of `V ⊕ W` acts on `E ⊗ F` by `Γ_V ⊗ Γ_W`. Unlike
`CliffordAlgebra.complexProdTensor_complexVolume`, this requires no positively oriented basis of
`V` or `W`, so it also covers the negative orientation of a zero-dimensional summand. -/
theorem complexProdTensor_complexVolume_of_map_prod (hm : Even m) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (ho : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) =
      TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) := by
  let b₁ : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  let b₂ : OrthonormalBasis (Fin m) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr Fact.out)
  have hQb₂ := b₂.isOrthoᵢ_associated hQ₂
  have hinv₂ : ρ₂ (complexVolume Q₂ b₂.toBasis.orientation) *
      ρ₂ (complexVolume Q₂ b₂.toBasis.orientation) = 1 := by
    rw [← map_mul, complexVolume_mul_self _ hQ₂, map_one]
  have hpos (o₂' : Orientation ℝ W (Fin m)) :
      complexProdTensor hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂
          (complexVolume Q ((b₁.toBasis.orientation.prod o₂' Fact.out Fact.out).map (Fin (n + m))
            (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
        TensorProduct.map (ρ₁ (complexVolume Q₁ b₁.toBasis.orientation))
          (ρ₂ (complexVolume Q₂ o₂')) := by
    rcases b₂.toBasis.orientation_eq_or_eq_neg o₂' with rfl | rfl
    · exact complexProdTensor_complexVolume hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂
        b₂.toBasis.orientation _ hm b₁ rfl b₂ rfl hQb₂
        (b₁.orientation_reindex_prod b₂ Fact.out Fact.out)
    · rw [Orientation.prod_neg_right, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
        complexVolume_neg_orientation, map_neg, map_neg_right]
      exact congrArg Neg.neg (complexProdTensor_complexVolume hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂
        b₂.toBasis.orientation _ hm b₁ rfl b₂ rfl hQb₂
        (b₁.orientation_reindex_prod b₂ Fact.out Fact.out))
  subst ho
  rcases b₁.toBasis.orientation_eq_or_eq_neg o₁ with rfl | rfl
  · exact hpos o₂
  · rw [Orientation.prod_neg_left, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
      complexVolume_neg_orientation, map_neg, map_neg_left]
    congr 1
    -- Conjugate the `-b₁.orientation` action by the involution `1 ⊗ Γ_W` to reduce to `+b₁`.
    have hint := lTensor_complexVolume_comp_complexProdTensor_neg_orientation hQ
      b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂ b₂.toBasis.orientation hm
      (complexVolume Q ((b₁.toBasis.orientation.prod o₂ Fact.out Fact.out).map (Fin (n + m))
        (WithLp.linearEquiv 2 ℝ (V × W)).symm))
    have hlinv : (ρ₂ (complexVolume Q₂ b₂.toBasis.orientation)).lTensor E *
        (ρ₂ (complexVolume Q₂ b₂.toBasis.orientation)).lTensor E = 1 := by
      rw [← LinearMap.lTensor_mul, hinv₂]
      exact TensorProduct.map_one
    have hcomm : Commute ((ρ₂ (complexVolume Q₂ b₂.toBasis.orientation)).lTensor E)
        (TensorProduct.map (ρ₁ (complexVolume Q₁ b₁.toBasis.orientation))
          (ρ₂ (complexVolume Q₂ o₂))) := by
      rcases b₂.toBasis.orientation_eq_or_eq_neg o₂ with rfl | rfl
      · rw [Commute, SemiconjBy, LinearMap.lTensor, ← Module.End.one_eq_id,
          ← TensorProduct.map_mul, ← TensorProduct.map_mul, one_mul, mul_one]
      · rw [Commute, SemiconjBy, complexVolume_neg_orientation, map_neg, LinearMap.lTensor,
          ← Module.End.one_eq_id, ← TensorProduct.map_mul, ← TensorProduct.map_mul,
          one_mul, mul_one, mul_neg, neg_mul]
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, hpos o₂, ← hcomm.eq] at hint
    calc complexProdTensor hQ (-b₁.toBasis.orientation) hQ₁ hn ρ₁ ρ₂ _
        = 1 * complexProdTensor hQ (-b₁.toBasis.orientation) hQ₁ hn ρ₁ ρ₂ _ := (one_mul _).symm
      _ = (ρ₂ (complexVolume Q₂ b₂.toBasis.orientation)).lTensor E *
            ((ρ₂ (complexVolume Q₂ b₂.toBasis.orientation)).lTensor E *
              complexProdTensor hQ (-b₁.toBasis.orientation) hQ₁ hn ρ₁ ρ₂ _) := by
          rw [← mul_assoc, hlinv]
      _ = (ρ₂ (complexVolume Q₂ b₂.toBasis.orientation)).lTensor E *
            (ρ₂ (complexVolume Q₂ b₂.toBasis.orientation)).lTensor E *
            TensorProduct.map (ρ₁ (complexVolume Q₁ b₁.toBasis.orientation))
              (ρ₂ (complexVolume Q₂ o₂)) := by rw [hint, mul_assoc]
      _ = TensorProduct.map (ρ₁ (complexVolume Q₁ b₁.toBasis.orientation))
            (ρ₂ (complexVolume Q₂ o₂)) := by rw [hlinv, one_mul]

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
  have hQb₂ := b₂.isOrthoᵢ_associated hQ₂
  have hpos (o₂' : Orientation ℝ W (Fin m)) :
      complexProdTensor hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂
          (complexVolume Q ((b₁.toBasis.orientation.prod o₂' Fact.out Fact.out).map (Fin (n + m))
            (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
        (ρ₂ (complexVolume Q₂ o₂')).lTensor E := by
    rcases b₂.toBasis.orientation_eq_or_eq_neg o₂' with rfl | rfl
    · exact complexProdTensor_complexVolume_of_odd hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂
        b₂.toBasis.orientation _ hm b₁ rfl b₂ rfl hQb₂
        (b₁.orientation_reindex_prod b₂ Fact.out Fact.out)
    · rw [Orientation.prod_neg_right, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
        complexVolume_neg_orientation, map_neg, LinearMap.lTensor_neg]
      exact congrArg Neg.neg (complexProdTensor_complexVolume_of_odd hQ b₁.toBasis.orientation hQ₁
        hn ρ₁ ρ₂ b₂.toBasis.orientation _ hm b₁ rfl b₂ rfl hQb₂
        (b₁.orientation_reindex_prod b₂ Fact.out Fact.out))
  subst ho
  rcases b₁.toBasis.orientation_eq_or_eq_neg o₁ with rfl | rfl
  · exact hpos o₂
  · -- Replacing `o₁` by `-o₁` negates each of the `m` odd factors of `W`, contributing
    -- `(-1)^m = -1`, which cancels the sign from `(-o₁).prod o₂ = -(o₁.prod o₂)`.
    have hneg_b₂ :
        complexProdTensor hQ (-b₁.toBasis.orientation) hQ₁ hn ρ₁ ρ₂
            (complexVolume Q ((b₁.toBasis.orientation.prod b₂.toBasis.orientation
              Fact.out Fact.out).map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
          -(ρ₂ (complexVolume Q₂ b₂.toBasis.orientation)).lTensor E := by
      have hQb₁ := b₁.isOrthoᵢ_associated hQ₁
      have hQb : (QuadraticMap.associated Q).IsOrthoᵢ
          ((b₁.prod b₂).reindex finSumFinEquiv).toBasis := by
        have h := OrthonormalBasis.isOrthoᵢ_associated_prod hQ hQb₁ hQb₂
        rw [LinearMap.isOrthoᵢ_def] at h ⊢
        intro i j hij
        simpa [OrthonormalBasis.reindex_apply] using h _ _ (finSumFinEquiv.symm.injective.ne hij)
      have hl : (List.finRange (n + m)).map ((b₁.prod b₂).reindex finSumFinEquiv) =
          ((List.finRange n).map fun i ↦ WithLp.toLp 2 (b₁ i, 0)) ++
            (List.finRange m).map fun j ↦ WithLp.toLp 2 (0, b₂ j) := by
        rw [← List.ofFn_eq_map, List.ofFn_add, ← List.ofFn_eq_map, ← List.ofFn_eq_map]
        congr 2 <;> ext i
        · have hcast : Fin.castLE (Nat.le_add_right n m) i = Fin.castAdd m i := by ext; simp
          simp [OrthonormalBasis.reindex_apply, hcast]
        · simp [OrthonormalBasis.reindex_apply]
      have hV (l : List V) :
          complexProdTensor hQ (-b₁.toBasis.orientation) hQ₁ hn ρ₁ ρ₂
              ((l.map fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, 0))).prod) =
            complexProdTensor hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂
              ((l.map fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, 0))).prod) := by
        induction l with
        | nil => simp
        | cons v l ih =>
          simp only [List.map_cons, List.prod_cons, map_mul, ih,
            complexProdTensor_ι_one_tmul_toLp_inl]
      have hW (l : List W) :
          complexProdTensor hQ (-b₁.toBasis.orientation) hQ₁ hn ρ₁ ρ₂
              ((l.map fun w ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))).prod) =
            (-1 : ℂ) ^ l.length • complexProdTensor hQ b₁.toBasis.orientation hQ₁ hn ρ₁ ρ₂
              ((l.map fun w ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))).prod) := by
        induction l with
        | nil => simp
        | cons w l ih =>
          rw [List.map_cons, List.prod_cons, List.length_cons, map_mul, map_mul, ih,
            complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr,
            complexProdTensor_ι_one_tmul_toLp_inr]
          ext z
          simp [pow_succ']
      have hmap₁ : ((List.finRange n).map fun i ↦ WithLp.toLp 2 (b₁ i, 0)).map
          (fun x ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ x)) =
          ((List.finRange n).map b₁).map
            (fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, 0))) := by
        simp [Function.comp_def]
      have hmap₂ : ((List.finRange m).map fun j ↦ WithLp.toLp 2 (0, b₂ j)).map
          (fun x ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ x)) =
          ((List.finRange m).map b₂).map
            (fun w ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) := by
        simp [Function.comp_def]
      have hneg_smul (x : Module.End ℂ (E ⊗[ℂ] F)) : (-1 : ℂ) • x = -x := neg_one_smul ℂ x
      have hmul_neg (x y : Module.End ℂ (E ⊗[ℂ] F)) : x * -y = -(x * y) := mul_neg x y
      have hsmul_neg (c : ℂ) (x : Module.End ℂ (E ⊗[ℂ] F)) : c • -x = -(c • x) := smul_neg c x
      rw [← b₁.orientation_reindex_prod b₂ Fact.out Fact.out,
        complexVolume_eq _ _ rfl hQb, hl, List.map_append, List.prod_append,
        map_smul, map_mul, hmap₁, hmap₂, hV, hW, List.length_map, List.length_finRange,
        hm.neg_one_pow, hneg_smul, hmul_neg, hsmul_neg, ← hmap₁, ← hmap₂, ← map_mul,
        ← map_smul, ← List.prod_append, ← List.map_append, ← hl, ← complexVolume_eq _ _ rfl hQb,
        b₁.orientation_reindex_prod b₂ Fact.out Fact.out, hpos]
    rcases b₂.toBasis.orientation_eq_or_eq_neg o₂ with rfl | rfl
    · rw [Orientation.prod_neg_left, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
        hneg_b₂, neg_neg]
    · rw [Orientation.prod_neg_neg, hneg_b₂, complexVolume_neg_orientation, map_neg,
        LinearMap.lTensor_neg]

/-- **Product chirality under orientation reversal**: for even `n` and `m`, reversing `o₁` to
`-o₁` reverses the product orientation `o` to `-o` (`Orientation.prod_neg_left`) and negates the
action of the product chirality on `E ⊗ F`. -/
theorem complexProdTensor_neg_orientation_complexVolume_neg (hm : Even m)
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
