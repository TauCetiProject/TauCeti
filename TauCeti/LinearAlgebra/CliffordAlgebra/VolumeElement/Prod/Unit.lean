/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.ProdEquiv
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Unit

/-!
# Orientation-sign and rank-zero unit laws of `CliffordAlgebra.complexProdTensor`

This file establishes how changing `o₁` affects `CliffordAlgebra.complexProdTensor` and how
`complexProdTensor` behaves when either `V` or `W` is zero-dimensional:

1. **Reversing `o₁` on `V`**: replacing `o₁` by `-o₁` negates `Γ_V`
   (`CliffordAlgebra.complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr`). When `W` is
   even-dimensional, `1 ⊗ Γ_W` intertwines the product actions for `o₁` and `-o₁`
   (`CliffordAlgebra.lTensor_complexVolume_comp_complexProdTensor`,
   `CliffordAlgebra.conjAlgEquiv_lTensor_complexVolume_complexProdTensor`).
2. **Rank-zero unit laws**: for `[Unique V]`, `TensorProduct.lid ℂ F` intertwines
   `complexProdTensor` with `ρ₂` for `positiveOrientation` and with `ρ₂ ∘ involute` for
   `-positiveOrientation` (`CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_positiveOrientation`,
   `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation`). For `[Unique W]`,
   `TensorProduct.rid ℂ E` intertwines `complexProdTensor` with `ρ₁` for either orientation `o₁`
   (`CliffordAlgebra.conjAlgEquiv_rid_complexProdTensor`).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module TensorProduct

namespace CliffordAlgebra

section NegOrientation

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] {n : ℕ} [Fact (finrank ℝ V = n)]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (o₁ : Orientation ℝ V (Fin n)) (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- Reversing the orientation `o₁` of `V` negates the action of `(0, w)` on `E ⊗ F`. -/
theorem complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr (w : W) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂
        (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) =
      -TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) := by
  rw [complexProdTensor_ι_one_tmul_toLp, TensorProduct.tmul_zero, map_zero, map_zero,
    LinearMap.rTensor_zero, zero_add, complexVolume_neg_orientation, map_neg,
    ← neg_one_smul ℂ (ρ₁ _), TensorProduct.map_smul_left]
  ext z; simp

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]

/-- **Intertwining under reversal of `o₁`**: when `W` is even-dimensional, `1 ⊗ Γ_W` intertwines
`complexProdTensor` for `o₁` with `complexProdTensor` for `-o₁` on every Clifford element. -/
theorem lTensor_complexVolume_comp_complexProdTensor (o₂ : Orientation ℝ W (Fin m)) (hm : Even m)
    (x : CliffordAlgebra (Q.baseChange ℂ)) :
    (ρ₂ (complexVolume Q₂ o₂)).lTensor E ∘ₗ complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ x =
      complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ x ∘ₗ (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  have hneg : ρ₁ (complexVolume Q₁ (-o₁)) = -ρ₁ (complexVolume Q₁ o₁) := by
    rw [complexVolume_neg_orientation, map_neg]
  rw [complexProdTensor_eq_cliffordProdTensor, complexProdTensor_eq_cliffordProdTensor]
  simpa only [hneg] using
    AlgHom.lTensor_comp_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (by rw [← map_mul, complexVolume_mul_self o₁ hQ₁, map_one])
      (fun v ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg])
      ρ₂ (ρ₂ (complexVolume Q₂ o₂))
      (fun u ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₂ hm, map_neg])
      (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ) x)

/-- **Equivalence of product representations under `o₁ ↦ -o₁`**: when `W` is even-dimensional with
`Q₂ w = -‖w‖²`, conjugating `complexProdTensor` for `o₁` by `1 ⊗ Γ_W` gives that for `-o₁`. -/
theorem conjAlgEquiv_lTensor_complexVolume_complexProdTensor (o₂ : Orientation ℝ W (Fin m))
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m) :
    (((LinearEquiv.ofInvolutive (ρ₂ (complexVolume Q₂ o₂))
        (map_complexVolume_involutive o₂ hQ₂ ρ₂)).lTensor E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ := by
  let e := (LinearEquiv.ofInvolutive (ρ₂ (complexVolume Q₂ o₂))
    (map_complexVolume_involutive o₂ hQ₂ ρ₂)).lTensor E
  have he : ∀ t, e t = (ρ₂ (complexVolume Q₂ o₂)).lTensor E t := fun t ↦ by
    induction t using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  refine AlgHom.ext fun x ↦ LinearMap.ext fun z ↦ ?_
  obtain ⟨t, rfl⟩ := e.surjective z
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [e.symm_apply_apply, he, he]
  exact LinearMap.congr_fun
    (lTensor_complexVolume_comp_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm x) t

/-- Reversing `o₁` in BOTH `complexProdTensor` and `Orientation.prod` multiplies the product volume
action by `-(-1) ^ m`. -/
theorem complexProdTensor_neg_orientation_complexVolume_of_map_prod
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)] (o₂ : Orientation ℝ W (Fin m))
    (o o' : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    {b₂ : OrthonormalBasis (Fin m) ℝ W} (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (ho' : (Orientation.prod (-o₁) o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o') :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (complexVolume Q o') =
      -((-1 : ℂ) ^ m • complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)) := by
  subst o o'
  rw [Orientation.prod_neg_left, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
    complexProdTensor_neg_orientation_complexVolume hQ o₁ hQ₁ hn ρ₁ ρ₂ _ hQb₂]

end NegOrientation

section UnitLeft

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Unique V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fact (finrank ℝ V = 0)]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2)
  {F : Type*} [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- **Left unit law (`positiveOrientation`)**: when `V` is zero-dimensional and positively oriented,
conjugating `complexProdTensor` on `ℂ ⊗ F` by `TensorProduct.lid ℂ F` recovers `ρ₂` along
`QuadraticMap.IsometryEquiv.withLpUniqueProd`. -/
theorem conjAlgEquiv_lid_complexProdTensor_positiveOrientation :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂) =
      ρ₂.comp (equivOfIsometry
        ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ)).toAlgHom := by
  refine CliffordAlgebra.hom_ext <| LinearMap.ext fun u ↦ ?_
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
    have hx : z ⊗ₜ[ℝ] x =
        z • ((1 : ℂ) ⊗ₜ[ℝ] WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, WithLp.toLp_ofLp]
    rw [hx, map_smul, map_smul]; ext f
    simp [LinearEquiv.conjAlgEquiv_apply, complexProdTensor_ι_one_tmul_toLp, equivOfIsometry_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Applied form of `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_positiveOrientation`. -/
theorem lid_complexProdTensor_positiveOrientation (x : CliffordAlgebra (Q.baseChange ℂ))
    (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂ x z) =
      ρ₂ (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ) x)
        (TensorProduct.lid ℂ F z) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using LinearMap.congr_fun
    (AlgHom.congr_fun (conjAlgEquiv_lid_complexProdTensor_positiveOrientation hQ hQ₁ ρ₁ ρ₂) x)
    (TensorProduct.lid ℂ F z)

/-- **Left unit law (`-positiveOrientation`)**: when `V` is zero-dimensional and negatively
oriented, conjugating `complexProdTensor` on `ℂ ⊗ F` by `TensorProduct.lid ℂ F` twists `ρ₂` by
`CliffordAlgebra.involute`. -/
theorem conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (-positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂) =
      (ρ₂.comp (CliffordAlgebra.involute :
          CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] CliffordAlgebra (Q₂.baseChange ℂ))).comp
        (equivOfIsometry
          ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ)).toAlgHom := by
  refine CliffordAlgebra.hom_ext <| LinearMap.ext fun u ↦ ?_
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
    have hx : z ⊗ₜ[ℝ] x =
        z • ((1 : ℂ) ⊗ₜ[ℝ] WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, WithLp.toLp_ofLp]
    rw [hx, map_smul, map_smul]; ext f
    simp [LinearEquiv.conjAlgEquiv_apply, complexProdTensor_ι_one_tmul_toLp, equivOfIsometry_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Applied form of `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation`. -/
theorem lid_complexProdTensor_neg_positiveOrientation (x : CliffordAlgebra (Q.baseChange ℂ))
    (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ (-positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂ x z) =
      ρ₂ (CliffordAlgebra.involute
          (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ) x))
        (TensorProduct.lid ℂ F z) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using LinearMap.congr_fun
    (AlgHom.congr_fun (conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation hQ hQ₁ ρ₁ ρ₂) x)
    (TensorProduct.lid ℂ F z)

private theorem equivOfIsometry_withLpUniqueProd_complexVolume
    [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
    [Fact (finrank ℝ (WithLp 2 (V × W)) = 0 + m)] (o₂ : Orientation ℝ W (Fin m)) :
    equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ)
        (complexVolume Q
          ((Orientation.prod (positiveOrientation : Orientation ℝ V (Fin 0)) o₂
            Fact.out Fact.out).map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm)) =
      complexVolume Q₂ o₂ := by
  have hnorm : ∀ x, ‖QuadraticMap.IsometryEquiv.withLpUniqueProd hQ x‖ = ‖x‖ := fun x ↦ by
    simpa using (LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W).norm_map x
  have horient :
      Orientation.map (Fin (0 + m)) (QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).toLinearEquiv
          ((Orientation.prod (positiveOrientation : Orientation ℝ V (Fin 0)) o₂
            Fact.out Fact.out).map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm) =
        Orientation.reindex ℝ W (finCongr (zero_add m).symm) o₂ := by
    simpa [← Orientation.map_symm] using
      Orientation.map_uniqueProd_prod_positiveOrientation o₂ Fact.out Fact.out
  rw [equivOfIsometry_apply, QuadraticMap.IsometryEquiv.baseChange_toIsometry,
    map_complexVolume_of_eq _ _ hnorm (zero_add m), horient,
    Orientation.reindex_finCongr_reindex_finCongr]
  simp [finCongr_refl, Orientation.reindex_refl]

/-- For `positiveOrientation` on trivial `V`, `TensorProduct.lid ℂ F` conjugates the action of
`complexVolume Q o` to `ρ₂ (complexVolume Q₂ o₂)`, for any quadratic form `Q₂` on `W`. -/
theorem conj_lid_complexProdTensor_positiveOrientation_complexVolume
    [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
    [Fact (finrank ℝ (WithLp 2 (V × W)) = 0 + m)] (o₂ : Orientation ℝ W (Fin m))
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (0 + m)))
    (ho : (Orientation.prod (positiveOrientation : Orientation ℝ V (Fin 0)) o₂
      Fact.out Fact.out).map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    (TensorProduct.lid ℂ F).conj
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂ (complexVolume Q o)) =
      ρ₂ (complexVolume Q₂ o₂) := by
  subst o; ext f
  rw [LinearEquiv.conj_apply_apply,
    lid_complexProdTensor_positiveOrientation hQ hQ₁ ρ₁ ρ₂ _ ((TensorProduct.lid ℂ F).symm f),
    LinearEquiv.apply_symm_apply, equivOfIsometry_withLpUniqueProd_complexVolume hQ o₂]

/-- For `-positiveOrientation` on trivial `V` and the product orientation of
`(-positiveOrientation, o₂)`, `TensorProduct.lid ℂ F` conjugates the action of `complexVolume Q o`
to `-((-1) ^ m • ρ₂ (complexVolume Q₂ o₂))`. -/
theorem conj_lid_complexProdTensor_neg_positiveOrientation_complexVolume
    [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
    [Fact (finrank ℝ (WithLp 2 (V × W)) = 0 + m)] (o₂ : Orientation ℝ W (Fin m))
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (0 + m)))
    (ho : (Orientation.prod (-positiveOrientation : Orientation ℝ V (Fin 0)) o₂
      Fact.out Fact.out).map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    (TensorProduct.lid ℂ F).conj
        (complexProdTensor hQ (-positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂ (complexVolume Q o)) =
      -((-1 : ℂ) ^ m • ρ₂ (complexVolume Q₂ o₂)) := by
  subst o; ext f
  rw [LinearEquiv.conj_apply_apply,
    lid_complexProdTensor_neg_positiveOrientation hQ hQ₁ ρ₁ ρ₂ _ ((TensorProduct.lid ℂ F).symm f),
    LinearEquiv.apply_symm_apply, Orientation.prod_neg_left, Orientation.map_neg,
    complexVolume_neg_orientation, map_neg, map_neg, map_neg, LinearMap.neg_apply,
    equivOfIsometry_withLpUniqueProd_complexVolume hQ o₂]
  simp [involute_complexVolume]

end UnitLeft

section UnitRight

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Unique W] {n : ℕ} [Fact (finrank ℝ V = n)]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (o₁ : Orientation ℝ V (Fin n)) (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E : Type*} [AddCommGroup E] [Module ℂ E]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)

/-- **Right unit law**: when `W` is zero-dimensional, conjugating `complexProdTensor` on `E ⊗ ℂ`
by `TensorProduct.rid ℂ E` recovers `ρ₁` along `QuadraticMap.IsometryEquiv.withLpProdUnique`, for
either orientation `o₁` of `V`. -/
theorem conjAlgEquiv_rid_complexProdTensor :
    ((TensorProduct.rid ℂ E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      ρ₁.comp (equivOfIsometry
        ((QuadraticMap.IsometryEquiv.withLpProdUnique hQ).baseChange ℂ)).toAlgHom := by
  refine CliffordAlgebra.hom_ext <| LinearMap.ext fun u ↦ ?_
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
    have hx : z ⊗ₜ[ℝ] x =
        z • ((1 : ℂ) ⊗ₜ[ℝ] WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, WithLp.toLp_ofLp]
    rw [hx, map_smul, map_smul]; ext e
    simp [LinearEquiv.conjAlgEquiv_apply, complexProdTensor_ι_one_tmul_toLp, equivOfIsometry_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Applied form of `CliffordAlgebra.conjAlgEquiv_rid_complexProdTensor`. -/
theorem rid_complexProdTensor (x : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ E (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ x z) =
      ρ₁ (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProdUnique hQ).baseChange ℂ) x)
        (TensorProduct.rid ℂ E z) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using LinearMap.congr_fun
    (AlgHom.congr_fun (conjAlgEquiv_rid_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) x)
    (TensorProduct.rid ℂ E z)

/-- For `positiveOrientation` on trivial `W`, `TensorProduct.rid ℂ E` conjugates the action of
`complexVolume Q o` to `ρ₁ (complexVolume Q₁ o₁)`. -/
theorem conj_rid_complexProdTensor_complexVolume_positiveOrientation
    [Fact (finrank ℝ W = 0)] [Fact (finrank ℝ (WithLp 2 (V × W)) = n)]
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin n))
    (ho : (Orientation.prod o₁ (positiveOrientation : Orientation ℝ W (Fin 0))
      Fact.out Fact.out).map (Fin n) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    (TensorProduct.rid ℂ E).conj (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)) =
      ρ₁ (complexVolume Q₁ o₁) := by
  subst o
  have hnorm : ∀ x, ‖QuadraticMap.IsometryEquiv.withLpProdUnique hQ x‖ = ‖x‖ := fun x ↦ by
    simpa using (LinearIsometryEquiv.withLpProdUnique 2 ℝ V W).norm_map x
  have horient :
      Orientation.map (Fin n) (QuadraticMap.IsometryEquiv.withLpProdUnique hQ).toLinearEquiv
          ((Orientation.prod o₁ (positiveOrientation : Orientation ℝ W (Fin 0))
            Fact.out Fact.out).map (Fin n) (WithLp.linearEquiv 2 ℝ (V × W)).symm) = o₁ := by
    simpa [← Orientation.map_symm] using
      Orientation.map_prodUnique_prod_positiveOrientation o₁ Fact.out Fact.out
  ext e
  rw [LinearEquiv.conj_apply_apply,
    rid_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ _ ((TensorProduct.rid ℂ E).symm e),
    LinearEquiv.apply_symm_apply, equivOfIsometry_apply,
    QuadraticMap.IsometryEquiv.baseChange_toIsometry, map_complexVolume _ _ hnorm, horient]

end UnitRight

end CliffordAlgebra
