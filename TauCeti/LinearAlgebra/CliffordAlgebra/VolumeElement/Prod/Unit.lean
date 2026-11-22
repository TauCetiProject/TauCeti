/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.ProdEquiv
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Neg
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Unit

/-!
# Orientation-sign and rank-zero unit laws of `CliffordAlgebra.complexProdTensor`

This file establishes how changing `o₁` affects `CliffordAlgebra.complexProdTensor` and how
`complexProdTensor` behaves when either `V` or `W` is zero-dimensional:

1. **Reversing `o₁` on `V`**: replacing `o₁` by `-o₁` negates `Γ_V`
   (`CliffordAlgebra.complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr`). When `W` is
   even-dimensional, conjugating `complexProdTensor` for `o₁` by `1 ⊗ Γ_W` gives that for `-o₁`
   (`CliffordAlgebra.conjAlgEquiv_lTensor_complexVolume_complexProdTensor`).
2. **Rank-zero unit laws**: for `[Unique V]`, `TensorProduct.lid ℂ F` intertwines
   `complexProdTensor` with `ρ₂` for `positiveOrientation` and with `ρ₂ ∘ involute` for
   `-positiveOrientation` (`CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_positiveOrientation`,
   `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation`). For `[Unique W]`,
   `TensorProduct.rid ℂ E` intertwines `complexProdTensor` with `ρ₁` for either orientation `o₁`
   (`CliffordAlgebra.conjAlgEquiv_rid_complexProdTensor`), and transports `complexVolume` with
   sign determined by the orientation of `W`
   (`CliffordAlgebra.conj_rid_complexProdTensor_complexVolume_of_positiveOrientation`,
   `CliffordAlgebra.conj_rid_complexProdTensor_complexVolume_of_neg_positiveOrientation`).

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

/-- **Equivalence of product representations under `o₁ ↦ -o₁`**: when `W` is even-dimensional with
`Q₂ w = -‖w‖²`, conjugating `complexProdTensor` for `o₁` by `1 ⊗ Γ_W` gives that for `-o₁`. -/
theorem conjAlgEquiv_lTensor_complexVolume_complexProdTensor (o₂ : Orientation ℝ W (Fin m))
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m) :
    (((LinearEquiv.ofInvolutive (ρ₂ (complexVolume Q₂ o₂))
        (ρ₂.involutive_complexVolume o₂ hQ₂)).lTensor E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ := by
  rw [complexProdTensor_eq_comp, complexProdTensor_eq_comp, ← AlgHom.comp_assoc,
    AlgHom.conjAlgEquiv_lTensor_cliffordProdTensor _ _ _ _ _ _
      (ρ₂.involutive_complexVolume o₂ hQ₂) (map_complexVolume_mul_map_ι o₂ hm ρ₂)]
  simp only [complexVolume_neg_orientation, map_neg]

/-- Reversing `o₁` in BOTH `complexProdTensor` and `Orientation.prod` multiplies the product volume
action by `-(-1) ^ m`. -/
theorem complexProdTensor_neg_orientation_complexVolume_of_map_prod (o₂ : Orientation ℝ W (Fin m))
    (o o' : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (ho' : (Orientation.prod (-o₁) o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o') :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (complexVolume Q o') =
      -((-1 : ℂ) ^ m • complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)) := by
  subst o o'
  rw [Orientation.prod_neg_left, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
    complexProdTensor_neg_orientation_complexVolume hQ o₁ hQ₁ hn ρ₁ ρ₂ _]

end NegOrientation

section UnitLeft

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Unique V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  {F : Type*} [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

private theorem map_uniqueProd_comp_equivOfIsometry_withLpProd :
    (map (QuadraticMap.IsometryEquiv.uniqueProd
        (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry).comp
        (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).toAlgHom =
      (equivOfIsometry
        ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ)).toAlgHom := by
  rw [← equivOfIsometry_toAlgHom, equivOfIsometry_toAlgHom_comp,
    QuadraticMap.IsometryEquiv.baseChangeProd_trans_uniqueProd (A := ℂ) hQ]

/-- **Left unit law (`positiveOrientation`)**: when `V` is zero-dimensional and positively oriented,
conjugating `complexProdTensor` on `ℂ ⊗ F` by `TensorProduct.lid ℂ F` recovers `ρ₂` along
`QuadraticMap.IsometryEquiv.withLpUniqueProd`. -/
theorem conjAlgEquiv_lid_complexProdTensor_positiveOrientation :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0))
          (fun v ↦ by simp [Subsingleton.elim v 0]) Even.zero ρ₁ ρ₂) =
      ρ₂.comp (equivOfIsometry
        ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ)).toAlgHom := by
  have hγ : ρ₁ (complexVolume Q₁ (positiveOrientation : Orientation ℝ V (Fin 0))) = 1 := by
    simp [complexVolume_positiveOrientation]
  simp only [complexProdTensor_eq_comp, hγ, ← AlgHom.comp_assoc]
  rw [AlgHom.conjAlgEquiv_lid_cliffordProdTensor_one, AlgHom.comp_assoc,
    map_uniqueProd_comp_equivOfIsometry_withLpProd]

/-- **Left unit law (`-positiveOrientation`)**: when `V` is zero-dimensional and negatively
oriented, conjugating `complexProdTensor` on `ℂ ⊗ F` by `TensorProduct.lid ℂ F` twists `ρ₂` by
`CliffordAlgebra.involute`. -/
theorem conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (-positiveOrientation : Orientation ℝ V (Fin 0))
          (fun v ↦ by simp [Subsingleton.elim v 0]) Even.zero ρ₁ ρ₂) =
      (ρ₂.comp (CliffordAlgebra.involute :
          CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] CliffordAlgebra (Q₂.baseChange ℂ))).comp
        (equivOfIsometry
          ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ)).toAlgHom := by
  have hγ : ρ₁ (complexVolume Q₁ (-positiveOrientation : Orientation ℝ V (Fin 0))) = -1 := by
    simp [complexVolume_neg_orientation, complexVolume_positiveOrientation]
  simp only [complexProdTensor_eq_comp, hγ, ← AlgHom.comp_assoc]
  rw [AlgHom.conjAlgEquiv_lid_cliffordProdTensor_neg_one, AlgHom.comp_assoc,
    map_uniqueProd_comp_equivOfIsometry_withLpProd]

/-- For `positiveOrientation` on trivial `V`, `TensorProduct.lid ℂ F` conjugates the action of
`complexVolume Q o` to `ρ₂ (complexVolume Q₂ o₂)`, for any quadratic form `Q₂` on `W`. -/
theorem conj_lid_complexProdTensor_positiveOrientation_complexVolume
    [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
    (o₂ : Orientation ℝ W (Fin m)) (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (0 + m)))
    (ho : (Orientation.prod (positiveOrientation : Orientation ℝ V (Fin 0)) o₂
      Fact.out Fact.out).map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    (TensorProduct.lid ℂ F).conj
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0))
          (fun v ↦ by simp [Subsingleton.elim v 0]) Even.zero ρ₁ ρ₂ (complexVolume Q o)) =
      ρ₂ (complexVolume Q₂ o₂) := by
  subst o
  exact conj_complexVolume_of_conjAlgEquiv_comp
    (conjAlgEquiv_lid_complexProdTensor_positiveOrientation hQ ρ₁ ρ₂)
    (equivOfIsometry_withLpUniqueProd_complexVolume hQ o₂)

/-- For `-positiveOrientation` on trivial `V` and the product orientation of
`(-positiveOrientation, o₂)`, `TensorProduct.lid ℂ F` conjugates the action of `complexVolume Q o`
to `-((-1) ^ m • ρ₂ (complexVolume Q₂ o₂))`. -/
theorem conj_lid_complexProdTensor_neg_positiveOrientation_complexVolume
    [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
    (o₂ : Orientation ℝ W (Fin m)) (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (0 + m)))
    (ho : (Orientation.prod (-positiveOrientation : Orientation ℝ V (Fin 0)) o₂
      Fact.out Fact.out).map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    (TensorProduct.lid ℂ F).conj
        (complexProdTensor hQ (-positiveOrientation : Orientation ℝ V (Fin 0))
          (fun v ↦ by simp [Subsingleton.elim v 0]) Even.zero ρ₁ ρ₂ (complexVolume Q o)) =
      -((-1 : ℂ) ^ m • ρ₂ (complexVolume Q₂ o₂)) := by
  subst o
  have h := conj_complexVolume_of_conjAlgEquiv_comp
    (conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation hQ ρ₁ ρ₂)
    (equivOfIsometry_withLpUniqueProd_complexVolume hQ o₂)
  rw [Orientation.prod_neg_left, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
    map_neg, h]
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

omit [FiniteDimensional ℝ V] in
private theorem map_prodUnique_comp_equivOfIsometry_withLpProd :
    (map (QuadraticMap.IsometryEquiv.prodUnique
        (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry).comp
        (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).toAlgHom =
      (equivOfIsometry
        ((QuadraticMap.IsometryEquiv.withLpProdUnique hQ).baseChange ℂ)).toAlgHom := by
  rw [← equivOfIsometry_toAlgHom, equivOfIsometry_toAlgHom_comp,
    QuadraticMap.IsometryEquiv.baseChangeProd_trans_prodUnique (A := ℂ) hQ]

/-- **Right unit law**: when `W` is zero-dimensional, conjugating `complexProdTensor` on `E ⊗ ℂ`
by `TensorProduct.rid ℂ E` recovers `ρ₁` along `QuadraticMap.IsometryEquiv.withLpProdUnique`, for
either orientation `o₁` of `V`. -/
theorem conjAlgEquiv_rid_complexProdTensor :
    ((TensorProduct.rid ℂ E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      ρ₁.comp (equivOfIsometry
        ((QuadraticMap.IsometryEquiv.withLpProdUnique hQ).baseChange ℂ)).toAlgHom := by
  rw [complexProdTensor_eq_comp, ← AlgHom.comp_assoc,
    AlgHom.conjAlgEquiv_rid_cliffordProdTensor, AlgHom.comp_assoc,
    map_prodUnique_comp_equivOfIsometry_withLpProd]

/-- For `positiveOrientation` on trivial `W`, `TensorProduct.rid ℂ E` conjugates the action of
`complexVolume Q o` to `ρ₁ (complexVolume Q₁ o₁)`. -/
theorem conj_rid_complexProdTensor_complexVolume_of_positiveOrientation
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin n))
    (ho : (Orientation.prod o₁ (positiveOrientation : Orientation ℝ W (Fin 0))
      Fact.out Fact.out).map (Fin n) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    (TensorProduct.rid ℂ E).conj (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)) =
      ρ₁ (complexVolume Q₁ o₁) := by
  subst o
  exact conj_complexVolume_of_conjAlgEquiv_comp
    (conjAlgEquiv_rid_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂)
    (equivOfIsometry_withLpProdUnique_complexVolume hQ o₁)

/-- For `-positiveOrientation` on trivial `W`, `TensorProduct.rid ℂ E` conjugates the action of
`complexVolume Q o` to `-ρ₁ (complexVolume Q₁ o₁)`. -/
theorem conj_rid_complexProdTensor_complexVolume_of_neg_positiveOrientation
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin n))
    (ho : (Orientation.prod o₁ (-positiveOrientation : Orientation ℝ W (Fin 0))
      Fact.out Fact.out).map (Fin n) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    (TensorProduct.rid ℂ E).conj (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)) =
      -ρ₁ (complexVolume Q₁ o₁) := by
  subst o
  rw [Orientation.prod_neg_right, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
    map_neg,
    conj_rid_complexProdTensor_complexVolume_of_positiveOrientation hQ o₁ hQ₁ hn ρ₁ ρ₂ _ rfl]

end UnitRight

end CliffordAlgebra
