/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp.QuadraticForm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Unit
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic

/-!
# Rank-zero unit laws for the graded tensor product of complex Clifford modules

When one Euclidean summand in `V ⊕ W` is trivial (`Unique V` or `Unique W`), the unitors
`TensorProduct.lid ℂ F` and `TensorProduct.rid ℂ E` compare `CliffordAlgebra.complexProdTensor` with
the Clifford action on the remaining summand along `QuadraticMap.IsometryEquiv.withLpUniqueProd` and
`QuadraticMap.IsometryEquiv.withLpProdUnique`.

* **Left unit** (`Unique V`, `0 ⊕ W`): for `positiveOrientation` on `V`, `Γ_V = 1`, so
  `TensorProduct.lid ℂ F` intertwines `complexProdTensor` with `ρ₂` and carries `Γ_(0 ⊕ W)` to
  `Γ_W`; for `-positiveOrientation`, `Γ_V = -1` and `(0, w)` acts under `lid ℂ F` as `-c_W(w)`.
* **Right unit** (`Unique W`, `V ⊕ 0`): for any `o₁`, `TensorProduct.rid ℂ E` intertwines
  `complexProdTensor` with `ρ₁`, carrying `Γ_(V ⊕ 0)` to `±Γ_V` according to the orientation of `0`.

## Main results

* `CliffordAlgebra.conjAlgEquiv_complexProdTensor_uniqueProd`,
  `CliffordAlgebra.lid_complexProdTensor`, and
  `CliffordAlgebra.lid_complexProdTensor_neg_positiveOrientation_ι`: left unit laws for `0 ⊕ W`.
* `CliffordAlgebra.conjAlgEquiv_complexProdTensor_prodUnique` and
  `CliffordAlgebra.rid_complexProdTensor`: right unit laws for `V ⊕ 0`.
* `CliffordAlgebra.lid_complexProdTensor_complexVolume`,
  `CliffordAlgebra.rid_complexProdTensor_complexVolume`, and
  `CliffordAlgebra.rid_complexProdTensor_complexVolume_neg_right`: volume comparisons.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module TensorProduct

namespace CliffordAlgebra

section LeftUnit

local instance {V : Type*} [AddCommGroup V] [Module ℝ V] [Subsingleton V] :
    Fact (finrank ℝ V = 0) :=
  ⟨finrank_zero_of_subsingleton⟩

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Unique V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  {F : Type*} [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- `TensorProduct.lid ℂ F` intertwines `complexProdTensor` of `0 ⊕ W` (for `positiveOrientation`)
with `ρ₂`. -/
theorem lid_complexProdTensor (a : CliffordAlgebra (Q.baseChange ℂ)) (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ positiveOrientation Q₁.eq_neg_norm_sq_of_subsingleton
          Even.zero ρ₁ ρ₂ a z) =
      ρ₂ (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ) a)
        (TensorProduct.lid ℂ F z) := by
  have : Unique (ℂ ⊗[ℝ] V) := TensorProduct.uniqueRight
  have hdiag : (map (QuadraticMap.IsometryEquiv.uniqueProd
        (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry).comp
        (equivOfIsometry (complexWithLpProd hQ)).toAlgHom =
      (equivOfIsometry
        ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ)).toAlgHom :=
    CliffordAlgebra.hom_ext <| TensorProduct.AlgebraTensorModule.ext fun c x ↦ by
      simp [equivOfIsometry_apply]
  have hγ : ρ₁ (complexVolume Q₁ (positiveOrientation : Orientation ℝ V (Fin 0))) = 1 := by simp
  rw [complexProdTensor_def,
    AlgHom.cliffordProdTensor_congr_grading ρ₁ _ _ _ ρ₂ hγ (one_mul 1)
      (fun v ↦ by simp [Subsingleton.elim v 0]),
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.lid_cliffordProdTensor]
  exact congrArg (ρ₂ · (TensorProduct.lid ℂ F z)) (DFunLike.congr_fun hdiag a)

/-- **Left unit of `CliffordAlgebra.complexProdTensor`**: for the zero space `V` with
`positiveOrientation`, conjugating by `TensorProduct.lid ℂ F` identifies `complexProdTensor` on
`ℂ ⊗ F` with `ρ₂` pulled back along `QuadraticMap.IsometryEquiv.withLpUniqueProd`. -/
theorem conjAlgEquiv_complexProdTensor_uniqueProd :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ positiveOrientation Q₁.eq_neg_norm_sq_of_subsingleton
          Even.zero ρ₁ ρ₂) =
      ρ₂.comp
        (equivOfIsometry
          ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ)).toAlgHom := by
  refine AlgHom.ext fun a ↦ LinearMap.ext fun f ↦ ?_
  simpa [LinearEquiv.conjAlgEquiv_apply] using
    lid_complexProdTensor hQ ρ₁ ρ₂ a ((TensorProduct.lid ℂ F).symm f)

/-- For the negative orientation `-positiveOrientation` of the zero space `V`, `Γ_V = -1`, so a
vector `(0, w)` acts under `TensorProduct.lid ℂ F` by `-c_W(w)` rather than `c_W(w)`. -/
theorem lid_complexProdTensor_neg_positiveOrientation_ι (w : W) (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ (-positiveOrientation) Q₁.eq_neg_norm_sq_of_subsingleton
          Even.zero ρ₁ ρ₂ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) z) =
      -ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)) (TensorProduct.lid ℂ F z) := by
  rw [complexProdTensor_ι_one_tmul_toLp_inr]
  induction z using TensorProduct.inductionOn with
  | tmul c f => simp [neg_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, neg_add]

/-- For `0 ⊕ W` with `positiveOrientation` on `0`, `TensorProduct.lid ℂ F` carries the action of
`Γ_(0 ⊕ W)` (for the ordered product orientation) to `Γ_W`, in both even and odd dimensions `m`. -/
theorem lid_complexProdTensor_complexVolume [FiniteDimensional ℝ W] {m : ℕ}
    [Fact (finrank ℝ W = m)] [Fact (finrank ℝ (WithLp 2 (V × W)) = 0 + m)]
    (o₂ : Orientation ℝ W (Fin m)) (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (0 + m)))
    (ho : o.map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)) =
      positiveOrientation.prod o₂ finrank_zero_of_subsingleton Fact.out) (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ positiveOrientation Q₁.eq_neg_norm_sq_of_subsingleton
          Even.zero ρ₁ ρ₂ (complexVolume Q o) z) =
      ρ₂ (complexVolume Q₂ o₂) (TensorProduct.lid ℂ F z) := by
  have := Fact.mk
    ((LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W).toLinearEquiv.finrank_eq.symm.trans
      (Fact.out : finrank ℝ (WithLp 2 (V × W)) = 0 + m))
  have hmap : o.map (Fin (0 + m)) (QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).toLinearEquiv =
      Orientation.reindex ℝ W (finCongr (zero_add m).symm) o₂ := by
    rw [QuadraticMap.IsometryEquiv.toLinearEquiv_withLpUniqueProd, Orientation.map_trans, ho,
      Orientation.map_uniqueProd_positiveOrientation_prod]
  rw [lid_complexProdTensor, equivOfIsometry_apply,
    QuadraticMap.IsometryEquiv.baseChange_toIsometry,
    map_complexVolume o (QuadraticMap.IsometryEquiv.withLpUniqueProd hQ)
      (QuadraticMap.IsometryEquiv.norm_withLpUniqueProd hQ),
    hmap, complexVolume_reindex_finCongr]

end LeftUnit

section RightUnit

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Unique W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)]
  (o₁ : Orientation ℝ V (Fin n)) (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E : Type*} [AddCommGroup E] [Module ℂ E]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)

/-- `TensorProduct.rid ℂ E` intertwines `complexProdTensor` of `V ⊕ 0` with `ρ₁`. -/
theorem rid_complexProdTensor (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ E (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      ρ₁ (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProdUnique hQ).baseChange ℂ) a)
        (TensorProduct.rid ℂ E z) := by
  have : Unique (ℂ ⊗[ℝ] W) := TensorProduct.uniqueRight
  have hdiag : (map (QuadraticMap.IsometryEquiv.prodUnique
        (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry).comp
        (equivOfIsometry (complexWithLpProd hQ)).toAlgHom =
      (equivOfIsometry
        ((QuadraticMap.IsometryEquiv.withLpProdUnique hQ).baseChange ℂ)).toAlgHom :=
    CliffordAlgebra.hom_ext <| TensorProduct.AlgebraTensorModule.ext fun c x ↦ by
      simp [equivOfIsometry_apply]
  rw [complexProdTensor_def, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgHom.rid_cliffordProdTensor]
  exact congrArg (ρ₁ · (TensorProduct.rid ℂ E z)) (DFunLike.congr_fun hdiag a)

/-- **Right unit of `CliffordAlgebra.complexProdTensor`**: when `W` is trivial, conjugating by
`TensorProduct.rid ℂ E` identifies `complexProdTensor` on `E ⊗ ℂ` with `ρ₁` pulled back along
`QuadraticMap.IsometryEquiv.withLpProdUnique`, for any orientation `o₁` of `V`. -/
theorem conjAlgEquiv_complexProdTensor_prodUnique :
    ((TensorProduct.rid ℂ E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      ρ₁.comp
        (equivOfIsometry
          ((QuadraticMap.IsometryEquiv.withLpProdUnique hQ).baseChange ℂ)).toAlgHom := by
  refine AlgHom.ext fun a ↦ LinearMap.ext fun e ↦ ?_
  simpa [LinearEquiv.conjAlgEquiv_apply] using
    rid_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a ((TensorProduct.rid ℂ E).symm e)

/-- For `V ⊕ 0` with `positiveOrientation` on `0`, `TensorProduct.rid ℂ E` carries `Γ_(V ⊕ 0)` to
`Γ_V`. -/
theorem rid_complexProdTensor_complexVolume
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + 0)]
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + 0)))
    (ho : o.map (Fin (n + 0)) (WithLp.linearEquiv 2 ℝ (V × W)) =
      o₁.prod positiveOrientation Fact.out finrank_zero_of_subsingleton) (z : E ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ E (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) z) =
      ρ₁ (complexVolume Q₁ o₁) (TensorProduct.rid ℂ E z) := by
  have := Fact.mk
    ((LinearIsometryEquiv.withLpProdUnique 2 ℝ V W).toLinearEquiv.finrank_eq.symm.trans
      (Fact.out : finrank ℝ (WithLp 2 (V × W)) = n + 0))
  have hmap : o.map (Fin (n + 0)) (QuadraticMap.IsometryEquiv.withLpProdUnique hQ).toLinearEquiv =
      Orientation.reindex ℝ V (finCongr (Nat.add_zero n).symm) o₁ := by
    rw [QuadraticMap.IsometryEquiv.toLinearEquiv_withLpProdUnique, Orientation.map_trans, ho,
      Orientation.map_prodUnique_prod_positiveOrientation]
  rw [rid_complexProdTensor, equivOfIsometry_apply,
    QuadraticMap.IsometryEquiv.baseChange_toIsometry,
    map_complexVolume o (QuadraticMap.IsometryEquiv.withLpProdUnique hQ)
      (QuadraticMap.IsometryEquiv.norm_withLpProdUnique hQ),
    hmap, complexVolume_reindex_finCongr]

/-- Reversing the orientation of the trivial right factor `0` to `-positiveOrientation` negates the
chirality `Γ_(V ⊕ 0)` under `TensorProduct.rid ℂ E` (corresponding to a purely odd one-dimensional
twisting space). -/
theorem rid_complexProdTensor_complexVolume_neg_right
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + 0)]
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + 0)))
    (ho : o.map (Fin (n + 0)) (WithLp.linearEquiv 2 ℝ (V × W)) =
      o₁.prod (-positiveOrientation) Fact.out finrank_zero_of_subsingleton) (z : E ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ E (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) z) =
      -ρ₁ (complexVolume Q₁ o₁) (TensorProduct.rid ℂ E z) := by
  rw [← neg_neg o, complexVolume_neg_orientation, map_neg, LinearMap.neg_apply, map_neg,
    rid_complexProdTensor_complexVolume hQ o₁ hQ₁ hn ρ₁ ρ₂ (-o) ?_ z]
  rw [Orientation.map_neg, ho, Orientation.prod_neg_right]
  exact neg_neg (o₁.prod _ _ _)

end RightUnit

end CliffordAlgebra
