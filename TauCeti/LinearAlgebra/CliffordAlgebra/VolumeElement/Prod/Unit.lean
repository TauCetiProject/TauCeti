/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Unit
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic

/-!
# Rank-zero unit laws for the graded tensor product of complex Clifford modules

When one of the Euclidean summands in `V ⊕ W` is trivial (`Unique V` or `Unique W`), the tensor
unitors `TensorProduct.lid ℂ F` and `TensorProduct.rid ℂ E` compare
`CliffordAlgebra.complexProdTensor` with the Clifford action on the remaining summand along
Mathlib's `LinearIsometryEquiv.withLpUniqueProd` and `LinearIsometryEquiv.withLpProdUnique`.

* **Left unit** (`Unique V`, `0 ⊕ W`): for the positive orientation `positiveOrientation` of `V`,
  `Γ_V = 1`, so `TensorProduct.lid ℂ F : ℂ ⊗ F ≃ F` intertwines `complexProdTensor` with `ρ₂`
  (`CliffordAlgebra.conjAlgEquiv_complexProdTensor_uniqueProd`,
  `CliffordAlgebra.lid_complexProdTensor`) and carries `Γ_(0 ⊕ W)` to `Γ_W`
  (`CliffordAlgebra.lid_complexProdTensor_complexVolume`). By contrast, for the negative
  orientation `-positiveOrientation` of `V`, `Γ_V = -1`, so `c(0, w)` acts under `lid ℂ F` as
  `-c_W(w)` (`CliffordAlgebra.lid_complexProdTensor_neg_positiveOrientation_ι`), showing that the
  unit object is the positively oriented zero space rather than the negatively oriented one;
  likewise `withLpUniqueProd` carries `(-positiveOrientation) × o₂` to `-o₂`.
* **Right unit** (`Unique W`, `V ⊕ 0`): for any orientation `o₁` of `V`, `TensorProduct.rid ℂ E`
  intertwines `complexProdTensor` with `ρ₁`
  (`CliffordAlgebra.conjAlgEquiv_complexProdTensor_prodUnique`,
  `CliffordAlgebra.rid_complexProdTensor`), carrying `Γ_(V ⊕ 0)` to `Γ_V` when `W` has
  `positiveOrientation` and to `-Γ_V` when `W` has `-positiveOrientation`.

## Main definitions

* `CliffordAlgebra.withLpUniqueProdIsometry` and `CliffordAlgebra.withLpProdUniqueIsometry`:
  `LinearIsometryEquiv.withLpUniqueProd` and `LinearIsometryEquiv.withLpProdUnique` as quadratic
  isometry equivalences.

## Main results

* `CliffordAlgebra.conjAlgEquiv_complexProdTensor_uniqueProd` and
  `CliffordAlgebra.lid_complexProdTensor`: left unit law for `0 ⊕ W` with `positiveOrientation`.
* `CliffordAlgebra.lid_complexProdTensor_neg_positiveOrientation_ι`: with `-positiveOrientation`,
  `(0, w)` acts under `lid ℂ F` by `-c_W(w)`.
* `CliffordAlgebra.conjAlgEquiv_complexProdTensor_prodUnique` and
  `CliffordAlgebra.rid_complexProdTensor`: right unit law for `V ⊕ 0`.
* `CliffordAlgebra.lid_complexProdTensor_complexVolume`,
  `CliffordAlgebra.rid_complexProdTensor_complexVolume`, and
  `CliffordAlgebra.rid_complexProdTensor_complexVolume_neg_right`: volume comparisons under the
  unitors.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module TensorProduct

namespace CliffordAlgebra

/-- On a subsingleton seminormed real module, every quadratic form satisfies `Q₁ v = -‖v‖²`. -/
theorem eq_neg_norm_sq_of_subsingleton {V : Type*} [SeminormedAddCommGroup V] [Module ℝ V]
    [Subsingleton V] (Q₁ : QuadraticForm ℝ V) (v : V) :
    Q₁ v = -‖v‖ ^ 2 := by
  simp [Subsingleton.elim v 0]

section LeftUnitIsometry

variable {V W : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V] [Unique V]
  [SeminormedAddCommGroup W] [NormedSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

include hQ in
/-- `LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W` as a quadratic isometry equivalence `Q ≃ Q₂`
when `V` is trivial. -/
def withLpUniqueProdIsometry : Q.IsometryEquiv Q₂ where
  toLinearEquiv := (LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W).toLinearEquiv
  map_app' x := by
    rw [hQ, Subsingleton.elim (WithLp.ofLp x).1 0, map_zero, zero_add]
    rfl

/-- Applying `CliffordAlgebra.withLpUniqueProdIsometry` projects onto the second coordinate. -/
@[simp]
theorem withLpUniqueProdIsometry_apply (x : WithLp 2 (V × W)) :
    withLpUniqueProdIsometry hQ x = x.snd :=
  (rfl)

/-- The underlying linear equivalence of `CliffordAlgebra.withLpUniqueProdIsometry`. -/
@[simp]
theorem withLpUniqueProdIsometry_toLinearEquiv :
    (withLpUniqueProdIsometry hQ).toLinearEquiv =
      (LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W).toLinearEquiv :=
  (rfl)

end LeftUnitIsometry

section LeftUnit

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Unique V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [Fact (finrank ℝ V = 0)] {F : Type*} [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- **Left unit of `CliffordAlgebra.complexProdTensor`**: for the zero space `V` with
`positiveOrientation`, conjugating by `TensorProduct.lid ℂ F` identifies `complexProdTensor` on
`ℂ ⊗ F` with `ρ₂` pulled back along `CliffordAlgebra.withLpUniqueProdIsometry`. -/
theorem conjAlgEquiv_complexProdTensor_uniqueProd :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ positiveOrientation (eq_neg_norm_sq_of_subsingleton Q₁)
          Even.zero ρ₁ ρ₂) =
      ρ₂.comp (equivOfIsometry ((withLpUniqueProdIsometry hQ).baseChange ℂ)).toAlgHom := by
  have : Unique (ℂ ⊗[ℝ] V) := TensorProduct.uniqueRight
  have hdiag : (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd
        (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))).toAlgHom.comp
        (equivOfIsometry (complexWithLpProd hQ)).toAlgHom =
      (equivOfIsometry ((withLpUniqueProdIsometry hQ).baseChange ℂ)).toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro z x
    simp [equivOfIsometry_apply]
  have hγ : ρ₁ (complexVolume Q₁ (positiveOrientation : Orientation ℝ V (Fin 0))) = 1 := by simp
  rw [complexProdTensor_def,
    AlgHom.cliffordProdTensor_congr_grading ρ₁ _ _ _ ρ₂ hγ (mul_one 1)
      (fun v ↦ by simp [Subsingleton.elim v 0]),
    ← AlgHom.comp_assoc, AlgHom.conjAlgEquiv_cliffordProdTensor_uniqueProd ρ₁ ρ₂,
    AlgHom.comp_assoc, hdiag]

/-- `TensorProduct.lid ℂ F` intertwines `complexProdTensor` of `0 ⊕ W` (for `positiveOrientation`)
with `ρ₂`. -/
theorem lid_complexProdTensor (a : CliffordAlgebra (Q.baseChange ℂ)) (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ positiveOrientation (eq_neg_norm_sq_of_subsingleton Q₁)
          Even.zero ρ₁ ρ₂ a z) =
      ρ₂ (equivOfIsometry ((withLpUniqueProdIsometry hQ).baseChange ℂ) a)
        (TensorProduct.lid ℂ F z) := by
  have h := congrArg (fun g ↦ g a (TensorProduct.lid ℂ F z))
    (conjAlgEquiv_complexProdTensor_uniqueProd hQ ρ₁ ρ₂)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

/-- For the negative orientation `-positiveOrientation` of the zero space `V`, `Γ_V = -1`, so a
vector `(0, w)` acts under `TensorProduct.lid ℂ F` by `-c_W(w)` rather than `c_W(w)`. -/
theorem lid_complexProdTensor_neg_positiveOrientation_ι (w : W) (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ (-positiveOrientation) (eq_neg_norm_sq_of_subsingleton Q₁)
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
      positiveOrientation.prod o₂ Fact.out Fact.out) (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ positiveOrientation (eq_neg_norm_sq_of_subsingleton Q₁)
          Even.zero ρ₁ ρ₂ (complexVolume Q o) z) =
      ρ₂ (complexVolume Q₂ o₂) (TensorProduct.lid ℂ F z) := by
  have := Fact.mk
    ((LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W).toLinearEquiv.finrank_eq.symm.trans
      (Fact.out : finrank ℝ (WithLp 2 (V × W)) = 0 + m))
  have hcomm : (WithLp.linearEquiv 2 ℝ (V × W)).trans LinearEquiv.uniqueProd =
      (LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W).toLinearEquiv := by ext x; simp
  have hmap : o.map (Fin (0 + m)) (withLpUniqueProdIsometry hQ).toLinearEquiv =
      Orientation.reindex ℝ W (finCongr (zero_add m).symm) o₂ := by
    rw [withLpUniqueProdIsometry_toLinearEquiv, ← hcomm, Orientation.map_trans, ho,
      Orientation.map_uniqueProd_positiveOrientation_prod]
  rw [lid_complexProdTensor, equivOfIsometry_apply,
    QuadraticMap.IsometryEquiv.baseChange_toIsometry,
    map_complexVolume o (withLpUniqueProdIsometry hQ)
      (LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W).norm_map,
    hmap, complexVolume_reindex_finCongr]

end LeftUnit

section RightUnitIsometry

variable {V W : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
  [SeminormedAddCommGroup W] [NormedSpace ℝ W] [Unique W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

include hQ in
/-- `LinearIsometryEquiv.withLpProdUnique 2 ℝ V W` as a quadratic isometry equivalence `Q ≃ Q₁`
when `W` is trivial. -/
def withLpProdUniqueIsometry : Q.IsometryEquiv Q₁ where
  toLinearEquiv := (LinearIsometryEquiv.withLpProdUnique 2 ℝ V W).toLinearEquiv
  map_app' x := by
    rw [hQ, Subsingleton.elim (WithLp.ofLp x).2 0, map_zero, add_zero]
    rfl

/-- Applying `CliffordAlgebra.withLpProdUniqueIsometry` projects onto the first coordinate. -/
@[simp]
theorem withLpProdUniqueIsometry_apply (x : WithLp 2 (V × W)) :
    withLpProdUniqueIsometry hQ x = x.fst :=
  (rfl)

/-- The underlying linear equivalence of `CliffordAlgebra.withLpProdUniqueIsometry`. -/
@[simp]
theorem withLpProdUniqueIsometry_toLinearEquiv :
    (withLpProdUniqueIsometry hQ).toLinearEquiv =
      (LinearIsometryEquiv.withLpProdUnique 2 ℝ V W).toLinearEquiv :=
  (rfl)

end RightUnitIsometry

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

/-- **Right unit of `CliffordAlgebra.complexProdTensor`**: when `W` is trivial, conjugating by
`TensorProduct.rid ℂ E` identifies `complexProdTensor` on `E ⊗ ℂ` with `ρ₁` pulled back along
`CliffordAlgebra.withLpProdUniqueIsometry`, for any orientation `o₁` of `V`. -/
theorem conjAlgEquiv_complexProdTensor_prodUnique :
    ((TensorProduct.rid ℂ E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      ρ₁.comp (equivOfIsometry ((withLpProdUniqueIsometry hQ).baseChange ℂ)).toAlgHom := by
  have : Unique (ℂ ⊗[ℝ] W) := TensorProduct.uniqueRight
  have hdiag : (equivOfIsometry (QuadraticMap.IsometryEquiv.prodUnique
        (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))).toAlgHom.comp
        (equivOfIsometry (complexWithLpProd hQ)).toAlgHom =
      (equivOfIsometry ((withLpProdUniqueIsometry hQ).baseChange ℂ)).toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro z x
    simp [equivOfIsometry_apply]
  rw [complexProdTensor_def, ← AlgHom.comp_assoc,
    AlgHom.conjAlgEquiv_cliffordProdTensor_prodUnique, AlgHom.comp_assoc, hdiag]

/-- `TensorProduct.rid ℂ E` intertwines `complexProdTensor` of `V ⊕ 0` with `ρ₁`. -/
theorem rid_complexProdTensor (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ E (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      ρ₁ (equivOfIsometry ((withLpProdUniqueIsometry hQ).baseChange ℂ) a)
        (TensorProduct.rid ℂ E z) := by
  have h := congrArg (fun g ↦ g a (TensorProduct.rid ℂ E z))
    (conjAlgEquiv_complexProdTensor_prodUnique hQ o₁ hQ₁ hn ρ₁ ρ₂)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

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
  have hcomm : (WithLp.linearEquiv 2 ℝ (V × W)).trans LinearEquiv.prodUnique =
      (LinearIsometryEquiv.withLpProdUnique 2 ℝ V W).toLinearEquiv := by ext x; simp
  have hmap : o.map (Fin (n + 0)) (withLpProdUniqueIsometry hQ).toLinearEquiv =
      Orientation.reindex ℝ V (finCongr (Nat.add_zero n).symm) o₁ := by
    rw [withLpProdUniqueIsometry_toLinearEquiv, ← hcomm, Orientation.map_trans, ho,
      Orientation.map_prodUnique_prod_positiveOrientation]
  rw [rid_complexProdTensor, equivOfIsometry_apply,
    QuadraticMap.IsometryEquiv.baseChange_toIsometry,
    map_complexVolume o (withLpProdUniqueIsometry hQ)
      (LinearIsometryEquiv.withLpProdUnique 2 ℝ V W).norm_map,
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
  have := Fact.mk
    ((LinearIsometryEquiv.withLpProdUnique 2 ℝ V W).toLinearEquiv.finrank_eq.symm.trans
      (Fact.out : finrank ℝ (WithLp 2 (V × W)) = n + 0))
  have hcomm : (WithLp.linearEquiv 2 ℝ (V × W)).trans LinearEquiv.prodUnique =
      (LinearIsometryEquiv.withLpProdUnique 2 ℝ V W).toLinearEquiv := by ext x; simp
  have hmap : o.map (Fin (n + 0)) (withLpProdUniqueIsometry hQ).toLinearEquiv =
      -(Orientation.reindex ℝ V (finCongr (Nat.add_zero n).symm) o₁) := by
    rw [withLpProdUniqueIsometry_toLinearEquiv, ← hcomm, Orientation.map_trans, ho,
      Orientation.prod_neg_right, Orientation.map_neg,
      Orientation.map_prodUnique_prod_positiveOrientation]
  rw [rid_complexProdTensor, equivOfIsometry_apply,
    QuadraticMap.IsometryEquiv.baseChange_toIsometry,
    map_complexVolume o (withLpProdUniqueIsometry hQ)
      (LinearIsometryEquiv.withLpProdUnique 2 ℝ V W).norm_map,
    hmap, complexVolume_neg_orientation, complexVolume_reindex_finCongr, map_neg,
    LinearMap.neg_apply]

end RightUnit

end CliffordAlgebra
