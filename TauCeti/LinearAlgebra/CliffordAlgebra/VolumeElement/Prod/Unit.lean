/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation

/-!
# Rank-zero unit laws for `complexProdTensor`

The trivial real inner product space (`[Unique V]`, `finrank ℝ V = 0`) with its positive orientation
`positiveOrientation` and the scalar module `ℂ` (on which `1` acts as `1` and vectors act as `0`)
is the two-sided unit for `CliffordAlgebra.complexProdTensor`:

* **Left unit (`0 ⊕ W ≃ W`)**: `LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W` is an isometric
  equivalence `Q.IsometryEquiv Q₂` (`CliffordAlgebra.withLpUniqueProdIsometry`). For
  `positiveOrientation : Orientation ℝ V (Fin 0)`, we have `Γ_V = 1`
  (`CliffordAlgebra.complexVolume_positiveOrientation`), so `(0, w)` acts on `ℂ ⊗ F` by
  `1 ⊗ c_W(w)`, the left unitor `TensorProduct.lid ℂ F` intertwines `complexProdTensor` with `ρ₂`
  (`CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_positiveOrientation` and
  `CliffordAlgebra.lid_complexProdTensor_positiveOrientation`), and the product volume element
  becomes `ρ₂ (complexVolume Q₂ o₂)`.
* **Negative-orientation contrast on `0`**: for `-positiveOrientation : Orientation ℝ V (Fin 0)`,
  `Γ_V = -1`, so `(0, w)` acts by `-1 ⊗ c_W(w)`: `TensorProduct.lid ℂ F` twists `ρ₂` by
  `CliffordAlgebra.involute` instead of intertwining `ρ₂` on the nose
  (`CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation`), and for even `W`
  the product chirality becomes `-ρ₂ (complexVolume Q₂ o₂)`
  (`CliffordAlgebra.lid_complexProdTensor_neg_positiveOrientation_complexVolume_neg`). Thus the
  unit of the graded product is specifically the positively oriented zero space.
* **Right unit (`V ⊕ 0 ≃ V`)**: for `[Unique W]` and any even-dimensional oriented `V`,
  `LinearIsometryEquiv.withLpProdUnique 2 ℝ V W` is an isometric equivalence `Q.IsometryEquiv Q₁`
  (`CliffordAlgebra.withLpProdUniqueIsometry`), and the right unitor `TensorProduct.rid ℂ E`
  intertwines `complexProdTensor` with `ρ₁` (`CliffordAlgebra.conjAlgEquiv_rid_complexProdTensor`
  and `CliffordAlgebra.rid_complexProdTensor`).

## Main definitions

* `CliffordAlgebra.withLpUniqueProdIsometry`: `Q.IsometryEquiv Q₂` when `[Unique V]`.
* `CliffordAlgebra.withLpProdUniqueIsometry`: `Q.IsometryEquiv Q₁` when `[Unique W]`.

## Main results

* `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_positiveOrientation` and
  `CliffordAlgebra.lid_complexProdTensor_positiveOrientation`: left-unit intertwining for
  `positiveOrientation`.
* `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation` and
  `CliffordAlgebra.lid_complexProdTensor_neg_positiveOrientation_complexVolume_neg`: negative
  orientation twists by `involute` and negates the product chirality.
* `CliffordAlgebra.conjAlgEquiv_rid_complexProdTensor` and
  `CliffordAlgebra.rid_complexProdTensor`: right-unit intertwining.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Definition 2.2.42.
-/

public section

noncomputable section

open Module TensorProduct

namespace CliffordAlgebra

/-! ### Left unit: `0 ⊕ W ≃ W` -/

section LeftUnit

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

/-- When `V` is trivial (`[Unique V]`), `LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W` is an
isometric equivalence `Q.IsometryEquiv Q₂`. -/
def withLpUniqueProdIsometry [Unique V] : Q.IsometryEquiv Q₂ where
  toLinearEquiv := (LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W).toLinearEquiv
  map_app' x := by
    rw [hQ x, Subsingleton.elim (WithLp.ofLp x).1 0, map_zero, zero_add]
    rfl

/-- `CliffordAlgebra.withLpUniqueProdIsometry` projects onto the `W` coordinate. -/
@[simp]
theorem withLpUniqueProdIsometry_apply [Unique V] (x : WithLp 2 (V × W)) :
    withLpUniqueProdIsometry hQ x = (WithLp.ofLp x).2 :=
  (rfl)

/-- `CliffordAlgebra.withLpUniqueProdIsometry` preserves norms. -/
theorem norm_withLpUniqueProdIsometry [Unique V] (x : WithLp 2 (V × W)) :
    ‖withLpUniqueProdIsometry hQ x‖ = ‖x‖ :=
  (LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W).norm_map x

variable [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 0)] (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2)
  {F : Type*} [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- For the positive orientation of `V` (`finrank ℝ V = 0`), a vector `(0, w)` acts on `ℂ ⊗ F` by
`1 ⊗ c_W(w)`. -/
theorem complexProdTensor_positiveOrientation_ι_inr (w : W) :
    complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero ρ₁ ρ₂
        (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) =
      (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))).lTensor ℂ := by
  simp [LinearMap.lTensor, Module.End.one_eq_id]

/-- **Negative-orientation contrast on `0`-dimensional `V`**: for `-positiveOrientation`, a vector
`(0, w)` acts on `ℂ ⊗ F` by `-1 ⊗ c_W(w)`. -/
theorem complexProdTensor_neg_positiveOrientation_ι_inr (w : W) :
    complexProdTensor hQ (-positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero ρ₁ ρ₂
        (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) =
      -(ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))).lTensor ℂ := by
  apply TensorProduct.ext'
  intro c f
  simp [TensorProduct.neg_tmul]

variable [Unique V]

/-- **Left-unit law for `complexProdTensor`**: for the zero space `V` with its positive orientation
and any `CliffordAlgebra (Q₁.baseChange ℂ)`-algebra map `ρ₁` to `End_ℂ ℂ`, conjugating
`complexProdTensor` by `TensorProduct.lid ℂ F : ℂ ⊗ F ≃ F` recovers `ρ₂` along
`CliffordAlgebra.withLpUniqueProdIsometry`. -/
theorem conjAlgEquiv_lid_complexProdTensor_positiveOrientation :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂) =
      ρ₂.comp (CliffordAlgebra.map ((withLpUniqueProdIsometry hQ).toIsometry.baseChange ℂ)) := by
  refine baseChange_algHom_ext Q fun x ↦ ?_
  apply LinearMap.ext
  intro f
  have hx : x = WithLp.toLp 2 (0, (WithLp.ofLp x).2) :=
    (WithLp.equiv 2 (V × W)).injective (Prod.ext (Subsingleton.elim _ 0) rfl)
  rw [hx]
  simp [LinearEquiv.conjAlgEquiv_apply]

/-- Pointwise left-unit law for `complexProdTensor` with `positiveOrientation`. -/
theorem lid_complexProdTensor_positiveOrientation (a : CliffordAlgebra (Q.baseChange ℂ))
    (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂ a z) =
      ρ₂ (CliffordAlgebra.map ((withLpUniqueProdIsometry hQ).toIsometry.baseChange ℂ) a)
        (TensorProduct.lid ℂ F z) := by
  have h := congrArg
    (fun g : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F ↦
      g a (TensorProduct.lid ℂ F z))
    (conjAlgEquiv_lid_complexProdTensor_positiveOrientation hQ hQ₁ ρ₁ ρ₂)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

/-- **Negative-orientation left-unit contrast**: when the zero space `V` is given
`-positiveOrientation`, conjugating `complexProdTensor` by `TensorProduct.lid ℂ F` twists `ρ₂` by
`CliffordAlgebra.involute` rather than recovering `ρ₂`. -/
theorem conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (-positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂) =
      (ρ₂.comp (involute (Q := Q₂.baseChange ℂ))).comp
        (CliffordAlgebra.map ((withLpUniqueProdIsometry hQ).toIsometry.baseChange ℂ)) := by
  rw [complexProdTensor_neg_orientation_eq_comp_involute,
    conjAlgEquiv_lid_complexProdTensor_positiveOrientation]

omit [Unique V] in
/-- Under `TensorProduct.lid ℂ F`, the product chirality of `0 ⊕ W` for `positiveOrientation` on `0`
and `o₂` on even-dimensional `W` becomes `ρ₂ (complexVolume Q₂ o₂)`, whereas reversing `0` to
`-positiveOrientation` (and hence reversing the product orientation to `-o`) negates it to
`-ρ₂ (complexVolume Q₂ o₂)`. -/
theorem lid_complexProdTensor_neg_positiveOrientation_complexVolume_neg
    [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
    [Fact (finrank ℝ (WithLp 2 (V × W)) = 0 + m)]
    (o₂ : Orientation ℝ W (Fin m)) (hm : Even m) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    {o : Orientation ℝ (WithLp 2 (V × W)) (Fin (0 + m))}
    (ho : (Orientation.prod (positiveOrientation : Orientation ℝ V (Fin 0)) o₂
      Fact.out Fact.out).map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ (-positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂ (complexVolume Q (-o)) z) =
      -ρ₂ (complexVolume Q₂ o₂) (TensorProduct.lid ℂ F z) := by
  rw [complexProdTensor_neg_orientation_complexVolume_neg hQ _ hQ₁ Even.zero ρ₁ ρ₂ o₂ hm hQ₂ ho,
    complexVolume_positiveOrientation, map_one, LinearMap.neg_apply, map_neg]
  congr 1
  induction z using TensorProduct.inductionOn with
  | tmul c f => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end LeftUnit

/-! ### Right unit: `V ⊕ 0 ≃ V` -/

section RightUnit

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Unique W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

/-- When `W` is trivial (`[Unique W]`), `LinearIsometryEquiv.withLpProdUnique 2 ℝ V W` is an
isometric equivalence `Q.IsometryEquiv Q₁`. -/
def withLpProdUniqueIsometry : Q.IsometryEquiv Q₁ where
  toLinearEquiv := (LinearIsometryEquiv.withLpProdUnique 2 ℝ V W).toLinearEquiv
  map_app' x := by
    rw [hQ x, Subsingleton.elim (WithLp.ofLp x).2 0, map_zero, add_zero]
    rfl

/-- `CliffordAlgebra.withLpProdUniqueIsometry` projects onto the `V` coordinate. -/
@[simp]
theorem withLpProdUniqueIsometry_apply (x : WithLp 2 (V × W)) :
    withLpProdUniqueIsometry hQ x = (WithLp.ofLp x).1 :=
  (rfl)

/-- `CliffordAlgebra.withLpProdUniqueIsometry` preserves norms. -/
theorem norm_withLpProdUniqueIsometry (x : WithLp 2 (V × W)) :
    ‖withLpProdUniqueIsometry hQ x‖ = ‖x‖ :=
  (LinearIsometryEquiv.withLpProdUnique 2 ℝ V W).norm_map x

variable [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E : Type*} [AddCommGroup E] [Module ℂ E]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)

/-- **Right-unit law for `complexProdTensor`**: for the zero space `W`, conjugating
`complexProdTensor` by `TensorProduct.rid ℂ E : E ⊗ ℂ ≃ E` recovers `ρ₁` along
`CliffordAlgebra.withLpProdUniqueIsometry`, for any orientation `o₁` of `V`. -/
theorem conjAlgEquiv_rid_complexProdTensor :
    ((TensorProduct.rid ℂ E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      ρ₁.comp (CliffordAlgebra.map ((withLpProdUniqueIsometry hQ).toIsometry.baseChange ℂ)) := by
  refine baseChange_algHom_ext Q fun x ↦ ?_
  apply LinearMap.ext
  intro e
  have hx : x = WithLp.toLp 2 ((WithLp.ofLp x).1, 0) :=
    (WithLp.equiv 2 (V × W)).injective (Prod.ext rfl (Subsingleton.elim _ 0))
  rw [hx]
  simp [LinearEquiv.conjAlgEquiv_apply]

/-- Pointwise right-unit law for `complexProdTensor`. -/
theorem rid_complexProdTensor (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ E (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      ρ₁ (CliffordAlgebra.map ((withLpProdUniqueIsometry hQ).toIsometry.baseChange ℂ) a)
        (TensorProduct.rid ℂ E z) := by
  have h := congrArg
    (fun g : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E ↦
      g a (TensorProduct.rid ℂ E z))
    (conjAlgEquiv_rid_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

end RightUnit

end CliffordAlgebra
