/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp.QuadraticForm
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
-- Private: ring-generic left and right unit laws of `cliffordProdTensor` are proof-only.
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Unit

/-!
# Rank-zero unit laws for `complexProdTensor`

The trivial real inner product space (`[Unique V]`, `finrank ℝ V = 0`) with its positive orientation
`positiveOrientation` and the scalar module `ℂ` (on which `1` acts as `1` and vectors act as `0`)
is the two-sided unit for `CliffordAlgebra.complexProdTensor`, specializing the ring-generic unit
theorems `AlgHom.conjAlgEquiv_lid_cliffordProdTensor`,
`AlgHom.conjAlgEquiv_lid_cliffordProdTensor_neg_one`, and
`AlgHom.conjAlgEquiv_rid_cliffordProdTensor` from
`TauCeti/LinearAlgebra/CliffordAlgebra/Prod/Unit.lean` along the `WithLp` quadratic isometries of
`TauCeti/Analysis/Normed/Lp/ProdLp/QuadraticForm.lean`:

* **Left unit (`0 ⊕ W ≃ W`)**: for `[Unique V]` and arbitrary `(W, Q₂)`,
  `TauCeti.withLpUniqueProdIsometryEquiv` is an isometric equivalence `Q.IsometryEquiv Q₂`. For
  `positiveOrientation : Orientation ℝ V (Fin 0)`, we have `Γ_V = 1`
  (`CliffordAlgebra.complexVolume_positiveOrientation`), so `(0, w)` acts on `ℂ ⊗ F` by
  `1 ⊗ c_W(w)`, the left unitor `TensorProduct.lid ℂ F` intertwines `complexProdTensor` with `ρ₂`
  (`CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_positiveOrientation` and
  `CliffordAlgebra.lid_complexProdTensor_positiveOrientation`), and for even-dimensional oriented
  `W` with `Q₂ w = -‖w‖²` the product chirality becomes `ρ₂ (complexVolume Q₂ o₂)`
  (`CliffordAlgebra.lid_complexProdTensor_positiveOrientation_complexVolume`).
* **Negative-orientation contrast on `0`**: for `-positiveOrientation : Orientation ℝ V (Fin 0)`,
  `Γ_V = -1`, so `(0, w)` acts by `-1 ⊗ c_W(w)`: `TensorProduct.lid ℂ F` twists `ρ₂` by
  `CliffordAlgebra.involute` instead of intertwining `ρ₂` on the nose
  (`CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation` and
  `CliffordAlgebra.lid_complexProdTensor_neg_positiveOrientation`), and for even `W` the product
  chirality for `-o` becomes `-ρ₂ (complexVolume Q₂ o₂)`
  (`CliffordAlgebra.lid_complexProdTensor_neg_positiveOrientation_complexVolume_neg`). Thus the
  unit of the graded product is specifically the positively oriented zero space.
* **Right unit (`V ⊕ 0 ≃ V`)**: for `[Unique W]` and any even-dimensional oriented `V`,
  `TauCeti.withLpProdUniqueIsometryEquiv` is an isometric equivalence `Q.IsometryEquiv Q₁`, the
  right unitor `TensorProduct.rid ℂ E` intertwines `complexProdTensor` with `ρ₁`
  (`CliffordAlgebra.conjAlgEquiv_rid_complexProdTensor` and
  `CliffordAlgebra.rid_complexProdTensor`), and the product chirality for `o₁ × positiveOrientation`
  becomes `ρ₁ (complexVolume Q₁ o₁)` (`CliffordAlgebra.rid_complexProdTensor_complexVolume`).

## Main results

* `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_positiveOrientation`,
  `CliffordAlgebra.lid_complexProdTensor_positiveOrientation`, and
  `CliffordAlgebra.lid_complexProdTensor_positiveOrientation_complexVolume`: left-unit intertwining
  and product chirality for `positiveOrientation`.
* `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation`,
  `CliffordAlgebra.lid_complexProdTensor_neg_positiveOrientation`, and
  `CliffordAlgebra.lid_complexProdTensor_neg_positiveOrientation_complexVolume_neg`: negative
  orientation twists by `involute` and negates the product chirality.
* `CliffordAlgebra.conjAlgEquiv_rid_complexProdTensor`,
  `CliffordAlgebra.rid_complexProdTensor`, and
  `CliffordAlgebra.rid_complexProdTensor_complexVolume`: right-unit intertwining and product
  chirality.

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
  [AddCommGroup W] [Module ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 0)] (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2)
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
`TauCeti.withLpUniqueProdIsometryEquiv`. -/
theorem conjAlgEquiv_lid_complexProdTensor_positiveOrientation :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂) =
      ρ₂.comp
        (CliffordAlgebra.map
          ((TauCeti.withLpUniqueProdIsometryEquiv hQ).toIsometry.baseChange ℂ)) := by
  have hgrade : complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
      ρ₁ ρ₂ =
      (AlgHom.cliffordProdTensor ρ₁ 1 (one_mul 1) (fun v ↦ by simp [Subsingleton.elim v 0])
        ρ₂).comp
        (equivOfIsometry (TauCeti.baseChangeWithLpProdIsometryEquiv hQ ℂ)).toAlgHom := by
    rw [complexProdTensor_def]
    congr 1
    exact AlgHom.cliffordProdTensor_congr_grading ρ₁ _ _ _ ρ₂
      (by rw [complexVolume_positiveOrientation, map_one]) _ _
  rw [hgrade, ← AlgHom.comp_assoc, AlgHom.conjAlgEquiv_lid_cliffordProdTensor ρ₁ ρ₂,
    AlgHom.comp_assoc]
  congr 1
  refine baseChange_algHom_ext Q fun x ↦ ?_
  simp [equivOfIsometry_apply]

/-- Pointwise left-unit law for `complexProdTensor` with `positiveOrientation`. -/
theorem lid_complexProdTensor_positiveOrientation (a : CliffordAlgebra (Q.baseChange ℂ))
    (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂ a z) =
      ρ₂ (CliffordAlgebra.map
          ((TauCeti.withLpUniqueProdIsometryEquiv hQ).toIsometry.baseChange ℂ) a)
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
        (CliffordAlgebra.map
          ((TauCeti.withLpUniqueProdIsometryEquiv hQ).toIsometry.baseChange ℂ)) := by
  rw [complexProdTensor_neg_orientation_eq_comp_involute,
    conjAlgEquiv_lid_complexProdTensor_positiveOrientation]

/-- Pointwise negative-orientation left-unit contrast: for `-positiveOrientation` on `0`, the left
unitor `TensorProduct.lid ℂ F` carries `complexProdTensor` to `ρ₂ ∘ involute`. -/
theorem lid_complexProdTensor_neg_positiveOrientation (a : CliffordAlgebra (Q.baseChange ℂ))
    (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ (-positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂ a z) =
      ρ₂ (involute (CliffordAlgebra.map
          ((TauCeti.withLpUniqueProdIsometryEquiv hQ).toIsometry.baseChange ℂ) a))
        (TensorProduct.lid ℂ F z) := by
  have h := congrArg
    (fun g : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F ↦
      g a (TensorProduct.lid ℂ F z))
    (conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation hQ hQ₁ ρ₁ ρ₂)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

end LeftUnit

section LeftUnitVolume

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 0)]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
  [Fact (finrank ℝ (WithLp 2 (V × W)) = 0 + m)]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2)
  {F : Type*} [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- Under `TensorProduct.lid ℂ F`, the product chirality of `0 ⊕ W` for `positiveOrientation` on
`0` and `o₂` on even-dimensional `W` (`Q₂ w = -‖w‖²`) becomes `ρ₂ (complexVolume Q₂ o₂)`. -/
theorem lid_complexProdTensor_positiveOrientation_complexVolume
    (o₂ : Orientation ℝ W (Fin m)) (hm : Even m) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    {o : Orientation ℝ (WithLp 2 (V × W)) (Fin (0 + m))}
    (ho : (Orientation.prod (positiveOrientation : Orientation ℝ V (Fin 0)) o₂
      Fact.out Fact.out).map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂ (complexVolume Q o) z) =
      ρ₂ (complexVolume Q₂ o₂) (TensorProduct.lid ℂ F z) := by
  rw [complexProdTensor_complexVolume_of_prod hQ _ hQ₁ Even.zero ρ₁ ρ₂ o₂ hm hQ₂ ho,
    complexVolume_positiveOrientation, map_one]
  exact LinearMap.congr_fun
    (f := (TensorProduct.lid ℂ F).toLinearMap ∘ₗ TensorProduct.map 1 (ρ₂ (complexVolume Q₂ o₂)))
    (g := ρ₂ (complexVolume Q₂ o₂) ∘ₗ (TensorProduct.lid ℂ F).toLinearMap)
    (TensorProduct.ext' fun c f ↦ by simp) z

/-- Under `TensorProduct.lid ℂ F`, reversing the zero-space orientation to `-positiveOrientation`
(and hence reversing the product orientation `o` to `-o`) negates the product chirality action on
even-dimensional `W` (`Q₂ w = -‖w‖²`) to `-ρ₂ (complexVolume Q₂ o₂)`, in contrast to
`CliffordAlgebra.lid_complexProdTensor_positiveOrientation_complexVolume`. -/
theorem lid_complexProdTensor_neg_positiveOrientation_complexVolume_neg
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
  exact congrArg Neg.neg (LinearMap.congr_fun
    (f := (TensorProduct.lid ℂ F).toLinearMap ∘ₗ TensorProduct.map 1 (ρ₂ (complexVolume Q₂ o₂)))
    (g := ρ₂ (complexVolume Q₂ o₂) ∘ₗ (TensorProduct.lid ℂ F).toLinearMap)
    (TensorProduct.ext' fun c f ↦ by simp) z)

end LeftUnitVolume

/-! ### Right unit: `V ⊕ 0 ≃ V` -/

section RightUnit

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [AddCommGroup W] [Module ℝ W] [Unique W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E : Type*} [AddCommGroup E] [Module ℂ E]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)

/-- **Right-unit law for `complexProdTensor`**: for the zero space `W`, conjugating
`complexProdTensor` by `TensorProduct.rid ℂ E : E ⊗ ℂ ≃ E` recovers `ρ₁` along
`TauCeti.withLpProdUniqueIsometryEquiv`, for any orientation `o₁` of `V`. -/
theorem conjAlgEquiv_rid_complexProdTensor :
    ((TensorProduct.rid ℂ E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      ρ₁.comp
        (CliffordAlgebra.map
          ((TauCeti.withLpProdUniqueIsometryEquiv hQ).toIsometry.baseChange ℂ)) := by
  rw [complexProdTensor_def, ← AlgHom.comp_assoc,
    AlgHom.conjAlgEquiv_rid_cliffordProdTensor ρ₁ _ _ _ ρ₂, AlgHom.comp_assoc]
  congr 1
  refine baseChange_algHom_ext Q fun x ↦ ?_
  simp [equivOfIsometry_apply]

/-- Pointwise right-unit law for `complexProdTensor`. -/
theorem rid_complexProdTensor (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ E (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      ρ₁ (CliffordAlgebra.map
          ((TauCeti.withLpProdUniqueIsometryEquiv hQ).toIsometry.baseChange ℂ) a)
        (TensorProduct.rid ℂ E z) := by
  have h := congrArg
    (fun g : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E ↦
      g a (TensorProduct.rid ℂ E z))
    (conjAlgEquiv_rid_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

end RightUnit

section RightUnitVolume

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Unique W]
  [FiniteDimensional ℝ W] [Fact (finrank ℝ W = 0)]
  [Fact (finrank ℝ (WithLp 2 (V × W)) = n + 0)]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E : Type*} [AddCommGroup E] [Module ℂ E]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)

/-- Under `TensorProduct.rid ℂ E`, the product chirality of `V ⊕ 0` for `o₁` on even-dimensional `V`
and `positiveOrientation` on `0` becomes `ρ₁ (complexVolume Q₁ o₁)`. -/
theorem rid_complexProdTensor_complexVolume
    {o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + 0))}
    (ho : (Orientation.prod o₁ (positiveOrientation : Orientation ℝ W (Fin 0))
      Fact.out Fact.out).map (Fin (n + 0)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (z : E ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ E (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) z) =
      ρ₁ (complexVolume Q₁ o₁) (TensorProduct.rid ℂ E z) := by
  have hQ₂ : ∀ w : W, Q₂ w = -‖w‖ ^ 2 := fun w ↦ by simp [Subsingleton.elim w 0]
  rw [complexProdTensor_complexVolume_of_prod hQ o₁ hQ₁ hn ρ₁ ρ₂
      (positiveOrientation : Orientation ℝ W (Fin 0)) Even.zero hQ₂ ho,
    complexVolume_positiveOrientation, map_one]
  exact LinearMap.congr_fun
    (f := (TensorProduct.rid ℂ E).toLinearMap ∘ₗ TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) 1)
    (g := ρ₁ (complexVolume Q₁ o₁) ∘ₗ (TensorProduct.rid ℂ E).toLinearMap)
    (TensorProduct.ext' fun e c ↦ by simp) z

end RightUnitVolume

end CliffordAlgebra
