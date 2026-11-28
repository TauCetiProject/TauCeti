/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.QuadraticForm.WithLp.L2
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Unit
import TauCeti.LinearAlgebra.LinearEquiv.Basic
import TauCeti.LinearAlgebra.Ray
import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Rank-zero unit laws for graded tensor products of complex Clifford modules

A zero-dimensional real inner product space (`finrank = 0`) with `positiveOrientation` and scalar
module `ℂ` acts as a left and right unit for `CliffordAlgebra.complexProdTensor` via
`TensorProduct.lid ℂ F` and `TensorProduct.rid ℂ E` along
`QuadraticMap.IsometryEquiv.withLpSubsingletonProd` / `withLpProdSubsingleton`. Using
`-positiveOrientation` on the left sets `Γ_V = -1`, twisting `ρ₂` by `CliffordAlgebra.involute` and
multiplying the product volume action by `-(-1) ^ m`.

## Main results

* `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_positiveOrientation` and
  `CliffordAlgebra.lid_complexProdTensor_positiveOrientation`: `TensorProduct.lid ℂ F` intertwines
  the left-unit product action with `ρ₂`.
* `CliffordAlgebra.lid_complexProdTensor_positiveOrientation_complexVolume`: `lid ℂ F` carries the
  product volume element to `Γ_W`.
* `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation`,
  `CliffordAlgebra.lid_complexProdTensor_neg_positiveOrientation`, and
  `CliffordAlgebra.lid_complexProdTensor_neg_positiveOrientation_complexVolume`: the negative
  rank-zero orientation twists `ρ₂` by `involute` and multiplies `Γ_W` by `-(-1) ^ m`.
* `CliffordAlgebra.conjAlgEquiv_rid_complexProdTensor`, `CliffordAlgebra.rid_complexProdTensor`,
  `CliffordAlgebra.rid_complexProdTensor_positiveOrientation_complexVolume`, and
  `CliffordAlgebra.rid_complexProdTensor_neg_positiveOrientation_complexVolume`: the right
  unit laws.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Chapter 2, §2.2.
-/

public section

noncomputable section

open Module
open scoped TensorProduct

namespace CliffordAlgebra

section LeftUnit

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] [Subsingleton V] [Fact (finrank ℝ V = 0)]
  {F : Type*} [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- **Left unit law (`positiveOrientation`, pointwise form).** For a zero-dimensional space `V`
with `positiveOrientation`, `TensorProduct.lid ℂ F` intertwines `complexProdTensor` with `ρ₂`. -/
theorem lid_complexProdTensor_positiveOrientation
    (a : CliffordAlgebra (Q.baseChange ℂ)) (z : ℂ ⊗[ℂ] F) :
    (TensorProduct.lid ℂ F)
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0))
          (QuadraticForm.eq_neg_norm_sq_of_subsingleton Q₁) Even.zero ρ₁ ρ₂ a z) =
      ρ₂ (map ((QuadraticMap.IsometryEquiv.withLpSubsingletonProd hQ).toIsometry.baseChange ℂ) a)
        ((TensorProduct.lid ℂ F) z) := by
  rw [complexProdTensor_eq_comp, AlgHom.comp_apply,
    AlgHom.cliffordProdTensor_congr (hγ' := one_mul (1 : Module.End ℂ ℂ))
      (hγ'ρ := fun v ↦ by simp [Subsingleton.elim v 0]) rfl
      (by rw [complexVolume_positiveOrientation, map_one]) rfl,
    AlgHom.lid_cliffordProdTensor, ← AlgHom.comp_apply (map _),
    map_comp_map, QuadraticMap.IsometryEquiv.withLpSubsingletonProd_toIsometry_baseChange]

/-- **Left unit law (`positiveOrientation`, algebra-map form).** Conjugating `complexProdTensor`
for `(V, positiveOrientation, ℂ)` by `TensorProduct.lid ℂ F` recovers `ρ₂` along
`QuadraticMap.IsometryEquiv.withLpSubsingletonProd`. -/
theorem conjAlgEquiv_lid_complexProdTensor_positiveOrientation :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0))
          (QuadraticForm.eq_neg_norm_sq_of_subsingleton Q₁) Even.zero ρ₁ ρ₂) =
      ρ₂.comp (map ((QuadraticMap.IsometryEquiv.withLpSubsingletonProd
        hQ).toIsometry.baseChange ℂ)) :=
  (LinearEquiv.conjAlgEquiv_toAlgHom_comp_eq_iff _ _ _).2
    (lid_complexProdTensor_positiveOrientation hQ ρ₁ ρ₂)

/-- **Signed left unit law (`-positiveOrientation`, algebra-map form).** Choosing
`-positiveOrientation` in dimension zero sets `Γ_V = -1`, twisting `ρ₂` by `involute`. -/
theorem conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (-(positiveOrientation : Orientation ℝ V (Fin 0)))
          (QuadraticForm.eq_neg_norm_sq_of_subsingleton Q₁) Even.zero ρ₁ ρ₂) =
      (ρ₂.comp (involute : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] _)).comp
        (map ((QuadraticMap.IsometryEquiv.withLpSubsingletonProd
          hQ).toIsometry.baseChange ℂ)) := by
  rw [complexProdTensor_neg_orientation_eq_involute]
  exact conjAlgEquiv_lid_complexProdTensor_positiveOrientation hQ ρ₁ (ρ₂.comp involute)

/-- Pointwise form of `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation`.
-/
theorem lid_complexProdTensor_neg_positiveOrientation
    (a : CliffordAlgebra (Q.baseChange ℂ)) (z : ℂ ⊗[ℂ] F) :
    (TensorProduct.lid ℂ F)
        (complexProdTensor hQ (-(positiveOrientation : Orientation ℝ V (Fin 0)))
          (QuadraticForm.eq_neg_norm_sq_of_subsingleton Q₁) Even.zero ρ₁ ρ₂ a z) =
      ρ₂ (involute (map ((QuadraticMap.IsometryEquiv.withLpSubsingletonProd
        hQ).toIsometry.baseChange ℂ) a))
        ((TensorProduct.lid ℂ F) z) :=
  (LinearEquiv.conjAlgEquiv_toAlgHom_comp_eq_iff _ _ _).1
    (conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation hQ ρ₁ ρ₂) a z

section Volume

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))
  [Fact (finrank ℝ (WithLp 2 (V × W)) = 0 + m)]
  (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (0 + m)))

/-- **Left unit law on the volume element.** For `positiveOrientation` on a zero-dimensional space
`V` and any dimension `m` of `W`, `TensorProduct.lid ℂ F` carries the product volume element of
`0 ⊕ W` to `ρ₂ (complexVolume Q₂ o₂)`. -/
theorem lid_complexProdTensor_positiveOrientation_complexVolume
    (ho : ((positiveOrientation : Orientation ℝ V (Fin 0)).prod o₂ Fact.out Fact.out).map
      (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (z : ℂ ⊗[ℂ] F) :
    (TensorProduct.lid ℂ F)
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0))
          (QuadraticForm.eq_neg_norm_sq_of_subsingleton Q₁) Even.zero ρ₁ ρ₂ (complexVolume Q o) z) =
      ρ₂ (complexVolume Q₂ o₂) ((TensorProduct.lid ℂ F) z) := by
  rcases Nat.even_or_odd m with hm | hm
  · rw [complexProdTensor_complexVolume_of_map_prod hQ _ _ Even.zero ρ₁ ρ₂ o₂ o hm ho,
      complexVolume_positiveOrientation, map_one, Module.End.one_eq_id, ← LinearMap.lTensor_def,
      LinearMap.lid_lTensor_apply]
  · rw [complexProdTensor_complexVolume_of_odd_of_map_prod hQ _ _ Even.zero ρ₁ ρ₂ o₂ o hm ho,
      LinearMap.lid_lTensor_apply]

/-- **Signed left unit law on the product volume element.** Choosing `-positiveOrientation` on
`0` multiplies the volume action of `0 ⊕ W` under `TensorProduct.lid ℂ F` by `-(-1) ^ m`, so it
negates `ρ₂ (complexVolume Q₂ o₂)` for even `m` and preserves it for odd `m`. -/
theorem lid_complexProdTensor_neg_positiveOrientation_complexVolume
    (ho : ((-(positiveOrientation : Orientation ℝ V (Fin 0))).prod o₂ Fact.out Fact.out).map
      (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (z : ℂ ⊗[ℂ] F) :
    (TensorProduct.lid ℂ F)
        (complexProdTensor hQ (-(positiveOrientation : Orientation ℝ V (Fin 0)))
          (QuadraticForm.eq_neg_norm_sq_of_subsingleton Q₁) Even.zero ρ₁ ρ₂ (complexVolume Q o) z) =
      (-(-1 : ℂ) ^ m) • ρ₂ (complexVolume Q₂ o₂) ((TensorProduct.lid ℂ F) z) := by
  have ho' : ((positiveOrientation : Orientation ℝ V (Fin 0)).prod o₂ Fact.out Fact.out).map
      (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = -o := by
    rw [← ho, Orientation.map_prod_neg_left, Module.Ray.neg_neg]
  have h := lid_complexProdTensor_positiveOrientation_complexVolume hQ ρ₁ (ρ₂.comp involute) o₂
    (-o) ho' z
  simp only [complexVolume_neg_orientation, map_neg, LinearMap.neg_apply,
    AlgHom.comp_apply, involute_complexVolume, map_smul, LinearMap.smul_apply] at h
  rw [complexProdTensor_neg_orientation_eq_involute, neg_eq_iff_eq_neg.1 h, neg_smul]

end Volume

end LeftUnit

section RightUnit

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  [Subsingleton W]
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E : Type*} [AddCommGroup E] [Module ℂ E]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)

/-- **Right unit law (pointwise form).** `TensorProduct.rid ℂ E` intertwines `complexProdTensor` on
`E ⊗ ℂ` with `ρ₁` on `E` for every Clifford element. -/
theorem rid_complexProdTensor (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] ℂ) :
    (TensorProduct.rid ℂ E) (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      ρ₁ (map ((QuadraticMap.IsometryEquiv.withLpProdSubsingleton hQ).toIsometry.baseChange ℂ) a)
        ((TensorProduct.rid ℂ E) z) := by
  rw [complexProdTensor_eq_comp, AlgHom.comp_apply,
    AlgHom.rid_cliffordProdTensor, ← AlgHom.comp_apply (map _),
    map_comp_map, QuadraticMap.IsometryEquiv.withLpProdSubsingleton_toIsometry_baseChange]

/-- **Right unit law (algebra-map form).** When `W` is a subsingleton, conjugating
`complexProdTensor` on `E ⊗ ℂ` by `TensorProduct.rid ℂ E` recovers `ρ₁` along
`QuadraticMap.IsometryEquiv.withLpProdSubsingleton`. -/
theorem conjAlgEquiv_rid_complexProdTensor :
    ((TensorProduct.rid ℂ E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      ρ₁.comp (map ((QuadraticMap.IsometryEquiv.withLpProdSubsingleton
        hQ).toIsometry.baseChange ℂ)) :=
  (LinearEquiv.conjAlgEquiv_toAlgHom_comp_eq_iff _ _ _).2
    (rid_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂)

section Volume

variable [FiniteDimensional ℝ W] [Fact (finrank ℝ W = 0)]
  [Fact (finrank ℝ (WithLp 2 (V × W)) = n + 0)]
  (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + 0)))

omit [Subsingleton W] in
/-- **Right unit law on the product chirality.** For `positiveOrientation` on `W` of dimension `0`,
`TensorProduct.rid ℂ E` carries the product chirality of `V ⊕ 0` to `ρ₁ (complexVolume Q₁ o₁)`. -/
theorem rid_complexProdTensor_positiveOrientation_complexVolume
    (ho : (o₁.prod (positiveOrientation : Orientation ℝ W (Fin 0)) Fact.out Fact.out).map
      (Fin (n + 0)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (z : E ⊗[ℂ] ℂ) :
    (TensorProduct.rid ℂ E)
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) z) =
      ρ₁ (complexVolume Q₁ o₁) ((TensorProduct.rid ℂ E) z) := by
  rw [complexProdTensor_complexVolume_of_map_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ _ o Even.zero ho,
    complexVolume_positiveOrientation, map_one, Module.End.one_eq_id, ← LinearMap.rTensor_def,
    LinearMap.rid_rTensor_apply]

omit [Subsingleton W] in
/-- **Signed right unit law on the product chirality.** Choosing `-positiveOrientation` on `W` of
dimension `0` negates the product chirality under `TensorProduct.rid ℂ E`. -/
theorem rid_complexProdTensor_neg_positiveOrientation_complexVolume
    (ho : (o₁.prod (-(positiveOrientation : Orientation ℝ W (Fin 0))) Fact.out Fact.out).map
      (Fin (n + 0)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (z : E ⊗[ℂ] ℂ) :
    (TensorProduct.rid ℂ E)
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) z) =
      -ρ₁ (complexVolume Q₁ o₁) ((TensorProduct.rid ℂ E) z) := by
  have ho' : (o₁.prod (positiveOrientation : Orientation ℝ W (Fin 0)) Fact.out Fact.out).map
      (Fin (n + 0)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = -o := by
    rw [← ho, Orientation.map_prod_neg_right, Module.Ray.neg_neg]
  have h := rid_complexProdTensor_positiveOrientation_complexVolume hQ o₁ hQ₁ hn ρ₁ ρ₂ (-o) ho' z
  simp only [complexVolume_neg_orientation, map_neg, LinearMap.neg_apply] at h
  exact neg_eq_iff_eq_neg.1 h

end Volume

end RightUnit

end CliffordAlgebra
