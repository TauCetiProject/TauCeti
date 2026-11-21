/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.QuadraticForm.WithLp
public import Mathlib.LinearAlgebra.TensorProduct.Associator
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Unit

/-!
# Rank-zero unit laws for graded tensor products of complex Clifford modules

A zero-dimensional real inner product space (`finrank = 0`) with `positiveOrientation` and scalar
module `ℂ` acts as a left and right unit for `CliffordAlgebra.complexProdTensor` via
`TensorProduct.lid ℂ F` and `TensorProduct.rid ℂ E` along
`QuadraticMap.IsometryEquiv.withLpSubsingletonProd` / `withLpProdSubsingleton`. Using
`-positiveOrientation` on the left sets `Γ_V = -1`, twisting `ρ₂` by `CliffordAlgebra.involute` and
negating the product chirality for even `m`.

## Main results

* `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_positiveOrientation` and
  `CliffordAlgebra.lid_complexProdTensor_positiveOrientation`: `TensorProduct.lid ℂ F` intertwines
  the left-unit product action with `ρ₂`.
* `CliffordAlgebra.lid_complexProdTensor_positiveOrientation_complexVolume`: `lid ℂ F` carries the
  product volume element to `Γ_W`.
* `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation`,
  `CliffordAlgebra.lid_complexProdTensor_neg_positiveOrientation`, and
  `CliffordAlgebra.lid_complexProdTensor_neg_positiveOrientation_complexVolume`: the negative
  rank-zero orientation twists `ρ₂` by `involute` and negates `Γ_W`.
* `CliffordAlgebra.conjAlgEquiv_rid_complexProdTensor`, `CliffordAlgebra.rid_complexProdTensor`, and
  `CliffordAlgebra.rid_complexProdTensor_positiveOrientation_complexVolume`: the right unit laws.

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
  [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 0)]
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even 0)
  {F : Type*} [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- **Left unit law (`positiveOrientation`, pointwise form).** For a zero-dimensional space `V`
with `positiveOrientation`, `TensorProduct.lid ℂ F` intertwines `complexProdTensor` with `ρ₂`. -/
theorem lid_complexProdTensor_positiveOrientation
    (a : CliffordAlgebra (Q.baseChange ℂ)) (z : ℂ ⊗[ℂ] F) :
    (TensorProduct.lid ℂ F)
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ hn ρ₁ ρ₂ a z) =
      ρ₂ (map ((QuadraticMap.IsometryEquiv.withLpSubsingletonProd hQ
        (Module.finrank_zero_iff.mp (Fact.out : finrank ℝ V = 0))).toIsometry.baseChange ℂ) a)
        ((TensorProduct.lid ℂ F) z) := by
  have hV : Subsingleton V := Module.finrank_zero_iff.mp (Fact.out : finrank ℝ V = 0)
  have hCV : Subsingleton (ℂ ⊗[ℝ] V) := ⟨fun x y ↦ by
    suffices ∀ t : ℂ ⊗[ℝ] V, t = 0 from (this x).trans (this y).symm
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c v => rw [hV.elim v 0, TensorProduct.tmul_zero]
    | add x' y' hx hy => rw [hx, hy, add_zero]⟩
  let : Unique (ℂ ⊗[ℝ] V) := @uniqueOfSubsingleton _ hCV 0
  have hcongr : ∀ (γ : Module.End ℂ ℂ) (h1 : γ * γ = 1)
      (h2 : ∀ v, γ * ρ₁ (ι (Q₁.baseChange ℂ) v) = -(ρ₁ (ι (Q₁.baseChange ℂ) v) * γ)),
      γ = 1 →
      AlgHom.cliffordProdTensor ρ₁ γ h1 h2 ρ₂ =
        AlgHom.cliffordProdTensor ρ₁ 1 (one_mul 1)
          (fun v ↦ by simp [Subsingleton.elim v 0]) ρ₂ := by
    rintro γ h1 h2 rfl; rfl
  have hisom :
      (QuadraticMap.IsometryEquiv.uniqueProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry.comp
          ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ).toIsometry =
        (QuadraticMap.IsometryEquiv.withLpSubsingletonProd hQ hV).toIsometry.baseChange ℂ := by
    refine QuadraticMap.Isometry.ext fun y ↦ ?_
    induction y using TensorProduct.inductionOn with
    | tmul c x =>
      rcases x with ⟨⟨v, w⟩⟩
      simp [QuadraticMap.Isometry.baseChange_tmul,
        QuadraticMap.IsometryEquiv.baseChangeProd_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmap :
      map (QuadraticMap.IsometryEquiv.uniqueProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry
          (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ) a) =
        map ((QuadraticMap.IsometryEquiv.withLpSubsingletonProd hQ hV).toIsometry.baseChange ℂ)
          a := by
    rw [equivOfIsometry_apply, ← AlgHom.comp_apply, map_comp_map, hisom]
  rw [complexProdTensor_eq_comp, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    hcongr _ _ _ (by rw [complexVolume_positiveOrientation, map_one]),
    AlgHom.lid_cliffordProdTensor, hmap]

/-- **Left unit law (`positiveOrientation`, algebra-map form).** Conjugating `complexProdTensor`
for `(V, positiveOrientation, ℂ)` by `TensorProduct.lid ℂ F` recovers `ρ₂` along
`QuadraticMap.IsometryEquiv.withLpSubsingletonProd`. -/
theorem conjAlgEquiv_lid_complexProdTensor_positiveOrientation :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ hn ρ₁ ρ₂) =
      ρ₂.comp (map ((QuadraticMap.IsometryEquiv.withLpSubsingletonProd hQ
        (Module.finrank_zero_iff.mp (Fact.out : finrank ℝ V = 0))).toIsometry.baseChange ℂ)) := by
  refine AlgHom.ext fun a ↦ LinearMap.ext fun y ↦ ?_
  obtain ⟨z, rfl⟩ := (TensorProduct.lid ℂ F).surjective y
  simpa [LinearEquiv.conjAlgEquiv_apply] using
    lid_complexProdTensor_positiveOrientation hQ hQ₁ hn ρ₁ ρ₂ a z

/-- **Signed left unit law (`-positiveOrientation`, algebra-map form).** Choosing
`-positiveOrientation` in dimension zero sets `Γ_V = -1`, twisting `ρ₂` by `involute`. -/
theorem conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (-(positiveOrientation : Orientation ℝ V (Fin 0))) hQ₁ hn ρ₁ ρ₂) =
      (ρ₂.comp (involute : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] _)).comp
        (map ((QuadraticMap.IsometryEquiv.withLpSubsingletonProd hQ
          (Module.finrank_zero_iff.mp (Fact.out : finrank ℝ V = 0))).toIsometry.baseChange ℂ)) := by
  rw [complexProdTensor_neg_orientation_eq_involute]
  exact conjAlgEquiv_lid_complexProdTensor_positiveOrientation hQ hQ₁ hn ρ₁ (ρ₂.comp involute)

/-- Pointwise form of `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation`.
-/
theorem lid_complexProdTensor_neg_positiveOrientation
    (a : CliffordAlgebra (Q.baseChange ℂ)) (z : ℂ ⊗[ℂ] F) :
    (TensorProduct.lid ℂ F)
        (complexProdTensor hQ (-(positiveOrientation : Orientation ℝ V (Fin 0))) hQ₁ hn ρ₁ ρ₂ a z) =
      ρ₂ (involute (map ((QuadraticMap.IsometryEquiv.withLpSubsingletonProd hQ
        (Module.finrank_zero_iff.mp (Fact.out : finrank ℝ V = 0))).toIsometry.baseChange ℂ) a))
        ((TensorProduct.lid ℂ F) z) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using congrArg
    (fun φ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F ↦
      φ a ((TensorProduct.lid ℂ F) z))
    (conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation hQ hQ₁ hn ρ₁ ρ₂)

section Volume

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))
  [Fact (finrank ℝ (WithLp 2 (V × W)) = 0 + m)]
  (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (0 + m)))

/-- **Left unit law on the volume element.** For `positiveOrientation` on a zero-dimensional space
`V` and any dimension `m` of `W`, `TensorProduct.lid ℂ F` carries the product volume element of
`0 ⊕ W` to `ρ₂ (complexVolume Q₂ o₂)`. -/
theorem lid_complexProdTensor_positiveOrientation_complexVolume
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (ho : ((positiveOrientation : Orientation ℝ V (Fin 0)).prod o₂ Fact.out Fact.out).map
      (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (z : ℂ ⊗[ℂ] F) :
    (TensorProduct.lid ℂ F)
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ hn ρ₁ ρ₂
          (complexVolume Q o) z) =
      ρ₂ (complexVolume Q₂ o₂) ((TensorProduct.lid ℂ F) z) := by
  rcases Nat.even_or_odd m with hm | hm
  · rw [complexProdTensor_complexVolume_of_map_prod hQ _ hQ₁ hn ρ₁ ρ₂ o₂ o hm hQ₂ ho,
      complexVolume_positiveOrientation, map_one]
    induction z using TensorProduct.inductionOn with
    | tmul c f => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  · rw [complexProdTensor_complexVolume_of_odd_of_map_prod hQ _ hQ₁ hn ρ₁ ρ₂ o₂ o hm hQ₂ ho]
    induction z using TensorProduct.inductionOn with
    | tmul c f => simp
    | add x y hx hy => simp only [map_add, hx, hy]

/-- **Signed left unit law on the product chirality.** Choosing `-positiveOrientation` on `0`
negates the action of the chirality operator under `TensorProduct.lid ℂ F` for even `m`. -/
theorem lid_complexProdTensor_neg_positiveOrientation_complexVolume (hm : Even m)
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (ho : ((-(positiveOrientation : Orientation ℝ V (Fin 0))).prod o₂ Fact.out Fact.out).map
      (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (z : ℂ ⊗[ℂ] F) :
    (TensorProduct.lid ℂ F)
        (complexProdTensor hQ (-(positiveOrientation : Orientation ℝ V (Fin 0))) hQ₁ hn ρ₁ ρ₂
          (complexVolume Q o) z) =
      -ρ₂ (complexVolume Q₂ o₂) ((TensorProduct.lid ℂ F) z) := by
  rw [complexProdTensor_complexVolume_of_map_prod hQ _ hQ₁ hn ρ₁ ρ₂ o₂ o hm hQ₂ ho,
    complexVolume_neg_orientation, complexVolume_positiveOrientation, map_neg, map_one]
  induction z using TensorProduct.inductionOn with
  | tmul c f => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add_rev, add_comm]

end Volume

end LeftUnit

section RightUnit

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  [FiniteDimensional ℝ W] [Fact (finrank ℝ W = 0)]
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E : Type*} [AddCommGroup E] [Module ℂ E]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)

/-- **Right unit law (pointwise form).** `TensorProduct.rid ℂ E` intertwines `complexProdTensor` on
`E ⊗ ℂ` with `ρ₁` on `E` for every Clifford element. -/
theorem rid_complexProdTensor (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] ℂ) :
    (TensorProduct.rid ℂ E) (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      ρ₁ (map ((QuadraticMap.IsometryEquiv.withLpProdSubsingleton hQ
        (Module.finrank_zero_iff.mp (Fact.out : finrank ℝ W = 0))).toIsometry.baseChange ℂ) a)
        ((TensorProduct.rid ℂ E) z) := by
  have hW : Subsingleton W := Module.finrank_zero_iff.mp (Fact.out : finrank ℝ W = 0)
  have hCW : Subsingleton (ℂ ⊗[ℝ] W) := ⟨fun x y ↦ by
    suffices ∀ t : ℂ ⊗[ℝ] W, t = 0 from (this x).trans (this y).symm
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c w => rw [hW.elim w 0, TensorProduct.tmul_zero]
    | add x' y' hx hy => rw [hx, hy, add_zero]⟩
  let : Unique (ℂ ⊗[ℝ] W) := @uniqueOfSubsingleton _ hCW 0
  have hisom :
      (QuadraticMap.IsometryEquiv.prodUnique (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry.comp
          ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ).toIsometry =
        (QuadraticMap.IsometryEquiv.withLpProdSubsingleton hQ hW).toIsometry.baseChange ℂ := by
    refine QuadraticMap.Isometry.ext fun y ↦ ?_
    induction y using TensorProduct.inductionOn with
    | tmul c x =>
      rcases x with ⟨⟨v, w⟩⟩
      simp [QuadraticMap.Isometry.baseChange_tmul,
        QuadraticMap.IsometryEquiv.baseChangeProd_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmap :
      map (QuadraticMap.IsometryEquiv.prodUnique (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry
          (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ) a) =
        map ((QuadraticMap.IsometryEquiv.withLpProdSubsingleton hQ hW).toIsometry.baseChange ℂ)
          a := by
    rw [equivOfIsometry_apply, ← AlgHom.comp_apply, map_comp_map, hisom]
  rw [complexProdTensor_eq_comp, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgHom.rid_cliffordProdTensor, hmap]

/-- **Right unit law (algebra-map form).** When `finrank ℝ W = 0`, conjugating `complexProdTensor`
on `E ⊗ ℂ` by `TensorProduct.rid ℂ E` recovers `ρ₁` along
`QuadraticMap.IsometryEquiv.withLpProdSubsingleton`. -/
theorem conjAlgEquiv_rid_complexProdTensor :
    ((TensorProduct.rid ℂ E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      ρ₁.comp (map ((QuadraticMap.IsometryEquiv.withLpProdSubsingleton hQ
        (Module.finrank_zero_iff.mp (Fact.out : finrank ℝ W = 0))).toIsometry.baseChange ℂ)) := by
  refine AlgHom.ext fun a ↦ LinearMap.ext fun y ↦ ?_
  obtain ⟨z, rfl⟩ := (TensorProduct.rid ℂ E).surjective y
  simpa [LinearEquiv.conjAlgEquiv_apply] using
    rid_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z

/-- **Right unit law on the product chirality.** For `positiveOrientation` on `W` of dimension `0`,
`TensorProduct.rid ℂ E` carries the product chirality of `V ⊕ 0` to `ρ₁ (complexVolume Q₁ o₁)`. -/
theorem rid_complexProdTensor_positiveOrientation_complexVolume
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + 0)]
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + 0)))
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (ho : (o₁.prod (positiveOrientation : Orientation ℝ W (Fin 0)) Fact.out Fact.out).map
      (Fin (n + 0)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (z : E ⊗[ℂ] ℂ) :
    (TensorProduct.rid ℂ E)
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) z) =
      ρ₁ (complexVolume Q₁ o₁) ((TensorProduct.rid ℂ E) z) := by
  rw [complexProdTensor_complexVolume_of_map_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ _ o Even.zero hQ₂ ho,
    complexVolume_positiveOrientation, map_one]
  induction z using TensorProduct.inductionOn with
  | tmul e c => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end RightUnit

end CliffordAlgebra
