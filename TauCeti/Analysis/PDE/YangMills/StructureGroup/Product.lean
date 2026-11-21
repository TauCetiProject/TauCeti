/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.YangMills.StructureGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import TauCeti.Analysis.Matrix.Exponential.Block

/-!
# Reindexing and block-diagonal products of structure groups

This file constructs the functorial closure operations on compact matrix structure groups:

* `TauCeti.YangMills.StructureGroup.reindex`: transports a structure group along a bijection of
  index types `e : n ≃ m`, with isometric Lie-algebra isomorphism `reindexLieEquiv`.
* `TauCeti.YangMills.StructureGroup.sum`: the block-diagonal product `G₁ × G₂ ≤ U(n ⊕ m)` with
  the orthogonal direct-sum inner product on `𝔤₁ × 𝔤₂`.
* `TauCeti.YangMills.StructureGroup.blockProd`: the `Fin (N₁ + N₂)`-indexed block-diagonal
  product obtained by composing `sum` with `reindex finSumFinEquiv`.

## Main definitions

* `TauCeti.YangMills.unitaryGroupReindexEquiv`: the group isomorphism
  `Matrix.unitaryGroup n ℂ ≃* Matrix.unitaryGroup m ℂ` induced by `e : n ≃ m`.
* `TauCeti.YangMills.StructureGroup.reindex` and `TauCeti.YangMills.StructureGroup.reindexLieEquiv`.
* `TauCeti.YangMills.StructureGroup.sum` and `TauCeti.YangMills.StructureGroup.sumLieEquiv`.
* `TauCeti.YangMills.StructureGroup.blockProd` and
  `TauCeti.YangMills.StructureGroup.blockProdLieEquiv`.

## Main results

* `TauCeti.YangMills.StructureGroup.mem_reindex_lieSubalgebra_iff`,
  `TauCeti.YangMills.StructureGroup.reindexLieEquiv_lie`,
  `TauCeti.YangMills.StructureGroup.reindex_inner`: reindexing induces an isometric Lie-algebra
  isomorphism.
* `TauCeti.YangMills.StructureGroup.mem_sum_lieSubalgebra_iff`,
  `TauCeti.YangMills.StructureGroup.sum_inner_eq`,
  `TauCeti.YangMills.StructureGroup.blockProd_inner_eq`: block-diagonal products have Lie algebra
  `𝔤₁ × 𝔤₂` with the orthogonal direct-sum inner product.

## References

* S.-J. Oh and D. Tataru, *The Yang–Mills heat flow and the caloric gauge*, Astérisque 436 (2022),
  §1.1.
* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), §1.1.
-/

public section

open NormedSpace Set
open scoped ComplexConjugate InnerProductSpace Matrix

noncomputable section

namespace TauCeti.YangMills

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Reindexing along a bijection of index types -/

section ReindexCont

variable {n : Type u} {m : Type v}

private theorem continuous_reindex_matrix (e : n ≃ m) :
    Continuous (fun A : Matrix n n ℂ ↦ Matrix.reindex e e A) := by
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  exact (continuous_apply (e.symm j)).comp (continuous_apply (e.symm i))

end ReindexCont

section Reindex

variable {n : Type u} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Reindexing unitary matrices along an equivalence `e : n ≃ m`, as a group isomorphism
`Matrix.unitaryGroup n ℂ ≃* Matrix.unitaryGroup m ℂ`. -/
def unitaryGroupReindexEquiv (e : n ≃ m) :
    Matrix.unitaryGroup n ℂ ≃* Matrix.unitaryGroup m ℂ where
  toFun U := ⟨Matrix.reindex e e (U : Matrix n n ℂ),
    Matrix.submatrix_equiv_mem_unitary.2 U.2⟩
  invFun V := ⟨Matrix.reindex e.symm e.symm (V : Matrix m m ℂ),
    Matrix.submatrix_equiv_mem_unitary.2 V.2⟩
  left_inv U := Subtype.ext (by simp [Matrix.reindex_apply])
  right_inv V := Subtype.ext (by simp [Matrix.reindex_apply])
  map_mul' U V := Subtype.ext (by
    simp only [Submonoid.coe_mul, Matrix.reindex_apply, Matrix.submatrix_mul_equiv])

@[simp]
theorem coe_unitaryGroupReindexEquiv (e : n ≃ m) (U : Matrix.unitaryGroup n ℂ) :
    (unitaryGroupReindexEquiv e U : Matrix m m ℂ) = Matrix.reindex e e (U : Matrix n n ℂ) :=
  (rfl)

@[simp]
theorem coe_unitaryGroupReindexEquiv_symm (e : n ≃ m) (V : Matrix.unitaryGroup m ℂ) :
    ((unitaryGroupReindexEquiv e).symm V : Matrix n n ℂ) =
      Matrix.reindex e.symm e.symm (V : Matrix m m ℂ) :=
  (rfl)

theorem continuous_unitaryGroupReindexEquiv (e : n ≃ m) :
    Continuous (unitaryGroupReindexEquiv e) :=
  continuous_induced_rng.mpr ((continuous_reindex_matrix e).comp continuous_subtype_val)

open scoped Matrix.Norms.Operator in
private theorem reindex_exp_eq_op (e : n ≃ m) (X : Matrix n n ℂ) :
    NormedSpace.exp (Matrix.reindex e e X) = Matrix.reindex e e (NormedSpace.exp X) := by
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := TauCeti.normedAlgebraRatOfReal
  have hcont : Continuous (Matrix.reindexRingEquiv ℂ e : Matrix n n ℂ → Matrix m m ℂ) :=
    continuous_reindex_matrix e
  exact (NormedSpace.map_exp (Matrix.reindexRingEquiv ℂ e) hcont X).symm

private theorem reindex_exp_eq (e : n ≃ m) (X : Matrix n n ℂ) :
    NormedSpace.exp (Matrix.reindex e e X) = Matrix.reindex e e (NormedSpace.exp X) :=
  reindex_exp_eq_op e X

private theorem isClosed_map_reindex {H : Subgroup (Matrix.unitaryGroup n ℂ)}
    (hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ))) (e : n ≃ m) :
    IsClosed ((H.map (unitaryGroupReindexEquiv e).toMonoidHom :
      Subgroup (Matrix.unitaryGroup m ℂ)) : Set (Matrix.unitaryGroup m ℂ)) := by
  have hcomp : IsCompact (H : Set (Matrix.unitaryGroup n ℂ)) := hH.isCompact
  have himg : ((H.map (unitaryGroupReindexEquiv e).toMonoidHom :
      Subgroup (Matrix.unitaryGroup m ℂ)) : Set (Matrix.unitaryGroup m ℂ)) =
      unitaryGroupReindexEquiv e '' (H : Set (Matrix.unitaryGroup n ℂ)) :=
    Subgroup.coe_map _ _
  rw [himg]
  exact (hcomp.image (continuous_unitaryGroupReindexEquiv e)).isClosed

private theorem mem_unitaryLieSubalgebra_reindex_iff {H : Subgroup (Matrix.unitaryGroup n ℂ)}
    (hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ))) (e : n ≃ m) (Y : Matrix m m ℂ) :
    Y ∈ unitaryLieSubalgebra (H.map (unitaryGroupReindexEquiv e).toMonoidHom) ↔
      Matrix.reindex e.symm e.symm Y ∈ unitaryLieSubalgebra H := by
  have hH' := isClosed_map_reindex hH e
  rw [mem_unitaryLieSubalgebra_iff hH', mem_unitaryLieSubalgebra_iff hH]
  refine forall_congr' fun t ↦ ?_
  have hsmul : Matrix.reindex e.symm e.symm (t • Y) = t • Matrix.reindex e.symm e.symm Y := by
    ext i j; rfl
  simp only [Set.mem_image, SetLike.mem_coe, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨V, ⟨U, hU, rfl⟩, hEq⟩
    refine ⟨U, hU, ?_⟩
    have hre := congrArg (Matrix.reindex e.symm e.symm) hEq
    rw [coe_unitaryGroupReindexEquiv, ← reindex_exp_eq e.symm, hsmul] at hre
    simpa [Matrix.reindex_apply] using hre
  · rintro ⟨U, hU, hEq⟩
    refine ⟨unitaryGroupReindexEquiv e U, ⟨U, hU, rfl⟩, ?_⟩
    have hre := congrArg (Matrix.reindex e e) hEq
    rw [← coe_unitaryGroupReindexEquiv, ← reindex_exp_eq e, ← hsmul] at hre
    simpa [Matrix.reindex_apply] using hre

namespace StructureGroup

private def reindexLieSubalgebraSymm (G : StructureGroup n) (e : n ≃ m) :
    unitaryLieSubalgebra (G.subgroup.map (unitaryGroupReindexEquiv e).toMonoidHom) →ₗ[ℝ]
      G.lieSubalgebra where
  toFun X := ⟨Matrix.reindex e.symm e.symm X.1,
    (mem_unitaryLieSubalgebra_reindex_iff G.isClosed e X.1).1 X.2⟩
  map_add' _ _ := Subtype.ext (by ext i j; rfl)
  map_smul' _ _ := Subtype.ext (by ext i j; rfl)

/-- Transport a compact matrix structure group along a bijection of index types `e : n ≃ m`. -/
def reindex (G : StructureGroup n) (e : n ≃ m) : StructureGroup m where
  subgroup := G.subgroup.map (unitaryGroupReindexEquiv e).toMonoidHom
  isClosed := isClosed_map_reindex G.isClosed e
  bilinForm :=
    G.bilinForm.comp (reindexLieSubalgebraSymm G e) (reindexLieSubalgebraSymm G e)
  bilinForm_symm := LinearMap.BilinForm.isSymm_def.2 fun X Y ↦ by
    simp only [LinearMap.BilinForm.comp_apply]
    exact G.bilinForm_symm.eq _ _
  bilinForm_pos X hX := by
    rw [LinearMap.BilinForm.comp_apply]
    apply G.bilinForm_pos
    intro h
    apply hX
    apply Subtype.ext
    have hval : Matrix.reindex e.symm e.symm X.1 = 0 :=
      congrArg (Subtype.val : G.lieSubalgebra → Matrix n n ℂ) h
    have hre := congrArg (Matrix.reindex e e) hval
    simpa [Matrix.reindex_apply] using hre
  bilinForm_conj g X Y := by
    rcases g.2 with ⟨u, hu, hgu⟩
    have hgu' : (g.1 : Matrix m m ℂ) = Matrix.reindex e e (u : Matrix n n ℂ) := by
      have := congrArg Subtype.val hgu
      simpa [coe_unitaryGroupReindexEquiv] using this.symm
    have hmul : ∀ Z : Matrix m m ℂ,
        Matrix.reindex e.symm e.symm ((g.1 : Matrix m m ℂ) * Z * (g.1 : Matrix m m ℂ)ᴴ) =
          (u : Matrix n n ℂ) * Matrix.reindex e.symm e.symm Z * (u : Matrix n n ℂ)ᴴ := by
      intro Z
      rw [hgu']
      change Matrix.reindexRingEquiv ℂ e.symm
        (Matrix.reindex e e (u : Matrix n n ℂ) * Z * (Matrix.reindex e e (u : Matrix n n ℂ))ᴴ) = _
      rw [map_mul, map_mul]
      simp [Matrix.reindexRingEquiv, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
    have hX : reindexLieSubalgebraSymm G e
        ⟨(g.1 : Matrix m m ℂ) * X.1 * (g.1 : Matrix m m ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra g.2 X.2⟩ =
        ⟨(u : Matrix n n ℂ) * (reindexLieSubalgebraSymm G e X).1 * (u : Matrix n n ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra hu (reindexLieSubalgebraSymm G e X).2⟩ :=
      Subtype.ext (hmul X.1)
    have hY : reindexLieSubalgebraSymm G e
        ⟨(g.1 : Matrix m m ℂ) * Y.1 * (g.1 : Matrix m m ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra g.2 Y.2⟩ =
        ⟨(u : Matrix n n ℂ) * (reindexLieSubalgebraSymm G e Y).1 * (u : Matrix n n ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra hu (reindexLieSubalgebraSymm G e Y).2⟩ :=
      Subtype.ext (hmul Y.1)
    simp only [LinearMap.BilinForm.comp_apply]
    rw [hX, hY]
    exact G.bilinForm_conj ⟨u, hu⟩ (reindexLieSubalgebraSymm G e X)
      (reindexLieSubalgebraSymm G e Y)

theorem mem_reindex_subgroup_iff (G : StructureGroup n) (e : n ≃ m)
    (V : Matrix.unitaryGroup m ℂ) :
    V ∈ (G.reindex e).subgroup ↔ (unitaryGroupReindexEquiv e).symm V ∈ G.subgroup := by
  change V ∈ G.subgroup.map (unitaryGroupReindexEquiv e).toMonoidHom ↔ _
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨U, hU, rfl⟩
    simpa using hU
  · intro hV
    exact ⟨(unitaryGroupReindexEquiv e).symm V, hV, by simp⟩

theorem mem_reindex_lieSubalgebra_iff (G : StructureGroup n) (e : n ≃ m) (Y : Matrix m m ℂ) :
    Y ∈ (G.reindex e).lieSubalgebra ↔ Matrix.reindex e.symm e.symm Y ∈ G.lieSubalgebra :=
  mem_unitaryLieSubalgebra_reindex_iff G.isClosed e Y

/-- The canonical isometric isomorphism `G.LieAlgebra ≃ₗᵢ[ℝ] (G.reindex e).LieAlgebra`. -/
def reindexLieEquiv (G : StructureGroup n) (e : n ≃ m) :
    G.LieAlgebra ≃ₗᵢ[ℝ] (G.reindex e).LieAlgebra where
  toFun X := ⟨Matrix.reindex e e X.val,
    (G.mem_reindex_lieSubalgebra_iff e _).2 (by simpa [Matrix.reindex_apply] using X.property)⟩
  invFun Y := ⟨Matrix.reindex e.symm e.symm Y.val,
    (G.mem_reindex_lieSubalgebra_iff e Y.val).1 Y.property⟩
  map_add' _ _ := LieAlgebra.ext (by ext i j; rfl)
  map_smul' _ _ := LieAlgebra.ext (by ext i j; rfl)
  left_inv X := LieAlgebra.ext (by simp [Matrix.reindex_apply])
  right_inv Y := LieAlgebra.ext (by simp [Matrix.reindex_apply])
  norm_map' X := by
    let Y : (G.reindex e).LieAlgebra := ⟨Matrix.reindex e e X.val,
      (G.mem_reindex_lieSubalgebra_iff e _).2 (by simpa [Matrix.reindex_apply] using X.property)⟩
    change ‖Y‖ = ‖X‖
    have hsq : ‖Y‖ ^ 2 = ‖X‖ ^ 2 := by
      rw [LieAlgebra.norm_sq_eq_bilinForm, LieAlgebra.norm_sq_eq_bilinForm]
      have hre : reindexLieSubalgebraSymm G e Y.toSubalgebra = X.toSubalgebra := by
        apply Subtype.ext
        change Matrix.reindex e.symm e.symm (Matrix.reindex e e X.val) = X.val
        simp [Matrix.reindex_apply]
      change G.bilinForm (reindexLieSubalgebraSymm G e Y.toSubalgebra)
        (reindexLieSubalgebraSymm G e Y.toSubalgebra) = G.bilinForm X.toSubalgebra X.toSubalgebra
      rw [hre]
    nlinarith [norm_nonneg X, norm_nonneg Y]

@[simp]
theorem reindexLieEquiv_val (G : StructureGroup n) (e : n ≃ m) (X : G.LieAlgebra) :
    (G.reindexLieEquiv e X).val = Matrix.reindex e e X.val :=
  (rfl)

@[simp]
theorem reindexLieEquiv_symm_val (G : StructureGroup n) (e : n ≃ m)
    (Y : (G.reindex e).LieAlgebra) :
    ((G.reindexLieEquiv e).symm Y).val = Matrix.reindex e.symm e.symm Y.val :=
  (rfl)

theorem reindexLieEquiv_lie (G : StructureGroup n) (e : n ≃ m) (X Y : G.LieAlgebra) :
    G.reindexLieEquiv e ⁅X, Y⁆ = ⁅G.reindexLieEquiv e X, G.reindexLieEquiv e Y⁆ := by
  apply LieAlgebra.ext
  simp [reindexLieEquiv_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.submatrix_sub]

theorem reindex_inner (G : StructureGroup n) (e : n ≃ m) (X Y : G.LieAlgebra) :
    ⟪G.reindexLieEquiv e X, G.reindexLieEquiv e Y⟫_ℝ = ⟪X, Y⟫_ℝ :=
  (G.reindexLieEquiv e).inner_map_map X Y

end StructureGroup

end Reindex

/-! ### Block-diagonal products `G₁.sum G₂` and `G₁.blockProd G₂` -/

section BlockProduct

variable {n : Type u} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

private theorem continuous_unitaryGroup_sum :
    Continuous (Matrix.UnitaryGroup.sum :
      Matrix.unitaryGroup n ℂ × Matrix.unitaryGroup m ℂ → Matrix.unitaryGroup (n ⊕ m) ℂ) := by
  refine continuous_induced_rng.mpr (continuous_pi fun i ↦ continuous_pi fun j ↦ ?_)
  have h1 : Continuous fun p : Matrix.unitaryGroup n ℂ × Matrix.unitaryGroup m ℂ ↦
      (p.1 : Matrix n n ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun p : Matrix.unitaryGroup n ℂ × Matrix.unitaryGroup m ℂ ↦
      (p.2 : Matrix m m ℂ) :=
    continuous_subtype_val.comp continuous_snd
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [Function.comp_def, Matrix.UnitaryGroup.coe_sum, Matrix.fromBlocks_apply₁₁]
      exact (continuous_apply j).comp ((continuous_apply i).comp h1)
    | inr j =>
      simpa [Matrix.UnitaryGroup.coe_sum] using (continuous_const : Continuous fun _ ↦ (0 : ℂ))
  | inr i =>
    cases j with
    | inl j =>
      simpa [Matrix.UnitaryGroup.coe_sum] using (continuous_const : Continuous fun _ ↦ (0 : ℂ))
    | inr j =>
      simp only [Function.comp_def, Matrix.UnitaryGroup.coe_sum, Matrix.fromBlocks_apply₂₂]
      exact (continuous_apply j).comp ((continuous_apply i).comp h2)

private theorem isClosed_sum_subgroup {H₁ : Subgroup (Matrix.unitaryGroup n ℂ)}
    {H₂ : Subgroup (Matrix.unitaryGroup m ℂ)}
    (hH₁ : IsClosed (H₁ : Set (Matrix.unitaryGroup n ℂ)))
    (hH₂ : IsClosed (H₂ : Set (Matrix.unitaryGroup m ℂ))) :
    IsClosed (((H₁.prod H₂).map Matrix.UnitaryGroup.sum :
      Subgroup (Matrix.unitaryGroup (n ⊕ m) ℂ)) : Set (Matrix.unitaryGroup (n ⊕ m) ℂ)) := by
  have hcomp : IsCompact ((H₁.prod H₂ : Subgroup _) :
      Set (Matrix.unitaryGroup n ℂ × Matrix.unitaryGroup m ℂ)) :=
    hH₁.isCompact.prod hH₂.isCompact
  have himg : (((H₁.prod H₂).map Matrix.UnitaryGroup.sum :
      Subgroup (Matrix.unitaryGroup (n ⊕ m) ℂ)) : Set (Matrix.unitaryGroup (n ⊕ m) ℂ)) =
      Matrix.UnitaryGroup.sum '' ((H₁.prod H₂ : Subgroup _) :
        Set (Matrix.unitaryGroup n ℂ × Matrix.unitaryGroup m ℂ)) :=
    Subgroup.coe_map _ _
  rw [himg]
  exact (hcomp.image continuous_unitaryGroup_sum).isClosed

open scoped Matrix.Norms.Operator in
private theorem exp_fromBlocks_diagonal_op (X₁ : Matrix n n ℂ) (X₂ : Matrix m m ℂ) :
    NormedSpace.exp (Matrix.fromBlocks X₁ 0 0 X₂) =
      Matrix.fromBlocks (NormedSpace.exp X₁) 0 0 (NormedSpace.exp X₂) := by
  let _ : NormedAlgebra ℚ ℂ := TauCeti.normedAlgebraRatOfReal
  exact Matrix.exp_fromBlocks_diagonal X₁ X₂

private theorem exp_fromBlocks_diagonal_complex (X₁ : Matrix n n ℂ) (X₂ : Matrix m m ℂ) :
    NormedSpace.exp (Matrix.fromBlocks X₁ 0 0 X₂) =
      Matrix.fromBlocks (NormedSpace.exp X₁) 0 0 (NormedSpace.exp X₂) :=
  exp_fromBlocks_diagonal_op X₁ X₂

open scoped Matrix.Norms.Operator in
private theorem hasDerivAt_exp_smul_entry_op {p : Type*} [Fintype p] [DecidableEq p]
    (X : Matrix p p ℂ) (a b : p) :
    HasDerivAt (fun t : ℝ ↦ NormedSpace.exp (t • X) a b) (X a b) 0 := by
  let _ : NormedAlgebra ℚ (Matrix p p ℂ) := TauCeti.normedAlgebraRatOfReal
  let eval : Matrix p p ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M ↦ M a b
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hexp := hasDerivAt_exp_smul_const X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hexp
  exact (LinearMap.toContinuousLinearMap eval).hasFDerivAt.comp_hasDerivAt 0 hexp

private theorem hasDerivAt_exp_smul_entry {p : Type*} [Fintype p] [DecidableEq p]
    (X : Matrix p p ℂ) (a b : p) :
    HasDerivAt (fun t : ℝ ↦ NormedSpace.exp (t • X) a b) (X a b) 0 :=
  hasDerivAt_exp_smul_entry_op X a b

private theorem mem_unitaryLieSubalgebra_sum_iff {H₁ : Subgroup (Matrix.unitaryGroup n ℂ)}
    {H₂ : Subgroup (Matrix.unitaryGroup m ℂ)}
    (hH₁ : IsClosed (H₁ : Set (Matrix.unitaryGroup n ℂ)))
    (hH₂ : IsClosed (H₂ : Set (Matrix.unitaryGroup m ℂ)))
    (X : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    X ∈ unitaryLieSubalgebra ((H₁.prod H₂).map Matrix.UnitaryGroup.sum) ↔
      ∃ X₁ ∈ unitaryLieSubalgebra H₁, ∃ X₂ ∈ unitaryLieSubalgebra H₂,
        X = Matrix.fromBlocks X₁ 0 0 X₂ := by
  have hH := isClosed_sum_subgroup hH₁ hH₂
  rw [mem_unitaryLieSubalgebra_iff hH]
  constructor
  · intro hX
    have h12 : ∀ i j, X (Sum.inl i) (Sum.inr j) = 0 := by
      intro i j
      have hconst : (fun t : ℝ ↦ NormedSpace.exp (t • X) (Sum.inl i) (Sum.inr j)) =
          fun _ ↦ 0 := by
        funext t
        rcases hX t with ⟨U, ⟨⟨u₁, u₂⟩, -, rfl⟩, hEq⟩
        rw [← hEq]
        simp [Matrix.UnitaryGroup.coe_sum]
      have h0 :
          HasDerivAt (fun t : ℝ ↦ NormedSpace.exp (t • X) (Sum.inl i) (Sum.inr j)) 0 0 := by
        rw [hconst]
        exact hasDerivAt_const 0 (0 : ℂ)
      exact (hasDerivAt_exp_smul_entry X (Sum.inl i) (Sum.inr j)).unique h0
    have h21 : ∀ i j, X (Sum.inr i) (Sum.inl j) = 0 := by
      intro i j
      have hconst : (fun t : ℝ ↦ NormedSpace.exp (t • X) (Sum.inr i) (Sum.inl j)) =
          fun _ ↦ 0 := by
        funext t
        rcases hX t with ⟨U, ⟨⟨u₁, u₂⟩, -, rfl⟩, hEq⟩
        rw [← hEq]
        simp [Matrix.UnitaryGroup.coe_sum]
      have h0 :
          HasDerivAt (fun t : ℝ ↦ NormedSpace.exp (t • X) (Sum.inr i) (Sum.inl j)) 0 0 := by
        rw [hconst]
        exact hasDerivAt_const 0 (0 : ℂ)
      exact (hasDerivAt_exp_smul_entry X (Sum.inr i) (Sum.inl j)).unique h0
    have hblock : X = Matrix.fromBlocks X.toBlocks₁₁ 0 0 X.toBlocks₂₂ := by
      ext (i | i) (j | j)
      · rfl
      · exact h12 i j
      · exact h21 i j
      · rfl
    refine ⟨X.toBlocks₁₁, ?_, X.toBlocks₂₂, ?_, hblock⟩
    · rw [mem_unitaryLieSubalgebra_iff hH₁]
      intro t
      rcases hX t with ⟨U, ⟨⟨u₁, u₂⟩, ⟨hu₁, _⟩, rfl⟩, hEq⟩
      have hsmul : t • X = Matrix.fromBlocks (t • X.toBlocks₁₁) 0 0 (t • X.toBlocks₂₂) := by
        rw [hblock]
        ext (i | i) (j | j) <;> simp
      rw [hsmul, exp_fromBlocks_diagonal_complex, Matrix.UnitaryGroup.coe_sum] at hEq
      exact ⟨u₁, hu₁, (Matrix.fromBlocks_inj.1 hEq).1⟩
    · rw [mem_unitaryLieSubalgebra_iff hH₂]
      intro t
      rcases hX t with ⟨U, ⟨⟨u₁, u₂⟩, ⟨_, hu₂⟩, rfl⟩, hEq⟩
      have hsmul : t • X = Matrix.fromBlocks (t • X.toBlocks₁₁) 0 0 (t • X.toBlocks₂₂) := by
        rw [hblock]
        ext (i | i) (j | j) <;> simp
      rw [hsmul, exp_fromBlocks_diagonal_complex, Matrix.UnitaryGroup.coe_sum] at hEq
      exact ⟨u₂, hu₂, (Matrix.fromBlocks_inj.1 hEq).2.2.2⟩
  · rintro ⟨X₁, hX₁, X₂, hX₂, rfl⟩ t
    obtain ⟨u₁, hu₁, heq₁⟩ := (mem_unitaryLieSubalgebra_iff hH₁ X₁).1 hX₁ t
    obtain ⟨u₂, hu₂, heq₂⟩ := (mem_unitaryLieSubalgebra_iff hH₂ X₂).1 hX₂ t
    refine ⟨Matrix.UnitaryGroup.sum (u₁, u₂), ⟨(u₁, u₂), ⟨hu₁, hu₂⟩, rfl⟩, ?_⟩
    have hsmul : t • Matrix.fromBlocks X₁ 0 0 X₂ = Matrix.fromBlocks (t • X₁) 0 0 (t • X₂) := by
      ext (i | i) (j | j) <;> simp
    rw [hsmul, exp_fromBlocks_diagonal_complex, Matrix.UnitaryGroup.coe_sum, heq₁, heq₂]

namespace StructureGroup

private def sumLieSubalgebraFst (G₁ : StructureGroup n) (G₂ : StructureGroup m) :
    unitaryLieSubalgebra ((G₁.subgroup.prod G₂.subgroup).map Matrix.UnitaryGroup.sum) →ₗ[ℝ]
      G₁.lieSubalgebra where
  toFun X := ⟨X.1.toBlocks₁₁, by
    obtain ⟨X₁, hX₁, _, _, hEq⟩ :=
      (mem_unitaryLieSubalgebra_sum_iff G₁.isClosed G₂.isClosed X.1).1 X.2
    simpa [hEq] using hX₁⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private def sumLieSubalgebraSnd (G₁ : StructureGroup n) (G₂ : StructureGroup m) :
    unitaryLieSubalgebra ((G₁.subgroup.prod G₂.subgroup).map Matrix.UnitaryGroup.sum) →ₗ[ℝ]
      G₂.lieSubalgebra where
  toFun X := ⟨X.1.toBlocks₂₂, by
    obtain ⟨_, _, X₂, hX₂, hEq⟩ :=
      (mem_unitaryLieSubalgebra_sum_iff G₁.isClosed G₂.isClosed X.1).1 X.2
    simpa [hEq] using hX₂⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The block-diagonal product `G₁ × G₂ ≤ U(n ⊕ m)` of two compact matrix structure groups,
equipped with the orthogonal direct-sum inner product on `𝔤₁ × 𝔤₂`. -/
def sum (G₁ : StructureGroup n) (G₂ : StructureGroup m) : StructureGroup (n ⊕ m) where
  subgroup := (G₁.subgroup.prod G₂.subgroup).map Matrix.UnitaryGroup.sum
  isClosed := isClosed_sum_subgroup G₁.isClosed G₂.isClosed
  bilinForm :=
    G₁.bilinForm.comp (sumLieSubalgebraFst G₁ G₂) (sumLieSubalgebraFst G₁ G₂) +
      G₂.bilinForm.comp (sumLieSubalgebraSnd G₁ G₂) (sumLieSubalgebraSnd G₁ G₂)
  bilinForm_symm := LinearMap.BilinForm.isSymm_def.2 fun X Y ↦ by
    simp only [LinearMap.add_apply, LinearMap.BilinForm.comp_apply]
    rw [G₁.bilinForm_symm.eq _ _, G₂.bilinForm_symm.eq _ _]
  bilinForm_pos X hX := by
    simp only [LinearMap.add_apply, LinearMap.BilinForm.comp_apply]
    obtain ⟨X₁, _, X₂, _, hEq⟩ :=
      (mem_unitaryLieSubalgebra_sum_iff G₁.isClosed G₂.isClosed X.1).1 X.2
    have h1_nonneg : 0 ≤ G₁.bilinForm (sumLieSubalgebraFst G₁ G₂ X)
        (sumLieSubalgebraFst G₁ G₂ X) := by
      by_cases h0 : sumLieSubalgebraFst G₁ G₂ X = 0
      · simp [h0]
      · exact le_of_lt (G₁.bilinForm_pos _ h0)
    have h2_nonneg : 0 ≤ G₂.bilinForm (sumLieSubalgebraSnd G₁ G₂ X)
        (sumLieSubalgebraSnd G₁ G₂ X) := by
      by_cases h0 : sumLieSubalgebraSnd G₁ G₂ X = 0
      · simp [h0]
      · exact le_of_lt (G₂.bilinForm_pos _ h0)
    by_cases h1 : sumLieSubalgebraFst G₁ G₂ X = 0
    · have h2 : sumLieSubalgebraSnd G₁ G₂ X ≠ 0 := by
        intro h20
        apply hX
        apply Subtype.ext
        have hX₁0 : X₁ = 0 := by
          have := congrArg (Subtype.val : G₁.lieSubalgebra → Matrix n n ℂ) h1
          simpa [sumLieSubalgebraFst, hEq] using this
        have hX₂0 : X₂ = 0 := by
          have := congrArg (Subtype.val : G₂.lieSubalgebra → Matrix m m ℂ) h20
          simpa [sumLieSubalgebraSnd, hEq] using this
        simp [hEq, hX₁0, hX₂0]
      linarith [G₂.bilinForm_pos _ h2]
    · linarith [G₁.bilinForm_pos _ h1]
  bilinForm_conj g X Y := by
    rcases g.2 with ⟨⟨u₁, u₂⟩, ⟨hu₁, hu₂⟩, hgu⟩
    have hgmat : (g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) =
        Matrix.fromBlocks (u₁ : Matrix n n ℂ) 0 0 (u₂ : Matrix m m ℂ) := by
      have := congrArg Subtype.val hgu
      simpa [Matrix.UnitaryGroup.coe_sum] using this.symm
    obtain ⟨X₁, _, X₂, _, hXEq⟩ :=
      (mem_unitaryLieSubalgebra_sum_iff G₁.isClosed G₂.isClosed X.1).1 X.2
    obtain ⟨Y₁, _, Y₂, _, hYEq⟩ :=
      (mem_unitaryLieSubalgebra_sum_iff G₁.isClosed G₂.isClosed Y.1).1 Y.2
    have hconj_blocks : ∀ (A₁ : Matrix n n ℂ) (A₂ : Matrix m m ℂ),
        (g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) * Matrix.fromBlocks A₁ 0 0 A₂ *
          (g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ)ᴴ =
        Matrix.fromBlocks
          ((u₁ : Matrix n n ℂ) * A₁ * (u₁ : Matrix n n ℂ)ᴴ) 0 0
          ((u₂ : Matrix m m ℂ) * A₂ * (u₂ : Matrix m m ℂ)ᴴ) := by
      intro A₁ A₂
      rw [hgmat, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp
    have hX1 : sumLieSubalgebraFst G₁ G₂
        ⟨(g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) * X.1 * (g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra g.2 X.2⟩ =
        ⟨(u₁ : Matrix n n ℂ) * (sumLieSubalgebraFst G₁ G₂ X).1 * (u₁ : Matrix n n ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra hu₁ (sumLieSubalgebraFst G₁ G₂ X).2⟩ := by
      apply Subtype.ext
      change ((g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) * X.1 *
        (g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ)ᴴ).toBlocks₁₁ = _
      rw [hXEq, hconj_blocks]
      simp [sumLieSubalgebraFst, hXEq]
    have hX2 : sumLieSubalgebraSnd G₁ G₂
        ⟨(g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) * X.1 * (g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra g.2 X.2⟩ =
        ⟨(u₂ : Matrix m m ℂ) * (sumLieSubalgebraSnd G₁ G₂ X).1 * (u₂ : Matrix m m ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra hu₂ (sumLieSubalgebraSnd G₁ G₂ X).2⟩ := by
      apply Subtype.ext
      change ((g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) * X.1 *
        (g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ)ᴴ).toBlocks₂₂ = _
      rw [hXEq, hconj_blocks]
      simp [sumLieSubalgebraSnd, hXEq]
    have hY1 : sumLieSubalgebraFst G₁ G₂
        ⟨(g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) * Y.1 * (g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra g.2 Y.2⟩ =
        ⟨(u₁ : Matrix n n ℂ) * (sumLieSubalgebraFst G₁ G₂ Y).1 * (u₁ : Matrix n n ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra hu₁ (sumLieSubalgebraFst G₁ G₂ Y).2⟩ := by
      apply Subtype.ext
      change ((g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) * Y.1 *
        (g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ)ᴴ).toBlocks₁₁ = _
      rw [hYEq, hconj_blocks]
      simp [sumLieSubalgebraFst, hYEq]
    have hY2 : sumLieSubalgebraSnd G₁ G₂
        ⟨(g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) * Y.1 * (g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra g.2 Y.2⟩ =
        ⟨(u₂ : Matrix m m ℂ) * (sumLieSubalgebraSnd G₁ G₂ Y).1 * (u₂ : Matrix m m ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra hu₂ (sumLieSubalgebraSnd G₁ G₂ Y).2⟩ := by
      apply Subtype.ext
      change ((g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) * Y.1 *
        (g.1 : Matrix (n ⊕ m) (n ⊕ m) ℂ)ᴴ).toBlocks₂₂ = _
      rw [hYEq, hconj_blocks]
      simp [sumLieSubalgebraSnd, hYEq]
    simp only [LinearMap.add_apply, LinearMap.BilinForm.comp_apply]
    rw [hX1, hX2, hY1, hY2, G₁.bilinForm_conj ⟨u₁, hu₁⟩, G₂.bilinForm_conj ⟨u₂, hu₂⟩]

theorem mem_sum_subgroup_iff (G₁ : StructureGroup n) (G₂ : StructureGroup m)
    (U : Matrix.unitaryGroup (n ⊕ m) ℂ) :
    U ∈ (G₁.sum G₂).subgroup ↔
      ∃ u₁ ∈ G₁.subgroup, ∃ u₂ ∈ G₂.subgroup, Matrix.UnitaryGroup.sum (u₁, u₂) = U := by
  change U ∈ (G₁.subgroup.prod G₂.subgroup).map Matrix.UnitaryGroup.sum ↔ _
  simp only [Subgroup.mem_map, Subgroup.mem_prod, Prod.exists]
  exact ⟨fun ⟨a, b, ⟨ha, hb⟩, h⟩ ↦ ⟨a, ha, b, hb, h⟩,
    fun ⟨a, ha, b, hb, h⟩ ↦ ⟨a, b, ⟨ha, hb⟩, h⟩⟩

theorem mem_sum_lieSubalgebra_iff (G₁ : StructureGroup n) (G₂ : StructureGroup m)
    (X : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    X ∈ (G₁.sum G₂).lieSubalgebra ↔
      ∃ X₁ ∈ G₁.lieSubalgebra, ∃ X₂ ∈ G₂.lieSubalgebra, X = Matrix.fromBlocks X₁ 0 0 X₂ :=
  mem_unitaryLieSubalgebra_sum_iff G₁.isClosed G₂.isClosed X

/-- The canonical Lie-algebra isomorphism `(G₁.sum G₂).LieAlgebra ≃ₗ⁅ℝ⁆
G₁.LieAlgebra × G₂.LieAlgebra`. -/
def sumLieEquiv (G₁ : StructureGroup n) (G₂ : StructureGroup m) :
    (G₁.sum G₂).LieAlgebra ≃ₗ⁅ℝ⁆ G₁.LieAlgebra × G₂.LieAlgebra where
  toFun X :=
    (⟨(sumLieSubalgebraFst G₁ G₂ X.toSubalgebra).1,
        (sumLieSubalgebraFst G₁ G₂ X.toSubalgebra).2⟩,
     ⟨(sumLieSubalgebraSnd G₁ G₂ X.toSubalgebra).1,
        (sumLieSubalgebraSnd G₁ G₂ X.toSubalgebra).2⟩)
  invFun p :=
    ⟨Matrix.fromBlocks p.1.val 0 0 p.2.val,
      (G₁.mem_sum_lieSubalgebra_iff G₂ _).2 ⟨p.1.val, p.1.property, p.2.val, p.2.property, rfl⟩⟩
  left_inv X := by
    apply LieAlgebra.ext
    obtain ⟨X₁, _, X₂, _, hEq⟩ := (G₁.mem_sum_lieSubalgebra_iff G₂ X.val).1 X.property
    simp [sumLieSubalgebraFst, sumLieSubalgebraSnd, hEq]
  right_inv p := by
    apply Prod.ext <;> apply LieAlgebra.ext <;> simp [sumLieSubalgebraFst, sumLieSubalgebraSnd]
  map_add' _ _ := Prod.ext (LieAlgebra.ext rfl) (LieAlgebra.ext rfl)
  map_smul' _ _ := Prod.ext (LieAlgebra.ext rfl) (LieAlgebra.ext rfl)
  map_lie' {X Y} := by
    obtain ⟨X₁, _, X₂, _, hXEq⟩ := (G₁.mem_sum_lieSubalgebra_iff G₂ X.val).1 X.property
    obtain ⟨Y₁, _, Y₂, _, hYEq⟩ := (G₁.mem_sum_lieSubalgebra_iff G₂ Y.val).1 Y.property
    apply Prod.ext <;> apply LieAlgebra.ext
    · ext i j
      simp [sumLieSubalgebraFst, LieAlgebra.val_lie, hXEq, hYEq, Matrix.fromBlocks_multiply,
        Matrix.toBlocks₁₁]
      rfl
    · ext i j
      simp [sumLieSubalgebraSnd, LieAlgebra.val_lie, hXEq, hYEq, Matrix.fromBlocks_multiply,
        Matrix.toBlocks₂₂]
      rfl

@[simp]
theorem sumLieEquiv_symm_val (G₁ : StructureGroup n) (G₂ : StructureGroup m)
    (p : G₁.LieAlgebra × G₂.LieAlgebra) :
    ((G₁.sumLieEquiv G₂).symm p).val = Matrix.fromBlocks p.1.val 0 0 p.2.val :=
  (rfl)

/-- The inner product on `(G₁.sum G₂).LieAlgebra` is the orthogonal direct sum of the inner
products on `G₁.LieAlgebra` and `G₂.LieAlgebra`. -/
@[simp]
theorem sum_inner_eq (G₁ : StructureGroup n) (G₂ : StructureGroup m)
    (X Y : (G₁.sum G₂).LieAlgebra) :
    ⟪X, Y⟫_ℝ =
      ⟪(G₁.sumLieEquiv G₂ X).1, (G₁.sumLieEquiv G₂ Y).1⟫_ℝ +
        ⟪(G₁.sumLieEquiv G₂ X).2, (G₁.sumLieEquiv G₂ Y).2⟫_ℝ := by
  rw [LieAlgebra.inner_eq_bilinForm, LieAlgebra.inner_eq_bilinForm, LieAlgebra.inner_eq_bilinForm]
  rfl

theorem sum_norm_sq (G₁ : StructureGroup n) (G₂ : StructureGroup m)
    (X : (G₁.sum G₂).LieAlgebra) :
    ‖X‖ ^ 2 = ‖(G₁.sumLieEquiv G₂ X).1‖ ^ 2 + ‖(G₁.sumLieEquiv G₂ X).2‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    sum_inner_eq]

/-- The block-diagonal product of structure groups on `Fin N₁` and `Fin N₂`, landing on
`Fin (N₁ + N₂)` via `finSumFinEquiv`. -/
def blockProd {N₁ N₂ : ℕ} (G₁ : StructureGroup (Fin N₁)) (G₂ : StructureGroup (Fin N₂)) :
    StructureGroup (Fin (N₁ + N₂)) :=
  (G₁.sum G₂).reindex finSumFinEquiv

theorem mem_blockProd_subgroup_iff {N₁ N₂ : ℕ}
    (G₁ : StructureGroup (Fin N₁)) (G₂ : StructureGroup (Fin N₂))
    (U : Matrix.unitaryGroup (Fin (N₁ + N₂)) ℂ) :
    U ∈ (G₁.blockProd G₂).subgroup ↔
      ∃ u₁ ∈ G₁.subgroup, ∃ u₂ ∈ G₂.subgroup,
        unitaryGroupReindexEquiv finSumFinEquiv (Matrix.UnitaryGroup.sum (u₁, u₂)) = U := by
  rw [blockProd, mem_reindex_subgroup_iff, mem_sum_subgroup_iff]
  constructor
  · rintro ⟨u₁, hu₁, u₂, hu₂, hEq⟩
    refine ⟨u₁, hu₁, u₂, hu₂, ?_⟩
    have := congrArg (unitaryGroupReindexEquiv finSumFinEquiv) hEq
    simpa using this
  · rintro ⟨u₁, hu₁, u₂, hu₂, rfl⟩
    exact ⟨u₁, hu₁, u₂, hu₂, by simp⟩

/-- The canonical Lie-algebra isomorphism `(G₁.blockProd G₂).LieAlgebra ≃ₗ⁅ℝ⁆
G₁.LieAlgebra × G₂.LieAlgebra`. -/
def blockProdLieEquiv {N₁ N₂ : ℕ}
    (G₁ : StructureGroup (Fin N₁)) (G₂ : StructureGroup (Fin N₂)) :
    (G₁.blockProd G₂).LieAlgebra ≃ₗ⁅ℝ⁆ G₁.LieAlgebra × G₂.LieAlgebra :=
  let e : ((G₁.sum G₂).reindex finSumFinEquiv).LieAlgebra ≃ₗ⁅ℝ⁆ G₁.LieAlgebra × G₂.LieAlgebra :=
    { __ := ((G₁.sum G₂).reindexLieEquiv finSumFinEquiv).symm.toLinearEquiv.trans
        (G₁.sumLieEquiv G₂).toLinearEquiv
      map_lie' := fun {X Y} ↦ by
        have hre : ((G₁.sum G₂).reindexLieEquiv finSumFinEquiv).symm ⁅X, Y⁆ =
            ⁅((G₁.sum G₂).reindexLieEquiv finSumFinEquiv).symm X,
              ((G₁.sum G₂).reindexLieEquiv finSumFinEquiv).symm Y⁆ := by
          apply ((G₁.sum G₂).reindexLieEquiv finSumFinEquiv).injective
          rw [reindexLieEquiv_lie]
          simp
        change G₁.sumLieEquiv G₂
          (((G₁.sum G₂).reindexLieEquiv finSumFinEquiv).symm ⁅X, Y⁆) = _
        rw [hre, (G₁.sumLieEquiv G₂).map_lie]
        rfl }
  e

/-- The inner product on `(G₁.blockProd G₂).LieAlgebra` is the orthogonal direct sum of the inner
products on `G₁.LieAlgebra` and `G₂.LieAlgebra`. -/
theorem blockProd_inner_eq {N₁ N₂ : ℕ}
    (G₁ : StructureGroup (Fin N₁)) (G₂ : StructureGroup (Fin N₂))
    (X Y : (G₁.blockProd G₂).LieAlgebra) :
    ⟪X, Y⟫_ℝ =
      ⟪(G₁.blockProdLieEquiv G₂ X).1, (G₁.blockProdLieEquiv G₂ Y).1⟫_ℝ +
        ⟪(G₁.blockProdLieEquiv G₂ X).2, (G₁.blockProdLieEquiv G₂ Y).2⟫_ℝ := by
  have h1 : ⟪X, Y⟫_ℝ =
      ⟪((G₁.sum G₂).reindexLieEquiv finSumFinEquiv).symm X,
        ((G₁.sum G₂).reindexLieEquiv finSumFinEquiv).symm Y⟫_ℝ :=
    (((G₁.sum G₂).reindexLieEquiv finSumFinEquiv).symm.inner_map_map X Y).symm
  rw [h1, sum_inner_eq]
  rfl

theorem blockProd_norm_sq {N₁ N₂ : ℕ}
    (G₁ : StructureGroup (Fin N₁)) (G₂ : StructureGroup (Fin N₂))
    (X : (G₁.blockProd G₂).LieAlgebra) :
    ‖X‖ ^ 2 = ‖(G₁.blockProdLieEquiv G₂ X).1‖ ^ 2 + ‖(G₁.blockProdLieEquiv G₂ X).2‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    blockProd_inner_eq]

end StructureGroup

end BlockProduct

end TauCeti.YangMills
