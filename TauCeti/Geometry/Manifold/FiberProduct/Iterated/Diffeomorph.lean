/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Iterated.Basic

/-!
# Regrouping diffeomorphisms and submersive projections for iterated fibre products

For a `C^n` submersion `π : Y → M` (`1 ≤ n`) between boundaryless finite-dimensional real
manifolds, grouping factors in any order yields canonical `C^n` diffeomorphisms (`One`, `Two`,
`SuccRight`, `SuccLeft`, `Add`, `Perm`, `Id`), and every factor projection
`IteratedFiberProduct.proj i` is a `C^n` submersion (`isSubmersion_proj_iteratedFiberProduct`).
-/

public section

noncomputable section

open Function Module
open scoped Manifold ContDiff

namespace TauCeti

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y] [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} [IsManifold IY n Y] [IsManifold IM n M] [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM] {π : Y → M}

/-- The 1-fold iterated fibre product `IteratedFiberProduct π 1` is `C^n` diffeomorphic to `Y`. -/
def iteratedFiberProductOneDiffeomorph (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π) :
    letI := iteratedFiberProductChartedSpace 1 hn hπ
    IteratedFiberProduct π 1 ≃ₘ^n⟮𝓘(ℝ, Fin (iteratedFiberProductDim EY EM 1) → ℝ), IY⟯ Y := by
  let := iteratedFiberProductChartedSpace 1 hn hπ
  refine { toFun := IteratedFiberProduct.proj 0, invFun := fun x ↦ .constDiagonal x 1
           left_inv := fun y ↦ IteratedFiberProduct.ext fun i ↦ by
             rw [IteratedFiberProduct.val_apply, IteratedFiberProduct.proj_constDiagonal,
               ← IteratedFiberProduct.val_apply]
             exact congrArg y.1 (Subsingleton.elim 0 i)
           right_inv := fun x ↦ IteratedFiberProduct.proj_constDiagonal x 1 0
           contMDiff_toFun := contMDiff_proj_iteratedFiberProduct 1 hn hπ le_rfl 0
           contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 fun _ ↦ by
             simp only [Equiv.coe_fn_symm_mk, IteratedFiberProduct.proj_constDiagonal]
             rw [← Function.id_def]; exact contMDiff_id }
@[simp] theorem iteratedFiberProductOneDiffeomorph_apply (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (y : IteratedFiberProduct π 1) :
    iteratedFiberProductOneDiffeomorph hn hπ y = IteratedFiberProduct.proj 0 y := (rfl)
@[simp] theorem iteratedFiberProductOneDiffeomorph_symm_apply (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (x : Y) :
    letI := iteratedFiberProductChartedSpace 1 hn hπ
    (iteratedFiberProductOneDiffeomorph hn hπ).symm x = .constDiagonal x 1 := (rfl)

/-- The 2-fold iterated fibre product `IteratedFiberProduct π 2` is `C^n` diffeomorphic to
`{p : Y × Y // π p.1 = π p.2}`. -/
def iteratedFiberProductTwoDiffeomorph (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π) :
    letI := iteratedFiberProductChartedSpace 2 hn hπ
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun p _ ↦ hπ.transverse_left (ne_of_gt (zero_lt_one.trans_le hn)) π p)
    IteratedFiberProduct π 2 ≃ₘ^n⟮𝓘(ℝ, Fin (iteratedFiberProductDim EY EM 2) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ EY + finrank ℝ EY - finrank ℝ EM) → ℝ)⟯
      {p : Y × Y // π p.1 = π p.2} := by
  let := iteratedFiberProductChartedSpace 2 hn hπ
  let htrans := fun (p : Y × Y) (_ : π p.1 = π p.2) ↦
    hπ.transverse_left (IY := IY) (ne_of_gt (zero_lt_one.trans_le hn)) π p
  let := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff htrans
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct hn hπ.contMDiff hπ.contMDiff htrans
  refine {
    toFun := fun y ↦
      ⟨(IteratedFiberProduct.proj 0 y, IteratedFiberProduct.proj 1 y), y.apply_proj_eq 0 1⟩
    invFun := fun p ↦ ⟨Fin.cons (α := fun _ ↦ Y) p.1.1 (fun _ ↦ p.1.2), fun i j ↦ by
      refine Fin.cases ?_ (fun _ ↦ ?_) i <;> refine Fin.cases ?_ (fun _ ↦ ?_) j <;>
        [rfl; exact p.2; exact p.2.symm; rfl]⟩
    left_inv := fun y ↦ IteratedFiberProduct.ext <| Fin.cases
      (by simp [← IteratedFiberProduct.val_apply])
      (fun j ↦ by
        rw [show j.succ = 1 from congrArg Fin.succ (Subsingleton.elim j 0)]
        simp [← IteratedFiberProduct.val_apply])
    right_inv := fun p ↦ Subtype.ext <| Prod.ext
      ((IteratedFiberProduct.proj_mk _ _ 0).trans
        (Fin.cons_zero (α := fun _ ↦ Y) p.1.1 (fun _ ↦ p.1.2)))
      ((IteratedFiberProduct.proj_mk _ _ 1).trans
        (Fin.cons_succ (α := fun _ ↦ Y) p.1.1 (fun _ ↦ p.1.2) 0))
    contMDiff_toFun := hemb.contMDiff_iff_comp.2 <|
      (contMDiff_proj_iteratedFiberProduct 2 hn hπ le_rfl 0).prodMk
        (contMDiff_proj_iteratedFiberProduct 2 hn hπ le_rfl 1)
    contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 <| Fin.cases
      (by simpa only [Equiv.coe_fn_symm_mk, IteratedFiberProduct.proj_mk,
        Fin.cons_zero (α := fun _ ↦ Y)] using hemb.contMDiff.fst)
      (fun _ ↦ by simpa only [Equiv.coe_fn_symm_mk, IteratedFiberProduct.proj_mk,
        Fin.cons_succ (α := fun _ ↦ Y)] using hemb.contMDiff.snd) }
@[simp] theorem iteratedFiberProductTwoDiffeomorph_apply (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (y : IteratedFiberProduct π 2) :
    iteratedFiberProductTwoDiffeomorph hn hπ y =
      ⟨(IteratedFiberProduct.proj 0 y, IteratedFiberProduct.proj 1 y),
        y.apply_proj_eq 0 1⟩ := (rfl)
@[simp] theorem iteratedFiberProductTwoDiffeomorph_symm_apply (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (p : {p : Y × Y // π p.1 = π p.2}) (i : Fin 2) :
    letI := iteratedFiberProductChartedSpace 2 hn hπ
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun q _ ↦ hπ.transverse_left (ne_of_gt (zero_lt_one.trans_le hn)) π q)
    IteratedFiberProduct.proj i ((iteratedFiberProductTwoDiffeomorph hn hπ).symm p) =
      Fin.cons (α := fun _ ↦ Y) p.1.1 (fun _ ↦ p.1.2) i :=
  IteratedFiberProduct.proj_mk _ _ i

/-- Right-grouped iteration: `IteratedFiberProduct π (k + 1)` (`k ≥ 1`) is `C^n` diffeomorphic to
`{p : IteratedFiberProduct π k × Y // baseProj p.1 = π p.2}`. -/
def iteratedFiberProductSuccRightDiffeomorph (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    haveI := isManifold_iteratedFiberProduct k hn hπ
    letI := iteratedFiberProductChartedSpace (k + 1) hn hπ
    letI := transverseFiberProductChartedSpace hn
      (isSubmersion_baseProj_iteratedFiberProduct k hn hπ).contMDiff hπ.contMDiff
      (fun p _ ↦ (isSubmersion_baseProj_iteratedFiberProduct k hn hπ).transverse_left
        (ne_of_gt (zero_lt_one.trans_le hn)) π p)
    IteratedFiberProduct π (k + 1) ≃ₘ^n⟮𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (k + 1)) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ (Fin (iteratedFiberProductDim EY EM k) → ℝ) +
        finrank ℝ EY - finrank ℝ EM) → ℝ)⟯
      {p : IteratedFiberProduct π k × Y // IteratedFiberProduct.baseProj p.1 = π p.2} := by
  let := iteratedFiberProductChartedSpace k hn hπ; have := isManifold_iteratedFiberProduct k hn hπ
  let := iteratedFiberProductChartedSpace (k + 1) hn hπ
  let hsub := isSubmersion_baseProj_iteratedFiberProduct k hn hπ
  let htrans := fun (p : IteratedFiberProduct π k × Y)
      (_ : IteratedFiberProduct.baseProj p.1 = π p.2) ↦
    hsub.transverse_left (IY := IY) (ne_of_gt (zero_lt_one.trans_le hn)) π p
  let := transverseFiberProductChartedSpace hn hsub.contMDiff hπ.contMDiff htrans
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct hn hsub.contMDiff hπ.contMDiff htrans
  refine {
    toFun := fun y ↦
      ⟨(y.precomp Fin.castSucc, IteratedFiberProduct.proj (Fin.last k) y),
        (y.baseProj_precomp Fin.castSucc).trans (y.proj_comp_eq_baseProj (Fin.last k)).symm⟩
    invFun := fun p ↦ ⟨Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2, by
      have hall : ∀ i : Fin (k + 1), π (Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 i) =
          IteratedFiberProduct.baseProj p.1.1 := Fin.lastCases
        (by rw [Fin.snoc_last (α := fun _ ↦ Y)]; exact p.2.symm)
        (fun j ↦ by
          rw [Fin.snoc_castSucc (α := fun _ ↦ Y), IteratedFiberProduct.val_apply]
          exact p.1.1.proj_comp_eq_baseProj j)
      exact fun i j ↦ (hall i).trans (hall j).symm⟩
    left_inv := fun y ↦ IteratedFiberProduct.ext <| Fin.lastCases
      (by simp [Fin.snoc_last (α := fun _ ↦ Y)])
      (fun _ ↦ by simp [Fin.snoc_castSucc (α := fun _ ↦ Y)])
    right_inv := fun p ↦ Subtype.ext <| Prod.ext
      (IteratedFiberProduct.ext fun _ ↦ by simp [Fin.snoc_castSucc (α := fun _ ↦ Y)])
      ((IteratedFiberProduct.proj_mk _ _ (Fin.last k)).trans
        (Fin.snoc_last (α := fun _ ↦ Y) p.1.2 p.1.1.1))
    contMDiff_toFun := hemb.contMDiff_iff_comp.2 <|
      (IteratedFiberProduct.contMDiff_precomp hn hπ le_rfl Fin.castSucc).prodMk
        (contMDiff_proj_iteratedFiberProduct (k + 1) hn hπ le_rfl (Fin.last k))
    contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 <| Fin.lastCases
      (by simpa only [Equiv.coe_fn_symm_mk, IteratedFiberProduct.proj_mk,
        Fin.snoc_last (α := fun _ ↦ Y)] using hemb.contMDiff.snd)
      (fun j ↦ by simpa only [Equiv.coe_fn_symm_mk, IteratedFiberProduct.proj_mk,
        Fin.snoc_castSucc (α := fun _ ↦ Y), IteratedFiberProduct.val_apply, Function.comp_def]
        using (contMDiff_proj_iteratedFiberProduct k hn hπ le_rfl j).comp hemb.contMDiff.fst) }
@[simp] theorem iteratedFiberProductSuccRightDiffeomorph_apply (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (y : IteratedFiberProduct π (k + 1)) :
    iteratedFiberProductSuccRightDiffeomorph k hn hπ y =
      ⟨(y.precomp Fin.castSucc, IteratedFiberProduct.proj (Fin.last k) y),
        (y.baseProj_precomp Fin.castSucc).trans (y.proj_comp_eq_baseProj (Fin.last k)).symm⟩ :=
  (rfl)
@[simp] theorem iteratedFiberProductSuccRightDiffeomorph_symm_apply (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π)
    (p : {p : IteratedFiberProduct π k × Y // IteratedFiberProduct.baseProj p.1 = π p.2})
    (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    haveI := isManifold_iteratedFiberProduct k hn hπ
    letI := iteratedFiberProductChartedSpace (k + 1) hn hπ
    letI := transverseFiberProductChartedSpace hn
      (isSubmersion_baseProj_iteratedFiberProduct k hn hπ).contMDiff hπ.contMDiff
      (fun q _ ↦ (isSubmersion_baseProj_iteratedFiberProduct k hn hπ).transverse_left
        (ne_of_gt (zero_lt_one.trans_le hn)) π q)
    IteratedFiberProduct.proj i ((iteratedFiberProductSuccRightDiffeomorph k hn hπ).symm p) =
      Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 i :=
  IteratedFiberProduct.proj_mk _ _ i

/-- Left-grouped iteration: `IteratedFiberProduct π (k + 1)` (`k ≥ 1`) is `C^n` diffeomorphic to
`{p : Y × IteratedFiberProduct π k // π p.1 = baseProj p.2}`. -/
def iteratedFiberProductSuccLeftDiffeomorph (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    haveI := isManifold_iteratedFiberProduct k hn hπ
    letI := iteratedFiberProductChartedSpace (k + 1) hn hπ
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff
      (isSubmersion_baseProj_iteratedFiberProduct k hn hπ).contMDiff
      (fun p _ ↦ hπ.transverse_left (ne_of_gt (zero_lt_one.trans_le hn))
        IteratedFiberProduct.baseProj p)
    IteratedFiberProduct π (k + 1) ≃ₘ^n⟮𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (k + 1)) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ EY +
        finrank ℝ (Fin (iteratedFiberProductDim EY EM k) → ℝ) - finrank ℝ EM) → ℝ)⟯
      {p : Y × IteratedFiberProduct π k // π p.1 = IteratedFiberProduct.baseProj p.2} := by
  let := iteratedFiberProductChartedSpace k hn hπ; have := isManifold_iteratedFiberProduct k hn hπ
  let := iteratedFiberProductChartedSpace (k + 1) hn hπ
  let hsub := isSubmersion_baseProj_iteratedFiberProduct k hn hπ
  let htrans := fun (p : Y × IteratedFiberProduct π k)
      (_ : π p.1 = IteratedFiberProduct.baseProj p.2) ↦
    hπ.transverse_left (IY := 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ))
      (ne_of_gt (zero_lt_one.trans_le hn)) IteratedFiberProduct.baseProj p
  let := transverseFiberProductChartedSpace hn hπ.contMDiff hsub.contMDiff htrans
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct hn hπ.contMDiff hsub.contMDiff htrans
  refine {
    toFun := fun y ↦
      ⟨(IteratedFiberProduct.proj 0 y, y.precomp Fin.succ),
        (y.proj_comp_eq_baseProj 0).trans (y.baseProj_precomp Fin.succ).symm⟩
    invFun := fun p ↦ ⟨Fin.cons (α := fun _ ↦ Y) p.1.1 p.1.2.1, by
      have hall : ∀ i : Fin (k + 1), π (Fin.cons (α := fun _ ↦ Y) p.1.1 p.1.2.1 i) =
          IteratedFiberProduct.baseProj p.1.2 := Fin.cases p.2 fun j ↦ by
        rw [Fin.cons_succ (α := fun _ ↦ Y), IteratedFiberProduct.val_apply]
        exact p.1.2.proj_comp_eq_baseProj j
      exact fun i j ↦ (hall i).trans (hall j).symm⟩
    left_inv := fun y ↦ IteratedFiberProduct.ext <| Fin.cases (by simp)
      (fun _ ↦ by simp [Fin.cons_succ (α := fun _ ↦ Y)])
    right_inv := fun p ↦ Subtype.ext <| Prod.ext
      ((IteratedFiberProduct.proj_mk _ _ 0).trans (Fin.cons_zero (α := fun _ ↦ Y) p.1.1 p.1.2.1))
      (IteratedFiberProduct.ext fun _ ↦ by simp [Fin.cons_succ (α := fun _ ↦ Y)])
    contMDiff_toFun := hemb.contMDiff_iff_comp.2 <|
      (contMDiff_proj_iteratedFiberProduct (k + 1) hn hπ le_rfl 0).prodMk
        (IteratedFiberProduct.contMDiff_precomp hn hπ le_rfl Fin.succ)
    contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 <| Fin.cases
      (by simpa only [Equiv.coe_fn_symm_mk, IteratedFiberProduct.proj_mk,
        Fin.cons_zero (α := fun _ ↦ Y)] using hemb.contMDiff.fst)
      (fun j ↦ by simpa only [Equiv.coe_fn_symm_mk, IteratedFiberProduct.proj_mk,
        Fin.cons_succ (α := fun _ ↦ Y), IteratedFiberProduct.val_apply, Function.comp_def]
        using (contMDiff_proj_iteratedFiberProduct k hn hπ le_rfl j).comp hemb.contMDiff.snd) }
@[simp] theorem iteratedFiberProductSuccLeftDiffeomorph_apply (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (y : IteratedFiberProduct π (k + 1)) :
    iteratedFiberProductSuccLeftDiffeomorph k hn hπ y =
      ⟨(IteratedFiberProduct.proj 0 y, y.precomp Fin.succ),
        (y.proj_comp_eq_baseProj 0).trans (y.baseProj_precomp Fin.succ).symm⟩ := (rfl)
@[simp] theorem iteratedFiberProductSuccLeftDiffeomorph_symm_apply (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π)
    (p : {p : Y × IteratedFiberProduct π k // π p.1 = IteratedFiberProduct.baseProj p.2})
    (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    haveI := isManifold_iteratedFiberProduct k hn hπ
    letI := iteratedFiberProductChartedSpace (k + 1) hn hπ
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff
      (isSubmersion_baseProj_iteratedFiberProduct k hn hπ).contMDiff
      (fun q _ ↦ hπ.transverse_left (ne_of_gt (zero_lt_one.trans_le hn))
        IteratedFiberProduct.baseProj q)
    IteratedFiberProduct.proj i ((iteratedFiberProductSuccLeftDiffeomorph k hn hπ).symm p) =
      Fin.cons (α := fun _ ↦ Y) p.1.1 p.1.2.1 i :=
  IteratedFiberProduct.proj_mk _ _ i

/-- General associative regrouping: `IteratedFiberProduct π (a + b)` (`a, b ≥ 1`) is `C^n`
diffeomorphic to the transverse fibre product of `IteratedFiberProduct π a` and
`IteratedFiberProduct π b` over `M`. -/
def iteratedFiberProductAddDiffeomorph (a b : ℕ) [NeZero a] [NeZero b] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    letI := iteratedFiberProductChartedSpace a hn hπ
    haveI := isManifold_iteratedFiberProduct a hn hπ
    letI := iteratedFiberProductChartedSpace b hn hπ
    haveI := isManifold_iteratedFiberProduct b hn hπ
    letI := iteratedFiberProductChartedSpace (a + b) hn hπ
    letI := transverseFiberProductChartedSpace hn
      (isSubmersion_baseProj_iteratedFiberProduct a hn hπ).contMDiff
      (isSubmersion_baseProj_iteratedFiberProduct b hn hπ).contMDiff
      (fun p _ ↦ (isSubmersion_baseProj_iteratedFiberProduct a hn hπ).transverse_left
        (ne_of_gt (zero_lt_one.trans_le hn)) IteratedFiberProduct.baseProj p)
    IteratedFiberProduct π (a + b) ≃ₘ^n⟮𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (a + b)) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ (Fin (iteratedFiberProductDim EY EM a) → ℝ) +
        finrank ℝ (Fin (iteratedFiberProductDim EY EM b) → ℝ) - finrank ℝ EM) → ℝ)⟯
      {p : IteratedFiberProduct π a × IteratedFiberProduct π b //
        IteratedFiberProduct.baseProj p.1 = IteratedFiberProduct.baseProj p.2} := by
  have : NeZero (a + b) := ⟨by have := NeZero.ne a; omega⟩
  let := iteratedFiberProductChartedSpace a hn hπ; have := isManifold_iteratedFiberProduct a hn hπ
  let := iteratedFiberProductChartedSpace b hn hπ; have := isManifold_iteratedFiberProduct b hn hπ
  let := iteratedFiberProductChartedSpace (a + b) hn hπ
  let hsuba := isSubmersion_baseProj_iteratedFiberProduct a hn hπ
  let hsubb := isSubmersion_baseProj_iteratedFiberProduct b hn hπ
  let htrans := fun (p : IteratedFiberProduct π a × IteratedFiberProduct π b)
      (_ : IteratedFiberProduct.baseProj p.1 = IteratedFiberProduct.baseProj p.2) ↦
    hsuba.transverse_left (IY := 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM b) → ℝ))
      (ne_of_gt (zero_lt_one.trans_le hn)) IteratedFiberProduct.baseProj p
  let := transverseFiberProductChartedSpace hn hsuba.contMDiff hsubb.contMDiff htrans
  have hemb :=
    isSmoothEmbedding_coe_transverseFiberProduct hn hsuba.contMDiff hsubb.contMDiff htrans
  refine {
    toFun := fun y ↦
      ⟨(y.precomp (Fin.castAdd b), y.precomp (Fin.natAdd a)),
        (y.baseProj_precomp (Fin.castAdd b)).trans (y.baseProj_precomp (Fin.natAdd a)).symm⟩
    invFun := fun p ↦ ⟨Fin.append p.1.1.1 p.1.2.1, by
      have hall : ∀ i : Fin (a + b),
          π (Fin.append p.1.1.1 p.1.2.1 i) = IteratedFiberProduct.baseProj p.1.1 :=
        Fin.addCases
          (fun i₁ ↦ by
            rw [Fin.append_left, IteratedFiberProduct.val_apply]
            exact p.1.1.proj_comp_eq_baseProj i₁)
          (fun i₂ ↦ by
            rw [Fin.append_right, IteratedFiberProduct.val_apply]
            exact (p.1.2.proj_comp_eq_baseProj i₂).trans p.2.symm)
      exact fun i j ↦ (hall i).trans (hall j).symm⟩
    left_inv := fun y ↦ IteratedFiberProduct.ext <| Fin.addCases
      (fun _ ↦ by simp [Fin.append_left]) (fun _ ↦ by simp [Fin.append_right])
    right_inv := fun p ↦ Subtype.ext <| Prod.ext
      (IteratedFiberProduct.ext fun _ ↦ by simp [Fin.append_left])
      (IteratedFiberProduct.ext fun _ ↦ by simp [Fin.append_right])
    contMDiff_toFun := hemb.contMDiff_iff_comp.2 <|
      (IteratedFiberProduct.contMDiff_precomp hn hπ le_rfl (Fin.castAdd b)).prodMk
        (IteratedFiberProduct.contMDiff_precomp hn hπ le_rfl (Fin.natAdd a))
    contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 <| Fin.addCases
      (fun i₁ ↦ by simpa only [Equiv.coe_fn_symm_mk, IteratedFiberProduct.proj_mk,
        Fin.append_left, IteratedFiberProduct.val_apply, Function.comp_def] using
        (contMDiff_proj_iteratedFiberProduct a hn hπ le_rfl i₁).comp hemb.contMDiff.fst)
      (fun i₂ ↦ by simpa only [Equiv.coe_fn_symm_mk, IteratedFiberProduct.proj_mk,
        Fin.append_right, IteratedFiberProduct.val_apply, Function.comp_def] using
        (contMDiff_proj_iteratedFiberProduct b hn hπ le_rfl i₂).comp hemb.contMDiff.snd) }
@[simp] theorem iteratedFiberProductAddDiffeomorph_apply (a b : ℕ) [NeZero a] [NeZero b]
    (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π) (y : IteratedFiberProduct π (a + b)) :
    iteratedFiberProductAddDiffeomorph a b hn hπ y =
      ⟨(y.precomp (Fin.castAdd b), y.precomp (Fin.natAdd a)),
        (y.baseProj_precomp (Fin.castAdd b)).trans
          (y.baseProj_precomp (Fin.natAdd a)).symm⟩ := (rfl)
@[simp] theorem iteratedFiberProductAddDiffeomorph_symm_apply (a b : ℕ) [NeZero a] [NeZero b]
    (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    (p : {p : IteratedFiberProduct π a × IteratedFiberProduct π b //
      IteratedFiberProduct.baseProj p.1 = IteratedFiberProduct.baseProj p.2})
    (i : Fin (a + b)) :
    letI := iteratedFiberProductChartedSpace a hn hπ
    haveI := isManifold_iteratedFiberProduct a hn hπ
    letI := iteratedFiberProductChartedSpace b hn hπ
    haveI := isManifold_iteratedFiberProduct b hn hπ
    letI := iteratedFiberProductChartedSpace (a + b) hn hπ
    letI := transverseFiberProductChartedSpace hn
      (isSubmersion_baseProj_iteratedFiberProduct a hn hπ).contMDiff
      (isSubmersion_baseProj_iteratedFiberProduct b hn hπ).contMDiff
      (fun q _ ↦ (isSubmersion_baseProj_iteratedFiberProduct a hn hπ).transverse_left
        (ne_of_gt (zero_lt_one.trans_le hn)) IteratedFiberProduct.baseProj q)
    IteratedFiberProduct.proj i ((iteratedFiberProductAddDiffeomorph a b hn hπ).symm p) =
      Fin.append p.1.1.1 p.1.2.1 i :=
  IteratedFiberProduct.proj_mk _ _ i

/-- Any coordinate permutation `σ : Equiv.Perm (Fin k)` induces a `C^n` diffeomorphism of
`IteratedFiberProduct π k`. -/
def iteratedFiberProductPermDiffeomorph (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (σ : Equiv.Perm (Fin k)) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    IteratedFiberProduct π k ≃ₘ^n⟮𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ),
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ)⟯ IteratedFiberProduct π k := by
  let := iteratedFiberProductChartedSpace k hn hπ
  exact { toFun := .precomp σ, invFun := .precomp σ.symm
          left_inv := fun _ ↦ IteratedFiberProduct.ext fun _ ↦ by simp
          right_inv := fun _ ↦ IteratedFiberProduct.ext fun _ ↦ by simp
          contMDiff_toFun := IteratedFiberProduct.contMDiff_precomp hn hπ le_rfl σ
          contMDiff_invFun := IteratedFiberProduct.contMDiff_precomp hn hπ le_rfl σ.symm }
@[simp] theorem iteratedFiberProductPermDiffeomorph_apply (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (σ : Equiv.Perm (Fin k))
    (y : IteratedFiberProduct π k) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    iteratedFiberProductPermDiffeomorph k hn hπ σ y = y.precomp σ := (rfl)
@[simp] theorem iteratedFiberProductPermDiffeomorph_symm_apply (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (σ : Equiv.Perm (Fin k))
    (y : IteratedFiberProduct π k) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    (iteratedFiberProductPermDiffeomorph k hn hπ σ).symm y = y.precomp σ.symm := (rfl)

/-- For the identity cover `id : M → M`, every iterated fibre product `IteratedFiberProduct id k`
(`k ≥ 1`) is `C^n` diffeomorphic to `M`. -/
def iteratedFiberProductIdDiffeomorph (IM : ModelWithCorners ℝ EM HM) (M : Type*)
    [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM n M] [IM.Boundaryless]
    (k : ℕ) [NeZero k] (hn : 1 ≤ n) :
    letI := iteratedFiberProductChartedSpace k hn
      (Manifold.IsSubmersion.id (I := IM) (M := M) (n := n))
    IteratedFiberProduct (@id M) k ≃ₘ^n⟮𝓘(ℝ, Fin (iteratedFiberProductDim EM EM k) → ℝ),
      IM⟯ M := by
  let hid := Manifold.IsSubmersion.id (I := IM) (M := M) (n := n)
  let := iteratedFiberProductChartedSpace k hn hid
  refine { toFun := IteratedFiberProduct.proj 0
           invFun := fun x ↦ IteratedFiberProduct.constDiagonal (π := @id M) x k
           left_inv := fun y ↦ IteratedFiberProduct.ext fun i ↦ by
             rw [IteratedFiberProduct.val_apply, IteratedFiberProduct.proj_constDiagonal,
               IteratedFiberProduct.val_apply]
             exact y.apply_proj_eq 0 i
           right_inv := fun x ↦ IteratedFiberProduct.proj_constDiagonal x k 0
           contMDiff_toFun := contMDiff_proj_iteratedFiberProduct k hn hid le_rfl 0
           contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hid le_rfl).2 fun _ ↦ by
             simp only [Equiv.coe_fn_symm_mk, IteratedFiberProduct.proj_constDiagonal]
             rw [← Function.id_def]; exact contMDiff_id }
@[simp] theorem iteratedFiberProductIdDiffeomorph_apply (IM : ModelWithCorners ℝ EM HM) (M : Type*)
    [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM n M] [IM.Boundaryless]
    (k : ℕ) [NeZero k] (hn : 1 ≤ n) (y : IteratedFiberProduct (@id M) k) :
    iteratedFiberProductIdDiffeomorph IM M k hn y = IteratedFiberProduct.proj 0 y := (rfl)
@[simp] theorem iteratedFiberProductIdDiffeomorph_symm_apply (IM : ModelWithCorners ℝ EM HM)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM n M] [IM.Boundaryless]
    (k : ℕ) [NeZero k] (hn : 1 ≤ n) (x : M) :
    letI := iteratedFiberProductChartedSpace k hn
      (Manifold.IsSubmersion.id (I := IM) (M := M) (n := n))
    (iteratedFiberProductIdDiffeomorph IM M k hn).symm x =
      IteratedFiberProduct.constDiagonal (π := @id M) x k := (rfl)

/-- Every factor projection `IteratedFiberProduct.proj i` (`k ≥ 1`) is a `C^n` submersion. -/
theorem isSubmersion_proj_iteratedFiberProduct (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (i : Fin k) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    Manifold.IsSubmersion 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) IY n
      (IteratedFiberProduct.proj i : IteratedFiberProduct π k → Y) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  rcases k with _ | _ | m
  · exact False.elim (NeZero.ne 0 rfl)
  · let := iteratedFiberProductChartedSpace 1 hn hπ; have := isManifold_iteratedFiberProduct 1 hn hπ
    obtain rfl : i = 0 := Fin.eq_zero i
    exact (iteratedFiberProductOneDiffeomorph hn hπ).isSubmersion hn0
  · let := iteratedFiberProductChartedSpace (m + 1) hn hπ
    let := iteratedFiberProductChartedSpace (m + 2) hn hπ
    have := isManifold_iteratedFiberProduct (m + 1) hn hπ
    have := isManifold_iteratedFiberProduct (m + 2) hn hπ
    have hsubk := isSubmersion_baseProj_iteratedFiberProduct (m + 1) hn hπ
    let htrans := fun (p : IteratedFiberProduct π (m + 1) × Y)
        (_ : IteratedFiberProduct.baseProj p.1 = π p.2) ↦
      hsubk.transverse_left (IY := IY) hn0 π p
    let := transverseFiberProductChartedSpace hn hsubk.contMDiff hπ.contMDiff htrans
    have := isManifold_transverseFiberProduct hn hsubk.contMDiff hπ.contMDiff htrans
    have hsnd :=
      isSubmersion_snd_transverseFiberProduct hn hsubk.contMDiff hπ.contMDiff htrans hsubk
    have hlast : Manifold.IsSubmersion
        𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (m + 2)) → ℝ) IY n
        (IteratedFiberProduct.proj (Fin.last (m + 1)) : IteratedFiberProduct π (m + 2) → Y) :=
      hsnd.comp ((iteratedFiberProductSuccRightDiffeomorph (m + 1) hn hπ).isSubmersion hn0)
    let σ := Equiv.swap i (Fin.last (m + 1))
    have heq : (IteratedFiberProduct.proj i : IteratedFiberProduct π (m + 2) → Y) =
        IteratedFiberProduct.proj (Fin.last (m + 1)) ∘
          ⇑(iteratedFiberProductPermDiffeomorph (m + 2) hn hπ σ) := by ext y; simp [σ]
    exact heq ▸ hlast.comp ((iteratedFiberProductPermDiffeomorph (m + 2) hn hπ σ).isSubmersion hn0)

end TauCeti
