/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Iterated.Manifold

/-!
# Canonical comparisons and associativity of iterated fibre products

This file establishes the canonical `C^n` diffeomorphisms identifying the iterated fibre product
`IteratedFiberProduct π (k + 1)` with binary transverse fibre products:

* `TauCeti.iteratedFiberProductOneDiffeomorph`: `Y^[1] ≃ₘ^n Y`.
* `TauCeti.iteratedFiberProductTwoDiffeomorph`: `Y^[2] ≃ₘ^n Y ×_M Y`.
* `TauCeti.iteratedFiberProductStepDiffeomorph`: `Y^[k+2] ≃ₘ^n Y^[k+1] ×_M Y`.
* `TauCeti.iteratedFiberProductSplitDiffeomorph`: `Y^[(a+1)+(b+1)] ≃ₘ^n Y^[a+1] ×_M Y^[b+1]`
  (independence of the order of iteration).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013),
  Theorem 6.30 (transverse preimages).
* M. K. Murray, *Bundle gerbes*, J. London Math. Soc. (2) 54 (1996), 403–416, §3.
-/

public section

open Function Set Module Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} [IsManifold IY n Y] [IsManifold IM n M]
  [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]
  {π : Y → M} (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)

/-- Canonical `C^n` diffeomorphism `Y^[1] ≃ₘ^n Y`, given by the unique coordinate projection with
inverse the diagonal. -/
noncomputable def iteratedFiberProductOneDiffeomorph :
    letI := iteratedFiberProductChartedSpace hn hπ 0
    IteratedFiberProduct π 1 ≃ₘ^n⟮
      𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ), IY⟯ Y :=
  letI := iteratedFiberProductChartedSpace hn hπ 0
  { toFun := IteratedFiberProduct.proj π 0
    invFun := IteratedFiberProduct.diag π 1
    left_inv := fun y ↦ IteratedFiberProduct.ext π fun i ↦ by
      rw [IteratedFiberProduct.coe_diag, IteratedFiberProduct.proj_apply]
      exact congrArg y.1 (Subsingleton.elim 0 i)
    right_inv := IteratedFiberProduct.proj_diag π 0
    contMDiff_toFun := contMDiff_proj_iteratedFiberProduct hn hπ 0 0
    contMDiff_invFun := contMDiff_diag_iteratedFiberProduct hn hπ 0 }

/-- The comparison `Y^[1] ≃ₘ^n Y` evaluates at coordinate `0`. -/
@[simp]
theorem iteratedFiberProductOneDiffeomorph_apply (y : IteratedFiberProduct π 1) :
    iteratedFiberProductOneDiffeomorph hn hπ y = y.1 0 :=
  IteratedFiberProduct.proj_apply π 0 y

/-- The inverse comparison `Y ≃ₘ^n Y^[1]` is the diagonal. -/
@[simp]
theorem iteratedFiberProductOneDiffeomorph_symm_apply (y : Y) :
    letI := iteratedFiberProductChartedSpace hn hπ 0
    (iteratedFiberProductOneDiffeomorph hn hπ).symm y = IteratedFiberProduct.diag π 1 y :=
  (rfl)

/-- Canonical `C^n` diffeomorphism `Y^[2] ≃ₘ^n Y ×_M Y` comparing the 2-fold iterated fibre
product with the binary transverse fibre product `TauCeti.transverseFiberProductChartedSpace`. -/
noncomputable def iteratedFiberProductTwoDiffeomorph :
    letI := iteratedFiberProductChartedSpace hn hπ 1
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right (IX := IY) π hn hπ p)
    IteratedFiberProduct π 2 ≃ₘ^n⟮
      𝓘(ℝ, Fin ((1 + 1) * finrank ℝ EY - 1 * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ EY + finrank ℝ EY - finrank ℝ EM) → ℝ)⟯
      {p : Y × Y // π p.1 = π p.2} :=
  letI := iteratedFiberProductChartedSpace hn hπ 1
  let htrans := fun (p : Y × Y) (_ : π p.1 = π p.2) ↦
    transverse_of_isSubmersion_right (IX := IY) π hn hπ p
  letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff htrans
  have hP := isSmoothEmbedding_coe_transverseFiberProduct hn hπ.contMDiff hπ.contMDiff htrans
  { toFun := fun y ↦ ⟨(y.1 0, y.1 1), y.2 0 1⟩
    invFun := fun p ↦ ⟨![p.1.1, p.1.2], fun i j ↦ by fin_cases i <;> fin_cases j <;> simp [p.2]⟩
    left_inv := fun y ↦ IteratedFiberProduct.ext π fun i ↦ by fin_cases i <;> rfl
    right_inv := fun _ ↦ rfl
    contMDiff_toFun := hP.contMDiff_iff_comp.2 <| by
      have h01 := (contMDiff_proj_iteratedFiberProduct hn hπ 1 0).prodMk
        (contMDiff_proj_iteratedFiberProduct hn hπ 1 1)
      simp only [IteratedFiberProduct.proj_apply] at h01
      exact h01
    contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ 1).2 fun i ↦ by
      fin_cases i
      · exact hP.contMDiff.fst
      · exact hP.contMDiff.snd }

/-- The comparison `Y^[2] ≃ₘ^n Y ×_M Y` pairs coordinates `0` and `1`. -/
@[simp]
theorem iteratedFiberProductTwoDiffeomorph_apply (y : IteratedFiberProduct π 2) :
    iteratedFiberProductTwoDiffeomorph hn hπ y = ⟨(y.1 0, y.1 1), y.2 0 1⟩ :=
  (rfl)

/-- The inverse comparison `Y ×_M Y ≃ₘ^n Y^[2]` forms the 2-tuple `![p.1.1, p.1.2]`. -/
@[simp]
theorem iteratedFiberProductTwoDiffeomorph_symm_apply (p : {p : Y × Y // π p.1 = π p.2}) :
    letI := iteratedFiberProductChartedSpace hn hπ 1
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun q _ ↦ transverse_of_isSubmersion_right (IX := IY) π hn hπ q)
    ((iteratedFiberProductTwoDiffeomorph hn hπ).symm p).1 = ![p.1.1, p.1.2] :=
  (rfl)

/-- Canonical `C^n` diffeomorphism `Y^[k+2] ≃ₘ^n Y^[k+1] ×_M Y` identifying the `(k + 2)`-fold
iterated fibre product with one binary transverse fibre-product step over `M`. -/
noncomputable def iteratedFiberProductStepDiffeomorph (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    letI := iteratedFiberProductChartedSpace hn hπ k
    haveI := isManifold_iteratedFiberProduct hn hπ k
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj_iteratedFiberProduct hn hπ k) hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right
        (IX := 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ))
        (IteratedFiberProduct.baseProj π) hn hπ p)
    IteratedFiberProduct π (k + 2) ≃ₘ^n⟮
      𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ (Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) +
        finrank ℝ EY - finrank ℝ EM) → ℝ)⟯
      {p : IteratedFiberProduct π (k + 1) × Y // IteratedFiberProduct.baseProj π p.1 = π p.2} :=
  letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
  letI := iteratedFiberProductChartedSpace hn hπ k
  haveI := isManifold_iteratedFiberProduct hn hπ k
  let htrans := fun (p : IteratedFiberProduct π (k + 1) × Y) (_ : _) ↦
    transverse_of_isSubmersion_right
      (IX := 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ))
      (IteratedFiberProduct.baseProj π) hn hπ p
  letI := transverseFiberProductChartedSpace hn
    (contMDiff_baseProj_iteratedFiberProduct hn hπ k) hπ.contMDiff htrans
  have hP := isSmoothEmbedding_coe_transverseFiberProduct hn
    (contMDiff_baseProj_iteratedFiberProduct hn hπ k) hπ.contMDiff htrans
  { toFun := fun y ↦
      ⟨(IteratedFiberProduct.reindex π Fin.castSucc y, y.1 (Fin.last (k + 1))),
        (IteratedFiberProduct.baseProj_reindex π Fin.castSucc y).trans
          (IteratedFiberProduct.baseProj_eq π y (Fin.last (k + 1)))⟩
    invFun := fun p ↦ ⟨Fin.snoc p.1.1.1 p.1.2, fun i j ↦ by
      have hbase : ∀ m : Fin (k + 2),
          π (Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 m) =
            IteratedFiberProduct.baseProj π p.1.1 := fun m ↦
        Fin.lastCases (by rw [Fin.snoc_last]; exact p.2.symm)
          (fun j ↦ by
            rw [Fin.snoc_castSucc, IteratedFiberProduct.baseProj_eq_zero]; exact p.1.1.2 j 0) m
      rw [hbase i, hbase j]⟩
    left_inv := fun y ↦ IteratedFiberProduct.ext π fun i ↦ by
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
    right_inv := fun p ↦ Subtype.ext <| Prod.ext
      (IteratedFiberProduct.ext π fun j ↦ by simp) (by simp)
    contMDiff_toFun := hP.contMDiff_iff_comp.2 <|
      (contMDiff_reindex_iteratedFiberProduct hn hπ
        (Fin.castSucc : Fin (k + 1) → Fin (k + 2))).prodMk <| by
        have h := contMDiff_proj_iteratedFiberProduct hn hπ (k + 1) (Fin.last (k + 1))
        rw [IteratedFiberProduct.proj_eq_comp] at h; exact h
    contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ (k + 1)).2 fun i ↦ by
      change ContMDiff _ _ _ (fun p :
        {p : IteratedFiberProduct π (k + 1) × Y // IteratedFiberProduct.baseProj π p.1 = π p.2} ↦
        Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 i)
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp only [Fin.snoc_last]; exact hP.contMDiff.snd
      · simp only [Fin.snoc_castSucc]
        have h := (contMDiff_proj_iteratedFiberProduct hn hπ k j).comp hP.contMDiff.fst
        simp only [Function.comp_def, IteratedFiberProduct.proj_apply] at h; exact h }

/-- The step comparison splits off the last coordinate of a `(k + 2)`-tuple. -/
@[simp]
theorem iteratedFiberProductStepDiffeomorph_apply (k : ℕ) (y : IteratedFiberProduct π (k + 2)) :
    (iteratedFiberProductStepDiffeomorph hn hπ k y).1 =
      (IteratedFiberProduct.reindex π Fin.castSucc y, y.1 (Fin.last (k + 1))) :=
  (rfl)

/-- The inverse step comparison appends the last coordinate with `Fin.snoc`. -/
@[simp]
theorem iteratedFiberProductStepDiffeomorph_symm_apply (k : ℕ)
    (p : {p : IteratedFiberProduct π (k + 1) × Y // IteratedFiberProduct.baseProj π p.1 = π p.2}) :
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    letI := iteratedFiberProductChartedSpace hn hπ k
    haveI := isManifold_iteratedFiberProduct hn hπ k
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj_iteratedFiberProduct hn hπ k) hπ.contMDiff
      (fun q _ ↦ transverse_of_isSubmersion_right
        (IX := 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ))
        (IteratedFiberProduct.baseProj π) hn hπ q)
    ((iteratedFiberProductStepDiffeomorph hn hπ k).symm p).1 = Fin.snoc p.1.1.1 p.1.2 :=
  (rfl)

/-- **Independence of the order of iteration.** For all `a, b : ℕ`, the `((a + 1) + (b + 1))`-fold
iterated fibre product is canonically `C^n` diffeomorphic to the binary transverse fibre product
`Y^[a+1] ×_M Y^[b+1]` formed over the two base projections. -/
noncomputable def iteratedFiberProductSplitDiffeomorph (a b : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ ((a + 1) + b)
    letI := iteratedFiberProductChartedSpace hn hπ a
    letI := iteratedFiberProductChartedSpace hn hπ b
    haveI := isManifold_iteratedFiberProduct hn hπ a
    haveI := isManifold_iteratedFiberProduct hn hπ b
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj_iteratedFiberProduct hn hπ a)
      (contMDiff_baseProj_iteratedFiberProduct hn hπ b)
      (fun p _ ↦ transverse_of_isSubmersion_right
        (IX := 𝓘(ℝ, Fin ((a + 1) * finrank ℝ EY - a * finrank ℝ EM) → ℝ))
        (IteratedFiberProduct.baseProj π) hn
        (isSubmersion_baseProj_iteratedFiberProduct hn hπ b) p)
    IteratedFiberProduct π ((a + 1) + (b + 1)) ≃ₘ^n⟮
      𝓘(ℝ, Fin (((a + 1) + b + 1) * finrank ℝ EY - ((a + 1) + b) * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ (Fin ((a + 1) * finrank ℝ EY - a * finrank ℝ EM) → ℝ) +
        finrank ℝ (Fin ((b + 1) * finrank ℝ EY - b * finrank ℝ EM) → ℝ) - finrank ℝ EM) → ℝ)⟯
      {p : IteratedFiberProduct π (a + 1) × IteratedFiberProduct π (b + 1) //
        IteratedFiberProduct.baseProj π p.1 = IteratedFiberProduct.baseProj π p.2} :=
  letI := iteratedFiberProductChartedSpace hn hπ ((a + 1) + b)
  letI := iteratedFiberProductChartedSpace hn hπ a
  letI := iteratedFiberProductChartedSpace hn hπ b
  haveI := isManifold_iteratedFiberProduct hn hπ a
  haveI := isManifold_iteratedFiberProduct hn hπ b
  let htrans := fun (p : IteratedFiberProduct π (a + 1) × IteratedFiberProduct π (b + 1)) (_ : _) ↦
    transverse_of_isSubmersion_right
      (IX := 𝓘(ℝ, Fin ((a + 1) * finrank ℝ EY - a * finrank ℝ EM) → ℝ))
      (IteratedFiberProduct.baseProj π) hn (isSubmersion_baseProj_iteratedFiberProduct hn hπ b) p
  letI := transverseFiberProductChartedSpace hn
    (contMDiff_baseProj_iteratedFiberProduct hn hπ a)
    (contMDiff_baseProj_iteratedFiberProduct hn hπ b) htrans
  have hP := isSmoothEmbedding_coe_transverseFiberProduct hn
    (contMDiff_baseProj_iteratedFiberProduct hn hπ a)
    (contMDiff_baseProj_iteratedFiberProduct hn hπ b) htrans
  { toFun := fun y ↦
      ⟨(IteratedFiberProduct.reindex π (Fin.castAdd (b + 1)) y,
        IteratedFiberProduct.reindex π (Fin.natAdd (a + 1)) y), by simp⟩
    invFun := fun p ↦ ⟨Fin.addCases p.1.1.1 p.1.2.1, fun i j ↦ by
      have hbase : ∀ m : Fin ((a + 1) + (b + 1)),
          π (Fin.addCases (motive := fun _ ↦ Y) p.1.1.1 p.1.2.1 m) =
            IteratedFiberProduct.baseProj π p.1.1 := fun m ↦
        Fin.addCases
          (fun j ↦ by
            rw [Fin.addCases_left, IteratedFiberProduct.baseProj_eq_zero]; exact p.1.1.2 j 0)
          (fun j ↦ by
            rw [Fin.addCases_right]
            exact (p.1.2.2 j 0).trans
              ((IteratedFiberProduct.baseProj_eq_zero π p.1.2).symm.trans p.2.symm)) m
      rw [hbase i, hbase j]⟩
    left_inv := fun y ↦ IteratedFiberProduct.ext π fun i ↦ by
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
    right_inv := fun p ↦ Subtype.ext <| Prod.ext
      (IteratedFiberProduct.ext π fun j ↦ by simp) (IteratedFiberProduct.ext π fun j ↦ by simp)
    contMDiff_toFun := hP.contMDiff_iff_comp.2
      ((contMDiff_reindex_iteratedFiberProduct hn hπ
          (Fin.castAdd (b + 1) : Fin (a + 1) → Fin ((a + 1) + (b + 1)))).prodMk
        (contMDiff_reindex_iteratedFiberProduct hn hπ
          (Fin.natAdd (a + 1) : Fin (b + 1) → Fin ((a + 1) + (b + 1)))))
    contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ ((a + 1) + b)).2 fun i ↦ by
      change ContMDiff _ _ _ (fun p :
        {p : IteratedFiberProduct π (a + 1) × IteratedFiberProduct π (b + 1) //
          IteratedFiberProduct.baseProj π p.1 = IteratedFiberProduct.baseProj π p.2} ↦
        Fin.addCases (motive := fun _ ↦ Y) p.1.1.1 p.1.2.1 i)
      refine Fin.addCases (m := a + 1) (n := b + 1) (fun j ↦ ?_) (fun j ↦ ?_) i
      · simp only [Fin.addCases_left]
        have h := (contMDiff_proj_iteratedFiberProduct hn hπ a j).comp hP.contMDiff.fst
        simp only [Function.comp_def, IteratedFiberProduct.proj_apply] at h; exact h
      · simp only [Fin.addCases_right]
        have h := (contMDiff_proj_iteratedFiberProduct hn hπ b j).comp hP.contMDiff.snd
        simp only [Function.comp_def, IteratedFiberProduct.proj_apply] at h; exact h }

/-- The splitting diffeomorphism restricts a tuple to its first `a + 1` and last `b + 1`
coordinates. -/
@[simp]
theorem iteratedFiberProductSplitDiffeomorph_apply (a b : ℕ)
    (y : IteratedFiberProduct π ((a + 1) + (b + 1))) :
    (iteratedFiberProductSplitDiffeomorph hn hπ a b y).1 =
      (IteratedFiberProduct.reindex π (Fin.castAdd (b + 1)) y,
        IteratedFiberProduct.reindex π (Fin.natAdd (a + 1)) y) :=
  (rfl)

/-- The inverse splitting diffeomorphism concatenates the two tuples with `Fin.addCases`. -/
@[simp]
theorem iteratedFiberProductSplitDiffeomorph_symm_apply (a b : ℕ)
    (p : {p : IteratedFiberProduct π (a + 1) × IteratedFiberProduct π (b + 1) //
      IteratedFiberProduct.baseProj π p.1 = IteratedFiberProduct.baseProj π p.2}) :
    letI := iteratedFiberProductChartedSpace hn hπ ((a + 1) + b)
    letI := iteratedFiberProductChartedSpace hn hπ a
    letI := iteratedFiberProductChartedSpace hn hπ b
    haveI := isManifold_iteratedFiberProduct hn hπ a
    haveI := isManifold_iteratedFiberProduct hn hπ b
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj_iteratedFiberProduct hn hπ a)
      (contMDiff_baseProj_iteratedFiberProduct hn hπ b)
      (fun q _ ↦ transverse_of_isSubmersion_right
        (IX := 𝓘(ℝ, Fin ((a + 1) * finrank ℝ EY - a * finrank ℝ EM) → ℝ))
        (IteratedFiberProduct.baseProj π) hn
        (isSubmersion_baseProj_iteratedFiberProduct hn hπ b) q)
    ((iteratedFiberProductSplitDiffeomorph hn hπ a b).symm p).1 =
      Fin.addCases p.1.1.1 p.1.2.1 :=
  (rfl)

end TauCeti
