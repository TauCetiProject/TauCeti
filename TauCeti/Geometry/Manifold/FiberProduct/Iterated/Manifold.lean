/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Iterated.Basic
public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
public import TauCeti.Geometry.Manifold.FiberProduct.Submersion
public import TauCeti.Geometry.Manifold.IsManifold.Pi
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.Diffeomorph.Pi
import TauCeti.Geometry.Manifold.FiberProduct.Identity
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Pi
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# Manifold structure on iterated fibre products of a submersion

For a `C^n` submersion `π : Y → M` (`1 ≤ n`) between boundaryless finite-dimensional real
manifolds, iterating the binary transverse fibre-product manifold
`TauCeti.transverseFiberProductChartedSpace` equips each `(k + 1)`-fold fibre product
`IteratedFiberProduct π (k + 1)` with a named, non-instance `C^n` atlas
`TauCeti.iteratedFiberProductChartedSpace` of model dimension `(k + 1) * dim Y - k * dim M`
using the inherited subspace topology of `Fin (k + 1) → Y`.

The inclusion `Y^[k+1] ↪ Fin (k + 1) → Y` is a `C^n` smooth embedding
(`TauCeti.isSmoothEmbedding_coe_iteratedFiberProduct`), yielding the smooth universal property
`TauCeti.contMDiff_iteratedFiberProduct_iff`: a map into `Y^[k+1]` is `C^n` exactly when all
`k + 1` coordinate projections are `C^n`. Its tangent image consists precisely of tuples of tangent
vectors in `T Y` with equal images under `dπ`
(`TauCeti.mem_range_mfderiv_coe_iteratedFiberProduct_iff`).

Every reindexing map is `C^n`. Injective reindexings — in particular all coordinate projections
`proj π i` and all face maps `face π i` — are `C^n` submersions, as is the base projection
`baseProj π : Y^[k+1] → M`. Surjective reindexings — in particular all degeneracy maps `degen π i`
and the diagonal `diag π (k + 1)` — are `C^n` smooth embeddings, and permutations of `Fin (k + 1)`
act by `C^n` diffeomorphisms.

No Hausdorff, countability, surjectivity, or nonemptiness assumptions are needed.

## Main definitions

* `TauCeti.iteratedFiberProductChartedSpace`: the named `C^n` atlas on
  `IteratedFiberProduct π (k + 1)` of dimension `(k + 1) * dim Y - k * dim M`.
* `TauCeti.reindexIteratedFiberProductDiffeomorph`: permutation diffeomorphisms of `Y^[k+1]`.

## Main results

* `TauCeti.isManifold_iteratedFiberProduct`,
  `TauCeti.isSmoothEmbedding_coe_iteratedFiberProduct`,
  `TauCeti.mem_range_mfderiv_coe_iteratedFiberProduct_iff`,
  `TauCeti.contMDiff_iteratedFiberProduct_iff`.
* `TauCeti.mfderiv_proj_iteratedFiberProduct`,
  `TauCeti.exists_mfderiv_proj_eq_of_iteratedFiberProduct`,
  `TauCeti.eq_zero_of_mfderiv_proj_iteratedFiberProduct`.
* `TauCeti.isSubmersion_reindex_iteratedFiberProduct`, `isSubmersion_proj_iteratedFiberProduct`,
  `isSubmersion_baseProj_iteratedFiberProduct`, `isSubmersion_face_iteratedFiberProduct`.
* `TauCeti.isSmoothEmbedding_reindex_iteratedFiberProduct`,
  `isSmoothEmbedding_degen_iteratedFiberProduct`, `isSmoothEmbedding_diag_iteratedFiberProduct`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013),
  Theorem 6.30 (transverse preimages) and Theorem 4.12 (submersion normal form).
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
  {n : ℕ∞ω}

private theorem iteratedFiberProduct_dim_zero (dY dM : ℕ) :
    dY + dM - dM = 1 * dY - 0 * dM := by simp

private theorem iteratedFiberProduct_dim_succ (k dY dM : ℕ) :
    ((k + 1) * dY - k * dM) + dY - dM = (k + 2) * dY - (k + 1) * dM := by
  by_cases h : k * dM ≤ (k + 1) * dY
  · rw [← Nat.sub_add_comm h, Nat.sub_sub]; ring_nf
  · push Not at h
    have hlt : dY < dM := by nlinarith
    have h2 : (k + 2) * dY ≤ (k + 1) * dM := by nlinarith
    rw [Nat.sub_eq_zero_of_le h.le, zero_add, Nat.sub_eq_zero_of_le hlt.le,
      Nat.sub_eq_zero_of_le h2]

private def baseHomeomorph {π : Y → M} (hπ : Continuous π) :
    IteratedFiberProduct π 1 ≃ₜ {p : Y × M // π p.1 = id p.2} where
  toFun y := ⟨(y.1 0, π (y.1 0)), rfl⟩
  invFun p := ⟨fun _ ↦ p.1.1, fun _ _ ↦ rfl⟩
  left_inv y := IteratedFiberProduct.ext π fun i ↦ congrArg y.1 (Subsingleton.elim 0 i)
  right_inv p := Subtype.ext (Prod.ext rfl p.2)
  continuous_toFun :=
    (((continuous_apply (0 : Fin 1)).comp continuous_subtype_val).prodMk
      (hπ.comp ((continuous_apply (0 : Fin 1)).comp continuous_subtype_val))).subtype_mk _
  continuous_invFun :=
    (continuous_pi fun _ ↦ continuous_fst.comp continuous_subtype_val).subtype_mk _

private def stepHomeomorph (π : Y → M) (k : ℕ) :
    IteratedFiberProduct π (k + 2) ≃ₜ
      {p : IteratedFiberProduct π (k + 1) × Y // IteratedFiberProduct.baseProj π p.1 = π p.2} where
  toFun y := ⟨(⟨Fin.init y.1, fun i j ↦ y.2 i.castSucc j.castSucc⟩, y.1 (Fin.last (k + 1))),
    (IteratedFiberProduct.baseProj_eq_zero π _).trans (y.2 0 (Fin.last (k + 1)))⟩
  invFun p := ⟨Fin.snoc p.1.1.1 p.1.2, fun i j ↦ by
    have hbase : ∀ m : Fin (k + 2),
        π (Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 m) = IteratedFiberProduct.baseProj π p.1.1 :=
      fun m ↦ Fin.lastCases (by rw [Fin.snoc_last]; exact p.2.symm)
        (fun j ↦ by
          rw [Fin.snoc_castSucc, IteratedFiberProduct.baseProj_eq_zero]; exact p.1.1.2 j 0) m
    rw [hbase i, hbase j]⟩
  left_inv y := Subtype.ext (Fin.snoc_init_self y.1)
  right_inv p := Subtype.ext (Prod.ext (Subtype.ext (by simp)) (by simp))
  continuous_toFun :=
    (((continuous_pi fun j : Fin (k + 1) ↦
      (continuous_apply j.castSucc).comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_apply (Fin.last (k + 1))).comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := (continuous_pi fun i : Fin (k + 2) ↦
    Fin.lastCases
      (motive := fun i ↦ Continuous (fun p :
        {p : IteratedFiberProduct π (k + 1) × Y // IteratedFiberProduct.baseProj π p.1 = π p.2} ↦
        Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 i))
      (by simp only [Fin.snoc_last]; exact continuous_snd.comp continuous_subtype_val)
      (fun j ↦ by
        simp only [Fin.snoc_castSucc]
        exact ((continuous_apply j).comp continuous_subtype_val).comp
          (continuous_fst.comp continuous_subtype_val)) i).subtype_mk _

/-- Shared differential formula for the base projection `baseProj π : Y^[k+1] → M`. -/
private theorem mfderiv_baseProj_eq {π : Y → M} {k d : ℕ}
    [ChartedSpace (Fin d → ℝ) (IteratedFiberProduct π (k + 1))]
    {y : IteratedFiberProduct π (k + 1)}
    (hπd : MDifferentiableAt IY IM π (y.1 0))
    (hvald : MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY))
      (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y) y)
    (ξ : TangentSpace 𝓘(ℝ, Fin d → ℝ) y) :
    mfderiv 𝓘(ℝ, Fin d → ℝ) IM (IteratedFiberProduct.baseProj π) y ξ =
      mfderiv IY IM π (y.1 0)
        ((mfderiv 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY))
          Subtype.val y ξ) 0) := by
  rw [IteratedFiberProduct.baseProj_eq_comp, IteratedFiberProduct.proj_eq_comp,
    mfderiv_comp_apply y hπd (mdifferentiableAt_apply.comp y hvald)]
  exact congrArg (mfderiv IY IM π (y.1 0)) (hvald.mfderiv_apply 0 ξ)

variable [IsManifold IY n Y] [IsManifold IM n M]
  [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]

/-- Inductive bundle carrying the manifold structure, smooth embedding, base submersion, and
tangent-space characterization of `IteratedFiberProduct π (k + 1)`. -/
private structure IteratedFiberProductData (π : Y → M) (n : ℕ∞ω) (k : ℕ) where
  chartedSpace : ChartedSpace (Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
    (IteratedFiberProduct π (k + 1))
  isManifold :
    letI := chartedSpace
    IsManifold 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct π (k + 1))
  isSmoothEmbedding_coe :
    letI := chartedSpace
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      (ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY)) n
      (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y)
  isSubmersion_baseProj :
    letI := chartedSpace
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IM n
      (IteratedFiberProduct.baseProj π : IteratedFiberProduct π (k + 1) → M)
  mem_range_mfderiv_coe_iff :
    letI := chartedSpace
    ∀ (y : IteratedFiberProduct π (k + 1))
      (v : TangentSpace (ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY)) y.1),
      v ∈ (mfderiv
        𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY))
        (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y) y).range ↔
      ∀ i j : Fin (k + 1),
        mfderiv IY IM π (y.1 i) (v i) =
          tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j))

/-- Base step `k = 0`: `Y^[1]` receives its atlas by pulling back `Y ×_M M` along
`baseHomeomorph`. -/
private noncomputable def iteratedFiberProductDataZero {π : Y → M} (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    IteratedFiberProductData (IY := IY) (IM := IM) π n 0 := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let htrans₀ := fun (p : Y × M) (_ : π p.1 = id p.2) ↦ transverse_id_right (I := IY) (J := IM) π p
  letI := transverseFiberProductChartedSpace hn hπ.contMDiff (contMDiff_id (I := IM)) htrans₀
  let e := baseHomeomorph hπ.contMDiff.continuous
  let cs₀ : ChartedSpace (Fin (finrank ℝ EY + finrank ℝ EM - finrank ℝ EM) → ℝ)
      (IteratedFiberProduct π 1) :=
    e.pullbackChartedSpace (H := Fin (finrank ℝ EY + finrank ℝ EM - finrank ℝ EM) → ℝ)
  have hdim := iteratedFiberProduct_dim_zero (finrank ℝ EY) (finrank ℝ EM)
  let cs := castFinChartedSpace hdim cs₀
  have hM : letI := cs; IsManifold 𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct π 1) :=
    castFinChartedSpace_isManifold hdim cs₀ <|
      have := isManifold_transverseFiberProduct hn hπ.contMDiff (contMDiff_id (I := IM)) htrans₀
      e.pullback_isManifold _ n
  letI := cs
  haveI := hM
  let ΦY : IteratedFiberProduct π 1 ≃ₘ^n⟮
      𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ), IY⟯ Y :=
    (castFinDiffeomorph (n := n) hdim cs₀).symm.trans
      ((e.pullbackDiffeomorph 𝓘(ℝ, Fin (finrank ℝ EY + finrank ℝ EM - finrank ℝ EM) → ℝ) n).trans
        (transverseFiberProductIdRightDiffeomorph hn hπ.contMDiff))
  have hΦY_apply : ∀ y : IteratedFiberProduct π 1, ΦY y = y.1 0 := fun y ↦ by
    dsimp only [ΦY]
    rw [Diffeomorph.coe_trans, Function.comp_apply, castFinDiffeomorph_symm_apply,
      Diffeomorph.coe_trans, Function.comp_apply, Homeomorph.coe_pullbackDiffeomorph,
      transverseFiberProductIdRightDiffeomorph_apply]
    rfl
  let ΦFin : IteratedFiberProduct π 1 ≃ₘ^n⟮
      𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ),
      ModelWithCorners.pi (fun _ : Fin 1 ↦ IY)⟯ (Fin 1 → Y) :=
    ΦY.trans (Diffeomorph.finOneDiffeomorph (I := IY) (n := n))
  have hΦFin_coe : (⇑ΦFin : IteratedFiberProduct π 1 → Fin 1 → Y) = Subtype.val := funext fun y ↦
    funext fun i ↦ by
      simp [ΦFin, Diffeomorph.finOneDiffeomorph_apply, hΦY_apply y, Subsingleton.elim 0 i]
  have hemb : Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ)
      (ModelWithCorners.pi (fun _ : Fin 1 ↦ IY)) n
      (Subtype.val : IteratedFiberProduct π 1 → Fin 1 → Y) := by
    have h := ΦFin.isSmoothEmbedding_comp hn (Manifold.IsSmoothEmbedding.id
      (I := 𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ)) (n := n))
    rwa [Function.comp_id, hΦFin_coe] at h
  have hbase_eq : (IteratedFiberProduct.baseProj π : IteratedFiberProduct π 1 → M) = π ∘ ΦY :=
    funext fun y ↦ (IteratedFiberProduct.baseProj_eq_zero π y).trans (congrArg π (hΦY_apply y).symm)
  have hsubm : Manifold.IsSubmersion
      𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ) IM n
      (IteratedFiberProduct.baseProj π : IteratedFiberProduct π 1 → M) := by
    rw [hbase_eq]
    refine ((hπ.contMDiff.comp ΦY.contMDiff).isSubmersionOfComplement_of_surjective_mfderiv hn
      fun y ↦ ?_).isSubmersion
    rw [ΦY.mfderiv_comp_diffeomorph hn0, ContinuousLinearMap.coe_comp,
      ← ΦY.mfderivToContinuousLinearEquiv_coe hn0]
    exact (hπ.surjective_mfderiv hn0 (ΦY y)).comp
      (ΦY.mfderivToContinuousLinearEquiv hn0 y).surjective
  have hrange : ∀ (y : IteratedFiberProduct π 1)
      (v : TangentSpace (ModelWithCorners.pi (fun _ : Fin 1 ↦ IY)) y.1),
      v ∈ (mfderiv
        𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi (fun _ : Fin 1 ↦ IY))
        (Subtype.val : IteratedFiberProduct π 1 → Fin 1 → Y) y).range ↔
      ∀ i j : Fin 1,
        mfderiv IY IM π (y.1 i) (v i) =
          tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j)) := by
    intro y v
    refine ⟨fun _ i j ↦ Subsingleton.elim i j ▸ rfl, fun _ ↦ ?_⟩
    rw [← hΦFin_coe]
    obtain ⟨ξ, hξ⟩ := (ΦFin.mfderivToContinuousLinearEquiv hn0 y).surjective v
    exact ⟨ξ, by rw [← ΦFin.mfderivToContinuousLinearEquiv_coe hn0]; exact hξ⟩
  exact ⟨cs, hM, hemb, hsubm, hrange⟩

/-- Inductive step `k → k + 1`: `Y^[k+2]` receives its atlas by pulling back `Y^[k+1] ×_M Y`
along `stepHomeomorph`. -/
private noncomputable def iteratedFiberProductDataSucc {π : Y → M} (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (k : ℕ)
    (ih : IteratedFiberProductData (IY := IY) (IM := IM) π n k) :
    IteratedFiberProductData (IY := IY) (IM := IM) π n (k + 1) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let dk := (k + 1) * finrank ℝ EY - k * finrank ℝ EM
  let dk' := (k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM
  let Kk := 𝓘(ℝ, Fin dk → ℝ)
  let Kk' := 𝓘(ℝ, Fin dk' → ℝ)
  letI := ih.chartedSpace
  haveI := ih.isManifold
  let P := {p : IteratedFiberProduct π (k + 1) × Y // IteratedFiberProduct.baseProj π p.1 = π p.2}
  let htrans := fun (p : IteratedFiberProduct π (k + 1) × Y)
      (_ : IteratedFiberProduct.baseProj π p.1 = π p.2) ↦
    transverse_of_isSubmersion_right (IX := Kk) (IteratedFiberProduct.baseProj π) hn hπ p
  letI := transverseFiberProductChartedSpace hn ih.isSubmersion_baseProj.contMDiff
    hπ.contMDiff htrans
  let e := stepHomeomorph π k
  let cs₀ : ChartedSpace (Fin (finrank ℝ (Fin dk → ℝ) + finrank ℝ EY - finrank ℝ EM) → ℝ)
      (IteratedFiberProduct π (k + 2)) :=
    e.pullbackChartedSpace
      (H := Fin (finrank ℝ (Fin dk → ℝ) + finrank ℝ EY - finrank ℝ EM) → ℝ)
  have hdim : finrank ℝ (Fin dk → ℝ) + finrank ℝ EY - finrank ℝ EM = dk' := by
    rw [Module.finrank_fin_fun]; exact iteratedFiberProduct_dim_succ k _ _
  let cs := castFinChartedSpace hdim cs₀
  have hM : letI := cs; IsManifold Kk' n (IteratedFiberProduct π (k + 2)) :=
    castFinChartedSpace_isManifold hdim cs₀ <|
      have := isManifold_transverseFiberProduct hn ih.isSubmersion_baseProj.contMDiff
        hπ.contMDiff htrans
      e.pullback_isManifold _ n
  letI := cs
  haveI := hM
  let KP := 𝓘(ℝ, Fin (finrank ℝ (Fin dk → ℝ) + finrank ℝ EY - finrank ℝ EM) → ℝ)
  let stepDiff : IteratedFiberProduct π (k + 2) ≃ₘ^n⟮Kk', KP⟯ P :=
    (castFinDiffeomorph (n := n) hdim cs₀).symm.trans (e.pullbackDiffeomorph KP n)
  have hstepDiff_apply : ∀ y : IteratedFiberProduct π (k + 2), stepDiff y = e y := fun y ↦ by
    simp [stepDiff]
  have hP_emb := isSmoothEmbedding_coe_transverseFiberProduct hn
    ih.isSubmersion_baseProj.contMDiff hπ.contMDiff htrans
  haveI := isManifold_transverseFiberProduct hn
    ih.isSubmersion_baseProj.contMDiff hπ.contMDiff htrans
  let snocD := Diffeomorph.snocDiffeomorph (I := IY) (Y := Y) (n := n) k
  have hval_eq : (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) =
      (⇑snocD ∘ (Prod.map Subtype.val id ∘ Subtype.val)) ∘ ⇑stepDiff := funext fun y ↦ by
    dsimp only [snocD]
    simp only [Function.comp_apply, hstepDiff_apply, Diffeomorph.snocDiffeomorph_apply]
    exact (Fin.snoc_init_self y.1).symm
  have hprod_emb := ih.isSmoothEmbedding_coe.prodMap
    (Manifold.IsSmoothEmbedding.id : Manifold.IsSmoothEmbedding IY IY n (id : Y → Y))
  have hval_smooth : ContMDiff Kk' (ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY)) n
      (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) :=
    hval_eq ▸ (snocD.contMDiff.comp (hprod_emb.contMDiff.comp hP_emb.contMDiff)).comp
      stepDiff.contMDiff
  have hval_inj : ∀ y : IteratedFiberProduct π (k + 2),
      Injective (mfderiv Kk' (ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY))
        (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) y) := fun y ↦ by
    rw [hval_eq, stepDiff.mfderiv_comp_diffeomorph hn0, snocD.mfderiv_diffeomorph_comp hn0,
      mfderiv_comp (stepDiff y) (hprod_emb.contMDiff.mdifferentiable hn0 _)
        (hP_emb.contMDiff.mdifferentiable hn0 _)]
    exact (LeftInverse.injective (snocD.mfderiv_symm_apply_mfderiv_apply hn0 _)).comp
      ((hprod_emb.isImmersion.mfderiv_injective hn0 _).comp
        ((hP_emb.isImmersion.mfderiv_injective hn0 _).comp
          (LeftInverse.injective (stepDiff.mfderiv_symm_apply_mfderiv_apply hn0 y))))
  have hemb : Manifold.IsSmoothEmbedding Kk' (ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY)) n
      (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) :=
    ⟨hval_smooth.isImmersion_of_injective_mfderiv hn hval_inj, IsEmbedding.subtypeVal⟩
  have hrange : ∀ (y : IteratedFiberProduct π (k + 2))
      (v : TangentSpace (ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY)) y.1),
      v ∈ (mfderiv Kk' (ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY))
        (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) y).range ↔
      ∀ i j : Fin (k + 2),
        mfderiv IY IM π (y.1 i) (v i) =
          tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j)) := by
    intro y v
    have hval_d := hval_smooth.mdifferentiable hn0 y
    constructor
    · rintro ⟨ξ, rfl⟩ i j
      rw [ContinuousLinearMap.coe_coe]
      have hπ_coord : ∀ m : Fin (k + 2),
          mfderiv Kk' IM (fun z : IteratedFiberProduct π (k + 2) ↦ π (z.1 m)) y ξ =
            mfderiv IY IM π (y.1 m)
              ((mfderiv Kk' (ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY))
                Subtype.val y ξ) m) := fun m ↦
        (mfderiv_comp_apply y (hπ.contMDiff.mdifferentiable hn0 _)
          (mdifferentiableAt_apply.comp y hval_d) ξ).trans
          (congrArg (mfderiv IY IM π (y.1 m)) (hval_d.mfderiv_apply m ξ))
      rw [← hπ_coord i, ← hπ_coord j]
      exact mfderiv_apply_eq_of_eq (funext fun z ↦ z.2 i j) y ξ
    · intro hv
      let yInit : IteratedFiberProduct π (k + 1) :=
        ⟨Fin.init y.1, fun i j ↦ y.2 i.castSucc j.castSucc⟩
      obtain ⟨u₁, hu₁⟩ := (ih.mem_range_mfderiv_coe_iff yInit (Fin.init v)).2
        fun i j ↦ hv i.castSucc j.castSucc
      rw [ContinuousLinearMap.coe_coe] at hu₁
      have hbase_u₁ : mfderiv Kk IM (IteratedFiberProduct.baseProj π) yInit u₁ =
          mfderiv IY IM π (y.1 0) (v 0) := by
        rw [mfderiv_baseProj_eq (hπ.contMDiff.mdifferentiable hn0 _)
          (ih.isSmoothEmbedding_coe.contMDiff.mdifferentiable hn0 yInit) u₁]
        exact congrArg (mfderiv IY IM π (y.1 0)) (congrFun hu₁ 0)
      obtain ⟨η, hη₁, hη₂⟩ := exists_mfderiv_eq_of_transverseFiberProduct hn
        ih.isSubmersion_baseProj.contMDiff hπ.contMDiff htrans (stepDiff y)
        (tangentSpaceCast Kk yInit (stepDiff y).1.1 u₁)
        (tangentSpaceCast IY (y.1 (Fin.last (k + 1))) (stepDiff y).1.2 (v (Fin.last (k + 1))))
        (by rw [hstepDiff_apply y]; exact hbase_u₁.trans (hv 0 (Fin.last (k + 1))))
      let ξ : TangentSpace Kk' y := mfderiv KP Kk' stepDiff.symm (stepDiff y) η
      have hstepξ : mfderiv Kk' KP stepDiff y ξ = η :=
        stepDiff.mfderiv_apply_mfderiv_symm_apply hn0 y η
      refine ⟨ξ, ?_⟩
      rw [ContinuousLinearMap.coe_coe]
      funext i
      rw [← hval_d.mfderiv_apply i ξ]
      refine Fin.lastCases ?_ ?_ i
      · have hlast : (fun z : IteratedFiberProduct π (k + 2) ↦ z.1 (Fin.last (k + 1))) =
            (fun q : P ↦ q.1.2) ∘ stepDiff :=
          funext fun z ↦ by rw [Function.comp_apply, hstepDiff_apply]; rfl
        rw [mfderiv_apply_eq_of_eq hlast y ξ, stepDiff.mfderiv_comp_diffeomorph_apply hn0,
          hstepξ, hη₂, hstepDiff_apply y]
        rfl
      · intro j
        have hj : (fun z : IteratedFiberProduct π (k + 2) ↦ z.1 j.castSucc) =
            (fun q : P ↦ q.1.1.1 j) ∘ stepDiff :=
          funext fun z ↦ by rw [Function.comp_apply, hstepDiff_apply]; rfl
        have heq : (stepDiff y).1.1 = yInit := congrArg (fun q : P ↦ q.1.1) (hstepDiff_apply y)
        have hP1d := hP_emb.contMDiff.fst.mdifferentiable hn0 (stepDiff y)
        have hsd := ih.isSmoothEmbedding_coe.contMDiff.mdifferentiable hn0 (stepDiff y).1.1
        have h_rhs : mfderiv KP IY (fun q : P ↦ q.1.1.1 j) (stepDiff y) η = v j.castSucc := by
          have hcomp : mfderiv KP IY (fun q : P ↦ q.1.1.1 j) (stepDiff y) η =
              mfderiv Kk IY (fun z : IteratedFiberProduct π (k + 1) ↦ z.1 j) (stepDiff y).1.1
                (mfderiv KP Kk (fun q : P ↦ q.1.1) (stepDiff y) η) :=
            mfderiv_comp_apply (stepDiff y) (mdifferentiableAt_apply.comp _ hsd) hP1d η
          rw [hcomp, hsd.mfderiv_apply j _, hη₁]
          generalize (stepDiff y).1.1 = z at heq ⊢
          subst heq
          exact congrFun hu₁ j
        rw [mfderiv_apply_eq_of_eq hj y ξ, stepDiff.mfderiv_comp_diffeomorph_apply hn0,
          hstepξ, h_rhs]
        rfl
  have hbase_smooth : ContMDiff Kk' IM n
      (IteratedFiberProduct.baseProj π : IteratedFiberProduct π (k + 2) → M) := by
    rw [IteratedFiberProduct.baseProj_eq_comp, IteratedFiberProduct.proj_eq_comp]
    exact hπ.contMDiff.comp (contMDiff_apply.comp hval_smooth)
  have hsubm : Manifold.IsSubmersion Kk' IM n
      (IteratedFiberProduct.baseProj π : IteratedFiberProduct π (k + 2) → M) := by
    refine (hbase_smooth.isSubmersionOfComplement_of_surjective_mfderiv hn
      fun y w ↦ ?_).isSubmersion
    have hex : ∀ i : Fin (k + 2), ∃ vi : TangentSpace IY (y.1 i),
        mfderiv IY IM π (y.1 i) vi =
          tangentSpaceCast IM (IteratedFiberProduct.baseProj π y) (π (y.1 i)) w :=
      fun i ↦ hπ.surjective_mfderiv hn0 (y.1 i) _
    obtain ⟨ξ, hξ⟩ := (hrange y fun i ↦ (hex i).choose).2 fun i j ↦ by
      rw [(hex i).choose_spec, (hex j).choose_spec]; rfl
    rw [ContinuousLinearMap.coe_coe] at hξ
    refine ⟨ξ, ?_⟩
    rw [mfderiv_baseProj_eq (hπ.contMDiff.mdifferentiable hn0 _)
      (hval_smooth.mdifferentiable hn0 y) ξ]
    exact (congrArg (mfderiv IY IM π (y.1 0)) (congrFun hξ 0)).trans (hex 0).choose_spec
  exact ⟨cs, hM, hemb, hsubm, hrange⟩

private noncomputable def iteratedFiberProductData {π : Y → M} (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    ∀ k : ℕ, IteratedFiberProductData (IY := IY) (IM := IM) π n k
  | 0 => iteratedFiberProductDataZero hn hπ
  | k + 1 => iteratedFiberProductDataSucc hn hπ k (iteratedFiberProductData hn hπ k)

variable {π : Y → M} (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)

/-- A fixed `C^n` atlas on the `(k + 1)`-fold fibre product `IteratedFiberProduct π (k + 1)` of a
submersion `π : Y → M`, built by iterating `TauCeti.transverseFiberProductChartedSpace`. It uses
the inherited subspace topology of `Fin (k + 1) → Y` and is not a global instance. -/
@[instance_reducible]
noncomputable def iteratedFiberProductChartedSpace (k : ℕ) :
    ChartedSpace (Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      (IteratedFiberProduct π (k + 1)) :=
  (iteratedFiberProductData hn hπ k).chartedSpace

/-- The `(k + 1)`-fold fibre product of a `C^n` submersion (`1 ≤ n`) is a `C^n` manifold of
dimension `(k + 1) * dim Y - k * dim M`. -/
theorem isManifold_iteratedFiberProduct (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    IsManifold 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct π (k + 1)) :=
  (iteratedFiberProductData hn hπ k).isManifold

/-- The inclusion of `IteratedFiberProduct π (k + 1)` into the finite product manifold
`Fin (k + 1) → Y` is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_coe_iteratedFiberProduct (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      (ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY)) n
      (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y) :=
  (iteratedFiberProductData hn hπ k).isSmoothEmbedding_coe

/-- A tangent vector to `Fin (k + 1) → Y` at `y ∈ Y^[k+1]` lies in the tangent image of the
inclusion `Y^[k+1] ↪ Fin (k + 1) → Y` exactly when all of its components have equal images under
`dπ`. -/
theorem mem_range_mfderiv_coe_iteratedFiberProduct_iff (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ∀ (y : IteratedFiberProduct π (k + 1))
      (v : TangentSpace (ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY)) y.1),
      v ∈ (mfderiv
        𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY))
        (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y) y).range ↔
      ∀ i j : Fin (k + 1),
        mfderiv IY IM π (y.1 i) (v i) =
          tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j)) :=
  (iteratedFiberProductData hn hπ k).mem_range_mfderiv_coe_iff

/-- **Smooth universal property of the iterated fibre product.** A map into
`IteratedFiberProduct π (k + 1)` is `C^n` if and only if each of its `k + 1` coordinate
projections into `Y` is `C^n`. -/
theorem contMDiff_iteratedFiberProduct_iff {EX HX X : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    (k : ℕ) {f : X → IteratedFiberProduct π (k + 1)} :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ContMDiff IX 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n f ↔
      ∀ i : Fin (k + 1), ContMDiff IX IY n (fun x ↦ (f x).1 i) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  rw [(isSmoothEmbedding_coe_iteratedFiberProduct hn hπ k).contMDiff_iff_comp, contMDiff_pi_iff]
  rfl

/-- The differential of the `i`-th coordinate projection `Y^[k+1] → Y` is the `i`-th component of
the differential of the inclusion `Y^[k+1] ↪ Fin (k + 1) → Y`. -/
theorem mfderiv_proj_iteratedFiberProduct (k : ℕ) (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ∀ (y : IteratedFiberProduct π (k + 1))
      (ξ : TangentSpace 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) y),
      mfderiv 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IY
        (IteratedFiberProduct.proj π i) y ξ =
        (mfderiv 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
          (ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY)) Subtype.val y ξ) i := by
  let := iteratedFiberProductChartedSpace hn hπ k
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  intro y ξ
  rw [IteratedFiberProduct.proj_eq_comp]
  exact ((isSmoothEmbedding_coe_iteratedFiberProduct hn hπ k).contMDiff.mdifferentiable
    hn0 y).mfderiv_apply i ξ

/-- Any `(k + 1)`-tuple of tangent vectors `v i ∈ T_{y i} Y` whose images under `dπ` agree arises
as the differentials of the coordinate projections `proj π i` evaluated on a tangent vector of
`Y^[k+1]`. -/
theorem exists_mfderiv_proj_eq_of_iteratedFiberProduct (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ∀ (y : IteratedFiberProduct π (k + 1)) (v : ∀ i : Fin (k + 1), TangentSpace IY (y.1 i)),
      (∀ i j : Fin (k + 1),
        mfderiv IY IM π (y.1 i) (v i) =
          tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j))) →
      ∃ ξ : TangentSpace 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) y,
        ∀ i : Fin (k + 1),
          mfderiv 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IY
            (IteratedFiberProduct.proj π i) y ξ = v i := by
  let := iteratedFiberProductChartedSpace hn hπ k
  intro y v hv
  obtain ⟨ξ, hξ⟩ := (mem_range_mfderiv_coe_iteratedFiberProduct_iff hn hπ k y v).2 hv
  exact ⟨ξ, fun i ↦ (mfderiv_proj_iteratedFiberProduct hn hπ k i y ξ).trans (congrFun hξ i)⟩

/-- A tangent vector to `IteratedFiberProduct π (k + 1)` vanishes when the differentials of all
`k + 1` coordinate projections vanish on it. -/
theorem eq_zero_of_mfderiv_proj_iteratedFiberProduct (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ∀ (y : IteratedFiberProduct π (k + 1))
      (ξ : TangentSpace 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) y),
      (∀ i : Fin (k + 1),
        mfderiv 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IY
          (IteratedFiberProduct.proj π i) y ξ = 0) →
      ξ = 0 := by
  let := iteratedFiberProductChartedSpace hn hπ k
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  intro y ξ hξ
  have hemb := isSmoothEmbedding_coe_iteratedFiberProduct hn hπ k
  refine (injective_iff_map_eq_zero _).1 (hemb.isImmersion.mfderiv_injective hn0 y) ξ ?_
  exact funext fun i ↦ (mfderiv_proj_iteratedFiberProduct hn hπ k i y ξ).symm.trans (hξ i)

/-! ### Smoothness, submersions, embeddings, and permutations of structure maps -/

/-- Each coordinate projection `Y^[k+1] → Y` is `C^n`. -/
theorem contMDiff_proj_iteratedFiberProduct (k : ℕ) (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ContMDiff 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IY n
      (IteratedFiberProduct.proj π i) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  rw [IteratedFiberProduct.proj_eq_comp]
  exact contMDiff_apply.comp (isSmoothEmbedding_coe_iteratedFiberProduct hn hπ k).contMDiff

/-- Each coordinate projection `Y^[k+1] → Y` is a `C^n` submersion. -/
theorem isSubmersion_proj_iteratedFiberProduct (k : ℕ) (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    Manifold.IsSubmersion 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IY n
      (IteratedFiberProduct.proj π i) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  have := isManifold_iteratedFiberProduct hn hπ k
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine
    ((contMDiff_proj_iteratedFiberProduct hn hπ k i).isSubmersionOfComplement_of_surjective_mfderiv
      hn fun y u ↦ ?_).isSubmersion
  classical
  have hex : ∀ j : Fin (k + 1), ∃ w : TangentSpace IY (y.1 j),
      mfderiv IY IM π (y.1 j) w =
        tangentSpaceCast IM (π (y.1 i)) (π (y.1 j)) (mfderiv IY IM π (y.1 i) u) :=
    fun j ↦ hπ.surjective_mfderiv hn0 (y.1 j) _
  let v : ∀ j : Fin (k + 1), TangentSpace IY (y.1 j) :=
    fun j ↦ if j = i then tangentSpaceCast IY (y.1 i) (y.1 j) u else (hex j).choose
  have hv : ∀ j : Fin (k + 1), mfderiv IY IM π (y.1 j) (v j) =
      tangentSpaceCast IM (π (y.1 i)) (π (y.1 j)) (mfderiv IY IM π (y.1 i) u) := fun j ↦ by
    by_cases hji : j = i
    · subst hji; simp [v]; rfl
    · simp [v, hji, (hex j).choose_spec]
  obtain ⟨ξ, hξ⟩ := exists_mfderiv_proj_eq_of_iteratedFiberProduct hn hπ k y v fun j₁ j₂ ↦ by
    rw [hv j₁, hv j₂]; rfl
  exact ⟨ξ, (hξ i).trans (by simp [v]; rfl)⟩

/-- The base projection `Y^[k+1] → M` is `C^n`. -/
theorem contMDiff_baseProj_iteratedFiberProduct (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ContMDiff 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IM n
      (IteratedFiberProduct.baseProj π : IteratedFiberProduct π (k + 1) → M) :=
  letI := iteratedFiberProductChartedSpace hn hπ k
  (iteratedFiberProductData hn hπ k).isSubmersion_baseProj.contMDiff

/-- The base projection `Y^[k+1] → M` is a `C^n` submersion. -/
theorem isSubmersion_baseProj_iteratedFiberProduct (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    Manifold.IsSubmersion 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IM n
      (IteratedFiberProduct.baseProj π : IteratedFiberProduct π (k + 1) → M) :=
  (iteratedFiberProductData hn hπ k).isSubmersion_baseProj

/-- Every reindexing map `Y^[k+1] → Y^[l+1]` is `C^n`. -/
theorem contMDiff_reindex_iteratedFiberProduct {k l : ℕ} (f : Fin (l + 1) → Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := iteratedFiberProductChartedSpace hn hπ l
    ContMDiff
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((l + 1) * finrank ℝ EY - l * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.reindex π f) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  let := iteratedFiberProductChartedSpace hn hπ l
  refine (contMDiff_iteratedFiberProduct_iff hn hπ l).2 fun j ↦ ?_
  simpa only [← IteratedFiberProduct.proj_apply, ← Function.comp_def,
    IteratedFiberProduct.proj_comp_reindex] using contMDiff_proj_iteratedFiberProduct hn hπ k (f j)

/-- Every injective index map `f : Fin (l + 1) → Fin (k + 1)` induces a `C^n` submersion
`Y^[k+1] → Y^[l+1]`. -/
theorem isSubmersion_reindex_iteratedFiberProduct {k l : ℕ} {f : Fin (l + 1) → Fin (k + 1)}
    (hf : Injective f) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := iteratedFiberProductChartedSpace hn hπ l
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((l + 1) * finrank ℝ EY - l * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.reindex π f) := by
  classical
  let := iteratedFiberProductChartedSpace hn hπ k
  let := iteratedFiberProductChartedSpace hn hπ l
  have := isManifold_iteratedFiberProduct hn hπ k
  have := isManifold_iteratedFiberProduct hn hπ l
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let Kk := 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
  let Kl := 𝓘(ℝ, Fin ((l + 1) * finrank ℝ EY - l * finrank ℝ EM) → ℝ)
  have hrf : ContMDiff Kk Kl n (IteratedFiberProduct.reindex π f) :=
    contMDiff_reindex_iteratedFiberProduct hn hπ f
  refine (hrf.isSubmersionOfComplement_of_surjective_mfderiv hn fun y ζ ↦ ?_).isSubmersion
  let z := IteratedFiberProduct.reindex π f y
  let u : TangentSpace (ModelWithCorners.pi (fun _ : Fin (l + 1) ↦ IY)) z.1 :=
    mfderiv Kl (ModelWithCorners.pi (fun _ : Fin (l + 1) ↦ IY)) Subtype.val z ζ
  have hu : ∀ j₁ j₂ : Fin (l + 1),
      mfderiv IY IM π (z.1 j₁) (u j₁) =
        tangentSpaceCast IM (π (z.1 j₂)) (π (z.1 j₁)) (mfderiv IY IM π (z.1 j₂) (u j₂)) :=
    (mem_range_mfderiv_coe_iteratedFiberProduct_iff hn hπ l z u).1 ⟨ζ, rfl⟩
  have hex : ∀ i : Fin (k + 1), ∃ w : TangentSpace IY (y.1 i),
      mfderiv IY IM π (y.1 i) w =
        tangentSpaceCast IM (π (z.1 0)) (π (y.1 i)) (mfderiv IY IM π (z.1 0) (u 0)) :=
    fun i ↦ hπ.surjective_mfderiv hn0 (y.1 i) _
  let v : ∀ i : Fin (k + 1), TangentSpace IY (y.1 i) := fun i ↦
    if hi : i ∈ range f then tangentSpaceCast IY (z.1 hi.choose) (y.1 i) (u hi.choose)
    else (hex i).choose
  have hv_apply : ∀ j : Fin (l + 1), v (f j) = u j := fun j ↦ by
    have hi : f j ∈ range f := ⟨j, rfl⟩
    simp only [v, hi, ↓reduceDIte, hf hi.choose_spec]; rfl
  have hv_match : ∀ i : Fin (k + 1), mfderiv IY IM π (y.1 i) (v i) =
      tangentSpaceCast IM (π (z.1 0)) (π (y.1 i)) (mfderiv IY IM π (z.1 0) (u 0)) := fun i ↦ by
    by_cases hi : i ∈ range f
    · obtain ⟨j, rfl⟩ := hi
      have hzj : z.1 j = y.1 (f j) := congrFun (IteratedFiberProduct.coe_reindex π f y) j
      rw [hv_apply j, ← hzj]; exact hu j 0
    · simp only [v, hi, ↓reduceDIte]; exact (hex i).choose_spec
  obtain ⟨ξ, hξ⟩ := exists_mfderiv_proj_eq_of_iteratedFiberProduct hn hπ k y v fun i₁ i₂ ↦ by
    rw [hv_match i₁, hv_match i₂]; rfl
  refine ⟨ξ, sub_eq_zero.1 <| eq_zero_of_mfderiv_proj_iteratedFiberProduct hn hπ l z _ fun j ↦ ?_⟩
  rw [map_sub, sub_eq_zero]
  have hcomp_l := mfderiv_comp_apply y
    ((contMDiff_proj_iteratedFiberProduct hn hπ l j).mdifferentiable hn0 z)
    (hrf.mdifferentiable hn0 y) ξ
  rw [IteratedFiberProduct.proj_comp_reindex] at hcomp_l
  rw [← hcomp_l, hξ (f j), mfderiv_proj_iteratedFiberProduct hn hπ l j z ζ, hv_apply j]

/-- Every surjective index map `f : Fin (l + 1) → Fin (k + 1)` induces a `C^n` smooth embedding
`Y^[k+1] → Y^[l+1]`, since reindexing along a right inverse of `f` is a global `C^n` left
inverse. -/
theorem isSmoothEmbedding_reindex_iteratedFiberProduct {k l : ℕ} {f : Fin (l + 1) → Fin (k + 1)}
    (hf : Surjective f) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := iteratedFiberProductChartedSpace hn hπ l
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((l + 1) * finrank ℝ EY - l * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.reindex π f) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  let := iteratedFiberProductChartedSpace hn hπ l
  have := isManifold_iteratedFiberProduct hn hπ k
  have := isManifold_iteratedFiberProduct hn hπ l
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let g : Fin (k + 1) → Fin (l + 1) := surjInv hf
  have hleft : LeftInverse (IteratedFiberProduct.reindex π g) (IteratedFiberProduct.reindex π f) :=
    fun y ↦ IteratedFiberProduct.ext π fun i ↦ by
      simpa only [IteratedFiberProduct.coe_reindex, Function.comp_apply] using
        congrArg y.1 (surjInv_eq hf i)
  refine ⟨(contMDiff_reindex_iteratedFiberProduct hn hπ f).isImmersion_of_leftInverse hn
    (fun y ↦ (contMDiff_reindex_iteratedFiberProduct hn hπ g).mdifferentiable hn0 _) hleft,
    IteratedFiberProduct.isEmbedding_reindex π hf⟩

/-- Any permutation `e : Fin (k + 1) ≃ Fin (k + 1)` acts on `IteratedFiberProduct π (k + 1)` by a
`C^n` diffeomorphism. -/
noncomputable def reindexIteratedFiberProductDiffeomorph {k : ℕ}
    (e : Fin (k + 1) ≃ Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    IteratedFiberProduct π (k + 1) ≃ₘ^n⟮
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)⟯
      IteratedFiberProduct π (k + 1) :=
  letI := iteratedFiberProductChartedSpace hn hπ k
  { toFun := IteratedFiberProduct.reindex π e
    invFun := IteratedFiberProduct.reindex π e.symm
    left_inv := fun y ↦ IteratedFiberProduct.ext π fun i ↦ by
      simpa only [IteratedFiberProduct.coe_reindex, Function.comp_apply] using
        congrArg y.1 (e.apply_symm_apply i)
    right_inv := fun y ↦ IteratedFiberProduct.ext π fun i ↦ by
      simpa only [IteratedFiberProduct.coe_reindex, Function.comp_apply] using
        congrArg y.1 (e.symm_apply_apply i)
    contMDiff_toFun := contMDiff_reindex_iteratedFiberProduct hn hπ e
    contMDiff_invFun := contMDiff_reindex_iteratedFiberProduct hn hπ e.symm }

/-- Applying the permutation diffeomorphism reindexes the tuple by `e`. -/
@[simp]
theorem reindexIteratedFiberProductDiffeomorph_apply {k : ℕ} (e : Fin (k + 1) ≃ Fin (k + 1))
    (y : IteratedFiberProduct π (k + 1)) :
    reindexIteratedFiberProductDiffeomorph hn hπ e y = IteratedFiberProduct.reindex π e y :=
  (rfl)

/-- Applying the inverse permutation diffeomorphism reindexes the tuple by `e.symm`. -/
@[simp]
theorem reindexIteratedFiberProductDiffeomorph_symm_apply {k : ℕ}
    (e : Fin (k + 1) ≃ Fin (k + 1)) (y : IteratedFiberProduct π (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    (reindexIteratedFiberProductDiffeomorph hn hπ e).symm y =
      IteratedFiberProduct.reindex π e.symm y :=
  (rfl)

/-- Every simplicial face map `Y^[k+2] → Y^[k+1]` is `C^n`. -/
theorem contMDiff_face_iteratedFiberProduct {k : ℕ} (i : Fin (k + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    letI := iteratedFiberProductChartedSpace hn hπ k
    ContMDiff
      𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.face π i) :=
  IteratedFiberProduct.face_eq_reindex π i ▸
    contMDiff_reindex_iteratedFiberProduct hn hπ i.succAbove

/-- Every simplicial face map `Y^[k+2] → Y^[k+1]` is a `C^n` submersion. -/
theorem isSubmersion_face_iteratedFiberProduct {k : ℕ} (i : Fin (k + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    letI := iteratedFiberProductChartedSpace hn hπ k
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.face π i) :=
  IteratedFiberProduct.face_eq_reindex π i ▸
    isSubmersion_reindex_iteratedFiberProduct hn hπ Fin.succAbove_right_injective

/-- Every simplicial degeneracy map `Y^[k+1] → Y^[k+2]` is `C^n`. -/
theorem contMDiff_degen_iteratedFiberProduct {k : ℕ} (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    ContMDiff
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.degen π i) :=
  IteratedFiberProduct.degen_eq_reindex π i ▸
    contMDiff_reindex_iteratedFiberProduct hn hπ i.predAbove

/-- Every simplicial degeneracy map `Y^[k+1] → Y^[k+2]` is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_degen_iteratedFiberProduct {k : ℕ} (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.degen π i) :=
  IteratedFiberProduct.degen_eq_reindex π i ▸
    isSmoothEmbedding_reindex_iteratedFiberProduct hn hπ (Fin.predAbove_surjective i)

/-- The diagonal map `Y → Y^[k+1]` is `C^n`. -/
theorem contMDiff_diag_iteratedFiberProduct (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ContMDiff IY 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.diag π (k + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  exact (contMDiff_iteratedFiberProduct_iff hn hπ k).2 fun _ ↦ by
    simp only [IteratedFiberProduct.coe_diag]; exact contMDiff_id

/-- The diagonal map `Y → Y^[k+1]` is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_diag_iteratedFiberProduct (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    Manifold.IsSmoothEmbedding IY 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.diag π (k + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  have := isManifold_iteratedFiberProduct hn hπ k
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  exact ⟨(contMDiff_diag_iteratedFiberProduct hn hπ k).isImmersion_of_leftInverse hn
    (fun _ ↦ (contMDiff_proj_iteratedFiberProduct hn hπ k 0).mdifferentiable hn0 _)
    (IteratedFiberProduct.proj_diag π 0),
    IteratedFiberProduct.isEmbedding_diag π k⟩

end TauCeti
