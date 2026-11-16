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
import TauCeti.Geometry.Manifold.FiberProduct.Identity
import TauCeti.Geometry.Manifold.Immersion.Differential
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
act by `C^n` diffeomorphisms. The resulting manifold agrees up to canonical `C^n` diffeomorphism
with `Y` at `k = 0`, with `Y ×_M Y` at `k = 1`, with the inductive step `Y^[k+1] ×_M Y`, and with
arbitrary binary splittings `Y^[a+1] ×_M Y^[b+1]` (independence of the order of iteration).

No Hausdorff, countability, surjectivity, or nonemptiness assumptions are needed.

## Main definitions

* `TauCeti.iteratedFiberProductChartedSpace`: the named `C^n` atlas on
  `IteratedFiberProduct π (k + 1)` of dimension `(k + 1) * dim Y - k * dim M`.
* `TauCeti.reindexIteratedFiberProductDiffeomorph`: permutation diffeomorphisms of `Y^[k+1]`.
* `TauCeti.iteratedFiberProductOneDiffeomorph`, `iteratedFiberProductTwoDiffeomorph`,
  `iteratedFiberProductStepDiffeomorph`, `iteratedFiberProductSplitDiffeomorph`: canonical
  diffeomorphisms with `Y`, `Y ×_M Y`, `Y^[k+1] ×_M Y`, and `Y^[a+1] ×_M Y^[b+1]`.

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
    dY + dM - dM = 1 * dY - 0 * dM := by
  simp

private theorem iteratedFiberProduct_dim_succ (k dY dM : ℕ) :
    ((k + 1) * dY - k * dM) + dY - dM = (k + 2) * dY - (k + 1) * dM := by
  by_cases h : k * dM ≤ (k + 1) * dY
  · rw [← Nat.sub_add_comm h, Nat.sub_sub]
    ring_nf
  · push Not at h
    have hlt : dY < dM := by nlinarith
    have h1 : (k + 1) * dY - k * dM = 0 := Nat.sub_eq_zero_of_le h.le
    have h2 : (k + 2) * dY ≤ (k + 1) * dM := by nlinarith
    rw [h1, zero_add, Nat.sub_eq_zero_of_le hlt.le, Nat.sub_eq_zero_of_le h2]

/-- Transport a charted-space structure along an equality of model dimensions. -/
@[instance_reducible]
private def castFinChartedSpace {X : Type*} [TopologicalSpace X] {d₁ d₂ : ℕ} (h : d₁ = d₂)
    (cs : ChartedSpace (Fin d₁ → ℝ) X) : ChartedSpace (Fin d₂ → ℝ) X :=
  h ▸ cs

/-- The identity map as a `C^n` diffeomorphism between a charted space and its dimension-cast
copy. -/
private noncomputable def castFinDiffeomorph {X : Type*} [TopologicalSpace X] {d₁ d₂ : ℕ}
    (h : d₁ = d₂) (cs : ChartedSpace (Fin d₁ → ℝ) X) :
    letI := cs
    letI : ChartedSpace (Fin d₂ → ℝ) X := castFinChartedSpace h cs
    X ≃ₘ^n⟮𝓘(ℝ, Fin d₁ → ℝ), 𝓘(ℝ, Fin d₂ → ℝ)⟯ X := by
  subst h
  letI := cs
  exact Diffeomorph.refl 𝓘(ℝ, Fin d₁ → ℝ) X n

private theorem castFinDiffeomorph_symm_apply {X : Type*} [TopologicalSpace X] {d₁ d₂ : ℕ}
    (h : d₁ = d₂) (cs : ChartedSpace (Fin d₁ → ℝ) X) (x : X) :
    letI := cs
    letI : ChartedSpace (Fin d₂ → ℝ) X := castFinChartedSpace h cs
    (castFinDiffeomorph (n := n) h cs).symm x = x := by
  subst h
  rfl

private theorem castFinChartedSpace_isManifold {X : Type*} [TopologicalSpace X] {d₁ d₂ : ℕ}
    (h : d₁ = d₂) (cs : ChartedSpace (Fin d₁ → ℝ) X)
    (hM : letI := cs; IsManifold 𝓘(ℝ, Fin d₁ → ℝ) n X) :
    letI := castFinChartedSpace h cs
    IsManifold 𝓘(ℝ, Fin d₂ → ℝ) n X := by
  subst h
  exact hM

private theorem mfderiv_apply_eq_of_eq {EX HX X : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {f₁ f₂ : X → M} (h : f₁ = f₂) (x : X) (v : TangentSpace IX x) :
    mfderiv IX IM f₁ x v = tangentSpaceCast IM (f₂ x) (f₁ x) (mfderiv IX IM f₂ x v) := by
  subst h
  rfl

private def baseHomeomorph {π : Y → M} (hπ : Continuous π) :
    IteratedFiberProduct π 1 ≃ₜ {p : Y × M // π p.1 = id p.2} where
  toFun y := ⟨(y.1 0, π (y.1 0)), rfl⟩
  invFun p := ⟨fun _ ↦ p.1.1, fun _ _ ↦ rfl⟩
  left_inv y := IteratedFiberProduct.ext π fun i ↦ congrArg y.1 (Subsingleton.elim 0 i)
  right_inv p := Subtype.ext (Prod.ext rfl p.2)
  continuous_toFun :=
    ((IteratedFiberProduct.continuous_proj π 0).prodMk
      (hπ.comp (IteratedFiberProduct.continuous_proj π 0))).subtype_mk _
  continuous_invFun :=
    (continuous_pi fun _ ↦ continuous_fst.comp continuous_subtype_val).subtype_mk _

private def stepHomeomorph (π : Y → M) (k : ℕ) :
    IteratedFiberProduct π (k + 2) ≃ₜ
      {p : IteratedFiberProduct π (k + 1) × Y // IteratedFiberProduct.baseProj π p.1 = π p.2} where
  toFun y := ⟨(⟨Fin.init y.1, fun i j ↦ y.2 i.castSucc j.castSucc⟩, y.1 (Fin.last (k + 1))),
    y.2 0 (Fin.last (k + 1))⟩
  invFun p := ⟨Fin.snoc p.1.1.1 p.1.2, by
    have hbase : ∀ i : Fin (k + 2),
        π (Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 i) = IteratedFiberProduct.baseProj π p.1.1 := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last]
        exact p.2.symm
      · intro j
        rw [Fin.snoc_castSucc]
        exact p.1.1.2 j 0
    intro i j
    rw [hbase i, hbase j]⟩
  left_inv y := Subtype.ext (Fin.snoc_init_self y.1)
  right_inv p := by
    apply Subtype.ext
    refine Prod.ext (Subtype.ext (by simp)) (by simp)
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact (continuous_pi fun j : Fin (k + 1) ↦
        IteratedFiberProduct.continuous_proj π j.castSucc).subtype_mk _
    · exact IteratedFiberProduct.continuous_proj π (Fin.last (k + 1))
  continuous_invFun := by
    refine (continuous_pi fun i : Fin (k + 2) ↦ ?_).subtype_mk _
    refine Fin.lastCases
      (motive := fun i ↦ Continuous (fun p :
        {p : IteratedFiberProduct π (k + 1) × Y // IteratedFiberProduct.baseProj π p.1 = π p.2} ↦
        Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 i)) ?_ ?_ i
    · simp only [Fin.snoc_last]
      exact continuous_snd.comp continuous_subtype_val
    · intro j
      simp only [Fin.snoc_castSucc]
      exact (IteratedFiberProduct.continuous_proj π j).comp
        (continuous_fst.comp continuous_subtype_val)

private def finOneDiffeomorph :
    Y ≃ₘ^n⟮IY, ModelWithCorners.pi (fun _ : Fin 1 ↦ IY)⟯ (Fin 1 → Y) where
  toFun y := fun _ ↦ y
  invFun w := w 0
  left_inv _ := rfl
  right_inv w := funext fun i ↦ congrArg w (Subsingleton.elim 0 i)
  contMDiff_toFun := contMDiff_pi_iff.2 fun _ ↦ contMDiff_id
  contMDiff_invFun := contMDiff_apply

private def snocDiffeomorph (k : ℕ) :
    ((Fin (k + 1) → Y) × Y) ≃ₘ^n⟮
      (ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY)).prod IY,
      ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY)⟯ (Fin (k + 2) → Y) where
  toFun p := Fin.snoc p.1 p.2
  invFun w := (Fin.init w, w (Fin.last (k + 1)))
  left_inv p := Prod.ext (by simp) (by simp)
  right_inv w := Fin.snoc_init_self w
  contMDiff_toFun := by
    refine contMDiff_pi_iff.2 fun i ↦ ?_
    refine Fin.lastCases
      (motive := fun i ↦ ContMDiff ((ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY)).prod IY)
        IY n (fun p : (Fin (k + 1) → Y) × Y ↦ Fin.snoc (α := fun _ ↦ Y) p.1 p.2 i)) ?_ ?_ i
    · simp only [Fin.snoc_last]
      exact contMDiff_snd
    · intro j
      simp only [Fin.snoc_castSucc]
      exact (contMDiff_apply (i := j)).comp contMDiff_fst
  contMDiff_invFun :=
    (contMDiff_pi_iff.2 fun j ↦ contMDiff_apply (i := j.castSucc)).prodMk
      (contMDiff_apply (i := Fin.last (k + 1)))

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
  let csP := transverseFiberProductChartedSpace hn hπ.contMDiff (contMDiff_id (I := IM)) htrans₀
  letI := csP
  let e := baseHomeomorph hπ.contMDiff.continuous
  let cs₀ : ChartedSpace (Fin (finrank ℝ EY + finrank ℝ EM - finrank ℝ EM) → ℝ)
      (IteratedFiberProduct π 1) :=
    e.pullbackChartedSpace (H := Fin (finrank ℝ EY + finrank ℝ EM - finrank ℝ EM) → ℝ)
  have hdim : finrank ℝ EY + finrank ℝ EM - finrank ℝ EM =
      (0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM :=
    iteratedFiberProduct_dim_zero (finrank ℝ EY) (finrank ℝ EM)
  let cs := castFinChartedSpace hdim cs₀
  have hM : letI := cs; IsManifold 𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct π 1) := by
    refine castFinChartedSpace_isManifold hdim cs₀ ?_
    have := isManifold_transverseFiberProduct hn hπ.contMDiff (contMDiff_id (I := IM)) htrans₀
    exact e.pullback_isManifold _ n
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
    ΦY.trans (finOneDiffeomorph (IY := IY) (n := n))
  have hΦFin_coe : (⇑ΦFin : IteratedFiberProduct π 1 → Fin 1 → Y) = Subtype.val := by
    funext y i
    have hi : 0 = i := Subsingleton.elim 0 i
    simp only [ΦFin, Diffeomorph.coe_trans, Function.comp_apply, finOneDiffeomorph]
    exact (hΦY_apply y).trans (congrArg y.1 hi)
  have hemb : Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ)
      (ModelWithCorners.pi (fun _ : Fin 1 ↦ IY)) n
      (Subtype.val : IteratedFiberProduct π 1 → Fin 1 → Y) := by
    have h := ΦFin.isSmoothEmbedding_comp hn (Manifold.IsSmoothEmbedding.id
      (I := 𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ)) (n := n))
    rwa [Function.comp_id, hΦFin_coe] at h
  have hbase_eq : (IteratedFiberProduct.baseProj π : IteratedFiberProduct π 1 → M) = π ∘ ΦY := by
    funext y
    exact congrArg π (hΦY_apply y).symm
  have hsubm : Manifold.IsSubmersion
      𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ) IM n
      (IteratedFiberProduct.baseProj π : IteratedFiberProduct π 1 → M) := by
    rw [hbase_eq]
    refine ((hπ.contMDiff.comp ΦY.contMDiff).isSubmersionOfComplement_of_surjective_mfderiv hn
      fun y ↦ ?_).isSubmersion
    rw [mfderiv_comp y (hπ.contMDiff.mdifferentiable hn0 _) (ΦY.mdifferentiable hn0 _),
      ContinuousLinearMap.coe_comp, ← ΦY.mfderivToContinuousLinearEquiv_coe hn0]
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
    constructor
    · intro _ i j
      have hij : i = j := Subsingleton.elim i j
      subst hij
      rfl
    · intro _
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
  have htrans : ∀ p : IteratedFiberProduct π (k + 1) × Y,
      IteratedFiberProduct.baseProj π p.1 = π p.2 →
      (mfderiv Kk IM (IteratedFiberProduct.baseProj π) p.1).range ⊔
        ((tangentSpaceCast IM (π p.2)
            (IteratedFiberProduct.baseProj π p.1)).toContinuousLinearMap.comp
          (mfderiv IY IM π p.2)).range = ⊤ :=
    fun p _ ↦ transverse_of_isSubmersion_right (IteratedFiberProduct.baseProj π) hn hπ p
  let csP := transverseFiberProductChartedSpace hn ih.isSubmersion_baseProj.contMDiff
    hπ.contMDiff htrans
  letI := csP
  let e := stepHomeomorph π k
  let cs₀ : ChartedSpace (Fin (finrank ℝ (Fin dk → ℝ) + finrank ℝ EY - finrank ℝ EM) → ℝ)
      (IteratedFiberProduct π (k + 2)) :=
    e.pullbackChartedSpace
      (H := Fin (finrank ℝ (Fin dk → ℝ) + finrank ℝ EY - finrank ℝ EM) → ℝ)
  have hdim : finrank ℝ (Fin dk → ℝ) + finrank ℝ EY - finrank ℝ EM = dk' := by
    rw [Module.finrank_fin_fun]
    exact iteratedFiberProduct_dim_succ k (finrank ℝ EY) (finrank ℝ EM)
  let cs := castFinChartedSpace hdim cs₀
  have hM : letI := cs; IsManifold Kk' n (IteratedFiberProduct π (k + 2)) := by
    refine castFinChartedSpace_isManifold hdim cs₀ ?_
    have := isManifold_transverseFiberProduct hn ih.isSubmersion_baseProj.contMDiff
      hπ.contMDiff htrans
    exact e.pullback_isManifold _ n
  letI := cs
  haveI := hM
  let KP := 𝓘(ℝ, Fin (finrank ℝ (Fin dk → ℝ) + finrank ℝ EY - finrank ℝ EM) → ℝ)
  let stepDiff : IteratedFiberProduct π (k + 2) ≃ₘ^n⟮Kk', KP⟯ P :=
    (castFinDiffeomorph (n := n) hdim cs₀).symm.trans (e.pullbackDiffeomorph KP n)
  have hstepDiff_apply : ∀ y : IteratedFiberProduct π (k + 2), stepDiff y = e y := fun y ↦ by
    simp only [stepDiff, Diffeomorph.coe_trans, Function.comp_apply,
      Homeomorph.coe_pullbackDiffeomorph, castFinDiffeomorph_symm_apply]
  have hP_emb := isSmoothEmbedding_coe_transverseFiberProduct hn
    ih.isSubmersion_baseProj.contMDiff hπ.contMDiff htrans
  haveI := isManifold_transverseFiberProduct hn
    ih.isSubmersion_baseProj.contMDiff hπ.contMDiff htrans
  let snocD := snocDiffeomorph (IY := IY) (Y := Y) (n := n) k
  have hval_eq : (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) =
      ⇑snocD ∘ Prod.map Subtype.val id ∘ Subtype.val ∘ ⇑stepDiff := by
    funext y
    simp only [Function.comp_apply, hstepDiff_apply]
    exact (Fin.snoc_init_self y.1).symm
  have hprod_emb : Manifold.IsSmoothEmbedding (Kk.prod IY)
      ((ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY)).prod IY) n
      (Prod.map (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y)
        (id : Y → Y)) :=
    ih.isSmoothEmbedding_coe.prodMap Manifold.IsSmoothEmbedding.id
  have hval_smooth : ContMDiff Kk' (ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY)) n
      (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) := by
    rw [hval_eq]
    exact snocD.contMDiff.comp (hprod_emb.contMDiff.comp (hP_emb.contMDiff.comp stepDiff.contMDiff))
  have hval_inj : ∀ y : IteratedFiberProduct π (k + 2),
      Injective (mfderiv Kk' (ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY))
        (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) y) := by
    intro y
    rw [hval_eq]
    have hd1 : MDifferentiableAt Kk' KP stepDiff y := stepDiff.mdifferentiable hn0 y
    have hd2 : MDifferentiableAt KP (Kk.prod IY) (Subtype.val : P → _) (stepDiff y) :=
      hP_emb.contMDiff.mdifferentiable hn0 _
    have hd3 : MDifferentiableAt (Kk.prod IY)
        ((ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY)).prod IY)
        (Prod.map (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y) id)
        (stepDiff y).1 := hprod_emb.contMDiff.mdifferentiable hn0 _
    have hd4 : MDifferentiableAt ((ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY)).prod IY)
        (ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY)) snocD
        ((stepDiff y).1.1.1, (stepDiff y).1.2) :=
      snocD.mdifferentiable hn0 _
    rw [mfderiv_comp y hd4 (hd3.comp y (hd2.comp y hd1)),
      mfderiv_comp y hd3 (hd2.comp y hd1), mfderiv_comp y hd2 hd1,
      ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp,
      ← snocD.mfderivToContinuousLinearEquiv_coe hn0,
      ← stepDiff.mfderivToContinuousLinearEquiv_coe hn0]
    exact (snocD.mfderivToContinuousLinearEquiv hn0 _).injective.comp
      ((hprod_emb.isImmersion.mfderiv_injective hn0 _).comp
        ((hP_emb.isImmersion.mfderiv_injective hn0 _).comp
          (stepDiff.mfderivToContinuousLinearEquiv hn0 y).injective))
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
    have hcoord_d : ∀ i : Fin (k + 2),
        MDifferentiableAt Kk' IY (fun z : IteratedFiberProduct π (k + 2) ↦ z.1 i) y :=
      fun i ↦ mdifferentiableAt_apply.comp y hval_d
    have hcoord_mfderiv : ∀ (i : Fin (k + 2)) (ξ : TangentSpace Kk' y),
        mfderiv Kk' IY (fun z : IteratedFiberProduct π (k + 2) ↦ z.1 i) y ξ =
          (mfderiv Kk' (ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY)) Subtype.val y ξ) i := by
      intro i ξ
      have h := mfderiv_comp (I' := ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY)) y
        (hasMFDerivAt_apply i y.1).mdifferentiableAt hval_d
      rw [mfderiv_apply] at h
      exact congrArg (fun L ↦ L ξ) h
    constructor
    · rintro ⟨ξ, rfl⟩ i j
      rw [ContinuousLinearMap.coe_coe]
      have hfun : (fun z : IteratedFiberProduct π (k + 2) ↦ π (z.1 i)) =
          (fun z ↦ π (z.1 j)) := funext fun z ↦ z.2 i j
      have hπi : mfderiv Kk' IM (fun z : IteratedFiberProduct π (k + 2) ↦ π (z.1 i)) y ξ =
          mfderiv IY IM π (y.1 i)
            ((mfderiv Kk' (ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY)) Subtype.val y ξ) i) := by
        rw [← hcoord_mfderiv i ξ]
        exact congrArg (fun L ↦ L ξ)
          (mfderiv_comp y (hπ.contMDiff.mdifferentiable hn0 _) (hcoord_d i))
      have hπj : mfderiv Kk' IM (fun z : IteratedFiberProduct π (k + 2) ↦ π (z.1 j)) y ξ =
          mfderiv IY IM π (y.1 j)
            ((mfderiv Kk' (ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY)) Subtype.val y ξ) j) := by
        rw [← hcoord_mfderiv j ξ]
        exact congrArg (fun L ↦ L ξ)
          (mfderiv_comp y (hπ.contMDiff.mdifferentiable hn0 _) (hcoord_d j))
      rw [← hπi, ← hπj]
      exact mfderiv_apply_eq_of_eq hfun y ξ
    · intro hv
      let yInit : IteratedFiberProduct π (k + 1) :=
        ⟨Fin.init y.1, fun i j ↦ y.2 i.castSucc j.castSucc⟩
      have hvInit : ∀ i j : Fin (k + 1),
          mfderiv IY IM π (yInit.1 i) (Fin.init v i) =
            tangentSpaceCast IM (π (yInit.1 j)) (π (yInit.1 i))
              (mfderiv IY IM π (yInit.1 j) (Fin.init v j)) :=
        fun i j ↦ hv i.castSucc j.castSucc
      obtain ⟨u₁, hu₁⟩ := (ih.mem_range_mfderiv_coe_iff yInit (Fin.init v)).2 hvInit
      rw [ContinuousLinearMap.coe_coe] at hu₁
      have hinit_d := ih.isSmoothEmbedding_coe.contMDiff.mdifferentiable hn0 yInit
      have hbase_u₁ : mfderiv Kk IM (IteratedFiberProduct.baseProj π) yInit u₁ =
          mfderiv IY IM π (y.1 0) (v 0) := by
        have h0 : (IteratedFiberProduct.baseProj π : IteratedFiberProduct π (k + 1) → M) =
            π ∘ (fun w : Fin (k + 1) → Y ↦ w 0) ∘ Subtype.val := rfl
        rw [h0, mfderiv_comp yInit (hπ.contMDiff.mdifferentiable hn0 _)
            (mdifferentiableAt_apply.comp yInit hinit_d),
          mfderiv_comp yInit mdifferentiableAt_apply hinit_d,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, mfderiv_apply]
        exact congrArg (mfderiv IY IM π (y.1 0)) (congrFun hu₁ 0)
      obtain ⟨η, hη₁, hη₂⟩ := exists_mfderiv_eq_of_transverseFiberProduct hn
        ih.isSubmersion_baseProj.contMDiff hπ.contMDiff htrans (stepDiff y)
        (tangentSpaceCast Kk yInit (stepDiff y).1.1 u₁)
        (tangentSpaceCast IY (y.1 (Fin.last (k + 1))) (stepDiff y).1.2 (v (Fin.last (k + 1))))
        (by
          have heq : stepDiff y = e y := hstepDiff_apply y
          rw [heq]
          exact hbase_u₁.trans (hv 0 (Fin.last (k + 1))))
      let ξ : TangentSpace Kk' y := (stepDiff.mfderivToContinuousLinearEquiv hn0 y).symm η
      have hstepξ : mfderiv Kk' KP stepDiff y ξ = η := by
        rw [← stepDiff.mfderivToContinuousLinearEquiv_coe hn0]
        exact (stepDiff.mfderivToContinuousLinearEquiv hn0 y).apply_symm_apply η
      refine ⟨ξ, ?_⟩
      rw [ContinuousLinearMap.coe_coe]
      funext i
      rw [← hcoord_mfderiv i ξ]
      refine Fin.lastCases ?_ ?_ i
      · have hlast : (fun z : IteratedFiberProduct π (k + 2) ↦ z.1 (Fin.last (k + 1))) =
            (fun q : P ↦ q.1.2) ∘ stepDiff := by
          funext z
          simp [hstepDiff_apply, e, stepHomeomorph]
        have hPd := hP_emb.contMDiff.snd.mdifferentiable hn0 (stepDiff y)
        rw [mfderiv_apply_eq_of_eq hlast y ξ,
          mfderiv_comp y hPd (stepDiff.mdifferentiable hn0 y),
          ContinuousLinearMap.comp_apply, hstepξ, hη₂]
        have heq : stepDiff y = e y := hstepDiff_apply y
        rw [heq]
        rfl
      · intro j
        have hj : (fun z : IteratedFiberProduct π (k + 2) ↦ z.1 j.castSucc) =
            (fun w : Fin (k + 1) → Y ↦ w j) ∘ Subtype.val ∘ (fun q : P ↦ q.1.1) ∘ stepDiff := by
          funext z
          simp [hstepDiff_apply, e, stepHomeomorph, Fin.init]
        have hP1d := hP_emb.contMDiff.fst.mdifferentiable hn0 (stepDiff y)
        have hsd := ih.isSmoothEmbedding_coe.contMDiff.mdifferentiable hn0 (stepDiff y).1.1
        rw [mfderiv_apply_eq_of_eq hj y ξ,
          mfderiv_comp y mdifferentiableAt_apply
            (hsd.comp y (hP1d.comp y (stepDiff.mdifferentiable hn0 y))),
          mfderiv_comp y hsd (hP1d.comp y (stepDiff.mdifferentiable hn0 y)),
          mfderiv_comp y hP1d (stepDiff.mdifferentiable hn0 y),
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.comp_apply, mfderiv_apply, hstepξ, hη₁]
        simp only [Function.comp_apply]
        have heq : (stepDiff y).1.1 = yInit := congrArg (fun q : P ↦ q.1.1) (hstepDiff_apply y)
        generalize (stepDiff y).1.1 = z at heq ⊢
        subst heq
        exact congrFun hu₁ j
  have hbase_smooth : ContMDiff Kk' IM n
      (IteratedFiberProduct.baseProj π : IteratedFiberProduct π (k + 2) → M) :=
    hπ.contMDiff.comp (contMDiff_apply.comp hval_smooth)
  have hsubm : Manifold.IsSubmersion Kk' IM n
      (IteratedFiberProduct.baseProj π : IteratedFiberProduct π (k + 2) → M) := by
    refine (hbase_smooth.isSubmersionOfComplement_of_surjective_mfderiv hn
      fun y w ↦ ?_).isSubmersion
    have hex : ∀ i : Fin (k + 2), ∃ vi : TangentSpace IY (y.1 i),
        mfderiv IY IM π (y.1 i) vi =
          tangentSpaceCast IM (IteratedFiberProduct.baseProj π y) (π (y.1 i)) w :=
      fun i ↦ hπ.surjective_mfderiv hn0 (y.1 i) _
    let v : TangentSpace (ModelWithCorners.pi (fun _ : Fin (k + 2) ↦ IY)) y.1 :=
      fun i ↦ (hex i).choose
    have hv : ∀ i, mfderiv IY IM π (y.1 i) (v i) =
        tangentSpaceCast IM (IteratedFiberProduct.baseProj π y) (π (y.1 i)) w :=
      fun i ↦ (hex i).choose_spec
    obtain ⟨ξ, hξ⟩ := (hrange y v).2 fun i j ↦ by
      rw [hv i, hv j]
      rfl
    rw [ContinuousLinearMap.coe_coe] at hξ
    refine ⟨ξ, ?_⟩
    have h0 : (IteratedFiberProduct.baseProj π : IteratedFiberProduct π (k + 2) → M) =
        π ∘ (fun z : Fin (k + 2) → Y ↦ z 0) ∘ Subtype.val := rfl
    rw [h0, mfderiv_comp y (hπ.contMDiff.mdifferentiable hn0 _)
        (mdifferentiableAt_apply.comp y (hval_smooth.mdifferentiable hn0 y)),
      mfderiv_comp y mdifferentiableAt_apply (hval_smooth.mdifferentiable hn0 y),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, mfderiv_apply]
    exact (congrArg (mfderiv IY IM π (y.1 0)) (congrFun hξ 0)).trans (hv 0)
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
  have hval := (isSmoothEmbedding_coe_iteratedFiberProduct hn hπ k).contMDiff.mdifferentiable hn0 y
  have hcomp := mfderiv_comp (I' := ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY)) y
    (hasMFDerivAt_apply i y.1).mdifferentiableAt hval
  rw [mfderiv_apply] at hcomp
  exact congrArg (fun L ↦ L ξ) hcomp

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
      tangentSpaceCast IM (π (y.1 i)) (π (y.1 j)) (mfderiv IY IM π (y.1 i) u) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp [v]
      rfl
    · simp [v, hji, (hex j).choose_spec]
  obtain ⟨ξ, hξ⟩ := exists_mfderiv_proj_eq_of_iteratedFiberProduct hn hπ k y v fun j₁ j₂ ↦ by
    rw [hv j₁, hv j₂]
    rfl
  refine ⟨ξ, ?_⟩
  exact (hξ i).trans (by simp [v]; rfl)

/-- The base projection `Y^[k+1] → M` is `C^n`. -/
theorem contMDiff_baseProj_iteratedFiberProduct (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ContMDiff 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IM n
      (IteratedFiberProduct.baseProj π : IteratedFiberProduct π (k + 1) → M) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  exact (iteratedFiberProductData hn hπ k).isSubmersion_baseProj.contMDiff

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
  exact (contMDiff_iteratedFiberProduct_iff hn hπ l).2 fun j ↦
    contMDiff_proj_iteratedFiberProduct hn hπ k (f j)

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
    if hi : i ∈ range f then
      tangentSpaceCast IY (z.1 hi.choose) (y.1 i) (u hi.choose)
    else (hex i).choose
  have hv_apply : ∀ j : Fin (l + 1), v (f j) = u j := by
    intro j
    have hi : f j ∈ range f := ⟨j, rfl⟩
    have hj : hi.choose = j := hf hi.choose_spec
    simp only [v, hi, ↓reduceDIte, hj]
    rfl
  have hv_match : ∀ i : Fin (k + 1),
      mfderiv IY IM π (y.1 i) (v i) =
        tangentSpaceCast IM (π (z.1 0)) (π (y.1 i)) (mfderiv IY IM π (z.1 0) (u 0)) := by
    intro i
    by_cases hi : i ∈ range f
    · obtain ⟨j, rfl⟩ := hi
      rw [hv_apply j]
      exact hu j 0
    · simp only [v, hi, ↓reduceDIte]
      exact (hex i).choose_spec
  obtain ⟨ξ, hξ⟩ := exists_mfderiv_proj_eq_of_iteratedFiberProduct hn hπ k y v fun i₁ i₂ ↦ by
    rw [hv_match i₁, hv_match i₂]
    rfl
  refine ⟨ξ, ?_⟩
  have hsub : mfderiv Kk Kl (IteratedFiberProduct.reindex π f) y ξ - ζ = 0 := by
    refine eq_zero_of_mfderiv_proj_iteratedFiberProduct hn hπ l z _ fun j ↦ ?_
    rw [map_sub, sub_eq_zero]
    have hcomp_l := mfderiv_comp y
      ((contMDiff_proj_iteratedFiberProduct hn hπ l j).mdifferentiable hn0 z)
      (hrf.mdifferentiable hn0 y)
    have hcomp_eq : IteratedFiberProduct.proj π j ∘ IteratedFiberProduct.reindex π f =
        IteratedFiberProduct.proj π (f j) := rfl
    rw [hcomp_eq] at hcomp_l
    have hlhs : mfderiv Kl IY (IteratedFiberProduct.proj π j) z
        (mfderiv Kk Kl (IteratedFiberProduct.reindex π f) y ξ) = v (f j) :=
      (congrArg (fun L ↦ L ξ) hcomp_l).symm.trans (hξ (f j))
    have hrhs : mfderiv Kl IY (IteratedFiberProduct.proj π j) z ζ = u j :=
      mfderiv_proj_iteratedFiberProduct hn hπ l j z ζ
    rw [hlhs, hrhs, hv_apply j]
  exact sub_eq_zero.1 hsub

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
    fun y ↦ IteratedFiberProduct.ext π fun i ↦ congrArg y.1 (surjInv_eq hf i)
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
    left_inv := fun y ↦ IteratedFiberProduct.ext π fun i ↦ congrArg y.1 (e.apply_symm_apply i)
    right_inv := fun y ↦ IteratedFiberProduct.ext π fun i ↦ congrArg y.1 (e.symm_apply_apply i)
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
  contMDiff_reindex_iteratedFiberProduct hn hπ i.succAbove

/-- Every simplicial face map `Y^[k+2] → Y^[k+1]` is a `C^n` submersion. -/
theorem isSubmersion_face_iteratedFiberProduct {k : ℕ} (i : Fin (k + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    letI := iteratedFiberProductChartedSpace hn hπ k
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.face π i) :=
  isSubmersion_reindex_iteratedFiberProduct hn hπ Fin.succAbove_right_injective

/-- Every simplicial degeneracy map `Y^[k+1] → Y^[k+2]` is `C^n`. -/
theorem contMDiff_degen_iteratedFiberProduct {k : ℕ} (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    ContMDiff
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.degen π i) :=
  contMDiff_reindex_iteratedFiberProduct hn hπ i.predAbove

/-- Every simplicial degeneracy map `Y^[k+1] → Y^[k+2]` is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_degen_iteratedFiberProduct {k : ℕ} (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.degen π i) :=
  isSmoothEmbedding_reindex_iteratedFiberProduct hn hπ (Fin.predAbove_surjective i)

/-- The diagonal map `Y → Y^[k+1]` is `C^n`. -/
theorem contMDiff_diag_iteratedFiberProduct (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ContMDiff IY 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.diag π (k + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  exact (contMDiff_iteratedFiberProduct_iff hn hπ k).2 fun _ ↦ contMDiff_id

/-- The diagonal map `Y → Y^[k+1]` is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_diag_iteratedFiberProduct (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    Manifold.IsSmoothEmbedding IY 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.diag π (k + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  have := isManifold_iteratedFiberProduct hn hπ k
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine ⟨(contMDiff_diag_iteratedFiberProduct hn hπ k).isImmersion_of_leftInverse hn
    (fun _ ↦ (contMDiff_proj_iteratedFiberProduct hn hπ k 0).mdifferentiable hn0 _)
    (IteratedFiberProduct.proj_diag π 0),
    IteratedFiberProduct.isEmbedding_diag π k⟩

/-! ### Canonical comparisons and independence of the order of iteration -/

/-- Canonical `C^n` diffeomorphism `Y^[1] ≃ₘ^n Y`, given by the unique coordinate projection with
inverse the diagonal. -/
noncomputable def iteratedFiberProductOneDiffeomorph :
    letI := iteratedFiberProductChartedSpace hn hπ 0
    IteratedFiberProduct π 1 ≃ₘ^n⟮
      𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ), IY⟯ Y :=
  letI := iteratedFiberProductChartedSpace hn hπ 0
  { toFun := IteratedFiberProduct.proj π 0
    invFun := IteratedFiberProduct.diag π 1
    left_inv := fun y ↦ IteratedFiberProduct.ext π fun i ↦ congrArg y.1 (Subsingleton.elim 0 i)
    right_inv := fun _ ↦ rfl
    contMDiff_toFun := contMDiff_proj_iteratedFiberProduct hn hπ 0 0
    contMDiff_invFun := contMDiff_diag_iteratedFiberProduct hn hπ 0 }

/-- The comparison `Y^[1] ≃ₘ^n Y` evaluates at coordinate `0`. -/
@[simp]
theorem iteratedFiberProductOneDiffeomorph_apply (y : IteratedFiberProduct π 1) :
    iteratedFiberProductOneDiffeomorph hn hπ y = y.1 0 :=
  (rfl)

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
    invFun := fun p ↦ ⟨![p.1.1, p.1.2], fun i j ↦ by
      fin_cases i <;> fin_cases j <;> simp [p.2]⟩
    left_inv := fun y ↦ IteratedFiberProduct.ext π fun i ↦ by fin_cases i <;> rfl
    right_inv := fun _ ↦ rfl
    contMDiff_toFun := hP.contMDiff_iff_comp.2
      ((contMDiff_proj_iteratedFiberProduct hn hπ 1 0).prodMk
        (contMDiff_proj_iteratedFiberProduct hn hπ 1 1))
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
  let htrans := fun (p : IteratedFiberProduct π (k + 1) × Y)
    (_ : IteratedFiberProduct.baseProj π p.1 = π p.2) ↦
    transverse_of_isSubmersion_right
      (IX := 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ))
      (IteratedFiberProduct.baseProj π) hn hπ p
  letI := transverseFiberProductChartedSpace hn
    (contMDiff_baseProj_iteratedFiberProduct hn hπ k) hπ.contMDiff htrans
  have hP := isSmoothEmbedding_coe_transverseFiberProduct hn
    (contMDiff_baseProj_iteratedFiberProduct hn hπ k) hπ.contMDiff htrans
  { toFun := stepHomeomorph π k
    invFun := (stepHomeomorph π k).symm
    left_inv := (stepHomeomorph π k).left_inv
    right_inv := (stepHomeomorph π k).right_inv
    contMDiff_toFun := hP.contMDiff_iff_comp.2
      ((contMDiff_reindex_iteratedFiberProduct hn hπ
          (Fin.castSucc : Fin (k + 1) → Fin (k + 2))).prodMk
        (contMDiff_proj_iteratedFiberProduct hn hπ (k + 1) (Fin.last (k + 1))))
    contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ (k + 1)).2 fun i ↦ by
      refine Fin.lastCases
        (motive := fun i ↦ ContMDiff
          𝓘(ℝ, Fin (finrank ℝ (Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) +
            finrank ℝ EY - finrank ℝ EM) → ℝ) IY n
          (fun p : {p : IteratedFiberProduct π (k + 1) × Y //
            IteratedFiberProduct.baseProj π p.1 = π p.2} ↦
            Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 i)) ?_ ?_ i
      · simp only [Fin.snoc_last]
        exact hP.contMDiff.snd
      · intro j
        simp only [Fin.snoc_castSucc]
        exact (contMDiff_proj_iteratedFiberProduct hn hπ k j).comp hP.contMDiff.fst }

/-- The step comparison splits off the last coordinate of a `(k + 2)`-tuple. -/
@[simp]
theorem iteratedFiberProductStepDiffeomorph_apply (k : ℕ) (y : IteratedFiberProduct π (k + 2)) :
    (iteratedFiberProductStepDiffeomorph hn hπ k y).1 =
      (⟨Fin.init y.1, fun i j ↦ y.2 i.castSucc j.castSucc⟩, y.1 (Fin.last (k + 1))) :=
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
  let htrans := fun (p : IteratedFiberProduct π (a + 1) × IteratedFiberProduct π (b + 1))
    (_ : IteratedFiberProduct.baseProj π p.1 = IteratedFiberProduct.baseProj π p.2) ↦
    transverse_of_isSubmersion_right
      (IX := 𝓘(ℝ, Fin ((a + 1) * finrank ℝ EY - a * finrank ℝ EM) → ℝ))
      (IteratedFiberProduct.baseProj π) hn
      (isSubmersion_baseProj_iteratedFiberProduct hn hπ b) p
  letI := transverseFiberProductChartedSpace hn
    (contMDiff_baseProj_iteratedFiberProduct hn hπ a)
    (contMDiff_baseProj_iteratedFiberProduct hn hπ b) htrans
  have hP := isSmoothEmbedding_coe_transverseFiberProduct hn
    (contMDiff_baseProj_iteratedFiberProduct hn hπ a)
    (contMDiff_baseProj_iteratedFiberProduct hn hπ b) htrans
  { toFun := fun y ↦
      ⟨(IteratedFiberProduct.reindex π (Fin.castAdd (b + 1)) y,
        IteratedFiberProduct.reindex π (Fin.natAdd (a + 1)) y),
        y.2 _ _⟩
    invFun := fun p ↦ ⟨Fin.addCases p.1.1.1 p.1.2.1, by
      have hbase : ∀ i : Fin ((a + 1) + (b + 1)),
          π (Fin.addCases (motive := fun _ ↦ Y) p.1.1.1 p.1.2.1 i) =
            IteratedFiberProduct.baseProj π p.1.1 := by
        intro i
        refine Fin.addCases ?_ ?_ i
        · intro j
          rw [Fin.addCases_left]
          exact p.1.1.2 j 0
        · intro j
          rw [Fin.addCases_right]
          exact (p.1.2.2 j 0).trans p.2.symm
      intro i j
      rw [hbase i, hbase j]⟩
    left_inv := fun y ↦ IteratedFiberProduct.ext π fun i ↦ by
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp
      · intro j
        simp
    right_inv := fun p ↦ by
      apply Subtype.ext
      refine Prod.ext (IteratedFiberProduct.ext π fun j ↦ ?_)
        (IteratedFiberProduct.ext π fun j ↦ ?_)
      · simp
      · simp
    contMDiff_toFun := hP.contMDiff_iff_comp.2
      ((contMDiff_reindex_iteratedFiberProduct hn hπ
          (Fin.castAdd (b + 1) : Fin (a + 1) → Fin ((a + 1) + (b + 1)))).prodMk
        (contMDiff_reindex_iteratedFiberProduct hn hπ
          (Fin.natAdd (a + 1) : Fin (b + 1) → Fin ((a + 1) + (b + 1)))))
    contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ ((a + 1) + b)).2 fun i ↦ by
      refine Fin.addCases
        (motive := fun i ↦ ContMDiff
          𝓘(ℝ, Fin (finrank ℝ (Fin ((a + 1) * finrank ℝ EY - a * finrank ℝ EM) → ℝ) +
            finrank ℝ (Fin ((b + 1) * finrank ℝ EY - b * finrank ℝ EM) → ℝ) - finrank ℝ EM) → ℝ)
          IY n
          (fun p : {p : IteratedFiberProduct π (a + 1) × IteratedFiberProduct π (b + 1) //
            IteratedFiberProduct.baseProj π p.1 = IteratedFiberProduct.baseProj π p.2} ↦
            Fin.addCases (motive := fun _ ↦ Y) p.1.1.1 p.1.2.1 i)) ?_ ?_ i
      · intro j
        simp only [Fin.addCases_left]
        exact (contMDiff_proj_iteratedFiberProduct hn hπ a j).comp hP.contMDiff.fst
      · intro j
        simp only [Fin.addCases_right]
        exact (contMDiff_proj_iteratedFiberProduct hn hπ b j).comp hP.contMDiff.snd }

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
