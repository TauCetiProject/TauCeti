/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Iterated.Basic
public import TauCeti.Geometry.Manifold.FiberProduct.Submersion
public import TauCeti.Geometry.Manifold.IsManifold.Pi
import TauCeti.Geometry.Manifold.FiberProduct.Identity
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.MFDeriv.Pi
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse

/-!
# Manifold structure on iterated fibre products of a submersion

For a `C^n` submersion `π : Y → M` (`1 ≤ n`) between finite-dimensional boundaryless manifolds,
each nonempty-index iterated fibre product `Y^[k + 1] := TauCeti.IteratedFiberProduct π (k + 1)`
carries an embedded `C^n` manifold structure `TauCeti.iteratedFiberProductChartedSpace` with its
subspace topology and model dimension `(k + 1) * dim Y - k * dim M`.

The atlas is built recursively by applying `TauCeti.transverseFiberProductChartedSpace` at each
step to `baseProj : Y^[k + 1] → M` and `π : Y → M`, and pulling back along the canonical
homeomorphism `TauCeti.iteratedFiberProductSuccHomeomorph`. Its tangent space at `y` consists of
all tuples `(v_0, …, v_k)` of tangent vectors of `Y` with equal images under `dπ`
(`TauCeti.mem_range_mfderiv_coe_iteratedFiberProduct_iff`), and maps into `Y^[k + 1]` are `C^n`
iff all coordinate maps are `C^n` (`TauCeti.contMDiff_iteratedFiberProduct_iff`).

No Hausdorff, countability, nonemptiness, or surjectivity hypotheses are required.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013),
  Theorem 4.26 (submersion theorem) and Theorem 6.30 (transverse fibre products).
* M. K. Murray, *Bundle gerbes*, J. London Math. Soc. (2) 54 (1996), 403–416.
-/

public section

open Function Set Module Topology
open scoped Manifold ContDiff

namespace TauCeti

/-- The canonical homeomorphism between `Y^[1]` and the diagonal
`{p : Y × Y // id p.1 = id p.2}`. -/
private def iteratedFiberProductOneHomeomorph {Y M : Type*} {π : Y → M} [TopologicalSpace Y] :
    IteratedFiberProduct π 1 ≃ₜ {p : Y × Y // id p.1 = id p.2} where
  toFun y := ⟨(y.coord 0, y.coord 0), rfl⟩
  invFun p := IteratedFiberProduct.diag 1 p.1.1
  left_inv y := Subtype.ext (funext fun i ↦ by rw [Subsingleton.elim i 0]; simp)
  right_inv p := Subtype.ext (Prod.ext (by simp)
    (by simp only [IteratedFiberProduct.coord_apply, IteratedFiberProduct.coe_diag]; exact p.2))
  continuous_toFun :=
    ((IteratedFiberProduct.continuous_coord 0).prodMk
      (IteratedFiberProduct.continuous_coord 0)).subtype_mk _
  continuous_invFun :=
    (IteratedFiberProduct.continuous_diag 1).comp (continuous_fst.comp continuous_subtype_val)

section ManifoldHelpers

variable {EY HY Y M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  {IY : ModelWithCorners ℝ EY HY}
  [TopologicalSpace Y] [ChartedSpace HY Y]
  {n : ℕ∞ω} {π : Y → M}

/-- Smoothness of `Subtype.val : Y^[k + 2] → (Fin (k + 2) → Y)` for the pulled-back atlas. -/
private theorem contMDiff_val_succ (k dk d : ℕ)
    [ChartedSpace (Fin dk → ℝ) (IteratedFiberProduct π (k + 1))]
    [ChartedSpace (Fin d → ℝ)
      {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2}]
    (hemb_k : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin dk → ℝ)
      (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y))
    (hembQ : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin dk → ℝ).prod IY) n
      (Subtype.val : {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2} →
        IteratedFiberProduct π (k + 1) × Y)) :
    let e := iteratedFiberProductSuccHomeomorph (π := π) k
    letI := e.pullbackChartedSpace (H := Fin d → ℝ)
    ContMDiff 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 2) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) := by
  let e := iteratedFiberProductSuccHomeomorph (π := π) k
  let := e.pullbackChartedSpace (H := Fin d → ℝ)
  let Φ := e.pullbackDiffeomorph 𝓘(ℝ, Fin d → ℝ) n
  have hΦ : ⇑Φ = e := e.coe_pullbackDiffeomorph 𝓘(ℝ, Fin d → ℝ) n
  refine contMDiff_pi_iff.2 fun i ↦ Fin.lastCases ?_ (fun i' ↦ ?_) i
  · exact (contMDiff_snd.comp (hembQ.contMDiff.comp Φ.contMDiff)).congr fun z ↦ by
      simp [hΦ, e]
  · exact ((contMDiff_apply (i := i')).comp
      (hemb_k.contMDiff.comp (contMDiff_fst.comp (hembQ.contMDiff.comp Φ.contMDiff)))).congr
      fun z ↦ by simp [hΦ, e]

/-- Differential of the initial `k + 1` coordinates of `Subtype.val` on `Y^[k + 2]`. -/
private theorem mfderiv_succ_castSucc (hn : 1 ≤ n) (k dk d : ℕ)
    [ChartedSpace (Fin dk → ℝ) (IteratedFiberProduct π (k + 1))]
    [ChartedSpace (Fin d → ℝ)
      {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2}]
    (hemb_k : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin dk → ℝ)
      (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y))
    (hembQ : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin dk → ℝ).prod IY) n
      (Subtype.val : {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2} →
        IteratedFiberProduct π (k + 1) × Y)) :
    let e := iteratedFiberProductSuccHomeomorph (π := π) k
    letI := e.pullbackChartedSpace (H := Fin d → ℝ)
    let Φ := e.pullbackDiffeomorph 𝓘(ℝ, Fin d → ℝ) n
    ∀ (y : IteratedFiberProduct π (k + 2)) (i' : Fin (k + 1))
      (ξ : TangentSpace 𝓘(ℝ, Fin d → ℝ) y),
      (mfderiv 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 2) ↦ IY)
          (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) y ξ) i'.castSucc =
        (mfderiv 𝓘(ℝ, Fin dk → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
          (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y) (Φ y).1.1
          ((mfderiv 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin dk → ℝ).prod IY) Subtype.val (Φ y)
            (mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) Φ y ξ)).1)) i' := by
  let Q := {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2}
  let Kk := 𝓘(ℝ, Fin dk → ℝ)
  let K := 𝓘(ℝ, Fin d → ℝ)
  let e := iteratedFiberProductSuccHomeomorph (π := π) k
  let := e.pullbackChartedSpace (H := Fin d → ℝ)
  let Φ : IteratedFiberProduct π (k + 2) ≃ₘ^n⟮K, K⟯ Q := e.pullbackDiffeomorph K n
  have hΦ : ⇑Φ = e := e.coe_pullbackDiffeomorph K n
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hval := contMDiff_val_succ k dk d hemb_k hembQ
  dsimp only
  intro y i' ξ
  have hpi : (mfderiv K (ModelWithCorners.pi fun _ : Fin (k + 2) ↦ IY)
        (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) y ξ) i'.castSucc =
      mfderiv K IY (fun z : IteratedFiberProduct π (k + 2) ↦ z.1 i'.castSucc) y ξ :=
    congrFun (DFunLike.congr_fun
      (mfderiv_pi (mdifferentiableAt_pi_iff.1 ((hval y).mdifferentiableAt hn0))) ξ) i'.castSucc
  rw [hpi]
  have hΦd := (Φ.contMDiff y).mdifferentiableAt hn0
  have hQd := (hembQ.contMDiff (Φ y)).mdifferentiableAt hn0
  have hkd := (hemb_k.contMDiff (Φ y).1.1).mdifferentiableAt hn0
  have hfstd : MDifferentiableAt K Kk (Prod.fst ∘ (Subtype.val : Q → _)) (Φ y) :=
    mdifferentiableAt_fst.comp (Φ y) hQd
  have hcd : MDifferentiableAt Kk IY
      ((fun f : Fin (k + 1) → Y ↦ f i') ∘ Subtype.val) (Φ y).1.1 :=
    (hasMFDerivAt_apply i' (Φ y).1.1.1).mdifferentiableAt.comp (Φ y).1.1 hkd
  have hcomp : (fun z : IteratedFiberProduct π (k + 2) ↦ z.1 i'.castSucc) =
      ((fun f : Fin (k + 1) → Y ↦ f i') ∘ Subtype.val) ∘
        (Prod.fst ∘ (Subtype.val : Q → _)) ∘ Φ :=
    funext fun z ↦ by simp [hΦ, e]
  have hstep : mfderiv K IY (fun z : IteratedFiberProduct π (k + 2) ↦ z.1 i'.castSucc) y ξ =
      mfderiv K IY (((fun f : Fin (k + 1) → Y ↦ f i') ∘ Subtype.val) ∘
        (Prod.fst ∘ (Subtype.val : Q → _)) ∘ Φ) y ξ :=
    congrArg (fun g ↦ (mfderiv K IY g y ξ : EY)) hcomp
  rw [hstep, mfderiv_comp y hcd (hfstd.comp y hΦd), mfderiv_comp y hfstd hΦd,
    mfderiv_comp (Φ y) mdifferentiableAt_fst hQd]
  dsimp only [Function.comp_apply]
  rw [mfderiv_comp (Φ y).1.1 (hasMFDerivAt_apply i' (Φ y).1.1.1).mdifferentiableAt hkd,
    mfderiv_fst, mfderiv_apply]
  rfl

/-- Differential of the last coordinate of `Subtype.val` on `Y^[k + 2]`. -/
private theorem mfderiv_succ_last (hn : 1 ≤ n) (k dk d : ℕ)
    [ChartedSpace (Fin dk → ℝ) (IteratedFiberProduct π (k + 1))]
    [ChartedSpace (Fin d → ℝ)
      {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2}]
    (hemb_k : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin dk → ℝ)
      (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y))
    (hembQ : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin dk → ℝ).prod IY) n
      (Subtype.val : {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2} →
        IteratedFiberProduct π (k + 1) × Y)) :
    let e := iteratedFiberProductSuccHomeomorph (π := π) k
    letI := e.pullbackChartedSpace (H := Fin d → ℝ)
    let Φ := e.pullbackDiffeomorph 𝓘(ℝ, Fin d → ℝ) n
    ∀ (y : IteratedFiberProduct π (k + 2)) (ξ : TangentSpace 𝓘(ℝ, Fin d → ℝ) y),
      (mfderiv 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 2) ↦ IY)
          (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) y ξ)
          (Fin.last (k + 1)) =
        (mfderiv 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin dk → ℝ).prod IY) Subtype.val (Φ y)
          (mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) Φ y ξ)).2 := by
  let Q := {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2}
  let K := 𝓘(ℝ, Fin d → ℝ)
  let e := iteratedFiberProductSuccHomeomorph (π := π) k
  let := e.pullbackChartedSpace (H := Fin d → ℝ)
  let Φ : IteratedFiberProduct π (k + 2) ≃ₘ^n⟮K, K⟯ Q := e.pullbackDiffeomorph K n
  have hΦ : ⇑Φ = e := e.coe_pullbackDiffeomorph K n
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hval := contMDiff_val_succ k dk d hemb_k hembQ
  dsimp only
  intro y ξ
  have hpi : (mfderiv K (ModelWithCorners.pi fun _ : Fin (k + 2) ↦ IY)
        (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) y ξ) (Fin.last (k + 1)) =
      mfderiv K IY (fun z : IteratedFiberProduct π (k + 2) ↦ z.1 (Fin.last (k + 1))) y ξ :=
    congrFun (DFunLike.congr_fun
      (mfderiv_pi (mdifferentiableAt_pi_iff.1 ((hval y).mdifferentiableAt hn0))) ξ)
      (Fin.last (k + 1))
  rw [hpi]
  have hΦd := (Φ.contMDiff y).mdifferentiableAt hn0
  have hQd := (hembQ.contMDiff (Φ y)).mdifferentiableAt hn0
  have hcomp : (fun z : IteratedFiberProduct π (k + 2) ↦ z.1 (Fin.last (k + 1))) =
      Prod.snd ∘ (Subtype.val : Q → _) ∘ Φ :=
    funext fun z ↦ by simp [hΦ, e]
  have hstep :
      mfderiv K IY (fun z : IteratedFiberProduct π (k + 2) ↦ z.1 (Fin.last (k + 1))) y ξ =
        mfderiv K IY (Prod.snd ∘ (Subtype.val : Q → _) ∘ Φ) y ξ :=
    congrArg (fun g ↦ (mfderiv K IY g y ξ : EY)) hcomp
  rw [hstep, mfderiv_comp y mdifferentiableAt_snd (hQd.comp y hΦd),
    mfderiv_comp y hQd hΦd, mfderiv_snd]
  rfl

/-- Inductive step for `IsSmoothEmbedding` of `Subtype.val : Y^[k + 2] → (Fin (k + 2) → Y)`. -/
private theorem isSmoothEmbedding_succ [IsManifold IY n Y] [IY.Boundaryless]
    [FiniteDimensional ℝ EY] (hn : 1 ≤ n) (k dk d : ℕ)
    [ChartedSpace (Fin dk → ℝ) (IteratedFiberProduct π (k + 1))]
    [ChartedSpace (Fin d → ℝ)
      {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2}]
    [IsManifold 𝓘(ℝ, Fin d → ℝ) n
      {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2}]
    (hemb_k : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin dk → ℝ)
      (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y))
    (hembQ : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin dk → ℝ).prod IY) n
      (Subtype.val : {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2} →
        IteratedFiberProduct π (k + 1) × Y)) :
    let e := iteratedFiberProductSuccHomeomorph (π := π) k
    letI := e.pullbackChartedSpace (H := Fin d → ℝ)
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 2) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) := by
  let Q := {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2}
  let Kk := 𝓘(ℝ, Fin dk → ℝ)
  let K := 𝓘(ℝ, Fin d → ℝ)
  let e := iteratedFiberProductSuccHomeomorph (π := π) k
  let := e.pullbackChartedSpace (H := Fin d → ℝ)
  have := e.pullback_isManifold K n
  let Φ : IteratedFiberProduct π (k + 2) ≃ₘ^n⟮K, K⟯ Q := e.pullbackDiffeomorph K n
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hval := contMDiff_val_succ k dk d hemb_k hembQ
  have hderiv_cast := mfderiv_succ_castSucc hn k dk d hemb_k hembQ
  have hderiv_last := mfderiv_succ_last hn k dk d hemb_k hembQ
  refine ⟨hval.isImmersion_of_injective_mfderiv hn fun y ↦ ?_, IsEmbedding.subtypeVal⟩
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  have h1 : (mfderiv K (Kk.prod IY) (Subtype.val : Q → _) (Φ y) (mfderiv K K Φ y ξ)).1 = 0 :=
    (injective_iff_map_eq_zero _).1
      ((hemb_k.isImmersion.isImmersionAt (Φ y).1.1).mfderiv_injective hn0) _
      (funext fun i' ↦ by rw [← hderiv_cast y i' ξ, hξ]; rfl)
  have h2 : (mfderiv K (Kk.prod IY) (Subtype.val : Q → _) (Φ y) (mfderiv K K Φ y ξ)).2 = 0 := by
    rw [← hderiv_last y ξ, hξ]; rfl
  have hQ0 : mfderiv K K Φ y ξ = 0 :=
    (injective_iff_map_eq_zero _).1 ((hembQ.isImmersion.isImmersionAt (Φ y)).mfderiv_injective hn0)
      _ (Prod.ext h1 h2)
  have hΦinj : Injective (mfderiv K K Φ y) := by
    rw [← Φ.mfderivToContinuousLinearEquiv_coe hn0]
    exact (Φ.mfderivToContinuousLinearEquiv hn0 y).injective
  exact (injective_iff_map_eq_zero _).1 hΦinj ξ hQ0

end ManifoldHelpers

section Manifold

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} {π : Y → M}

/-- For a nonempty domain `Y`, a submersion `π : Y → M` satisfies `dim M ≤ dim Y`, so the
model dimension `(k + 1) * dim Y - k * dim M` of `Y^[k + 1]` has no natural-number truncation. -/
theorem finrank_iteratedFiberProduct_add [FiniteDimensional ℝ EY] [Nonempty Y]
    (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π) (k : ℕ) :
    ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) + k * finrank ℝ EM = (k + 1) * finrank ℝ EY := by
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have hle : finrank ℝ EM ≤ finrank ℝ EY :=
    LinearMap.finrank_le_finrank_of_surjective
      (hπ.surjective_mfderiv (ne_of_gt (zero_lt_one.trans_le hn)) y₀)
  exact Nat.sub_add_cancel (by nlinarith)

/-- Base case (`k = 0`) of the recursive manifold structure on `Y^[k + 1]`. -/
private theorem exists_isManifold_iteratedFiberProduct_zero [IsManifold IY n Y] [IY.Boundaryless]
    [FiniteDimensional ℝ EY] (hn : 1 ≤ n) :
    ∃ cs : ChartedSpace (Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ)
        (IteratedFiberProduct π 1),
      letI := cs
      IsManifold 𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ) n
        (IteratedFiberProduct π 1) ∧
      Manifold.IsSmoothEmbedding
        𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi fun _ : Fin 1 ↦ IY) n
        (Subtype.val : IteratedFiberProduct π 1 → Fin 1 → Y) ∧
      ∀ (y : IteratedFiberProduct π 1)
        (v : TangentSpace (ModelWithCorners.pi fun _ : Fin 1 ↦ IY) y.1),
        v ∈ (mfderiv
          𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ)
          (ModelWithCorners.pi fun _ : Fin 1 ↦ IY)
          (Subtype.val : IteratedFiberProduct π 1 → Fin 1 → Y) y).range ↔
        ∀ i j : Fin 1,
          mfderiv IY IM π (y.1 i) (v i) =
            tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j)) := by
  have hdim : finrank ℝ EY + finrank ℝ EY - finrank ℝ EY =
      (0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM := by omega
  rw [← hdim]
  let d := finrank ℝ EY + finrank ℝ EY - finrank ℝ EY
  let K := 𝓘(ℝ, Fin d → ℝ)
  let := transverseFiberProductChartedSpace hn (contMDiff_id (I := IY) (M := Y))
    (contMDiff_id (I := IY) (M := Y)) (fun p _ ↦ transverse_id_right id p)
  have := isManifold_transverseFiberProduct hn (contMDiff_id (I := IY) (M := Y))
    (contMDiff_id (I := IY) (M := Y)) (fun p _ ↦ transverse_id_right id p)
  let e := iteratedFiberProductOneHomeomorph (π := π)
  let := e.pullbackChartedSpace (H := Fin d → ℝ)
  have := e.pullback_isManifold K n
  let ψ : IteratedFiberProduct π 1 ≃ₘ^n⟮K, IY⟯ Y :=
    (e.pullbackDiffeomorph K n).trans
      (transverseFiberProductIdRightDiffeomorph hn (contMDiff_id (I := IY) (M := Y)))
  have hψ : ∀ y : IteratedFiberProduct π 1, ψ y = y.1 0 := fun y ↦ by
    rw [Diffeomorph.coe_trans, Function.comp_apply,
      transverseFiberProductIdRightDiffeomorph_apply,
      congrFun (e.coe_pullbackDiffeomorph K n) y]
    exact IteratedFiberProduct.coord_apply 0 y
  let r : (Fin 1 → Y) → IteratedFiberProduct π 1 := fun f ↦ ψ.symm (f 0)
  have hval : ContMDiff K (ModelWithCorners.pi fun _ : Fin 1 ↦ IY) n
      (Subtype.val : IteratedFiberProduct π 1 → Fin 1 → Y) :=
    contMDiff_pi_iff.2 fun i ↦ ψ.contMDiff.congr fun y ↦ by rw [Subsingleton.elim i 0, hψ y]
  have hr : ContMDiff (ModelWithCorners.pi fun _ : Fin 1 ↦ IY) K n r :=
    ψ.symm.contMDiff.comp contMDiff_apply
  have hleft : LeftInverse r (Subtype.val : IteratedFiberProduct π 1 → Fin 1 → Y) := fun y ↦ by
    simpa only [r, ← hψ y] using ψ.symm_apply_apply y
  have hright : RightInverse r (Subtype.val : IteratedFiberProduct π 1 → Fin 1 → Y) := fun f ↦ by
    funext i; rw [Subsingleton.elim i 0, ← hψ (r f)]; exact ψ.apply_symm_apply (f 0)
  refine ⟨inferInstance, inferInstance,
    hval.isSmoothEmbedding_of_leftInverse hn (hr.of_le hn) hleft,
    fun y v ↦ ⟨fun _ i j ↦ by rw [Subsingleton.elim i j]; rfl, fun _ ↦ ?_⟩⟩
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hd := mfderiv_comp (I := ModelWithCorners.pi fun _ : Fin 1 ↦ IY) (I' := K)
    (I'' := ModelWithCorners.pi fun _ : Fin 1 ↦ IY) y.1
    (by simpa only [hleft y] using (hval y).mdifferentiableAt hn0) ((hr y.1).mdifferentiableAt hn0)
  have hcomp : (Subtype.val : IteratedFiberProduct π 1 → Fin 1 → Y) ∘ r = id := funext hright
  rw [hcomp, mfderiv_id] at hd
  refine ⟨mfderiv (ModelWithCorners.pi fun _ : Fin 1 ↦ IY) K r y.1 v, ?_⟩
  have hdv : mfderiv K (ModelWithCorners.pi fun _ : Fin 1 ↦ IY) Subtype.val (r y.1)
      (mfderiv (ModelWithCorners.pi fun _ : Fin 1 ↦ IY) K r y.1 v) = v :=
    (DFunLike.congr_fun hd v).symm
  rw [ContinuousLinearMap.coe_coe]
  exact (congrArg (fun z : IteratedFiberProduct π 1 ↦
    (mfderiv K (ModelWithCorners.pi fun _ : Fin 1 ↦ IY) Subtype.val z
      (mfderiv (ModelWithCorners.pi fun _ : Fin 1 ↦ IY) K r y.1 v) : Fin 1 → EY))
    (hleft y)).symm.trans hdv

/-- Differential of `baseProj` on `Y^[k + 1]` in terms of the `0`-th coordinate differential. -/
private theorem mfderiv_baseProj_succ_aux (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    (k dk : ℕ) [ChartedSpace (Fin dk → ℝ) (IteratedFiberProduct π (k + 1))]
    (hemb_k : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin dk → ℝ)
      (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y))
    (z : IteratedFiberProduct π (k + 1)) (u : TangentSpace 𝓘(ℝ, Fin dk → ℝ) z) :
    mfderiv 𝓘(ℝ, Fin dk → ℝ) IM (IteratedFiberProduct.baseProj (π := π) (k := k)) z u =
      mfderiv IY IM π (z.1 0)
        ((mfderiv 𝓘(ℝ, Fin dk → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
          Subtype.val z u) 0) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hbe : IteratedFiberProduct.baseProj (π := π) (k := k) =
      π ∘ (fun f : Fin (k + 1) → Y ↦ f 0) ∘ Subtype.val :=
    funext fun w ↦ IteratedFiberProduct.baseProj_def w
  have hstep : mfderiv 𝓘(ℝ, Fin dk → ℝ) IM (IteratedFiberProduct.baseProj (π := π) (k := k)) z u =
      mfderiv 𝓘(ℝ, Fin dk → ℝ) IM (π ∘ (fun f : Fin (k + 1) → Y ↦ f 0) ∘ Subtype.val) z u :=
    congrArg (fun g ↦ (mfderiv 𝓘(ℝ, Fin dk → ℝ) IM g z u : EM)) hbe
  have hkd := (hemb_k.contMDiff z).mdifferentiableAt hn0
  rw [hstep, mfderiv_comp z ((hπ.contMDiff (z.1 0)).mdifferentiableAt hn0)
      ((hasMFDerivAt_apply 0 z.1).mdifferentiableAt.comp z hkd),
    mfderiv_comp z (hasMFDerivAt_apply 0 z.1).mdifferentiableAt hkd, mfderiv_apply]
  rfl

/-- Forward direction of the inductive tangent-space characterization on `Y^[k + 2]`. -/
private theorem mem_range_mfderiv_succ_mp (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    (k dk d : ℕ) [ChartedSpace (Fin dk → ℝ) (IteratedFiberProduct π (k + 1))]
    [ChartedSpace (Fin d → ℝ)
      {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2}]
    (hemb_k : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin dk → ℝ)
      (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y))
    (htang_k : ∀ (y : IteratedFiberProduct π (k + 1))
      (v : TangentSpace (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) y.1),
      v ∈ (mfderiv 𝓘(ℝ, Fin dk → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
        (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y) y).range ↔
      ∀ i j : Fin (k + 1),
        mfderiv IY IM π (y.1 i) (v i) =
          tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j)))
    (hembQ : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin dk → ℝ).prod IY) n
      (Subtype.val : {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2} →
        IteratedFiberProduct π (k + 1) × Y))
    (htangQ : ∀ (q : {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2})
      (w : TangentSpace (𝓘(ℝ, Fin dk → ℝ).prod IY) q.1),
      w ∈ (mfderiv 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin dk → ℝ).prod IY) Subtype.val q).range ↔
        mfderiv 𝓘(ℝ, Fin dk → ℝ) IM IteratedFiberProduct.baseProj q.1.1 w.1 =
          tangentSpaceCast IM (π q.1.2) q.1.1.baseProj (mfderiv IY IM π q.1.2 w.2)) :
    let e := iteratedFiberProductSuccHomeomorph (π := π) k
    letI := e.pullbackChartedSpace (H := Fin d → ℝ)
    ∀ (y : IteratedFiberProduct π (k + 2))
      (v : TangentSpace (ModelWithCorners.pi fun _ : Fin (k + 2) ↦ IY) y.1),
      v ∈ (mfderiv 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 2) ↦ IY)
        (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) y).range →
      ∀ i j : Fin (k + 2),
        mfderiv IY IM π (y.1 i) (v i) =
          tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j)) := by
  let Q := {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2}
  let Kk := 𝓘(ℝ, Fin dk → ℝ)
  let K := 𝓘(ℝ, Fin d → ℝ)
  let Ip_k := ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY
  let Ip := ModelWithCorners.pi fun _ : Fin (k + 2) ↦ IY
  let e := iteratedFiberProductSuccHomeomorph (π := π) k
  let := e.pullbackChartedSpace (H := Fin d → ℝ)
  let Φ : IteratedFiberProduct π (k + 2) ≃ₘ^n⟮K, K⟯ Q := e.pullbackDiffeomorph K n
  have hΦ : ∀ z, Φ z = e z := fun z ↦ congrFun (e.coe_pullbackDiffeomorph K n) z
  have hcast (y : IteratedFiberProduct π (k + 2)) (i' : Fin (k + 1)) (u : EY) :
      (mfderiv IY IM π ((Φ y).1.1.1 i') u : EM) = mfderiv IY IM π (y.1 i'.castSucc) u :=
    congrArg (fun x ↦ (mfderiv IY IM π x u : EM)) (by simp [hΦ, e])
  have hlast (y : IteratedFiberProduct π (k + 2)) (u : EY) :
      (mfderiv IY IM π (Φ y).1.2 u : EM) = mfderiv IY IM π (y.1 (Fin.last (k + 1))) u :=
    congrArg (fun x ↦ (mfderiv IY IM π x u : EM)) (by simp [hΦ, e])
  have hderiv_cast := mfderiv_succ_castSucc hn k dk d hemb_k hembQ
  have hderiv_last := mfderiv_succ_last hn k dk d hemb_k hembQ
  dsimp only
  rintro y v ⟨ξ, hv⟩
  rw [ContinuousLinearMap.coe_coe] at hv
  subst hv
  let w := mfderiv K (Kk.prod IY) (Subtype.val : Q → _) (Φ y) (mfderiv K K Φ y ξ)
  have hinit (i' j' : Fin (k + 1)) :
      mfderiv IY IM π (y.1 i'.castSucc) ((mfderiv K Ip Subtype.val y ξ) i'.castSucc) =
      tangentSpaceCast IM (π (y.1 j'.castSucc)) (π (y.1 i'.castSucc))
        (mfderiv IY IM π (y.1 j'.castSucc) ((mfderiv K Ip Subtype.val y ξ) j'.castSucc)) := by
    have h := (htang_k (Φ y).1.1 (mfderiv Kk Ip_k Subtype.val (Φ y).1.1 w.1)).1 ⟨w.1, rfl⟩ i' j'
    rw [← hderiv_cast y i' ξ, ← hderiv_cast y j' ξ] at h
    exact (hcast y i' _).symm.trans (h.trans (hcast y j' _))
  have h0last : mfderiv IY IM π (y.1 (Fin.castSucc 0))
      ((mfderiv K Ip Subtype.val y ξ) (Fin.castSucc 0)) =
      tangentSpaceCast IM (π (y.1 (Fin.last (k + 1)))) (π (y.1 (Fin.castSucc 0)))
        (mfderiv IY IM π (y.1 (Fin.last (k + 1)))
          ((mfderiv K Ip Subtype.val y ξ) (Fin.last (k + 1)))) := by
    have hwQ := (htangQ (Φ y) w).1 ⟨mfderiv K K Φ y ξ, rfl⟩
    rw [mfderiv_baseProj_succ_aux hn hπ k dk hemb_k (Φ y).1.1 w.1,
      ← hderiv_cast y 0 ξ, ← hderiv_last y ξ] at hwQ
    exact (hcast y 0 _).symm.trans (hwQ.trans (hlast y _))
  intro i j
  refine Fin.lastCases ?_ (fun i' ↦ ?_) i <;> refine Fin.lastCases ?_ (fun j' ↦ ?_) j
  · rfl
  · exact h0last.symm.trans (hinit 0 j')
  · exact (hinit i' 0).trans h0last
  · exact hinit i' j'

/-- Backward direction of the inductive tangent-space characterization on `Y^[k + 2]`. -/
private theorem mem_range_mfderiv_succ_mpr (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    (k dk d : ℕ) [ChartedSpace (Fin dk → ℝ) (IteratedFiberProduct π (k + 1))]
    [ChartedSpace (Fin d → ℝ)
      {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2}]
    (hemb_k : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin dk → ℝ)
      (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y))
    (htang_k : ∀ (y : IteratedFiberProduct π (k + 1))
      (v : TangentSpace (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) y.1),
      v ∈ (mfderiv 𝓘(ℝ, Fin dk → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
        (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y) y).range ↔
      ∀ i j : Fin (k + 1),
        mfderiv IY IM π (y.1 i) (v i) =
          tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j)))
    (hembQ : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin dk → ℝ).prod IY) n
      (Subtype.val : {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2} →
        IteratedFiberProduct π (k + 1) × Y))
    (htangQ : ∀ (q : {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2})
      (w : TangentSpace (𝓘(ℝ, Fin dk → ℝ).prod IY) q.1),
      w ∈ (mfderiv 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin dk → ℝ).prod IY) Subtype.val q).range ↔
        mfderiv 𝓘(ℝ, Fin dk → ℝ) IM IteratedFiberProduct.baseProj q.1.1 w.1 =
          tangentSpaceCast IM (π q.1.2) q.1.1.baseProj (mfderiv IY IM π q.1.2 w.2)) :
    let e := iteratedFiberProductSuccHomeomorph (π := π) k
    letI := e.pullbackChartedSpace (H := Fin d → ℝ)
    ∀ (y : IteratedFiberProduct π (k + 2))
      (v : TangentSpace (ModelWithCorners.pi fun _ : Fin (k + 2) ↦ IY) y.1),
      (∀ i j : Fin (k + 2),
        mfderiv IY IM π (y.1 i) (v i) =
          tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j))) →
      v ∈ (mfderiv 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 2) ↦ IY)
        (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) y).range := by
  let Q := {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2}
  let Kk := 𝓘(ℝ, Fin dk → ℝ)
  let K := 𝓘(ℝ, Fin d → ℝ)
  let e := iteratedFiberProductSuccHomeomorph (π := π) k
  let := e.pullbackChartedSpace (H := Fin d → ℝ)
  let Φ : IteratedFiberProduct π (k + 2) ≃ₘ^n⟮K, K⟯ Q := e.pullbackDiffeomorph K n
  have hΦ : ∀ z, Φ z = e z := fun z ↦ congrFun (e.coe_pullbackDiffeomorph K n) z
  have hcast (y : IteratedFiberProduct π (k + 2)) (i' : Fin (k + 1)) (u : EY) :
      (mfderiv IY IM π ((Φ y).1.1.1 i') u : EM) = mfderiv IY IM π (y.1 i'.castSucc) u :=
    congrArg (fun x ↦ (mfderiv IY IM π x u : EM)) (by simp [hΦ, e])
  have hlast (y : IteratedFiberProduct π (k + 2)) (u : EY) :
      (mfderiv IY IM π (Φ y).1.2 u : EM) = mfderiv IY IM π (y.1 (Fin.last (k + 1))) u :=
    congrArg (fun x ↦ (mfderiv IY IM π x u : EM)) (by simp [hΦ, e])
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hderiv_cast := mfderiv_succ_castSucc hn k dk d hemb_k hembQ
  have hderiv_last := mfderiv_succ_last hn k dk d hemb_k hembQ
  dsimp only
  intro y v hv
  obtain ⟨u₁, hu₁⟩ := (htang_k (Φ y).1.1 (Fin.init v)).2 fun i' j' ↦
    (hcast y i' _).trans ((hv i'.castSucc j'.castSucc).trans (hcast y j' _).symm)
  rw [ContinuousLinearMap.coe_coe] at hu₁
  have hmatch : mfderiv Kk IM IteratedFiberProduct.baseProj (Φ y).1.1 u₁ =
      tangentSpaceCast IM (π (Φ y).1.2) (Φ y).1.1.baseProj
        (mfderiv IY IM π (Φ y).1.2 (v (Fin.last (k + 1)))) := by
    rw [mfderiv_baseProj_succ_aux hn hπ k dk hemb_k (Φ y).1.1 u₁, hu₁]
    exact (hcast y 0 _).trans ((hv (Fin.castSucc 0) (Fin.last (k + 1))).trans (hlast y _).symm)
  obtain ⟨η, hη⟩ := (htangQ (Φ y) (u₁, v (Fin.last (k + 1)))).2 hmatch
  rw [ContinuousLinearMap.coe_coe] at hη
  let ξ : TangentSpace K y := (Φ.mfderivToContinuousLinearEquiv hn0 y).symm η
  have hΦξ : mfderiv K K Φ y ξ = η := by
    rw [← Φ.mfderivToContinuousLinearEquiv_coe hn0]
    exact (Φ.mfderivToContinuousLinearEquiv hn0 y).apply_symm_apply η
  refine ⟨ξ, ?_⟩
  rw [ContinuousLinearMap.coe_coe]
  refine funext fun i ↦ Fin.lastCases ?_ (fun i' ↦ ?_) i
  · rw [hderiv_last y ξ, hΦξ, hη]
  · rw [hderiv_cast y i' ξ, hΦξ, hη]
    exact congrFun hu₁ i'

variable [IsManifold IY n Y] [IsManifold IM n M]
  [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]

/-- Inductive step (`k → k + 1`) of the recursive manifold structure on `Y^[k + 1]`. -/
private theorem exists_isManifold_iteratedFiberProduct_succ (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (k : ℕ)
    (cs_k : ChartedSpace (Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      (IteratedFiberProduct π (k + 1)))
    (hm_k : letI := cs_k
      IsManifold 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
        (IteratedFiberProduct π (k + 1)))
    (hemb_k : letI := cs_k
      Manifold.IsSmoothEmbedding
        𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) n
        (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y))
    (htang_k : letI := cs_k
      ∀ (y : IteratedFiberProduct π (k + 1))
        (v : TangentSpace (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) y.1),
        v ∈ (mfderiv
          𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
          (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
          (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y) y).range ↔
        ∀ i j : Fin (k + 1),
          mfderiv IY IM π (y.1 i) (v i) =
            tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j))) :
    ∃ cs : ChartedSpace (Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ)
        (IteratedFiberProduct π (k + 2)),
      letI := cs
      IsManifold 𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ) n
        (IteratedFiberProduct π (k + 2)) ∧
      Manifold.IsSmoothEmbedding
        𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi fun _ : Fin (k + 2) ↦ IY) n
        (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) ∧
      ∀ (y : IteratedFiberProduct π (k + 2))
        (v : TangentSpace (ModelWithCorners.pi fun _ : Fin (k + 2) ↦ IY) y.1),
        v ∈ (mfderiv
          𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ)
          (ModelWithCorners.pi fun _ : Fin (k + 2) ↦ IY)
          (Subtype.val : IteratedFiberProduct π (k + 2) → Fin (k + 2) → Y) y).range ↔
        ∀ i j : Fin (k + 2),
          mfderiv IY IM π (y.1 i) (v i) =
            tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j)) := by
  let := cs_k
  have := hm_k
  let dk := (k + 1) * finrank ℝ EY - k * finrank ℝ EM
  have hdim : finrank ℝ (Fin dk → ℝ) + finrank ℝ EY - finrank ℝ EM =
      (k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM := by
    rw [Module.finrank_fin_fun]
    dsimp only [dk]
    set a := finrank ℝ EY
    set b := finrank ℝ EM
    by_cases h : k * b ≤ (k + 1) * a
    · rw [← Nat.sub_add_comm h, Nat.sub_sub]
      have h1 : (k + 1) * a + a = (k + 2) * a := by ring
      have h2 : k * b + b = (k + 1) * b := by ring
      rw [h1, h2]
    · have hlt : (k + 1) * a < k * b := Nat.lt_of_not_ge h
      have hab : a ≤ b := by nlinarith
      have hle2 : (k + 2) * a ≤ (k + 1) * b := by nlinarith
      rw [Nat.sub_eq_zero_of_le hlt.le, Nat.zero_add, Nat.sub_eq_zero_of_le hab,
        Nat.sub_eq_zero_of_le hle2]
  rw [← hdim]
  let Kk := 𝓘(ℝ, Fin dk → ℝ)
  let d := finrank ℝ (Fin dk → ℝ) + finrank ℝ EY - finrank ℝ EM
  let K := 𝓘(ℝ, Fin d → ℝ)
  have hbase : ContMDiff Kk IM n (IteratedFiberProduct.baseProj (π := π) (k := k)) :=
    (hπ.contMDiff.comp (contMDiff_apply.comp hemb_k.contMDiff)).congr fun z ↦
      IteratedFiberProduct.baseProj_def z
  have htrans : ∀ p : IteratedFiberProduct π (k + 1) × Y, p.1.baseProj = π p.2 →
      (mfderiv Kk IM (IteratedFiberProduct.baseProj (π := π) (k := k)) p.1).range ⊔
        (((tangentSpaceCast IM (π p.2) p.1.baseProj).toContinuousLinearMap).comp
          (mfderiv IY IM π p.2)).range = ⊤ :=
    fun p _ ↦ transverse_of_isSubmersion_right hn hπ p
  let := transverseFiberProductChartedSpace hn hbase hπ.contMDiff htrans
  have := isManifold_transverseFiberProduct hn hbase hπ.contMDiff htrans
  have hembQ := isSmoothEmbedding_coe_transverseFiberProduct hn hbase hπ.contMDiff htrans
  have htangQ := mem_range_mfderiv_coe_transverseFiberProduct_iff hn hbase hπ.contMDiff htrans
  let e := iteratedFiberProductSuccHomeomorph (π := π) k
  let := e.pullbackChartedSpace (H := Fin d → ℝ)
  have := e.pullback_isManifold K n
  exact ⟨inferInstance, inferInstance, isSmoothEmbedding_succ hn k dk d hemb_k hembQ,
    fun y v ↦ ⟨mem_range_mfderiv_succ_mp hn hπ k dk d hemb_k htang_k hembQ htangQ y v,
      mem_range_mfderiv_succ_mpr hn hπ k dk d hemb_k htang_k hembQ htangQ y v⟩⟩

/-- **The iterated fibre-product theorem for a submersion.** For a `C^n` submersion
`π : Y → M` (`1 ≤ n`) between finite-dimensional boundaryless manifolds, the `(k + 1)`-fold
iterated fibre product `Y^[k + 1]` is an embedded `C^n` manifold in `Fin (k + 1) → Y` of
dimension `(k + 1) * dim Y - k * dim M` with its subspace topology. Its tangent vectors are
exactly the tuples of tangent vectors of `Y` with equal images under `dπ`. No separation,
countability, nonemptiness, or surjectivity hypotheses are needed. -/
theorem exists_isManifold_iteratedFiberProduct_isSmoothEmbedding
    (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π) (k : ℕ) :
    ∃ cs : ChartedSpace (Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
        (IteratedFiberProduct π (k + 1)),
      letI := cs
      IsManifold 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
        (IteratedFiberProduct π (k + 1)) ∧
      Manifold.IsSmoothEmbedding
        𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) n
        (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y) ∧
      ∀ (y : IteratedFiberProduct π (k + 1))
        (v : TangentSpace (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) y.1),
        v ∈ (mfderiv
          𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
          (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
          (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y) y).range ↔
        ∀ i j : Fin (k + 1),
          mfderiv IY IM π (y.1 i) (v i) =
            tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j)) := by
  induction k with
  | zero => exact exists_isManifold_iteratedFiberProduct_zero (IM := IM) (π := π) hn
  | succ k ih =>
    obtain ⟨cs_k, hm_k, hemb_k, htang_k⟩ := ih
    exact exists_isManifold_iteratedFiberProduct_succ hn hπ k cs_k hm_k hemb_k htang_k

variable (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)

/-- A fixed atlas on the `(k + 1)`-fold iterated fibre product `Y^[k + 1]` of a `C^n` submersion
`π : Y → M`. It uses the subspace topology inherited from `Fin (k + 1) → Y` and is not a global
instance. Its manifold, embedding, and tangent-space properties are given by the lemmas below. -/
@[instance_reducible]
noncomputable def iteratedFiberProductChartedSpace (k : ℕ) :
    ChartedSpace (Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      (IteratedFiberProduct π (k + 1)) :=
  (exists_isManifold_iteratedFiberProduct_isSmoothEmbedding hn hπ k).choose

/-- The `(k + 1)`-fold iterated fibre product with its chosen atlas is a `C^n` manifold. -/
theorem isManifold_iteratedFiberProduct (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    IsManifold 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct π (k + 1)) :=
  (exists_isManifold_iteratedFiberProduct_isSmoothEmbedding hn hπ k).choose_spec.1

/-- The inclusion of `Y^[k + 1]` into `Fin (k + 1) → Y` is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_coe_iteratedFiberProduct (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y) :=
  (exists_isManifold_iteratedFiberProduct_isSmoothEmbedding hn hπ k).choose_spec.2.1

/-- A tangent vector `v : Fin (k + 1) → EY` lies in the image of the differential of the
inclusion `Y^[k + 1] → (Fin (k + 1) → Y)` at `y` exactly when all components `v i` have equal
images under `dπ`. -/
theorem mem_range_mfderiv_coe_iteratedFiberProduct_iff (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ∀ (y : IteratedFiberProduct π (k + 1))
      (v : TangentSpace (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) y.1),
      v ∈ (mfderiv
        𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
        (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y) y).range ↔
      ∀ i j : Fin (k + 1),
        mfderiv IY IM π (y.1 i) (v i) =
          tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j)) :=
  (exists_isManifold_iteratedFiberProduct_isSmoothEmbedding hn hπ k).choose_spec.2.2

/-- The differential of the `i`-th coordinate projection on `Y^[k + 1]` is the `i`-th component
of the differential of the ambient inclusion `Subtype.val`. -/
theorem IteratedFiberProduct.mfderiv_coord_apply {k : ℕ} (i : Fin (k + 1))
    (y : IteratedFiberProduct π (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ∀ ξ : TangentSpace 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) y,
      mfderiv 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IY
          (IteratedFiberProduct.coord i) y ξ =
        (mfderiv 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
          (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
          (Subtype.val : IteratedFiberProduct π (k + 1) → Fin (k + 1) → Y) y ξ) i := by
  let := iteratedFiberProductChartedSpace hn hπ k
  intro ξ
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hc : IteratedFiberProduct.coord (π := π) i = fun z ↦ z.1 i :=
    funext (IteratedFiberProduct.coord_apply i)
  have hstep :
      mfderiv 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IY
          (IteratedFiberProduct.coord i) y ξ =
        mfderiv 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IY
          (fun z : IteratedFiberProduct π (k + 1) ↦ z.1 i) y ξ :=
    congrArg (fun g ↦ (mfderiv 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IY
      g y ξ : EY)) hc
  exact hstep.trans (congrFun (DFunLike.congr_fun (mfderiv_pi (mdifferentiableAt_pi_iff.1
    (((isSmoothEmbedding_coe_iteratedFiberProduct hn hπ k).contMDiff y).mdifferentiableAt hn0)))
    ξ) i).symm

/-- Any tuple of tangent vectors `v i ∈ T_{y_i} Y` with equal images under `dπ` arises as the
tuple of coordinate differentials of a tangent vector `ξ` of `Y^[k + 1]` at `y`. -/
theorem exists_mfderiv_eq_of_iteratedFiberProduct (k : ℕ)
    (y : IteratedFiberProduct π (k + 1)) (v : ∀ i : Fin (k + 1), TangentSpace IY (y.1 i))
    (hv : ∀ i j : Fin (k + 1),
      mfderiv IY IM π (y.1 i) (v i) =
        tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j))) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ∃ ξ, ∀ i : Fin (k + 1),
      mfderiv 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IY
        (IteratedFiberProduct.coord i) y ξ = v i := by
  let := iteratedFiberProductChartedSpace hn hπ k
  obtain ⟨ξ, hξ⟩ := (mem_range_mfderiv_coe_iteratedFiberProduct_iff hn hπ k y v).2 hv
  exact ⟨ξ, fun i ↦ (IteratedFiberProduct.mfderiv_coord_apply hn hπ i y ξ).trans (congrFun hξ i)⟩

/-- A tangent vector of `Y^[k + 1]` is zero when all coordinate projections have vanishing
differential on it. -/
theorem eq_zero_of_mfderiv_iteratedFiberProduct (k : ℕ) (y : IteratedFiberProduct π (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ∀ ξ : TangentSpace 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) y,
      (∀ i : Fin (k + 1),
        mfderiv 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IY
          (IteratedFiberProduct.coord i) y ξ = 0) →
      ξ = 0 := by
  let := iteratedFiberProductChartedSpace hn hπ k
  intro ξ hξ
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hi := isSmoothEmbedding_coe_iteratedFiberProduct hn hπ k
  refine (injective_iff_map_eq_zero _).1 ((hi.isImmersion.isImmersionAt y).mfderiv_injective hn0)
    ξ (funext fun i ↦ ?_)
  rw [← IteratedFiberProduct.mfderiv_coord_apply hn hπ i y ξ]
  exact hξ i

/-! ### Universal property, smooth maps, submersions, and embeddings -/

/-- **Smooth universal property of `Y^[k + 1]`.** A map into the iterated fibre product is `C^n`
exactly when each of its `k + 1` coordinate maps into `Y` is `C^n`. -/
theorem contMDiff_iteratedFiberProduct_iff {EZ HZ Z : Type*}
    [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
    {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]
    {k : ℕ} {f : Z → IteratedFiberProduct π (k + 1)} :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ContMDiff IZ 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n f ↔
      ∀ i : Fin (k + 1), ContMDiff IZ IY n (fun z ↦ (f z).1 i) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  exact (isSmoothEmbedding_coe_iteratedFiberProduct hn hπ k).contMDiff_iff_comp.trans
    contMDiff_pi_iff

end Manifold

end TauCeti
