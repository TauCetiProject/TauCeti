/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Identity
public import TauCeti.Geometry.Manifold.FiberProduct.Submersion
public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Geometry.Manifold.MFDeriv.Pi
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Manifold.Submersion.Composition

/-!
# Iterated submersion fibre products

Given `π : Y → M` and `k : ℕ`, `TauCeti.IteratedFiberProduct π k` (`Y ×_M ⋯ ×_M Y`) is the subtype
of `k`-tuples `y : Fin k → Y` whose images under `π` all agree. When `Y` and `M` are boundaryless
finite-dimensional real `C^n` manifolds (`1 ≤ n`) and `π` is a `C^n` submersion, this file equips
`IteratedFiberProduct π k` (`k ≥ 1`) with its canonical embedded `C^n` manifold structure of
dimension `k * dim Y - (k - 1) * dim M` (requiring neither `T2Space` nor
`SecondCountableTopology`), establishing Hausdorff closedness (`isClosedEmbedding_val`), smooth
universal properties (`contMDiff_iteratedFiberProduct_iff`, `contMDiffOn_iteratedFiberProduct_iff`),
tangent space (`mem_range_mfderiv_coe_iteratedFiberProduct_iff`), and local product normal form
(`exists_localNormalForm_iteratedFiberProduct`).

## References
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Thms. 4.12, 6.30.
* M. K. Murray, *Bundle gerbes*, J. London Math. Soc. (2) 54 (1996), 403–416, §2.
-/

public section

noncomputable section

open Function Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

/-- The `k`-fold iterated fibre product `Y ×_M ⋯ ×_M Y` of a map `π : Y → M`, realized as the
subtype of `k`-tuples in `Fin k → Y` whose images under `π` all agree. -/
abbrev IteratedFiberProduct {Y M : Type*} (π : Y → M) (k : ℕ) : Type _ :=
  {y : Fin k → Y // ∀ i j : Fin k, π (y i) = π (y j)}

namespace IteratedFiberProduct

variable {Y M : Type*} {π : Y → M} {k l m : ℕ}

@[ext] theorem ext {y z : IteratedFiberProduct π k} (h : ∀ i : Fin k, y.1 i = z.1 i) : y = z :=
  Subtype.ext (funext h)

/-- The `i`-th factor projection `IteratedFiberProduct π k → Y`. -/
def proj (i : Fin k) (y : IteratedFiberProduct π k) : Y := y.1 i
@[simp] theorem proj_mk (y : Fin k → Y) (hy : ∀ i j, π (y i) = π (y j)) (i : Fin k) :
    proj i (⟨y, hy⟩ : IteratedFiberProduct π k) = y i := (rfl)
@[simp] theorem val_apply (y : IteratedFiberProduct π k) (i : Fin k) : y.1 i = proj i y := (rfl)
theorem apply_proj_eq (y : IteratedFiberProduct π k) (i j : Fin k) :
    π (proj i y) = π (proj j y) := y.2 i j

/-- For `k ≥ 1`, the common base projection `IteratedFiberProduct π k → M`. -/
def baseProj [NeZero k] (y : IteratedFiberProduct π k) : M := π (proj 0 y)
@[simp] theorem baseProj_mk [NeZero k] (y : Fin k → Y) (hy : ∀ i j, π (y i) = π (y j)) :
    baseProj (⟨y, hy⟩ : IteratedFiberProduct π k) = π (y 0) := (rfl)
theorem proj_comp_eq_baseProj [NeZero k] (y : IteratedFiberProduct π k) (i : Fin k) :
    π (proj i y) = baseProj y := y.2 i 0
theorem comp_proj [NeZero k] (i : Fin k) :
    π ∘ (proj i : IteratedFiberProduct π k → Y) = baseProj :=
  funext fun y ↦ proj_comp_eq_baseProj y i

/-- Contravariant reindexing of `IteratedFiberProduct` along any map `α : Fin k → Fin l`. -/
def precomp (α : Fin k → Fin l) (y : IteratedFiberProduct π l) : IteratedFiberProduct π k :=
  ⟨y.1 ∘ α, fun i j ↦ y.2 (α i) (α j)⟩
@[simp] theorem proj_precomp (α : Fin k → Fin l) (y : IteratedFiberProduct π l) (i : Fin k) :
    proj i (precomp α y) = proj (α i) y := (rfl)
@[simp] theorem baseProj_precomp [NeZero k] [NeZero l] (α : Fin k → Fin l)
    (y : IteratedFiberProduct π l) : baseProj (precomp α y) = baseProj y := y.2 (α 0) 0
@[simp] theorem precomp_id (y : IteratedFiberProduct π k) : precomp id y = y := (rfl)
theorem precomp_comp (α : Fin k → Fin l) (β : Fin l → Fin m) (y : IteratedFiberProduct π m) :
    precomp (β ∘ α) y = precomp α (precomp β y) := (rfl)

/-- The multidiagonal embedding `Y → IteratedFiberProduct π k` repeating `y` in all `k` factors. -/
def constDiagonal (y : Y) (k : ℕ) : IteratedFiberProduct π k := ⟨fun _ ↦ y, fun _ _ ↦ rfl⟩
@[simp] theorem proj_constDiagonal (y : Y) (k : ℕ) (i : Fin k) :
    proj i (constDiagonal (π := π) y k) = y := (rfl)
@[simp] theorem baseProj_constDiagonal [NeZero k] (y : Y) :
    baseProj (constDiagonal (π := π) y k) = π y := (rfl)
theorem surjective_proj (i : Fin k) : Surjective (proj i : IteratedFiberProduct π k → Y) :=
  fun y ↦ ⟨constDiagonal y k, rfl⟩
theorem surjective_baseProj [NeZero k] (hπ : Surjective π) :
    Surjective (baseProj : IteratedFiberProduct π k → M) := fun x ↦ by
  obtain ⟨y, rfl⟩ := hπ x; exact ⟨constDiagonal y k, rfl⟩

/-- The multidiagonal `{m : Fin k → M | ∀ i j, m i = m j}` of `M^k`. -/
def multidiagonal (M : Type*) (k : ℕ) : Set (Fin k → M) := {x | ∀ i j : Fin k, x i = x j}
@[simp] theorem mem_multidiagonal {x : Fin k → M} :
    x ∈ multidiagonal M k ↔ ∀ i j : Fin k, x i = x j := Iff.rfl
theorem range_val_eq_preimage_multidiagonal :
    range (Subtype.val : IteratedFiberProduct π k → Fin k → Y) =
      (Pi.map fun _ : Fin k ↦ π) ⁻¹' multidiagonal M k := by ext y; simp

theorem isClosed_multidiagonal [TopologicalSpace M] [T2Space M] (k : ℕ) :
    IsClosed (multidiagonal M k) := by
  have heq : multidiagonal M k = ⋂ (i : Fin k) (j : Fin k), {x : Fin k → M | x i = x j} := by
    ext x; simp
  exact heq ▸ isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
    isClosed_eq (continuous_apply i) (continuous_apply j)

theorem isClosed_setOf_apply_eq [TopologicalSpace Y] [TopologicalSpace M] [T2Space M]
    (hπ : Continuous π) (k : ℕ) :
    IsClosed {y : Fin k → Y | ∀ i j : Fin k, π (y i) = π (y j)} :=
  (isClosed_multidiagonal (M := M) k).preimage (continuous_pi fun i ↦ hπ.comp (continuous_apply i))

/-- When `M` is Hausdorff and `π : Y → M` is continuous, `Subtype.val` is a closed embedding. -/
theorem isClosedEmbedding_val [TopologicalSpace Y] [TopologicalSpace M] [T2Space M]
    (hπ : Continuous π) (k : ℕ) :
    IsClosedEmbedding (Subtype.val : IteratedFiberProduct π k → Fin k → Y) :=
  (isClosed_setOf_apply_eq hπ k).isClosedEmbedding_subtypeVal

theorem continuous_proj [TopologicalSpace Y] (i : Fin k) :
    Continuous (proj i : IteratedFiberProduct π k → Y) :=
  (continuous_apply i).comp continuous_subtype_val
theorem continuous_baseProj [TopologicalSpace Y] [TopologicalSpace M] [NeZero k]
    (hπ : Continuous π) : Continuous (baseProj : IteratedFiberProduct π k → M) :=
  hπ.comp (continuous_proj 0)

end IteratedFiberProduct

section Dimension

/-- Expected dimension `k * dim Y - (k - 1) * dim M` of the `k`-fold iterated fibre product of a
submersion `Y → M`. -/
@[expose]
def iteratedFiberProductDim (EY EM : Type*) [AddCommGroup EY] [Module ℝ EY]
    [AddCommGroup EM] [Module ℝ EM] (k : ℕ) : ℕ :=
  k * finrank ℝ EY - (k - 1) * finrank ℝ EM

section

variable (EY EM : Type*) [AddCommGroup EY] [Module ℝ EY] [AddCommGroup EM] [Module ℝ EM]

@[simp] theorem iteratedFiberProductDim_one :
    iteratedFiberProductDim EY EM 1 = finrank ℝ EY := by simp [iteratedFiberProductDim]
@[simp] theorem iteratedFiberProductDim_two :
    iteratedFiberProductDim EY EM 2 = finrank ℝ EY + finrank ℝ EY - finrank ℝ EM := by
  simp [iteratedFiberProductDim, two_mul]

theorem iteratedFiberProductDim_succ {k : ℕ} [NeZero k] :
    iteratedFiberProductDim EY EM (k + 1) =
      iteratedFiberProductDim EY EM k + finrank ℝ EY - finrank ℝ EM := by
  rcases k with _ | m; · exact False.elim (NeZero.ne 0 rfl)
  simp only [iteratedFiberProductDim, Nat.add_sub_cancel]
  set a := finrank ℝ EY; set b := finrank ℝ EM
  have ha1 : (m + 1) * a = m * a + a := Nat.succ_mul m a
  have ha2 : (m + 1 + 1) * a = m * a + a + a := by rw [Nat.succ_mul, ha1]
  rw [ha1, ha2, Nat.succ_mul m b]; set ma := m * a; set mb := m * b
  by_cases h : mb ≤ ma + a
  · omega
  · have hab : a < b := by by_contra hba; have := Nat.mul_le_mul_left m (not_lt.mp hba); omega
    omega

theorem finrank_le_iteratedFiberProductDim {EY EM : Type*} [AddCommGroup EY] [Module ℝ EY]
    [AddCommGroup EM] [Module ℝ EM] (hle : finrank ℝ EM ≤ finrank ℝ EY) (k : ℕ) [NeZero k] :
    finrank ℝ EM ≤ iteratedFiberProductDim EY EM k := by
  rcases k with _ | m; · exact False.elim (NeZero.ne 0 rfl)
  induction m with
  | zero => simpa using hle
  | succ m ih => rw [iteratedFiberProductDim_succ EY EM (k := m + 1)]; omega

theorem iteratedFiberProductDim_add {a b : ℕ} [NeZero a] [NeZero b]
    (hle : finrank ℝ EM ≤ finrank ℝ EY) :
    iteratedFiberProductDim EY EM (a + b) =
      iteratedFiberProductDim EY EM a + iteratedFiberProductDim EY EM b - finrank ℝ EM := by
  have hda := finrank_le_iteratedFiberProductDim hle a
  rcases b with _ | m; · exact False.elim (NeZero.ne 0 rfl)
  induction m with
  | zero => rw [iteratedFiberProductDim_succ, iteratedFiberProductDim_one]
  | succ m ih =>
    have hdm := finrank_le_iteratedFiberProductDim hle (m + 1)
    rw [show a + (m + 1 + 1) = (a + (m + 1)) + 1 by omega,
      iteratedFiberProductDim_succ EY EM (k := a + (m + 1)), ih,
      iteratedFiberProductDim_succ EY EM (k := m + 1)]
    omega

@[simp] theorem iteratedFiberProductDim_self (k : ℕ) [NeZero k] :
    iteratedFiberProductDim EM EM k = finrank ℝ EM := by
  rcases k with _ | m; · exact False.elim (NeZero.ne 0 rfl)
  simp [iteratedFiberProductDim, Nat.succ_mul]

end

end Dimension

private theorem isSmoothEmbedding_contMDiffOn_iff_comp
    {𝕜 E₁ H₁ X₁ E₂ H₂ X₂ E₃ H₃ X₃ : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [TopologicalSpace H₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [TopologicalSpace H₂]
    [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [TopologicalSpace H₃]
    {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
    {I₃ : ModelWithCorners 𝕜 E₃ H₃}
    [TopologicalSpace X₁] [ChartedSpace H₁ X₁] [TopologicalSpace X₂] [ChartedSpace H₂ X₂]
    [TopologicalSpace X₃] [ChartedSpace H₃ X₃]
    {m : ℕ∞ω} {g : X₁ → X₂} {φ : X₂ → X₃} {s : Set X₁}
    (hφ : Manifold.IsSmoothEmbedding I₂ I₃ m φ) :
    ContMDiffOn I₁ I₂ m g s ↔ ContMDiffOn I₁ I₃ m (φ ∘ g) s := by
  refine ⟨fun hg ↦ hφ.contMDiff.comp_contMDiffOn hg, fun h' ↦ ?_⟩
  have hg_cont : ContinuousOn g s := continuousOn_iff_continuous_domRestrict.2
    (hφ.isEmbedding.continuous_iff.2 (continuousOn_iff_continuous_domRestrict.1 h'.continuousOn))
  intro x hx
  let h := (hφ.isImmersion.isImmersionAt (g x)).isImmersionAtOfComplement_complement
  let t := s ∩ g ⁻¹' h.domChart.source; have hxt : x ∈ t := ⟨hx, h.mem_domChart_source⟩
  have ht_mem : t ∈ 𝓝[s] x := Filter.inter_mem self_mem_nhdsWithin <|
    (hg_cont x hx).preimage_mem_nhdsWithin (h.domChart.open_source.mem_nhds h.mem_domChart_source)
  suffices ContMDiffWithinAt I₁ I₂ m g t x from this.mono_of_mem_nhdsWithin ht_mem
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas' h.domChart_mem_maximalAtlas h.mem_domChart_source]
  refine ⟨(hg_cont x hx).mono inter_subset_left, ?_⟩
  set f' := (h.domChart.extend I₂) ∘ g ∘ (extChartAt I₁ x).symm
  set φ' := (h.codChart.extend I₃) ∘ φ ∘ (h.domChart.extend I₂).symm
  set x' := extChartAt I₁ x x; set u := (extChartAt I₁ x).symm ⁻¹' t ∩ range I₁
  have hx' : x' ∈ u := ⟨by simp [x', hxt], mem_range_self _⟩
  have h'loc : ContDiffWithinAt 𝕜 m ((h.codChart.extend I₃) ∘ (φ ∘ g) ∘ (extChartAt I₁ x).symm)
      u x' := by
    have h't : ContMDiffWithinAt I₁ I₃ m (φ ∘ g) t x := (h' x hx).mono inter_subset_left
    rw [contMDiffWithinAt_iff_of_mem_maximalAtlas' h.codChart_mem_maximalAtlas] at h't
    exacts [h't.2, h.mem_codChart_source]
  have hcomp : ContDiffWithinAt 𝕜 m (φ' ∘ f') u x' :=
    h'loc.congr_of_mem (fun y hy ↦ by
      simp only [mfld_simps, φ', f']; rw [h.domChart.left_inv]; exact hy.1.2) hx'
  set f'' := (h.equiv ∘ fun z ↦ (z, 0)) ∘ f'
  have hf'' : ContDiffWithinAt 𝕜 m f'' u x' :=
    hcomp.congr_of_mem (fun y hy ↦ by
      simp only [f'', φ', f']; nth_rw 2 [Function.comp_apply]
      rw [Function.comp_apply, h.writtenInCharts]
      rw [h.domChart.extend_target_eq_image_source]
      exact ⟨g ((extChartAt I₁ x).symm y), hy.1.2, rfl⟩) hx'
  let P : _ →L[𝕜] E₂ := (ContinuousLinearMap.fst 𝕜 E₂ _).comp h.equiv.symm.toContinuousLinearMap
  exact (P.contDiff.contDiffWithinAt.comp x' hf'' (mapsTo_univ _ _)).congr_of_mem
    (fun _ _ ↦ by simp [P, f'']) hx'

section Manifold

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y] [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}

private theorem isSmoothEmbedding_comp_of_boundaryless
    {E₁ H₁ X₁ E₂ H₂ X₂ E₃ H₃ X₃ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [TopologicalSpace H₃]
    {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
    {I₃ : ModelWithCorners ℝ E₃ H₃}
    [I₁.Boundaryless] [I₃.Boundaryless] [FiniteDimensional ℝ E₃]
    [TopologicalSpace X₁] [ChartedSpace H₁ X₁] [IsManifold I₁ n X₁]
    [TopologicalSpace X₂] [ChartedSpace H₂ X₂]
    [TopologicalSpace X₃] [ChartedSpace H₃ X₃] [IsManifold I₃ n X₃]
    {f : X₁ → X₂} {g : X₂ → X₃} (hn : 1 ≤ n)
    (hg : Manifold.IsSmoothEmbedding I₂ I₃ n g) (hf : Manifold.IsSmoothEmbedding I₁ I₂ n f) :
    Manifold.IsSmoothEmbedding I₁ I₃ n (g ∘ f) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine ⟨(hg.contMDiff.comp hf.contMDiff).isImmersion_of_injective_mfderiv hn fun x ↦ ?_,
    hg.isEmbedding.comp hf.isEmbedding⟩
  rw [mfderiv_comp x ((hg.contMDiff (f x)).mdifferentiableAt hn0)
    ((hf.contMDiff x).mdifferentiableAt hn0)]
  exact ((hg.isImmersion.isImmersionAt (f x)).mfderiv_injective hn0).comp
    ((hf.isImmersion.isImmersionAt x).mfderiv_injective hn0)

private theorem exists_chartedSpace_of_homeomorph_fin {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {d d' : ℕ} [ChartedSpace (Fin d' → ℝ) B]
    [IsManifold 𝓘(ℝ, Fin d' → ℝ) n B] (e : A ≃ₜ B) (hd : d = d') :
    ∃ cs : ChartedSpace (Fin d → ℝ) A,
      letI := cs
      IsManifold 𝓘(ℝ, Fin d → ℝ) n A ∧
      ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d' → ℝ) n e ∧
      ContMDiff 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d → ℝ) n e.symm := by
  subst hd
  let cs := e.isLocalHomeomorph.chartedSpaceComap (H := Fin d → ℝ)
  have he : (⇑e ∘ ⇑e.symm) = id := funext e.apply_symm_apply
  exact ⟨cs, e.isLocalHomeomorph.isManifold_chartedSpaceComap,
    e.isLocalHomeomorph.isLocalDiffeomorph_chartedSpaceComap.contMDiff,
    e.isLocalHomeomorph.contMDiff_chartedSpaceComap_iff.2
      ⟨e.symm.continuous, by rw [he]; exact contMDiff_id⟩⟩

private def piFinOneDiffeomorph :
    Y ≃ₘ^n⟮IY, ModelWithCorners.pi fun _ : Fin 1 ↦ IY⟯ (Fin 1 → Y) where
  toFun y _ := y
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := funext fun i ↦ congrArg f (Subsingleton.elim 0 i)
  contMDiff_toFun := contMDiff_pi_iff.2 fun _ ↦ contMDiff_id
  contMDiff_invFun := contMDiff_apply

private def piSnocDiffeomorph (k : ℕ) :
    ((Fin k → Y) × Y) ≃ₘ^n⟮(ModelWithCorners.pi fun _ : Fin k ↦ IY).prod IY,
      ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY⟯ (Fin (k + 1) → Y) where
  toFun p := Fin.snoc (α := fun _ ↦ Y) p.1 p.2
  invFun f := (Fin.init f, f (Fin.last k))
  left_inv p :=
    Prod.ext (Fin.init_snoc (α := fun _ ↦ Y) p.2 p.1) (Fin.snoc_last (α := fun _ ↦ Y) p.2 p.1)
  right_inv f := Fin.snoc_init_self f
  contMDiff_toFun := contMDiff_pi_iff.2 <| Fin.lastCases
    (by simp only [Equiv.coe_fn_mk, Fin.snoc_last]; exact contMDiff_snd)
    (fun _ ↦ by
      simp only [Equiv.coe_fn_mk, Fin.snoc_castSucc]; exact contMDiff_apply.comp contMDiff_fst)
  contMDiff_invFun := (contMDiff_pi_iff.2 fun _ ↦ contMDiff_apply).prodMk contMDiff_apply

/-- **Existence of the embedded manifold structure on iterated submersion fibre products.** -/
theorem exists_isManifold_iteratedFiberProduct [IsManifold IY n Y] [IsManifold IM n M]
    [IY.Boundaryless] [IM.Boundaryless] [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]
    {π : Y → M} (k : ℕ) [hk : NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    ∃ cs : ChartedSpace (Fin (iteratedFiberProductDim EY EM k) → ℝ) (IteratedFiberProduct π k),
      letI := cs
      IsManifold 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) n (IteratedFiberProduct π k) ∧
      Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ)
        (ModelWithCorners.pi fun _ : Fin k ↦ IY) n
        (Subtype.val : IteratedFiberProduct π k → Fin k → Y) ∧
      Manifold.IsSubmersion 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) IM n
        (IteratedFiberProduct.baseProj : IteratedFiberProduct π k → M) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  rcases k with _ | m; · exact False.elim (NeZero.ne 0 rfl)
  revert hk; induction m with
  | zero =>
    intro
    let B₁ := {p : Y × M // π p.1 = id p.2}
    let := transverseFiberProductChartedSpace hn hπ.contMDiff (contMDiff_id (I := IM))
      (fun p _ ↦ transverse_id_right π p)
    have := isManifold_transverseFiberProduct hn hπ.contMDiff (contMDiff_id (I := IM))
      (fun p _ ↦ transverse_id_right π p)
    have hc₀ : Continuous fun y : IteratedFiberProduct π 1 ↦ y.1 0 :=
      (continuous_apply 0).comp continuous_subtype_val
    let e₁ : IteratedFiberProduct π 1 ≃ₜ B₁ :=
      { toFun := fun y ↦ ⟨(y.1 0, π (y.1 0)), rfl⟩
        invFun := fun p ↦ ⟨fun _ ↦ p.1.1, fun _ _ ↦ rfl⟩
        left_inv := fun y ↦ Subtype.ext (funext fun i ↦ congrArg y.1 (Subsingleton.elim 0 i))
        right_inv := fun p ↦ Subtype.ext (Prod.ext rfl p.2)
        continuous_toFun := (hc₀.prodMk (hπ.contMDiff.continuous.comp hc₀)).subtype_mk _
        continuous_invFun :=
          (continuous_pi fun _ ↦ continuous_fst.comp continuous_subtype_val).subtype_mk _ }
    have hd₁ : iteratedFiberProductDim EY EM 1 =
        finrank ℝ EY + finrank ℝ EM - finrank ℝ EM := by simp [iteratedFiberProductDim]
    obtain ⟨cs₁, hman₁, hto₁, hinv₁⟩ := exists_chartedSpace_of_homeomorph_fin (n := n) e₁ hd₁
    let := cs₁
    let ΦB₁ : IteratedFiberProduct π 1 ≃ₘ^n⟮𝓘(ℝ, Fin (iteratedFiberProductDim EY EM 1) → ℝ),
        𝓘(ℝ, Fin (finrank ℝ EY + finrank ℝ EM - finrank ℝ EM) → ℝ)⟯ B₁ :=
      { toEquiv := e₁.toEquiv, contMDiff_toFun := hto₁, contMDiff_invFun := hinv₁ }
    let ΦY := ΦB₁.trans (transverseFiberProductIdRightDiffeomorph hn hπ.contMDiff)
    let ΦPi := ΦY.trans (piFinOneDiffeomorph (IY := IY) (n := n))
    have hΦY : ∀ y : IteratedFiberProduct π 1, ΦY y = y.1 0 := fun y ↦
      transverseFiberProductIdRightDiffeomorph_apply hn hπ.contMDiff (e₁ y)
    have hval_eq : (Subtype.val : IteratedFiberProduct π 1 → Fin 1 → Y) = ⇑ΦPi := by
      ext y i; change y.1 i = ΦY y; rw [hΦY y]; exact congrArg y.1 (Subsingleton.elim i 0)
    have hemb₁ : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM 1) → ℝ)
        (ModelWithCorners.pi fun _ : Fin 1 ↦ IY) n
        (Subtype.val : IteratedFiberProduct π 1 → Fin 1 → Y) := by
      rw [hval_eq]
      simpa [Function.comp_id] using ΦPi.isSmoothEmbedding_comp hn Manifold.IsSmoothEmbedding.id
    have hbase_eq : (IteratedFiberProduct.baseProj : IteratedFiberProduct π 1 → M) = π ∘ ⇑ΦY :=
      funext fun y ↦ congrArg π (hΦY y).symm
    exact ⟨cs₁, hman₁, hemb₁, hbase_eq ▸ hπ.comp (ΦY.isSubmersion hn0)⟩
  | succ m ih =>
    intro; obtain ⟨csk, hmank, hembk, hsubk⟩ := ih (hk := inferInstance); let := csk
    let htrans := fun (p : IteratedFiberProduct π (m + 1) × Y)
        (_ : IteratedFiberProduct.baseProj p.1 = π p.2) ↦ hsubk.transverse_left (IY := IY) hn0 π p
    let B := {p : IteratedFiberProduct π (m + 1) × Y // IteratedFiberProduct.baseProj p.1 = π p.2}
    let := transverseFiberProductChartedSpace hn hsubk.contMDiff hπ.contMDiff htrans
    have := isManifold_transverseFiberProduct hn hsubk.contMDiff hπ.contMDiff htrans
    have hembB :=
      isSmoothEmbedding_coe_transverseFiberProduct hn hsubk.contMDiff hπ.contMDiff htrans
    have hsubB :=
      isSubmersion_fst_transverseFiberProduct hn hsubk.contMDiff hπ.contMDiff htrans hπ
    let e : IteratedFiberProduct π (m + 2) ≃ₜ B :=
      { toFun := fun y ↦
          ⟨(y.precomp Fin.castSucc, y.1 (Fin.last (m + 1))),
            (y.baseProj_precomp Fin.castSucc).trans (y.2 (Fin.last (m + 1)) 0).symm⟩
        invFun := fun p ↦ ⟨Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2, by
          have hall : ∀ i : Fin (m + 2), π (Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 i) =
              IteratedFiberProduct.baseProj p.1.1 := Fin.lastCases
            (by rw [Fin.snoc_last (α := fun _ ↦ Y)]; exact p.2.symm)
            (fun j ↦ by
              rw [Fin.snoc_castSucc (α := fun _ ↦ Y)]; exact p.1.1.proj_comp_eq_baseProj j)
          exact fun i j ↦ (hall i).trans (hall j).symm⟩
        left_inv := fun y ↦ Subtype.ext (Fin.snoc_init_self y.1)
        right_inv := fun p ↦ Subtype.ext <| Prod.ext
          (Subtype.ext (Fin.init_snoc (α := fun _ ↦ Y) p.1.2 p.1.1.1))
          (Fin.snoc_last (α := fun _ ↦ Y) p.1.2 p.1.1.1)
        continuous_toFun :=
          (((continuous_pi fun j ↦ (continuous_apply j.castSucc).comp
            continuous_subtype_val).subtype_mk _).prodMk
            ((continuous_apply (Fin.last (m + 1))).comp continuous_subtype_val)).subtype_mk _
        continuous_invFun := by
          refine (continuous_pi <| Fin.lastCases ?_ fun j ↦ ?_).subtype_mk _
          · have h : (fun p : B ↦ Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 (Fin.last (m + 1))) =
                Prod.snd ∘ Subtype.val :=
              funext fun p ↦ Fin.snoc_last (α := fun _ ↦ Y) p.1.2 p.1.1.1
            exact h ▸ continuous_snd.comp continuous_subtype_val
          · have h : (fun p : B ↦ Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 j.castSucc) =
                (fun f : Fin (m + 1) → Y ↦ f j) ∘ Subtype.val ∘ Prod.fst ∘ Subtype.val :=
              funext fun p ↦ Fin.snoc_castSucc (α := fun _ ↦ Y) p.1.2 p.1.1.1 j
            exact h ▸ (continuous_apply j).comp (continuous_subtype_val.comp
              (continuous_fst.comp continuous_subtype_val)) }
    have hd : iteratedFiberProductDim EY EM (m + 2) =
        finrank ℝ (Fin (iteratedFiberProductDim EY EM (m + 1)) → ℝ) +
          finrank ℝ EY - finrank ℝ EM := by
      simpa [Module.finrank_fin_fun] using iteratedFiberProductDim_succ EY EM (k := m + 1)
    obtain ⟨cs', hman', hto', hinv'⟩ := exists_chartedSpace_of_homeomorph_fin (n := n) e hd
    let := cs'
    let ΦB : IteratedFiberProduct π (m + 2) ≃ₘ^n⟮
        𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (m + 2)) → ℝ),
        𝓘(ℝ, Fin (finrank ℝ (Fin (iteratedFiberProductDim EY EM (m + 1)) → ℝ) +
          finrank ℝ EY - finrank ℝ EM) → ℝ)⟯ B :=
      { toEquiv := e.toEquiv, contMDiff_toFun := hto', contMDiff_invFun := hinv' }
    have hembΦB : Manifold.IsSmoothEmbedding
        𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (m + 2)) → ℝ)
        𝓘(ℝ, Fin (finrank ℝ (Fin (iteratedFiberProductDim EY EM (m + 1)) → ℝ) +
          finrank ℝ EY - finrank ℝ EM) → ℝ) n ⇑ΦB := by
      simpa [Function.comp_id] using ΦB.isSmoothEmbedding_comp hn Manifold.IsSmoothEmbedding.id
    have hembChain := (piSnocDiffeomorph (IY := IY) (n := n) (m + 1)).isSmoothEmbedding_comp hn <|
      isSmoothEmbedding_comp_of_boundaryless hn
        (hembk.prodMap (Manifold.IsSmoothEmbedding.id (I := IY) (M := Y))) <|
        isSmoothEmbedding_comp_of_boundaryless hn hembB hembΦB
    have hval_eq : (Subtype.val : IteratedFiberProduct π (m + 2) → Fin (m + 2) → Y) =
        ⇑(piSnocDiffeomorph (IY := IY) (n := n) (m + 1)) ∘
          Prod.map (Subtype.val : IteratedFiberProduct π (m + 1) → Fin (m + 1) → Y) (@id Y) ∘
          (Subtype.val : B → IteratedFiberProduct π (m + 1) × Y) ∘ ⇑ΦB := by
      ext y i; change y.1 i = Fin.snoc (Fin.init y.1) (y.1 (Fin.last (m + 1))) i
      rw [Fin.snoc_init_self]
    rw [← hval_eq] at hembChain
    have hbase_eq : (IteratedFiberProduct.baseProj : IteratedFiberProduct π (m + 2) → M) =
        (IteratedFiberProduct.baseProj : IteratedFiberProduct π (m + 1) → M) ∘
          (fun p : B ↦ p.1.1) ∘ ⇑ΦB := funext fun y ↦ (y.baseProj_precomp Fin.castSucc).symm
    exact ⟨cs', hman', hembChain, hbase_eq ▸ hsubk.comp (hsubB.comp (ΦB.isSubmersion hn0))⟩

variable [IsManifold IY n Y] [IsManifold IM n M] [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM] {π : Y → M}

/-- Chosen `C^n` atlas on `IteratedFiberProduct π k` (`k ≥ 1`) for a `C^n` submersion `π : Y → M`
(`1 ≤ n`), scoped via `letI` on the inherited subspace topology. -/
@[instance_reducible]
noncomputable def iteratedFiberProductChartedSpace (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    ChartedSpace (Fin (iteratedFiberProductDim EY EM k) → ℝ) (IteratedFiberProduct π k) :=
  (exists_isManifold_iteratedFiberProduct k hn hπ).choose

theorem isManifold_iteratedFiberProduct (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    IsManifold 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) n (IteratedFiberProduct π k) :=
  (exists_isManifold_iteratedFiberProduct k hn hπ).choose_spec.1

theorem isSmoothEmbedding_coe_iteratedFiberProduct (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ)
      (ModelWithCorners.pi fun _ : Fin k ↦ IY) n
      (Subtype.val : IteratedFiberProduct π k → Fin k → Y) :=
  (exists_isManifold_iteratedFiberProduct k hn hπ).choose_spec.2.1

theorem isSubmersion_baseProj_iteratedFiberProduct (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    Manifold.IsSubmersion 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) IM n
      (IteratedFiberProduct.baseProj : IteratedFiberProduct π k → M) :=
  (exists_isManifold_iteratedFiberProduct k hn hπ).choose_spec.2.2

/-- **Smooth universal property of `IteratedFiberProduct`.** -/
theorem contMDiff_iteratedFiberProduct_iff
    {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
    {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]
    {k : ℕ} [NeZero k] (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    {m : ℕ∞ω} (hmn : m ≤ n) {g : Z → IteratedFiberProduct π k} :
    letI := iteratedFiberProductChartedSpace k hn hπ
    ContMDiff IZ 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) m g ↔
      ∀ i : Fin k, ContMDiff IZ IY m (fun z ↦ IteratedFiberProduct.proj i (g z)) := by
  let := iteratedFiberProductChartedSpace k hn hπ
  have hemb := (isSmoothEmbedding_coe_iteratedFiberProduct k hn hπ).of_le hmn
  rw [hemb.contMDiff_iff_comp, contMDiff_pi_iff]; rfl

/-- **Smooth universal property on subsets.** -/
theorem contMDiffOn_iteratedFiberProduct_iff
    {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
    {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]
    {k : ℕ} [NeZero k] (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    {m : ℕ∞ω} (hmn : m ≤ n) {g : Z → IteratedFiberProduct π k} {s : Set Z} :
    letI := iteratedFiberProductChartedSpace k hn hπ
    ContMDiffOn IZ 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) m g s ↔
      ∀ i : Fin k, ContMDiffOn IZ IY m (fun z ↦ IteratedFiberProduct.proj i (g z)) s := by
  let := iteratedFiberProductChartedSpace k hn hπ
  have hemb := (isSmoothEmbedding_coe_iteratedFiberProduct k hn hπ).of_le hmn
  rw [isSmoothEmbedding_contMDiffOn_iff_comp hemb, contMDiffOn_pi_iff]; rfl
theorem contMDiff_proj_iteratedFiberProduct (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) {m : ℕ∞ω} (hmn : m ≤ n) (i : Fin k) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    ContMDiff 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) IY m
      (IteratedFiberProduct.proj i : IteratedFiberProduct π k → Y) := by
  let := iteratedFiberProductChartedSpace k hn hπ
  exact ((contMDiff_iteratedFiberProduct_iff hn hπ hmn (g := id)).1 contMDiff_id) i
theorem contMDiff_baseProj_iteratedFiberProduct (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) {m : ℕ∞ω} (hmn : m ≤ n) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    ContMDiff 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) IM m
      (IteratedFiberProduct.baseProj : IteratedFiberProduct π k → M) := by
  let := iteratedFiberProductChartedSpace k hn hπ
  exact (hπ.contMDiff.of_le hmn).comp (contMDiff_proj_iteratedFiberProduct k hn hπ hmn 0)
theorem IteratedFiberProduct.contMDiff_precomp {k l : ℕ} [NeZero k] [NeZero l] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) {m : ℕ∞ω} (hmn : m ≤ n) (α : Fin k → Fin l) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    letI := iteratedFiberProductChartedSpace l hn hπ
    ContMDiff 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM l) → ℝ)
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) m
      (IteratedFiberProduct.precomp (π := π) α) := by
  let := iteratedFiberProductChartedSpace k hn hπ; let := iteratedFiberProductChartedSpace l hn hπ
  exact (contMDiff_iteratedFiberProduct_iff hn hπ hmn).2 fun i ↦
    contMDiff_proj_iteratedFiberProduct l hn hπ hmn (α i)

/-- **Tangent space of `IteratedFiberProduct`.** -/
theorem mem_range_mfderiv_coe_iteratedFiberProduct_iff (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (y : IteratedFiberProduct π k)
    (v : TangentSpace (ModelWithCorners.pi fun _ : Fin k ↦ IY) y.1) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    v ∈ (mfderiv 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ)
      (ModelWithCorners.pi fun _ : Fin k ↦ IY)
      (Subtype.val : IteratedFiberProduct π k → Fin k → Y) y).range ↔
      ∀ i j : Fin k, mfderiv IY IM π (IteratedFiberProduct.proj i y) (v i) =
        tangentSpaceCast IM (π (IteratedFiberProduct.proj j y))
          (π (IteratedFiberProduct.proj i y))
          (mfderiv IY IM π (IteratedFiberProduct.proj j y) (v j)) := by
  let := iteratedFiberProductChartedSpace k hn hπ; have := isManifold_iteratedFiberProduct k hn hπ
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hemb := isSmoothEmbedding_coe_iteratedFiberProduct k hn hπ
  have hval_diff := (hemb.contMDiff y).mdifferentiableAt hn0
  let Ik (d : ℕ) := 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM d) → ℝ)
  let IPi (d : ℕ) := ModelWithCorners.pi fun _ : Fin d ↦ IY
  have hproj_mfderiv : ∀ (i : Fin k) (u),
      mfderiv (Ik k) IY (IteratedFiberProduct.proj i : IteratedFiberProduct π k → Y) y u =
        (mfderiv (Ik k) (IPi k) (Subtype.val : IteratedFiberProduct π k → Fin k → Y) y u) i :=
    fun i u ↦ by
      have hc := mfderiv_comp (I' := IPi k) y (hasMFDerivAt_apply i y.1).mdifferentiableAt hval_diff
      rw [mfderiv_apply] at hc; exact DFunLike.congr_fun hc u
  have hfwd : ∀ w ∈ (mfderiv (Ik k) (IPi k)
      (Subtype.val : IteratedFiberProduct π k → Fin k → Y) y).range,
      ∀ i j : Fin k, mfderiv IY IM π (IteratedFiberProduct.proj i y) (w i) =
        tangentSpaceCast IM (π (IteratedFiberProduct.proj j y))
          (π (IteratedFiberProduct.proj i y))
          (mfderiv IY IM π (IteratedFiberProduct.proj j y) (w j)) := by
    rintro _ ⟨u, rfl⟩ i j
    have hci := mfderiv_comp y
      ((hπ.contMDiff (IteratedFiberProduct.proj i y)).mdifferentiableAt hn0)
      ((contMDiff_proj_iteratedFiberProduct k hn hπ le_rfl i y).mdifferentiableAt hn0)
    have hcj := mfderiv_comp y
      ((hπ.contMDiff (IteratedFiberProduct.proj j y)).mdifferentiableAt hn0)
      ((contMDiff_proj_iteratedFiberProduct k hn hπ le_rfl j y).mdifferentiableAt hn0)
    have heq : (π ∘ IteratedFiberProduct.proj i : IteratedFiberProduct π k → M) =ᶠ[𝓝 y]
        π ∘ IteratedFiberProduct.proj j := Filter.Eventually.of_forall fun z ↦ z.apply_proj_eq i j
    have hm := DFunLike.congr_fun (heq.mfderiv_eq (I := Ik k) (I' := IM)) u
    rw [hci, hcj] at hm
    dsimp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] at hm
    rwa [hproj_mfderiv i u, hproj_mfderiv j u] at hm
  refine ⟨fun hv ↦ hfwd v hv, ?_⟩
  rcases k with _ | m; · exact False.elim (NeZero.ne 0 rfl)
  intro hv
  let V := TangentSpace (IPi (m + 1)) y.1
  let TM₀ := TangentSpace IM (π (IteratedFiberProduct.proj 0 y))
  let eV : V ≃ₗ[ℝ] (Fin (m + 1) → EY) := (tangentSpaceCastModel (IPi (m + 1)) y.1).toLinearEquiv
  have : FiniteDimensional ℝ V := eV.symm.finiteDimensional
  have : FiniteDimensional ℝ TM₀ :=
    (tangentSpaceCastModel IM (π (IteratedFiberProduct.proj 0 y))).symm
      |>.toLinearEquiv.finiteDimensional
  have hfinV : finrank ℝ V = (m + 1) * finrank ℝ EY := by
    rw [eV.finrank_eq, Module.finrank_pi_fintype]; simp
  have hfinM : finrank ℝ TM₀ = finrank ℝ EM :=
    (tangentSpaceCastModel IM (π (IteratedFiberProduct.proj 0 y))).toLinearEquiv.finrank_eq
  let cLin : ∀ j : Fin m, TangentSpace IM (π (IteratedFiberProduct.proj j.succ y)) →ₗ[ℝ] TM₀ :=
    fun j ↦ (tangentSpaceCast IM (π (IteratedFiberProduct.proj j.succ y))
      (π (IteratedFiberProduct.proj 0 y))).toLinearEquiv.toLinearMap
  let dLin : ∀ i : Fin (m + 1), EY →ₗ[ℝ] TangentSpace IM (π (IteratedFiberProduct.proj i y)) :=
    fun i ↦ (mfderiv IY IM π (IteratedFiberProduct.proj i y)).toLinearMap.comp
      (tangentSpaceCastModel IY (IteratedFiberProduct.proj i y)).symm.toLinearEquiv.toLinearMap
  let T : V →ₗ[ℝ] (Fin m → TM₀) := LinearMap.pi fun j ↦
    (cLin j).comp ((dLin j.succ).comp ((LinearMap.proj j.succ).comp eV.toLinearMap)) -
      (dLin 0).comp ((LinearMap.proj 0).comp eV.toLinearMap)
  have hT_apply : ∀ (w : V) (j : Fin m), T w j =
      tangentSpaceCast IM (π (IteratedFiberProduct.proj j.succ y))
        (π (IteratedFiberProduct.proj 0 y))
        (mfderiv IY IM π (IteratedFiberProduct.proj j.succ y) (w j.succ)) -
        mfderiv IY IM π (IteratedFiberProduct.proj 0 y) (w 0) := fun _ _ ↦ rfl
  have hT_surj : Surjective T := fun z ↦ by
    let u : Fin m → EY := fun j ↦
      tangentSpaceCastModel IY (IteratedFiberProduct.proj j.succ y) <|
        Classical.choose <| hπ.surjective_mfderiv hn0 (IteratedFiberProduct.proj j.succ y)
          ((tangentSpaceCast IM (π (IteratedFiberProduct.proj j.succ y))
            (π (IteratedFiberProduct.proj 0 y))).symm (z j))
    have hu : ∀ j : Fin m, dLin j.succ (u j) =
        (tangentSpaceCast IM (π (IteratedFiberProduct.proj j.succ y))
          (π (IteratedFiberProduct.proj 0 y))).symm (z j) := fun j ↦ by
      simp only [dLin, u, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.symm_apply_apply]
      exact Classical.choose_spec <|
        hπ.surjective_mfderiv hn0 (IteratedFiberProduct.proj j.succ y) _
    refine ⟨eV.symm (Fin.cons (α := fun _ ↦ EY) 0 u), ?_⟩
    ext j
    simp only [T, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, eV.apply_symm_apply, LinearMap.proj_apply,
      Fin.cons_succ (α := fun _ ↦ EY), Fin.cons_zero (α := fun _ ↦ EY), map_zero, sub_zero,
      hu j, cLin, ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply]
  have hle_ker : (mfderiv (Ik (m + 1)) (IPi (m + 1))
      (Subtype.val : IteratedFiberProduct π (m + 1) → Fin (m + 1) → Y) y).range ≤
      LinearMap.ker T := fun w hw ↦ by
    rw [LinearMap.mem_ker]; ext j; rw [hT_apply]; exact sub_eq_zero.2 (hfwd w hw 0 j.succ).symm
  have hdim_ker : finrank ℝ (LinearMap.ker T) = iteratedFiberProductDim EY EM (m + 1) := by
    have hrk := LinearMap.finrank_range_add_finrank_ker T
    have hfinCod : finrank ℝ (Fin m → TM₀) = m * finrank ℝ EM := by
      rw [Module.finrank_pi_fintype]; simp [hfinM]
    rw [LinearMap.range_eq_top.2 hT_surj, finrank_top, hfinCod, hfinV] at hrk
    simp only [iteratedFiberProductDim, Nat.add_sub_cancel]; omega
  have hdim_rng : finrank ℝ (mfderiv (Ik (m + 1)) (IPi (m + 1))
      (Subtype.val : IteratedFiberProduct π (m + 1) → Fin (m + 1) → Y) y).range =
      iteratedFiberProductDim EY EM (m + 1) := by
    have hinj := (hemb.isImmersion.isImmersionAt y).mfderiv_injective hn0
    have : FiniteDimensional ℝ (TangentSpace (Ik (m + 1)) y) :=
      (tangentSpaceCastModel _ y).symm.toLinearEquiv.finiteDimensional
    rw [LinearMap.finrank_range_of_inj hinj,
      (tangentSpaceCastModel _ y).toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  rw [Submodule.eq_of_le_of_finrank_eq hle_ker (hdim_rng.trans hdim_ker.symm), LinearMap.mem_ker]
  ext j; rw [hT_apply]; exact sub_eq_zero.2 (hv 0 j.succ).symm

/-- **Local product normal form of `IteratedFiberProduct`.** -/
theorem exists_localNormalForm_iteratedFiberProduct (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (y₀ : IteratedFiberProduct π k) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    ∃ (U : Set EM) (V : Fin k → Set (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
      (Φ : PartialDiffeomorph
        𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ)
        𝓘(ℝ, EM × (Fin k → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
        (IteratedFiberProduct π k)
        (EM × (Fin k → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ)) n),
      IsOpen U ∧ (∀ i, IsOpen (V i)) ∧
      y₀ ∈ Φ.source ∧ Φ.target = U ×ˢ Set.pi univ V ∧
      (∀ y ∈ Φ.source,
        IteratedFiberProduct.baseProj y ∈ (chartAt HM (IteratedFiberProduct.baseProj y₀)).source ∧
        (Φ y).1 = extChartAt IM (IteratedFiberProduct.baseProj y₀)
          (IteratedFiberProduct.baseProj y)) ∧
      (∀ p ∈ Φ.target,
        IteratedFiberProduct.baseProj (Φ.symm p) =
          (extChartAt IM (IteratedFiberProduct.baseProj y₀)).symm p.1) := by
  let := iteratedFiberProductChartedSpace k hn hπ; have := isManifold_iteratedFiberProduct k hn hπ
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let F := Fin (finrank ℝ EY - finrank ℝ EM) → ℝ
  let x₀ := IteratedFiberProduct.baseProj y₀; let ψ := chartAt HM x₀
  have hψ_max : ψ ∈ IsManifold.maximalAtlas IM n M := IsManifold.chart_mem_maximalAtlas x₀
  have hπF := hπ.contMDiff.isSubmersionOfComplement_of_surjective_mfderiv hn
    (hπ.surjective_mfderiv hn0)
  let L : Fin k → (EY ≃L[ℝ] EM × F) := fun i ↦ (hπF.isSubmersionAt (y₀.1 i)).equiv
  have hdom := fun i : Fin k ↦ (hπF.isSubmersionAt (y₀.1 i)).exists_domChart_of_codChart
    (by rw [IteratedFiberProduct.val_apply, y₀.proj_comp_eq_baseProj i]; exact mem_chart_source _ _)
    hψ_max
  choose φ hy₀_src hφ_max _ hφ_main using hdom
  have hsymm_eq : ∀ i, ∀ w ∈ ((φ i).extend IY).target,
      π (((φ i).extend IY).symm w) = (ψ.extend IM).symm (L i w).1 :=
    fun i w hw ↦ (hφ_main i w hw).2.1
  have hext_eq : ∀ i, ∀ w ∈ ((φ i).extend IY).target,
      ψ.extend IM (π (((φ i).extend IY).symm w)) = (L i w).1 :=
    fun i w hw ↦ (hφ_main i w hw).2.2
  have hφ_tgt_open : ∀ i, IsOpen (((φ i).extend IY).target) := fun i ↦ by
    rw [(φ i).extend_target, IY.range_eq_univ, inter_univ]
    exact (φ i).open_target.preimage IY.continuous_symm
  have hψ_tgt_open : IsOpen ((ψ.extend IM).target) := by
    rw [ψ.extend_target, IM.range_eq_univ, inter_univ]
    exact ψ.open_target.preimage IM.continuous_symm
  let u₀ : EM := ψ.extend IM x₀; let v₀ : Fin k → F := fun i ↦ (L i ((φ i).extend IY (y₀.1 i))).2
  have hmem_W : ∀ i : Fin k, (L i).symm (u₀, v₀ i) ∈ ((φ i).extend IY).target := fun i ↦ by
    have hw₀ : (φ i).extend IY (y₀.1 i) ∈ ((φ i).extend IY).target :=
      ((φ i).extend IY).map_source (by simpa using hy₀_src i)
    have hfst : (L i ((φ i).extend IY (y₀.1 i))).1 = u₀ := by
      rw [← hext_eq i _ hw₀, ((φ i).extend IY).left_inv (by simpa using hy₀_src i)]
      exact congrArg (ψ.extend IM) (y₀.proj_comp_eq_baseProj i)
    rw [show (u₀, v₀ i) = L i ((φ i).extend IY (y₀.1 i)) from Prod.ext hfst.symm rfl,
      ContinuousLinearEquiv.symm_apply_apply]; exact hw₀
  have hrect := fun i : Fin k ↦
    isOpen_prod_iff.1 ((hφ_tgt_open i).preimage (L i).symm.continuous) u₀ (v₀ i) (hmem_W i)
  choose Ui V hUi_open hV_open hu₀_Ui hv₀_V hUiV_sub using hrect
  let U : Set EM := (ψ.extend IM).target ∩ ⋂ i : Fin k, Ui i
  have hU_open : IsOpen U := hψ_tgt_open.inter (isOpen_iInter_of_finite hUi_open)
  have hu₀_U : u₀ ∈ U := ⟨(ψ.extend IM).map_source (by simp [ψ, mem_chart_source HM x₀]),
    mem_iInter.2 hu₀_Ui⟩
  let T : Set (EM × (Fin k → F)) := U ×ˢ Set.pi univ V
  have hT_open : IsOpen T := hU_open.prod (isOpen_set_pi finite_univ fun i _ ↦ hV_open i)
  have hp_mem_tgt : ∀ {p : EM × (Fin k → F)}, p ∈ T → ∀ i : Fin k,
      (L i).symm (p.1, p.2 i) ∈ ((φ i).extend IY).target := fun hp i ↦
    hUiV_sub i ⟨mem_iInter.1 hp.1.2 i, hp.2 i (mem_univ i)⟩
  let Ω : Set (IteratedFiberProduct π k) :=
    {y | IteratedFiberProduct.baseProj y ∈ ψ.source ∧
      ψ.extend IM (IteratedFiberProduct.baseProj y) ∈ U ∧
      ∀ i : Fin k, y.1 i ∈ (φ i).source ∧ (L i ((φ i).extend IY (y.1 i))).2 ∈ V i}
  have hΩ_open : IsOpen Ω := by
    have hcψ : ContinuousOn (ψ.extend IM) ψ.source := by simpa using ψ.continuousOn_extend (I := IM)
    have hS₀ := (hcψ.isOpen_inter_preimage ψ.open_source hU_open).preimage
      (IteratedFiberProduct.continuous_baseProj (k := k) hπ.contMDiff.continuous)
    have hS₁ : ∀ i : Fin k, IsOpen {y : IteratedFiberProduct π k |
        y.1 i ∈ (φ i).source ∧ (L i ((φ i).extend IY (y.1 i))).2 ∈ V i} := fun i ↦ by
      have hcφ : ContinuousOn ((φ i).extend IY) (φ i).source := by
        simpa using (φ i).continuousOn_extend (I := IY)
      have hc := (continuous_snd.comp (L i).continuous).comp_continuousOn hcφ
      exact (hc.isOpen_inter_preimage (φ i).open_source (hV_open i)).preimage
        (IteratedFiberProduct.continuous_proj i)
    have hΩ_eq : Ω = {y | IteratedFiberProduct.baseProj y ∈ ψ.source ∧
        ψ.extend IM (IteratedFiberProduct.baseProj y) ∈ U} ∩
        ⋂ i : Fin k, {y | y.1 i ∈ (φ i).source ∧
          (L i ((φ i).extend IY (y.1 i))).2 ∈ V i} := by ext y; simp [Ω, and_assoc]
    exact hΩ_eq ▸ hS₀.inter (isOpen_iInter_of_finite hS₁)
  have hy₀_Ω : y₀ ∈ Ω := ⟨mem_chart_source HM x₀, hu₀_U, fun i ↦ ⟨hy₀_src i, hv₀_V i⟩⟩
  let toFun : IteratedFiberProduct π k → EM × (Fin k → F) := fun y ↦
    (ψ.extend IM (IteratedFiberProduct.baseProj y), fun i ↦ (L i ((φ i).extend IY (y.1 i))).2)
  let raw : EM × (Fin k → F) → Fin k → Y := fun p i ↦
    ((φ i).extend IY).symm ((L i).symm (p.1, p.2 i))
  have hraw_mem : ∀ {p : EM × (Fin k → F)}, p ∈ T → ∀ i j : Fin k,
      π (raw p i) = π (raw p j) := fun {p} hp i j ↦ by
    have hall : ∀ l : Fin k, π (raw p l) = (ψ.extend IM).symm p.1 := fun l ↦ by
      simpa [raw] using hsymm_eq l _ (hp_mem_tgt hp l)
    rw [hall i, hall j]
  classical
  let invFun : EM × (Fin k → F) → IteratedFiberProduct π k := fun p ↦
    if hp : p ∈ T then ⟨raw p, hraw_mem hp⟩ else y₀
  have hinv_proj : ∀ {p : EM × (Fin k → F)}, p ∈ T → ∀ i : Fin k,
      IteratedFiberProduct.proj i (invFun p) = raw p i := fun hp _ ↦ by simp [invFun, hp]
  have hinv_base : ∀ {p : EM × (Fin k → F)}, p ∈ T →
      IteratedFiberProduct.baseProj (invFun p) = (ψ.extend IM).symm p.1 := fun {p} hp ↦ by
    rw [← IteratedFiberProduct.proj_comp_eq_baseProj (invFun p) 0, hinv_proj hp 0]
    simpa [raw] using hsymm_eq 0 _ (hp_mem_tgt hp 0)
  let Φ : PartialDiffeomorph
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) 𝓘(ℝ, EM × (Fin k → F))
      (IteratedFiberProduct π k) (EM × (Fin k → F)) n :=
    { toFun := toFun, invFun := invFun, source := Ω, target := T
      map_source' := fun _ hy ↦ ⟨hy.2.1, fun i _ ↦ (hy.2.2 i).2⟩
      map_target' := fun p hp ↦ ⟨by rw [hinv_base hp]; simpa using (ψ.extend IM).map_target hp.1.1,
        by rw [hinv_base hp, (ψ.extend IM).right_inv hp.1.1]; exact hp.1,
        fun i ↦ ⟨by
          rw [IteratedFiberProduct.val_apply, hinv_proj hp i]
          simpa [raw] using ((φ i).extend IY).map_target (hp_mem_tgt hp i),
        by
          rw [IteratedFiberProduct.val_apply, hinv_proj hp i]
          simp only [raw, ((φ i).extend IY).right_inv (hp_mem_tgt hp i),
            ContinuousLinearEquiv.apply_symm_apply]; exact hp.2 i (mem_univ i)⟩⟩
      left_inv' := fun y hy ↦ IteratedFiberProduct.ext fun i ↦ by
        rw [IteratedFiberProduct.val_apply, hinv_proj ⟨hy.2.1, fun j _ ↦ (hy.2.2 j).2⟩ i]
        have hw : (φ i).extend IY (y.1 i) ∈ ((φ i).extend IY).target :=
          ((φ i).extend IY).map_source (by simpa using (hy.2.2 i).1)
        have hfst : (L i ((φ i).extend IY (y.1 i))).1 =
            ψ.extend IM (IteratedFiberProduct.baseProj y) := by
          rw [← hext_eq i _ hw, ((φ i).extend IY).left_inv (by simpa using (hy.2.2 i).1)]
          exact congrArg (ψ.extend IM) (y.proj_comp_eq_baseProj i)
        dsimp only [raw, toFun]
        rw [show (ψ.extend IM (IteratedFiberProduct.baseProj y),
            (L i ((φ i).extend IY (y.1 i))).2) = L i ((φ i).extend IY (y.1 i)) from
            Prod.ext hfst.symm rfl, ContinuousLinearEquiv.symm_apply_apply]
        exact ((φ i).extend IY).left_inv (by simpa using (hy.2.2 i).1)
      right_inv' := fun p hp ↦ Prod.ext
        (by dsimp only [toFun]; rw [hinv_base hp]; exact (ψ.extend IM).right_inv hp.1.1)
        (funext fun i ↦ by
          dsimp only [toFun]; rw [IteratedFiberProduct.val_apply, hinv_proj hp i]
          simp only [raw, ((φ i).extend IY).right_inv (hp_mem_tgt hp i),
            ContinuousLinearEquiv.apply_symm_apply])
      open_source := hΩ_open, open_target := hT_open
      contMDiffOn_toFun :=
        ((ψ.contMDiffOn_extend hψ_max).comp
          (contMDiff_baseProj_iteratedFiberProduct k hn hπ le_rfl).contMDiffOn
          (s := Ω) fun _ hy ↦ hy.1)
          |>.prodMk_space <| contMDiffOn_pi_module_iff.2 fun i ↦
            (((ContinuousLinearMap.snd ℝ EM F).comp
              (L i).toContinuousLinearMap).contDiff.contMDiff).comp_contMDiffOn <|
              ((φ i).contMDiffOn_extend (hφ_max i)).comp
                (contMDiff_proj_iteratedFiberProduct k hn hπ le_rfl i).contMDiffOn
                (s := Ω) fun _ hy ↦ (hy.2.2 i).1
      contMDiffOn_invFun := (contMDiffOn_iteratedFiberProduct_iff hn hπ le_rfl).2 fun i ↦ by
        let Q : (EM × (Fin k → F)) →L[ℝ] EY := (L i).symm.toContinuousLinearMap.comp <|
          (ContinuousLinearMap.fst ℝ EM (Fin k → F)).prod
            ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ EM (Fin k → F)))
        have hsymm_smooth : ContMDiffOn 𝓘(ℝ, EY) IY n
            (((φ i).extend IY).symm) (((φ i).extend IY).target) := by
          rw [show ((φ i).extend IY).target = IY '' (φ i).target by
            rw [(φ i).extend_target, IY.image_eq]]
          exact contMDiffOn_extend_symm (hφ_max i)
        exact (hsymm_smooth.comp Q.contDiff.contMDiff.contMDiffOn
          fun _ hp ↦ hp_mem_tgt hp i).congr fun _ hp ↦ hinv_proj hp i }
  exact ⟨U, V, Φ, hU_open, hV_open, hy₀_Ω, rfl, fun _ hy ↦ ⟨hy.1, rfl⟩, fun _ hp ↦ hinv_base hp⟩

end Manifold

end TauCeti
