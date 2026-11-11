/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Banach
public import Mathlib.Topology.MetricSpace.HolderNorm

/-!
# Hölder spaces `C^{k,α}` on a compact manifold

Let `M` be a manifold, `k` a natural number and `α` a nonnegative real. For a vector-valued
`C^n` map `f` with `k ≤ n`, a point `x` and a compact set `K` in the extended chart target at `x`,
`ContMDiffMap.chartHolderNorm x K k hk α f` is the `α`-Hölder seminorm of the `k`th coordinate
derivative `ContMDiffMap.chartIteratedFDeriv f x k hk` on `K`, and
`ContMDiffMap.MemChartHolder x K k hk α f` says that this derivative is `α`-Hölder on `K`.

A *compact chart atlas* `TauCeti.CompactChartAtlas I M` is a finite family of points `center i`
together with compact subsets `piece i` of the extended chart targets at them, whose relative
interiors cover `M`. Every compact manifold modelled on a locally compact space has one
(`TauCeti.CompactChartAtlas.instNonempty`). For such an atlas `A`, the space
`A.CkHolderSpace k α F` consists of the `C^k` maps `M → F` whose `k`th coordinate derivatives are
`α`-Hölder on every piece, with the norm

`‖f‖ = max_i max_{m ≤ k} sup_{K i} ‖D^m f‖ + ∑_i [D^k f]_{α, K i}`,

the finite-atlas `C^k` norm `ContMDiffMap.finiteAtlasSeminorm` plus the Hölder seminorms of the
`k`th coordinate derivatives on the pieces. It is a Banach space when `M` is boundaryless and
modelled on a locally compact space over `ℝ` or `ℂ`, and `F` is complete
(`TauCeti.CompactChartAtlas.CkHolderSpace.instCompleteSpace`). The comparison of the spaces
and norms of two atlases, by chart-change estimates, is not part of this file.

The derivatives are taken within the extended chart targets, so the definitions also apply to
manifolds with boundary and corners; only completeness uses that `M` is boundaryless.

## Main definitions

* `ContMDiffMap.chartHolderNorm`, `ContMDiffMap.MemChartHolder`: the Hölder seminorm of a
  coordinate derivative on a compact coordinate set, and its finiteness.
* `ContMDiffMap.finiteAtlasHolderSubmodule`: the maps whose `k`th coordinate derivatives are
  `α`-Hölder on every compact piece of a finite family.
* `TauCeti.CompactChartAtlas`: a finite atlas of compact coordinate pieces covering `M`.
* `TauCeti.CompactChartAtlas.CkHolderSpace`: the normed space `C^{k,α}(M, F)` of an atlas.

## Main results

* `TauCeti.CompactChartAtlas.CkHolderSpace.norm_def`: the norm is the finite-atlas `C^k` norm
  plus the Hölder seminorms of the `k`th coordinate derivatives on the pieces.
* `TauCeti.CompactChartAtlas.CkHolderSpace.norm_chartIteratedFDeriv_sub_le`: the Hölder estimate
  of the `k`th coordinate derivatives by the norm.
* `TauCeti.CompactChartAtlas.CkHolderSpace.instCompleteSpace`: completeness.

## References

* M. Taylor, *Partial Differential Equations III*, Chapter 13, for Hölder spaces on compact
  manifolds defined through finitely many charts.
-/

public section

open Set Filter Topology
open scoped Manifold NNReal

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} [IsManifold I n M]

section Chart

variable (x : M) (K : TopologicalSpace.Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n)
  (α : ℝ≥0)

/-- The `α`-Hölder seminorm of the `k`th coordinate derivative of `f` in the chart at `x`, on the
compact coordinate set `K`. It is zero when this derivative is not `α`-Hölder on `K`. -/
noncomputable def chartHolderNorm (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) : ℝ≥0 :=
  nnHolderNorm α ⇑((chartIteratedFDeriv f x k hk).restrict (K : Set (extChartAt I x).target))

/-- The `k`th coordinate derivative of `f` in the chart at `x` is `α`-Hölder on the compact
coordinate set `K`. -/
def MemChartHolder (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) : Prop :=
  MemHolder α ⇑((chartIteratedFDeriv f x k hk).restrict (K : Set (extChartAt I x).target))

variable {x K k hk α}

/-- The restricted coordinate derivative is additive. -/
theorem coe_restrict_chartIteratedFDeriv_add (f g : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    ⇑((chartIteratedFDeriv (f + g) x k hk).restrict (K : Set (extChartAt I x).target)) =
      ⇑((chartIteratedFDeriv f x k hk).restrict (K : Set (extChartAt I x).target)) +
        ⇑((chartIteratedFDeriv g x k hk).restrict (K : Set (extChartAt I x).target)) := by
  have h : chartIteratedFDeriv (f + g) x k hk =
      chartIteratedFDeriv f x k hk + chartIteratedFDeriv g x k hk :=
    (chartIteratedFDerivLinearMap_apply x k hk (f + g)).symm.trans
      ((map_add (chartIteratedFDerivLinearMap (F := F) x k hk) f g).trans
        (congrArg₂ (· + ·) (chartIteratedFDerivLinearMap_apply x k hk f)
          (chartIteratedFDerivLinearMap_apply x k hk g)))
  rw [h]
  rfl

/-- The restricted coordinate derivative commutes with scalar multiplication. -/
theorem coe_restrict_chartIteratedFDeriv_smul (c : 𝕜) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    ⇑((chartIteratedFDeriv (c • f) x k hk).restrict (K : Set (extChartAt I x).target)) =
      c • ⇑((chartIteratedFDeriv f x k hk).restrict (K : Set (extChartAt I x).target)) := by
  have h : chartIteratedFDeriv (c • f) x k hk = c • chartIteratedFDeriv f x k hk :=
    (chartIteratedFDerivLinearMap_apply x k hk (c • f)).symm.trans
      ((map_smul (chartIteratedFDerivLinearMap (F := F) x k hk) c f).trans
        (congrArg (c • ·) (chartIteratedFDerivLinearMap_apply x k hk f)))
  rw [h]
  rfl

/-- The restricted coordinate derivative commutes with subtraction. -/
theorem coe_restrict_chartIteratedFDeriv_sub (f g : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    ⇑((chartIteratedFDeriv (f - g) x k hk).restrict (K : Set (extChartAt I x).target)) =
      ⇑((chartIteratedFDeriv f x k hk).restrict (K : Set (extChartAt I x).target)) -
        ⇑((chartIteratedFDeriv g x k hk).restrict (K : Set (extChartAt I x).target)) := by
  rw [chartIteratedFDeriv_sub]
  rfl

/-- The restricted coordinate derivative of the zero map is zero. -/
@[simp]
theorem coe_restrict_chartIteratedFDeriv_zero :
    ⇑((chartIteratedFDeriv (0 : C^n⟮I, M; 𝓘(𝕜, F), F⟯) x k hk).restrict
      (K : Set (extChartAt I x).target)) = 0 := by
  have h := chartIteratedFDeriv_sub (0 : C^n⟮I, M; 𝓘(𝕜, F), F⟯) 0 x k hk
  rw [sub_self, sub_self] at h
  rw [h]
  rfl

/-- The zero map has Hölder coordinate derivatives. -/
theorem memChartHolder_zero : MemChartHolder (F := F) x K k hk α 0 := by
  rw [MemChartHolder, coe_restrict_chartIteratedFDeriv_zero]
  exact memHolder_zero

/-- The Hölder seminorm of the coordinate derivatives of the zero map is zero. -/
@[simp]
theorem chartHolderNorm_zero : chartHolderNorm (F := F) x K k hk α 0 = 0 := by
  rw [chartHolderNorm, coe_restrict_chartIteratedFDeriv_zero, nnHolderNorm_zero]

theorem MemChartHolder.add {f g : C^n⟮I, M; 𝓘(𝕜, F), F⟯} (hf : MemChartHolder x K k hk α f)
    (hg : MemChartHolder x K k hk α g) : MemChartHolder x K k hk α (f + g) := by
  rw [MemChartHolder, coe_restrict_chartIteratedFDeriv_add]
  exact MemHolder.add hf hg

theorem MemChartHolder.smul {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯} (hf : MemChartHolder x K k hk α f)
    (c : 𝕜) : MemChartHolder x K k hk α (c • f) := by
  rw [MemChartHolder, coe_restrict_chartIteratedFDeriv_smul]
  exact MemHolder.smul hf

/-- The Hölder seminorm of a coordinate derivative is subadditive on Hölder maps. -/
theorem chartHolderNorm_add_le {f g : C^n⟮I, M; 𝓘(𝕜, F), F⟯}
    (hf : MemChartHolder x K k hk α f) (hg : MemChartHolder x K k hk α g) :
    chartHolderNorm x K k hk α (f + g) ≤
      chartHolderNorm x K k hk α f + chartHolderNorm x K k hk α g := by
  rw [chartHolderNorm, coe_restrict_chartIteratedFDeriv_add]
  exact MemHolder.nnHolderNorm_add_le hf hg

/-- The Hölder seminorm of a coordinate derivative is absolutely homogeneous. -/
theorem chartHolderNorm_smul (c : 𝕜) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    chartHolderNorm x K k hk α (c • f) = ‖c‖₊ * chartHolderNorm x K k hk α f := by
  rw [chartHolderNorm, chartHolderNorm, coe_restrict_chartIteratedFDeriv_smul, nnHolderNorm,
    nnHolderNorm, eHolderNorm_smul (Y := E [×k]→L[𝕜] F) c, ENNReal.toNNReal_mul,
    ENNReal.toNNReal_coe]

/-- **Hölder estimate.** On a map whose coordinate derivative is Hölder, the Hölder seminorm
bounds the oscillation of the `k`th coordinate derivative on `K`. -/
theorem MemChartHolder.norm_chartIteratedFDeriv_sub_le {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯}
    (hf : MemChartHolder x K k hk α f) {z w : (extChartAt I x).target} (hz : z ∈ K)
    (hw : w ∈ K) :
    ‖chartIteratedFDeriv f x k hk z - chartIteratedFDeriv f x k hk w‖ ≤
      chartHolderNorm x K k hk α f * dist z w ^ (α : ℝ) := by
  have h := hf.holderWith.dist_le (⟨z, hz⟩ : (K : Set (extChartAt I x).target)) ⟨w, hw⟩
  rw [dist_eq_norm] at h
  exact h

end Chart

section FiniteAtlas

variable {ι : Type*} (c : ι → M)
  (K : ∀ i, TopologicalSpace.Compacts (extChartAt I (c i)).target) (k : ℕ) (hk : k ≤ n)
  (α : ℝ≥0)

/-- The vector-valued `C^n` maps whose `k`th coordinate derivatives in the charts at the points
`c i` are `α`-Hölder on the compact coordinate pieces `K i`. -/
def finiteAtlasHolderSubmodule : Submodule 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯ where
  carrier := {f | ∀ i, MemChartHolder (c i) (K i) k hk α f}
  zero_mem' _ := memChartHolder_zero
  add_mem' hf hg i := (hf i).add (hg i)
  smul_mem' a _ hf i := (hf i).smul a

theorem mem_finiteAtlasHolderSubmodule_iff (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    f ∈ finiteAtlasHolderSubmodule c K k hk α ↔ ∀ i, MemChartHolder (c i) (K i) k hk α f :=
  Iff.rfl

end FiniteAtlas

end ContMDiffMap

/-- A pointwise limit of maps that are `r`-Hölder with a common constant `C` is `r`-Hölder with
constant `C`. -/
private theorem holderWith_of_tendsto {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {C r : ℝ≥0} {u : ℕ → X → Y} {v : X → Y} (hu : ∀ x, Tendsto (fun n ↦ u n x) atTop (𝓝 (v x)))
    (hC : ∀ᶠ n in atTop, HolderWith C r (u n)) : HolderWith C r v := fun x y ↦
  le_of_tendsto ((hu x).edist (hu y)) (hC.mono fun _ hn ↦ hn x y)

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]

/-- A *compact chart atlas* of `M`: finitely many points `center i` of `M` with compact subsets
`piece i` of the extended chart targets at them, whose relative interiors cover `M`. Its pieces
define the finite-atlas `C^k` norm `ContMDiffMap.finiteAtlasSeminorm` and the Hölder spaces
`TauCeti.CompactChartAtlas.CkHolderSpace`. -/
structure CompactChartAtlas (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] where
  /-- The index type of the atlas. -/
  ι : Type
  /-- The atlas is finite. -/
  [fintype : Fintype ι]
  /-- The chart centers. -/
  center : ι → M
  /-- The compact coordinate pieces. -/
  piece : ∀ i, TopologicalSpace.Compacts (extChartAt I (center i)).target
  /-- The relative interiors of the pieces cover the manifold. -/
  interior_cover : ∀ y : M, ∃ i, ∃ hy : y ∈ (extChartAt I (center i)).source,
    (⟨extChartAt I (center i) y, (extChartAt I (center i)).map_source hy⟩ :
      (extChartAt I (center i)).target) ∈ interior (piece i : Set (extChartAt I (center i)).target)

namespace CompactChartAtlas

attribute [instance] CompactChartAtlas.fintype

variable {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Existence of compact chart atlases.** A compact manifold modelled on a locally compact space
has a compact chart atlas. -/
instance instNonempty [CompactSpace M] [LocallyCompactSpace H] :
    Nonempty (CompactChartAtlas I M) := by
  obtain ⟨N, c, K, hK⟩ := TauCeti.exists_finite_compact_chart_cover (I := I) (M := M)
  exact ⟨⟨Fin N, c, K, hK⟩⟩

variable (A : CompactChartAtlas I M) (k : ℕ) (α : ℝ≥0)
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsManifold I k M]

/-- The Hölder space `C^{k,α}(M, F)` of a compact chart atlas `A`: the `C^k` maps `M → F` whose
`k`th coordinate derivatives are `α`-Hölder on the pieces of `A`. Its norm
(`TauCeti.CompactChartAtlas.CkHolderSpace.norm_def`) is the finite-atlas `C^k` norm plus the
Hölder seminorms of the `k`th coordinate derivatives on the pieces. -/
@[expose] def CkHolderSpace : Type _ :=
  ↥(ContMDiffMap.finiteAtlasHolderSubmodule (F := F) (n := k) A.center A.piece k le_rfl α)

namespace CkHolderSpace

variable {A k α F}

instance instAddCommGroup : AddCommGroup (A.CkHolderSpace k α F) :=
  inferInstanceAs (AddCommGroup ↥(ContMDiffMap.finiteAtlasHolderSubmodule (F := F) (n := k)
    A.center A.piece k le_rfl α))

instance instModule : Module 𝕜 (A.CkHolderSpace k α F) :=
  inferInstanceAs (Module 𝕜 ↥(ContMDiffMap.finiteAtlasHolderSubmodule (F := F) (n := k)
    A.center A.piece k le_rfl α))

variable (A k α F) in
/-- The underlying `C^k` map, as a linear map. -/
@[expose] def toContMDiffMap : A.CkHolderSpace k α F →ₗ[𝕜] C^k⟮I, M; 𝓘(𝕜, F), F⟯ :=
  Submodule.subtype _

theorem toContMDiffMap_injective :
    Function.Injective (toContMDiffMap (𝕜 := 𝕜) A k α F) :=
  Subtype.val_injective

/-- The `k`th coordinate derivatives of an element are `α`-Hölder on the pieces. -/
theorem memChartHolder (f : A.CkHolderSpace k α F) (i : A.ι) :
    ContMDiffMap.MemChartHolder (A.center i) (A.piece i) k le_rfl α
      (toContMDiffMap A k α F f) :=
  f.2 i

/-- An element of `C^{k,α}(M, F)` from a `C^k` map whose `k`th coordinate derivatives are
`α`-Hölder on the pieces. -/
@[expose] def mk (f : C^k⟮I, M; 𝓘(𝕜, F), F⟯)
    (hf : ∀ i, ContMDiffMap.MemChartHolder (A.center i) (A.piece i) k le_rfl α f) :
    A.CkHolderSpace k α F :=
  ⟨f, (ContMDiffMap.mem_finiteAtlasHolderSubmodule_iff _ _ _ _ _ f).mpr hf⟩

@[simp]
theorem toContMDiffMap_mk (f : C^k⟮I, M; 𝓘(𝕜, F), F⟯)
    (hf : ∀ i, ContMDiffMap.MemChartHolder (A.center i) (A.piece i) k le_rfl α f) :
    toContMDiffMap A k α F (mk f hf) = f :=
  rfl

instance instFunLike : FunLike (A.CkHolderSpace k α F) M F where
  coe f := toContMDiffMap A k α F f
  coe_injective _ _ h := toContMDiffMap_injective (DFunLike.coe_injective h)

@[simp]
theorem coe_toContMDiffMap (f : A.CkHolderSpace k α F) : ⇑(toContMDiffMap A k α F f) = f :=
  rfl

@[ext]
theorem ext {f g : A.CkHolderSpace k α F} (h : ∀ y, f y = g y) : f = g :=
  DFunLike.ext _ _ h

/-- The `C^{k,α}` norm: the finite-atlas `C^k` norm plus the Hölder seminorms of the `k`th
coordinate derivatives on the pieces. -/
noncomputable instance instNorm : Norm (A.CkHolderSpace k α F) where
  norm f := ContMDiffMap.finiteAtlasSeminorm A.center A.piece k le_rfl (toContMDiffMap A k α F f) +
    ∑ i, (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α
      (toContMDiffMap A k α F f) : ℝ)

theorem norm_def (f : A.CkHolderSpace k α F) :
    ‖f‖ = ContMDiffMap.finiteAtlasSeminorm A.center A.piece k le_rfl (toContMDiffMap A k α F f) +
      ∑ i, (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α
        (toContMDiffMap A k α F f) : ℝ) :=
  rfl

/-- The normed group structure of the Hölder norm. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (A.CkHolderSpace k α F) :=
  NormedAddCommGroup.ofCore (𝕜 := 𝕜)
    { norm_nonneg f := add_nonneg (apply_nonneg _ _)
        (Finset.sum_nonneg fun _ _ ↦ NNReal.coe_nonneg _)
      norm_smul a f := by
        rw [norm_def, norm_def, map_smul, map_smul_eq_mul, mul_add, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [ContMDiffMap.chartHolderNorm_smul, NNReal.coe_mul, coe_nnnorm]
      norm_triangle f g := by
        rw [norm_def, norm_def, norm_def, map_add]
        have hsum : ∑ i, (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α
            (toContMDiffMap A k α F f + toContMDiffMap A k α F g) : ℝ) ≤
            ∑ i, (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α
              (toContMDiffMap A k α F f) : ℝ) +
            ∑ i, (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α
              (toContMDiffMap A k α F g) : ℝ) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun i _ ↦ by
            exact_mod_cast ContMDiffMap.chartHolderNorm_add_le (memChartHolder f i)
              (memChartHolder g i)
        linarith [map_add_le_add (ContMDiffMap.finiteAtlasSeminorm (F := F) A.center A.piece k
          le_rfl) (toContMDiffMap A k α F f) (toContMDiffMap A k α F g)]
      norm_eq_zero_iff f := by
        constructor
        · intro h
          have h0 : ContMDiffMap.finiteAtlasSeminorm A.center A.piece k le_rfl
              (toContMDiffMap A k α F f) = 0 := by
            have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦
              (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α
                (toContMDiffMap A k α F f)).coe_nonneg
            have := apply_nonneg (ContMDiffMap.finiteAtlasSeminorm (F := F) A.center A.piece k
              le_rfl) (toContMDiffMap A k α F f)
            rw [norm_def] at h
            linarith
          refine toContMDiffMap_injective ?_
          rw [map_zero]
          exact (ContMDiffMap.finiteAtlasSeminorm_eq_zero_iff
            (fun y ↦ (A.interior_cover y).imp fun _ ⟨hy, hyK⟩ ↦ ⟨hy, interior_subset hyK⟩)
            k le_rfl _).mp h0
        · rintro rfl
          rw [norm_def, map_zero, map_zero]
          simp }

/-- The normed space structure of the Hölder norm. -/
noncomputable instance instNormedSpace : NormedSpace 𝕜 (A.CkHolderSpace k α F) where
  norm_smul_le a f := by
    rw [norm_def, norm_def, map_smul, map_smul_eq_mul, mul_add, Finset.mul_sum]
    refine (add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦ ?_))
    rw [ContMDiffMap.chartHolderNorm_smul, NNReal.coe_mul, coe_nnnorm]

/-- The finite-atlas `C^k` norm is bounded by the Hölder norm. -/
theorem finiteAtlasSeminorm_le_norm (f : A.CkHolderSpace k α F) :
    ContMDiffMap.finiteAtlasSeminorm A.center A.piece k le_rfl (toContMDiffMap A k α F f) ≤
      ‖f‖ := by
  rw [norm_def]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ NNReal.coe_nonneg _)

/-- The Hölder seminorm on each piece is bounded by the Hölder norm. -/
theorem chartHolderNorm_le_norm (f : A.CkHolderSpace k α F) (i : A.ι) :
    (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α
      (toContMDiffMap A k α F f) : ℝ) ≤ ‖f‖ := by
  rw [norm_def]
  exact le_add_of_nonneg_of_le (apply_nonneg _ _)
    (Finset.single_le_sum (f := fun i ↦ (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i)
      k le_rfl α (toContMDiffMap A k α F f) : ℝ)) (fun _ _ ↦ NNReal.coe_nonneg _)
      (Finset.mem_univ i))

/-- The coordinate derivatives of order at most `k` are bounded on the pieces by the Hölder
norm. -/
theorem norm_chartIteratedFDeriv_le (f : A.CkHolderSpace k α F) (i : A.ι) {m : ℕ} (hm : m ≤ k)
    {z : (extChartAt I (A.center i)).target} (hz : z ∈ A.piece i) :
    ‖ContMDiffMap.chartIteratedFDeriv (toContMDiffMap A k α F f) (A.center i) m
      (Nat.cast_le.mpr hm) z‖ ≤ ‖f‖ :=
  (ContMDiffMap.finiteAtlasSeminorm_le_iff A.center A.piece k le_rfl _ (norm_nonneg f)).mp
    (finiteAtlasSeminorm_le_norm f) i m hm z hz

/-- **Hölder estimate.** The oscillation of the `k`th coordinate derivative on a piece is bounded
by the Hölder norm times the `α`th power of the distance. -/
theorem norm_chartIteratedFDeriv_sub_le (f : A.CkHolderSpace k α F) (i : A.ι)
    {z w : (extChartAt I (A.center i)).target} (hz : z ∈ A.piece i) (hw : w ∈ A.piece i) :
    ‖ContMDiffMap.chartIteratedFDeriv (toContMDiffMap A k α F f) (A.center i) k le_rfl z -
      ContMDiffMap.chartIteratedFDeriv (toContMDiffMap A k α F f) (A.center i) k le_rfl w‖ ≤
      ‖f‖ * dist z w ^ (α : ℝ) :=
  ((memChartHolder f i).norm_chartIteratedFDeriv_sub_le hz hw).trans
    (mul_le_mul_of_nonneg_right (chartHolderNorm_le_norm f i)
      (Real.rpow_nonneg dist_nonneg _))

section Complete

variable [IsRCLikeNormedField 𝕜] [LocallyCompactSpace E] [I.Boundaryless] [CompleteSpace F]

/-- **The Banach space `C^{k,α}(M, F)`.** On a boundaryless manifold modelled on a locally
compact space over `ℝ` or `ℂ`, the Hölder space of a compact chart atlas with values in a Banach
space is complete. -/
instance instCompleteSpace : CompleteSpace (A.CkHolderSpace k α F) := by
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := F) k A.interior_cover
  have := ContMDiffMap.completeSpace_finiteAtlas (F := F) k A.interior_cover
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  let D (f : C^k⟮I, M; 𝓘(𝕜, F), F⟯) (i : A.ι)
      (z : (A.piece i : Set (extChartAt I (A.center i)).target)) : E [×k]→L[𝕜] F :=
    ContMDiffMap.chartIteratedFDeriv f (A.center i) k le_rfl z
  let v (n : ℕ) : C^k⟮I, M; 𝓘(𝕜, F), F⟯ := toContMDiffMap A k α F (u n)
  -- The underlying `C^k` maps form a Cauchy sequence for the finite-atlas norm.
  have hv : CauchySeq v := by
    refine Metric.cauchySeq_iff.mpr fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have h := hN m hm n hn
    rw [dist_eq_norm] at h ⊢
    rw [ContMDiffMap.norm_finiteAtlas]
    refine lt_of_le_of_lt ?_ h
    rw [← map_sub]
    exact finiteAtlasSeminorm_le_norm (u m - u n)
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hv
  have hg0 : Tendsto (fun n ↦ ContMDiffMap.finiteAtlasSeminorm A.center A.piece k le_rfl
      (v n - g)) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hg
  -- The `k`th coordinate derivatives converge pointwise on the pieces.
  have hpt (i : A.ι) (z : (A.piece i : Set (extChartAt I (A.center i)).target)) :
      Tendsto (fun n ↦ D (v n) i z) atTop (𝓝 (D g i z)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hg0
    have h := (ContMDiffMap.finiteAtlasSeminorm_le_iff A.center A.piece k le_rfl (v n - g)
      (apply_nonneg _ _)).mp le_rfl i k le_rfl z z.2
    rwa [ContMDiffMap.chartIteratedFDeriv_sub, ContinuousMap.sub_apply] at h
  -- A uniform bound on the tail of the sequence bounds the Hölder seminorm of the difference
  -- with the limit.
  have hH (n : ℕ) (C : ℝ≥0) (hC : ∀ m ≥ n, ‖u n - u m‖ ≤ C) (i : A.ι) :
      HolderWith C α (fun z ↦ D (v n) i z - D g i z) := by
    refine holderWith_of_tendsto (fun z ↦ tendsto_const_nhds.sub (hpt i z)) ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    have h1 := (memChartHolder (u n - u m) i).holderWith
    have h2 : ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α
        (toContMDiffMap A k α F (u n - u m)) ≤ C := by
      exact_mod_cast (chartHolderNorm_le_norm (u n - u m) i).trans (hC m hm)
    have heq : ⇑((ContMDiffMap.chartIteratedFDeriv (toContMDiffMap A k α F (u n - u m))
        (A.center i) k le_rfl).restrict (A.piece i : Set _)) =
        fun z ↦ D (v n) i z - D (v m) i z := by
      rw [map_sub, ContMDiffMap.coe_restrict_chartIteratedFDeriv_sub]
      rfl
    rw [← heq]
    exact h1.mono h2
  have htail (C : ℝ≥0) (hC : 0 < C) : ∃ N, ∀ n ≥ N, ∀ m ≥ n, ‖u n - u m‖ ≤ C := by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu C hC
    refine ⟨N, fun n hn m hm ↦ ?_⟩
    have h := hN n hn m (hn.trans hm)
    rw [dist_eq_norm] at h
    exact h.le
  -- The limit lies in the Hölder space.
  have hmem (i : A.ι) : ContMDiffMap.MemChartHolder (A.center i) (A.piece i) k le_rfl α g := by
    obtain ⟨N, hN⟩ := htail 1 zero_lt_one
    have heq : ⇑((ContMDiffMap.chartIteratedFDeriv g (A.center i) k le_rfl).restrict
        (A.piece i : Set (extChartAt I (A.center i)).target)) =
        ⇑((ContMDiffMap.chartIteratedFDeriv (v N) (A.center i) k le_rfl).restrict
          (A.piece i : Set (extChartAt I (A.center i)).target)) +
          (-1 : 𝕜) • fun z ↦ D (v N) i z - D g i z := by
      funext z
      change D g i z = D (v N) i z + (-1 : 𝕜) • (D (v N) i z - D g i z)
      rw [neg_one_smul, neg_sub, add_sub_cancel]
    have h1 : MemHolder α ⇑((ContMDiffMap.chartIteratedFDeriv (v N) (A.center i) k
        le_rfl).restrict (A.piece i : Set (extChartAt I (A.center i)).target)) :=
      memChartHolder (u N) i
    have h2 : MemHolder α ((-1 : 𝕜) • fun z ↦ D (v N) i z - D g i z) :=
      MemHolder.smul (hH N 1 (hN N le_rfl) i).memHolder
    rw [ContMDiffMap.MemChartHolder, heq]
    exact h1.add h2
  refine ⟨mk g hmem, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  have hc : (0 : ℝ) < Fintype.card A.ι + 1 := by positivity
  let C : ℝ≥0 := ⟨ε / (4 * (Fintype.card A.ι + 1)), by positivity⟩
  have hCval : (C : ℝ) = ε / (4 * (Fintype.card A.ι + 1)) := rfl
  have hCpos : 0 < C := by
    rw [← NNReal.coe_pos, hCval]
    positivity
  have hcardC : (Fintype.card A.ι : ℝ) * C ≤ ε / 4 := by
    have h : ((Fintype.card A.ι : ℝ) + 1) * C = ε / 4 := by
      rw [hCval]
      field_simp
    calc (Fintype.card A.ι : ℝ) * C ≤ ((Fintype.card A.ι : ℝ) + 1) * C :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) C.coe_nonneg
      _ = ε / 4 := h
  obtain ⟨N₁, hN₁⟩ := htail C hCpos
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hg0 (ε / 2) (half_pos hε)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hsup : ContMDiffMap.finiteAtlasSeminorm A.center A.piece k le_rfl (v n - g) < ε / 2 := by
    have h := hN₂ n (le_of_max_le_right hn)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)] at h
  have hhol (i : A.ι) : (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α
      (v n - g) : ℝ) ≤ C := by
    have heq : ⇑((ContMDiffMap.chartIteratedFDeriv (v n - g) (A.center i) k le_rfl).restrict
        (A.piece i : Set (extChartAt I (A.center i)).target)) =
        fun z ↦ D (v n) i z - D g i z := by
      rw [ContMDiffMap.coe_restrict_chartIteratedFDeriv_sub]
      rfl
    rw [ContMDiffMap.chartHolderNorm, heq]
    exact_mod_cast (hH n C (hN₁ n (le_of_max_le_left hn)) i).nnholderNorm_le
  have hnorm : ‖u n - mk g hmem‖ =
      ContMDiffMap.finiteAtlasSeminorm A.center A.piece k le_rfl (v n - g) +
        ∑ i, (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α (v n - g) : ℝ) := by
    rw [norm_def, map_sub]
    rfl
  rw [dist_eq_norm, hnorm]
  calc _ ≤ ε / 2 + ∑ _i : A.ι, (C : ℝ) := add_le_add hsup.le (Finset.sum_le_sum fun i _ ↦ hhol i)
    _ = ε / 2 + Fintype.card A.ι * C := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ < ε := by linarith

end Complete

end CkHolderSpace

end CompactChartAtlas

end TauCeti
