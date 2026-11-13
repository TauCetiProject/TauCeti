/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Banach
public import Mathlib.Topology.MetricSpace.HolderNorm
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder spaces `C^{k,α}` on a compact manifold

Let `M` be a manifold, `k` a natural number and `α` a nonnegative real. For a vector-valued
`C^n` map `f` with `k ≤ n`, a point `x` and a set `K` in the extended chart target at `x`,
`ContMDiffMap.chartHolderNorm x K k hk α f` is the `α`-Hölder seminorm of the `k`th coordinate
derivative `ContMDiffMap.chartIteratedFDeriv f x k hk` on `K`, and
`ContMDiffMap.MemChartHolder x K k hk α f` says that this derivative is `α`-Hölder on `K`.

For a compact chart atlas `A : TauCeti.CompactChartAtlas I M`, the space `A.CkHolderSpace k α F`
consists of the `C^k` maps `M → F` whose `k`th coordinate derivatives are `α`-Hölder on every
piece, with the norm

`‖f‖ = max_i max_{m ≤ k} sup_{K i} ‖D^m f‖ + ∑_i [D^k f]_{α, K i}`,

the finite-atlas `C^k` norm `ContMDiffMap.finiteAtlasSeminorm` plus the Hölder seminorms of the
`k`th coordinate derivatives on the pieces. It is a Banach space when `M` is boundaryless and
modelled on a locally compact space over `ℝ` or `ℂ`, and `F` is complete
(`TauCeti.CompactChartAtlas.CkHolderSpace.instCompleteSpace`). The comparison of the spaces
and norms of two atlases, by chart-change estimates, is not part of this file.

The usual Hölder spaces are those with `0 < α ≤ 1`, but the definitions accept every `α`.

The derivatives are taken within the extended chart targets, so the definitions also apply to
manifolds with boundary and corners; only completeness uses that `M` is boundaryless.

## Main definitions

* `ContMDiffMap.chartHolderNorm`, `ContMDiffMap.MemChartHolder`: the Hölder seminorm of a
  coordinate derivative on a coordinate set, and its finiteness.
* `ContMDiffMap.finiteAtlasHolderSubmodule`: the maps whose `k`th coordinate derivatives are
  `α`-Hölder on every piece of a finite family.
* `TauCeti.CompactChartAtlas.CkHolderSpace`: the normed space `C^{k,α}(M, F)` of an atlas.

## Main results

* `ContMDiffMap.holderWith_restrict_chartIteratedFDeriv_of_tendsto`: Hölder bounds on the
  `k`th coordinate derivatives pass to pointwise limits.
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

variable (x : M) (K : Set (extChartAt I x).target) (k : ℕ) (hk : k ≤ n) (α : ℝ≥0)

/-- The `α`-Hölder seminorm of the `k`th coordinate derivative of `f` in the chart at `x`, on the
coordinate set `K`. It is zero when this derivative is not `α`-Hölder on `K`. -/
noncomputable def chartHolderNorm (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) : ℝ≥0 :=
  nnHolderNorm α ⇑((chartIteratedFDeriv f x k hk).restrict K)

/-- The `k`th coordinate derivative of `f` in the chart at `x` is `α`-Hölder on the coordinate
set `K`. -/
def MemChartHolder (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) : Prop :=
  MemHolder α ⇑((chartIteratedFDeriv f x k hk).restrict K)

variable {x K k hk α}

theorem chartHolderNorm_def (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    chartHolderNorm x K k hk α f = nnHolderNorm α ⇑((chartIteratedFDeriv f x k hk).restrict K) :=
  (rfl)

theorem memChartHolder_iff {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯} :
    MemChartHolder x K k hk α f ↔ MemHolder α ⇑((chartIteratedFDeriv f x k hk).restrict K) :=
  Iff.rfl

/-- A coordinate derivative that is `α`-Hölder on `K` with some constant is Hölder. -/
theorem MemChartHolder.of_holderOnWith {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯} {C : ℝ≥0}
    (h : HolderOnWith C α (chartIteratedFDeriv f x k hk) K) : MemChartHolder x K k hk α f :=
  ⟨C, h.holderWith⟩

/-- A bound on the oscillation of the `k`th coordinate derivative on `K` by `C` times the `α`th
power of the distance makes it `α`-Hölder on `K`. -/
theorem MemChartHolder.of_norm_sub_le {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯} {C : ℝ≥0}
    (h : ∀ z ∈ K, ∀ w ∈ K, ‖chartIteratedFDeriv f x k hk z - chartIteratedFDeriv f x k hk w‖ ≤
      C * dist z w ^ (α : ℝ)) :
    MemChartHolder x K k hk α f :=
  .of_holderOnWith (C := C) <| HolderOnWith.of_dist_le fun z hz w hw ↦ by
    simpa only [dist_eq_norm] using h z hz w hw

/-- A Hölder constant of the coordinate derivative on `K` bounds its Hölder seminorm. -/
theorem chartHolderNorm_le_of_holderOnWith {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯} {C : ℝ≥0}
    (h : HolderOnWith C α (chartIteratedFDeriv f x k hk) K) :
    chartHolderNorm x K k hk α f ≤ C :=
  h.holderWith.nnholderNorm_le

/-- A bound on the oscillation of the `k`th coordinate derivative on `K` by `C` times the `α`th
power of the distance bounds its Hölder seminorm by `C`. -/
theorem chartHolderNorm_le_of_norm_sub_le {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯} {C : ℝ≥0}
    (h : ∀ z ∈ K, ∀ w ∈ K, ‖chartIteratedFDeriv f x k hk z - chartIteratedFDeriv f x k hk w‖ ≤
      C * dist z w ^ (α : ℝ)) :
    chartHolderNorm x K k hk α f ≤ C :=
  chartHolderNorm_le_of_holderOnWith <| HolderOnWith.of_dist_le fun z hz w hw ↦ by
    simpa only [dist_eq_norm] using h z hz w hw

/-- The zero map has Hölder coordinate derivatives. -/
@[simp]
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

theorem MemChartHolder.neg {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯} (hf : MemChartHolder x K k hk α f) :
    MemChartHolder x K k hk α (-f) := by
  rw [← neg_one_smul 𝕜 f]
  exact hf.smul (-1)

@[simp]
theorem memChartHolder_neg {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯} :
    MemChartHolder x K k hk α (-f) ↔ MemChartHolder x K k hk α f :=
  ⟨fun h ↦ neg_neg f ▸ h.neg, MemChartHolder.neg⟩

theorem MemChartHolder.sub {f g : C^n⟮I, M; 𝓘(𝕜, F), F⟯} (hf : MemChartHolder x K k hk α f)
    (hg : MemChartHolder x K k hk α g) : MemChartHolder x K k hk α (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- The Hölder seminorm of a coordinate derivative is subadditive on Hölder maps. -/
theorem chartHolderNorm_add_le {f g : C^n⟮I, M; 𝓘(𝕜, F), F⟯}
    (hf : MemChartHolder x K k hk α f) (hg : MemChartHolder x K k hk α g) :
    chartHolderNorm x K k hk α (f + g) ≤
      chartHolderNorm x K k hk α f + chartHolderNorm x K k hk α g := by
  rw [chartHolderNorm, coe_restrict_chartIteratedFDeriv_add]
  exact MemHolder.nnHolderNorm_add_le hf hg

/-- The Hölder seminorm of a coordinate derivative is absolutely homogeneous. -/
@[simp]
theorem chartHolderNorm_smul (c : 𝕜) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    chartHolderNorm x K k hk α (c • f) = ‖c‖₊ * chartHolderNorm x K k hk α f := by
  simp only [chartHolderNorm, coe_restrict_chartIteratedFDeriv_smul, nnHolderNorm,
    eHolderNorm_smul (Y := E [×k]→L[𝕜] F) c, ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]

@[simp]
theorem chartHolderNorm_neg (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    chartHolderNorm x K k hk α (-f) = chartHolderNorm x K k hk α f := by
  rw [← neg_one_smul 𝕜 f, chartHolderNorm_smul, nnNorm_neg, nnNorm_one, one_mul]

/-- **Hölder estimate.** On a map whose coordinate derivative is Hölder, the Hölder seminorm
bounds the oscillation of the `k`th coordinate derivative on `K`. -/
theorem MemChartHolder.norm_chartIteratedFDeriv_sub_le {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯}
    (hf : MemChartHolder x K k hk α f) {z w : (extChartAt I x).target} (hz : z ∈ K)
    (hw : w ∈ K) :
    ‖chartIteratedFDeriv f x k hk z - chartIteratedFDeriv f x k hk w‖ ≤
      chartHolderNorm x K k hk α f * dist z w ^ (α : ℝ) := by
  simpa only [chartHolderNorm, dist_eq_norm, ContinuousMap.restrict_apply, Subtype.dist_eq] using
    hf.holderWith.dist_le (⟨z, hz⟩ : K) ⟨w, hw⟩

/-- On a map whose coordinate derivative is Hölder on `K`, the Hölder seminorm is at most `C`
exactly when `C` bounds the oscillation of the `k`th coordinate derivative on `K` against the
`α`th power of the distance. -/
theorem MemChartHolder.chartHolderNorm_le_iff {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯}
    (hf : MemChartHolder x K k hk α f) {C : ℝ≥0} :
    chartHolderNorm x K k hk α f ≤ C ↔
      ∀ z ∈ K, ∀ w ∈ K, ‖chartIteratedFDeriv f x k hk z - chartIteratedFDeriv f x k hk w‖ ≤
        C * dist z w ^ (α : ℝ) :=
  ⟨fun h _ hz _ hw ↦ (hf.norm_chartIteratedFDeriv_sub_le hz hw).trans
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr h) (Real.rpow_nonneg dist_nonneg _)),
    chartHolderNorm_le_of_norm_sub_le⟩

/-- **Hölder bounds pass to limits.** If the `k`th coordinate derivatives of `u b` converge
pointwise on `K` to those of `g` along `l`, and eventually along `l` they are `α`-Hölder on `K`
with seminorm at most `C`, then the `k`th coordinate derivative of `g` is `α`-Hölder on `K` with
constant `C`. -/
theorem holderWith_restrict_chartIteratedFDeriv_of_tendsto {β : Type*} {l : Filter β} [l.NeBot]
    {u : β → C^n⟮I, M; 𝓘(𝕜, F), F⟯} {g : C^n⟮I, M; 𝓘(𝕜, F), F⟯} {C : ℝ≥0}
    (hu : ∀ z ∈ K, Tendsto (fun b ↦ chartIteratedFDeriv (u b) x k hk z) l
      (𝓝 (chartIteratedFDeriv g x k hk z)))
    (hmem : ∀ᶠ b in l, MemChartHolder x K k hk α (u b))
    (hC : ∀ᶠ b in l, chartHolderNorm x K k hk α (u b) ≤ C) :
    HolderWith C α ⇑((chartIteratedFDeriv g x k hk).restrict K) :=
  HolderWith.of_tendsto (u := fun b ↦ ⇑((chartIteratedFDeriv (u b) x k hk).restrict K))
    (fun z ↦ hu z z.2) ((hmem.and hC).mono fun _ hb ↦ hb.1.holderWith.mono hb.2)

/-- A pointwise limit on `K` of `k`th coordinate derivatives that are eventually `α`-Hölder on `K`
with bounded seminorms is `α`-Hölder on `K`. -/
theorem MemChartHolder.of_tendsto {β : Type*} {l : Filter β} [l.NeBot]
    {u : β → C^n⟮I, M; 𝓘(𝕜, F), F⟯} {g : C^n⟮I, M; 𝓘(𝕜, F), F⟯} {C : ℝ≥0}
    (hu : ∀ z ∈ K, Tendsto (fun b ↦ chartIteratedFDeriv (u b) x k hk z) l
      (𝓝 (chartIteratedFDeriv g x k hk z)))
    (hmem : ∀ᶠ b in l, MemChartHolder x K k hk α (u b))
    (hC : ∀ᶠ b in l, chartHolderNorm x K k hk α (u b) ≤ C) :
    MemChartHolder x K k hk α g :=
  (holderWith_restrict_chartIteratedFDeriv_of_tendsto hu hmem hC).memHolder

/-- A bound on the Hölder seminorms of `k`th coordinate derivatives that converge pointwise on
`K` passes to the limit. -/
theorem chartHolderNorm_le_of_tendsto {β : Type*} {l : Filter β} [l.NeBot]
    {u : β → C^n⟮I, M; 𝓘(𝕜, F), F⟯} {g : C^n⟮I, M; 𝓘(𝕜, F), F⟯} {C : ℝ≥0}
    (hu : ∀ z ∈ K, Tendsto (fun b ↦ chartIteratedFDeriv (u b) x k hk z) l
      (𝓝 (chartIteratedFDeriv g x k hk z)))
    (hmem : ∀ᶠ b in l, MemChartHolder x K k hk α (u b))
    (hC : ∀ᶠ b in l, chartHolderNorm x K k hk α (u b) ≤ C) :
    chartHolderNorm x K k hk α g ≤ C :=
  (holderWith_restrict_chartIteratedFDeriv_of_tendsto hu hmem hC).nnholderNorm_le

end Chart

section FiniteAtlas

variable {ι : Type*} (c : ι → M) (K : ∀ i, Set (extChartAt I (c i)).target) (k : ℕ) (hk : k ≤ n)
  (α : ℝ≥0)

/-- The vector-valued `C^n` maps whose `k`th coordinate derivatives in the charts at the points
`c i` are `α`-Hölder on the coordinate pieces `K i`. -/
def finiteAtlasHolderSubmodule : Submodule 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯ where
  carrier := {f | ∀ i, MemChartHolder (c i) (K i) k hk α f}
  zero_mem' _ := memChartHolder_zero
  add_mem' hf hg i := (hf i).add (hg i)
  smul_mem' a _ hf i := (hf i).smul a

@[simp]
theorem mem_finiteAtlasHolderSubmodule_iff (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    f ∈ finiteAtlasHolderSubmodule c K k hk α ↔ ∀ i, MemChartHolder (c i) (K i) k hk α f :=
  Iff.rfl

end FiniteAtlas

end ContMDiffMap

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]

namespace CompactChartAtlas

noncomputable section

variable {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (A : CompactChartAtlas I M) (k : ℕ) (α : ℝ≥0)
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsManifold I k M]

/-- The Hölder space `C^{k,α}(M, F)` of a compact chart atlas `A`: the `C^k` maps `M → F` whose
`k`th coordinate derivatives are `α`-Hölder on the pieces of `A`. Its norm
(`TauCeti.CompactChartAtlas.CkHolderSpace.norm_def`) is the finite-atlas `C^k` norm plus the
Hölder seminorms of the `k`th coordinate derivatives on the pieces. The usual range of exponents
is `0 < α ≤ 1`. -/
def CkHolderSpace : Type _ :=
  ↥(ContMDiffMap.finiteAtlasHolderSubmodule (F := F) (n := k) A.center
    (fun i ↦ (A.piece i : Set (extChartAt I (A.center i)).target)) k le_rfl α)

namespace CkHolderSpace

variable {A k α F}

instance instAddCommGroup : AddCommGroup (A.CkHolderSpace k α F) :=
  inferInstanceAs (AddCommGroup ↥(ContMDiffMap.finiteAtlasHolderSubmodule (F := F) (n := k)
    A.center (fun i ↦ (A.piece i : Set (extChartAt I (A.center i)).target)) k le_rfl α))

instance instModule : Module 𝕜 (A.CkHolderSpace k α F) :=
  inferInstanceAs (Module 𝕜 ↥(ContMDiffMap.finiteAtlasHolderSubmodule (F := F) (n := k)
    A.center (fun i ↦ (A.piece i : Set (extChartAt I (A.center i)).target)) k le_rfl α))

variable (A k α F) in
/-- The underlying `C^k` map, as a linear map. -/
def toContMDiffMap : A.CkHolderSpace k α F →ₗ[𝕜] C^k⟮I, M; 𝓘(𝕜, F), F⟯ :=
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
def mk (f : C^k⟮I, M; 𝓘(𝕜, F), F⟯)
    (hf : ∀ i, ContMDiffMap.MemChartHolder (A.center i) (A.piece i) k le_rfl α f) :
    A.CkHolderSpace k α F :=
  ⟨f, (ContMDiffMap.mem_finiteAtlasHolderSubmodule_iff _ _ _ _ _ f).mpr hf⟩

@[simp]
theorem toContMDiffMap_mk (f : C^k⟮I, M; 𝓘(𝕜, F), F⟯)
    (hf : ∀ i, ContMDiffMap.MemChartHolder (A.center i) (A.piece i) k le_rfl α f) :
    toContMDiffMap A k α F (mk f hf) = f :=
  (rfl)

@[simp]
theorem mk_toContMDiffMap (f : A.CkHolderSpace k α F) :
    mk (toContMDiffMap A k α F f) (memChartHolder f) = f :=
  (rfl)

instance instFunLike : FunLike (A.CkHolderSpace k α F) M F where
  coe f := toContMDiffMap A k α F f
  coe_injective _ _ h := toContMDiffMap_injective (DFunLike.coe_injective h)

@[simp]
theorem coe_toContMDiffMap (f : A.CkHolderSpace k α F) : ⇑(toContMDiffMap A k α F f) = f :=
  (rfl)

@[ext]
theorem ext {f g : A.CkHolderSpace k α F} (h : ∀ y, f y = g y) : f = g :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_mk (f : C^k⟮I, M; 𝓘(𝕜, F), F⟯)
    (hf : ∀ i, ContMDiffMap.MemChartHolder (A.center i) (A.piece i) k le_rfl α f) :
    ⇑(mk f hf) = f :=
  (rfl)

@[simp]
theorem coe_zero : ⇑(0 : A.CkHolderSpace k α F) = 0 :=
  (rfl)

@[simp]
theorem coe_add (f g : A.CkHolderSpace k α F) : ⇑(f + g) = f + g :=
  (rfl)

@[simp]
theorem coe_neg (f : A.CkHolderSpace k α F) : ⇑(-f) = -f :=
  (rfl)

@[simp]
theorem coe_sub (f g : A.CkHolderSpace k α F) : ⇑(f - g) = f - g :=
  (rfl)

@[simp]
theorem coe_smul (c : 𝕜) (f : A.CkHolderSpace k α F) : ⇑(c • f) = c • ⇑f :=
  (rfl)

/-- An element of `C^{k,α}(M, F)` is `C^k`. -/
protected theorem contMDiff (f : A.CkHolderSpace k α F) : ContMDiff I 𝓘(𝕜, F) k f :=
  ContMDiffMap.contMDiff (toContMDiffMap A k α F f)

instance instContinuousMapClass : ContinuousMapClass (A.CkHolderSpace k α F) M F where
  map_continuous f := (ContMDiffMap.contMDiff (toContMDiffMap A k α F f)).continuous

/-- The `C^{k,α}` norm: the finite-atlas `C^k` norm plus the Hölder seminorms of the `k`th
coordinate derivatives on the pieces. -/
noncomputable instance instNorm : Norm (A.CkHolderSpace k α F) where
  norm f := ContMDiffMap.finiteAtlasSeminorm A.center A.piece k le_rfl (toContMDiffMap A k α F f) +
    ∑ i, (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α
      (toContMDiffMap A k α F f) : ℝ)

/-- The `C^{k,α}` norm is the finite-atlas `C^k` norm plus the sum over the pieces of the
`α`-Hölder seminorms of the `k`th coordinate derivatives. -/
theorem norm_def (f : A.CkHolderSpace k α F) :
    ‖f‖ = ContMDiffMap.finiteAtlasSeminorm A.center A.piece k le_rfl (toContMDiffMap A k α F f) +
      ∑ i, (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α
        (toContMDiffMap A k α F f) : ℝ) :=
  (rfl)

/-- The `C^{k,α}` norm is absolutely homogeneous. -/
private theorem norm_smul_eq (a : 𝕜) (f : A.CkHolderSpace k α F) : ‖a • f‖ = ‖a‖ * ‖f‖ := by
  rw [norm_def, norm_def, map_smul, map_smul_eq_mul, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ContMDiffMap.chartHolderNorm_smul, NNReal.coe_mul, coe_nnNorm]

/-- The `C^{k,α}` norm vanishes only at zero. -/
private theorem norm_eq_zero_iff' (f : A.CkHolderSpace k α F) : ‖f‖ = 0 ↔ f = 0 := by
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
    rw [norm_def, map_zero, map_zero, zero_add]
    exact Finset.sum_eq_zero fun i _ ↦ by
      rw [ContMDiffMap.chartHolderNorm_zero, NNReal.coe_zero]

/-- The normed group structure of the Hölder norm. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (A.CkHolderSpace k α F) :=
  NormedAddCommGroup.ofCore (𝕜 := 𝕜)
    { norm_nonneg f := add_nonneg (apply_nonneg _ _)
        (Finset.sum_nonneg fun _ _ ↦ NNReal.coe_nonneg _)
      norm_smul a f := by exact norm_smul_eq a f
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
      norm_eq_zero_iff f := by exact norm_eq_zero_iff' f }

/-- The normed space structure of the Hölder norm. -/
noncomputable instance instNormedSpace : NormedSpace 𝕜 (A.CkHolderSpace k α F) where
  norm_smul_le a f := by exact (norm_smul_eq a f).le

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
    -- Naming `I` lets the coercion of `A.piece i` to a set elaborate without a timeout.
    (Finset.single_le_sum (f := fun i ↦ (ContMDiffMap.chartHolderNorm (I := I) (A.center i)
      (A.piece i) k le_rfl α (toContMDiffMap A k α F f) : ℝ)) (fun _ _ ↦ NNReal.coe_nonneg _)
      (Finset.mem_univ i))

/-- The coordinate derivatives of order at most `k` are bounded on the pieces by the Hölder
norm. -/
theorem norm_chartIteratedFDeriv_le (f : A.CkHolderSpace k α F) (i : A.ι) {m : ℕ} (hm : m ≤ k)
    {z : (extChartAt I (A.center i)).target} (hz : z ∈ A.piece i) :
    ‖ContMDiffMap.chartIteratedFDeriv (toContMDiffMap A k α F f) (A.center i) m
      (Nat.cast_le.mpr hm) z‖ ≤ ‖f‖ :=
  (ContMDiffMap.finiteAtlasSeminorm_le_iff A.center A.piece k le_rfl _ (norm_nonneg f)).mp
    (finiteAtlasSeminorm_le_norm f) i m hm z hz

/-- The values of an element are bounded by its Hölder norm. -/
theorem norm_apply_le (f : A.CkHolderSpace k α F) (y : M) : ‖f y‖ ≤ ‖f‖ := by
  obtain ⟨i, hy, hyK⟩ := A.interior_cover y
  refine le_of_eq_of_le ?_ (norm_chartIteratedFDeriv_le f i (Nat.zero_le k) (interior_subset hyK))
  rw [ContMDiffMap.chartIteratedFDeriv_self_target_apply, norm_iteratedFDerivWithin_zero,
    Function.comp_apply, (extChartAt I (A.center i)).left_inv hy, coe_toContMDiffMap]

variable (A k α F) in
/-- Evaluation at a point, as a continuous linear map on `C^{k,α}(M, F)` of norm at most one. -/
def evalCLM (y : M) : A.CkHolderSpace k α F →L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun f := f y
      map_add' _ _ := rfl
      map_smul' _ _ := rfl } 1
    fun f ↦ (one_mul ‖f‖).symm ▸ norm_apply_le f y

@[simp]
theorem evalCLM_apply (y : M) (f : A.CkHolderSpace k α F) : evalCLM A k α F y f = f y :=
  (rfl)

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

/-- The inclusion of `C^{k,α}(M, F)` into `C^k(M, F)` with the finite-atlas norm is
`1`-Lipschitz. -/
theorem lipschitzWith_toContMDiffMap :
    letI := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := F) k A.interior_cover
    LipschitzWith 1 (toContMDiffMap A k α F) := by
  let _ := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := F) k A.interior_cover
  refine LipschitzWith.mk_one fun f g ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, ContMDiffMap.norm_finiteAtlas, ← map_sub]
  exact finiteAtlasSeminorm_le_norm (f - g)

/-- The inclusion of `C^{k,α}(M, F)` into `C^k(M, F)` with the finite-atlas norm is
continuous. -/
theorem continuous_toContMDiffMap :
    letI := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := F) k A.interior_cover
    Continuous (toContMDiffMap A k α F) := by
  let _ := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := F) k A.interior_cover
  exact lipschitzWith_toContMDiffMap.continuous

/-- A Cauchy sequence in `C^{k,α}(M, F)` has underlying `C^k` maps Cauchy for the finite-atlas
`C^k` norm. -/
theorem cauchySeq_toContMDiffMap {β : Type*} [Preorder β] {u : β → A.CkHolderSpace k α F}
    (hu : CauchySeq u) :
    letI := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := F) k A.interior_cover
    CauchySeq fun b ↦ toContMDiffMap A k α F (u b) := by
  let _ := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := F) k A.interior_cover
  exact lipschitzWith_toContMDiffMap.uniformContinuous.comp_cauchySeq hu

section Complete

variable [IsRCLikeNormedField 𝕜] [LocallyCompactSpace E] [I.Boundaryless] [CompleteSpace F]

/-- **The Banach space `C^{k,α}(M, F)`.** On a boundaryless manifold modelled on a locally
compact space over `ℝ` or `ℂ`, the Hölder space of a compact chart atlas with values in a Banach
space is complete. -/
instance instCompleteSpace : CompleteSpace (A.CkHolderSpace k α F) := by
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := F) k A.interior_cover
  have := ContMDiffMap.completeSpace_finiteAtlas (F := F) k A.interior_cover
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  let v (n : ℕ) : C^k⟮I, M; 𝓘(𝕜, F), F⟯ := toContMDiffMap A k α F (u n)
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (cauchySeq_toContMDiffMap hu)
  have hg0 : Tendsto (fun n ↦ ContMDiffMap.finiteAtlasSeminorm A.center A.piece k le_rfl
      (v n - g)) atTop (𝓝 0) := by
    refine (tendsto_iff_norm_sub_tendsto_zero.mp hg).congr fun n ↦ ?_
    exact ContMDiffMap.norm_finiteAtlas k A.interior_cover (v n - g)
  -- The `k`th coordinate derivatives converge pointwise on the pieces.
  have hpt (i : A.ι) (z) (hz : z ∈ (A.piece i : Set (extChartAt I (A.center i)).target)) :
      Tendsto (fun n ↦ ContMDiffMap.chartIteratedFDeriv (v n) (A.center i) k le_rfl z) atTop
        (𝓝 (ContMDiffMap.chartIteratedFDeriv g (A.center i) k le_rfl z)) :=
    ContMDiffMap.tendsto_chartIteratedFDeriv_of_tendsto_finiteAtlasSeminorm hg0 i le_rfl hz
  -- A uniform bound `C` on the tail of the sequence bounds the Hölder seminorms of the
  -- difference with the limit.
  have hH (n : ℕ) (C : ℝ≥0) (hC : ∀ m ≥ n, ‖u n - u m‖ ≤ C) (i : A.ι) :
      HolderWith C α ⇑((ContMDiffMap.chartIteratedFDeriv (v n - g) (A.center i) k
        le_rfl).restrict (A.piece i)) := by
    refine ContMDiffMap.holderWith_restrict_chartIteratedFDeriv_of_tendsto (l := atTop)
      (u := fun m ↦ v n - v m) (fun z hz ↦ ?_) (.of_forall fun m ↦ ?_) ?_
    · simp only [ContMDiffMap.chartIteratedFDeriv_sub, ContinuousMap.sub_apply]
      exact tendsto_const_nhds.sub (hpt i z hz)
    · rw [← map_sub]
      exact memChartHolder (u n - u m) i
    · filter_upwards [eventually_ge_atTop n] with m hm
      rw [← map_sub]
      exact_mod_cast (chartHolderNorm_le_norm (u n - u m) i).trans (hC m hm)
  have htail (C : ℝ≥0) (hC : 0 < C) : ∃ N, ∀ n ≥ N, ∀ m ≥ n, ‖u n - u m‖ ≤ C := by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu C hC
    refine ⟨N, fun n hn m hm ↦ ?_⟩
    have h := hN n hn m (hn.trans hm)
    rw [dist_eq_norm] at h
    exact h.le
  -- The limit lies in the Hölder space: `g = v N - (v N - g)`.
  have hmem (i : A.ι) : ContMDiffMap.MemChartHolder (A.center i) (A.piece i) k le_rfl α g := by
    obtain ⟨N, hN⟩ := htail 1 zero_lt_one
    rw [← sub_sub_cancel (v N) g]
    exact (memChartHolder (u N) i).sub (hH N 1 (hN N le_rfl) i).memHolder
  refine ⟨mk g hmem, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  -- Choose `C` with `card ι * C < ε / 2`.
  obtain ⟨C, hCpos, hC⟩ : ∃ C : ℝ≥0, 0 < C ∧ (Fintype.card A.ι : ℝ) * C < ε / 2 := by
    refine ⟨Real.toNNReal (ε / (2 * (Fintype.card A.ι + 1))),
      Real.toNNReal_pos.mpr (by positivity), ?_⟩
    rw [Real.coe_toNNReal _ (by positivity), ← mul_div_assoc,
      div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith
  obtain ⟨N₁, hN₁⟩ := htail C hCpos
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hg0 (ε / 2) (half_pos hε)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hsup : ContMDiffMap.finiteAtlasSeminorm A.center A.piece k le_rfl (v n - g) < ε / 2 := by
    have h := hN₂ n (le_of_max_le_right hn)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)] at h
  have hhol (i : A.ι) :
      (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α (v n - g) : ℝ) ≤ C :=
    NNReal.coe_le_coe.mpr (hH n C (hN₁ n (le_of_max_le_left hn)) i).nnholderNorm_le
  rw [dist_eq_norm, norm_def, map_sub, toContMDiffMap_mk]
  calc _ ≤ ε / 2 + ∑ _i : A.ι, (C : ℝ) := add_le_add hsup.le (Finset.sum_le_sum fun i _ ↦ hhol i)
    _ = ε / 2 + Fintype.card A.ι * C := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ < ε := by linarith

end Complete

end CkHolderSpace

end

end CompactChartAtlas

end TauCeti
