/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Level
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
public import TauCeti.Geometry.Manifold.VectorBundle.Core.MaximalAtlas
public import TauCeti.Geometry.Manifold.VectorBundle.Core.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.LinearMapTrivialization
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Transverse defining equations and cocycle models of intrinsic normal bundles

For a `C^n` smooth embedding `f : M → N` (`m + 1 ≤ n`) between manifolds over a complete
nontrivially normed field `𝕜` with finite-dimensional models `E`, `V`, and codimension model `P`
(`finrank 𝕜 P = finrank 𝕜 V - finrank 𝕜 E`), this file connects the quotient normal bundle
`x ↦ f.NormalSpace x hn` (`T_{f x} N / df(T_x M)`) with local defining equations and cocycles:

1. `normalSpaceTrivializationOfLevel`: `C^m`-compatible linear trivializations of `f.NormalSpace`
   from regular level maps, intertwining `dg₀` and `dg₁` on overlaps.
2. `exists_transverse_zero` and `isClosed_range_iff_forall_exists_transverse_zero`: smooth slice
   charts, local regular defining equations, and the defining-equation criterion for closedness.
3. `transverseNormalCore` and `transverseNormalCoreDiffeomorph`: canonical `C^m` bundle
   diffeomorphism between the transverse transition-cocycle model and `f.NormalSpace`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapters 5, 6, and 10.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public noncomputable section

open Set Function Filter Topology Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E V P H G M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n m : ℕ∞ω}

section LevelTrivialization

/-- For a positive-regularity smooth embedding `f`, injectivity of `mfderiv I J f x` turns the
codimension hypothesis `finrank P = finrank V - finrank E` into `finrank E + finrank P = finrank V`
whenever `M` is inhabited by a point `x`. -/
theorem finrank_add_eq_of_sub_eq [FiniteDimensional 𝕜 V] (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x : M) :
    Module.finrank 𝕜 E + Module.finrank 𝕜 P = Module.finrank 𝕜 V := by
  have hle : Module.finrank 𝕜 E ≤ Module.finrank 𝕜 V :=
    LinearMap.finrank_le_finrank_of_injective
      (f.isImmersion.mfderiv_injective hn x : Injective ((mfderiv I J (f : M → N) x).toLinearMap))
  omega

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 P]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 P] in
private def levelLinearMap (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {g : N → P} {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x)) (x : M) :
    f.NormalSpace x hn →L[𝕜] P := by
  classical
  exact if hx : x ∈ W then
      (f.normalSpaceEquivOfLevel x hn (eventually_of_mem (hW.mem_nhds hx) hgf)
        (hreg x hx) (f.finrank_add_eq_of_sub_eq hn hdim x)).toContinuousLinearMap
    else 0

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 P] in
private theorem levelLinearMap_normalClass (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {g : N → P} {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x))
    {x : M} (hx : x ∈ W) (v : TangentSpace J (f x)) :
    f.levelLinearMap hn hdim hW hgf hreg x (f.normalClass x hn v) =
      mfderiv J 𝓘(𝕜, P) g (f x) v := by
  simp only [levelLinearMap, hx, ↓reduceDIte]
  exact f.normalSpaceEquivOfLevel_normalClass x hn _ _ _ v

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 P] in
private theorem bijective_levelLinearMap (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {g : N → P} {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x)) :
    ∀ x ∈ W, Bijective (f.levelLinearMap hn hdim hW hgf hreg x) := fun x hx ↦ by
  simp only [levelLinearMap, hx, ↓reduceDIte]
  exact (f.normalSpaceEquivOfLevel x hn _ _ _).bijective

variable [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]

private theorem contMDiffOn_levelLinearMap (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {U : Set N} (hU : IsOpen U) (hfW : MapsTo f W U)
    {g : N → P} (hg : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g U) {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiffOn (I.prod 𝓘(𝕜, P)) 𝓘(𝕜, P) m
      (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
        f.levelLinearMap hn hdim hW hgf hreg p.proj p.2)
      (π P (fun x ↦ f.NormalSpace x hn) ⁻¹' W) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  intro p hp
  obtain ⟨O, hO, hpO, s, hs, hright⟩ :=
    f.exists_contMDiffOn_normalQuotientMap_rightInverse hn hm hdim p
  let fc : C^m⟮I, M; J, N⟯ := ⟨f, f.contMDiff.of_le ((le_add_right le_rfl).trans hm)⟩
  have hlift : ContMDiffAt (I.prod 𝓘(𝕜, P)) J.tangent m (fun q ↦ Pullback.lift fc (s q)) p :=
    (Pullback.contMDiff_lift fc fc.contMDiff).contMDiffAt.comp p (hs.contMDiffAt (hO.mem_nhds hpO))
  have hsproj : (s p).proj = p.proj := by
    have h := hright hpO; simp only [Function.comp_apply, normalQuotientMap_apply, id_eq] at h
    exact congrArg TotalSpace.proj h
  have hgAt : ContMDiffAt J 𝓘(𝕜, P) (m + 1) g (Pullback.lift fc (s p)).proj := by
    rw [Pullback.lift_proj]; dsimp only [fc]; rw [hsproj]
    exact hg.contMDiffAt (hU.mem_nhds (hfW hp))
  have hcomp : ContMDiffAt (I.prod 𝓘(𝕜, P)) 𝓘(𝕜, P) m
      (fun q ↦ (tangentMap J 𝓘(𝕜, P) g (Pullback.lift fc (s q))).2) p :=
    (contMDiff_snd_tangentBundle_modelSpace P 𝓘(𝕜, P)).contMDiffAt.comp p
      ((hgAt.contMDiffAt_tangentMap (m := m) le_rfl).comp p hlift)
  have hopen := hO.inter (hW.preimage (FiberBundle.continuous_proj P _))
  refine (hcomp.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hopen.mem_nhds ⟨hpO, hp⟩] with q ⟨hqO, hqW⟩
  have hsq : f.normalQuotientMap hn (s q) = q := hright hqO
  rw [normalQuotientMap_apply] at hsq
  have hqproj : (s q).proj = q.proj := congrArg TotalSpace.proj hsq
  exact (congrArg (fun r : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
      f.levelLinearMap hn hdim hW hgf hreg r.proj r.2) hsq.symm).trans
    (f.levelLinearMap_normalClass hn hdim hW hgf hreg (hqproj.symm ▸ hqW) (s q).2)

/-- **Level-set trivialization of the intrinsic normal bundle.** If `g : N → P` is `C^(m + 1)` on an
open `U ⊆ N` containing `f '' W`, constant along `f '' W`, and regular at `f x` for every `x ∈ W`,
then `mfderiv J 𝓘(𝕜, P) g (f x)` descends to a linear trivialization of `f.NormalSpace` over `W`
belonging to the `C^m` maximal atlas of `f.NormalSpace`. -/
def normalSpaceTrivializationOfLevel (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {U : Set N} (hU : IsOpen U) (hfW : MapsTo f W U)
    {g : N → P} (hg : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g U) {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    Trivialization P (π P (fun x ↦ f.NormalSpace x hn)) :=
  haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  letI := f.normalSpaceFiberBundle hn hdim; letI := f.normalSpaceVectorBundle hn hdim
  letI := f.normalSpaceContMDiffVectorBundle hn hm hdim
  Trivialization.ofContinuousLinearMapOn hW (f.levelLinearMap hn hdim hW hgf hreg)
    (f.contMDiffOn_levelLinearMap hn hm hdim hW hU hfW hg hgf hreg)
    (f.bijective_levelLinearMap hn hdim hW hgf hreg)

@[simp]
theorem baseSet_normalSpaceTrivializationOfLevel (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {U : Set N} (hU : IsOpen U) (hfW : MapsTo f W U)
    {g : N → P} (hg : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g U) {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    (f.normalSpaceTrivializationOfLevel hn hm hdim hW hU hfW hg hgf hreg).baseSet = W := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  rw [normalSpaceTrivializationOfLevel.eq_def]
  exact Trivialization.baseSet_ofContinuousLinearMapOn _ _ _ _

/-- `normalSpaceTrivializationOfLevel` is `𝕜`-linear on every fibre over `W`. -/
instance isLinear_normalSpaceTrivializationOfLevel (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {U : Set N} (hU : IsOpen U) (hfW : MapsTo f W U)
    {g : N → P} (hg : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g U) {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    (f.normalSpaceTrivializationOfLevel hn hm hdim hW hU hfW hg hgf hreg).IsLinear 𝕜 := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  rw [normalSpaceTrivializationOfLevel.eq_def]
  exact Trivialization.isLinear_ofContinuousLinearMapOn _ _ _ _

/-- `normalSpaceTrivializationOfLevel` belongs to the `C^m` maximal atlas of `f.NormalSpace`. -/
theorem normalSpaceTrivializationOfLevel_mem_maximalAtlas
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {U : Set N} (hU : IsOpen U) (hfW : MapsTo f W U)
    {g : N → P} (hg : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g U) {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    (f.normalSpaceTrivializationOfLevel hn hm hdim hW hU hfW hg hgf hreg).toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear M P I m).maximalAtlas
        (TotalSpace P (fun x ↦ f.NormalSpace x hn)) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  rw [normalSpaceTrivializationOfLevel.eq_def]
  exact Trivialization.ofContinuousLinearMapOn_mem_maximalAtlas _ _ _ _

/-- Over `W`, `normalSpaceTrivializationOfLevel` evaluates `normalSpaceEquivOfLevel` on the normal
fibre. -/
theorem normalSpaceTrivializationOfLevel_apply (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {U : Set N} (hU : IsOpen U) (hfW : MapsTo f W U)
    {g : N → P} (hg : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g U) {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x))
    {p : TotalSpace P (fun x ↦ f.NormalSpace x hn)} (hp : p.proj ∈ W) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    f.normalSpaceTrivializationOfLevel hn hm hdim hW hU hfW hg hgf hreg p =
      (p.proj, f.normalSpaceEquivOfLevel p.proj hn (eventually_of_mem (hW.mem_nhds hp) hgf)
        (hreg p.proj hp) (f.finrank_add_eq_of_sub_eq hn hdim p.proj) p.2) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  rw [normalSpaceTrivializationOfLevel.eq_def,
    Trivialization.ofContinuousLinearMapOn_apply _ _ _ _ hp]
  simp only [levelLinearMap, hp, ↓reduceDIte]; rfl

/-- Over `W`, `normalSpaceTrivializationOfLevel` sends the normal class of an ambient tangent vector
`v` to `(x, mfderiv J 𝓘(𝕜, P) g (f x) v)`. -/
@[simp]
theorem normalSpaceTrivializationOfLevel_normalClass (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {U : Set N} (hU : IsOpen U) (hfW : MapsTo f W U)
    {g : N → P} (hg : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g U) {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x))
    {x : M} (hx : x ∈ W) (v : TangentSpace J (f x)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    f.normalSpaceTrivializationOfLevel hn hm hdim hW hU hfW hg hgf hreg
        ⟨x, f.normalClass x hn v⟩ = (x, mfderiv J 𝓘(𝕜, P) g (f x) v) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  rw [f.normalSpaceTrivializationOfLevel_apply hn hm hdim hW hU hfW hg hgf hreg hx]
  exact Prod.ext rfl (f.normalSpaceEquivOfLevel_normalClass _ _ _ _ _ v)

/-- **Overlap transition law for level-set normal trivializations.** On `W₀ ∩ W₁`, the fibrewise
coordinate change between two level-set trivializations sends `mfderiv J 𝓘(𝕜, P) g₀ (f x) v` to
`mfderiv J 𝓘(𝕜, P) g₁ (f x) v`. -/
theorem coordChangeL_normalSpaceTrivializationOfLevel_mfderiv
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W₀ W₁ : Set M} (hW₀ : IsOpen W₀) (hW₁ : IsOpen W₁)
    {U₀ U₁ : Set N} (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (hfW₀ : MapsTo f W₀ U₀) (hfW₁ : MapsTo f W₁ U₁)
    {g₀ g₁ : N → P} (hg₀ : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g₀ U₀)
    (hg₁ : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g₁ U₁) {c₀ c₁ : P}
    (hgf₀ : ∀ x ∈ W₀, g₀ (f x) = c₀) (hgf₁ : ∀ x ∈ W₁, g₁ (f x) = c₁)
    (hreg₀ : ∀ x ∈ W₀, IsRegularPoint J 𝓘(𝕜, P) g₀ (f x))
    (hreg₁ : ∀ x ∈ W₁, IsRegularPoint J 𝓘(𝕜, P) g₁ (f x))
    {x : M} (hx : x ∈ W₀ ∩ W₁) (v : TangentSpace J (f x)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    (f.normalSpaceTrivializationOfLevel hn hm hdim hW₀ hU₀ hfW₀ hg₀ hgf₀ hreg₀).coordChangeL 𝕜
      (f.normalSpaceTrivializationOfLevel hn hm hdim hW₁ hU₁ hfW₁ hg₁ hgf₁ hreg₁) x
      (mfderiv J 𝓘(𝕜, P) g₀ (f x) v) = mfderiv J 𝓘(𝕜, P) g₁ (f x) v := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  rw [← f.levelLinearMap_normalClass hn hdim hW₀ hgf₀ hreg₀ hx.1 v,
    ← f.levelLinearMap_normalClass hn hdim hW₁ hgf₁ hreg₁ hx.2 v]
  simp only [normalSpaceTrivializationOfLevel.eq_def]
  exact Trivialization.coordChangeL_ofContinuousLinearMapOn_apply _ _ _ _ _ _ _ _ hx _

/-- **Scalar transition law in codimension one (`P = 𝕜`).** On the overlap `W₀ ∩ W₁` of two scalar
defining equations `g₀, g₁ : N → 𝕜`, `dg₁ (f x)` equals `dg₀ (f x)` scaled by `(e₀.coordChangeL 𝕜
e₁ x) 1`. -/
theorem mfderiv_eq_coordChangeL_normalSpaceTrivializationOfLevel_one_smul
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 𝕜 = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W₀ W₁ : Set M} (hW₀ : IsOpen W₀) (hW₁ : IsOpen W₁)
    {U₀ U₁ : Set N} (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (hfW₀ : MapsTo f W₀ U₀) (hfW₁ : MapsTo f W₁ U₁)
    {g₀ g₁ : N → 𝕜} (hg₀ : ContMDiffOn J 𝓘(𝕜, 𝕜) (m + 1) g₀ U₀)
    (hg₁ : ContMDiffOn J 𝓘(𝕜, 𝕜) (m + 1) g₁ U₁) {c₀ c₁ : 𝕜}
    (hgf₀ : ∀ x ∈ W₀, g₀ (f x) = c₀) (hgf₁ : ∀ x ∈ W₁, g₁ (f x) = c₁)
    (hreg₀ : ∀ x ∈ W₀, IsRegularPoint J 𝓘(𝕜, 𝕜) g₀ (f x))
    (hreg₁ : ∀ x ∈ W₁, IsRegularPoint J 𝓘(𝕜, 𝕜) g₁ (f x))
    {x : M} (hx : x ∈ W₀ ∩ W₁) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    mfderiv J 𝓘(𝕜, 𝕜) g₁ (f x) =
      ((f.normalSpaceTrivializationOfLevel hn hm hdim hW₀ hU₀ hfW₀ hg₀ hgf₀ hreg₀).coordChangeL 𝕜
        (f.normalSpaceTrivializationOfLevel hn hm hdim hW₁ hU₁ hfW₁ hg₁ hgf₁ hreg₁) x 1) •
        mfderiv J 𝓘(𝕜, 𝕜) g₀ (f x) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  set τ := (f.normalSpaceTrivializationOfLevel hn hm hdim hW₀ hU₀ hfW₀ hg₀ hgf₀ hreg₀).coordChangeL
    𝕜 (f.normalSpaceTrivializationOfLevel hn hm hdim hW₁ hU₁ hfW₁ hg₁ hgf₁ hreg₁) x
  refine ContinuousLinearMap.ext fun v ↦ ?_
  let y₀ : 𝕜 := mfderiv J 𝓘(𝕜, 𝕜) g₀ (f x) v
  let y₁ : 𝕜 := mfderiv J 𝓘(𝕜, 𝕜) g₁ (f x) v
  have hv : τ y₀ = y₁ := f.coordChangeL_normalSpaceTrivializationOfLevel_mfderiv hn hm hdim
    hW₀ hW₁ hU₀ hU₁ hfW₀ hfW₁ hg₀ hg₁ hgf₀ hgf₁ hreg₀ hreg₁ hx v
  calc y₁ = τ (y₀ • 1) := by rw [smul_eq_mul, mul_one, hv]
    _ = (τ 1) • y₀ := by rw [map_smul]; simp [smul_eq_mul, mul_comm]

end LevelTrivialization

/-! ### Smooth slice charts, transverse defining equations, and closed submanifolds -/

section SliceAndTransverse

private theorem immersionSliceChart_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
    {f : M → N} {x₀ : M} (h : Manifold.IsImmersionAtOfComplement F I J n f x₀) (p : N) :
    h.codChart.transHomeomorph (J.toHomeomorph.trans h.equiv.toHomeomorph.symm) p =
      h.equiv.symm ((h.codChart.extend J) p) := by
  simp [OpenPartialHomeomorph.transHomeomorph_apply]

/-- **Smooth slice chart at an embedded point.** Upgrading
`TauCeti.exists_isSliceChart_of_isEmbedding_of_isImmersionAtOfComplement`, if `f : M → N` is a
topological embedding into a boundaryless `C^n` manifold `N` with `C^n` immersion normal form at
`x₀` and complement `F`, then around `f x₀` there is an ambient `OpenPartialHomeomorph N (E × F)`
whose forward and inverse maps are `C^n` and which flattens `Set.range f` onto `range I ×ˢ {0}`. -/
theorem _root_.TauCeti.exists_contMDiffOn_isSliceChart_of_isEmbedding_of_isImmersionAtOfComplement
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
    {f : M → N} (hf : IsEmbedding f) {x₀ : M}
    (h : Manifold.IsImmersionAtOfComplement F I J n f x₀) :
    ∃ Φ : OpenPartialHomeomorph N (E × F), f x₀ ∈ Φ.source ∧
      IsSliceChart Φ (range I ×ˢ ({0} : Set F)) (range f) ∧
      ContMDiffOn J 𝓘(𝕜, E × F) n Φ Φ.source ∧
      ContMDiffOn 𝓘(𝕜, E × F) J n Φ.symm Φ.target := by
  set Ψ : OpenPartialHomeomorph N (E × F) :=
    h.codChart.transHomeomorph (J.toHomeomorph.trans h.equiv.toHomeomorph.symm)
  have key {y} (hy : y ∈ h.domChart.source) : Ψ (f y) = ((h.domChart.extend I) y, 0) := by
    have hy' : y ∈ (h.domChart.extend I).source := by rwa [h.domChart.extend_source]
    have hw := h.writtenInCharts ((h.domChart.extend I).map_source hy')
    simp only [Function.comp_apply, (h.domChart.extend I).left_inv hy'] at hw
    rw [immersionSliceChart_apply h, hw, ContinuousLinearEquiv.symm_apply_apply]
  obtain ⟨W, hW, hWf⟩ := hf.isInducing.isOpen_iff.1 h.domChart.open_source
  have hmemW (y : M) : f y ∈ W ↔ y ∈ h.domChart.source := by rw [← hWf]; rfl
  set O : Set N := (Ψ.source ∩ Ψ ⁻¹' ((I.symm ⁻¹' h.domChart.target) ×ˢ (univ : Set F))) ∩ W
  have hOopen : IsOpen O :=
    (Ψ.isOpen_inter_preimage ((h.domChart.open_target.preimage I.continuous_symm).prod
      isOpen_univ)).inter hW
  have hx₀ : x₀ ∈ h.domChart.source := h.mem_domChart_source
  have hfx₀O : f x₀ ∈ O := ⟨⟨h.mem_codChart_source, by
    rw [mem_preimage, key hx₀, mem_prod, mem_preimage, OpenPartialHomeomorph.extend_coe,
      Function.comp_apply, I.left_inv]
    exact ⟨h.domChart.map_source hx₀, mem_univ _⟩⟩, (hmemW x₀).2 hx₀⟩
  let Φ := Ψ.restrOpen O hOopen
  have hΨ : ContMDiffOn J 𝓘(𝕜, E × F) n Ψ Ψ.source :=
    (h.equiv.symm.contDiff.contMDiff.comp_contMDiffOn
      (h.codChart.contMDiffOn_extend h.codChart_mem_maximalAtlas)).congr fun p _ ↦
        immersionSliceChart_apply h p
  have hi := contMDiffOn_extend_symm h.codChart_mem_maximalAtlas
  rw [← h.codChart.extend_target'] at hi
  have hΨsymm : ContMDiffOn 𝓘(𝕜, E × F) J n Ψ.symm Ψ.target :=
    (hi.comp h.equiv.contDiff.contMDiff.contMDiffOn fun q hq ↦ by
      rw [h.codChart.extend_target]
      exact ⟨hq, J.range_eq_univ ▸ mem_univ _⟩).congr fun q _ ↦ by
        simp [Ψ, OpenPartialHomeomorph.transHomeomorph_symm_apply]
  refine ⟨Φ, ⟨h.mem_codChart_source, hfx₀O⟩, isSliceChart_iff.2 fun p hp ↦ ?_,
    hΨ.mono fun _ hp ↦ hp.1,
    (hΨsymm.mono fun q hq ↦ Φ.right_inv hq ▸ Ψ.map_source (Φ.map_target hq).1).congr fun _ _ ↦ rfl⟩
  rw [OpenPartialHomeomorph.restrOpen_source] at hp
  simp only [Φ, OpenPartialHomeomorph.coe_restrOpen]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun hps ↦ ?_⟩
  · subst hy
    rw [key ((hmemW y).1 hp.2.2), OpenPartialHomeomorph.extend_coe, Function.comp_apply]
    exact ⟨mem_range_self _, rfl⟩
  · have hmem : (Ψ p).1 ∈ (h.domChart.extend I).target := by
      rw [h.domChart.extend_target]; exact ⟨hp.2.1.2.1, hps.1⟩
    have hys : (h.domChart.extend I).symm (Ψ p).1 ∈ h.domChart.source := by
      rw [← h.domChart.extend_source (I := I)]; exact (h.domChart.extend I).map_target hmem
    refine ⟨_, Ψ.injOn (h.source_subset_preimage_source hys) hp.1 ?_⟩
    rw [key hys, (h.domChart.extend I).right_inv hmem, ← (hps.2 : (Ψ p).2 = 0)]

section TransverseEquations

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 P]
  [I.Boundaryless] [J.Boundaryless] [IsManifold J n N]

private structure TransverseZeroData (f : SmoothEmbedding I J n M N) (x₀ : M) where
  ambSet : Set N
  isOpen_ambSet : IsOpen ambSet
  mem_ambSet : f x₀ ∈ ambSet
  eqFun : N → P
  contMDiffOn_eqFun : ContMDiffOn J 𝓘(𝕜, P) n eqFun ambSet
  mem_range_iff : ∀ y ∈ ambSet, y ∈ range f ↔ eqFun y = 0
  regular : ∀ y ∈ ambSet, IsRegularPoint J 𝓘(𝕜, P) eqFun y

private theorem nonempty_transverseZeroData (f : SmoothEmbedding I J n M N) (hn1 : 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    Nonempty (TransverseZeroData (P := P) f x₀) := by
  have hn0 : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp hn1
  have : IsManifold J 1 N := .of_le hn1
  let F := f.isImmersion.complement
  let h : Manifold.IsImmersionAtOfComplement F I J n f x₀ :=
    f.isImmersion.isImmersionOfComplement_complement x₀
  obtain ⟨Φ, hfx₀, hslice, hΦ, hΦsymm⟩ :=
    exists_contMDiffOn_isSliceChart_of_isEmbedding_of_isImmersionAtOfComplement f.isEmbedding h
  have : FiniteDimensional 𝕜 (E × F) := h.equiv.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional 𝕜 F :=
    Module.Finite.of_surjective (LinearMap.snd 𝕜 E F) Prod.snd_surjective
  have hFdim : Module.finrank 𝕜 F = Module.finrank 𝕜 P := by
    have heq := h.equiv.toLinearEquiv.finrank_eq
    have hadd := f.finrank_add_eq_of_sub_eq hn0 hdim x₀
    rw [Module.finrank_prod] at heq; omega
  let c : F ≃L[𝕜] P := ContinuousLinearEquiv.ofFinrankEq hFdim
  let π₂ : E × F →L[𝕜] P := c.toContinuousLinearMap.comp (ContinuousLinearMap.snd 𝕜 E F)
  refine ⟨⟨Φ.source, Φ.open_source, hfx₀, π₂ ∘ Φ, π₂.contDiff.contMDiff.comp_contMDiffOn hΦ,
    fun y hy ↦ ?_, fun y hy ↦ ?_⟩⟩
  · rw [(isSliceChart_iff.1 hslice) y hy, I.range_eq_univ, mem_prod, and_iff_right (mem_univ _),
      mem_singleton_iff]
    exact (c.map_eq_zero_iff (x := (Φ y).2)).symm
  · have hloc := (PartialDiffeomorph.mk Φ.toPartialEquiv Φ.open_source Φ.open_target hΦ
      hΦsymm).isLocalDiffeomorphAt J 𝓘(𝕜, E × F) n hy
    have hΦAt := (hΦ.contMDiffAt (Φ.open_source.mem_nhds hy)).mdifferentiableAt hn0
    rw [isRegularPoint_iff, (π₂.hasMFDerivAt.comp y hΦAt.hasMFDerivAt).mfderiv,
      ContinuousLinearMap.coe_comp]
    exact (c.surjective.comp Prod.snd_surjective).comp
      (hloc.mfderivToContinuousLinearEquiv hn0).surjective

/-- **Local transverse defining equations of a smooth embedding.** Around every `x₀ : M`, there is
an open ambient set `S ⊆ N` containing `f x₀` and a `C^n` map `g : N → P` cutting out `Set.range f`
on `S` (`y ∈ Set.range f ↔ g y = 0`) and regular at every `y ∈ S`. -/
theorem exists_transverse_zero (f : SmoothEmbedding I J n M N) (hn1 : 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    ∃ S : Set N, IsOpen S ∧ f x₀ ∈ S ∧ ∃ g : N → P, ContMDiffOn J 𝓘(𝕜, P) n g S ∧
      (∀ y ∈ S, y ∈ range f ↔ g y = 0) ∧ ∀ y ∈ S, IsRegularPoint J 𝓘(𝕜, P) g y :=
  let ⟨d⟩ := f.nonempty_transverseZeroData hn1 hdim x₀
  ⟨d.ambSet, d.isOpen_ambSet, d.mem_ambSet, d.eqFun, d.contMDiffOn_eqFun, d.mem_range_iff,
    d.regular⟩

/-- **Characterization of closed embedded submanifolds by local defining equations.** When the
codimension model `P` is nontrivial, the image of a `C^n` (`1 ≤ n`) smooth embedding `f : M → N`
between boundaryless manifolds is closed in `N` if and only if every ambient point `y₀ : N` admits
an open neighbourhood `S` on which `Set.range f` is cut out by a `C^n` map `g : N → P` that is
regular along `S ∩ Set.range f`. -/
theorem isClosed_range_iff_forall_exists_transverse_zero [Nontrivial P]
    (f : SmoothEmbedding I J n M N) (hn1 : 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    IsClosed (range f) ↔
      ∀ y₀ : N, ∃ S : Set N, IsOpen S ∧ y₀ ∈ S ∧ ∃ g : N → P, ContMDiffOn J 𝓘(𝕜, P) n g S ∧
        (∀ y ∈ S, y ∈ range f ↔ g y = 0) ∧ ∀ y ∈ S ∩ range f, IsRegularPoint J 𝓘(𝕜, P) g y := by
  refine ⟨fun hclosed y₀ ↦ ?_, fun h ↦ ?_⟩
  · by_cases hy₀ : y₀ ∈ range f
    · obtain ⟨x₀, rfl⟩ := hy₀
      obtain ⟨S, hS, hx₀, g, hg, hzero, hreg⟩ := f.exists_transverse_zero hn1 hdim x₀
      exact ⟨S, hS, hx₀, g, hg, hzero, fun y hy ↦ hreg y hy.1⟩
    · obtain ⟨c, hc⟩ := exists_ne (0 : P)
      exact ⟨(range f)ᶜ, hclosed.isOpen_compl, hy₀, fun _ ↦ c, contMDiffOn_const,
        fun y hy ↦ ⟨fun hyr ↦ (hy hyr).elim, fun hcz ↦ (hc hcz).elim⟩, fun y hy ↦ (hy.1 hy.2).elim⟩
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y₀ hy₀
    obtain ⟨S, hS, hy₀S, g, hg, hzero, -⟩ := h y₀
    refine mem_of_superset ((hg.continuousOn.isOpen_inter_preimage hS
      isClosed_singleton.isOpen_compl).mem_nhds
      ⟨hy₀S, fun hgy₀ ↦ hy₀ ((hzero y₀ hy₀S).2 hgy₀)⟩) fun y hy hyr ↦ hy.2 ((hzero y hy.1).1 hyr)

/-! ### Transition-cocycle model from transverse defining equations -/

variable [IsManifold I (m + 1) M]

omit [IsManifold I (m + 1) M] in
private def chosenTransverseZeroData (f : SmoothEmbedding I J n M N) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    TransverseZeroData (P := P) f x₀ :=
  Classical.choice (f.nonempty_transverseZeroData ((le_add_left le_rfl).trans hm) hdim x₀)

omit [IsManifold I (m + 1) M] in
/-- The open ambient neighbourhood around `f x₀` on which `f.transverseDefiningMap` cuts out
`Set.range f`. -/
def transverseAmbSet (f : SmoothEmbedding I J n M N) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) : Set N :=
  (f.chosenTransverseZeroData hm hdim x₀).ambSet

omit [IsManifold I (m + 1) M] in
/-- The chosen local `C^n` transverse defining map `N → P` cutting out `Set.range f` on
`f.transverseAmbSet hm hdim x₀`. -/
def transverseDefiningMap (f : SmoothEmbedding I J n M N) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) : N → P :=
  (f.chosenTransverseZeroData hm hdim x₀).eqFun

omit [IsManifold I (m + 1) M] in
/-- The chosen ambient slice neighbourhood `f.transverseAmbSet hm hdim x₀` is open in `N`. -/
theorem isOpen_transverseAmbSet (f : SmoothEmbedding I J n M N) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    IsOpen (f.transverseAmbSet hm hdim x₀) :=
  (f.chosenTransverseZeroData hm hdim x₀).isOpen_ambSet

omit [IsManifold I (m + 1) M] in
/-- The point `f x₀` lies in `f.transverseAmbSet hm hdim x₀`. -/
theorem apply_mem_transverseAmbSet (f : SmoothEmbedding I J n M N) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    f x₀ ∈ f.transverseAmbSet hm hdim x₀ :=
  (f.chosenTransverseZeroData hm hdim x₀).mem_ambSet

omit [IsManifold I (m + 1) M] in
/-- `f.transverseDefiningMap hm hdim x₀` is `C^n` on `f.transverseAmbSet hm hdim x₀`. -/
theorem contMDiffOn_transverseDefiningMap (f : SmoothEmbedding I J n M N) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    ContMDiffOn J 𝓘(𝕜, P) n (f.transverseDefiningMap hm hdim x₀)
      (f.transverseAmbSet hm hdim x₀) :=
  (f.chosenTransverseZeroData hm hdim x₀).contMDiffOn_eqFun

omit [IsManifold I (m + 1) M] in
/-- On `f.transverseAmbSet hm hdim x₀`, `Set.range f` coincides with the zero locus of
`f.transverseDefiningMap hm hdim x₀`. -/
theorem mem_range_iff_transverseDefiningMap_eq_zero (f : SmoothEmbedding I J n M N)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) {y : N} (hy : y ∈ f.transverseAmbSet hm hdim x₀) :
    y ∈ range f ↔ f.transverseDefiningMap hm hdim x₀ y = 0 :=
  (f.chosenTransverseZeroData hm hdim x₀).mem_range_iff y hy

omit [IsManifold I (m + 1) M] in
/-- Every point of `f.transverseAmbSet hm hdim x₀` is a regular point of
`f.transverseDefiningMap hm hdim x₀`. -/
theorem isRegularPoint_transverseDefiningMap (f : SmoothEmbedding I J n M N)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) {y : N} (hy : y ∈ f.transverseAmbSet hm hdim x₀) :
    IsRegularPoint J 𝓘(𝕜, P) (f.transverseDefiningMap hm hdim x₀) y :=
  (f.chosenTransverseZeroData hm hdim x₀).regular y hy

/-- The `C^m`-compatible linear trivialization of `f.NormalSpace` around `x₀` induced by the chosen
transverse defining equation `f.transverseDefiningMap hm hdim x₀`. -/
def transverseNormalTrivialization (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
    Trivialization P (π P (fun x ↦ f.NormalSpace x hn)) :=
  haveI : IsManifold J (m + 1) N := .of_le hm
  f.normalSpaceTrivializationOfLevel hn hm hdim
    ((f.isOpen_transverseAmbSet hm hdim x₀).preimage (map_continuous f))
    (f.isOpen_transverseAmbSet hm hdim x₀) (fun _ hx ↦ hx)
    ((f.contMDiffOn_transverseDefiningMap hm hdim x₀).of_le hm)
    (fun x hx ↦ (f.mem_range_iff_transverseDefiningMap_eq_zero hm hdim x₀ hx).1 (mem_range_self x))
    (fun _ hx ↦ f.isRegularPoint_transverseDefiningMap hm hdim x₀ hx)

@[simp]
theorem baseSet_transverseNormalTrivialization (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
    (f.transverseNormalTrivialization hn hm hdim x₀).baseSet =
      f ⁻¹' f.transverseAmbSet hm hdim x₀ := by
  have : IsManifold J (m + 1) N := .of_le hm
  rw [transverseNormalTrivialization.eq_def]
  exact f.baseSet_normalSpaceTrivializationOfLevel hn hm hdim _ _ _ _ _ _

/-- The base point `x₀` belongs to the base set of `f.transverseNormalTrivialization` at `x₀`. -/
theorem mem_baseSet_transverseNormalTrivialization (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
    x₀ ∈ (f.transverseNormalTrivialization hn hm hdim x₀).baseSet := by
  rw [f.baseSet_transverseNormalTrivialization hn hm hdim x₀]
  exact f.apply_mem_transverseAmbSet hm hdim x₀

/-- `f.transverseNormalTrivialization` is `𝕜`-linear on every fibre over its base set. -/
instance isLinear_transverseNormalTrivialization (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
    (f.transverseNormalTrivialization hn hm hdim x₀).IsLinear 𝕜 := by
  have : IsManifold J (m + 1) N := .of_le hm
  rw [transverseNormalTrivialization.eq_def]
  exact f.isLinear_normalSpaceTrivializationOfLevel hn hm hdim _ _ _ _ _ _

/-- `f.transverseNormalTrivialization` lies in the `C^m` maximal atlas of `f.NormalSpace`. -/
theorem transverseNormalTrivialization_mem_maximalAtlas (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
    letI := f.normalSpaceFiberBundle hn hdim
    (f.transverseNormalTrivialization hn hm hdim x₀).toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear M P I m).maximalAtlas
        (TotalSpace P (fun x ↦ f.NormalSpace x hn)) := by
  have : IsManifold J (m + 1) N := .of_le hm
  rw [transverseNormalTrivialization.eq_def]
  exact f.normalSpaceTrivializationOfLevel_mem_maximalAtlas hn hm hdim _ _ _ _ _ _

@[simp]
theorem transverseNormalTrivialization_normalClass (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) {x : M} (hx : f x ∈ f.transverseAmbSet hm hdim x₀) (v : TangentSpace J (f x)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
    f.transverseNormalTrivialization hn hm hdim x₀ ⟨x, f.normalClass x hn v⟩ =
      (x, mfderiv J 𝓘(𝕜, P) (f.transverseDefiningMap hm hdim x₀) (f x) v) := by
  have : IsManifold J (m + 1) N := .of_le hm
  rw [transverseNormalTrivialization.eq_def]
  exact f.normalSpaceTrivializationOfLevel_normalClass hn hm hdim _ _ _ _ _ _ hx v

/-- **Transition-cocycle `VectorBundleCore` of the normal bundle from transverse charts.** At each
point `x₀ : M`, the open set is `f ⁻¹' (f.transverseAmbSet hm hdim x₀)` and the transition cocycle
is the coordinate change between `f.transverseNormalTrivialization` charts. -/
def transverseNormalCore (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    VectorBundleCore 𝕜 M P M :=
  haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  haveI : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
  letI := f.normalSpaceFiberBundle hn hdim
  VectorBundleCore.ofMaximalAtlas (f.transverseNormalTrivialization hn hm hdim)
    (f.transverseNormalTrivialization_mem_maximalAtlas hn hm hdim) _root_.id
    (f.mem_baseSet_transverseNormalTrivialization hn hm hdim)

@[simp]
theorem transverseNormalCore_localTriv_baseSet (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) :
    ((f.transverseNormalCore hn hm hdim).localTriv x₀).baseSet =
      f ⁻¹' f.transverseAmbSet hm hdim x₀ := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
  let := f.normalSpaceFiberBundle hn hdim
  rw [transverseNormalCore.eq_def, VectorBundleCore.ofMaximalAtlas_localTriv_baseSet,
    f.baseSet_transverseNormalTrivialization]

/-- The coordinate change of `f.transverseNormalCore` from `x₀` to `x₁` at `x` is the
`coordChangeL` between the corresponding transverse defining-equation trivializations. -/
theorem transverseNormalCore_coordChange (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ x₁ x : M) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
    (f.transverseNormalCore hn hm hdim).coordChange x₀ x₁ x =
      ((f.transverseNormalTrivialization hn hm hdim x₀).coordChangeL 𝕜
        (f.transverseNormalTrivialization hn hm hdim x₁) x : P →L[𝕜] P) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
  let := f.normalSpaceFiberBundle hn hdim
  rw [transverseNormalCore.eq_def, VectorBundleCore.ofMaximalAtlas_coordChange]

/-- The transition cocycle `f.transverseNormalCore` is `C^m`. -/
instance isContMDiff_transverseNormalCore (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    (f.transverseNormalCore hn hm hdim).IsContMDiff I m := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
  let := f.normalSpaceFiberBundle hn hdim
  rw [transverseNormalCore.eq_def]
  exact VectorBundleCore.isContMDiff_ofMaximalAtlas _ _ _ _

/-- Fibrewise continuous linear equivalence between the reconstructed fibre of
`f.transverseNormalCore` at `x` and the quotient normal space `f.NormalSpace x hn`. -/
def transverseNormalCoreFiberEquiv (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x : M) :
    (f.transverseNormalCore hn hm hdim).Fiber x ≃L[𝕜] f.NormalSpace x hn :=
  haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  haveI : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
  letI := f.normalSpaceFiberBundle hn hdim
  VectorBundleCore.ofMaximalAtlasFiberEquiv (f.transverseNormalTrivialization hn hm hdim)
    (f.transverseNormalTrivialization_mem_maximalAtlas hn hm hdim) _root_.id
    (f.mem_baseSet_transverseNormalTrivialization hn hm hdim) x

/-- **Equivalence of the transition-cocycle model and the quotient normal bundle.** Reconstructing a
vector bundle from the transverse defining-equation cocycle `f.transverseNormalCore` produces a
bundle canonically `C^m`-diffeomorphic to `TotalSpace P (fun x ↦ f.NormalSpace x hn)` via
`f.transverseNormalCoreFiberEquiv` on every fibre. -/
def transverseNormalCoreDiffeomorph (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
    letI := f.normalSpaceFiberBundle hn hdim
    (f.transverseNormalCore hn hm hdim).TotalSpace ≃ₘ^m⟮I.prod 𝓘(𝕜, P), I.prod 𝓘(𝕜, P)⟯
      TotalSpace P (fun x ↦ f.NormalSpace x hn) :=
  haveI : IsManifold J (m + 1) N := .of_le hm
  haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  haveI : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
  letI := f.normalSpaceFiberBundle hn hdim; letI := f.normalSpaceVectorBundle hn hdim
  letI := f.normalSpaceContMDiffVectorBundle hn hm hdim
  VectorBundleCore.ofMaximalAtlasDiffeomorph (f.transverseNormalTrivialization hn hm hdim)
    (f.transverseNormalTrivialization_mem_maximalAtlas hn hm hdim) _root_.id
    (f.mem_baseSet_transverseNormalTrivialization hn hm hdim)

@[simp]
theorem transverseNormalCoreDiffeomorph_apply (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (p : (f.transverseNormalCore hn hm hdim).TotalSpace) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
    letI := f.normalSpaceFiberBundle hn hdim
    f.transverseNormalCoreDiffeomorph hn hm hdim p =
      ⟨p.proj, f.transverseNormalCoreFiberEquiv hn hm hdim p.proj p.2⟩ := by
  have : IsManifold J (m + 1) N := .of_le hm
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  rw [transverseNormalCoreDiffeomorph.eq_def, transverseNormalCoreFiberEquiv.eq_def]
  exact VectorBundleCore.ofMaximalAtlasDiffeomorph_apply _ _ _ _ p

@[simp]
theorem transverseNormalCoreDiffeomorph_symm_apply (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (q : TotalSpace P (fun x ↦ f.NormalSpace x hn)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
    letI := f.normalSpaceFiberBundle hn hdim
    (f.transverseNormalCoreDiffeomorph hn hm hdim).symm q =
      ⟨q.proj, (f.transverseNormalCoreFiberEquiv hn hm hdim q.proj).symm q.2⟩ := by
  have : IsManifold J (m + 1) N := .of_le hm
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  rw [transverseNormalCoreDiffeomorph.eq_def, transverseNormalCoreFiberEquiv.eq_def]
  exact VectorBundleCore.ofMaximalAtlasDiffeomorph_symm_apply _ _ _ _ q

/-- `transverseNormalCoreDiffeomorph` intertwines every core chart `localTriv x₀` with the
corresponding transverse defining-equation trivialization `f.transverseNormalTrivialization`. -/
theorem apply_transverseNormalCoreDiffeomorph (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) (p : (f.transverseNormalCore hn hm hdim).TotalSpace)
    (hp : f p.proj ∈ f.transverseAmbSet hm hdim x₀) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
    letI := f.normalSpaceFiberBundle hn hdim
    f.transverseNormalTrivialization hn hm hdim x₀
        (f.transverseNormalCoreDiffeomorph hn hm hdim p) =
      (f.transverseNormalCore hn hm hdim).localTriv x₀ p := by
  have : IsManifold J (m + 1) N := .of_le hm
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le ((le_add_left le_rfl).trans hm)
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  rw [transverseNormalCoreDiffeomorph.eq_def]
  exact VectorBundleCore.apply_ofMaximalAtlasDiffeomorph _ _ _ _ x₀ p
    ((f.baseSet_transverseNormalTrivialization hn hm hdim x₀).symm ▸ hp)

/-! ### Codimension-one scalar transition cocycle -/

omit [FiniteDimensional 𝕜 P] in
/-- **Regularity of the scalar transition cocycle in codimension one.** For `P = 𝕜`, the scalar
transition function `x ↦ (f.transverseNormalCore hn hm hdim).coordChange x₀ x₁ x 1` is `C^m` on
each overlap `f ⁻¹' transverseAmbSet x₀ ∩ f ⁻¹' transverseAmbSet x₁`. -/
theorem contMDiffOn_transverseNormalCore_coordChange_one (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 𝕜 = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ x₁ : M) :
    ContMDiffOn I 𝓘(𝕜) m
      (fun x ↦ (f.transverseNormalCore hn hm hdim).coordChange x₀ x₁ x 1)
      (f ⁻¹' f.transverseAmbSet hm hdim x₀ ∩ f ⁻¹' f.transverseAmbSet hm hdim x₁) := by
  simpa only [VectorBundleCore.baseSet_at, f.transverseNormalCore_localTriv_baseSet] using
    ((f.transverseNormalCore hn hm hdim).isContMDiff_iff_contMDiffOn_coordChange_one
      (IB := I) (n := m)).1 inferInstance x₀ x₁

omit [FiniteDimensional 𝕜 P] in
/-- On every overlap, the scalar transition function of `f.transverseNormalCore` is nonzero. -/
theorem transverseNormalCore_coordChange_one_ne_zero (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 𝕜 = Module.finrank 𝕜 V - Module.finrank 𝕜 E) {x₀ x₁ x : M}
    (hx : x ∈ f ⁻¹' f.transverseAmbSet hm hdim x₀ ∩ f ⁻¹' f.transverseAmbSet hm hdim x₁) :
    (f.transverseNormalCore hn hm hdim).coordChange x₀ x₁ x 1 ≠ 0 := by
  set Z := f.transverseNormalCore hn hm hdim
  have hx0 : x ∈ Z.baseSet x₀ := by
    rw [Z.baseSet_at, f.transverseNormalCore_localTriv_baseSet]; exact hx.1
  have hx1 : x ∈ Z.baseSet x₁ := by
    rw [Z.baseSet_at, f.transverseNormalCore_localTriv_baseSet]; exact hx.2
  intro h0
  have h1 : Z.coordChange x₁ x₀ x (Z.coordChange x₀ x₁ x 1) = 1 := by
    rw [Z.coordChange_comp x₀ x₁ x₀ x ⟨⟨hx0, hx1⟩, hx0⟩ 1, Z.coordChange_self x₀ x hx0 1]
  rw [h0, map_zero] at h1; exact zero_ne_one h1

omit [FiniteDimensional 𝕜 P] in
/-- **Scalar cocycle relation for transverse defining differentials.** On the overlap of two
transverse defining equations in codimension one (`P = 𝕜`), `dg_{x₁}(f x)` equals `dg_{x₀}(f x)`
multiplied by `(f.transverseNormalCore hn hm hdim).coordChange x₀ x₁ x 1`. -/
theorem mfderiv_transverseDefiningMap_eq_coordChange_one_smul (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 𝕜 = Module.finrank 𝕜 V - Module.finrank 𝕜 E) {x₀ x₁ x : M}
    (hx : x ∈ f ⁻¹' f.transverseAmbSet hm hdim x₀ ∩ f ⁻¹' f.transverseAmbSet hm hdim x₁) :
    mfderiv J 𝓘(𝕜, 𝕜) (f.transverseDefiningMap hm hdim x₁) (f x) =
      ((f.transverseNormalCore hn hm hdim).coordChange x₀ x₁ x 1) •
        mfderiv J 𝓘(𝕜, 𝕜) (f.transverseDefiningMap hm hdim x₀) (f x) := by
  have : IsManifold J (m + 1) N := .of_le hm
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  rw [f.transverseNormalCore_coordChange hn hm hdim x₀ x₁ x]
  simp only [transverseNormalTrivialization.eq_def]
  exact f.mfderiv_eq_coordChangeL_normalSpaceTrivializationOfLevel_one_smul hn hm hdim
    _ _ _ _ _ _ _ _ _ _ _ _ hx

end TransverseEquations

end SliceAndTransverse

/-- In codimension one (`finrank 𝕜 E + 1 = finrank 𝕜 V`), the scalar field `𝕜` has dimension equal
to the codimension `finrank 𝕜 V - finrank 𝕜 E`. -/
theorem finrank_self_eq_sub_of_codim_one
    (hcodim : Module.finrank 𝕜 E + 1 = Module.finrank 𝕜 V) :
    Module.finrank 𝕜 𝕜 = Module.finrank 𝕜 V - Module.finrank 𝕜 E := by
  rw [Module.finrank_self]; omega

/-- In codimension one (`finrank 𝕜 E + 1 = finrank 𝕜 V`), every normal fibre has `𝕜`-rank `1`. -/
theorem finrank_normalSpace_of_codim_one [FiniteDimensional 𝕜 V]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hcodim : Module.finrank 𝕜 E + 1 = Module.finrank 𝕜 V) (x : M) :
    Module.finrank 𝕜 (f.NormalSpace x hn) = 1 := by
  have h := f.finrank_normalSpace x hn
  have hV : Module.finrank 𝕜 (TangentSpace J (f x)) = Module.finrank 𝕜 V := rfl
  have hE : Module.finrank 𝕜 (TangentSpace I x) = Module.finrank 𝕜 E := rfl
  omega

end TauCeti.SmoothEmbedding
