/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.DefiningEquation
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Level
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
public import TauCeti.Geometry.Manifold.VectorBundle.Core.MaximalAtlas
public import TauCeti.Geometry.Manifold.VectorBundle.Core.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.LinearMapTrivialization
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Level-set trivializations and cocycle models of intrinsic normal bundles

For a `C^n` smooth embedding `f : M → N` (`m + 1 ≤ n`) between manifolds over a complete
nontrivially normed field `𝕜` with finite-dimensional models `E`, `V`, and codimension model `P`
(`finrank 𝕜 P = finrank 𝕜 V - finrank 𝕜 E`), this file connects the quotient normal bundle
`x ↦ f.NormalSpace x hn` (`T_{f x} N / df(T_x M)`) with local defining equations and transition
cocycles:

1. `normalSpaceTrivializationOfLevel`: `C^m`-compatible linear trivializations of `f.NormalSpace`
   from regular level maps, intertwining `dg₀` and `dg₁` on overlaps
   (`coordChangeL_normalSpaceTrivializationOfLevel_mfderiv`,
   `mfderiv_eq_coordChangeL_normalSpaceTrivializationOfLevel_one_smul`).
2. `transverseNormalTrivialization`, `transverseNormalCore`, and `transverseNormalCoreDiffeomorph`:
   canonical `C^m` bundle diffeomorphism between the transverse transition-cocycle model built from
   `TauCeti.SmoothEmbedding.transverseDefiningMap` and `f.NormalSpace`, together with its scalar
   transition properties in codimension one.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapters 5, 6, and 10.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public noncomputable section

open Set Function Filter Topology Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E V P H G M N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [FiniteDimensional 𝕜 P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {n m : ℕ∞ω} [IsManifold I (m + 1) M]

section LevelTrivialization

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 P]
  [IsManifold I 1 M] [IsManifold J 1 N] [IsManifold I (m + 1) M] in
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

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 P]
  [IsManifold I 1 M] [IsManifold J 1 N] [IsManifold I (m + 1) M] in
private theorem levelLinearMap_normalClass (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {g : N → P} {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x))
    {x : M} (hx : x ∈ W) (v : TangentSpace J (f x)) :
    f.levelLinearMap hn hdim hW hgf hreg x (f.normalClass x hn v) =
      mfderiv J 𝓘(𝕜, P) g (f x) v := by
  simp only [levelLinearMap, hx, ↓reduceDIte]
  exact f.normalSpaceEquivOfLevel_normalClass x hn _ _ _ v

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 P]
  [IsManifold I 1 M] [IsManifold J 1 N] [IsManifold I (m + 1) M] in
private theorem bijective_levelLinearMap (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {g : N → P} {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x)) :
    ∀ x ∈ W, Bijective (f.levelLinearMap hn hdim hW hgf hreg x) := fun x hx ↦ by
  simp only [levelLinearMap, hx, ↓reduceDIte]
  exact (f.normalSpaceEquivOfLevel x hn _ _ _).bijective

variable [IsManifold J (m + 1) N]

private theorem contMDiffOn_levelLinearMap (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {U : Set N} (hU : IsOpen U) (hfW : MapsTo f W U)
    {g : N → P} (hg : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g U) {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x)) :
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiffOn (I.prod 𝓘(𝕜, P)) 𝓘(𝕜, P) m
      (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
        f.levelLinearMap hn hdim hW hgf hreg p.proj p.2)
      (π P (fun x ↦ f.NormalSpace x hn) ⁻¹' W) := by
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
    Trivialization P (π P (fun x ↦ f.NormalSpace x hn)) :=
  letI := f.normalSpaceFiberBundle hn hdim; letI := f.normalSpaceVectorBundle hn hdim
  Trivialization.ofContinuousLinearMapOn hW (f.levelLinearMap hn hdim hW hgf hreg)
    (f.contMDiffOn_levelLinearMap hn hm hdim hW hU hfW hg hgf hreg)
    (f.bijective_levelLinearMap hn hdim hW hgf hreg)

@[simp]
theorem baseSet_normalSpaceTrivializationOfLevel (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {U : Set N} (hU : IsOpen U) (hfW : MapsTo f W U)
    {g : N → P} (hg : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g U) {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x)) :
    (f.normalSpaceTrivializationOfLevel hn hm hdim hW hU hfW hg hgf hreg).baseSet = W := by
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  rw [normalSpaceTrivializationOfLevel.eq_def]
  exact Trivialization.baseSet_ofContinuousLinearMapOn _ _ _ _

/-- `normalSpaceTrivializationOfLevel` is `𝕜`-linear on every fibre over `W`. -/
instance isLinear_normalSpaceTrivializationOfLevel (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {U : Set N} (hU : IsOpen U) (hfW : MapsTo f W U)
    {g : N → P} (hg : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g U) {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x)) :
    (f.normalSpaceTrivializationOfLevel hn hm hdim hW hU hfW hg hgf hreg).IsLinear 𝕜 := by
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  rw [normalSpaceTrivializationOfLevel.eq_def]
  exact Trivialization.isLinear_ofContinuousLinearMapOn _ _ _ _

/-- `normalSpaceTrivializationOfLevel` belongs to the `C^m` maximal atlas of `f.NormalSpace`. -/
theorem normalSpaceTrivializationOfLevel_mem_maximalAtlas
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {U : Set N} (hU : IsOpen U) (hfW : MapsTo f W U)
    {g : N → P} (hg : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g U) {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x)) :
    letI := f.normalSpaceFiberBundle hn hdim
    (f.normalSpaceTrivializationOfLevel hn hm hdim hW hU hfW hg hgf hreg).toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear M P I m).maximalAtlas
        (TotalSpace P (fun x ↦ f.NormalSpace x hn)) := by
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
    f.normalSpaceTrivializationOfLevel hn hm hdim hW hU hfW hg hgf hreg p =
      (p.proj, f.normalSpaceEquivOfLevel p.proj hn (eventually_of_mem (hW.mem_nhds hp) hgf)
        (hreg p.proj hp) (f.finrank_add_eq_of_sub_eq hn hdim p.proj) p.2) := by
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  rw [normalSpaceTrivializationOfLevel.eq_def,
    Trivialization.ofContinuousLinearMapOn_apply _ _ _ _ hp]
  simp only [levelLinearMap, hp, ↓reduceDIte, ContinuousLinearEquiv.coe_coe]

/-- Over `W`, `normalSpaceTrivializationOfLevel` sends the normal class of an ambient tangent vector
`v` to `(x, mfderiv J 𝓘(𝕜, P) g (f x) v)`. -/
@[simp]
theorem normalSpaceTrivializationOfLevel_normalClass (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W : Set M} (hW : IsOpen W) {U : Set N} (hU : IsOpen U) (hfW : MapsTo f W U)
    {g : N → P} (hg : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g U) {c : P}
    (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x))
    {x : M} (hx : x ∈ W) (v : TangentSpace J (f x)) :
    f.normalSpaceTrivializationOfLevel hn hm hdim hW hU hfW hg hgf hreg
        ⟨x, f.normalClass x hn v⟩ = (x, mfderiv J 𝓘(𝕜, P) g (f x) v) := by
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
    (f.normalSpaceTrivializationOfLevel hn hm hdim hW₀ hU₀ hfW₀ hg₀ hgf₀ hreg₀).coordChangeL 𝕜
      (f.normalSpaceTrivializationOfLevel hn hm hdim hW₁ hU₁ hfW₁ hg₁ hgf₁ hreg₁) x
      (mfderiv J 𝓘(𝕜, P) g₀ (f x) v) = mfderiv J 𝓘(𝕜, P) g₁ (f x) v := by
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  rw [← f.levelLinearMap_normalClass hn hdim hW₀ hgf₀ hreg₀ hx.1 v,
    ← f.levelLinearMap_normalClass hn hdim hW₁ hgf₁ hreg₁ hx.2 v]
  simp only [normalSpaceTrivializationOfLevel.eq_def]
  exact Trivialization.coordChangeL_ofContinuousLinearMapOn_apply _ _ _ _ _ _ _ _ hx _

omit [FiniteDimensional 𝕜 P] in
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
    mfderiv J 𝓘(𝕜, 𝕜) g₁ (f x) =
      ((f.normalSpaceTrivializationOfLevel hn hm hdim hW₀ hU₀ hfW₀ hg₀ hgf₀ hreg₀).coordChangeL 𝕜
        (f.normalSpaceTrivializationOfLevel hn hm hdim hW₁ hU₁ hfW₁ hg₁ hgf₁ hreg₁) x 1) •
        mfderiv J 𝓘(𝕜, 𝕜) g₀ (f x) := by
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

/-! ### Transition-cocycle model from transverse defining equations -/

section TransverseCore

variable [I.Boundaryless] [J.Boundaryless] [IsManifold J n N]

/-- The `C^m`-compatible linear trivialization of `f.NormalSpace` around `x₀` induced by the chosen
transverse defining equation `f.transverseDefiningMap`. -/
def transverseNormalTrivialization (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    Trivialization P (π P (fun x ↦ f.NormalSpace x hn)) :=
  haveI : IsManifold J (m + 1) N := .of_le hm
  have hn1 : 1 ≤ n := ENat.one_le_iff_ne_zero_withTop.mpr hn
  f.normalSpaceTrivializationOfLevel hn hm hdim
    ((f.isOpen_transverseAmbSet hn1 hdim x₀).preimage (map_continuous f))
    (f.isOpen_transverseAmbSet hn1 hdim x₀) (fun _ hx ↦ hx)
    ((f.contMDiffOn_transverseDefiningMap hn1 hdim x₀).of_le hm)
    (fun x hx ↦ (f.mem_range_iff_transverseDefiningMap_eq_zero hn1 hdim x₀ hx).1 (mem_range_self x))
    (fun _ hx ↦ f.isRegularPoint_transverseDefiningMap hn1 hdim x₀ hx)

@[simp]
theorem baseSet_transverseNormalTrivialization (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) :
    (f.transverseNormalTrivialization hn hm hdim x₀).baseSet =
      f ⁻¹' f.transverseAmbSet (ENat.one_le_iff_ne_zero_withTop.mpr hn) hdim x₀ := by
  have : IsManifold J (m + 1) N := .of_le hm
  rw [transverseNormalTrivialization.eq_def]
  exact f.baseSet_normalSpaceTrivializationOfLevel hn hm hdim _ _ _ _ _ _

/-- The base point `x₀` belongs to the base set of `f.transverseNormalTrivialization` at `x₀`. -/
theorem mem_baseSet_transverseNormalTrivialization (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) :
    x₀ ∈ (f.transverseNormalTrivialization hn hm hdim x₀).baseSet := by
  rw [f.baseSet_transverseNormalTrivialization hn hm hdim x₀]
  exact f.apply_mem_transverseAmbSet _ hdim x₀

/-- `f.transverseNormalTrivialization` is `𝕜`-linear on every fibre over its base set. -/
instance isLinear_transverseNormalTrivialization (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) :
    (f.transverseNormalTrivialization hn hm hdim x₀).IsLinear 𝕜 := by
  have : IsManifold J (m + 1) N := .of_le hm
  rw [transverseNormalTrivialization.eq_def]
  exact f.isLinear_normalSpaceTrivializationOfLevel hn hm hdim _ _ _ _ _ _

/-- `f.transverseNormalTrivialization` lies in the `C^m` maximal atlas of `f.NormalSpace`. -/
theorem transverseNormalTrivialization_mem_maximalAtlas (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) :
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
    {hn1 : 1 ≤ n} (x₀ : M) {x : M} (hx : f x ∈ f.transverseAmbSet hn1 hdim x₀)
    (v : TangentSpace J (f x)) :
    f.transverseNormalTrivialization hn hm hdim x₀ ⟨x, f.normalClass x hn v⟩ =
      (x, mfderiv J 𝓘(𝕜, P) (f.transverseDefiningMap hn1 hdim x₀) (f x) v) := by
  have : IsManifold J (m + 1) N := .of_le hm
  rw [transverseNormalTrivialization.eq_def]
  exact f.normalSpaceTrivializationOfLevel_normalClass hn hm hdim _ _ _ _ _ _ hx v

/-- **Transition-cocycle `VectorBundleCore` of the normal bundle from transverse charts.** At each
point `x₀ : M`, the open set is `f ⁻¹' (f.transverseAmbSet _ hdim x₀)` and the transition cocycle is
the coordinate change between `f.transverseNormalTrivialization` charts. -/
def transverseNormalCore (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    VectorBundleCore 𝕜 M P M :=
  letI := f.normalSpaceFiberBundle hn hdim
  VectorBundleCore.ofMaximalAtlas (f.transverseNormalTrivialization hn hm hdim)
    (f.transverseNormalTrivialization_mem_maximalAtlas hn hm hdim) _root_.id
    (f.mem_baseSet_transverseNormalTrivialization hn hm hdim)

@[simp]
theorem transverseNormalCore_localTriv_baseSet (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) :
    ((f.transverseNormalCore hn hm hdim).localTriv x₀).baseSet =
      f ⁻¹' f.transverseAmbSet (ENat.one_le_iff_ne_zero_withTop.mpr hn) hdim x₀ := by
  let := f.normalSpaceFiberBundle hn hdim
  rw [transverseNormalCore.eq_def, VectorBundleCore.ofMaximalAtlas_localTriv_baseSet,
    f.baseSet_transverseNormalTrivialization]

/-- The `x₀`-th base set of `f.transverseNormalCore` is `f ⁻¹' f.transverseAmbSet _ hdim x₀`.
(Note that `simp` reduces `(f.transverseNormalCore ...).baseSet x₀` via
`VectorBundleCore.baseSet_at` and `transverseNormalCore_localTriv_baseSet`.) -/
theorem transverseNormalCore_baseSet (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ : M) :
    (f.transverseNormalCore hn hm hdim).baseSet x₀ =
      f ⁻¹' f.transverseAmbSet (ENat.one_le_iff_ne_zero_withTop.mpr hn) hdim x₀ := by
  rw [VectorBundleCore.baseSet_at, f.transverseNormalCore_localTriv_baseSet]

/-- The coordinate change of `f.transverseNormalCore` from `x₀` to `x₁` at `x` is the
`coordChangeL` between the corresponding transverse defining-equation trivializations. -/
theorem transverseNormalCore_coordChange (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (x₀ x₁ x : M) :
    (f.transverseNormalCore hn hm hdim).coordChange x₀ x₁ x =
      ((f.transverseNormalTrivialization hn hm hdim x₀).coordChangeL 𝕜
        (f.transverseNormalTrivialization hn hm hdim x₁) x : P →L[𝕜] P) := by
  let := f.normalSpaceFiberBundle hn hdim
  rw [transverseNormalCore.eq_def, VectorBundleCore.ofMaximalAtlas_coordChange]

/-- The transition cocycle `f.transverseNormalCore` is `C^m`. -/
instance isContMDiff_transverseNormalCore (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    (f.transverseNormalCore hn hm hdim).IsContMDiff I m := by
  let := f.normalSpaceFiberBundle hn hdim
  rw [transverseNormalCore.eq_def]
  exact VectorBundleCore.isContMDiff_ofMaximalAtlas _ _ _ _

/-- Fibrewise continuous linear equivalence between the reconstructed fibre of
`f.transverseNormalCore` at `x` and the quotient normal space `f.NormalSpace x hn`. -/
def transverseNormalCoreFiberEquiv (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x : M) :
    (f.transverseNormalCore hn hm hdim).Fiber x ≃L[𝕜] f.NormalSpace x hn :=
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
    letI := f.normalSpaceFiberBundle hn hdim
    (f.transverseNormalCore hn hm hdim).TotalSpace ≃ₘ^m⟮I.prod 𝓘(𝕜, P), I.prod 𝓘(𝕜, P)⟯
      TotalSpace P (fun x ↦ f.NormalSpace x hn) :=
  haveI : IsManifold J (m + 1) N := .of_le hm
  letI := f.normalSpaceFiberBundle hn hdim; letI := f.normalSpaceVectorBundle hn hdim
  letI := f.normalSpaceContMDiffVectorBundle hn hm hdim
  VectorBundleCore.ofMaximalAtlasDiffeomorph (f.transverseNormalTrivialization hn hm hdim)
    (f.transverseNormalTrivialization_mem_maximalAtlas hn hm hdim) _root_.id
    (f.mem_baseSet_transverseNormalTrivialization hn hm hdim)

@[simp]
theorem transverseNormalCoreDiffeomorph_apply (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (p : (f.transverseNormalCore hn hm hdim).TotalSpace) :
    letI := f.normalSpaceFiberBundle hn hdim
    f.transverseNormalCoreDiffeomorph hn hm hdim p =
      ⟨p.proj, f.transverseNormalCoreFiberEquiv hn hm hdim p.proj p.2⟩ := by
  have : IsManifold J (m + 1) N := .of_le hm
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  rw [transverseNormalCoreDiffeomorph.eq_def, transverseNormalCoreFiberEquiv.eq_def]
  exact VectorBundleCore.ofMaximalAtlasDiffeomorph_apply _ _ _ _ p

@[simp]
theorem transverseNormalCoreDiffeomorph_symm_apply (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (q : TotalSpace P (fun x ↦ f.NormalSpace x hn)) :
    letI := f.normalSpaceFiberBundle hn hdim
    (f.transverseNormalCoreDiffeomorph hn hm hdim).symm q =
      ⟨q.proj, (f.transverseNormalCoreFiberEquiv hn hm hdim q.proj).symm q.2⟩ := by
  have : IsManifold J (m + 1) N := .of_le hm
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  rw [transverseNormalCoreDiffeomorph.eq_def, transverseNormalCoreFiberEquiv.eq_def]
  exact VectorBundleCore.ofMaximalAtlasDiffeomorph_symm_apply _ _ _ _ q

/-- `transverseNormalCoreDiffeomorph` intertwines every core chart `localTriv x₀` with the
corresponding transverse defining-equation trivialization `f.transverseNormalTrivialization`. -/
theorem apply_transverseNormalCoreDiffeomorph (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {hn1 : 1 ≤ n} (x₀ : M) (p : (f.transverseNormalCore hn hm hdim).TotalSpace)
    (hp : f p.proj ∈ f.transverseAmbSet hn1 hdim x₀) :
    letI := f.normalSpaceFiberBundle hn hdim
    f.transverseNormalTrivialization hn hm hdim x₀
        (f.transverseNormalCoreDiffeomorph hn hm hdim p) =
      (f.transverseNormalCore hn hm hdim).localTriv x₀ p := by
  have : IsManifold J (m + 1) N := .of_le hm
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
    (hdim : Module.finrank 𝕜 𝕜 = Module.finrank 𝕜 V - Module.finrank 𝕜 E) {hn1 : 1 ≤ n}
    (x₀ x₁ : M) :
    ContMDiffOn I 𝓘(𝕜) m
      (fun x ↦ (f.transverseNormalCore hn hm hdim).coordChange x₀ x₁ x 1)
      (f ⁻¹' f.transverseAmbSet hn1 hdim x₀ ∩ f ⁻¹' f.transverseAmbSet hn1 hdim x₁) := by
  simpa only [f.transverseNormalCore_baseSet] using
    ((f.transverseNormalCore hn hm hdim).isContMDiff_iff_contMDiffOn_coordChange_one
      (IB := I) (n := m)).1 inferInstance x₀ x₁

omit [FiniteDimensional 𝕜 P] in
/-- On every overlap, the scalar transition function of `f.transverseNormalCore` is nonzero. -/
theorem transverseNormalCore_coordChange_one_ne_zero (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 𝕜 = Module.finrank 𝕜 V - Module.finrank 𝕜 E) {hn1 : 1 ≤ n}
    {x₀ x₁ x : M}
    (hx : x ∈ f ⁻¹' f.transverseAmbSet hn1 hdim x₀ ∩ f ⁻¹' f.transverseAmbSet hn1 hdim x₁) :
    (f.transverseNormalCore hn hm hdim).coordChange x₀ x₁ x 1 ≠ 0 := by
  set Z := f.transverseNormalCore hn hm hdim
  have hx0 : x ∈ Z.baseSet x₀ := by rw [f.transverseNormalCore_baseSet]; exact hx.1
  have hx1 : x ∈ Z.baseSet x₁ := by rw [f.transverseNormalCore_baseSet]; exact hx.2
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
    (hdim : Module.finrank 𝕜 𝕜 = Module.finrank 𝕜 V - Module.finrank 𝕜 E) {hn1 : 1 ≤ n}
    {x₀ x₁ x : M}
    (hx : x ∈ f ⁻¹' f.transverseAmbSet hn1 hdim x₀ ∩ f ⁻¹' f.transverseAmbSet hn1 hdim x₁) :
    mfderiv J 𝓘(𝕜, 𝕜) (f.transverseDefiningMap hn1 hdim x₁) (f x) =
      ((f.transverseNormalCore hn hm hdim).coordChange x₀ x₁ x 1) •
        mfderiv J 𝓘(𝕜, 𝕜) (f.transverseDefiningMap hn1 hdim x₀) (f x) := by
  have : IsManifold J (m + 1) N := .of_le hm
  rw [f.transverseNormalCore_coordChange hn hm hdim x₀ x₁ x]
  simp only [transverseNormalTrivialization.eq_def]
  exact f.mfderiv_eq_coordChangeL_normalSpaceTrivializationOfLevel_one_smul hn hm hdim
    _ _ _ _ _ _ _ _ _ _ _ _ hx

end TransverseCore

end TauCeti.SmoothEmbedding
