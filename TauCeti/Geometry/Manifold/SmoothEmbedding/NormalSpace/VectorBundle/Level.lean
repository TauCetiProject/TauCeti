/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Level
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
public import TauCeti.Geometry.Manifold.VectorBundle.LinearMapTrivialization
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Level-set trivializations of intrinsic normal bundles

For a `C^n` smooth embedding `f : M → N` (`m + 1 ≤ n`) between manifolds over a complete
nontrivially normed field `𝕜` with finite-dimensional models `E`, `V`, and codimension model `P`
(`finrank 𝕜 P = finrank 𝕜 V - finrank 𝕜 E`), a `C^(m + 1)` map `g : N → P` on an open `U ⊆ N`
containing `f '' W` that is constant along `f '' W` and regular at `f x` for every `x ∈ W` induces
a linear trivialization `TauCeti.SmoothEmbedding.normalSpaceTrivializationOfLevel` of the quotient
normal bundle `x ↦ f.NormalSpace x hn` over `W` belonging to the `C^m` maximal atlas
(`normalSpaceTrivializationOfLevel_mem_maximalAtlas`). On overlaps `W₀ ∩ W₁`, the coordinate change
`coordChangeL` intertwines `dg₀` and `dg₁` (`coordChangeL_normalSpaceTrivializationOfLevel_mfderiv`,
`mfderiv_eq_coordChangeL_normalSpaceTrivializationOfLevel_one_smul`).

For the global `M`-indexed transition-cocycle core built from a point-indexed atlas of defining
functions and its `C^m` bundle diffeomorphism with `f.NormalSpace`, see
`TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.DefiningFunctions`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapters 5, 6, and 10.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public noncomputable section

open Set Function Filter Topology Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E V P H G M N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [FiniteDimensional 𝕜 V] [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  {n m : ℕ∞ω}

section LevelLinearMap

variable (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
  (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
  {W : Set M} (hW : IsOpen W) {g : N → P} {c : P}
  (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x))

private def levelLinearMap (x : M) : f.NormalSpace x hn →L[𝕜] P := by
  classical
  exact if hx : x ∈ W then
      (f.normalSpaceEquivOfLevel x hn (eventually_of_mem (hW.mem_nhds hx) hgf)
        (hreg x hx) (f.finrank_add_eq_of_eq_sub hn hdim x)).toContinuousLinearMap
    else 0

private theorem levelLinearMap_normalClass {x : M} (hx : x ∈ W) (v : TangentSpace J (f x)) :
    f.levelLinearMap hn hdim hW hgf hreg x (f.normalClass x hn v) =
      mfderiv J 𝓘(𝕜, P) g (f x) v := by
  simp only [levelLinearMap, hx, ↓reduceDIte]
  exact f.normalSpaceEquivOfLevel_normalClass x hn _ _ _ v

private theorem bijective_levelLinearMap :
    ∀ x ∈ W, Bijective (f.levelLinearMap hn hdim hW hgf hreg x) := fun x hx ↦ by
  simp only [levelLinearMap, hx, ↓reduceDIte]
  exact (f.normalSpaceEquivOfLevel x hn _ _ _).bijective

end LevelLinearMap

variable [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold J 1 N] [IsManifold I (m + 1) M]
  [IsManifold J (m + 1) N]

section SingleLevel

variable [FiniteDimensional 𝕜 P] (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
  (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
  {W : Set M} (hW : IsOpen W) {U : Set N} (hU : IsOpen U) (hfW : MapsTo f W U)
  {g : N → P} (hg : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g U) {c : P}
  (hgf : ∀ x ∈ W, g (f x) = c) (hreg : ∀ x ∈ W, IsRegularPoint J 𝓘(𝕜, P) g (f x))

include hm hU hfW hg in
private theorem contMDiffOn_levelLinearMap :
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiffOn (I.prod 𝓘(𝕜, P)) 𝓘(𝕜, P) m
      (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
        f.levelLinearMap hn hdim hW hgf hreg p.proj p.snd)
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
      (fun q ↦ (tangentMap J 𝓘(𝕜, P) g (Pullback.lift fc (s q))).snd) p :=
    (contMDiff_snd_tangentBundle_modelSpace P 𝓘(𝕜, P)).contMDiffAt.comp p
      ((hgAt.contMDiffAt_tangentMap (m := m) le_rfl).comp p hlift)
  have hopen := hO.inter (hW.preimage (FiberBundle.continuous_proj P _))
  refine (hcomp.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hopen.mem_nhds ⟨hpO, hp⟩] with q ⟨hqO, hqW⟩
  have hsq : f.normalQuotientMap hn (s q) = q := hright hqO
  rw [normalQuotientMap_apply] at hsq
  have hqproj : (s q).proj = q.proj := congrArg TotalSpace.proj hsq
  exact (congrArg (fun r : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
      f.levelLinearMap hn hdim hW hgf hreg r.proj r.snd) hsq.symm).trans
    (f.levelLinearMap_normalClass hn hdim hW hgf hreg (hqproj.symm ▸ hqW) (s q).snd)

/-- **Level-set trivialization of the intrinsic normal bundle.** If `g : N → P` is `C^(m + 1)` on an
open `U ⊆ N` containing `f '' W`, constant along `f '' W`, and regular at `f x` for every `x ∈ W`,
then `mfderiv J 𝓘(𝕜, P) g (f x)` descends to a linear trivialization of `f.NormalSpace` over `W`
belonging to the `C^m` maximal atlas of `f.NormalSpace`. -/
def normalSpaceTrivializationOfLevel : Trivialization P (π P (fun x ↦ f.NormalSpace x hn)) :=
  letI := f.normalSpaceFiberBundle hn hdim; letI := f.normalSpaceVectorBundle hn hdim
  Trivialization.ofContinuousLinearMapOn hW (f.levelLinearMap hn hdim hW hgf hreg)
    (f.contMDiffOn_levelLinearMap hn hm hdim hW hU hfW hg hgf hreg)
    (f.bijective_levelLinearMap hn hdim hW hgf hreg)

@[simp] theorem baseSet_normalSpaceTrivializationOfLevel :
    (f.normalSpaceTrivializationOfLevel hn hm hdim hW hU hfW hg hgf hreg).baseSet = W := by
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  rw [normalSpaceTrivializationOfLevel.eq_def]
  exact Trivialization.baseSet_ofContinuousLinearMapOn _ _ _ _

/-- `normalSpaceTrivializationOfLevel` is `𝕜`-linear on every fibre over `W`. -/
instance isLinear_normalSpaceTrivializationOfLevel :
    (f.normalSpaceTrivializationOfLevel hn hm hdim hW hU hfW hg hgf hreg).IsLinear 𝕜 := by
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  rw [normalSpaceTrivializationOfLevel.eq_def]
  exact Trivialization.isLinear_ofContinuousLinearMapOn _ _ _ _

/-- `normalSpaceTrivializationOfLevel` belongs to the `C^m` maximal atlas of `f.NormalSpace`. -/
theorem normalSpaceTrivializationOfLevel_mem_maximalAtlas :
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
theorem normalSpaceTrivializationOfLevel_apply
    {p : TotalSpace P (fun x ↦ f.NormalSpace x hn)} (hp : p.proj ∈ W) :
    f.normalSpaceTrivializationOfLevel hn hm hdim hW hU hfW hg hgf hreg p =
      (p.proj, f.normalSpaceEquivOfLevel p.proj hn (eventually_of_mem (hW.mem_nhds hp) hgf)
        (hreg p.proj hp) (f.finrank_add_eq_of_eq_sub hn hdim p.proj) p.snd) := by
  let := f.normalSpaceFiberBundle hn hdim; let := f.normalSpaceVectorBundle hn hdim
  rw [normalSpaceTrivializationOfLevel.eq_def,
    Trivialization.ofContinuousLinearMapOn_apply _ _ _ _ hp]
  simp only [levelLinearMap, hp, ↓reduceDIte, ContinuousLinearEquiv.coe_coe]

/-- Over `W`, `normalSpaceTrivializationOfLevel` sends the normal class of an ambient tangent vector
`v` to `(x, mfderiv J 𝓘(𝕜, P) g (f x) v)`. -/
@[simp] theorem normalSpaceTrivializationOfLevel_normalClass
    {x : M} (hx : x ∈ W) (v : TangentSpace J (f x)) :
    f.normalSpaceTrivializationOfLevel hn hm hdim hW hU hfW hg hgf hreg
        ⟨x, f.normalClass x hn v⟩ = (x, mfderiv J 𝓘(𝕜, P) g (f x) v) := by
  rw [f.normalSpaceTrivializationOfLevel_apply hn hm hdim hW hU hfW hg hgf hreg hx]
  exact Prod.ext rfl (f.normalSpaceEquivOfLevel_normalClass _ _ _ _ _ v)

end SingleLevel

/-- **Overlap transition law for level-set normal trivializations.** On `W₀ ∩ W₁`, the fibrewise
coordinate change between two level-set trivializations sends `mfderiv J 𝓘(𝕜, P) g₀ (f x) v` to
`mfderiv J 𝓘(𝕜, P) g₁ (f x) v`. -/
theorem coordChangeL_normalSpaceTrivializationOfLevel_mfderiv [FiniteDimensional 𝕜 P]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W₀ W₁ : Set M} (hW₀ : IsOpen W₀) (hW₁ : IsOpen W₁) {U₀ U₁ : Set N} (hU₀ : IsOpen U₀)
    (hU₁ : IsOpen U₁) (hfW₀ : MapsTo f W₀ U₀) (hfW₁ : MapsTo f W₁ U₁) {g₀ g₁ : N → P}
    (hg₀ : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g₀ U₀) (hg₁ : ContMDiffOn J 𝓘(𝕜, P) (m + 1) g₁ U₁)
    {c₀ c₁ : P} (hgf₀ : ∀ x ∈ W₀, g₀ (f x) = c₀) (hgf₁ : ∀ x ∈ W₁, g₁ (f x) = c₁)
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

/-- **Scalar transition law in codimension one (`P = 𝕜`).** On the overlap `W₀ ∩ W₁` of two scalar
defining equations `g₀, g₁ : N → 𝕜`, `dg₁ (f x)` equals `dg₀ (f x)` scaled by `(e₀.coordChangeL 𝕜
e₁ x) 1`. -/
theorem mfderiv_eq_coordChangeL_normalSpaceTrivializationOfLevel_one_smul
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 𝕜 = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {W₀ W₁ : Set M} (hW₀ : IsOpen W₀) (hW₁ : IsOpen W₁) {U₀ U₁ : Set N} (hU₀ : IsOpen U₀)
    (hU₁ : IsOpen U₁) (hfW₀ : MapsTo f W₀ U₀) (hfW₁ : MapsTo f W₁ U₁) {g₀ g₁ : N → 𝕜}
    (hg₀ : ContMDiffOn J 𝓘(𝕜, 𝕜) (m + 1) g₀ U₀) (hg₁ : ContMDiffOn J 𝓘(𝕜, 𝕜) (m + 1) g₁ U₁)
    {c₀ c₁ : 𝕜} (hgf₀ : ∀ x ∈ W₀, g₀ (f x) = c₀) (hgf₁ : ∀ x ∈ W₁, g₁ (f x) = c₁)
    (hreg₀ : ∀ x ∈ W₀, IsRegularPoint J 𝓘(𝕜, 𝕜) g₀ (f x))
    (hreg₁ : ∀ x ∈ W₁, IsRegularPoint J 𝓘(𝕜, 𝕜) g₁ (f x)) {x : M} (hx : x ∈ W₀ ∩ W₁) :
    mfderiv J 𝓘(𝕜, 𝕜) g₁ (f x) =
      ((f.normalSpaceTrivializationOfLevel hn hm hdim hW₀ hU₀ hfW₀ hg₀ hgf₀ hreg₀).coordChangeL 𝕜
        (f.normalSpaceTrivializationOfLevel hn hm hdim hW₁ hU₁ hfW₁ hg₁ hgf₁ hreg₁) x 1) •
        mfderiv J 𝓘(𝕜, 𝕜) g₀ (f x) := by
  set τ := (f.normalSpaceTrivializationOfLevel hn hm hdim hW₀ hU₀ hfW₀ hg₀ hgf₀ hreg₀).coordChangeL
    𝕜 (f.normalSpaceTrivializationOfLevel hn hm hdim hW₁ hU₁ hfW₁ hg₁ hgf₁ hreg₁) x
  refine ContinuousLinearMap.ext fun v ↦ ?_
  let y₀ : 𝕜 := mfderiv J 𝓘(𝕜, 𝕜) g₀ (f x) v; let y₁ : 𝕜 := mfderiv J 𝓘(𝕜, 𝕜) g₁ (f x) v
  have hv : τ y₀ = y₁ := f.coordChangeL_normalSpaceTrivializationOfLevel_mfderiv hn hm hdim
    hW₀ hW₁ hU₀ hU₁ hfW₀ hfW₁ hg₀ hg₁ hgf₀ hgf₁ hreg₀ hreg₁ hx v
  calc y₁ = τ (y₀ • 1) := by rw [smul_eq_mul, mul_one, hv]
    _ = (τ 1) • y₀ := by rw [map_smul]; simp [smul_eq_mul, mul_comm]

end TauCeti.SmoothEmbedding
