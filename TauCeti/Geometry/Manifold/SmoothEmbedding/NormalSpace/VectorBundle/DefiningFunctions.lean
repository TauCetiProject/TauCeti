/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Level
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Equiv
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Normal bundles from local defining functions

Let `f : M → N` be an embedding of positive regularity into a finite-dimensional manifold, and
let `P` be a space whose dimension is the codimension of `f`. A *local defining function* near a
point of `M` is a map `g : N → P` which is constant on the image of `f` near that point and whose
differential there is onto, so that the image of `f` is locally a regular level set of `g`.
`TauCeti.SmoothEmbedding.DefiningFunctions` is a point-indexed atlas of such functions: for every
`x : M`, a defining function `φ x` valid on an open neighbourhood `φ.baseSet x` of `x`. For a
complex hypersurface of a complex manifold, `P = ℂ` and the `φ x` are local holomorphic equations.

The differential of `φ x` identifies the intrinsic normal space `T_(f y) N / df(T_y M)` at a point
`y` of `φ.baseSet x` with `P` (`TauCeti.SmoothEmbedding.DefiningFunctions.normalEquiv`). Two
defining functions are related on their overlap by the transition
`TauCeti.SmoothEmbedding.DefiningFunctions.coordChange`, the linear automorphism of `P` sending
`d(φ x₀)(v)` to `d(φ x₁)(v)`. These transitions are `C^m` when `m + 1 ≤ n`
(`contMDiffOn_coordChange`), and for scalar defining functions they are multiplication by the
ratio of the normal derivatives (`coordChange_apply_eq_div_mul`). They form the vector-bundle
core `TauCeti.SmoothEmbedding.DefiningFunctions.core`, the *transition-cocycle model* of the
normal bundle, which is a `C^m` vector bundle (`isContMDiff_core`).

The main result, `TauCeti.SmoothEmbedding.DefiningFunctions.normalBundleDiffeomorph`, identifies
the intrinsic normal bundle, with its quotient topology and its atlas of complementary normal
coordinates, `C^m`-diffeomorphically over the identity of `M` with the transition-cocycle model:
in the chart at `x₀` of the model, a normal vector is read through the differential of the
defining function `φ x₀` (`localTriv_core_normalBundleDiffeomorph`). Every embedding has such an
atlas (`TauCeti.SmoothEmbedding.nonempty_definingFunctions`): in charts in which the embedding is
the inclusion `u ↦ (u, 0)`, the second coordinate is a defining function.

Over `𝕜 = ℂ` with `m = n = ∞` all of this is holomorphic. The normal bundle of a complex
hypersurface is then biholomorphic to the holomorphic line bundle whose transition functions are
the ratios `∂_ν g₁ / ∂_ν g₀` of the normal derivatives of local equations. This is the cocycle
through which the adjunction formula compares the normal bundle with the line bundle of the
hypersurface; that comparison is not made here.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 5 (embedded
  submanifolds, slice charts and local defining functions).
* D. Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.4 (the normal
  bundle of a hypersurface and the adjunction formula).
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 1,
  Section 1 (normal bundles of submanifolds and line bundles of divisors).
-/

public noncomputable section

open Set Function Filter Topology Bundle Module
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

variable (P) in
/-- A point-indexed atlas of local defining functions for the image of an embedding
`f : M → N`: for every `x : M`, a `C^n` map `φ x : N → P` which is constant on the image of `f`
near every point `y` of an open neighbourhood `φ.baseSet x` of `x`, and whose differential at
`f y` is onto. When `P` has the dimension of the codimension of `f`, the image of `f` is locally
the regular level set of `φ x`. For a complex hypersurface, `P = ℂ` and `φ x` is a local
holomorphic equation of the hypersurface. -/
structure DefiningFunctions (f : SmoothEmbedding I J n M N) where
  /-- The open set of `M` on which the defining function chosen at `x` cuts out the image. -/
  baseSet : M → Set M
  /-- Each base set is open. -/
  isOpen_baseSet (x : M) : IsOpen (baseSet x)
  /-- Each point lies in its own base set. -/
  mem_baseSet (x : M) : x ∈ baseSet x
  /-- The defining function chosen at `x`. -/
  toFun : M → N → P
  /-- The defining function chosen at `x` is `C^n` at the image of every point of its base set. -/
  contMDiffAt (x : M) {y : M} (hy : y ∈ baseSet x) : ContMDiffAt J 𝓘(𝕜, P) n (toFun x) (f y)
  /-- The defining function chosen at `x` is constant on the image of `f` near every point of its
  base set. -/
  eventually_eq (x : M) {y : M} (hy : y ∈ baseSet x) :
    ∀ᶠ z in 𝓝 y, toFun x (f z) = toFun x (f y)
  /-- The differential of the defining function chosen at `x` is onto at the image of every point
  of its base set. -/
  isRegularPoint (x : M) {y : M} (hy : y ∈ baseSet x) :
    IsRegularPoint J 𝓘(𝕜, P) (toFun x) (f y)

namespace DefiningFunctions

variable {f : SmoothEmbedding I J n M N}

attribute [coe] DefiningFunctions.toFun

instance : CoeFun (f.DefiningFunctions P) (fun _ ↦ M → N → P) :=
  ⟨DefiningFunctions.toFun⟩

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 V] (φ : f.DefiningFunctions P) (hn : n ≠ 0)
  (hdim : finrank 𝕜 E + finrank 𝕜 P = finrank 𝕜 V)

/-- The identification of the normal space at `y` with `P` by the differential of the defining
function chosen at `x`, for `y` in its base set. -/
def normalEquiv (x : M) {y : M} (hy : y ∈ φ.baseSet x) : f.isImmersion.NormalSpace y hn ≃L[𝕜] P :=
  f.normalSpaceEquivOfLevel y hn (φ.eventually_eq x hy) (φ.isRegularPoint x hy) hdim

/-- The defining function chosen at `x` sends the normal class of an ambient tangent vector to
its differential. -/
@[simp]
theorem normalEquiv_normalClass (x : M) {y : M} (hy : y ∈ φ.baseSet x)
    (v : TangentSpace J (f y)) :
    φ.normalEquiv hn hdim x hy (f.isImmersion.normalClass y hn v) =
      mfderiv J 𝓘(𝕜, P) (φ x) (f y) v :=
  f.normalSpaceEquivOfLevel_normalClass y hn _ _ hdim v

/-- The transition from the defining function chosen at `x₀` to the one chosen at `x₁`: at a
point `y` of both base sets it is the linear automorphism of `P` sending `d(φ x₀)(v)` to
`d(φ x₁)(v)` for every ambient tangent vector `v` at `f y`. Outside the overlap it is the
identity. -/
def coordChange (x₀ x₁ y : M) : P →L[𝕜] P :=
  open scoped Classical in
  if h : y ∈ φ.baseSet x₀ ∩ φ.baseSet x₁ then
    (((φ.normalEquiv hn hdim x₀ h.1).symm.trans (φ.normalEquiv hn hdim x₁ h.2) : P ≃L[𝕜] P) :
      P →L[𝕜] P)
  else ContinuousLinearMap.id 𝕜 P

/-- The transition between two defining functions intertwines their normal identifications. -/
theorem coordChange_normalEquiv {x₀ x₁ y : M} (h₀ : y ∈ φ.baseSet x₀) (h₁ : y ∈ φ.baseSet x₁)
    (v : f.isImmersion.NormalSpace y hn) :
    φ.coordChange hn hdim x₀ x₁ y (φ.normalEquiv hn hdim x₀ h₀ v) =
      φ.normalEquiv hn hdim x₁ h₁ v := by
  simp [coordChange, h₀, h₁]

/-- **The transition law of defining functions.** The transition from the defining function
chosen at `x₀` to the one chosen at `x₁` sends the differential of the first to the differential
of the second. For a hypersurface, with `P` the scalar field, it is multiplication by the ratio
of the two normal derivatives (`coordChange_apply_eq_div_mul`). -/
theorem coordChange_mfderiv {x₀ x₁ y : M} (h₀ : y ∈ φ.baseSet x₀) (h₁ : y ∈ φ.baseSet x₁)
    (v : TangentSpace J (f y)) :
    φ.coordChange hn hdim x₀ x₁ y (mfderiv J 𝓘(𝕜, P) (φ x₀) (f y) v) =
      mfderiv J 𝓘(𝕜, P) (φ x₁) (f y) v := by
  rw [← φ.normalEquiv_normalClass hn hdim x₀ h₀, φ.coordChange_normalEquiv hn hdim h₀ h₁,
    φ.normalEquiv_normalClass]

/-- The transition from a defining function to itself is the identity on its base set. -/
theorem coordChange_self {x y : M} (hy : y ∈ φ.baseSet x) (w : P) :
    φ.coordChange hn hdim x x y w = w := by
  obtain ⟨v, rfl⟩ := (φ.normalEquiv hn hdim x hy).surjective w
  exact φ.coordChange_normalEquiv hn hdim hy hy v

/-- The transitions between defining functions satisfy the cocycle condition on triple
overlaps. -/
theorem coordChange_comp {x₀ x₁ x₂ y : M} (h₀ : y ∈ φ.baseSet x₀) (h₁ : y ∈ φ.baseSet x₁)
    (h₂ : y ∈ φ.baseSet x₂) (w : P) :
    φ.coordChange hn hdim x₁ x₂ y (φ.coordChange hn hdim x₀ x₁ y w) =
      φ.coordChange hn hdim x₀ x₂ y w := by
  obtain ⟨v, rfl⟩ := (φ.normalEquiv hn hdim x₀ h₀).surjective w
  rw [φ.coordChange_normalEquiv hn hdim h₀ h₁, φ.coordChange_normalEquiv hn hdim h₁ h₂,
    φ.coordChange_normalEquiv hn hdim h₀ h₂]

/-- **The transitions of a hypersurface are ratios of normal derivatives.** For scalar-valued
defining functions, as for the local equations of a hypersurface, the transition from the
defining function chosen at `x₀` to the one chosen at `x₁` is multiplication by the ratio
`d(φ x₁)(ν) / d(φ x₀)(ν)` of their derivatives along any nonzero normal vector `ν`. On the normal
class of an ambient tangent vector `v`, `normalEquiv` is `d(φ x)(v)` (`normalEquiv_normalClass`). -/
theorem coordChange_apply_eq_div_mul (φ : f.DefiningFunctions 𝕜)
    (hdim : finrank 𝕜 E + finrank 𝕜 𝕜 = finrank 𝕜 V) {x₀ x₁ y : M} (h₀ : y ∈ φ.baseSet x₀)
    (h₁ : y ∈ φ.baseSet x₁) {ν : f.isImmersion.NormalSpace y hn} (hν : ν ≠ 0) (w : 𝕜) :
    φ.coordChange hn hdim x₀ x₁ y w =
      φ.normalEquiv hn hdim x₁ h₁ ν / φ.normalEquiv hn hdim x₀ h₀ ν * w := by
  have ha : φ.normalEquiv hn hdim x₀ h₀ ν ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (φ.normalEquiv hn hdim x₀ h₀).injective]
  have hw : w = (w / φ.normalEquiv hn hdim x₀ h₀ ν) • φ.normalEquiv hn hdim x₀ h₀ ν := by
    rw [smul_eq_mul, div_mul_cancel₀ w ha]
  rw [hw, map_smul, φ.coordChange_normalEquiv hn hdim h₀ h₁, smul_eq_mul, smul_eq_mul]
  field_simp

variable [FiniteDimensional 𝕜 P] [IsManifold I 1 M] [IsManifold J 1 N]

/-- The transitions between defining functions are `C^m` on the overlaps of their base sets, for
a `C^n` embedding and `C^n` defining functions with `m + 1 ≤ n`. -/
theorem contMDiffOn_coordChange (hm : m + 1 ≤ n) (x₀ x₁ : M) :
    ContMDiffOn I 𝓘(𝕜, P →L[𝕜] P) m (φ.coordChange hn hdim x₀ x₁)
      (φ.baseSet x₀ ∩ φ.baseSet x₁) := by
  intro y₀ hy₀
  apply ContMDiffAt.contMDiffWithinAt
  have : CompleteSpace P := FiniteDimensional.completeSpace 𝕜 P
  -- The differentials of the defining functions, read in the tangent chart at `f y₀`.
  let A : M → M → V →L[𝕜] P := fun x ↦ inTangentCoordinates J 𝓘(𝕜, P) (f : M → N)
    (fun y ↦ φ x (f y)) (fun y ↦ mfderiv J 𝓘(𝕜, P) (φ x) (f y)) y₀
  have hA (x : M) (hx : y₀ ∈ φ.baseSet x) : ContMDiffAt I 𝓘(𝕜, V →L[𝕜] P) m (A x) y₀ :=
    ContMDiffAt.mfderiv (fun _ ↦ φ x) (f : M → N)
      ((φ.contMDiffAt x hx).comp (y₀, f y₀) contMDiffAt_snd)
      (f.contMDiff.contMDiffAt.of_le (le_self_add.trans hm)) hm
  have hAeq (x y : M) (v : V) : A x y v = mfderiv J 𝓘(𝕜, P) (φ x) (f y)
      ((trivializationAt V (TangentSpace J) (f y₀)).symmL 𝕜 (f y) v) := by
    simp only [A, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
      TangentBundle.continuousLinearMapAt_model_space]
    -- `1 ∘L _` applied to `v`: the composition passes through the tangent spaces of the model
    -- space `P`, which are `P` itself, so `simp` cannot match `comp_apply`; the identity is `rfl`.
    rfl
  have hcomp {y : M} (hy : y ∈ φ.baseSet x₀ ∩ φ.baseSet x₁) (v : V) :
      φ.coordChange hn hdim x₀ x₁ y (A x₀ y v) = A x₁ y v := by
    rw [hAeq, hAeq]
    exact φ.coordChange_mfderiv hn hdim hy.1 hy.2 _
  -- A smooth right inverse `R` of the first differential near `y₀` gives `coordChange = A₁ ∘ R`.
  have hsurj : Surjective (A x₀ y₀) := by
    intro w
    obtain ⟨v, hv⟩ := isRegularPoint_iff.1 (φ.isRegularPoint x₀ hy₀.1) w
    refine ⟨(trivializationAt V (TangentSpace J) (f y₀)).continuousLinearMapAt 𝕜 (f y₀) v, ?_⟩
    rw [hAeq, Trivialization.symmL_continuousLinearMapAt _
      (mem_baseSet_trivializationAt V (TangentSpace J) (f y₀))]
    exact hv
  obtain ⟨R, hR, hRA⟩ := (hA x₀ hy₀.1).exists_contMDiffAt_rightInverse (𝕜' := 𝕜)
    (.of_surjective_of_finiteDimensional hsurj)
  apply ((hA x₁ hy₀.2).clm_comp hR).congr_of_eventuallyEq
  filter_upwards [hRA, ((φ.isOpen_baseSet x₀).inter (φ.isOpen_baseSet x₁)).mem_nhds hy₀]
    with y hy hy'
  ext w
  rw [ContinuousLinearMap.comp_apply, ← hcomp hy', hy w]

/-- **The transition-cocycle model of the normal bundle.** The vector-bundle core over `M` with
fibre `P` whose chart at `x` has base set `φ.baseSet x` and whose transitions are the transitions
`φ.coordChange` between the differentials of the defining functions. Its charts are indexed by
the points of `M`, the chart at `x` being labelled by `x`. -/
def core : VectorBundleCore 𝕜 M P M where
  baseSet := φ.baseSet
  isOpen_baseSet := φ.isOpen_baseSet
  indexAt x := x
  mem_baseSet_at := φ.mem_baseSet
  coordChange := φ.coordChange hn hdim
  coordChange_self _ _ hy := φ.coordChange_self hn hdim hy
  continuousOn_coordChange x₀ x₁ :=
    (φ.contMDiffOn_coordChange hn hdim (m := 0)
      (by simpa using ENat.one_le_iff_ne_zero_withTop.mpr hn) x₀ x₁).continuousOn
  coordChange_comp _ _ _ _ hy w := φ.coordChange_comp hn hdim hy.1.1 hy.1.2 hy.2 w

@[simp]
theorem core_baseSet : (φ.core hn hdim).baseSet = φ.baseSet := (rfl)

@[simp]
theorem core_indexAt (x : M) : (φ.core hn hdim).indexAt x = x := (rfl)

@[simp]
theorem core_coordChange : (φ.core hn hdim).coordChange = φ.coordChange hn hdim := (rfl)

/-- The transition-cocycle model of the normal bundle is a `C^m` vector bundle for a `C^n`
embedding and `C^n` defining functions with `m + 1 ≤ n`. Over `ℂ`, with `m = n = ∞`, it is a
holomorphic vector bundle. -/
theorem isContMDiff_core (hm : m + 1 ≤ n) : (φ.core hn hdim).IsContMDiff I m :=
  ⟨fun x₀ x₁ ↦ by
    simpa only [core_coordChange, core_baseSet] using φ.contMDiffOn_coordChange hn hdim hm x₀ x₁⟩

/-- The chart at `x` of the transition-cocycle model reads a vector over a point `y` of its base
set, given in the chart at `y` by a differential `d(φ y)(v)`, as the differential `d(φ x)(v)`. -/
theorem localTriv_core_mk_mfderiv {x y : M} (hy : y ∈ φ.baseSet x) (v : TangentSpace J (f y)) :
    (φ.core hn hdim).localTriv x ⟨y, mfderiv J 𝓘(𝕜, P) (φ y) (f y) v⟩ =
      (y, mfderiv J 𝓘(𝕜, P) (φ x) (f y) v) := by
  rw [VectorBundleCore.localTriv_apply, core_indexAt, core_coordChange,
    φ.coordChange_mfderiv hn hdim (φ.mem_baseSet y) hy]
  rfl

/-- Reading an ambient tangent vector along the embedding through the differential of the
defining function chosen at its base point is a `C^m` map from the pulled-back ambient tangent
bundle to the transition-cocycle model. -/
theorem contMDiff_totalSpaceMk_mfderiv (hm : m + 1 ≤ n) :
    ContMDiff (I.prod 𝓘(𝕜, V)) (I.prod 𝓘(𝕜, P)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' P (E := (φ.core hn hdim).Fiber) p.proj
          (mfderiv J 𝓘(𝕜, P) (φ p.proj) (f p.proj) p.snd)) := by
  intro p
  have hfm : ContMDiff I J m f := f.contMDiff.of_le (le_self_add.trans hm)
  have hproj : ContMDiff (I.prod 𝓘(𝕜, V)) I m
      (fun q : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦ q.proj) :=
    Bundle.contMDiff_proj _
  rw [contMDiffAt_totalSpace_iff]
  refine ⟨hproj p, ?_⟩
  -- In the chart at `p.proj`, the vector is the differential of the defining function at `p.proj`.
  have hlift := (Bundle.Pullback.contMDiff_lift (E := TangentSpace J) f hfm) p
  have htan : ContMDiffAt (I.prod 𝓘(𝕜, V)) (𝓘(𝕜, P).prod 𝓘(𝕜, P)) m
      (fun q : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' P (E := TangentSpace 𝓘(𝕜, P)) (φ p.proj (f q.proj))
          (mfderiv J 𝓘(𝕜, P) (φ p.proj) (f q.proj) q.snd)) p :=
    ContMDiffAt.mfderiv_apply_sectionAlong (φ.contMDiffAt p.proj (φ.mem_baseSet p.proj))
      (b := fun q : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦ f q.proj) hlift hm
  -- The fibre coordinate of the tangent bundle of the model space `P` is the vector itself.
  have hsnd : ContMDiffAt (I.prod 𝓘(𝕜, V)) 𝓘(𝕜, P) m
      (fun q : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        mfderiv J 𝓘(𝕜, P) (φ p.proj) (f q.proj) q.snd) p := by
    simpa [TangentBundle.trivializationAt_apply] using (contMDiffAt_totalSpace_iff.1 htan).2
  apply hsnd.congr_of_eventuallyEq
  filter_upwards [((φ.isOpen_baseSet p.proj).preimage (hproj.continuous)).mem_nhds
    (φ.mem_baseSet p.proj)] with q hq
  exact congrArg Prod.snd (φ.localTriv_core_mk_mfderiv hn hdim hq q.snd)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 P] [IsManifold I 1 M] [IsManifold J 1 N] in
include hdim in
/-- The differential of the defining function chosen at `x` vanishes exactly on the vectors
tangent to the embedded submanifold. -/
theorem mfderiv_eq_zero_iff (x : M) (v : TangentSpace J (f x)) :
    mfderiv J 𝓘(𝕜, P) (φ x) (f x) v = 0 ↔ v ∈ f.isImmersion.tangentRange x hn := by
  rw [f.tangentRange_eq_ker_mfderiv x hn (φ.eventually_eq x (φ.mem_baseSet x))
    (φ.isRegularPoint x (φ.mem_baseSet x)) hdim, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

variable [FiniteDimensional 𝕜 E] [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]

/-- The identification of the normal spaces by the differentials of the chosen defining functions
is a `C^m` map from the intrinsic normal bundle to the transition-cocycle model. -/
theorem contMDiff_normalEquiv (hm : m + 1 ≤ n) :
    letI := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
    ContMDiff (I.prod 𝓘(𝕜, P)) (I.prod 𝓘(𝕜, P)) m
      (fun p : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ↦
        TotalSpace.mk' P (E := (φ.core hn hdim).Fiber) p.proj
          (φ.normalEquiv hn hdim p.proj (φ.mem_baseSet p.proj) p.snd)) := by
  let := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
  rw [f.contMDiff_normalBundle_iff hn hm (Nat.eq_sub_of_add_eq' hdim)]
  refine (φ.contMDiff_totalSpaceMk_mfderiv hn hdim hm).congr fun ⟨x, v⟩ ↦ ?_
  rw [Function.comp_apply, normalQuotientMap_apply]
  exact congrArg (TotalSpace.mk' P x) (φ.normalEquiv_normalClass hn hdim x _ v)

/-- **The normal bundle is the transition-cocycle model.** For a `C^n` embedding with local
defining functions `φ` and `m + 1 ≤ n`, the intrinsic normal bundle, with model fibre `P` of the
codimension, is `C^m`-diffeomorphic over the identity of `M` to the total space of the
vector-bundle core `φ.core` built from the transitions between the differentials of the defining
functions. On the fibre over `x` it is the identification `φ.normalEquiv` given by the defining
function chosen at `x`, and in the chart at `x₀` of the core it is the one given by the defining
function chosen at `x₀` (`localTriv_core_normalBundleDiffeomorph`). For a complex hypersurface,
with `𝕜 = ℂ`, `P = ℂ` and `m = n = ∞`, it identifies the normal bundle biholomorphically with
the holomorphic line bundle whose transitions are the ratios of the normal derivatives of local
equations (`coordChange_apply_eq_div_mul`). -/
def normalBundleDiffeomorph (hm : m + 1 ≤ n) :
    letI := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
    TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^m⟮I.prod 𝓘(𝕜, P), I.prod 𝓘(𝕜, P)⟯
      (φ.core hn hdim).TotalSpace :=
  letI := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
  letI := f.normalSpaceVectorBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
  TauCeti.bundleDiffeomorph (E₂ := (φ.core hn hdim).Fiber)
    (fun x ↦ φ.normalEquiv hn hdim x (φ.mem_baseSet x)) (φ.contMDiff_normalEquiv hn hdim hm)

/-- The diffeomorphism sends a normal vector at `x` to its image under the differential of the
defining function chosen at `x`. -/
@[simp]
theorem normalBundleDiffeomorph_apply (hm : m + 1 ≤ n)
    (p : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn)) :
    letI := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
    φ.normalBundleDiffeomorph hn hdim hm p =
      ⟨p.proj, φ.normalEquiv hn hdim p.proj (φ.mem_baseSet p.proj) p.snd⟩ :=
  letI := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
  letI := f.normalSpaceVectorBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
  TauCeti.bundleDiffeomorph_apply _ _ p

/-- The inverse diffeomorphism sends a vector over `x` to the normal vector whose image under the
differential of the defining function chosen at `x` it is. -/
@[simp]
theorem normalBundleDiffeomorph_symm_apply (hm : m + 1 ≤ n) (q : (φ.core hn hdim).TotalSpace) :
    letI := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
    (φ.normalBundleDiffeomorph hn hdim hm).symm q =
      ⟨q.proj, (φ.normalEquiv hn hdim q.proj (φ.mem_baseSet q.proj)).symm q.snd⟩ := by
  let := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
  let := f.normalSpaceVectorBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
  exact TauCeti.bundleDiffeomorph_symm_apply _ _ q

/-- In the chart at `x₀` of the transition-cocycle model, the comparison diffeomorphism is the
identification of the normal spaces by the differential of the defining function chosen at
`x₀`: the defining function at `x₀` trivializes the normal bundle over its base set. -/
theorem localTriv_core_normalBundleDiffeomorph (hm : m + 1 ≤ n) {x₀ : M}
    (p : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn)) (hp : p.proj ∈ φ.baseSet x₀) :
    letI := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
    (φ.core hn hdim).localTriv x₀ (φ.normalBundleDiffeomorph hn hdim hm p) =
      (p.proj, φ.normalEquiv hn hdim x₀ hp p.snd) := by
  rw [normalBundleDiffeomorph_apply, VectorBundleCore.localTriv_apply, core_indexAt,
    core_coordChange, φ.coordChange_normalEquiv hn hdim (φ.mem_baseSet p.proj) hp]

end DefiningFunctions

/-! ### Existence of local defining functions -/

section Existence

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 V]

/-- Near every point an embedding of positive regularity into a finite-dimensional manifold has
a defining function with values in a space `P` of the codimension: the second coordinate, read
in `P`, of a chart of the target in which the embedding is the inclusion `u ↦ (u, 0)`. -/
theorem exists_definingFunction [FiniteDimensional 𝕜 P] (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hdim : finrank 𝕜 E + finrank 𝕜 P = finrank 𝕜 V) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ g : N → P,
      (∀ y ∈ U, ContMDiffAt J 𝓘(𝕜, P) n g (f y)) ∧
      (∀ y ∈ U, ∀ᶠ z in 𝓝 y, g (f z) = g (f y)) ∧
      (∀ y ∈ U, IsRegularPoint J 𝓘(𝕜, P) g (f y)) := by
  have h := f.isImmersion.isImmersionAt x
  obtain ⟨c⟩ := h.nonempty_complement_continuousLinearEquiv (Nat.eq_sub_of_add_eq' hdim)
  -- The second coordinate of the chart `h.codChart`, identified with `P`.
  let T : V →L[𝕜] P := c.toContinuousLinearMap ∘L
    ContinuousLinearMap.snd 𝕜 E h.complement ∘L h.equiv.symm.toContinuousLinearMap
  have hT : Surjective T :=
    c.surjective.comp (Prod.snd_surjective.comp h.equiv.symm.surjective)
  have hzero (y : M) (hy : y ∈ h.domChart.source) : (T ∘ h.codChart.extend J) (f y) = 0 := by
    have hw := h.writtenInCharts ((h.domChart.extend I).map_source (by simpa using hy))
    simp only [Function.comp_apply, (h.domChart.extend I).left_inv (by simpa using hy)] at hw
    simp only [T, ContinuousLinearMap.coe_comp, Function.comp_apply, hw]
    simp
  have hmax : h.codChart ∈ IsManifold.maximalAtlas J 1 N :=
    IsManifold.maximalAtlas_subset_of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn)
      h.codChart_mem_maximalAtlas
  refine ⟨h.domChart.source, h.domChart.open_source, h.mem_domChart_source,
    T ∘ h.codChart.extend J, fun y hy ↦ ?_, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · exact T.contDiff.comp_contMDiffAt (h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas
      (h.source_subset_preimage_source hy))
  · filter_upwards [h.domChart.open_source.mem_nhds hy] with z hz
    rw [hzero z hz, hzero y hy]
  · have hfy := h.source_subset_preimage_source hy
    obtain ⟨D, hD⟩ := isInvertible_mfderiv_extend hmax hfy
    rw [isRegularPoint_iff, mfderiv_comp (f y) T.mdifferentiableAt
      (h.codChart.mdifferentiableAt_extend hmax hfy), T.mfderiv_eq, ← hD]
    exact hT.comp D.surjective

/-- **Every embedding has local defining functions.** An embedding of positive regularity into a
finite-dimensional manifold admits local defining functions with values in any space `P` of the
codimension (`exists_definingFunction`). -/
theorem nonempty_definingFunctions [FiniteDimensional 𝕜 P] (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hdim : finrank 𝕜 E + finrank 𝕜 P = finrank 𝕜 V) :
    Nonempty (f.DefiningFunctions P) := by
  choose U hU hxU g hg hgf hreg using f.exists_definingFunction hn hdim
  exact ⟨⟨U, hU, hxU, g, hg, hgf, hreg⟩⟩

end Existence

end TauCeti.SmoothEmbedding
