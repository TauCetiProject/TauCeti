/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Section
public import TauCeti.Geometry.Manifold.VectorBundle.RealForm
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Hermitian
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import TauCeti.LinearAlgebra.TotallyReal.CompatibleForm
public import TauCeti.LinearAlgebra.TotallyReal.Complex
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Hermitian metrics compatible with a totally real subbundle

Let `V` be a smooth complex vector bundle over a real manifold and `L` a smooth real subbundle
of `V` whose fibres are maximal totally real, so that `V x = L x ⊕ i L x`. Write `P x` for the
projection of `V x` onto `L x` along `i L x`. For any smooth real bundle metric `g`, the metric

`g'(v, w) = g(P v, P w) + g(P (i v), P (i w))`

is again a smooth bundle metric. It is invariant under multiplication by `i`, so it is the real
part of a Hermitian metric, it agrees with `g` on `L`, and `i L x` is the `g'`-orthogonal
complement of `L x` at every point. Such metrics therefore exist whenever bundle metrics do,
for instance over a σ-compact Hausdorff base.

The projection `P` is defined in `TauCeti.Topology.VectorBundle.RealForm`, and its smoothness is
proved in `TauCeti.Geometry.Manifold.VectorBundle.RealForm`.

Boundary value problems need the relative form. When `L` is only given near a
closed set `S`, such as the boundary of a manifold with boundary, and is maximal totally real
over `S`, there is a smooth Hermitian metric with `i L x = (L x)^⊥` at the points of `S`.

## Main declarations

* `Bundle.ContMDiffRiemannianMetric.totallyRealCompatible`: the metric `g'`.
* `TauCeti.exists_contMDiffRiemannianMetric_compatible_totallyReal`: a smooth Hermitian metric
  with `i L x = (L x)^⊥` at every point exists over a σ-compact Hausdorff base.
* `TauCeti.exists_contMDiffRiemannianMetric_compatible_totallyReal_on`: the same along a closed
  set `S`, for `L` given only near `S` and maximal totally real over `S`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  AMS (2012), Section C.1.
-/

public noncomputable section

open Bundle Set Topology
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {n : ℕ∞ω} {ι : Type*} [Finite ι] {L : ∀ x, Submodule ℝ (V x)}

local instance instVectorBundleRealTotallyReal : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle n F V IB]

/-- **A metric compatible with a totally real subbundle.** For a `C^n` real subbundle `L` of a
complex bundle whose fibres are maximal totally real, and `P` the projection onto `L` along
`i L`, the metric `g'(v, w) = g(P v, P w) + g(P (i v), P (i w))`. -/
def totallyRealCompatible (g : ContMDiffRiemannianMetric IB n F V)
    (hLs : HasLocalContMDiffSubbundleFrames IB n F ι L)
    (hL : ∀ x, IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x)) :
    ContMDiffRiemannianMetric IB n F V :=
  let : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  let : ∀ x, IsNormableSpace ℝ (V x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt ℝ F V x).isNormableSpace
  let P x := totallyRealProjection F (hL x)
  have hP := contMDiff_totallyRealProjection hLs hL
  have hPJ := hP.clm_bundle_comp (contMDiff_smulIEquiv_bundle (IB := IB) (n := n) (G := F) (W := V))
  let b₁ : TauCeti.Manifold.BilinearSection IB F V ℝ n :=
    ⟨fun x ↦ (g.inner x).bilinearComp (P x) (P x), g.contMDiff.bilinearComp_bundle hP⟩
  let b₂ : TauCeti.Manifold.BilinearSection IB F V ℝ n :=
    ⟨fun x ↦ (g.inner x).bilinearComp (P x ∘L (Complex.smulIEquiv (V x) : V x →L[ℝ] V x))
      (P x ∘L (Complex.smulIEquiv (V x) : V x →L[ℝ] V x)),
      g.contMDiff.bilinearComp_bundle hPJ⟩
  have hJ := lsmul_I_comp_lsmul_I
  ofPositiveDefiniteSection (b₁ + b₂) <| by
    refine (TauCeti.Manifold.mem_positiveDefiniteBilinearSections _).2
      ⟨(TauCeti.Manifold.mem_symmetricBilinearSections _).2 fun x v w ↦ ?_, fun x v hv ↦ ?_⟩
    · simp [b₁, b₂, g.symm x (P x v), g.symm x (P x (Complex.I • v))]
    · have h := (hL x).compatibleForm_pos (hJ (V x)) (g := (g.inner x).toLinearMap₁₂)
        (fun a _ ha ↦ g.pos x a ha) hv
      simpa [b₁, b₂, P, Complex.smulIEquiv_apply] using h

variable (g : ContMDiffRiemannianMetric IB n F V)
  (hLs : HasLocalContMDiffSubbundleFrames IB n F ι L)
  (hL : ∀ x, IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x))

/-- Evaluation of the compatible metric. -/
@[simp]
theorem totallyRealCompatible_inner (x : B) (v w : V x) :
    (g.totallyRealCompatible hLs hL).inner x v w =
      g.inner x ((L x).projection _ (hL x).isCompl v) ((L x).projection _ (hL x).isCompl w) +
        g.inner x ((L x).projection _ (hL x).isCompl (Complex.I • v))
          ((L x).projection _ (hL x).isCompl (Complex.I • w)) := by
  simp [totallyRealCompatible]

/-- The compatible metric is the pointwise compatible form of `g`. -/
theorem toLinearMap₁₂_totallyRealCompatible_inner (x : B) :
    ((g.totallyRealCompatible hLs hL).inner x).toLinearMap₁₂ =
      (hL x).compatibleForm (g.inner x).toLinearMap₁₂ := by
  ext v w
  simp

/-- The compatible metric is invariant under multiplication by `i`, so it is the real part of a
Hermitian metric (`Bundle.ContMDiffRiemannianMetric.complexInnerProductSpace`). -/
theorem totallyRealCompatible_inner_smul_I (x : B) (v w : V x) :
    (g.totallyRealCompatible hLs hL).inner x (Complex.I • v) (Complex.I • w) =
      (g.totallyRealCompatible hLs hL).inner x v w := by
  have h := (hL x).compatibleForm_map_map (lsmul_I_comp_lsmul_I (V x))
    (g.inner x).toLinearMap₁₂ v w
  simpa using h

/-- The compatible metric agrees with `g` on `L`. -/
theorem totallyRealCompatible_inner_of_mem {x : B} {a b : V x} (ha : a ∈ L x) (hb : b ∈ L x) :
    (g.totallyRealCompatible hLs hL).inner x a b = g.inner x a b := by
  have h := (hL x).compatibleForm_apply_of_mem_of_mem (g.inner x).toLinearMap₁₂ ha hb
  simpa using h

/-- **`i L = L^⊥`.** For the compatible metric, the `i`-image of each fibre of `L` is the
orthogonal complement of that fibre. -/
theorem orthogonal_totallyRealCompatible (x : B) :
    LinearMap.BilinForm.orthogonal ((g.totallyRealCompatible hLs hL).inner x).toLinearMap₁₂ (L x) =
      (L x).map ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) := by
  rw [toLinearMap₁₂_totallyRealCompatible_inner]
  exact (hL x).orthogonal_compatibleForm fun a _ ha ↦ g.pos x a ha

/-- **Uniqueness of the compatible metric.** A metric invariant under multiplication by `i`,
agreeing with `g` on `L`, and making `L` orthogonal to `i L` is the compatible metric of `g`. -/
theorem eq_totallyRealCompatible {g' : ContMDiffRiemannianMetric IB n F V}
    (hI : ∀ x (v w : V x), g'.inner x (Complex.I • v) (Complex.I • w) = g'.inner x v w)
    (hLg : ∀ x, ∀ a ∈ L x, ∀ b ∈ L x, g'.inner x a b = g.inner x a b)
    (hLI : ∀ x, ∀ a ∈ L x, ∀ b ∈ L x, g'.inner x a (Complex.I • b) = 0) :
    g' = g.totallyRealCompatible hLs hL := by
  ext x v w
  have h := (hL x).eq_compatibleForm (lsmul_I_comp_lsmul_I (V x))
    (g := (g.inner x).toLinearMap₁₂) (h := (g'.inner x).toLinearMap₁₂)
    (fun v w ↦ by simpa using hI x v w) (fun a ha b hb ↦ by simpa using hLg x a ha b hb)
    (fun a ha b hb ↦ by simpa using hLI x a ha b hb)
  rw [← toLinearMap₁₂_totallyRealCompatible_inner g hLs hL] at h
  exact LinearMap.congr_fun₂ h v w

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B] [T2Space B] [SigmaCompactSpace B]
  [IsManifold IB ∞ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {ι : Type*} [Finite ι] {L : ∀ x, Submodule ℝ (V x)}

local instance instVectorBundleRealTotallyRealMetric : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

/-- **Existence of metrics compatible with a totally real subbundle.** Let `L` be a `C^n` real
subbundle of a finite-rank `C^n` complex bundle over a σ-compact Hausdorff manifold, whose fibres
are maximal totally real. There is a `C^n` metric invariant under multiplication by `i`, hence
the real part of a Hermitian metric, for which `i (L x)` is the orthogonal complement of `L x`
at every point. -/
theorem exists_contMDiffRiemannianMetric_compatible_totallyReal {n : ℕ∞}
    [ContMDiffVectorBundle n F V IB] (hLs : HasLocalContMDiffSubbundleFrames IB n F ι L)
    (hL : ∀ x, IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x)) :
    ∃ g : ContMDiffRiemannianMetric IB n F V,
      (∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) ∧
      ∀ x, LinearMap.BilinForm.orthogonal (g.inner x).toLinearMap₁₂ (L x) =
        (L x).map ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) := by
  let : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  let : ∀ x, ContinuousConstSMul ℝ (V x) := fun x ↦ inferInstance
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := IB) (n := n) (F := F) (E := V)
  exact ⟨g.totallyRealCompatible hLs hL, g.totallyRealCompatible_inner_smul_I hLs hL,
    g.orthogonal_totallyRealCompatible hLs hL⟩

/-- **Metrics compatible with a totally real subbundle along a closed set.** Let `S` be a closed
subset of a σ-compact Hausdorff manifold, possibly with boundary or corners, for instance its
boundary, and let `L` be a family of real subspaces of the fibres of a finite-rank `C^n` complex
bundle which near every point of `S` has a `C^n` local frame and whose fibres over `S` are maximal
totally real. There is a `C^n` metric invariant under multiplication by `i`, hence the real part
of a Hermitian metric, for which `i (L x)` is the orthogonal complement of `L x` at every point of
`S`. -/
theorem exists_contMDiffRiemannianMetric_compatible_totallyReal_on {n : ℕ∞}
    [ContMDiffVectorBundle n F V IB] {S : Set B} (hS : IsClosed S)
    (hLs : ∀ x ∈ S, ∃ U : Set B, IsOpen U ∧ x ∈ U ∧
      ∃ X : ι → Π x, V x, IsSubbundleFrameOn F L X U ∧ ∀ i, CMDiff[U] n (T% (X i)))
    (hL : ∀ x ∈ S,
      IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x)) :
    ∃ g : ContMDiffRiemannianMetric IB n F V,
      (∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) ∧
      ∀ x ∈ S, LinearMap.BilinForm.orthogonal (g.inner x).toLinearMap₁₂ (L x) =
        (L x).map ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) := by
  let : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  let : ∀ x, ContinuousConstSMul ℝ (V x) := fun x ↦ inferInstance
  let : ∀ x, IsNormableSpace ℝ (V x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt ℝ F V x).isNormableSpace
  have : ∀ b, ContinuousAdd (V b →L[ℝ] ℝ) := fun b ↦ inferInstance
  let : ∀ b, AddCommGroup (V b →L[ℝ] V b →L[ℝ] ℝ) := fun b ↦ inferInstance
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := IB) (n := n) (F := F) (E := V)
  -- Near a point of `S` the fibres of `L` stay maximal totally real, and the compatible form of
  -- `g` is a local solution; away from `S` the Hermitian average of `g` is one. The conditions
  -- below are convex at each point, so a smooth partition of unity glues the local solutions.
  -- The fibrewise conditions: a positive definite symmetric form, invariant under `i`, and over
  -- `S` making `L` orthogonal to `i L`. Each is convex.
  let t (b : B) : Set (V b →L[ℝ] V b →L[ℝ] ℝ) := {s | (∀ v w, s v w = s w v) ∧
    (∀ v, v ≠ 0 → 0 < s v v) ∧ (∀ v w, s (Complex.I • v) (Complex.I • w) = s v w) ∧
    (b ∈ S → ∀ a ∈ L b, ∀ c ∈ L b, s a (Complex.I • c) = 0)}
  have ht (b : B) : Convex ℝ (t b) := by
    rintro s ⟨hs₁, hs₂, hs₃, hs₄⟩ s' ⟨hs₁', hs₂', hs₃', hs₄'⟩ a d ha hd had
    obtain ⟨h₁, h₂⟩ := convex_setOfPred_symm_pos ⟨hs₁, hs₂⟩ ⟨hs₁', hs₂'⟩ ha hd had
    exact ⟨h₁, h₂, fun v w ↦ by simp [hs₃ v w, hs₃' v w],
      fun hb x hx y hy ↦ by simp [hs₄ hb x hx y hy, hs₄' hb x hx y hy]⟩
  obtain ⟨σ, hσ⟩ := exists_contMDiffSection_forall_mem_convex_of_local (n := n) IB
    (fun b ↦ V b →L[ℝ] V b →L[ℝ] ℝ) t ht fun x₀ ↦ by
      by_cases hx₀ : x₀ ∈ S
      · -- Near a point of `S`: the compatible form of `g`.
        obtain ⟨U, hU, hx₀U, X, hX, hXs⟩ := hLs x₀ hx₀
        let W := U ∩ interior {y | IsMaximalTotallyReal
          ((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ) (L y)}
        have hW : IsOpen W := hU.inter isOpen_interior
        have hx₀W : x₀ ∈ W := ⟨hx₀U, mem_interior_iff_mem_nhds.2
          (eventually_isMaximalTotallyReal hU hX hx₀U (hL x₀ hx₀))⟩
        have hLW (y : B) (hy : y ∈ W) :
            IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ) (L y) :=
          interior_subset hy.2
        classical
        let P (y : B) : V y →L[ℝ] V y := if h : IsMaximalTotallyReal
          ((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ) (L y) then
            totallyRealProjection F h else 0
        have hP (y : B) (hy : y ∈ W) : P y = totallyRealProjection F (hLW y hy) := by
          dsimp only [P]
          split_ifs with h
          · rfl
          · exact absurd (hLW y hy) h
        let J (y : B) : V y →L[ℝ] V y := (Complex.smulIEquiv (V y) : V y →L[ℝ] V y)
        let s (y : B) : V y →L[ℝ] V y →L[ℝ] ℝ :=
          (g.inner y).bilinearComp (P y) (P y) +
            (g.inner y).bilinearComp (P y ∘L J y) (P y ∘L J y)
        have hs (y : B) (hy : y ∈ W) (v w : V y) :
            s y v w = (hLW y hy).compatibleForm (g.inner y).toLinearMap₁₂ v w := by
          simp [s, hP y hy, J, Complex.smulIEquiv_apply]
        refine ⟨W, hW.mem_nhds hx₀W, s, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
        · have hPy := contMDiffAt_totallyRealProjection hW (hX.mono inter_subset_left)
            (fun i ↦ (hXs i).mono inter_subset_left) hLW hP hy
          have hPJy := hPy.clm_bundle_comp
            (contMDiff_smulIEquiv_bundle (IB := IB) (n := n) (G := F) (W := V) y)
          exact (((g.contMDiff y).bilinearComp_bundle hPy).add_section
            ((g.contMDiff y).bilinearComp_bundle hPJy)).contMDiffWithinAt
        · have hJ := lsmul_I_comp_lsmul_I (E := V y)
          refine ⟨fun v w ↦ ?_, fun v hv ↦ ?_, fun v w ↦ ?_, fun _ a ha c hc ↦ ?_⟩
          · rw [hs y hy, hs y hy]
            exact ((hLW y hy).isSymm_compatibleForm
              fun a _ b _ ↦ by simpa using g.symm y a b).eq v w
          · rw [hs y hy]
            exact (hLW y hy).compatibleForm_pos hJ (fun a _ ha ↦ by simpa using g.pos y a ha) hv
          · rw [hs y hy, hs y hy]
            simpa using (hLW y hy).compatibleForm_map_map hJ (g.inner y).toLinearMap₁₂ v w
          · rw [hs y hy]
            simpa using (hLW y hy).compatibleForm_apply_map (g.inner y).toLinearMap₁₂ ha hc
      · -- Away from `S`: the Hermitian average of `g`.
        refine ⟨Sᶜ, hS.isOpen_compl.mem_nhds hx₀, g.hermitianAverage.inner,
          g.hermitianAverage.contMDiff.contMDiffOn, fun y hy ↦ ⟨g.hermitianAverage.symm y,
            g.hermitianAverage.pos y, g.hermitianAverage_inner_smul_I y,
            fun hyS ↦ absurd hyS hy⟩⟩
  let G : ContMDiffRiemannianMetric IB n F V :=
    ContMDiffRiemannianMetric.ofPositiveDefiniteSection ⟨σ, σ.contMDiff⟩
      ((TauCeti.Manifold.mem_positiveDefiniteBilinearSections _).2
        ⟨(TauCeti.Manifold.mem_symmetricBilinearSections _).2 fun x v w ↦ (hσ x).1 v w,
          fun x v hv ↦ (hσ x).2.1 v hv⟩)
  have hGσ (x : B) (v w : V x) : G.inner x v w = σ x v w :=
    ContMDiffRiemannianMetric.ofPositiveDefiniteSection_inner _ _ x v w
  refine ⟨G, fun x v w ↦ by rw [hGσ, hGσ]; exact (hσ x).2.2.1 v w, fun x hx ↦ ?_⟩
  -- At a point of `S` the metric is its own compatible form, so `i L` is `L^⊥`.
  have hJ := lsmul_I_comp_lsmul_I (E := V x)
  have hG : (G.inner x).toLinearMap₁₂ = (hL x hx).compatibleForm (G.inner x).toLinearMap₁₂ :=
    (hL x hx).eq_compatibleForm hJ (fun v w ↦ by simpa [hGσ] using (hσ x).2.2.1 v w)
      (fun _ _ _ _ ↦ rfl) fun a ha c hc ↦ by simpa [hGσ] using (hσ x).2.2.2 hx a ha c hc
  rw [hG]
  exact (hL x hx).orthogonal_compatibleForm fun a _ ha ↦ by simpa using G.pos x a ha

end TauCeti
