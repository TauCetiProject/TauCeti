/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Principal
public import TauCeti.Geometry.Manifold.Instances.Unitary
public import TauCeti.Geometry.Manifold.VectorBundle.Associated.Metric
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Associated
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Geometry.Manifold.FiberBundle.Principal.Equivariant
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity

/-!
# Smooth orthonormal frame principal bundles and associated-bundle reconstruction

Let `E → B` be a `C^n` Riemannian vector bundle with finite-dimensional model fibre `F` over a
manifold `B` modelled on `IB` (possibly with boundary or corners), and let `V` be a real inner
product space of the same dimension as `F`. In
`TauCeti.Topology.VectorBundle.OrthonormalFrame.Principal`, the orthonormal frames `V ≃ₗᵢ[ℝ] E b`
form a principal bundle `TauCeti.OrthonormalFrameBundle.Fiber ℝ F E V` with structure group the
orthogonal group `unitary (V →L[ℝ] V)`, whose native `C^∞` Lie-group atlas modelled on
`Unitary.model (V →L[ℝ] V)` is constructed in `TauCeti.Geometry.Manifold.Instances.Unitary`.

This file equips the orthonormal frame principal bundle with its `C^n` fibre-bundle structure
(for any `n : ℕ∞ω` with `[ENat.LEInfty n]`, excluding real-analytic regularity `ω` because the
native unitary atlas is `C^∞`), connects smooth maps into the frame bundle to smooth sections of
`E`, registers automatic `C^n` smoothness instances for associated bundles, upgrades the
topological associated-bundle reconstruction of `E` to a `C^n` diffeomorphism, and establishes
smooth naturality under Riemannian bundle isometries.

Note that `Fiber ℝ F E V` takes `[TauCeti.ContinuousFiberNorm F E]` for its topological bundle
structure. This class is inferred automatically from `[Bundle.IsContinuousRiemannianBundle F E]`;
when only `[IsContMDiffRiemannianBundle IB n F E]` is in scope, supply the continuous metric
instance via `IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle`.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.instContMDiffFiberBundle`: `Fiber ℝ F E V` is a `C^n` principal
  bundle (`ContMDiffFiberBundle n (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) IB
  (Unitary.model (V →L[ℝ] V))`).
* `TauCeti.OrthonormalFrameBundle.instContMDiffFiberBundleAssociatedBundle` and
  `TauCeti.OrthonormalFrameBundle.instContMDiffVectorBundleAssociatedBundle`: any `C^n` action
  (respectively finite-dimensional linear `C^n` action, real or complex viewed over `ℝ`) of
  `unitary (V →L[ℝ] V)` yields a `C^n` associated fibre or vector bundle over `B`.
* `TauCeti.OrthonormalFrameBundle.associatedBundleDiffeomorph`: canonical `C^n` diffeomorphism
  identifying `TotalSpace V (AssociatedBundle (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) V)` with
  `TotalSpace F E`, acting on each fibre by the linear isometry `associatedLinearIsometryEquiv`.
* `TauCeti.OrthonormalFrameBundle.manifoldTotalSpaceMapDiffeomorph`: `C^n` equivariant
  diffeomorphism between charted orthonormal frame bundles induced by a `C^n` Riemannian bundle
  isometry.

## Main results

* `Bundle.Trivialization.contMDiffOn_totalSpaceMk_orthonormalFrameAt`,
  `Bundle.Trivialization.contMDiffOn_orthonormalFrameAt_symm`, and
  `Bundle.Trivialization.contMDiffOn_orthonormalFrameAt`: `C^n` regularity of the local
  Gram–Schmidt orthonormal frame of a compatible trivialization and of its coordinate map.
* `TauCeti.OrthonormalFrameBundle.contMDiffWithinAt_totalSpace_iff` (and `At`, `On`, global
  variants): universal smoothness property of the charted orthonormal frame bundle — a map into
  `ManifoldTotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)` is `C^n` if and only if applying the
  frame to each fixed vector `v : V` gives a `C^n` map into `TotalSpace F E`.
* `ContMDiffWithinAt.totalSpaceMk_frame_apply` and `ContMDiffWithinAt.frame_symm_apply` (and `At`,
  `On`, global variants): joint `C^n` smoothness of evaluating frames on vectors and reading
  vectors in frames.
* `TauCeti.contMDiff_totalSpaceMk_apply_iff_orthonormalFrame`: a family of continuous linear
  endomorphisms of `E` is `C^n` on `TotalSpace F E` if and only if its matrix representations in
  local Gram–Schmidt orthonormal frames are `C^n`.
* `TauCeti.OrthonormalFrameBundle.contMDiff_fiberwiseMap_map` and
  `TauCeti.OrthonormalFrameBundle.contMDiff_fiberwiseMap_map_iff`: the induced map on charted
  orthonormal frame bundles is `C^n` if and only if the underlying bundle isometry is `C^n` on
  vector-bundle total spaces.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, volume I, Interscience (1963),
  Chapter I, §5.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §10.7.
* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer (1994),
  Chapter 4, §5 and Chapter 5, §§4–5.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §2.
-/

public noncomputable section

open Bundle Filter MulOpposite Set TauCeti TauCeti.OrthonormalFrameBundle
open scoped Manifold Topology ContDiff InnerProductSpace

/-! ### Smoothness of Gram–Schmidt local frames and operator representations -/

section LocalFrame

variable {n : ℕ∞ω}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle n F E IB] [IsContMDiffRiemannianBundle IB n F E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace Bundle.Trivialization

variable (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  (c : Module.Basis ι ℝ F) (b : OrthonormalBasis ι ℝ V)

open scoped Classical in
/-- Over the base set of a compatible trivialization `e`, applying the local Gram–Schmidt
orthonormal frame `e.orthonormalFrameAt c b` to a fixed vector `v : V` gives a `C^n` local section.
This is the smooth counterpart of
`Bundle.Trivialization.continuousOn_totalSpaceMk_orthonormalFrameAt`, and holds for every
regularity `n : ℕ∞ω` (including `ω`). -/
theorem contMDiffOn_totalSpaceMk_orthonormalFrameAt (v : V) :
    ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F y (e.orthonormalFrameAt c b y v)) e.baseSet := by
  let s : ι → ∀ y : B, E y := fun i y ↦
    ⟪b i, v⟫_ℝ • (if hy : y ∈ e.baseSet then e.orthonormalBasis c ⟨y, hy⟩ i else 0)
  have hs (i : ι) :
      ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (fun y ↦ TotalSpace.mk' F y (s i y)) e.baseSet :=
    (contMDiffOn_const (c := ⟪b i, v⟫_ℝ)).smul_totalSpace (e.contMDiffOn_orthonormalBasis c i)
  refine (ContMDiffOn.sum_sectionAlong Finset.univ s contMDiffOn_id
    fun i _ ↦ hs i).congr fun y hy ↦ ?_
  apply congrArg (TotalSpace.mk' F y)
  rw [e.orthonormalFrameAt_of_mem c b hy, e.orthonormalFrame_apply c b ⟨y, hy⟩ v]
  exact Finset.sum_congr rfl fun i _ ↦ by simp only [s, dite_eq_left_of_eq_true (eq_true hy)]

open scoped Classical in
/-- Over `TotalSpace.proj ⁻¹' e.baseSet`, reading a vector of `TotalSpace F E` in the local
Gram–Schmidt orthonormal frame `e.orthonormalFrameAt c b` is `C^n` into `V`. This is the smooth
counterpart of `Bundle.Trivialization.continuousOn_orthonormalFrameAt_symm`, and holds for every
regularity `n : ℕ∞ω` (including `ω`). -/
theorem contMDiffOn_orthonormalFrameAt_symm :
    ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) n
      (fun x : TotalSpace F E ↦ (e.orthonormalFrameAt c b x.proj).symm x.snd)
      (TotalSpace.proj ⁻¹' e.baseSet) := by
  let U : Set (TotalSpace F E) := TotalSpace.proj ⁻¹' e.baseSet
  have hσ (i : ι) : ContMDiffOn (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) n
      (fun x : TotalSpace F E ↦ TotalSpace.mk' F x.proj
        (if hy : x.proj ∈ e.baseSet then e.orthonormalBasis c ⟨x.proj, hy⟩ i else 0)) U :=
    (e.contMDiffOn_orthonormalBasis c i).comp (Bundle.contMDiff_proj E).contMDiffOn fun _ hx ↦ hx
  have hsum : ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) n
      (fun x : TotalSpace F E ↦ ∑ i, ⟪(if hy : x.proj ∈ e.baseSet then
        e.orthonormalBasis c ⟨x.proj, hy⟩ i else 0), x.snd⟫_ℝ • b i) U := fun x hx ↦
    ContMDiffWithinAt.sum (t := Finset.univ) fun i _ ↦
      (((hσ i x hx).inner_bundle (contMDiffOn_id x hx)).smul
        (contMDiffWithinAt_const (c := b i)))
  refine hsum.congr fun x hx ↦ ?_
  have hx' : x.proj ∈ e.baseSet := hx
  rw [e.orthonormalFrameAt_of_mem c b hx', e.orthonormalFrame_symm_apply c b ⟨x.proj, hx'⟩ x.snd]
  exact Finset.sum_congr rfl fun i _ ↦ by simp only [dite_eq_left_of_eq_true (eq_true hx')]

end Bundle.Trivialization

/-- A family of continuous linear endomorphisms `A b : E b →L[ℝ] E b` acts `C^n`-smoothly on
`TotalSpace F E` if and only if, over the base set of every trivialization in the atlas of `E`, its
conjugation by the local Gram–Schmidt orthonormal frame is `C^n`. This refines
`TauCeti.continuous_totalSpaceMk_apply_of_orthonormalFrame` into a smooth equivalence and holds for
all `n : ℕ∞ω`. -/
theorem TauCeti.contMDiff_totalSpaceMk_apply_iff_orthonormalFrame [FiniteDimensional ℝ F]
    {A : ∀ b, E b →L[ℝ] E b} :
    ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) n
        (fun p : TotalSpace F E ↦ (⟨p.proj, A p.proj p.snd⟩ : TotalSpace F E)) ↔
      ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
        (d : ℕ) (c : Module.Basis (Fin d) ℝ F),
        ContMDiffOn IB
          𝓘(ℝ, EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) n
          (fun y ↦
            ((e.orthonormalFrameAt c (EuclideanSpace.basisFun (Fin d) ℝ) y).symm :
              E y →L[ℝ] EuclideanSpace ℝ (Fin d)) ∘L A y ∘L
            (e.orthonormalFrameAt c (EuclideanSpace.basisFun (Fin d) ℝ) y :
              EuclideanSpace ℝ (Fin d) →L[ℝ] E y))
          e.baseSet := by
  refine ⟨fun hA e _ d c y hy ↦ ?_, fun hA p₀ ↦ ?_⟩
  · refine TauCeti.contMDiffWithinAt_clm_apply.2 fun v ↦ ?_
    let b := EuclideanSpace.basisFun (Fin d) ℝ
    have hv := hA.comp_contMDiffOn (e.contMDiffOn_totalSpaceMk_orthonormalFrameAt c b v)
    exact ((e.contMDiffOn_orthonormalFrameAt_symm c b).comp hv fun _ hx ↦ hx) y hy
  · let e := trivializationAt F E p₀.proj
    have hp₀ : p₀.proj ∈ e.baseSet := mem_baseSet_trivializationAt F E p₀.proj
    let d := Module.finrank ℝ F
    let c := Module.finBasis ℝ F
    let b := EuclideanSpace.basisFun (Fin d) ℝ
    let σ := e.orthonormalFrameAt c b
    let U : Set (TotalSpace F E) := TotalSpace.proj ⁻¹' e.baseSet
    have hU : U ∈ 𝓝 p₀ :=
      (e.open_baseSet.preimage (FiberBundle.continuous_proj F E)).mem_nhds hp₀
    have hproj : ContMDiffOn (IB.prod 𝓘(ℝ, F)) IB n (TotalSpace.proj : TotalSpace F E → B) U :=
      (Bundle.contMDiff_proj E).contMDiffOn
    have hu : ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) n
        (fun p : TotalSpace F E ↦
          (((σ p.proj).symm : E p.proj →L[ℝ] EuclideanSpace ℝ (Fin d)) ∘L A p.proj ∘L
            (σ p.proj : EuclideanSpace ℝ (Fin d) →L[ℝ] E p.proj)) ((σ p.proj).symm p.snd)) U :=
      ((hA e d c).comp hproj fun _ hp ↦ hp).clm_apply (e.contMDiffOn_orthonormalFrameAt_symm c b)
    let s : Fin d → ∀ p : TotalSpace F E, E p.proj := fun i p ↦
      ⟪b i, (((σ p.proj).symm : E p.proj →L[ℝ] EuclideanSpace ℝ (Fin d)) ∘L A p.proj ∘L
        (σ p.proj : EuclideanSpace ℝ (Fin d) →L[ℝ] E p.proj)) ((σ p.proj).symm p.snd)⟫_ℝ •
        σ p.proj (b i)
    have hs (i : Fin d) : ContMDiffOn (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) n
        (fun p : TotalSpace F E ↦ TotalSpace.mk' F p.proj (s i p)) U := by
      have hc : ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) n
          (fun p : TotalSpace F E ↦ ⟪b i, _⟫_ℝ) U :=
        (innerSL ℝ (b i)).contDiff.contMDiff.comp_contMDiffOn hu
      exact hc.smul_totalSpace
        ((e.contMDiffOn_totalSpaceMk_orthonormalFrameAt c b (b i)).comp hproj fun _ hp ↦ hp)
    refine ((ContMDiffOn.sum_sectionAlong Finset.univ s hproj
      fun i _ ↦ hs i).congr fun p _ ↦ ?_).contMDiffAt hU
    apply congrArg (TotalSpace.mk' F p.proj)
    have hsum : ∑ i : Fin d, s i p = σ p.proj
        ((((σ p.proj).symm : E p.proj →L[ℝ] EuclideanSpace ℝ (Fin d)) ∘L A p.proj ∘L
          (σ p.proj : EuclideanSpace ℝ (Fin d) →L[ℝ] E p.proj)) ((σ p.proj).symm p.snd)) := by
      simp only [s, ← _root_.map_smul, ← map_sum, b.sum_repr']
    rw [hsum]
    simp

end LocalFrame

/-! ### Universal smoothness property and smooth principal bundle structure -/

section PrincipalBundle

variable {n : ℕ∞ω} [ENat.LEInfty n]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle n F E IB] [IsContMDiffRiemannianBundle IB n F E]
  [ContinuousFiberNorm F E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [hV : Fact (Module.finrank ℝ V = Module.finrank ℝ F)]

namespace TauCeti.OrthonormalFrameBundle

/-- **Universal smoothness property of the orthonormal frame bundle** (within a set at a point): a
map `f` into `TotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)`, charted through the fibre via
`ManifoldTotalSpace`, is `C^n` within `s` at `x₀` if and only if applying `(f x).2.frame` to each
fixed model vector `v : V` yields a `C^n` map into `TotalSpace F E`. -/
theorem contMDiffWithinAt_totalSpace_iff
    {f : M → TotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)} {s : Set M} {x₀ : M} :
    ContMDiffWithinAt IM (IB.prod (Unitary.model (V →L[ℝ] V))) n
        (fun x ↦ ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) (f x))
        s x₀ ↔
      ∀ v : V, ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
        (fun x ↦ (⟨(f x).proj, (f x).snd.frame v⟩ : TotalSpace F E)) s x₀ := by
  rw [ManifoldTotalSpace.contMDiffWithinAt_iff, Unitary.contMDiffWithinAt_iff,
    TauCeti.contMDiffWithinAt_clm_apply]
  let b₀ := (f x₀).proj
  let e₀ := trivializationAt F E b₀
  have hb₀ : b₀ ∈ e₀.baseSet := mem_baseSet_trivializationAt F E b₀
  let c₀ := Module.finBasisOfFinrankEq ℝ F hV.out.symm
  let b_mod := stdOrthonormalBasis ℝ V
  let σ := e₀.orthonormalFrameAt c₀ b_mod
  refine ⟨fun ⟨hf, hu⟩ v ↦ ?_, fun h ↦ ?_⟩
  · -- (⇒) Expand `(f x).2.frame v` in the local Gram–Schmidt basis via its trivialization coords.
    have hmem : (fun x ↦ (f x).proj) ⁻¹' e₀.baseSet ∈ 𝓝[s] x₀ :=
      hf.continuousWithinAt (e₀.open_baseSet.mem_nhds hb₀)
    let g : Fin (Module.finrank ℝ V) → ∀ x : M, E (f x).proj := fun i x ↦
      ⟪b_mod i, ((trivializationAt (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) b₀ (f x)).2 :
        V →L[ℝ] V) v⟫_ℝ • σ (f x).proj (b_mod i)
    have hg (i : Fin (Module.finrank ℝ V)) :
        ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
          (fun x ↦ TotalSpace.mk' F (f x).proj (g i x)) s x₀ :=
      (((innerSL ℝ (b_mod i)).contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt x₀
        (hu v)).smul_totalSpace
        (((e₀.contMDiffOn_totalSpaceMk_orthonormalFrameAt c₀ b_mod (b_mod i)).contMDiffAt
          (e₀.open_baseSet.mem_nhds hb₀)).comp_contMDiffWithinAt x₀ hf))
    have hsum_eq {x : M} (hx : (f x).proj ∈ e₀.baseSet) :
        TotalSpace.mk' F (f x).proj (∑ i, g i x) = ⟨(f x).proj, (f x).snd.frame v⟩ := by
      apply congrArg (TotalSpace.mk' F (f x).proj)
      have h1 : ∑ i, g i x = σ (f x).proj
          (((trivializationAt (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) b₀ (f x)).2 :
            V →L[ℝ] V) v) := by
        simp only [g, ← _root_.map_smul, ← map_sum, b_mod.sum_repr']
      rw [h1, trivializationAt_fiber_snd_apply hx v, LinearIsometryEquiv.apply_symm_apply]
    exact (ContMDiffWithinAt.sum_sectionAlong Finset.univ g hf fun i _ ↦ hg i).congr_of_eventuallyEq
      (eventually_of_mem hmem fun x hx ↦ (hsum_eq hx).symm) (hsum_eq hb₀).symm
  · -- (⇐) Read each vector `(f x).2.frame v` in the local Gram–Schmidt frame `σ`.
    have hf : ContMDiffWithinAt IM IB n (fun x ↦ (f x).proj) s x₀ :=
      (Bundle.contMDiffWithinAt_totalSpace_iff.1 (h 0)).1
    refine ⟨hf, fun v ↦ ?_⟩
    have hmem : (fun x ↦ (f x).proj) ⁻¹' e₀.baseSet ∈ 𝓝[s] x₀ :=
      hf.continuousWithinAt (e₀.open_baseSet.mem_nhds hb₀)
    exact (((e₀.contMDiffOn_orthonormalFrameAt_symm c₀ b_mod).contMDiffAt
      ((e₀.open_baseSet.preimage (FiberBundle.continuous_proj F E)).mem_nhds
        hb₀)).comp_contMDiffWithinAt x₀ (h v)).congr_of_eventuallyEq
      (eventually_of_mem hmem fun x hx ↦ trivializationAt_fiber_snd_apply hx v)
      (trivializationAt_fiber_snd_apply hb₀ v)

/-- Universal smoothness property of the orthonormal frame bundle at a point. -/
theorem contMDiffAt_totalSpace_iff
    {f : M → TotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)} {x₀ : M} :
    ContMDiffAt IM (IB.prod (Unitary.model (V →L[ℝ] V))) n
        (fun x ↦ ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) (f x)) x₀ ↔
      ∀ v : V, ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n
        (fun x ↦ (⟨(f x).proj, (f x).snd.frame v⟩ : TotalSpace F E)) x₀ := by
  simp_rw [← contMDiffWithinAt_univ]
  exact contMDiffWithinAt_totalSpace_iff

/-- Universal smoothness property of the orthonormal frame bundle on a set. -/
theorem contMDiffOn_totalSpace_iff
    {f : M → TotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)} {s : Set M} :
    ContMDiffOn IM (IB.prod (Unitary.model (V →L[ℝ] V))) n
        (fun x ↦ ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) (f x)) s ↔
      ∀ v : V, ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n
        (fun x ↦ (⟨(f x).proj, (f x).snd.frame v⟩ : TotalSpace F E)) s :=
  ⟨fun h v x hx ↦ contMDiffWithinAt_totalSpace_iff.1 (h x hx) v,
    fun h x hx ↦ contMDiffWithinAt_totalSpace_iff.2 fun v ↦ h v x hx⟩

/-- Universal smoothness property of the orthonormal frame bundle for global `C^n` maps. -/
theorem contMDiff_totalSpace_iff
    {f : M → TotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)} :
    ContMDiff IM (IB.prod (Unitary.model (V →L[ℝ] V))) n
        (fun x ↦ ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) (f x)) ↔
      ∀ v : V, ContMDiff IM (IB.prod 𝓘(ℝ, F)) n
        (fun x ↦ (⟨(f x).proj, (f x).snd.frame v⟩ : TotalSpace F E)) :=
  ⟨fun h v x ↦ contMDiffAt_totalSpace_iff.1 (h x) v,
    fun h x ↦ contMDiffAt_totalSpace_iff.2 fun v ↦ h v x⟩

end TauCeti.OrthonormalFrameBundle

/-- Over the base set of a compatible trivialization `e`, the local Gram–Schmidt orthonormal frame
`e.orthonormalFrameAt c b` is a `C^n` local section of the charted orthonormal frame bundle
`ManifoldTotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)`. -/
theorem Bundle.Trivialization.contMDiffOn_orthonormalFrameAt
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
    (c : Module.Basis ι ℝ F) (b : OrthonormalBasis ι ℝ V) :
    ContMDiffOn IB (IB.prod (Unitary.model (V →L[ℝ] V))) n
      (fun y ↦ ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)
        ⟨y, .ofFrame (e.orthonormalFrameAt c b y)⟩) e.baseSet :=
  OrthonormalFrameBundle.contMDiffOn_totalSpace_iff.2 fun v ↦
    e.contMDiffOn_totalSpaceMk_orthonormalFrameAt c b v

namespace TauCeti.OrthonormalFrameBundle

/-- **The orthonormal frame bundle of a `C^n` Riemannian vector bundle is a `C^n` principal
bundle.** Its transition functions between Gram–Schmidt trivializations are divisions of `C^n`
local Gram–Schmidt frames in `ManifoldTotalSpace`. -/
instance instContMDiffFiberBundle :
    ContMDiffFiberBundle n (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)
      IB (Unitary.model (V →L[ℝ] V)) := by
  rw [PrincipalBundle.contMDiffFiberBundle_iff]
  intro t t' ht ht'
  obtain ⟨e, _, c, b, rfl⟩ := ht.out
  obtain ⟨e', _, c', b', rfl⟩ := ht'.out
  simp only [Trivialization.baseSet_orthonormalFrameBundleFiber,
    Trivialization.baseSet_orthonormalFrameBundle]
  let σ : ∀ y : B, Fiber ℝ F E V y := fun y ↦ .ofFrame (e.orthonormalFrameAt c b y)
  let σ' : ∀ y : B, Fiber ℝ F E V y := fun y ↦ .ofFrame (e'.orthonormalFrameAt c' b' y)
  have hdiv : ContMDiffOn IB (Unitary.model (V →L[ℝ] V)) n
      (fun y ↦ PrincipalBundle.division (unitary (V →L[ℝ] V)) (σ' y) (σ y))
      (e.baseSet ∩ e'.baseSet) :=
    ((e'.contMDiffOn_orthonormalFrameAt c' b').mono inter_subset_right).division
      ((e.contMDiffOn_orthonormalFrameAt c b).mono inter_subset_left)
  refine hdiv.congr fun y hy ↦ ?_
  have ht₁ : ((e.orthonormalFrameBundle c b).orthonormalFrameBundleFiber ⟨y, σ y⟩).2 = 1 := by
    rw [Trivialization.orthonormalFrameBundleFiber_apply, totalSpaceEquiv_apply]
    simp only [σ, e.orthonormalFrameAt_of_mem c b hy.1]
    exact congrArg Prod.snd (e.orthonormalFrameBundle_apply_orthonormalFrame c b ⟨y, hy.1⟩)
  have ht₂ : ((e'.orthonormalFrameBundle c' b').orthonormalFrameBundleFiber ⟨y, σ' y⟩).2 = 1 := by
    rw [Trivialization.orthonormalFrameBundleFiber_apply, totalSpaceEquiv_apply]
    simp only [σ', e'.orthonormalFrameAt_of_mem c' b' hy.2]
    exact congrArg Prod.snd (e'.orthonormalFrameBundle_apply_orthonormalFrame c' b' ⟨y, hy.2⟩)
  have hhy₁ : y ∈ (e.orthonormalFrameBundle c b).orthonormalFrameBundleFiber.baseSet := by
    simpa using hy.1
  have hhy₂ : y ∈ (e'.orthonormalFrameBundle c' b').orthonormalFrameBundleFiber.baseSet := by
    simpa using hy.2
  have hcoord := ((e.orthonormalFrameBundle c b).orthonormalFrameBundleFiber).coordChange_apply_snd
    (e'.orthonormalFrameBundle c' b').orthonormalFrameBundleFiber (p := ⟨y, σ y⟩) hhy₁
  rw [ht₁] at hcoord
  rw [hcoord, PrincipalBundle.division_eq_of_mem_baseSet
    (e := (e'.orthonormalFrameBundle c' b').orthonormalFrameBundleFiber) hhy₂, ht₂, inv_one,
    one_mul]

end TauCeti.OrthonormalFrameBundle

/-! ### Joint smoothness of frame evaluation and frame coordinates -/

section Evaluation

variable {p : M → TotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)}
  {v : M → V} {w : ∀ x, E (p x).proj} {s : Set M} {x₀ : M}

/-- Applying a `C^n` family of orthonormal frames to a `C^n` family of vectors in `V` yields a `C^n`
map into `TotalSpace F E` (within a set at a point). -/
theorem ContMDiffWithinAt.totalSpaceMk_frame_apply
    (hp : ContMDiffWithinAt IM (IB.prod (Unitary.model (V →L[ℝ] V))) n
      (fun x ↦ ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) (p x)) s x₀)
    (hv : ContMDiffWithinAt IM 𝓘(ℝ, V) n v s x₀) :
    ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun x ↦ (⟨(p x).proj, (p x).snd.frame (v x)⟩ : TotalSpace F E)) s x₀ := by
  let b_mod := stdOrthonormalBasis ℝ V
  have hproj : ContMDiffWithinAt IM IB n (fun x ↦ (p x).proj) s x₀ :=
    (ManifoldTotalSpace.contMDiffWithinAt_iff.1 hp).1
  let g : Fin (Module.finrank ℝ V) → ∀ x : M, E (p x).proj := fun i x ↦
    ⟪b_mod i, v x⟫_ℝ • (p x).snd.frame (b_mod i)
  have hg (i : Fin (Module.finrank ℝ V)) :
      ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
        (fun x ↦ TotalSpace.mk' F (p x).proj (g i x)) s x₀ :=
    ((innerSL ℝ (b_mod i)).contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt x₀
      hv).smul_totalSpace (OrthonormalFrameBundle.contMDiffWithinAt_totalSpace_iff.1 hp (b_mod i))
  have hsum_eq (x : M) :
      (⟨(p x).proj, (p x).snd.frame (v x)⟩ : TotalSpace F E) =
        TotalSpace.mk' F (p x).proj (∑ i, g i x) := by
    apply congrArg (TotalSpace.mk' F (p x).proj)
    symm
    simp only [g, ← _root_.map_smul, ← map_sum, b_mod.sum_repr']
  exact (ContMDiffWithinAt.sum_sectionAlong Finset.univ g hproj fun i _ ↦ hg i).congr
    (fun x _ ↦ hsum_eq x) (hsum_eq x₀)

/-- Applying a `C^n` family of orthonormal frames to a `C^n` family of vectors in `V` is `C^n` at a
point. -/
theorem ContMDiffAt.totalSpaceMk_frame_apply
    (hp : ContMDiffAt IM (IB.prod (Unitary.model (V →L[ℝ] V))) n
      (fun x ↦ ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) (p x)) x₀)
    (hv : ContMDiffAt IM 𝓘(ℝ, V) n v x₀) :
    ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun x ↦ (⟨(p x).proj, (p x).snd.frame (v x)⟩ : TotalSpace F E)) x₀ :=
  ContMDiffWithinAt.totalSpaceMk_frame_apply hp hv

/-- Applying a `C^n` family of orthonormal frames to a `C^n` family of vectors in `V` is `C^n` on a
set. -/
theorem ContMDiffOn.totalSpaceMk_frame_apply
    (hp : ContMDiffOn IM (IB.prod (Unitary.model (V →L[ℝ] V))) n
      (fun x ↦ ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) (p x)) s)
    (hv : ContMDiffOn IM 𝓘(ℝ, V) n v s) :
    ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n
      (fun x ↦ (⟨(p x).proj, (p x).snd.frame (v x)⟩ : TotalSpace F E)) s :=
  fun x hx ↦ (hp x hx).totalSpaceMk_frame_apply (hv x hx)

/-- Applying a `C^n` family of orthonormal frames to a `C^n` family of vectors in `V` is `C^n`. -/
theorem ContMDiff.totalSpaceMk_frame_apply
    (hp : ContMDiff IM (IB.prod (Unitary.model (V →L[ℝ] V))) n
      (fun x ↦ ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) (p x)))
    (hv : ContMDiff IM 𝓘(ℝ, V) n v) :
    ContMDiff IM (IB.prod 𝓘(ℝ, F)) n
      (fun x ↦ (⟨(p x).proj, (p x).snd.frame (v x)⟩ : TotalSpace F E)) :=
  fun x ↦ (hp x).totalSpaceMk_frame_apply (hv x)

/-- Reading a `C^n` section along `(p ·).proj` in a `C^n` family of orthonormal frames `p` gives a
`C^n` map into `V` (within a set at a point). -/
theorem ContMDiffWithinAt.frame_symm_apply
    (hp : ContMDiffWithinAt IM (IB.prod (Unitary.model (V →L[ℝ] V))) n
      (fun x ↦ ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) (p x)) s x₀)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun x ↦ (⟨(p x).proj, w x⟩ : TotalSpace F E)) s x₀) :
    ContMDiffWithinAt IM 𝓘(ℝ, V) n (fun x ↦ (p x).snd.frame.symm (w x)) s x₀ := by
  let b_mod := stdOrthonormalBasis ℝ V
  have hsum_eq (x : M) :
      (p x).snd.frame.symm (w x) = ∑ i, ⟪(p x).snd.frame (b_mod i), w x⟫_ℝ • b_mod i := by
    conv_lhs => rw [← b_mod.sum_repr' ((p x).snd.frame.symm (w x))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← (p x).snd.frame.inner_map_map (b_mod i) ((p x).snd.frame.symm (w x)),
      LinearIsometryEquiv.apply_symm_apply]
  exact (ContMDiffWithinAt.sum (t := Finset.univ) fun i _ ↦
    ((OrthonormalFrameBundle.contMDiffWithinAt_totalSpace_iff.1 hp (b_mod i)).inner_bundle
      hw).smul (contMDiffWithinAt_const (c := b_mod i))).congr (fun x _ ↦ hsum_eq x) (hsum_eq x₀)

/-- Reading a `C^n` section along `(p ·).proj` in a `C^n` family of orthonormal frames is `C^n` at
a point. -/
theorem ContMDiffAt.frame_symm_apply
    (hp : ContMDiffAt IM (IB.prod (Unitary.model (V →L[ℝ] V))) n
      (fun x ↦ ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) (p x)) x₀)
    (hw : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun x ↦ (⟨(p x).proj, w x⟩ : TotalSpace F E)) x₀) :
    ContMDiffAt IM 𝓘(ℝ, V) n (fun x ↦ (p x).snd.frame.symm (w x)) x₀ :=
  ContMDiffWithinAt.frame_symm_apply hp hw

/-- Reading a `C^n` section along `(p ·).proj` in a `C^n` family of orthonormal frames is `C^n` on
a set. -/
theorem ContMDiffOn.frame_symm_apply
    (hp : ContMDiffOn IM (IB.prod (Unitary.model (V →L[ℝ] V))) n
      (fun x ↦ ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) (p x)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n
      (fun x ↦ (⟨(p x).proj, w x⟩ : TotalSpace F E)) s) :
    ContMDiffOn IM 𝓘(ℝ, V) n (fun x ↦ (p x).snd.frame.symm (w x)) s :=
  fun x hx ↦ (hp x hx).frame_symm_apply (hw x hx)

/-- Reading a `C^n` section along `(p ·).proj` in a `C^n` family of orthonormal frames is `C^n`. -/
theorem ContMDiff.frame_symm_apply
    (hp : ContMDiff IM (IB.prod (Unitary.model (V →L[ℝ] V))) n
      (fun x ↦ ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) (p x)))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n
      (fun x ↦ (⟨(p x).proj, w x⟩ : TotalSpace F E))) :
    ContMDiff IM 𝓘(ℝ, V) n (fun x ↦ (p x).snd.frame.symm (w x)) :=
  fun x ↦ (hp x).frame_symm_apply (hw x)

end Evaluation

namespace TauCeti.OrthonormalFrameBundle

/-- **Jointly `C^n` evaluation map** from the product of the charted orthonormal frame bundle
`ManifoldTotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)` and `V` onto `TotalSpace F E`. -/
theorem contMDiff_totalSpaceMk_frame_apply :
    ContMDiff ((IB.prod (Unitary.model (V →L[ℝ] V))).prod 𝓘(ℝ, V)) (IB.prod 𝓘(ℝ, F)) n
      (fun q : ManifoldTotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) × V ↦
        (⟨((ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)).symm q.1).proj,
          ((ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V))
            (Fiber ℝ F E V)).symm q.1).snd.frame q.2⟩ : TotalSpace F E)) :=
  ContMDiff.totalSpaceMk_frame_apply
    (contMDiff_fst.congr fun q ↦
      Homeomorph.apply_symm_apply
        (ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)) q.1)
    contMDiff_snd

/-! ### Smooth associated bundles and smooth associated-bundle reconstruction -/

section Associated

/-- Any manifold `W` carrying a `C^n` action of `unitary (V →L[ℝ] V)` defines a `C^n` associated
fibre bundle `AssociatedBundle (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) W` over `B`. Unlike
`TauCeti.AssociatedBundle.contMDiffFiberBundle` for an abstract group, this is a global instance
because the model `Unitary.model (V →L[ℝ] V)` of the structure group is determined by `V`. -/
instance instContMDiffFiberBundleAssociatedBundle
    {EW HW W : Type*} [NormedAddCommGroup EW] [NormedSpace ℝ EW]
    [TopologicalSpace HW] {IW : ModelWithCorners ℝ EW HW}
    [TopologicalSpace W] [ChartedSpace HW W]
    [MulAction (unitary (V →L[ℝ] V)) W] [ContinuousSMul (unitary (V →L[ℝ] V)) W]
    [ContMDiffSMul (Unitary.model (V →L[ℝ] V)) IW n (unitary (V →L[ℝ] V)) W] :
    ContMDiffFiberBundle n W
      (AssociatedBundle (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) W) IB IW :=
  AssociatedBundle.contMDiffFiberBundle (Unitary.model (V →L[ℝ] V))

/-- Any finite-dimensional real normed space `W` carrying a `C^n` linear action of
`unitary (V →L[ℝ] V)` (including complex representations regarded over `ℝ`) defines a `C^n`
associated vector bundle `AssociatedBundle (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) W` over `B`. When
`W` carries an invariant inner product, `TauCeti.AssociatedBundle.instIsContMDiffRiemannianBundle`
then automatically equips this associated bundle with a `C^n` Riemannian metric. -/
instance instContMDiffVectorBundleAssociatedBundle
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [DistribMulAction (unitary (V →L[ℝ] V)) W] [SMulCommClass (unitary (V →L[ℝ] V)) ℝ W]
    [ContinuousSMul (unitary (V →L[ℝ] V)) W]
    [ContMDiffSMul (Unitary.model (V →L[ℝ] V)) 𝓘(ℝ, W) n (unitary (V →L[ℝ] V)) W] :
    ContMDiffVectorBundle n W
      (AssociatedBundle (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) W) IB :=
  AssociatedBundle.contMDiffVectorBundle (Unitary.model (V →L[ℝ] V))

variable (n IB F E V) in
/-- **Smooth associated-bundle reconstruction of a Riemannian vector bundle.** For any `C^n`
Riemannian vector bundle `E` of rank `Module.finrank ℝ V`, the canonical homeomorphism
`associatedBundleHomeomorph ℝ F E V` from the total space of the associated bundle
`AssociatedBundle (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) V` onto `TotalSpace F E` is a `C^n`
diffeomorphism, acting on each fibre over `b` by the linear isometric equivalence
`associatedLinearIsometryEquiv ℝ F E V b` sending `[φ, v]` to `φ v`. -/
def associatedBundleDiffeomorph :
    TotalSpace V (AssociatedBundle (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) V)
      ≃ₘ^n⟮IB.prod 𝓘(ℝ, V), IB.prod 𝓘(ℝ, F)⟯ TotalSpace F E :=
  bundleDiffeomorph
    (fun b ↦ (associatedLinearIsometryEquiv ℝ F E V b).toContinuousLinearEquiv) <| by
      intro u₀
      let b₀ := u₀.proj
      let e₀ := trivializationAt F E b₀
      have hb₀ : b₀ ∈ e₀.baseSet := mem_baseSet_trivializationAt F E b₀
      let c₀ := Module.finBasisOfFinrankEq ℝ F hV.out.symm
      let b_mod := stdOrthonormalBasis ℝ V
      have hproj : ContMDiffAt (IB.prod 𝓘(ℝ, V)) IB n
          (TotalSpace.proj :
            TotalSpace V (AssociatedBundle (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) V) → B) u₀ :=
        Bundle.contMDiffAt_proj (AssociatedBundle (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) V)
      have hsec : ContMDiffAt (IB.prod 𝓘(ℝ, V)) (IB.prod (Unitary.model (V →L[ℝ] V))) n
          (fun u : TotalSpace V (AssociatedBundle (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) V) ↦
            ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)
              ⟨u.proj, .ofFrame (e₀.orthonormalFrameAt c₀ b_mod u.proj)⟩) u₀ :=
        ((e₀.contMDiffOn_orthonormalFrameAt (IB := IB) (n := n) c₀ b_mod).contMDiffAt
          (e₀.open_baseSet.mem_nhds hb₀)).comp (f := TotalSpace.proj) u₀ hproj
      have hcoord : ContMDiffAt (IB.prod 𝓘(ℝ, V)) 𝓘(ℝ, V) n
          (fun u : TotalSpace V (AssociatedBundle (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) V) ↦
            (trivializationAt V (AssociatedBundle (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) V)
              b₀ u).2) u₀ :=
        (Bundle.contMDiffAt_totalSpace_iff.1 (contMDiffAt_id (x := u₀))).2
      have hU : TotalSpace.proj ⁻¹' e₀.baseSet ∈ 𝓝 u₀ :=
        (e₀.open_baseSet.preimage (FiberBundle.continuous_proj _ _)).mem_nhds hb₀
      refine (hsec.totalSpaceMk_frame_apply hcoord).congr_of_eventuallyEq
        (eventually_of_mem hU fun u hu ↦ ?_)
      simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
        congrArg (TotalSpace.mk' F u.proj)
          (associatedLinearIsometryEquiv_eq_orthonormalFrameAt_apply hu u.snd)

/-- `associatedBundleDiffeomorph` acts on each fibre by the linear isometric equivalence
`associatedLinearIsometryEquiv`. -/
theorem associatedBundleDiffeomorph_apply
    (u : TotalSpace V (AssociatedBundle (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) V)) :
    associatedBundleDiffeomorph n IB F E V u =
      ⟨u.proj, associatedLinearIsometryEquiv ℝ F E V u.proj u.snd⟩ :=
  bundleDiffeomorph_apply _ _ u

/-- `(associatedBundleDiffeomorph n IB F E V).symm` acts on each fibre by the inverse linear
isometric equivalence `(associatedLinearIsometryEquiv ℝ F E V ·).symm`. -/
theorem associatedBundleDiffeomorph_symm_apply (x : TotalSpace F E) :
    (associatedBundleDiffeomorph n IB F E V).symm x =
      ⟨x.proj, (associatedLinearIsometryEquiv ℝ F E V x.proj).symm x.snd⟩ :=
  bundleDiffeomorph_symm_apply _ _ x

/-- Coercion of `associatedBundleDiffeomorph` to a function agrees with
`associatedBundleHomeomorph`. -/
@[simp]
theorem coe_associatedBundleDiffeomorph :
    ⇑(associatedBundleDiffeomorph n IB F E V) = associatedBundleHomeomorph ℝ F E V :=
  funext fun u ↦
    (associatedBundleDiffeomorph_apply u).trans (associatedBundleHomeomorph_apply u).symm

/-- Coercion of `(associatedBundleDiffeomorph n IB F E V).symm` to a function agrees with
`(associatedBundleHomeomorph ℝ F E V).symm`. -/
@[simp]
theorem coe_associatedBundleDiffeomorph_symm :
    ⇑(associatedBundleDiffeomorph n IB F E V).symm = (associatedBundleHomeomorph ℝ F E V).symm :=
  funext fun x ↦
    (associatedBundleDiffeomorph_symm_apply x).trans (associatedBundleHomeomorph_symm_apply x).symm

/-- The underlying homeomorphism of `associatedBundleDiffeomorph` is
`associatedBundleHomeomorph`. -/
@[simp]
theorem toHomeomorph_associatedBundleDiffeomorph :
    (associatedBundleDiffeomorph n IB F E V).toHomeomorph = associatedBundleHomeomorph ℝ F E V :=
  Homeomorph.ext fun u ↦
    (associatedBundleDiffeomorph_apply u).trans (associatedBundleHomeomorph_apply u).symm

/-- Evaluating `associatedBundleDiffeomorph` on the class `[φ, v]` over `b` of an orthonormal
frame `φ` and a model vector `v` applies `φ` to `v` in `E b`. -/
theorem associatedBundleDiffeomorph_mk {b : B} (φ : Fiber ℝ F E V b) (v : V) :
    associatedBundleDiffeomorph n IB F E V ⟨b, AssociatedBundle.mk (unitary (V →L[ℝ] V)) φ v⟩ =
      ⟨b, φ.frame v⟩ := by
  rw [coe_associatedBundleDiffeomorph, associatedBundleHomeomorph_mk]

/-- Evaluating `(associatedBundleDiffeomorph n IB F E V).symm` on `⟨b, w⟩` expresses `w : E b` in
any orthonormal frame `φ` of `E b` as the class `[φ, φ⁻¹ w]` over `b`. -/
theorem associatedBundleDiffeomorph_symm_mk_apply {b : B} (φ : Fiber ℝ F E V b) (w : E b) :
    (associatedBundleDiffeomorph n IB F E V).symm ⟨b, w⟩ =
      ⟨b, AssociatedBundle.mk (unitary (V →L[ℝ] V)) φ (φ.frame.symm w)⟩ := by
  rw [coe_associatedBundleDiffeomorph_symm, associatedBundleHomeomorph_symm_mk_apply]

end Associated

/-! ### Smooth naturality under Riemannian bundle isometries -/

section Naturality

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {E' : B → Type*} [TopologicalSpace (TotalSpace F' E')]
  [∀ b, NormedAddCommGroup (E' b)] [∀ b, InnerProductSpace ℝ (E' b)]
  [FiberBundle F' E'] [VectorBundle ℝ F' E']
  [ContMDiffVectorBundle n F' E' IB] [IsContMDiffRiemannianBundle IB n F' E']
  [ContinuousFiberNorm F' E']
  [Fact (Module.finrank ℝ V = Module.finrank ℝ F')]

/-- If a family of fibrewise linear isometric equivalences `Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b` is `C^n` on
vector-bundle total spaces, the induced equivariant map between the charted orthonormal frame
bundles of `E` and `E'` is `C^n`. -/
theorem contMDiff_fiberwiseMap_map {Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b}
    (hΦ : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F')) n
      (fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.snd⟩ : TotalSpace F' E'))) :
    ContMDiff (IB.prod (Unitary.model (V →L[ℝ] V))) (IB.prod (Unitary.model (V →L[ℝ] V))) n
      (ManifoldTotalSpace.fiberwiseMap (F := unitary (V →L[ℝ] V))
        (fun b ↦ Fiber.map (F := F) (F' := F') (V := V) Φ (b := b))) := by
  let f₀ : ManifoldTotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) →
      TotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) :=
    (ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)).symm
  have hf₀ : ∀ v : V, ContMDiff (IB.prod (Unitary.model (V →L[ℝ] V))) (IB.prod 𝓘(ℝ, F)) n
      (fun x ↦ (⟨(f₀ x).proj, (f₀ x).snd.frame v⟩ : TotalSpace F E)) :=
    contMDiff_totalSpace_iff.1 <| contMDiff_id.congr fun x ↦
      Homeomorph.apply_symm_apply
        (ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)) x
  let g : ManifoldTotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V) →
      TotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F' E' V) :=
    fun x ↦ ⟨(f₀ x).proj, Fiber.map (F := F) (F' := F') Φ (f₀ x).snd⟩
  have hg : ContMDiff (IB.prod (Unitary.model (V →L[ℝ] V))) (IB.prod (Unitary.model (V →L[ℝ] V))) n
      (fun x ↦ ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F' E' V) (g x)) :=
    contMDiff_totalSpace_iff.2 fun v ↦ (hΦ.comp (hf₀ v)).congr fun x ↦
      congrArg (TotalSpace.mk' F' (f₀ x).proj) <| by
        simp only [g, Fiber.frame_map, LinearIsometryEquiv.trans_apply]
  refine hg.congr fun x ↦ ?_
  obtain ⟨p, rfl⟩ :=
    (ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)).surjective x
  dsimp only [g, f₀]
  rw [ManifoldTotalSpace.fiberwiseMap_homeomorph, Homeomorph.symm_apply_apply]

/-- **Smooth naturality of the orthonormal frame bundle under fibrewise linear isometries.** For
two `C^n` Riemannian vector bundles `E` and `E'` of rank `Module.finrank ℝ V` over `B` and a family
of fibrewise linear isometric equivalences `Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b`, the induced equivariant map
`ManifoldTotalSpace.fiberwiseMap (fun b ↦ Fiber.map Φ (b := b))` between their charted orthonormal
frame bundles is `C^n` if and only if `Φ` is `C^n` on vector-bundle total spaces. -/
theorem contMDiff_fiberwiseMap_map_iff {Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b} :
    ContMDiff (IB.prod (Unitary.model (V →L[ℝ] V))) (IB.prod (Unitary.model (V →L[ℝ] V))) n
        (ManifoldTotalSpace.fiberwiseMap (F := unitary (V →L[ℝ] V))
          (fun b ↦ Fiber.map (F := F) (F' := F') (V := V) Φ (b := b))) ↔
      ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F')) n
        (fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.snd⟩ : TotalSpace F' E')) := by
  refine ⟨fun h x₀ ↦ ?_, contMDiff_fiberwiseMap_map⟩
  let b₀ := x₀.proj
  let e₀ := trivializationAt F E b₀
  have hb₀ : b₀ ∈ e₀.baseSet := mem_baseSet_trivializationAt F E b₀
  have hVF : Module.finrank ℝ F = Module.finrank ℝ V :=
    (Fact.out : Module.finrank ℝ V = Module.finrank ℝ F).symm
  let c₀ := Module.finBasisOfFinrankEq ℝ F hVF
  let b_mod := stdOrthonormalBasis ℝ V
  let σ := e₀.orthonormalFrameAt c₀ b_mod
  have hsec : ContMDiffAt (IB.prod 𝓘(ℝ, F)) (IB.prod (Unitary.model (V →L[ℝ] V))) n
      (fun x : TotalSpace F E ↦
        ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F' E' V)
          ⟨x.proj, Fiber.map (F := F) (F' := F') Φ (.ofFrame (σ x.proj))⟩) x₀ := by
    have h₀ := ((e₀.contMDiffOn_orthonormalFrameAt (IB := IB) (n := n) c₀ b_mod).contMDiffAt
      (e₀.open_baseSet.mem_nhds hb₀)).comp x₀ (Bundle.contMDiffAt_proj E)
    exact (h.contMDiffAt.comp x₀ h₀).congr_of_eventuallyEq
      (.of_forall fun x ↦ by
        simp only [σ, Function.comp_apply, ManifoldTotalSpace.fiberwiseMap_homeomorph])
  have hU : TotalSpace.proj ⁻¹' e₀.baseSet ∈ 𝓝 x₀ :=
    (e₀.open_baseSet.preimage (FiberBundle.continuous_proj F E)).mem_nhds hb₀
  have hcoord : ContMDiffAt (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) n
      (fun x : TotalSpace F E ↦ (σ x.proj).symm x.snd) x₀ :=
    (e₀.contMDiffOn_orthonormalFrameAt_symm c₀ b_mod).contMDiffAt hU
  refine (hsec.totalSpaceMk_frame_apply hcoord).congr_of_eventuallyEq
    (.of_forall fun x ↦ congrArg (TotalSpace.mk' F' x.proj) ?_)
  simp only [Fiber.frame_map, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]

variable (V) in
/-- A family of fibrewise linear isometric equivalences `Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b` that is `C^n` on
vector-bundle total spaces induces an equivariant `C^n` diffeomorphism between the charted
orthonormal frame bundles of `E` and `E'`. Smoothness of the inverse is automatic via
`TauCeti.PrincipalBundle.diffeomorphOfEquivariant`. -/
def manifoldTotalSpaceMapDiffeomorph (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b)
    (hΦ : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F')) n
      (fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.snd⟩ : TotalSpace F' E'))) :
    ManifoldTotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)
      ≃ₘ^n⟮IB.prod (Unitary.model (V →L[ℝ] V)), IB.prod (Unitary.model (V →L[ℝ] V))⟯
    ManifoldTotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F' E' V) :=
  PrincipalBundle.diffeomorphOfEquivariant (unitary (V →L[ℝ] V))
    (Fiber.mapEquiv F F' V Φ)
    (fun _ g φ ↦ by simp only [Fiber.mapEquiv_apply, Fiber.map_smul])
    ((contMDiff_fiberwiseMap_map hΦ).congr fun x ↦ by
      obtain ⟨p, rfl⟩ :=
        (ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)).surjective x
      simp)

/-- `manifoldTotalSpaceMapDiffeomorph` acts on `ManifoldTotalSpace` by the fibrewise map
`Fiber.map Φ`. -/
@[simp]
theorem manifoldTotalSpaceMapDiffeomorph_apply (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b)
    (hΦ : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F')) n
      (fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.snd⟩ : TotalSpace F' E')))
    (x : ManifoldTotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)) :
    manifoldTotalSpaceMapDiffeomorph V Φ hΦ x =
      ManifoldTotalSpace.fiberwiseMap (fun b ↦ Fiber.map (F := F) (F' := F') Φ (b := b)) x := by
  obtain ⟨p, rfl⟩ :=
    (ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)).surjective x
  simp [manifoldTotalSpaceMapDiffeomorph]

/-- `(manifoldTotalSpaceMapDiffeomorph V Φ hΦ).symm` acts on `ManifoldTotalSpace` by the fibrewise
map `Fiber.map (fun y ↦ (Φ y).symm)`. -/
@[simp]
theorem manifoldTotalSpaceMapDiffeomorph_symm_apply (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b)
    (hΦ : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F')) n
      (fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.snd⟩ : TotalSpace F' E')))
    (x : ManifoldTotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F' E' V)) :
    (manifoldTotalSpaceMapDiffeomorph V Φ hΦ).symm x =
      ManifoldTotalSpace.fiberwiseMap
        (fun b ↦ Fiber.map (F := F') (F' := F) (fun y ↦ (Φ y).symm) (b := b)) x := by
  obtain ⟨p, rfl⟩ :=
    (ManifoldTotalSpace.homeomorph (unitary (V →L[ℝ] V)) (Fiber ℝ F' E' V)).surjective x
  simp [manifoldTotalSpaceMapDiffeomorph]

/-- The diffeomorphism `manifoldTotalSpaceMapDiffeomorph` is equivariant for the right action of
`unitary (V →L[ℝ] V)`. -/
theorem manifoldTotalSpaceMapDiffeomorph_smul (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b)
    (hΦ : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F')) n
      (fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.snd⟩ : TotalSpace F' E')))
    (g : (unitary (V →L[ℝ] V))ᵐᵒᵖ)
    (x : ManifoldTotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)) :
    manifoldTotalSpaceMapDiffeomorph V Φ hΦ (g • x) =
      g • manifoldTotalSpaceMapDiffeomorph V Φ hΦ x := by
  rcases g with ⟨g⟩
  exact PrincipalBundle.diffeomorphOfEquivariant_op_smul _ _ _ g x

end Naturality

end TauCeti.OrthonormalFrameBundle

end PrincipalBundle

end
