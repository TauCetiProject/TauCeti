/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothApprox
public import TauCeti.Geometry.Manifold.Transversality.Parametric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.UniformSpace.OfCompactT2
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.ContMDiffMap.Radius
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.ModelTransport.Interior
import TauCeti.Geometry.Manifold.SmoothEmbedding.Euclidean
import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence

/-!
# Relative transversality with diagonal control

A continuous map `f : C(M, P)` from a σ-compact Hausdorff smooth manifold `M` into a Hausdorff
boundaryless smooth manifold `P`, whose image has compact closure and which is already smooth and
transverse to a smooth map `g : Z → P` on a neighbourhood `U` of a closed set `C ⊆ M`, is homotopic
relative to `C` to a smooth map `f'` globally transverse to `g`, by a homotopy `K` controlled by any
prescribed neighbourhood `D` of the diagonal of `P` (`(K (t, x), f x) ∈ D` for all `t` and `x`).
In particular, this holds without extra hypotheses whenever `P` is compact or `M` is compact.

Both boundaryless sources (`[BoundarylessManifold IM M]`) and manifolds with boundary modelled on
the Euclidean half-space `𝓡∂ (m + 1)` are covered. In the half-space case, facewise transversality
on `U` (ambient transversality on `U ∩ interior M` together with transversality of `f ∘ Subtype.val`
on `∂M ∩ U`) is upgraded relative to `C` to global transversality on both `M` and `∂M`.

## Proof architecture

1. **Embedded-target smooth perturbation.** Suppose `e : SmoothEmbedding IN 𝓘(ℝ, V) ∞ N V` embeds a
   boundaryless manifold `N` into a finite-dimensional real normed space `V`, and let `r : O → N` be
   a smooth submersive tubular retraction of an open neighbourhood `O ⊆ V` of `range e`
   (`TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction`). Given a smooth map `f₁ : M → N`
   transverse to `g` on an open neighbourhood `V₁` of `C`, choose a positive smooth radius
   `ρ : C^∞(M, ℝ)` (`TauCeti.exists_contMDiffMap_closedBall_subset`) keeping the perturbations
   inside `O` and inside a diagonal neighbourhood `D₁`, and a smooth cutoff `ψ : C^∞(M, [0, 1])`
   equal to `0` on `C` and `1` outside `V₁`. On the open unit ball `B ⊆ V`, define
   `H(x, v) = r(e(f₁ x) + ψ(x)² ρ(x) v)`. Along any smooth stratum map `h : X → M`:
   * where `ψ(h x') ≠ 0`, `H(h x', ·)` is an affine diffeomorphism onto a ball composed with the
     submersion `r`, so `(x', v)` is a regular point of `(x', v) ↦ H(h x', v)`;
   * where `ψ(h x') = 0`, we have `h x' ∈ V₁` and the squared cutoff `ψ²` vanishes to first order,
     so the differential of `(x', v) ↦ H(h x', v)` reduces to `d(f₁ ∘ h)_{x'} ∘ fst`.
   Parametric transversality (`TauCeti.dense_isTransverse_slice` and
   `TauCeti.dense_isTransverse_slice_halfSpace`) then furnishes a parameter `v₀ ∈ B` whose slice is
   transverse, joined to `f₁` relative to `C` by the straight-line homotopy `t ↦ H(·, t • v₀)`.
2. **Reduction from relatively compact image.** For general `f : C(M, P)` with
   `IsCompact (closure (range f))`, rechart `P` to its interior vector-space model
   `TauCeti.BoundarylessModel JP P` and choose an open neighbourhood `W` of `closure (range f)` with
   compact closure admitting a Euclidean embedding
   (`IsCompact.exists_opens_nonempty_smoothEmbedding_euclidean`). Using the unique uniformity of the
   compact Hausdorff space `closure W` (`uniformSpaceOfCompactR1`), choose `D₁` with `D₁ ○ D₁ ⊆ D`.
   First smooth `f` relative to `closure V₁ ⊆ interior U` within `D₁`
   (`TauCeti.SmoothEmbedding.exists_contMDiff_homotopyRel`), then apply the smooth perturbation step
   on `W` within `D₁` against the restricted target map `g⁻¹(W) → W`, and concatenate the two
   relative homotopies.

## Main results

* `TauCeti.SmoothEmbedding.exists_contMDiff_isTransverse_homotopyRel_of_contMDiff`,
  `TauCeti.SmoothEmbedding.exists_contMDiff_isTransverse_homotopyRel_halfSpace_of_contMDiff`:
  smooth relative perturbation to transversality into a smoothly embedded target.
* `ContinuousMap.exists_contMDiff_isTransverse_homotopyRel_of_isCompact_closure_range`,
  `ContinuousMap.exists_contMDiff_isTransverse_homotopicRel_of_isCompact_closure_range`,
  `ContinuousMap.exists_contMDiff_isTransverse_homotopic_of_isCompact_closure_range`,
  `ContinuousMap.exists_contMDiff_isTransverse_homotopyRel`,
  `ContinuousMap.exists_contMDiff_isTransverse_homotopicRel`,
  `ContinuousMap.exists_contMDiff_isTransverse_homotopic`,
  `ContinuousMap.exists_contMDiff_isTransverse_homotopyRel_of_compactSpace`: relative and global
  transversality with diagonal control for boundaryless sources.
* `ContinuousMap.exists_contMDiff_isTransverse_homotopyRel_halfSpace_of_isCompact_closure_range`,
  `ContinuousMap.exists_contMDiff_isTransverse_homotopicRel_halfSpace_of_isCompact_closure_range`,
  `ContinuousMap.exists_contMDiff_isTransverse_homotopic_halfSpace_of_isCompact_closure_range`,
  `ContinuousMap.exists_contMDiff_isTransverse_homotopyRel_halfSpace`,
  `ContinuousMap.exists_contMDiff_isTransverse_homotopicRel_halfSpace`,
  `ContinuousMap.exists_contMDiff_isTransverse_homotopic_halfSpace`,
  `ContinuousMap.exists_contMDiff_isTransverse_homotopyRel_halfSpace_of_compactSpace`: facewise
  relative and global transversality with diagonal control on half-space manifolds with boundary.

## References

* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976, Chapter 3,
  Theorem 2.1, pp. 74–78.
* V. Guillemin and A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 2, §3,
  pp. 68–75.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.36, pp. 146–147.
-/

public noncomputable section

open Function Filter Set Topology TopologicalSpace
open scoped Manifold ContDiff Topology

namespace TauCeti

section Helpers

private theorem exists_nhdsSet_diagonal_comp_subset {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {D : Set (X × X)} (hD : D ∈ 𝓝ˢ (diagonal X)) :
    ∃ D₁ ∈ 𝓝ˢ (diagonal X), ∀ ⦃a b c : X⦄, (a, b) ∈ D₁ → (b, c) ∈ D₁ → (a, c) ∈ D := by
  let := uniformSpaceOfCompactR1 (γ := X)
  obtain ⟨D₁, hD₁, hD₁D⟩ := comp_mem_uniformity_sets (α := X) hD
  exact ⟨D₁, hD₁, fun _ _ _ hab hbc ↦ hD₁D ⟨_, hab, hbc⟩⟩

private theorem preimage_prodMap_mem_nhdsSet_diagonal {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {j : X → Y} (hj : Continuous j) {D : Set (Y × Y)}
    (hD : D ∈ 𝓝ˢ (diagonal Y)) :
    Prod.map j j ⁻¹' D ∈ 𝓝ˢ (diagonal X) := by
  rw [mem_nhdsSet_iff_forall]
  rintro ⟨x, _⟩ (rfl : x = _)
  exact (hj.prodMap hj).continuousAt.preimage_mem_nhds (mem_nhdsSet_iff_forall.1 hD (j x, j x) rfl)

private theorem secondCountableTopology_of_boundaryless_lindelof
    {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
    [TopologicalSpace HZ] (IZ : ModelWithCorners ℝ EZ HZ)
    [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold IZ 1 Z] [BoundarylessManifold IZ Z]
    [LindelofSpace Z] :
    SecondCountableTopology Z := by
  let := BoundarylessModel.interiorChartedSpace IZ (M := Z)
  have : LindelofSpace (BoundarylessModel IZ Z) := inferInstanceAs (LindelofSpace Z)
  have : SecondCountableTopology (BoundarylessModel IZ Z) :=
    ChartedSpace.secondCountable_of_lindelof EZ (BoundarylessModel IZ Z)
  exact (BoundarylessModel.homeomorph IZ Z).secondCountableTopology

private theorem tangentSpaceCast_self {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    [TopologicalSpace HN] (IN : ModelWithCorners ℝ EN HN) [TopologicalSpace N] [ChartedSpace HN N]
    (a : N) (v : TangentSpace IN a) :
    tangentSpaceCast IN a a v = v :=
  rfl

private theorem tangentSpaceCast_trans {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    [TopologicalSpace HN] (IN : ModelWithCorners ℝ EN HN) [TopologicalSpace N] [ChartedSpace HN N]
    (a b c : N) (v : TangentSpace IN a) :
    tangentSpaceCast IN b c (tangentSpaceCast IN a b v) = tangentSpaceCast IN a c v :=
  rfl

private theorem tangentSpaceCast_mfderiv_of_eq {EX HX X EN HN N : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
    (φ : X → N) {a b : X} (hab : a = b) (v : TangentSpace IX b) :
    tangentSpaceCast IN (φ b) (φ a) (mfderiv IX IN φ b v) =
      mfderiv IX IN φ a (tangentSpaceCast IX b a v) := by
  subst hab
  rfl

private theorem tangentSpaceCast_mfderiv_congr {EX HX X EN HN N : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
    {f₁ f₂ : X → N} (h : f₁ = f₂) (x : X) (v : TangentSpace IX x) :
    tangentSpaceCast IN (f₁ x) (f₂ x) (mfderiv IX IN f₁ x v) = mfderiv IX IN f₂ x v := by
  subst h
  rfl

private theorem tangentSpaceCast_self_model {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y₁ y₂ : E} (hy : y₁ = y₂) {v₁ : TangentSpace 𝓘(ℝ, E) y₁} {v₂ : TangentSpace 𝓘(ℝ, E) y₂}
    (hv : NormedSpace.fromTangentSpace y₁ v₁ = NormedSpace.fromTangentSpace y₂ v₂) :
    tangentSpaceCast 𝓘(ℝ, E) y₂ y₁ v₂ = v₁ := by
  subst hy
  exact (NormedSpace.fromTangentSpace y₁).injective hv.symm

private theorem isRegularPoint_perturbation_of_ne_zero
    {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Opens E}
    {FW HW W : Type*} [NormedAddCommGroup FW] [NormedSpace ℝ FW] [TopologicalSpace HW]
    {IW : ModelWithCorners ℝ FW HW} [TopologicalSpace W] [ChartedSpace HW W]
    {O : Set E} (hO : IsOpen O) {r : E → W} (hrO : ContMDiffOn 𝓘(ℝ, E) IW ∞ r O)
    (hrreg : ∀ y ∈ O, IsRegularPoint 𝓘(ℝ, E) IW r y)
    {e₀ : X → E} {ψ₀ ρ₀ : X → ℝ} {x : X} {v : B}
    (hΦO : e₀ x + ψ₀ x • ((ψ₀ x * ρ₀ x) • (v : E)) ∈ O)
    (hΦd : MDifferentiableAt (IX.prod 𝓘(ℝ, E)) 𝓘(ℝ, E)
      (fun q : X × B ↦ e₀ q.1 + ψ₀ q.1 • ((ψ₀ q.1 * ρ₀ q.1) • (q.2 : E))) (x, v))
    (hψ : ψ₀ x ≠ 0) (hρ : ρ₀ x ≠ 0) :
    IsRegularPoint (IX.prod 𝓘(ℝ, E)) IW
      (fun q : X × B ↦ r (e₀ q.1 + ψ₀ q.1 • ((ψ₀ q.1 * ρ₀ q.1) • (q.2 : E)))) (x, v) := by
  let Φ : X × B → E := fun q ↦ e₀ q.1 + ψ₀ q.1 • ((ψ₀ q.1 * ρ₀ q.1) • (q.2 : E))
  let c : ℝ := ψ₀ x * (ψ₀ x * ρ₀ x)
  have hc : c ≠ 0 := mul_ne_zero hψ (mul_ne_zero hψ hρ)
  let σ : B → X × B := fun v' ↦ (x, v')
  have hσ : MDifferentiableAt 𝓘(ℝ, E) (IX.prod 𝓘(ℝ, E)) σ v :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hΦσ_eq : Φ ∘ σ = (fun y : E ↦ c • y + e₀ x) ∘ (Subtype.val : B → E) := by
    ext v'
    simp [Φ, σ, c, smul_smul, add_comm]
  have hΦσ_surj : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ ∘ σ) v) := by
    intro u
    let uE : E := NormedSpace.fromTangentSpace (Φ (σ v)) u
    let wE : TangentSpace 𝓘(ℝ, E) (v : E) := (NormedSpace.fromTangentSpace (v : E)).symm (c⁻¹ • uE)
    let w : TangentSpace 𝓘(ℝ, E) v := (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, E)) v).symm wE
    refine ⟨w, (NormedSpace.fromTangentSpace (Φ (σ v))).injective ?_⟩
    change mvfderiv 𝓘(ℝ, E) (Φ ∘ σ) v w = uE
    have haff : HasFDerivAt (fun y : E ↦ c • y + e₀ x)
        (c • ContinuousLinearMap.id ℝ E) (v : E) := by
      simpa using ((hasFDerivAt_id (v : E)).const_smul c).add_const (e₀ x)
    rw [hΦσ_eq,
      mvfderiv_comp_apply v haff.differentiableAt.mdifferentiableAt
        (contMDiff_subtype_val.mdifferentiableAt one_ne_zero) w,
      Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, mvfderiv_eq_fderiv, haff.fderiv,
      ContinuousLinearMap.comp_apply]
    simp [wE, inv_smul_smul₀ hc]
  have hrd : MDifferentiableAt 𝓘(ℝ, E) IW r (Φ (x, v)) :=
    (hrO.contMDiffAt (hO.mem_nhds hΦO)).mdifferentiableAt (by simp)
  have hcomp_surj : Surjective (mfderiv 𝓘(ℝ, E) IW ((r ∘ Φ) ∘ σ) v) := by
    change Surjective (mfderiv 𝓘(ℝ, E) IW (r ∘ (Φ ∘ σ)) v)
    rw [mfderiv_comp v hrd (hΦd.comp v hσ), ContinuousLinearMap.coe_comp]
    exact (isRegularPoint_iff.1 (hrreg _ hΦO)).comp hΦσ_surj
  rw [mfderiv_comp v (hrd.comp (x, v) hΦd) hσ, ContinuousLinearMap.coe_comp] at hcomp_surj
  exact isRegularPoint_iff.2 hcomp_surj.of_comp

private theorem isTransverseAt_perturbation_of_eq_zero
    {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
    {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Opens E}
    {FW HW W : Type*} [NormedAddCommGroup FW] [NormedSpace ℝ FW] [TopologicalSpace HW]
    {IW : ModelWithCorners ℝ FW HW} [TopologicalSpace W] [ChartedSpace HW W]
    {O : Set E} (hO : IsOpen O) {r : E → W} (hrO : ContMDiffOn 𝓘(ℝ, E) IW ∞ r O)
    {e₀ : X → E} {ψ₀ ρ₀ : X → ℝ} {f₀ : X → W} {g' : Z → W} {x : X} {v : B} {z' : Z}
    (he₀ : MDifferentiableAt IX 𝓘(ℝ, E) e₀ x) (hψd : MDifferentiableAt IX 𝓘(ℝ) ψ₀ x)
    (hρd : MDifferentiableAt IX 𝓘(ℝ) ρ₀ x) (hf₀ : ∀ x', r (e₀ x') = f₀ x')
    (hΦO : e₀ x + ψ₀ x • ((ψ₀ x * ρ₀ x) • (v : E)) ∈ O) (hψ0 : ψ₀ x = 0)
    (htrans : IsTransverseAt IX IZ IW f₀ g' x z') :
    IsTransverseAt (IX.prod 𝓘(ℝ, E)) IZ IW
      (fun q : X × B ↦ r (e₀ q.1 + ψ₀ q.1 • ((ψ₀ q.1 * ρ₀ q.1) • (q.2 : E)))) g' (x, v) z' := by
  let q₀ : X × B := (x, v); let Φ₀ : X × B → E := e₀ ∘ Prod.fst
  let a : X × B → ℝ := ψ₀ ∘ Prod.fst; let b : X × B → E := fun q ↦ (ψ₀ q.1 * ρ₀ q.1) • (q.2 : E)
  let Φ : X × B → E := Φ₀ + a • b
  have hΦ₀d : MDifferentiableAt (IX.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) Φ₀ q₀ := he₀.comp q₀ mdifferentiableAt_fst
  have had : MDifferentiableAt (IX.prod 𝓘(ℝ, E)) 𝓘(ℝ) a q₀ := hψd.comp q₀ mdifferentiableAt_fst
  have hbd : MDifferentiableAt (IX.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) b q₀ :=
    (had.mul (hρd.comp q₀ mdifferentiableAt_fst)).smul
      ((contMDiff_subtype_val.mdifferentiableAt one_ne_zero).comp q₀ mdifferentiableAt_snd)
  have hΦ_eq : Φ₀ q₀ = Φ q₀ := by simp [Φ, Φ₀, a, q₀, hψ0]
  have hmv : mvfderiv (IX.prod 𝓘(ℝ, E)) Φ₀ q₀ = mvfderiv (IX.prod 𝓘(ℝ, E)) Φ q₀ := by
    change mvfderiv (IX.prod 𝓘(ℝ, E)) Φ₀ q₀ = mvfderiv (IX.prod 𝓘(ℝ, E)) (Φ₀ + a • b) q₀
    rw [mvfderiv_add hΦ₀d (had.smul hbd), mvfderiv_smul had hbd,
      show a q₀ = 0 from hψ0, show b q₀ = 0 by simp [b, q₀, hψ0]]
    ext w
    simp only [add_apply, zero_smul, zero_apply, ContinuousLinearMap.smulRight_apply, smul_zero,
      add_zero]
  have hrd : MDifferentiableAt 𝓘(ℝ, E) IW r (Φ q₀) :=
    (hrO.contMDiffAt (hO.mem_nhds hΦO)).mdifferentiableAt (by simp)
  have hreq : r ∘ Φ₀ = f₀ ∘ Prod.fst := funext fun q ↦ hf₀ q.1
  have hcast_u (u : TangentSpace IX x) :
      tangentSpaceCast IW ((r ∘ Φ) q₀) (f₀ x)
        (mfderiv (IX.prod 𝓘(ℝ, E)) IW (r ∘ Φ) q₀ (u, (0 : TangentSpace 𝓘(ℝ, E) v))) =
        mfderiv IX IW f₀ x u := by
    let w₀ : TangentSpace (IX.prod 𝓘(ℝ, E)) q₀ := (u, (0 : TangentSpace 𝓘(ℝ, E) v))
    have hcast_E :
        tangentSpaceCast 𝓘(ℝ, E) (Φ q₀) (Φ₀ q₀) (mfderiv (IX.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) Φ q₀ w₀) =
          mfderiv (IX.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) Φ₀ q₀ w₀ :=
      tangentSpaceCast_self_model hΦ_eq (DFunLike.congr_fun hmv w₀)
    have h1 : tangentSpaceCast IW (r (Φ q₀)) (r (Φ₀ q₀))
        (mfderiv (IX.prod 𝓘(ℝ, E)) IW (r ∘ Φ) q₀ w₀) =
        mfderiv (IX.prod 𝓘(ℝ, E)) IW (r ∘ Φ₀) q₀ w₀ := by
      rw [mfderiv_comp_apply q₀ hrd (hΦ₀d.add (had.smul hbd)) w₀,
        tangentSpaceCast_mfderiv_of_eq r hΦ_eq, hcast_E,
        ← mfderiv_comp_apply q₀ (hΦ_eq.symm ▸ hrd) hΦ₀d w₀]
    have h12 := (congrArg (tangentSpaceCast IW (r (Φ₀ q₀)) (f₀ x)) h1).trans
      (tangentSpaceCast_mfderiv_congr (IN := IW) hreq q₀ w₀)
    rw [tangentSpaceCast_trans] at h12
    exact h12.trans (by rw [mfderiv_comp_fst]; rfl)
  change IsTransverseAt (IX.prod 𝓘(ℝ, E)) IZ IW (r ∘ Φ) g' q₀ z'
  rw [isTransverseAt_iff_forall]
  intro hxy vt
  have hf₀_eq : (r ∘ Φ) q₀ = f₀ x := (congrArg r hΦ_eq.symm).trans (hf₀ x)
  obtain ⟨u, wz, huw⟩ := isTransverseAt_iff_forall.1 htrans (hf₀_eq.symm.trans hxy)
    (tangentSpaceCast IW ((r ∘ Φ) q₀) (f₀ x) vt)
  refine ⟨(u, (0 : TangentSpace 𝓘(ℝ, E) v)), wz, ?_⟩
  have hback := congrArg (tangentSpaceCast IW (f₀ x) ((r ∘ Φ) q₀)) huw
  rw [← hcast_u u, map_add, tangentSpaceCast_trans, tangentSpaceCast_self,
    tangentSpaceCast_trans, tangentSpaceCast_trans, tangentSpaceCast_self] at hback
  exact hback

end Helpers

namespace SmoothEmbedding

section Perturbation

private abbrev unitBallOpens (V : Type*) [SeminormedAddCommGroup V] : Opens V :=
  ⟨Metric.ball (0 : V) 1, Metric.isOpen_ball⟩

private instance (V : Type*) [SeminormedAddCommGroup V] : Nonempty (unitBallOpens V) :=
  ⟨⟨0, Metric.mem_ball_self zero_lt_one⟩⟩

private abbrev perturbationCoord {M N V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (e : N → V) (f₁ : M → N) (ψ ρ : M → ℝ) (q : M × unitBallOpens V) : V :=
  e (f₁ q.1) + ψ q.1 • ((ψ q.1 * ρ q.1) • (q.2 : V))

private abbrev perturbationMap {M N V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (r : V → N) (e : N → V) (f₁ : M → N) (ψ ρ : M → ℝ) (q : M × unitBallOpens V) : N :=
  r (perturbationCoord e f₁ ψ ρ q)

private theorem contMDiff_perturbationCoord
    {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
    {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
    {FN GN N : Type*} [NormedAddCommGroup FN] [NormedSpace ℝ FN] [TopologicalSpace GN]
    {IN : ModelWithCorners ℝ FN GN} [TopologicalSpace N] [ChartedSpace GN N]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {e : N → V} (he : ContMDiff IN 𝓘(ℝ, V) ∞ e) {f₁ : M → N} (hf₁ : ContMDiff IM IN ∞ f₁)
    {ψ ρ : M → ℝ} (hψ : ContMDiff IM 𝓘(ℝ) ∞ ψ) (hρ : ContMDiff IM 𝓘(ℝ) ∞ ρ) :
    ContMDiff (IM.prod 𝓘(ℝ, V)) 𝓘(ℝ, V) ∞ (perturbationCoord e f₁ ψ ρ) :=
  ((he.comp hf₁).comp contMDiff_fst).add
    ((hψ.comp contMDiff_fst).smul
      (((hψ.mul hρ).comp contMDiff_fst).smul (contMDiff_subtype_val.comp contMDiff_snd)))

private theorem isTransverseAt_perturbationMap
    {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
    {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
    {FN GN N : Type*} [NormedAddCommGroup FN] [NormedSpace ℝ FN] [TopologicalSpace GN]
    {IN : ModelWithCorners ℝ FN GN} [TopologicalSpace N] [ChartedSpace GN N]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
    {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]
    {O : Set V} (hO : IsOpen O) {r : V → N} (hrO : ContMDiffOn 𝓘(ℝ, V) IN ∞ r O)
    (hrreg : ∀ y ∈ O, IsRegularPoint 𝓘(ℝ, V) IN r y)
    {e : N → V} (he : ContMDiff IN 𝓘(ℝ, V) ∞ e) (hre : ∀ y, r (e y) = y)
    {f₁ : M → N} (hf₁ : ContMDiff IM IN ∞ f₁) {ψ ρ : M → ℝ}
    (hψ : ContMDiff IM 𝓘(ℝ) ∞ ψ) (hρ : ContMDiff IM 𝓘(ℝ) ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) {V₁ : Set M} (hψV₁ : ∀ x, x ∉ V₁ → ψ x = 1)
    (hO_mem : ∀ q : M × unitBallOpens V, perturbationCoord e f₁ ψ ρ q ∈ O)
    {h : X → M} (hh : ContMDiff IX IM ∞ h) {g : Z → N} {x' : X} {v : unitBallOpens V} {z : Z}
    (htrans : h x' ∈ V₁ → IsTransverseAt IX IZ IN (f₁ ∘ h) g x' z) :
    IsTransverseAt (IX.prod 𝓘(ℝ, V)) IZ IN
      (fun q : X × unitBallOpens V ↦ perturbationMap r e f₁ ψ ρ (h q.1, q.2)) g (x', v) z := by
  by_cases hψ0 : ψ (h x') = 0
  · have hx'V₁ : h x' ∈ V₁ := by_contra fun hx' ↦ zero_ne_one (hψ0.symm.trans (hψV₁ (h x') hx'))
    exact isTransverseAt_perturbation_of_eq_zero hO hrO
      (((he.comp hf₁).comp hh).mdifferentiableAt (by simp))
      ((hψ.comp hh).mdifferentiableAt (by simp))
      ((hρ.comp hh).mdifferentiableAt (by simp))
      (fun y ↦ hre (f₁ (h y))) (hO_mem (h x', v)) hψ0 (htrans hx'V₁)
  · have hΦhd : MDifferentiableAt (IX.prod 𝓘(ℝ, V)) 𝓘(ℝ, V)
        (fun q : X × unitBallOpens V ↦ perturbationCoord e f₁ ψ ρ (h q.1, q.2)) (x', v) :=
      ((contMDiff_perturbationCoord he hf₁ hψ hρ).comp
        ((hh.comp contMDiff_fst).prodMk contMDiff_snd)).mdifferentiableAt (by simp)
    exact (isRegularPoint_perturbation_of_ne_zero hO hrO hrreg
      (e₀ := e ∘ f₁ ∘ h) (ψ₀ := ψ ∘ h) (ρ₀ := ρ ∘ h) (x := x')
      (hO_mem (h x', v)) hΦhd hψ0 (hρpos (h x')).ne').isTransverseAt_left g z

private theorem perturbation_smul_mem_closedBall {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] {a r : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hr : 0 < r) (v : unitBallOpens V) :
    a • ((a * r) • (v : V)) ∈ Metric.closedBall (0 : V) r := by
  have ha0 := ha.1; have ha1 := ha.2; have hr0 := hr.le
  have hc_nonneg : 0 ≤ a * (a * r) := by positivity
  have hc_le : a * (a * r) ≤ r :=
    (mul_le_of_le_one_left (by positivity) ha1).trans (mul_le_of_le_one_left hr0 ha1)
  rw [smul_smul, Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hc_nonneg]
  exact (mul_le_of_le_one_right hc_nonneg (mem_ball_zero_iff.1 v.2).le).trans hc_le

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M] [SigmaCompactSpace M] [T2Space M]
  {FN GN N : Type*} [NormedAddCommGroup FN] [NormedSpace ℝ FN] [FiniteDimensional ℝ FN]
  [TopologicalSpace GN] {IN : ModelWithCorners ℝ FN GN} [IN.Boundaryless]
  [TopologicalSpace N] [ChartedSpace GN N] [IsManifold IN ∞ N]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private theorem exists_perturbation_data [Nonempty M]
    (e : SmoothEmbedding IN 𝓘(ℝ, V) ∞ N V) {f₁ : M → N} (hf₁ : ContMDiff IM IN ∞ f₁)
    {C V₁ : Set M} (hC : IsClosed C) (hV₁ : IsOpen V₁) (hCV₁ : C ⊆ V₁)
    {D₁ : Set (N × N)} (hD₁ : D₁ ∈ 𝓝ˢ (diagonal N)) :
    ∃ (O : Set V) (r : V → N) (ψ ρ : M → ℝ)
      (hH : ContMDiff (IM.prod 𝓘(ℝ, V)) IN ∞ (perturbationMap r e f₁ ψ ρ)),
      IsOpen O ∧ ContMDiffOn 𝓘(ℝ, V) IN ∞ r O ∧ (∀ y ∈ O, IsRegularPoint 𝓘(ℝ, V) IN r y) ∧
      (∀ y, r (e y) = y) ∧ ContMDiff IM 𝓘(ℝ) ∞ ψ ∧ ContMDiff IM 𝓘(ℝ) ∞ ρ ∧
      (∀ x, 0 < ρ x) ∧ (∀ x, x ∉ V₁ → ψ x = 1) ∧
      (∀ q : M × unitBallOpens V, perturbationCoord e f₁ ψ ρ q ∈ O) ∧
      ∀ v : unitBallOpens V, ∃ K : (⟨f₁, hf₁.continuous⟩ : C(M, N)).HomotopyRel
          ⟨fun x ↦ perturbationMap r e f₁ ψ ρ (x, v),
            hH.continuous.comp (continuous_id.prodMk continuous_const)⟩ C,
          ∀ t x, (K (t, x), f₁ x) ∈ D₁ := by
  have : Nonempty N := ⟨f₁ (Classical.arbitrary M)⟩
  obtain ⟨O, hO, heO, -, r, hrO, hrreg, hre⟩ :=
    e.exists_contMDiffOn_retraction isOpen_univ (subset_univ _)
  let Ω : Set (M × V) := {p | e (f₁ p.1) + p.2 ∈ O ∧ (r (e (f₁ p.1) + p.2), f₁ p.1) ∈ interior D₁}
  have hΩ (x : M) : Ω ∈ 𝓝 (x, (0 : V)) := by
    have hefx : e (f₁ x) + (0 : V) ∈ O := by simpa using heO (mem_range_self (f₁ x))
    have hadd : ContinuousAt (fun p : M × V ↦ e (f₁ p.1) + p.2) (x, 0) :=
      ((e.contMDiff.continuous.comp (hf₁.continuous.comp continuous_fst)).add
        continuous_snd).continuousAt
    have hr_at : ContinuousAt (fun p : M × V ↦ r (e (f₁ p.1) + p.2)) (x, 0) :=
      Tendsto.comp (hrO.continuousOn.continuousAt (hO.mem_nhds hefx)) hadd
    have hr_cont : ContinuousAt (fun p : M × V ↦ (r (e (f₁ p.1) + p.2), f₁ p.1)) (x, 0) :=
      hr_at.prodMk (hf₁.continuous.comp continuous_fst).continuousAt
    refine inter_mem (hadd.preimage_mem_nhds (hO.mem_nhds hefx))
      (hr_cont.preimage_mem_nhds (isOpen_interior.mem_nhds ?_))
    simpa [hre (f₁ x)] using subset_interior_iff_mem_nhdsSet.2 hD₁ (mem_diagonal (f₁ x))
  obtain ⟨ρ, hρpos, -, hρΩ⟩ := exists_contMDiffMap_closedBall_subset (I := IM) hΩ
    (ε := fun _ ↦ (1 : ℝ)) continuous_const.lowerSemicontinuous (fun _ ↦ zero_lt_one)
  obtain ⟨ψ, hψC, hψV₁, hψIcc⟩ := exists_contMDiffMap_zero_one_of_isClosed IM (n := ⊤)
    hC hV₁.isClosed_compl (disjoint_compl_right_iff_subset.2 hCV₁)
  have hΦ_ball (q : M × unitBallOpens V) :
      ψ q.1 • ((ψ q.1 * ρ q.1) • (q.2 : V)) ∈ Metric.closedBall (0 : V) (ρ q.1) :=
    perturbation_smul_mem_closedBall (hψIcc q.1) (hρpos q.1) q.2
  have hO_mem (q : M × unitBallOpens V) : perturbationCoord e f₁ ψ ρ q ∈ O :=
    (hρΩ q.1 _ (hΦ_ball q)).1
  have hH : ContMDiff (IM.prod 𝓘(ℝ, V)) IN ∞ (perturbationMap r e f₁ ψ ρ) :=
    hrO.comp_contMDiff (contMDiff_perturbationCoord e.contMDiff hf₁ ψ.contMDiff ρ.contMDiff) hO_mem
  refine ⟨O, r, ψ, ρ, hH, hO, hrO, hrreg, hre, ψ.contMDiff, ρ.contMDiff, hρpos,
    fun _ hx ↦ hψV₁ hx, hO_mem, fun v ↦ ?_⟩
  have htv (t : unitInterval) : (t : ℝ) • (v : V) ∈ unitBallOpens V := by
    change (t : ℝ) • (v : V) ∈ Metric.ball (0 : V) 1
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg t.2.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) t.2.2).trans_lt (mem_ball_zero_iff.1 v.2)
  let K : (⟨f₁, hf₁.continuous⟩ : C(M, N)).HomotopyRel
      ⟨fun x ↦ perturbationMap r e f₁ ψ ρ (x, v),
        hH.continuous.comp (continuous_id.prodMk continuous_const)⟩ C :=
    { toFun p := perturbationMap r e f₁ ψ ρ (p.2, ⟨(p.1 : ℝ) • (v : V), htv p.1⟩)
      continuous_toFun := hH.continuous.comp
        (continuous_snd.prodMk ((continuous_subtype_val.comp continuous_fst).smul
          continuous_const |>.subtype_mk _))
      map_zero_left x := by simp [perturbationMap, perturbationCoord, hre (f₁ x)]
      map_one_left x := by simp [perturbationMap, perturbationCoord]
      prop' t x hx := by simp [perturbationMap, perturbationCoord, hψC hx, hre (f₁ x)] }
  exact ⟨K, fun t x ↦ interior_subset (hρΩ x _ (hΦ_ball (x, ⟨(t : ℝ) • (v : V), htv t⟩))).2⟩

/-- **Smooth relative transversality into an embedded target.** Let `e : N → V` be a smooth
embedding into a finite-dimensional real normed space. A smooth map `f : M → N` from a σ-compact
Hausdorff boundaryless manifold `M` that is transverse to a smooth map `g : Z → N` on an open
neighbourhood `V₁` of a closed set `C ⊆ M` can be perturbed relative to `C`, within any prescribed
diagonal neighbourhood `D₁` of `N`, to a smooth map globally transverse to `g`. -/
theorem exists_contMDiff_isTransverse_homotopyRel_of_contMDiff [BoundarylessManifold IM M]
    {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
    [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ}
    [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold IZ ∞ Z] [BoundarylessManifold IZ Z]
    [LindelofSpace Z]
    (e : SmoothEmbedding IN 𝓘(ℝ, V) ∞ N V) {f : M → N} (hf : ContMDiff IM IN ∞ f)
    {g : Z → N} (hg : ContMDiff IZ IN ∞ g) {C V₁ : Set M} (hC : IsClosed C) (hV₁ : IsOpen V₁)
    (hCV₁ : C ⊆ V₁) (hftrans : IsTransverseOn IM IZ IN f g V₁)
    {D₁ : Set (N × N)} (hD₁ : D₁ ∈ 𝓝ˢ (diagonal N)) :
    ∃ f' : C(M, N), ContMDiff IM IN ∞ f' ∧ IsTransverse IM IZ IN f' g ∧
      ∃ K : (⟨f, hf.continuous⟩ : C(M, N)).HomotopyRel f' C, ∀ t x, (K (t, x), f x) ∈ D₁ := by
  by_cases hM : Nonempty M
  · obtain ⟨O, r, ψ, ρ, hH, hO, hrO, hrreg, hre, hψ, hρ, hρpos, hψV₁, hO_mem, hK⟩ :=
      exists_perturbation_data e hf hC hV₁ hCV₁ hD₁
    have hH_all : IsTransverse (IM.prod 𝓘(ℝ, V)) IZ IN (perturbationMap r e f ψ ρ) g :=
      isTransverse_def.2 fun ⟨x, v⟩ z ↦
        isTransverseAt_perturbationMap hO hrO hrreg e.contMDiff hre hf hψ hρ hρpos hψV₁ hO_mem
          (h := fun y : M ↦ y) contMDiff_id (fun hx ↦ hftrans.isTransverseAt hx z)
    obtain ⟨v₀, hv₀⟩ := (dense_isTransverse_slice hH hg hH_all (by simp)).nonempty
    obtain ⟨K, hKD₁⟩ := hK v₀
    exact ⟨⟨fun x ↦ perturbationMap r e f ψ ρ (x, v₀),
        hH.continuous.comp (continuous_id.prodMk continuous_const)⟩,
      hH.comp (contMDiff_id.prodMk contMDiff_const), hv₀, K, hKD₁⟩
  · have : IsEmpty M := not_nonempty_iff.1 hM
    exact ⟨⟨f, hf.continuous⟩, hf, isTransverse_def.2 fun x ↦ isEmptyElim x,
      .refl _ C, fun _ x ↦ isEmptyElim x⟩

/-- **Smooth facewise relative transversality on a half-space manifold into an embedded target.**
For a σ-compact Hausdorff smooth manifold `M` modelled on `𝓡∂ (m + 1)`, a smooth map `f : M → N`
into a smoothly embedded target `e : N → V` that is transverse to `g : Z → N` on `V₁ ∩ interior M`
and along `∂M ∩ V₁` can be perturbed relative to `C ⊆ V₁`, within `D₁ ∈ 𝓝ˢ (diagonal N)`, to a
smooth map globally transverse to `g` both on `M` and along `∂M`. -/
theorem exists_contMDiff_isTransverse_homotopyRel_halfSpace_of_contMDiff {m : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (m + 1)) M]
    [IsManifold (𝓡∂ (m + 1)) ∞ M] [SigmaCompactSpace M] [T2Space M]
    {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
    [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ}
    [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold IZ ∞ Z] [BoundarylessManifold IZ Z]
    [LindelofSpace Z]
    (e : SmoothEmbedding IN 𝓘(ℝ, V) ∞ N V) {f : M → N} (hf : ContMDiff (𝓡∂ (m + 1)) IN ∞ f)
    {g : Z → N} (hg : ContMDiff IZ IN ∞ g) {C V₁ : Set M} (hC : IsClosed C) (hV₁ : IsOpen V₁)
    (hCV₁ : C ⊆ V₁) (hfint : IsTransverseOn (𝓡∂ (m + 1)) IZ IN f g (V₁ ∩ (𝓡∂ (m + 1)).interior M))
    (hfbdy : IsTransverseOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ IN
      (f ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g (Subtype.val ⁻¹' V₁))
    {D₁ : Set (N × N)} (hD₁ : D₁ ∈ 𝓝ˢ (diagonal N)) :
    ∃ f' : C(M, N), ContMDiff (𝓡∂ (m + 1)) IN ∞ f' ∧
      IsTransverse (𝓡∂ (m + 1)) IZ IN f' g ∧
      IsTransverse 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ IN
        (f' ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g ∧
      ∃ K : (⟨f, hf.continuous⟩ : C(M, N)).HomotopyRel f' C, ∀ t x, (K (t, x), f x) ∈ D₁ := by
  have : SecondCountableTopology (EuclideanHalfSpace (m + 1)) :=
    (𝓡∂ (m + 1)).secondCountableTopology
  have : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_lindelof (EuclideanHalfSpace (m + 1)) M
  have : IsManifold (𝓡∂ (m + 1)) 1 M := .of_le (WithTop.coe_le_coe.2 le_top)
  have := isManifold_boundary (n := m) (k := ∞) M (by simp)
  by_cases hM : Nonempty M
  · obtain ⟨O, r, ψ, ρ, hH, hO, hrO, hrreg, hre, hψ, hρ, hρpos, hψV₁, hO_mem, hK⟩ :=
      exists_perturbation_data e hf hC hV₁ hCV₁ hD₁
    have hH_int : IsTransverseOn ((𝓡∂ (m + 1)).prod 𝓘(ℝ, V)) IZ IN
        (perturbationMap r e f ψ ρ) g (((𝓡∂ (m + 1)).interior M) ×ˢ univ) :=
      isTransverseOn_def.2 fun ⟨x, v⟩ hx z ↦
        isTransverseAt_perturbationMap hO hrO hrreg e.contMDiff hre hf hψ hρ hρpos hψV₁ hO_mem
          (h := fun y : M ↦ y) contMDiff_id (fun hxV₁ ↦ hfint.isTransverseAt ⟨hxV₁, hx.1⟩ z)
    have hH_bdy : IsTransverse (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, V)) IZ IN
        (fun q : ↥((𝓡∂ (m + 1)).boundary M) × unitBallOpens V ↦
          perturbationMap r e f ψ ρ (q.1, q.2)) g :=
      isTransverse_def.2 fun ⟨p, v⟩ z ↦
        isTransverseAt_perturbationMap hO hrO hrreg e.contMDiff hre hf hψ hρ hρpos hψV₁ hO_mem
          (isSmoothEmbedding_subtypeVal_boundary (n := m) (k := ∞) M (by simp)).contMDiff
          (fun hpV₁ ↦ hfbdy.isTransverseAt hpV₁ z)
    obtain ⟨v₀, hv₀_int, hv₀_bdy⟩ :=
      (dense_isTransverse_slice_halfSpace hH hg hH_int hH_bdy (by simp)).nonempty
    obtain ⟨K, hKD₁⟩ := hK v₀
    exact ⟨⟨fun x ↦ perturbationMap r e f ψ ρ (x, v₀),
        hH.continuous.comp (continuous_id.prodMk continuous_const)⟩,
      hH.comp (contMDiff_id.prodMk contMDiff_const), hv₀_int, hv₀_bdy, K, hKD₁⟩
  · have : IsEmpty M := not_nonempty_iff.1 hM
    exact ⟨⟨f, hf.continuous⟩, hf, isTransverse_def.2 fun x ↦ isEmptyElim x,
      isTransverse_def.2 fun p ↦ isEmptyElim p.1, .refl _ C, fun _ x ↦ isEmptyElim x⟩

end Perturbation

end SmoothEmbedding

end TauCeti

namespace ContinuousMap

open TauCeti

section Reduction

private theorem isTransverseAt_openTarget_iff
    {FP GP P : Type*} [NormedAddCommGroup FP] [NormedSpace ℝ FP]
    [TopologicalSpace GP] {JP : ModelWithCorners ℝ FP GP}
    [TopologicalSpace P] [ChartedSpace GP P] [IsManifold JP ∞ P] [BoundarylessManifold JP P]
    {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
    {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]
    (φ : letI := BoundarylessModel.interiorChartedSpace JP (M := P)
      P ≃ₘ^∞⟮JP, 𝓘(ℝ, FP)⟯ BoundarylessModel JP P)
    (W : Opens (BoundarylessModel JP P)) {g : Z → P} (hg : ContMDiff IZ JP ∞ g)
    {a : X → W} {x : X}
    (ha : letI := BoundarylessModel.interiorChartedSpace JP (M := P)
      MDifferentiableAt IX 𝓘(ℝ, FP) a x) :
    letI := BoundarylessModel.interiorChartedSpace JP (M := P)
    let Z' : Opens Z := ⟨(φ ∘ g) ⁻¹' (W : Set (BoundarylessModel JP P)),
      W.isOpen.preimage (φ.continuous.comp hg.continuous)⟩
    (∀ z : Z, IsTransverseAt IX IZ JP (fun y ↦ φ.symm (a y).1) g x z) ↔
      (∀ z' : Z', IsTransverseAt IX IZ 𝓘(ℝ, FP) a (fun z ↦ ⟨φ (g z.1), z.2⟩) x z') := by
  let := BoundarylessModel.interiorChartedSpace JP (M := P)
  intro Z'
  let g' : Z' → W := fun z ↦ ⟨φ (g z.1), z.2⟩
  have hn0 : (∞ : ℕ∞ω) ≠ 0 := by simp
  have had : MDifferentiableAt IX JP (fun y ↦ φ.symm (a y).1) x :=
    (φ.symm.contMDiff.mdifferentiableAt hn0).comp x
      ((contMDiff_subtype_val.mdifferentiableAt hn0).comp x ha)
  have hstep (z' : Z') : IsTransverseAt IX IZ JP (fun y ↦ φ.symm (a y).1) g x z'.1 ↔
      IsTransverseAt IX IZ 𝓘(ℝ, FP) a g' x z' := by
    rw [isTransverseAt_comm, ← isTransverseAt_comp_subtype_val_iff (U := Z'), isTransverseAt_comm,
      ← isTransverseAt_diffeomorph_comp_iff φ hn0 had
        ((hg.comp contMDiff_subtype_val).mdifferentiableAt hn0),
      show φ ∘ (fun y ↦ φ.symm (a y).1) = (Subtype.val : W → BoundarylessModel JP P) ∘ a from
        funext fun y ↦ φ.right_inv (a y).1,
      show φ ∘ (g ∘ (Subtype.val : Z' → Z)) = (Subtype.val : W → BoundarylessModel JP P) ∘ g' from
        rfl]
    exact isTransverseAt_subtype_val_comp_iff (IN := 𝓘(ℝ, FP)) (N := BoundarylessModel JP P)
      (U := W)
  refine ⟨fun h z' ↦ (hstep z').1 (h z'.1), fun h z ↦ ?_⟩
  by_cases hz : φ (g z) ∈ W
  · exact (hstep ⟨z, hz⟩).2 (h ⟨z, hz⟩)
  · refine .of_ne fun heq ↦ hz ?_
    have hφeq : φ (g z) = (a x).1 := by simpa [φ.right_inv] using congrArg φ heq.symm
    exact hφeq ▸ (a x).2

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M] [SigmaCompactSpace M] [T2Space M]
  {FP GP P : Type*} [NormedAddCommGroup FP] [NormedSpace ℝ FP] [FiniteDimensional ℝ FP]
  [TopologicalSpace GP] {JP : ModelWithCorners ℝ FP GP}
  [TopologicalSpace P] [ChartedSpace GP P] [IsManifold JP ∞ P] [BoundarylessManifold JP P]
  [T2Space P]

private theorem exists_opens_smoothing_reduction (f : C(M, P)) (hf : IsCompact (closure (range f)))
    {C U : Set M} (hC : IsClosed C) (hU : U ∈ 𝓝ˢ C) (hfU : ContMDiffOn IM JP ∞ f U)
    {D : Set (P × P)} (hD : D ∈ 𝓝ˢ (diagonal P)) :
    letI := BoundarylessModel.interiorChartedSpace JP (M := P)
    let φ : P ≃ₘ^∞⟮JP, 𝓘(ℝ, FP)⟯ BoundarylessModel JP P :=
      BoundarylessModel.interiorDiffeomorph JP (M := P) ∞
    ∃ (W : Opens (BoundarylessModel JP P)) (k : ℕ)
      (_ : SmoothEmbedding 𝓘(ℝ, FP) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ W (EuclideanSpace ℝ (Fin k)))
      (V₁ : Set M) (D₁W : Set (W × W)) (f₁ : C(M, W)),
      IsOpen V₁ ∧ C ⊆ V₁ ∧ V₁ ⊆ interior U ∧ D₁W ∈ 𝓝ˢ (diagonal W) ∧
      ContMDiff IM 𝓘(ℝ, FP) ∞ f₁ ∧ EqOn (fun x ↦ φ.symm (f₁ x).1) f V₁ ∧
      ∀ (f₂ : C(M, W)), ContMDiff IM 𝓘(ℝ, FP) ∞ f₂ →
        (∃ K₂ : f₁.HomotopyRel f₂ C, ∀ t x, (K₂ (t, x), f₁ x) ∈ D₁W) →
        ∃ f' : C(M, P), (⇑f' = fun x ↦ φ.symm (f₂ x).1) ∧ ContMDiff IM JP ∞ f' ∧
          ∃ K : f.HomotopyRel f' C, ∀ t x, (K (t, x), f x) ∈ D := by
  let P' := BoundarylessModel JP P
  let := BoundarylessModel.interiorChartedSpace JP (M := P)
  have : T2Space P' := inferInstanceAs (T2Space P)
  let φ : P ≃ₘ^∞⟮JP, 𝓘(ℝ, FP)⟯ P' := BoundarylessModel.interiorDiffeomorph JP (M := P) ∞
  have hfc : IsCompact (closure (range (φ ∘ f))) :=
    (hf.image φ.continuous).closure_of_subset (by rw [range_comp]; exact image_mono subset_closure)
  obtain ⟨W, hW, hWc, k, ⟨e⟩⟩ := hfc.exists_opens_nonempty_smoothEmbedding_euclidean (I := 𝓘(ℝ, FP))
  let L := closure (W : Set P')
  have : CompactSpace L := isCompact_iff_compactSpace.1 hWc
  let jL : C(L, P) := ⟨fun y ↦ φ.symm y.1, φ.symm.continuous.comp continuous_subtype_val⟩
  obtain ⟨D₁L, hD₁L, hD₁LD⟩ :=
    exists_nhdsSet_diagonal_comp_subset (preimage_prodMap_mem_nhdsSet_diagonal jL.continuous hD)
  let ιWL : C(W, L) := ⟨fun w ↦ ⟨w.1, subset_closure w.2⟩, continuous_subtype_val.subtype_mk _⟩
  have hD₁W : Prod.map ιWL ιWL ⁻¹' D₁L ∈ 𝓝ˢ (diagonal W) :=
    preimage_prodMap_mem_nhdsSet_diagonal ιWL.continuous hD₁L
  have : LocallyCompactSpace HM := IM.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace HM M
  obtain ⟨V₁, hV₁, hCV₁, hV₁U⟩ :=
    normal_exists_closure_subset hC isOpen_interior (subset_interior_iff_mem_nhdsSet.2 hU)
  let f₀ : C(M, W) := ⟨fun x ↦ ⟨φ (f x), hW (subset_closure (mem_range_self x))⟩,
    (φ.continuous.comp f.continuous).subtype_mk _⟩
  have hf₀U : ContMDiffOn IM 𝓘(ℝ, FP) ∞ f₀ U :=
    (TauCeti.ContMDiffOn.subtypeVal_comp_iff W f₀ U).1 (φ.contMDiff.comp_contMDiffOn hfU)
  obtain ⟨f₁, hf₁, K₁, hK₁D⟩ := e.exists_contMDiff_homotopyRel ⊤ f₀ isClosed_closure
    (isOpen_interior.mem_nhdsSet.2 hV₁U) (hf₀U.mono interior_subset) hD₁W
  let jW : C(W, P) := jL.comp ιWL
  have hjf₀ : jW.comp f₀ = f := ContinuousMap.ext fun x ↦ φ.left_inv (f x)
  have hEqV₁ : EqOn (fun x ↦ φ.symm (f₁ x).1) f V₁ := fun x hx ↦
    (congrArg jW (K₁.fst_eq_snd (subset_closure hx)).symm).trans (φ.left_inv (f x))
  refine ⟨W, k, e, V₁, _, f₁, hV₁, hCV₁, subset_closure.trans hV₁U, hD₁W, hf₁, hEqV₁,
    fun f₂ hf₂ ⟨K₂, hK₂D⟩ ↦ ?_⟩
  let K₁' : f₀.HomotopyRel f₁ C :=
    { toHomotopy := K₁.toHomotopy, prop' t x hx := K₁.prop t x (hCV₁.trans subset_closure hx) }
  let K_W : f₀.HomotopyRel f₂ C := K₁'.trans K₂
  refine ⟨jW.comp f₂, rfl, φ.symm.contMDiff.comp (contMDiff_subtype_val.comp hf₂),
    (K_W.compContinuousMap jW).cast hjf₀ rfl, fun t x ↦ ?_⟩
  change (jL (ιWL (K_W (t, x))), f x) ∈ D
  rw [← φ.left_inv (f x)]
  change (jL (ιWL (K_W (t, x))), jL (ιWL (f₀ x))) ∈ D
  rw [show K_W (t, x) = (K₁'.trans K₂) (t, x) from rfl, HomotopyRel.trans_apply]
  split_ifs with ht
  · exact hD₁LD (hK₁D _ x) (subset_of_mem_nhdsSet hD₁L (mem_diagonal (ιWL (f₀ x))))
  · exact hD₁LD (hK₂D _ x) (by simpa using hK₁D 1 x)

end Reduction

section Boundaryless

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M] [BoundarylessManifold IM M]
  [SigmaCompactSpace M] [T2Space M]
  {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ}
  [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold IZ ∞ Z] [BoundarylessManifold IZ Z]
  [LindelofSpace Z]
  {FP GP P : Type*} [NormedAddCommGroup FP] [NormedSpace ℝ FP] [FiniteDimensional ℝ FP]
  [TopologicalSpace GP] {JP : ModelWithCorners ℝ FP GP}
  [TopologicalSpace P] [ChartedSpace GP P] [IsManifold JP ∞ P] [BoundarylessManifold JP P]
  [T2Space P]

/-- **Relative transversality with relatively compact image and diagonal control.** A continuous map
`f : C(M, P)` from a σ-compact Hausdorff boundaryless manifold `M` into a Hausdorff boundaryless
manifold `P`, whose image has compact closure and which is smooth and transverse to a smooth map
`g : Z → P` on a neighbourhood `U` of a closed set `C ⊆ M`, is homotopic relative to `C` to a smooth
map `f'` globally transverse to `g`, by a homotopy `K` satisfying `(K (t, x), f x) ∈ D` for any
prescribed neighbourhood `D` of the diagonal of `P`. -/
theorem exists_contMDiff_isTransverse_homotopyRel_of_isCompact_closure_range
    (f : C(M, P)) (hf : IsCompact (closure (range f))) {g : Z → P} (hg : ContMDiff IZ JP ∞ g)
    {C U : Set M} (hC : IsClosed C) (hU : U ∈ 𝓝ˢ C) (hfU : ContMDiffOn IM JP ∞ f U)
    (hftrans : IsTransverseOn IM IZ JP f g U) {D : Set (P × P)} (hD : D ∈ 𝓝ˢ (diagonal P)) :
    ∃ f' : C(M, P), ContMDiff IM JP ∞ f' ∧ IsTransverse IM IZ JP f' g ∧
      ∃ K : f.HomotopyRel f' C, ∀ t x, (K (t, x), f x) ∈ D := by
  let := BoundarylessModel.interiorChartedSpace JP (M := P)
  let φ : P ≃ₘ^∞⟮JP, 𝓘(ℝ, FP)⟯ BoundarylessModel JP P :=
    BoundarylessModel.interiorDiffeomorph JP (M := P) ∞
  obtain ⟨W, k, e, V₁, D₁W, f₁, hV₁, hCV₁, hV₁U, hD₁W, hf₁, hEqV₁, hfinish⟩ :=
    exists_opens_smoothing_reduction f hf hC hU hfU hD
  have : IsManifold IZ 1 Z := .of_le (WithTop.coe_le_coe.2 le_top)
  have := secondCountableTopology_of_boundaryless_lindelof IZ (Z := Z)
  let Z' : Opens Z := ⟨(φ ∘ g) ⁻¹' (W : Set (BoundarylessModel JP P)),
    W.isOpen.preimage (φ.continuous.comp hg.continuous)⟩
  let g' : Z' → W := fun z ↦ ⟨φ (g z.1), z.2⟩
  have hg' : ContMDiff IZ 𝓘(ℝ, FP) ∞ g' :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff W g').1
      (φ.contMDiff.comp (hg.comp contMDiff_subtype_val))
  have hf₁_on : IsTransverseOn IM IZ JP (fun x ↦ φ.symm (f₁ x).1) g V₁ :=
    (hftrans.mono (hV₁U.trans interior_subset)).congr_of_isOpen hV₁ hEqV₁
  have hf₁W : IsTransverseOn IM IZ 𝓘(ℝ, FP) f₁ g' V₁ :=
    isTransverseOn_def.2 fun x hx z' ↦ (isTransverseAt_openTarget_iff φ W hg
      (hf₁.mdifferentiableAt (by simp))).1 (fun z ↦ hf₁_on.isTransverseAt hx z) z'
  obtain ⟨f₂, hf₂, hf₂trans, K₂, hK₂D⟩ :=
    e.exists_contMDiff_isTransverse_homotopyRel_of_contMDiff hf₁ hg' hC hV₁ hCV₁ hf₁W hD₁W
  obtain ⟨f', hf'eq, hf', K, hKD⟩ := hfinish f₂ hf₂ ⟨K₂, hK₂D⟩
  refine ⟨f', hf', isTransverse_def.2 fun x ↦ ?_, K, hKD⟩
  rw [hf'eq]
  exact (isTransverseAt_openTarget_iff φ W hg (hf₂.mdifferentiableAt (by simp))).2
    fun z' ↦ hf₂trans.isTransverseAt x z'

/-- **Relative transversality with relatively compact image.** Specializing
`exists_contMDiff_isTransverse_homotopyRel_of_isCompact_closure_range` to `D = univ` yields a
smooth map transverse to `g` and homotopic to `f` relative to `C`. -/
theorem exists_contMDiff_isTransverse_homotopicRel_of_isCompact_closure_range
    (f : C(M, P)) (hf : IsCompact (closure (range f))) {g : Z → P} (hg : ContMDiff IZ JP ∞ g)
    {C U : Set M} (hC : IsClosed C) (hU : U ∈ 𝓝ˢ C) (hfU : ContMDiffOn IM JP ∞ f U)
    (hftrans : IsTransverseOn IM IZ JP f g U) :
    ∃ f' : C(M, P), ContMDiff IM JP ∞ f' ∧ IsTransverse IM IZ JP f' g ∧ f.HomotopicRel f' C := by
  obtain ⟨f', hf', htr, K, -⟩ :=
    f.exists_contMDiff_isTransverse_homotopyRel_of_isCompact_closure_range hf hg hC hU hfU hftrans
      univ_mem
  exact ⟨f', hf', htr, ⟨K⟩⟩

/-- **Global transversality up to homotopy with relatively compact image.** Every continuous map
with relatively compact image from a σ-compact Hausdorff boundaryless manifold into a Hausdorff
boundaryless manifold is homotopic to a smooth map transverse to `g`. -/
theorem exists_contMDiff_isTransverse_homotopic_of_isCompact_closure_range
    (f : C(M, P)) (hf : IsCompact (closure (range f))) {g : Z → P} (hg : ContMDiff IZ JP ∞ g) :
    ∃ f' : C(M, P), ContMDiff IM JP ∞ f' ∧ IsTransverse IM IZ JP f' g ∧ f.Homotopic f' := by
  obtain ⟨f', hf', htr, hhom⟩ :=
    f.exists_contMDiff_isTransverse_homotopicRel_of_isCompact_closure_range (IM := IM) hf hg
      isClosed_empty (U := ∅) (by simp) (contMDiffOn_empty (I' := JP)) isTransverseOn_empty
  exact ⟨f', hf', htr, hhom.homotopic⟩

/-- **Relative transversality with diagonal control into a compact manifold.** A continuous map `f`
from a σ-compact Hausdorff boundaryless manifold into a compact Hausdorff boundaryless manifold `P`,
smooth and transverse to `g : Z → P` on a neighbourhood `U` of a closed set `C`, is homotopic
relative to `C` within `D ∈ 𝓝ˢ (diagonal P)` to a smooth map globally transverse to `g`. -/
theorem exists_contMDiff_isTransverse_homotopyRel [CompactSpace P]
    (f : C(M, P)) {g : Z → P} (hg : ContMDiff IZ JP ∞ g) {C U : Set M} (hC : IsClosed C)
    (hU : U ∈ 𝓝ˢ C) (hfU : ContMDiffOn IM JP ∞ f U) (hftrans : IsTransverseOn IM IZ JP f g U)
    {D : Set (P × P)} (hD : D ∈ 𝓝ˢ (diagonal P)) :
    ∃ f' : C(M, P), ContMDiff IM JP ∞ f' ∧ IsTransverse IM IZ JP f' g ∧
      ∃ K : f.HomotopyRel f' C, ∀ t x, (K (t, x), f x) ∈ D :=
  f.exists_contMDiff_isTransverse_homotopyRel_of_isCompact_closure_range isClosed_closure.isCompact
    hg hC hU hfU hftrans hD

/-- **Relative transversality into a compact manifold.** A continuous map `f` from a σ-compact
Hausdorff boundaryless manifold into a compact Hausdorff boundaryless manifold `P`, smooth and
transverse to `g : Z → P` on a neighbourhood `U` of a closed set `C`, is homotopic relative to `C`
to a smooth map globally transverse to `g`. -/
theorem exists_contMDiff_isTransverse_homotopicRel [CompactSpace P]
    (f : C(M, P)) {g : Z → P} (hg : ContMDiff IZ JP ∞ g) {C U : Set M} (hC : IsClosed C)
    (hU : U ∈ 𝓝ˢ C) (hfU : ContMDiffOn IM JP ∞ f U) (hftrans : IsTransverseOn IM IZ JP f g U) :
    ∃ f' : C(M, P), ContMDiff IM JP ∞ f' ∧ IsTransverse IM IZ JP f' g ∧ f.HomotopicRel f' C :=
  f.exists_contMDiff_isTransverse_homotopicRel_of_isCompact_closure_range isClosed_closure.isCompact
    hg hC hU hfU hftrans

/-- **Global transversality up to homotopy into a compact manifold.** Every continuous map from a
σ-compact Hausdorff boundaryless manifold into a compact Hausdorff boundaryless manifold is
homotopic to a smooth map transverse to `g`. -/
theorem exists_contMDiff_isTransverse_homotopic [CompactSpace P]
    (f : C(M, P)) {g : Z → P} (hg : ContMDiff IZ JP ∞ g) :
    ∃ f' : C(M, P), ContMDiff IM JP ∞ f' ∧ IsTransverse IM IZ JP f' g ∧ f.Homotopic f' :=
  f.exists_contMDiff_isTransverse_homotopic_of_isCompact_closure_range isClosed_closure.isCompact hg

/-- **Relative transversality with diagonal control from a compact manifold.** When the source `M`
is compact, no compactness hypothesis on the Hausdorff boundaryless target `P` is needed. -/
theorem exists_contMDiff_isTransverse_homotopyRel_of_compactSpace [CompactSpace M]
    (f : C(M, P)) {g : Z → P} (hg : ContMDiff IZ JP ∞ g) {C U : Set M} (hC : IsClosed C)
    (hU : U ∈ 𝓝ˢ C) (hfU : ContMDiffOn IM JP ∞ f U) (hftrans : IsTransverseOn IM IZ JP f g U)
    {D : Set (P × P)} (hD : D ∈ 𝓝ˢ (diagonal P)) :
    ∃ f' : C(M, P), ContMDiff IM JP ∞ f' ∧ IsTransverse IM IZ JP f' g ∧
      ∃ K : f.HomotopyRel f' C, ∀ t x, (K (t, x), f x) ∈ D := by
  have hfc : IsCompact (range f) := isCompact_range f.continuous
  exact f.exists_contMDiff_isTransverse_homotopyRel_of_isCompact_closure_range
    (by rwa [hfc.isClosed.closure_eq]) hg hC hU hfU hftrans hD

end Boundaryless

section HalfSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (m + 1)) M]
  [IsManifold (𝓡∂ (m + 1)) ∞ M] [SigmaCompactSpace M] [T2Space M]
  {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ}
  [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold IZ ∞ Z] [BoundarylessManifold IZ Z]
  [LindelofSpace Z]
  {FP GP P : Type*} [NormedAddCommGroup FP] [NormedSpace ℝ FP] [FiniteDimensional ℝ FP]
  [TopologicalSpace GP] {JP : ModelWithCorners ℝ FP GP}
  [TopologicalSpace P] [ChartedSpace GP P] [IsManifold JP ∞ P] [BoundarylessManifold JP P]
  [T2Space P]

/-- **Facewise relative transversality on a half-space manifold with relatively compact image and
diagonal control.** Let `M` be a σ-compact Hausdorff smooth manifold with boundary modelled on
`𝓡∂ (m + 1)`. A continuous map `f : C(M, P)` with relatively compact image that is smooth on a
neighbourhood `U` of a closed set `C ⊆ M`, transverse to `g : Z → P` on `U ∩ interior M`, and whose
boundary restriction `f ∘ Subtype.val` is transverse to `g` on `∂M ∩ U`, is homotopic relative to
`C` within any `D ∈ 𝓝ˢ (diagonal P)` to a smooth map `f'` globally transverse to `g` both on `M`
and along `∂M`. -/
theorem exists_contMDiff_isTransverse_homotopyRel_halfSpace_of_isCompact_closure_range
    (f : C(M, P)) (hf : IsCompact (closure (range f))) {g : Z → P} (hg : ContMDiff IZ JP ∞ g)
    {C U : Set M} (hC : IsClosed C) (hU : U ∈ 𝓝ˢ C) (hfU : ContMDiffOn (𝓡∂ (m + 1)) JP ∞ f U)
    (hfint : IsTransverseOn (𝓡∂ (m + 1)) IZ JP f g (U ∩ (𝓡∂ (m + 1)).interior M))
    (hfbdy : IsTransverseOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ JP
      (f ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g (Subtype.val ⁻¹' U))
    {D : Set (P × P)} (hD : D ∈ 𝓝ˢ (diagonal P)) :
    ∃ f' : C(M, P), ContMDiff (𝓡∂ (m + 1)) JP ∞ f' ∧
      IsTransverse (𝓡∂ (m + 1)) IZ JP f' g ∧
      IsTransverse 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ JP
        (f' ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g ∧
      ∃ K : f.HomotopyRel f' C, ∀ t x, (K (t, x), f x) ∈ D := by
  have : SecondCountableTopology (EuclideanHalfSpace (m + 1)) :=
    (𝓡∂ (m + 1)).secondCountableTopology
  have : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_lindelof (EuclideanHalfSpace (m + 1)) M
  have : IsManifold (𝓡∂ (m + 1)) 1 M := .of_le (WithTop.coe_le_coe.2 le_top)
  have := isManifold_boundary (n := m) (k := ∞) M (by simp)
  have hbdy := (isSmoothEmbedding_subtypeVal_boundary (n := m) (k := ∞) M (by simp)).contMDiff
  let := BoundarylessModel.interiorChartedSpace JP (M := P)
  let φ : P ≃ₘ^∞⟮JP, 𝓘(ℝ, FP)⟯ BoundarylessModel JP P :=
    BoundarylessModel.interiorDiffeomorph JP (M := P) ∞
  obtain ⟨W, k, e, V₁, D₁W, f₁, hV₁, hCV₁, hV₁U, hD₁W, hf₁, hEqV₁, hfinish⟩ :=
    exists_opens_smoothing_reduction f hf hC hU hfU hD
  have : IsManifold IZ 1 Z := .of_le (WithTop.coe_le_coe.2 le_top)
  have := secondCountableTopology_of_boundaryless_lindelof IZ (Z := Z)
  let Z' : Opens Z := ⟨(φ ∘ g) ⁻¹' (W : Set (BoundarylessModel JP P)),
    W.isOpen.preimage (φ.continuous.comp hg.continuous)⟩
  let g' : Z' → W := fun z ↦ ⟨φ (g z.1), z.2⟩
  have hg' : ContMDiff IZ 𝓘(ℝ, FP) ∞ g' :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff W g').1
      (φ.contMDiff.comp (hg.comp contMDiff_subtype_val))
  have hf₁_int : IsTransverseOn (𝓡∂ (m + 1)) IZ 𝓘(ℝ, FP) f₁ g' (V₁ ∩ (𝓡∂ (m + 1)).interior M) := by
    have hopen : IsOpen (V₁ ∩ (𝓡∂ (m + 1)).interior M) :=
      hV₁.inter ((𝓡∂ (m + 1)).isOpen_interior one_ne_zero)
    have hP := (hfint.mono (inter_subset_inter_left _ (hV₁U.trans interior_subset))).congr_of_isOpen
      hopen (hEqV₁.mono inter_subset_left)
    exact isTransverseOn_def.2 fun x hx z' ↦ (isTransverseAt_openTarget_iff φ W hg
      (hf₁.mdifferentiableAt (by simp))).1 (fun z ↦ hP.isTransverseAt hx z) z'
  have hf₁_bdy : IsTransverseOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ 𝓘(ℝ, FP)
      (f₁ ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g' (Subtype.val ⁻¹' V₁) := by
    have hP := (hfbdy.mono (preimage_mono (hV₁U.trans interior_subset))).congr_of_isOpen
      (hV₁.preimage continuous_subtype_val) (fun p hp ↦ hEqV₁ hp)
    exact isTransverseOn_def.2 fun p hp z' ↦ (isTransverseAt_openTarget_iff φ W hg
      ((hf₁.comp hbdy).mdifferentiableAt (by simp))).1 (fun z ↦ hP.isTransverseAt hp z) z'
  obtain ⟨f₂, hf₂, hf₂_int, hf₂_bdy, K₂, hK₂D⟩ :=
    e.exists_contMDiff_isTransverse_homotopyRel_halfSpace_of_contMDiff hf₁ hg' hC hV₁ hCV₁
      hf₁_int hf₁_bdy hD₁W
  obtain ⟨f', hf'eq, hf', K, hKD⟩ := hfinish f₂ hf₂ ⟨K₂, hK₂D⟩
  refine ⟨f', hf', isTransverse_def.2 fun x ↦ ?_, isTransverse_def.2 fun p ↦ ?_, K, hKD⟩
  · rw [hf'eq]
    exact (isTransverseAt_openTarget_iff φ W hg (hf₂.mdifferentiableAt (by simp))).2
      fun z' ↦ hf₂_int.isTransverseAt x z'
  · change ∀ z, IsTransverseAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ JP (f' ∘ Subtype.val) g p z
    rw [hf'eq]
    exact (isTransverseAt_openTarget_iff φ W hg ((hf₂.comp hbdy).mdifferentiableAt (by simp))).2
      fun z' ↦ hf₂_bdy.isTransverseAt p z'

/-- **Facewise relative transversality on a half-space manifold with relatively compact image.** -/
theorem exists_contMDiff_isTransverse_homotopicRel_halfSpace_of_isCompact_closure_range
    (f : C(M, P)) (hf : IsCompact (closure (range f))) {g : Z → P} (hg : ContMDiff IZ JP ∞ g)
    {C U : Set M} (hC : IsClosed C) (hU : U ∈ 𝓝ˢ C) (hfU : ContMDiffOn (𝓡∂ (m + 1)) JP ∞ f U)
    (hfint : IsTransverseOn (𝓡∂ (m + 1)) IZ JP f g (U ∩ (𝓡∂ (m + 1)).interior M))
    (hfbdy : IsTransverseOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ JP
      (f ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g (Subtype.val ⁻¹' U)) :
    ∃ f' : C(M, P), ContMDiff (𝓡∂ (m + 1)) JP ∞ f' ∧
      IsTransverse (𝓡∂ (m + 1)) IZ JP f' g ∧
      IsTransverse 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ JP
        (f' ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g ∧
      f.HomotopicRel f' C := by
  obtain ⟨f', hf', hint, hbdy, K, -⟩ :=
    f.exists_contMDiff_isTransverse_homotopyRel_halfSpace_of_isCompact_closure_range hf hg hC hU
      hfU hfint hfbdy univ_mem
  exact ⟨f', hf', hint, hbdy, ⟨K⟩⟩

/-- **Global facewise transversality up to homotopy on a half-space manifold with relatively compact
image.** -/
theorem exists_contMDiff_isTransverse_homotopic_halfSpace_of_isCompact_closure_range
    (f : C(M, P)) (hf : IsCompact (closure (range f))) {g : Z → P} (hg : ContMDiff IZ JP ∞ g) :
    ∃ f' : C(M, P), ContMDiff (𝓡∂ (m + 1)) JP ∞ f' ∧
      IsTransverse (𝓡∂ (m + 1)) IZ JP f' g ∧
      IsTransverse 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ JP
        (f' ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g ∧
      f.Homotopic f' := by
  obtain ⟨f', hf', hint, hbdy, hhom⟩ :=
    f.exists_contMDiff_isTransverse_homotopicRel_halfSpace_of_isCompact_closure_range (m := m) hf hg
      isClosed_empty (U := ∅) (by simp) (contMDiffOn_empty (I' := JP))
      (by simp) (by simp)
  exact ⟨f', hf', hint, hbdy, hhom.homotopic⟩

/-- **Facewise relative transversality on a half-space manifold with diagonal control into a compact
manifold.** -/
theorem exists_contMDiff_isTransverse_homotopyRel_halfSpace [CompactSpace P]
    (f : C(M, P)) {g : Z → P} (hg : ContMDiff IZ JP ∞ g) {C U : Set M} (hC : IsClosed C)
    (hU : U ∈ 𝓝ˢ C) (hfU : ContMDiffOn (𝓡∂ (m + 1)) JP ∞ f U)
    (hfint : IsTransverseOn (𝓡∂ (m + 1)) IZ JP f g (U ∩ (𝓡∂ (m + 1)).interior M))
    (hfbdy : IsTransverseOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ JP
      (f ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g (Subtype.val ⁻¹' U))
    {D : Set (P × P)} (hD : D ∈ 𝓝ˢ (diagonal P)) :
    ∃ f' : C(M, P), ContMDiff (𝓡∂ (m + 1)) JP ∞ f' ∧
      IsTransverse (𝓡∂ (m + 1)) IZ JP f' g ∧
      IsTransverse 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ JP
        (f' ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g ∧
      ∃ K : f.HomotopyRel f' C, ∀ t x, (K (t, x), f x) ∈ D :=
  f.exists_contMDiff_isTransverse_homotopyRel_halfSpace_of_isCompact_closure_range
    isClosed_closure.isCompact hg hC hU hfU hfint hfbdy hD

/-- **Facewise relative transversality on a half-space manifold into a compact manifold.** -/
theorem exists_contMDiff_isTransverse_homotopicRel_halfSpace [CompactSpace P]
    (f : C(M, P)) {g : Z → P} (hg : ContMDiff IZ JP ∞ g) {C U : Set M} (hC : IsClosed C)
    (hU : U ∈ 𝓝ˢ C) (hfU : ContMDiffOn (𝓡∂ (m + 1)) JP ∞ f U)
    (hfint : IsTransverseOn (𝓡∂ (m + 1)) IZ JP f g (U ∩ (𝓡∂ (m + 1)).interior M))
    (hfbdy : IsTransverseOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ JP
      (f ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g (Subtype.val ⁻¹' U)) :
    ∃ f' : C(M, P), ContMDiff (𝓡∂ (m + 1)) JP ∞ f' ∧
      IsTransverse (𝓡∂ (m + 1)) IZ JP f' g ∧
      IsTransverse 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ JP
        (f' ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g ∧
      f.HomotopicRel f' C :=
  f.exists_contMDiff_isTransverse_homotopicRel_halfSpace_of_isCompact_closure_range
    isClosed_closure.isCompact hg hC hU hfU hfint hfbdy

/-- **Global facewise transversality up to homotopy on a half-space manifold into a compact
manifold.** -/
theorem exists_contMDiff_isTransverse_homotopic_halfSpace [CompactSpace P]
    (f : C(M, P)) {g : Z → P} (hg : ContMDiff IZ JP ∞ g) :
    ∃ f' : C(M, P), ContMDiff (𝓡∂ (m + 1)) JP ∞ f' ∧
      IsTransverse (𝓡∂ (m + 1)) IZ JP f' g ∧
      IsTransverse 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ JP
        (f' ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g ∧
      f.Homotopic f' :=
  f.exists_contMDiff_isTransverse_homotopic_halfSpace_of_isCompact_closure_range
    isClosed_closure.isCompact hg

/-- **Facewise relative transversality on a compact half-space manifold with diagonal control.**
When the half-space source `M` is compact, no compactness hypothesis on the Hausdorff boundaryless
target `P` is needed. -/
theorem exists_contMDiff_isTransverse_homotopyRel_halfSpace_of_compactSpace [CompactSpace M]
    (f : C(M, P)) {g : Z → P} (hg : ContMDiff IZ JP ∞ g) {C U : Set M} (hC : IsClosed C)
    (hU : U ∈ 𝓝ˢ C) (hfU : ContMDiffOn (𝓡∂ (m + 1)) JP ∞ f U)
    (hfint : IsTransverseOn (𝓡∂ (m + 1)) IZ JP f g (U ∩ (𝓡∂ (m + 1)).interior M))
    (hfbdy : IsTransverseOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ JP
      (f ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g (Subtype.val ⁻¹' U))
    {D : Set (P × P)} (hD : D ∈ 𝓝ˢ (diagonal P)) :
    ∃ f' : C(M, P), ContMDiff (𝓡∂ (m + 1)) JP ∞ f' ∧
      IsTransverse (𝓡∂ (m + 1)) IZ JP f' g ∧
      IsTransverse 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ JP
        (f' ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g ∧
      ∃ K : f.HomotopyRel f' C, ∀ t x, (K (t, x), f x) ∈ D := by
  have hfc : IsCompact (range f) := isCompact_range f.continuous
  exact f.exists_contMDiff_isTransverse_homotopyRel_halfSpace_of_isCompact_closure_range
    (by rwa [hfc.isClosed.closure_eq]) hg hC hU hfU hfint hfbdy hD

end HalfSpace

end ContinuousMap
