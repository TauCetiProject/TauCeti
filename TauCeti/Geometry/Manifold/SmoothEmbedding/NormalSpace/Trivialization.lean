/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Complement
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Topology

/-!
# Local trivializations of intrinsic normal bundles

The intrinsic normal spaces of a smooth embedding in an arbitrary ambient manifold admit local
product coordinates. Fix source and ambient tangent charts at a point and a closed complement to
the coordinate differential there. On a sufficiently small open set, projection along the moving
tangent range identifies every intrinsic normal fibre with that fixed complement.

This file assembles those fibrewise equivalences into a topological bundle trivialization while
retaining the quotient topology on the intrinsic normal total space. Its forward coordinate map is
the quotient-range coordinate operator in tangent charts, and its inverse takes the normal class of
the fixed complementary representative. The construction is the local topological input for the
normal vector bundle and the tubular-neighbourhood theorem in a general ambient manifold.

The construction follows J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the
normal-bundle construction preceding Theorem 6.24. It uses the quotient-total-space coordinates in
`SmoothEmbedding.normalQuotientMap` and the intrinsic fibre coordinates in
`SmoothEmbedding.normalSpaceEquivOfComplement`.
-/

public section

noncomputable section

open Set Function Topology Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E F P H G M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {n : ℕ∞ω}

private def normalCoordinateOn (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (x₀ : M) (U : Set M) (B : P →L[𝕜] F)
    (hU : U ⊆ (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source)
    (hB : ∀ x ∈ U, ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible)
    (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) : M × P := by
  classical
  exact if hp : p.proj ∈ U then
      (p.proj, f.normalSpaceEquivOfComplement hn (hU hp).1 (hU hp).2 B (hB p.proj hp) p.2)
    else (p.proj, 0)

private def normalCoordinateOnInv (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (x₀ : M) (U : Set M) (B : P →L[𝕜] F)
    (hU : U ⊆ (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source)
    (hB : ∀ x ∈ U, ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible)
    (p : M × P) : TotalSpace P (fun x ↦ f.NormalSpace x hn) := by
  classical
  exact if hp : p.1 ∈ U then
      ⟨p.1, (f.normalSpaceEquivOfComplement hn (hU hp).1 (hU hp).2 B
        (hB p.1 hp)).symm p.2⟩
    else zeroSection P (fun x ↦ f.NormalSpace x hn) p.1

private theorem normalCoordinateOn_apply (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (x₀ : M) (U : Set M) (B : P →L[𝕜] F)
    (hU : U ⊆ (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source)
    (hB : ∀ x ∈ U, ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible)
    (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) (hp : p.proj ∈ U) :
    normalCoordinateOn f hn x₀ U B hU hB p =
      (p.proj, f.normalSpaceEquivOfComplement hn (hU hp).1 (hU hp).2 B
        (hB p.proj hp) p.2) := by
  simp [normalCoordinateOn, hp]

private theorem normalCoordinateOnInv_apply (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (x₀ : M) (U : Set M) (B : P →L[𝕜] F)
    (hU : U ⊆ (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source)
    (hB : ∀ x ∈ U, ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible)
    (p : M × P) (hp : p.1 ∈ U) :
    normalCoordinateOnInv f hn x₀ U B hU hB p =
      ⟨p.1, (f.normalSpaceEquivOfComplement hn (hU hp).1 (hU hp).2 B
        (hB p.1 hp)).symm p.2⟩ := by
  simp [normalCoordinateOnInv, hp]

/-- Local product coordinates on the intrinsic normal bundle from a fixed complement in tangent
coordinates. The total space retains its quotient topology from ambient tangent representatives.

The open set must lie in the source and ambient tangent-chart domains, and `B` must complement the
coordinate differential throughout it. Continuity of the quotient-coordinate operator is the
only regularity input needed for this topological trivialization. -/
def normalSpaceTrivializationOfComplement (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (x₀ : M) (U : Set M) (hUopen : IsOpen U)
    (hU : U ⊆ (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source)
    (B : P →L[𝕜] F)
    (hB : ∀ x ∈ U, ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible)
    (hcoord : ContinuousOn
      (fun x ↦ (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₀ x).quotientRangeCoordinate B) U) :
    letI := f.instTopologicalSpaceNormalBundle (K := P) hn
    Trivialization P (π P (fun x ↦ f.NormalSpace x hn)) := by
  letI := f.instTopologicalSpaceNormalBundle (K := P) hn
  exact {
  toFun := normalCoordinateOn f hn x₀ U B hU hB
  invFun := normalCoordinateOnInv f hn x₀ U B hU hB
  source := π P (fun x ↦ f.NormalSpace x hn) ⁻¹' U
  target := U ×ˢ univ
  map_source' p hp := by
    rw [mem_preimage] at hp
    simp [normalCoordinateOn, hp]
  map_target' p hp := by
    have hpU : p.1 ∈ U := hp.1
    simp [normalCoordinateOnInv, hpU]
  left_inv' p hp := by
    rw [mem_preimage] at hp
    rw [normalCoordinateOn_apply f hn x₀ U B hU hB p hp]
    rw [normalCoordinateOnInv_apply f hn x₀ U B hU hB _ hp]
    simp
  right_inv' p hp := by
    have hpU : p.1 ∈ U := hp.1
    rw [normalCoordinateOnInv_apply f hn x₀ U B hU hB p hpU]
    rw [normalCoordinateOn_apply f hn x₀ U B hU hB _ hpU]
    exact Prod.ext rfl (f.normalSpaceEquivOfComplement_apply_symm_apply hn
      (hU hpU).1 (hU hpU).2 B (hB p.1 hpU) p.2)
  open_source := hUopen.preimage (f.continuous_normalBundle_proj hn)
  open_target := hUopen.prod isOpen_univ
  continuousOn_toFun := by
    rw [(f.isQuotientMap_normalQuotientMap (K := P) hn).continuousOn_isOpen_iff
      (hUopen.preimage (f.continuous_normalBundle_proj hn))]
    have hpre : f.normalQuotientMap (K := P) hn ⁻¹'
        (π P (fun x ↦ f.NormalSpace x hn) ⁻¹' U) =
        π F ((f : M → N) *ᵖ (TangentSpace J)) ⁻¹' U := by
      ext p
      simp only [mem_preimage, normalQuotientMap_apply]
    let e := trivializationAt F (TangentSpace J) (f x₀)
    have hbase : Continuous (π F ((f : M → N) *ᵖ (TangentSpace J))) :=
      Pullback.continuous_proj F (TangentSpace J) (f : M → N)
    have hlift := Pullback.continuous_lift F (TangentSpace J) (f : M → N)
    have hvec : ContinuousOn
        (fun p : TotalSpace F ((f : M → N) *ᵖ (TangentSpace J)) =>
          (e (Pullback.lift (f : M → N) p)).2)
        (π F ((f : M → N) *ᵖ (TangentSpace J)) ⁻¹' U) := by
      exact continuous_snd.comp_continuousOn
        (e.continuousOn.comp hlift.continuousOn fun p hp => by
          rw [e.mem_source]
          simpa only [e, TangentBundle.trivializationAt_baseSet, Pullback.lift, mem_preimage]
            using (hU hp).2)
    have hop : ContinuousOn
        (fun p : TotalSpace F ((f : M → N) *ᵖ (TangentSpace J)) =>
          (inTangentCoordinates I J _root_.id (f : M → N)
            (mfderiv I J (f : M → N)) x₀ p.proj).quotientRangeCoordinate B)
        (π F ((f : M → N) *ᵖ (TangentSpace J)) ⁻¹' U) :=
      hcoord.comp hbase.continuousOn fun _ hp => hp
    rw [hpre]
    refine (hbase.continuousOn.prodMk (hop.clm_apply hvec)).congr ?_
    intro p hp
    have hpU : p.proj ∈ U := hp
    simp only [Function.comp_apply]
    rw [normalQuotientMap_apply]
    rw [normalCoordinateOn_apply f hn x₀ U B hU hB _ hpU]
    simp only [e, Pullback.lift]
    exact Prod.ext rfl (f.normalSpaceEquivOfComplement_normalClass hn
      (hU hpU).1 (hU hpU).2 B (hB p.proj hpU) p.2)
  continuousOn_invFun := by
    let e := trivializationAt F (TangentSpace J) (f x₀)
    let q : M × P → TotalSpace F ((f : M → N) *ᵖ (TangentSpace J)) := fun p =>
      TotalSpace.mk' F p.1 (e.symm (f p.1) (B p.2))
    have hin : ContinuousOn
        (fun p : M × P => TotalSpace.mk' F (f p.1) (e.symm (f p.1) (B p.2)))
        (U ×ˢ univ) := by
      refine (e.continuousOn_symm.comp
        ((f.contMDiff.continuous.comp_continuousOn continuousOn_fst).prodMk
          (B.continuous.comp_continuousOn continuousOn_snd)) (by
            intro (p : M × P) hp
            exact ⟨by
              rw [TangentBundle.trivializationAt_baseSet]
              exact (hU hp.1).2, mem_univ _⟩)).congr ?_
      intro p hp
      rfl
    have hq : ContinuousOn q (U ×ˢ univ) := by
      rw [(inducing_pullbackTotalSpaceEmbedding F (TangentSpace J)
        (f : M → N)).continuousOn_iff]
      simp_rw [Function.comp_def, pullbackTotalSpaceEmbedding, q]
      exact continuousOn_fst.prodMk hin
    refine ((f.isQuotientMap_normalQuotientMap (K := P) hn).continuous.continuousOn.comp
      hq fun _ _ => mem_univ _).congr ?_
    intro p hp
    have hpU : p.1 ∈ U := hp.1
    rw [normalCoordinateOnInv_apply f hn x₀ U B hU hB p hpU]
    simp only [Function.comp_apply, q, normalQuotientMap_apply, e]
    exact congrArg (TotalSpace.mk p.1)
      (f.normalSpaceEquivOfComplement_symm_apply hn (hU hpU).1 (hU hpU).2 B
        (hB p.1 hpU) p.2)
  baseSet := U
  open_baseSet := hUopen
  source_eq := rfl
  target_eq := rfl
  proj_toFun p hp := by
    rw [mem_preimage] at hp
    simp [normalCoordinateOn, hp]
  }

/-- The base set of complementary normal coordinates is the prescribed open set. -/
@[simp] theorem normalSpaceTrivializationOfComplement_baseSet
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (x₀ : M) (U : Set M) (hUopen : IsOpen U)
    (hU : U ⊆ (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source)
    (B : P →L[𝕜] F)
    (hB : ∀ x ∈ U, ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible)
    (hcoord : ContinuousOn
      (fun x ↦ (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₀ x).quotientRangeCoordinate B) U) :
    letI := f.instTopologicalSpaceNormalBundle (K := P) hn
    (f.normalSpaceTrivializationOfComplement hn x₀ U hUopen hU B hB hcoord).baseSet = U := by
  simp [normalSpaceTrivializationOfComplement]

/-- Complementary normal coordinates are the fibre equivalence supplied by the tangent charts. -/
@[simp] theorem normalSpaceTrivializationOfComplement_apply
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (x₀ : M) (U : Set M) (hUopen : IsOpen U)
    (hU : U ⊆ (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source)
    (B : P →L[𝕜] F)
    (hB : ∀ x ∈ U, ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible)
    (hcoord : ContinuousOn
      (fun x ↦ (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₀ x).quotientRangeCoordinate B) U)
    (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) (hp : p.proj ∈ U) :
    letI := f.instTopologicalSpaceNormalBundle (K := P) hn
    f.normalSpaceTrivializationOfComplement hn x₀ U hUopen hU B hB hcoord p =
      (p.proj, f.normalSpaceEquivOfComplement hn (hU hp).1 (hU hp).2 B
        (hB p.proj hp) p.2) := by
  exact normalCoordinateOn_apply f hn x₀ U B hU hB p hp

/-- Inverse complementary normal coordinates take the normal class of the corresponding
complementary ambient tangent vector. -/
@[simp] theorem normalSpaceTrivializationOfComplement_symm_apply
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (x₀ : M) (U : Set M) (hUopen : IsOpen U)
    (hU : U ⊆ (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source)
    (B : P →L[𝕜] F)
    (hB : ∀ x ∈ U, ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible)
    (hcoord : ContinuousOn
      (fun x ↦ (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₀ x).quotientRangeCoordinate B) U)
    (p : M × P) (hp : p.1 ∈ U) :
    letI := f.instTopologicalSpaceNormalBundle (K := P) hn
    (f.normalSpaceTrivializationOfComplement hn x₀ U hUopen hU B hB
      hcoord).toOpenPartialHomeomorph.symm p =
      ⟨p.1, (f.normalSpaceEquivOfComplement hn (hU hp).1 (hU hp).2 B
        (hB p.1 hp)).symm p.2⟩ := by
  exact normalCoordinateOnInv_apply f hn x₀ U B hU hB p hp

/-- Complementary normal coordinates are linear on every fibre over their base set. -/
instance instIsLinearNormalSpaceTrivializationOfComplement
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (x₀ : M) (U : Set M) (hUopen : IsOpen U)
    (hU : U ⊆ (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source)
    (B : P →L[𝕜] F)
    (hB : ∀ x ∈ U, ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible)
    (hcoord : ContinuousOn
      (fun x ↦ (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₀ x).quotientRangeCoordinate B) U) :
    letI := f.instTopologicalSpaceNormalBundle (K := P) hn
    (f.normalSpaceTrivializationOfComplement hn x₀ U hUopen hU B hB hcoord).IsLinear 𝕜 where
  linear x hx := by
    have hxU : x ∈ U := by
      simpa using hx
    constructor
    · intro v w
      rw [normalSpaceTrivializationOfComplement_apply f hn x₀ U hUopen hU B hB
        hcoord ⟨x, v + w⟩ hxU]
      rw [normalSpaceTrivializationOfComplement_apply f hn x₀ U hUopen hU B hB
        hcoord ⟨x, v⟩ hxU]
      rw [normalSpaceTrivializationOfComplement_apply f hn x₀ U hUopen hU B hB
        hcoord ⟨x, w⟩ hxU]
      exact map_add _ v w
    · intro c v
      rw [normalSpaceTrivializationOfComplement_apply f hn x₀ U hUopen hU B hB
        hcoord ⟨x, c • v⟩ hxU]
      rw [normalSpaceTrivializationOfComplement_apply f hn x₀ U hUopen hU B hB
        hcoord ⟨x, v⟩ hxU]
      exact map_smul _ c v

end TauCeti.SmoothEmbedding
