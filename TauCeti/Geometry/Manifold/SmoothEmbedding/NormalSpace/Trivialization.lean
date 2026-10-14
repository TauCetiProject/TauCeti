/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Complement
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Topology
import TauCeti.Topology.VectorBundle.QuotientRange

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

private noncomputable def normalSourceHomeomorphOfComplement
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
    {p : TotalSpace P (fun x ↦ f.NormalSpace x hn) // p.proj ∈ U} ≃ₜ U × P := by
  letI := f.instTopologicalSpaceNormalBundle (K := P) hn
  let A : U → E →L[𝕜] F := fun x =>
    inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x
  let Q := TotalSpace P (fun x : U => F ⧸ (A x).range)
  letI : TopologicalSpace Q := TopologicalSpace.coinduced
    (rangeQuotientMap (G := P) A) inferInstance
  have hq : IsQuotientMap (rangeQuotientMap (G := P) A) := {
    eq_coinduced := rfl
    surjective := rangeQuotientMap_surjective A
  }
  let normalToQ : {p : TotalSpace P (fun x ↦ f.NormalSpace x hn) // p.proj ∈ U} → Q :=
    fun p => ⟨⟨p.1.proj, p.2⟩,
      f.normalSpaceEquivInTangentCoordinates hn (hU p.2).1 (hU p.2).2 p.1.2⟩
  let qToNormal : Q → {p : TotalSpace P (fun x ↦ f.NormalSpace x hn) // p.proj ∈ U} :=
    fun p => ⟨⟨p.1.1,
      (f.normalSpaceEquivInTangentCoordinates hn (hU p.1.2).1 (hU p.1.2).2).symm p.2⟩,
      p.1.2⟩
  have hnormalToQ : Continuous normalToQ := by
    let source := π P (fun x ↦ f.NormalSpace x hn) ⁻¹' U
    rw [((f.isQuotientMap_normalQuotientMap (K := P) hn).restrictPreimage_isOpen
      (hUopen.preimage (f.continuous_normalBundle_proj hn))).continuous_iff]
    let e := trivializationAt F (TangentSpace J) (f x₀)
    let c : (f.normalQuotientMap (K := P) hn ⁻¹' source) → U × F := fun p =>
      (⟨p.1.proj, by
        simpa only [source, mem_preimage, normalQuotientMap_apply] using p.2⟩,
        (e (Pullback.lift (f : M → N) p.1)).2)
    have hc : Continuous c := by
      have hbase : Continuous
          (fun p : (f.normalQuotientMap (K := P) hn ⁻¹' source) =>
            (⟨p.1.proj, by
              simpa only [source, mem_preimage, normalQuotientMap_apply] using p.2⟩ : U)) := by
        exact ((Pullback.continuous_proj F (TangentSpace J) (f : M → N)).comp
          continuous_subtype_val).subtype_mk _
      have hvec : Continuous
          (fun p : (f.normalQuotientMap (K := P) hn ⁻¹' source) =>
            (e (Pullback.lift (f : M → N) p.1)).2) := by
        refine continuous_snd.comp (e.continuousOn.comp_continuous ?_ ?_)
        · exact (Pullback.continuous_lift F (TangentSpace J) (f : M → N)).comp
            continuous_subtype_val
        · intro p
          rw [e.mem_source]
          apply (hU ?_).2
          simpa only [source, mem_preimage, normalQuotientMap_apply] using p.2
      exact hbase.prodMk hvec
    refine (hq.continuous.comp hc).congr ?_
    rintro ⟨⟨x, v⟩, hx⟩
    have hxU : x ∈ U := by
      simpa only [source, mem_preimage, normalQuotientMap_apply] using hx
    have hrestrict : source.restrictPreimage (f.normalQuotientMap (K := P) hn)
        ⟨⟨x, v⟩, hx⟩ = ⟨⟨x, f.normalClass x hn v⟩, hxU⟩ := by
      apply Subtype.ext
      exact f.normalQuotientMap_apply hn ⟨x, v⟩
    simp only [Function.comp_apply]
    rw [hrestrict]
    simp only [normalToQ, c, rangeQuotientMap_apply]
    exact congrArg (@TotalSpace.mk U P (fun x : U => F ⧸ (A x).range) ⟨x, hxU⟩)
      (f.normalSpaceEquivInTangentCoordinates_normalClass hn
        (hU hxU).1 (hU hxU).2 v).symm
  have hqToNormal : Continuous qToNormal := by
    rw [hq.continuous_iff]
    let e := trivializationAt F (TangentSpace J) (f x₀)
    let q : U × F → TotalSpace F ((f : M → N) *ᵖ (TangentSpace J)) := fun p =>
      TotalSpace.mk' F p.1.1 (e.symm (f p.1.1) p.2)
    have hq' : Continuous q := by
      rw [(inducing_pullbackTotalSpaceEmbedding F (TangentSpace J)
        (f : M → N)).continuous_iff]
      have h := (continuous_subtype_val.comp continuous_fst).prodMk
        (e.continuousOn_symm.comp_continuous
          (((f.contMDiff.continuous.comp continuous_subtype_val).comp continuous_fst).prodMk
            continuous_snd) (fun p => by
              rw [TangentBundle.trivializationAt_baseSet]
              exact ⟨(hU p.1.2).2, mem_univ _⟩))
      convert h using 1
      funext p
      rfl
    have hnq : Continuous (fun p : U × F =>
        (⟨f.normalQuotientMap (K := P) hn (q p), by
          simpa only [q, normalQuotientMap_apply] using p.1.2⟩ :
          {p : TotalSpace P (fun x ↦ f.NormalSpace x hn) // p.proj ∈ U})) := by
      exact ((f.isQuotientMap_normalQuotientMap (K := P) hn).continuous.comp hq').subtype_mk _
    refine hnq.congr ?_
    rintro ⟨⟨x, hx⟩, v⟩
    have hnqapply : f.normalQuotientMap (K := P) hn (q (⟨x, hx⟩, v)) =
        ⟨x, f.normalClass x hn
          ((trivializationAt F (TangentSpace J) (f x₀)).symm (f x) v)⟩ := by
      exact f.normalQuotientMap_apply hn _
    simp only [Function.comp_apply]
    rw [rangeQuotientMap_apply]
    apply Subtype.ext
    -- Expose the underlying fibre map after restricting both quotient maps to `U`.
    change f.normalQuotientMap (K := P) hn (q (⟨x, hx⟩, v)) =
      (qToNormal ⟨⟨x, hx⟩, Submodule.Quotient.mk v⟩).1
    simp only [qToNormal]
    calc
      _ = ⟨x, f.normalClass x hn
          ((trivializationAt F (TangentSpace J) (f x₀)).symm (f x) v)⟩ := hnqapply
      _ = ⟨x, (f.normalSpaceEquivInTangentCoordinates hn
          (hU hx).1 (hU hx).2).symm (Submodule.Quotient.mk v)⟩ :=
        congrArg (TotalSpace.mk x)
          (f.normalSpaceEquivInTangentCoordinates_symm_mk hn
            (hU hx).1 (hU hx).2 v).symm
      _ = _ := by congr
  let normalQHomeomorph :
      {p : TotalSpace P (fun x ↦ f.NormalSpace x hn) // p.proj ∈ U} ≃ₜ Q := {
    toFun := normalToQ
    invFun := qToNormal
    left_inv := by
      rintro ⟨⟨x, v⟩, hx⟩
      apply Subtype.ext
      exact congrArg (TotalSpace.mk x) ((f.normalSpaceEquivInTangentCoordinates hn
        (hU hx).1 (hU hx).2).symm_apply_apply v)
    right_inv := by
      rintro ⟨⟨x, hx⟩, v⟩
      exact congrArg (@TotalSpace.mk U P (fun x : U => F ⧸ (A x).range) ⟨x, hx⟩)
        ((f.normalSpaceEquivInTangentCoordinates hn
          (hU hx).1 (hU hx).2).apply_symm_apply v)
    continuous_toFun := hnormalToQ
    continuous_invFun := hqToNormal
  }
  have hcoord' : Continuous
      (fun p : U × F => (A p.1).quotientRangeCoordinate B p.2) := by
    have hop : Continuous (fun p : U × F =>
        (inTangentCoordinates I J _root_.id (f : M → N)
          (mfderiv I J (f : M → N)) x₀ p.1).quotientRangeCoordinate B) :=
      (hcoord.domRestrict (f := fun x ↦
        (inTangentCoordinates I J _root_.id (f : M → N)
          (mfderiv I J (f : M → N)) x₀ x).quotientRangeCoordinate B)).comp continuous_fst
    exact hop.clm_apply continuous_snd
  exact normalQHomeomorph.trans (rangeQuotientHomeomorph A B
    (fun x => hB x x.2) hq hcoord')

private theorem normalSourceHomeomorphOfComplement_apply
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
    normalSourceHomeomorphOfComplement f hn x₀ U hUopen hU B hB hcoord ⟨p, hp⟩ =
      (⟨p.proj, hp⟩, f.normalSpaceEquivOfComplement hn
        (hU hp).1 (hU hp).2 B (hB p.proj hp) p.2) := by
  simp only [normalSourceHomeomorphOfComplement, Homeomorph.trans_apply]
  rw [rangeQuotientHomeomorph_apply]
  -- Compare the composite homeomorphism with the established intrinsic fibre coordinates.
  change (((⟨p.proj, hp⟩ : U),
      (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₀ p.proj).quotientRangeEquiv B
          (hB p.proj hp)
          (f.normalSpaceEquivInTangentCoordinates hn (hU hp).1 (hU hp).2 p.2)) : U × P) =
    (((⟨p.proj, hp⟩ : U), f.normalSpaceEquivOfComplement hn
      (hU hp).1 (hU hp).2 B (hB p.proj hp) p.2) : U × P)
  apply Prod.ext
  · rfl
  obtain ⟨v, hv⟩ := f.normalClass_surjective p.proj hn p.2
  rw [← hv]
  rw [f.normalSpaceEquivInTangentCoordinates_normalClass hn (hU hp).1 (hU hp).2]
  rw [ContinuousLinearMap.quotientRangeEquiv_apply_mk]
  exact (f.normalSpaceEquivOfComplement_normalClass hn
    (hU hp).1 (hU hp).2 B (hB p.proj hp) v).symm

private theorem normalSourceHomeomorphOfComplement_symm_apply
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
    (normalSourceHomeomorphOfComplement f hn x₀ U hUopen hU B hB hcoord).symm
        (⟨p.1, hp⟩, p.2) =
      ⟨⟨p.1, (f.normalSpaceEquivOfComplement hn
        (hU hp).1 (hU hp).2 B (hB p.1 hp)).symm p.2⟩, hp⟩ := by
  simp only [normalSourceHomeomorphOfComplement, Homeomorph.symm_trans_apply]
  rw [rangeQuotientHomeomorph_symm_apply]
  -- Compare the two inverse formulas after the generic quotient homeomorphism is evaluated.
  change (⟨⟨p.1, (f.normalSpaceEquivInTangentCoordinates hn
      (hU hp).1 (hU hp).2).symm (Submodule.Quotient.mk (B p.2))⟩, hp⟩ :
        {p : TotalSpace P (fun x ↦ f.NormalSpace x hn) // p.proj ∈ U}) =
    ⟨⟨p.1, (f.normalSpaceEquivOfComplement hn
      (hU hp).1 (hU hp).2 B (hB p.1 hp)).symm p.2⟩, hp⟩
  apply Subtype.ext
  exact congrArg (TotalSpace.mk p.1)
    ((f.normalSpaceEquivInTangentCoordinates_symm_mk hn
      (hU hp).1 (hU hp).2 (B p.2)).trans
        (f.normalSpaceEquivOfComplement_symm_apply hn
          (hU hp).1 (hU hp).2 B (hB p.1 hp) p.2).symm)

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
    rw [continuousOn_iff_continuous_domRestrict]
    let e := normalSourceHomeomorphOfComplement f hn x₀ U hUopen hU B hB hcoord
    have he : Continuous (fun p => ((e p).1.1, (e p).2)) :=
      (continuous_subtype_val.comp (continuous_fst.comp e.continuous)).prodMk
        (continuous_snd.comp e.continuous)
    refine he.congr ?_
    rintro ⟨p, hp⟩
    -- The restricted homeomorphism has the same forward formula as the partial map.
    change ((e ⟨p, hp⟩).1.1, (e ⟨p, hp⟩).2) =
      normalCoordinateOn f hn x₀ U B hU hB p
    rw [normalCoordinateOn_apply f hn x₀ U B hU hB p hp]
    simpa only [e] using congrArg (fun q : U × P => (q.1.1, q.2))
      (normalSourceHomeomorphOfComplement_apply f hn x₀ U hUopen hU B hB hcoord p hp)
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    let e := normalSourceHomeomorphOfComplement f hn x₀ U hUopen hU B hB hcoord
    let c : (U ×ˢ univ : Set (M × P)) → U × P := fun p =>
      (⟨p.1.1, p.2.1⟩, p.1.2)
    have hc : Continuous c := by
      exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        (continuous_snd.comp continuous_subtype_val)
    have he : Continuous (fun p => (e.symm (c p)).1) :=
      continuous_subtype_val.comp (e.symm.continuous.comp hc)
    refine he.congr ?_
    rintro ⟨p, hp⟩
    -- The restricted homeomorphism has the same inverse formula as the partial map.
    change (e.symm (c ⟨p, hp⟩)).1 = normalCoordinateOnInv f hn x₀ U B hU hB p
    rw [normalCoordinateOnInv_apply f hn x₀ U B hU hB p hp.1]
    simpa only [e, c] using congrArg Subtype.val
      (normalSourceHomeomorphOfComplement_symm_apply f hn x₀ U hUopen hU B hB
        hcoord p hp.1)
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
