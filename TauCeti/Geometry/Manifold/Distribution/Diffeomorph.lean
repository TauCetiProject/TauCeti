/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Transport of distributions through diffeomorphisms

A partial diffeomorphism transports local frames and involutivity between its source and target,
while a global diffeomorphism transports smooth constant-rank distributions. This allows
regularity and involutivity to be checked in local or global coordinate models when constructing
integral manifolds. In particular, the pullback of a smooth distribution is smooth, and a
distribution is involutive if and only if its pullback by a diffeomorphism is involutive.

The vector-field pullback and Lie-bracket naturality APIs are provided by Mathlib.

`TauCeti.IsDistributionFrameOn.comap_mfderivWithin` pulls a local frame back through partial
coordinates, and `TauCeti.IsDistributionFrameOn.comap_mfderiv` is its global specialization.
`TauCeti.IsContMDiffDistribution.exists_isDistributionFrameOn_of_eventually_eq_comap` is the local
version for distributions: a distribution that a local diffeomorphism pulls back from a `C^m` one
near a point has a `C^m` local frame there. Hence pullbacks along local diffeomorphisms of `C^m`
distributions are `C^m` (`TauCeti.IsContMDiffDistribution.comap_mfderiv_of_isLocalDiffeomorph`,
with the special case `TauCeti.IsContMDiffDistribution.comap_mfderiv` of a diffeomorphism), and
conversely a distribution whose pullback along a surjective local diffeomorphism is `C^m` is itself
`C^m` (`TauCeti.IsContMDiffDistribution.of_comap_mfderiv_of_isLocalDiffeomorph`), as local
inverses pull the pullback back to it.
In particular the restriction of a `C^m` distribution to an open subset is `C^m`
(`TauCeti.IsContMDiffDistribution.comp_subtypeVal`).
When `D x` is the preimage of `D' (f x)` under the differential of a local diffeomorphism `f` at
`x`, the differential restricts to a linear equivalence `D x ≃ D' (f x)`
(`IsLocalDiffeomorphAt.mfderivRestrictEquiv`) and induces one of normal spaces
`T_x M ⧸ D x ≃ T_(f x) N ⧸ D' (f x)` (`IsLocalDiffeomorphAt.mfderivQuotientEquiv`).
Such pullbacks compose (`IsLocalDiffeomorphAt.eventually_eq_comap_mfderiv_comp`), and so do the
two equivalences (`IsLocalDiffeomorphAt.mfderivRestrictEquiv_trans`,
`IsLocalDiffeomorphAt.mfderivQuotientEquiv_trans`).
`PartialDiffeomorph.isInvolutiveDistributionOn` transports local involutivity,
`TauCeti.IsInvolutiveDistribution.diffeomorph` is its global specialization, and
`Diffeomorph.isInvolutiveDistribution_iff` gives the equivalence for identified distributions.
`Diffeomorph.isInvolutiveDistribution_comap_mfderiv_iff` gives the pullback characterization.
`PartialDiffeomorph.isInvolutiveDistributionOn_comap_mfderivWithin` shows that the pullback of a
distribution involutive on the target is involutive on the source.

The distributions remain families of tangent subspaces, and their pullback is expressed by
`Submodule.comap` along the differential. Pulling back a `C^m` frame through a `C^n`
diffeomorphism requires `m + 1 ≤ n`, because the vector-field pullback contains the inverse
differential. Involutivity requires the diffeomorphism to be at least `C²` over the reals
(`minSmoothness 𝕜 2` over a general scalar field), so that pullbacks of differentiable vector
fields are differentiable and their Lie brackets transform naturally.
-/

public section

noncomputable section

open Set Bundle VectorField
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω}
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}
  {D' : Π y : N, Submodule 𝕜 (TangentSpace J y)}

namespace TauCeti

section Regularity

variable [IsManifold I 1 M] [IsManifold J 1 N]

private theorem isDistributionFrameOn_comap_mfderivWithin_of_isInvertible {m : ℕ∞ω}
    {ι : Type*} {X : ι → Π y : N, TangentSpace J y} {U : Set N}
    (hX : IsDistributionFrameOn J m D' X U) (f : M → N) (s : Set M)
    (hf : CMDiff[s] n f) (hfinv : ∀ x ∈ s, (mfderivWithin I J f s x).IsInvertible)
    (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) :
    IsDistributionFrameOn I m
      (fun x ↦ (D' (f x)).comap (mfderivWithin I J f s x).toLinearMap)
      (fun i ↦ mpullbackWithin I J f (X i) s) (s ∩ f ⁻¹' U) := by
  refine ⟨fun i ↦ (hX.contMDiffOn i).mpullbackWithin_vectorField_inter hf
      (fun x hx ↦ hfinv x hx.1) hs hmn, fun {x} hx ↦ ?_, fun {x} hx ↦ ?_⟩
  · apply LinearIndependent.of_comp (mfderivWithin I J f s x).toLinearMap
    convert hX.linearIndependent hx.2 using 1
    funext i
    exact (hfinv x hx.1).self_apply_inverse _
  · apply Submodule.map_injective_of_injective (hfinv x hx.1).injective
    rw [Submodule.map_comap_eq_of_surjective (hfinv x hx.1).surjective]
    rw [Submodule.map_span, ← hX.span_eq hx.2, ← Set.range_comp]
    congr 2
    funext i
    exact (hfinv x hx.1).self_apply_inverse _

/-- Pulling a local frame back through partial coordinates gives a frame on the part of the
coordinate source mapping into the original frame domain. The loss of one derivative comes from
the inverse differential in the vector-field pullback. -/
theorem IsDistributionFrameOn.comap_mfderivWithin {m : ℕ∞ω} {ι : Type*}
    {X : ι → Π y : N, TangentSpace J y} {U : Set N}
    (hX : IsDistributionFrameOn J m D' X U) (Φ : PartialDiffeomorph I J M N n)
    (hmn : m + 1 ≤ n) :
    IsDistributionFrameOn I m
      (fun x ↦ (D' (Φ x)).comap (mfderivWithin I J Φ Φ.source x).toLinearMap)
      (fun i ↦ mpullbackWithin I J Φ (X i) Φ.source) (Φ.source ∩ Φ ⁻¹' U) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hmn
  have hΦinv (x : M) (hx : x ∈ Φ.source) :
      (mfderivWithin I J Φ Φ.source x).IsInvertible := by
    rw [Φ.mfderivWithin_source hx]
    exact (_root_.PartialDiffeomorph.isLocalDiffeomorphAt I J n Φ hx).isInvertible_mfderiv hn0
  exact isDistributionFrameOn_comap_mfderivWithin_of_isInvertible hX Φ Φ.source
    Φ.contMDiffOn hΦinv Φ.open_source.uniqueMDiffOn hmn

/-- Pulling a local frame back through a diffeomorphism gives a local frame for the pullback
distribution. The loss of one derivative comes from the inverse differential in the vector-field
pullback. -/
theorem IsDistributionFrameOn.comap_mfderiv {m : ℕ∞ω} {ι : Type*}
    {X : ι → Π y : N, TangentSpace J y} {U : Set N}
    (hX : IsDistributionFrameOn J m D' X U) (h : M ≃ₘ^n⟮I, J⟯ N) (hmn : m + 1 ≤ n) :
    IsDistributionFrameOn I m
      (fun x ↦ (D' (h x)).comap (mfderiv I J h x).toLinearMap)
      (fun i ↦ mpullback I J h (X i)) (h ⁻¹' U) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hmn
  simpa only [univ_inter, mfderivWithin_univ, mpullbackWithin_univ] using
    isDistributionFrameOn_comap_mfderivWithin_of_isInvertible hX h Set.univ
      h.contMDiff.contMDiffOn
      (fun x _ ↦ by simpa only [mfderivWithin_univ] using h.isInvertible_mfderiv hn0)
      uniqueMDiffOn_univ hmn

open Filter in
open scoped Topology in
/-- **Local frames of a pulled-back distribution.** If a `C^n` local diffeomorphism `f` at `x`
pulls a `C^m` distribution `D'` back to `D` near `x`, that is `D z` is the preimage of `D' (f z)`
under the differential of `f` for `z` near `x`, and `m + 1 ≤ n`, then `D` has a `C^m` local frame
of the same rank on a neighbourhood of `x`. -/
theorem IsContMDiffDistribution.exists_isDistributionFrameOn_of_eventually_eq_comap {m : ℕ∞ω}
    {k : ℕ} {f : M → N} {x : M} (hD' : IsContMDiffDistribution J m k D')
    (hf : IsLocalDiffeomorphAt I J n f x) (hmn : m + 1 ≤ n)
    (hDf : ∀ᶠ z in 𝓝 x, D z = (D' (f z)).comap (mfderiv I J f z).toLinearMap) :
    ∃ U ∈ 𝓝 x, ∃ X : Fin k → Π y : M, TangentSpace I y, IsDistributionFrameOn I m D X U := by
  obtain ⟨Φ, hxΦ, -, hfΦ⟩ := hf.exists_partialDiffeomorph_eqOn isOpen_univ (mem_univ x)
  obtain ⟨U', hU', hxU', X', hX'⟩ := isContMDiffDistribution_iff.mp hD' (f x)
  have hY := hX'.comap_mfderivWithin Φ hmn
  have hsrc : Φ.source ∈ 𝓝 x := Φ.open_source.mem_nhds hxΦ
  -- On the open source of `Φ`, the pulled-back family is the preimage of `D'` under `df`.
  have hcomap : ∀ᶠ z in 𝓝 x, (D' (Φ z)).comap (mfderivWithin I J Φ Φ.source z).toLinearMap =
      (D' (f z)).comap (mfderiv I J f z).toLinearMap := by
    filter_upwards [hsrc] with z hz
    have hfz : f =ᶠ[𝓝 z] Φ := eventually_of_mem (Φ.open_source.mem_nhds hz) fun _ h ↦ hfΦ h
    -- The tangent spaces at `f z = Φ z` are the same, so the two differentials agree.
    have hd (w : TangentSpace I z) : mfderiv I J f z w = mfderiv I J Φ z w := by
      rw [hfz.mfderiv_eq]
      rfl
    ext w
    rw [Φ.mfderivWithin_source hz, Submodule.mem_comap, Submodule.mem_comap,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, hd, hfΦ hz]
  have hU : Φ.source ∩ Φ ⁻¹' U' ∈ 𝓝 x := inter_mem hsrc <|
    (Φ.contMDiffOn_toFun.continuousOn.continuousAt hsrc).preimage_mem_nhds
      (hU'.mem_nhds (hfΦ hxΦ ▸ hxU'))
  refine ⟨_, inter_mem hU (hDf.and hcomap), fun i ↦ mpullbackWithin I J Φ (X' i) Φ.source,
    (hY.mono inter_subset_left).contMDiffOn, fun hz ↦ hY.linearIndependent hz.1, fun hz ↦ ?_⟩
  rw [hY.span_eq hz.1, hz.2.2, hz.2.1]

/-- **Pullback of a distribution along a local diffeomorphism.** The pullback
`x ↦ (df_x)⁻¹ (D' (f x))` of a `C^m` distribution of rank `k` along a `C^n` local diffeomorphism
`f` is a `C^m` distribution of rank `k` when `m + 1 ≤ n`. -/
theorem IsContMDiffDistribution.comap_mfderiv_of_isLocalDiffeomorph {m : ℕ∞ω} {k : ℕ}
    {f : M → N} (hD' : IsContMDiffDistribution J m k D') (hf : IsLocalDiffeomorph I J n f)
    (hmn : m + 1 ≤ n) :
    IsContMDiffDistribution I m k
      (fun x ↦ (D' (f x)).comap (mfderiv I J f x).toLinearMap) :=
  .of_mem_nhds fun x ↦ hD'.exists_isDistributionFrameOn_of_eventually_eq_comap (hf x) hmn
    (.of_forall fun _ ↦ rfl)

/-- The pullback of a `C^m` distribution through a `C^n` diffeomorphism is a `C^m`
distribution of the same rank when `m + 1 ≤ n`. -/
theorem IsContMDiffDistribution.comap_mfderiv {m : ℕ∞ω} {k : ℕ}
    (hD' : IsContMDiffDistribution J m k D') (h : M ≃ₘ^n⟮I, J⟯ N) (hmn : m + 1 ≤ n) :
    IsContMDiffDistribution I m k
      (fun x ↦ (D' (h x)).comap (mfderiv I J h x).toLinearMap) :=
  hD'.comap_mfderiv_of_isLocalDiffeomorph h.isLocalDiffeomorph hmn

/-- **Restriction of a distribution to an open subset.** The restriction `x ↦ D x` of a `C^m`
distribution of rank `k` to an open subset `U` is a `C^m` distribution of rank `k` on `U`, the
tangent spaces of `U` being those of `M`. -/
theorem IsContMDiffDistribution.comp_subtypeVal {m : ℕ∞ω} {k : ℕ}
    (hD : IsContMDiffDistribution I m k D) (U : TopologicalSpace.Opens M) :
    IsContMDiffDistribution I m k (fun x : U ↦ D x) := by
  rw [show (fun x : U ↦ D x) = fun x : U ↦ (D x).comap (mfderiv I I Subtype.val x).toLinearMap from
    funext fun x ↦ (Submodule.comap_mfderiv_subtype_val (D x)).symm]
  exact hD.comap_mfderiv_of_isLocalDiffeomorph isLocalDiffeomorph_subtype_val le_rfl

omit [CompleteSpace E] in
/-- **Descent of a distribution along a surjective local diffeomorphism.** Let `f` be a surjective
`C^n` local diffeomorphism and `D'` a distribution on its target. If the pullback
`x ↦ (df_x)⁻¹ (D' (f x))` is a `C^m` distribution of rank `k` and `m + 1 ≤ n`, then so is `D'`:
near each point `f x`, a local inverse of `f` pulls the pullback back to `D'`. -/
theorem IsContMDiffDistribution.of_comap_mfderiv_of_isLocalDiffeomorph [CompleteSpace F]
    {m : ℕ∞ω} {k : ℕ} {f : M → N}
    (hD : IsContMDiffDistribution I m k
      (fun x ↦ (D' (f x)).comap (mfderiv I J f x).toLinearMap))
    (hf : IsLocalDiffeomorph I J n f) (hsurj : Function.Surjective f) (hmn : m + 1 ≤ n) :
    IsContMDiffDistribution J m k D' := by
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hmn
  refine .of_mem_nhds fun y ↦ ?_
  obtain ⟨x, rfl⟩ := hsurj y
  refine hD.exists_isDistributionFrameOn_of_eventually_eq_comap
    (hf x).localInverse_isLocalDiffeomorphAt hmn ?_
  filter_upwards [(hf x).localInverse_open_source.mem_nhds (hf x).localInverse_mem_source]
    with z hz
  ext v
  rw [Submodule.mem_comap, Submodule.mem_comap, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_coe, (hf x).mfderiv_apply_mfderiv_localInverse_apply hn hz v,
    (hf x).localInverse_right_inv hz]

end Regularity

end TauCeti

namespace IsLocalDiffeomorphAt

section Restrict

omit [CompleteSpace E]

variable {f : M → N} {x : M}

/-- The differential of a local diffeomorphism `f` at `x` carries `D x` onto `D' (f x)` when `D x`
is the preimage of `D' (f x)`. -/
theorem map_mfderiv_eq (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0)
    (hD : D x = (D' (f x)).comap (mfderiv I J f x).toLinearMap) :
    (D x).map (mfderiv I J f x).toLinearMap = D' (f x) := by
  rw [hD]
  exact Submodule.map_comap_eq_of_surjective (hf.isInvertible_mfderiv hn).surjective _

/-- The differential of a local diffeomorphism `f` at `x`, restricted to a linear equivalence
`D x ≃ D' (f x)` when `D x` is the preimage of `D' (f x)`. -/
def mfderivRestrictEquiv (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0)
    (hD : D x = (D' (f x)).comap (mfderiv I J f x).toLinearMap) : D x ≃ₗ[𝕜] D' (f x) :=
  (hf.mfderivToContinuousLinearEquiv hn).toLinearEquiv.ofSubmodules _ _ <| by
    rw [← hf.map_mfderiv_eq hn hD, ← hf.mfderivToContinuousLinearEquiv_coe hn,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]

/-- The restricted differential sends `u` to `df_x u`. -/
@[simp]
theorem coe_mfderivRestrictEquiv_apply (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0)
    (hD : D x = (D' (f x)).comap (mfderiv I J f x).toLinearMap) (u : D x) :
    (hf.mfderivRestrictEquiv hn hD u : TangentSpace J (f x)) = mfderiv I J f x u := by
  rw [mfderivRestrictEquiv, LinearEquiv.ofSubmodules_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv, ← ContinuousLinearEquiv.coe_coe,
    hf.mfderivToContinuousLinearEquiv_coe hn]

/-- The differential of a local diffeomorphism `f` at `x` induces a linear equivalence
`T_x M ⧸ D x ≃ T_(f x) N ⧸ D' (f x)` of normal spaces when `D x` is the preimage of
`D' (f x)`. -/
def mfderivQuotientEquiv (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0)
    (hD : D x = (D' (f x)).comap (mfderiv I J f x).toLinearMap) :
    (TangentSpace I x ⧸ D x) ≃ₗ[𝕜] TangentSpace J (f x) ⧸ D' (f x) :=
  Submodule.Quotient.equiv _ _ (hf.mfderivToContinuousLinearEquiv hn).toLinearEquiv <| by
    rw [← hf.map_mfderiv_eq hn hD, ← hf.mfderivToContinuousLinearEquiv_coe hn,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]

/-- The induced map of normal spaces sends the class of `u` to the class of `df_x u`. -/
@[simp]
theorem mfderivQuotientEquiv_mk (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0)
    (hD : D x = (D' (f x)).comap (mfderiv I J f x).toLinearMap) (u : TangentSpace I x) :
    hf.mfderivQuotientEquiv hn hD (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (mfderiv I J f x u) := by
  rw [mfderivQuotientEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, ← ContinuousLinearEquiv.coe_coe,
    hf.mfderivToContinuousLinearEquiv_coe hn]

/-- As a linear map, the induced map of normal spaces is the quotient map `Submodule.mapQ` of
`df_x`. -/
theorem coe_mfderivQuotientEquiv (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0)
    (hD : D x = (D' (f x)).comap (mfderiv I J f x).toLinearMap) :
    (hf.mfderivQuotientEquiv hn hD :
        (TangentSpace I x ⧸ D x) →ₗ[𝕜] TangentSpace J (f x) ⧸ D' (f x)) =
      (D x).mapQ (D' (f x)) (mfderiv I J f x).toLinearMap hD.le := by
  ext u
  simp

section Comp

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {D'' : Π z : P, Submodule 𝕜 (TangentSpace K z)} {g : N → P}

/-- **Pullbacks of subspaces compose.** If `D x` is the preimage of `D' (f x)` under `df_x` and
`D' (f x)` is the preimage of `D'' (g (f x))` under `dg_(f x)`, then `D x` is the preimage of
`D'' (g (f x))` under `d(g ∘ f)_x`. -/
theorem _root_.MDifferentiableAt.eq_comap_mfderiv_comp (hf : MDifferentiableAt I J f x)
    (hg : MDifferentiableAt J K g (f x))
    (hD : D x = (D' (f x)).comap (mfderiv I J f x).toLinearMap)
    (hD' : D' (f x) = (D'' (g (f x))).comap (mfderiv J K g (f x)).toLinearMap) :
    D x = (D'' ((g ∘ f) x)).comap (mfderiv I K (g ∘ f) x).toLinearMap := by
  rw [hD, hD', mfderiv_comp x hg hf]
  ext v
  simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  rfl

open Filter Topology in
/-- **Local pullbacks of distributions compose.** If `f` pulls `D'` back to `D` near `x` and `g`
pulls `D''` back to `D'` near `f x`, then `g ∘ f` pulls `D''` back to `D` near `x`. -/
theorem eventually_eq_comap_mfderiv_comp (hf : IsLocalDiffeomorphAt I J n f x)
    (hg : IsLocalDiffeomorphAt J K n g (f x)) (hn : n ≠ 0)
    (hD : ∀ᶠ z in 𝓝 x, D z = (D' (f z)).comap (mfderiv I J f z).toLinearMap)
    (hD' : ∀ᶠ z in 𝓝 (f x), D' z = (D'' (g z)).comap (mfderiv J K g z).toLinearMap) :
    ∀ᶠ z in 𝓝 x, D z = (D'' ((g ∘ f) z)).comap (mfderiv I K (g ∘ f) z).toLinearMap := by
  filter_upwards [hD, hf.eventually,
    hf.contMDiffAt.continuousAt.tendsto.eventually (hD'.and hg.eventually)]
    with z hDz hfz hgz
  exact (hfz.mdifferentiableAt hn).eq_comap_mfderiv_comp (hgz.2.mdifferentiableAt hn) hDz hgz.1

/-- The restricted differential of a composite is the composite of the restricted
differentials. -/
theorem mfderivRestrictEquiv_trans (hf : IsLocalDiffeomorphAt I J n f x)
    (hg : IsLocalDiffeomorphAt J K n g (f x)) (hn : n ≠ 0)
    (hD : D x = (D' (f x)).comap (mfderiv I J f x).toLinearMap)
    (hD' : D' (f x) = (D'' (g (f x))).comap (mfderiv J K g (f x)).toLinearMap) :
    (hf.comp (hg := hg)).mfderivRestrictEquiv hn
      ((hf.mdifferentiableAt hn).eq_comap_mfderiv_comp (hg.mdifferentiableAt hn) hD hD') =
      (hf.mfderivRestrictEquiv hn hD).trans (hg.mfderivRestrictEquiv hn hD') := by
  ext u
  rw [coe_mfderivRestrictEquiv_apply, LinearEquiv.trans_apply, coe_mfderivRestrictEquiv_apply,
    coe_mfderivRestrictEquiv_apply]
  exact mfderiv_comp_apply x (hg.mdifferentiableAt hn) (hf.mdifferentiableAt hn) _

/-- The map of normal spaces induced by the differential of a composite is the composite of the
induced maps. -/
theorem mfderivQuotientEquiv_trans (hf : IsLocalDiffeomorphAt I J n f x)
    (hg : IsLocalDiffeomorphAt J K n g (f x)) (hn : n ≠ 0)
    (hD : D x = (D' (f x)).comap (mfderiv I J f x).toLinearMap)
    (hD' : D' (f x) = (D'' (g (f x))).comap (mfderiv J K g (f x)).toLinearMap) :
    (hf.comp (hg := hg)).mfderivQuotientEquiv hn
      ((hf.mdifferentiableAt hn).eq_comap_mfderiv_comp (hg.mdifferentiableAt hn) hD hD') =
      (hf.mfderivQuotientEquiv hn hD).trans (hg.mfderivQuotientEquiv hn hD') := by
  ext a
  induction a using Submodule.Quotient.induction_on with
  | H u =>
    rw [mfderivQuotientEquiv_mk, LinearEquiv.trans_apply, mfderivQuotientEquiv_mk,
      mfderivQuotientEquiv_mk,
      mfderiv_comp_apply x (hg.mdifferentiableAt hn) (hf.mdifferentiableAt hn)]

end Comp

end Restrict

end IsLocalDiffeomorphAt

namespace PartialDiffeomorph

open TauCeti

omit [CompleteSpace E] in
/-- The differential of a partial diffeomorphism carries a family of subspaces onto its pullback
through the inverse. -/
theorem map_mfderiv_eq_comap_mfderivWithin_symm (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0)
    (D : Π x : M, Submodule 𝕜 (TangentSpace I x)) {x : M} (hx : x ∈ Φ.source) :
    (D x).map (mfderiv I J Φ x).toLinearMap =
      (D (Φ.symm (Φ x))).comap (mfderivWithin J I Φ.symm Φ.symm.source (Φ x)).toLinearMap := by
  have hleft : Φ.symm (Φ x) = x := Φ.left_inv hx
  rw [Φ.symm.mfderivWithin_source (Φ.map_source hx), hleft]
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h : mfderiv J I Φ.symm (Φ x) (mfderiv I J Φ x u) ∈ D x :=
      (Φ.mfderiv_symm_apply_mfderiv_apply hn hx u).symm ▸ hu
    exact Submodule.mem_comap.2 h
  · refine fun hv ↦ ⟨_, Submodule.mem_comap.1 hv, ?_⟩
    have h := Φ.mfderiv_apply_mfderiv_symm_apply hn (Φ.map_source hx) v
    rwa [hleft] at h

section Involutive

variable [IsManifold I (minSmoothness 𝕜 2) M]
  [IsManifold J (minSmoothness 𝕜 2) N]

/-- A partial diffeomorphism whose differential identifies two distributions transports
involutivity from its source to its target. The tangent-space identification is stated as
membership equivalence, so it applies directly to both images and preimages of subspaces under
the differential. -/
theorem isInvolutiveDistributionOn (Φ : PartialDiffeomorph I J M N n)
    (hD : IsInvolutiveDistributionOn I D Φ.source)
    (hn : minSmoothness 𝕜 2 ≤ n)
    (hDD' : ∀ x ∈ Φ.source, ∀ v, v ∈ D x ↔ mfderiv I J Φ x v ∈ D' (Φ x)) :
    IsInvolutiveDistributionOn J D' Φ.target := by
  have hn0 : n ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0 : ℕ∞ω) < 2) (le_minSmoothness.trans hn))
  rw [isInvolutiveDistributionOn_iff]
  intro U hU hUtarget V W hV hW hVD hWD y hy
  let U₀ := Φ.source ∩ Φ ⁻¹' U
  let V₀ := mpullback I J Φ V
  let W₀ := mpullback I J Φ W
  have hU₀ : IsOpen U₀ := Φ.toOpenPartialHomeomorph.isOpen_inter_preimage hU
  have hU₀source : U₀ ⊆ Φ.source := inter_subset_left
  have hΦinv (x : M) (hx : x ∈ Φ.source) : (mfderiv I J Φ x).IsInvertible :=
    (_root_.PartialDiffeomorph.isLocalDiffeomorphAt I J n Φ hx).isInvertible_mfderiv hn0
  have hΦsmooth (x : M) (hx : x ∈ Φ.source) : CMDiffAt n Φ x :=
    (Φ.contMDiffOn x hx).contMDiffAt (Φ.open_source.mem_nhds hx)
  have hV₀ : MDiff[U₀] (T% V₀) := by
    intro x hx
    exact ((hV (Φ x) hx.2).mpullback_vectorField_preimage (hΦsmooth x hx.1)
      (hΦinv x hx.1) (le_minSmoothness.trans hn)).mono inter_subset_right
  have hW₀ : MDiff[U₀] (T% W₀) := by
    intro x hx
    exact ((hW (Φ x) hx.2).mpullback_vectorField_preimage (hΦsmooth x hx.1)
      (hΦinv x hx.1) (le_minSmoothness.trans hn)).mono inter_subset_right
  have hV₀D : ∀ x ∈ U₀, V₀ x ∈ D x := by
    intro x hx
    apply (hDD' x hx.1 _).mpr
    simpa only [V₀, mpullback_apply, (hΦinv x hx.1).self_apply_inverse] using
      hVD (Φ x) hx.2
  have hW₀D : ∀ x ∈ U₀, W₀ x ∈ D x := by
    intro x hx
    apply (hDD' x hx.1 _).mpr
    simpa only [W₀, mpullback_apply, (hΦinv x hx.1).self_apply_inverse] using
      hWD (Φ x) hx.2
  have hyTarget : y ∈ Φ.target := hUtarget hy
  have hxSource : Φ.symm y ∈ Φ.source := Φ.map_target hyTarget
  have hΦx : Φ (Φ.symm y) = y := Φ.right_inv hyTarget
  have hx : Φ.symm y ∈ U₀ := by
    refine ⟨hxSource, ?_⟩
    simpa only [mem_preimage, hΦx] using hy
  have hbr := hD.mlieBracket_mem hU₀ hU₀source hV₀ hW₀ hV₀D hW₀D hx
  have hVy : MDiffAt (T% V) (Φ (Φ.symm y)) :=
    (hV _ hx.2).mdifferentiableAt (hU.mem_nhds hx.2)
  have hWy : MDiffAt (T% W) (Φ (Φ.symm y)) :=
    (hW _ hx.2).mdifferentiableAt (hU.mem_nhds hx.2)
  rw [← mpullback_mlieBracket hVy hWy (hΦsmooth _ hxSource) hn] at hbr
  have hmem := (hDD' (Φ.symm y) hxSource _).mp hbr
  rw [mpullback_apply, (hΦinv _ hxSource).self_apply_inverse, hΦx] at hmem
  exact hmem

omit [CompleteSpace E] in
/-- The pullback of a distribution through the differential of a partial diffeomorphism is
involutive on the source when the distribution is involutive on the target. -/
theorem isInvolutiveDistributionOn_comap_mfderivWithin [CompleteSpace F]
    (Φ : PartialDiffeomorph I J M N n)
    (hD' : IsInvolutiveDistributionOn J D' Φ.target) (hn : minSmoothness 𝕜 2 ≤ n) :
    IsInvolutiveDistributionOn I
      (fun x ↦ (D' (Φ x)).comap (mfderivWithin I J Φ Φ.source x).toLinearMap) Φ.source := by
  have hn0 : n ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0 : ℕ∞ω) < 2) (le_minSmoothness.trans hn))
  refine Φ.symm.isInvolutiveDistributionOn hD' hn fun y hy v ↦ ?_
  have hx : Φ.symm y ∈ Φ.source := Φ.map_target hy
  have hmem : mfderiv J I Φ.symm y v ∈ (D' (Φ (Φ.symm y))).comap
      (mfderivWithin I J Φ Φ.source (Φ.symm y)).toLinearMap ↔ v ∈ D' y := by
    have hright : Φ (Φ.symm y) = y := Φ.right_inv hy
    rw [Submodule.mem_comap, Φ.mfderivWithin_source hx, ContinuousLinearMap.coe_coe,
      Φ.mfderiv_apply_mfderiv_symm_apply hn0 hy, hright]
  exact hmem.symm

end Involutive

end PartialDiffeomorph

namespace TauCeti

section Involutive

variable [IsManifold I (minSmoothness 𝕜 2) M]
  [IsManifold J (minSmoothness 𝕜 2) N]

/-- A diffeomorphism whose differential identifies two distributions transports involutivity.
The tangent-space identification is stated as membership equivalence, so it applies directly
to both images and preimages of subspaces under the differential. -/
theorem IsInvolutiveDistribution.diffeomorph (hD : IsInvolutiveDistribution I D)
    (h : M ≃ₘ^n⟮I, J⟯ N) (hn : minSmoothness 𝕜 2 ≤ n)
    (hDD' : ∀ x v, v ∈ D x ↔ mfderiv I J h x v ∈ D' (h x)) :
    IsInvolutiveDistribution J D' := by
  have hDlocal := hD.isInvolutiveDistributionOn h.toPartialDiffeomorph.source
  -- Use the public characterization because Mathlib keeps the constructor opaque.
  have hcoe : (h.toPartialDiffeomorph.toPartialEquiv : M → N) = h := by
    funext x
    have happ := congrArg (fun e : PartialEquiv M N ↦ e x)
      h.toPartialDiffeomorph_toPartialEquiv
    simpa only [Equiv.toPartialEquiv_apply, Diffeomorph.coe_toEquiv] using happ
  have htarget : h.toPartialDiffeomorph.target = univ := by
    calc
      _ = h.toEquiv.toPartialEquiv.target := congrArg (fun e : PartialEquiv M N ↦ e.target)
        h.toPartialDiffeomorph_toPartialEquiv
      _ = univ := Equiv.toPartialEquiv_target h.toEquiv
  have hlocal := h.toPartialDiffeomorph.isInvolutiveDistributionOn
    (D := D) (D' := D') hDlocal hn (by
      intro x _ v
      rw [hcoe]
      exact hDD' x v)
  rw [← isInvolutiveDistributionOn_univ]
  rw [← htarget]
  exact hlocal

end Involutive

end TauCeti

namespace Diffeomorph

section Membership

omit [CompleteSpace E]

/-- If the differential of `h` carries `D` onto `D'`, then the differential of `h⁻¹` carries `D'`
onto `D`. -/
theorem mem_iff_mfderiv_symm_apply_mem (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (hDD' : ∀ x v, v ∈ D x ↔ mfderiv I J h x v ∈ D' (h x)) (y : N) (w : TangentSpace J y) :
    w ∈ D' y ↔ mfderiv J I h.symm y w ∈ D (h.symm y) := by
  obtain ⟨x, rfl⟩ : ∃ x, h x = y := ⟨h.symm y, h.apply_symm_apply y⟩
  -- Membership of a vector of the model space only depends on the base point up to equality.
  have hcongr : ∀ {x' : M}, x' = x → ∀ v : E,
      ((v : TangentSpace I x') ∈ D x' ↔ (v : TangentSpace I x) ∈ D x) := by
    rintro _ rfl _
    rfl
  refine Iff.trans ?_ (hcongr (h.symm_apply_apply x) _).symm
  refine Iff.trans ?_ (hDD' x _).symm
  rw [h.mfderiv_apply_mfderiv_symm_apply hn x w]

/-- If the differential of `h` carries `D` onto `D'`, then the inverse of the differential of `h`
at `x` carries `D' (h x)` back into `D x`. -/
theorem inverse_mfderiv_apply_mem (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (hDD' : ∀ x v, v ∈ D x ↔ mfderiv I J h x v ∈ D' (h x)) {x : M}
    {w : TangentSpace J (h x)} (hw : w ∈ D' (h x)) :
    (mfderiv I J h x).inverse w ∈ D x :=
  (hDD' x _).2 <| by rwa [(h.isInvertible_mfderiv hn).self_apply_inverse]

/-- If the differentials of `h` and `g` carry `D` onto `D'` and `D'` onto `D''`, then the
differential of the composite carries `D` onto `D''`. -/
theorem mem_iff_mfderiv_trans_apply_mem {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H'' X]
    {D'' : Π z : X, Submodule 𝕜 (TangentSpace K z)} (h : M ≃ₘ^n⟮I, J⟯ N) (g : N ≃ₘ^n⟮J, K⟯ X)
    (hn : n ≠ 0)
    (hDD' : ∀ x v, v ∈ D x ↔ mfderiv I J h x v ∈ D' (h x))
    (hD'D'' : ∀ y w, w ∈ D' y ↔ mfderiv J K g y w ∈ D'' (g y)) (x : M) (v : TangentSpace I x) :
    v ∈ D x ↔ mfderiv I K (h.trans g) x v ∈ D'' ((h.trans g) x) := by
  rw [coe_trans, mfderiv_comp_apply x (g.mdifferentiable hn (h x)) (h.mdifferentiable hn x), hDD',
    hD'D'', Function.comp_apply]

end Membership

open TauCeti

variable [CompleteSpace F] [IsManifold I (minSmoothness 𝕜 2) M]
  [IsManifold J (minSmoothness 𝕜 2) N]

/-- Involutivity is invariant under a diffeomorphism identifying tangent distributions. -/
theorem isInvolutiveDistribution_iff (h : M ≃ₘ^n⟮I, J⟯ N)
    (hn : minSmoothness 𝕜 2 ≤ n)
    (hDD' : ∀ x v, v ∈ D x ↔ mfderiv I J h x v ∈ D' (h x)) :
    IsInvolutiveDistribution I D ↔ IsInvolutiveDistribution J D' := by
  have hn0 : n ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0 : ℕ∞ω) < 2) (le_minSmoothness.trans hn))
  exact ⟨fun hD ↦ hD.diffeomorph h hn hDD',
    fun hD' ↦ hD'.diffeomorph h.symm hn (h.mem_iff_mfderiv_symm_apply_mem hn0 hDD')⟩

/-- A distribution is involutive exactly when its pullback by a diffeomorphism is involutive.
This form expresses the transported distribution directly as the preimage of each tangent
subspace under the differential. -/
@[simp]
theorem isInvolutiveDistribution_comap_mfderiv_iff (h : M ≃ₘ^n⟮I, J⟯ N)
    (hn : minSmoothness 𝕜 2 ≤ n) (D' : Π y : N, Submodule 𝕜 (TangentSpace J y)) :
    IsInvolutiveDistribution I
      (fun x ↦ (D' (h x)).comap (mfderiv I J h x).toLinearMap) ↔
        IsInvolutiveDistribution J D' :=
  h.isInvolutiveDistribution_iff hn (fun _ _ ↦ Iff.rfl)

end Diffeomorph
