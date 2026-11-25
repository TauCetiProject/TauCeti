/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Diffeomorph
import TauCeti.LinearAlgebra.LinearMap.Coprod
import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# Transverse slices of Lie group actions

Let a Lie group `G` act smoothly on a manifold `M`, and let `σ : S → M` be a smooth map, thought
of as a slice through the point `σ s₀`. The **slice map** `(g, s) ↦ g • σ s : G × S → M` sweeps
the slice along the orbits of the action. Its differential at `(1, s₀)` is
`(ξ, v) ↦ ξ_M(σ s₀) + dσ v`. By the inverse function theorem, the slice map is therefore a local
diffeomorphism at `(1, s₀)` exactly when the action is locally free at `σ s₀` (its isotropy
algebra `𝔤_{σ s₀}` is trivial), `dσ` is injective at `s₀`, and the tangent image of `σ` is a
complement of the orbit tangent space `𝔤 · σ s₀`. By equivariance it is then a local
diffeomorphism at `(g, s)` for every `g` and every `s` near `s₀`.

At a locally free point `x`, every complement `W` of `𝔤 · x` gives such a slice, namely the
preimage of the affine subspace `φ x + W` under the extended chart `φ` at `x`.

These are the transverse local charts from which quotient charts of free proper actions are
built: properness of the action makes the slice map injective after shrinking the slice
(`IsLocalDiffeomorphAt.exists_isOpen_smul_slice`), and the slice then parametrises the orbits near
`x`.

## Main results

* `TauCeti.mfderiv_smul_slice_apply`: the differential `(ξ, v) ↦ ξ_M(σ s₀) + dσ v` of the slice
  map at `(1, s₀)`.
* `TauCeti.isLocalDiffeomorphAt_smul_slice_iff`: the slice map is a local diffeomorphism at
  `(1, s₀)` exactly when `𝔤_{σ s₀} = 0`, `dσ` is injective at `s₀` and its range is a complement
  of `𝔤 · σ s₀`.
* `IsLocalDiffeomorphAt.eventually_forall_smul_slice`: a slice map which is a local
  diffeomorphism at `(1, s₀)` is one at `(g, s)` for all `g` and all `s` near `s₀`.
* `TauCeti.surjective_mfderiv_smul_slice_of_surjective_one`: if the differential of a slice map
  is onto at `(1, s₀)`, it is onto at `(g, s₀)` for every `g`.
* `IsLocalDiffeomorphAt.exists_isOpen_smul_slice`: for a proper action at a point with trivial
  stabilizer, a slice map which is a `C^n` local diffeomorphism at `(1, s₀)` is injective and a
  `C^n` local diffeomorphism on `G × U` for some open neighbourhood `U` of `s₀`.
* `TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`: at a locally free point `x`, the chart
  slice `w ↦ φ.symm (φ x + w)` along a complement `W` of `𝔤 · x` gives a slice map which is a
  local diffeomorphism at `(1, 0)`.
* `TauCeti.surjective_mfderiv_smul_slice`, `TauCeti.mfderiv_smul_slice_eq_zero_iff`: for a slice
  along a subspace `V` of `T_x M` with derivative the inclusion, the differential of the slice
  map at `(1, 0)` is onto when `𝔤 · x + V = T_x M`, and vanishes exactly on `𝔤_x × 0` when
  `𝔤 · x ∩ V = 0`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, proof of Theorem 21.10 (the
  map `G × S → M` on a slice transverse to an orbit, and the inverse function theorem).
* Eckhard Meinrenken, *Group actions on manifolds*, lecture notes (2003), proof of Theorem 1.21.
-/

public section

noncomputable section

open Function Set Filter Manifold Topology
open scoped ContDiff Manifold

namespace TauCeti

section Differential

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners 𝕜 F K}
  {S : Type*} [TopologicalSpace S] [ChartedSpace K S]
  {σ : S → M} {s₀ : S}

/-- **Slice maps are differentiable.** If `σ` is differentiable at `s₀`, then the slice map
`(h, s) ↦ h • σ s` is differentiable at `(g, s₀)` for every `g`. -/
theorem mdifferentiableAt_smul_slice [ContMDiffSMul I I' 1 G M]
    (hσ : MDifferentiableAt J I' σ s₀) (g : G) :
    MDifferentiableAt (I.prod J) I' (fun p : G × S ↦ p.1 • σ p.2) (g, s₀) :=
  ((ContMDiffSMul.contMDiff_smul (I := I) (I' := I') (n := 1)).mdifferentiableAt
    one_ne_zero).comp _ (mdifferentiableAt_fst.prodMk (hσ.comp _ mdifferentiableAt_snd))

/-- **The differential of a slice map at the identity.** At `(1, s₀)`, the differential of
`(g, s) ↦ g • σ s` sends `(ξ, v)` to `ξ_M(σ s₀) + dσ v`. -/
theorem mfderiv_smul_slice_apply [ContMDiffSMul I I' 1 G M] (hσ : MDifferentiableAt J I' σ s₀)
    (ξ : GroupLieAlgebra I G) (v : TangentSpace J s₀) :
    mfderiv (I.prod J) I' (fun p : G × S ↦ p.1 • σ p.2) (1, s₀) (ξ, v) =
      fundamentalVectorField I' ξ (σ s₀) + mfderiv J I' σ s₀ v := by
  rw [fundamentalVectorField_apply]
  refine (mfderiv_prod_eq_add_apply (v := ((ξ, v) : E × F))
    (mdifferentiableAt_smul_slice hσ 1)).trans ?_
  -- `simp only [one_smul]` cannot rewrite under `mfderiv`, whose codomain `TangentSpace I' (f s₀)`
  -- depends on the function `f`, so the identity action is rewritten as a function equality.
  have hone : (fun z : S ↦ (1 : G) • σ z) = σ := funext fun z ↦ one_smul G (σ z)
  rw [hone]
  -- The two sides now agree up to projections of the explicit pairs `(ξ, v)` and `(1, s₀)`.
  rfl

/-- **Slice maps are local diffeomorphisms along whole orbits.** If the slice map
`(g, s) ↦ g • σ s` is a `C^n` local diffeomorphism at `(1, s₀)`, then for every `s` near `s₀` it is
one at `(g, s)` for every `g`, because it intertwines left multiplication on `G` with the action
on `M`. -/
theorem _root_.IsLocalDiffeomorphAt.eventually_forall_smul_slice {n : ℕ∞ω} [LieGroup I n G]
    [ContMDiffSMul I I' n G M]
    (h : IsLocalDiffeomorphAt (I.prod J) I' n (fun p : G × S ↦ p.1 • σ p.2) (1, s₀)) :
    ∀ᶠ s in 𝓝 s₀, ∀ g : G,
      IsLocalDiffeomorphAt (I.prod J) I' n (fun p : G × S ↦ p.1 • σ p.2) (g, s) := by
  have hcont : Tendsto (fun s : S ↦ ((1 : G), s)) (𝓝 s₀) (𝓝 (1, s₀)) :=
    (continuous_const.prodMk continuous_id).tendsto s₀
  filter_upwards [hcont.eventually h.eventually] with s hs g
  -- Left multiplication by `g` on the first factor is a diffeomorphism of `G × S`.
  have : ContMDiffSMul I I n G G := ⟨contMDiff_mul I n⟩
  let T : (G × S) ≃ₘ^n⟮I.prod J, I.prod J⟯ (G × S) :=
    (Diffeomorph.smul I I n g).prodCongr (Diffeomorph.refl J S n)
  have hT : (fun p : G × S ↦ p.1 • σ p.2) ∘ T =
      Diffeomorph.smul I I' n g (M := M) ∘ fun p : G × S ↦ p.1 • σ p.2 :=
    funext fun p ↦ by simp [T, mul_smul]
  simpa [T] using hs.of_comp_diffeomorph_eq T (Diffeomorph.smul I I' n g) le_rfl hT

/-- **The differential of a slice map is onto along whole orbits.** For a slice `σ`
differentiable at `s₀`, if the differential of `(h, s) ↦ h • σ s` at `(1, s₀)` is onto, then so is
its differential at `(g, s₀)` for every `g`. -/
theorem surjective_mfderiv_smul_slice_of_surjective_one [LieGroup I 1 G]
    [ContMDiffSMul I I' 1 G M] (hσ : MDifferentiableAt J I' σ s₀)
    (hsurj : Surjective (mfderiv (I.prod J) I' (fun p : G × S ↦ p.1 • σ p.2) (1, s₀))) (g : G) :
    Surjective (mfderiv (I.prod J) I' (fun p : G × S ↦ p.1 • σ p.2) (g, s₀)) := by
  set f : G × S → M := fun p ↦ p.1 • σ p.2
  have hf (h : G) : MDifferentiableAt (I.prod J) I' f (h, s₀) := mdifferentiableAt_smul_slice hσ h
  -- Left translation `T` by `g` on the `G` factor intertwines the slice map `f` with the
  -- diffeomorphism `g • ·` of `M`, whose differential is invertible.
  set T : G × S → G × S := fun p ↦ (g * p.1, p.2)
  have hT : ContMDiff (I.prod J) (I.prod J) 1 T :=
    (contMDiff_const.mul contMDiff_fst).prodMk contMDiff_snd
  have hT1 : T (1, s₀) = (g, s₀) := by simp [T]
  have hcomm : f ∘ T = Diffeomorph.smul I I' 1 g ∘ f :=
    funext fun p ↦ by simp only [Function.comp_apply, f, T, Diffeomorph.smul_apply, mul_smul]
  have h₁ := mfderiv_comp (1, s₀) (hT1 ▸ hf g) (hT.mdifferentiableAt one_ne_zero)
  have h₂ := mfderiv_comp (1, s₀)
    ((Diffeomorph.smul I I' 1 g).contMDiff.mdifferentiableAt one_ne_zero) (hf 1)
  rw [hcomm, h₂, hT1] at h₁
  have hs : Surjective ((mfderiv I' I' (Diffeomorph.smul I I' 1 g) (f (1, s₀))).comp
      (mfderiv (I.prod J) I' f (1, s₀))) :=
    ((Diffeomorph.smul I I' 1 g).isInvertible_mfderiv one_ne_zero).surjective.comp hsurj
  rw [h₁] at hs
  exact Surjective.of_comp hs

/-- **Shrinking a transverse slice of a proper action.** If the slice map `(g, s) ↦ g • σ s` is a
`C^n` local diffeomorphism at `(1, s₀)` and `σ s₀` has trivial stabilizer under a proper action of
`G`, then on some open neighbourhood `U` of `s₀` the slice map is both injective and a `C^n` local
diffeomorphism on the whole tube `G × U`. -/
theorem _root_.IsLocalDiffeomorphAt.exists_isOpen_smul_slice {n : ℕ∞ω} [LieGroup I n G]
    [ContMDiffSMul I I' n G M] [ProperSMul G M]
    (h : IsLocalDiffeomorphAt (I.prod J) I' n (fun p : G × S ↦ p.1 • σ p.2) (1, s₀))
    (hfree : MulAction.stabilizer G (σ s₀) = ⊥) :
    ∃ U : Set S, IsOpen U ∧ s₀ ∈ U ∧
      InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) ∧
      IsLocalDiffeomorphOn (I.prod J) I' n (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) := by
  have hσ : ContinuousAt σ s₀ := by
    have hcomp : ContinuousAt (fun s : S ↦ (1 : G) • σ s) s₀ :=
      h.contMDiffAt.continuousAt.comp_of_eq
        (continuous_const.prodMk continuous_id).continuousAt rfl
    simpa [one_smul] using hcomp
  obtain ⟨N, hN, hinjN⟩ := h.exists_mem_nhds_injOn
  obtain ⟨V, hV, hinjV⟩ := ProperSMul.exists_mem_nhds_injOn_smul_slice hσ hfree hN hinjN
  obtain ⟨U, hU_sub, hU_open, hs₀U⟩ :=
    mem_nhds_iff.1 (inter_mem h.eventually_forall_smul_slice hV)
  exact ⟨U, hU_open, hs₀U, hinjV.mono (prod_mono_right fun _ hu ↦ (hU_sub hu).2),
    fun ⟨⟨g, _⟩, _, hu⟩ ↦ (hU_sub hu).1 g⟩

end Differential

section Real

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [BoundarylessManifold I G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]

/-- **Transverse slices.** Let `σ` be smooth on an open neighbourhood of `s₀`. The slice map
`(g, s) ↦ g • σ s` is a smooth local diffeomorphism at `(1, s₀)` exactly when the action is
locally free at `σ s₀`, the differential of `σ` at `s₀` is injective, and its range is a
complement of the orbit tangent space `𝔤 · σ s₀`. -/
theorem isLocalDiffeomorphAt_smul_slice_iff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    {S : Type*} [TopologicalSpace S] [ChartedSpace K S] [IsManifold J ∞ S]
    [BoundarylessManifold J S] {σ : S → M} {s₀ : S} {t : Set S} (hσ : ContMDiffOn J I' ∞ σ t)
    (ht : IsOpen t) (hs₀ : s₀ ∈ t) :
    IsLocalDiffeomorphAt (I.prod J) I' ∞ (fun p : G × S ↦ p.1 • σ p.2) (1, s₀) ↔
      (InfinitesimalAction.fundamental I G I' M).isotropy (σ s₀) = ⊥ ∧
        Injective (mfderiv J I' σ s₀) ∧
        IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent (σ s₀))
          (LinearMap.range (mfderiv J I' σ s₀).toLinearMap) := by
  have hf : ContMDiffOn (I.prod J) I' ∞ (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ t) :=
    (ContMDiffSMul.contMDiff_smul (I := I) (I' := I') (n := ∞)).comp_contMDiffOn
      (contMDiffOn_fst.prodMk (hσ.comp (s := univ ×ˢ t) contMDiffOn_snd fun _ hp ↦ hp.2))
  have hdσ : MDifferentiableAt J I' σ s₀ :=
    (hσ.contMDiffAt (ht.mem_nhds hs₀)).mdifferentiableAt (by simp)
  -- The differential at `(1, s₀)` is `(ξ, v) ↦ ξ_M(σ s₀) + dσ v`.
  have hL' (ξ : GroupLieAlgebra I G) (v : TangentSpace J s₀) :
      mfderiv (I.prod J) I' (fun p : G × S ↦ p.1 • σ p.2) (1, s₀) (ξ, v) =
        ((InfinitesimalAction.fundamental I G I' M).eval (σ s₀)).coprod
          (mfderiv J I' σ s₀).toLinearMap (ξ, v) := by
    rw [mfderiv_smul_slice_apply hdσ, LinearMap.coprod_apply, InfinitesimalAction.eval_apply,
      InfinitesimalAction.fundamental_apply, ContinuousLinearMap.coe_coe]
  have hL : ⇑(mfderiv (I.prod J) I' (fun p : G × S ↦ p.1 • σ p.2) (1, s₀)) =
      ⇑(((InfinitesimalAction.fundamental I G I' M).eval (σ s₀)).coprod
        (mfderiv J I' σ s₀).toLinearMap) :=
    funext fun p ↦ hL' p.1 p.2
  rw [isLocalDiffeomorphAt_iff_exists_mfderiv_eq hf (isOpen_univ.prod ht) ⟨mem_univ _, hs₀⟩
    BoundarylessManifold.isInteriorPoint (by simp), InfinitesimalAction.isotropy_eq_bot_iff,
    InfinitesimalAction.orbitTangent_eq_range, ← ContinuousLinearMap.coe_coe (mfderiv J I' σ s₀),
    ← LinearMap.bijective_coprod_iff, ← hL]
  -- By the open mapping theorem, a bijective continuous linear map between Banach spaces is a
  -- continuous linear equivalence.
  refine ⟨fun ⟨e, he⟩ ↦ he ▸ e.bijective, fun hb ↦ ?_⟩
  let L : E × F →L[ℝ] E' := mfderiv (I.prod J) I' (fun p : G × S ↦ p.1 • σ p.2) (1, s₀)
  have hLb : Bijective L := hb
  let e := ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot_of_injective hLb.1)
    (LinearMap.range_eq_top_of_surjective _ hLb.2)
  exact ⟨e, ContinuousLinearMap.ext fun _ ↦ rfl⟩

/-- **Chart slices at locally free points.** Let `x` be a point where the action is locally free,
let `φ` be the extended chart at `x`, and let `W` be a complement of the orbit tangent space
`𝔤 · x` in `T_x M`, which is the model space `E'`. Then the slice map
`(g, w) ↦ g • φ.symm (φ x + w)` on `G × W` is a smooth local diffeomorphism at `(1, 0)`. -/
theorem isLocalDiffeomorphAt_smul_extChartAt_symm [FiniteDimensional ℝ E'] [I'.Boundaryless] {x : M}
    (hx : (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥) {W : Submodule ℝ E'}
    (hW : IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) W) :
    IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, W)) I' ∞
      (fun p : G × W ↦ p.1 • (extChartAt I' x).symm (extChartAt I' x x + p.2)) (1, 0) := by
  set φ := extChartAt I' x with hφ
  -- The slice is the preimage under `φ` of the affine subspace `φ x + W`.
  set τ : W → E' := fun w ↦ φ x + w with hτ
  have hτd : HasFDerivAt τ W.subtypeL 0 := W.subtypeL.hasFDerivAt.const_add (φ x)
  have hτsmooth : ContMDiff 𝓘(ℝ, W) 𝓘(ℝ, E') ∞ τ :=
    (contDiff_const.add W.subtypeL.contDiff).contMDiff
  have hτ0 : τ 0 = φ x := by simp [hτ]
  have ht : IsOpen (τ ⁻¹' φ.target) :=
    (isOpen_extChartAt_target x).preimage hτsmooth.continuous
  have h0t : (0 : W) ∈ τ ⁻¹' φ.target := by
    rw [mem_preimage, hτ0]
    exact mem_extChartAt_target x
  have hσ : ContMDiffOn 𝓘(ℝ, W) I' ∞ (φ.symm ∘ τ) (τ ⁻¹' φ.target) :=
    (contMDiffOn_extChartAt_symm x).comp hτsmooth.contMDiffOn fun _ hw ↦ hw
  have hx0 : (φ.symm ∘ τ) 0 = x := by rw [comp_apply, hτ0, hφ, extChartAt_to_inv]
  -- The differential of the slice at `0` is the inclusion of `W`.
  have hd : ⇑(mfderiv 𝓘(ℝ, W) I' (φ.symm ∘ τ) 0) = W.subtype := by
    have hsymm : mfderiv 𝓘(ℝ, E') I' φ.symm (φ x) = ContinuousLinearMap.id ℝ E' := by
      rw [← mfderivWithin_univ, ← I'.range_eq_univ, hφ]
      exact mfderivWithin_range_extChartAt_symm
    have hsymmd : MDifferentiableAt 𝓘(ℝ, E') I' φ.symm (τ 0) :=
      ((contMDiffOn_extChartAt_symm (n := ∞) x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds h0t)).mdifferentiableAt (by simp)
    rw [mfderiv_comp (0 : W) hsymmd hτd.hasMFDerivAt.mdifferentiableAt, hτd.hasMFDerivAt.mfderiv,
      hτ0, hsymm]
    -- `id ∘ W.subtypeL` is `W.subtype`; `simp` cannot see this through the identification of
    -- `TangentSpace 𝓘(ℝ, E') (φ x)` with `E'`, but the two maps agree by definition.
    rfl
  refine (isLocalDiffeomorphAt_smul_slice_iff (G := G) hσ ht h0t).2 ⟨?_, ?_, ?_⟩
  · rwa [hx0]
  · rw [hd]
    exact W.injective_subtype
  · have hrange : LinearMap.range (mfderiv 𝓘(ℝ, W) I' (φ.symm ∘ τ) 0).toLinearMap = W := by
      rw [LinearMap.ext (congrFun hd)]
      exact W.range_subtype
    rw [hrange, hx0]
    exact hW

section SliceDifferential

omit [BoundarylessManifold I G]

variable {x : M} {V : Submodule ℝ E'} {σ : V → M}

/-- The differential of the slice map along a linear slice, as `(ξ, v) ↦ ξ_M(x) + ι v` for the
inclusion `ι` of `V` into `T_x M`. -/
private theorem mfderiv_smul_slice_eq_coprod (ι : V →ₗ[ℝ] TangentSpace I' x)
    (hι : ∀ v, ι v = (v : E')) (hσd : MDifferentiableAt 𝓘(ℝ, V) I' σ 0) (hσ0 : σ 0 = x)
    (hσL : ∀ v : V, mfderiv 𝓘(ℝ, V) I' σ 0 v = (v : E')) :
    ⇑(mfderiv (I.prod 𝓘(ℝ, V)) I' (fun p : G × V ↦ p.1 • σ p.2) (1, 0)) =
      ⇑(((InfinitesimalAction.fundamental I G I' M).eval x).coprod ι) := by
  have : ContMDiffSMul I I' 1 G M := ContMDiffSMul.of_le (M := M) ENat.LEInfty.out
  refine funext fun p : GroupLieAlgebra I G × V ↦ ?_
  refine (mfderiv_smul_slice_apply hσd p.1 p.2).trans ?_
  rw [hσL, hσ0, LinearMap.coprod_apply, InfinitesimalAction.eval_apply,
    InfinitesimalAction.fundamental_apply, hι]

/-- **Linear slices are transverse.** Let `V` be a subspace of `T_x M` which together with the
orbit tangent space `𝔤 · x` spans `T_x M`, and `σ : V → M` a slice through `σ 0 = x` with
derivative the inclusion of `V` at `0`. Then the slice map `(g, v) ↦ g • σ v` has surjective
differential at `(1, 0)`. -/
theorem surjective_mfderiv_smul_slice
    (hV : (InfinitesimalAction.fundamental I G I' M).orbitTangent x ⊔ V = ⊤)
    (hσd : MDifferentiableAt 𝓘(ℝ, V) I' σ 0) (hσ0 : σ 0 = x)
    (hσL : ∀ v : V, mfderiv 𝓘(ℝ, V) I' σ 0 v = (v : E')) :
    Surjective (mfderiv (I.prod 𝓘(ℝ, V)) I' (fun p : G × V ↦ p.1 • σ p.2) (1, 0)) := by
  let ι : V →ₗ[ℝ] TangentSpace I' x := V.subtype
  have hι : LinearMap.range ι = V := Submodule.range_subtype V
  have hrange : LinearMap.range (((InfinitesimalAction.fundamental I G I' M).eval x).coprod ι) =
      ⊤ := by
    rw [LinearMap.range_coprod, ← InfinitesimalAction.orbitTangent_eq_range, hι]
    exact hV
  intro w
  obtain ⟨p, hp⟩ := LinearMap.range_eq_top.mp hrange w
  exact ⟨p, (congrFun (mfderiv_smul_slice_eq_coprod (I := I) (G := G) ι (fun _ ↦ rfl) hσd hσ0
    hσL) p).trans hp⟩

/-- **The kernel of the differential of a slice map.** Let `V` be a subspace of `T_x M` meeting
the orbit tangent space `𝔤 · x` only in `0`, and `σ : V → M` a slice through `σ 0 = x` with
derivative the inclusion of `V` at `0`. Then the differential of `(g, v) ↦ g • σ v` at `(1, 0)`
vanishes exactly on `𝔤_x × 0`, where `𝔤_x` is the isotropy algebra. -/
theorem mfderiv_smul_slice_eq_zero_iff
    (hV : Disjoint ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) V)
    (hσd : MDifferentiableAt 𝓘(ℝ, V) I' σ 0) (hσ0 : σ 0 = x)
    (hσL : ∀ v : V, mfderiv 𝓘(ℝ, V) I' σ 0 v = (v : E')) (ξ : GroupLieAlgebra I G) (v : V) :
    mfderiv (I.prod 𝓘(ℝ, V)) I' (fun p : G × V ↦ p.1 • σ p.2) (1, 0) (ξ, v) = 0 ↔
      ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy x ∧ v = 0 := by
  let ι : V →ₗ[ℝ] TangentSpace I' x := V.subtype
  have hι : LinearMap.range ι = V := Submodule.range_subtype V
  have hdisj : Disjoint (LinearMap.range ((InfinitesimalAction.fundamental I G I' M).eval x))
      (LinearMap.range ι) := by
    rw [← InfinitesimalAction.orbitTangent_eq_range, hι]
    exact hV
  have hker : LinearMap.ker (((InfinitesimalAction.fundamental I G I' M).eval x).coprod ι) =
      (LinearMap.ker ((InfinitesimalAction.fundamental I G I' M).eval x)).prod ⊥ := by
    rw [LinearMap.ker_coprod_of_disjoint_range _ _ hdisj]
    congr 1
    exact Submodule.ker_subtype V
  rw [congrFun (mfderiv_smul_slice_eq_coprod (I := I) (G := G) ι (fun _ ↦ rfl) hσd hσ0 hσL)
    (ξ, v)]
  refine (LinearMap.mem_ker (f := ((InfinitesimalAction.fundamental I G I' M).eval x).coprod ι)
    (y := (ξ, v))).symm.trans ?_
  rw [hker, Submodule.mem_prod, Submodule.mem_bot, LinearMap.mem_ker,
    InfinitesimalAction.mem_isotropy_iff, InfinitesimalAction.eval_apply]

end SliceDifferential

end Real

end TauCeti
