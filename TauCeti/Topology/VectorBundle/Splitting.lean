/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.Algebra.Exact.Split
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Section

/-!
# Splitting exact sequences of vector bundles

Bundle maps `p : E₁ → E₂` are encoded as sections of the Hom bundle `x ↦ E₁ x →L[𝕜] E₂ x`, and
continuity always means continuity of such a section. A continuous Hom-bundle section `p` whose
fibre maps have continuous right inverses has a continuous right inverse, which is again a
continuous Hom-bundle section, provided the base is normal and paracompact
(`Continuous.exists_continuous_clm_bundle_rightInverse`). Dually, a continuous Hom-bundle section
with fibrewise continuous left inverses has a continuous left inverse
(`Continuous.exists_continuous_clm_bundle_leftInverse`). For finite-rank bundles these fibrewise
hypotheses are just surjectivity and injectivity. Consequently every short exact sequence
`0 → E₁ → E₂ → E₃ → 0` of finite-rank bundles over a normal paracompact base splits:
`E₂` is isomorphic to the Whitney sum `E₁ ×ᵇ E₃` by a homeomorphism of total spaces which is
linear on fibres (`TauCeti.exists_bundleHomeomorph_prod_of_exact`). No metric is used, and the
scalars may be `ℝ` or `ℂ`.

The argument is local-to-global. Near a point `x₀`, extend a right inverse `R` of `p x₀` to a
Hom-bundle section `r` continuous near `x₀` (`FiberBundle.continuousOn_extend`). Then
`p ∘ r` is a continuous section of the endomorphism bundle of `E₂` which is the identity at `x₀`,
hence invertible near `x₀`, and `r ∘ (p ∘ r)⁻¹` is a continuous local right inverse
(`ContinuousOn.exists_continuousOn_clm_bundle_rightInverse`). The right inverses of `p x` form an
affine subspace, so local right inverses glue along a partition of unity
(`TauCeti.exists_continuous_section_map_eq_of_local`).

The model fibres may be Banach spaces in the four one-sided inverse theorems, as long as the fibre
maps split. The three splitting theorems use finite rank, over a complete scalar field, to see that
a continuous fibrewise bijective bundle map is a homeomorphism: the outer bundles `E₁` and `E₃`
have finite rank in `TauCeti.exists_bundleHomeomorph_prod_of_rightInverse` and
`TauCeti.exists_bundleHomeomorph_prod_of_exact`, and the middle bundle `E₂` has finite rank in
`TauCeti.exists_bundleHomeomorph_prod_of_leftInverse`.

## Main results

* `ContinuousOn.exists_continuousOn_clm_bundle_rightInverse`,
  `ContinuousOn.exists_continuousOn_clm_bundle_leftInverse`: local one-sided inverses near a point
  where the fibre map splits.
* `Continuous.exists_continuous_clm_bundle_rightInverse`,
  `Continuous.exists_continuous_clm_bundle_leftInverse`: global one-sided inverses over a normal
  paracompact base.
* `TauCeti.exists_bundleHomeomorph_prod_of_rightInverse`: a fibrewise exact sequence of
  finite-rank outer bundles with a continuous section of the projection identifies the middle
  bundle with the Whitney sum of the outer ones.
* `TauCeti.exists_bundleHomeomorph_prod_of_leftInverse`: the same for a continuous retraction of
  the inclusion, when the middle bundle has finite rank.
* `TauCeti.exists_bundleHomeomorph_prod_of_exact`: every short exact sequence of finite-rank
  bundles over a normal paracompact base splits.

## References

* M. F. Atiyah, *K-Theory*, Chapter I.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.1, where the splitting is obtained from an inner
  product by taking orthogonal complements.
-/

public section

open Bundle Filter Function Set
open scoped Topology

section Inverse

variable {𝕜 B F₁ F₂ : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₁ E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- An endomorphism Hom-bundle section `q` of `E₁`, continuous on a neighbourhood `W` of `x₀` and
the identity at `x₀`, is invertible on a smaller neighbourhood of `x₀`, where its fibrewise
inverse is again continuous. This is the common local step of the two one-sided inverse
theorems below. -/
private theorem ContinuousOn.exists_continuousOn_clm_bundle_inverse_of_eq_id [CompleteSpace F₁]
    {q : ∀ x, E₁ x →L[𝕜] E₁ x} {W : Set B} {x₀ : B}
    (hq : ContinuousOn (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁)
      (E := fun x ↦ E₁ x →L[𝕜] E₁ x) x (q x)) W) (hW : W ∈ 𝓝 x₀)
    (hq₀ : q x₀ = ContinuousLinearMap.id 𝕜 (E₁ x₀)) :
    ∃ U ∈ 𝓝 x₀, U ⊆ W ∧ (∀ x ∈ U, (q x).IsInvertible) ∧
      ContinuousOn (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁)
        (E := fun x ↦ E₁ x →L[𝕜] E₁ x) x (q x).inverse) U := by
  have hinv : (q x₀).IsInvertible := by
    rw [hq₀, ← ContinuousLinearEquiv.coe_refl]
    exact ContinuousLinearMap.isInvertible_equiv
  exact ⟨W ∩ {x | (q x).IsInvertible},
    inter_mem hW ((hq.continuousAt hW).eventually_clm_bundle_isInvertible hinv),
    inter_subset_left, fun _ hx ↦ hx.2,
    (hq.mono inter_subset_left).clm_bundle_inverse fun _ hx ↦ hx.2⟩

/-- Let `p : E₁ → E₂` be a Hom-bundle section which is continuous on a neighbourhood `u` of `x₀`,
and whose fibre map at `x₀` has a continuous right inverse. Then `p` has a right inverse which is
a Hom-bundle section continuous on a neighbourhood of `x₀`. The model fibre of `E₂` must be
complete. -/
theorem ContinuousOn.exists_continuousOn_clm_bundle_rightInverse [CompleteSpace F₂]
    {p : ∀ x, E₁ x →L[𝕜] E₂ x} {u : Set B} {x₀ : B}
    (hp : ContinuousOn (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (p x)) u) (hu : u ∈ 𝓝 x₀)
    (h : (p x₀).HasRightInverse) :
    ∃ U ∈ 𝓝 x₀, ∃ s : ∀ x, E₂ x →L[𝕜] E₁ x,
      ContinuousOn (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
        (E := fun x ↦ E₂ x →L[𝕜] E₁ x) x (s x)) U ∧
      ∀ x ∈ U, (p x).comp (s x) = ContinuousLinearMap.id 𝕜 (E₂ x) := by
  -- Extend the fibre inverse at `x₀` to a Hom-bundle section `r` continuous near `x₀`.
  let r := FiberBundle.extend (F₂ →L[𝕜] F₁) (E := fun x ↦ E₂ x →L[𝕜] E₁ x) h.rightInverse
  let e := trivializationAt (F₂ →L[𝕜] F₁) (fun x ↦ E₂ x →L[𝕜] E₁ x) x₀
  have hW : u ∩ e.baseSet ∈ 𝓝 x₀ :=
    inter_mem hu (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x₀))
  have hr := (FiberBundle.continuousOn_extend (F₂ →L[𝕜] F₁)
    (E := fun x ↦ E₂ x →L[𝕜] E₁ x) h.rightInverse).mono (inter_subset_right (s := u))
  -- `p ∘ r` is the identity at `x₀`, so it is invertible near `x₀`, and `r ∘ (p ∘ r)⁻¹` works.
  obtain ⟨U, hU, hUW, hinv, hcont⟩ :=
    ((hp.mono inter_subset_left).clm_bundle_comp hr).exists_continuousOn_clm_bundle_inverse_of_eq_id
      hW (ContinuousLinearMap.ext fun w ↦ by
        simp [FiberBundle.extend_apply_self, h.rightInverse_rightInverse w])
  refine ⟨U, hU, fun x ↦ (r x).comp ((p x).comp (r x)).inverse,
    (hr.mono hUW).clm_bundle_comp hcont, fun x hx ↦ ?_⟩
  rw [← ContinuousLinearMap.comp_assoc]
  exact (hinv x hx).self_comp_inverse

/-- Let `i : E₁ → E₂` be a Hom-bundle section which is continuous on a neighbourhood `u` of `x₀`,
and whose fibre map at `x₀` has a continuous left inverse. Then `i` has a left inverse which is
a Hom-bundle section continuous on a neighbourhood of `x₀`. The model fibre of `E₁` must be
complete. This is the bundle counterpart of `ContinuousAt.exists_continuousAt_leftInverse` for
operator families. -/
theorem ContinuousOn.exists_continuousOn_clm_bundle_leftInverse [CompleteSpace F₁]
    {i : ∀ x, E₁ x →L[𝕜] E₂ x} {u : Set B} {x₀ : B}
    (hi : ContinuousOn (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (i x)) u) (hu : u ∈ 𝓝 x₀)
    (h : (i x₀).HasLeftInverse) :
    ∃ U ∈ 𝓝 x₀, ∃ t : ∀ x, E₂ x →L[𝕜] E₁ x,
      ContinuousOn (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
        (E := fun x ↦ E₂ x →L[𝕜] E₁ x) x (t x)) U ∧
      ∀ x ∈ U, (t x).comp (i x) = ContinuousLinearMap.id 𝕜 (E₁ x) := by
  -- Extend the fibre inverse at `x₀` to a Hom-bundle section `l` continuous near `x₀`.
  let l := FiberBundle.extend (F₂ →L[𝕜] F₁) (E := fun x ↦ E₂ x →L[𝕜] E₁ x) h.leftInverse
  let e := trivializationAt (F₂ →L[𝕜] F₁) (fun x ↦ E₂ x →L[𝕜] E₁ x) x₀
  have hW : u ∩ e.baseSet ∈ 𝓝 x₀ :=
    inter_mem hu (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x₀))
  have hl := (FiberBundle.continuousOn_extend (F₂ →L[𝕜] F₁)
    (E := fun x ↦ E₂ x →L[𝕜] E₁ x) h.leftInverse).mono (inter_subset_right (s := u))
  -- `l ∘ i` is the identity at `x₀`, so it is invertible near `x₀`, and `(l ∘ i)⁻¹ ∘ l` works.
  obtain ⟨U, hU, hUW, hinv, hcont⟩ :=
    (hl.clm_bundle_comp (hi.mono inter_subset_left)).exists_continuousOn_clm_bundle_inverse_of_eq_id
      hW (ContinuousLinearMap.ext fun v ↦ by
        simp [FiberBundle.extend_apply_self, h.leftInverse_leftInverse v])
  refine ⟨U, hU, fun x ↦ ((l x).comp (i x)).inverse.comp (l x),
    hcont.clm_bundle_comp (hl.mono hUW), fun x hx ↦ ?_⟩
  rw [ContinuousLinearMap.comp_assoc]
  exact (hinv x hx).inverse_comp_self

variable [NormedAlgebra ℝ 𝕜] [NormalSpace B] [ParacompactSpace B]

/-- A continuous Hom-bundle section `p : E₁ → E₂` over a normal paracompact base, whose fibre
maps all have continuous right inverses, has a right inverse which is again a continuous
Hom-bundle section. For finite-rank bundles the hypothesis says that `p` is fibrewise
surjective. -/
theorem Continuous.exists_continuous_clm_bundle_rightInverse [CompleteSpace F₂]
    {p : ∀ x, E₁ x →L[𝕜] E₂ x}
    (hp : Continuous fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (p x))
    (h : ∀ x, (p x).HasRightInverse) :
    ∃ s : ∀ x, E₂ x →L[𝕜] E₁ x,
      Continuous (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun x ↦ E₂ x →L[𝕜] E₁ x) x (s x)) ∧
      ∀ x, (p x).comp (s x) = ContinuousLinearMap.id 𝕜 (E₂ x) :=
  TauCeti.exists_continuous_section_map_eq_of_local
    (fun x ↦ (ContinuousLinearMap.postcomp (E₂ x) (p x)).toLinearMap)
    (fun x ↦ ContinuousLinearMap.id 𝕜 (E₂ x))
    fun x₀ ↦ hp.continuousOn.exists_continuousOn_clm_bundle_rightInverse univ_mem (h x₀)

/-- A continuous Hom-bundle section `i : E₁ → E₂` over a normal paracompact base, whose fibre
maps all have continuous left inverses, has a left inverse which is again a continuous
Hom-bundle section. For finite-rank bundles the hypothesis says that `i` is fibrewise
injective. -/
theorem Continuous.exists_continuous_clm_bundle_leftInverse [CompleteSpace F₁]
    {i : ∀ x, E₁ x →L[𝕜] E₂ x}
    (hi : Continuous fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (i x))
    (h : ∀ x, (i x).HasLeftInverse) :
    ∃ t : ∀ x, E₂ x →L[𝕜] E₁ x,
      Continuous (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun x ↦ E₂ x →L[𝕜] E₁ x) x (t x)) ∧
      ∀ x, (t x).comp (i x) = ContinuousLinearMap.id 𝕜 (E₁ x) :=
  TauCeti.exists_continuous_section_map_eq_of_local
    (fun x ↦ (ContinuousLinearMap.precomp (E₁ x) (i x)).toLinearMap)
    (fun x ↦ ContinuousLinearMap.id 𝕜 (E₁ x))
    fun x₀ ↦ hi.continuousOn.exists_continuousOn_clm_bundle_leftInverse univ_mem (h x₀)

end Inverse

namespace TauCeti

section Exact

variable {𝕜 B F₁ F₂ F₃ : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₁ E₂ E₃ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)] [∀ x, TopologicalSpace (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  [CompleteSpace 𝕜] {i : ∀ x, E₁ x →L[𝕜] E₂ x} {p : ∀ x, E₂ x →L[𝕜] E₃ x}

/-- Let `0 → E₁ → E₂ → E₃ → 0` be fibrewise exact, with `i : E₁ → E₂` and `p : E₂ → E₃`, and
let `s` be a right inverse of `p`. If `i` and `s` are continuous Hom-bundle sections and `E₁` and
`E₃` have finite rank, then `(v, w) ↦ i v + s w` is a homeomorphism from the Whitney sum
`E₁ ×ᵇ E₃` onto `E₂`, linear on fibres. -/
theorem exists_bundleHomeomorph_prod_of_rightInverse
    [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₃]
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
    {s : ∀ x, E₃ x →L[𝕜] E₂ x}
    (hi : Continuous fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (i x))
    (hs : Continuous fun x ↦ TotalSpace.mk' (F₃ →L[𝕜] F₂)
      (E := fun x ↦ E₃ x →L[𝕜] E₂ x) x (s x))
    (hinj : ∀ x, Injective (i x)) (hexact : ∀ x, (i x).range = (p x).ker)
    (hps : ∀ x, (p x).comp (s x) = ContinuousLinearMap.id 𝕜 (E₃ x)) :
    ∃ h : TotalSpace (F₁ × F₃) (E₁ ×ᵇ E₃) ≃ₜ TotalSpace F₂ E₂,
      ∀ (x : B) (v : E₁ x) (w : E₃ x), h ⟨x, (v, w)⟩ = ⟨x, i x v + s x w⟩ := by
  -- The fibre components of a point of the Whitney sum depend continuously on it.
  have hdiag := (FiberBundle.Prod.isInducing_diag F₁ E₁ F₃ E₃).continuous
  have h₁ := (hi.comp (FiberBundle.continuous_proj (F₁ × F₃) (E₁ ×ᵇ E₃))).clm_bundle_apply
    (continuous_fst.comp hdiag)
  have h₃ := (hs.comp (FiberBundle.continuous_proj (F₁ × F₃) (E₁ ×ᵇ E₃))).clm_bundle_apply
    (continuous_snd.comp hdiag)
  -- Fibrewise, `(v, w) ↦ i v + s w` is the splitting isomorphism of the exact sequence.
  have hbij (x : B) : Bijective ((i x).coprod (s x)) :=
    (LinearMap.exact_iff.2 (hexact x).symm).bijective_coprod_of_comp_eq_id (hinj x)
      congr(ContinuousLinearMap.toLinearMap $(hps x))
  obtain ⟨h, hh⟩ := exists_bundleHomeomorph_of_bijective (fun x ↦ (i x).coprod (s x))
    ((h₁.add_totalSpace 𝕜 h₃).congr fun q ↦ by rw [ContinuousLinearMap.coprod_apply]) hbij
  exact ⟨h, fun x v w ↦ by rw [hh, ContinuousLinearMap.coprod_apply]⟩

/-- Let `0 → E₁ → E₂ → E₃ → 0` be fibrewise exact, with `i : E₁ → E₂` and `p : E₂ → E₃`, and
let `t` be a left inverse of `i`. If `t` and `p` are continuous Hom-bundle sections and `E₂` has
finite rank, then `u ↦ (t u, p u)` is a homeomorphism from `E₂` onto the Whitney sum `E₁ ×ᵇ E₃`,
linear on fibres. -/
theorem exists_bundleHomeomorph_prod_of_leftInverse [FiniteDimensional 𝕜 F₂]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
    {t : ∀ x, E₂ x →L[𝕜] E₁ x}
    (ht : Continuous fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
      (E := fun x ↦ E₂ x →L[𝕜] E₁ x) x (t x))
    (hp : Continuous fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
      (E := fun x ↦ E₂ x →L[𝕜] E₃ x) x (p x))
    (hsurj : ∀ x, Surjective (p x)) (hexact : ∀ x, (i x).range = (p x).ker)
    (hti : ∀ x, (t x).comp (i x) = ContinuousLinearMap.id 𝕜 (E₁ x)) :
    ∃ h : TotalSpace F₂ E₂ ≃ₜ TotalSpace (F₁ × F₃) (E₁ ×ᵇ E₃),
      ∀ (x : B) (u : E₂ x), h ⟨x, u⟩ = ⟨x, (t x u, p x u)⟩ := by
  -- A map into the Whitney sum is continuous once both of its components are.
  have hv : Continuous fun q : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₂ q.proj q.snd := continuous_id
  have h₁ := (ht.comp (FiberBundle.continuous_proj F₂ E₂)).clm_bundle_apply hv
  have h₃ := (hp.comp (FiberBundle.continuous_proj F₂ E₂)).clm_bundle_apply hv
  have hc : Continuous fun q : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' (F₁ × F₃) (E := E₁ ×ᵇ E₃) q.proj (t q.proj q.snd, p q.proj q.snd) :=
    (FiberBundle.Prod.isInducing_diag F₁ E₁ F₃ E₃).continuous_iff.2 (h₁.prodMk h₃)
  -- Fibrewise, `u ↦ (t u, p u)` is the splitting isomorphism of the exact sequence.
  have hbij (x : B) : Bijective ((t x).prod (p x)) :=
    (LinearMap.exact_iff.2 (hexact x).symm).bijective_prod_of_comp_eq_id (hsurj x)
      congr(ContinuousLinearMap.toLinearMap $(hti x))
  obtain ⟨h, hh⟩ := exists_bundleHomeomorph_of_bijective (fun x ↦ (t x).prod (p x))
    (hc.congr fun q ↦ by rw [ContinuousLinearMap.prod_apply]) hbij
  exact ⟨h, fun x u ↦ by rw [hh, ContinuousLinearMap.prod_apply]⟩

/-- Every short exact sequence `0 → E₁ → E₂ → E₃ → 0` of continuous Hom-bundle sections between
finite-rank vector bundles over a normal paracompact base splits: the projection `p` has a right
inverse `s` which is a continuous Hom-bundle section, and `(v, w) ↦ i v + s w` is a homeomorphism
from the Whitney sum `E₁ ×ᵇ E₃` onto `E₂`, linear on fibres. -/
theorem exists_bundleHomeomorph_prod_of_exact [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₃]
    [NormedAlgebra ℝ 𝕜] [NormalSpace B] [ParacompactSpace B]
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
    [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
    (hi : Continuous fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (i x))
    (hp : Continuous fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
      (E := fun x ↦ E₂ x →L[𝕜] E₃ x) x (p x))
    (hinj : ∀ x, Injective (i x)) (hexact : ∀ x, (i x).range = (p x).ker)
    (hsurj : ∀ x, Surjective (p x)) :
    ∃ s : ∀ x, E₃ x →L[𝕜] E₂ x,
      Continuous (fun x ↦ TotalSpace.mk' (F₃ →L[𝕜] F₂) (E := fun x ↦ E₃ x →L[𝕜] E₂ x) x (s x)) ∧
      (∀ x, (p x).comp (s x) = ContinuousLinearMap.id 𝕜 (E₃ x)) ∧
      ∃ h : TotalSpace (F₁ × F₃) (E₁ ×ᵇ E₃) ≃ₜ TotalSpace F₂ E₂,
        ∀ (x : B) (v : E₁ x) (w : E₃ x), h ⟨x, (v, w)⟩ = ⟨x, i x v + s x w⟩ := by
  have := FiniteDimensional.completeSpace 𝕜 F₃
  obtain ⟨s, hs, hps⟩ := hp.exists_continuous_clm_bundle_rightInverse fun x ↦
    have := VectorBundle.finiteDimensional 𝕜 F₃ E₃ x
    have := FiberBundle.t2Space F₃ E₃ x
    .of_surjective_of_finiteDimensional (hsurj x)
  exact ⟨s, hs, hps, exists_bundleHomeomorph_prod_of_rightInverse hi hs hinj hexact hps⟩

end Exact

end TauCeti
