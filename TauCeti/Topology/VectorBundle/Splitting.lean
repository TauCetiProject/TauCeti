/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Section

/-!
# Splitting exact sequences of vector bundles

A continuous bundle map `p : E₁ → E₂` whose fibre maps have continuous right inverses has a
continuous right inverse as a bundle map, provided the base is normal and paracompact
(`TauCeti.exists_continuous_clm_bundle_rightInverse`). Dually, a continuous bundle map with
fibrewise continuous left inverses has a continuous left inverse
(`TauCeti.exists_continuous_clm_bundle_leftInverse`). For finite-rank bundles these fibrewise
hypotheses are just surjectivity and injectivity. Consequently every short exact sequence
`0 → E₁ → E₂ → E₃ → 0` of finite-rank bundles over a normal paracompact base splits:
`E₂` is isomorphic to the Whitney sum `E₁ ×ᵇ E₃` by a homeomorphism of total spaces which is
linear on fibres (`TauCeti.exists_bundleHomeomorph_prod_of_exact`). No metric is used, and the
scalars may be `ℝ` or `ℂ`.

The argument is local-to-global. Near a point `x₀`, extend a right inverse `R` of `p x₀` to a
Hom-bundle section `r` with constant coordinates. Then `p ∘ r` is a continuous section of the
endomorphism bundle of `E₂` which is the identity at `x₀`, hence invertible near `x₀`, and
`r ∘ (p ∘ r)⁻¹` is a continuous local right inverse
(`TauCeti.exists_continuousOn_clm_bundle_rightInverse`). The right inverses of `p x` form an
affine subspace, so local right inverses glue along a partition of unity
(`TauCeti.exists_continuous_section_map_eq_of_local`). Apart from finiteness of rank in the final
splitting theorem, the model fibres may be Banach spaces, as long as the fibre maps split.

## Main results

* `TauCeti.exists_continuousOn_clm_bundle_rightInverse`,
  `TauCeti.exists_continuousOn_clm_bundle_leftInverse`: local one-sided inverses near a point
  where the fibre map splits.
* `TauCeti.exists_continuous_clm_bundle_rightInverse`,
  `TauCeti.exists_continuous_clm_bundle_leftInverse`: global one-sided inverses over a normal
  paracompact base.
* `TauCeti.exists_bundleHomeomorph_prod_of_rightInverse`: a fibrewise exact sequence with a
  continuous splitting identifies the middle bundle with the Whitney sum of the outer ones.
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

namespace TauCeti

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

omit [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] in
/-- Every continuous linear map `E₂ x₀ → E₁ x₀` is the value at `x₀` of a Hom-bundle section
continuous on a neighbourhood of `x₀`: the section with constant coordinates in the preferred
Hom-bundle trivialization at `x₀`. -/
private theorem exists_continuousOn_clm_bundle_eq (x₀ : B) (R : E₂ x₀ →L[𝕜] E₁ x₀) :
    ∃ U, IsOpen U ∧ x₀ ∈ U ∧ ∃ r : ∀ x, E₂ x →L[𝕜] E₁ x,
      ContinuousOn (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
        (E := fun x ↦ E₂ x →L[𝕜] E₁ x) x (r x)) U ∧ r x₀ = R := by
  let e := trivializationAt (F₂ →L[𝕜] F₁) (fun x ↦ E₂ x →L[𝕜] E₁ x) x₀
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x₀
  exact ⟨e.baseSet, e.open_baseSet, hx₀, fun x ↦ e.symmL 𝕜 x (e.continuousLinearMapAt 𝕜 x₀ R),
    e.continuousOn_mk_symmL _, e.symmL_continuousLinearMapAt hx₀ R⟩

/-- A bundle map `p : E₁ → E₂`, continuous on a neighbourhood `u` of `x₀`, whose fibre map at
`x₀` has a continuous right inverse, has a continuous right inverse as a bundle map on a
neighbourhood of `x₀`. The model fibre of `E₂` must be complete. -/
theorem exists_continuousOn_clm_bundle_rightInverse [CompleteSpace F₂]
    {p : ∀ x, E₁ x →L[𝕜] E₂ x} {u : Set B} {x₀ : B}
    (hp : ContinuousOn (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (p x)) u) (hu : u ∈ 𝓝 x₀)
    (h : (p x₀).HasRightInverse) :
    ∃ U ∈ 𝓝 x₀, ∃ s : ∀ x, E₂ x →L[𝕜] E₁ x,
      ContinuousOn (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
        (E := fun x ↦ E₂ x →L[𝕜] E₁ x) x (s x)) U ∧
      ∀ x ∈ U, (p x).comp (s x) = ContinuousLinearMap.id 𝕜 (E₂ x) := by
  obtain ⟨V', hV', hx₀', r, hr, hr₀⟩ := exists_continuousOn_clm_bundle_eq (F₁ := F₁) (F₂ := F₂)
    x₀ h.rightInverse
  set V := interior u ∩ V'
  have hV : IsOpen V := isOpen_interior.inter hV'
  have hx₀ : x₀ ∈ V := ⟨mem_interior_iff_mem_nhds.2 hu, hx₀'⟩
  replace hr := hr.mono (inter_subset_right (s := interior u))
  -- `p ∘ r` is a continuous endomorphism section of `E₂` near `x₀`, the identity at `x₀`.
  have hq := (hp.mono ((inter_subset_left (t := V')).trans interior_subset)).clm_bundle_comp hr
  have hq₀ : ((p x₀).comp (r x₀)).IsInvertible := by
    have : (p x₀).comp (r x₀) = ContinuousLinearMap.id 𝕜 (E₂ x₀) := by
      ext w
      simp [hr₀, h.rightInverse_rightInverse w]
    rw [this]
    exact ⟨ContinuousLinearEquiv.refl 𝕜 _, rfl⟩
  have hV₀ := hV.mem_nhds hx₀
  refine ⟨V ∩ {x | ((p x).comp (r x)).IsInvertible},
    inter_mem hV₀ ((hq.continuousAt hV₀).eventually_clm_bundle_isInvertible hq₀),
    fun x ↦ (r x).comp ((p x).comp (r x)).inverse,
    fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have hqx := hq.continuousAt (hV.mem_nhds hx.1)
    exact ((hr.continuousAt (hV.mem_nhds hx.1)).clm_bundle_comp
      (hqx.clm_bundle_inverse hx.2)).continuousWithinAt
  · rw [← ContinuousLinearMap.comp_assoc]
    exact hx.2.self_comp_inverse

/-- A bundle map `i : E₁ → E₂`, continuous on a neighbourhood `u` of `x₀`, whose fibre map at
`x₀` has a continuous left inverse, has a continuous left inverse as a bundle map on a
neighbourhood of `x₀`. The model fibre of `E₁` must be complete. This is the bundle counterpart
of `ContinuousAt.exists_continuousAt_leftInverse` for operator families. -/
theorem exists_continuousOn_clm_bundle_leftInverse [CompleteSpace F₁]
    {i : ∀ x, E₁ x →L[𝕜] E₂ x} {u : Set B} {x₀ : B}
    (hi : ContinuousOn (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (i x)) u) (hu : u ∈ 𝓝 x₀)
    (h : (i x₀).HasLeftInverse) :
    ∃ U ∈ 𝓝 x₀, ∃ t : ∀ x, E₂ x →L[𝕜] E₁ x,
      ContinuousOn (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
        (E := fun x ↦ E₂ x →L[𝕜] E₁ x) x (t x)) U ∧
      ∀ x ∈ U, (t x).comp (i x) = ContinuousLinearMap.id 𝕜 (E₁ x) := by
  obtain ⟨V', hV', hx₀', l, hl, hl₀⟩ := exists_continuousOn_clm_bundle_eq (F₁ := F₁) (F₂ := F₂)
    x₀ h.leftInverse
  set V := interior u ∩ V'
  have hV : IsOpen V := isOpen_interior.inter hV'
  have hx₀ : x₀ ∈ V := ⟨mem_interior_iff_mem_nhds.2 hu, hx₀'⟩
  replace hl := hl.mono (inter_subset_right (s := interior u))
  -- `l ∘ i` is a continuous endomorphism section of `E₁` near `x₀`, the identity at `x₀`.
  have hq := hl.clm_bundle_comp (hi.mono ((inter_subset_left (t := V')).trans interior_subset))
  have hq₀ : ((l x₀).comp (i x₀)).IsInvertible := by
    have : (l x₀).comp (i x₀) = ContinuousLinearMap.id 𝕜 (E₁ x₀) := by
      ext v
      simp [hl₀, h.leftInverse_leftInverse v]
    rw [this]
    exact ⟨ContinuousLinearEquiv.refl 𝕜 _, rfl⟩
  have hV₀ := hV.mem_nhds hx₀
  refine ⟨V ∩ {x | ((l x).comp (i x)).IsInvertible},
    inter_mem hV₀ ((hq.continuousAt hV₀).eventually_clm_bundle_isInvertible hq₀),
    fun x ↦ ((l x).comp (i x)).inverse.comp (l x),
    fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have hqx := hq.continuousAt (hV.mem_nhds hx.1)
    exact ((hqx.clm_bundle_inverse hx.2).clm_bundle_comp
      (hl.continuousAt (hV.mem_nhds hx.1))).continuousWithinAt
  · rw [ContinuousLinearMap.comp_assoc]
    exact hx.2.inverse_comp_self

variable [NormedAlgebra ℝ 𝕜] [NormalSpace B] [ParacompactSpace B]

/-- A continuous bundle map `p : E₁ → E₂` over a normal paracompact base, whose fibre maps all
have continuous right inverses, has a continuous right inverse as a bundle map. For finite-rank
bundles the hypothesis says that `p` is fibrewise surjective. -/
theorem exists_continuous_clm_bundle_rightInverse [CompleteSpace F₂]
    {p : ∀ x, E₁ x →L[𝕜] E₂ x}
    (hp : Continuous fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (p x))
    (h : ∀ x, (p x).HasRightInverse) :
    ∃ s : ∀ x, E₂ x →L[𝕜] E₁ x,
      Continuous (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun x ↦ E₂ x →L[𝕜] E₁ x) x (s x)) ∧
      ∀ x, (p x).comp (s x) = ContinuousLinearMap.id 𝕜 (E₂ x) :=
  exists_continuous_section_map_eq_of_local
    (fun x ↦ (ContinuousLinearMap.postcomp (E₂ x) (p x)).toLinearMap)
    (fun x ↦ ContinuousLinearMap.id 𝕜 (E₂ x))
    fun x₀ ↦ exists_continuousOn_clm_bundle_rightInverse hp.continuousOn univ_mem (h x₀)

/-- A continuous bundle map `i : E₁ → E₂` over a normal paracompact base, whose fibre maps all
have continuous left inverses, has a continuous left inverse as a bundle map. For finite-rank
bundles the hypothesis says that `i` is fibrewise injective. -/
theorem exists_continuous_clm_bundle_leftInverse [CompleteSpace F₁]
    {i : ∀ x, E₁ x →L[𝕜] E₂ x}
    (hi : Continuous fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (i x))
    (h : ∀ x, (i x).HasLeftInverse) :
    ∃ t : ∀ x, E₂ x →L[𝕜] E₁ x,
      Continuous (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun x ↦ E₂ x →L[𝕜] E₁ x) x (t x)) ∧
      ∀ x, (t x).comp (i x) = ContinuousLinearMap.id 𝕜 (E₁ x) :=
  exists_continuous_section_map_eq_of_local
    (fun x ↦ (ContinuousLinearMap.precomp (E₁ x) (i x)).toLinearMap)
    (fun x ↦ ContinuousLinearMap.id 𝕜 (E₁ x))
    fun x₀ ↦ exists_continuousOn_clm_bundle_leftInverse hi.continuousOn univ_mem (h x₀)

end Inverse

section Exact

variable {𝕜 B F₁ F₂ F₃ : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₁ E₂ E₃ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)] [∀ x, TopologicalSpace (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₃]
  {i : ∀ x, E₁ x →L[𝕜] E₂ x} {p : ∀ x, E₂ x →L[𝕜] E₃ x}

/-- Let `0 → E₁ → E₂ → E₃ → 0` be fibrewise exact, with `i : E₁ → E₂` and `p : E₂ → E₃`, and
let `s` be a right inverse of `p`. If `i` and `s` are continuous bundle maps and `E₁` and `E₃`
have finite rank, then `(v, w) ↦ i v + s w` is a homeomorphism from the Whitney sum `E₁ ×ᵇ E₃`
onto `E₂`, linear on fibres. -/
theorem exists_bundleHomeomorph_prod_of_rightInverse {s : ∀ x, E₃ x →L[𝕜] E₂ x}
    (hi : Continuous fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (i x))
    (hs : Continuous fun x ↦ TotalSpace.mk' (F₃ →L[𝕜] F₂)
      (E := fun x ↦ E₃ x →L[𝕜] E₂ x) x (s x))
    (hinj : ∀ x, Injective (i x)) (hexact : ∀ x, (i x).range = (p x).ker)
    (hps : ∀ x, (p x).comp (s x) = ContinuousLinearMap.id 𝕜 (E₃ x)) :
    ∃ h : TotalSpace (F₁ × F₃) (E₁ ×ᵇ E₃) ≃ₜ TotalSpace F₂ E₂,
      ∀ (x : B) (v : E₁ x) (w : E₃ x), h ⟨x, (v, w)⟩ = ⟨x, i x v + s x w⟩ := by
  have hps' (x : B) (w : E₃ x) : p x (s x w) = w := by
    simpa using congr($(hps x) w)
  -- The fibre components of a point of the Whitney sum depend continuously on it.
  have hdiag := (FiberBundle.Prod.isInducing_diag F₁ E₁ F₃ E₃).continuous
  have h₁ := (hi.comp (FiberBundle.continuous_proj (F₁ × F₃) (E₁ ×ᵇ E₃))).clm_bundle_apply
    (continuous_fst.comp hdiag)
  have h₃ := (hs.comp (FiberBundle.continuous_proj (F₁ × F₃) (E₁ ×ᵇ E₃))).clm_bundle_apply
    (continuous_snd.comp hdiag)
  have hbij (x : B) : Bijective ((i x).coprod (s x)) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun ⟨v, w⟩ hvw ↦ ?_, fun u ↦ ?_⟩
    · rw [ContinuousLinearMap.coprod_apply] at hvw
      have hpi : p x (i x v) = 0 :=
        LinearMap.mem_ker.1 (hexact x ▸ LinearMap.mem_range_self _ v)
      have hw : w = 0 := by
        simpa [hpi, hps'] using congr(p x $hvw)
      subst hw
      simpa using (map_eq_zero_iff _ (hinj x)).1 (by simpa using hvw)
    · -- `u - s (p u)` lies in the kernel of `p`, which is the range of `i`.
      obtain ⟨v, hv⟩ : u - s x (p x u) ∈ (i x).range := by
        simp [hexact x, hps']
      exact ⟨(v, p x u), by
        rw [ContinuousLinearMap.coprod_apply, ← ContinuousLinearMap.coe_coe, hv, sub_add_cancel]⟩
  obtain ⟨h, hh⟩ := exists_bundleHomeomorph_of_bijective (fun x ↦ (i x).coprod (s x))
    (h₁.add_totalSpace 𝕜 h₃) hbij
  exact ⟨h, fun x v w ↦ hh x (v, w)⟩

/-- Every short exact sequence `0 → E₁ → E₂ → E₃ → 0` of continuous bundle maps between
finite-rank vector bundles over a normal paracompact base splits: the projection `p` has a
continuous right inverse `s`, and `(v, w) ↦ i v + s w` is a homeomorphism from the Whitney sum
`E₁ ×ᵇ E₃` onto `E₂`, linear on fibres. -/
theorem exists_bundleHomeomorph_prod_of_exact [NormedAlgebra ℝ 𝕜] [NormalSpace B]
    [ParacompactSpace B] [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
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
  obtain ⟨s, hs, hps⟩ := exists_continuous_clm_bundle_rightInverse hp fun x ↦
    have := VectorBundle.finiteDimensional 𝕜 F₃ E₃ x
    have := FiberBundle.t2Space F₃ E₃ x
    .of_surjective_of_finiteDimensional (hsurj x)
  exact ⟨s, hs, hps, exists_bundleHomeomorph_prod_of_rightInverse hi hs hinj hexact hps⟩

end Exact

end TauCeti
