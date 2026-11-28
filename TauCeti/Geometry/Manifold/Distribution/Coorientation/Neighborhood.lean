/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Coorientation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.Topology.VectorBundle.ZeroSection

/-!
# Defining forms of a hyperplane field near a subset

Let `D` be a smooth hyperplane field on a Hausdorff second-countable manifold `M` modelled on a
finite-dimensional space. A global one-form vanishing nowhere with kernel `D` exists exactly when
the annihilator line `D⁰ ⊆ T*M` has a continuous section vanishing nowhere
(`TauCeti.IsContMDiffDistribution.exists_smoothForm_ker_eq_iff_exists_continuous`). This file
proves the relative statement: it is enough to trivialize `D⁰` along a subset to get a defining
form near it.

Let `ι : X → M` be an inducing map, for instance the inclusion of a subset or a topological
embedding of a submanifold, and let `σ q ∈ D⁰_(ι q)` be nonzero annihilating covectors depending
continuously on `q`. Then there are an open neighbourhood `W` of the image of `ι` and a smooth
one-form `α` on `W`, vanishing nowhere with kernel `D`, which at every point `ι q` is a positive
multiple of `σ q` (`TauCeti.IsContMDiffDistribution.exists_opens_smoothForm_pos_smul`). The image
of `ι` need not be closed, and `D` need not be the kernel of any one-form on all of `M`: the
annihilator line may be nontrivial away from the image.

The proof glues local defining forms. Near each point `ι q` a local defining form, multiplied by
a constant, is a positive multiple of `σ` at every point of the image close to `ι q`, since the
sign of the proportionality factor is read off continuously by pairing both with a vector field.
These neighbourhoods cover an open set `O` containing the image, and Mathlib's convex gluing
`exists_contMDiffSection_forall_mem_convex_of_local` assembles a smooth section of `T*O` which
annihilates `D` and is a positive multiple of `σ` along the image: both conditions cut out convex
subsets of each fibre. Such a section may vanish away from the image, where local forms of
opposite signs can cancel; it does not vanish on an open neighbourhood `W` of the image, and on
`W` its kernel is `D`.

## Main results

* `TauCeti.IsContMDiffDistribution.exists_opens_smoothForm_pos_smul`: a continuous nowhere-zero
  section of the annihilator line along an inducing map is, along the map, a positive multiple of
  a smooth defining form on an open neighbourhood of its image.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218, 2013,
  Chapter 13 (partitions of unity) and Chapter 19 (local defining forms).
-/

public section

noncomputable section

open Bundle Set Module Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace X] {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}

namespace IsContMDiffDistribution

/-- Near a point `ι q`, a local defining form of a smooth hyperplane field, multiplied by a
constant, annihilates the hyperplanes and is a positive multiple of a continuous nowhere-zero
annihilating covector field `σ` along `ι` at every point of `ι` close to `ι q`. -/
private theorem exists_smoothForm_pos_smul_near (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) {ι : X → M} (hι : IsInducing ι)
    {σ : Π q : X, TangentSpace I (ι q) →L[ℝ] ℝ}
    (hσ : Continuous fun q ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (ι q) (σ q))
    (hσ₀ : ∀ q, σ q ≠ 0) (hσD : ∀ q, σ q ∈ CotangentBundle.annihilatorSpace I D (ι q)) (q : X) :
    ∃ U : Set M, IsOpen U ∧ ι q ∈ U ∧ ∃ α : SmoothForm I M ℝ 1,
      (∀ y ∈ U, SmoothForm.degreeOneEquiv α y ∈ CotangentBundle.annihilatorSpace I D y) ∧
      ∀ q', ι q' ∈ U → ∃ c : ℝ, 0 < c ∧ SmoothForm.degreeOneEquiv α (ι q') = c • σ q' := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨W, hW, hqW, α₀, hα₀, hα₀W⟩ := hD.exists_isSmoothForm_ker_eq hk (ι q)
  let α : SmoothForm I M ℝ 1 := ⟨α₀, hα₀.mem_smoothBundleForms⟩
  have hαW : ∀ y ∈ W, RoughForm.ker α.val y = D y := fun y hy ↦ (hα₀W y hy).2
  -- On `W` the covector of `α` spans the annihilator line.
  have hmem : ∀ y ∈ W, ∀ τ ∈ CotangentBundle.annihilatorSpace I D y, τ ≠ 0 →
      ∃ b : ℝ, b ≠ 0 ∧ τ = b • SmoothForm.degreeOneEquiv α y := fun y hy τ hτ hτ₀ ↦ by
    rw [CotangentBundle.annihilatorSpace_eq_span_singleton
      (by rw [← hαW y hy, RoughForm.ker_eq_ker_eval, SmoothForm.eval_val]),
      Submodule.mem_span_singleton] at hτ
    obtain ⟨b, rfl⟩ := hτ
    exact ⟨b, fun hb ↦ hτ₀ (by rw [hb, zero_smul]), rfl⟩
  -- Rescale `α` by the constant making it equal to `σ q` at `ι q`.
  obtain ⟨c, -, hσc⟩ := hmem _ hqW _ (hσD q) (hσ₀ q)
  set α' := c • α with hα'
  have hα'_apply : ∀ y, SmoothForm.degreeOneEquiv α' y = c • SmoothForm.degreeOneEquiv α y :=
    fun y ↦ by rw [hα', map_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
  -- The sign of the factor between `α'` and `σ` is read off by pairing both with a vector field
  -- `Y` on which `σ q` does not vanish.
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : TangentSpace I (ι q), σ q v₀ ≠ 0 := by
    by_contra! h
    exact hσ₀ q (ContinuousLinearMap.ext h)
  obtain ⟨Y, hY, hYq⟩ := FiberBundle.exists_contMDiff_section_eq I E (∞ : ℕ∞ω) v₀
  have hYc : Continuous fun q' ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) (ι q')
      (Y (ι q')) := hY.continuous.comp hι.continuous
  -- Pairing a continuous covector field along `ι` with `Y` gives a continuous function.
  have hpair : ∀ τ : Π q' : X, TangentSpace I (ι q') →L[ℝ] ℝ, Continuous (fun q' ↦
      TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (ι q') (τ q')) →
      Continuous fun q' ↦ τ q' (Y (ι q')) := fun τ hτ ↦
    continuous_snd.comp ((Bundle.Trivial.homeomorphProd M ℝ).continuous.comp
      (Continuous.clm_bundle_apply (E₂ := Bundle.Trivial M ℝ) hτ hYc))
  have hf₂ := hpair σ hσ
  have hf₁ := hpair (fun q' ↦ SmoothForm.degreeOneEquiv α' (ι q'))
    ((SmoothForm.degreeOneEquiv α').contMDiff.continuous.comp hι.continuous)
  obtain ⟨V, hV, hVP⟩ := hι.isOpen_iff.1 (isOpen_lt continuous_const (hf₁.mul hf₂))
  have hqV : q ∈ ι ⁻¹' V := by
    rw [hVP, mem_ofPred, Pi.mul_apply, hα'_apply, ← hσc, hYq]
    exact mul_self_pos.2 hv₀
  refine ⟨W ∩ V, hW.inter hV, ⟨hqW, hqV⟩, α', fun y hy ↦ ?_, fun q' hq' ↦ ?_⟩
  · rw [hα'_apply]
    exact Submodule.smul_mem _ c (SmoothForm.degreeOneEquiv_mem_annihilatorSpace (hαW y hy.1))
  obtain ⟨b, hb, hσb⟩ := hmem _ hq'.1 _ (hσD q') (hσ₀ q')
  have heq : SmoothForm.degreeOneEquiv α' (ι q') = (c / b) • σ q' := by
    rw [hα'_apply, hσb, smul_smul, div_mul_cancel₀ c hb]
  refine ⟨c / b, ?_, heq⟩
  have hpos : 0 < SmoothForm.degreeOneEquiv α' (ι q') (Y (ι q')) * σ q' (Y (ι q')) := by
    have h : q' ∈ ι ⁻¹' V := hq'.2
    rwa [hVP, mem_ofPred, Pi.mul_apply] at h
  rw [heq, smul_apply, smul_eq_mul, mul_assoc] at hpos
  exact pos_of_mul_pos_left hpos (mul_self_nonneg _)

variable [SecondCountableTopology M]

/-- The local defining forms near the points of `ι` glue, on the open set `O` they cover, to a
smooth section of `T^* O` which annihilates `D` and is a positive multiple of `σ` along `ι`. -/
private theorem exists_opens_contMDiffSection_pos_smul (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) {ι : X → M} (hι : IsInducing ι)
    {σ : Π q : X, TangentSpace I (ι q) →L[ℝ] ℝ}
    (hσ : Continuous fun q ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (ι q) (σ q))
    (hσ₀ : ∀ q, σ q ≠ 0) (hσD : ∀ q, σ q ∈ CotangentBundle.annihilatorSpace I D (ι q)) :
    ∃ O : TopologicalSpace.Opens M, range ι ⊆ O ∧
      ∃ s : ContMDiffSection I (E →L[ℝ] ℝ) ∞ (fun y : O ↦ TangentSpace I y →L[ℝ] ℝ),
        ∀ y : O, (∀ w ∈ D y, s y w = 0) ∧ ∀ q, ι q = y → ∃ c : ℝ, 0 < c ∧ s y = c • σ q := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  choose U hU hqU α hαD hαpos using
    fun q ↦ exists_smoothForm_pos_smul_near hD hk hι hσ hσ₀ hσD q
  let O : TopologicalSpace.Opens M := ⟨⋃ q, U q, isOpen_iUnion hU⟩
  have : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  refine ⟨O, range_subset_iff.2 fun q ↦ mem_iUnion.2 ⟨q, hqU q⟩, ?_⟩
  -- Both conditions cut out convex subsets of the fibres, and near each point of `O` one of the
  -- local defining forms, restricted to `O`, satisfies them.
  refine exists_contMDiffSection_forall_mem_convex_of_local I (n := ⊤)
    (fun y : O ↦ TangentSpace I y →L[ℝ] ℝ)
    (fun y ↦ {τ | (∀ w ∈ D y, τ w = 0) ∧ ∀ q, ι q = y → ∃ c : ℝ, 0 < c ∧ τ = c • σ q})
    (fun y τ₁ h₁ τ₂ h₂ a b ha hb hab ↦ ⟨fun w hw ↦ ?_, fun q hq ↦ ?_⟩) fun y₀ ↦ ?_
  · -- The fibres `TangentSpace I y` and `TangentSpace I ↑y` are both `E`; `change` evaluates the
    -- combination of covectors without going through that identification.
    change a * τ₁ w + b * τ₂ w = 0
    rw [h₁.1 w hw, h₂.1 w hw, mul_zero, mul_zero, add_zero]
  · obtain ⟨c₁, hc₁, e₁⟩ := h₁.2 q hq
    obtain ⟨c₂, hc₂, e₂⟩ := h₂.2 q hq
    refine ⟨a * c₁ + b * c₂, ?_, ContinuousLinearMap.ext fun w ↦ ?_⟩
    · rcases ha.eq_or_lt with rfl | ha'
      · rw [zero_add] at hab
        simp [hab, hc₂]
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' hc₁) (mul_nonneg hb hc₂.le)
    · rw [e₁, e₂]
      -- As above, evaluate the combination of covectors on `w`.
      change a * (c₁ * σ q w) + b * (c₂ * σ q w) = (a * c₁ + b * c₂) * σ q w
      ring
  obtain ⟨q, hq⟩ := mem_iUnion.1 y₀.property
  refine ⟨Subtype.val ⁻¹' U q, (continuous_subtypeVal.isOpen_preimage _ (hU q)).mem_nhds hq,
    fun y ↦ SmoothForm.degreeOneEquiv
      (SmoothForm.mpullback (Subtype.val : O → M) contMDiff_subtypeVal (α q)) y,
    (SmoothForm.degreeOneEquiv _).contMDiff.contMDiffOn, ?_⟩
  rintro ⟨y, hyO⟩ hy
  have e : SmoothForm.degreeOneEquiv (SmoothForm.mpullback (Subtype.val : O → M)
      contMDiff_subtypeVal (α q)) ⟨y, hyO⟩ = SmoothForm.degreeOneEquiv (α q) y :=
    ContinuousLinearMap.ext fun v ↦ (SmoothForm.degreeOneEquiv_mpullback_apply _ _ _ v).trans
      (congrArg _ (Manifold.mfderiv_subtype_val_apply _ v))
  rw [mem_preimage] at hy
  refine ⟨fun w hw ↦ ?_, fun q' hq' ↦ ?_⟩
  · dsimp only
    rw [e]
    exact CotangentBundle.mem_annihilatorSpace_iff.1 (hαD q y hy) w hw
  dsimp only at hq' ⊢
  subst hq'
  rw [e]
  exact hαpos q q' hy

/-- **A hyperplane field with a trivial annihilator line along a subset is defined by a one-form
near it.** Let `D` be a smooth hyperplane field on a Hausdorff second-countable manifold,
`ι : X → M` an inducing map, and `σ q` a nonzero covector annihilating `D (ι q)`, depending
continuously on `q`. Then on some open neighbourhood `W` of the image of `ι` there is a smooth
one-form vanishing nowhere with kernel `D`, which at every point `ι q` is a positive multiple of
`σ q`. -/
theorem exists_opens_smoothForm_pos_smul (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) {ι : X → M} (hι : IsInducing ι)
    {σ : Π q : X, TangentSpace I (ι q) →L[ℝ] ℝ}
    (hσ : Continuous fun q ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (ι q) (σ q))
    (hσ₀ : ∀ q, σ q ≠ 0) (hσD : ∀ q, σ q ∈ CotangentBundle.annihilatorSpace I D (ι q)) :
    ∃ W : TopologicalSpace.Opens M, range ι ⊆ W ∧ ∃ α : SmoothForm I W ℝ 1,
      (∀ y : W, α.val y ≠ 0 ∧ RoughForm.ker α.val y = D y) ∧
      ∀ q (hq : ι q ∈ W), ∃ c : ℝ, 0 < c ∧ SmoothForm.degreeOneEquiv α ⟨ι q, hq⟩ = c • σ q := by
  obtain ⟨O, hιO, s, hs⟩ := exists_opens_contMDiffSection_pos_smul hD hk hι hσ hσ₀ hσD
  -- The glued section may vanish away from `ι`; restrict to the open set where it does not.
  have hsW : IsOpen {y : O | s y ≠ 0} := by
    convert s.contMDiff.continuous.isOpen_preimage _
      (isOpen_zeroSectionCompl (E →L[ℝ] ℝ) (fun y : O ↦ TangentSpace I y →L[ℝ] ℝ)) using 1
    ext y
    exact (mem_zeroSectionCompl (v := TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun y : O ↦ TangentSpace I y →L[ℝ] ℝ) y (s y))).symm
  let W : TopologicalSpace.Opens M := ⟨Subtype.val '' {y : O | s y ≠ 0},
    O.isOpen.isOpenMap_subtypeVal _ hsW⟩
  have hWO : W ≤ O := by
    rintro _ ⟨y, -, rfl⟩
    exact y.property
  let α : SmoothForm I W ℝ 1 := SmoothForm.mpullback _ (contMDiff_inclusion hWO)
    (SmoothForm.degreeOneEquiv.symm s)
  have hαs : ∀ y : W, SmoothForm.degreeOneEquiv α y =
      s (TopologicalSpace.Opens.inclusion hWO y) := fun y ↦ ContinuousLinearMap.ext fun v ↦ by
    rw [SmoothForm.degreeOneEquiv_mpullback_apply, Manifold.mfderiv_inclusion_apply,
      LinearEquiv.apply_symm_apply]
    -- Both sides are `s` at the same point applied to `v`; they differ only in whether `v` is
    -- typed in `TangentSpace I y` or in `TangentSpace I (inclusion hWO y)`, which are both `E`.
    rfl
  have hα₀ : ∀ y : W, SmoothForm.degreeOneEquiv α y ≠ 0 := by
    rintro ⟨_, y, hy, rfl⟩
    rw [hαs]
    exact hy
  refine ⟨W, ?_, α, fun y ↦ ⟨fun h ↦ hα₀ y (SmoothForm.degreeOneEquiv_apply_eq_zero_iff.2 h), ?_⟩,
    fun q hq ↦ ?_⟩
  · rintro _ ⟨q, rfl⟩
    obtain ⟨c, hc, hcs⟩ := (hs ⟨ι q, hιO ⟨q, rfl⟩⟩).2 q rfl
    refine ⟨⟨ι q, hιO ⟨q, rfl⟩⟩, fun h ↦ hσ₀ q ?_, rfl⟩
    exact (smul_eq_zero.1 (hcs.symm.trans h)).resolve_left hc.ne'
  · -- The kernel of the nonzero covector `α_y` contains the hyperplane `D y`, so equals it.
    rw [RoughForm.ker_eq_ker_eval, SmoothForm.eval_val]
    refine Module.Dual.ker_eq_of_le_of_finrank_add_one _ ?_ (fun w hw ↦ ?_)
      ((congrArg (· + 1) (hD.finrank_eq y)).trans hk)
    · rw [Ne, ← ContinuousLinearMap.toLinearMap_zero, ContinuousLinearMap.coe_inj]
      exact hα₀ y
    · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hαs]
      exact (hs _).1 w hw
  · rw [hαs]
    exact (hs _).2 q rfl

end IsContMDiffDistribution

end TauCeti
