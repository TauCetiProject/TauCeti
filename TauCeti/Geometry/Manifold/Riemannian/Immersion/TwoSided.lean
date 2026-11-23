/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.NormalBundle
public import TauCeti.Topology.VectorBundle.SphereBundle.Orientation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Topology.VectorBundle.Riemannian.Basic

/-!
# Two-sided hypersurfaces and the unit normal double cover

Let `f : M → N` be a `C^n` immersion of codimension one into a manifold with a `C^m` Riemannian
metric, `m + 1 ≤ n`. Its normal spaces `ν_f x` (`TauCeti.orthogonalNormalSpace`) are lines
(`TauCeti.finrank_orthogonalNormalSpace_eq_one`), and form the normal bundle `ν_f`, a `C^m` line
bundle over `M` (`TauCeti.orthogonalNormalFiberBundle`). The map `f` is *two-sided*
(`TauCeti.IsTwoSidedHypersurface`) when it has a `C^m` unit normal field, and *one-sided*
otherwise. No compactness, injectivity or closedness of the image is assumed.

Near every point there is a `C^m` unit normal field, the normalization of a local frame of `ν_f`
(`TauCeti.exists_contMDiffOn_unit_orthogonalNormalSpace`), and every unit normal vector is plus
or minus it. Hence a continuous unit normal field orients `ν_f`, and an orientation of `ν_f`
selects at each point the positive unit normal vector, which is locally plus or minus a `C^m` one
with a constant sign. So `f` is two-sided exactly when `ν_f` is orientable
(`TauCeti.isTwoSidedHypersurface_iff_nonempty_vectorBundleOrientation`), and exactly when it has
a continuous unit normal field (`TauCeti.isTwoSidedHypersurface_iff_exists_continuous`).

The unit vectors of `ν_f` form its unit sphere bundle `S(ν_f)`, the *unit normal double cover*:
a two-sheeted covering of `M` (`TauCeti.isCoveringMap_sphereBundleProj_orthogonalNormalSpace`),
homeomorphic over `M` to the orientation double cover of `ν_f`, with `u ↦ -u` corresponding to
the deck involution (`TauCeti.sphereBundleOrientationHomeomorph`). The map `f` is two-sided
exactly when this covering has a continuous section
(`TauCeti.isTwoSidedHypersurface_iff_exists_section_sphereBundle`), and, for connected `M`,
one-sided exactly when `S(ν_f)` is connected
(`TauCeti.not_isTwoSidedHypersurface_iff_connectedSpace_sphereBundle`). Tau Ceti's sphere
bundles have base and fibres in one universe, so these last statements take `M` and the model
`V` of `N` in one universe.

## Main definitions

* `TauCeti.IsTwoSidedHypersurface`: `f` has a `C^k` unit normal field.

## Main results

* `TauCeti.exists_contMDiffOn_unit_orthogonalNormalSpace`: local `C^m` unit normal fields.
* `TauCeti.isTwoSidedHypersurface_iff_nonempty_vectorBundleOrientation`: two-sided exactly when
  the normal bundle is orientable.
* `TauCeti.isTwoSidedHypersurface_iff_exists_continuous`: a continuous unit normal field suffices.
* `TauCeti.isCoveringMap_sphereBundleProj_orthogonalNormalSpace`: the unit normal double cover is
  a covering.
* `TauCeti.isTwoSidedHypersurface_iff_exists_section_sphereBundle`,
  `TauCeti.not_isTwoSidedHypersurface_iff_connectedSpace_sphereBundle`: two-sidedness read on the
  unit normal double cover.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 4, §4 (orientability of normal bundles of hypersurfaces).
* H. Samelson, *Orientability of hypersurfaces in ℝⁿ*, Proc. Amer. Math. Soc. 22 (1969),
  301–302.
-/

public section

noncomputable section

open Bundle Filter Manifold Module Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti

section General

variable {E V H G M N K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- The normal spaces of an immersion of codimension one are lines. -/
theorem finrank_orthogonalNormalSpace_eq_one [FiniteDimensional ℝ V] {f : M → N} {x : M}
    (hinj : Function.Injective (mfderiv I J f x)) (hr : finrank ℝ V = finrank ℝ E + 1) :
    finrank ℝ (orthogonalNormalSpace I J f x) = 1 := by
  have := finrank_orthogonalNormalSpace_add_finrank hinj
  omega

section Definition

variable [IsManifold J 1 N]

variable (I J) in
/-- A map `f : M → N` into a Riemannian manifold is *two-sided* in regularity `k` when it has a
`C^k` unit normal field: a `C^k` field `ν` along `f` of unit vectors orthogonal to the range of
the differential of `f`. For an immersed hypersurface, whose normal spaces
(`TauCeti.orthogonalNormalSpace`) are lines, these are the two-sided hypersurfaces; a one-sided
one, such as the core circle of a Möbius band, has no continuous unit normal field. -/
def IsTwoSidedHypersurface (k : ℕ∞ω) (f : M → N) : Prop :=
  ∃ ν : ∀ x, TangentSpace J (f x),
    ContMDiff I J.tangent k (fun x ↦ (⟨f x, ν x⟩ : TangentBundle J N)) ∧
      ∀ x, ‖ν x‖ = 1 ∧ ν x ∈ orthogonalNormalSpace I J f x

end Definition

variable [FiniteDimensional ℝ V] {n m : ℕ∞ω} [IsManifold I 1 M] [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J m V (fun y : N ↦ TangentSpace J y)] [IsManifold J (m + 1) N]
  [FunLike K M N] [ContinuousMapClass K M N]

/-- **Local unit normal fields.** Near every point, an immersion of codimension one has a `C^m`
field of unit normal vectors, as a section of the pulled-back tangent bundle `f *ᵖ TN`: the
normalization of a `C^m` local frame of its normal bundle. -/
theorem exists_contMDiffOn_unit_orthogonalNormalSpace {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) (hm : m + 1 ≤ n)
    (hr : finrank ℝ V = finrank ℝ E + 1) (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ τ : ∀ x, TangentSpace J (f x),
      ContMDiffOn I (I.prod 𝓘(ℝ, V)) m
        (fun x ↦ (⟨x, τ x⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) U ∧
      (∀ x, τ x ∈ orthogonalNormalSpace I J f x) ∧ ∀ x ∈ U, ‖τ x‖ = 1 := by
  obtain ⟨U, hU, hx₀, X, hX, hXs⟩ :=
    hasLocalContMDiffSubbundleFrames_iff.1
      (hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace hf hinj hm hr) x₀
  have := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  have := Pullback.contMDiffVectorBundle (F := V) (E := TangentSpace J)
    (hf.of_le (le_self_add.trans hm))
  let s : ∀ x, TangentSpace J (f x) := X 0
  have hs : ContMDiffOn I (I.prod 𝓘(ℝ, V)) m
      (fun x ↦ (⟨x, s x⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) U := hXs 0
  have hsN : ContMDiffOn I (J.prod 𝓘(ℝ, V)) m
      (fun x ↦ (⟨f x, s x⟩ : TangentBundle J N)) U :=
    (Pullback.contMDiff_lift (E := TangentSpace J) f (hf.of_le (le_self_add.trans hm))
      ).comp_contMDiffOn hs
  have hs0 {x : M} (hx : x ∈ U) : s x ≠ 0 := (hX.linearIndependent hx).ne_zero 0
  have hsmem {x : M} (hx : x ∈ U) : s x ∈ orthogonalNormalSpace I J f x := by
    have h := Submodule.subset_span (R := ℝ) (Set.mem_range_self (f := fun i ↦ X i x) 0)
    rwa [hX.span_eq hx] at h
  have hsq : ContMDiffOn I 𝓘(ℝ) m (fun x ↦ ⟪s x, s x⟫_ℝ) U :=
    ContMDiffOn.inner_bundle (IB := J) (F := V) (E := fun y : N ↦ TangentSpace J y) (b := f)
      hsN hsN
  have hnorm : ContMDiffOn I 𝓘(ℝ) m (fun x ↦ ‖s x‖⁻¹) U := fun x hx ↦ by
    have hne : ⟪s x, s x⟫_ℝ ≠ 0 := by
      rw [real_inner_self_eq_norm_sq, pow_ne_zero_iff two_ne_zero, norm_ne_zero_iff]
      exact hs0 hx
    have h : ContMDiffWithinAt I 𝓘(ℝ) m (fun y ↦ √⟪s y, s y⟫_ℝ) U x :=
      (Real.contDiffAt_sqrt hne).comp_contMDiffWithinAt (f := fun y ↦ ⟪s y, s y⟫_ℝ) (hsq x hx)
    simpa only [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)] using
      h.inv₀ (by simpa [real_inner_self_eq_norm_sq] using hs0 hx)
  classical
  refine ⟨U, hU, hx₀, fun x ↦ if x ∈ U then ‖s x‖⁻¹ • s x else 0, ?_, fun x ↦ ?_, fun x hx ↦ ?_⟩
  · refine (ContMDiffOn.smul_section hnorm hs).congr fun x hx ↦ ?_
    simp only [hx, ↓reduceIte]
    rfl
  · dsimp only
    split_ifs with hx
    · exact Submodule.smul_mem _ _ (hsmem hx)
    · exact Submodule.zero_mem _
  · simp only [hx, ↓reduceIte, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hs0 hx))

/-- A continuous unit normal field of an immersion of codimension one orients its normal bundle
`ν_f`: the orientation given at `x` by the basis `(ν x)` of the line `ν_f x`. -/
theorem nonempty_vectorBundleOrientation_of_continuous {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) (hm : m + 1 ≤ n)
    (hr : finrank ℝ V = finrank ℝ E + 1) {ν : ∀ x, TangentSpace J (f x)}
    (hν : Continuous fun x ↦ (⟨f x, ν x⟩ : TangentBundle J N)) (hν₁ : ∀ x, ‖ν x‖ = 1)
    (hνf : ∀ x, ν x ∈ orthogonalNormalSpace I J f x) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    Nonempty (VectorBundleOrientation (Fin 1 → ℝ) (fun x ↦ orthogonalNormalSpace I J f x)
      (Fin 1)) := by
  let := orthogonalNormalFiberBundle hf hinj hm hr
  let := orthogonalNormalVectorBundle hf hinj hm hr
  have hσ : Continuous fun x ↦ (⟨x, ⟨ν x, hνf x⟩⟩ :
      TotalSpace (Fin 1 → ℝ) fun x ↦ orthogonalNormalSpace I J f x) :=
    ((contMDiff_orthogonalNormalSpace_mk_iff_tangentBundle hf hinj hm hr zero_le (b := id)
      (w := ν) hνf).2 ⟨contMDiff_id, contMDiff_zero_iff.2 hν⟩).continuous
  have hne (x : M) : (⟨ν x, hνf x⟩ : orthogonalNormalSpace I J f x) ≠ 0 := fun h ↦ by
    simpa [(Submodule.mk_eq_zero _ _).1 h] using hν₁ x
  exact ⟨VectorBundleOrientation.ofContinuous _
    (VectorBundleOrientationCover.continuous_mk_basis_orientation continuous_id
      (fun x ↦ FiniteDimensional.basisSingleton (Fin 1)
        (finrank_orthogonalNormalSpace_eq_one (hinj x) hr) _ (hne x))
      fun i ↦ by simpa only [FiniteDimensional.basisSingleton_apply, id_eq] using hσ)⟩

/-- Near a point, the unit normal vectors `w x` that are positive for an orientation `o` of
`ν_f` are the values of a local unit normal field `τ`, or their opposites: the set where `τ x` is
positive for `o x`, and the set where `-τ x` is, are open. -/
private theorem eventually_eq_or_eq_neg_of_orientation {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) (hm : m + 1 ≤ n)
    (hr : finrank ℝ V = finrank ℝ E + 1) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ∀ (o : VectorBundleOrientation (Fin 1 → ℝ) (fun x ↦ orthogonalNormalSpace I J f x) (Fin 1))
      (w : ∀ x, orthogonalNormalSpace I J f x) (hw₀ : ∀ x, w x ≠ 0), (∀ x, ‖w x‖ = 1) →
      (∀ x, (FiniteDimensional.basisSingleton (Fin 1)
        (finrank_orthogonalNormalSpace_eq_one (hinj x) hr) (w x) (hw₀ x)).orientation = o x) →
      ∀ {U : Set M} {τ : ∀ x, TangentSpace J (f x)} {x₀ : M}, IsOpen U → x₀ ∈ U →
      ContMDiffOn I (I.prod 𝓘(ℝ, V)) m
        (fun x ↦ (⟨x, τ x⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) U →
      (∀ x, τ x ∈ orthogonalNormalSpace I J f x) → (∀ x ∈ U, ‖τ x‖ = 1) →
      (∀ᶠ x in 𝓝 x₀, (w x : TangentSpace J (f x)) = τ x) ∨
        ∀ᶠ x in 𝓝 x₀, (w x : TangentSpace J (f x)) = -τ x := by
  let := orthogonalNormalFiberBundle hf hinj hm hr
  let := orthogonalNormalVectorBundle hf hinj hm hr
  intro o w hw₀ hw₁ hwo U τ x₀ hU hx₀ hτ hτf hτ₁
  have hline (x : M) := finrank_orthogonalNormalSpace_eq_one (hinj x) hr
  have hτ₀ {x : M} (hx : x ∈ U) : (⟨τ x, hτf x⟩ : orthogonalNormalSpace I J f x) ≠ 0 :=
    norm_ne_zero_iff.1 ((hτ₁ x hx).trans_ne one_ne_zero)
  -- The orientations given by `τ` on `U`, as a continuous map into the orientation cover.
  let g : U → VectorBundleOrientationCover (Fin 1 → ℝ)
      (fun x ↦ orthogonalNormalSpace I J f x) (Fin 1) := fun x ↦
    ⟨x, (FiniteDimensional.basisSingleton (Fin 1) (hline x) _ (hτ₀ x.property)).orientation⟩
  have hg : Continuous g := by
    have hσ : ContinuousOn (fun x ↦ (⟨x, ⟨τ x, hτf x⟩⟩ :
        TotalSpace (Fin 1 → ℝ) fun x ↦ orthogonalNormalSpace I J f x)) U :=
      ((contMDiffOn_orthogonalNormalSpace_mk_iff hf hinj hm hr le_rfl (b := id) (w := τ)
        hτf).2 hτ).continuousOn
    exact VectorBundleOrientationCover.continuous_mk_basis_orientation continuous_subtypeVal
      _ fun i ↦ by
        simp only [FiniteDimensional.basisSingleton_apply]
        exact continuousOn_iff_continuous_domRestrict.1 hσ
  have hA := (VectorBundleOrientation.isOpen_setOf_orientation_eq o).preimage hg
  have hB := ((VectorBundleOrientation.isOpen_setOf_orientation_eq o).preimage
    VectorBundleOrientationCover.deck.continuous).preimage hg
  rcases Module.Basis.orientation_eq_or_eq_neg
    (FiniteDimensional.basisSingleton (Fin 1) (hline x₀) _ (hτ₀ hx₀)) (o x₀) with h | h
  · refine .inl ?_
    filter_upwards [(hU.isOpenMap_subtypeVal _ hA).mem_nhds ⟨⟨x₀, hx₀⟩, h.symm, rfl⟩]
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (eq_of_orientation_basisSingleton_eq (hline x)
      ((hw₁ x).trans (hτ₁ x x.property).symm) (hτ₀ x.property) (hw₀ x)
      ((hwo x).trans hx.symm))
  · refine .inr ?_
    filter_upwards [(hU.isOpenMap_subtypeVal _ hB).mem_nhds ⟨⟨x₀, hx₀⟩,
      by rw [mem_preimage, mem_preimage, VectorBundleOrientationCover.deck_apply]; exact h.symm,
      rfl⟩]
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_preimage, mem_preimage, VectorBundleOrientationCover.deck_apply] at hx
    have hx' : -(FiniteDimensional.basisSingleton (Fin 1) (hline x) _
        (hτ₀ x.property)).orientation = o x := hx
    rw [← orientation_basisSingleton_neg] at hx'
    exact congrArg Subtype.val (eq_of_orientation_basisSingleton_eq (hline x)
      ((hw₁ x).trans ((norm_neg _).trans (hτ₁ x x.property)).symm) _ (hw₀ x)
      ((hwo x).trans hx'.symm))

/-- An orientation of the normal bundle `ν_f` of an immersion of codimension one gives a `C^m`
unit normal field: at `x`, the unit vector of `ν_f x` that is positive for the orientation.
Near each point it is plus or minus a local `C^m` unit normal field
(`TauCeti.exists_contMDiffOn_unit_orthogonalNormalSpace`), with the sign fixed where the
orientation is read. -/
theorem isTwoSidedHypersurface_of_vectorBundleOrientation {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) (hm : m + 1 ≤ n)
    (hr : finrank ℝ V = finrank ℝ E + 1) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    VectorBundleOrientation (Fin 1 → ℝ) (fun x ↦ orthogonalNormalSpace I J f x) (Fin 1) →
      IsTwoSidedHypersurface I J m f := by
  let := orthogonalNormalFiberBundle hf hinj hm hr
  let := orthogonalNormalVectorBundle hf hinj hm hr
  intro o
  have hline (x : M) := finrank_orthogonalNormalSpace_eq_one (hinj x) hr
  -- The unit vector of `ν_f x` positive for `o x`.
  have hex (x : M) : ∃ (w : orthogonalNormalSpace I J f x) (hw : w ≠ 0), ‖w‖ = 1 ∧
      (FiniteDimensional.basisSingleton (Fin 1) (hline x) w hw).orientation = o x := by
    obtain ⟨U, -, hxU, τ, -, hτf, hτ₁⟩ :=
      exists_contMDiffOn_unit_orthogonalNormalSpace hf hinj hm hr x
    have hw₁ : ‖(⟨τ x, hτf x⟩ : orthogonalNormalSpace I J f x)‖ = 1 := hτ₁ x hxU
    have hw₀ : (⟨τ x, hτf x⟩ : orthogonalNormalSpace I J f x) ≠ 0 :=
      norm_ne_zero_iff.1 (hw₁.trans_ne one_ne_zero)
    rcases Module.Basis.orientation_eq_or_eq_neg
      (FiniteDimensional.basisSingleton (Fin 1) (hline x) _ hw₀) (o x) with h | h
    · exact ⟨_, hw₀, hw₁, h.symm⟩
    · exact ⟨_, neg_ne_zero.2 hw₀, (norm_neg _).trans hw₁,
        by rw [orientation_basisSingleton_neg, h]⟩
  choose w hw₀ hw₁ hwo using hex
  have hf' : ContMDiff I J m f := hf.of_le (le_self_add.trans hm)
  have := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  have := Pullback.contMDiffVectorBundle (F := V) (E := TangentSpace J) hf'
  refine ⟨fun x ↦ (w x : TangentSpace J (f x)), fun x₀ ↦ ?_, fun x ↦ ⟨hw₁ x, (w x).property⟩⟩
  obtain ⟨U, hU, hx₀, τ, hτ, hτf, hτ₁⟩ :=
    exists_contMDiffOn_unit_orthogonalNormalSpace hf hinj hm hr x₀
  have hτ₀ : ContMDiffAt I (I.prod 𝓘(ℝ, V)) m
      (fun x ↦ (⟨x, τ x⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) x₀ :=
    hτ.contMDiffAt (hU.mem_nhds hx₀)
  have hsec : ContMDiffAt I (I.prod 𝓘(ℝ, V)) m
      (fun x ↦ (⟨x, (w x : TangentSpace J (f x))⟩ :
        TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) x₀ := by
    rcases eventually_eq_or_eq_neg_of_orientation hf hinj hm hr o w hw₀ hw₁ hwo hU hx₀ hτ hτf
      hτ₁ with h | h
    · exact hτ₀.congr_of_eventuallyEq (h.mono fun x hx ↦
        congrArg (fun v ↦ (⟨x, v⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) hx)
    · exact (ContMDiffAt.neg_section hτ₀).congr_of_eventuallyEq (h.mono fun x hx ↦
        congrArg (fun v ↦ (⟨x, v⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) hx)
  exact (Pullback.contMDiffAt_lift (E := TangentSpace J) f (hf' x₀)).comp x₀ hsec

/-- **Two-sidedness is orientability of the normal bundle.** An immersion of codimension one is
two-sided, with a `C^m` unit normal field, exactly when its normal bundle `ν_f` is orientable. -/
theorem isTwoSidedHypersurface_iff_nonempty_vectorBundleOrientation {f : K}
    (hf : ContMDiff I J n f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + 1) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    IsTwoSidedHypersurface I J m f ↔
      Nonempty (VectorBundleOrientation (Fin 1 → ℝ) (fun x ↦ orthogonalNormalSpace I J f x)
        (Fin 1)) :=
  ⟨fun ⟨_, hν, hν'⟩ ↦ nonempty_vectorBundleOrientation_of_continuous hf hinj hm hr hν.continuous
    (fun x ↦ (hν' x).1) fun x ↦ (hν' x).2,
    fun ⟨o⟩ ↦ isTwoSidedHypersurface_of_vectorBundleOrientation hf hinj hm hr o⟩

/-- **A continuous unit normal field can be made smooth.** An immersion of codimension one with a
continuous unit normal field is two-sided, with a `C^m` unit normal field. -/
theorem isTwoSidedHypersurface_iff_exists_continuous {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) (hm : m + 1 ≤ n)
    (hr : finrank ℝ V = finrank ℝ E + 1) :
    IsTwoSidedHypersurface I J m f ↔ ∃ ν : ∀ x, TangentSpace J (f x),
      Continuous (fun x ↦ (⟨f x, ν x⟩ : TangentBundle J N)) ∧
        ∀ x, ‖ν x‖ = 1 ∧ ν x ∈ orthogonalNormalSpace I J f x := by
  refine ⟨fun ⟨ν, hν, hν'⟩ ↦ ⟨ν, hν.continuous, hν'⟩, fun ⟨ν, hν, hν'⟩ ↦ ?_⟩
  obtain ⟨o⟩ := nonempty_vectorBundleOrientation_of_continuous hf hinj hm hr hν
    (fun x ↦ (hν' x).1) fun x ↦ (hν' x).2
  exact isTwoSidedHypersurface_of_vectorBundleOrientation hf hinj hm hr o

/-- The fibre norm of the normal bundle `ν_f` of an immersion, the norm of the ambient metric, is
continuous on its total space. -/
theorem continuous_norm_orthogonalNormalSpace {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) (hm : m + 1 ≤ n)
    (hr : finrank ℝ V = finrank ℝ E + r) :
    Continuous fun v : TotalSpace (Fin r → ℝ) (fun x ↦ orthogonalNormalSpace I J f x) ↦
      ‖v.snd‖ := by
  let := orthogonalNormalFiberBundle hf hinj hm hr
  let := orthogonalNormalVectorBundle hf hinj hm hr
  have : IsContinuousRiemannianBundle V (fun y : N ↦ TangentSpace J y) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := J) (n := m)
  exact (continuous_norm_bundle V (fun y : N ↦ TangentSpace J y)).comp
    (contMDiff_orthogonalNormalSpace_inclusion_tangentBundle hf hinj hm hr).continuous

end General

section SphereBundle

universe u

variable {E H G N K : Type*} {V M : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [FiniteDimensional ℝ V] {n m : ℕ∞ω} [IsManifold I 1 M] [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J m V (fun y : N ↦ TangentSpace J y)] [IsManifold J (m + 1) N]
  [FunLike K M N] [ContinuousMapClass K M N]

/-- **The unit normal double cover.** The unit normal vectors of an immersion of codimension
one, the unit sphere bundle `S(ν_f)` of its normal bundle, form a two-sheeted covering of the
source. -/
theorem isCoveringMap_sphereBundleProj_orthogonalNormalSpace {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) (hm : m + 1 ≤ n)
    (hr : finrank ℝ V = finrank ℝ E + 1) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    IsCoveringMap (sphereBundleProj (Fin 1 → ℝ) fun x ↦ orthogonalNormalSpace I J f x) :=
  let := orthogonalNormalFiberBundle hf hinj hm hr
  let := orthogonalNormalVectorBundle hf hinj hm hr
  isCoveringMap_sphereBundleProj _ _ (continuous_norm_orthogonalNormalSpace hf hinj hm hr)
    (Module.finrank_fin_fun ℝ)

/-- An immersion of codimension one is two-sided exactly when its unit normal double cover
`S(ν_f) → M` has a continuous section. -/
theorem isTwoSidedHypersurface_iff_exists_section_sphereBundle {f : K}
    (hf : ContMDiff I J n f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + 1) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    IsTwoSidedHypersurface I J m f ↔
      ∃ s : M → sphereBundle (Fin 1 → ℝ) (fun x ↦ orthogonalNormalSpace I J f x),
        Continuous s ∧ ∀ x, sphereBundleProj _ _ (s x) = x := by
  let := orthogonalNormalFiberBundle hf hinj hm hr
  let := orthogonalNormalVectorBundle hf hinj hm hr
  rw [isTwoSidedHypersurface_iff_nonempty_vectorBundleOrientation hf hinj hm hr]
  exact nonempty_vectorBundleOrientation_iff_exists_section_sphereBundle
    (continuous_norm_orthogonalNormalSpace hf hinj hm hr) (Module.finrank_fin_fun ℝ)

/-- An immersion of codimension one from a connected manifold is one-sided exactly when its unit
normal double cover `S(ν_f)` is connected. -/
theorem not_isTwoSidedHypersurface_iff_connectedSpace_sphereBundle [ConnectedSpace M] {f : K}
    (hf : ContMDiff I J n f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + 1) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ¬ IsTwoSidedHypersurface I J m f ↔
      ConnectedSpace (sphereBundle (Fin 1 → ℝ) (fun x ↦ orthogonalNormalSpace I J f x)) := by
  let := orthogonalNormalFiberBundle hf hinj hm hr
  let := orthogonalNormalVectorBundle hf hinj hm hr
  rw [isTwoSidedHypersurface_iff_nonempty_vectorBundleOrientation hf hinj hm hr,
    nonempty_vectorBundleOrientation_iff_not_connectedSpace_sphereBundle
      (continuous_norm_orthogonalNormalSpace hf hinj hm hr) (Module.finrank_fin_fun ℝ),
    not_not]

end SphereBundle

end TauCeti
