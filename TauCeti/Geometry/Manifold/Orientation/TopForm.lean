/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Orientations from nowhere-vanishing top forms

A nonzero top form on a tangent space selects the orientation on which it is positive
(`TauCeti.topFormOrientationAt`). For a continuous top form that vanishes nowhere, these tangent
orientations are locally constant: read in a tangent-bundle trivialization, the form evaluated on
the trivialization's frame is a continuous nowhere-vanishing function, so its sign is locally
constant. They therefore form an orientation of the manifold on which the form is positive,
`TauCeti.Manifold.Orientation.ofTopForm`. This is the first direction of the correspondence
between nowhere-vanishing top forms and orientations; it holds at boundary and corner points too.

## Main declarations

* `TauCeti.topFormOrientationAt`: the orientation of a tangent space on which a top form is
  positive, characterized by `TauCeti.topFormOrientationAt_spec`.
* `TauCeti.Manifold.Orientation.ofTopForm`: the orientation of a nowhere-vanishing continuous top
  form.
* `TauCeti.Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff`: a tangent basis is
  positive for it exactly when the form is positive on the basis.
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul`,
  `TauCeti.Manifold.Orientation.isOrientationReversingAt_ofTopForm_of_mpullback_eq_smul`: a map
  pulling one such top form back at `x` to a positive (negative) multiple of the other preserves
  (reverses) their orientations at `x`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Proposition 15.5.
-/

public section

noncomputable section

open Bundle Filter
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

private def topFormBasis [IsManifold I 1 M] (hk : Module.finrank ℝ E = k) (x : M) :
    Module.Basis (Fin k) ℝ (TangentSpace I x) :=
  (trivializationAt E (TangentSpace I) x).basisAt (Module.finBasisOfFinrankEq ℝ E hk)
    (FiberBundle.mem_baseSet_trivializationAt' x)

/-- The fibre orientation selected by a nonzero top-degree form using the chart-local basis. -/
def topFormOrientationAt [IsManifold I 1 M] (hk : Module.finrank ℝ E = k)
    (φ : RoughForm I M ℝ k) (x : M) :
    _root_.Orientation ℝ (TangentSpace I x) (Fin k) :=
  if 0 < φ x (topFormBasis (I := I) hk x) then
    (topFormBasis (I := I) hk x).orientation
  else
    -(topFormBasis (I := I) hk x).orientation

/-- A basis is positive for `topFormOrientationAt` exactly when the form evaluates positively. -/
theorem topFormOrientationAt_spec [IsManifold I 1 M] (hk : Module.finrank ℝ E = k)
    {φ : RoughForm I M ℝ k} (x : M) (h0 : φ x ≠ 0)
    (b : Module.Basis (Fin k) ℝ (TangentSpace I x)) :
    b.orientation = topFormOrientationAt (I := I) hk φ x ↔ 0 < φ x b := by
  let b₀ := topFormBasis (I := I) hk x
  have hbase : φ x b₀ ≠ 0 := ((φ x).map_basis_ne_zero_iff b₀).mpr h0
  have hformula : φ x b = b₀.det b * φ x b₀ := by
    exact ContinuousAlternatingMap.apply_eq_det_mul (φ x) b₀ b
  have hformula' : φ x b₀ = b.det b₀ * φ x b := by
    exact ContinuousAlternatingMap.apply_eq_det_mul (φ x) b b₀
  by_cases hp : 0 < φ x b₀
  -- `topFormOrientationAt` is defined with the chart basis; expose that branch before
  -- applying the basis-orientation characterization.
  · change b.orientation = (if 0 < φ x b₀ then b₀.orientation else -b₀.orientation) ↔ _
    rw [ite_eq_left hp]
    have hor : b.orientation = b₀.orientation ↔ 0 < b₀.det b := by
      simpa only [eq_comm] using (b₀.orientation_eq_iff_det_pos b)
    rw [hor]
    constructor
    · intro hd
      rw [hformula]
      exact mul_pos hd hp
    · intro hb
      rw [hformula] at hb
      rcases (mul_pos_iff.mp hb) with ⟨hd, _⟩ | ⟨_, hneg⟩
      · exact hd
      · exact False.elim ((not_lt_of_ge (le_of_lt hp)) hneg)
  · have hn : φ x b₀ < 0 := lt_of_le_of_ne (le_of_not_gt hp) hbase
    change b.orientation = (if 0 < φ x b₀ then b₀.orientation else -b₀.orientation) ↔ _
    rw [ite_eq_right hp]
    rw [Module.Basis.orientation_eq_neg_iff_det_neg]
    constructor
    · intro hd
      have hprod : b.det b₀ * φ x b < 0 := by rw [← hformula']; exact hn
      rcases (mul_neg_iff.mp hprod) with ⟨hdetpos, hφneg⟩ | ⟨hdet, hφ⟩
      · exact False.elim ((not_lt_of_ge (le_of_lt hdetpos)) hd)
      · exact hφ
    · intro hφ
      have hprod : b.det b₀ * φ x b < 0 := by rw [← hformula']; exact hn
      rcases (mul_neg_iff.mp hprod) with ⟨hdetpos, hφneg⟩ | ⟨hdet, _⟩
      · exact False.elim ((not_lt_of_ge (le_of_lt hφ)) hφneg)
      · exact hdet

/-- Read in a trivialization of the tangent bundle, the orientation selected by a top form is the
orientation of a model basis exactly when the form is positive on the corresponding frame. -/
private theorem mapOrientation_topFormOrientationAt [IsManifold I 1 M]
    (hk : Module.finrank ℝ E = k) {φ : RoughForm I M ℝ k} {x : M} (h0 : φ x ≠ 0)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (hx : x ∈ e.baseSet) (B : Module.Basis (Fin k) ℝ E) :
    e.mapOrientation (Fin k) hx (topFormOrientationAt (I := I) hk φ x) =
      if 0 < φ x (e.basisAt B hx) then B.orientation else -B.orientation := by
  have hmap : e.mapOrientation (Fin k) hx (e.basisAt B hx).orientation = B.orientation := by
    rw [Trivialization.mapOrientation_apply, ← Module.Basis.orientation_map]
    congr 1
    ext i
    simp [Trivialization.basisAt, e.apply_mk_symm hx]
  split_ifs with hpos
  · rw [← (topFormOrientationAt_spec hk x h0 _).mpr hpos, hmap]
  · have hne : (e.basisAt B hx).orientation ≠ topFormOrientationAt (I := I) hk φ x :=
      fun h ↦ hpos ((topFormOrientationAt_spec hk x h0 _).mp h)
    rcases Orientation.eq_or_eq_neg (topFormOrientationAt (I := I) hk φ x)
        (e.basisAt B hx).orientation ((Fintype.card_fin k).trans hk.symm) with h | h
    · exact absurd h.symm hne
    · rw [h, Trivialization.mapOrientation_neg, hmap]

/-- The tangent orientations selected by a nowhere-vanishing continuous top form are locally
constant in the preferred trivializations of the tangent bundle. -/
private theorem eventually_mapOrientation_topFormOrientationAt_eq [IsManifold I 1 M]
    (hk : Module.finrank ℝ E = k) {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ)
    (h0 : ∀ x, φ x ≠ 0) (b : M) :
    ∀ᶠ x in 𝓝 b, ∀ hx : x ∈ (trivializationAt E (TangentSpace I) b).baseSet,
      (trivializationAt E (TangentSpace I) b).mapOrientation (Fin k) hx
          (topFormOrientationAt (I := I) hk φ x) =
        (trivializationAt E (TangentSpace I) b).mapOrientation (Fin k)
          (FiberBundle.mem_baseSet_trivializationAt' b) (topFormOrientationAt (I := I) hk φ b) := by
  let e := trivializationAt E (TangentSpace I) b
  let B := Module.finBasisOfFinrankEq ℝ E hk
  -- On the chart source, the form evaluated on the trivialization frame is the coordinate
  -- expression of the form evaluated on the model basis, which is continuous.
  let g : M → ℝ := fun x ↦ φ.inChartAt b (extChartAt I b x) B
  have hg (x : M) (hx : x ∈ e.baseSet) : φ x (e.basisAt B hx) = g x := by
    have hx' : x ∈ (chartAt H b).source := by
      simpa only [e, TangentBundle.trivializationAt_baseSet] using hx
    dsimp only [g]
    rw [RoughForm.inChartAt_apply, ← TangentBundle.symmL_trivializationAt hx',
      (extChartAt I b).left_inv (by simpa only [extChartAt_source] using hx')]
    congr 1
    ext i
    rw [Trivialization.basisAt, Module.Basis.map_apply, Trivialization.linearEquivAt_symm_apply]
    exact (e.symmL_apply hx _).symm
  have hgc : ContinuousAt g b := by
    have hc := (hφ.continuousOn_inChartAt b).comp (continuousOn_extChartAt b)
      (extChartAt I b).mapsTo
    exact (continuous_eval_const _).continuousAt.comp
      (hc.continuousAt (extChartAt_source_mem_nhds b))
  have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  have hgb : g b ≠ 0 := hg b hb ▸ ((φ b).map_basis_ne_zero_iff _).mpr (h0 b)
  have hsign : ∀ᶠ x in 𝓝 b, (0 < g x ↔ 0 < g b) := by
    rcases hgb.lt_or_gt with hneg | hpos
    · filter_upwards [hgc.eventually (gt_mem_nhds hneg)] with x hx
      exact iff_of_false hx.not_gt hneg.not_gt
    · filter_upwards [hgc.eventually (lt_mem_nhds hpos)] with x hx
      exact iff_of_true hx hpos
  filter_upwards [hsign] with x hx hxe
  rw [mapOrientation_topFormOrientationAt hk (h0 x) e hxe B,
    mapOrientation_topFormOrientationAt hk (h0 b) e hb B, hg x hxe, hg b hb]
  simp only [hx]

namespace Manifold.Orientation

/-- The orientation of a manifold on which a nowhere-vanishing continuous top form is positive. -/
def ofTopForm [IsManifold I 1 M] (hk : Module.finrank ℝ E = k) (φ : RoughForm I M ℝ k)
    (hφ : IsSmoothForm I 0 φ) (h0 : ∀ x, φ x ≠ 0) : Orientation I M (Fin k) :=
  ofVectorBundleOrientation (Module.finBasisOfFinrankEq ℝ E hk).orientation
    ((Fintype.card_fin k).trans hk.symm)
    ⟨topFormOrientationAt (I := I) hk φ,
      eventually_mapOrientation_topFormOrientationAt_eq hk hφ h0⟩

/-- The tangent orientations of `ofTopForm` are those selected by the top form. -/
@[simp]
theorem orientationAt_ofTopForm [IsManifold I 1 M] (hk : Module.finrank ℝ E = k)
    (φ : RoughForm I M ℝ k) (hφ : IsSmoothForm I 0 φ) (h0 : ∀ x, φ x ≠ 0) (x : M) :
    orientationAt (ofTopForm hk φ hφ h0) x = topFormOrientationAt (I := I) hk φ x := by
  rw [ofTopForm, orientationAt_ofVectorBundleOrientation, VectorBundleOrientation.coe_mk]

/-- A tangent basis is positive for the orientation of a nowhere-vanishing continuous top form
exactly when the form is positive on it. -/
theorem orientation_eq_orientationAt_ofTopForm_iff [IsManifold I 1 M]
    (hk : Module.finrank ℝ E = k) {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ)
    (h0 : ∀ x, φ x ≠ 0) {x : M} (b : Module.Basis (Fin k) ℝ (TangentSpace I x)) :
    b.orientation = orientationAt (ofTopForm hk φ hφ h0) x ↔ 0 < φ x b := by
  rw [orientationAt_ofTopForm]
  exact topFormOrientationAt_spec hk x (h0 x) b

/-- A tangent basis is positive or negative for the orientation of a nowhere-vanishing continuous
top form according to the sign of the form on it. -/
theorem orientation_eq_ite_orientationAt_ofTopForm [IsManifold I 1 M]
    (hk : Module.finrank ℝ E = k) {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ)
    (h0 : ∀ x, φ x ≠ 0) {x : M} (b : Module.Basis (Fin k) ℝ (TangentSpace I x)) :
    b.orientation = if 0 < φ x b then orientationAt (ofTopForm hk φ hφ h0) x
      else -orientationAt (ofTopForm hk φ hφ h0) x := by
  split_ifs with h
  · exact (orientation_eq_orientationAt_ofTopForm_iff hk hφ h0 b).mpr h
  · refine ((b.orientation).eq_or_eq_neg _ ((Fintype.card_fin k).trans hk.symm)).resolve_left ?_
    exact fun h' ↦ h ((orientation_eq_orientationAt_ofTopForm_iff hk hφ h0 b).mp h')

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']

/-- If a map pulls a nonzero top form `φ'` back at `x` to a nonzero multiple of a nonzero top form
`φ`, its derivative at `x` is invertible, and the image of a basis `b` is a basis on which `φ'` is
`c` times the value of `φ` on `b`. -/
private theorem exists_equiv_of_mpullback_eq_smul (hk : Module.finrank ℝ E = k)
    (hk' : Module.finrank ℝ E' = k) {φ : RoughForm I M ℝ k} {φ' : RoughForm I' M' ℝ k}
    {f : M → M'} {x : M} (h0 : φ x ≠ 0) {c : ℝ} (hc : c ≠ 0)
    (hf : mpullback I I' f φ' x = c • φ x) :
    ∃ e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x),
      (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x ∧
        ∀ b : Module.Basis (Fin k) ℝ (TangentSpace I x),
          φ' (f x) (b.map e.toLinearEquiv) = c * φ x b := by
  have hval (v : Fin k → TangentSpace I x) :
      φ' (f x) (fun i ↦ mfderiv I I' f x (v i)) = c * φ x v := by
    simpa only [mpullback_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] using
      DFunLike.congr_fun hf v
  let b := Module.finBasisOfFinrankEq ℝ (TangentSpace I x) hk
  -- The derivative carries `b` to a family on which `φ'` does not vanish, hence to a basis.
  have hli : LinearIndependent ℝ fun i ↦ mfderiv I I' f x (b i) := by
    by_contra h
    have hz := (φ' (f x)).toAlternatingMap.map_linearDependent _ h
    rw [ContinuousAlternatingMap.coe_toAlternatingMap, hval] at hz
    exact mul_ne_zero hc (((φ x).map_basis_ne_zero_iff b).mpr h0) hz
  let b' := basisOfLinearIndependentOfCardEqFinrank' _ hli ((Fintype.card_fin k).trans hk'.symm)
  let e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x) :=
    (b.equiv b' (Equiv.refl _)).toContinuousLinearEquiv
  have he : (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x :=
    ContinuousLinearMap.coe_injective <| b.ext fun i ↦ by
      simp [e, b', Module.Basis.equiv_apply]
  refine ⟨e, he, fun b₀ ↦ ?_⟩
  rw [← hval]
  congr 1
  ext i
  rw [Module.Basis.map_apply, ← he, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv]

/-- If a map `f` pulls the top form `φ'` back at `x` to a nonzero multiple `c • φ` of the top
form `φ`, its derivative at `x` is invertible, and it carries the orientation of `φ` at `x` to the
orientation of `φ'` at `f x` when `0 < c`, and to its negation when `c < 0`. -/
private theorem exists_map_orientationAt_ofTopForm_of_mpullback_eq_smul [IsManifold I 1 M]
    [IsManifold I' 1 M'] (hk : Module.finrank ℝ E = k) (hk' : Module.finrank ℝ E' = k)
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ) (h0 : ∀ x, φ x ≠ 0)
    {φ' : RoughForm I' M' ℝ k} (hφ' : IsSmoothForm I' 0 φ') (h0' : ∀ x, φ' x ≠ 0)
    {f : M → M'} {x : M} {c : ℝ} (hc : c ≠ 0) (hf : mpullback I I' f φ' x = c • φ x) :
    ∃ e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x),
      (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x ∧
        _root_.Orientation.map (Fin k) e.toLinearEquiv (orientationAt (ofTopForm hk φ hφ h0) x) =
          if 0 < c then orientationAt (ofTopForm hk' φ' hφ' h0') (f x)
            else -orientationAt (ofTopForm hk' φ' hφ' h0') (f x) := by
  obtain ⟨e, he, hb⟩ := exists_equiv_of_mpullback_eq_smul hk hk' (h0 x) hc hf
  refine ⟨e, he, ?_⟩
  let b := Module.finBasisOfFinrankEq ℝ (TangentSpace I x) hk
  have h₁ := orientation_eq_ite_orientationAt_ofTopForm hk hφ h0 b
  have h₂ := orientation_eq_ite_orientationAt_ofTopForm hk' hφ' h0' (b.map e.toLinearEquiv)
  rw [Module.Basis.orientation_map, hb] at h₂
  -- Both orientations are read off the signs of the forms on `b` and on its image.
  have h₁' : orientationAt (ofTopForm hk φ hφ h0) x =
      if 0 < φ x b then b.orientation else -b.orientation := by
    split_ifs at h₁ ⊢
    · exact h₁.symm
    · rw [h₁]
      exact (neg_neg (G := _root_.Orientation ℝ (TangentSpace I x) (Fin k)) _).symm
  rw [h₁', apply_ite (_root_.Orientation.map (Fin k) e.toLinearEquiv), Orientation.map_neg, h₂]
  rcases lt_or_gt_of_ne hc with hc | hc <;>
    rcases lt_or_gt_of_ne (((φ x).map_basis_ne_zero_iff b).mpr (h0 x)) with hb | hb <;>
    simp [mul_pos_iff, hc, hb, hc.not_gt, hb.not_gt,
      neg_neg (G := _root_.Orientation ℝ (TangentSpace I' (f x)) (Fin k))]

/-- **Orientation of a pullback of top forms.** If a map `f` pulls the top form `φ'` back at `x`
to a positive multiple of the top form `φ`, it preserves the orientations of `φ` and `φ'` at
`x`. -/
theorem isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul [IsManifold I 1 M]
    [IsManifold I' 1 M'] (hk : Module.finrank ℝ E = k) (hk' : Module.finrank ℝ E' = k)
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ) (h0 : ∀ x, φ x ≠ 0)
    {φ' : RoughForm I' M' ℝ k} (hφ' : IsSmoothForm I' 0 φ') (h0' : ∀ x, φ' x ≠ 0)
    {f : M → M'} {x : M} {c : ℝ} (hc : 0 < c) (hf : mpullback I I' f φ' x = c • φ x) :
    IsOrientationPreservingAt (ofTopForm hk φ hφ h0) (ofTopForm hk' φ' hφ' h0') f x := by
  obtain ⟨e, he, h⟩ :=
    exists_map_orientationAt_ofTopForm_of_mpullback_eq_smul hk hk' hφ h0 hφ' h0' hc.ne' hf
  exact (isOrientationPreservingAt_iff_of_coe_eq _ _ f x e he).mpr (h.trans (ite_eq_left hc))

/-- **Orientation of a pullback of top forms.** If a map `f` pulls the top form `φ'` back at `x`
to a negative multiple of the top form `φ`, it reverses the orientations of `φ` and `φ'` at
`x`. -/
theorem isOrientationReversingAt_ofTopForm_of_mpullback_eq_smul [IsManifold I 1 M]
    [IsManifold I' 1 M'] (hk : Module.finrank ℝ E = k) (hk' : Module.finrank ℝ E' = k)
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ) (h0 : ∀ x, φ x ≠ 0)
    {φ' : RoughForm I' M' ℝ k} (hφ' : IsSmoothForm I' 0 φ') (h0' : ∀ x, φ' x ≠ 0)
    {f : M → M'} {x : M} {c : ℝ} (hc : c < 0) (hf : mpullback I I' f φ' x = c • φ x) :
    IsOrientationReversingAt (ofTopForm hk φ hφ h0) (ofTopForm hk' φ' hφ' h0') f x := by
  obtain ⟨e, he, h⟩ :=
    exists_map_orientationAt_ofTopForm_of_mpullback_eq_smul hk hk' hφ h0 hφ' h0' hc.ne hf
  exact (isOrientationReversingAt_iff_of_coe_eq _ _ f x e he).mpr (h.trans (ite_eq_right hc.not_gt))

end Manifold.Orientation

end TauCeti
