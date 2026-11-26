/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Extension
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Pushing almost complex structures forward along partial diffeomorphisms

A partial diffeomorphism `φ : M' → M` carries a smooth almost complex structure `J'` on `M'` to
the endomorphism field

`(φ_* J')_y = dφ_(φ⁻¹ y) ∘ J'_(φ⁻¹ y) ∘ d(φ⁻¹)_y`

on `M` (`PartialDiffeomorph.pushforwardEndomorphism`). The formula is total, but only its values
on the target of `φ` are meaningful: there it is a smooth section of the tangent endomorphism
bundle (`PartialDiffeomorph.contMDiffOn_pushforwardEndomorphism`) squaring to `-1`
(`PartialDiffeomorph.pushforwardEndomorphism_apply_pushforwardEndomorphism`), and it is the unique
field on the target making every differential of `φ` complex linear
(`PartialDiffeomorph.pushforwardEndomorphism_mfderiv_apply` and
`PartialDiffeomorph.eq_pushforwardEndomorphism_of_mfderiv_apply`). Where `φ` pulls a
nondegenerate two-form `σ` on `M` back to forms compatible with `J'`, the pushed-forward field is
compatible with `σ` (`PartialDiffeomorph.compatible_pushforwardAt`).

Combined with the relative extension of compatible structures
(`TauCeti.SmoothTwoForm.Compatible.exists_compatible_eqOn`), this gives a global smooth
`σ`-compatible structure on `M` for which `φ` is pseudoholomorphic on any prescribed compact set
where `φ` is symplectic (`PartialDiffeomorph.exists_compatible_mfderiv_apply_eq`). This is the
relative extension of the pushed-forward standard structure from an embedded ball used in
Gromov's proof of the nonsqueezing theorem.

## Main results

* `PartialDiffeomorph.pushforwardEndomorphism`: the field `dφ ∘ J' ∘ dφ⁻¹`.
* `PartialDiffeomorph.pushforwardEndomorphism_mfderiv_apply`: `(φ_* J') ∘ dφ = dφ ∘ J'`.
* `PartialDiffeomorph.eq_pushforwardEndomorphism_of_mfderiv_apply`: the intertwining identity
  characterizes it on the target.
* `PartialDiffeomorph.contMDiffOn_pushforwardEndomorphism`: it is smooth on the target.
* `PartialDiffeomorph.exists_compatible_mfderiv_apply_eq`: the relative extension of the
  pushed-forward structure from a compact set to a global compatible structure.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 9.3 (the structure extending the pushed-forward standard structure on an embedded ball).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Section 4.1
  (relative existence of compatible almost complex structures).
-/

public noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace PartialDiffeomorph

open TauCeti

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  (φ : PartialDiffeomorph I' I M' M ∞) (J' : SmoothAlmostComplexStructure I' M')

/-- The endomorphism field `dφ_(φ⁻¹ y) ∘ J'_(φ⁻¹ y) ∘ d(φ⁻¹)_y` obtained by pushing an almost
complex structure `J'` forward along a partial diffeomorphism `φ`. It is meaningful on the target
of `φ`, where it is a smooth almost complex structure. -/
def pushforwardEndomorphism (y : M) : TangentSpace I y →L[ℝ] TangentSpace I y :=
  mfderiv I' I φ (φ.symm y) ∘L J'.toEndomorphism (φ.symm y) ∘L mfderiv I I' φ.symm y

/-- Evaluate the pushed-forward field. -/
theorem pushforwardEndomorphism_apply (y : M) (v : TangentSpace I y) :
    φ.pushforwardEndomorphism J' y v =
      mfderiv I' I φ (φ.symm y) (J' (φ.symm y) (mfderiv I I' φ.symm y v)) :=
  (rfl)

/-- **The pushed-forward field makes `φ` complex linear**: on the source of `φ`,
`(φ_* J')_(φ x) ∘ dφ_x = dφ_x ∘ J'_x`. -/
@[simp]
theorem pushforwardEndomorphism_mfderiv_apply {x : M'} (hx : x ∈ φ.source)
    (v : TangentSpace I' x) :
    φ.pushforwardEndomorphism J' (φ x) (mfderiv I' I φ x v) = mfderiv I' I φ x (J' x v) := by
  rw [pushforwardEndomorphism_apply, φ.mfderiv_symm_apply_mfderiv_apply (by simp) hx]
  -- The base point `φ⁻¹ (φ x)` is `x`; every tangent space is the model space `E'`.
  have key : ∀ x' : M', x' = x → ∀ w : E',
      mfderiv I' I φ x' (J' x' w) = mfderiv I' I φ x (J' x w) := by
    rintro x' rfl w
    rfl
  exact key _ (φ.left_inv hx) v

/-- On the target of `φ`, the pushed-forward field squares to `-1`. -/
theorem pushforwardEndomorphism_apply_pushforwardEndomorphism {y : M} (hy : y ∈ φ.target)
    (v : TangentSpace I y) :
    φ.pushforwardEndomorphism J' y (φ.pushforwardEndomorphism J' y v) = -v := by
  obtain ⟨x, hx, rfl⟩ : ∃ x ∈ φ.source, φ x = y := ⟨φ.symm y, φ.map_target hy, φ.right_inv hy⟩
  obtain ⟨w, rfl⟩ := (φ.isInvertible_mfderiv (by simp) hx).surjective v
  simp [hx]

/-- **Uniqueness of the pushed-forward field**: at a point `φ x` of the target, an endomorphism
`A` with `A ∘ dφ_x = dφ_x ∘ J'_x` is `(φ_* J')_(φ x)`. -/
theorem eq_pushforwardEndomorphism_of_mfderiv_apply {x : M'} (hx : x ∈ φ.source)
    {A : TangentSpace I (φ x) →L[ℝ] TangentSpace I (φ x)}
    (hA : ∀ v : TangentSpace I' x, A (mfderiv I' I φ x v) = mfderiv I' I φ x (J' x v)) :
    A = φ.pushforwardEndomorphism J' (φ x) := by
  ext v
  obtain ⟨w, rfl⟩ := (φ.isInvertible_mfderiv (by simp) hx).surjective v
  rw [hA, pushforwardEndomorphism_mfderiv_apply φ J' hx]

/-- The pushed-forward structure at a point of the target of `φ`, as an almost complex structure
on the tangent space. -/
def pushforwardAt {y : M} (hy : y ∈ φ.target) : AlmostComplexStructure (TangentSpace I y) where
  toLinearMap := (φ.pushforwardEndomorphism J' y).toLinearMap
  square_neg := by
    ext v
    exact φ.pushforwardEndomorphism_apply_pushforwardEndomorphism J' hy v

/-- The pushed-forward structure at `y` is the pushed-forward field at `y`. -/
theorem pushforwardAt_toLinearMap {y : M} (hy : y ∈ φ.target) :
    (φ.pushforwardAt J' hy).toLinearMap = (φ.pushforwardEndomorphism J' y).toLinearMap :=
  (rfl)

/-- Evaluate the pushed-forward structure at a point of the target. -/
@[simp]
theorem pushforwardAt_apply {y : M} (hy : y ∈ φ.target) (v : TangentSpace I y) :
    φ.pushforwardAt J' hy v = φ.pushforwardEndomorphism J' y v :=
  (rfl)

/-- **Compatibility of the pushed-forward structure.** If the differential of `φ` at `x` pulls
the two-form `σ` back to a form `τ` compatible with `J'_x`, then `σ` is compatible with the
pushed-forward structure at `φ x`. -/
theorem compatible_pushforwardAt [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
    (hσ : σ.IsNondegenerate) {x : M'} (hx : x ∈ φ.source)
    {τ : SymplecticForm (TangentSpace I' x)} (hτ : τ.Compatible (J'.almostComplexStructureAt x))
    (hφ : ∀ v w, σ.eval₂ (φ x) (mfderiv I' I φ x v) (mfderiv I' I φ x w) = τ v w) :
    (hσ.symplecticFormAt (φ x)).Compatible (φ.pushforwardAt J' (φ.map_source hx)) := by
  have hsurj := (φ.isInvertible_mfderiv (by simp) hx).surjective
  refine SymplecticForm.Compatible.of_tames ?_ fun a ha ↦ ?_
  · rw [SymplecticForm.invariant_iff]
    intro a b
    obtain ⟨a, rfl⟩ := hsurj a
    obtain ⟨b, rfl⟩ := hsurj b
    simp only [pushforwardAt_apply, pushforwardEndomorphism_mfderiv_apply φ J' hx,
      SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply, hφ]
    simpa only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using
      (SymplecticForm.invariant_iff τ _).1 hτ.invariant a b
  · obtain ⟨a, rfl⟩ := hsurj a
    have ha' : a ≠ 0 := by
      rintro rfl
      exact ha (map_zero _)
    simp only [pushforwardAt_apply, pushforwardEndomorphism_mfderiv_apply φ J' hx,
      SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply, hφ]
    simpa only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using hτ.tames a ha'

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M]

/-- **The pushed-forward field is smooth on the target of `φ`**, as a section of the tangent
endomorphism bundle. On total spaces it is the composite `Tφ ∘ J' ∘ T(φ⁻¹)` of tangent maps. -/
theorem contMDiffOn_pushforwardEndomorphism :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) y
        (φ.pushforwardEndomorphism J' y)) φ.target := by
  intro y hy
  refine ContMDiffAt.contMDiffWithinAt ?_
  rw [TauCeti.contMDiffAt_hom_bundle_iff]
  intro v
  -- The structure `J'` on total spaces.
  have hJ := (TauCeti.contMDiff_hom_bundle_iff _).1 J'.toEndomorphism.contMDiff
  have hsymm : ContMDiffAt (I.prod 𝓘(ℝ, E)) (I'.prod 𝓘(ℝ, E')) ∞
      (tangentMap I I' φ.symm) (⟨y, v⟩ : TangentBundle I M) :=
    (φ.symm.contMDiffOn.contMDiffAt (φ.symm.open_source.mem_nhds hy)).contMDiffAt_tangentMap
      (by simp)
  have hφ : ContMDiffAt (I'.prod 𝓘(ℝ, E')) (I.prod 𝓘(ℝ, E)) ∞ (tangentMap I' I φ)
      (TotalSpace.mk' E' (φ.symm y) (J' (φ.symm y) (mfderiv I I' φ.symm y v))) :=
    (φ.contMDiffOn.contMDiffAt (φ.open_source.mem_nhds (φ.map_target hy))).contMDiffAt_tangentMap
      (by simp)
  refine (hφ.comp (⟨y, v⟩ : TangentBundle I M) ((hJ _).comp (⟨y, v⟩ : TangentBundle I M)
    hsymm)).congr_of_eventuallyEq ?_
  filter_upwards [(φ.open_target.preimage (FiberBundle.continuous_proj E (TangentSpace I))).mem_nhds
    (show (⟨y, v⟩ : TangentBundle I M).proj ∈ φ.target from hy)] with p hp
  -- Over the target, `φ (φ⁻¹ y) = y`, so the composite of tangent maps lands in the fibre of `y`.
  rcases p with ⟨y', v'⟩
  have key : ∀ y'' : M, y'' = y' → ∀ w : E,
      (TotalSpace.mk' E y'' w : TangentBundle I M) = TotalSpace.mk' E y' w := by
    rintro y'' rfl w
    rfl
  exact (key _ (φ.right_inv hp) _).symm

/-- **Relative extension of a pushed-forward structure.** Let `φ : M' → M` be a partial
diffeomorphism into a Hausdorff σ-compact manifold with a nondegenerate two-form `σ`, and let
`W` be an open subset of the source on which `φ` pulls `σ` back to forms `τ x` compatible with a
smooth almost complex structure `J'` on `M'`. For every compact `K ⊆ W` there is a smooth
`σ`-compatible almost complex structure `J` on `M` for which `φ` is pseudoholomorphic at the
points of `K`: `dφ_x ∘ J'_x = J_(φ x) ∘ dφ_x`. -/
theorem exists_compatible_mfderiv_apply_eq [T2Space M] [SigmaCompactSpace M]
    {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) {W : Set M'} (hW : IsOpen W)
    (hWs : W ⊆ φ.source) (τ : ∀ x : M', SymplecticForm (TangentSpace I' x))
    (hτ : ∀ x ∈ W, (τ x).Compatible (J'.almostComplexStructureAt x))
    (hφ : ∀ x ∈ W, ∀ v w,
      σ.eval₂ (φ x) (mfderiv I' I φ x v) (mfderiv I' I φ x w) = τ x v w)
    {K : Set M'} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ J : SmoothAlmostComplexStructure I M, σ.Compatible J ∧
      ∀ x ∈ K, ∀ v : TangentSpace I' x,
        mfderiv I' I φ x (J' x v) = J (φ x) (mfderiv I' I φ x v) := by
  obtain ⟨J₀, hJ₀⟩ := hσ.exists_compatible
  -- The pushed-forward structure on the target of `φ`, and `J₀` elsewhere.
  classical
  let L : M → AlmostComplexStructure E := fun y ↦
    if hy : y ∈ φ.target then φ.pushforwardAt J' hy else J₀.almostComplexStructureAt y
  have hLt {y : M} (hy : y ∈ φ.target) : L y = φ.pushforwardAt J' hy := dite_eq_left hy
  have hL {x : M'} (hx : x ∈ φ.source) : L (φ x) = φ.pushforwardAt J' (φ.map_source hx) :=
    hLt (φ.map_source hx)
  have hUo : IsOpen (φ '' W) := φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hW hWs
  have hUt : φ '' W ⊆ φ.target := (image_mono hWs).trans φ.image_source_subset
  have hLc : ∀ y ∈ φ '' W, (hσ.symplecticFormAt y).Compatible (L y) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hL (hWs hx)]
    exact φ.compatible_pushforwardAt J' hσ (hWs hx) (hτ x hx) (hφ x hx)
  have hLs : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) y
        (LinearMap.toContinuousLinearMap (L y).toLinearMap)) (φ '' W) := by
    refine ((φ.contMDiffOn_pushforwardEndomorphism J').mono hUt).congr fun y hy ↦ ?_
    rw [hLt (hUt hy), pushforwardAt_toLinearMap]
    -- Converting a continuous linear map to a linear map and back gives the original map.
    congr 1
  have hKc : IsClosed (φ '' K) :=
    (hK.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono (hKW.trans hWs))).isClosed
  obtain ⟨J, hJ, hJK, -, -⟩ :=
    hJ₀.exists_compatible_eqOn L hLc hUo hKc (image_mono hKW) hLs
  refine ⟨J, hJ, fun x hx v ↦ ?_⟩
  have h := congrArg (· (mfderiv I' I φ x v)) (hJK _ (mem_image_of_mem φ hx))
  simp only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply, hL (hWs (hKW hx)),
    pushforwardAt_apply, pushforwardEndomorphism_mfderiv_apply φ J' (hWs (hKW hx))] at h
  exact h.symm

end PartialDiffeomorph
