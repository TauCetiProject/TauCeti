/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.NormalFrame

/-!
# Local trivializations of the Euclidean normal bundle

The normal fibres of a `C^(n+1)` immersion into a finite-dimensional real inner product
space admit local linear trivializations whose coordinate maps are `C^n`. The model fibre at a
chosen point `x₀` is its normal space.
Orthogonal projection transports that space to nearby normal spaces; the inverse is
obtained by inverting the compression of this projection to the original normal space.

`normalTrivialization` uses the existing subspace topology on the total normal space.
The forward fibre coordinates extend smoothly to all ambient vectors, and the inverse
fibre coordinates are smooth as ambient-vector-valued maps. These formulas also give
smooth changes of normal coordinates without assuming a smooth bundle structure in
advance. No compactness, injectivity of the core map, or choice of basis is needed.

The projection and its regularity are supplied by `normalSubspace` and
`contMDiff_normalSubspace_starProjection`; the fibrewise inverse identity uses
`Submodule.starProjection_inverse_apply`. The algebraic coordinate operators only require
orthogonal projections onto the relevant fibres; their recovery identity only requires the
moving normal fibre to be finite-dimensional. Regularity holds in a complete ambient space.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), the normal-bundle construction preceding Theorem 6.24.
-/

public section

noncomputable section

open Set Function Filter Topology Bundle
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {f : M → V}

section Projection

/-- The normal projection at `x`, compressed to the normal space at `x₀`. Its
invertibility specifies the domain of the local normal trivialization at `x₀`. -/
def normalCompression (I : ModelWithCorners ℝ E H) (f : M → V) (x₀ x : M)
    [(normalSubspace I f x₀).HasOrthogonalProjection]
    [(normalSubspace I f x).HasOrthogonalProjection] :
    normalSubspace I f x₀ →L[ℝ] normalSubspace I f x₀ :=
  (normalSubspace I f x₀).orthogonalProjectionOnto ∘L
    (normalSubspace I f x).starProjection ∘L (normalSubspace I f x₀).subtypeL

/-- The compression is the moving normal projection sandwiched between inclusion
and projection for the reference fibre. -/
theorem normalCompression_def (x₀ x : M)
    [(normalSubspace I f x₀).HasOrthogonalProjection]
    [(normalSubspace I f x).HasOrthogonalProjection] :
    normalCompression I f x₀ x = (normalSubspace I f x₀).orthogonalProjectionOnto ∘L
      (normalSubspace I f x).starProjection ∘L (normalSubspace I f x₀).subtypeL :=
  (rfl)

/-- At the reference point the compression is the identity. -/
@[simp] theorem normalCompression_self (x₀ : M)
    [(normalSubspace I f x₀).HasOrthogonalProjection] : normalCompression I f x₀ x₀ = 1 := by
  ext w
  simp [normalCompression, Submodule.starProjection_eq_self_iff.mpr w.property]

/-- Ambient-vector coordinates in the reference normal fibre. These recover a reference
vector after projection to the moving normal fibre whenever the compression is invertible. -/
def normalCoordinateMap (I : ModelWithCorners ℝ E H) (f : M → V) (x₀ x : M)
    [(normalSubspace I f x₀).HasOrthogonalProjection]
    [(normalSubspace I f x).HasOrthogonalProjection] :
    V →L[ℝ] normalSubspace I f x₀ :=
  Ring.inverse (normalCompression I f x₀ x) ∘L
    (normalSubspace I f x₀).orthogonalProjectionOnto

/-- The ambient coordinate operator is the inverse compression followed by
projection onto the reference normal space. -/
theorem normalCoordinateMap_def (x₀ x : M)
    [(normalSubspace I f x₀).HasOrthogonalProjection]
    [(normalSubspace I f x).HasOrthogonalProjection] :
    normalCoordinateMap I f x₀ x = Ring.inverse (normalCompression I f x₀ x) ∘L
      (normalSubspace I f x₀).orthogonalProjectionOnto :=
  (rfl)

/-- Coordinates of a projected reference vector recover that vector. -/
@[simp] theorem normalCoordinateMap_starProjection (x₀ x : M)
    [(normalSubspace I f x₀).HasOrthogonalProjection]
    [(normalSubspace I f x).HasOrthogonalProjection]
    (hx : IsUnit (normalCompression I f x₀ x)) (w : normalSubspace I f x₀) :
    normalCoordinateMap I f x₀ x ((normalSubspace I f x).starProjection w) = w := by
  have h := congrArg (fun T : normalSubspace I f x₀ →L[ℝ] normalSubspace I f x₀ => T w)
    (Ring.inverse_mul_cancel _ hx)
  simpa [normalCoordinateMap, normalCompression, mul_apply_eq_comp] using h

/-- The continuous-linear change from the reference normal fibre at `x₀` to that at `x₁`.
On overlaps it transports coordinates between the corresponding normal trivializations. -/
def normalCoordinateChange (I : ModelWithCorners ℝ E H) (f : M → V) (x₀ x₁ x : M)
    [(normalSubspace I f x₁).HasOrthogonalProjection]
    [(normalSubspace I f x).HasOrthogonalProjection] :
    normalSubspace I f x₀ →L[ℝ] normalSubspace I f x₁ :=
  normalCoordinateMap I f x₁ x ∘L (normalSubspace I f x).starProjection ∘L
    (normalSubspace I f x₀).subtypeL

/-- A change of normal coordinates projects into the moving fibre and takes its target
reference coordinates. -/
@[simp] theorem normalCoordinateChange_apply (x₀ x₁ x : M)
    [(normalSubspace I f x₁).HasOrthogonalProjection]
    [(normalSubspace I f x).HasOrthogonalProjection]
    (w : normalSubspace I f x₀) :
    normalCoordinateChange I f x₀ x₁ x w =
      normalCoordinateMap I f x₁ x ((normalSubspace I f x).starProjection w) :=
  (rfl)

/-- Projecting the coordinates recovers a normal vector, when the two fibres have the
same finite dimension and the compression is invertible. -/
theorem starProjection_normalCoordinateMap (x₀ x : M)
    [FiniteDimensional ℝ (normalSubspace I f x)]
    [(normalSubspace I f x₀).HasOrthogonalProjection]
    (hrank : Module.finrank ℝ (normalSubspace I f x₀) =
      Module.finrank ℝ (normalSubspace I f x))
    (hx : IsUnit (normalCompression I f x₀ x)) {v : V} (hv : v ∈ normalSubspace I f x) :
    (normalSubspace I f x).starProjection (normalCoordinateMap I f x₀ x v) = v :=
  Submodule.starProjection_inverse_apply hrank hx hv

end Projection

section Regularity

variable [CompleteSpace V] [FiniteDimensional ℝ E] [I.Boundaryless]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M]

/-- The compression of the normal projection varies `C^n` along a `C^(n+1)` immersion. -/
theorem contMDiff_normalCompression
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (x₀ : M) :
    ContMDiff I 𝓘(ℝ, normalSubspace I f x₀ →L[ℝ] normalSubspace I f x₀) n
      (fun x => normalCompression I f x₀ x) :=
  contMDiff_const.clm_comp
    ((contMDiff_normalSubspace_starProjection hf himm).clm_comp contMDiff_const)

/-- The ambient coordinate operator of a `C^(n+1)` map is `C^n` at an immersion point
where the compression is invertible. -/
theorem contMDiffAt_normalCoordinateMap {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f x)
    (himm : Injective (mfderiv I 𝓘(ℝ, V) f x)) (x₀ : M)
    (hx : IsUnit (normalCompression I f x₀ x)) :
    ContMDiffAt I 𝓘(ℝ, V →L[ℝ] normalSubspace I f x₀) n
      (fun y => normalCoordinateMap I f x₀ y) x := by
  simp_rw [normalCoordinateMap_def]
  have hinv := (contDiffAt_ringInverse ℝ
    (R := normalSubspace I f x₀ →L[ℝ] normalSubspace I f x₀) (n := n) hx.unit).contMDiffAt
  rw [hx.unit_spec] at hinv
  have hcompression :=
    (contMDiffAt_const (c := (normalSubspace I f x₀).orthogonalProjectionOnto)).clm_comp
    ((contMDiffAt_normalSubspace_starProjection hf himm).clm_comp
      (contMDiffAt_const (c := (normalSubspace I f x₀).subtypeL)))
  exact (hinv.comp x hcompression).clm_comp
    (contMDiffAt_const (c := (normalSubspace I f x₀).orthogonalProjectionOnto))

/-- Changes between projected normal-fibre coordinates are `C^n` wherever the target
compression is invertible. On the overlap of two trivializations these are their fibrewise
transition operators. -/
theorem contMDiffOn_normalCoordinateChange
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (x₀ x₁ : M) :
    ContMDiffOn I 𝓘(ℝ, normalSubspace I f x₀ →L[ℝ] normalSubspace I f x₁) n
      (fun x => normalCoordinateChange I f x₀ x₁ x)
      {x | IsUnit (normalCompression I f x₁ x)} := by
  intro x hx
  exact ((contMDiffAt_normalCoordinateMap (hf x) (himm x) x₁ hx).clm_comp
    ((contMDiff_normalSubspace_starProjection hf himm x).clm_comp
      contMDiffAt_const)).contMDiffWithinAt

end Regularity

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [I.Boundaryless]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M]

/-- Local linear trivialization of the normal bundle of a `C^(n+1)` immersion, with
model fibre the normal space at `x₀`. Its base set is the open neighbourhood on which
`normalCompression I f x₀` is invertible. -/
def normalTrivialization
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (x₀ : M) :
    Trivialization (normalSubspace I f x₀)
      (π (normalSubspace I f x₀) (fun x => normalSubspace I f x)) := by
  let U : Set M := {x | IsUnit (normalCompression I f x₀ x)}
  have hU : IsOpen U := (Units.isOpen (R := normalSubspace I f x₀ →L[ℝ]
    normalSubspace I f x₀)).preimage (contMDiff_normalCompression hf himm x₀).continuous
  let ι : TotalSpace (normalSubspace I f x₀) (fun x => normalSubspace I f x) → M × V :=
    fun p => (p.proj, (p.2 : V))
  have hι : IsEmbedding ι := isEmbedding_totalSpace_normalSubspace f
  refine
    { toFun := fun p => (p.proj, normalCoordinateMap I f x₀ p.proj p.2)
      invFun := fun p => ⟨p.1, ⟨(normalSubspace I f p.1).starProjection p.2,
        Submodule.starProjection_apply_mem _ _⟩⟩
      source := (π (normalSubspace I f x₀) (fun x => normalSubspace I f x)) ⁻¹' U
      target := U ×ˢ univ
      map_source' := fun p hp => ⟨hp, mem_univ _⟩
      map_target' := fun p hp => hp.1
      left_inv' := ?_
      right_inv' := ?_
      open_source := hU.preimage hι.continuous.fst
      open_target := hU.prod isOpen_univ
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_
      baseSet := U
      open_baseSet := hU
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ => rfl }
  · intro p hp
    apply hι.injective
    exact Prod.ext rfl (starProjection_normalCoordinateMap x₀ p.proj
      ((finrank_normalSubspace (himm x₀)).trans (finrank_normalSubspace (himm p.proj)).symm)
      hp p.2.property)
  · rintro ⟨x, w⟩ hx
    exact Prod.ext rfl (normalCoordinateMap_starProjection x₀ x hx.1 w)
  · intro p hp
    exact (hι.continuous.fst.continuousAt.prodMk
      (((contMDiffAt_normalCoordinateMap (hf p.proj) (himm p.proj) x₀ hp).continuousAt.comp
        hι.continuous.fst.continuousAt).clm_apply
          hι.continuous.snd.continuousAt)).continuousWithinAt
  · apply hι.isInducing.continuousOn_iff.mpr
    exact (continuous_fst.prodMk
      (((contMDiff_normalSubspace_starProjection hf himm).continuous.comp continuous_fst).clm_apply
        ((normalSubspace I f x₀).subtypeL.continuous.comp continuous_snd))).continuousOn

/-- The base set of the normal trivialization is characterized by invertibility of
its compression. -/
@[simp] theorem mem_normalTrivialization_baseSet
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (x₀ x : M) :
    x ∈ (normalTrivialization hf himm x₀).baseSet ↔ IsUnit (normalCompression I f x₀ x) :=
  Iff.rfl

/-- The forward normal trivialization uses the ambient coordinate operator. -/
@[simp] theorem normalTrivialization_apply
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (x₀ : M)
    (p : TotalSpace (normalSubspace I f x₀) (fun x => normalSubspace I f x)) :
    normalTrivialization hf himm x₀ p = (p.proj, normalCoordinateMap I f x₀ p.proj p.2) :=
  (rfl)

/-- The transition operator takes source trivialization coordinates to target coordinates.
Source base-set membership suffices, so the identity applies in particular on overlaps. -/
theorem normalCoordinateChange_normalTrivialization
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (x₀ x₁ : M)
    (p : TotalSpace (normalSubspace I f x₀) (fun x => normalSubspace I f x))
    (hp : p.proj ∈ (normalTrivialization hf himm x₀).baseSet) :
    normalCoordinateChange I f x₀ x₁ p.proj (normalTrivialization hf himm x₀ p).2 =
      (normalTrivialization hf himm x₁ ⟨p.proj, p.2⟩).2 := by
  simp only [normalTrivialization_apply, normalCoordinateChange_apply]
  rw [starProjection_normalCoordinateMap x₀ p.proj
    ((finrank_normalSubspace (himm x₀)).trans (finrank_normalSubspace (himm p.proj)).symm)
    hp p.2.property]

/-- The inverse normal trivialization projects the reference vector into the moving
normal fibre, retaining its base point. -/
@[simp] theorem normalTrivialization_symm_apply
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (x₀ : M)
    (p : M × normalSubspace I f x₀) :
    (normalTrivialization hf himm x₀).toOpenPartialHomeomorph.symm p =
      ⟨p.1, ⟨(normalSubspace I f p.1).starProjection p.2,
        Submodule.starProjection_apply_mem _ _⟩⟩ :=
  (rfl)

/-- Normal trivializations are linear on each fibre. -/
instance instIsLinearNormalTrivialization
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (x₀ : M) :
    (normalTrivialization hf himm x₀).IsLinear ℝ where
  linear x _ := by
    constructor <;> intros <;> simp

/-- The forward normal coordinates extend to a `C^n` map on the ambient product,
above the base set of the trivialization. -/
theorem contMDiffOn_normalCoordinates
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (x₀ : M) :
    ContMDiffOn (I.prod 𝓘(ℝ, V)) 𝓘(ℝ, normalSubspace I f x₀) n
      (fun p : M × V => normalCoordinateMap I f x₀ p.1 p.2)
      ((normalTrivialization hf himm x₀).baseSet ×ˢ univ) := by
  intro p hp
  exact (((contMDiffAt_normalCoordinateMap (hf p.1) (himm p.1) x₀ hp.1).comp p
    contMDiffAt_fst).clm_apply contMDiffAt_snd).contMDiffWithinAt

/-- The inverse normal coordinates, viewed in the ambient vector space, are `C^n`. -/
theorem contMDiff_normalTrivialization_symm_snd
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (x₀ : M) :
    ContMDiff (I.prod 𝓘(ℝ, normalSubspace I f x₀)) 𝓘(ℝ, V) n
      (fun p : M × normalSubspace I f x₀ =>
        ((normalTrivialization hf himm x₀).toOpenPartialHomeomorph.symm p).2.val) := by
  convert ((contMDiff_normalSubspace_starProjection hf himm).comp contMDiff_fst).clm_apply
    ((normalSubspace I f x₀).subtypeL.contMDiff.comp contMDiff_snd) using 1
  funext p
  exact congrArg (fun q => (q.2 : V)) (normalTrivialization_symm_apply hf himm x₀ p)

end TauCeti
