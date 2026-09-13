/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Ray.Primitive

/-!
# Transport of toric rays along lattice equivalences

A linear equivalence of ambient real vector spaces sends a ray of a pointed cone to a ray of the
image cone.  When it is compatible with an equivalence of integral lattices, it also sends the
primitive lattice generator of the ray to the primitive generator of the image ray.

This is the coordinate-free naturality needed when a toric cone is transported to an isomorphic
lattice.  In particular, the canonical primitive generator does not depend on presenting the
lattice and its ambient real vector space in particular coordinates.

## Main declarations

* `TauCeti.Toric.ToricRay.map`: the image ray under a real-linear equivalence.
* `TauCeti.Toric.ToricRay.mapLinearEquiv`: the induced equivalence between the ray types.
* `TauCeti.Toric.IsPrimitiveGenerator.map_equiv`: transport of an arbitrary primitive generator
  under compatible integral and real equivalences.
* `TauCeti.Toric.primitiveGenerator_map_equiv`: naturality of the canonical primitive generator.

## References

The construction is the invariance of primitive ray generators under a lattice isomorphism; see
W. Fulton, *Introduction to Toric Varieties*, §1.2, and D. Cox, J. Little and H. Schenck,
*Toric Varieties*, §1.2.
-/

public section

namespace TauCeti.Toric

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {σ : PointedCone ℝ V}

namespace ToricRay

/-- The image of a ray under a real-linear equivalence, regarded as a ray of the image cone. -/
def map (rho : ToricRay σ) (e : V ≃ₗ[ℝ] V') :
    ToricRay (σ.map (e : V →ₗ[ℝ] V')) where
  val :=
    { toSubmodule := rho.toPointedCone.map (e : V →ₗ[ℝ] V')
      isFaceOf := rho.1.isFaceOf.map_equiv e }
  property := by
    -- Normalize the nested ray/face/cone coercion before applying the span-map theorem.
    rw [show Submodule.span ℝ
        ((rho.toPointedCone.map (e : V →ₗ[ℝ] V') : PointedCone ℝ V') : Set V') =
          (Submodule.span ℝ (rho : Set V)).map (e : V →ₗ[ℝ] V') by
      rw [Submodule.map_span]
      congr]
    exact (e.finrank_map_eq _).trans rho.finrank_span

/-- The pointed cone underlying the image ray is the image of the original ray's cone. -/
@[simp]
theorem toPointedCone_map (rho : ToricRay σ) (e : V ≃ₗ[ℝ] V') :
    (rho.map e).toPointedCone =
      rho.toPointedCone.map (e : V →ₗ[ℝ] V') :=
  (rfl)

/-- A vector belongs to the image ray exactly when it is the image of a vector in the original
ray. -/
@[simp]
theorem mem_map (rho : ToricRay σ) (e : V ≃ₗ[ℝ] V') (x : V') :
    x ∈ rho.map e ↔ e.symm x ∈ rho := by
  -- Expose the underlying cone so `PointedCone.mem_map` supplies an actual preimage.
  rw [show (x ∈ rho.map e) ↔
      x ∈ rho.toPointedCone.map (e : V →ₗ[ℝ] V') from Iff.rfl,
    PointedCone.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    -- The ray and its underlying pointed cone have distinct `SetLike` instances.
    change e.symm (e y) ∈ rho.toPointedCone
    simpa only [LinearEquiv.symm_apply_apply] using hy
  · intro hx
    exact ⟨e.symm x, hx, by simp⟩

/-- Mapping rays along a linear equivalence is injective. -/
private theorem map_injective (e : V ≃ₗ[ℝ] V') :
    Function.Injective
      (fun rho : ToricRay σ ↦ rho.map e) := by
  intro rho tau h
  -- Beta-reduce the function equality before rewriting membership with it.
  change rho.map e = tau.map e at h
  apply SetLike.ext
  intro x
  constructor
  · intro hx
    have hx' : e x ∈ rho.map e := by
      rw [mem_map]
      simpa using hx
    rw [h] at hx'
    have := (mem_map tau e (e x)).1 hx'
    simpa using this
  · intro hx
    have hx' : e x ∈ tau.map e := by
      rw [mem_map]
      simpa using hx
    rw [← h] at hx'
    have := (mem_map rho e (e x)).1 hx'
    simpa using this

/-- Every ray of the image cone comes from a ray of the original cone. -/
private theorem map_surjective (e : V ≃ₗ[ℝ] V') :
    Function.Surjective
      (fun rho : ToricRay σ ↦ rho.map e) := by
  intro tau
  have hcone : (σ.map (e : V →ₗ[ℝ] V')).comap (e : V →ₗ[ℝ] V') = σ := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact e.injective hxy ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  let F : σ.Face :=
    { toSubmodule := tau.toPointedCone.comap (e : V →ₗ[ℝ] V')
      isFaceOf := by
        have hface := tau.1.isFaceOf.comap (e : V →ₗ[ℝ] V')
        rwa [hcone] at hface }
  have hspan :
      (Submodule.span ℝ ((F.toPointedCone : PointedCone ℝ V) : Set V)).map
          (e : V →ₗ[ℝ] V') =
        Submodule.span ℝ (tau : Set V') := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hxF : e.symm x ∈ F := by
        -- Unfold membership in the comapped face through its pointed-cone carrier.
        change e (e.symm x) ∈ tau.toPointedCone
        change x ∈ tau.toPointedCone at hx
        simpa using hx
      exact ⟨e.symm x, hxF, by simp⟩
  let rho : ToricRay σ :=
    ⟨F, by
      rw [← tau.finrank_span, ← hspan]
      exact (e.finrank_map_eq _).symm⟩
  refine ⟨rho, ?_⟩
  apply SetLike.ext
  intro x
  rw [mem_map]
  -- Both sides now use the pointed-cone carrier of the target ray.
  change e (e.symm x) ∈ tau.toPointedCone ↔ x ∈ tau.toPointedCone
  simp

/-- A real-linear equivalence induces an equivalence between the rays of a cone and those of its
image cone. -/
noncomputable def mapLinearEquiv (e : V ≃ₗ[ℝ] V') :
    ToricRay σ ≃ ToricRay (σ.map (e : V →ₗ[ℝ] V')) :=
  Equiv.ofBijective (fun rho ↦ rho.map e) ⟨map_injective e, map_surjective e⟩

@[simp]
theorem mapLinearEquiv_apply (e : V ≃ₗ[ℝ] V') (rho : ToricRay σ) :
    mapLinearEquiv e rho = rho.map e :=
  (rfl)

end ToricRay

namespace IsPrimitiveGenerator

/-- A compatible pair of integral and real-linear equivalences sends a primitive generator to a
primitive generator of the image ray. -/
theorem map_equiv {f : N ≃+ N'} {e : V ≃ₗ[ℝ] V'} (hfe : ∀ n, e (i n) = i' (f n))
    {rho : ToricRay σ} {v : N} (hv : IsPrimitiveGenerator i rho v) :
    IsPrimitiveGenerator i' (rho.map e) (f v) := by
  rw [isPrimitiveGenerator_iff]
  refine ⟨?_, (f.toIntLinearEquiv.isPrimitive_iff).2 hv.isPrimitive⟩
  rw [← hfe]
  -- Pass through the pointed-cone carrier to use the defining witness for `PointedCone.map`.
  change e (i v) ∈ rho.toPointedCone.map (e : V →ₗ[ℝ] V')
  have hv' := hv.mem
  change i v ∈ rho.toPointedCone at hv'
  exact ⟨i v, hv', rfl⟩

end IsPrimitiveGenerator

/-- The canonical primitive generator commutes with transport along compatible integral and
real-linear equivalences. -/
theorem primitiveGenerator_map_equiv {f : N ≃+ N'} {e : V ≃ₗ[ℝ] V'}
    (hfe : ∀ n, e (i n) = i' (f n)) (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (rho : ToricRay σ) :
    f (primitiveGenerator hi hσ rho) =
      primitiveGenerator ((isIntegralLattice_congr f e hfe).1 hi)
        ((isToricCone_map_equiv_iff hfe).2 hσ) (rho.map e) :=
  (isPrimitiveGenerator_primitiveGenerator hi hσ rho).map_equiv hfe
    |>.eq_primitiveGenerator ((isIntegralLattice_congr f e hfe).1 hi)
      ((isToricCone_map_equiv_iff hfe).2 hσ)

end TauCeti.Toric
