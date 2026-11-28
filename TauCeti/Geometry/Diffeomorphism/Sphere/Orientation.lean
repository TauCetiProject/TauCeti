/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Preserving
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Orientation
import TauCeti.Geometry.Diffeomorphism.Inversion
import TauCeti.Geometry.Diffeomorphism.Sphere.Isotopy
import TauCeti.Geometry.Diffeomorphism.Sphere.LocalIsotopy
import TauCeti.Geometry.Manifold.Orientation.Pullback
import TauCeti.Geometry.Manifold.Orientation.Sphere
import TauCeti.Geometry.Sphere.Connected
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# The orientation-preserving diffeomorphisms of a sphere

Let `Sⁿ` be the unit sphere of a real inner product space `E` of dimension `n + 1` and `o` an
orientation of `Sⁿ`. For `k ≠ 0` the `C^k` diffeomorphisms of `Sⁿ` preserving `o` form the subgroup
`Diff⁺(Sⁿ) = Diffeomorph.orientationPreservingSubgroup hk o` of `Diff(Sⁿ)`. This file compares it
with the reference inclusion `O(n + 1) → Diff(Sⁿ)` and with the path components of `Diff(Sⁿ)` in
the weak Whitney topology.

`Diff⁺(Sⁿ)` is open, hence closed, in `Diff(Sⁿ)`: by the local isotopy lemma for spheres
(`TauCeti.eventually_exists_diffeotopy_final_eq`) every diffeomorphism near the identity is the
final diffeomorphism of a diffeotopy, which preserves every orientation
(`TauCeti.Diffeotopy.isOrientationPreservingAt_final`). So `Diff⁺(Sⁿ)` is a union of path
components. When `n ≥ 1` the sphere is connected, so it has two orientations, `o` and `-o`, and a
linear isometry of `E` preserves `o` exactly when its determinant is positive, as it does for the
outward-normal orientation (`Orientation.isOrientationPreservingAt_unitSphereEquiv`). A
diffeomorphism outside `Diff⁺(Sⁿ)` reverses `o` everywhere
(`Diffeomorph.isOrientationReversingAt_of_notMem_orientationPreservingSubgroup`), so composing it
with a reflection brings it into `Diff⁺(Sⁿ)`.

Together these give the comparison of the orientation-free statement "every diffeomorphism of `Sⁿ`
is joined to an orthogonal one", the shape of Cerf's theorem `TauCeti.CerfTheorem`, with the
classical statement `π₀ Diff⁺(Sⁿ) = 0`: the two are equivalent for every `n ≥ 1`.

## Main results

* `TauCeti.isClopen_orientationPreservingSubgroup_sphere`: `Diff⁺(Sⁿ)` is open and closed in
  `Diff(Sⁿ)`.
* `TauCeti.unitSphereDiffeomorph_mem_orientationPreservingSubgroup_iff`: for `n ≥ 1`, the
  restriction of a linear isometry `e` of `E` to the sphere preserves an orientation exactly when
  `det e > 0`.
* `TauCeti.orthogonalToDiffSphere_mem_orientationPreservingSubgroup_iff`: the restriction of an
  orthogonal matrix lies in `Diff⁺(Sⁿ)` exactly when its determinant is `1`.
* `TauCeti.forall_exists_joined_orthogonalToDiffSphere_iff_pathConnectedSpace`: every
  diffeomorphism of `Sⁿ`, `n ≥ 1`, is joined to an orthogonal one exactly when `Diff⁺(Sⁿ)` is
  path-connected.

## References

* J. Cerf, *Sur les difféomorphismes de la sphère de dimension trois (Γ₄ = 0)*, Lecture Notes in
  Mathematics 53, Springer (1968), Théorème 1.
-/

public section

open Metric Module
open scoped Manifold ContDiff Topology TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

open Manifold.Orientation

variable {ι : Type*} [Fintype ι] {n : ℕ} {k : ℕ∞ω}

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)]

/-- **`Diff⁺(Sⁿ)` is open and closed.** For `k ≠ 0` and every orientation `o` of the unit sphere,
the `C^k` diffeomorphisms preserving `o` form an open, hence closed, subgroup of `Diff(Sⁿ)` with
the weak Whitney topology: by the local isotopy lemma every diffeomorphism near the identity is
the final diffeomorphism of a diffeotopy, and those preserve every orientation. -/
theorem isClopen_orientationPreservingSubgroup_sphere [FiniteDimensional ℝ E] (hk : k ≠ 0)
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) ι) :
    IsClopen (Diffeomorph.orientationPreservingSubgroup hk o :
      Set (Diff (𝓡 n) (sphere (0 : E) 1) k)) := by
  have hk₁ : 1 ≤ k := ENat.one_le_iff_ne_zero_withTop.2 hk
  have hmem : (Diffeomorph.orientationPreservingSubgroup hk o :
      Set (Diff (𝓡 n) (sphere (0 : E) 1) k)) ∈ 𝓝 1 :=
    (eventually_exists_diffeotopy_final_eq hk₁).mono fun f ⟨Φ, hΦ⟩ ↦
      Diffeomorph.mem_orientationPreservingSubgroup_iff.2 fun x ↦
        hΦ ▸ Φ.isOrientationPreservingAt_final hk₁ o x
  exact (⟨_, Subgroup.isOpen_of_mem_nhds _ hmem⟩ : OpenSubgroup _).isClopen

/-- **Linear isometries and the orientations of a sphere.** For `n ≥ 1` and every orientation `o`
of the unit sphere `Sⁿ`, the restriction to `Sⁿ` of a linear isometry `e` of `E` preserves `o`
exactly when `det e > 0`. The sphere is connected, so `o` is the outward-normal orientation or its
opposite, and `e` preserves or reverses both according to the sign of its determinant. -/
theorem unitSphereDiffeomorph_mem_orientationPreservingSubgroup_iff [NeZero n] (hk : k ≠ 0)
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) ι) (e : E ≃ₗᵢ[ℝ] E) :
    e.unitSphereDiffeomorph k ∈ Diffeomorph.orientationPreservingSubgroup hk o ↔
      0 < LinearMap.det (e.toLinearEquiv : E →ₗ[ℝ] E) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1)
  have : ConnectedSpace (sphere (0 : E) 1) := connectedSpace_sphere n
  -- `o` is the outward-normal orientation of a basis orientation of `E`, or its opposite.
  let σ : Fin n ≃ ι := Fintype.equivOfCardEq (by rw [o.card_eq, finrank_euclideanSpace_fin,
    Fintype.card_fin])
  let oS := (finBasisOfFinrankEq ℝ E Fact.out).orientation.sphereOrientation.reindex σ
  -- Negating both orientations does not change preservation, so `o` may be replaced by `oS`.
  have ho : ∀ x, IsOrientationPreservingAt o o e.unitSphereEquiv x ↔
      IsOrientationPreservingAt oS oS e.unitSphereEquiv x := fun x ↦ by
    rcases Manifold.Orientation.eq_or_eq_neg o oS with ho | ho <;>
      simp only [ho, isOrientationPreservingAt_neg_left, isOrientationReversingAt_neg_right]
  rw [Diffeomorph.mem_orientationPreservingSubgroup_iff,
    LinearIsometryEquiv.coe_unitSphereDiffeomorph, forall_congr' ho]
  refine ⟨fun h ↦ ?_, fun he x ↦
    ((finBasisOfFinrankEq ℝ E Fact.out).orientation.isOrientationPreservingAt_unitSphereEquiv
      he x).reindex σ⟩
  obtain ⟨u⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  refine lt_of_le_of_ne (not_lt.1 fun he ↦ ?_) (LinearEquiv.isUnit_det' _).ne_zero.symm
  exact not_isOrientationPreservingAt_and_isOrientationReversingAt oS oS _ u ⟨h u,
    ((finBasisOfFinrankEq ℝ E Fact.out).orientation.isOrientationReversingAt_unitSphereEquiv
      he u).reindex σ⟩

end InnerProductSpace

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- **Orthogonal matrices in `Diff⁺(Sⁿ)`.** For `n ≥ 1` and every orientation `o` of `Sⁿ`, the
restriction of an orthogonal matrix `A` to the sphere preserves `o` exactly when `det A = 1`. -/
theorem orthogonalToDiffSphere_mem_orientationPreservingSubgroup_iff [NeZero n] (hk : k ≠ 0)
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ι)
    (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
    orthogonalToDiffSphere n k A ∈ Diffeomorph.orientationPreservingSubgroup hk o ↔
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det = 1 := by
  rw [orthogonalToDiffSphere_apply, LinearIsometryEquiv.unitSphereDiffHom_apply,
    unitSphereDiffeomorph_mem_orientationPreservingSubgroup_iff]
  -- The linear map of the isometry has the determinant of the matrix, which is `1` or `-1`.
  -- `Matrix.UnitaryGroup.det_toLinearIsometryEquiv` is stated for the linear map
  -- `toLinearIsometry.toLinearMap`, while the goal carries the coercion of `toLinearEquiv`; the
  -- two are equal by definition but not syntactically, so a plain `rw` does not match and the
  -- lemma is restated for the coercion in the goal.
  rw [show LinearMap.det ((Matrix.UnitaryGroup.toLinearIsometryEquiv A).toLinearEquiv :
      EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) =
        (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det from
      Matrix.UnitaryGroup.det_toLinearIsometryEquiv A]
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup A.property with h | h <;> norm_num [h]

/-- **Cerf's form against the classical form.** For `n ≥ 1`, `k ≠ 0` and every orientation `o` of
the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`, every `C^k` diffeomorphism of `Sⁿ` is joined in the weak Whitney
topology to the restriction of an orthogonal transformation exactly when the orientation-preserving
subgroup `Diff⁺(Sⁿ)` is path-connected, that is, `π₀ Diff⁺(Sⁿ) = 0`. For `n = 3` and `k = ∞` the
first statement is Cerf's theorem `TauCeti.CerfTheorem`. -/
theorem forall_exists_joined_orthogonalToDiffSphere_iff_pathConnectedSpace [NeZero n]
    (hk : k ≠ 0)
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ι) :
    (∀ f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) k,
        ∃ A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ, Joined (orthogonalToDiffSphere n k A) f) ↔
      PathConnectedSpace (Diffeomorph.orientationPreservingSubgroup hk o) := by
  set G := Diffeomorph.orientationPreservingSubgroup hk o
  have hk₁ : 1 ≤ k := ENat.one_le_iff_ne_zero_withTop.2 hk
  -- Joined diffeomorphisms differ by the final diffeomorphism of a diffeotopy, which lies in `G`.
  have hmem {f g} (h : Joined f g) (hg : g ∈ G) : f ∈ G := by
    obtain ⟨Φ, rfl⟩ := (joined_iff_exists_diffeotopy_mul_final_eq hk₁).1 h
    simpa only [mul_inv_cancel_right] using G.mul_mem hg (G.inv_mem
      (Diffeomorph.mem_orientationPreservingSubgroup_iff.2
        (Φ.isOrientationPreservingAt_final hk₁ o)))
  -- The path component of the identity lies in `G`.
  have hsub : pathComponent 1 ⊆ (G : Set (Diff (𝓡 n)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) k)) := fun f hf ↦
    hmem (mem_pathComponent_iff.1 hf).symm G.one_mem
  have hG' : IsPathConnected (G : Set (Diff (𝓡 n)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) k)) ↔ PathConnectedSpace G :=
    isPathConnected_iff_pathConnectedSpace
  rw [← hG']
  refine ⟨fun h ↦ ?_, fun h f ↦ ?_⟩
  · -- `G` is the path component of the identity: an element of `G` is joined to some `A`, which
    -- then lies in `G`, so has determinant `1` and is joined to the identity.
    convert isPathConnected_pathComponent (x := (1 : Diff (𝓡 n)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) k))
    refine Set.Subset.antisymm (fun f hf ↦ ?_) hsub
    obtain ⟨A, hA⟩ := h f
    have hAG := hmem hA hf
    rw [orthogonalToDiffSphere_mem_orientationPreservingSubgroup_iff] at hAG
    have h1 : Joined 1 (orthogonalToDiffSphere n k A) := by
      rw [← map_one (orthogonalToDiffSphere n k), joined_orthogonalToDiffSphere_iff, hAG,
        Submonoid.coe_one, Matrix.det_one]
    exact h1.trans hA
  · -- A diffeomorphism in `G` is joined to the identity; one outside `G` reverses `o`, so its
    -- composite with a reflection `ρ` lies in `G`, and it is joined to `ρ⁻¹ = ρ`.
    have : ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
      connectedSpace_sphere n
    have hjoin : ∀ g ∈ G, Joined 1 g := fun g hg ↦ (h.joinedIn 1 G.one_mem g hg).joined
    by_cases hf : f ∈ G
    · exact ⟨1, by simpa only [map_one] using hjoin f hf⟩
    set R := orthogonalDiagonalReflection ℝ (0 : Fin (n + 1))
    set ρ := orthogonalToDiffSphere n k R
    have hρ : ρ ∉ G := by
      rw [orthogonalToDiffSphere_mem_orientationPreservingSubgroup_iff,
        det_orthogonalDiagonalReflection]
      norm_num
    have hfρ : f * ρ ∈ G := Diffeomorph.mem_orientationPreservingSubgroup_iff.2 fun x ↦ by
      rw [Diffeomorph.coe_mul]
      exact (Diffeomorph.isOrientationReversingAt_of_notMem_orientationPreservingSubgroup hf
        (ρ x)).comp
        (Diffeomorph.isOrientationReversingAt_of_notMem_orientationPreservingSubgroup hρ x)
    refine ⟨R, ?_⟩
    have hρρ : ρ * ρ = 1 := by rw [← map_mul, orthogonalDiagonalReflection_mul_self, map_one]
    simpa only [one_mul, mul_assoc, hρρ, mul_one] using (hjoin _ hfρ).map (continuous_mul_const ρ)

end TauCeti
