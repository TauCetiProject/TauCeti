/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.FirstOrder
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Ext
import TauCeti.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The full isometry group of the round sphere

Every Riemannian isometry between round unit spheres is the restriction of a unique
ambient linear isometry. Thus the full isometry group of the round sphere is the
orthogonal group, not merely a group containing the orthogonal action.

In positive sphere dimension, extend the value and tangent isometry at one point and
use determination of isometries by first-order data on a connected manifold.
The zero-dimensional sphere is disconnected: it consists of two antipodal points,
so bijectivity and agreement at one point suffice instead.

## Main results

* `LinearIsometryEquiv.unitSphereRiemannianIsometry_surjective`: all round-sphere
  isometries come from ambient linear isometries, including in dimension zero.
* `TauCeti.RiemannianIsometry.toLinearIsometryEquiv`: the unique ambient extension.
* `LinearIsometryEquiv.unitSphereIsomMulEquiv`: the orthogonal group is the full
  round-sphere isometry group.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Proposition 5.22
  (determination by value and differential).
* W. P. Thurston, *Three-Dimensional Geometry and Topology*, Vol. 1, §3.8
  (the spherical model geometry and its isometry group).
-/

public section

noncomputable section

open Metric Module
open scoped ContDiff Manifold

namespace LinearIsometryEquiv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n k : ℕ}
  [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ F = k + 1)]

/-- Every Riemannian isometry between round spheres extends to an ambient linear isometry. -/
theorem unitSphereRiemannianIsometry_surjective :
    Function.Surjective
      (unitSphereRiemannianIsometry (E := E) (F := F) (n := n) (k := k)) := by
  have hdim : finrank ℝ E = n + 1 := Fact.out
  let : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
  obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (E := E).mpr zero_le_one
  intro Φ
  obtain ⟨f, hfx, hdf⟩ := Φ.exists_linearIsometryEquiv_apply_eq_and_mfderiv_eq ⟨x, hx⟩
  let Ψ := unitSphereRiemannianIsometry (n := n) (k := k) f
  have hvalue : Ψ ⟨x, hx⟩ = Φ ⟨x, hx⟩ := by
    simpa only [Ψ, coe_unitSphereRiemannianIsometry] using hfx
  refine ⟨f, ?_⟩
  by_cases hn : n = 0
  · -- A permutation of the two-point sphere is fixed by its value at one point.
    have hpair : ∀ y : sphere (0 : E) 1, y = ⟨x, hx⟩ ∨ y = -⟨x, hx⟩ := by
      intro y
      have heq := TauCeti.eq_or_eq_neg_of_norm_eq_of_finrank_eq_one
        (by simpa [hn] using hdim) (x := (y : E)) (y := x)
        (by simp only [norm_eq_of_mem_sphere y, mem_sphere_zero_iff_norm.mp hx])
      exact heq.imp Subtype.ext Subtype.ext
    apply TauCeti.RiemannianIsometry.ext
    intro y
    rcases hpair y with rfl | rfl
    · exact hvalue
    · rcases hpair (Ψ.symm (Φ (-⟨x, hx⟩))) with heq | heq
      · have hbad : Φ (-⟨x, hx⟩) = Φ ⟨x, hx⟩ := by
          simpa [hvalue] using congrArg Ψ heq
        exact (ne_neg_of_mem_unit_sphere ℝ ⟨x, hx⟩ (Φ.injective hbad).symm).elim
      · simpa using (congrArg Ψ heq).symm
  · let : PreconnectedSpace (sphere (0 : E) 1) :=
      Subtype.preconnectedSpace (isPreconnected_sphere
        (Module.one_lt_rank_of_one_lt_finrank (by omega)) (0 : E) 1)
    apply TauCeti.RiemannianIsometry.ext_of_mfderiv_eq Ψ Φ hvalue
    dsimp only [Ψ]
    rw [coe_unitSphereRiemannianIsometry]
    exact hdf

/-- The orthogonal action exhausts the full isometry group of the round sphere. -/
theorem unitSphereIsomHom_surjective :
    Function.Surjective (unitSphereIsomHom (E := E) (n := n)) := by
  intro Φ
  obtain ⟨f, hf⟩ := unitSphereRiemannianIsometry_surjective Φ
  exact ⟨f, by rw [unitSphereIsomHom_apply]; exact hf⟩

end LinearIsometryEquiv

namespace TauCeti.RiemannianIsometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n k : ℕ}
  [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ F = k + 1)]

/-- The unique ambient linear isometry extending a Riemannian isometry of round spheres. -/
def toLinearIsometryEquiv
    (Φ : RiemannianIsometry (𝓡 n) (𝓡 k) (sphere (0 : E) 1) (sphere (0 : F) 1)) : E ≃ₗᵢ[ℝ] F :=
  Classical.choose (LinearIsometryEquiv.unitSphereRiemannianIsometry_surjective Φ)

/-- Restricting the ambient extension recovers the original sphere isometry. -/
@[simp]
theorem unitSphereRiemannianIsometry_toLinearIsometryEquiv
    (Φ : RiemannianIsometry (𝓡 n) (𝓡 k) (sphere (0 : E) 1) (sphere (0 : F) 1)) :
    LinearIsometryEquiv.unitSphereRiemannianIsometry (n := n) (k := k)
      Φ.toLinearIsometryEquiv = Φ :=
  Classical.choose_spec (LinearIsometryEquiv.unitSphereRiemannianIsometry_surjective Φ)

/-- Extending the restriction of an ambient linear isometry recovers that linear isometry. -/
@[simp]
theorem toLinearIsometryEquiv_unitSphereRiemannianIsometry (f : E ≃ₗᵢ[ℝ] F) :
    (LinearIsometryEquiv.unitSphereRiemannianIsometry (n := n) (k := k) f).toLinearIsometryEquiv =
      f := by
  apply LinearIsometryEquiv.unitSphereRiemannianIsometry_injective (n := n) (k := k)
  simp

/-- On unit vectors, the ambient extension agrees with the sphere isometry. -/
@[simp]
theorem toLinearIsometryEquiv_apply
    (Φ : RiemannianIsometry (𝓡 n) (𝓡 k) (sphere (0 : E) 1) (sphere (0 : F) 1))
    (x : sphere (0 : E) 1) : Φ.toLinearIsometryEquiv (x : E) = (Φ x : F) := by
  have h := congrArg (fun Ψ => (Ψ x : F)) Φ.unitSphereRiemannianIsometry_toLinearIsometryEquiv
  simpa only [LinearIsometryEquiv.coe_unitSphereRiemannianIsometry_apply] using h

/-- Ambient extension commutes with inversion of round-sphere isometries. -/
@[simp]
theorem toLinearIsometryEquiv_symm
    (Φ : RiemannianIsometry (𝓡 n) (𝓡 k) (sphere (0 : E) 1) (sphere (0 : F) 1)) :
    Φ.symm.toLinearIsometryEquiv = Φ.toLinearIsometryEquiv.symm := by
  apply LinearIsometryEquiv.unitSphereRiemannianIsometry_injective (n := k) (k := n)
  simp [← LinearIsometryEquiv.unitSphereRiemannianIsometry_symm]

/-- Ambient extension commutes with composition of round-sphere isometries. -/
@[simp]
theorem toLinearIsometryEquiv_trans {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] {l : ℕ} [Fact (finrank ℝ G = l + 1)]
    (Φ : RiemannianIsometry (𝓡 n) (𝓡 k) (sphere (0 : E) 1) (sphere (0 : F) 1))
    (Ψ : RiemannianIsometry (𝓡 k) (𝓡 l) (sphere (0 : F) 1) (sphere (0 : G) 1)) :
    (Φ.trans Ψ).toLinearIsometryEquiv = Φ.toLinearIsometryEquiv.trans Ψ.toLinearIsometryEquiv := by
  apply LinearIsometryEquiv.unitSphereRiemannianIsometry_injective (n := n) (k := l)
  rw [← LinearIsometryEquiv.unitSphereRiemannianIsometry_trans (n := n) (k := k) (l := l)]
  simp

end TauCeti.RiemannianIsometry

namespace LinearIsometryEquiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The orthogonal group is the full Riemannian isometry group of the round unit sphere. -/
def unitSphereIsomMulEquiv : (E ≃ₗᵢ[ℝ] E) ≃* TauCeti.Isom (𝓡 n) (sphere (0 : E) 1) :=
  MulEquiv.ofBijective (unitSphereIsomHom (E := E) (n := n))
    ⟨unitSphereIsomHom_injective, unitSphereIsomHom_surjective⟩

/-- The group isomorphism is the existing orthogonal restriction homomorphism. -/
@[simp]
theorem unitSphereIsomMulEquiv_apply (f : E ≃ₗᵢ[ℝ] E) :
    unitSphereIsomMulEquiv (n := n) f = unitSphereIsomHom f :=
  (rfl)

/-- The inverse group isomorphism takes the unique ambient extension. -/
@[simp]
theorem unitSphereIsomMulEquiv_symm_apply (Φ : TauCeti.Isom (𝓡 n) (sphere (0 : E) 1)) :
    unitSphereIsomMulEquiv.symm Φ = Φ.toLinearIsometryEquiv := by
  apply unitSphereIsomHom_injective (n := n)
  calc
    unitSphereIsomHom (unitSphereIsomMulEquiv.symm Φ) = Φ := by
      rw [← unitSphereIsomMulEquiv_apply]
      exact unitSphereIsomMulEquiv.apply_symm_apply Φ
    _ = unitSphereIsomHom Φ.toLinearIsometryEquiv := by simp

end LinearIsometryEquiv
