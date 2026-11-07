/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.Rigidity
public import TauCeti.Geometry.Manifold.Instances.Stiefel
public import TauCeti.Geometry.Sphere.LinearIsometry
public import TauCeti.LinearAlgebra.OrthogonalGroup
public import TauCeti.Topology.Grassmannian.Orthonormal

/-!
# The Stiefel manifold as a homogeneous space

Linear isometries of a real inner product space `E` act on its orthonormal `k`-frames
`TauCeti.stiefel E k`, vector by vector and continuously (`TauCeti.stiefel.instMulAction`,
`TauCeti.stiefel.instContinuousConstSMul`). Projecting a frame to one of its vectors, a point of
the unit sphere, is equivariant (`TauCeti.stiefelProj_smul`), and when `E` is finite-dimensional
the action is transitive (`TauCeti.stiefel.instIsPretransitive`): two orthonormal frames have
the same Gram matrix, so a linear isometry moves one to the other
(`TauCeti.exists_linearIsometryEquiv_of_inner_eq`).

On Euclidean space `ℝᴺ` the Stiefel manifold, which carries the smooth structure, has the same
points as the orthonormal frames `TauCeti.finiteOrthonormalFrame ℝ r N` of the Grassmannian
theory, read in the coordinates of `Fin N → ℝ`. The two carriers are homeomorphic
(`TauCeti.stiefel.finiteOrthonormalFrameHomeomorph`), the homeomorphism sends the action of an
orthogonal matrix through its linear isometry to its action
`TauCeti.finiteOrthonormalFrame.unitaryMap` on frames
(`TauCeti.stiefel.finiteOrthonormalFrameHomeomorph_smul`), and it sends the frame of the first
`r` standard basis vectors to the standard frame. Composing with
`TauCeti.finiteOrthonormalFrame.unitaryQuotientHomeomorph` and
`TauCeti.finiteOrthonormalFrame.specialOrthogonalQuotientHomeomorph` presents the Stiefel manifold
`V_r(ℝ^(r + m))` as `O(r + m) / O(m)`, and as `SO(r + m) / SO(m)` for `m ≥ 1`; in particular the
ordered orthonormal two-frames of `ℝⁿ`, the unit tangent bundle of `Sⁿ⁻¹`, are `SO(n) / SO(n - 2)`
for `n ≥ 3`.

## Main declarations

* `TauCeti.stiefel.instMulAction`, `TauCeti.stiefel.instContinuousConstSMul`: linear isometries
  act continuously on orthonormal frames.
* `TauCeti.stiefelProj_smul`: the projections to the sphere are equivariant.
* `TauCeti.stiefel.instIsPretransitive`: the action is transitive in finite dimension.
* `TauCeti.stiefel.finiteOrthonormalFrameHomeomorph`: the Stiefel manifold of `ℝᴺ` is homeomorphic
  to the orthonormal frames of the Grassmannian theory.
* `TauCeti.stiefel.finiteOrthonormalFrameHomeomorph_smul`: the homeomorphism intertwines the
  actions of orthogonal matrices.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7 (Stiefel
  manifolds as coset spaces of orthogonal groups).
-/

public section

noncomputable section

open Function Matrix Module MulAction

namespace TauCeti

/-! ### Linear isometries act on frames -/

section Action

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

/-- Linear isometries of `E` act on orthonormal `k`-frames of `E`, vector by vector. -/
instance stiefel.instMulAction : MulAction (E ≃ₗᵢ[ℝ] E) (stiefel E k) where
  smul e v := ⟨e ∘ v.1, mem_stiefel_iff.2 ((mem_stiefel_iff.1 v.2).comp_linearIsometryEquiv e)⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- A linear isometry moves a frame by moving each of its vectors. -/
@[simp]
theorem stiefel.coe_smul (e : E ≃ₗᵢ[ℝ] E) (v : stiefel E k) :
    ((e • v : stiefel E k) : Fin k → E) = e ∘ v.1 :=
  (rfl)

/-- Each linear isometry acts continuously on orthonormal frames. -/
instance stiefel.instContinuousConstSMul : ContinuousConstSMul (E ≃ₗᵢ[ℝ] E) (stiefel E k) where
  continuous_const_smul e := continuous_induced_rng.2 <| continuous_pi fun i ↦
    e.continuous.comp ((continuous_apply i).comp continuous_subtype_val)

/-- Projecting a frame to one of its vectors, a point of the unit sphere, is equivariant for the
actions of linear isometries on frames and on the sphere. -/
@[simp]
theorem stiefelProj_smul (e : E ≃ₗᵢ[ℝ] E) (i : Fin k) (v : stiefel E k) :
    stiefelProj E k i (e • v) = e • stiefelProj E k i v :=
  Subtype.ext (by simp)

/-- **Linear isometries act transitively on orthonormal frames** of a finite-dimensional real
inner product space. -/
instance stiefel.instIsPretransitive [FiniteDimensional ℝ E] :
    IsPretransitive (E ≃ₗᵢ[ℝ] E) (stiefel E k) where
  exists_smul_eq v w := by
    classical
    obtain ⟨e, he⟩ := exists_linearIsometryEquiv_of_inner_eq (𝕜 := ℝ) (v := v.1) (w := w.1)
      fun i j ↦ by rw [orthonormal_iff_ite.1 (mem_stiefel_iff.1 v.2),
        orthonormal_iff_ite.1 (mem_stiefel_iff.1 w.2)]
    exact ⟨e, Subtype.ext (funext he)⟩

end Action

/-! ### Comparison with the orthonormal frames of the Grassmannian theory -/

section Comparison

variable (r N : ℕ)

/-- **The Stiefel manifold of `ℝᴺ` is the space of orthonormal frames** of the Grassmannian
theory: a frame of `EuclideanSpace ℝ (Fin N)` is read in the coordinates of `Fin N → ℝ`. -/
def stiefel.finiteOrthonormalFrameHomeomorph :
    stiefel (EuclideanSpace ℝ (Fin N)) r ≃ₜ finiteOrthonormalFrame ℝ r N :=
  (Homeomorph.piCongrRight fun _ ↦ PiLp.homeomorph 2 fun _ : Fin N ↦ ℝ).subtype
    fun _ ↦ mem_stiefel_iff

variable {r N}

@[simp]
theorem stiefel.coe_finiteOrthonormalFrameHomeomorph_apply
    (v : stiefel (EuclideanSpace ℝ (Fin N)) r) (i : Fin r) :
    (finiteOrthonormalFrameHomeomorph r N v : Fin r → Fin N → ℝ) i = (v.1 i).ofLp :=
  (rfl)

@[simp]
theorem stiefel.coe_finiteOrthonormalFrameHomeomorph_symm_apply
    (f : finiteOrthonormalFrame ℝ r N) (i : Fin r) :
    ((finiteOrthonormalFrameHomeomorph r N).symm f : Fin r → EuclideanSpace ℝ (Fin N)) i =
      WithLp.toLp 2 (f.1 i) :=
  (rfl)

/-- The comparison homeomorphism intertwines the action of an orthogonal matrix on the Stiefel
manifold, through its linear isometry, with its action on orthonormal frames by applying it to
each vector. -/
theorem stiefel.finiteOrthonormalFrameHomeomorph_smul (A : orthogonalGroup (Fin N) ℝ)
    (v : stiefel (EuclideanSpace ℝ (Fin N)) r) :
    finiteOrthonormalFrameHomeomorph r N (orthogonalGroupToLinearIsometryEquiv A • v) =
      finiteOrthonormalFrame.unitaryMap A (finiteOrthonormalFrameHomeomorph r N v) :=
  Subtype.ext <| funext fun i ↦ by simp

/-- The comparison homeomorphism sends the frame of the first `r` standard basis vectors of
`ℝᴺ` to the standard frame. -/
theorem stiefel.finiteOrthonormalFrameHomeomorph_symm_standard (h : r ≤ N) (i : Fin r) :
    ((finiteOrthonormalFrameHomeomorph r N).symm (finiteOrthonormalFrame.standard ℝ h) :
        Fin r → EuclideanSpace ℝ (Fin N)) i =
      EuclideanSpace.single (Fin.castLE h i) 1 := by
  simp

end Comparison

end TauCeti
