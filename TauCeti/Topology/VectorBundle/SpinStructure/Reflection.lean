/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.RealForm
public import TauCeti.Topology.VectorBundle.Orientation.OrthonormalFrame
public import TauCeti.Topology.VectorBundle.SpinStructure.Basic
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Orientation reversal of `Spinᶜ` structures

A `Spinᶜ` structure `s` on a real vector bundle `E` with fibre inner products
(`TauCeti.SpinCStructure`) chooses an orientation of `E`: the frames of its points are positive
for it. This file constructs, from an orthogonal transformation `f` of `ℝⁿ`, the `Spinᶜ` structure
`s.reflect f` whose frames are those of `s` precomposed with `f`; when `f` reverses orientation, as
the reflection `TauCeti.realCliffordCoordReflection i` in the `i`-th coordinate hyperplane does,
it is a `Spinᶜ` structure for the opposite orientation of `E`, the *orientation reversal*
`s.reverse`.

The construction has two steps.

1. **Changing the model frame.** For a lift `s` of the orthonormal frame bundle along
   `ρ : G →* GL(ℝⁿ)` (`TauCeti.OrthonormalFrameLift`) and a linear isometry `r` of `ℝⁿ`, the frames
   `φ ∘ r` of the points of `s` form a lift along `ρ'` whenever `ρ g ∘ r = r ∘ ρ' g` for all `g`
   (`TauCeti.OrthonormalFrameLift.precomp`); its principal bundle is that of `s`. For
   `r = f` and `ρ` the rotation homomorphism of `Spinᶜ(n)`, take `ρ' = ρ ∘ σ`, where
   `σ : Spinᶜ(n) → Spinᶜ(n)`, `[g, z] ↦ [f⁻¹ g, z]`, is the automorphism induced by the quadratic
   isometry `f⁻¹` (`QuadraticMap.Isometry.spinCGroupMap`): its rotation is `f⁻¹ π(g) f`.
2. **Extending along `σ`.** The resulting lift along `ρ ∘ σ` is extended along `σ` to a lift
   along `ρ` (`TauCeti.OrthonormalFrameLift.extendSpinC`), whose principal bundle is
   `P ×_σ Spinᶜ(n)`.

The frame of `[p, 1]` in `s.reflect f` is the frame of `p` precomposed with `f`
(`TauCeti.SpinCStructure.toFrame_reflect_inl`). Consequently `s.reflect f` transports a model
orientation `o` to the orientation that `s` transports `f o` to
(`TauCeti.SpinCStructure.toOrientationCover_toFrame_reflect_inl`), and when `det f < 0` this is
the orientation that `s` transports `-o` to
(`TauCeti.SpinCStructure.toOrientationCover_toFrame_reflect_inl_of_det_neg`,
`TauCeti.SpinCStructure.toOrientationCover_toFrame_reverse_inl`).

The extension of structure group is only available for principal bundles in the universe of the
structure group, so the bundles here have fibres in `Type`, as for
`TauCeti.OrthonormalFrameLift.extendSpinC`.

## Main definitions

* `TauCeti.OrthonormalFrameLift.precomp`: the lift whose frames are those of a lift precomposed
  with a fixed isometry of the model.
* `TauCeti.realCliffordIsometryEquivEuclidean`: an isometry of `realCliffordForm n 0` as a linear
  isometry of `EuclideanSpace ℝ (Fin n)`.
* `TauCeti.realCliffordCoordReflection`: the reflection of `ℝⁿ` in a coordinate hyperplane.
* `TauCeti.SpinCStructure.reflect`: the `Spinᶜ` structure whose frames are those of a `Spinᶜ`
  structure precomposed with an orthogonal transformation of `ℝⁿ`.
* `TauCeti.SpinCStructure.reverse`: the orientation reversal of a `Spinᶜ` structure.

## Main results

* `TauCeti.SpinCStructure.toFrame_reflect_inl`: the frame of `[p, 1]` in `s.reflect f` is the
  frame of `p` precomposed with `f`.
* `TauCeti.SpinCStructure.toOrientationCover_toFrame_reverse_inl`: the orientation reversal
  transports a model orientation `o` to the orientation that the original structure transports
  `-o` to.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

open Bundle MulOpposite CliffordAlgebra

universe w

namespace TauCeti

/-! ### Changing the model frame of a lift -/

namespace OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] {n : ℕ}
  {G : Type*} [Group G] [TopologicalSpace G] {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)}

/-- The **lift with precomposed frames**: for a lift `s` along `ρ`, a linear isometry `r` of the
model `ℝⁿ` and a homomorphism `ρ'` with `ρ g ∘ r = r ∘ ρ' g`, the lift along `ρ'` with the same
principal bundle, whose frame at `p` is the frame of `p` in `s` precomposed with `r`. Its body is
exposed so that the fibre `(s.precomp r ρ' hr).P x` unfolds to `s.P x` downstream. -/
@[expose]
noncomputable def precomp (s : OrthonormalFrameLift F E n G ρ)
    (r : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ' : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hr : ∀ g v, ρ g (r (WithLp.toLp 2 v)).ofLp = (r (WithLp.toLp 2 (ρ' g v))).ofLp) :
    OrthonormalFrameLift F E n G ρ' where
  P := s.P
  toFrame p := ⟨(s.toFrame p).proj, r.trans (s.toFrame p).frame⟩
  continuous_toFrame := OrthonormalFrameBundle.continuous_iff.2 fun v ↦
    (OrthonormalFrameBundle.continuous_totalSpaceMk_frame (r v)).comp s.continuous_toFrame
  proj_toFrame p := s.proj_toFrame p
  toFrame_smul x p g v := by
    have h := s.toFrame_smul x p g (r (WithLp.toLp 2 v)).ofLp
    simp only [WithLp.toLp_ofLp, hr] at h
    simpa only [LinearIsometryEquiv.trans_apply] using h

/-- The frame of a point in the lift with precomposed frames is its frame in the original lift
precomposed with `r`. -/
@[simp]
theorem toFrame_precomp (s : OrthonormalFrameLift F E n G ρ)
    (r : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ' : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hr : ∀ g v, ρ g (r (WithLp.toLp 2 v)).ofLp = (r (WithLp.toLp 2 (ρ' g v))).ofLp)
    (p : TotalSpace G s.P) :
    (s.precomp r ρ' hr).toFrame p = ⟨(s.toFrame p).proj, r.trans (s.toFrame p).frame⟩ :=
  (rfl)

end OrthonormalFrameLift

/-! ### Orthogonal transformations of `ℝⁿ` -/

section Isometry

variable {n : ℕ}

/-- An isometry `f` of the positive-definite form `realCliffordForm n 0` on `Fin n → ℝ`, read as
a linear isometry of `EuclideanSpace ℝ (Fin n)`: it applies `f` to coordinates. -/
noncomputable def realCliffordIsometryEquivEuclidean
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0)) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) where
  toLinearEquiv := ((EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.trans f.toLinearEquiv).trans
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv
  norm_map' u := by
    have h := realCliffordForm_zero_euclideanSpaceEquiv_eq_norm_sq
      ((EuclideanSpace.equiv (Fin n) ℝ).symm (f (EuclideanSpace.equiv (Fin n) ℝ u)))
    rw [ContinuousLinearEquiv.apply_symm_apply, f.map_app,
      realCliffordForm_zero_euclideanSpaceEquiv_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h.symm

@[simp]
theorem realCliffordIsometryEquivEuclidean_apply
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0)) (v : Fin n → ℝ) :
    realCliffordIsometryEquivEuclidean f (WithLp.toLp 2 v) = WithLp.toLp 2 (f v) :=
  (rfl)

/-- The determinant of an isometry read on `EuclideanSpace ℝ (Fin n)` is its determinant on
`Fin n → ℝ`. -/
theorem det_realCliffordIsometryEquivEuclidean
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0)) :
    LinearMap.det ((realCliffordIsometryEquivEuclidean f).toLinearEquiv :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
      LinearMap.det (f.toLinearEquiv : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :=
  LinearMap.det_conj _ (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv

/-- The **reflection of `ℝⁿ` in the `i`-th coordinate hyperplane**, negating the `i`-th
coordinate: the reflection `TauCeti.QuadraticMap.reflection` in the coordinate vector
`Pi.single i 1`, as an isometry of the positive-definite form `realCliffordForm n 0`. Its
determinant is `-1` (`TauCeti.det_realCliffordCoordReflection`), so it reverses orientation. -/
noncomputable def realCliffordCoordReflection (i : Fin n) :
    (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0) :=
  letI : Invertible (realCliffordForm n 0 (Pi.single i 1)) := invertibleOfNonzero (by simp)
  QuadraticMap.orthogonalGroupEquivIsometryEquiv _
    (QuadraticMap.reflectionOrthogonal _ (Pi.single i 1))

/-- The reflection in a coordinate hyperplane is the reflection in the coordinate vector. -/
theorem coe_realCliffordCoordReflection (i : Fin n)
    [Invertible (realCliffordForm n 0 (Pi.single i 1))] :
    ⇑(realCliffordCoordReflection i) =
      ⇑(QuadraticMap.reflection (realCliffordForm n 0) (Pi.single i 1)) := by
  simp only [realCliffordCoordReflection, QuadraticMap.coe_orthogonalGroupEquivIsometryEquiv,
    QuadraticMap.coe_reflectionOrthogonal]
  congr
  exact Subsingleton.elim _ _

/-- The reflection in a coordinate hyperplane has determinant `-1`. -/
theorem det_realCliffordCoordReflection (i : Fin n) :
    LinearMap.det ((realCliffordCoordReflection i).toLinearEquiv :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = -1 := by
  let _ : Invertible (realCliffordForm n 0 (Pi.single i 1)) := invertibleOfNonzero (by simp)
  have he : (realCliffordCoordReflection i).toLinearEquiv =
      QuadraticMap.reflection (realCliffordForm n 0) (Pi.single i 1) :=
    LinearEquiv.ext fun v ↦ congrFun (coe_realCliffordCoordReflection i) v
  have h : LinearEquiv.det (realCliffordCoordReflection i).toLinearEquiv = -1 := by
    rw [he, QuadraticMap.det_reflection]
  rw [← LinearEquiv.coe_det, h, Units.val_neg, Units.val_one]

end Isometry

/-! ### The reflected `Spinᶜ` structure -/

namespace SpinCStructure

open OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ} [NeZero n]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQ" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)

/-- The automorphism `[g, z] ↦ [f⁻¹ g, z]` of `Spinᶜ(n)` induced by an isometry `f` of `ℝⁿ`,
through which the reflected `Spinᶜ` structure is extended: its rotation is `f⁻¹ π(g) f`. -/
noncomputable abbrev reflectHom (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0)) :
    spinCGroup (realCliffordForm n 0) hQ →* spinCGroup (realCliffordForm n 0) hQ :=
  f.symm.toIsometry.spinCGroupMap hQ hQ

/-- The rotation of `[f⁻¹ g, z]` is `f⁻¹ π(g) f`: applying `π(g)` after `f` is applying `f` after
the rotation of `[f⁻¹ g, z]`. -/
theorem toSpecialOrthogonal_reflectHom_apply
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (g : spinCGroup (realCliffordForm n 0) hQ) (v : Fin n → ℝ) :
    (spinCGroup.toSpecialOrthogonal _ hQ g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (f v) =
      f ((spinCGroup.toSpecialOrthogonal _ hQ (reflectHom f g) :
        (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) v) := by
  have h := f.symm.toIsometry.toSpecialOrthogonal_spinCGroupMap_apply hQ hQ g (f v)
  simp only [QuadraticMap.IsometryEquiv.toIsometry_apply,
    QuadraticMap.IsometryEquiv.symm_apply_apply] at h
  rw [h, QuadraticMap.IsometryEquiv.apply_symm_apply]

/-- The **reflection of a `Spinᶜ` structure** `s` by an isometry `f` of `ℝⁿ`: the `Spinᶜ`
structure whose principal bundle is `P ×_σ Spinᶜ(n)`, for the automorphism
`σ : [g, z] ↦ [f⁻¹ g, z]` of `Spinᶜ(n)` (`TauCeti.SpinCStructure.reflectHom`), and in which the
frame of `[p, 1]` is the frame of `p` precomposed with `f`
(`TauCeti.SpinCStructure.toFrame_reflect_inl`). When `f` reverses orientation, it is a `Spinᶜ`
structure for the opposite orientation of the bundle. Its body is exposed so that the fibre
`(s.reflect f).P x` unfolds to `P ×_σ Spinᶜ(n)` downstream. -/
@[expose]
noncomputable def reflect (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (s : SpinCStructure F V n) : SpinCStructure F V n :=
  (s.precomp (realCliffordIsometryEquivEuclidean f)
      (((QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)).subtype.comp
        (spinCGroup.toSpecialOrthogonal (realCliffordForm n 0) _)).comp (reflectHom f))
      fun g v ↦ by
        simpa using toSpecialOrthogonal_reflectHom_apply f g v).extendSpinC
    (reflectHom f) (f.symm.toIsometry.continuous_spinCGroupMap hQ hQ) rfl

/-- **The frame of `[p, 1]`** in the reflection of a `Spinᶜ` structure by `f` is the frame of `p`
precomposed with `f`. -/
theorem toFrame_reflect_inl (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (s : SpinCStructure F V n) (x : X) (p : s.P x) :
    (s.reflect f).toFrame ⟨x, PrincipalBundle.Extend.inl (reflectHom f)
        (f.symm.toIsometry.continuous_spinCGroupMap hQ hQ) p⟩ =
      ⟨(s.toFrame ⟨x, p⟩).proj, (realCliffordIsometryEquivEuclidean f).trans
        (s.toFrame ⟨x, p⟩).frame⟩ := by
  unfold reflect
  exact (toFrame_extendSpinC_inl (s.precomp _ _ _) _ _ _ x p).trans (toFrame_precomp _ _ _ _ _)

/-- The reflection of a `Spinᶜ` structure by `f` transports a model orientation `o` of
`EuclideanSpace ℝ (Fin n)`, along the frame of `[p, 1]`, to the orientation that the frame of
`p` transports `f o` to. -/
theorem toOrientationCover_toFrame_reflect_inl
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0)) (s : SpinCStructure F V n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) (p : s.P x) :
    OrthonormalFrameBundle.toOrientationCover o ((s.reflect f).toFrame ⟨x,
        PrincipalBundle.Extend.inl (reflectHom f)
          (f.symm.toIsometry.continuous_spinCGroupMap hQ hQ) p⟩) =
      OrthonormalFrameBundle.toOrientationCover
        (Orientation.map (Fin n) (realCliffordIsometryEquivEuclidean f).toLinearEquiv o)
        (s.toFrame ⟨x, p⟩) := by
  rw [toFrame_reflect_inl, OrthonormalFrameBundle.toOrientationCover_eq_mk,
    OrthonormalFrameBundle.toOrientationCover_eq_mk, LinearIsometryEquiv.toLinearEquiv_trans,
    Orientation.map_trans]

/-- **Reflection by an orientation-reversing isometry reverses orientation**: if `det f < 0`, the
reflection of a `Spinᶜ` structure by `f` transports a model orientation `o` of
`EuclideanSpace ℝ (Fin n)`, along the frame of `[p, 1]`, to the orientation that the frame of `p`
transports `-o` to. -/
theorem toOrientationCover_toFrame_reflect_inl_of_det_neg
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (hf : LinearMap.det (f.toLinearEquiv : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) < 0)
    (s : SpinCStructure F V n) (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X)
    (p : s.P x) :
    OrthonormalFrameBundle.toOrientationCover o ((s.reflect f).toFrame ⟨x,
        PrincipalBundle.Extend.inl (reflectHom f)
          (f.symm.toIsometry.continuous_spinCGroupMap hQ hQ) p⟩) =
      OrthonormalFrameBundle.toOrientationCover (-o) (s.toFrame ⟨x, p⟩) := by
  rw [toOrientationCover_toFrame_reflect_inl, (Orientation.map_eq_neg_iff_det_neg o _
    (by simp [finrank_euclideanSpace])).2 (by rwa [det_realCliffordIsometryEquivEuclidean])]

/-- The **orientation reversal** of a `Spinᶜ` structure: its reflection by the reflection of `ℝⁿ`
in the first coordinate hyperplane. The frame of `[p, 1]` is the frame of `p` with its first
vector negated, and the structure is a `Spinᶜ` structure for the opposite orientation of the
bundle (`TauCeti.SpinCStructure.toOrientationCover_toFrame_reverse_inl`). -/
noncomputable abbrev reverse (s : SpinCStructure F V n) : SpinCStructure F V n :=
  s.reflect (realCliffordCoordReflection 0)

/-- **The orientation reversal reverses orientation**: it transports a model orientation `o` of
`EuclideanSpace ℝ (Fin n)`, along the frame of `[p, 1]`, to the orientation that the frame of `p`
transports `-o` to. -/
theorem toOrientationCover_toFrame_reverse_inl (s : SpinCStructure F V n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) (p : s.P x) :
    OrthonormalFrameBundle.toOrientationCover o (s.reverse.toFrame ⟨x,
        PrincipalBundle.Extend.inl (reflectHom (realCliffordCoordReflection 0))
          ((realCliffordCoordReflection 0).symm.toIsometry.continuous_spinCGroupMap hQ hQ) p⟩) =
      OrthonormalFrameBundle.toOrientationCover (-o) (s.toFrame ⟨x, p⟩) :=
  toOrientationCover_toFrame_reflect_inl_of_det_neg _
    (by rw [det_realCliffordCoordReflection]; norm_num) s o x p

end SpinCStructure

end TauCeti
