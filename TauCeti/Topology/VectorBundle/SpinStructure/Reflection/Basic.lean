/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Reflection
public import TauCeti.Topology.Algebra.CliffordAlgebra.RealForm
public import TauCeti.Topology.VectorBundle.Orientation.OrthonormalFrame
public import TauCeti.Topology.VectorBundle.SpinStructure.Basic

/-!
# Orientation reversal of `Spinᶜ` structures

A `Spinᶜ` structure `s` on a real vector bundle `E` with fibre inner products
(`TauCeti.SpinCStructure`) chooses an orientation of `E`: the frames of its points are positive
for it. This file constructs, from an orthogonal transformation `f` of `ℝⁿ`, the `Spinᶜ` structure
`s.precompIsometry f` whose frames are those of `s` precomposed with `f`; when `f` reverses
orientation, it is a `Spinᶜ` structure for the opposite orientation of `E`. Choosing for `f` the
reflection `TauCeti.realCliffordCoordReflection 0` in the first coordinate hyperplane defines the
*orientation reversal* `s.reverse`.

The construction has two steps.

1. **Changing the model frame.** For a lift `s` of the orthonormal frame bundle along
   `ρ : G →* GL(ℝⁿ)` (`TauCeti.OrthonormalFrameLift`) and a linear isometry `r` of `ℝⁿ`, the frames
   `φ ∘ r` of the points of `s` form a lift along `ρ'` whenever `ρ g ∘ r = r ∘ ρ' g` for all `g`
   (`TauCeti.OrthonormalFrameLift.precomp`); its principal bundle is that of `s`. For
   `r = f` (read on `EuclideanSpace ℝ (Fin n)` through
   `TauCeti.realCliffordIsometryEquivEuclidean`) and `ρ` the rotation homomorphism of `Spinᶜ(n)`,
   take `ρ' = ρ ∘ σ`, where `σ : Spinᶜ(n) → Spinᶜ(n)`, `[g, z] ↦ [f⁻¹ g, z]`, is the automorphism
   induced by the quadratic isometry `f⁻¹` (`QuadraticMap.Isometry.spinCGroupMap`): its rotation
   is `f⁻¹ π(g) f`. This gives the lift `TauCeti.SpinCStructure.precompIsometryLift`.
2. **Extending along `σ`.** The resulting lift along `ρ ∘ σ` is extended along `σ` to a lift
   along `ρ` (`TauCeti.OrthonormalFrameLift.extendSpinC`), whose principal bundle is
   `P ×_σ Spinᶜ(n)`.

The frame of `[p, 1]` in `s.precompIsometry f` is the frame of `p` precomposed with `f`
(`TauCeti.SpinCStructure.toFrame_precompIsometry_inl`). Consequently `s.precompIsometry f`
transports a model orientation `o` to the orientation that `s` transports `f o` to
(`TauCeti.SpinCStructure.toOrientationCover_toFrame_precompIsometry_inl`), and when `det f < 0`
this is the orientation that `s` transports `-o` to
(`TauCeti.SpinCStructure.toOrientationCover_toFrame_precompIsometry_inl_of_det_neg`,
`TauCeti.SpinCStructure.toOrientationCover_toFrame_reverse_inl`).

The extension of structure group is only available for principal bundles in the universe of the
structure group, so `SpinCStructure.precompIsometry` and `SpinCStructure.reverse` are stated for
bundles with fibres in `Type`, as for `TauCeti.OrthonormalFrameLift.extendSpinC`.

## Main definitions

* `TauCeti.SpinCStructure.precompIsometry`: the `Spinᶜ` structure whose frames are those of a
  `Spinᶜ` structure precomposed with an orthogonal transformation of `ℝⁿ`.
* `TauCeti.SpinCStructure.reverse`: the orientation reversal of a `Spinᶜ` structure.

## Main results

* `TauCeti.SpinCStructure.precompIsometryHom_refl`,
  `TauCeti.SpinCStructure.precompIsometryHom_comp`: the automorphism of `Spinᶜ(n)` induced by an
  isometry of `ℝⁿ` is functorial.
* `TauCeti.SpinCStructure.toFrame_precompIsometry_inl`: the frame of `[p, 1]` in
  `s.precompIsometry f` is the frame of `p` precomposed with `f`.
* `TauCeti.SpinCStructure.toOrientationCover_toFrame_reverse_inl`: the orientation reversal
  transports a model orientation `o` to the orientation that the original structure transports
  `-o` to.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

open Bundle MulOpposite CliffordAlgebra

namespace TauCeti

/-! ### Precomposing the frames of a `Spinᶜ` structure with an isometry -/

namespace SpinCStructure

open OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ} [NeZero n]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQ" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)

/-- The automorphism `[g, z] ↦ [f⁻¹ g, z]` of `Spinᶜ(n)` induced by an isometry `f` of `ℝⁿ`,
through which `TauCeti.SpinCStructure.precompIsometry` is extended: its rotation is
`f⁻¹ π(g) f`. -/
noncomputable abbrev precompIsometryHom
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0)) :
    spinCGroup (realCliffordForm n 0) hQ →* spinCGroup (realCliffordForm n 0) hQ :=
  f.symm.toIsometry.spinCGroupMap hQ hQ

/-- The automorphism `σ` of `Spinᶜ(n)` defining `s.precompIsometry f` is continuous. -/
theorem continuous_precompIsometryHom
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0)) :
    Continuous (precompIsometryHom f) :=
  f.symm.toIsometry.continuous_spinCGroupMap hQ hQ

/-- The rotation of `[f⁻¹ g, z]` is `f⁻¹ π(g) f`: applying `π(g)` after `f` is applying `f` after
the rotation of `[f⁻¹ g, z]`. -/
theorem toSpecialOrthogonal_precompIsometryHom_apply
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (g : spinCGroup (realCliffordForm n 0) hQ) (v : Fin n → ℝ) :
    (spinCGroup.toSpecialOrthogonal _ hQ g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (f v) =
      f ((spinCGroup.toSpecialOrthogonal _ hQ (precompIsometryHom f g) :
        (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) v) := by
  have h := f.symm.toIsometry.toSpecialOrthogonal_spinCGroupMap_apply hQ hQ g (f v)
  simp only [QuadraticMap.IsometryEquiv.toIsometry_apply,
    QuadraticMap.IsometryEquiv.symm_apply_apply] at h
  rw [h, QuadraticMap.IsometryEquiv.apply_symm_apply]

/-- **Frames precomposed with `f` are compatible with `σ`**: on `EuclideanSpace ℝ (Fin n)`,
applying `π(g)` after `f` is applying `f` after the rotation of `σ(g)`. This is the compatibility
hypothesis of `TauCeti.OrthonormalFrameLift.precomp` for `r = f` and `ρ' = π ∘ σ`. -/
theorem toSpecialOrthogonal_realCliffordIsometryEquivEuclidean_apply
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (g : spinCGroup (realCliffordForm n 0) hQ) (v : Fin n → ℝ) :
    (spinCGroup.toSpecialOrthogonal _ hQ g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
        (realCliffordIsometryEquivEuclidean f (WithLp.toLp 2 v)).ofLp =
      (realCliffordIsometryEquivEuclidean f (WithLp.toLp 2
        ((spinCGroup.toSpecialOrthogonal _ hQ (precompIsometryHom f g) :
          (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) v))).ofLp := by
  simpa using toSpecialOrthogonal_precompIsometryHom_apply f g v

/-- The automorphism of `Spinᶜ(n)` induced by the identity of `ℝⁿ` is the identity. -/
@[simp]
theorem precompIsometryHom_refl :
    precompIsometryHom (QuadraticMap.IsometryEquiv.refl (realCliffordForm n 0)) =
      MonoidHom.id _ :=
  QuadraticMap.Isometry.spinCGroupMap_id hQ

/-- The automorphism of `Spinᶜ(n)` induced by the identity of `ℝⁿ` fixes every element. (Not
`@[simp]`: `simp` proves it from `TauCeti.SpinCStructure.precompIsometryHom_refl`.) -/
theorem precompIsometryHom_refl_apply (h : spinCGroup (realCliffordForm n 0) hQ) :
    precompIsometryHom (QuadraticMap.IsometryEquiv.refl (realCliffordForm n 0)) h = h :=
  DFunLike.congr_fun precompIsometryHom_refl h

/-- The automorphisms of `Spinᶜ(n)` induced by isometries `f` and `g` of `ℝⁿ` compose to the one
induced by `f ∘ g`: `σ_g ∘ σ_f = σ_{f ∘ g}`. (Not `@[simp]`: `precompIsometryHom` is reducible,
so `QuadraticMap.Isometry.spinCGroupMap_comp` already rewrites its left-hand side.) -/
theorem precompIsometryHom_comp
    (f g : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0)) :
    (precompIsometryHom g).comp (precompIsometryHom f) = precompIsometryHom (g.trans f) :=
  QuadraticMap.Isometry.spinCGroupMap_comp _ hQ hQ _ hQ

/-- Pointwise form of `TauCeti.SpinCStructure.precompIsometryHom_comp`:
`σ_g (σ_f h) = σ_{f ∘ g} h`. -/
@[simp]
theorem precompIsometryHom_comp_apply
    (f g : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (h : spinCGroup (realCliffordForm n 0) hQ) :
    precompIsometryHom g (precompIsometryHom f h) = precompIsometryHom (g.trans f) h :=
  DFunLike.congr_fun (precompIsometryHom_comp f g) h

/-- The lift along `ρ ∘ σ`, for the rotation homomorphism `ρ` of `Spinᶜ(n)` and
`σ = TauCeti.SpinCStructure.precompIsometryHom f`, with the principal bundle of a `Spinᶜ`
structure `s` and its frames precomposed with `f` (`TauCeti.OrthonormalFrameLift.precomp`); its
extension along `σ` is `s.precompIsometry f`. -/
noncomputable abbrev precompIsometryLift
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (s : SpinCStructure F V n) :
    OrthonormalFrameLift F V n (spinCGroup (realCliffordForm n 0) hQ)
      (((QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)).subtype.comp
        (spinCGroup.toSpecialOrthogonal (realCliffordForm n 0) _)).comp (precompIsometryHom f)) :=
  s.precomp (realCliffordIsometryEquivEuclidean f) _
    (toSpecialOrthogonal_realCliffordIsometryEquivEuclidean_apply f)

/-- The **precomposition of a `Spinᶜ` structure** `s` with an isometry `f` of `ℝⁿ`: the `Spinᶜ`
structure whose principal bundle is `P ×_σ Spinᶜ(n)`, for the automorphism
`σ : [g, z] ↦ [f⁻¹ g, z]` of `Spinᶜ(n)` (`TauCeti.SpinCStructure.precompIsometryHom`), and in
which the frame of `[p, 1]` is the frame of `p` precomposed with `f`
(`TauCeti.SpinCStructure.toFrame_precompIsometry_inl`). When `f` reverses orientation, it is a
`Spinᶜ` structure for the opposite orientation of the bundle. Its body is exposed so that the fibre
`(s.precompIsometry f).P x` unfolds to `P ×_σ Spinᶜ(n)` downstream. -/
@[expose]
noncomputable def precompIsometry
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (s : SpinCStructure F V n) : SpinCStructure F V n :=
  (s.precompIsometryLift f).extendSpinC (precompIsometryHom f) (continuous_precompIsometryHom f)
    rfl

/-- **The frame of `[p, 1]`** in the precomposition of a `Spinᶜ` structure with `f` is the frame
of `p` precomposed with `f`. -/
@[simp]
theorem toFrame_precompIsometry_inl
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0)) (s : SpinCStructure F V n)
    (x : X) (p : s.P x) :
    (s.precompIsometry f).toFrame ⟨x, PrincipalBundle.Extend.inl (precompIsometryHom f)
        (continuous_precompIsometryHom f) p⟩ =
      ⟨(s.toFrame ⟨x, p⟩).proj, (realCliffordIsometryEquivEuclidean f).trans
        (s.toFrame ⟨x, p⟩).frame⟩ := by
  unfold precompIsometry
  exact (toFrame_extendSpinC_inl (s.precompIsometryLift f) _ _ _ x p).trans
    (toFrame_precomp _ _ _ _ _)

/-- The precomposition of a `Spinᶜ` structure with `f` transports a model orientation `o` of
`EuclideanSpace ℝ (Fin n)`, along the frame of `[p, 1]`, to the orientation that the frame of
`p` transports `f o` to. -/
theorem toOrientationCover_toFrame_precompIsometry_inl
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0)) (s : SpinCStructure F V n)
    {ι : Type*} (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) ι) (x : X) (p : s.P x) :
    OrthonormalFrameBundle.toOrientationCover o ((s.precompIsometry f).toFrame ⟨x,
        PrincipalBundle.Extend.inl (precompIsometryHom f)
          (continuous_precompIsometryHom f) p⟩) =
      OrthonormalFrameBundle.toOrientationCover
        (Orientation.map ι (realCliffordIsometryEquivEuclidean f).toLinearEquiv o)
        (s.toFrame ⟨x, p⟩) := by
  rw [toFrame_precompIsometry_inl, OrthonormalFrameBundle.toOrientationCover_eq_mk,
    OrthonormalFrameBundle.toOrientationCover_eq_mk, LinearIsometryEquiv.toLinearEquiv_trans,
    Orientation.map_trans]

/-- **Precomposition with an orientation-reversing isometry reverses orientation**: if
`det f < 0`, the precomposition of a `Spinᶜ` structure with `f` transports a model orientation
`o` of `EuclideanSpace ℝ (Fin n)`, along the frame of `[p, 1]`, to the orientation that the frame
of `p` transports `-o` to. -/
theorem toOrientationCover_toFrame_precompIsometry_inl_of_det_neg
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (hf : LinearMap.det (f.toLinearEquiv : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) < 0)
    (s : SpinCStructure F V n) {ι : Type*} [Fintype ι] (hι : Fintype.card ι = n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) ι) (x : X) (p : s.P x) :
    OrthonormalFrameBundle.toOrientationCover o ((s.precompIsometry f).toFrame ⟨x,
        PrincipalBundle.Extend.inl (precompIsometryHom f)
          (continuous_precompIsometryHom f) p⟩) =
      OrthonormalFrameBundle.toOrientationCover (-o) (s.toFrame ⟨x, p⟩) := by
  rw [toOrientationCover_toFrame_precompIsometry_inl, (Orientation.map_eq_neg_iff_det_neg o _
    (by simp [finrank_euclideanSpace, hι])).2 (by rwa [det_realCliffordIsometryEquivEuclidean])]

/-- The **orientation reversal** of a `Spinᶜ` structure: its precomposition with the reflection
of `ℝⁿ` in the first coordinate hyperplane. The frame of `[p, 1]` is the frame of `p` with its first
vector negated, and the structure is a `Spinᶜ` structure for the opposite orientation of the
bundle (`TauCeti.SpinCStructure.toOrientationCover_toFrame_reverse_inl`). -/
noncomputable abbrev reverse (s : SpinCStructure F V n) : SpinCStructure F V n :=
  s.precompIsometry (realCliffordCoordReflection 0)

/-- **The orientation reversal reverses orientation**: it transports a model orientation `o` of
`EuclideanSpace ℝ (Fin n)`, along the frame of `[p, 1]`, to the orientation that the frame of `p`
transports `-o` to. -/
theorem toOrientationCover_toFrame_reverse_inl (s : SpinCStructure F V n) {ι : Type*}
    [Fintype ι] (hι : Fintype.card ι = n) (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) ι) (x : X)
    (p : s.P x) :
    OrthonormalFrameBundle.toOrientationCover o (s.reverse.toFrame ⟨x,
        PrincipalBundle.Extend.inl (precompIsometryHom (realCliffordCoordReflection 0))
          (continuous_precompIsometryHom (realCliffordCoordReflection 0)) p⟩) =
      OrthonormalFrameBundle.toOrientationCover (-o) (s.toFrame ⟨x, p⟩) :=
  toOrientationCover_toFrame_precompIsometry_inl_of_det_neg _
    (by rw [det_realCliffordCoordReflection]; norm_num) s hι o x p

end SpinCStructure

end TauCeti
