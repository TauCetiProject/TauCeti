/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Pullback
public import TauCeti.Topology.VectorBundle.SpinStructure.Reflection.Basic

/-!
# Orientation reversal of `Spinᶜ` structures commutes with pullback

For a `Spinᶜ` structure `s` on a real vector bundle `V → X` with fibre inner products, a continuous
map `g : Y → X` and an orthogonal transformation `f` of `ℝⁿ`, precomposing with `f` commutes with
pulling back along `g`: `(g^* s).precompIsometry f ≃ g^* (s.precompIsometry f)`
(`TauCeti.SpinCStructure.precompIsometryPullbackEquiv`). Both principal bundles are, over `y ∈ Y`,
the extension `P_{g y} ×_σ Spinᶜ(n)`; the equivalence is the identity `[p, h] ↦ [p, h]`,
obtained from the universal property of the extension
(`TauCeti.OrthonormalFrameLift.extendSpinCEquivOfEquivariant`) applied to `p ↦ [p, 1]`, which
preserves frames (`TauCeti.SpinCStructure.toFrame_pullback_precompIsometry_inl`). In particular
orientation reversal commutes with pullback (`TauCeti.SpinCStructure.reversePullbackEquiv`).

## Main definitions

* `TauCeti.SpinCStructure.precompIsometryPullbackEquiv`:
  `(g^* s).precompIsometry f ≃ g^* (s.precompIsometry f)`.
* `TauCeti.SpinCStructure.reversePullbackEquiv`: `(g^* s).reverse ≃ g^* s.reverse`.

## Main results

* `TauCeti.SpinCStructure.toFrame_pullback_precompIsometry_inl`: the frame of `[p, 1]` in
  `g^* (s.precompIsometry f)` is the frame of `p` in `g^* s` precomposed with `f`.
* `TauCeti.SpinCStructure.precompIsometryPullbackEquiv_toEquiv_mk`,
  `TauCeti.SpinCStructure.reversePullbackEquiv_toEquiv_mk`: the equivalences send `[p, h]` to
  `[p, h]`, and in particular (`_toEquiv_inl`) `[p, 1]` to `[p, 1]`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

noncomputable section

open Bundle MulOpposite CliffordAlgebra TauCeti.PrincipalBundle

namespace TauCeti

namespace SpinCStructure

open OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ} [NeZero n]
  {Y : Type*} [TopologicalSpace Y] {K : Type*} [FunLike K Y X] [ContinuousMapClass K Y X]

/-- **The frame of `[p, 1]`** in the pullback of the precomposition of a `Spinᶜ` structure `s`
with `f` is the frame of `p` in the pullback of `s`, precomposed with `f`. -/
theorem toFrame_pullback_precompIsometry_inl (g : K)
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (s : SpinCStructure F V n) (y : Y) (p : s.P (g y)) :
    ((s.precompIsometry f).pullback g).toFrame
        ⟨y, Extend.inl (precompIsometryHom f) (continuous_precompIsometryHom f) p⟩ =
      (precompIsometryLift f (s.pullback g)).toFrame ⟨y, p⟩ := by
  obtain ⟨φ, hφ⟩ := s.exists_toFrame_eq_mk ⟨g y, p⟩
  have hs : (s.pullback g).toFrame ⟨y, p⟩ = ⟨y, φ⟩ := s.toFrame_pullback_mk g y p hφ
  have ht : (s.precompIsometry f).toFrame ⟨g y, Extend.inl (precompIsometryHom f)
      (continuous_precompIsometryHom f) p⟩ =
        ⟨g y, (realCliffordIsometryEquivEuclidean f).trans φ⟩ :=
    (toFrame_precompIsometry_inl f s (g y) p).trans (by rw [hφ])
  rw [(s.precompIsometry f).toFrame_pullback_mk g y _ ht]
  -- `rw [hs]` does not see `hs` in the frame given by `toFrame_precomp`, whose fibre
  -- instances are unfolded differently, so `hs` is transported along the precomposition.
  exact ((toFrame_precomp _ _ _ _ _).trans (congrArg
    (fun q : OrthonormalFrameBundle ℝ F ((g : Y → X) *ᵖ V) (EuclideanSpace ℝ (Fin n)) ↦
      (⟨q.proj, (realCliffordIsometryEquivEuclidean f).trans q.frame⟩ :
        OrthonormalFrameBundle ℝ F ((g : Y → X) *ᵖ V) (EuclideanSpace ℝ (Fin n)))) hs)).symm

/-- **Precomposition commutes with pullback**: for a continuous map `g : Y → X`,
`(g^* s).precompIsometry f ≃ g^* (s.precompIsometry f)`. Over `y`, both principal bundles are
`P_{g y} ×_σ Spinᶜ(n)`, and the equivalence is `[p, h] ↦ [p, h]`. -/
def precompIsometryPullbackEquiv (g : K)
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (s : SpinCStructure F V n) :
    (SpinCStructure.precompIsometry f (s.pullback g)).Equiv ((s.precompIsometry f).pullback g) :=
  (precompIsometryLift f (s.pullback g)).extendSpinCEquivOfEquivariant (precompIsometryHom f)
    (continuous_precompIsometryHom f) rfl ((s.precompIsometry f).pullback g)
    (fun _ (p : s.P _) ↦ Extend.inl (precompIsometryHom f) (continuous_precompIsometryHom f) p)
    (fun _ (p : s.P _) h ↦ Extend.inl_smul _ _ p h)
    (Pullback.continuous_fiberwise
      (Extend.continuous_inl s.P (precompIsometryHom f) (continuous_precompIsometryHom f))
      (g : Y → X))
    (toFrame_pullback_precompIsometry_inl g f s)

/-- The equivalence `(g^* s).precompIsometry f ≃ g^* (s.precompIsometry f)` sends `[p, h]` to
`[p, h]`. -/
theorem precompIsometryPullbackEquiv_toEquiv_mk (g : K)
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (s : SpinCStructure F V n) (y : Y) (p : s.P (g y))
    (h : spinCGroup (realCliffordForm n 0)
      (QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0))) :
    (precompIsometryPullbackEquiv g f s).toEquiv y
        (Extend.mk (P := (g : Y → X) *ᵖ s.P) (precompIsometryHom f)
          (continuous_precompIsometryHom f) p h) =
      Extend.mk (P := s.P) (precompIsometryHom f) (continuous_precompIsometryHom f) p h := by
  unfold precompIsometryPullbackEquiv
  exact (extendSpinCEquivOfEquivariant_toEquiv_mk ..).trans (Extend.smul_inl _ _ p h)

/-- The equivalence `(g^* s).precompIsometry f ≃ g^* (s.precompIsometry f)` sends `[p, 1]` to
`[p, 1]`. -/
theorem precompIsometryPullbackEquiv_toEquiv_inl (g : K)
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (s : SpinCStructure F V n) (y : Y) (p : s.P (g y)) :
    (precompIsometryPullbackEquiv g f s).toEquiv y
        (Extend.inl (P := (g : Y → X) *ᵖ s.P) (precompIsometryHom f)
          (continuous_precompIsometryHom f) p) =
      Extend.inl (P := s.P) (precompIsometryHom f) (continuous_precompIsometryHom f) p := by
  unfold precompIsometryPullbackEquiv
  apply extendSpinCEquivOfEquivariant_toEquiv_inl

/-- **Orientation reversal commutes with pullback**: for a continuous map `g : Y → X`,
`(g^* s).reverse ≃ g^* s.reverse`. -/
def reversePullbackEquiv (g : K) (s : SpinCStructure F V n) :
    (SpinCStructure.reverse (s.pullback g)).Equiv (s.reverse.pullback g) :=
  precompIsometryPullbackEquiv g _ s

/-- The equivalence `(g^* s).reverse ≃ g^* s.reverse` sends `[p, h]` to `[p, h]`. -/
theorem reversePullbackEquiv_toEquiv_mk (g : K) (s : SpinCStructure F V n) (y : Y)
    (p : s.P (g y)) (h : spinCGroup (realCliffordForm n 0)
      (QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0))) :
    (reversePullbackEquiv g s).toEquiv y
        (Extend.mk (P := (g : Y → X) *ᵖ s.P) (precompIsometryHom (realCliffordCoordReflection 0))
          (continuous_precompIsometryHom _) p h) =
      Extend.mk (P := s.P) (precompIsometryHom (realCliffordCoordReflection 0))
        (continuous_precompIsometryHom _) p h :=
  precompIsometryPullbackEquiv_toEquiv_mk g _ s y p h

/-- The equivalence `(g^* s).reverse ≃ g^* s.reverse` sends `[p, 1]` to `[p, 1]`. -/
theorem reversePullbackEquiv_toEquiv_inl (g : K) (s : SpinCStructure F V n) (y : Y)
    (p : s.P (g y)) :
    (reversePullbackEquiv g s).toEquiv y
        (Extend.inl (P := (g : Y → X) *ᵖ s.P) (precompIsometryHom (realCliffordCoordReflection 0))
          (continuous_precompIsometryHom _) p) =
      Extend.inl (P := s.P) (precompIsometryHom (realCliffordCoordReflection 0))
        (continuous_precompIsometryHom _) p :=
  precompIsometryPullbackEquiv_toEquiv_inl g _ s y p

end SpinCStructure

end TauCeti
