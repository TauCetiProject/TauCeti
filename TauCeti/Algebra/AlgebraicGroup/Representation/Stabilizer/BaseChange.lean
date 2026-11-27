/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.BaseChange
public import TauCeti.LinearAlgebra.TensorProduct.Tower

/-!
# Stabilizers under corestriction and base change

Let `W` be a subspace of a representation `M` of an affine group `G = Spec H` over a field `k`.
The points of `G` in the stabilizer of `W` are detected by their action on `W`
(`Submodule.stabilizerHopfIdeal_le_ker_iff`). This file transports that criterion along the two
standard operations on representations.

* **Restriction along a homomorphism.** A homomorphism `G' → G`, with coordinate morphism
  `φ : H → H'`, makes `M` a representation of `G'` by corestriction along `φ`. A point of `G'`
  lies in the stabilizer of `W` for this representation exactly when its image in `G` lies in the
  stabilizer of `W`.
* **Extension of scalars.** For an extension `K / k`, a point of `G_K` lies in the stabilizer of
  `W_K ≤ K ⊗[k] M` exactly when the corresponding point of `G` lies in the stabilizer of `W`.

Evaluating at the universal point, represented by the identity map of the coordinate algebra,
gives the special cases about whole stabilizers: `W` is a subrepresentation of the restriction
exactly when the image of `G'` stabilizes `W`, and `W_K` is a subrepresentation of `K ⊗[k] M`
exactly when `W` is a subrepresentation of `M`.

## Main declarations

* `Submodule.stabilizerHopfIdeal_corestrict_le_ker_iff`: the stabilizer under restriction along a
  homomorphism.
* `Submodule.stabilizerHopfIdeal_corestrict_eq_bot_iff`: `W` is a subrepresentation of the
  restriction exactly when the image of the homomorphism stabilizes `W`.
* `Submodule.stabilizerHopfIdeal_baseChange_le_ker_iff`: the stabilizer under extension of
  scalars.
* `Submodule.stabilizerHopfIdeal_baseChange_eq_bot_iff`: `W_K` is a subrepresentation exactly when
  `W` is.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 4 and 10.
-/

public section

open scoped TensorProduct
open TauCeti

namespace Submodule

section Corestrict

variable {k H₁ H₂ M : Type*} [Field k] [CommRing H₁] [HopfAlgebra k H₁] [CommRing H₂]
  [HopfAlgebra k H₂] [AddCommGroup M] [Module k M] [Comodule k H₁ M]

/-- **The stabilizer under restriction along a homomorphism.** Let `φ : H₁ → H₂` be the coordinate
morphism of a homomorphism `G₂ → G₁`, and regard the representation `M` of `G₁` as a
representation of `G₂` by corestriction. A point `g` of `G₂` stabilizes `W` exactly when its image
`g ∘ φ` in `G₁` does. -/
theorem stabilizerHopfIdeal_corestrict_le_ker_iff (W : Submodule k M) (φ : H₁ →ₐc[k] H₂)
    {A : Type*} [CommRing A] [Algebra k A] (g : H₂ →ₐ[k] A) :
    (letI : Comodule k H₂ M := Comodule.Corestrict φ.toCoalgHom;
      (W.stabilizerHopfIdeal H₂).toIdeal ≤ RingHom.ker g) ↔
      (W.stabilizerHopfIdeal H₁).toIdeal ≤ RingHom.ker (g.comp (φ : H₁ →ₐ[k] H₂)) := by
  let _ : Comodule k H₂ M := Comodule.Corestrict φ.toCoalgHom
  have h₂ := W.stabilizerHopfIdeal_le_ker_iff (H := H₂) (WithConv.toConv g)
  have h₁ := W.stabilizerHopfIdeal_le_ker_iff (H := H₁) (WithConv.toConv (g.comp φ))
  rw [WithConv.ofConv_toConv] at h₁ h₂
  rw [h₂, h₁, Comodule.endOfPoint_corestrict]

/-- **Subrepresentations of a restriction.** `W` is a subrepresentation of `M` regarded as a
representation of `G₂` through `φ` exactly when the image of `G₂` stabilizes `W`:
`φ` kills the defining Hopf ideal of the stabilizer of `W` in `G₁`. -/
theorem stabilizerHopfIdeal_corestrict_eq_bot_iff (W : Submodule k M) (φ : H₁ →ₐc[k] H₂) :
    (letI : Comodule k H₂ M := Comodule.Corestrict φ.toCoalgHom;
      W.stabilizerHopfIdeal H₂ = ⊥) ↔
      (W.stabilizerHopfIdeal H₁).toIdeal ≤ RingHom.ker (φ : H₁ →ₐ[k] H₂) := by
  let _ : Comodule k H₂ M := Comodule.Corestrict φ.toCoalgHom
  have h := stabilizerHopfIdeal_corestrict_le_ker_iff W φ (AlgHom.id k H₂)
  rw [AlgHom.id_comp] at h
  rw [← h, HopfIdeal.toIdeal_le_ker_iff_of_injective (f := AlgHom.id k H₂)
    (AlgHom.coe_id k H₂ ▸ Function.injective_id)]

end Corestrict

section BaseChange

variable {k K H M : Type*} [Field k] [Field K] [Algebra k K] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M]

/-- **The stabilizer under extension of scalars.** For an extension `K / k`, a point `f` of
`G_K = Spec (K ⊗[k] H)` stabilizes `W_K ≤ K ⊗[k] M` exactly when the corresponding point
`h ↦ f (1 ⊗ h)` of `G` stabilizes `W`. -/
theorem stabilizerHopfIdeal_baseChange_le_ker_iff (W : Submodule k M) {A : Type*} [CommRing A]
    [Algebra k A] [Algebra K A] [IsScalarTower k K A] (f : K ⊗[k] H →ₐ[K] A) :
    (letI := Comodule.baseChange (R := k) (H := H) (M := M) K;
      ((W.baseChange K).stabilizerHopfIdeal (K ⊗[k] H)).toIdeal ≤ RingHom.ker f) ↔
      (W.stabilizerHopfIdeal H).toIdeal ≤
        RingHom.ker ((f.restrictScalars k).comp Algebra.TensorProduct.includeRight) := by
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  set f' : H →ₐ[k] A := (f.restrictScalars k).comp Algebra.TensorProduct.includeRight
  have hf : AlgHom.liftEquiv k K H A f' = f := (AlgHom.liftEquiv k K H A).apply_symm_apply f
  have h₂ := (W.baseChange K).stabilizerHopfIdeal_le_ker_iff (H := K ⊗[k] H)
    (WithConv.toConv f)
  have h₁ := W.stabilizerHopfIdeal_le_ker_iff (H := H) (WithConv.toConv f')
  rw [WithConv.ofConv_toConv] at h₁ h₂
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange k K A A M
  have hcomm : e.toLinearMap ∘ₗ Comodule.endOfPoint (K ⊗[k] M) f =
      Comodule.endOfPoint M f' ∘ₗ e.toLinearMap := by
    refine LinearMap.ext fun y ↦ ?_
    simpa [hf] using Comodule.cancelBaseChange_endOfPoint_liftEquiv (K := K) (R := A) f' y
  rw [h₂, h₁, ← map_cancelBaseChange_baseChange_baseChange (K := K) W A, ← map_comp, ← hcomm,
    map_comp]
  exact (map_injective_of_injective e.injective).eq_iff.symm

/-- **Subrepresentations under extension of scalars.** For an extension `K / k`, `W_K` is a
subrepresentation of `K ⊗[k] M` exactly when `W` is a subrepresentation of `M`. -/
theorem stabilizerHopfIdeal_baseChange_eq_bot_iff (W : Submodule k M) :
    (letI := Comodule.baseChange (R := k) (H := H) (M := M) K;
      (W.baseChange K).stabilizerHopfIdeal (K ⊗[k] H) = ⊥) ↔ W.stabilizerHopfIdeal H = ⊥ := by
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  have h := stabilizerHopfIdeal_baseChange_le_ker_iff (K := K) W (AlgHom.id K (K ⊗[k] H))
  have hinj : Function.Injective
      (((AlgHom.id K (K ⊗[k] H)).restrictScalars k).comp Algebra.TensorProduct.includeRight) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  rwa [HopfIdeal.toIdeal_le_ker_iff_of_injective (f := AlgHom.id K (K ⊗[k] H))
      (AlgHom.coe_id K (K ⊗[k] H) ▸ Function.injective_id),
    HopfIdeal.toIdeal_le_ker_iff_of_injective hinj] at h

end BaseChange

end Submodule
