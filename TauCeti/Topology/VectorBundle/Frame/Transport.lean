/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Contractible
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Transport
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Linear transport along a frame

A vector bundle `E → B` carries no canonical linear isomorphism between two of its fibres: only
orientations can be transported canonically along a path, by lifting it to the orientation double
cover (`TauCeti.VectorBundleOrientationCover.orientationTransport`). Linear transport needs a
choice. This file makes that choice a **frame along a map** `f : X → B`, a family of linear
isomorphisms `φ x : F ≃ E (f x)` from the model fibre whose values depend continuously on `x` in
the total space, and records how the resulting transport depends on it.

The **frame transport** from `s` to `t` is `φ t ∘ (φ s)⁻¹ : E (f s) ≃ E (f t)`
(`TauCeti.frameTransport`). It is the identity from `s` to `s`, reversing the direction inverts it,
and transports compose (`TauCeti.frameTransport_self`, `TauCeti.frameTransport_symm`,
`TauCeti.frameTransport_trans`). Frames exist along every continuous map from a contractible
paracompact space, in particular along every path (`TauCeti.exists_continuous_frame`).

**Change of frame.** Two frames `φ` and `ψ` along `f` differ by automorphisms
`A x = (φ x)⁻¹ ∘ ψ x` of `F`, which depend continuously on `x` when `F` is finite-dimensional
(`TauCeti.continuous_trans_symm_of_continuous_frame`). The transport of `ψ` is the transport of
`φ` twisted by them, `φ t ∘ A t ∘ (A s)⁻¹ ∘ (φ s)⁻¹`
(`TauCeti.frameTransport_eq_of_forall_eq_trans`), so it is unchanged by a constant change of frame
(`TauCeti.frameTransport_eq_of_forall_eq_trans_const`) but in general depends on the frame. Over
the reals and a preconnected parameter space the determinants of the `A x` all have one sign
(`TauCeti.det_mul_det_pos_of_continuous_frame`). For a line bundle the `A x` are scalars, so the
transports of any two frames differ by a positive scalar
(`TauCeti.exists_pos_forall_frameTransport_eq_smul`): this is the change-of-choice law of linear
transport, and it is why only the orientation of the transport is independent of the choice.

**Orientations.** Frame transport along a path induces orientation transport: for every
continuous frame `φ` along a path `γ` of the base, the orientation transport along `γ` sends an
orientation `o` of `E (γ 0)` to its image under the linear isomorphism `φ 1 ∘ (φ 0)⁻¹`
(`TauCeti.orientationTransport_eq_map_frameTransport`). The frame turns each basis of `F` into a
continuously varying basis of the fibres along `γ`, whose orientations form a lift of `γ` to the
orientation double cover.

For instance, the determinant lines of a continuous path of real Fredholm operators form a line
bundle (`TauCeti.FredholmDetLine.vectorBundle`), so a frame of it along the path gives a linear
isomorphism between the determinant lines at the ends. That isomorphism is determined by the frame
only up to a positive scalar, and it carries orientations as orientation transport does.

## Main definitions

* `TauCeti.frameTransport`: the linear transport between the fibres along a frame.

## Main results

* `TauCeti.frameTransport_eq_of_forall_eq_trans`: the change-of-frame law.
* `TauCeti.det_mul_det_pos_of_continuous_frame`: two continuous frames along a map from a
  preconnected space differ by automorphisms whose determinants have one sign.
* `TauCeti.exists_pos_forall_frameTransport_eq_smul`: in a line bundle, the transports of two
  continuous frames differ by a positive scalar.
* `TauCeti.orientationTransport_eq_map_frameTransport`: frame transport along a path induces
  orientation transport.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (orientations of determinant line bundles).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton, 1974, §12 (orientations of vector bundles).
-/

public section

noncomputable section

open Bundle Module Set
open scoped unitInterval

namespace TauCeti

section Transport

variable {𝕜 : Type*} [Semiring 𝕜] {X B : Type*}
  {F : Type*} [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)]
  {f : X → B}

/-- The **linear transport along a frame**: for linear isomorphisms `φ x : F ≃ E (f x)` from the
model fibre to the fibres along `f`, the isomorphism `φ t ∘ (φ s)⁻¹` from the fibre over `f s` to
the fibre over `f t`. It depends on the frame, not only on `f`. -/
def frameTransport (φ : ∀ x, F ≃L[𝕜] E (f x)) (s t : X) : E (f s) ≃L[𝕜] E (f t) :=
  (φ s).symm.trans (φ t)

variable (φ ψ : ∀ x, F ≃L[𝕜] E (f x)) (r s t : X)

@[simp]
theorem frameTransport_apply (v : E (f s)) : frameTransport φ s t v = φ t ((φ s).symm v) :=
  (rfl)

@[simp]
theorem frameTransport_self : frameTransport φ s s = ContinuousLinearEquiv.refl 𝕜 (E (f s)) := by
  ext v
  simp

@[simp]
theorem frameTransport_symm : (frameTransport φ s t).symm = frameTransport φ t s :=
  (rfl)

@[simp]
theorem frameTransport_trans :
    (frameTransport φ r s).trans (frameTransport φ s t) = frameTransport φ r t := by
  ext v
  simp

/-- **Change of frame.** If `ψ x = φ x ∘ A x` for automorphisms `A x` of the model fibre, the
transport of `ψ` from `s` to `t` is the transport of `φ` twisted by the change of frame,
`φ t ∘ A t ∘ (A s)⁻¹ ∘ (φ s)⁻¹`. -/
theorem frameTransport_eq_of_forall_eq_trans {A : X → F ≃L[𝕜] F}
    (hA : ∀ x, ψ x = (A x).trans (φ x)) :
    frameTransport ψ s t = (φ s).symm.trans (((A s).symm.trans (A t)).trans (φ t)) := by
  ext v
  simp [hA]

/-- **Constant changes of frame.** Frames that differ by one fixed automorphism of the model fibre
have the same transport. -/
theorem frameTransport_eq_of_forall_eq_trans_const {A : F ≃L[𝕜] F}
    (hA : ∀ x, ψ x = A.trans (φ x)) : frameTransport ψ s t = frameTransport φ s t := by
  ext v
  simp [frameTransport_eq_of_forall_eq_trans φ ψ s t (A := fun _ ↦ A) hA]

end Transport

section Real

variable {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  {f : X → B} {φ ψ : ∀ x, F ≃L[ℝ] E (f x)}

/-- **Changes of frame have determinants of one sign.** Two continuous frames `φ` and `ψ` along a
map from a preconnected space differ by the automorphisms `(φ x)⁻¹ ∘ ψ x` of the model fibre, and
the determinants of these automorphisms at any two points have the same sign. -/
theorem det_mul_det_pos_of_continuous_frame [PreconnectedSpace X]
    (hφ : Continuous fun q : X × F ↦ TotalSpace.mk' F (f q.1) (φ q.1 q.2))
    (hψ : Continuous fun q : X × F ↦ TotalSpace.mk' F (f q.1) (ψ q.1 q.2)) (s t : X) :
    0 < (((ψ s).trans (φ s).symm : F ≃L[ℝ] F) : F →L[ℝ] F).det *
      (((ψ t).trans (φ t).symm : F ≃L[ℝ] F) : F →L[ℝ] F).det := by
  set d : X → ℝ := fun x ↦ (((ψ x).trans (φ x).symm : F ≃L[ℝ] F) : F →L[ℝ] F).det
  have hd : Continuous d :=
    ContinuousLinearMap.continuous_det.comp (continuous_trans_symm_of_continuous_frame hψ hφ)
  have hne (x : X) : d x ≠ 0 := (((ψ x).trans (φ x).symm).toLinearEquiv.isUnit_det').ne_zero
  have h := isPreconnected_univ.sign_eq_of_continuousOn hd.continuousOn (fun x _ ↦ hne x)
    (mem_univ s) (mem_univ t)
  rcases (hne s).lt_or_gt with hs | hs
  · exact mul_pos_of_neg_of_neg hs (sign_eq_neg_one_iff.1 (h ▸ sign_neg hs))
  · exact mul_pos hs (sign_eq_one_iff.1 (h ▸ sign_pos hs))

/-- **Change of frame in a line bundle.** In a vector bundle of rank one, the linear transports of
two continuous frames along a map from a preconnected space differ by a positive scalar. So the
transport is not determined by the map alone, but its orientation is. -/
theorem exists_pos_forall_frameTransport_eq_smul [PreconnectedSpace X] (hF : finrank ℝ F = 1)
    (hφ : Continuous fun q : X × F ↦ TotalSpace.mk' F (f q.1) (φ q.1 q.2))
    (hψ : Continuous fun q : X × F ↦ TotalSpace.mk' F (f q.1) (ψ q.1 q.2)) (s t : X) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, frameTransport ψ s t v = c • frameTransport φ s t v := by
  set A : X → F ≃L[ℝ] F := fun x ↦ (ψ x).trans (φ x).symm
  set d : X → ℝ := fun x ↦ ((A x : F ≃L[ℝ] F) : F →L[ℝ] F).det
  -- In rank one every endomorphism is multiplication by its determinant.
  have hA (x : X) (v : F) : A x v = d x • v :=
    LinearMap.apply_eq_det_smul_of_finrank_eq_one hF ((A x : F →L[ℝ] F) : F →ₗ[ℝ] F) v
  have hψφ (x : X) (v : F) : ψ x v = d x • φ x v := by
    rw [← map_smul, ← hA]
    simp [A]
  have hpos := det_mul_det_pos_of_continuous_frame hφ hψ s t
  have hds : d s ≠ 0 := left_ne_zero_of_mul hpos.ne'
  refine ⟨d t / d s, ?_, fun v ↦ ?_⟩
  · exact div_pos_iff.2 ((mul_pos_iff.1 hpos).imp And.symm And.symm)
  · have hsymm : (ψ s).symm v = (d s)⁻¹ • (φ s).symm v := by
      rw [ContinuousLinearEquiv.symm_apply_eq]
      simp [hψφ, smul_smul, hds]
    simp [hsymm, hψφ, smul_smul, div_eq_mul_inv]

/-- **Frame transport induces orientation transport.** Let `φ` be a continuous frame along a path
`γ` of the base. Orientation transport along `γ`, the monodromy of the orientation double cover,
sends each orientation `o` of the fibre over `γ 0` to its image under the linear isomorphism
`φ 1 ∘ (φ 0)⁻¹` between the fibres at the ends. -/
theorem orientationTransport_eq_map_frameTransport {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = finrank ℝ F) (γ : C(I, B)) {φ : ∀ t : I, F ≃L[ℝ] E (γ t)}
    (hφ : Continuous fun q : I × F ↦ TotalSpace.mk' F (γ q.1) (φ q.1 q.2))
    (o : Orientation ℝ (E (γ 0)) ι) :
    VectorBundleOrientationCover.orientationTransport E hι ⟨γ, rfl, rfl⟩ o =
      Orientation.map ι (frameTransport φ 0 1).toLinearEquiv o := by
  classical
  -- A basis `b` of the model fibre, carried along `γ` by the frame.
  let b : Basis ι ℝ F :=
    (Module.finBasisOfFinrankEq ℝ F hι.symm).reindex (Fintype.equivFin ι).symm
  let v (t : I) : Basis ι ℝ (E (γ t)) := b.map (φ t).toLinearEquiv
  -- Its orientations form a lift of `γ` to the orientation double cover.
  have key : VectorBundleOrientationCover.orientationTransport E hι ⟨γ, rfl, rfl⟩
      (v 0).orientation = (v 1).orientation := by
    let Γ : C(I, VectorBundleOrientationCover F E ι) :=
      ⟨fun t ↦ ⟨γ t, (v t).orientation⟩,
        VectorBundleOrientationCover.continuous_mk_basis_orientation γ.continuous v fun i ↦
          (hφ.comp (continuous_id.prodMk (continuous_const (y := b i)))).congr fun t ↦ by simp [v]⟩
    have h := VectorBundleOrientationCover.orientationTransport_eq_of_lift hι ⟨γ, rfl, rfl⟩ Γ
      (funext fun _ ↦ rfl) rfl rfl
    simpa [Γ] using h
  -- The transport carries the frame basis at `0` to the frame basis at `1`.
  have hmap : Orientation.map ι (frameTransport φ 0 1).toLinearEquiv (v 0).orientation =
      (v 1).orientation := by
    rw [← Basis.orientation_map]
    congr 1
    exact Basis.eq_of_apply_eq fun i ↦ by simp [v]
  have : Module.Finite ℝ (E (γ 0)) := Module.Finite.equiv (φ 0).toLinearEquiv
  rcases Orientation.eq_or_eq_neg o (v 0).orientation
      ((Nat.card_eq_fintype_card.trans hι).trans (φ 0).toLinearEquiv.finrank_eq) with rfl | rfl
  · rw [key, hmap]
  · rw [VectorBundleOrientationCover.orientationTransport_neg, key, Orientation.map_neg, hmap]

end Real

end TauCeti
