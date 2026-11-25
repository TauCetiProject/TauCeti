/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Reduction
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Marked residual lifts

Let `A` be a local ring with residue field `k = k_A`, let `ρ` be a continuous representation of
`Γ` on an `A`-module `M`, and let `ρbar` be a continuous representation of `Γ` on a
`k`-vector space `V`. A *marking* is a `k`-linear equivalence `ι : k ⊗[A] M ≃ₗ[k] V`, and `ρ` is a
*lift of `ρbar` marked by `ι`* (`TauCeti.ContinuousRep.IsLiftOf ρ ρbar ι`) when `ι` intertwines
the raw reduction of `ρ` (the action of `ρ` extended to `k ⊗[A] M`, as in
`TauCeti.ContinuousRep.reduction`) with `ρbar`, in the sense of Mathlib's
`Representation.IsIntertwiningMap`. The marking is part of the data, and the raw reduction is used
without semisimplification.

Marked lifts compose with isomorphisms on both sides (`IsLiftOf.trans_iso`, `IsLiftOf.iso_trans`),
and a second marking `ι` followed by `s` marks the same lift exactly when `s` commutes with `ρbar`
(`IsLiftOf.trans_iff`). Marked lifts extend along local homomorphisms `A → B`, marked through the
identifications of `TauCeti.ContinuousRep.baseChangeTransIso` (`IsLiftOf.baseChange`).
When the reduction carries its module topology, a marked lift is the same as an isomorphism
`ρ.reduction ≅ ρbar` of continuous representations (`IsLiftOf.toIso`, `Iso.isLiftOf`, inverse to
each other by `Iso.toIso_isLiftOf` and `IsLiftOf.toLinearEquiv_toIso`). In frame form
(`isLiftOf_iff_toMatrix`): for a basis `b` of `M`, `ρ` is a lift of `ρbar` marked by `ι` if and
only if in the basis `ι (1 ⊗ b i)` of `V` the matrices of `ρbar` are the reductions of the
matrices of `ρ` in `b`. Two bases of `M` lifting the same marked residual basis differ by a
matrix reducing to `1`: this is the case `S = k_A` of `Module.Basis.toMatrix_map_algebraMap_eq_one`
in `TauCeti.LinearAlgebra.TensorProduct.Basis`, which holds for any commutative algebra `S` over
the coefficient ring.

## Main definitions

* `TauCeti.ContinuousRep.IsLiftOf`: `ρ` is a lift of `ρbar` marked by `ι`.
* `TauCeti.ContinuousRep.baseChangeMarking`: the marking of a scalar extension.

## Main results

* `TauCeti.ContinuousRep.isLiftOf_iff_tmul`: the lift condition on pure tensors `1 ⊗ m`.
* `TauCeti.ContinuousRep.IsLiftOf.trans_iff`: two markings of the same lift differ by an
  automorphism of `V` commuting with `ρbar`, and every such automorphism gives a second marking.
* `TauCeti.ContinuousRep.IsLiftOf.baseChange`: scalar extension along a local homomorphism.
* `TauCeti.ContinuousRep.IsLiftOf.toIso`, `TauCeti.ContinuousRep.Iso.isLiftOf`: marked lifts are
  isomorphisms between the reduction and `ρbar`.
* `TauCeti.ContinuousRep.isLiftOf_iff_toMatrix`: the frame description.

## References

* K. Ribet, *Galois representations attached to eigenforms with Nebentypus*, §2.
* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1.
-/

public section

open IsLocalRing
open scoped TensorProduct

namespace TauCeti.ContinuousRep

variable {Γ A M M' V W : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [IsLocalRing A]
  [AddCommGroup M] [Module A M] [TopologicalSpace M]
  [AddCommGroup M'] [Module A M'] [TopologicalSpace M']
  [AddCommGroup V] [Module (ResidueField A) V] [TopologicalSpace V]
  [AddCommGroup W] [Module (ResidueField A) W] [TopologicalSpace W]

/-- **Marked residual lift.** The continuous representation `ρ` over the local ring `A` is a lift
of the continuous representation `ρbar` over the residue field `k_A`, marked by the
`k_A`-linear equivalence `ι : k_A ⊗[A] M ≃ₗ V`, when `ι` intertwines the raw reduction of `ρ`,
the action `g ↦ k_A ⊗ ρ g` on `k_A ⊗[A] M`, with `ρbar`. -/
abbrev IsLiftOf (ρ : ContinuousRep Γ A M) (ρbar : ContinuousRep Γ (ResidueField A) V)
    (ι : ResidueField A ⊗[A] M ≃ₗ[ResidueField A] V) : Prop :=
  (ρ.toRepresentation.baseChange (ResidueField A)).IsIntertwiningMap ρbar.toRepresentation
    ι.toLinearMap

variable {ρ : ContinuousRep Γ A M} {ρ' : ContinuousRep Γ A M'}
  {ρbar : ContinuousRep Γ (ResidueField A) V} {σbar : ContinuousRep Γ (ResidueField A) W}
  {ι : ResidueField A ⊗[A] M ≃ₗ[ResidueField A] V}

/-- **The lift condition on pure tensors**: `ρ` is a lift of `ρbar` marked by `ι` exactly when
`ι (1 ⊗ ρ g m) = ρbar g (ι (1 ⊗ m))` for all `g` and `m`. -/
theorem isLiftOf_iff_tmul :
    IsLiftOf ρ ρbar ι ↔ ∀ (g : Γ) (m : M), ι (1 ⊗ₜ ρ g m) = ρbar g (ι (1 ⊗ₜ m)) := by
  refine ⟨fun h g m ↦ by simpa using h.isIntertwining g (1 ⊗ₜ m), fun h ↦ ⟨fun g x ↦ ?_⟩⟩
  induction x using TensorProduct.inductionOn with
  | tmul c m =>
    rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    simp [h]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (Γ) in
/-- The trivial representation on `M` is a lift of the trivial representation on `V`, for every
marking. -/
theorem isLiftOf_trivial (ι : ResidueField A ⊗[A] M ≃ₗ[ResidueField A] V) :
    IsLiftOf (trivial Γ A M) (trivial Γ (ResidueField A) V) ι :=
  isLiftOf_iff_tmul.2 fun _ _ ↦ by simp

/-- **Changing the marking of a lift.** If `ρ` lifts `ρbar` with the marking `ι`, then `ι`
followed by an automorphism `s` of `V` marks the same lift exactly when `s` commutes with every
`ρbar g`. -/
theorem IsLiftOf.trans_iff (h : IsLiftOf ρ ρbar ι) {s : V ≃ₗ[ResidueField A] V} :
    IsLiftOf ρ ρbar (ι.trans s) ↔
      ρbar.toRepresentation.IsIntertwiningMap ρbar.toRepresentation s.toLinearMap := by
  have h' := h.isIntertwining
  simp only [Representation.baseChange_apply, coe_toRepresentation, LinearEquiv.coe_coe] at h'
  refine ⟨fun hs ↦ ⟨fun g v ↦ ?_⟩, fun hs ↦ ⟨fun g x ↦ ?_⟩⟩
  · obtain ⟨x, rfl⟩ := ι.surjective v
    simpa [h'] using hs.isIntertwining g x
  · simpa [h'] using hs.isIntertwining g (ι x)

/-- **Composition with an isomorphism of residual representations.** -/
theorem IsLiftOf.trans_iso (h : IsLiftOf ρ ρbar ι) (e : Iso ρbar σbar) :
    IsLiftOf ρ σbar (ι.trans e.toContinuousLinearEquiv.toLinearEquiv) :=
  ⟨fun g x ↦ by simpa [e.isIntertwining] using congrArg e (h.isIntertwining g x)⟩

/-- **Composition with an isomorphism of lifts**: if `e : ρ' ≅ ρ` and `ρ` is a lift of `ρbar`
marked by `ι`, then `ρ'` is a lift of `ρbar` marked by `k_A ⊗ e` followed by `ι`. -/
theorem IsLiftOf.iso_trans (e : Iso ρ' ρ) (h : IsLiftOf ρ ρbar ι) :
    IsLiftOf ρ' ρbar
      ((e.toContinuousLinearEquiv.toLinearEquiv.baseChange A (ResidueField A) M' M).trans ι) := by
  refine isLiftOf_iff_tmul.2 fun g m ↦ ?_
  simpa [e.isIntertwining] using isLiftOf_iff_tmul.1 h g (e m)

section Topology

variable [TopologicalSpace A] [IsModuleTopology A M] [Module.Finite A M]
  [TopologicalSpace (ResidueField A)] [IsTopologicalRing (ResidueField A)]
  [ContinuousSMul A (ResidueField A)] [TopologicalSpace (ResidueField A ⊗[A] M)]
  [IsModuleTopology (ResidueField A) (ResidueField A ⊗[A] M)] [IsModuleTopology (ResidueField A) V]

/-- A lift of `ρbar` marked by `ι` gives the isomorphism `ι : ρ.reduction ≅ ρbar` of continuous
representations. -/
noncomputable def IsLiftOf.toIso (h : IsLiftOf ρ ρbar ι) : Iso ρ.reduction ρbar :=
  .ofEquiv (.mk ι fun g ↦ LinearMap.ext fun x ↦ by
    simpa [baseChange_apply] using h.isIntertwining g x)

@[simp]
theorem IsLiftOf.toIso_apply (h : IsLiftOf ρ ρbar ι) (x : ResidueField A ⊗[A] M) :
    h.toIso x = ι x := by
  simp [IsLiftOf.toIso]

/-- The marking underlying the isomorphism of a marked lift is the marking itself. -/
@[simp]
theorem IsLiftOf.toLinearEquiv_toIso (h : IsLiftOf ρ ρbar ι) :
    h.toIso.toContinuousLinearEquiv.toLinearEquiv = ι :=
  LinearEquiv.ext h.toIso_apply

omit [IsModuleTopology (ResidueField A) V] in
/-- An isomorphism `e : ρ.reduction ≅ ρbar` makes `ρ` a lift of `ρbar` marked by `e`. -/
theorem Iso.isLiftOf (e : Iso ρ.reduction ρbar) :
    IsLiftOf ρ ρbar e.toContinuousLinearEquiv.toLinearEquiv :=
  ⟨fun g x ↦ by simpa [baseChange_apply] using e.isIntertwining g x⟩

/-- The isomorphism of the marked lift given by `e : ρ.reduction ≅ ρbar` is `e` itself. -/
@[simp]
theorem Iso.toIso_isLiftOf (e : Iso ρ.reduction ρbar) : e.isLiftOf.toIso = e :=
  Iso.ext e.isLiftOf.toIso_apply

end Topology

section ScalarExtension

open TensorProduct

variable (B : Type*) [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- **The marking of a scalar extension.** For a local homomorphism `A → B` with residue fields
`k_A → k_B`, a marking `ι : k_A ⊗[A] M ≃ V` induces the marking
`k_B ⊗[B] (B ⊗[A] M) ≃ k_B ⊗[A] M ≃ k_B ⊗[k_A] (k_A ⊗[A] M) ≃ k_B ⊗[k_A] V`; the first two steps
are the identifications of `TauCeti.ContinuousRep.baseChangeTransIso`. -/
noncomputable def baseChangeMarking (ι : ResidueField A ⊗[A] M ≃ₗ[ResidueField A] V) :
    ResidueField B ⊗[B] (B ⊗[A] M) ≃ₗ[ResidueField B] ResidueField B ⊗[ResidueField A] V :=
  (AlgebraTensorModule.cancelBaseChange A B (ResidueField B) (ResidueField B) M).trans <|
    (AlgebraTensorModule.cancelBaseChange A (ResidueField A) (ResidueField B) (ResidueField B)
      M).symm.trans <|
    LinearEquiv.baseChange (ResidueField A) (ResidueField B) _ _ ι

omit [TopologicalSpace M] [TopologicalSpace V] in
@[simp]
theorem baseChangeMarking_tmul (ι : ResidueField A ⊗[A] M ≃ₗ[ResidueField A] V)
    (c : ResidueField B) (b : B) (m : M) :
    baseChangeMarking B ι (c ⊗ₜ (b ⊗ₜ m)) = (b • c) ⊗ₜ ι (1 ⊗ₜ m) := by
  simp [baseChangeMarking]

/-- **Scalar extension of a marked lift.** If `ρ` is a lift of `ρbar` marked by `ι`, then for a
local homomorphism `A → B` the extension `B ⊗[A] ρ` is a lift of `k_B ⊗[k_A] ρbar`, marked by
`baseChangeMarking B ι`. -/
theorem IsLiftOf.baseChange [TopologicalSpace A] [IsModuleTopology A M] [Module.Finite A M]
    [TopologicalSpace B] [IsTopologicalSemiring B] [ContinuousSMul A B]
    [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)]
    [TopologicalSpace (ResidueField A)] [TopologicalSpace (ResidueField B)]
    [IsTopologicalSemiring (ResidueField B)] [ContinuousSMul (ResidueField A) (ResidueField B)]
    [IsModuleTopology (ResidueField A) V] [Module.Finite (ResidueField A) V]
    [TopologicalSpace (ResidueField B ⊗[ResidueField A] V)]
    [IsModuleTopology (ResidueField B) (ResidueField B ⊗[ResidueField A] V)]
    (h : IsLiftOf ρ ρbar ι) :
    IsLiftOf (ρ.baseChange B) (ρbar.baseChange (ResidueField B)) (baseChangeMarking B ι) := by
  refine isLiftOf_iff_tmul.2 fun g x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul b m => simp [baseChange_apply, isLiftOf_iff_tmul.1 h]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]

end ScalarExtension

section Frame

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Frame description of a marked lift.** For a basis `b` of `M`, `ρ` is a lift of `ρbar` marked
by `ι` if and only if, in the basis `ι (1 ⊗ b i)` of `V`, the matrix of every `ρbar g` is the
reduction of the matrix of `ρ g` in `b`. -/
theorem isLiftOf_iff_toMatrix (b : Module.Basis n A M) :
    IsLiftOf ρ ρbar ι ↔ ∀ g : Γ,
      (LinearMap.toMatrix b b (ρ g)).map (residue A) =
        LinearMap.toMatrix ((Algebra.TensorProduct.basis (ResidueField A) b).map ι)
          ((Algebra.TensorProduct.basis (ResidueField A) b).map ι) (ρbar g) := by
  refine (Representation.isIntertwiningMap_iff _ _ _).trans (forall_congr' fun g ↦ ?_)
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right, ← ResidueField.algebraMap_eq,
    ← LinearMap.toMatrix_baseChange, (LinearMap.toMatrix _ _).injective.eq_iff, LinearMap.ext_iff]
  refine forall_congr' fun x ↦ ?_
  simp [LinearEquiv.eq_symm_apply]

end Frame

end TauCeti.ContinuousRep
