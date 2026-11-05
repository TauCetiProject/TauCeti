/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Pushout.Basic
public import TauCeti.RingTheory.Huber.TensorProduct.Completion
public import Mathlib.Topology.Algebra.Algebra.Equiv

import TauCeti.RingTheory.Affinoid.FiniteQuotient
import TauCeti.RingTheory.Huber.ClosedSubmodule
import TauCeti.RingTheory.Huber.Normed
import TauCeti.Topology.Algebra.Nonarchimedean.Quotient
import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# The affinoid pushout is the completed tensor product

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, carrying a complete
ultrametric algebra norm, and let `B = A⟨X₁, …, Xₘ⟩ ⧸ I` and `C = A⟨Y₁, …, Yₙ⟩ ⧸ J`, with their
quotient topologies. This file identifies the affinoid pushout
`TauCeti.AffinoidPushout I J = A⟨X, Y⟩ ⧸ (I, J)` with the completed tensor product
`B ⊗̂_A C = TauCeti.Huber.CompletedTensor A B C`, the separated completion of `B ⊗[A] C` for the
tensor topology of the Huber rings `A`, `B` and `C`. The isomorphism is an isomorphism of
topological `A`-algebras and is compatible with the two coprojections on each side.

The structure maps `A → B` and `A → C` are adic for the quotient topologies
(`TauCeti.MvPowerSeries.isAdicHom_algebraMap_isRestrictedSubring_quotient`), which is what the
completed tensor product requires of them. As in `TauCeti.Huber.CompletedTensor`, these facts
enter the isomorphism as instance arguments. Only the rings are compared here; rings of integral
elements are not.

The map `B ⊗̂_A C → A⟨X, Y⟩ ⧸ (I, J)` comes from the universal property of the completed tensor
product, `TauCeti.Huber.CompletedTensor.lift`, applied to the continuous coprojections of the
affinoid pushout; its target is complete and separated because every ideal of `A⟨X, Y⟩` is
closed. The inverse map sends the variables `Xᵢ` and `Yⱼ` to `Xᵢ ⊗ 1` and `1 ⊗ Yⱼ`
by the universal property of the affinoid pushout for continuous maps,
`TauCeti.AffinoidPushout.liftRingHom`, which applies because the images of the variables are
power-bounded. Both composites are the identity since continuous maps out of either side are
determined by the coprojections.

In particular, results about completed tensor products of Huber rings apply to affinoid pushouts.

## Main results

* `TauCeti.AffinoidPushout.completedTensorEquiv`: the isomorphism of topological `A`-algebras
  `A⟨X, Y⟩ ⧸ (I, J) ≃ B ⊗̂_A C`.
* `TauCeti.AffinoidPushout.completedTensorEquiv_inl` and
  `TauCeti.AffinoidPushout.completedTensorEquiv_inr`: it is compatible with the coprojections.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.1.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, proof of Proposition 3.7.
-/

public section

namespace TauCeti

open _root_.MvPowerSeries TauCeti.MvPowerSeries TauCeti.Huber

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
  {m n : ℕ}

namespace AffinoidPushout

variable (I : Ideal (IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1)))
  (J : Ideal (IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1)))
  [IsAdicHom (algebraMap A (IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1) ⧸ I))]
  [IsAdicHom (algebraMap A (IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1) ⧸ J))]

local notation "B" => IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1) ⧸ I
local notation "C" => IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1) ⧸ J

/-! ### The map from the completed tensor product -/

include K in
omit [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)] in
-- Every ideal of `A⟨X, Y⟩` is closed, since `A⟨X, Y⟩` is a noetherian Banach algebra over `K`.
private theorem isClosed_pushoutIdeal (hA : IsAffinoidAlgebra K A) :
    IsClosed (pushoutIdeal I J : Set (IsRestricted.subring (R := A) (fun _ : Fin (m + n) ↦ 1))) :=
  have := (hA.isRestricted_subring (τ := Fin (m + n))).isNoetherianRing
  have : IsTateRing (IsRestricted.subring (R := A) (fun _ : Fin (m + n) ↦ 1)) :=
    IsTateRing.of_normedAlgebra K _
  isClosed_of_isNoetherian _

/-- The map `B ⊗̂_A C → A⟨X, Y⟩ ⧸ (I, J)` induced by the coprojections of the affinoid pushout. -/
private noncomputable def ofCompletedTensor (hA : IsAffinoidAlgebra K A) :
    CompletedTensor A B C →+* AffinoidPushout I J :=
  have := isClosed_pushoutIdeal I J hA
  CompletedTensor.lift (inl I J).toRingHom (inr I J).toRingHom
    ((inl I J).comp_algebraMap.trans (inr I J).comp_algebraMap.symm)
    (continuous_inl I J) (continuous_inr I J)

private theorem continuous_ofCompletedTensor (hA : IsAffinoidAlgebra K A) :
    Continuous (ofCompletedTensor I J hA) :=
  have := isClosed_pushoutIdeal I J hA
  CompletedTensor.continuous_lift _ _ _ _ _

private theorem ofCompletedTensor_inl (hA : IsAffinoidAlgebra K A) (x : B) :
    ofCompletedTensor I J hA (CompletedTensor.inl A B C x) = inl I J x :=
  have := isClosed_pushoutIdeal I J hA
  CompletedTensor.lift_inl _ _ _ _ _ x

private theorem ofCompletedTensor_inr (hA : IsAffinoidAlgebra K A) (y : C) :
    ofCompletedTensor I J hA (CompletedTensor.inr A B C y) = inr I J y :=
  have := isClosed_pushoutIdeal I J hA
  CompletedTensor.lift_inr _ _ _ _ _ y

/-! ### The map to the completed tensor product -/

include K in
omit [IsUltrametricDist K] [CompleteSpace K] [CompleteSpace A] in
private theorem isPowerBounded_inl_X (i : Fin m) :
    IsPowerBounded (CompletedTensor.inl A B C (Ideal.Quotient.mk I ⟨X i, isRestricted_X _ i⟩)) :=
  have : IsTateRing (IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1)) :=
    IsTateRing.of_normedAlgebra K _
  (CompletedTensor.isAdicHom_inl A B C).isPowerBounded_map
    ((IsAdicHom.of_isOpenQuotientMap (QuotientRing.isOpenQuotientMap_mk I)).isPowerBounded_map
      (isPowerBounded_X i))

include K in
omit [IsUltrametricDist K] [CompleteSpace K] [CompleteSpace A] in
private theorem isPowerBounded_inr_X (j : Fin n) :
    IsPowerBounded (CompletedTensor.inr A B C (Ideal.Quotient.mk J ⟨X j, isRestricted_X _ j⟩)) :=
  have : IsTateRing (IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1)) :=
    IsTateRing.of_normedAlgebra K _
  (CompletedTensor.isAdicHom_inr A B C).isPowerBounded_map
    ((IsAdicHom.of_isOpenQuotientMap (QuotientRing.isOpenQuotientMap_mk J)).isPowerBounded_map
      (isPowerBounded_X j))

/-- The map `A⟨X, Y⟩ ⧸ (I, J) → B ⊗̂_A C` sending `Xᵢ` to `Xᵢ ⊗ 1` and `Yⱼ` to `1 ⊗ Yⱼ`. -/
private noncomputable def toCompletedTensor : AffinoidPushout I J →+* CompletedTensor A B C :=
  liftRingHom (CompletedTensor.continuous_inl A B C) (CompletedTensor.continuous_inr A B C)
    (isPowerBounded_inl_X (K := K) I J) (isPowerBounded_inr_X (K := K) I J)
    (CompletedTensor.inl_comp_algebraMap A B C)

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem continuous_toCompletedTensor : Continuous (toCompletedTensor (K := K) I J) :=
  continuous_liftRingHom _ _ _ _ _

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem toCompletedTensor_inl (x : B) :
    toCompletedTensor (K := K) I J (inl I J x) = CompletedTensor.inl A B C x :=
  liftRingHom_inl _ _ _ _ _ x

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem toCompletedTensor_inr (y : C) :
    toCompletedTensor (K := K) I J (inr I J y) = CompletedTensor.inr A B C y :=
  liftRingHom_inr _ _ _ _ _ y

/-! ### The isomorphism -/

variable (hA : IsAffinoidAlgebra K A)

private theorem ofCompletedTensor_toCompletedTensor (x : AffinoidPushout I J) :
    ofCompletedTensor I J hA (toCompletedTensor (K := K) I J x) = x := by
  have := isClosed_pushoutIdeal I J hA
  suffices h : (ofCompletedTensor I J hA).comp (toCompletedTensor (K := K) I J) = RingHom.id _ from
    congr($h x)
  refine ringHom_ext_of_continuous
    ((continuous_ofCompletedTensor I J hA).comp (continuous_toCompletedTensor I J)) continuous_id
    (fun x ↦ ?_) (fun y ↦ ?_)
  · simp [ofCompletedTensor_inl, toCompletedTensor_inl]
  · simp [ofCompletedTensor_inr, toCompletedTensor_inr]

private theorem toCompletedTensor_ofCompletedTensor (y : CompletedTensor A B C) :
    toCompletedTensor (K := K) I J (ofCompletedTensor I J hA y) = y := by
  suffices h : (toCompletedTensor (K := K) I J).comp (ofCompletedTensor I J hA) = RingHom.id _ from
    congr($h y)
  refine CompletedTensor.hom_ext
    ((continuous_toCompletedTensor I J).comp (continuous_ofCompletedTensor I J hA)) continuous_id
    (RingHom.ext fun x ↦ ?_) (RingHom.ext fun y ↦ ?_)
  · simp [ofCompletedTensor_inl, toCompletedTensor_inl]
  · simp [ofCompletedTensor_inr, toCompletedTensor_inr]

/-- **The affinoid pushout is the completed tensor product.** For an affinoid algebra `A` with a
complete ultrametric algebra norm, `A⟨X, Y⟩ ⧸ (I, J)` is isomorphic, as a topological
`A`-algebra, to the completed tensor product `B ⊗̂_A C` of `B = A⟨X⟩ ⧸ I` and `C = A⟨Y⟩ ⧸ J`
with their quotient topologies. It sends `inl x` to `x ⊗ 1` and `inr y` to `1 ⊗ y`
(`completedTensorEquiv_inl` and `completedTensorEquiv_inr`). -/
noncomputable def completedTensorEquiv : AffinoidPushout I J ≃A[A] CompletedTensor A B C where
  toFun := toCompletedTensor (K := K) I J
  invFun := ofCompletedTensor I J hA
  left_inv := ofCompletedTensor_toCompletedTensor I J hA
  right_inv := toCompletedTensor_ofCompletedTensor I J hA
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' a := by
    rw [← (inl I J).commutes a, toCompletedTensor_inl, CompletedTensor.inl_algebraMap]
  continuous_toFun := continuous_toCompletedTensor I J
  continuous_invFun := continuous_ofCompletedTensor I J hA

/-- `completedTensorEquiv` sends the left coprojection to the left coprojection. -/
@[simp]
theorem completedTensorEquiv_inl (x : B) :
    completedTensorEquiv I J hA (inl I J x) = CompletedTensor.inl A B C x :=
  toCompletedTensor_inl I J x

/-- `completedTensorEquiv` sends the right coprojection to the right coprojection. -/
@[simp]
theorem completedTensorEquiv_inr (y : C) :
    completedTensorEquiv I J hA (inr I J y) = CompletedTensor.inr A B C y :=
  toCompletedTensor_inr I J y

/-- The inverse of `completedTensorEquiv` sends the left coprojection to the left coprojection. -/
@[simp]
theorem completedTensorEquiv_symm_inl (x : B) :
    (completedTensorEquiv I J hA).symm (CompletedTensor.inl A B C x) = inl I J x :=
  ofCompletedTensor_inl I J hA x

/-- The inverse of `completedTensorEquiv` sends the right coprojection to the right coprojection. -/
@[simp]
theorem completedTensorEquiv_symm_inr (y : C) :
    (completedTensorEquiv I J hA).symm (CompletedTensor.inr A B C y) = inr I J y :=
  ofCompletedTensor_inr I J hA y

end AffinoidPushout

end TauCeti
