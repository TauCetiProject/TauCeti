/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Nilpotent.Cone
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Nilpotent.WeightedDiagram

/-!
# Closure order on nilpotent adjoint orbits

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k` of
characteristic zero whose Lie algebra `𝔤 = (𝔪 / 𝔪²)*` has nondegenerate Killing form.

By `TauCeti.Comodule.VectorOrbit.finite_setOf_le_of_isNilpotentAd`, only finitely many rational
orbits lie below any nilpotent orbit `O` in the closure order, and by
`TauCeti.Comodule.VectorOrbit.IsNilpotentAd.of_le` every orbit below a nilpotent orbit is again
nilpotent. Consequently, the generic scheme-point decompositions of `closure O` and `closure O \ O`
inside the affine chart `𝔤 = {t ≠ 0}` of `P(𝔤 × k)` specialize to finite unions indexed by the
subtype of nilpotent orbits (`closure_image_inter_basicOpen_snd_eq_biUnion_le_nilpotentOrbit` and
`closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt_nilpotentOrbit`), without assuming `G` is
connected.

## Main declarations

* `closure_image_inter_basicOpen_snd_eq_biUnion_le_nilpotentOrbit` and
  `closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt_nilpotentOrbit` in
  `TauCeti.Comodule.VectorOrbit`: inside the affine chart `𝔤 = {t ≠ 0}` of `P(𝔤 × k)`, the
  closure `closure O` and boundary `closure O \ O` of a nilpotent adjoint orbit `O` are the
  unions of the scheme-point orbit images of all nilpotent orbits `O' ≤ O` and `O' < O`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §6.2.
-/

public section

namespace TauCeti.Comodule.VectorOrbit

universe u

attribute [local instance] Derivation.adjointComodule

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Orbit closure decomposition for nilpotent orbits.** Inside the affine chart `𝔤 = {t ≠ 0}` of
`P(𝔤 × k)`, the closure of a nilpotent adjoint orbit `O` is the finite union of the scheme-point
orbit images of all nilpotent orbits `O' ≤ O`, indexed by the nilpotent orbit subtype. No
connectedness of `G` is assumed. -/
theorem closure_image_inter_basicOpen_snd_eq_biUnion_le_nilpotentOrbit
    (O : {O : VectorOrbit k H 𝔤 // O.IsNilpotentAd}) :
    closure O.val.image ∩
        (AlgebraicGeometry.Proj.basicOpen
          (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (𝔤 × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (𝔤 × k)) (LinearMap.snd k 𝔤 k)) : Set _) =
      ⋃ O' ∈ {O' : {O' : VectorOrbit k H 𝔤 // O'.IsNilpotentAd} | O' ≤ O}, O'.val.image := by
  rw [closure_image_inter_basicOpen_snd_eq_biUnion_le (finite_setOf_le_of_isNilpotentAd O.property)]
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Subtype.exists, exists_prop]
  exact ⟨fun ⟨O', hle, hx⟩ ↦ ⟨O', O.property.of_le hle, hle, hx⟩,
    fun ⟨O', _, hle, hx⟩ ↦ ⟨O', hle, hx⟩⟩

/-- **Orbit boundary decomposition for nilpotent orbits.** Inside the affine chart `𝔤 = {t ≠ 0}` of
`P(𝔤 × k)`, the boundary `closure O \ O` of a nilpotent adjoint orbit `O` is the finite union of
the scheme-point orbit images of all strictly smaller nilpotent orbits `O' < O`, indexed by the
nilpotent orbit subtype. No connectedness of `G` is assumed. -/
theorem closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt_nilpotentOrbit
    (O : {O : VectorOrbit k H 𝔤 // O.IsNilpotentAd}) :
    (closure O.val.image \ O.val.image) ∩
        (AlgebraicGeometry.Proj.basicOpen
          (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (𝔤 × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (𝔤 × k)) (LinearMap.snd k 𝔤 k)) : Set _) =
      ⋃ O' ∈ {O' : {O' : VectorOrbit k H 𝔤 // O'.IsNilpotentAd} | O' < O}, O'.val.image := by
  rw [closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt
    (finite_setOf_le_of_isNilpotentAd O.property)]
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Subtype.exists, exists_prop]
  exact ⟨fun ⟨O', hlt, hx⟩ ↦ ⟨O', O.property.of_le hlt.le, hlt, hx⟩,
    fun ⟨O', _, hlt, hx⟩ ↦ ⟨O', hlt, hx⟩⟩

end TauCeti.Comodule.VectorOrbit
