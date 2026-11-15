/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Pair
public import TauCeti.RingTheory.Huber.TateGauge.Spectral.Uniformization

/-!
# The uniform completed tensor product of Tate Huber pairs

Let `A → B` and `A → C` be adic homomorphisms of Huber rings with Tate completed tensor ring
`B ⊗̂_A C` (for instance, `A` Tate), and let `(B, B⁺)` and `(C, C⁺)` be Huber pairs. The completed
tensor product of uniform Huber pairs need not be uniform (Kedlaya–Liu, Remark 2.8.5), so it is
not a pushout among uniform pairs. The *uniform completed tensor product*
`(B, B⁺) ⊗̂ᵘ_A (C, C⁺)` is the uniformization of the completed tensor product
`(B, B⁺) ⊗̂_A (C, C⁺)`. It is a complete Hausdorff uniform Tate Huber pair, and its two
coprojections represent compatible pairs of morphisms into complete Hausdorff uniform Huber
pairs (Kedlaya–Liu, the sentence before Definition 2.8.13).

The canonical morphism `ι : (B, B⁺) ⊗̂_A (C, C⁺) → (B, B⁺) ⊗̂ᵘ_A (C, C⁺)` is a homeomorphism exactly
when the completed tensor ring is uniform.

## Main definitions

* `TauCeti.Huber.Pair.uniformCompletedTensor A S T`: the uniform completed tensor product of the
  Huber pairs `S` on `B` and `T` on `C` over `A`.
* `TauCeti.Huber.Pair.uniformCompletedTensor.fromCompletedTensor`: the canonical morphism `ι` from
  the completed tensor product.
* `TauCeti.Huber.Pair.uniformCompletedTensor.inl`, `TauCeti.Huber.Pair.uniformCompletedTensor.inr`:
  the coprojections as morphisms of Huber pairs.
* `TauCeti.Huber.Pair.uniformCompletedTensor.lift`: the morphism induced by compatible morphisms
  into a complete Hausdorff uniform Huber pair.
* `TauCeti.Huber.Pair.uniformCompletedTensor.comm`: exchanging the two factors.

## Main results

* `TauCeti.Huber.Pair.uniformCompletedTensor.lift_comp_inl`,
  `TauCeti.Huber.Pair.uniformCompletedTensor.lift_comp_inr` and
  `TauCeti.Huber.Pair.uniformCompletedTensor.hom_ext`: the universal property.
* `TauCeti.Huber.Pair.uniformCompletedTensor.isHomeomorph_fromCompletedTensor_iff`: `ι` is a
  homeomorphism if and only if the completed tensor ring is uniform.
* `TauCeti.Huber.Pair.uniformCompletedTensor.comm_comp_comm`: exchanging the factors twice is the
  identity.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.8, Remark 2.8.5 and Definition 2.8.13.
* D. Hansen and K. S. Kedlaya, *Sheafiness criteria for Huber rings*, §7, Remark 7.2.
-/

public section

namespace TauCeti.Huber

variable (A : Type*) {B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  [IsTateRing (CompletedTensor A B C)]

namespace Pair

variable (S : Pair B) (T : Pair C)

/-- **The uniform completed tensor product `(B, B⁺) ⊗̂ᵘ_A (C, C⁺)` of Huber pairs**: the
uniformization of the completed tensor product `(B, B⁺) ⊗̂_A (C, C⁺)` (Kedlaya–Liu, the sentence
before Definition 2.8.13). Its ring is a complete Hausdorff uniform Tate ring, and its plus ring
is the closure of the image of the plus ring of the completed tensor product
(`TauCeti.Huber.Pair.uniformCompletedTensor.plus_eq`). -/
noncomputable def uniformCompletedTensor : Pair (Uniformization (CompletedTensor A B C)) :=
  (S.completedTensor A T).uniformization

namespace uniformCompletedTensor

/-- The plus ring of the uniform completed tensor product is the closure of the image of the plus
ring of the completed tensor product. -/
theorem plus_eq : (S.uniformCompletedTensor A T).plus =
    ((S.completedTensor A T).plus.map
      (toUniformization (CompletedTensor A B C))).topologicalClosure :=
  uniformization_plus _

/-- The canonical morphism `ι : (B, B⁺) ⊗̂_A (C, C⁺) → (B, B⁺) ⊗̂ᵘ_A (C, C⁺)`, the uniformization
map of the completed tensor product. -/
noncomputable def fromCompletedTensor :
    Hom (S.completedTensor A T) (S.uniformCompletedTensor A T) :=
  (S.completedTensor A T).uniformizationHom

/-- The left coprojection `(B, B⁺) → (B, B⁺) ⊗̂ᵘ_A (C, C⁺)` as a morphism of Huber pairs. -/
noncomputable def inl : Hom S (S.uniformCompletedTensor A T) :=
  (fromCompletedTensor A S T).comp (completedTensor.inl A S T)

/-- The right coprojection `(C, C⁺) → (B, B⁺) ⊗̂ᵘ_A (C, C⁺)` as a morphism of Huber pairs. -/
noncomputable def inr : Hom T (S.uniformCompletedTensor A T) :=
  (fromCompletedTensor A S T).comp (completedTensor.inr A S T)

/-- The underlying ring homomorphism of `ι` is the uniformization map of the completed tensor
ring. -/
@[simp]
theorem toRingHom_fromCompletedTensor :
    (fromCompletedTensor A S T).toRingHom = toUniformization (CompletedTensor A B C) :=
  Hom.toRingHom_uniformizationHom _

/-- The left coprojection factors through the completed tensor product. -/
@[simp]
theorem fromCompletedTensor_comp_inl :
    (fromCompletedTensor A S T).comp (completedTensor.inl A S T) = inl A S T :=
  (rfl)

/-- The right coprojection factors through the completed tensor product. -/
@[simp]
theorem fromCompletedTensor_comp_inr :
    (fromCompletedTensor A S T).comp (completedTensor.inr A S T) = inr A S T :=
  (rfl)

/-- The underlying ring homomorphism of the left coprojection. -/
@[simp]
theorem toRingHom_inl : (inl A S T).toRingHom =
    (toUniformization (CompletedTensor A B C)).comp (CompletedTensor.inl A B C) := by
  simp [← fromCompletedTensor_comp_inl]

/-- The underlying ring homomorphism of the right coprojection. -/
@[simp]
theorem toRingHom_inr : (inr A S T).toRingHom =
    (toUniformization (CompletedTensor A B C)).comp (CompletedTensor.inr A B C) := by
  simp [← fromCompletedTensor_comp_inr]

variable {S T} in
/-- The two coprojections agree on a Huber pair of the base whose morphisms into `(B, B⁺)` and
`(C, C⁺)` are the structure maps. -/
theorem inl_comp [IsHuberRing A] {P : Pair A} {f : Hom P S} {g : Hom P T}
    (hf : f.toRingHom = algebraMap A B) (hg : g.toRingHom = algebraMap A C) :
    (inl A S T).comp f = (inr A S T).comp g := by
  rw [← fromCompletedTensor_comp_inl, ← fromCompletedTensor_comp_inr, Hom.comp_assoc,
    Hom.comp_assoc, completedTensor.inl_comp hf hg]

variable {S T} in
/-- **Morphisms out of the uniform completed tensor product are determined by the
coprojections**, for a Hausdorff target. -/
theorem hom_ext {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [IsHuberRing R] {U : Pair R} {f g : Hom (S.uniformCompletedTensor A T) U}
    (hB : f.comp (inl A S T) = g.comp (inl A S T))
    (hC : f.comp (inr A S T) = g.comp (inr A S T)) : f = g := by
  refine Hom.ext <| Uniformization.ringHom_ext f.continuous_toRingHom g.continuous_toRingHom <|
    CompletedTensor.hom_ext (f.continuous_toRingHom.comp continuous_toUniformization)
      (g.continuous_toRingHom.comp continuous_toUniformization) ?_ ?_
  · simpa [RingHom.comp_assoc] using congrArg Hom.toRingHom hB
  · simpa [RingHom.comp_assoc] using congrArg Hom.toRingHom hC

section Lift

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [CompleteSpace R] [T0Space R] [IsHuberRing R] [IsUniform R] {S T} {U : Pair R}

/-- **The universal property of the uniform completed tensor product.** Morphisms
`φ : (B, B⁺) → (R, R⁺)` and `ψ : (C, C⁺) → (R, R⁺)` into a complete Hausdorff Huber pair with `R`
uniform, agreeing on `A`, induce a morphism `(B, B⁺) ⊗̂ᵘ_A (C, C⁺) → (R, R⁺)` (Kedlaya–Liu,
Definition 2.8.13). It is unique by `TauCeti.Huber.Pair.uniformCompletedTensor.hom_ext`. -/
noncomputable def lift (φ : Hom S U) (ψ : Hom T U)
    (h : φ.toRingHom.comp (algebraMap A B) = ψ.toRingHom.comp (algebraMap A C)) :
    Hom (S.uniformCompletedTensor A T) U :=
  (completedTensor.lift φ ψ h).uniformizationLift

/-- The underlying ring homomorphism of the induced morphism is the extension to the
uniformization of the continuous extension of `φ` and `ψ` to the completed tensor ring. -/
@[simp]
theorem toRingHom_lift (φ : Hom S U) (ψ : Hom T U)
    (h : φ.toRingHom.comp (algebraMap A B) = ψ.toRingHom.comp (algebraMap A C)) :
    (lift A φ ψ h).toRingHom = Uniformization.lift
      (CompletedTensor.lift φ.toRingHom ψ.toRingHom h φ.continuous_toRingHom
        ψ.continuous_toRingHom) (CompletedTensor.continuous_lift _ _ _ _ _) := by
  simp only [lift, Hom.toRingHom_uniformizationLift, completedTensor.toRingHom_lift]

/-- The induced morphism restricts along `ι` to the morphism induced on the completed tensor
product. -/
@[simp]
theorem lift_comp_fromCompletedTensor (φ : Hom S U) (ψ : Hom T U)
    (h : φ.toRingHom.comp (algebraMap A B) = ψ.toRingHom.comp (algebraMap A C)) :
    (lift A φ ψ h).comp (fromCompletedTensor A S T) = completedTensor.lift φ ψ h :=
  Hom.uniformizationLift_comp_uniformizationHom _

/-- The induced morphism restricts to the given morphism on the left factor. -/
@[simp]
theorem lift_comp_inl (φ : Hom S U) (ψ : Hom T U)
    (h : φ.toRingHom.comp (algebraMap A B) = ψ.toRingHom.comp (algebraMap A C)) :
    (lift A φ ψ h).comp (inl A S T) = φ := by
  rw [← fromCompletedTensor_comp_inl, ← Hom.comp_assoc, lift_comp_fromCompletedTensor,
    completedTensor.lift_comp_inl]

/-- The induced morphism restricts to the given morphism on the right factor. -/
@[simp]
theorem lift_comp_inr (φ : Hom S U) (ψ : Hom T U)
    (h : φ.toRingHom.comp (algebraMap A B) = ψ.toRingHom.comp (algebraMap A C)) :
    (lift A φ ψ h).comp (inr A S T) = ψ := by
  rw [← fromCompletedTensor_comp_inr, ← Hom.comp_assoc, lift_comp_fromCompletedTensor,
    completedTensor.lift_comp_inr]

end Lift

/-- **The comparison with the completed tensor product.** The canonical morphism
`ι : (B, B⁺) ⊗̂_A (C, C⁺) → (B, B⁺) ⊗̂ᵘ_A (C, C⁺)` is a homeomorphism if and only if the completed
tensor ring is uniform. -/
theorem isHomeomorph_fromCompletedTensor_iff :
    IsHomeomorph (fromCompletedTensor A S T).toRingHom ↔ IsUniform (CompletedTensor A B C) := by
  rw [toRingHom_fromCompletedTensor]
  exact isHomeomorph_toUniformization_iff

section Comm

variable [IsTateRing (CompletedTensor A C B)]

/-- **Exchanging the factors** `(B, B⁺) ⊗̂ᵘ_A (C, C⁺) → (C, C⁺) ⊗̂ᵘ_A (B, B⁺)`. It is an isomorphism
of Huber pairs, inverse to the exchange in the other order
(`TauCeti.Huber.Pair.uniformCompletedTensor.comm_comp_comm`). -/
noncomputable def comm : Hom (S.uniformCompletedTensor A T) (T.uniformCompletedTensor A S) :=
  lift A (inr A T S) (inl A T S) <| by
    simp only [toRingHom_inl, toRingHom_inr, RingHom.comp_assoc,
      CompletedTensor.inl_comp_algebraMap]

/-- Exchanging the factors sends the left coprojection to the right coprojection. -/
@[simp]
theorem comm_comp_inl : (comm A S T).comp (inl A S T) = inr A T S :=
  lift_comp_inl A _ _ _

/-- Exchanging the factors sends the right coprojection to the left coprojection. -/
@[simp]
theorem comm_comp_inr : (comm A S T).comp (inr A S T) = inl A T S :=
  lift_comp_inr A _ _ _

/-- Exchanging the factors twice is the identity. -/
@[simp]
theorem comm_comp_comm : (comm A T S).comp (comm A S T) = Hom.id _ :=
  hom_ext A (by rw [Hom.comp_assoc, comm_comp_inl, comm_comp_inr, Hom.id_comp])
    (by rw [Hom.comp_assoc, comm_comp_inr, comm_comp_inl, Hom.id_comp])

end Comm

end uniformCompletedTensor

end Pair

end TauCeti.Huber
