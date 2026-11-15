/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Counting the intermediate fields isomorphic to a given field

Let `E / K` and `Ω / K` be field extensions. Every `K`-embedding `φ : E →ₐ[K] Ω` is an
isomorphism onto its image `φ.fieldRange`, and the intermediate fields of `Ω / K` arising this way
are exactly those `K`-isomorphic to `E`. Two embeddings with the same image differ by a unique
`K`-automorphism of `E`, so the embeddings are partitioned by their images into fibres that are
torsors under `E ≃ₐ[K] E`. Counting gives

`#{M : IntermediateField K Ω | M ≃ₐ[K] E} · #Aut_K(E) = #Hom_K(E, Ω)`.

For a finite separable extension `E / K` and a separably closed `Ω`, the right-hand side is
`[E : K]`. This is the form in which Serre's mass formula regroups the totally ramified extensions
of a local field inside a separable closure along their isomorphism classes.

## Main definitions

* `IntermediateField.algHomFieldRangeEquiv M`: the `K`-embeddings of `E` into `Ω` with image `M`
  are the `K`-isomorphisms `E ≃ₐ[K] M`.

## Main results

* `IntermediateField.ncard_isomorphic_mul_natCard_algEquiv`: the number of intermediate fields of
  `Ω / K` that are `K`-isomorphic to `E`, times the number of `K`-automorphisms of `E`, is the
  number of `K`-embeddings of `E` into `Ω`. No finiteness hypothesis is needed, since `Nat.card`
  and `Set.ncard` take the value `0` on infinite types and sets on both sides at once.
* `IntermediateField.ncard_isomorphic_mul_natCard_algEquiv_of_isSepClosed`: for `E / K` finite
  separable and `Ω` separably closed, the same product is `[E : K]`.
* `IntermediateField.setOf_isomorphic_eq_singleton_of_normal`: a normal intermediate field
  is `K`-isomorphic to no other intermediate field.
-/

public section
noncomputable section

namespace IntermediateField

variable {K E Ω : Type*} [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω]

/-- The `K`-embeddings of `E` into `Ω` whose image is the intermediate field `M` correspond to the
`K`-isomorphisms from `E` onto `M`: an embedding is sent to its corestriction, and an isomorphism
`e` to `M.val.comp e`. -/
def algHomFieldRangeEquiv (M : IntermediateField K Ω) :
    {φ : E →ₐ[K] Ω // φ.fieldRange = M} ≃ (E ≃ₐ[K] M) where
  toFun φ := φ.1.equivFieldRange.trans (equivOfEq φ.2)
  invFun e := ⟨M.val.comp e.toAlgHom, by
    ext x
    simp only [AlgHom.mem_fieldRange, AlgHom.coe_comp, Function.comp_apply, coe_val]
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ (e y).2, fun hx ↦ ⟨e.symm ⟨x, hx⟩, by simp⟩⟩⟩
  left_inv φ := by
    ext x
    simp
  right_inv e := by
    ext x
    simp

/-- `algHomFieldRangeEquiv` corestricts an embedding to its image. -/
@[simp]
theorem coe_algHomFieldRangeEquiv_apply (M : IntermediateField K Ω)
    (φ : {φ : E →ₐ[K] Ω // φ.fieldRange = M}) (x : E) :
    (algHomFieldRangeEquiv M φ x : Ω) = φ.1 x := by
  simp [algHomFieldRangeEquiv]

/-- The inverse of `algHomFieldRangeEquiv` composes an isomorphism onto `M` with the inclusion of
`M`. -/
@[simp]
theorem coe_algHomFieldRangeEquiv_symm_apply (M : IntermediateField K Ω) (e : E ≃ₐ[K] M) :
    ((algHomFieldRangeEquiv M).symm e : E →ₐ[K] Ω) = M.val.comp e.toAlgHom :=
  (rfl)

variable (K E Ω) in
/-- **The orbit count for embeddings.** The intermediate fields of `Ω / K` that are
`K`-isomorphic to `E`, counted with the `K`-automorphisms of `E`, account for every
`K`-embedding of `E` into `Ω` exactly once: an embedding is determined by its image `M` together
with an isomorphism `E ≃ₐ[K] M`, and each such `M` admits exactly `#Aut_K(E)` of them. -/
theorem ncard_isomorphic_mul_natCard_algEquiv :
    {M : IntermediateField K Ω | Nonempty (E ≃ₐ[K] M)}.ncard * Nat.card (E ≃ₐ[K] E) =
      Nat.card (E →ₐ[K] Ω) := by
  let S := {M : IntermediateField K Ω | Nonempty (E ≃ₐ[K] M)}
  -- The image of an embedding is isomorphic to `E`, so the embeddings fibre over `S`.
  let range : (E →ₐ[K] Ω) → S := fun φ ↦ ⟨φ.fieldRange, ⟨φ.equivFieldRange⟩⟩
  -- Each fibre is `E ≃ₐ[K] M`, which composing with a chosen `E ≃ₐ[K] M` identifies with
  -- `E ≃ₐ[K] E`.
  let fibre (M : S) : {φ // range φ = M} ≃ (E ≃ₐ[K] E) :=
    ((Equiv.subtypeEquivRight fun φ ↦ Subtype.ext_iff).trans
      (algHomFieldRangeEquiv M.1)).trans
      (AlgEquiv.refl.equivCongr M.2.some.symm)
  rw [← Nat.card_coe_set_eq, ← Nat.card_prod]
  exact Nat.card_congr <| ((Equiv.sigmaEquivProd S (E ≃ₐ[K] E)).symm.trans
    (Equiv.sigmaCongrRight fun M ↦ (fibre M).symm)).trans (Equiv.sigmaFiberEquiv range)

variable (K E Ω) in
/-- **The orbit count in a separably closed field.** For a finite separable extension `E / K` and a
separably closed `Ω`, the intermediate fields of `Ω / K` that are `K`-isomorphic to `E`, counted
with the `K`-automorphisms of `E`, number `[E : K]`. -/
theorem ncard_isomorphic_mul_natCard_algEquiv_of_isSepClosed [IsSepClosed Ω]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    {M : IntermediateField K Ω | Nonempty (E ≃ₐ[K] M)}.ncard * Nat.card (E ≃ₐ[K] E) =
      Module.finrank K E := by
  rw [ncard_isomorphic_mul_natCard_algEquiv, AlgHom.natCard_of_splits K E Ω fun x ↦
    IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable K x)]

/-- A normal intermediate field is the only intermediate field `K`-isomorphic to it: every
`K`-embedding of a normal extension into `Ω` has the same image. -/
theorem setOf_isomorphic_eq_singleton_of_normal (L : IntermediateField K Ω) [Normal K L] :
    {M : IntermediateField K Ω | Nonempty (L ≃ₐ[K] M)} = {L} := by
  ext M
  refine ⟨fun ⟨e⟩ ↦ ?_, fun h ↦ h ▸ ⟨AlgEquiv.refl⟩⟩
  rw [Set.mem_singleton_iff, ← ((algHomFieldRangeEquiv M).symm e).2]
  exact AlgHom.fieldRange_of_normal _

end IntermediateField
