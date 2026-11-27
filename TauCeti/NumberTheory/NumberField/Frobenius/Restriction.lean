/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.Invariant.Basic

/-!
# Restriction of arithmetic Frobenius

An arithmetic Frobenius in a field extension remains an arithmetic Frobenius after restriction
to a normal intermediate extension. More precisely, if `L/M/K` is a tower with `M/K` normal and
`σ ∈ Gal(L/K)` is an arithmetic Frobenius at `Q`, then `σ|_M` is an arithmetic Frobenius at the
contracted prime `Q ∩ 𝓞 M`.

This is the unpowered restriction law: both Frobenius elements are relative to the same base
field `K`, so both act on residue fields by the cardinality of the residue field of the same base
prime. The distinct tower law obtained by raising the base from `K` to `M` involves the inertia
degree as an exponent and is not proved here.

The argument follows Jürgen Neukirch, *Algebraic Number Theory*, Chapter I, §9.

The same holds for the residue action by any fixed power `x ↦ x ^ q`. Conversely, over a Galois
extension in which some automorphism acts by `x ↦ x ^ q` modulo `Q`, every automorphism of a
normal intermediate field acting by `x ↦ x ^ q` modulo the contracted prime is the restriction of
one acting by `x ↦ x ^ q` modulo `Q`: correct the restriction of the given automorphism by an
element of the inertia group, which surjects onto the inertia group below
(`Ideal.map_inertia_of_surjective`).

## Main results

* `IsArithFrobAt.restrictNormal`: restriction to a normal intermediate extension preserves the
  arithmetic-Frobenius property at the contracted prime.
* `NumberField.forall_quotient_mk_restrictNormal_smul_eq_pow`: restriction to a normal
  intermediate extension preserves acting on residues by `x ↦ x ^ q`.
* `NumberField.restrictNormal_smul_under`, `NumberField.restrictNormal_mem_stabilizer_under`:
  restriction to a normal intermediate extension commutes with contracting ideals, so it maps
  the stabilizer of a prime into the stabilizer of the contracted prime.
* `NumberField.restrictScalars_smul_ideal`: restricting the scalars of an automorphism does not
  change its action on ideals of the ring of integers.
* `NumberField.image_restrictNormal_setOf_forall_quotient_mk_smul_eq_pow`: over a Galois
  extension, if some automorphism acts on residues by `x ↦ x ^ q`, the automorphisms doing so
  restrict onto those of a normal intermediate field doing so at the contracted prime.
-/

public section

open Ideal
open scoped NumberField Pointwise

namespace IsArithFrobAt

variable {K M L : Type*} [Field K] [Field M] [Field L] [Algebra K M] [Algebra M L]
  [Algebra K L] [IsScalarTower K M L] [Normal K M]

/-- **Arithmetic Frobenius restricts without a power along a normal subextension.**

If `σ ∈ Gal(L/K)` is an arithmetic Frobenius at `Q`, its restriction to a normal intermediate
extension `M/K` is an arithmetic Frobenius at `Q ∩ 𝓞 M`. The exponent on both sides is the
cardinality of `𝓞 K` modulo the contraction of `Q`; `Ideal.under_under` identifies the two
contractions. -/
theorem restrictNormal {Q : Ideal (𝓞 L)} {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    IsArithFrobAt (𝓞 K) (σ.restrictNormal M) (Q.under (𝓞 M)) := by
  intro x
  rw [Ideal.mem_under, MulSemiringAction.toAlgHom_apply, map_sub,
    NumberField.algebraMap_restrictNormal_smul, map_pow, Ideal.under_under]
  exact hσ (algebraMap (𝓞 M) (𝓞 L) x)

end IsArithFrobAt

namespace NumberField

section Tower

variable {K M L : Type*} [Field K] [Field M] [Field L] [Algebra K M] [Algebra M L]
  [Algebra K L] [IsScalarTower K M L] [Normal K M]

/-- Restriction to a normal intermediate extension `M/K` preserves acting on residues by a fixed
power: if `σ ∈ Gal(L/K)` acts on `𝓞 L ⧸ Q` by `x ↦ x ^ q`, then `σ|_M` acts on
`𝓞 M ⧸ (Q ∩ 𝓞 M)` by `x ↦ x ^ q`. -/
theorem forall_quotient_mk_restrictNormal_smul_eq_pow {Q : Ideal (𝓞 L)} {σ : L ≃ₐ[K] L} {q : ℕ}
    (hσ : ∀ x : 𝓞 L, Ideal.Quotient.mk Q (σ • x) = Ideal.Quotient.mk Q x ^ q) (x : 𝓞 M) :
    Ideal.Quotient.mk (Q.under (𝓞 M)) (σ.restrictNormal M • x) =
      Ideal.Quotient.mk (Q.under (𝓞 M)) x ^ q := by
  rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_under, map_sub, algebraMap_restrictNormal_smul,
    map_pow, ← Ideal.Quotient.eq, map_pow]
  exact hσ _

/-- Restriction to a normal intermediate extension `M/K` commutes with contracting ideals:
`σ|_M • (I ∩ 𝓞 M) = (σ • I) ∩ 𝓞 M` for `σ ∈ Gal(L/K)`. -/
theorem restrictNormal_smul_under (σ : L ≃ₐ[K] L) (I : Ideal (𝓞 L)) :
    σ.restrictNormal M • I.under (𝓞 M) = (σ • I).under (𝓞 M) := by
  -- Restriction is a monoid hom (`AlgEquiv.restrictNormalHom`), so it commutes with inverses.
  have hinv : (σ.restrictNormal M)⁻¹ = σ⁻¹.restrictNormal M := by
    simpa only [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply] using
      (map_inv (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M) σ).symm
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_under, Ideal.mem_under, hinv,
    algebraMap_restrictNormal_smul, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem]

/-- Restriction to a normal intermediate extension `M/K` maps the stabilizer of an ideal `I` of
`𝓞 L` into the stabilizer of its contraction `I ∩ 𝓞 M`. -/
theorem restrictNormal_mem_stabilizer_under {I : Ideal (𝓞 L)} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) I) :
    σ.restrictNormal M ∈ MulAction.stabilizer (M ≃ₐ[K] M) (I.under (𝓞 M)) := by
  rw [MulAction.mem_stabilizer_iff, restrictNormal_smul_under, MulAction.mem_stabilizer_iff.mp hσ]

end Tower

section RestrictScalars

variable {K F E : Type*} [Field K] [Field F] [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
  [IsScalarTower K F E]

/-- Restricting the scalars of `σ ∈ Gal(E/F)` to a subfield `K` of `F` does not change its action
on ideals of `𝓞 E`. -/
theorem restrictScalars_smul_ideal (σ : E ≃ₐ[F] E) (I : Ideal (𝓞 E)) :
    σ.restrictScalars K • I = σ • I := by
  simp only [Ideal.pointwise_smul_def]
  refine congrArg (Ideal.map · I) (RingHom.ext fun x ↦ RingOfIntegers.ext ?_)
  simp

end RestrictScalars

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **Residue powers lift along restriction.** Let `L/K` be a Galois extension of number fields,
`E` a normal intermediate field, `Q` a prime of `𝓞 L` and `q` an exponent such that some
automorphism of `L/K` acts on `𝓞 L ⧸ Q` by `x ↦ x ^ q`. Then the automorphisms of `E/K` acting on
`𝓞 E ⧸ (Q ∩ 𝓞 E)` by `x ↦ x ^ q` are exactly the restrictions of the automorphisms of `L/K`
acting on `𝓞 L ⧸ Q` by `x ↦ x ^ q`: any lift can be corrected by inertia.

The existence hypothesis cannot be dropped: for `L = ℚ(i)` over `K = ℚ`, `E = ⊥` and `Q = (3)`,
the identity of `E` acts by `x ↦ x ^ 5` on the residue field `𝔽₃`, but no automorphism of `L`
acts by `x ↦ x ^ 5` on `𝓞 L ⧸ Q ≅ 𝔽₉`, where the automorphisms act by `x ↦ x` and `x ↦ x ^ 3`. -/
theorem image_restrictNormal_setOf_forall_quotient_mk_smul_eq_pow (E : IntermediateField K L)
    [Normal K E] (Q : Ideal (𝓞 L)) [Q.IsPrime] {q : ℕ}
    (hq : ∃ σ : L ≃ₐ[K] L, ∀ x : 𝓞 L, Ideal.Quotient.mk Q (σ • x) = Ideal.Quotient.mk Q x ^ q) :
    (fun σ : L ≃ₐ[K] L => σ.restrictNormal E) ''
        {σ | ∀ x : 𝓞 L, Ideal.Quotient.mk Q (σ • x) = Ideal.Quotient.mk Q x ^ q} =
      {τ : E ≃ₐ[K] E | ∀ x : 𝓞 E,
        Ideal.Quotient.mk (Q.under (𝓞 E)) (τ • x) = Ideal.Quotient.mk (Q.under (𝓞 E)) x ^ q} := by
  let P := Q.under (𝓞 E)
  let r := AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E
  have hr (σ : L ≃ₐ[K] L) : r σ = σ.restrictNormal E :=
    AlgEquiv.ext fun x => Subtype.ext (by
      rw [AlgEquiv.restrictNormalHom_apply, ← IntermediateField.algebraMap_apply,
        ← AlgEquiv.restrictNormal_commutes, IntermediateField.algebraMap_apply])
  refine Set.Subset.antisymm ?_ fun τ hτ => ?_
  · rintro - ⟨σ, hσ, rfl⟩
    exact forall_quotient_mk_restrictNormal_smul_eq_pow hσ
  obtain ⟨σ, hσ⟩ := hq
  -- `τ (σ|_E)⁻¹` acts trivially on residues, so it lies in the inertia group of `P`.
  have hδ : τ * (r σ)⁻¹ ∈ P.inertia (E ≃ₐ[K] E) := by
    rw [Ideal.mem_inertia]
    intro x
    rw [← Ideal.Quotient.eq, mul_smul]
    have hx := (hτ ((r σ)⁻¹ • x)).trans
      (forall_quotient_mk_restrictNormal_smul_eq_pow hσ ((r σ)⁻¹ • x)).symm
    simpa only [← hr, smul_inv_smul] using hx
  -- Inertia of `Q` surjects onto inertia of `P`, so `τ (σ|_E)⁻¹ = δ|_E` with `δ` inert at `Q`.
  have : IsGaloisGroup E.fixingSubgroup E L := IsGaloisGroup.intermediateField (L ≃ₐ[K] L) K L E
  have : IsGaloisGroup E.fixingSubgroup (𝓞 E) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing E.fixingSubgroup (𝓞 E) (𝓞 L) E L
  have hmap : (Q.inertia (L ≃ₐ[K] L)).map r = P.inertia (E ≃ₐ[K] E) :=
    Ideal.map_inertia_of_surjective r E.fixingSubgroup P Q
      (AlgEquiv.restrictNormalHom_surjective L) E.restrictNormalHom_ker.ge
      algebraMap_restrictNormal_smul
  rw [← hmap] at hδ
  obtain ⟨δ, hδ, hδeq⟩ := hδ
  -- Then `δ σ` acts by `x ↦ x ^ q` modulo `Q` and restricts to `τ`.
  refine ⟨δ * σ, fun x => ?_, ?_⟩
  · rw [mul_smul, Ideal.Quotient.eq.mpr (Ideal.mem_inertia.mp hδ (σ • x)), hσ x]
  · simp only [← hr, map_mul, hδeq, inv_mul_cancel_right]

end NumberField
