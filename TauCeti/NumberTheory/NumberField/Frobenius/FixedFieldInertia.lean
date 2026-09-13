/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.FixedField
public import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup

/-!
# The residue degree of a prime below a fixed field

Let `H` be a subgroup of `Gal(L/K)`, let `E = L ^ H`, and let `Q` be a nonzero prime of `𝓞 L`
unramified over `𝓞 K`.  The residue degree of `Q ∩ 𝓞 E` over `𝓞 K`, times the number of elements
`H` shares with the decomposition group of `Q`, is the residue degree of `Q` itself.

Nothing in that needs `H` cyclic or a Frobenius in sight: the Galois correspondence identifies
`Gal(L/E)` with `H` acting on ideals exactly as it does over `K`, so the decomposition group of `Q`
over `E` is `H ⊓ D(Q)`, and multiplicativity of the inertia degree in the tower `K ⊆ E ⊆ L` does
the rest.  It is stated as a product so that no natural-number division is truncated.

A Frobenius `φ` at `Q` generates `D(Q)`, so the count is `Subgroup.relIndex` — the index of
`H ⊓ ⟨φ⟩` in `⟨φ⟩` — and the residue degree is one exactly when `φ ∈ H`.  At `H = ⟨φ⟩` membership
is automatic and the degree is one, which is the hypothesis of
`NumberField.restrictScalars_eq_of_inertiaDeg_eq_one` and so the step a fixed-field fibre count
runs through.

## Main results

* `Ideal.card_stabilizer_fixedField_eq_card_inf`: the decomposition group of `Q` over `L ^ H` has
  as many elements as `D(Q) ⊓ H`.
* `Ideal.inertiaDeg_under_fixedField_mul_card_inf`: that count times the residue degree below
  `L ^ H` is the residue degree of `Q`.
* `Ideal.inertiaDeg_under_fixedField_eq_relIndex`: that residue degree is `Subgroup.relIndex`,
  the index of `H ⊓ ⟨φ⟩` in `⟨φ⟩`.
* `Ideal.inertiaDeg_under_fixedField_eq_one_iff`: it is one exactly when a Frobenius lies in `H`.
* `Ideal.inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt`: at `σ = φ`, it is one.

## References

Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.  The corresponding step of the
Birkbeck--Brasca Chebotarev development,
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0) at
commit `55a89985d47a3befcf6069aca1da250ff088b5c7`, is the private declaration
`inertiaDeg_under_E_eq_one_of_frobenius` in `CebotarevDensity/FixedFieldDensity.lean`.  There it is
one conjunct of a triple that also records the ramification index and the residue-field count, and
it carries `orderOf σ = Nat.card Gal(L/E)` as a hypothesis; that equality is a consequence of the
Galois correspondence and is derived here rather than assumed.  Upstream states only the `σ = φ`
case; the general residue degree above is not there.
-/

public section

open IntermediateField

open scoped NumberField Pointwise

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

omit [IsGalois K L] in
/-- **The decomposition group over a fixed field is the intersection.**  For any subgroup `H` of
`Gal(L/K)` and `E = L ^ H`, the stabilizer of `Q` in `Gal(L/E)` has as many elements as the
intersection of `H` with the stabilizer of `Q` in `Gal(L/K)`. -/
theorem card_stabilizer_fixedField_eq_card_inf (Q : Ideal (𝓞 L)) (H : Subgroup (L ≃ₐ[K] L)) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[↥(fixedField H)] L) Q)
      = Nat.card ((MulAction.stabilizer (L ≃ₐ[K] L) Q ⊓ H : Subgroup (L ≃ₐ[K] L))) := by
  set e := subgroupEquivAlgEquiv H with he
  -- the Galois correspondence does not move points, so it does not move ideals either
  have hsmul : ∀ τ : ↥H, (e τ) • Q = (τ : L ≃ₐ[K] L) • Q := fun τ ↦ by
    rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]
    exact congrArg (Ideal.map · Q) (RingHom.ext fun y ↦ NumberField.RingOfIntegers.ext rfl)
  have hcomap : (MulAction.stabilizer (L ≃ₐ[↥(fixedField H)] L) Q).comap (e : ↥H →* _)
      = (MulAction.stabilizer (L ≃ₐ[K] L) Q).subgroupOf H := by
    ext τ
    simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    exact Eq.congr_left (hsmul τ)
  have h1 : Nat.card ((MulAction.stabilizer (L ≃ₐ[↥(fixedField H)] L) Q).comap (e : ↥H →* _))
      = Nat.card (MulAction.stabilizer (L ≃ₐ[↥(fixedField H)] L) Q) := by
    rw [Subgroup.comap_equiv_eq_map_symm]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ e.symm.injective).symm.toEquiv
  have h2 : Nat.card ((MulAction.stabilizer (L ≃ₐ[K] L) Q).subgroupOf H)
      = Nat.card ((MulAction.stabilizer (L ≃ₐ[K] L) Q ⊓ H : Subgroup (L ≃ₐ[K] L))) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← h1, hcomap, h2]

/-- **The residue degree below a fixed field.**  For any subgroup `H` and `E = L ^ H`, the residue
degree of `Q ∩ 𝓞 E` over `𝓞 K` times the size of the intersection of `H` with the decomposition
group is the residue degree of `Q` itself.  Stated as a product, so no natural-number division is
truncated. -/
theorem inertiaDeg_under_fixedField_mul_card_inf (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (H : Subgroup (L ≃ₐ[K] L)) :
    (Q.under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K)
        * Nat.card ((MulAction.stabilizer (L ≃ₐ[K] L) Q ⊓ H : Subgroup (L ≃ₐ[K] L)))
      = Q.inertiaDeg (𝓞 K) := by
  set E := fixedField H with hE
  have : IsScalarTower K ↥E L := E.isScalarTower_mid'
  have : IsGalois ↥E L := IsGalois.tower_top_intermediateField _
  have : Algebra.IsUnramifiedAt (𝓞 ↥E) Q := Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 K) Q
  have htower : Q.inertiaDeg (𝓞 K)
      = (Q.under (𝓞 ↥E)).inertiaDeg (𝓞 K) * Q.inertiaDeg (𝓞 ↥E) :=
    inertiaDeg_tower (Q.under (𝓞 ↥E)) Q
  rw [htower, ← card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt Q hQ,
    card_stabilizer_fixedField_eq_card_inf Q H]

/-- **The residue degree is a relative index.**  For any subgroup `H` and `φ` a Frobenius at an
unramified `Q`, the residue degree below `L ^ H` is `Subgroup.relIndex`, Mathlib's name for the
index of `H ⊓ ⟨φ⟩` in `⟨φ⟩`. -/
theorem inertiaDeg_under_fixedField_eq_relIndex (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (H : Subgroup (L ≃ₐ[K] L)) {φ : L ≃ₐ[K] L}
    (hφ : IsArithFrobAt (𝓞 K) φ Q) :
    (Q.under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K) = H.relIndex (Subgroup.zpowers φ) := by
  have hmul := inertiaDeg_under_fixedField_mul_card_inf Q hQ H
  rw [← zpowers_eq_stabilizer_of_isArithFrobAt Q hQ hφ,
    ← orderOf_eq_inertiaDeg_of_isArithFrobAt Q hQ hφ] at hmul
  have hidx : H.relIndex (Subgroup.zpowers φ)
      * Nat.card ((Subgroup.zpowers φ ⊓ H : Subgroup (L ≃ₐ[K] L))) = orderOf φ := by
    rw [Subgroup.relIndex, ← Nat.card_zpowers φ,
      ← Subgroup.index_mul_card (H.subgroupOf (Subgroup.zpowers φ))]
    congr 1
    rw [inf_comm, ← Subgroup.inf_subgroupOf_right]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := H ⊓ Subgroup.zpowers φ) (K := Subgroup.zpowers φ) inf_le_right).toEquiv).symm
  have hpos : 0 < Nat.card ((Subgroup.zpowers φ ⊓ H : Subgroup (L ≃ₐ[K] L))) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (hmul.trans hidx.symm)

/-- **Residue degree one is membership.**  The prime below `Q` in `L ^ H` has residue degree one
over `𝓞 K` exactly when a Frobenius at `Q` lies in `H`. -/
theorem inertiaDeg_under_fixedField_eq_one_iff (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (H : Subgroup (L ≃ₐ[K] L)) {φ : L ≃ₐ[K] L}
    (hφ : IsArithFrobAt (𝓞 K) φ Q) :
    (Q.under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K) = 1 ↔ φ ∈ H := by
  rw [inertiaDeg_under_fixedField_eq_relIndex Q hQ H hφ, Subgroup.relIndex_eq_one,
    Subgroup.zpowers_le]

/-- **The prime below `Q` in the fixed field of a Frobenius at `Q` has degree one.**  The case
`H = ⟨σ⟩` with `σ` itself the Frobenius, where membership is automatic. -/
theorem inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1 :=
  (inertiaDeg_under_fixedField_eq_one_iff Q hQ (Subgroup.zpowers σ) hσ).2 (Subgroup.mem_zpowers σ)

end Ideal
