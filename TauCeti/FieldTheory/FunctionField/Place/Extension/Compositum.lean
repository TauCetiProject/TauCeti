/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Tame
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Inertia
import TauCeti.FieldTheory.FunctionField.Place.Extension.TameInertia
import TauCeti.FieldTheory.FunctionField.Place.Extension.WildInertia
import TauCeti.GroupTheory.PGroup.Index

/-!
# Abhyankar's lemma

Let `F' / F` be a finite Galois extension, `k` a subfield of `F`, and `P` a place of `F' / k` whose
residue extension over `P ∩ F` is separable. For intermediate fields `E₁` and `E₂` write
`eᵢ = e(P ∩ Eᵢ ∣ P ∩ F)`. **Abhyankar's lemma** (Stichtenoth, Theorem 3.9.1) says that if
`P ∩ E₁` is tame over `F`, the ramification index of the place below `P` in the compositum is

`e(P ∩ (E₁ ⊔ E₂) ∣ P ∩ F) = lcm (e₁, e₂)`.

In particular a place unramified in both `E₁` and `E₂` stays unramified in `E₁ ⊔ E₂`
(Stichtenoth, Corollary 3.9.3). The statements concern two intermediate fields of a finite Galois
extension; for a compositum of two finite separable extensions of `F` that extension is the
Galois closure. Stichtenoth works over a perfect constant field, where the separability of the
residue extension is automatic.

The proof is group-theoretic. With separable residue extension, `eᵢ` is the index of
`Gal(F' / Eᵢ)` in the inertia group `G₀(P)`
(`TauCeti.Place.ramificationIdx_restrict_eq_relIndex`), and the compositum corresponds to the
intersection `Gal(F' / E₁) ⊓ Gal(F' / E₂)`. The first ramification group `G₁(P)` is a normal
`p`-subgroup of `G₀(P)` with cyclic quotient, `p` the characteristic (and `G₁(P)` is trivial in
characteristic zero). Tameness says that `p` does not divide `e₁`, and in such a group the index of
an intersection is the lcm of the indices when one of them is prime to `p`
(`IsPGroup.index_inf_eq_lcm`).

## Main results

* `TauCeti.Place.ramificationIdx_restrict_sup_eq_lcm`: **Abhyankar's lemma**.
* `TauCeti.Place.ramificationIdx_restrict_sup_eq_one`: a place unramified in `E₁` and in `E₂` is
  unramified in `E₁ ⊔ E₂`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.9.1 and Corollary 3.9.3.
-/

public section

namespace TauCeti.Place

variable {k F F' : Type*} [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [IsGalois F F']

variable (F) (P : Place k F') [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]

/-- **Abhyankar's lemma** (Stichtenoth, Theorem 3.9.1): in a finite Galois extension `F' / F` with
separable residue extension at `P`, if the place `P ∩ E₁` of an intermediate field `E₁` is tame
over `F`, then for every intermediate field `E₂` the ramification index of `P ∩ (E₁ ⊔ E₂)` over
`P ∩ F` is the lcm of those of `P ∩ E₁` and `P ∩ E₂`. -/
theorem ramificationIdx_restrict_sup_eq_lcm (E₁ E₂ : IntermediateField F F')
    (h₁ : IsTame k F (P.restrict k E₁)) :
    ramificationIdx F (P.restrict k ↥(E₁ ⊔ E₂)) =
      (ramificationIdx F (P.restrict k E₁)).lcm (ramificationIdx F (P.restrict k E₂)) := by
  -- Read the ramification indices as indices in the inertia group `T = G₀(P)`.
  set T := ramificationGroup F P 0
  set V := (ramificationGroup F P 1).subgroupOf T
  set ψ : T →* (F' ≃ₐ[F] F') := (P.integers.decompositionSubgroup F).subtype.comp T.subtype
  have he (E : IntermediateField F F') :
      ramificationIdx F (P.restrict k E) = (E.fixingSubgroup.comap ψ).index := by
    rw [ramificationIdx_restrict_eq_relIndex, Subgroup.index_comap, MonoidHom.range_comp,
      Subgroup.range_subtype, show T = _ from ramificationGroup_zero F P]
  rw [he, he, he, IntermediateField.fixingSubgroup_sup, Subgroup.comap_inf]
  -- A prime `p` such that `G₁(P)` is a `p`-group and `p` does not divide `e(P ∩ E₁ ∣ P ∩ F)`.
  obtain ⟨p, hp, hV, hA⟩ : ∃ p, p.Prime ∧ IsPGroup p V ∧
      ¬ p ∣ (E₁.fixingSubgroup.comap ψ).index := by
    rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
    · -- In characteristic `p`, `G₁(P)` is a `p`-group and tameness says `p ∤ e(P ∩ E₁ ∣ P ∩ F)`.
      have : Fact (ringChar k).Prime := ⟨hp⟩
      have : CharP P.ResidueField (ringChar k) :=
        charP_of_injective_algebraMap (algebraMap k P.ResidueField).injective _
      have : CharP ((P.restrict k E₁).restrict k F).ResidueField (ringChar k) :=
        charP_of_injective_algebraMap (algebraMap k _).injective _
      refine ⟨ringChar k, hp, (isPGroup_ramificationGroup_succ F P (ringChar k) 0).of_equiv
        (Subgroup.subgroupOfEquivOfLe (ramificationGroup_antitone F P (Nat.zero_le 1))).symm, ?_⟩
      have h := ((isTame_iff_isSeparable_residueField k F _).mp h₁).2
      rwa [Ne, CharP.cast_eq_zero_iff _ (ringChar k), he] at h
    · -- In characteristic zero `G₁(P)` is trivial, and any prime `p > e(P ∩ E₁ ∣ P ∩ F)` works.
      have : CharP k 0 := hp ▸ ringChar.charP k
      have : CharZero k := CharP.charP_to_charZero k
      have : CharZero P.ResidueField :=
        charZero_of_injective_algebraMap (algebraMap k P.ResidueField).injective
      have hV : V = ⊥ := by
        simp only [V, ramificationGroup_one_eq_bot F P, Subgroup.bot_subgroupOf]
      obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes ((E₁.fixingSubgroup.comap ψ).index + 1)
      refine ⟨p, hp, hV ▸ IsPGroup.of_bot, fun h ↦ ?_⟩
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h
      omega
  have : Fact p.Prime := ⟨hp⟩
  have : V.Normal := (normal_ramificationGroup F P 1).subgroupOf T
  have : IsCyclic (T ⧸ V) := isCyclic_quotient_ramificationGroup_one F P
  exact hV.index_inf_eq_lcm hA _

/-- **Unramified in both, unramified in the compositum** (Stichtenoth, Corollary 3.9.3): in a
finite Galois extension `F' / F` with separable residue extension at `P`, if `P ∩ E₁` and `P ∩ E₂`
are unramified over `F`, then so is `P ∩ (E₁ ⊔ E₂)`. -/
theorem ramificationIdx_restrict_sup_eq_one {E₁ E₂ : IntermediateField F F'}
    (h₁ : ramificationIdx F (P.restrict k E₁) = 1) (h₂ : ramificationIdx F (P.restrict k E₂) = 1) :
    ramificationIdx F (P.restrict k ↥(E₁ ⊔ E₂)) = 1 := by
  have := isSeparable_residueField_restrict_bot (k₀ := k) (F₀ := F) (k₁ := k) (F₁ := E₁) P
  have htame : IsTame k F (P.restrict k E₁) :=
    (isTame_iff_isSeparable_residueField k F _).mpr
      ⟨‹_›, by rw [h₁, Nat.cast_one]; exact one_ne_zero⟩
  rw [ramificationIdx_restrict_sup_eq_lcm F P E₁ E₂ htame, h₁, h₂, Nat.lcm_one_left]

end TauCeti.Place
