/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Equiv
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Inertia
public import TauCeti.FieldTheory.FunctionField.Place.Extension.TameInertia
import Mathlib.FieldTheory.Normal.Closure
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Index

/-!
# Abhyankar's lemma

Let `F' / F` be a finite separable extension of function fields, `F₁` and `F₂` intermediate
fields, and `P'` a place of the compositum `F₁ F₂` lying over `P₁` in `F₁`, `P₂` in `F₂` and `P`
in `F`. If the residue field of `P` is perfect (for instance if the constant field is perfect)
and the ramification index `e(P₁ ∣ P)` is prime to the characteristic, then

`e(P' ∣ P) = lcm (e(P₁ ∣ P), e(P₂ ∣ P))`.

This controls ramification in composita, for instance in towers of function fields built by
successive composita; in particular a compositum of two extensions in which `P` has ramification
index `1` again has ramification index `1` over `P`.

The proof is group-theoretic. Embed everything in a finite Galois extension and let `I` be the
inertia group of a place `Q` above `P'`. When the residue extension at `Q` is separable, the
ramification index of `Q` over `F` is `|I|`, so the ramification index over `F` of the restriction
of `Q` to an intermediate field `E` is the index in `I` of the elements fixing `E`
(`TauCeti.Place.ramificationIdx_restrict_eq_relIndex`). The wild inertia group `I₁` is a normal
`p`-subgroup of `I` with `I / I₁` cyclic of order prime to `p`; for such a group, the index of an
intersection `A ⊓ B` is the least common multiple of the indices as soon as `[I : A]` is prime to
`p` (`Subgroup.index_inf_eq_lcm_of_isCyclic_quotient`).

## Main results

* `TauCeti.Place.ramificationIdx_restrict_sup_of_isGalois`: **Abhyankar's lemma** for
  intermediate fields of a finite Galois extension with separable residue extension.
* `TauCeti.Place.ramificationIdx_restrict_sup`: **Abhyankar's lemma** for intermediate fields of
  a finite separable extension, when the residue field of the place below is perfect (for instance
  when the constant field is perfect, by `TauCeti.Place.perfectField_residueField`).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.9.1.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter IV, Corollaries 1–4 of
  Proposition 7, for the structure of the inertia group.
-/

public section

namespace TauCeti.Place

universe u v w

variable {k : Type u} {F : Type v} {F' : Type w}
variable [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F'] [Algebra F F']
variable [IsScalarTower k F F']

section Galois

variable [FiniteDimensional F F'] [IsGalois F F'] (Q : Place k F')
variable [Algebra.IsSeparable (Q.restrict k F).ResidueField Q.ResidueField]

/-- **Abhyankar's lemma in a Galois extension** (Stichtenoth, Theorem 3.9.1). Let `E₁` and `E₂` be
intermediate fields of a finite Galois extension `F' / F` and `Q` a place of `F'` whose residue
extension over `F` is separable. If the ramification index of `Q ∩ E₁` over `F` is nonzero in `k`,
then the ramification index of `Q ∩ E₁ E₂` over `F` is the least common multiple of those of
`Q ∩ E₁` and `Q ∩ E₂`.

The hypothesis on `E₁` cannot be dropped. Over `F = 𝔽_p(x)`, the Artin–Schreier extensions
`y₁ ^ p - y₁ = x` and `y₂ ^ p - y₂ = x ^ (p + 1)` are totally ramified of degree `p` at the pole
of `x`, and so is every other subextension of degree `p` of their compositum, which is therefore
totally ramified of degree `p ^ 2` there. -/
theorem ramificationIdx_restrict_sup_of_isGalois (E₁ E₂ : IntermediateField F F')
    (h₁ : (ramificationIdx F (Q.restrict k E₁) : k) ≠ 0) :
    ramificationIdx F (Q.restrict k ↥(E₁ ⊔ E₂)) =
      Nat.lcm (ramificationIdx F (Q.restrict k E₁)) (ramificationIdx F (Q.restrict k E₂)) := by
  -- Read the ramification indices as indices of subgroups of the inertia group `G₀`.
  let ι : ramificationGroup F Q 0 →* F' ≃ₐ[F] F' :=
    (Q.integers.decompositionSubgroup F).subtype.comp (ramificationGroup F Q 0).subtype
  have hrange : ι.range = (inertiaField F Q).fixingSubgroup := by
    rw [fixingSubgroup_inertiaField, ← ramificationGroup_zero, MonoidHom.range_comp,
      Subgroup.range_subtype]
  have he (E : IntermediateField F F') :
      ramificationIdx F (Q.restrict k E) = (E.fixingSubgroup.comap ι).index := by
    rw [Subgroup.index_comap, hrange, ramificationIdx_restrict_eq_relIndex]
  rw [he, IntermediateField.fixingSubgroup_sup, Subgroup.comap_inf, he, he]
  rw [he] at h₁
  have : Finite (ramificationGroup F Q 0) := Finite.of_injective _ (Subtype.val_injective.comp
    (Subtype.val_injective : Function.Injective (Subtype.val : ramificationGroup F Q 0 → _)))
  -- The wild inertia group `G₁` is normal in `G₀`, with cyclic quotient.
  let N := (ramificationGroup F Q 1).subgroupOf (ramificationGroup F Q 0)
  have : IsCyclic (ramificationGroup F Q 0 ⧸ N) := isCyclic_quotient_ramificationGroup_one F Q
  -- Its order is a power of the residue characteristic `p`, which divides neither `[G₀ : G₁]` nor
  -- the index of the subgroup fixing `E₁`; in characteristic zero `G₁` is trivial.
  have hcop : (Nat.card N).Coprime N.index ∧
      (Nat.card N).Coprime (E₁.fixingSubgroup.comap ι).index := by
    obtain ⟨p, hp⟩ := CharP.exists Q.ResidueField
    rcases CharP.char_is_prime_or_zero Q.ResidueField p with hprime | rfl
    · have : Fact p.Prime := ⟨hprime⟩
      obtain ⟨n, hn⟩ := ((isPGroup_ramificationGroup_succ F Q p 0).comap_of_injective
        (ramificationGroup F Q 0).subtype (Subgroup.subtype_injective _)).exists_card_eq
      have hdvd : ¬ p ∣ (E₁.fixingSubgroup.comap ι).index := fun hdvd ↦ h₁ <| by
        apply (algebraMap k Q.ResidueField).injective
        rw [map_natCast, map_zero]
        exact (CharP.cast_eq_zero_iff Q.ResidueField p _).mpr hdvd
      rw [show Nat.card N = p ^ n from hn]
      exact ⟨((Nat.Prime.coprime_iff_not_dvd hprime).mpr
        (not_dvd_index_ramificationGroup_one F Q p)).pow_left n,
        ((Nat.Prime.coprime_iff_not_dvd hprime).mpr hdvd).pow_left n⟩
    · have : CharZero Q.ResidueField := CharP.charP_zero_iff_charZero _ |>.mp hp
      have : Finite (ramificationGroup F Q 1) := Finite.of_injective _
        (Subtype.val_injective.comp
          (Subtype.val_injective : Function.Injective (Subtype.val : ramificationGroup F Q 1 → _)))
      have hN : Nat.card N = 1 := by
        rw [Subgroup.card_eq_one, Subgroup.subgroupOf_eq_bot]
        rw [ramificationGroup_one_eq_bot F Q]
        exact disjoint_bot_left
      simp [hN]
  exact Subgroup.index_inf_eq_lcm_of_isCyclic_quotient N hcop.1 hcop.2 _

end Galois

section Separable

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- **Abhyankar's lemma** (Stichtenoth, Theorem 3.9.1). Let `E₁` and `E₂` be intermediate fields
of a finite separable extension `F' / F` of function fields, and `P'` a place of `F'` such that
the residue field of the place `P` below it in `F` is perfect, for instance because `k` is perfect
(`TauCeti.Place.perfectField_residueField`). If the ramification index of `P' ∩ E₁` over `P` is
nonzero in `k`, then the ramification index of `P' ∩ E₁ E₂` over `P` is the least common multiple
of those of `P' ∩ E₁` and `P' ∩ E₂`.

In particular, if `P' ∩ E₁` and `P' ∩ E₂` have ramification index `1` over `P`, then so does
`P' ∩ E₁ E₂`. -/
theorem ramificationIdx_restrict_sup (hF : IsFunctionField k F) (P' : Place k F')
    [PerfectField (P'.restrict k F).ResidueField] (E₁ E₂ : IntermediateField F F')
    (h₁ : (ramificationIdx F (P'.restrict k E₁) : k) ≠ 0) :
    ramificationIdx F (P'.restrict k ↥(E₁ ⊔ E₂)) =
      Nat.lcm (ramificationIdx F (P'.restrict k E₁)) (ramificationIdx F (P'.restrict k E₂)) := by
  -- Embed `F'` in its Galois closure `N` inside a separable closure of `F`.
  let L := separableClosure F (AlgebraicClosure F)
  let N := IntermediateField.normalClosure F F' L
  let ι : F' →ₐ[F] L := IsSepClosed.lift
  let g : F' →ₐ[F] N := ι.codRestrict N.toSubalgebra fun x ↦ ι.fieldRange_le_normalClosure ⟨x, rfl⟩
  -- Transport of places along an isomorphism over `F`.
  have htr {L : Type w} {L' : Type v} [Field L] [Field L'] [Algebra k L] [Algebra k L']
      [Algebra F L] [Algebra F L'] [IsScalarTower k F L] [IsScalarTower k F L'] (e : L ≃ₐ[F] L')
      (R : Place k L) (x : L) :
      e x ∈ (equivOfRingEquiv (RingEquiv.refl k) (e.restrictScalars k).toRingEquiv
        (e.restrictScalars k).commutes R).integers ↔ x ∈ R.integers := by
    simp [mem_integers_iff]
  -- Choose a place `Q` of `N` lying over `P'` along `g`.
  obtain ⟨Q, hQ⟩ := restrict_surjective_of_finiteDimensional
    (hF.finite_extension (E := g.fieldRange)) (hF.finite_extension (E := N))
    (equivOfRingEquiv (RingEquiv.refl k) (g.equivFieldRange.restrictScalars k).toRingEquiv
      (g.equivFieldRange.restrictScalars k).commutes P')
  have hQint (y : F') : g y ∈ Q.integers ↔ y ∈ P'.integers := by
    rw [← htr g.equivFieldRange P' y, ← hQ, mem_integers_restrict_iff,
      IntermediateField.algebraMap_apply, AlgHom.equivFieldRange_apply_coe]
  -- Restriction to an intermediate field `E` corresponds to restriction to its image `g(E)`.
  have hrestrict (E : IntermediateField F F') :
      Q.restrict k ↥(E.map g) = equivOfRingEquiv (RingEquiv.refl k)
        ((E.equivMap g).restrictScalars k).toRingEquiv ((E.equivMap g).restrictScalars k).commutes
        (P'.restrict k E) := by
    apply integers_injective
    ext x
    obtain ⟨y, rfl⟩ := (E.equivMap g).surjective x
    rw [htr, mem_integers_restrict_iff, mem_integers_restrict_iff]
    exact hQint y
  have he (E : IntermediateField F F') :
      ramificationIdx F (P'.restrict k E) = ramificationIdx F (Q.restrict k ↥(E.map g)) := by
    simp only [hrestrict, AlgEquiv.toRingEquiv_restrictScalars, ramificationIdx_equivOfRingEquiv]
  -- The residue extension of `Q` over `F` is separable, the residue field below being perfect.
  have hbelow : Q.restrict k F = P'.restrict k F := by
    apply integers_injective
    ext c
    rw [mem_integers_restrict_iff, mem_integers_restrict_iff, ← hQint, AlgHom.commutes]
  have : PerfectField (Q.restrict k F).ResidueField := hbelow ▸ ‹_›
  rw [he] at h₁
  rw [he, he, he, IntermediateField.map_sup]
  exact ramificationIdx_restrict_sup_of_isGalois Q _ _ h₁

end Separable

end TauCeti.Place
