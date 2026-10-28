/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FiniteAbelian.Duality
public import TauCeti.NumberTheory.LocalField.Different.Hilbert
public import TauCeti.NumberTheory.LocalField.Discriminant.Basic
public import TauCeti.NumberTheory.LocalField.Herbrand.ArtinConductor
public import TauCeti.NumberTheory.LocalField.InertiaDegree

/-!
# The local conductor–discriminant formula

Let `L/K` be a finite abelian extension of nonarchimedean local fields with group `G` and lower
ramification groups `G_i`, and let `f(χ)` be the Artin conductor exponent of a character `χ` of
`G` (`TauCeti.LocalFieldsRamification.artinConductorExponent`). Serre's formula
`f(χ) · #G_0 = ∑_{i ≥ 0, χ(G_i) ≠ 1} #G_i` expresses it through the lower ramification groups.
Summing over the characters `χ : G → Mˣ` (with `M` having enough roots of unity, for instance
`M = ℂ`) and counting, for each `i`, the `#G - #G/#G_i` characters that are nontrivial on `G_i`,
Hilbert's formula `d(L/K) = ∑_{i ≥ 0} (#G_i - 1)` and `#G = e f` give the **local
conductor–discriminant formula**

`∑_χ f(χ) = f(L/K) d(L/K) = δ(L/K)`,

where `δ(L/K)` is the discriminant exponent. This is the local input to the conductor–discriminant
formula for a global abelian extension, read at the completions.

## Main results

* `TauCeti.LocalFieldsRamification.finsum_artinConductorExponent_eq_discriminantExponent`: the
  local conductor–discriminant formula `∑_χ f(χ) = δ(L/K)` for an abelian extension.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1–3 and Chapter VI, §§2–3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §11.
-/

public section
noncomputable section

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L] [IsAbelianGalois K L]
  (M : Type*) [CommMonoid M] [HasEnoughRootsOfUnity M (Monoid.exponent (L ≃ₐ[K] L))]

open scoped IsMulCommutative in
/-- **The local conductor–discriminant formula.** For a finite abelian extension `L/K` of
nonarchimedean local fields and a commutative monoid `M` with enough roots of unity (for instance
`M = ℂ`), the Artin conductor exponents of the characters `χ : Gal(L/K) →* Mˣ` add up to the
discriminant exponent: `∑_χ f(χ) = δ(L/K)`. -/
theorem finsum_artinConductorExponent_eq_discriminantExponent :
    ∑ᶠ χ : (L ≃ₐ[K] L) →* Mˣ, artinConductorExponent K L χ = discriminantExponent K L := by
  classical
  have := Fintype.ofFinite ((L ≃ₐ[K] L) →* Mˣ)
  obtain ⟨N, hN⟩ := exists_forall_lowerRamificationGroup_natCast_eq_bot K L
  -- Each `G_i` contributes `#G_i` for each of the `#G - #(G ⧸ G_i)` characters nontrivial on it.
  have hcount : ∀ i : ℕ, ∑ χ : (L ≃ₐ[K] L) →* Mˣ, (if lowerRamificationGroup K L i ≤ χ.ker then 0
      else Nat.card (lowerRamificationGroup K L i)) =
        Nat.card (L ≃ₐ[K] L) * (Nat.card (lowerRamificationGroup K L i) - 1) := fun i ↦ by
    set H := lowerRamificationGroup K L i
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul,
      ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, CommGroup.card_monoidHom_not_le_ker,
      Subgroup.card_eq_card_quotient_mul_card_subgroup H, ← Nat.mul_sub_one]
    ring
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := lowerRamificationGroup K L 0)) ?_
  rw [finsum_eq_sum_of_fintype, Finset.sum_mul,
    Finset.sum_congr rfl fun χ _ ↦ artinConductorExponent_mul_card_eq_sum_range K L χ
      ((hN _ le_rfl).trans_le bot_le), Finset.sum_comm, Finset.sum_congr rfl fun i _ ↦ hcount i,
    ← Finset.mul_sum, ← differentExponent_eq_sum_range_lowerRamificationGroup K L (hN _ le_rfl),
    discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    natCard_lowerRamificationGroup_zero, IsGalois.card_aut_eq_finrank,
    ← ramificationIndex_mul_inertiaDegree]
  ring

end TauCeti.LocalFieldsRamification
