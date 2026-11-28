/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.AppellHumbert.Translation

/-!
# Character-weighted sums of normalised translates

Let `D` be an Appell–Humbert datum for a subgroup `L` of a complex normed space `V`, and `b` a
continuous complex linear endomorphism with `E (b u, w) + E (u, b w) = E (u, w)` and `E (b l, m)`
an integer for `l, m ∈ L`, so that the normalised translations `N_x = D.normalizedTranslate b x` by
points of `L` compose without a phase
(`TauCeti.AppellHumbertData.normalizedTranslate_normalizedTranslate_of_mem`). Let `A` be an
additive endomorphism of `V` and `A⁻¹ L = L.comap A` the preimage of `L`.

For a function `f` fixed by every `N_{A l}`, `l ∈ L`:

* `N_{A k} f = N_{A k'} f` whenever `A k, A k' ∈ L` and `k - k' ∈ L`
  (`TauCeti.AppellHumbertData.normalizedTranslate_map_eq_of_sub_mem`);
* for a character `ξ` of `A⁻¹ L ⧸ (A⁻¹ L ∩ L)`, the character-weighted `finsum`
  `s = ∑ᶠ_{z} ξ (-z) N_{A k (z)} f` over that quotient, for any choice of representatives `k (z)`,
  satisfies `N_{A y} s = ξ (y) s` for `y ∈ A⁻¹ L`, so it is an eigenvector when it is nonzero
  (`TauCeti.AppellHumbertData.normalizedTranslate_finsum_eq_smul`). The `finsum` is the ordinary
  weighted sum when the quotient is finite and `0` when it is infinite. When `A L ⊆ L`, the
  quotient is `A⁻¹ L ⧸ L`.

For a Hermitian action, `b = F (β)` and `A = F (a)`
(`TauCeti.IsHermitianAction.normalizedTranslate_finsum_eq_smul`).

## Main results

* `TauCeti.AppellHumbertData.normalizedTranslate_map_eq_of_sub_mem`: independence of
  representatives.
* `TauCeti.AppellHumbertData.normalizedTranslate_finsum_eq_smul`: the character-weighted `finsum`
  of translates transforms by `ξ`.

## References

* These statements appear for Hermitian actions as
  `New.ThetaTori.IsHermitianAction.normShift_sum_eq_char_smul` in
  `Lib/Shimura/GoodReduction/GaussSums` of the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

namespace TauCeti.AppellHumbertData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}
  {D : AppellHumbertData L} {b : V →L[ℂ] V}
  (hadj : ∀ u w, D.riemannForm (b u) w + D.riemannForm u (b w) = D.riemannForm u w)
  (hint : ∀ l m : L, ∃ n : ℤ, D.riemannForm (b l) m = n) {A : V →ₗ[ℤ] V} {f : V → ℂ}

include hadj hint in
/-- **The translate of an invariant function does not depend on representatives.** Let `b` be a
continuous complex linear endomorphism with the adjoint-half law `E (b u, w) + E (u, b w) =
E (u, w)` and `E (b l, m)` integral on `L`, and let `f` be fixed by the normalised translations
`N_{A l}`, `l ∈ L`. Then `N_{A k} f = N_{A k'} f` whenever `A k, A k' ∈ L` and `k - k' ∈ L`. -/
theorem normalizedTranslate_map_eq_of_sub_mem
    (hf : ∀ l ∈ L, D.normalizedTranslate b (A l) f = f) {k k' : V} (hk : A k ∈ L)
    (hk' : A k' ∈ L) (hkk' : k - k' ∈ L) :
    D.normalizedTranslate b (A k) f = D.normalizedTranslate b (A k') f := by
  have hA : A (k - k') ∈ L := by
    rw [map_sub]
    exact L.sub_mem hk hk'
  have := normalizedTranslate_normalizedTranslate_of_mem hadj hint hk' hA f
  rw [hf _ hkk', ← map_add, add_sub_cancel] at this
  exact this.symm

include hadj hint in
/-- One term of the weighted sum: `N_{A y} (ξ (-z) N_{A k z} f)` is
`ξ (y) ξ (-(z + y)) N_{A k (z + y)} f` for a choice `k` of representatives. -/
private theorem normalizedTranslate_smul_normalizedTranslate_rep
    (hf : ∀ l ∈ L, D.normalizedTranslate b (A l) f = f)
    (ξ : AddChar (L.comap A ⧸ L.submoduleOf (L.comap A)) ℂ)
    (k : L.comap A ⧸ L.submoduleOf (L.comap A) → L.comap A)
    (hk : ∀ z, Submodule.Quotient.mk (k z) = z) (y : L.comap A)
    (z : L.comap A ⧸ L.submoduleOf (L.comap A)) :
    D.normalizedTranslate b (A y) (ξ (-z) • D.normalizedTranslate b (A (k z)) f) =
      ξ (Submodule.Quotient.mk y) • ξ (-(z + Submodule.Quotient.mk y)) •
        D.normalizedTranslate b (A (k (z + Submodule.Quotient.mk y))) f := by
  have hsub : (y : V) + k z - k (z + Submodule.Quotient.mk y) ∈ L := by
    have h1 : Submodule.Quotient.mk (p := L.submoduleOf _) (k z + y) =
        Submodule.Quotient.mk (k (z + Submodule.Quotient.mk y)) := by
      rw [Submodule.Quotient.mk_add, hk, hk]
    simpa [Submodule.submoduleOf, add_comm] using (Submodule.Quotient.eq _).mp h1
  -- A point `x` of the preimage `A⁻¹ L` has `A x ∈ L`.
  have hmem (x : L.comap A) : A x ∈ L := Submodule.mem_comap.mp x.property
  have hyk : A ((y : V) + k z) ∈ L := by
    rw [map_add]
    exact L.add_mem (hmem y) (hmem (k z))
  have hchar : ξ (-z) = ξ (Submodule.Quotient.mk y) * ξ (-(z + Submodule.Quotient.mk y)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    abel
  rw [map_smul, normalizedTranslate_normalizedTranslate_of_mem hadj hint (hmem y) (hmem (k z)),
    ← map_add, normalizedTranslate_map_eq_of_sub_mem hadj hint hf hyk (hmem _) hsub, hchar,
    smul_smul]

include hadj hint in
/-- **The character-weighted sum of translates transforms by the character.** Let `b` be a
continuous complex linear endomorphism with the adjoint-half law `E (b u, w) + E (u, b w) =
E (u, w)` and `E (b l, m)` integral on `L`, let `A` be additive with preimage
`A⁻¹ L = {y : A y ∈ L}`, let `f` be fixed by the normalised translations `N_{A l}`, `l ∈ L`, and
`ξ` a character of `A⁻¹ L ⧸ (A⁻¹ L ∩ L)`. Then the character-weighted `finsum`
`s = ∑ᶠ_{z} ξ (-z) N_{A k (z)} f`, for any choice `k (z) ∈ A⁻¹ L` of representatives (the terms do
not depend on it, `TauCeti.AppellHumbertData.normalizedTranslate_map_eq_of_sub_mem`), satisfies
`N_{A y} s = ξ (y) s` for every `y ∈ A⁻¹ L`, so `s` is an eigenvector when it is nonzero. The
`finsum` is the ordinary weighted sum when the quotient is finite and `0` when it is infinite. -/
theorem normalizedTranslate_finsum_eq_smul
    (hf : ∀ l ∈ L, D.normalizedTranslate b (A l) f = f)
    (ξ : AddChar (L.comap A ⧸ L.submoduleOf (L.comap A)) ℂ)
    (k : L.comap A ⧸ L.submoduleOf (L.comap A) → L.comap A)
    (hk : ∀ z, Submodule.Quotient.mk (k z) = z) (y : L.comap A) :
    D.normalizedTranslate b (A y) (∑ᶠ z, ξ (-z) • D.normalizedTranslate b (A (k z)) f) =
      ξ (Submodule.Quotient.mk y) • ∑ᶠ z, ξ (-z) • D.normalizedTranslate b (A (k z)) f := by
  have hmap := (D.normalizedTranslate b (A y)).toAddMonoidHom.map_finsum_of_injective
    (normalizedTranslate_injective b _) fun z ↦ ξ (-z) • D.normalizedTranslate b (A (k z)) f
  rw [LinearMap.toAddMonoidHom_coe] at hmap
  rw [hmap, smul_finsum]
  conv_rhs => rw [← finsum_comp_equiv (Equiv.addRight (Submodule.Quotient.mk y))]
  exact finsum_congr fun z ↦
    normalizedTranslate_smul_normalizedTranslate_rep hadj hint hf ξ k hk y z

end TauCeti.AppellHumbertData
