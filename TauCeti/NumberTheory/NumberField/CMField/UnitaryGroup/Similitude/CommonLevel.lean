/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.Similitude
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CongruenceLevel.Conj

/-!
# A common level for finitely many conjugates of principal levels of unitary similitudes

Let `E` be a CM field, `n` a finite type, `GU ⊆ GL_n(𝔸_f)` the unitary similitudes with rational
multipliers (`TauCeti.unitarySimilitudes`) and `K(𝔑) = GU ∩ {g ∈ GL_n(Ô) : g ≡ 1 mod 𝔑Ô}` the
principal level of an ideal `𝔑` of `𝓞 E` (`TauCeti.similitudePrincipalLevel`).

For a nonzero ideal `𝔑`, finitely many nonzero ideals `𝔞_k` and elements `g_k ∈ GU`, there is a
nonzero ideal `𝔪` with `g_k⁻¹ K(𝔪) g_k ⊆ K(𝔑) ∩ K(𝔞_k)` for every `k`. Conjugation by `g_k ∈ GU`
preserves `GU`, so this reduces to the principal congruence levels of `GL_n(𝔸_f)`
(`IsDedekindDomain.FiniteAdeleRing.exists_forall_map_conj_principalLevel_le`) at the nonzero
ideals `𝔑 ⊓ 𝔞_k`.

Only `g_k ∈ GU` is used, so the statement covers in particular the elements of the monoid
`GU⁺ ⊆ GU` (`TauCeti.unitarySimilitudesPlus`). The ideals `𝔞_k` must be nonzero: `K(⊥)` is
trivial, while `K(𝔪)` is not for `𝔪 ≠ ⊥` and `n` nonempty.

## Main results

* `TauCeti.exists_forall_map_conj_similitudePrincipalLevel_le`: the common level `𝔪`.

## References

* the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207 (`New.Variety.exists_level_conj_mem`).
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField
open scoped NumberField.AdeleRing

namespace TauCeti

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n : Type*} [Fintype n]
  [DecidableEq n]

/-- **A common level for finitely many conjugates in `GU`.** For a nonzero ideal `𝔑` of `𝓞 E`,
finitely many nonzero ideals `𝔞_k` and unitary similitudes `g_k ∈ GU`, there is a nonzero ideal
`𝔪` with `g_k⁻¹ K(𝔪) g_k ≤ K(𝔑) ⊓ K(𝔞_k)` for every `k`. -/
theorem exists_forall_map_conj_similitudePrincipalLevel_le {κ : Type*} [Finite κ]
    {𝔑 : Ideal (𝓞 E)} (h𝔑 : 𝔑 ≠ ⊥) {𝔞 : κ → Ideal (𝓞 E)} (h𝔞 : ∀ k, 𝔞 k ≠ ⊥)
    {g : κ → GL n 𝔸ᶠ[E]} (hg : ∀ k, g k ∈ unitarySimilitudes E n) :
    ∃ 𝔪 : Ideal (𝓞 E), 𝔪 ≠ ⊥ ∧ ∀ k,
      (similitudePrincipalLevel E n 𝔪).map (MulAut.conj (g k)⁻¹).toMonoidHom ≤
        similitudePrincipalLevel E n 𝔑 ⊓ similitudePrincipalLevel E n (𝔞 k) := by
  -- `𝔑 ⊓ 𝔞_k ⊇ 𝔑 𝔞_k` is nonzero.
  have hN k : 𝔑 ⊓ 𝔞 k ≠ ⊥ :=
    ne_bot_of_le_ne_bot (Ideal.mul_eq_bot.not.2 (not_or.2 ⟨h𝔑, h𝔞 k⟩)) Ideal.mul_le_inf
  obtain ⟨𝔪, h𝔪, hle⟩ := exists_forall_map_conj_principalLevel_le E g hN
  refine ⟨𝔪, h𝔪, fun k ↦ ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_similitudePrincipalLevel_iff] at hx
  have hGU : (MulAut.conj (g k)⁻¹).toMonoidHom x ∈ unitarySimilitudes E n := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact mul_mem (mul_mem (inv_mem (hg k)) hx.1) (hg k)
  have hK := hle k ⟨x, hx.2, rfl⟩
  exact ⟨mem_similitudePrincipalLevel_iff.2 ⟨hGU, principalLevel_mono E n inf_le_left hK⟩,
    mem_similitudePrincipalLevel_iff.2 ⟨hGU, principalLevel_mono E n inf_le_right hK⟩⟩

end TauCeti
