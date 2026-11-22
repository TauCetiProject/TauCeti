/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Algebraic
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.FiniteComponent

/-!
# Unit compatibility for algebraic Hecke characters

The monomial of embedding exponents describing an algebraic Hecke character on the identity
component is trivial on a finite-index congruence subgroup of global units with all real signs
positive. Consequently its restriction to all global units has finite order: every value is a
root of unity, with a single positive exponent valid for all units. Real sign parities of the
Hecke character remain unrestricted.

On a global element the product of the infinite components equals that monomial as soon as the
element is positive at every real place where the sign parity of the character differs from the
parity of the exponent (`coe_prod_infiniteComponent_eq_embeddingCharacter_of_realParity`), in
particular on totally positive elements.

The finite-idele input is `HeckeCharacter.exists_modulus_finitePart_eq_one`, the product
formula on principal ideles is
`HeckeCharacter.prod_infiniteComponent_mul_ofFiniteIdele_unitEmbedding`, the archimedean comparison
is `HeckeCharacter.coe_prod_infiniteComponent_eq_embeddingCharacter`, and the finite-index input
is `unitsCongruenceSubgroup_finiteIndex`.

## References

* A. Weil, *Basic Number Theory*, Chapter VII, §3.
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §2.3 and §3.
-/

public section
noncomputable section

open NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields
namespace HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

/-- The monomial of a matching algebraic infinity type is trivial on a congruence subgroup of
integer units whose modulus includes every real place. This subgroup has finite index. -/
theorem exists_modulus_embeddingCharacter_eq_one (χ : HeckeCharacter K)
    (n : AlgebraicInfinityType K)
    (hn : χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n)) :
    ∃ 𝔪 : Modulus K, 𝔪.infinitePart = (narrowModulus K).infinitePart ∧
      ∀ u ∈ unitsCongruenceSubgroup 𝔪,
        n.embeddingCharacter (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) = 1 := by
  classical
  obtain ⟨𝔫, h𝔫⟩ := χ.exists_modulus_finitePart_eq_one
  let 𝔪 : Modulus K := ⟨𝔫.finitePart, 𝔫.finitePart_ne_bot, (narrowModulus K).infinitePart⟩
  have hdvd : 𝔫 ∣ 𝔪 := Modulus.dvd_iff.mpr
    ⟨dvd_refl _, fun w _ ↦ mem_narrowModulus_infinitePart w⟩
  refine ⟨𝔪, rfl, fun u hu ↦ ?_⟩
  let x : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom u
  have hx : IdeleGroup.unitEmbedding (𝓞 K) K x ∈ ideleCongruenceSubgroup 𝔪 :=
    unitEmbedding_mem_ideleCongruenceSubgroup_iff.mpr ⟨u, hu, rfl⟩
  have hfinite := h𝔫 _ (ideleCongruenceSubgroup_antitone hdvd hx)
  rw [IdeleGroup.toFiniteIdele_unitEmbedding] at hfinite
  have hpos : IsTotallyPositive (x : K) :=
    isTotallyPositive_iff.mpr fun w hw ↦
      (mem_unitsCongruenceSubgroup.mp hu).pos (mem_narrowModulus_infinitePart ⟨w, hw⟩)
  have hinf := χ.prod_infiniteComponent_mul_ofFiniteIdele_unitEmbedding x
  rw [hfinite, mul_one] at hinf
  apply Units.ext
  refine (χ.coe_prod_infiniteComponent_eq_embeddingCharacter n hn x hpos).symm.trans ?_
  simpa only [Units.coe_prod] using congrArg Units.val hinf

/-- The exact kernel of the embedding monomial on integer units has finite index. No sign
condition is imposed on these units. -/
theorem finiteIndex_embeddingCharacter_units_ker (χ : HeckeCharacter K)
    (n : AlgebraicInfinityType K)
    (hn : χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n)) :
    (n.embeddingCharacter.comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom)).ker.FiniteIndex := by
  obtain ⟨𝔪, _, h𝔪⟩ := χ.exists_modulus_embeddingCharacter_eq_one n hn
  exact Subgroup.finiteIndex_of_le (fun u hu ↦ MonoidHom.mem_ker.mpr (h𝔪 u hu))

/-- The embedding monomial restricted to all integer units is a character of finite order,
with a single positive exponent annihilating every value. -/
theorem isOfFinOrder_embeddingCharacter_units (χ : HeckeCharacter K)
    (n : AlgebraicInfinityType K)
    (hn : χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n)) :
    IsOfFinOrder (n.embeddingCharacter.comp
      (Units.map (algebraMap (𝓞 K) K).toMonoidHom)) := by
  let f := n.embeddingCharacter.comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom)
  have : f.ker.FiniteIndex := χ.finiteIndex_embeddingCharacter_units_ker n hn
  refine isOfFinOrder_iff_pow_eq_one.mpr
    ⟨f.ker.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  apply MonoidHom.ext
  intro u
  simpa only [MonoidHom.pow_apply, MonoidHom.one_apply, map_pow] using
    MonoidHom.mem_ker.mp (f.ker.pow_index_mem u)

/-- Each embedding monomial value at a global integer unit is a root of unity, including units
with negative real signs. -/
theorem isOfFinOrder_prod_embeddings_unit (χ : HeckeCharacter K)
    (n : AlgebraicInfinityType K)
    (hn : χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n))
    (u : (𝓞 K)ˣ) :
    IsOfFinOrder (∏ σ : K →+* ℂ, σ ((u : 𝓞 K) : K) ^ n σ) := by
  simpa using (Units.coeHom ℂ).isOfFinOrder
    ((MonoidHom.eval u).isOfFinOrder (χ.isOfFinOrder_embeddingCharacter_units n hn))

end HeckeCharacter
end TauCeti.GlobalNumberFields
