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

The finite-idele input is `HeckeCharacter.exists_modulus_finitePart_eq_one`; the finite-index
input is `unitsCongruenceSubgroup_finiteIndex`. The comparison at infinity uses the local character
classification and groups the complex embeddings into the fibers of `InfinitePlace.mk`, as in
the signed norm formula in `TauCeti.NumberTheory.NumberField.TotallyPositive`.

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

/-- At a real place, the component of `χ` at `x : Kˣ` equals the monomial of an algebraic
infinity type `n` with `χ.infinityType = n + e`, twisted by `sgn(τ_w x) ^ (e w).val`. -/
theorem coe_infiniteComponent_real_of_eq_add (χ : HeckeCharacter K) (n : AlgebraicInfinityType K)
    (e : FiniteOrderInfinityType K)
    (hn : χ.infinityType = AlgebraicInfinityType.toContinuous n +
      FiniteOrderInfinityType.toContinuous e)
    (w : {w : InfinitePlace K // w.IsReal}) (x : Kˣ) :
    (χ.infiniteComponent w.val (Units.map (algebraMap K w.val.Completion).toMonoidHom x) : ℂ) =
      w.val.embedding (x : K) ^ n w.val.embedding *
        (SignType.sign (InfinitePlace.embedding_of_isReal w.property (x : K)) : ℂ) ^
          (e w).val := by
  rw [infiniteComponent_map_algebraMap_eq_realComponent, realComponent_eq, hn]
  simp only [ContinuousInfinityType.add_realExponent, ContinuousInfinityType.add_realParity,
    Pi.add_apply, AlgebraicInfinityType.toContinuous_realExponent,
    AlgebraicInfinityType.toContinuous_realParity,
    FiniteOrderInfinityType.toContinuous_realExponent,
    FiniteOrderInfinityType.toContinuous_realParity, add_zero]
  have hsplit : realUnitsCharacter (n w.val.embedding : ℂ)
        ((n w.val.embedding : ZMod 2) + e w) =
      realUnitsCharacter (n w.val.embedding : ℂ) (n w.val.embedding : ZMod 2) *
        realUnitsCharacter 0 (e w) := by
    rw [← realUnitsCharacter_add, add_zero]
  rw [hsplit, ContinuousMonoidHom.mul_apply, Units.val_mul, coe_realUnitsCharacter_intCast,
    realUnitsCharacter_zero_left]
  simp only [ContinuousMonoidHom.pow_apply, Units.val_pow_eq_pow_val, coe_realSignCharacter_apply,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    InfinitePlace.embedding_of_isReal_apply]

/-- At a real place, the component of `χ` agrees with the monomial of an algebraic infinity type
`n` with `χ.infinityType = n + e`, provided the sign twist `e` vanishes there or `x` is positive
there. -/
private theorem coe_infiniteComponent_real (χ : HeckeCharacter K) (n : AlgebraicInfinityType K)
    (e : FiniteOrderInfinityType K)
    (hn : χ.infinityType = AlgebraicInfinityType.toContinuous n +
      FiniteOrderInfinityType.toContinuous e)
    (w : {w : InfinitePlace K // w.IsReal}) (x : Kˣ)
    (hx : e w = 0 ∨ 0 < InfinitePlace.embedding_of_isReal w.property (x : K)) :
    (χ.infiniteComponent w.val (Units.map (algebraMap K w.val.Completion).toMonoidHom x) : ℂ) =
      w.val.embedding (x : K) ^ n w.val.embedding := by
  rw [coe_infiniteComponent_real_of_eq_add χ n e hn w x]
  rcases hx with he | hx
  · simp [he]
  · simp [sign_pos hx]

/-- At a complex place, the component of `χ` at `x : Kˣ` equals the product of the two conjugate
algebraic powers of an algebraic infinity type `n` with `χ.infinityType = n + e`. -/
theorem coe_infiniteComponent_complex (χ : HeckeCharacter K)
    (n : AlgebraicInfinityType K)
    (e : FiniteOrderInfinityType K)
    (hn : χ.infinityType = AlgebraicInfinityType.toContinuous n +
      FiniteOrderInfinityType.toContinuous e)
    (w : {w : InfinitePlace K // w.IsComplex}) (x : Kˣ) :
    (χ.infiniteComponent w.val (Units.map (algebraMap K w.val.Completion).toMonoidHom x) : ℂ) =
      w.val.embedding (x : K) ^ n w.val.embedding *
        ComplexEmbedding.conjugate w.val.embedding (x : K) ^
          n (ComplexEmbedding.conjugate w.val.embedding) := by
  rw [infiniteComponent_map_algebraMap_eq_complexComponent, complexComponent_eq, hn]
  simp only [ContinuousInfinityType.add_complexExponent, Pi.add_apply,
    AlgebraicInfinityType.toContinuous_complexExponent,
    FiniteOrderInfinityType.toContinuous_complexExponent, add_zero,
    ContinuousInfinityType.add_complexAngularFrequency,
    AlgebraicInfinityType.toContinuous_complexAngularFrequency,
    FiniteOrderInfinityType.toContinuous_complexAngularFrequency]
  simpa [ComplexEmbedding.conjugate_coe_eq] using
    coe_complexUnitsCharacter_intCast (n w.val.embedding)
      (n (ComplexEmbedding.conjugate w.val.embedding)) (Units.map w.val.embedding.toMonoidHom x)

/-- For every `x : Kˣ`, the product of the infinite components of `χ` equals the embedding
monomial of a matching algebraic infinity type `n` multiplied by the real sign twists
`sgn(τ_w x) ^ (χ.realParity w - n_w)` over any finset `S` of real places containing all real
places where the parities differ. -/
theorem coe_prod_infiniteComponent_eq_embeddingCharacter_mul_sign (χ : HeckeCharacter K)
    (n : AlgebraicInfinityType K)
    (hn : χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n))
    (S : Finset {w : InfinitePlace K // w.IsReal})
    (hS : ∀ w : {w : InfinitePlace K // w.IsReal},
      χ.infinityType.realParity w ≠ (AlgebraicInfinityType.toContinuous n).realParity w → w ∈ S)
    (x : Kˣ) :
    ((∏ w : InfinitePlace K,
      χ.infiniteComponent w (Units.map (algebraMap K w.Completion).toMonoidHom x)) : ℂ) =
      (n.embeddingCharacter x : ℂ) *
        ∏ w ∈ S,
          (SignType.sign (InfinitePlace.embedding_of_isReal w.property (x : K)) : ℂ) ^
            (χ.infinityType.realParity w -
              (AlgebraicInfinityType.toContinuous n).realParity w).val := by
  classical
  obtain ⟨e, he⟩ :=
    (ContinuousInfinityType.agreesOnIdentityComponent_iff_exists_finiteOrderInfinityType
      χ.infinityType (AlgebraicInfinityType.toContinuous n)).mp hn
  have he_eq (w : {w : InfinitePlace K // w.IsReal}) :
      χ.infinityType.realParity w - (AlgebraicInfinityType.toContinuous n).realParity w = e w := by
    simp [he]
  have hsign :
      (∏ w ∈ S,
        (SignType.sign (InfinitePlace.embedding_of_isReal w.property (x : K)) : ℂ) ^
          (χ.infinityType.realParity w -
            (AlgebraicInfinityType.toContinuous n).realParity w).val) =
      ∏ w : InfinitePlace K,
        if hw : w.IsReal then
          (SignType.sign (InfinitePlace.embedding_of_isReal hw (x : K)) : ℂ) ^
            (e ⟨w, hw⟩).val
        else 1 := by
    simp_rw [he_eq]
    symm
    rw [Finset.prod_dite, Finset.prod_const_one, mul_one]
    refine (Finset.prod_bij_ne_one
      (fun w _ _ ↦ ⟨w.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.property⟩⟩)
      (fun _ _ _ ↦ Finset.mem_univ _)
      (fun _ _ _ _ _ _ h ↦ Subtype.ext (Subtype.mk.inj h))
      (fun w _ hne ↦ ?_) (fun _ _ _ ↦ rfl)).symm
    refine ⟨⟨w.val, (Finset.mem_filter.mp w.property).2⟩, ?_, fun h ↦ hne h, rfl⟩
    by_contra hnot
    apply hne
    have hpar : χ.infinityType.realParity ⟨w.val, (Finset.mem_filter.mp w.property).2⟩ =
        (AlgebraicInfinityType.toContinuous n).realParity
          ⟨w.val, (Finset.mem_filter.mp w.property).2⟩ :=
      not_imp_comm.mp (hS _) hnot
    have he0 : e ⟨w.val, (Finset.mem_filter.mp w.property).2⟩ = 0 := by
      rw [← he_eq, hpar, sub_self]
    simp [he0]
  rw [AlgebraicInfinityType.coe_embeddingCharacter_apply, hsign,
    ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  by_cases hw : w.IsReal
  · have hfiber : (Finset.univ.filter fun σ : K →+* ℂ ↦ InfinitePlace.mk σ = w) =
        {w.embedding} := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      have h := InfinitePlace.mk_eq_iff (φ := w.embedding) (ψ := σ)
      rw [InfinitePlace.mk_embedding, InfinitePlace.conjugate_embedding_eq_of_isReal hw,
        or_self] at h
      simpa only [eq_comm] using h
    rw [hfiber, Finset.prod_singleton, dite_eq_left hw]
    exact coe_infiniteComponent_real_of_eq_add χ n e he ⟨w, hw⟩ x
  · have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h ↦
      hw (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
    have hfiber : (Finset.univ.filter fun σ : K →+* ℂ ↦ InfinitePlace.mk σ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      have h := InfinitePlace.mk_eq_iff (φ := w.embedding) (ψ := σ)
      rw [InfinitePlace.mk_embedding] at h
      simpa only [eq_comm] using h
    rw [hfiber, Finset.prod_pair hne, dite_eq_right hw, mul_one]
    exact coe_infiniteComponent_complex χ n e he
      ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩ x

/-- The product of the infinite components of `χ` at `x` is exactly the monomial of an algebraic
infinity type `n` matching the character on the identity component, provided `x` is positive at
every real place where the sign parity of `χ` differs from the parity of `n`. -/
theorem coe_prod_infiniteComponent_eq_embeddingCharacter_of_realParity (χ : HeckeCharacter K)
    (n : AlgebraicInfinityType K)
    (hn : χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n))
    (x : Kˣ) (hx : ∀ w : {w : InfinitePlace K // w.IsReal},
      χ.infinityType.realParity w ≠ (AlgebraicInfinityType.toContinuous n).realParity w →
        0 < InfinitePlace.embedding_of_isReal w.property (x : K)) :
    ((∏ w : InfinitePlace K,
      χ.infiniteComponent w (Units.map (algebraMap K w.Completion).toMonoidHom x)) : ℂ) =
      (n.embeddingCharacter x : ℂ) := by
  classical
  rw [coe_prod_infiniteComponent_eq_embeddingCharacter_mul_sign χ n hn
    Finset.univ (fun w _ ↦ Finset.mem_univ w) x]
  have h1 :
      (∏ w : {w : InfinitePlace K // w.IsReal},
        (SignType.sign (InfinitePlace.embedding_of_isReal w.property (x : K)) : ℂ) ^
          (χ.infinityType.realParity w -
            (AlgebraicInfinityType.toContinuous n).realParity w).val) = 1 :=
    Finset.prod_eq_one fun w _ ↦ by
      by_cases hpar :
          χ.infinityType.realParity w = (AlgebraicInfinityType.toContinuous n).realParity w
      · simp [hpar]
      · simp [sign_pos (hx w hpar)]
  rw [h1, mul_one]

/-- On totally positive global elements, the product of the infinite components is exactly the
monomial of any algebraic infinity type matching the character on the identity component. -/
theorem coe_prod_infiniteComponent_eq_embeddingCharacter (χ : HeckeCharacter K)
    (n : AlgebraicInfinityType K)
    (hn : χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n))
    (x : Kˣ) (hx : IsTotallyPositive (x : K)) :
    ((∏ w : InfinitePlace K,
      χ.infiniteComponent w (Units.map (algebraMap K w.Completion).toMonoidHom x)) : ℂ) =
      (n.embeddingCharacter x : ℂ) :=
  χ.coe_prod_infiniteComponent_eq_embeddingCharacter_of_realParity n hn x fun w _ ↦
    (isTotallyPositive_iff.mp hx) w.val w.property

/-- **Product formula for a Hecke character on a principal idele.** For `x : Kˣ`, the product of
the infinite components of `χ` at `x` times `χ` evaluated on the diagonal finite idele of `x` is
`1`. -/
theorem prod_infiniteComponent_mul_ofFiniteIdele_unitEmbedding (χ : HeckeCharacter K) (x : Kˣ) :
    (∏ w : InfinitePlace K,
        χ.infiniteComponent w (Units.map (algebraMap K w.Completion).toMonoidHom x)) *
      χ (QuotientGroup.mk
        (IdeleGroup.ofFiniteIdele (𝓞 K) K
          (IsDedekindDomain.FiniteAdeleRing.unitEmbedding (𝓞 K) K x))) = 1 := by
  have hprincipal :
      (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 K) K x) : IdeleClassGroup (𝓞 K) K) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
  have hsplit := congrArg (fun z : IdeleGroup (𝓞 K) K ↦ χ (QuotientGroup.mk z))
    (IdeleGroup.prod_ofCompletion_mul_ofFiniteIdele (IdeleGroup.unitEmbedding (𝓞 K) K x))
  rw [QuotientGroup.mk_mul, map_mul, hprincipal, map_one,
    QuotientGroup.mk_prod, map_prod, IdeleGroup.toFiniteIdele_unitEmbedding] at hsplit
  simpa only [infiniteComponent_apply, IdeleClassGroup.ofCompletion_apply,
    InfinitePlace.ideleInfiniteCoord_unitEmbedding] using hsplit

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
