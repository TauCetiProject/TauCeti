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

open NumberField NumberField.InfinitePlace.Completion
open scoped NumberField

namespace TauCeti.GlobalNumberFields
namespace HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

private theorem coe_infiniteComponent_real (χ : HeckeCharacter K) (n : AlgebraicInfinityType K)
    (e : FiniteOrderInfinityType K)
    (hn : χ.infinityType = AlgebraicInfinityType.toContinuous n +
      FiniteOrderInfinityType.toContinuous e)
    (w : {w : InfinitePlace K // w.IsReal}) (x : Kˣ)
    (hx : 0 < InfinitePlace.embedding_of_isReal w.2 (x : K)) :
    (χ.infiniteComponent w.1 (Units.map (algebraMap K w.1.Completion).toMonoidHom x) : ℂ) =
      w.1.embedding (x : K) ^ n w.1.embedding := by
  have htransport :
      χ.infiniteComponent w.1 (Units.map (algebraMap K w.1.Completion).toMonoidHom x) =
        χ.realComponent w (Units.map (InfinitePlace.embedding_of_isReal w.2).toMonoidHom x) := by
    rw [realComponent_apply]
    congr 1
    apply (Units.mapContinuousMulEquiv (continuousMulEquivRealOfIsReal w.2)).injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    apply Units.ext
    exact (continuousMulEquivRealOfIsReal_apply w.2 _).trans
      (by simp [InfinitePlace.Completion.algebraMap_apply])
  rw [htransport, realComponent_eq, coe_realUnitsCharacter_apply,
    hn]
  simp only [ContinuousInfinityType.add_realExponent, Pi.add_apply,
    AlgebraicInfinityType.toContinuous_realExponent,
    FiniteOrderInfinityType.toContinuous_realExponent, add_zero]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  rw [abs_of_pos hx, sign_pos hx]
  simp only [SignType.coe_one, one_pow, mul_one, Complex.cpow_intCast]
  rw [InfinitePlace.embedding_of_isReal_apply]

private theorem coe_infiniteComponent_complex (χ : HeckeCharacter K)
    (n : AlgebraicInfinityType K)
    (e : FiniteOrderInfinityType K)
    (hn : χ.infinityType = AlgebraicInfinityType.toContinuous n +
      FiniteOrderInfinityType.toContinuous e)
    (w : {w : InfinitePlace K // w.IsComplex}) (x : Kˣ) :
    (χ.infiniteComponent w.1 (Units.map (algebraMap K w.1.Completion).toMonoidHom x) : ℂ) =
      w.1.embedding (x : K) ^ n w.1.embedding *
        ComplexEmbedding.conjugate w.1.embedding (x : K) ^
          n (ComplexEmbedding.conjugate w.1.embedding) := by
  have htransport :
      χ.infiniteComponent w.1 (Units.map (algebraMap K w.1.Completion).toMonoidHom x) =
        χ.complexComponent w (Units.map w.1.embedding.toMonoidHom x) := by
    rw [complexComponent_apply]
    congr 1
    apply (Units.mapContinuousMulEquiv (continuousMulEquivComplexOfIsComplex w.2)).injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    apply Units.ext
    exact (continuousMulEquivComplexOfIsComplex_apply w.2 _).trans
      (by simp [InfinitePlace.Completion.algebraMap_apply])
  rw [htransport, complexComponent_eq, hn]
  simp only [ContinuousInfinityType.add_complexExponent, Pi.add_apply,
    AlgebraicInfinityType.toContinuous_complexExponent,
    FiniteOrderInfinityType.toContinuous_complexExponent, add_zero,
    ContinuousInfinityType.add_complexAngularFrequency,
    AlgebraicInfinityType.toContinuous_complexAngularFrequency,
    FiniteOrderInfinityType.toContinuous_complexAngularFrequency]
  simpa [ComplexEmbedding.conjugate_coe_eq] using
    coe_complexUnitsCharacter_intCast (n w.1.embedding)
      (n (ComplexEmbedding.conjugate w.1.embedding)) (Units.map w.1.embedding.toMonoidHom x)

/-- On totally positive global elements, the product of the infinite components is exactly the
monomial of any algebraic infinity type matching the character on the identity component. -/
theorem coe_prod_infiniteComponent_eq_embeddingCharacter (χ : HeckeCharacter K)
    (n : AlgebraicInfinityType K)
    (hn : χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n))
    (x : Kˣ) (hx : IsTotallyPositive (x : K)) :
    ((∏ w : InfinitePlace K,
      χ.infiniteComponent w (Units.map (algebraMap K w.Completion).toMonoidHom x)) : ℂ) =
      (n.embeddingCharacter x : ℂ) := by
  classical
  obtain ⟨e, he⟩ :=
    (ContinuousInfinityType.agreesOnIdentityComponent_iff_exists_finiteOrderInfinityType
      χ.infinityType (AlgebraicInfinityType.toContinuous n)).mp hn
  rw [AlgebraicInfinityType.coe_embeddingCharacter_apply,
    ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk]
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
    rw [hfiber, Finset.prod_singleton]
    exact coe_infiniteComponent_real χ n e he ⟨w, hw⟩ x ((isTotallyPositive_iff.mp hx) w hw)
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
    rw [hfiber, Finset.prod_pair hne]
    exact coe_infiniteComponent_complex χ n e he
      ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩ x

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
  have hpos : IsTotallyPositive (x : K) :=
    isTotallyPositive_iff.mpr fun w hw ↦
      (mem_unitsCongruenceSubgroup.mp hu).pos (mem_narrowModulus_infinitePart ⟨w, hw⟩)
  have hprincipal :
      (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 K) K x) : IdeleClassGroup (𝓞 K) K) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
  have hsplit := congrArg (fun z : IdeleGroup (𝓞 K) K ↦ χ (QuotientGroup.mk z))
    (IdeleGroup.prod_ofCompletion_mul_ofFiniteIdele (IdeleGroup.unitEmbedding (𝓞 K) K x))
  rw [QuotientGroup.mk_mul, map_mul, hfinite, mul_one, hprincipal, map_one,
    QuotientGroup.mk_prod, map_prod] at hsplit
  have hinf : (∏ w : InfinitePlace K,
      χ.infiniteComponent w (Units.map (algebraMap K w.Completion).toMonoidHom x)) = 1 := by
    simpa only [infiniteComponent_apply, IdeleClassGroup.ofCompletion_apply,
      InfinitePlace.ideleInfiniteCoord_unitEmbedding] using hsplit
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
