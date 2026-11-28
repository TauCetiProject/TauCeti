/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.Frobenius
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Splitting
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
import TauCeti.FieldTheory.Galois.Basic
import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Index
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Galois

/-!
# Restriction of splitting characters to the maximal real subfield

A splitting character is trivial on relative norms. A real idele with just one negative
infinite component has character value `-1`. The norm index theorem then identifies the
restriction with the quadratic character of the CM extension. At a finite unramified place
of the real field, the Artin symbol computes the value on an extended prime idele class.

The restriction argument follows `New.Cohomology.upsilon_eq_quadraticIdeleChar` in
`grh/src/Lib/ClassField/Global/CMSplittingCharacters.lean` of [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh
-/

public section

open IsDedekindDomain NumberField NumberField.IsCMField
open scoped AdeleGaloisAction

namespace TauCeti.GlobalNumberFields.HeckeCharacter.IsSplitting

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {Φ : CMType E} {υ : HeckeCharacter E}

local notation "F" => maximalRealSubfield E

/-- Splitting characters are trivial on the relative idele-class norms, viewed in the CM field. -/
theorem apply_ideleClassExtension_ideleClassNormMap (hυ : υ.IsSplitting Φ)
    (c : IdeleClassGroup (𝓞 E) E) : υ (ideleClassExtension F E (ideleClassNormMap F E c)) = 1 := by
  classical
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  rw [ideleClassExtension_ideleClassNormMap,
    Algebra.IsQuadraticExtension.univ_eq_pair F E (complexConj_ne_one E),
    Finset.prod_pair (complexConj_ne_one E).symm, ← idele_smul_def, ← idele_smul_def, one_smul,
    ← ideleClass_smul_mk]
  exact hυ.apply_mul_conj _

/-- The idele with component `-1` at one real place and `1` elsewhere has value `-1` under the
restriction of a splitting character to the maximal real subfield. -/
theorem apply_ideleClassExtension_ofCompletion_neg_one (hυ : υ.IsSplitting Φ)
    (v : InfinitePlace F) :
    υ (ideleClassExtension F E (IdeleClassGroup.ofCompletion (𝓞 F) F v (-1))) = -1 := by
  obtain ⟨w, rfl⟩ := (equivInfinitePlace E).surjective v
  rw [equivInfinitePlace_apply]
  have heq (u : InfinitePlace E)
      (h : u.comap (algebraMap F E) = w.comap (algebraMap F E)) : u = w :=
    (equivInfinitePlace E).injective (by simpa only [equivInfinitePlace_apply] using h)
  have hext : ideleExtension F E
      (IdeleGroup.ofCompletion (𝓞 F) F (w.comap (algebraMap F E)) (-1)) =
      IdeleGroup.ofCompletion (𝓞 E) E w (-1) := by
    refine IdeleGroup.ext (fun u ↦ ?_) (fun u ↦ ?_)
    · rw [ideleInfiniteCoord_ideleExtension]
      by_cases hu : u = w
      · subst u
        rw [InfinitePlace.ideleInfiniteCoord_ofCompletion_self,
          InfinitePlace.ideleInfiniteCoord_ofCompletion_self]
        apply Units.ext
        simp
      · rw [InfinitePlace.ideleInfiniteCoord_ofCompletion_of_ne _ hu,
          InfinitePlace.ideleInfiniteCoord_ofCompletion_of_ne _
            (fun h ↦ hu (heq u h)), map_one]
    · simp
  have hχ : υ.infiniteComponent w (-1) = -1 := by
    apply Units.ext
    rw [hυ.infiniteComponent_apply]
    norm_num [Units.val_neg]
  simpa only [HeckeCharacter.infiniteComponent_apply, IdeleClassGroup.ofCompletion_apply,
    ideleClassExtension_mk, hext] using hχ

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L]
  {Ψ : CMType L} {χ : HeckeCharacter L}

local notation "L⁺" => maximalRealSubfield L

open scoped Classical in
/-- On ideles extended from the maximal real subfield, a splitting character is the quadratic
norm character: its value is `1` on the idele-class norm group and `-1` on the other coset,
independently of the chosen CM type. -/
theorem apply_ideleClassExtension_eq_ite (hχ : χ.IsSplitting Ψ) (c : IdeleClassGroup (𝓞 L⁺) L⁺) :
    χ (ideleClassExtension L⁺ L c) =
      if c ∈ (ideleClassNormMap L⁺ L).range then 1 else -1 := by
  classical
  let N := (ideleClassNormMap L⁺ L).range
  have idx : N.index = 2 := ClassFieldTheory.index_range_ideleClassNormMap_eq_two L⁺ L
  have hN (z : IdeleClassGroup (𝓞 L⁺) L⁺) (hz : z ∈ N) : χ (ideleClassExtension L⁺ L z) = 1 := by
    obtain ⟨y, rfl⟩ := hz
    exact hχ.apply_ideleClassExtension_ideleClassNormMap y
  by_cases hc : c ∈ N
  · rw [ite_eq_left hc, hN c hc]
  · rw [ite_eq_right hc]
    let v : InfinitePlace L⁺ := Classical.ofNonempty
    let z := IdeleClassGroup.ofCompletion (𝓞 L⁺) L⁺ v (-1)
    have hz : χ (ideleClassExtension L⁺ L z) = -1 :=
      hχ.apply_ideleClassExtension_ofCompletion_neg_one v
    have hzN : z ∉ N := fun h ↦ by simpa [hz] using hN z h
    obtain ⟨a, _, hcoset⟩ := N.index_eq_two_iff_exists_notMem_and.mp idx
    have hca := (hcoset c).resolve_right hc
    have hza := (hcoset z).resolve_right hzN
    have hcz : c / z ∈ N := by
      simpa only [mul_div_mul_right_eq_div] using N.div_mem hca hza
    have h := hN (c / z) hcz
    rw [map_div, map_div, hz] at h
    exact div_eq_one.mp h

/-- On a prime idele class extended from an unramified finite place of the maximal real
subfield, the splitting character is `1` in the split case and `-1` in the inert case. -/
theorem apply_ideleClassExtension_primeIdeleClass (hχ : χ.IsSplitting Ψ)
    (v : HeightOneSpectrum (𝓞 L⁺)) (Q : Ideal (𝓞 L))
    [Q.IsPrime] [Q.LiesOver v.asIdeal] [Algebra.IsUnramifiedAt (𝓞 L⁺) Q] :
    χ (ideleClassExtension L⁺ L (ClassFieldTheory.primeIdeleClass L⁺ v)) =
      if Q.inertiaDeg (𝓞 L⁺) = 1 then 1 else -1 := by
  have hcard : Nat.card Gal(L/L⁺) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  let : Fact (Nat.card Gal(L/L⁺)).Prime := ⟨hcard ▸ Nat.prime_two⟩
  let : IsCyclic Gal(L/L⁺) := isCyclic_of_prime_card rfl
  let ι : L →ₐ[L⁺] SeparableClosure L⁺ := IsSepClosed.lift
  have hmem : ClassFieldTheory.primeIdeleClass L⁺ v ∈ (ideleClassNormMap L⁺ L).range ↔
      Q.inertiaDeg (𝓞 L⁺) = 1 :=
    (ClassFieldTheory.globalArtinMap_eq_zero_iff L⁺ L ι _).symm.trans
      (ClassFieldTheory.globalArtinMap_primeIdeleClass_eq_zero_iff_inertiaDeg_eq_one L ι v Q)
  rw [hχ.apply_ideleClassExtension_eq_ite]
  split_ifs <;> simp_all

end

end TauCeti.GlobalNumberFields.HeckeCharacter.IsSplitting
