/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Ring.Shrink
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Data.SignType.Parity
import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Index
import TauCeti.NumberTheory.NumberField.CMField.Extension
import TauCeti.NumberTheory.NumberField.ComplexConjugation.MaximalRealSubfield
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.CM
import TauCeti.NumberTheory.NumberField.InfinitePlace.Transport
import TauCeti.NumberTheory.QuadraticForm.Global.SignPrescription

/-!
# Sign prescription in a CM field

Let `L` be a CM field with maximal real subfield `L⁺` and complex conjugation `x ↦ conj x`,
extended to the finite adeles `𝔸_f` of `L` as the star structure
(`NumberField.IsCMField.finiteAdeleConj`). Given a sign `ε_w ∈ {±1}` at every infinite place `w`
of `L`, with `∏_w ε_w = 1`, there are `a ∈ Lˣ` such that `φ(a)` is real of sign `ε_w` for every
complex embedding `φ` of `L` at `w`, and a finite idele `z` of `L` with `a · z · conj z = 1`
(`TauCeti.NumberField.IsCMField.exists_sign_eq_and_algebraMap_mul_mul_star_eq_one`).

This is the input of the change of signs for hermitian forms over `L`. Scaling a hermitian form
`β` by `a` changes its signs at the infinite places by `ε`, and over the finite adeles the scaled
form is the transport of `β` by `z⁻¹`, since `conj (z⁻¹) · z⁻¹ = a`. So the two forms have the
same finite adelic invariants and differ only at the infinite places, by the prescribed signs.

The proof is class field theory for the quadratic extension `L / L⁺`. It follows the proof of
Hilbert sign prescription,
`TauCeti.NumberField.QuadraticForm.exists_hilbertSymbol_eq_ite_of_index_dvd_two`, but keeps the
idele norm in the decomposition `i = a · N(y)` below, which that proof discards.

Write `L = L⁺(√b)` with `b = (x - conj x)²` for some `x ≠ conj x`, so that `b` is negative
at every real place of `L⁺`
(`TauCeti.NumberField.IsCMField.exists_isSquare_algebraMap_and_neg`). The infinite places of
`L` and the real places of `L⁺` correspond, and the idele `i` of `L⁺` that is `ε_w` at the real
place below `w` and `1` at every other place lies in the kernel of the idele Hilbert character
`φ_b(x) = ∏_v (x_v, b)_v`, because `(-1, b)_v = -1` at each real place and the number of signs
`-1` is even. By the norm index theorem for `L / L⁺`
(`TauCeti.ClassFieldTheory.index_range_ideleClassNormMap_eq_two`), that kernel is
`L⁺ˣ · N_{L/L⁺}(𝕀_L)`
(`TauCeti.NumberField.QuadraticForm.sup_range_ideleNormMap_eq_ker_ideleHilbertCharacter`), so
`i = a · N(y)` with `a ∈ L⁺ˣ` and `y` an idele of `L`. At a real place `v` of `L⁺` the symbol
`(N(y)_v, b)_v` is `1`, so `a` has the sign of `i_v`; at the finite places, read in `L`, the norm
`N(y)` is `y · conj y`
(`NumberField.IdeleGroup.coe_toFiniteIdele_ideleExtension_ideleNormMap`), so the finite
part `z` of `y` satisfies `a · z · conj z = 1`. The norm index theorem is available for fields in
`Type`; the general statement follows by transport along `Shrink`.

## Main results

* `TauCeti.NumberField.IsCMField.exists_sign_eq_and_algebraMap_mul_mul_star_eq_one`: sign
  prescription with a finite idele `z` such that `a · z · conj z = 1`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 65:21 and 71:19a.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§1–2.
* The folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, file `Lib/ClassField/Global/CMSplittingCharacters.lean`
  (`New.Cohomology.exists_sign_principalIdele_mul_norm_eq_one`), for the statement.
-/

public section

noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.IsCMField
  TauCeti.GlobalNumberFields TauCeti.NumberField.QuadraticForm
open TauCeti (hilbertSymbol hilbertSymbol_completion_eq_unitAtRealPlace
  hilbertSymbol_completion_neg_one_left_eq_neg_one hilbertSymbol_completion_one_left
  hilbertSymbol_unitAtRealPlace_eq_neg_one_iff)
open scoped ComplexConjugate AdeleGaloisAction

namespace TauCeti.NumberField.IsCMField

section General

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]

local notation "K" => maximalRealSubfield L

/-- Let `a ∈ L⁺ˣ` and let `y` be an idele of `L`. If the idele `a · N_{L/L⁺}(y)` of `L⁺` has
trivial finite part, then `a · y_f · conj y_f = 1` in the finite adeles of `L`. -/
private theorem algebraMap_mul_mul_star_eq_one {a : Kˣ} {y : IdeleGroup (𝓞 L) L}
    {x : IdeleGroup (𝓞 K) K} (hx : IdeleGroup.toFiniteIdele (𝓞 K) K x = 1)
    (hxy : IdeleGroup.unitEmbedding (𝓞 K) K a * ideleNormMap K L y = x) :
    algebraMap L (FiniteAdeleRing (𝓞 L) L) (algebraMap K L a) *
        (IdeleGroup.toFiniteIdele (𝓞 L) L y : FiniteAdeleRing (𝓞 L) L) *
        star (IdeleGroup.toFiniteIdele (𝓞 L) L y : FiniteAdeleRing (𝓞 L) L) = 1 := by
  have h := congrArg (fun t ↦ (IdeleGroup.toFiniteIdele (𝓞 L) L (ideleExtension K L t) :
    FiniteAdeleRing (𝓞 L) L)) hxy
  simp only [map_mul, Units.val_mul] at h
  rw [IdeleGroup.coe_toFiniteIdele_ideleExtension_ideleNormMap, ideleExtension_unitEmbedding,
    toFiniteIdele_ideleExtension, hx, map_one, Units.val_one] at h
  rw [mul_assoc, ← h]
  simp

omit [IsCMField L] in
open scoped Classical in
/-- Let `b ∈ L⁺ˣ` be a square in `L`, negative at every real place. If `a · N_{L/L⁺}(y)` is `-1`
at the places of a set `T` of infinite places and `1` at the other infinite places, then `a` is
negative exactly at the real places in `T`. -/
private theorem embedding_neg_iff {a b : Kˣ} {y : IdeleGroup (𝓞 L) L}
    {T : Finset (InfinitePlace K)} (hb : IsSquare (algebraMap K L b))
    (hneg : ∀ v : {v : InfinitePlace K // v.IsReal}, embedding_of_isReal v.property (b : K) < 0)
    (hxy : IdeleGroup.unitEmbedding (𝓞 K) K a * ideleNormMap K L y =
      ∏ w ∈ T, IdeleGroup.ofCompletion (𝓞 K) K w
        (Units.map (algebraMap K w.Completion).toMonoidHom (-1)))
    (v : {v : InfinitePlace K // v.IsReal}) :
    embedding_of_isReal v.property (a : K) < 0 ↔ v.val ∈ T := by
  have h := hilbertSymbol_ideleInfiniteCoord_unitEmbedding_mul_ideleNormMap hb a y v.val
  rw [hxy, ideleInfiniteCoord_prod_ofCompletion v.val T
    fun w ↦ Units.map (algebraMap K w.Completion).toMonoidHom (-1)] at h
  split_ifs at h with hv
  · rw [hilbertSymbol_completion_neg_one_left_eq_neg_one v (hneg v),
      hilbertSymbol_completion_eq_unitAtRealPlace, eq_comm,
      hilbertSymbol_unitAtRealPlace_eq_neg_one_iff] at h
    exact iff_of_true h.1 hv
  · rw [hilbertSymbol_completion_one_left, hilbertSymbol_completion_eq_unitAtRealPlace] at h
    refine iff_of_false (fun ha ↦ ?_) hv
    have := (hilbertSymbol_unitAtRealPlace_eq_neg_one_iff v a b).mpr ⟨ha, hneg v⟩
    rw [← h] at this
    exact absurd this (by decide)

end General

section TypeZero

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation "K" => maximalRealSubfield L

open scoped Classical in
/-- Sign prescription for a CM field in `Type`, where the norm index theorem applies. -/
private theorem exists_sign_eq_and_algebraMap_mul_mul_star_eq_one_zero
    (ε : InfinitePlace L → SignType) (hε : ∏ w, ε w = 1) :
    ∃ a : Lˣ, (∀ φ : L →+* ℂ, (φ a).im = 0 ∧ SignType.sign (φ a).re = ε (.mk φ)) ∧
      ∃ z : (FiniteAdeleRing (𝓞 L) L)ˣ,
        algebraMap L (FiniteAdeleRing (𝓞 L) L) a * z * star (z : FiniteAdeleRing (𝓞 L) L) = 1 := by
  obtain ⟨b, hbsq, hbneg⟩ : ∃ b : Kˣ, IsSquare (algebraMap K L b) ∧
      ∀ v : {v : InfinitePlace K // v.IsReal}, embedding_of_isReal v.property (b : K) < 0 :=
    exists_isSquare_algebraMap_and_neg
  -- The real places of `L⁺` below the places of `L` with sign `-1`.
  let T := (Finset.univ.filter (ε · = -1)).map (equivInfinitePlace L).toEmbedding
  let u (w : InfinitePlace K) : w.Completionˣ :=
    Units.map (algebraMap K w.Completion).toMonoidHom (-1)
  -- `-1` is a local non-norm at every real place, so `φ_b` is `-1` on each factor.
  have hu (w : InfinitePlace K) :
      ideleHilbertCharacter b (IdeleGroup.ofCompletion (𝓞 K) K w (u w)) = -1 :=
    (ideleHilbertCharacter_ofCompletion b w _).trans
      (hilbertSymbol_completion_neg_one_left_eq_neg_one ⟨w, IsTotallyReal.isReal w⟩ (hbneg _))
  have hx : ∏ w ∈ T, IdeleGroup.ofCompletion (𝓞 K) K w (u w) ∈
      IdeleGroup.principalSubgroup (𝓞 K) K ⊔ (ideleNormMap K L).range := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
    rw [sup_range_ideleNormMap_eq_ker_ideleHilbertCharacter hbsq
      (dvd_of_eq (ClassFieldTheory.index_range_ideleClassNormMap_eq_two K L))
      (.inr ⟨⟨w, IsTotallyReal.isReal w⟩, hbneg _⟩), MonoidHom.mem_ker, map_prod,
      Finset.prod_congr rfl fun w _ ↦ hu w, Finset.prod_const, Finset.card_map]
    exact (SignType.even_card_filter_eq_neg_one_of_prod_eq_one hε).neg_one_pow
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨y, rfl⟩, hxy⟩ := Subgroup.mem_sup.mp hx
  refine ⟨Units.map (algebraMap K L).toMonoidHom a, fun φ ↦ ?_, IdeleGroup.toFiniteIdele (𝓞 L) L y,
    by simpa using algebraMap_mul_mul_star_eq_one (by simp) hxy⟩
  -- The real place `v` of `L⁺` below `φ`, at which the real embedding is `φ` on `L⁺`.
  set v := equivInfinitePlace L (.mk φ) with hvdef
  have hv : v.IsReal := IsTotallyReal.isReal v
  have hreal : ComplexEmbedding.IsReal (φ.comp (algebraMap K L)) :=
    isReal_mk_iff.mp (by rwa [← comap_mk, ← equivInfinitePlace_apply])
  have hφ : (embedding_of_isReal hv (a : K) : ℂ) = φ (algebraMap K L a) := by
    rw [embedding_of_isReal_apply, hvdef, equivInfinitePlace_apply, comap_mk,
      embedding_mk_eq_of_isReal hreal, RingHom.comp_apply]
  have hT : v ∈ T ↔ ε (.mk φ) = -1 := by
    simp only [T, hvdef, Finset.mem_map_equiv, Equiv.symm_apply_apply, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have hneg := embedding_neg_iff hbsq hbneg hxy ⟨v, hv⟩
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, ← hφ, Complex.ofReal_im,
    Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  have hr0 : embedding_of_isReal hv (a : K) ≠ 0 := (map_ne_zero _).mpr a.ne_zero
  have hε0 := Finset.prod_ne_zero_iff.mp (by rw [hε]; exact one_ne_zero) (InfinitePlace.mk φ)
    (Finset.mem_univ _)
  rcases h : ε (.mk φ) with _ | _ | _
  · exact absurd h hε0
  · exact sign_neg (hneg.mpr (hT.mpr h))
  · exact sign_pos (lt_of_le_of_ne (not_lt.mp fun hn ↦ by simpa [h] using hT.mp (hneg.mp hn))
      hr0.symm)

end TypeZero

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]

/-- **Sign prescription in a CM field.** Let `L` be a CM field and `ε` a sign at each infinite
place of `L`, with product `1`. Then there is `a ∈ Lˣ` such that `φ a` is real, of sign
`ε (mk φ)`, for every complex embedding `φ` of `L`, and a finite idele `z` of `L` with
`a · z · conj z = 1`, where `conj z = star z` is the complex conjugate of `z`. -/
theorem exists_sign_eq_and_algebraMap_mul_mul_star_eq_one (ε : InfinitePlace L → SignType)
    (hε : ∏ w, ε w = 1) :
    ∃ a : Lˣ, (∀ φ : L →+* ℂ, (φ a).im = 0 ∧ SignType.sign (φ a).re = ε (.mk φ)) ∧
      ∃ z : (FiniteAdeleRing (𝓞 L) L)ˣ,
        algebraMap L (FiniteAdeleRing (𝓞 L) L) a * z * star (z : FiniteAdeleRing (𝓞 L) L) = 1 := by
  -- Transport the statement from the copy `Shrink L` of `L` in `Type`.
  have : Small.{0} L := Module.Finite.small.{0} ℚ L
  let e : Shrink.{0} L ≃+* L := Shrink.ringEquiv L
  have : NumberField (Shrink.{0} L) := .of_ringEquiv L (Shrink.{0} L) e.symm
  have : IsTotallyComplex (Shrink.{0} L) := ⟨fun w ↦ (isComplex_equivOfRingEquiv_iff e w).mp
    (IsTotallyComplex.isComplex _)⟩
  let : Algebra (Shrink.{0} L) L := e.toRingHom.toAlgebra
  have : IsCMField (Shrink.{0} L) := of_algebra _ L
  obtain ⟨a, ha, z, hz⟩ := exists_sign_eq_and_algebraMap_mul_mul_star_eq_one_zero
    (ε ∘ equivOfRingEquiv e) (((equivOfRingEquiv e).prod_comp ε).trans hε)
  let f := finiteAdeleEquiv (Shrink.{0} L) L e
  refine ⟨Units.map e.toMonoidHom a, fun φ ↦ ?_, Units.map f.toMonoidHom z, ?_⟩
  · have h1 : (φ.comp e.toRingHom).comp (e.symm : L →+* Shrink.{0} L) = φ := by
      ext x
      simp
    have h := ha (φ.comp e.toRingHom)
    rw [Function.comp_apply, equivOfRingEquiv_mk, h1, RingHom.comp_apply] at h
    rwa [Units.coe_map]
  · have h := congrArg f hz
    rw [map_mul, map_mul, e.finiteAdeleEquiv_star, finiteAdeleEquiv_algebraMap, map_one] at h
    rwa [Units.coe_map, Units.coe_map]

end TauCeti.NumberField.IsCMField
