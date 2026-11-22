/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.NumberTheory.Chebotarev.Density.ResidueDegree
import Mathlib.FieldTheory.Normal.Closure
import TauCeti.GroupTheory.Subgroup.ConjugatesOfSet
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.Padics.NumberFieldEmbedding

/-!
# Rationality from embeddings into almost all `ℚ_[ℓ]`

A finite extension `K` of `ℚ` that embeds into `ℚ_[ℓ]` for every prime `ℓ` outside a finite set is
`ℚ` itself. Consequently, an algebraic number that some embedding into an algebraic closure of
`ℚ_[ℓ]` carries into `ℚ_[ℓ]`, for almost every `ℓ`, is rational. So is an algebraic point of an
affine `ℚ`-scheme that becomes `ℚ_[ℓ]`-rational for almost every `ℓ`, under embeddings that may
vary with `ℓ`.

Let `L` be a Galois closure of `K` and `H ≤ Gal(L/ℚ)` the subgroup fixing `K`. An embedding of
`K` into `ℚ_[ℓ]` gives a prime of `K` of residue degree one above `ℓ`
(`RingHom.exists_inertiaDeg_eq_one_of_padic`), and at a prime unramified in `L` this says that
the Frobenius class meets `H`. By Chebotarev every conjugacy class of `Gal(L/ℚ)` is the Frobenius
class of infinitely many primes, hence of one outside the finite exceptional set, so every class
meets `H`. Jordan's covering lemma (`Subgroup.conjugatesOfSet_eq_univ_iff`) then forces
`H = Gal(L/ℚ)`, that is `K = ℚ`.

The hypothesis concerns almost all primes: `ℚ(i)` embeds into `ℚ_[ℓ]` for every `ℓ ≡ 1 mod 4`.
It asks for a prime of residue degree one, not for complete splitting: `ℚ(∛2)` embeds into
`ℚ_[ℓ]` for every odd `ℓ ≡ 2 mod 3`, although no such `ℓ` splits completely; among the primes
`ℓ ∤ 6` it fails to embed exactly when `ℓ ≡ 1 mod 3` and `2` is not a cube modulo `ℓ`.

For points, the hypothesis concerns one fixed algebraic point: the `ℚ`-scheme defined by
`(x² - 2)(x² - 17)(x² - 34)` has points over every `ℚ_[ℓ]` and over `ℝ` but no rational point, and
each of its algebraic points is `ℚ_[ℓ]`-rational only for a set of primes of density one half.

## Main results

* `Subgroup.eq_top_of_forall_ringHom_padic`: for a finite Galois extension `L / ℚ`, a subgroup
  of `Gal(L/ℚ)` whose fixed field embeds into `ℚ_[ℓ]` for almost every prime `ℓ` is everything.
* `TauCeti.finrank_eq_one_of_embeddings_padic`: a finite extension of `ℚ` embedding into
  `ℚ_[ℓ]` for almost every prime `ℓ` has degree one.
* `IsIntegral.mem_range_algebraMap_of_padic`: an algebraic number carried into `ℚ_[ℓ]` by an
  embedding into `AlgebraicClosure ℚ_[ℓ]`, for almost every prime `ℓ`, is rational.
* `AlgHom.exists_ofId_comp_eq_of_padic`: an algebraic point of a `ℚ`-algebra that is
  `ℚ_[ℓ]`-rational for almost every `ℓ` is rational.

## References

* M. Kisin and R. Zhou, *Independence of ℓ for Frobenius conjugacy classes attached to abelian
  varieties*, Ann. of Math. 202 (2025); arXiv:2103.09945v2, §5.3.6, p.55.
* J.-P. Serre, *On a theorem of Jordan*, Bull. Amer. Math. Soc. 40 (2003), 429–440, §3.
-/

public section

open NumberField IsDedekindDomain IntermediateField

/-- For a finite Galois extension `L / ℚ` and a subgroup `H` of its Galois group, if the fixed
field of `H` embeds into `ℚ_[ℓ]` for every prime `ℓ` outside a finite set `S`, then
`H = Gal(L/ℚ)`. -/
theorem Subgroup.eq_top_of_forall_ringHom_padic {L : Type*} [Field L] [NumberField L]
    [IsGalois ℚ L] (H : Subgroup (L ≃ₐ[ℚ] L)) {S : Finset ℕ}
    (hH : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → Nonempty (fixedField H →+* ℚ_[ℓ])) :
    H = ⊤ := by
  rw [← Subgroup.conjugatesOfSet_eq_univ_iff]
  refine Set.eq_univ_of_forall fun σ ↦ ?_
  -- Choose a prime outside `S` whose Frobenius class is that of `σ`.
  have hfin : {𝔭 : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm 𝔭.asIdeal ∈ S}.Finite :=
    S.finite_toSet.preimage Rat.HeightOneSpectrum.absNorm_asIdeal_injective.injOn
  obtain ⟨𝔭, h𝔭C, h𝔭S⟩ :=
    ((Chebotarev.infinite_frobeniusPrimeSet ℚ L (ConjClasses.mk σ)).sdiff hfin).nonempty
  have : Fact (Ideal.absNorm 𝔭.asIdeal).Prime :=
    ⟨by simpa using Rat.HeightOneSpectrum.prime_natGenerator 𝔭⟩
  -- The embedding at that prime gives a residue-degree-one prime, so the class meets `H`.
  obtain ⟨φ⟩ := hH _ h𝔭S
  obtain ⟨τ, hτC, hτ⟩ := (Chebotarev.exists_inertiaDeg_eq_iff_of_mem_frobeniusPrimeSet h𝔭C).mp
    (φ.exists_inertiaDeg_eq_one_of_padic rfl)
  exact Group.mem_conjugatesOfSet_iff.mpr ⟨τ, Subgroup.relIndex_eq_one.mp hτ
    (Subgroup.mem_zpowers τ), ConjClasses.mk_eq_mk_iff_isConj.mp
      (ConjClasses.mem_carrier_iff_mk_eq.mp hτC)⟩

namespace TauCeti

/-- **Rational descent from embeddings into almost all `ℚ_[ℓ]`.** A finite extension `K` of `ℚ`
that embeds into `ℚ_[ℓ]` for every prime `ℓ` outside a finite set `S` has degree one over `ℚ`. -/
theorem finrank_eq_one_of_embeddings_padic {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] {S : Finset ℕ}
    (hK : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → Nonempty (K →+* ℚ_[ℓ])) :
    Module.finrank ℚ K = 1 := by
  -- Realize `K` as the fixed field of a subgroup of the Galois group of its normal closure.
  let f : K →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let N := normalClosure ℚ K (AlgebraicClosure ℚ)
  have : NumberField N := NumberField.of_module_finite ℚ N
  have : IsGalois ℚ N := ⟨⟩
  let g : K →ₐ[ℚ] N := f.codRestrict N.toSubalgebra fun x ↦ f.fieldRange_le_normalClosure ⟨x, rfl⟩
  let e : K ≃ₐ[ℚ] fixedField g.fieldRange.fixingSubgroup :=
    (AlgEquiv.ofInjectiveField g).trans
      (equivOfEq (IsGalois.fixedField_fixingSubgroup g.fieldRange).symm)
  have hH := Subgroup.eq_top_of_forall_ringHom_padic g.fieldRange.fixingSubgroup
    fun ℓ _ hℓ ↦ (hK ℓ hℓ).map fun φ ↦ φ.comp e.symm.toRingHom
  rw [e.toLinearEquiv.finrank_eq, hH, IsGalois.fixedField_top, IntermediateField.finrank_bot]

end TauCeti

/-- **Rational descent of algebraic numbers.** Let `α` be an element of a field `Ω`, algebraic
over `ℚ`. Suppose that for every prime `ℓ` outside a finite set `S` some ring embedding
`ι : Ω →+* AlgebraicClosure ℚ_[ℓ]` carries `α` into `ℚ_[ℓ]`; the embeddings may vary with `ℓ`.
Then `α` is rational. Algebraicity is needed: a transcendental element of `ℚ(t)` can be sent to
any transcendental element of `ℚ_[ℓ]`. -/
theorem IsIntegral.mem_range_algebraMap_of_padic {Ω : Type*} [Field Ω] [Algebra ℚ Ω] {α : Ω}
    (hα : IsIntegral ℚ α) {S : Finset ℕ}
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ ι : Ω →+* AlgebraicClosure ℚ_[ℓ],
      ι α ∈ Set.range (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))) :
    α ∈ Set.range (algebraMap ℚ Ω) := by
  have : FiniteDimensional ℚ ℚ⟮α⟯ := adjoin.finiteDimensional hα
  -- `ℚ⟮α⟯` carries two `ℚ`-algebra structures, `DivisionRing.toRatAlgebra` and the restriction
  -- `algebra'` of the one on `Ω`. They are equal but not definitionally so, and only the second
  -- matches the module structure of the `FiniteDimensional` instance, so it is passed explicitly.
  have hfin := @TauCeti.finrank_eq_one_of_embeddings_padic ℚ⟮α⟯ _ (ℚ⟮α⟯).algebra' this S
    fun ℓ _ hℓ ↦ by
    obtain ⟨ι, hι⟩ := h ℓ hℓ
    -- `ι` maps `ℚ⟮α⟯` into the image of `ℚ_[ℓ]`, a subfield containing `ℚ` and `ι α`.
    have hle : (ℚ⟮α⟯).toSubfield ≤
        (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])).fieldRange.comap ι := by
      refine adjoin_le_subfield _ _ ?_ (Set.singleton_subset_iff.mpr ?_)
      · rintro _ ⟨q, rfl⟩
        exact ⟨q, by simp⟩
      · exact Subfield.mem_comap.mpr (RingHom.mem_fieldRange.mpr hι)
    let e := AlgEquiv.ofInjective (Algebra.ofId ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))
      (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])).injective
    exact ⟨e.symm.toRingHom.comp ((ι.comp (algebraMap ℚ⟮α⟯ Ω)).codRestrict _ fun x ↦
      (Algebra.ofId _ _).mem_range.mpr (RingHom.mem_fieldRange.mp (hle x.2)))⟩
  have hbot : ℚ⟮α⟯ = ⊥ := finrank_eq_one_iff.mp hfin
  exact IntermediateField.mem_bot.mp (hbot ▸ mem_adjoin_simple_self ℚ α)

/-- **Rational descent of algebraic points.** Let `a` be a point of a `ℚ`-algebra `A` with values
in an algebraic extension `Ω` of `ℚ`. Suppose that for every prime `ℓ` outside a finite set `S`
some ring embedding `ι : Ω →+* AlgebraicClosure ℚ_[ℓ]` carries all coordinates of `a` into
`ℚ_[ℓ]`; the embeddings may vary with `ℓ`. Then `a` is a rational point: it factors through `ℚ`.
-/
theorem AlgHom.exists_ofId_comp_eq_of_padic {A : Type*} [Semiring A] [Algebra ℚ A] {Ω : Type*}
    [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (a : A →ₐ[ℚ] Ω) {S : Finset ℕ}
    (ha : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ ι : Ω →+* AlgebraicClosure ℚ_[ℓ],
      ∀ x, ι (a x) ∈ Set.range (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))) :
    ∃ b : A →ₐ[ℚ] ℚ, (Algebra.ofId ℚ Ω).comp b = a := by
  have hbot (x : A) : a x ∈ (⊥ : Subalgebra ℚ Ω) :=
    Algebra.mem_bot.mpr ((Algebra.IsIntegral.isIntegral (a x)).mem_range_algebraMap_of_padic
      fun ℓ _ hℓ ↦ (ha ℓ hℓ).imp fun _ hι ↦ hι x)
  refine ⟨(Algebra.botEquiv ℚ Ω).toAlgHom.comp (a.codRestrict ⊥ hbot), ?_⟩
  ext x
  have h := (Algebra.botEquiv ℚ Ω).symm_apply_apply (a.codRestrict ⊥ hbot x)
  rw [Algebra.botEquiv_symm_apply] at h
  simpa using congrArg Subtype.val h
