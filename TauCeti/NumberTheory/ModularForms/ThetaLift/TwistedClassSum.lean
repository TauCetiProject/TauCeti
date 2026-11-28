/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality

/-!
# Integral measures and ultrametric twisted class sums

A finitely supported integral measure on a set of characters is represented by one element of
`MonoidAlgebra R G`, evaluated at every character in the set. Evaluation makes the algebra
operations on measures functorial. When the coefficient subring is star-closed and the characters
are unitary, conjugating coefficients and inverting basis elements represents complex conjugation;
multiplication by this conjugate measure represents squared modulus.

Character orthogonality on a finite commutative group expresses a value as an average of Fourier
transforms. In an ultrametric target, that average is bounded by one character contribution. This
also yields a twisted class-sum inequality on an arbitrary system of representatives of a finite
commutative quotient.

## Main results

* `characterEval` and `IsIntegralMeasure`: evaluation of an integral monoid-algebra element on
  characters, with closure under algebra operations, conjugation, and `norm_sq`.
* `exists_character_norm_le_fourierTransform`: the finite commutative Fourier pigeonhole.
* `exists_character_norm_le_cosetTransform`: the quotient form with arbitrary representatives
  and an arbitrary base point, and `exists_character_norm_le_cosetTransform_one` at the identity.

## References

The integral-measure argument and the class-sum application follow [ShortProof]
(https://github.com/lsernau/grh-lean), `lsernau/grh-lean` at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, files
`grh/src/New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean` and
`grh/src/New/OneLift/HeckeValues/TwistedValueHeights.lean`. The present formulation uses the
project's character orthogonality API and treats arbitrary ultrametric normed fields.
-/

public noncomputable section

namespace TauCeti.ThetaLift

/-- Evaluate an `R`-coefficient monoid algebra at a unit-valued character. -/
def characterEval (R : Subring ℂ) {G : Type*} [Monoid G] (χ : G →* ℂˣ) :
    MonoidAlgebra R G →ₐ[R] ℂ :=
  MonoidAlgebra.lift R ℂ G ((Units.coeHom ℂ).comp χ)

/-- A character function is an integral measure if it is the evaluation of one integral
monoid-algebra element throughout `S`. -/
def IsIntegralMeasure (R : Subring ℂ) {G : Type*} [Monoid G]
    (S : Set (G →* ℂˣ)) (F : (G →* ℂˣ) → ℂ) : Prop :=
  ∃ μ : MonoidAlgebra R G, ∀ ϑ ∈ S, F ϑ = characterEval R ϑ μ

/-- The zero character function is evaluation of the zero measure. -/
theorem IsIntegralMeasure.zero (R : Subring ℂ) {G : Type*} [Monoid G]
    (S : Set (G →* ℂˣ)) : IsIntegralMeasure R S 0 :=
  ⟨0, by intros; simp⟩

/-- The constant one character function is evaluation of the identity measure. -/
theorem IsIntegralMeasure.one (R : Subring ℂ) {G : Type*} [Monoid G]
    (S : Set (G →* ℂˣ)) : IsIntegralMeasure R S 1 :=
  ⟨1, by intros; simp⟩

/-- The sum of two integral measures is an integral measure. -/
theorem IsIntegralMeasure.add {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {F F' : (G →* ℂˣ) → ℂ}
    (hF : IsIntegralMeasure R S F) (hF' : IsIntegralMeasure R S F') :
    IsIntegralMeasure R S (F + F') := by
  obtain ⟨μ, hμ⟩ := hF
  obtain ⟨ν, hν⟩ := hF'
  refine ⟨μ + ν, fun ϑ hϑ ↦ ?_⟩
  rw [Pi.add_apply, hμ ϑ hϑ, hν ϑ hϑ, map_add]

/-- The negative of an integral measure is an integral measure. -/
theorem IsIntegralMeasure.neg {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {F : (G →* ℂˣ) → ℂ}
    (hF : IsIntegralMeasure R S F) : IsIntegralMeasure R S (-F) := by
  obtain ⟨μ, hμ⟩ := hF
  refine ⟨-μ, fun ϑ hϑ ↦ ?_⟩
  rw [Pi.neg_apply, hμ ϑ hϑ, map_neg]

/-- The difference of two integral measures is an integral measure. -/
theorem IsIntegralMeasure.sub {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {F F' : (G →* ℂˣ) → ℂ}
    (hF : IsIntegralMeasure R S F) (hF' : IsIntegralMeasure R S F') :
    IsIntegralMeasure R S (F - F') := by
  simpa only [sub_eq_add_neg] using hF.add hF'.neg

/-- The pointwise product of integral measures is an integral measure. -/
theorem IsIntegralMeasure.mul {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {F F' : (G →* ℂˣ) → ℂ}
    (hF : IsIntegralMeasure R S F) (hF' : IsIntegralMeasure R S F') :
    IsIntegralMeasure R S (F * F') := by
  obtain ⟨μ, hμ⟩ := hF
  obtain ⟨ν, hν⟩ := hF'
  refine ⟨μ * ν, fun ϑ hϑ ↦ ?_⟩
  rw [Pi.mul_apply, hμ ϑ hϑ, hν ϑ hϑ, map_mul]

/-- A natural power of an integral measure is an integral measure. -/
theorem IsIntegralMeasure.pow {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {F : (G →* ℂˣ) → ℂ}
    (hF : IsIntegralMeasure R S F) (n : ℕ) : IsIntegralMeasure R S (F ^ n) := by
  obtain ⟨μ, hμ⟩ := hF
  refine ⟨μ ^ n, fun ϑ hϑ ↦ ?_⟩
  rw [Pi.pow_apply, hμ ϑ hϑ, map_pow]

/-- A finite sum of integral measures is an integral measure. -/
theorem IsIntegralMeasure.sum {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {ι : Type*} (t : Finset ι)
    {F : ι → (G →* ℂˣ) → ℂ} (hF : ∀ i ∈ t, IsIntegralMeasure R S (F i)) :
    IsIntegralMeasure R S (∑ i ∈ t, F i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using IsIntegralMeasure.zero R S
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a t)).add
      (ih fun i hi ↦ hF i (Finset.mem_insert_of_mem hi))

/-- A finite product of integral measures is an integral measure. -/
theorem IsIntegralMeasure.prod {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {ι : Type*} (t : Finset ι)
    {F : ι → (G →* ℂˣ) → ℂ} (hF : ∀ i ∈ t, IsIntegralMeasure R S (F i)) :
    IsIntegralMeasure R S (∏ i ∈ t, F i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using IsIntegralMeasure.one R S
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha]
    exact (hF a (Finset.mem_insert_self a t)).mul
      (ih fun i hi ↦ hF i (Finset.mem_insert_of_mem hi))

/-- Complex conjugation restricted to a star-closed subring. -/
private def starSubringEnd (R : Subring ℂ) (hR : ∀ z ∈ R, star z ∈ R) : R →+* R where
  toFun z := ⟨star (z : ℂ), hR z z.property⟩
  map_one' := Subtype.ext (map_one (starRingEnd ℂ))
  map_mul' x y := Subtype.ext (map_mul (starRingEnd ℂ) (x : ℂ) (y : ℂ))
  map_zero' := Subtype.ext (map_zero (starRingEnd ℂ))
  map_add' x y := Subtype.ext (map_add (starRingEnd ℂ) (x : ℂ) (y : ℂ))

/-- Conjugate the coefficients and invert the basis elements of a group-algebra element. -/
private def conjugateMeasure {G : Type*} [Group G] (R : Subring ℂ)
    (hR : ∀ z ∈ R, star z ∈ R) (μ : MonoidAlgebra R G) : MonoidAlgebra R G :=
  MonoidAlgebra.mapDomain (Equiv.inv G)
    (MonoidAlgebra.mapRingHom G (starSubringEnd R hR) μ)

/-- Evaluation of the conjugated measure is the conjugate of evaluation on unitary characters. -/
private theorem characterEval_conjugateMeasure {G : Type*} [Group G]
    (R : Subring ℂ) (hR : ∀ z ∈ R, star z ∈ R) (χ : G →* ℂˣ)
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = 1) (μ : MonoidAlgebra R G) :
    characterEval R χ (conjugateMeasure R hR μ) = star (characterEval R χ μ) := by
  induction μ using MonoidAlgebra.induction_linear with
  | zero => simp [conjugateMeasure]
  | add μ ν hμ hν =>
    have hadd : conjugateMeasure R hR (μ + ν) =
        conjugateMeasure R hR μ + conjugateMeasure R hR ν := by
      simp [conjugateMeasure, MonoidAlgebra.mapDomain_add]
    rw [hadd]
    simp only [map_add, hμ, hν, Complex.star_def]
  | single g c =>
    simp [conjugateMeasure, characterEval, MonoidAlgebra.lift_single, map_inv,
      Complex.inv_eq_conj (hχ g), starSubringEnd, Algebra.smul_def]
    rfl

/-- Conjugation of an integral measure is an integral measure on unitary characters. -/
theorem IsIntegralMeasure.conj {R : Subring ℂ} {G : Type*} [Group G]
    {S : Set (G →* ℂˣ)} {F : (G →* ℂˣ) → ℂ}
    (hR : ∀ z ∈ R, star z ∈ R) (hS : ∀ ϑ ∈ S, ∀ u, ‖(ϑ u : ℂ)‖ = 1)
    (hF : IsIntegralMeasure R S F) : IsIntegralMeasure R S (star F) := by
  obtain ⟨μ, hμ⟩ := hF
  refine ⟨conjugateMeasure R hR μ, fun ϑ hϑ ↦ ?_⟩
  rw [Pi.star_apply, hμ ϑ hϑ, characterEval_conjugateMeasure R hR ϑ (hS ϑ hϑ)]

/-- Squared modulus of an integral measure is an integral measure on unitary characters. -/
theorem IsIntegralMeasure.norm_sq {R : Subring ℂ} {G : Type*} [Group G]
    {S : Set (G →* ℂˣ)} {F : (G →* ℂˣ) → ℂ}
    (hR : ∀ z ∈ R, star z ∈ R) (hS : ∀ ϑ ∈ S, ∀ u, ‖(ϑ u : ℂ)‖ = 1)
    (hF : IsIntegralMeasure R S F) :
    IsIntegralMeasure R S (fun ϑ ↦ (‖F ϑ‖ : ℂ) ^ 2) := by
  obtain ⟨μ, hμ⟩ := hF
  refine ⟨μ * conjugateMeasure R hR μ, fun ϑ hϑ ↦ ?_⟩
  rw [map_mul, characterEval_conjugateMeasure R hR ϑ (hS ϑ hϑ), ← hμ ϑ hϑ]
  simpa only [Complex.star_def] using (Complex.mul_conj' (F ϑ)).symm

/-- Some character has normalized Fourier transform at least as large as any prescribed value after
applying an ultrametric place. -/
theorem exists_character_norm_le_fourierTransform {Q K : Type*} [Fintype Q] [CommGroup Q]
    [NormedField K] [IsUltrametricDist K] (place : ℂ →+* K) (s : Q → ℂ) (q₀ : Q) :
    ∃ χ : Q →* ℂˣ, ‖place (s q₀)‖ ≤
      ‖place ((Fintype.card Q : ℂ)⁻¹ * ∑ q : Q, (χ q : ℂ) * s q)‖ := by
  classical
  have hunit (χ : Q →* ℂˣ) (q : Q) : ‖place (χ q : ℂ)‖ = 1 :=
    (((place.toMonoidHom.comp (Units.coeHom ℂ)).comp χ).isOfFinOrder
      (isOfFinOrder_of_finite q)).norm_eq_one
  have hinv (χ : Q →* ℂˣ) : ‖place ((((χ q₀)⁻¹ : ℂˣ) : ℂ))‖ = 1 := by
    simpa only [map_inv] using hunit χ q₀⁻¹
  have hC : s q₀ = (Fintype.card Q : ℂ)⁻¹ * ∑ χ : Q →* ℂˣ,
      ((((χ q₀)⁻¹ : ℂˣ) : ℂ) * ∑ q : Q, (χ q : ℂ) * s q) := by
    have h := CommGroup.sum_inv_smul_sum_smul (M := ℂ) (V := ℂ) s q₀
    have hn := congrArg (fun z : ℂ => (Fintype.card Q : ℂ)⁻¹ * z) h
    simpa [smul_eq_mul, Nat.card_eq_fintype_card, ← mul_assoc] using hn.symm
  have hK := congrArg place hC
  simp only [map_mul, map_inv₀, map_natCast, map_sum] at hK
  obtain ⟨χ, -, hχ⟩ := IsUltrametricDist.exists_norm_finsetSum_le
    (Finset.univ : Finset (Q →* ℂˣ)) (fun χ =>
      place ((((χ q₀)⁻¹ : ℂˣ) : ℂ)) * ∑ q : Q, place (χ q : ℂ) * place (s q))
  have hχ' : ‖∑ ψ : Q →* ℂˣ, place ((((ψ q₀)⁻¹ : ℂˣ) : ℂ)) *
      ∑ q : Q, place (ψ q : ℂ) * place (s q)‖ ≤
      ‖place ((((χ q₀)⁻¹ : ℂˣ) : ℂ)) *
        ∑ q : Q, place (χ q : ℂ) * place (s q)‖ := by
    simpa using hχ
  refine ⟨χ, ?_⟩
  simp only [map_mul, map_inv₀, map_natCast, map_sum]
  calc
    ‖place (s q₀)‖ = ‖(Fintype.card Q : K)⁻¹ * ∑ ψ : Q →* ℂˣ,
        place ((((ψ q₀)⁻¹ : ℂˣ) : ℂ)) *
          ∑ q : Q, place (ψ q : ℂ) * place (s q)‖ := by
      rw [hK]
    _ = ‖(Fintype.card Q : K)⁻¹‖ * ‖∑ ψ : Q →* ℂˣ,
        place ((((ψ q₀)⁻¹ : ℂˣ) : ℂ)) * ∑ q : Q, place (ψ q : ℂ) * place (s q)‖ :=
      norm_mul _ _
    _ ≤ ‖(Fintype.card Q : K)⁻¹‖ * ‖place ((((χ q₀)⁻¹ : ℂˣ) : ℂ)) *
        ∑ q : Q, place (χ q : ℂ) * place (s q)‖ :=
      mul_le_mul_of_nonneg_left hχ' (norm_nonneg _)
    _ = ‖(Fintype.card Q : K)⁻¹ * ∑ q : Q, place (χ q : ℂ) * place (s q)‖ := by
      rw [norm_mul, norm_mul, hinv, one_mul]

/-- Some character killed by `H` has a normalized coset-representative transform at least as
large as any prescribed value after applying an ultrametric place. -/
theorem exists_character_norm_le_cosetTransform {G K : Type*} [CommGroup G]
    (H : Subgroup G) [Fintype (G ⧸ H)] [NormedField K] [IsUltrametricDist K]
    (place : ℂ →+* K) (rep : (G ⧸ H) → G)
    (hrep : ∀ q, QuotientGroup.mk (rep q) = q) (s : G → ℂ) (z₀ : G) :
    ∃ (z : G) (χ : G →* ℂˣ), H ≤ χ.ker ∧ ‖place (s z₀)‖ ≤
      ‖place ((Fintype.card (G ⧸ H) : ℂ)⁻¹ *
        ∑ q : G ⧸ H, (χ (rep q * z) : ℂ) * s (rep q * z))‖ := by
  let z : G := (rep 1)⁻¹ * z₀
  obtain ⟨χ, hχ⟩ := exists_character_norm_le_fourierTransform place
    (fun q ↦ s (rep q * z)) 1
  let χG : G →* ℂˣ := χ.comp (QuotientGroup.mk' H)
  have hker : H ≤ χG.ker := by
    intro h hh
    simp only [χG, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [(QuotientGroup.eq_one_iff h).mpr hh, map_one]
  have hz : rep 1 * z = z₀ := by simp [z]
  have hsum : (∑ q : G ⧸ H, (χG (rep q * z) : ℂ) * s (rep q * z)) =
      (χ (QuotientGroup.mk z) : ℂ) *
        ∑ q : G ⧸ H, (χ q : ℂ) * s (rep q * z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    simp only [χG, MonoidHom.comp_apply, QuotientGroup.mk'_apply, map_mul,
      Units.val_mul, hrep]
    ring
  have hnorm : ‖place (χ (QuotientGroup.mk z) : ℂ)‖ = 1 :=
    (((place.toMonoidHom.comp (Units.coeHom ℂ)).comp χ).isOfFinOrder
      (isOfFinOrder_of_finite (QuotientGroup.mk z))).norm_eq_one
  refine ⟨z, χG, hker, ?_⟩
  rw [← hz]
  calc
    ‖place (s (rep 1 * z))‖ ≤ ‖place ((Fintype.card (G ⧸ H) : ℂ)⁻¹ *
        ∑ q : G ⧸ H, (χ q : ℂ) * s (rep q * z))‖ := hχ
    _ = ‖place ((Fintype.card (G ⧸ H) : ℂ)⁻¹ *
        ∑ q : G ⧸ H, (χG (rep q * z) : ℂ) * s (rep q * z))‖ := by
      rw [hsum, ← mul_assoc, map_mul, map_mul, norm_mul, norm_mul,
        map_mul, norm_mul, hnorm, mul_one]

/-- The coset-representative Fourier pigeonhole normalized at the identity. -/
theorem exists_character_norm_le_cosetTransform_one {G K : Type*} [CommGroup G]
    (H : Subgroup G) [Fintype (G ⧸ H)] [NormedField K] [IsUltrametricDist K]
    (place : ℂ →+* K) (rep : (G ⧸ H) → G)
    (hrep : ∀ q, QuotientGroup.mk (rep q) = q) (s : G → ℂ) :
    ∃ (z : G) (χ : G →* ℂˣ), H ≤ χ.ker ∧ ‖place (s 1)‖ ≤
      ‖place ((Fintype.card (G ⧸ H) : ℂ)⁻¹ *
        ∑ q : G ⧸ H, (χ (rep q * z) : ℂ) * s (rep q * z))‖ :=
  exists_character_norm_le_cosetTransform H place rep hrep s 1

end TauCeti.ThetaLift
