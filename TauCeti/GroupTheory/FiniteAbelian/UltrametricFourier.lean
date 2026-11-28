/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality

/-!
# Ultrametric bounds for finite Fourier transforms

Character orthogonality on a finite commutative group expresses a value as an average of Fourier
transforms. In an ultrametric target, that average is bounded by one character contribution.
This also gives a twisted class-sum inequality for any system of representatives of a finite
commutative quotient.

## Main declarations

* `CommGroup.exists_character_norm_le_fourierTransform` gives the finite Fourier bound.
* `CommGroup.exists_character_norm_le_cosetTransform` gives the quotient form with arbitrary
  representatives and base point, and its `_one` variant specializes to the identity.

## References

The class-sum application follows [ShortProof](https://github.com/lsernau/grh-lean) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, in
`grh/src/New/OneLift/HeckeValues/TwistedValueHeights.lean`.
-/

public section

namespace CommGroup

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

end CommGroup
