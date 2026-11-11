/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import TauCeti.RingTheory.RootsOfUnity.LocalRing

/-!
# Roots of unity of invertible order in a Henselian local ring

Reduction modulo the maximal ideal of a Henselian local ring `R` identifies the `n`-th roots
of unity of `R` with those of its residue field, whenever `n` is invertible in `R`.

Surjectivity holds for every `n` and is Hensel's lemma applied to `X ^ m - 1`, where `m` is the
part of `n` prime to the residue characteristic, so that `m` is invertible and the roots are
simple. Injectivity needs `n` to be invertible.

## Main results

* `TauCeti.rootsOfUnityResidue_bijective` and `TauCeti.rootsOfUnityEquivResidueField`: reduction
  is a bijection, and the resulting isomorphism with the roots of unity of the residue field.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §4.
-/

public section

noncomputable section

open IsLocalRing Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- **Every root of unity of the residue field lifts**, by Hensel's lemma applied to `X ^ m - 1`,
where `m` is the part of `n` prime to the residue characteristic. -/
theorem rootsOfUnityResidue_surjective {n : ℕ} :
    Function.Surjective (rootsOfUnityResidue (R := R) n) := by
  rintro ⟨α, hα⟩
  obtain ⟨a₀, ha₀⟩ := surjective_units_map_of_local_ringHom (residue R) residue_surjective
    inferInstance α
  have ha₀' : residue R ((a₀ : Rˣ) : R) = (α : ResidueField R) := congrArg Units.val ha₀
  have hαpow : ((α : ResidueField R)) ^ n = 1 := (mem_rootsOfUnity' n _).mp hα
  -- a lift of `α` which is an `m`-th root of unity, for `m` invertible in `R`
  have key : ∀ m : ℕ, IsUnit (m : R) → (α : ResidueField R) ^ m = 1 →
      ∃ a : R, a ^ m = 1 ∧ residue R a = (α : ResidueField R) := by
    intro m hm hαm
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp only [Nat.cast_zero] at hm
      exact not_isUnit_zero (M₀ := R) hm
    have hroot : (X ^ m - C 1 : R[X]).eval ((a₀ : Rˣ) : R) ∈ maximalIdeal R := by
      rw [← residue_eq_zero_iff]
      simp [map_pow, ha₀', hαm]
    have hderiv : IsUnit ((X ^ m - C 1 : R[X]).derivative.eval ((a₀ : Rˣ) : R)) := by
      simpa [derivative_X_pow] using hm.mul (a₀.isUnit.pow (m - 1))
    obtain ⟨a, ha, hmem⟩ := HenselianLocalRing.is_henselian (X ^ m - C 1 : R[X])
      (monic_X_pow_sub_C 1 hm0) ((a₀ : Rˣ) : R) hroot hderiv
    refine ⟨a, ?_, ?_⟩
    · simpa [IsRoot.def, sub_eq_zero] using ha
    · rw [← ha₀', ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      exact hmem
  by_cases hn0 : n = 0
  · subst hn0
    exact ⟨⟨a₀, (mem_rootsOfUnity 0 a₀).mpr (pow_zero _)⟩, by ext; simpa using ha₀'⟩
  · obtain ⟨p, hp⟩ : ∃ p, ExpChar (ResidueField R) p := ⟨_, ringExpChar.expChar _⟩
    have hp' := hp
    obtain ⟨k, m, rfl, hm⟩ : ∃ k m, n = p ^ k * m ∧ IsUnit (m : R) := by
      cases hp with
      | zero =>
        refine ⟨0, n, by simp, ?_⟩
        rw [← residue_ne_zero_iff_isUnit, map_natCast]
        exact Nat.cast_ne_zero.mpr hn0
      | prime hpp =>
        obtain ⟨k, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hpp.ne_one
        refine ⟨k, m, hnm, ?_⟩
        rw [← residue_ne_zero_iff_isUnit, map_natCast]
        exact fun h ↦ hpm ((CharP.cast_eq_zero_iff _ p m).mp h)
    obtain ⟨a, ha, hres⟩ := key m hm
      ((@ExpChar.pow_prime_pow_mul_eq_one_iff _ _ _ p k m hp' _).mp hαpow)
    have : NeZero (p ^ k * m) := ⟨hn0⟩
    refine ⟨rootsOfUnity.mkOfPowEq a (by rw [pow_mul', ha, one_pow]), ?_⟩
    ext
    simpa using hres

/-- Reduction is a bijection on roots of unity of invertible order. -/
theorem rootsOfUnityResidue_bijective {n : ℕ}
    (hn : IsUnit (n : R)) : Function.Bijective (rootsOfUnityResidue (R := R) n) :=
  ⟨rootsOfUnityResidue_injective hn, rootsOfUnityResidue_surjective⟩

/-- **Roots of unity of invertible order lift uniquely along the residue map of a Henselian local
ring**: reduction is an isomorphism between the `n`-th roots of unity of `R` and those of its
residue field. -/
def rootsOfUnityEquivResidueField {n : ℕ}
    (hn : IsUnit (n : R)) : rootsOfUnity n R ≃* rootsOfUnity n (ResidueField R) :=
  MulEquiv.ofBijective _ (rootsOfUnityResidue_bijective hn)

/-- The value of `rootsOfUnityEquivResidueField` is the reduction of the root of unity. -/
@[simp]
theorem coe_rootsOfUnityEquivResidueField {n : ℕ}
    (hn : IsUnit (n : R)) (ζ : rootsOfUnity n R) :
    ((rootsOfUnityEquivResidueField hn ζ : (ResidueField R)ˣ) : ResidueField R) =
      residue R ((ζ : Rˣ) : R) :=
  coe_rootsOfUnityResidue n ζ

end TauCeti
