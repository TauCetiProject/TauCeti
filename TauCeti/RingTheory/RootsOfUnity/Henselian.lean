/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import TauCeti.RingTheory.RootsOfUnity.LocalRing
import TauCeti.RingTheory.Henselian.Basic

/-!
# Roots of unity of invertible order in a Henselian local ring

Reduction modulo the maximal ideal of a Henselian local ring `R` identifies the `n`-th roots
of unity of `R` with those of its residue field, whenever `n` is invertible in `R`.

Surjectivity holds for every `n`. For `n = 0` it is surjectivity on units, and for `n ≠ 0` it is
Hensel's lemma applied to `X ^ m - 1`, where `m` is the part of `n` prime to the exponential
characteristic of the residue field, so that `m` is invertible and the roots are simple.
Injectivity needs `n` to be invertible.

## Main results

* `TauCeti.rootsOfUnityResidue_surjective`: every root of unity of the residue field lifts, for
  every `n`.
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

/-- **Every `n`-th root of unity of the residue field of a Henselian local ring lifts** to an
`n`-th root of unity of the ring (for `n = 0`, every unit lifts to a unit). -/
theorem rootsOfUnityResidue_surjective {n : ℕ} :
    Function.Surjective (rootsOfUnityResidue (R := R) n) := by
  rintro ⟨α, hα⟩
  obtain ⟨a₀, ha₀⟩ := surjective_units_map_of_local_ringHom (residue R) residue_surjective
    inferInstance α
  have ha₀' : residue R ((a₀ : Rˣ) : R) = (α : ResidueField R) := congrArg Units.val ha₀
  have hαpow : ((α : ResidueField R)) ^ n = 1 := (mem_rootsOfUnity' n _).mp hα
  by_cases hn0 : n = 0
  · subst hn0
    exact ⟨⟨a₀, (mem_rootsOfUnity 0 a₀).mpr (pow_zero _)⟩, by ext; simpa using ha₀'⟩
  · obtain ⟨p, hp⟩ : ∃ p, ExpChar (ResidueField R) p := ⟨_, ringExpChar.expChar _⟩
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
    obtain ⟨a, ha, hres⟩ := HenselianLocalRing.exists_pow_eq_of_residue_pow_eq hm a₀.isUnit
      (u := 1) (by
        rw [ha₀', map_one]
        exact (ExpChar.pow_prime_pow_mul_eq_one_iff p k m _).mp hαpow)
    have : NeZero (p ^ k * m) := ⟨hn0⟩
    refine ⟨rootsOfUnity.mkOfPowEq a (by rw [pow_mul', ha, one_pow]), ?_⟩
    ext
    simpa [hres] using ha₀'

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
