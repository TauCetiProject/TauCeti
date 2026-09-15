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

Surjectivity is Hensel's lemma applied to `X ^ n - 1`, whose roots are simple exactly because
`n` is invertible.

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

/-- **Every root of unity of invertible order in the residue field lifts**, by Hensel's lemma
applied to `X ^ n - 1`. -/
theorem rootsOfUnityResidue_surjective {n : ℕ} (hn : IsUnit (n : R)) :
    Function.Surjective (rootsOfUnityResidue (R := R) n) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero] at hn
    exact not_isUnit_zero (M₀ := R) hn
  have : NeZero n := ⟨hn0⟩
  rintro ⟨α, hα⟩
  obtain ⟨a₀, ha₀⟩ := surjective_units_map_of_local_ringHom (residue R) residue_surjective
    inferInstance α
  have ha₀' : residue R ((a₀ : Rˣ) : R) = (α : ResidueField R) := congrArg Units.val ha₀
  have hαpow : ((α : ResidueField R)) ^ n = 1 := (mem_rootsOfUnity' n _).mp hα
  have hroot : (X ^ n - C 1 : R[X]).eval ((a₀ : Rˣ) : R) ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff]
    simp [map_pow, ha₀', hαpow]
  have hderiv : IsUnit ((X ^ n - C 1 : R[X]).derivative.eval ((a₀ : Rˣ) : R)) := by
    simpa [derivative_X_pow] using hn.mul (a₀.isUnit.pow (n - 1))
  obtain ⟨a, ha, hmem⟩ := HenselianLocalRing.is_henselian (X ^ n - C 1 : R[X])
    (monic_X_pow_sub_C 1 hn0) ((a₀ : Rˣ) : R) hroot hderiv
  have hpow : a ^ n = 1 := by
    have h := ha
    simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at h
    exact h
  refine ⟨rootsOfUnity.mkOfPowEq a hpow, ?_⟩
  have hres : residue R a = (α : ResidueField R) := by
    rw [← ha₀', ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hmem
  ext
  simpa using hres

/-- Reduction is a bijection on roots of unity of invertible order. -/
theorem rootsOfUnityResidue_bijective {n : ℕ}
    (hn : IsUnit (n : R)) : Function.Bijective (rootsOfUnityResidue (R := R) n) :=
  ⟨rootsOfUnityResidue_injective hn, rootsOfUnityResidue_surjective hn⟩

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
