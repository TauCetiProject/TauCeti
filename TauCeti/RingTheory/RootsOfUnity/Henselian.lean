/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Roots of unity of order invertible in a Henselian local domain

Reduction modulo the maximal ideal of a Henselian local domain `R` identifies the `n`-th roots
of unity of `R` with those of its residue field, whenever `n` is invertible in `R`.

Injectivity holds in any commutative domain: a root of unity congruent to `1` modulo a proper
ideal `I` forces its order into `I`, because the geometric sum attached to the root of unity
vanishes and is congruent to that order. Surjectivity is Hensel's lemma applied to `X ^ n - 1`,
whose roots are simple exactly because `n` is invertible.

## Main results

* `TauCeti.eq_one_of_pow_eq_one_of_sub_one_mem`: in a domain, a root of unity of invertible order
  that is congruent to `1` modulo a proper ideal is `1`.
* `TauCeti.rootsOfUnityResidue`: the reduction homomorphism on roots of unity.
* `TauCeti.rootsOfUnityResidue_bijective` and `TauCeti.rootsOfUnityEquivResidueField`: reduction
  is a bijection, and the resulting isomorphism with the roots of unity of the residue field.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §4.
-/

public section

noncomputable section

open IsLocalRing Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- In a commutative domain, a root of unity whose order is invertible and which is congruent to
`1` modulo a proper ideal is equal to `1`. -/
theorem eq_one_of_pow_eq_one_of_sub_one_mem [IsDomain R] {I : Ideal R} (hI : I ≠ ⊤) {n : ℕ}
    (hn : IsUnit (n : R)) {ζ : R} (hζ : ζ ^ n = 1) (hmem : ζ - 1 ∈ I) : ζ = 1 := by
  by_contra hne
  have hgeom : ∑ i ∈ Finset.range n, ζ ^ i = 0 := by
    have h := geom_sum_mul ζ n
    rw [hζ, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  have hres : Ideal.Quotient.mk I ζ = 1 := by
    have h : Ideal.Quotient.mk I (ζ - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rwa [map_sub, map_one, sub_eq_zero] at h
  refine hI (I.eq_top_of_isUnit_mem ?_ hn)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  have h := congrArg (Ideal.Quotient.mk I) hgeom
  rw [map_sum, map_zero] at h
  simpa [map_pow, hres] using h

section LocalRing

variable [IsLocalRing R]

/-- Reduction modulo the maximal ideal, as a homomorphism between the groups of `n`-th roots of
unity of a local ring and of its residue field. -/
def rootsOfUnityResidue (n : ℕ) :
    rootsOfUnity n R →* rootsOfUnity n (ResidueField R) :=
  ((Units.map (residue R).toMonoidHom).comp (rootsOfUnity n R).subtype).codRestrict _
    fun ζ ↦ by simpa [← map_pow] using congrArg (Units.map (residue R).toMonoidHom) ζ.2

/-- The value of the reduction homomorphism on roots of unity. -/
@[simp]
theorem coe_rootsOfUnityResidue (n : ℕ) (ζ : rootsOfUnity n R) :
    ((rootsOfUnityResidue n ζ : (ResidueField R)ˣ) : ResidueField R) =
      residue R ((ζ : Rˣ) : R) :=
  (rfl)

/-- **Distinct roots of unity of invertible order have distinct reductions.** -/
theorem rootsOfUnityResidue_injective [IsDomain R] {n : ℕ} (hn : IsUnit (n : R)) :
    Function.Injective (rootsOfUnityResidue (R := R) n) := by
  refine (injective_iff_map_eq_one _).mpr fun ζ hζ ↦ ?_
  have hval : residue R ((ζ : Rˣ) : R) = 1 := by
    have h := congrArg
      (fun x : rootsOfUnity n (ResidueField R) ↦ ((x : (ResidueField R)ˣ) : ResidueField R)) hζ
    simpa using h
  have hsub : ((ζ : Rˣ) : R) - 1 ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, hval, map_one, sub_self]
  have hpow : ((ζ : Rˣ) : R) ^ n = 1 := (mem_rootsOfUnity' n _).mp ζ.2
  ext
  exact eq_one_of_pow_eq_one_of_sub_one_mem (maximalIdeal.isMaximal R).ne_top hn hpow hsub

end LocalRing

section Henselian

variable [HenselianLocalRing R]

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
theorem rootsOfUnityResidue_bijective [IsDomain R] {n : ℕ}
    (hn : IsUnit (n : R)) : Function.Bijective (rootsOfUnityResidue (R := R) n) :=
  ⟨rootsOfUnityResidue_injective hn, rootsOfUnityResidue_surjective hn⟩

/-- **Roots of unity of invertible order lift uniquely along the residue map of a Henselian local
domain**: reduction is an isomorphism between the `n`-th roots of unity of `R` and those of its
residue field. -/
def rootsOfUnityEquivResidueField [IsDomain R] {n : ℕ}
    (hn : IsUnit (n : R)) : rootsOfUnity n R ≃* rootsOfUnity n (ResidueField R) :=
  MulEquiv.ofBijective _ (rootsOfUnityResidue_bijective hn)

/-- The value of `rootsOfUnityEquivResidueField` is the reduction of the root of unity. -/
@[simp]
theorem coe_rootsOfUnityEquivResidueField [IsDomain R] {n : ℕ}
    (hn : IsUnit (n : R)) (ζ : rootsOfUnity n R) :
    ((rootsOfUnityEquivResidueField hn ζ : (ResidueField R)ˣ) : ResidueField R) =
      residue R ((ζ : Rˣ) : R) :=
  (rfl)

end Henselian

end TauCeti
