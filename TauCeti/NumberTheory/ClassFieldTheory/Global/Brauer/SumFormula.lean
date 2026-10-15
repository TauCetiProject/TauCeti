/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.Compositum
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.Splitting
import TauCeti.NumberTheory.Cyclotomic.Adjoin
import TauCeti.RepresentationTheory.Homological.ContCohomology.Torsion

/-!
# The sum of the local invariants of a Brauer class, from the Hasse principle

Let `K` be a number field. The global Brauer sequence

```text
0 → Br K → ⨁_v Br K_v → ℚ/ℤ → 0
```

has zero composite `Br K → ℚ/ℤ` exactly when the local invariants of every global Brauer class
sum to zero; this is the inclusion of the image of `Br K` in the kernel of the sum, one half of
exactness in the middle. This file proves that sum formula for every class of `Br K`, assuming the
Hasse principle, injectivity of `Br E → ⨁_w Br E_w`, for the finite extensions `E` of `K`
(`sumLocalInv_brLocalization_eq_zero_of_brLocalization_injective`). The Hasse principle itself
follows from the vanishing of idele-class `H¹`
(`TauCeti.ClassFieldTheory.brLocalization_injective_of_subsingleton_groupCohomology_one`).

The argument is Milne's Lemma 8.6. A Brauer class is torsion, so it is a sum of classes killed by
powers of primes, and the sum of the local invariants is additive. Let `x` be killed by a power
of a prime `ℓ`. For `r` large, the cyclotomic field `K(μ_{ℓ^r})` contains a cyclic extension `E`
of `K` that kills every localization of `x`
(`TauCeti.ClassFieldTheory.eventually_exists_isCyclic_brLocalization_eq_zero`). By the Hasse
principle over `E`, the class `x` itself dies in `E`, so it is inflated from
`H²(Gal(E/K), Eˣ)` (`TauCeti.ClassFieldTheory.mem_range_relBrInfl_iff_brBaseChange_eq_zero`).
For classes split by a cyclic subextension of a cyclotomic extension, the sum formula comes from
the product formula for the local Artin symbols on cyclotomic extensions
(`TauCeti.ClassFieldTheory.sumLocalInv_brLocalization_relBrInfl_eq_zero_of_le_adjoin_nth_roots`).

## Main results

* `TauCeti.ClassFieldTheory.sumLocalInv_brLocalization_eq_zero_of_brLocalization_injective`: if
  the Hasse principle holds over every finite extension of `K`, then the local invariants of
  every Brauer class of `K` sum to zero.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Lemma 8.6 and Theorem 8.1, and
  Chapter VIII, Theorem 4.2.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.IntermediateField

variable (K : Type) [Field K] [NumberField K]

/-- The sum formula for a class killed by a power of a prime, from the Hasse principle over the
finite extensions of `K`. -/
private theorem sumLocalInv_brLocalization_eq_zero_of_pow_nsmul_eq_zero
    (h : ∀ (E : Type) [Field E] [NumberField E] [Algebra K E],
      Function.Injective (brLocalization E))
    {ℓ : ℕ} (hℓ : ℓ.Prime) {k : ℕ} (x : Br K) (hx : ℓ ^ k • x = 0) :
    sumLocalInv K (brLocalization K x) = 0 := by
  obtain ⟨r, hr⟩ := (eventually_exists_isCyclic_brLocalization_eq_zero K hℓ x hx).exists
  have : NeZero (ℓ ^ r) := ⟨pow_ne_zero r hℓ.ne_zero⟩
  -- The cyclotomic field `C = K(μ_{ℓ^r})` inside `Kˢ`.
  set C : IntermediateField K (SeparableClosure K) := adjoin K {b | b ^ (ℓ ^ r) = 1}
  have : IsCyclotomicExtension {ℓ ^ r} K C :=
    (HasEnoughRootsOfUnity.prim (M := SeparableClosure K) (n := ℓ ^ r)).choose_spec
      |>.isCyclotomicExtension_adjoin_nth_roots
  have : FiniteDimensional K C := IsCyclotomicExtension.finiteDimensional {ℓ ^ r} K C
  have : NumberField C := NumberField.of_module_finite K C
  obtain ⟨E, _, _, hE⟩ := hr C
  -- By the Hasse principle over `E`, the class `x` dies in `E`, hence in its copy `E'` in `Kˢ`.
  have hxE : brBaseChange K E x = 0 := h E (hE.trans (map_zero _).symm)
  set E' : IntermediateField K (SeparableClosure K) := lift E
  let e : E ≃ₐ[K] E' := liftAlgEquiv E
  have : FiniteDimensional K E' := e.toLinearEquiv.finiteDimensional
  have : IsGalois K E' := IsGalois.of_algEquiv e
  have : IsCyclic Gal(E'/K) := isCyclic_of_surjective e.autCongr e.autCongr.surjective
  obtain ⟨y, rfl⟩ := (mem_range_relBrInfl_iff_brBaseChange_eq_zero K E' E'.val x).2
    (brBaseChange_eq_zero_of_algHom e.toAlgHom hxE)
  exact sumLocalInv_brLocalization_relBrInfl_eq_zero_of_le_adjoin_nth_roots E' (NeZero.ne _)
    (lift_le E) y

/-- **The sum formula, from the Hasse principle.** If, for every finite extension `E` of the
number field `K`, a Brauer class of `E` with trivial localizations at all places is zero, then the
local invariants of every Brauer class of `K` sum to zero. -/
theorem sumLocalInv_brLocalization_eq_zero_of_brLocalization_injective
    (h : ∀ (E : Type) [Field E] [NumberField E] [Algebra K E],
      Function.Injective (brLocalization E))
    (x : Br K) : sumLocalInv K (brLocalization K x) = 0 := by
  -- Induction on an exponent `n` killing `x`, splitting `x` along coprime factors of `n`.
  suffices H : ∀ n : ℕ, 0 < n → ∀ x : Br K, n • x = 0 → sumLocalInv K (brLocalization K x) = 0 by
    obtain ⟨n, hn, hx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp
      (ContinuousCohomology.isAddTorsion_continuousCohomology (X := unitsRep K) 1 x)
    exact H n hn x hx
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow ℓ k hℓ _ =>
    exact fun _ x hx ↦ sumLocalInv_brLocalization_eq_zero_of_pow_nsmul_eq_zero K h hℓ x hx
  | zero => exact fun h0 ↦ absurd h0 (lt_irrefl 0)
  | one =>
    intro _ x hx
    rw [one_nsmul] at hx
    rw [hx, map_zero, map_zero]
  | coprime a b ha hb hab iha ihb =>
    intro _ x hx
    -- With `u a + v b = 1`, the class `x` is `(u a) x + (v b) x`, killed by `b` and `a`.
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
    have hx' : ((a : ℤ) * b) • x = 0 := by exact_mod_cast hx
    have hxa : a • ((v * b) • x) = 0 := by
      rw [← natCast_zsmul, smul_smul, show (a : ℤ) * (v * b) = v * (a * b) by ring, mul_zsmul,
        hx', zsmul_zero]
    have hxb : b • ((u * a) • x) = 0 := by
      rw [← natCast_zsmul, smul_smul, show (b : ℤ) * (u * a) = u * (a * b) by ring, mul_zsmul,
        hx', zsmul_zero]
    rw [show x = (u * a) • x + (v * b) • x by rw [← add_zsmul, huv, one_zsmul], map_add, map_add,
      ihb (by omega) _ hxb, iha (by omega) _ hxa, add_zero]

end TauCeti.ClassFieldTheory
