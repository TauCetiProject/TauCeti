/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Cyclotomic.Completion
import TauCeti.RingTheory.RootsOfUnity.LocalRing

/-!
# Checks for the completions of a cyclotomic field at a place over `p`

* `e = 1`: `F = ℚ`, and at every place over `p` the residue field is `𝔽_p`.
* `e = 3`, `p = 3`: `e' = 1`, and at every place over `3` the residue field has `3` elements.
* `e = 3`, `p = 2`: the residue field contains a primitive cube root of unity, the reduction of
  `complexRoot 3`, so it has at least `4` elements; `𝔽₂` contains no root of `X² + X + 1`.
* `e = 3`, `p = 7`: since `7 ≡ 1 mod 3`, at every place `v` over `7` the local degree
  `[F_v : ℚ₇]` is `1`, the completion map from `ℚ₇` to `F_v` is bijective, and `F_v ≅ ℚ₇`.
* The isomorphism on `e`-th roots of unity is the canonical map `F → F_v`.
-/

open IsDedekindDomain NumberField IsLocalRing TauCeti.Cyclotomic

namespace TauCeti.Examples.CyclotomicCompletion

example : complexField 1 = ⊥ := by simp

example (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 (complexField 1)))
    (hv : (p : 𝓞 (complexField 1)) ∈ v.asIdeal) :
    Nat.card (ResidueField (v.adicCompletionIntegers (complexField 1))) = p :=
  natCard_residueField_of_ordCompl_eq_one v p hv (by simp)

example (v : HeightOneSpectrum (𝓞 (complexField 3)))
    (hv : (3 : 𝓞 (complexField 3)) ∈ v.asIdeal) :
    Nat.card (ResidueField (v.adicCompletionIntegers (complexField 3))) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact natCard_residueField_of_ordCompl_eq_one v 3 (mod_cast hv)
    (by simp [Nat.Prime.factorization_self Nat.prime_three])

example (v : HeightOneSpectrum (𝓞 (complexField 3)))
    (hv : (2 : 𝓞 (complexField 3)) ∈ v.asIdeal) :
    4 ≤ Nat.card (ResidueField (v.adicCompletionIntegers (complexField 3))) := by
  set O := v.adicCompletionIntegers (complexField 3)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3v : ((3 : ℕ) : 𝓞 (complexField 3)) ∉ v.asIdeal := fun h ↦ v.isPrime.ne_top <| by
    rw [Ideal.eq_top_iff_one, show (1 : 𝓞 (complexField 3)) = (3 : ℕ) - 2 by norm_num]
    exact sub_mem h hv
  have h3 : IsUnit ((3 : ℕ) : O) := by
    rw [← map_natCast (algebraMap (𝓞 (complexField 3)) O)]
    exact (v.isUnit_algebraMap_adicCompletionIntegers_iff _).2 h3v
  have hr := (isPrimitiveRoot_algebraMap_zetaInteger v).map_residue h3
  have hcard := hr.card_rootsOfUnity
  have hle : Nat.card (rootsOfUnity 3 (ResidueField O)) ≤ Nat.card (ResidueField O)ˣ :=
    Subgroup.card_le_card_group _
  rw [Nat.card_units] at hle
  omega

section Seven

open Rat.HeightOneSpectrum (primesEquiv)
open scoped AdicCompletionExtension

example (v : HeightOneSpectrum (𝓞 (complexField 3)))
    [v.asIdeal.LiesOver ((primesEquiv (R := ℤ)).symm ⟨7, Nat.prime_seven⟩).asIdeal] :
    Module.finrank (((primesEquiv (R := ℤ)).symm ⟨7, Nat.prime_seven⟩).adicCompletion ℚ)
      (v.adicCompletion (complexField 3)) = 1 := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  rw [finrank_adicCompletion_eq_orderOf v 7 (by norm_num),
    show ((7 : ℕ) : ZMod 3) = 1 by decide, orderOf_one]

example (v : HeightOneSpectrum (𝓞 (complexField 3)))
    [v.asIdeal.LiesOver ((primesEquiv (R := ℤ)).symm ⟨7, Nat.prime_seven⟩).asIdeal] :
    Function.Bijective (HeightOneSpectrum.adicCompletionExtension ℚ (complexField 3)
      ((primesEquiv (R := ℤ)).symm ⟨7, Nat.prime_seven⟩) v) :=
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  adicCompletionExtension_bijective v 7 (by decide)

example [Fact (Nat.Prime 7)] (v : HeightOneSpectrum (𝓞 (complexField 3)))
    (hv : (7 : 𝓞 (complexField 3)) ∈ v.asIdeal) :
    Nonempty (v.adicCompletion (complexField 3) ≃+* ℚ_[7]) :=
  nonempty_ringEquiv_padic v 7 (by decide) (mod_cast hv)

end Seven

example (e : ℕ) [NeZero e] (v : HeightOneSpectrum (𝓞 (complexField e)))
    (ζ : rootsOfUnity e (complexField e)) :
    ((rootsOfUnityEquivOfPrimitiveRoots (FinitePlace.embedding v).injective
        ⟨_, (mem_primitiveRoots (NeZero.pos e)).2 (complexField.isPrimitiveRoot_zeta e)⟩ ζ :
        (v.adicCompletion (complexField e))ˣ) : v.adicCompletion (complexField e)) =
      FinitePlace.embedding v ((ζ : (complexField e)ˣ) : complexField e) :=
  val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe _ _ ζ

end TauCeti.Examples.CyclotomicCompletion
