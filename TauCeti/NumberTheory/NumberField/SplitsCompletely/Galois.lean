/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.SplitsCompletely.Basic

/-!
# The Galois torsor of a completely split prime

Choosing one prime above a completely split rational prime identifies its fiber with
the Galois group via the orbit map. The identification retains the actual action on primes.
-/

public section

open NumberField MulAction
open scoped Pointwise

namespace Ideal

variable {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E]

/-- Under complete splitting, evaluating a Galois automorphism at `Q` gives a bijection
from the Galois group to the primes above `P`. -/
noncomputable def galEquivPrimesOver (P : Ideal ℤ)
    (Q : P.primesOver (𝓞 E)) (hP : (P.primesOver (𝓞 E)).ncard = Module.finrank ℚ E) :
    Gal(E/ℚ) ≃ P.primesOver (𝓞 E) := by
  have := Q.prop.1
  have := Q.prop.2
  have h := (ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot ℚ E P Q.val).mp hP
  have hsmul (g : Gal(E/ℚ)) : (g • Q).val = g • Q.val := by
    rw [coe_smul_primesOver_eq_map_galRestrict, pointwise_smul_def]
    apply congrArg (fun f : 𝓞 E →+* 𝓞 E ↦ Q.val.map f)
    exact RingHom.ext fun x ↦ RingOfIntegers.coe_injective (algebraMap_galRestrict_apply ℤ g x)
  refine Equiv.ofBijective (fun g ↦ g • Q) ⟨?_, ?_⟩
  · intro g g' hgg'
    have hm : g'⁻¹ * g ∈ stabilizer Gal(E/ℚ) Q.val := by
      have he := (hsmul g).symm.trans ((congrArg Subtype.val hgg').trans (hsmul g'))
      rw [mem_stabilizer_iff, mul_smul, he, inv_smul_smul]
    rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hm
    exact hm.symm
  · intro R
    have := R.prop.1
    have := R.prop.2
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isGaloisGroup P Q.val R.val Gal(E/ℚ)
    exact ⟨g, Subtype.ext ((hsmul g).trans hg)⟩

/-- The Galois torsor bijection evaluates an automorphism at the chosen prime. -/
@[simp]
theorem galEquivPrimesOver_apply (P : Ideal ℤ)
    (Q : P.primesOver (𝓞 E)) (hP : (P.primesOver (𝓞 E)).ncard = Module.finrank ℚ E)
    (g : Gal(E/ℚ)) : P.galEquivPrimesOver Q hP g = g • Q := (rfl)

end Ideal
