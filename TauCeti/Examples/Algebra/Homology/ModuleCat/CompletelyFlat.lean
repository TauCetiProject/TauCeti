/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Homology.ModuleCat.CompletelyFlat.Basic
import TauCeti.Algebra.Homology.ModuleCat.CompletelyFlat.RegularElement
import TauCeti.Examples.RingTheory.Flat.CompletelyFlat
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Checks for complete flatness in the derived category

For every integer `p`, the ring `ℤ` placed in degree zero of `D(ℤ)` is `p`-completely flat, being a
flat `ℤ`-module, and so has `p`-complete Tor-amplitude `[0, 0]`. For a prime `p`, the `p`-adic
integers `ℤ_p` placed in degree zero are `p`-completely faithfully flat: `ℤ_p` is flat over `ℤ`, so
this is the module statement, and `F_p ⊗ ℤ_p` is a nonzero `F_p`-vector space. On the other hand
`F_p = ℤ ⧸ (p)` placed in degree zero is not `p`-completely flat over `ℤ`: `F_p ⊗^L_ℤ F_p` has the
nonzero term `F_p` in degree `-1`. The same holds for `ℤ_p ⧸ (p)` over `ℤ_p`.
-/

universe w w'

namespace TauCeti.Examples

open CategoryTheory DerivedCategory TauCeti.DerivedDeRham

variable (p : ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (ℤ ⧸ Ideal.span {p}))]

-- `ℤ[0]` is `p`-completely flat in `D(ℤ)`.
example : IsCompletelyFlat (Ideal.span {p}) ((singleFunctor (ModuleCat ℤ) 0).obj (.of ℤ ℤ)) :=
  ModuleCat.isCompletelyFlat_single _

-- `ℤ[0]` has `p`-complete Tor-amplitude `[0, 0]`.
example : HasCompleteTorAmplitude (Ideal.span {p}) 0 0
    ((singleFunctor (ModuleCat ℤ) 0).obj (.of ℤ ℤ)) :=
  (ModuleCat.isCompletelyFlat_single _).hasCompleteTorAmplitude

section Padic

variable (p : ℕ) [Fact p.Prime]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (ℤ ⧸ Ideal.span {(p : ℤ)}))]

-- `ℤ_p[0]` is `p`-completely faithfully flat in `D(ℤ)`.
example : IsCompletelyFaithfullyFlat (Ideal.span {(p : ℤ)})
    ((singleFunctor (ModuleCat ℤ) 0).obj (.of ℤ ℤ_[p])) :=
  (ModuleCat.isCompletelyFaithfullyFlat_single_iff _).mpr
    (isCompletelyFaithfullyFlatModule_padicInt p)

-- `F_p ⊗^L_ℤ F_p` has a nonzero term in degree `-1`, so `F_p[0]` is not `p`-completely flat in
-- `D(ℤ)`.
example : ¬ Limits.IsZero ((homologyFunctor (ModuleCat (ℤ ⧸ Ideal.span {(p : ℤ)})) (-1)).obj
      ((derivedReduction (Ideal.span {(p : ℤ)})).obj
        ((singleFunctor (ModuleCat ℤ) 0).obj (.of ℤ (ℤ ⧸ Ideal.span {(p : ℤ)}))))) ∧
    ¬ IsCompletelyFlat (Ideal.span {(p : ℤ)})
      ((singleFunctor (ModuleCat ℤ) 0).obj (.of ℤ (ℤ ⧸ Ideal.span {(p : ℤ)}))) :=
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hf := mem_nonZeroDivisors_of_ne_zero hp.ne_zero
  have hI := Ideal.span_singleton_ne_top hp.not_isUnit
  ⟨not_isZero_homology_derivedReduction_quotient hf hI, not_isCompletelyFlat_quotient_self hf hI⟩

-- `(ℤ_p ⧸ p)[0]` is not `p`-completely flat in `D(ℤ_p)`.
example [HasDerivedCategory.{w} (ModuleCat.{0} ℤ_[p])]
    [HasDerivedCategory.{w'} (ModuleCat.{0} (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}))] :
    ¬ IsCompletelyFlat (Ideal.span {(p : ℤ_[p])})
      ((singleFunctor (ModuleCat ℤ_[p]) 0).obj (.of ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}))) :=
  not_isCompletelyFlat_quotient_self (mem_nonZeroDivisors_of_ne_zero PadicInt.prime_p.ne_zero)
    (Ideal.span_singleton_ne_top PadicInt.prime_p.not_isUnit)

end Padic

end TauCeti.Examples
