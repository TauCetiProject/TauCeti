/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Homology.ModuleCat.CompletelyFlat
import TauCeti.Examples.RingTheory.Flat.CompletelyFlat
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Checks for complete flatness in the derived category

For every integer `p`, the ring `ℤ` placed in degree zero of `D(ℤ)` is `p`-completely flat, being a
flat `ℤ`-module, and so has `p`-complete Tor-amplitude `[0, 0]`. For a prime `p`, the `p`-adic
integers `ℤ_p` placed in degree zero are `p`-completely faithfully flat: `ℤ_p` is flat over `ℤ`, so
this is the module statement, and `F_p ⊗ ℤ_p` is a nonzero `F_p`-vector space.
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

end Padic

end TauCeti.Examples
