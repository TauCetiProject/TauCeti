/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Roots of unity in the ring of integers of a cyclotomic field

If `K` is an `n`-th cyclotomic extension of `ℚ`, then its ring of integers `𝓞 K` contains the
primitive `n`-th root of unity `IsCyclotomicExtension.zeta n ℚ K`, and, being a domain, has a cyclic
group of `n`-th roots of unity. So `𝓞 K` satisfies `HasEnoughRootsOfUnity (𝓞 K) n`, the hypothesis
under which the `n`-th power residue symbol `Ideal.powerResidueSymbol` is defined.
-/

public section

open NumberField

namespace NumberField.RingOfIntegers

/-- The ring of integers of an `n`-th cyclotomic field over `ℚ` contains a primitive `n`-th root of
unity. -/
instance hasEnoughRootsOfUnity_of_isCyclotomicExtension {n : ℕ} [NeZero n] {K : Type*} [Field K]
    [CharZero K] [IsCyclotomicExtension {n} ℚ K] : HasEnoughRootsOfUnity (𝓞 K) n where
  prim := ⟨_, (IsCyclotomicExtension.zeta_spec n ℚ K).toInteger_isPrimitiveRoot⟩
  cyc := rootsOfUnity.isCyclic _ _

end NumberField.RingOfIntegers
