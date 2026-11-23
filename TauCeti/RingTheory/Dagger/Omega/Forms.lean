/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.RingTheory.Dagger.Omega.Basic

/-!
# Exterior forms of universally finite differentials

Records degreewise vanishing results for exterior powers `⋀[A]^q (Omega R A)` without
requiring the exterior derivative or the de Rham complex: over a complete ultrametric normed field
`K`, the exterior powers of `Omega K (washnitzerAlgebra σ K)` vanish in degrees strictly above
`Nat.card σ`.
-/

public section

namespace TauCeti.Dagger.Omega

section Washnitzer

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- On `washnitzerAlgebra σ K` over a complete ultrametric normed field `K`, every exterior power
of `Omega` above `Nat.card σ` vanishes. -/
theorem subsingleton_forms_washnitzer_of_card_lt [Finite σ] {q : ℕ} (hq : Nat.card σ < q) :
    Subsingleton (⋀[washnitzerAlgebra σ K]^q (Omega K (washnitzerAlgebra σ K))) :=
  exteriorPower.subsingleton_of_span_eq_top_of_card_lt (washnitzerBasis σ K)
    (washnitzerBasis σ K).span_eq q hq

end Washnitzer

end TauCeti.Dagger.Omega
