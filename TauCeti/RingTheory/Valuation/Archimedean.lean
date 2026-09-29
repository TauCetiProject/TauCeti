/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.RankOne

/-!
# Archimedean value groups of valuations

An `ℝ≥0`-valued valuation has an archimedean value group, by restriction along its strictly
monotone value-group embedding.
-/

public section

open scoped NNReal

namespace TauCeti

/-- The value group of an `ℝ≥0`-valued valuation is archimedean. -/
theorem mulArchimedean_valueGroup₀ {A : Type*} [CommRing A] (v : Valuation A ℝ≥0) :
    MulArchimedean v.ValueGroup₀ :=
  MulArchimedean.comap MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom
    MonoidWithZeroHom.ValueGroup₀.embedding_strictMono

end TauCeti
