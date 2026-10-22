/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Field

/-!
# Étale field extensions

Mathlib's `Algebra.FormallyEtale.of_isSeparable` shows that a separable field extension is
formally étale. This file adds the finiteness condition: a finite separable field extension is
étale (`Algebra.Etale.of_isSeparable`).
-/

public section

namespace Algebra.Etale

/-- **A finite separable field extension is étale.** -/
theorem of_isSeparable (K L : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra.IsSeparable K L] : Algebra.Etale K L :=
  ⟨FormallyEtale.of_isSeparable K L, FinitePresentation.of_finiteType.mp inferInstance⟩

end Algebra.Etale
