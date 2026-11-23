/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Finite

/-!
# Étale field extensions

Mathlib's `Algebra.FormallyEtale.of_isSeparable` shows that a separable field extension is
formally étale. This file adds the finiteness condition: a finite separable field extension is
étale (`Algebra.Etale.of_isSeparable`) and packages it as an object of `CommAlgCat.FiniteEtale`
(`CommAlgCat.FiniteEtale.ofSeparableFieldExt`).
-/

public section

universe u

namespace Algebra.Etale

/-- **A finite separable field extension is étale.** -/
theorem of_isSeparable (K L : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra.IsSeparable K L] : Algebra.Etale K L :=
  ⟨FormallyEtale.of_isSeparable K L, FinitePresentation.of_finiteType.mp inferInstance⟩

end Algebra.Etale

namespace CommAlgCat.FiniteEtale

/-- A finite separable field extension `L / K` is a finite étale `K`-algebra. -/
-- Exposed so that `(ofSeparableFieldExt K L).obj` unfolds definitionally to `L` in downstream
-- statements about `L →ₐ[K] Ω`.
@[expose] noncomputable def ofSeparableFieldExt (K L : Type u) [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L] :
    CommAlgCat.FiniteEtale.{u} K :=
  have : Algebra.Etale K L := Algebra.Etale.of_isSeparable K L
  CommAlgCat.FiniteEtale.of K L

end CommAlgCat.FiniteEtale
