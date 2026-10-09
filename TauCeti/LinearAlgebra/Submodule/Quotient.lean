/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Lifting cyclic submodules from quotients

Pulling back the span of a quotient class and then mapping it along a linear map gives the
image of the quotient kernel plus the span of the image of a representative. This identifies
the underlying submodule when lifting a cyclic submodule of a subquotient, for example an
eigenline, into the ambient module.
-/

public section

namespace Submodule

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Mapping the inverse image of the span of a quotient class gives the image of the
quotient kernel plus the span of the image of a representative. -/
theorem map_comap_mkQ_span_singleton (S : Submodule R M) (f : M →ₗ[R] N) (v : M) :
    ((R ∙ S.mkQ v).comap S.mkQ).map f = S.map f ⊔ R ∙ f v := by
  have hspan : (R ∙ v).map S.mkQ = R ∙ S.mkQ v := by
    simp [Submodule.map_span]
  rw [← hspan, Submodule.comap_map_mkQ, Submodule.map_sup]
  simp [Submodule.map_span]

end Submodule
