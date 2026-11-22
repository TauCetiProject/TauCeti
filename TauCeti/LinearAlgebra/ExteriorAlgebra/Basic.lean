/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-! # Basic extensionality for exterior algebras -/

public section
namespace ExteriorAlgebra

/-- Two ring homomorphisms out of `ExteriorAlgebra R M` agreeing on `algebraMap R` and `ι R` are
equal. -/
theorem ringHom_ext {R M S : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Semiring S]
    {f₁ f₂ : ExteriorAlgebra R M →+* S}
    (halg : ∀ a, f₁ (algebraMap R _ a) = f₂ (algebraMap R _ a))
    (hι : ∀ m, f₁ (ι R m) = f₂ (ι R m)) : f₁ = f₂ := by
  ext x; induction x using ExteriorAlgebra.induction with
  | algebraMap a => exact halg a
  | ι m => exact hι m
  | mul _ _ hx hy | add _ _ hx hy => simp [hx, hy]
end ExteriorAlgebra
