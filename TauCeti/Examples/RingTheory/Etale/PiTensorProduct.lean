/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import TauCeti.RingTheory.Etale.PiTensorProduct
import TauCeti.RingTheory.Etale.Idempotent

/-!
# Checks for étale indexed tensor products

These examples check finite tensor powers, their idempotent components, empty products, and
localizations which need not be finite over the base. The idempotent-component case is the
algebraic operation used to select ordered distinct tuples from a tensor power.
-/

open scoped TensorProduct

namespace TauCeti.Examples.PiTensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Finite tensor powers of finite étale algebras are finite. -/
example [Module.Finite R S] (n : ℕ) : Module.Finite R (⨂[R] _ : Fin n, S) :=
  inferInstance

/-- Finite tensor powers of étale algebras are étale. -/
example [Algebra.Etale R S] (n : ℕ) : Algebra.Etale R (⨂[R] _ : Fin n, S) :=
  inferInstance

/-- Idempotent components of tensor powers remain finite étale. -/
example [Algebra.Etale R S] [Module.Finite R S] (n : ℕ)
    (e : ⨂[R] _ : Fin n, S) (he : IsIdempotentElem e) :
    Module.Finite R ((⨂[R] _ : Fin n, S) ⧸ Ideal.span {1 - e}) ∧
      Algebra.Etale R ((⨂[R] _ : Fin n, S) ⧸ Ideal.span {1 - e}) :=
  ⟨inferInstance, Algebra.Etale.quotient_span_singleton he.one_sub⟩

/-- The empty product is étale without assumptions on the nominal factor algebra. -/
example : Algebra.Etale R (⨂[R] _ : Fin 0, S) := by
  let (i : Fin 0) : Algebra.Etale R S := Fin.elim0 i
  infer_instance

/-- The result does not require module-finite factors: localizations away from elements suffice. -/
example {ι : Type*} [Finite ι] (r : ι → R) :
    Algebra.Etale R (⨂[R] i, Localization.Away (r i)) :=
  inferInstance

/-- Splitting one factor preserves the labelled entries, even when all factor types coincide. -/
example (a : Option (Fin 2) → R) :
    PiTensorProduct.optionAlgEquiv (R := R) (fun _ : Option (Fin 2) ↦ R)
        (PiTensorProduct.tprod R a) =
      PiTensorProduct.tprod R (fun i ↦ a (some i)) ⊗ₜ a none := by
  simp

end TauCeti.Examples.PiTensorProduct
