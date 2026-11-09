/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Cofinite kernels of Lie algebra maps into finite associative algebras

A Lie algebra map `f : L →ₗ⁅R⁆ A` into an associative algebra extends along the universal property
to an algebra homomorphism `UniversalEnvelopingAlgebra.lift R f`.  The motivating case is a
representation `ρ : L →ₗ⁅K⁆ Module.End K V` over a field, but nothing below uses the endomorphism
structure, so the results are stated for an arbitrary associative target.  When `A` is a Noetherian
`R`-module (for instance, finite-dimensional over a field), the kernel of this extension is
cofinite: its quotient embeds linearly in `A`, so it is a finite `R`-module.  As a ring-homomorphism
kernel it is automatically a two-sided ideal in Mathlib's ideal API.

The same kernel records nilpotence of the original map.  For `x : L`, the element `f x` is
nilpotent exactly when some power of the canonical generator `ι R x` belongs to the kernel.  This is
the form needed when a finite-dimensional representation is replaced by a smaller ideal while
preserving nilpotence of selected operators.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.finite_quotient_ker_lift`: the quotient of the enveloping
  algebra by the kernel of `lift R f` is a finite `R`-module when `A` is a Noetherian `R`-module.
* `TauCeti.UniversalEnvelopingAlgebra.isNilpotent_iff_exists_pow_ι_mem_ker_lift`: nilpotence of
  the image of an element is equivalent to membership of a power of its enveloping generator in
  the kernel.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra (lift ι)

universe u v w

variable (R : Type u) {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
variable {A : Type w} [Ring A] [Algebra R A]

/-- The quotient by the kernel of the enveloping-algebra extension of a Lie algebra map into an
associative algebra that is Noetherian as an `R`-module is a finite `R`-module. -/
theorem finite_quotient_ker_lift [IsNoetherian R A] (f : L →ₗ⁅R⁆ A) :
    Module.Finite R (_root_.UniversalEnvelopingAlgebra R L ⧸ RingHom.ker (lift R f)) :=
  .of_injective (Ideal.kerLiftAlg (lift R f)).toLinearMap <| by
    rw [AlgHom.coe_toLinearMap]
    exact Ideal.kerLiftAlg_injective _

/-- A power of the canonical enveloping generator belongs to the kernel of the extended map
exactly when the corresponding power of the image vanishes. -/
theorem pow_ι_mem_ker_lift_iff (f : L →ₗ⁅R⁆ A) (x : L) (n : ℕ) :
    ι R x ^ n ∈ RingHom.ker (lift R f) ↔ f x ^ n = 0 := by
  rw [RingHom.mem_ker, map_pow, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]

/-- The image of an element is nilpotent exactly when some power of its canonical
enveloping-algebra generator belongs to the kernel of the extended map. -/
theorem isNilpotent_iff_exists_pow_ι_mem_ker_lift (f : L →ₗ⁅R⁆ A) (x : L) :
    IsNilpotent (f x) ↔ ∃ n : ℕ, ι R x ^ n ∈ RingHom.ker (lift R f) := by
  simp only [IsNilpotent, pow_ι_mem_ker_lift_iff]

end UniversalEnvelopingAlgebra

end TauCeti
