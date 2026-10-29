/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Basic

/-!
# Finiteness of cotangent spaces of kernels

For a surjective `R`-algebra homomorphism `f : A →ₐ[R] S` onto a module-finite `R`-algebra, if
the kernel of `f` is finitely generated over `A`, then its cotangent space is finite over `R`.
The main case is an augmentation `f : A →ₐ[R] R`, whose kernel is the augmentation ideal.

## Main declarations

* `AlgHom.finite_cotangent_ker_of_fg`: finite generation of the kernel gives finiteness of its
  cotangent space over the base.
* `AlgHom.finite_cotangent_ker`: the noetherian specialization.

## References

* Mathlib's `Algebra.Extension.Cotangent.finite` provides the generic cotangent-space finiteness
  result used here.
-/

public section

namespace AlgHom

variable {R A S : Type*} [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
  [Module.Finite R S]

/-- The cotangent space of the kernel of a surjection onto a module-finite algebra is finite over
the base when the kernel is finitely generated. -/
theorem finite_cotangent_ker_of_fg (f : A →ₐ[R] S) (hf : Function.Surjective f)
    (h : (RingHom.ker f).FG) :
    Module.Finite R (RingHom.ker f).Cotangent := by
  -- The extension `P` has ring `A` and structure map `f`, so `P.ker` is `RingHom.ker f` by
  -- definition of `Algebra.Extension.ofSurjective`.
  let P : Algebra.Extension R S := .ofSurjective f hf
  have : Module.Finite S P.Cotangent := Algebra.Extension.Cotangent.finite h
  have : Module.Finite R P.Cotangent := .trans S _
  exact .equiv (P.cotangentEquivCotangentKer.restrictScalars R)

/-- The cotangent space of the kernel of a surjection from a noetherian algebra onto a
module-finite algebra is finite over the base. -/
theorem finite_cotangent_ker [IsNoetherianRing A] (f : A →ₐ[R] S) (hf : Function.Surjective f) :
    Module.Finite R (RingHom.ker f).Cotangent :=
  finite_cotangent_ker_of_fg f hf (RingHom.ker f).fg_of_isNoetherianRing

end AlgHom
