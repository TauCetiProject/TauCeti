/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Short exact kernel and cokernel sequences

This file records that the canonical kernel sequence of an epimorphism and the canonical cokernel
sequence of a monomorphism are short exact.

## Main statements

* `TauCeti.kernelSequence_shortExact`: the kernel sequence of an epimorphism is short exact.
* `TauCeti.cokernelSequence_shortExact`: the cokernel sequence of a monomorphism is short exact.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The second map in the kernel sequence of an epimorphism is an epimorphism. -/
instance epi_kernelSequence_g {X Y : C} (f : X ⟶ Y) [Epi f] :
    Epi (ShortComplex.kernelSequence f).g :=
  (inferInstance : Epi f)

/-- The kernel sequence of an epimorphism is short exact. -/
lemma kernelSequence_shortExact {X Y : C} (f : X ⟶ Y) [Epi f] :
    (ShortComplex.kernelSequence f).ShortExact :=
  { exact := ShortComplex.kernelSequence_exact _ }

/-- The first map in the cokernel sequence of a monomorphism is a monomorphism. -/
instance mono_cokernelSequence_f {X Y : C} (f : X ⟶ Y) [Mono f] :
    Mono (ShortComplex.cokernelSequence f).f :=
  (inferInstance : Mono f)

/-- The cokernel sequence of a monomorphism is short exact. -/
lemma cokernelSequence_shortExact {X Y : C} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.cokernelSequence f).ShortExact :=
  { exact := ShortComplex.cokernelSequence_exact _ }

end TauCeti
