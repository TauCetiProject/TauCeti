/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Short exact kernel and cokernel sequences

This file records that the canonical kernel sequence of an epimorphism and the canonical cokernel
sequence of a monomorphism are short exact, and that a short complex of functors with values in
an abelian category is short exact as soon as it is short exact objectwise.

## Main statements

* `TauCeti.kernelSequence_shortExact`: the kernel sequence of an epimorphism is short exact.
* `TauCeti.cokernelSequence_shortExact`: the cokernel sequence of a monomorphism is short exact.
* `CategoryTheory.ShortComplex.shortExact_of_forall_evaluation`: a short complex of functors is
  short exact if it is short exact after evaluation at every object.
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

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Short exactness of functors is checked objectwise.** A short complex of functors with values
in an abelian category is short exact if it becomes short exact after evaluation at every object.
-/
lemma shortExact_of_forall_evaluation {J : Type*} [Category* J] (S : ShortComplex (J ⥤ C))
    (h : ∀ j, (S.map ((evaluation J C).obj j)).ShortExact) : S.ShortExact := by
  have (j : J) : Mono (S.f.app j) := (h j).mono_f
  have (j : J) : Epi (S.g.app j) := (h j).epi_g
  have : Mono S.f := NatTrans.mono_of_mono_app S.f
  have : Epi S.g := NatTrans.epi_of_epi_app S.g
  refine ShortExact.mk' ?_ inferInstance inferInstance
  rw [exact_iff_isZero_homology]
  exact Functor.isZero _ fun j ↦ ((exact_iff_isZero_homology _).1 (h j).exact).of_iso
    (S.mapHomologyIso ((evaluation J C).obj j)).symm

end CategoryTheory.ShortComplex
