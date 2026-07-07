/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Comap

/-!
# Finiteness for inverse images and kernels of subcomodules

This file records finite-generation bookkeeping for the lightweight `Subcomodule` API.
Images of finitely generated subcomodules and ranges were already available in the base file;
here we add the noetherian inverse-image and kernel lemmas.

This is Layer 1 infrastructure for the ReductiveGroups roadmap target on finite-dimensional
subcomodules and the finite-dimensional comodule category. Kernels and inverse images of
comodule morphisms are finitely generated when the source module is noetherian, and hence
for finitely generated source comodules over a noetherian ring, so the usual categorical
constructions stay inside the finite-comodule subcategory.

## Main declarations

* `TauCeti.Subcomodule.comap_finite_of_isNoetherian`
* `TauCeti.Subcomodule.comap_finite_of_finite`
* `TauCeti.Comodule.Hom.ker_finite_of_isNoetherian`
* `TauCeti.Comodule.Hom.ker_finite_of_finite`

## References

The mathematical input is the standard module-theoretic fact that every submodule of a
noetherian module is finitely generated, reused from Mathlib via `IsNoetherian.noetherian`.
-/

public section

namespace TauCeti

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}

section Ring

variable [CommRing R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

namespace Subcomodule

/-- In a noetherian source module, the inverse image of any subcomodule is finitely
generated as an `R`-module. -/
theorem comap_finite_of_isNoetherian [IsNoetherian R M]
    (B : Subcomodule R C N) (f : Comodule.Hom R C M N) :
    Module.Finite R (B.comap f).toSubmodule := by
  rw [comap_toSubmodule, Module.Finite.iff_fg]
  exact IsNoetherian.noetherian _

/-- Over a noetherian ring, the inverse image of any subcomodule in a finitely generated
source comodule is finitely generated. -/
theorem comap_finite_of_finite [IsNoetherianRing R] [Module.Finite R M]
    (B : Subcomodule R C N) (f : Comodule.Hom R C M N) :
    Module.Finite R (B.comap f).toSubmodule := by
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R (M := M)
  haveI : IsNoetherian R M := inferInstance
  exact comap_finite_of_isNoetherian B f

end Subcomodule

namespace Comodule

namespace Hom

/-- In a noetherian source module, the kernel subcomodule of a comodule morphism is finitely
generated as an `R`-module. -/
theorem ker_finite_of_isNoetherian [IsNoetherian R M] (f : Hom R C M N) :
    Module.Finite R (ker (R := R) (C := C) f).toSubmodule := by
  rw [ker_toSubmodule, Module.Finite.iff_fg]
  exact IsNoetherian.noetherian _

/-- Over a noetherian ring, the kernel of a comodule morphism out of a finitely generated
comodule is finitely generated. -/
theorem ker_finite_of_finite [IsNoetherianRing R] [Module.Finite R M]
    (f : Hom R C M N) :
    Module.Finite R (ker (R := R) (C := C) f).toSubmodule := by
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R (M := M)
  haveI : IsNoetherian R M := inferInstance
  exact ker_finite_of_isNoetherian f

end Hom

end Comodule

end Ring

end TauCeti
