/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Module.ProjectiveCover.Simple
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.AlmostSplit

/-!
# The inclusion of the radical of a projective module

Let `P` be a finitely generated projective module with local endomorphism ring and finitely
generated radical, as for an indecomposable projective module over an Artin algebra. A morphism
into `P` that is not a split epimorphism is not surjective, so its image is a proper submodule and
lies in the radical of `P`. So the inclusion `rad P ⟶ P` is right almost split in `FGModuleCat`.
It plays the role of the final map of an almost-split sequence at a projective module, where no
such sequence ends. In the functorial picture it presents the simple functor `S_P`, and
`(-, rad P) ⟶ rad(-, P)` is a projective cover.

## Main results

* `FGModuleCat.isRightAlmostSplit_ofHom_subtype_jacobson`: the inclusion of the radical is right
  almost split.
* `FGModuleCat.isRepresentableProjectiveCover_radicalFunctorLift_ofHom_subtype_jacobson`: the map
  `(-, rad P) ⟶ rad(-, P)` is a projective cover.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section V.1.
-/

public section

namespace FGModuleCat

open CategoryTheory TauCeti

universe w v

variable (A : Type v) [Ring A] (P : Type w) [AddCommGroup P] [Module A P] [Module.Finite A P]
  [Module.Finite A (Module.jacobson A P)] [Module.Projective A P] [IsLocalRing (Module.End A P)]

/-- **The sink map of a projective module.** For a finitely generated projective module `P` with
local endomorphism ring and finitely generated radical, the inclusion `rad P ⟶ P` is right almost
split in `FGModuleCat`. -/
theorem isRightAlmostSplit_ofHom_subtype_jacobson :
    IsRightAlmostSplit (ofHom (Module.jacobson A P).subtype) := by
  have : Nontrivial P := nontrivial_of_nontrivial_end (R := A) (M := P)
  have hlt := Module.jacobson_lt_top A P
  refine isRightAlmostSplit_iff.2 ⟨fun hs ↦ hlt.ne (Submodule.eq_top_iff'.2 fun x ↦ ?_),
    fun W g hg ↦ ?_⟩
  · let s := section_ (ofHom (Module.jacobson A P).subtype)
    have hx : ((s.hom.hom x : Module.jacobson A P) : P) = x :=
      congrArg (fun φ : of A P ⟶ of A P ↦ φ.hom.hom x)
        (IsSplitEpi.id (ofHom (Module.jacobson A P).subtype))
    exact hx ▸ (s.hom.hom x).2
  · have hrange : LinearMap.range g.hom.hom ≠ ⊤ := fun htop ↦ hg ?_
    · have hle := le_jacobson_of_ne_top_of_isLocalRing_end hrange
      refine ⟨ObjectProperty.homMk (ModuleCat.ofHom
        (g.hom.hom.codRestrict _ fun x ↦ hle ⟨x, rfl⟩)), ?_⟩
      ext x
      rfl
    · obtain ⟨s, hs⟩ := Module.projective_lifting_property g.hom.hom LinearMap.id
        (LinearMap.range_eq_top.1 htop)
      exact .mk' ⟨ObjectProperty.homMk (ModuleCat.ofHom s), by
        ext x
        exact LinearMap.congr_fun hs x⟩

/-- For a finitely generated projective module `P` with local endomorphism ring and finitely
generated radical, the map `(-, rad P) ⟶ rad(-, P)` induced by the inclusion is a projective
cover. -/
theorem isRepresentableProjectiveCover_radicalFunctorLift_ofHom_subtype_jacobson :
    IsRepresentableProjectiveCover (radicalFunctorLift (ofHom (Module.jacobson A P).subtype)
      (isRightAlmostSplit_ofHom_subtype_jacobson A P).mem_jacobsonRadical) :=
  have : Mono (ofHom (Module.jacobson A P).subtype) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  (isRightAlmostSplit_ofHom_subtype_jacobson A P).isRepresentableProjectiveCover_radicalFunctorLift

end FGModuleCat
