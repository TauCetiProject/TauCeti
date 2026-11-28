/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Isogeny
public import TauCeti.AlgebraicGeometry.GroupScheme.Torsor.Kernel
import TauCeti.AlgebraicGeometry.GroupScheme.Cokernel

/-!
# An abelian-scheme isogeny as a torsor and quotient

An isogeny `f : A ⟶ B` is an fppf torsor over `B` under its scheme-theoretic kernel
pulled back to `B`. A homomorphism from `A` to an abelian scheme factors uniquely through
`f` exactly when it kills the scheme-theoretic kernel. This universal property identifies
the target of an existing isogeny with the quotient by its kernel.

## References

* G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties*, Chapter I, §1.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.4.
-/

public section

open CategoryTheory Limits
open _root_.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.AbelianScheme.IsIsogeny

variable {S : Scheme.{u}} {A B C : AbelianScheme S} {f : A ⟶ B}

/-- An isogeny of abelian schemes is an fppf torsor over its target under its
base-changed scheme-theoretic kernel acting by left translation. -/
theorem isTorsor_kernel (hf : IsIsogeny f) :
    let g := toGrpFunctor.map f
    let := GroupScheme.kernelAction g
    (Scheme.fppfTopology.over (toGrpFunctor.obj B).X.left).IsTorsor
      ((Over.pullback (toGrpFunctor.obj B).X.hom).mapGrp.obj (kernel g))
      (Over.mk g.hom.hom.left) := by
  have : Flat (toGrpFunctor.map f).hom.hom.left := hf.flat
  have : Surjective (toGrpFunctor.map f).hom.hom.left := hf.surjective
  have : LocallyOfFinitePresentation (toGrpFunctor.map f).hom.hom.left := by
    rw [toGrpFunctor_map_hom_hom]
    exact locallyOfFinitePresentation_toOverHom_left f
  exact GroupScheme.isTorsor_kernel (toGrpFunctor.map f)

/-- A homomorphism of abelian schemes factors uniquely through an isogeny if and only if
it vanishes on the scheme-theoretic kernel. -/
theorem existsUnique_comp_eq_iff (hf : IsIsogeny f) (g : A ⟶ C) :
    (∃! h : B ⟶ C, f ≫ h = g) ↔ kernel.ι (toGrpFunctor.map f) ≫ toGrpFunctor.map g = 0 := by
  constructor
  · rintro ⟨h, rfl, _⟩
    simp
  have : IsFinite (toGrpFunctor.map f).hom.hom.left := hf.isFinite
  have : Flat (toGrpFunctor.map f).hom.hom.left := hf.flat
  have : Surjective (toGrpFunctor.map f).hom.hom.left := hf.surjective
  let hc := GroupScheme.isColimitKernelCofork (toGrpFunctor.map f)
  intro hg
  let h := CokernelCofork.IsColimit.desc' hc (toGrpFunctor.map g) hg
  refine ⟨InducedCategory.homMk h.val, InducedCategory.hom_ext h.property, ?_⟩
  intro h' hh'
  apply InducedCategory.hom_ext
  apply Cofork.IsColimit.hom_ext hc
  exact (congrArg (fun k ↦ (toGrpFunctor (S := S)).map k) hh').trans h.property.symm

end TauCeti.AlgebraicGeometry.AbelianScheme.IsIsogeny
