/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.IsGerbe
public import TauCeti.CategoryTheory.Sites.Descent.Pi
public import TauCeti.CategoryTheory.Sites.Grothendieck

/-!
# Products of gerbes

Let `F i`, for `i : I`, be a family of pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` on a site
`(C, J)` and `TauCeti.Stack.pi F` their product, whose fibre over `U` is the product of the fibres
of the `F i`. When `I` is finite and every `F i` is a gerbe, so is the product
(`TauCeti.Stack.pi.isGerbe`): objects and isomorphisms exist on the intersection of the finitely
many covering sieves on which they exist for the factors. In particular the terminal pseudofunctor,
the product of the empty family, is a gerbe (`TauCeti.Stack.terminal.isGerbe`). The intersection
of infinitely many covering sieves need not be covering, which is why `I` is finite here.

Bandings of the factors induce a banding of the product
(`CategoryTheory.Pseudofunctor.AbelianBanding.pi`, in
`TauCeti.CategoryTheory.Sites.Descent.Banding.Product`), so products of banded gerbes are banded
gerbes.

## Main declarations

* `TauCeti.Stack.pi.isGerbe`: the product of a finite family of gerbes is a gerbe.
* `TauCeti.Stack.terminal.isGerbe`: the terminal pseudofunctor is a gerbe.

## References

* [Stacks Project, Section 06NY](https://stacks.math.columbia.edu/tag/06NY), Definition 8.11.1
-/

public section

universe w v u v' u'

open CategoryTheory

namespace TauCeti.Stack

open CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The product of a finite family of gerbes is a gerbe. -/
instance pi.isGerbe {I : Type w} [Finite I]
    {F : I → Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w u'}}
    [∀ i, (F i).IsGerbe J] : (pi F).IsGerbe J where
  isGroupoid _ := inferInstance
  exists_covering_nonempty U := by
    choose R hR h using fun i ↦ IsGerbe.exists_covering_nonempty (F := F i) (J := J) U
    exact ⟨⨅ i, R i, J.iInf_mem hR, fun _ f hf ↦ ⟨fun i ↦ (h i f (iInf_le R i _ hf)).some⟩⟩
  exists_covering_iso x y := by
    choose R hR h using fun i ↦ IsGerbe.exists_covering_iso (F := F i) (J := J) (x i) (y i)
    exact ⟨⨅ i, R i, J.iInf_mem hR, fun _ f hf ↦
      ⟨Pi.isoMk fun i ↦ (h i f (iInf_le R i _ hf)).some⟩⟩

/-- The terminal pseudofunctor is a gerbe. -/
instance terminal.isGerbe : (terminal.{u', v'} (C := C)).IsGerbe J :=
  have (i : PEmpty.{1}) :
      (i.elim : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}).IsGerbe J := i.elim
  pi.isGerbe

end TauCeti.Stack

end
