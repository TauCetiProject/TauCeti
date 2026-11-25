/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import Mathlib.AlgebraicTopology.SimplicialNerve
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import TauCeti.AlgebraicTopology.Quasicategory.OuterHorn.Basic
public import TauCeti.AlgebraicTopology.SimplicialNerve.Quasicategory
public import TauCeti.AlgebraicTopology.SimplicialSet.InternalHom

/-!
# The simplicial category of quasicategories and `Cat∞`

Simplicial sets form a simplicial category whose mapping simplicial sets are the function
complexes `Fun(A, B)` (Mathlib's `SimplicialCategory SSet`). Replacing each function complex by
its core `Fun(A, B)^≃`, the subcomplex of simplices all of whose edges are equivalences, gives
another simplicial category `SSet.CoreEnriched`: an edge of `Fun(A, B) ⊗ Fun(B, C)` whose two
components are equivalences is an equivalence, so composition preserves cores.

Restricting to quasicategories gives the simplicial category `SSet.CatInftyΔ`, and its simplicial
(homotopy coherent) nerve is `SSet.catInfty`, HTT's `Cat∞` of small quasicategories (HTT
Definition 3.0.0.1). The underlying ordinary category of `SSet.CatInftyΔ` is the category of
quasicategories and maps of simplicial sets.

By Joyal's theorem on special outer horns, the core of every quasicategory is a Kan complex
(`SSet.core.kanComplex`). Consequently `SSet.CatInftyΔ` is locally Kan, and its simplicial nerve
`SSet.catInfty` is a quasicategory (`SSet.catInfty.quasicategory`, HTT Proposition 1.1.5.10).
For a Kan complex `B`, the core of `Fun(A, B)` is all of `Fun(A, B)`; by contrast,
`Fun(Δ[0], Δ[n + 1]) ≅ Δ[n + 1]` is connected while `Fun(Δ[0], Δ[n + 1])^≃ ≅ (Δ[n + 1]).core`
has `n + 2` connected components (`SSet.CatInftyΔ.π₀SHomObj₀StdSimplexEquiv`).

## Main definitions

* `SSet.CoreEnriched`: simplicial sets, as a simplicial category with the cores of function
  complexes as mapping simplicial sets.
* `SSet.CatInftyΔ`: its full simplicial subcategory on the quasicategories.
* `SSet.catInfty`: the simplicial nerve of `SSet.CatInftyΔ`.

## Main results

* `SSet.range_sHomComp_le_core`: composition of function complexes preserves cores.
* `SSet.CoreEnriched.sHom_eq`: the mapping simplicial sets of `SSet.CoreEnriched` are the cores of
  function complexes, with identities, composition and the vertices given by morphisms
  characterized by `SSet.CoreEnriched.eId_ι`, `SSet.CoreEnriched.eComp_ι` and
  `SSet.CoreEnriched.eHomEquiv_ι`.
* `SSet.core_sHom_eq_top`: into a Kan complex, the core of a function complex is everything.
* The mapping simplicial sets of `SSet.CatInftyΔ` are Kan complexes, and `SSet.catInfty` is a
  quasicategory (`SSet.catInfty.quasicategory`).
* `SSet.CatInftyΔ.π₀SHomObj₀StdSimplexEquiv`: `π₀ Fun^≃(Δ[0], Δ[n]) ≃ Fin (n + 1)`, separating
  the `n + 1` vertices of `Δ[n]` whereas `Fun(Δ[0], Δ[n])` is connected.

## References

* J. Lurie, *Higher Topos Theory*, Definition 3.0.0.1 and Proposition 1.1.5.10.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open EnrichedCategory Opposite SimplicialCategory Simplicial

universe u

namespace SSet

/-- The cores of function complexes are closed under the composition of function complexes. -/
lemma range_sHomComp_le_core (A B C : SSet.{u}) :
    Subcomplex.range (((sHom A B).core.ι ⊗ₘ (sHom B C).core.ι) ≫ sHomComp A B C) ≤
      (sHom A C).core := by
  simp only [Subcomplex.range_comp, Subcomplex.range_tensorHom, Subfunctor.range_ι,
    ← core_tensor]
  exact image_core_le _

/-- Every simplex of a function complex into a Kan complex lies in its core. -/
lemma core_sHom_eq_top (A B : SSet.{u}) [KanComplex B] : (sHom A B).core = ⊤ :=
  -- The function complex of `SSet` is Mathlib's internal hom `(ihom A).obj B`.
  have : KanComplex (sHom A B) := inferInstanceAs (KanComplex ((ihom A).obj B))
  core_eq_top

/-- Simplicial sets, to be considered as a simplicial category whose mapping simplicial set from
`A` to `B` is the core `Fun(A, B)^≃` of the function complex. Morphisms are maps of simplicial
sets. -/
structure CoreEnriched : Type (u + 1) where
  /-- A simplicial set, as an object of `CoreEnriched`. -/
  of ::
  /-- The underlying simplicial set. -/
  toSSet : SSet.{u}

namespace CoreEnriched

instance : Category CoreEnriched.{u} := inferInstanceAs (Category (InducedCategory SSet toSSet))

noncomputable instance : EnrichedCategory SSet.{u} CoreEnriched.{u} where
  Hom A B := (sHom A.toSSet B.toSSet).core
  id A := Subcomplex.lift (eId SSet A.toSSet) (range_le_core_of_kanComplex _)
  comp A B C := Subcomplex.lift _ (range_sHomComp_le_core A.toSSet B.toSSet C.toSSet)
  id_comp A B := by
    rw [← cancel_mono (Subcomplex.ι _)]
    simp only [Category.assoc, Subcomplex.lift_ι, whiskerRight_comp_tensorHom_assoc,
      leftUnitor_inv_comp_tensorHom_assoc, e_id_comp, Category.comp_id, Category.id_comp]
  comp_id A B := by
    rw [← cancel_mono (Subcomplex.ι _)]
    simp only [Category.assoc, Subcomplex.lift_ι, whiskerLeft_comp_tensorHom_assoc,
      rightUnitor_inv_comp_tensorHom_assoc, e_comp_id, Category.comp_id, Category.id_comp]
  assoc A B C D := by
    rw [← cancel_mono (Subcomplex.ι _)]
    simp only [Category.assoc, Subcomplex.lift_ι, whiskerRight_comp_tensorHom_assoc,
      whiskerLeft_comp_tensorHom_assoc]
    rw [← tensorHom_comp_whiskerRight_assoc, ← tensorHom_comp_whiskerLeft_assoc,
      ← associator_inv_naturality_assoc, e_assoc]

/-- The identity of `A` is the identity of the function complex, viewed in its core. -/
@[reassoc (attr := simp)]
lemma eId_ι (A : CoreEnriched.{u}) :
    eId SSet A ≫ (sHom A.toSSet A.toSSet).core.ι = eId SSet A.toSSet :=
  rfl

/-- Composition is the composition of function complexes, restricted to cores. -/
@[reassoc (attr := simp)]
lemma eComp_ι (A B C : CoreEnriched.{u}) :
    eComp SSet A B C ≫ (sHom A.toSSet C.toSSet).core.ι =
      ((sHom A.toSSet B.toSSet).core.ι ⊗ₘ (sHom B.toSSet C.toSSet).core.ι) ≫
        eComp SSet A.toSSet B.toSSet C.toSSet :=
  rfl

noncomputable instance : SimplicialCategory CoreEnriched.{u} where
  homEquiv {A B} := (InducedCategory.homEquiv (F := toSSet)).trans
    ((eHomEquiv SSet).trans (coreHomEquiv (𝟙_ SSet.{u}) (sHom A.toSSet B.toSSet)).symm)
  homEquiv_id A := by
    rw [← cancel_mono (Subcomplex.ι _), eId_ι, Equiv.trans_apply, Equiv.trans_apply,
      coreHomEquiv_symm_apply_ι, InducedCategory.homEquiv_apply]
    exact eHomEquiv_id SSet A.toSSet
  homEquiv_comp f g := by
    rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Category.assoc, eComp_ι,
      tensorHom_comp_tensorHom_assoc]
    simp only [Equiv.trans_apply]
    rw [coreHomEquiv_symm_apply_ι, coreHomEquiv_symm_apply_ι,
      coreHomEquiv_symm_apply_ι]
    -- `InducedCategory.homEquiv` sends `f ≫ g` to `f.hom ≫ g.hom` by definition.
    exact eHomEquiv_comp SSet f.hom g.hom

/-- The mapping simplicial sets of `CoreEnriched` are the cores of the function complexes. -/
lemma sHom_eq (A B : CoreEnriched.{u}) : sHom A B = (sHom A.toSSet B.toSSet).core :=
  rfl

/-- A morphism of `CoreEnriched`, as a vertex of the core of the function complex, is the
underlying map of simplicial sets. -/
@[reassoc (attr := simp)]
lemma eHomEquiv_ι {A B : CoreEnriched.{u}} (f : A ⟶ B) :
    eHomEquiv SSet f ≫ (sHom A.toSSet B.toSSet).core.ι = eHomEquiv SSet f.hom :=
  coreHomEquiv_symm_apply_ι _

/-- The core functor space `Fun(Δ[0], X)^≃` is isomorphic to `X.core`. -/
noncomputable def sHomObj₀Iso (X : SSet.{u}) :
    sHom (of Δ[0]) (of X) ≅ (X.core : SSet.{u}) :=
  core.mapIso (SSet.sHomObj₀Iso X)

/-- The isomorphism `Fun(Δ[0], X)^≃ ≅ X.core` is the restriction of `SSet.sHomObj₀Iso X` to
cores. -/
@[reassoc (attr := simp)]
lemma sHomObj₀Iso_hom_ι (X : SSet.{u}) :
    (sHomObj₀Iso X).hom ≫ X.core.ι =
      (sHom (Δ[0] : SSet.{u}) X).core.ι ≫ (SSet.sHomObj₀Iso X).hom := by
  simp [sHomObj₀Iso]

/-- The inverse of `CoreEnriched.sHomObj₀Iso X` is the restriction of `(SSet.sHomObj₀Iso X).inv`
to cores. -/
@[reassoc (attr := simp)]
lemma sHomObj₀Iso_inv_ι (X : SSet.{u}) :
    (sHomObj₀Iso X).inv ≫ (sHom (Δ[0] : SSet.{u}) X).core.ι =
      X.core.ι ≫ (SSet.sHomObj₀Iso X).inv := by
  simp [sHomObj₀Iso]

end CoreEnriched

/-- The simplicial category of quasicategories, with the cores `Fun(A, B)^≃` of function complexes
as mapping simplicial sets. This is HTT's `Cat_∞^Δ`. -/
abbrev CatInftyΔ : Type (u + 1) :=
  ObjectProperty.FullSubcategory fun A : CoreEnriched.{u} ↦ Quasicategory A.toSSet

/-- The simplicial (homotopy coherent) nerve of `CatInftyΔ`, HTT's `Cat∞` of small quasicategories,
whose objects are the quasicategories in universe `u`. -/
noncomputable abbrev catInfty : SSet.{u + 1} :=
  SimplicialNerve CatInftyΔ.{u}

namespace CatInftyΔ

/-- **The simplicial category `CatInftyΔ` is locally Kan**: its mapping simplicial sets
`Fun(A, B)^≃` are Kan complexes, as cores of function complexes into quasicategories. -/
instance (A B : CatInftyΔ.{u}) : KanComplex (sHom A B) :=
  have := B.property
  -- The function complex of `SSet` is Mathlib's internal hom `(ihom A).obj B`.
  have : Quasicategory (sHom A.obj.toSSet B.obj.toSSet) :=
    inferInstanceAs (Quasicategory ((ihom A.obj.toSSet).obj B.obj.toSSet))
  core.kanComplex

/-- The connected components of the core functor space `Fun(Δ[0], Δ[n])^≃` in `CatInftyΔ` are in
bijection with `Fin (n + 1)`. -/
noncomputable def π₀SHomObj₀StdSimplexEquiv (n : ℕ) :
    π₀ (sHom (⟨.of Δ[0], inferInstance⟩ : CatInftyΔ.{u}) ⟨.of Δ[n], inferInstance⟩) ≃
      Fin (n + 1) :=
  (π₀Functor.mapIso (CoreEnriched.sHomObj₀Iso Δ[n])).toEquiv.trans (stdSimplex.π₀CoreEquiv n)

/-- The equivalence `π₀SHomObj₀StdSimplexEquiv n` sends the component of a vertex `x` of
`Fun(Δ[0], Δ[n])^≃` to the vertex of `Δ[n]` obtained by evaluating `x` at the point. -/
@[simp]
lemma π₀SHomObj₀StdSimplexEquiv_mk {n : ℕ}
    (x : (sHom (⟨.of Δ[0], inferInstance⟩ : CatInftyΔ.{u}) ⟨.of Δ[n], inferInstance⟩) _⦋0⦌) :
    π₀SHomObj₀StdSimplexEquiv n (π₀.mk x) =
      stdSimplex.obj₀Equiv ((SSet.sHomObj₀Iso Δ[n]).hom.app (op ⦋0⦌) x.val) := by
  -- `CatInftyΔ` inherits `sHom` definitionally from `CoreEnriched` as a `FullSubcategory`, and
  -- `π₀Functor.obj` unfolds to `π₀` at default transparency, so `Equiv.trans_apply` and
  -- `Iso.toEquiv_apply` are applied directly before rewriting with `mapπ₀_mk` and `π₀CoreEquiv_mk`.
  have hmap : ((π₀Functor.mapIso (CoreEnriched.sHomObj₀Iso Δ[n])).toEquiv (π₀.mk x) :
      π₀ ((Δ[n] : SSet.{u}).core : SSet.{u})) =
      π₀.mk ((CoreEnriched.sHomObj₀Iso Δ[n]).hom.app (op ⦋0⦌) x) :=
    (Iso.toEquiv_apply (π₀Functor.mapIso (CoreEnriched.sHomObj₀Iso Δ[n])) (π₀.mk x)).trans
      (by rw [Functor.mapIso_hom, π₀Functor_map]; exact mapπ₀_mk _ _)
  refine (Equiv.trans_apply (π₀Functor.mapIso (CoreEnriched.sHomObj₀Iso Δ[n])).toEquiv
    (stdSimplex.π₀CoreEquiv n) (π₀.mk x)).trans
    ((congrArg (stdSimplex.π₀CoreEquiv n) hmap).trans ?_)
  rw [stdSimplex.π₀CoreEquiv_mk]
  exact congrArg stdSimplex.obj₀Equiv congr($(CoreEnriched.sHomObj₀Iso_hom_ι Δ[n]).app (op ⦋0⦌) x)

/-- The inverse of `π₀SHomObj₀StdSimplexEquiv n` sends `i : Fin (n + 1)` to the component of the
constant map `Δ[0] ⟶ Δ[n]` at vertex `i`. -/
@[simp]
lemma π₀SHomObj₀StdSimplexEquiv_symm_apply {n : ℕ} (i : Fin (n + 1)) :
    (π₀SHomObj₀StdSimplexEquiv.{u} n).symm i =
      π₀.mk (X := sHom (⟨.of Δ[0], inferInstance⟩ : CatInftyΔ.{u}) ⟨.of Δ[n], inferInstance⟩)
        ⟨(SSet.sHomObj₀Iso Δ[n]).inv.app (op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i),
          mem_core_obj_zero _⟩ := by
  apply (π₀SHomObj₀StdSimplexEquiv.{u} n).injective
  simp

/-- Unlike `Fun(Δ[0], Δ[n + 1])`, the core functor space `Fun(Δ[0], Δ[n + 1])^≃` in `CatInftyΔ`
has at least two connected components. -/
instance (n : ℕ) :
    Nontrivial
      (π₀ (sHom (⟨.of Δ[0], inferInstance⟩ : CatInftyΔ.{u}) ⟨.of Δ[n + 1], inferInstance⟩)) :=
  (π₀SHomObj₀StdSimplexEquiv (n + 1)).nontrivial

end CatInftyΔ

/-- **`Cat∞` is a quasicategory** (HTT Definition 3.0.0.1 and Proposition 1.1.5.10): it is the
simplicial nerve of the locally Kan simplicial category `CatInftyΔ`. -/
theorem catInfty.quasicategory : Quasicategory catInfty.{u} :=
  inferInstance

end SSet
