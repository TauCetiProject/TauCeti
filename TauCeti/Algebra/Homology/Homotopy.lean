/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Chain homotopies descend to quotient complexes

Let `p : L ⟶ M` exhibit `M` in each degree as the cokernel of `u : K ⟶ L`, and likewise
`p' : L' ⟶ M'` as a degreewise cokernel of `u' : K' ⟶ L'`.  A chain homotopy between morphisms
`L ⟶ L'` whose components carry the image of `u` into the image of `u'` then descends to a chain
homotopy between the induced morphisms `M ⟶ M'`.  `Homotopy.descCokernel` performs that descent.

The factorisation through the subcomplexes is recorded as a family of morphisms `K.X i ⟶ K'.X j`;
it is not required to be a chain homotopy itself.  This is the mechanism behind homotopy
invariance of relative homology, where `M` is the relative chain complex of a pair, that is, the
degreewise cokernel of the chains of the subspace.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {K L M K' L' M' : HomologicalComplex C c} (u : K ⟶ L) (p : L ⟶ M) (u' : K' ⟶ L') (p' : L' ⟶ M')
  {fL gL : L ⟶ L'} {fM gM : M ⟶ M'}
  (hw : ∀ i, u.f i ≫ p.f i = 0)
  (hp : ∀ i, IsColimit (CokernelCofork.ofπ (p.f i) (hw i)))
  (hw' : ∀ i, u'.f i ≫ p'.f i = 0)
  (HL : Homotopy fL gL) (homK : ∀ i j, K.X i ⟶ K'.X j)
  (hcomm : ∀ i j, u.f i ≫ HL.hom i j = homK i j ≫ u'.f j)

include hw hp hw' hcomm

/-- The components of the chain homotopy that `Homotopy.descCokernel` obtains on the quotient
complexes. -/
def descCokernelHom (i j : ι) : M.X i ⟶ M'.X j :=
  (CokernelCofork.IsColimit.desc' (hp i) (HL.hom i j ≫ p'.f j) (by
    rw [← Category.assoc, hcomm, Category.assoc, hw', comp_zero])).1

@[reassoc (attr := simp)]
lemma π_descCokernelHom (i j : ι) :
    p.f i ≫ descCokernelHom u p u' p' hw hp hw' HL homK hcomm i j = HL.hom i j ≫ p'.f j :=
  (CokernelCofork.IsColimit.desc' (hp i) (HL.hom i j ≫ p'.f j) (by
    rw [← Category.assoc, hcomm, Category.assoc, hw', comp_zero])).2

private lemma π_comp_dNext (i : ι) :
    p.f i ≫ dNext i (descCokernelHom u p u' p' hw hp hw' HL homK hcomm) =
      dNext i HL.hom ≫ p'.f i := by
  rw [← dNext_comp_left, ← dNext_comp_right]
  exact congrArg (fun F ↦ dNext i F) (by funext a b; exact π_descCokernelHom ..)

private lemma π_comp_prevD (i : ι) :
    p.f i ≫ prevD i (descCokernelHom u p u' p' hw hp hw' HL homK hcomm) =
      prevD i HL.hom ≫ p'.f i := by
  rw [← prevD_comp_left, ← prevD_comp_right]
  exact congrArg (fun F ↦ prevD i F) (by funext a b; exact π_descCokernelHom ..)

/-- A chain homotopy on the total complexes whose components carry the subcomplexes into each
other descends to the quotient complexes. -/
def descCokernel (hf : p ≫ fM = fL ≫ p') (hg : p ≫ gM = gL ≫ p') : Homotopy fM gM where
  hom := descCokernelHom u p u' p' hw hp hw' HL homK hcomm
  zero i j hij := Cofork.IsColimit.hom_ext (hp i) (by simp [HL.zero i j hij])
  comm i := Cofork.IsColimit.hom_ext (hp i) (by
    simp only [Cofork.π_ofπ, Preadditive.comp_add, π_comp_dNext, π_comp_prevD,
      ← HomologicalComplex.comp_f p fM, ← HomologicalComplex.comp_f p gM, hf, hg,
      HomologicalComplex.comp_f]
    rw [← Preadditive.add_comp, ← Preadditive.add_comp, ← HL.comm i])

@[simp]
lemma descCokernel_hom (hf : p ≫ fM = fL ≫ p') (hg : p ≫ gM = gL ≫ p') :
    (descCokernel u p u' p' hw hp hw' HL homK hcomm hf hg).hom =
      descCokernelHom u p u' p' hw hp hw' HL homK hcomm := (rfl)

end Homotopy
