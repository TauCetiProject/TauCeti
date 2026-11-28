/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.ConvergenceBounds
public import TauCeti.Algebra.Homology.SpectralObject.Naturality
public import TauCeti.CategoryTheory.Filtration.Decreasing
import TauCeti.CategoryTheory.Subobject.Image

/-!
# The decreasingly filtered abutment of a spectral object

In the cohomological spectral sequence of a spectral object indexed by `EInt`, the term
at `(p, q)` has total degree `n = p + q`. The degree-`n` abutment has an increasing filtration
by the images of `H^n(⊥ ≤ j) ⟶ H^n(⊥ ≤ ⊤)`. Taking `j = n - p + 1` gives the decreasing filtration
in the first coordinate of the spectral sequence.

`filteredAbutmentFunctor n` takes a spectral object to this filtered object in degree `n`.
`EInftyIsoGr` identifies `EInfty (n - p) n` with its graded piece in degree `p`, through
`EInftyIsoCokernel`. Convergence bounds in degree `n` make the filtration finite.

For the image filtration in exact-couple notation, see G. O. Helle and J. Rognes,
*Boardman's whole-plane obstruction group for Cartan–Eilenberg systems*, Definition 3.6.
-/

public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows

variable {C : Type*} [Category* C] [Abelian C]

/-- The abutment in degree `n`, with decreasing filtration
`F^p H^n = im(H^n(⊥ ≤ n - p + 1) ⟶ H^n(⊥ ≤ ⊤))`. -/
@[expose, implicit_reducible, simps X filtration_toMonoOver_obj]
noncomputable def filteredAbutment (X : SpectralObject C EInt) (n : ℤ) :
    FilteredObject C ℤᵒᵖ where
  X := X.abutment n
  filtration.toMonoOver :=
    { obj p := MonoOver.mk (X.abutmentFiltrationι (n - p.unop + 1) n)
      map {p q} f := MonoOver.homMk
        (X.abutmentFiltrationMapOfLE _ _ n (by have := leOfHom f.unop; lia))
        (X.abutmentFiltrationMapOfLE_ι ..) }

variable (X : SpectralObject C EInt)

/-- The inclusion of a step is its abutment filtration inclusion. -/
@[simp]
lemma filteredAbutment_stepι (n : ℤ) (p : ℤᵒᵖ) :
    (X.filteredAbutment n).stepι p = X.abutmentFiltrationι (n - p.unop + 1) n := by
  rw [← FilteredObject.filtration_ι_app]
  rfl

/-- The transition maps are the inclusions between the corresponding increasing steps. -/
@[simp]
lemma filteredAbutment_stepMap (n : ℤ) {p q : ℤᵒᵖ} (f : p ⟶ q) :
    (X.filteredAbutment n).stepMap f =
      X.abutmentFiltrationMapOfLE _ _ n (by have := leOfHom f.unop; lia) := by
  rw [← FilteredObject.filtrationDiagram_map]
  rfl

/-- As a subobject, the step in degree `p` is the image of `H^n(⊥ ≤ n - p + 1)` in the abutment. -/
@[simp]
lemma filteredAbutment_step (n : ℤ) (p : ℤᵒᵖ) :
    (X.filteredAbutment n).step p = imageSubobject ((X.H n).map
      (twoδ₂Toδ₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((n - p.unop + 1 : ℤ) : EInt)))
        (homOfLE le_top) (homOfLE bot_le) (Subsingleton.elim _ _))) := by
  rw [← FilteredObject.mk_stepι, ← pOpcycles_abutmentFiltrationι, imageSubobject_comp_eq_of_epi,
    imageSubobject_mono]
  congr 1
  exact X.filteredAbutment_stepι n p

/-- A morphism of spectral objects acts on the abutment by its component on `H^n(⊥ ≤ ⊤)`
and on the steps by its maps on opcycles. -/
@[expose, implicit_reducible, simps! obj map_hom map_natTrans_app]
noncomputable def filteredAbutmentFunctor (n : ℤ) :
    SpectralObject C EInt ⥤ FilteredObject C ℤᵒᵖ where
  obj X := X.filteredAbutment n
  map φ := FilteredObject.homMk ((φ.hom n).app _) (fun _ ↦ opcyclesMapOfHom φ _ _ n)
    (fun p ↦ abutmentFiltrationι_naturality φ (n - p.unop + 1) n)
  map_id _ := FilteredObject.hom_ext (rfl)
  map_comp _ _ := FilteredObject.hom_ext (rfl)

/-- The spectral object's limit term at `(p, n - p)` is the `p`th graded piece
of its filtered abutment in degree `n`. -/
noncomputable def EInftyIsoGr (n p : ℤ) :
    X.EInfty (n - p) n ≅ (FilteredObject.gr p).obj (X.filteredAbutment n) :=
  X.EInftyIsoCokernel (n - p) n ≪≫
    cokernel.mapIso _ ((X.filteredAbutment n).stepMap (homOfLE (Int.le_add_one le_rfl)).op)
      (eqToIso (congrArg (X.abutmentFiltration · n) (by lia : n - p = n - (p + 1) + 1)))
      (Iso.refl _) (by
        rw [← cancel_mono ((X.filteredAbutment n).stepι (op p))]
        simp only [Category.assoc, FilteredObject.stepMap_stepι]
        simp only [filteredAbutment_stepι, unop_op]
        trans X.abutmentFiltrationι (n - p) n
        · exact (congrArg (X.abutmentFiltrationMap (n - p) n ≫ ·)
            (Category.id_comp (X.abutmentFiltrationι (n - p + 1) n))).trans
              (X.abutmentFiltrationMap_ι (n - p) n)
        · exact (Category.comp_id _).symm.trans (eqToHom_naturality (X.abutmentFiltrationι · n)
            (by lia : n - p = n - (p + 1) + 1)))

/-- Under the graded-piece isomorphism, the map from the filtration step to `EInfty` is
the canonical projection from the step to its graded piece. -/
@[reassoc (attr := simp)]
lemma opcyclesToE_EInftyIsoGr_hom (n p : ℤ) :
    X.opcyclesToE (homOfLE (bot_le : (⊥ : EInt) ≤ (n - p : ℤ)))
        (homOfLE (coe_le_coe_add_one (n - p))) (homOfLE le_top) (homOfLE bot_le)
        (Subsingleton.elim _ _) (n - 1) n (n + 1) (sub_add_cancel n 1) rfl ≫
      (X.EInftyIsoGr n p).hom =
        ((FilteredObject.grShortComplex p).obj (X.filteredAbutment n)).g := by
  refine (X.opcyclesToE_EInftyIsoCokernel_hom_assoc (n - p) n _).trans ?_
  exact (cokernel.π_desc ..).trans (Category.id_comp _)

variable {X} {Y : SpectralObject C EInt}

/-- The isomorphisms from `EInfty` to the graded pieces intertwine the maps induced by a
morphism of spectral objects. -/
@[reassoc]
lemma EInftyIsoGr_hom_naturality (φ : X ⟶ Y) (n p : ℤ) :
    EMap φ (homOfLE (bot_le : (⊥ : EInt) ≤ (n - p : ℤ)))
        (homOfLE (coe_le_coe_add_one (n - p))) (homOfLE le_top)
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl ≫ (Y.EInftyIsoGr n p).hom =
      (X.EInftyIsoGr n p).hom ≫ (FilteredObject.gr p).map ((filteredAbutmentFunctor n).map φ) := by
  rw [← cancel_epi (X.opcyclesToE (homOfLE (bot_le : (⊥ : EInt) ≤ (n - p : ℤ)))
    (homOfLE (coe_le_coe_add_one (n - p))) (homOfLE le_top) (homOfLE bot_le)
    (Subsingleton.elim _ _) (n - 1) n (n + 1) (sub_add_cancel n 1) rfl),
    ← opcyclesMapOfHom_opcyclesToE_assoc, opcyclesToE_EInftyIsoGr_hom,
    opcyclesToE_EInftyIsoGr_hom_assoc]
  exact ((FilteredObject.grShortComplex p).map ((filteredAbutmentFunctor n).map φ)).comm₂₃

/-- Convergence bounds give a finite decreasing filtration of the abutment in degree `n`. -/
lemma HasConvergenceBounds.isFinite_filteredAbutment {n a b : ℤ}
    (h : X.HasConvergenceBounds n a b) :
    (X.filteredAbutment n).IsFinite := by
  apply FilteredObject.IsFinite.mk (a := n + 1 - b) (b := n + 1 - a)
  · rw [FilteredObject.step_eq_top_iff, filteredAbutment_stepι]
    exact h.isIso_abutmentFiltrationι (by dsimp; lia)
  · rw [FilteredObject.step_eq_bot_iff]
    exact h.isZero_abutmentFiltration (by dsimp; lia)

end CategoryTheory.Abelian.SpectralObject
