/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.SimplicialSet.Factorization
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex
public import TauCeti.AlgebraicTopology.SimplicialSet.PrismRealization

/-!
# Weak homotopy equivalences realize to homotopy equivalences

A map `f : X ⟶ Y` of simplicial sets is a weak homotopy equivalence in the sense of
`SSet.IsWeakHomotopyEquivalence` when it induces a bijection on homotopy classes of maps into every
Kan complex. We show that its geometric realization `|f| : |X| ⟶ |Y|` is then a homotopy
equivalence (`SSet.IsWeakHomotopyEquivalence.toTopHomotopyEquiv`). Hence `f` is a weak equivalence
of the Kan–Quillen model structure, whose weak equivalences are the maps with weakly homotopy
equivalent realizations (`SSet.modelCategoryQuillen.weakEquivalence_of_isWeakHomotopyEquivalence`).

The test objects are the singular simplicial sets `Sing T` of spaces, which are Kan complexes. Maps
`X ⟶ Sing T` are homotopic exactly when their adjoints `|X| ⟶ T` are
(`SSet.nonempty_homotopy_iff_homotopic_homEquiv_symm`), so `f` induces a bijection between the
homotopy classes of maps `|Y| ⟶ T` and `|X| ⟶ T`, for every space `T`. Taking `T = |X|`, the
identity of `|X|` is homotopic to `g ∘ |f|` for some `g : |Y| ⟶ |X|`. Taking `T = |Y|`, the maps
`|f| ∘ g` and the identity of `|Y|` become homotopic after composing with `|f|`, hence are
homotopic.

Anodyne extensions are monomorphisms and weak homotopy equivalences
(`SSet.anodyneExtensions.isWeakHomotopyEquivalence`), so they are trivial cofibrations of the
Kan–Quillen model structure
(`SSet.modelCategoryQuillen.anodyneExtensions_le_trivialCofibrations`). The converse inclusion,
that every trivial cofibration is anodyne, is not proved here.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Sections I.4 and I.11.
* J. Lurie, *Kerodon*, Definition 3.1.7.12 (Tag 00UA).
-/

public section

open CategoryTheory HomotopicalAlgebra Simplicial

universe u

namespace SSet

variable {X Y : SSet.{u}}

namespace IsWeakHomotopyEquivalence

variable (f : X ⟶ Y) [IsWeakHomotopyEquivalence f]

/-- If `f : X ⟶ Y` is a weak homotopy equivalence, the unit `X ⟶ Sing |X|` of the
realization–singular adjunction is homotopic to the composite of `f` with a map
`Y ⟶ Sing |X|`. -/
private lemma exists_homotopy_unit :
    ∃ h : Y ⟶ TopCat.toSSet.obj |X|, Nonempty (Homotopy (f ≫ h) (sSetTopAdj.unit.app X)) :=
  exists_homotopy f _

/-- The realization of a weak homotopy equivalence `f : X ⟶ Y` is a homotopy equivalence. Its
homotopy inverse `|Y| ⟶ |X|` is adjoint to a map `h : Y ⟶ Sing |X|` such that `f ≫ h` is
homotopic to the unit `X ⟶ Sing |X|` of the realization–singular adjunction. -/
noncomputable def toTopHomotopyEquiv : ContinuousMap.HomotopyEquiv |X| |Y| where
  toFun := (toTop.map f).hom
  invFun := ((sSetTopAdj.homEquiv Y |X|).symm (exists_homotopy_unit f).choose).hom
  left_inv := by
    have H := (nonempty_homotopy_iff_homotopic_homEquiv_symm _ _).1
      (exists_homotopy_unit f).choose_spec
    rwa [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_symm_unit,
      TopCat.hom_comp, TopCat.hom_id] at H
  right_inv := by
    obtain ⟨H⟩ := (exists_homotopy_unit f).choose_spec
    -- Writing `g` for the homotopy inverse, the maps `Y ⟶ Sing |Y|` adjoint to `|f| ∘ g` and to
    -- the identity of `|Y|` become homotopic after precomposition with `f`, by composing with
    -- `Sing |f|` and using the naturality of the unit.
    have H' := H.postcomp (TopCat.toSSet.map (toTop.map f))
    rw [Category.assoc, sSetTopAdj.unit_naturality] at H'
    have H'' := (nonempty_homotopy_iff_homotopic_homEquiv_symm _ _).1 (nonempty_homotopy f ⟨H'⟩)
    rwa [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_symm_unit,
      TopCat.hom_comp, TopCat.hom_id] at H''

/-- The realization of a weak homotopy equivalence `f` is a homotopy equivalence with underlying
map `|f|`. -/
@[simp]
lemma toTopHomotopyEquiv_toFun : (toTopHomotopyEquiv f).toFun = (toTop.map f).hom :=
  (rfl)

end IsWeakHomotopyEquivalence

namespace modelCategoryQuillen

/-- A weak homotopy equivalence, tested against Kan complexes, is a weak equivalence of the
Kan–Quillen model structure: its realization is a weak homotopy equivalence. -/
theorem weakEquivalence_of_isWeakHomotopyEquivalence (f : X ⟶ Y) [IsWeakHomotopyEquivalence f] :
    WeakEquivalence f :=
  (weakEquivalence_iff f).2
    (IsWeakHomotopyEquivalence.toTopHomotopyEquiv f).isWeakHomotopyEquivalence

/-- An anodyne extension is a weak equivalence of the Kan–Quillen model structure. -/
theorem weakEquivalence_of_anodyneExtensions {i : X ⟶ Y} (hi : anodyneExtensions i) :
    WeakEquivalence i :=
  have := anodyneExtensions.isWeakHomotopyEquivalence hi
  weakEquivalence_of_isWeakHomotopyEquivalence i

/-- Anodyne extensions are trivial cofibrations of the Kan–Quillen model structure. -/
theorem anodyneExtensions_le_trivialCofibrations :
    anodyneExtensions.{u} ≤ trivialCofibrations SSet.{u} := fun _ _ i hi ↦
  have := weakEquivalence_of_anodyneExtensions hi
  ⟨anodyneExtensions_le_monomorphisms i hi, mem_weakEquivalences i⟩

end modelCategoryQuillen

end SSet
