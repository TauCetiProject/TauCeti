/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.Geometry.Hodge.BaseChange
public import TauCeti.Geometry.Hodge.Substructure

/-!
# Rational substructures of pure Hodge structures

A rational Hodge substructure is a rational subspace whose complexification is spanned by its
intersections with the Hodge components. This file packages that condition and equips the
complexified subspace with the pure Hodge structure it inherits from the ambient one, so that the
whole `HodgeStructureOn` API applies to it — in particular the Hodge decomposition of the
complexified subspace into its own components is `HodgeStructureOn.isInternal_piece`, not a second
copy of that argument.

Conjugation stability of the complexification is not a field of the structure: it holds for every
rational subspace, by `rationalToComplexSubmodule_conj`. Together with the spanning condition this
exhibits the complexification as a sub-Hodge structure in the sense of
`TauCeti.Hodge.HodgeStructureOn.IsSubstructure`, and the induced conjugation, filtration and
components are read off from that general construction.

The definition and its base-change interface are those specified in Layer L1 of
`TauCetiRoadmap/HodgeStructures/README.md`, following Voisin, *Hodge Theory and Complex Algebraic
Geometry I*, §7.1.2. The induced structure is what makes a rational Hodge substructure a subobject
of a Hodge structure, as the semisimplicity milestone of that layer requires.

The signatures of `RationalHodgeSubstructure` and `RationalHodgeSubstructure.WC` are adapted from
the roadmap's formal companion
[`HodgeStructures/Suggested.lean`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/HodgeStructures/Suggested.lean).

## Main declarations

* `TauCeti.Hodge.RationalHodgeSubstructure`: a rational subspace split by the Hodge components.
* `TauCeti.Hodge.RationalHodgeSubstructure.isSubstructure`: its complexification is a sub-Hodge
  structure of the ambient pure Hodge structure, so
  `TauCeti.Hodge.HodgeStructureOn.IsSubstructure.hodgeStructure` equips it with the induced pure
  Hodge structure, whose Hodge components are the intersections with the ambient ones.
* `TauCeti.Hodge.RationalHodgeSubstructure.ofIsSubstructure`: conversely, a rational subspace whose
  complexification is a sub-Hodge structure is a rational Hodge substructure.
* `TauCeti.Hodge.RationalHodgeSubstructure.ofRationalMorphismRange` and
  `…ofRationalMorphismKer`: the image and kernel of a rational linear map whose complexification is
  a morphism of pure Hodge structures, as rational Hodge substructures.
* The `Lattice`, `BoundedOrder` and `IsModularLattice` instances: rational Hodge substructures
  form a modular lattice under inclusion.
* `TauCeti.Hodge.RationalHodgeSubstructure.exists_isAtom_le`: over a finite-dimensional rational
  space that lattice is atomic, its atoms being the simple substructures.
-/

public section

namespace TauCeti.Hodge

universe u v w u' v' w'

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {n : ℤ} {hs : HodgeStructure hℂ n}

/-- A rational Hodge substructure of a pure Hodge structure.

Its rational subspace `WQ` complexifies to the sum of its intersections with the Hodge
components. Stability under conjugation is not a field: it follows from rationality via
`rationalToComplexSubmodule_conj`. -/
@[ext]
structure RationalHodgeSubstructure (hℚ : IsBaseChange ℚ ιℚ) (hs : HodgeStructure hℂ n) where
  /-- The underlying rational subspace. -/
  WQ : Submodule ℚ Vℚ
  /-- The complexification is spanned by its intersections with the Hodge components. -/
  hodge_spanning : rationalToComplexSubmodule hℚ hℂ WQ =
    ⨆ p, rationalToComplexSubmodule hℚ hℂ WQ ⊓ hs.piece p

namespace RationalHodgeSubstructure

/-- The complexification of a rational Hodge substructure inside the ambient complexification. -/
noncomputable def WC (W : RationalHodgeSubstructure hℚ hs) : Submodule ℂ Vℂ :=
  rationalToComplexSubmodule hℚ hℂ W.WQ

/-- The complexification of a rational Hodge substructure is the complexification of its rational
subspace. -/
theorem WC_def (W : RationalHodgeSubstructure hℚ hs) :
    W.WC = rationalToComplexSubmodule hℚ hℂ W.WQ :=
  (rfl)

/-- The complexification is the supremum of its intersections with the ambient Hodge
components. -/
theorem WC_eq_iSup_inf_piece (W : RationalHodgeSubstructure hℚ hs) :
    W.WC = ⨆ p, W.WC ⊓ hs.piece p :=
  W.hodge_spanning

/-- The complexification of a rational Hodge substructure is stable under conjugation. -/
@[simp]
theorem map_WC_conj (W : RationalHodgeSubstructure hℚ hs) :
    W.WC.map (latticeConjugation hℂ).toEquiv.toLinearMap = W.WC := by
  rw [latticeConjugation_toLinearMap, WC_def]
  exact rationalToComplexSubmodule_conj hℚ hℂ W.WQ

/-- Conjugation carries every vector of a rational Hodge substructure back into its
complexification. -/
theorem conj_mem_WC (W : RationalHodgeSubstructure hℚ hs) {x : Vℂ} (hx : x ∈ W.WC) :
    (latticeConjugation hℂ).toEquiv x ∈ W.WC := by
  rw [← W.map_WC_conj]
  exact Submodule.mem_map_of_mem hx

/-- The complexification of a rational Hodge substructure is a sub-Hodge structure of the ambient
pure Hodge structure: it is conjugation stable because it is rational, and spanned by its
intersections with the Hodge components by definition. The induced pure Hodge structure is
`TauCeti.Hodge.HodgeStructureOn.IsSubstructure.hodgeStructure`. -/
theorem isSubstructure (W : RationalHodgeSubstructure hℚ hs) : hs.IsSubstructure W.WC :=
  ⟨fun _ hx ↦ by
    simpa only [latticeConjugation_toEquiv_apply] using W.conj_mem_WC hx,
    le_of_eq W.WC_eq_iSup_inf_piece⟩

/-- A rational subspace whose complexification is a sub-Hodge structure is a rational Hodge
substructure. This is the converse of `TauCeti.Hodge.RationalHodgeSubstructure.isSubstructure`. -/
def ofIsSubstructure (A : Submodule ℚ Vℚ)
    (h : hs.IsSubstructure (rationalToComplexSubmodule hℚ hℂ A)) :
    RationalHodgeSubstructure hℚ hs where
  WQ := A
  hodge_spanning := h.eq_iSup_inf_piece

@[simp]
theorem ofIsSubstructure_WQ (A : Submodule ℚ Vℚ)
    (h : hs.IsSubstructure (rationalToComplexSubmodule hℚ hℂ A)) :
    (ofIsSubstructure A h).WQ = A :=
  (rfl)

/-! ### Subobjects cut out by rational morphisms -/

section Morphism

variable {V'ℤ : Type u'} {V'ℚ : Type v'} {V'ℂ : Type w'}
variable [AddCommGroup V'ℤ]
variable [AddCommGroup V'ℚ] [Module ℚ V'ℚ]
variable [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ι'ℚ : V'ℤ →ₗ[ℤ] V'ℚ} {ι'ℂ : V'ℤ →ₗ[ℤ] V'ℂ}
variable {h'ℚ : IsBaseChange ℚ ι'ℚ} {h'ℂ : IsBaseChange ℂ ι'ℂ}
variable {hs' : HodgeStructure h'ℂ n} {f : Vℚ →ₗ[ℚ] V'ℚ}
variable (hf : HodgeStructureOn.IsMorphism hs hs' (rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f))

/-- **The image of a rational Hodge morphism**, as a rational Hodge substructure of the target: its
complexification is the image of the complexified map, which is a sub-Hodge structure. -/
def ofRationalMorphismRange : RationalHodgeSubstructure h'ℚ hs' :=
  ofIsSubstructure (LinearMap.range f) <| by
    rw [← range_rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f]
    exact hf.isSubstructure_range

@[simp]
theorem ofRationalMorphismRange_WQ : (ofRationalMorphismRange hf).WQ = LinearMap.range f :=
  ofIsSubstructure_WQ _ _

/-- The complexification of the image of a rational Hodge morphism is the image of the
complexified map. -/
@[simp]
theorem ofRationalMorphismRange_WC :
    (ofRationalMorphismRange hf).WC = LinearMap.range (rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f) := by
  rw [WC_def, ofRationalMorphismRange_WQ, range_rationalMapToComplex]

/-- **The kernel of a rational Hodge morphism**, as a rational Hodge substructure of the source:
its complexification is the kernel of the complexified map, which is a sub-Hodge structure. -/
def ofRationalMorphismKer : RationalHodgeSubstructure hℚ hs :=
  ofIsSubstructure (LinearMap.ker f) <| by
    rw [← ker_rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f]
    exact hf.isSubstructure_ker

@[simp]
theorem ofRationalMorphismKer_WQ : (ofRationalMorphismKer hf).WQ = LinearMap.ker f :=
  ofIsSubstructure_WQ _ _

/-- The complexification of the kernel of a rational Hodge morphism is the kernel of the
complexified map. -/
@[simp]
theorem ofRationalMorphismKer_WC :
    (ofRationalMorphismKer hf).WC = LinearMap.ker (rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f) := by
  rw [WC_def, ofRationalMorphismKer_WQ, ker_rationalMapToComplex]

end Morphism

/-! ### The lattice of rational Hodge substructures

Rational Hodge substructures are ordered by inclusion of their rational subspaces, and the
intersection and the sum of two of them are again rational Hodge substructures. The resulting
lattice is modular, being a sublattice of the lattice of rational subspaces, and it satisfies the
descending chain condition as soon as the ambient rational space is finite-dimensional; so every
nonzero rational Hodge substructure contains a simple one, an atom of this lattice. -/

instance : LE (RationalHodgeSubstructure hℚ hs) where
  le W₁ W₂ := W₁.WQ ≤ W₂.WQ

instance : LT (RationalHodgeSubstructure hℚ hs) where
  lt W₁ W₂ := W₁.WQ < W₂.WQ

@[simp]
theorem le_def {W₁ W₂ : RationalHodgeSubstructure hℚ hs} : W₁ ≤ W₂ ↔ W₁.WQ ≤ W₂.WQ :=
  Iff.rfl

@[simp]
theorem lt_def {W₁ W₂ : RationalHodgeSubstructure hℚ hs} : W₁ < W₂ ↔ W₁.WQ < W₂.WQ :=
  Iff.rfl

instance : Max (RationalHodgeSubstructure hℚ hs) where
  max W₁ W₂ := ofIsSubstructure (W₁.WQ ⊔ W₂.WQ) <| by
    rw [rationalToComplexSubmodule_sup]
    exact W₁.isSubstructure.sup W₂.isSubstructure

instance : Min (RationalHodgeSubstructure hℚ hs) where
  min W₁ W₂ := ofIsSubstructure (W₁.WQ ⊓ W₂.WQ) <| by
    rw [rationalToComplexSubmodule_inf]
    exact W₁.isSubstructure.inf W₂.isSubstructure

instance : Bot (RationalHodgeSubstructure hℚ hs) where
  bot := ofIsSubstructure ⊥ (by simp)

instance : Top (RationalHodgeSubstructure hℚ hs) where
  top := ofIsSubstructure ⊤ (by simp)

@[simp]
theorem sup_WQ (W₁ W₂ : RationalHodgeSubstructure hℚ hs) :
    (W₁ ⊔ W₂).WQ = W₁.WQ ⊔ W₂.WQ :=
  (rfl)

@[simp]
theorem inf_WQ (W₁ W₂ : RationalHodgeSubstructure hℚ hs) :
    (W₁ ⊓ W₂).WQ = W₁.WQ ⊓ W₂.WQ :=
  (rfl)

@[simp]
theorem bot_WQ : (⊥ : RationalHodgeSubstructure hℚ hs).WQ = ⊥ :=
  (rfl)

@[simp]
theorem top_WQ : (⊤ : RationalHodgeSubstructure hℚ hs).WQ = ⊤ :=
  (rfl)

instance : Lattice (RationalHodgeSubstructure hℚ hs) :=
  Function.Injective.lattice WQ (fun _ _ h ↦ RationalHodgeSubstructure.ext h) Iff.rfl Iff.rfl
    sup_WQ inf_WQ

instance : BoundedOrder (RationalHodgeSubstructure hℚ hs) where
  bot_le _ := le_def.2 (by rw [bot_WQ]; exact bot_le)
  le_top _ := le_def.2 (by rw [top_WQ]; exact le_top)

@[simp]
theorem sup_WC (W₁ W₂ : RationalHodgeSubstructure hℚ hs) :
    (W₁ ⊔ W₂).WC = W₁.WC ⊔ W₂.WC := by
  rw [WC_def, sup_WQ, rationalToComplexSubmodule_sup, WC_def, WC_def]

@[simp]
theorem inf_WC (W₁ W₂ : RationalHodgeSubstructure hℚ hs) :
    (W₁ ⊓ W₂).WC = W₁.WC ⊓ W₂.WC := by
  rw [WC_def, inf_WQ, rationalToComplexSubmodule_inf, WC_def, WC_def]

@[simp]
theorem bot_WC : (⊥ : RationalHodgeSubstructure hℚ hs).WC = ⊥ := by
  rw [WC_def, bot_WQ, rationalToComplexSubmodule_bot]

@[simp]
theorem top_WC : (⊤ : RationalHodgeSubstructure hℚ hs).WC = ⊤ := by
  rw [WC_def, top_WQ, rationalToComplexSubmodule_top]

/-- Two rational Hodge substructures are complementary exactly when their rational subspaces
are. -/
@[simp]
theorem isCompl_iff_WQ {W₁ W₂ : RationalHodgeSubstructure hℚ hs} :
    IsCompl W₁ W₂ ↔ IsCompl W₁.WQ W₂.WQ := by
  constructor
  · refine fun h ↦ ⟨disjoint_iff.2 ?_, codisjoint_iff.2 ?_⟩
    · rw [← inf_WQ, disjoint_iff.1 h.disjoint, bot_WQ]
    · rw [← sup_WQ, codisjoint_iff.1 h.codisjoint, top_WQ]
  · refine fun h ↦ ⟨disjoint_iff.2 (RationalHodgeSubstructure.ext ?_),
      codisjoint_iff.2 (RationalHodgeSubstructure.ext ?_)⟩
    · rw [inf_WQ, bot_WQ, ← disjoint_iff]
      exact h.disjoint
    · rw [sup_WQ, top_WQ, ← codisjoint_iff]
      exact h.codisjoint

instance : IsModularLattice (RationalHodgeSubstructure hℚ hs) where
  sup_inf_le_assoc_of_le {_} y {_} hxz := by
    simp only [le_def, sup_WQ, inf_WQ]
    exact IsModularLattice.sup_inf_le_assoc_of_le y.WQ (le_def.1 hxz)

/-- The rational subspace of a finite supremum of rational Hodge substructures. -/
@[simp]
theorem finsetSup_WQ (s : Finset (RationalHodgeSubstructure hℚ hs)) :
    (s.sup id).WQ = s.sup fun W ↦ W.WQ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [ih]

/-- Passing to the underlying rational subspace is strictly monotone. -/
theorem WQ_strictMono :
    StrictMono (WQ : RationalHodgeSubstructure hℚ hs → Submodule ℚ Vℚ) :=
  fun _ _ h ↦ lt_def.1 h

instance [Module.Finite ℚ Vℚ] : WellFoundedLT (RationalHodgeSubstructure hℚ hs) :=
  (Submodule.finrank_strictMono.comp WQ_strictMono).wellFoundedLT

/-- **Every nonzero rational Hodge substructure contains a simple one.** The simple substructures
are the atoms of the lattice of rational Hodge substructures, and over a finite-dimensional
rational space that lattice is atomic. -/
theorem exists_isAtom_le [Module.Finite ℚ Vℚ] {W : RationalHodgeSubstructure hℚ hs} (hW : W ≠ ⊥) :
    ∃ U : RationalHodgeSubstructure hℚ hs, IsAtom U ∧ U ≤ W :=
  (eq_bot_or_exists_atom_le W).resolve_left hW

end RationalHodgeSubstructure

end TauCeti.Hodge
