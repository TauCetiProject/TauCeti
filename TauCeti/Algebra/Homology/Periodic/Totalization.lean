/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Totalizations of short complexes of periodic complexes

For a short complex `K ⟶ L ⟶ M` of cyclic cochain complexes, its totalization is the
iterated cone `cone(cone(K ⟶ L) ⟶ M)`. Its terms are `Kⁱ⁺² ⊞ Lⁱ⁺¹ ⊞ Mⁱ`, with the signs
inherited from the cochain cone. The construction is functorial in short complexes.

The totalization of a short exact sequence is acyclic. Indeed, the comparison from the first
cone to the last term is a quasi-isomorphism. No splitting of the sequence is assumed.

The definitions require only a preadditive category with binary biproducts; the acyclicity
result requires an abelian category. Period zero is allowed and gives integer-indexed complexes.

## References

* C. A. Weibel, *An introduction to homological algebra*, Section 1.5.
* T. Stai, *The triangulated hull of periodic complexes*, Section 3.

The cone comparison follows `HomologicalComplex.homotopyCofiber.descShortComplex`.
-/

public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {C : Type u} [Category.{v} C] {n : ℕ}

section Preadditive

variable [Preadditive C] [HasBinaryBiproducts C]

/-- The totalization of a short complex of cyclic cochain complexes, as an iterated cone. -/
-- Keep cone endpoints available for the component calculus of its maps.
@[expose, implicit_reducible]
noncomputable def totalization (S : ShortComplex (CochainComplex C (ZMod n))) :
    CochainComplex C (ZMod n) :=
  homotopyCofiber (homotopyCofiber.descShortComplex S)

/-- The defining iterated-cone formula for totalization. -/
theorem totalization_eq (S : ShortComplex (CochainComplex C (ZMod n))) :
    totalization S = homotopyCofiber (homotopyCofiber.descShortComplex S) :=
  (rfl)

/-- The three summands of a totalization in cyclic degree `i`. -/
noncomputable def totalizationXIso (S : ShortComplex (CochainComplex C (ZMod n)))
    (i : ZMod n) :
    (totalization S).X i ≅ (S.X₁.X (i + 1 + 1) ⊞ S.X₂.X (i + 1)) ⊞ S.X₃.X i :=
  homotopyCofiber.XIsoBiprod (homotopyCofiber.descShortComplex S) i (i + 1) rfl ≪≫
    biprod.mapIso (homotopyCofiber.XIsoBiprod S.f (i + 1) (i + 1 + 1) rfl) (Iso.refl _)

section Coordinates

open homotopyCofiber

variable (S : ShortComplex (CochainComplex C (ZMod n))) (i : ZMod n)

/-- The outer cone's left inclusion inserts the first two coordinate summands. -/
@[reassoc]
theorem inlX_totalizationXIso_hom :
    inlX (descShortComplex S) (i + 1) i rfl ≫ (totalizationXIso S i).hom =
      (XIsoBiprod S.f (i + 1) (i + 1 + 1) rfl).hom ≫ biprod.inl := by
  dsimp only [totalizationXIso, Iso.trans_hom, biprod.mapIso_hom, Iso.refl_hom]
  -- Keep relation proofs typed for the dependent cone coordinate API.
  generalize_proofs
  simp

/-- The last term is the rightmost summand of the totalization coordinates. -/
@[reassoc (attr := simp)]
theorem inrX_totalizationXIso_hom :
    inrX (descShortComplex S) i ≫ (totalizationXIso S i).hom = biprod.inr := by
  dsimp only [totalizationXIso, Iso.trans_hom, biprod.mapIso_hom, Iso.refl_hom]
  -- Keep relation proofs typed for the dependent cone coordinate API.
  generalize_proofs
  simp

/-- The shifted first term is the leftmost summand of the totalization coordinates. -/
@[reassoc (attr := simp)]
theorem inlX_inlX_totalizationXIso_hom :
    inlX S.f (i + 1 + 1) (i + 1) rfl ≫ inlX (descShortComplex S) (i + 1) i rfl ≫
      (totalizationXIso S i).hom = biprod.inl ≫ biprod.inl := by
  rw [inlX_totalizationXIso_hom]
  generalize_proofs
  simp

/-- The shifted middle term is the middle summand of the totalization coordinates. -/
@[reassoc (attr := simp)]
theorem inrX_inlX_totalizationXIso_hom :
    inrX S.f (i + 1) ≫ inlX (descShortComplex S) (i + 1) i rfl ≫
      (totalizationXIso S i).hom = biprod.inr ≫ biprod.inl := by
  rw [inlX_totalizationXIso_hom]
  generalize_proofs
  simp

/-- On the first summand, the two cone shifts give `d_K` and the off-diagonal entry `-f`. -/
@[reassoc]
theorem inlX_inlX_totalization_d :
    inlX S.f (i + 1 + 1) (i + 1) rfl ≫ inlX (descShortComplex S) (i + 1) i rfl ≫
      (totalization S).d i (i + 1) ≫ (totalizationXIso S (i + 1)).hom =
        S.X₁.d (i + 1 + 1) (i + 1 + 1 + 1) ≫ biprod.inl ≫ biprod.inl -
          S.f.f (i + 1 + 1) ≫ biprod.inr ≫ biprod.inl := by
  have hi : (ComplexShape.up (ZMod n)).Rel i (i + 1) := rfl
  have hi' : (ComplexShape.up (ZMod n)).Rel (i + 1) (i + 1 + 1) := rfl
  have hi'' : (ComplexShape.up (ZMod n)).Rel (i + 1 + 1) (i + 1 + 1 + 1) := rfl
  simp [totalization, inlX_d_assoc _ _ _ _ hi hi', inlX_d_assoc _ _ _ _ hi' hi'',
    Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
    inlX_totalizationXIso_hom, inlX_descShortComplex_f_assoc S _ _ hi',
    inrX_XIsoBiprod_hom_assoc S.f _ _ hi'', sub_eq_add_neg, add_comm]

/-- On the middle summand, the totalization differential has entries `-d_L` and `g`. -/
@[reassoc]
theorem inrX_inlX_totalization_d :
    inrX S.f (i + 1) ≫ inlX (descShortComplex S) (i + 1) i rfl ≫
      (totalization S).d i (i + 1) ≫ (totalizationXIso S (i + 1)).hom =
        -S.X₂.d (i + 1) (i + 1 + 1) ≫ biprod.inr ≫ biprod.inl +
          S.g.f (i + 1) ≫ biprod.inr := by
  have hi : (ComplexShape.up (ZMod n)).Rel i (i + 1) := rfl
  have hi' : (ComplexShape.up (ZMod n)).Rel (i + 1) (i + 1 + 1) := rfl
  simp [totalization, inlX_d_assoc _ _ _ _ hi hi',
    Preadditive.comp_add, Preadditive.add_comp, Category.assoc]

/-- On the last summand, the totalization differential is `d_M`. -/
@[reassoc]
theorem inrX_totalization_d :
    inrX (descShortComplex S) i ≫ (totalization S).d i (i + 1) ≫
      (totalizationXIso S (i + 1)).hom = S.X₃.d i (i + 1) ≫ biprod.inr := by
  simp only [totalization, homotopyCofiber_d, inrX_d_assoc,
    inrX_totalizationXIso_hom]

end Coordinates

/-- A morphism of short complexes gives a commutative square between their cone comparisons. -/
private noncomputable def totalizationArrowMap
    {S T : ShortComplex (CochainComplex C (ZMod n))} (α : S ⟶ T) :
    Arrow.mk (homotopyCofiber.descShortComplex S) ⟶
      Arrow.mk (homotopyCofiber.descShortComplex T) :=
  Arrow.homMk
    (homotopyCofiber.mapArrowHom S.f T.f (fun j ↦ ⟨j - 1, by simp⟩)
      (Arrow.homMk α.τ₁ α.τ₂ α.comm₁₂)) α.τ₃
    (homotopyCofiber.mapArrowHom_descShortComplex α _)

/-- The left map of the totalization square is induced by the first two maps of the sequence. -/
@[simp]
private theorem totalizationArrowMap_left
    {S T : ShortComplex (CochainComplex C (ZMod n))} (α : S ⟶ T) :
    (totalizationArrowMap α).left =
      homotopyCofiber.mapArrowHom S.f T.f (fun j ↦ ⟨j - 1, by simp⟩)
        (Arrow.homMk α.τ₁ α.τ₂ α.comm₁₂) :=
  (rfl)

/-- The right map of the totalization square is the map on the last terms. -/
@[simp]
private theorem totalizationArrowMap_right
    {S T : ShortComplex (CochainComplex C (ZMod n))} (α : S ⟶ T) :
    (totalizationArrowMap α).right = α.τ₃ :=
  (rfl)

/-- The map on totalizations induced by a morphism of short complexes. -/
noncomputable def totalizationMap
    {S T : ShortComplex (CochainComplex C (ZMod n))} (α : S ⟶ T) :
    totalization S ⟶ totalization T :=
  homotopyCofiber.mapArrowHom _ _ (fun j ↦ ⟨j - 1, by simp⟩) (totalizationArrowMap α)

/-- On the last term of the sequence, a totalization map is the given third map. -/
@[reassoc (attr := simp)]
theorem inr_totalizationMap
    {S T : ShortComplex (CochainComplex C (ZMod n))} (α : S ⟶ T) :
    homotopyCofiber.inr (homotopyCofiber.descShortComplex S) ≫ totalizationMap α =
      α.τ₃ ≫ homotopyCofiber.inr (homotopyCofiber.descShortComplex T) := by
  simp [totalizationMap]

/-- In the three-summand coordinates, a totalization map is diagonal. -/
@[reassoc]
theorem totalizationMap_f_comp_totalizationXIso_hom
    {S T : ShortComplex (CochainComplex C (ZMod n))} (α : S ⟶ T) (i : ZMod n) :
    (totalizationMap α).f i ≫ (totalizationXIso T i).hom =
      (totalizationXIso S i).hom ≫
        biprod.map (biprod.map (α.τ₁.f (i + 1 + 1)) (α.τ₂.f (i + 1))) (α.τ₃.f i) := by
  have hi : (ComplexShape.up (ZMod n)).Rel i (i + 1) := by simp
  have hi' : (ComplexShape.up (ZMod n)).Rel (i + 1) (i + 1 + 1) := by simp
  apply homotopyCofiber.ext_from_X (homotopyCofiber.descShortComplex S) (i + 1) i hi <;>
    simp only [totalizationMap, totalizationXIso, Iso.trans_hom, biprod.mapIso_hom]
  -- Keep shape-relation proofs typed while simplifying the dependent cone coordinates.
  all_goals generalize_proofs
  · rw [homotopyCofiber.inlX_mapArrowHom_f_assoc]
    simp only [totalizationArrowMap_left, homotopyCofiber.inlX_XIsoBiprod_hom_assoc]
    apply homotopyCofiber.ext_from_X S.f (i + 1 + 1) (i + 1) hi' <;>
      simp [Category.assoc]
  · rw [homotopyCofiber.inrX_mapArrowHom_f_assoc]
    simp [Category.assoc]

/-- Totalization preserves identity maps. -/
@[simp]
theorem totalizationMap_id (S : ShortComplex (CochainComplex C (ZMod n))) :
    totalizationMap (𝟙 S) = 𝟙 (totalization S) := by
  ext i
  rw [← cancel_mono (totalizationXIso S i).hom]
  simp only [totalizationMap_f_comp_totalizationXIso_hom, ShortComplex.id_τ₁,
    ShortComplex.id_τ₂, ShortComplex.id_τ₃, id_f, Category.id_comp]
  ext <;> simp

/-- Totalization preserves composition. -/
@[reassoc, simp]
theorem totalizationMap_comp
    {S T U : ShortComplex (CochainComplex C (ZMod n))} (α : S ⟶ T) (β : T ⟶ U) :
    totalizationMap (α ≫ β) = totalizationMap α ≫ totalizationMap β := by
  have h : totalizationArrowMap (α ≫ β) = totalizationArrowMap α ≫ totalizationArrowMap β := by
    apply Arrow.hom_ext
    · simp only [totalizationArrowMap_left, Arrow.comp_left]
      rw [← homotopyCofiber.mapArrowHom_comp]
      congr 1
    · rfl
  unfold totalizationMap
  rw [h, homotopyCofiber.mapArrowHom_comp]

/-- Totalization as a functor on short complexes of periodic complexes. -/
-- Expose the selected object formula for maps with represented endpoints.
@[expose, implicit_reducible]
noncomputable def totalizationFunctor :
    ShortComplex (CochainComplex C (ZMod n)) ⥤ CochainComplex C (ZMod n) where
  obj := totalization
  map := totalizationMap
  map_id := totalizationMap_id
  map_comp := totalizationMap_comp

/-- The totalization functor has the specified iterated cone as its object. -/
@[simp]
theorem totalizationFunctor_obj (S : ShortComplex (CochainComplex C (ZMod n))) :
    totalizationFunctor.obj S = totalization S :=
  (rfl)

/-- The totalization functor acts by the induced map of iterated cones. -/
@[simp]
theorem totalizationFunctor_map
    {S T : ShortComplex (CochainComplex C (ZMod n))} (α : S ⟶ T) :
    totalizationFunctor.map α = totalizationMap α :=
  (rfl)

/-- Totalization is additive in maps of short complexes. -/
instance : (totalizationFunctor (C := C) (n := n)).Additive where
  map_add {S T} α β := by
    ext i
    rw [← cancel_mono (totalizationXIso T i).hom]
    simp only [totalizationFunctor_map, HomologicalComplex.add_f_apply, Preadditive.add_comp,
      totalizationMap_f_comp_totalizationXIso_hom]
    simp only [ShortComplex.add_τ₁, ShortComplex.add_τ₂, ShortComplex.add_τ₃,
      HomologicalComplex.add_f_apply]
    rw [← Preadditive.comp_add]
    congr 1
    ext <;> simp [Preadditive.add_comp]

/-- Totalization respects the scalar-linear structure of the base category. -/
instance {R : Type*} [Semiring R] [Linear R C] :
    (totalizationFunctor (C := C) (n := n)).Linear R where
  map_smul {S T} α r := by
    ext i
    rw [← cancel_mono (totalizationXIso T i).hom]
    simp only [totalizationFunctor_map, HomologicalComplex.smul_f_apply, Linear.smul_comp,
      totalizationMap_f_comp_totalizationXIso_hom]
    simp only [ShortComplex.smul_τ₁, ShortComplex.smul_τ₂, ShortComplex.smul_τ₃,
      HomologicalComplex.smul_f_apply]
    rw [← Linear.comp_smul]
    congr 1
    ext <;> simp [Linear.smul_comp]

end Preadditive

variable [Abelian C]

/-- The totalization of a short exact sequence of periodic complexes is acyclic. -/
theorem acyclic_totalization {S : ShortComplex (CochainComplex C (ZMod n))}
    (hS : S.ShortExact) : (totalization S).Acyclic := by
  rw [totalization_eq, ← quasiIso_iff_acyclic_homotopyCofiber]
  exact homotopyCofiber.quasiIso_descShortComplex hS (fun j ↦ ⟨j - 1, by simp⟩)

/-- Every cyclic homology object of the totalization of a short exact sequence vanishes. -/
theorem isZero_homology_totalization {S : ShortComplex (CochainComplex C (ZMod n))}
    (hS : S.ShortExact) (i : ZMod n) : IsZero ((totalization S).homology i) :=
  (acyclic_totalization hS i).isZero_homology

end TauCeti.PeriodicComplex
