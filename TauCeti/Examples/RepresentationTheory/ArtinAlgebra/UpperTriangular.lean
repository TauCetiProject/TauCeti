/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.ValuedQuiver
public import TauCeti.RepresentationTheory.Quiver.AuslanderReiten.A2.Basic
public import TauCeti.RepresentationTheory.Quiver.Kronecker.UpperTriangular
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.CategoryTheory.AlmostSplit.Equivalence
import TauCeti.CategoryTheory.AlmostSplit.Uniqueness
import TauCeti.RepresentationTheory.Quiver.AuslanderReiten.A2.Translation
import TauCeti.RepresentationTheory.Quiver.Kronecker.AlmostSplit

/-!
# The valued Auslander–Reiten quiver of upper-triangular `2 × 2` matrices

Over any field, the upper-triangular algebra has three indecomposable finitely generated
modules. In the order given by the two simples of the one-arrow quiver and the source
projective, its valued Auslander–Reiten quiver is `1 ⟶ 2 ⟶ 0`, with valuations `(1, 1)`
and with `τ 0 = 1` the only defined translate.

The computation uses `TauCeti.Quiver.Kronecker.upperTriangularAlgEquiv` to identify the algebra
with a path algebra, and then uses the indecomposable and arrow calculations for the one-arrow
quiver.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Proposition III.2.2 for the triangular module description and
  Section VII.1 for the valued quiver and its translation.
-/

public section

namespace TauCeti

open CategoryTheory ModuleCat IrreducibleMorphismQuiver Quiver.Kronecker
open scoped ModuleCat.Algebra

universe u

variable (k : Type u) [Field k]

local notation "T₂" => Matrix.blockTriangularSubalgebra k k (id : Fin 2 → Fin 2)
local notation "Q" => Quiver.Kronecker Unit
local notation "IsFiniteModule" => (fun M : ModuleCat.{_} T₂ ↦ Module.Finite T₂ M)

local notation "matrixEquiv" => AlgEquiv.toRingEquiv (upperTriangularAlgEquiv (A := Unit) k)

/-- The module category of upper-triangular `2 × 2` matrices is equivalent to representations
of the one-arrow quiver. The off-diagonal matrix unit acts as the arrow map. -/
noncomputable def upperTriangularRepEquivalence :
    ModuleCat.{u} T₂ ≌ QuiverRep.{u, 0, 0, u} k Q :=
  (restrictScalarsEquivalenceOfRingEquiv matrixEquiv).trans
    (quiverRepFunctor k Q).asEquivalence

local notation "e" => upperTriangularRepEquivalence k
local notation "vertex" => IrreducibleMorphismQuiver.of

/-- The forward functor reads the representation of the path-algebra module obtained by
restricting scalars along the upper-triangular algebra identification. -/
theorem upperTriangularRepEquivalence_functor :
    (e).functor = restrictScalars (RingEquiv.toRingHom matrixEquiv) ⋙ quiverRepFunctor k Q :=
  (rfl)

instance : (e).functor.Additive :=
  inferInstanceAs <| Functor.Additive
    ((restrictScalarsEquivalenceOfRingEquiv matrixEquiv).functor ⋙ quiverRepFunctor k Q)

instance : (e).functor.Linear k :=
  inferInstanceAs <| Functor.Linear k
    ((restrictScalarsEquivalenceOfRingEquiv matrixEquiv).functor ⋙ quiverRepFunctor k Q)

/-- Finite generation of an upper-triangular module is equivalent to finite dimensionality of
both vertex spaces in the corresponding representation. -/
theorem isFinDim_upperTriangularRep_iff (M : ModuleCat.{u} T₂) :
    IsFinDim k Q ((e).functor.obj M) ↔ Module.Finite T₂ M := by
  let a := upperTriangularAlgEquiv (A := Unit) k
  let N := (restrictScalars a.toRingEquiv.toRingHom).obj M
  have hN := a.toRingEquiv.toRingHom.finite_restrictScalars_iff a.surjective M
  rw [upperTriangularRepEquivalence_functor, Functor.comp_obj, ← hN]
  constructor
  · intro h
    have : Module.Finite (pathAlgebra k Q)
        (((quiverRepEquivalence k Q).inverse ⋙ (quiverRepEquivalence k Q).functor).obj N) :=
      module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q _
        (by rwa [quiverRepEquivalence_inverse])
    exact Module.Finite.equiv ((quiverRepEquivalence k Q).counitIso.app N).toLinearEquiv
  · intro h
    exact isFinDim_quiverRepFunctor_obj k Q N (Module.Finite.trans (pathAlgebra k Q) N)

private noncomputable def upperTriangularRepVertex
    (x : IrreducibleMorphismQuiver k IsFiniteModule) :
    IrreducibleMorphismQuiver k (IsFinDim.{u, 0, 0, u} k Q) :=
  vertex k ((isFinDim_upperTriangularRep_iff k _).2 x.representative_property.1)
    ((e).indecomposable_functor_obj x.representative_property.2)

private theorem upperTriangularRepVertex_of {M : ModuleCat.{u} T₂}
    (hM : Module.Finite T₂ M) (hi : Indecomposable M) :
    upperTriangularRepVertex k (vertex k hM hi) =
      vertex k ((isFinDim_upperTriangularRep_iff k M).2 hM) ((e).indecomposable_functor_obj hi) :=
  (of_eq_of_iff _ _ _ _).2 ⟨(e).functor.mapIso (representativeIso (P := IsFiniteModule) k hM hi)⟩

private theorem bijective_upperTriangularRepVertex :
    Function.Bijective (upperTriangularRepVertex k) := by
  constructor
  · intro x y h
    rw [upperTriangularRepVertex, upperTriangularRepVertex, of_eq_of_iff] at h
    simpa only [of_representative] using (of_eq_of_iff (k := k) (P := IsFiniteModule)
      x.representative_property.1 x.representative_property.2 y.representative_property.1
      y.representative_property.2).2 (h.map (e).functor.preimageIso)
  · intro x
    let M := (e).inverse.obj x.representative
    let i : (e).functor.obj M ≅ x.representative := (e).counitIso.app _
    have hM := (isFinDim_upperTriangularRep_iff k M).1
      (ObjectProperty.prop_of_iso (IsFinDim k Q) i.symm x.representative_property.1)
    have hi := (e).symm.indecomposable_functor_obj x.representative_property.2
    refine ⟨vertex k hM hi, ?_⟩
    rw [upperTriangularRepVertex_of, ← of_representative x]
    exact (of_eq_of_iff _ _ _ _).2 ⟨i⟩

/-- The three indecomposable vertices of the upper-triangular algebra, ordered as the source
simple, target simple and source projective under the one-arrow representation equivalence. -/
noncomputable def upperTriangularARVertexEquiv :
    Fin 3 ≃ IrreducibleMorphismQuiver k IsFiniteModule :=
  (a2VertexEquiv k Unit).trans (Equiv.ofBijective _ (bijective_upperTriangularRepVertex k)).symm

private theorem upperTriangularRepVertex_vertexEquiv (i : Fin 3) :
    upperTriangularRepVertex k (upperTriangularARVertexEquiv k i) = a2VertexEquiv k Unit i :=
  (Equiv.ofBijective _ (bijective_upperTriangularRepVertex k)).apply_symm_apply _

/-- The index of an indecomposable module is determined by its image in the one-arrow
representation category. -/
theorem upperTriangularARVertexEquiv_eq_of_iff (i : Fin 3) {M : ModuleCat.{u} T₂}
    (hM : Module.Finite T₂ M) (hI : Indecomposable M) :
    upperTriangularARVertexEquiv k i = vertex k (M := M) hM hI ↔
      Nonempty ((a2VertexEquiv k Unit i).representative ≅ (e).functor.obj M) := by
  rw [← (bijective_upperTriangularRepVertex k).injective.eq_iff,
    upperTriangularRepVertex_vertexEquiv, upperTriangularRepVertex_of]
  conv_lhs => rw [← of_representative (a2VertexEquiv k Unit i)]
  exact of_eq_of_iff _ _ _ _

private theorem card_arrows_upperTriangularRepVertex
    (a b : IrreducibleMorphismQuiver k IsFiniteModule) :
    Nat.card (upperTriangularRepVertex k a ⟶ upperTriangularRepVertex k b) = Nat.card (a ⟶ b) := by
  rw [upperTriangularRepVertex, upperTriangularRepVertex, card_arrows_of, card_arrows]
  exact ((e).irreducibleMorphismSpaceEquiv k a.representative b.representative).finrank_eq.symm

/-- The complete valuation matrix for upper-triangular `2 × 2` matrices. The arrows `1 ⟶ 2`
and `2 ⟶ 0` carry valuation `(1, 1)`, and all other entries are empty. -/
@[simp↓]
theorem valuationMatrix_upperTriangularARVertexEquiv (i j : Fin 3) :
    valuationMatrix k IsFiniteModule
      (upperTriangularARVertexEquiv k i) (upperTriangularARVertexEquiv k j) =
      if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then some (1, 1) else none := by
  classical
  let a := upperTriangularARVertexEquiv k i
  let b := upperTriangularARVertexEquiv k j
  have h := card_arrows_upperTriangularRepVertex k a b
  rw [upperTriangularRepVertex_vertexEquiv, upperTriangularRepVertex_vertexEquiv,
    card_arrows_a2VertexEquiv, card_arrows] at h
  by_cases hij : (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0)
  · rw [ite_eq_left hij] at h ⊢
    apply valuationMatrix_eq_some_iff.mpr
    apply Prod.ext
    · rw [← finrank_residue_mul_irreducibleMorphismValuation_fst] at h
      exact Nat.eq_one_of_dvd_one (Dvd.intro_left _ h.symm)
    · rw [← finrank_residueOp_mul_irreducibleMorphismValuation_snd] at h
      exact Nat.eq_one_of_dvd_one (Dvd.intro_left _ h.symm)
  · rw [ite_eq_right hij] at h ⊢
    rw [← Option.not_isSome_iff_eq_none, isSome_valuationMatrix_iff,
      ← finrank_irreducibleMorphismSpace_pos_iff k, ← h]
    exact Nat.not_lt_zero _

private theorem projective_upperTriangularARVertexEquiv_iff (i : Fin 3) :
    Projective (upperTriangularARVertexEquiv k i).representative ↔ i ≠ 0 := by
  let a := upperTriangularARVertexEquiv k i
  rw [← (e).map_projective_iff]
  refine ((TauCeti.arTranslation k Q).translate_of_eq_none_iff (k := k)
    ((isFinDim_upperTriangularRep_iff k _).2 a.representative_property.1)
    ((e).indecomposable_functor_obj a.representative_property.2)).symm.trans ?_
  -- Express the image class via the vertex map so that the one-arrow formula applies.
  change (TauCeti.arTranslation k Q).translate (upperTriangularRepVertex k a) = none ↔ i ≠ 0
  rw [upperTriangularRepVertex_vertexEquiv, translate_a2VertexEquiv]
  by_cases hi : i = 0 <;> simp [hi]

local notation "translate" =>
  ModuleCat.arTranslation k T₂ k (length_quotient_linearMap_self_eq_one k)

private theorem translate_upperTriangularARVertexEquiv_zero :
    (translate).translate (upperTriangularARVertexEquiv k 0) =
      some (upperTriangularARVertexEquiv k 1) := by
  let a := upperTriangularARVertexEquiv k 0
  let b := upperTriangularARVertexEquiv k 1
  have hp : ¬ Projective a.representative := fun h ↦
    (projective_upperTriangularARVertexEquiv_iff k 0).mp h rfl
  suffices h : Nonempty
      ((translate).obj a.representative a.representative_property.1 ≅ b.representative) by
    have ht := ((translate).translate_of_eq_some_of_iff (k := k) a.representative_property.1
      a.representative_property.2 b.representative_property.1 b.representative_property.2).mpr
      ⟨hp, h⟩
    rwa [of_representative a, of_representative b] at ht
  rw [ModuleCat.arTranslation_obj]
  let S : ShortComplex (QuiverRep.{u, 0, 0, u} k Q) := kroneckerARSequence k Unit
  have h₀ : Nonempty ((e).functor.obj a.representative ≅ S.X₃) := by
    have h := upperTriangularRepVertex_vertexEquiv k 0
    rw [upperTriangularRepVertex, a2VertexEquiv_zero, of_eq_of_iff] at h
    simpa only [a, S, kroneckerARSequence_X₃] using h
  have h₁ : Nonempty ((e).functor.obj b.representative ≅ S.X₁) := by
    have h := upperTriangularRepVertex_vertexEquiv k 1
    rw [upperTriangularRepVertex, a2VertexEquiv_one, of_eq_of_iff] at h
    simpa only [b, S, kroneckerARSequence_X₁] using h
  obtain ⟨Y, f, g, hfg, _, hT⟩ := exists_isAlmostSplit_arTranslate k k
    (length_quotient_linearMap_self_eq_one k) a.representative a.representative_property.2 hp
  have hmap := ((ShortComplex.mk f g hfg).isAlmostSplit_map_iff (e).functor).mpr hT
  obtain ⟨j⟩ := hmap.nonempty_iso_X₁ (isAlmostSplit_kroneckerARSequence k Unit) h₀.some
  exact ⟨(e).functor.preimageIso (j ≪≫ h₁.some.symm)⟩

/-- The partial translation sends the source simple to the target simple and is undefined on
the two projective vertices. -/
@[simp↓]
theorem translate_upperTriangularARVertexEquiv (i : Fin 3) :
    (translate).translate (upperTriangularARVertexEquiv k i) =
      if i = 0 then some (upperTriangularARVertexEquiv k 1) else none := by
  by_cases hi : i = 0
  · subst i
    simpa only [ite_true] using translate_upperTriangularARVertexEquiv_zero k
  · rw [ite_eq_right hi, ARTranslation.translate_eq_none_iff]
    exact (projective_upperTriangularARVertexEquiv_iff k i).mpr hi

end TauCeti
