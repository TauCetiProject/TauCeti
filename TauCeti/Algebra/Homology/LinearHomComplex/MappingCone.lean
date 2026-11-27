/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearHomComplex.Basic
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Linear Hom complexes and mapping cones

The linear Hom complex into the mapping cone of a cochain map is naturally isomorphic to
the mapping cone of postcomposition by that map. The comparison uses Mathlib's inclusions
and projections, and hence its cochain signs. The component formulas retain the null
homotopies used in computations of mapping spaces in the differential graded nerve.

## References

* Joël Riou's `mappingCone.liftCochain`, `mappingCone.δ_liftCochain` and
  `mappingCone.ext_cochain_to_iff` in
  `Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean`.
-/

public section

noncomputable section

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace TauCeti

universe w v u

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {X Y : CochainComplex C ℤ} (f : X ⟶ Y) [HomologicalComplex.HasHomotopyCofiber f]
  (Z : CochainComplex C ℤ)

private def homConeEquiv (n : ℤ) :
    (mappingCone (linearHomComplexPostcomp R Z f)).X n ≃ₗ[R]
      Cochain Z (mappingCone f) n where
  toFun z := mappingCone.liftCochain f
    (((mappingCone.fst (linearHomComplexPostcomp R Z f)).val.v n (n + 1) rfl).hom z)
    (((mappingCone.snd (linearHomComplexPostcomp R Z f)).v n n (add_zero n)).hom z) rfl
  invFun z :=
    ((mappingCone.inl (linearHomComplexPostcomp R Z f)).v (n + 1) n (by omega)).hom
        (z.comp (mappingCone.fst f).val rfl) +
      ((mappingCone.inr (linearHomComplexPostcomp R Z f)).f n).hom
        (z.comp (mappingCone.snd f) (add_zero n))
  left_inv z := by
    simp only [mappingCone.liftCochain_fst, mappingCone.liftCochain_snd]
    have h := congrArg (fun g ↦ g.hom z)
      (mappingCone.id_X (linearHomComplexPostcomp R Z f) n (n + 1) rfl)
    simpa using h
  right_inv z := by
    apply (mappingCone.ext_cochain_to_iff f n (n + 1) rfl).2
    constructor <;>
      simp only [map_add, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
        mappingCone.inl_v_fst_v, mappingCone.inr_f_fst_v, mappingCone.inl_v_snd_v,
        mappingCone.inr_f_snd_v, ModuleCat.hom_id, ModuleCat.hom_zero,
        LinearMap.id_apply, LinearMap.zero_apply, add_zero, zero_add,
        mappingCone.liftCochain_fst, mappingCone.liftCochain_snd]
  map_add' z z' := by
    apply (mappingCone.ext_cochain_to_iff f n (n + 1) rfl).2
    constructor <;> simp only [mappingCone.liftCochain_fst, mappingCone.liftCochain_snd,
      Cochain.add_comp, map_add]
  map_smul' r z := by
    apply (mappingCone.ext_cochain_to_iff f n (n + 1) rfl).2
    constructor <;> simp only [mappingCone.liftCochain_fst, mappingCone.liftCochain_snd,
      Cochain.smul_comp, map_smul, RingHom.id_apply]

/-- The Hom complex into a mapping cone is the mapping cone of postcomposition. The direction
of this isomorphism assembles a pair of cochains using `mappingCone.liftCochain`. -/
def linearHomComplexMappingConeIso :
    mappingCone (linearHomComplexPostcomp R Z f) ≅ linearHomComplex R Z (mappingCone f) :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ (homConeEquiv R f Z n).toModuleIso) (by
    intro n m hnm
    obtain rfl : m = n + 1 := hnm.symm
    ext z
    dsimp only [LinearEquiv.toModuleIso, homConeEquiv]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ConcreteCategory.hom_ofHom,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [linearHomComplex_d_hom_apply, mappingCone.δ_liftCochain _ _ _ _ (n + 1 + 1) (by omega)]
    have hfst := congrArg (fun g ↦ g.hom z)
      (mappingCone.d_fst_v (linearHomComplexPostcomp R Z f) n (n + 1) (n + 1 + 1) rfl rfl)
    have hsnd := congrArg (fun g ↦ g.hom z)
      (mappingCone.d_snd_v (linearHomComplexPostcomp R Z f) n (n + 1) rfl)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_neg, LinearMap.neg_apply,
      ModuleCat.hom_add, LinearMap.add_apply] at hfst hsnd
    rw [hfst, hsnd, linearHomComplex_d_hom_apply R Z X,
      linearHomComplex_d_hom_apply R Z Y, linearHomComplexPostcomp_f_apply]
    apply (mappingCone.ext_cochain_to_iff f (n + 1) (n + 1 + 1) rfl).2
    constructor <;> simp [Cochain.add_comp, Cochain.neg_comp, add_comm])

/-- The comparison assembles the two components with the usual cone inclusions. -/
@[simp]
lemma linearHomComplexMappingConeIso_hom_f_apply (n : ℤ)
    (z : (mappingCone (linearHomComplexPostcomp R Z f)).X n) :
    (dsimp% only [linearHomComplex_X]
      ((linearHomComplexMappingConeIso R f Z).hom.f n).hom z) =
      mappingCone.liftCochain f
        (((mappingCone.fst (linearHomComplexPostcomp R Z f)).val.v n (n + 1) rfl).hom z)
        (((mappingCone.snd (linearHomComplexPostcomp R Z f)).v n n (add_zero n)).hom z) rfl :=
  (rfl)

/-- The inverse comparison extracts the two components with the usual cone projections. -/
@[simp]
lemma linearHomComplexMappingConeIso_inv_f_apply (n : ℤ)
    (z : Cochain Z (mappingCone f) n) :
    (dsimp% only [linearHomComplex_X]
      ((linearHomComplexMappingConeIso R f Z).inv.f n).hom z) =
      ((mappingCone.inl (linearHomComplexPostcomp R Z f)).v (n + 1) n (by omega)).hom
          (z.comp (mappingCone.fst f).val rfl) +
        ((mappingCone.inr (linearHomComplexPostcomp R Z f)).f n).hom
          (z.comp (mappingCone.snd f) (add_zero n)) :=
  (rfl)

/-- On the shifted source summand, the comparison is postcomposition with the degree `-1`
cone inclusion, the canonical null homotopy of `f` followed by the right inclusion. -/
lemma linearHomComplexMappingConeIso_hom_f_inl (n : ℤ) (a : Cochain Z X (n + 1)) :
    (dsimp% only [linearHomComplex_X]
      ((linearHomComplexMappingConeIso R f Z).hom.f n).hom
        (((mappingCone.inl (linearHomComplexPostcomp R Z f)).v (n + 1) n (by omega)).hom a)) =
      a.comp (mappingCone.inl f) (by omega) := by
  rw [linearHomComplexMappingConeIso_hom_f_apply]
  have hfst := congrArg (fun k ↦ k.hom a)
    (mappingCone.inl_v_fst_v (linearHomComplexPostcomp R Z f) (n + 1) n rfl)
  have hsnd := congrArg (fun k ↦ k.hom a)
    (mappingCone.inl_v_snd_v (linearHomComplexPostcomp R Z f) (n + 1) n (by omega))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] at hfst
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hsnd
  rw [hfst, hsnd]
  apply (mappingCone.ext_cochain_to_iff f n (n + 1) rfl).2
  constructor <;> simp

/-- On the target summand, the comparison is postcomposition with the cone inclusion. -/
@[reassoc (attr := simp)]
lemma linearHomComplexMappingConeIso_inr_hom :
    mappingCone.inr (linearHomComplexPostcomp R Z f) ≫
        (linearHomComplexMappingConeIso R f Z).hom =
      linearHomComplexPostcomp R Z (mappingCone.inr f) := by
  ext n (b : Cochain Z Y n)
  rw [HomologicalComplex.comp_f, ModuleCat.comp_apply,
    linearHomComplexMappingConeIso_hom_f_apply]
  simp only [← ModuleCat.comp_apply, mappingCone.inr_f_fst_v, mappingCone.inr_f_snd_v,
    ModuleCat.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
  rw [linearHomComplexPostcomp_f_apply]
  apply (mappingCone.ext_cochain_to_iff f n (n + 1) rfl).2
  constructor <;> simp

/-- Naturality of the comparison in the contravariant argument of the Hom complex. -/
@[reassoc]
lemma linearHomComplexMappingConeIso_hom_naturality {Z' : CochainComplex C ℤ} (a : Z' ⟶ Z) :
    mappingCone.map (linearHomComplexPostcomp R Z f) (linearHomComplexPostcomp R Z' f)
        (linearHomComplexPrecomp R a X) (linearHomComplexPrecomp R a Y)
        (linearHomComplexPrecomp_postcomp_comm R a f).symm ≫
      (linearHomComplexMappingConeIso R f Z').hom =
    (linearHomComplexMappingConeIso R f Z).hom ≫
      linearHomComplexPrecomp R a (mappingCone f) := by
  ext n : 1
  apply mappingCone.ext_from (linearHomComplexPostcomp R Z f) (n + 1) n rfl
  · ext (z : Cochain Z X (n + 1))
    simp only [HomologicalComplex.comp_f, ← Category.assoc, mappingCone.inl_v_map_f,
      ModuleCat.comp_apply]
    rw [linearHomComplexPrecomp_f_apply (R := R) a X, linearHomComplexPrecomp_f_apply,
      linearHomComplexMappingConeIso_hom_f_inl, linearHomComplexMappingConeIso_hom_f_inl]
    exact (Cochain.comp_assoc (n₁₂₃ := n) (Cochain.ofHom a) z (mappingCone.inl f)
      (zero_add (n + 1)) (show n + 1 + -1 = n by omega) (by omega))
  · simp only [HomologicalComplex.comp_f, ← Category.assoc, mappingCone.inr_f_map_f]
    rw [Category.assoc, ← HomologicalComplex.comp_f,
      linearHomComplexMappingConeIso_inr_hom]
    rw [← HomologicalComplex.comp_f (mappingCone.inr _) _,
      linearHomComplexMappingConeIso_inr_hom]
    exact HomologicalComplex.congr_hom
      (linearHomComplexPrecomp_postcomp_comm R a (mappingCone.inr f)) n

/-- Naturality in a commutative square of maps of complexes. -/
@[reassoc]
lemma linearHomComplexMappingConeIso_hom_naturality_mappingConeMap
    (f : X ⟶ Y) (Z : CochainComplex C ℤ) [HasBinaryBiproducts C]
    {X' Y' : CochainComplex C ℤ} (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    mappingCone.map (linearHomComplexPostcomp R Z f) (linearHomComplexPostcomp R Z g)
        (linearHomComplexPostcomp R Z a) (linearHomComplexPostcomp R Z b)
        (by rw [← linearHomComplexPostcomp_comp, ← linearHomComplexPostcomp_comp, h]) ≫
      (linearHomComplexMappingConeIso R g Z).hom =
    (linearHomComplexMappingConeIso R f Z).hom ≫
      linearHomComplexPostcomp R Z (mappingCone.map f g a b h) := by
  ext n : 1
  apply mappingCone.ext_from (linearHomComplexPostcomp R Z f) (n + 1) n rfl
  · ext (z : Cochain Z X (n + 1))
    simp only [HomologicalComplex.comp_f, ← Category.assoc, mappingCone.inl_v_map_f,
      ModuleCat.comp_apply]
    rw [linearHomComplexPostcomp_f_apply, linearHomComplexPostcomp_f_apply,
      linearHomComplexMappingConeIso_hom_f_inl, linearHomComplexMappingConeIso_hom_f_inl]
    apply Cochain.ext
    intro p q hpq
    simp only [Cochain.comp_v _ _ (show n + 1 + -1 = n by omega) p (p + (n + 1)) q
      rfl (by omega), Cochain.comp_zero_cochain_v,
      Cochain.ofHom_v, Category.assoc, mappingCone.inl_v_map_f]
  · simp only [HomologicalComplex.comp_f, ← Category.assoc, mappingCone.inr_f_map_f]
    rw [Category.assoc, ← HomologicalComplex.comp_f,
      linearHomComplexMappingConeIso_inr_hom]
    rw [← HomologicalComplex.comp_f (mappingCone.inr _) _,
      linearHomComplexMappingConeIso_inr_hom]
    simp only [← HomologicalComplex.comp_f, ← linearHomComplexPostcomp_comp]
    congr 2
    ext p
    exact (mappingCone.inr_f_map_f _ _ _ _ h p).symm

end TauCeti
