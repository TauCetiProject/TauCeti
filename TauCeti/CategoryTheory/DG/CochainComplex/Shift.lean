/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.ShiftClosure.CochainComplex
public import TauCeti.CategoryTheory.DG.NaturalTransformation
public import TauCeti.CategoryTheory.DG.CochainComplex.KInjective
public import TauCeti.AlgebraicTopology.DGNerve.FullSubcategory

/-!
# Differential graded shifts of cochain complexes

The cohomological shift by `a` acts on a degree-`p` cochain by
`(-1)^(a*p) • z.shift a`. The sign makes this action commute with the Hom differential;
in particular it negates degree-one cochains for an odd shift, while on cochain maps
it is the usual shift. This is the concrete realization of the shift on the formal
shift closure, evaluated by `DGShiftClosure.toCochainComplex`.

For the ambient category of complexes, the zero and addition comparisons use Mathlib's
ordinary cochain shift isomorphisms and satisfy the unit and associativity laws. They
are natural on homogeneous cochains of every degree. The shift functors induce maps
of native dg nerves.

For an abelian category the action restricts to K-injective complexes. On homotopy
categories it intertwines the canonical comparison with the ordinary derived shift.
No resolutions are required for that comparison; resolutions identify it with the
equivalence from the homotopy category of the native dg nerve.

The sign normalization follows Keller, *Deriving DG categories*, §1, and the existing
`DGShiftClosure.shiftCochainEquiv`. The underlying cochain operations and shift
isomorphisms are Mathlib's constructions of Joël Riou.
-/

public section

noncomputable section

open CategoryTheory CochainComplex.HomComplex

namespace TauCeti

universe w v u

variable (R : Type v) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

namespace CochainComplexDG

/-- The DG cohomological shift of cochain complexes. On degree-`p` cochains it is the
ordinary simultaneous shift multiplied by `(-1)^(a*p)`. -/
-- The object map must compute for the cast-free homogeneous cochain API.
abbrev shiftFunctor (a : ℤ) :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ)
      (CochainComplex C ℤ) (CochainComplex C ℤ) where
  obj K := K⟦a⟧
  __ := EnrichedFunctor.ofDGMap (fun K ↦ K⟦a⟧)
    (fun {K L} p ↦ (a * p).negOnePow • Cochain.shiftLinearMap R K L p a)
    (fun {K L} p z ↦ by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, dgDifferential_linearHomComplex,
        dgDifferential_linearHomComplex, Cochain.shiftLinearMap_apply,
        Cochain.shiftLinearMap_apply, δ_units_smul, Cochain.δ_shift, smul_smul,
        ← Int.negOnePow_add, mul_add, mul_one])
    (fun K ↦ by
      rw [LinearMap.smul_apply, mul_zero, Int.negOnePow_zero, one_smul,
        dgId_linearHomComplex, dgId_linearHomComplex, Cochain.shiftLinearMap_apply]
      rw [Cochain.shift_ofHom, CategoryTheory.Functor.map_id])
    (fun {K L M p q n} z w h ↦ by
      refine Cochain.ext _ _ fun i j hij ↦ ?_
      rw [LinearMap.smul_apply, Cochain.units_smul_v, Cochain.shiftLinearMap_apply,
        Cochain.shift_v', dgComp_v R z w h (i + a) (i + p + a) (j + a) (by omega) (by omega),
        dgComp_v R _ _ h i (i + p) j rfl (by omega)]
      rw [LinearMap.smul_apply, LinearMap.smul_apply, Cochain.units_smul_v,
        Cochain.units_smul_v, Cochain.shiftLinearMap_apply, Cochain.shiftLinearMap_apply,
        Cochain.shift_v', Cochain.shift_v']
      simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
      rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add]
      congr 1
      subst h
      congr 1; ring)

/-- The DG shift has the ordinary cochain shift as object map. -/
@[simp]
theorem shiftFunctor_obj (a : ℤ) (K : CochainComplex C ℤ) :
    (shiftFunctor R a).obj K = K⟦a⟧ := (rfl)

/-- The action of the DG shift on an arbitrary homogeneous cochain. -/
@[simp]
theorem dgMap_shiftFunctor (a : ℤ) {K L : CochainComplex C ℤ} {p : ℤ}
    (z : DGHom R p K L) :
    (shiftFunctor R a).dgMap p z = (a * p).negOnePow • (z : Cochain K L p).shift a :=
  (EnrichedFunctor.dgMap_apply _ z).trans rfl

/-- A cochain map shifts without a sign. -/
@[simp]
theorem dgMap_shiftFunctor_ofHom (a : ℤ) {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (shiftFunctor R a).dgMap 0 (Cochain.ofHom f) =
      Cochain.ofHom (F := K⟦a⟧) (G := L⟦a⟧) (f⟦a⟧') := by
  rw [dgMap_shiftFunctor, mul_zero, Int.negOnePow_zero, one_smul]
  exact Cochain.shift_ofHom f a

private theorem shiftZeroHom_naturality {K L : CochainComplex C ℤ} (p : ℤ)
    (z : DGHom R p K L) :
    dgComp R ((shiftFunctor (C := C) R 0).dgMap p z)
      (Cochain.ofHom ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app L))
        (add_zero p) =
      dgComp R
        (Cochain.ofHom ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K))
        ((EnrichedFunctor.id (CochainComplex (ModuleCat.{v} R) ℤ)
          (CochainComplex C ℤ)).dgMap p z) (zero_add p) := by
  -- Specify the concrete cochain endpoints: enriched identity objects are opaque to `rw`.
  rw [EnrichedFunctor.id_dgMap]
  change dgComp R ((shiftFunctor R 0).dgMap p z)
      (Cochain.ofHom ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app L)
        : Cochain (L⟦(0 : ℤ)⟧) L 0) (add_zero p) =
    dgComp R (Cochain.ofHom
      ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K)
        : Cochain (K⟦(0 : ℤ)⟧) K 0) z (zero_add p)
  refine Cochain.ext _ _ fun i j hij ↦ ?_
  rw [dgComp_v R _ _ (add_zero p) i j j hij (add_zero j),
    dgComp_v R _ _ (zero_add p) i i j (add_zero i) hij,
    dgMap_shiftFunctor, Cochain.units_smul_v, Cochain.shift_v',
    Cochain.ofHom_v, Cochain.ofHom_v]
  simp only [CochainComplex.shiftFunctor_obj_X', mul_zero, Int.negOnePow_zero,
    zero_mul, one_smul, CochainComplex.shiftFunctorZero_hom_app_f,
    HomologicalComplex.XIsoOfEq, eqToIso, Cochain.v]
  exact eqToHom_naturality (fun T : Triplet p ↦ z T)
    (show (⟨i + 0, j + 0, by omega⟩ : Triplet p) = ⟨i, j, hij⟩ from by
      simp only [add_zero])

/-- The concrete shift is formal translation followed by evaluation of formal shifts. -/
theorem shiftFunctor_eq (a : ℤ) :
    shiftFunctor (C := C) R a =
      ((DGShiftClosure.ι R).comp _ (DGShiftClosure.shiftFunctor R a)).comp _
        (DGShiftClosure.toCochainComplex R) := by
  let F := ((DGShiftClosure.ι (C := CochainComplex C ℤ) R).comp _
    (DGShiftClosure.shiftFunctor R a)).comp _ (DGShiftClosure.toCochainComplex R)
  have h (K L : CochainComplex C ℤ) : (shiftFunctor R (0 + a)).map K L = F.map K L := by
    ext p z
    -- Evaluate the enriched maps on homogeneous cochains before comparing their components.
    -- `F` is the composite whose object map is definitionally the concrete shifted complex.
    erw [← EnrichedFunctor.dgMap_apply, ← EnrichedFunctor.dgMap_apply,
      EnrichedFunctor.comp_dgMap, EnrichedFunctor.comp_dgMap,
      dgMap_shiftFunctor, DGShiftClosure.dgMap_toCochainComplex,
      DGShiftClosure.dgMap_shiftFunctor, DGShiftClosure.dgMap_ι]
    refine Cochain.ext _ _ fun i j hij ↦ ?_
    -- Formal-shift Hom identifications reduce to the concrete cochain family.
    erw [Cochain.units_smul_v, Cochain.shift_v', DGShiftClosure.shiftCochainEquiv_v,
      DGShiftClosure.dgHomEquiv_shiftHomEquiv, DGShiftClosure.dgHomEquiv_ιHomEquiv,
      castDeg_def, xIsoOfEq_hom_v, xIsoOfEq_hom_v]
    simp only [EnrichedFunctor.comp_obj, DGShiftClosure.ι_obj]
    -- The remaining equality computes the formal-shift object projections to 0 + a.
    -- Rewriting those projections separately would give an ill-typed dependent `Cochain.v` motive.
    rfl
  apply EnrichedFunctor.ext _ (fun K ↦ by simp [EnrichedFunctor.comp_obj])
  intro K L
  have heqMap {G H : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ)
      (CochainComplex C ℤ) (CochainComplex C ℤ)} (e : G = H) :
      G.map K L ≍ H.map K L := by subst H; rfl
  have hs := heqMap (congrArg (shiftFunctor (C := C) R) (zero_add a).symm)
  exact eq_of_heq ((comp_eqToHom_heq _ _).trans (hs.trans (heq_of_eq (h K L))))

/-- The DG transformation identifying shift by zero with the identity. -/
def shiftZeroHom : DGNatTrans (shiftFunctor (C := C) R 0) (EnrichedFunctor.id _ _) :=
  DGNatTrans.ofDGApp
    (fun K ↦ Cochain.ofHom (F := K⟦(0 : ℤ)⟧) (G := K)
      ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K))
    (fun _ ↦ (mem_dgCycles R).2
      ((dgDifferential_linearHomComplex R 0 _).trans (δ_ofHom _)))
    (fun p z ↦ shiftZeroHom_naturality R p z)

private theorem shiftZeroInv_naturality {K L : CochainComplex C ℤ} (p : ℤ)
    (z : DGHom R p K L) :
    dgComp R ((EnrichedFunctor.id (CochainComplex (ModuleCat.{v} R) ℤ)
          (CochainComplex C ℤ)).dgMap p z)
      (Cochain.ofHom ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app L))
        (add_zero p) =
      dgComp R
        (Cochain.ofHom ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app K))
        ((shiftFunctor (C := C) R 0).dgMap p z) (zero_add p) := by
  -- Specify the concrete cochain endpoints, as for the forward comparison.
  rw [EnrichedFunctor.id_dgMap]
  change dgComp R z
      (Cochain.ofHom ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app L)
        : Cochain L (L⟦(0 : ℤ)⟧) 0) (add_zero p) =
    dgComp R (Cochain.ofHom
      ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app K)
        : Cochain K (K⟦(0 : ℤ)⟧) 0) ((shiftFunctor R 0).dgMap p z) (zero_add p)
  refine Cochain.ext _ _ fun i j hij ↦ ?_
  rw [dgComp_v R _ _ (add_zero p) i j j hij (add_zero j),
    dgComp_v R _ _ (zero_add p) i i j (add_zero i) hij,
    dgMap_shiftFunctor, Cochain.units_smul_v, Cochain.shift_v',
    Cochain.ofHom_v, Cochain.ofHom_v]
  simp only [CochainComplex.shiftFunctor_obj_X', mul_zero, Int.negOnePow_zero,
    zero_mul, one_smul, CochainComplex.shiftFunctorZero_inv_app_f,
    HomologicalComplex.XIsoOfEq, eqToIso, Cochain.v]
  exact eqToHom_naturality (fun T : Triplet p ↦ z T)
    (show (⟨i, j, hij⟩ : Triplet p) = ⟨i + 0, j + 0, by omega⟩ from by
      simp only [add_zero])

/-- The DG transformation from the identity to shift by zero. -/
def shiftZeroInv : DGNatTrans
    (EnrichedFunctor.id (CochainComplex (ModuleCat.{v} R) ℤ) _) (shiftFunctor (C := C) R 0) :=
  DGNatTrans.ofDGApp
    (fun K ↦ Cochain.ofHom (F := K) (G := K⟦(0 : ℤ)⟧)
      ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app K))
    (fun _ ↦ (mem_dgCycles R).2
      ((dgDifferential_linearHomComplex R 0 _).trans (δ_ofHom _)))
    (fun p z ↦ shiftZeroInv_naturality R p z)

/-- The component of the zero-shift comparison is Mathlib's cochain shift comparison. -/
@[simp]
theorem dgApp_shiftZeroHom (K : CochainComplex C ℤ) :
    (shiftZeroHom (C := C) R).dgApp K =
      Cochain.ofHom (F := K⟦(0 : ℤ)⟧) (G := K)
        ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K) := by
  unfold shiftZeroHom
  exact DGNatTrans.dgApp_ofDGApp _ _ (fun p z ↦ shiftZeroHom_naturality R p z) K

/-- The inverse zero-shift comparison has the ordinary inverse component. -/
@[simp]
theorem dgApp_shiftZeroInv (K : CochainComplex C ℤ) :
    (shiftZeroInv (C := C) R).dgApp K =
      Cochain.ofHom (F := K) (G := K⟦(0 : ℤ)⟧)
        ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app K) := by
  unfold shiftZeroInv
  exact DGNatTrans.dgApp_ofDGApp _ _ (fun p z ↦ shiftZeroInv_naturality R p z) K

/-- Shift by zero is DG naturally isomorphic to the identity. -/
def shiftZeroIso : (⟨shiftFunctor (C := C) R 0⟩ : DGFunctor R _ _) ≅
    ⟨EnrichedFunctor.id _ _⟩ where
  hom := shiftZeroHom R
  inv := shiftZeroInv R
  hom_inv_id := by
    -- Categorical composition of DG transformations is their defined DG composition.
    change DGNatTrans.comp (shiftZeroHom R) (shiftZeroInv R) = DGNatTrans.id _
    apply DGNatTrans.ext_dgApp
    intro K
    rw [DGNatTrans.dgApp_comp, dgApp_shiftZeroHom, dgApp_shiftZeroInv, DGNatTrans.dgApp_id]
    let e := (CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).app K
    -- Normalize the endpoints of the enriched comparison to ordinary complexes.
    change dgCompZero R (X := K⟦(0 : ℤ)⟧) (Y := K) (Z := K⟦(0 : ℤ)⟧)
      (Cochain.ofHom e.hom) (Cochain.ofHom e.inv) = dgId R (K⟦(0 : ℤ)⟧)
    rw [dgCompZero_ofHom_ofHom, e.hom_inv_id,
      dgId_linearHomComplex]
  inv_hom_id := by
    -- The same identification applies to the other inverse law.
    change DGNatTrans.comp (shiftZeroInv R) (shiftZeroHom R) = DGNatTrans.id _
    apply DGNatTrans.ext_dgApp
    intro K
    rw [DGNatTrans.dgApp_comp, dgApp_shiftZeroInv, dgApp_shiftZeroHom, DGNatTrans.dgApp_id]
    let e := (CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).app K
    -- Normalize the endpoints of the enriched comparison to ordinary complexes.
    change dgCompZero R (X := K) (Y := K⟦(0 : ℤ)⟧) (Z := K)
      (Cochain.ofHom e.inv) (Cochain.ofHom e.hom) = dgId R K
    rw [dgCompZero_ofHom_ofHom, e.inv_hom_id, dgId_linearHomComplex]
    simp only [Functor.id_obj]

/-- The hom of the DG shift comparison is its specified transformation. -/
@[simp]
theorem shiftZeroIso_hom :
    (shiftZeroIso (C := C) R).hom = shiftZeroHom R := (rfl)

/-- The inv of the DG shift comparison is its specified transformation. -/
@[simp]
theorem shiftZeroIso_inv :
    (shiftZeroIso (C := C) R).inv = shiftZeroInv R := (rfl)

private theorem shiftAddHom_naturality (a b : ℤ) {K L : CochainComplex C ℤ}
    (p : ℤ) (z : DGHom R p K L) :
    dgComp R ((shiftFunctor R (a + b)).dgMap p z)
      (Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app L))
        (add_zero p) =
    dgComp R
      (Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app K))
      (((shiftFunctor R a).comp _ (shiftFunctor R b)).dgMap p z) (zero_add p) := by
  rw [EnrichedFunctor.comp_dgMap]
  -- Expose the ordinary cochain endpoints before using the component formulas.
  change dgComp R ((shiftFunctor R (a + b)).dgMap p z)
      (Cochain.ofHom
        ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app L)
          : Cochain (L⟦a + b⟧) (L⟦a⟧⟦b⟧) 0) (add_zero p) =
    dgComp R (Cochain.ofHom
      ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app K)
        : Cochain (K⟦a + b⟧) (K⟦a⟧⟦b⟧) 0)
      ((shiftFunctor R b).dgMap p ((shiftFunctor R a).dgMap p z)) (zero_add p)
  rw [dgMap_shiftFunctor, dgMap_shiftFunctor, dgMap_shiftFunctor]
  refine Cochain.ext _ _ fun i j hij ↦ ?_
  rw [dgComp_v R _ _ (add_zero p) i j j hij (add_zero j),
    dgComp_v R _ _ (zero_add p) i i j (add_zero i) hij]
  simp only [Cochain.units_smul_v, Cochain.shift_v',
    Cochain.ofHom_v, CochainComplex.shiftFunctorAdd_hom_app_f,
    HomologicalComplex.XIsoOfEq, eqToIso,
    mul_zero, zero_mul, Int.negOnePow_zero,
    Linear.units_smul_comp, Linear.comp_units_smul, Cochain.shift_units_smul,
    smul_smul, ← Int.negOnePow_add]
  rw [add_mul, add_comm (b * p)]
  congr 1
  exact eqToHom_naturality (fun T : Triplet p ↦ z T)
    (show (⟨i + (a + b), j + (a + b), by omega⟩ : Triplet p) =
      ⟨i + b + a, j + b + a, by omega⟩ from by
        congr 1 <;> omega)

/-- The DG comparison between a shift by a sum and the two successive shifts. -/
def shiftAddHom (a b : ℤ) : DGNatTrans (shiftFunctor (C := C) R (a + b))
    ((shiftFunctor R a).comp _ (shiftFunctor R b)) :=
  DGNatTrans.ofDGApp
    (fun K ↦ Cochain.ofHom
      ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app K))
    (fun _ ↦ (mem_dgCycles R).2
      ((dgDifferential_linearHomComplex R 0 _).trans (δ_ofHom _)))
    (fun p z ↦ shiftAddHom_naturality R a b p z)

private theorem shiftAddInv_naturality (a b : ℤ) {K L : CochainComplex C ℤ}
    (p : ℤ) (z : DGHom R p K L) :
    dgComp R (((shiftFunctor R a).comp _ (shiftFunctor R b)).dgMap p z)
      (Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app L))
        (add_zero p) =
    dgComp R
      (Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app K))
      ((shiftFunctor R (a + b)).dgMap p z) (zero_add p) := by
  rw [EnrichedFunctor.comp_dgMap]
  -- Use the concrete cochain endpoints of the successive shift.
  change dgComp R ((shiftFunctor R b).dgMap p ((shiftFunctor R a).dgMap p z))
      (Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app L)
        : Cochain (L⟦a⟧⟦b⟧) (L⟦a + b⟧) 0) (add_zero p) =
    dgComp R (Cochain.ofHom
      ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app K)
        : Cochain (K⟦a⟧⟦b⟧) (K⟦a + b⟧) 0)
      ((shiftFunctor R (a + b)).dgMap p z) (zero_add p)
  rw [dgMap_shiftFunctor, dgMap_shiftFunctor, dgMap_shiftFunctor]
  refine Cochain.ext _ _ fun i j hij ↦ ?_
  rw [dgComp_v R _ _ (add_zero p) i j j hij (add_zero j),
    dgComp_v R _ _ (zero_add p) i i j (add_zero i) hij]
  simp only [Cochain.units_smul_v, Cochain.shift_v', Cochain.ofHom_v,
    CochainComplex.shiftFunctorAdd_inv_app_f, HomologicalComplex.XIsoOfEq, eqToIso,
    mul_zero, zero_mul, Int.negOnePow_zero, Linear.units_smul_comp, Linear.comp_units_smul,
    Cochain.shift_units_smul, smul_smul, ← Int.negOnePow_add]
  rw [add_mul, add_comm (a * p)]
  congr 1
  exact eqToHom_naturality (fun T : Triplet p ↦ z T)
    (show (⟨i + b + a, j + b + a, by omega⟩ : Triplet p) =
      ⟨i + (a + b), j + (a + b), by omega⟩ from by congr 1 <;> omega)

/-- The inverse DG comparison from successive shifts to the shift by their sum. -/
def shiftAddInv (a b : ℤ) : DGNatTrans
    ((shiftFunctor (C := C) R a).comp _ (shiftFunctor R b)) (shiftFunctor R (a + b)) :=
  DGNatTrans.ofDGApp
    (fun K ↦ Cochain.ofHom
      ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app K))
    (fun _ ↦ (mem_dgCycles R).2
      ((dgDifferential_linearHomComplex R 0 _).trans (δ_ofHom _)))
    (fun p z ↦ shiftAddInv_naturality R a b p z)

/-- The forward DG addition comparison has the ordinary cochain comparison as component. -/
@[simp]
theorem dgApp_shiftAddHom (a b : ℤ) (K : CochainComplex C ℤ) :
    (shiftAddHom R a b).dgApp K =
      Cochain.ofHom (F := K⟦a + b⟧) (G := K⟦a⟧⟦b⟧)
        ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app K) := by
  unfold shiftAddHom
  exact DGNatTrans.dgApp_ofDGApp _ _ (fun p z ↦ shiftAddHom_naturality R a b p z) K

/-- The inverse DG addition comparison has the ordinary inverse as component. -/
@[simp]
theorem dgApp_shiftAddInv (a b : ℤ) (K : CochainComplex C ℤ) :
    (shiftAddInv R a b).dgApp K =
      Cochain.ofHom (F := K⟦a⟧⟦b⟧) (G := K⟦a + b⟧)
        ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app K) := by
  unfold shiftAddInv
  exact DGNatTrans.dgApp_ofDGApp _ _ (fun p z ↦ shiftAddInv_naturality R a b p z) K

/-- Shift by a sum is DG naturally isomorphic to the two successive shifts. -/
def shiftAddIso (a b : ℤ) : (⟨shiftFunctor (C := C) R (a + b)⟩ : DGFunctor R _ _) ≅
    ⟨(shiftFunctor R a).comp _ (shiftFunctor R b)⟩ where
  hom := shiftAddHom R a b
  inv := shiftAddInv R a b
  hom_inv_id := by
    -- Categorical composition is the defined DG composition.
    change DGNatTrans.comp (shiftAddHom R a b) (shiftAddInv R a b) = DGNatTrans.id _
    apply DGNatTrans.ext_dgApp
    intro K
    rw [DGNatTrans.dgApp_comp, dgApp_shiftAddHom, dgApp_shiftAddInv, DGNatTrans.dgApp_id]
    let e := (CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).app K
    -- Normalize the endpoints before computing the composite cochain.
    change dgCompZero R (X := K⟦a + b⟧) (Y := K⟦a⟧⟦b⟧) (Z := K⟦a + b⟧)
      (Cochain.ofHom e.hom) (Cochain.ofHom e.inv) = dgId R (K⟦a + b⟧)
    rw [dgCompZero_ofHom_ofHom, e.hom_inv_id,
      dgId_linearHomComplex]
  inv_hom_id := by
    -- Categorical composition is the defined DG composition.
    change DGNatTrans.comp (shiftAddInv R a b) (shiftAddHom R a b) = DGNatTrans.id _
    apply DGNatTrans.ext_dgApp
    intro K
    rw [DGNatTrans.dgApp_comp, dgApp_shiftAddInv, dgApp_shiftAddHom, DGNatTrans.dgApp_id]
    let e := (CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).app K
    -- Normalize the endpoints before computing the composite cochain.
    change dgCompZero R (X := K⟦a⟧⟦b⟧) (Y := K⟦a + b⟧) (Z := K⟦a⟧⟦b⟧)
      (Cochain.ofHom e.inv) (Cochain.ofHom e.hom) = dgId R (K⟦a⟧⟦b⟧)
    rw [dgCompZero_ofHom_ofHom, e.inv_hom_id, dgId_linearHomComplex]
    simp only [Functor.comp_obj]

/-- The hom of the DG shift comparison is its specified transformation. -/
@[simp]
theorem shiftAddIso_hom (a b : ℤ) :
    (shiftAddIso (C := C) R a b).hom = shiftAddHom R a b := (rfl)

/-- The inv of the DG shift comparison is its specified transformation. -/
@[simp]
theorem shiftAddIso_inv (a b : ℤ) :
    (shiftAddIso (C := C) R a b).inv = shiftAddInv R a b := (rfl)

/-- Associativity of DG shift addition, with Mathlib's transport between the two sums. -/
theorem dgApp_shiftAddHom_assoc (a b c : ℤ) (K : CochainComplex C ℤ) :
    dgCompZero R ((shiftAddHom R (a + b) c).dgApp K)
        ((shiftFunctor R c).dgMap 0 ((shiftAddHom R a b).dgApp K)) =
      dgCompZero R
        (Cochain.ofHom ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ)
          a (b + c) (a + b + c) (add_assoc a b c).symm).hom.app K))
        ((shiftAddHom R b c).dgApp (K⟦a⟧)) := by
  -- Composite enriched objects reduce to successive ordinary shifts in the cochain endpoints.
  erw [dgApp_shiftAddHom, dgApp_shiftAddHom, dgApp_shiftAddHom, dgMap_shiftFunctor_ofHom]
  -- Use concrete complexes to make the component compositions independent of enriched wrappers.
  change dgCompZero R (X := K⟦a + b + c⟧) (Y := K⟦a + b⟧⟦c⟧)
      (Z := K⟦a⟧⟦b⟧⟦c⟧)
      (Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) (a + b) c).hom.app K))
      (Cochain.ofHom (((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app K)⟦c⟧')) =
    dgCompZero R (X := K⟦a + b + c⟧) (Y := K⟦a⟧⟦b + c⟧) (Z := K⟦a⟧⟦b⟧⟦c⟧) _ _
  simp only [dgCompZero_ofHom_ofHom]
  exact congrArg Cochain.ofHom
    (CategoryTheory.shiftFunctorAdd_assoc_hom_app a b c K)

/-- The left unit law for DG shift addition. -/
theorem dgApp_shiftAddHom_zero_add (a : ℤ) (K : CochainComplex C ℤ) :
    (shiftAddHom R 0 a).dgApp K =
      dgCompZero R
        (Cochain.ofHom (eqToHom (congrArg (fun n : ℤ ↦ K⟦n⟧) (zero_add a))))
        ((shiftFunctor R a).dgMap 0 ((shiftZeroInv R).dgApp K)) := by
  -- The identity enriched functor's object reduces to the original complex.
  erw [dgApp_shiftAddHom, dgApp_shiftZeroInv, dgMap_shiftFunctor_ofHom]
  -- The source of the unit comparison is shifted by 0 + a.
  change Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) 0 a).hom.app K) =
    dgCompZero R (X := K⟦0 + a⟧) (Y := K⟦a⟧) (Z := K⟦(0 : ℤ)⟧⟦a⟧) _ _
  -- The equality transport and the shifted enriched endpoints are definitionally equal.
  erw [dgCompZero_ofHom_ofHom]
  exact congrArg Cochain.ofHom
    (CategoryTheory.shiftFunctorAdd_zero_add_hom_app a K)

/-- The right unit law for DG shift addition. -/
theorem dgApp_shiftAddHom_add_zero (a : ℤ) (K : CochainComplex C ℤ) :
    (shiftAddHom R a 0).dgApp K =
      dgCompZero R
        (Cochain.ofHom (eqToHom (congrArg (fun n : ℤ ↦ K⟦n⟧) (add_zero a))))
        ((shiftZeroInv R).dgApp (K⟦a⟧)) := by
  rw [dgApp_shiftAddHom, dgApp_shiftZeroInv]
  -- The source of the unit comparison is shifted by a + 0.
  change Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a 0).hom.app K) =
    dgCompZero R (X := K⟦a + 0⟧) (Y := K⟦a⟧) (Z := K⟦a⟧⟦(0 : ℤ)⟧) _ _
  simp only [dgCompZero_ofHom_ofHom]
  exact congrArg Cochain.ofHom
    (CategoryTheory.shiftFunctorAdd_add_zero_hom_app a K)

/-- On a native dg simplex, shift every object and apply the signed shift to each coherence. -/
theorem shiftFunctor_mapDGNerveSimplex_coh (a : ℤ) {n : ℕ}
    (x : DGNerve.Simplex R (CochainComplex C ℤ) n) (i j : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (d : ℤ) (hij : i ≤ j) (hS : S ⊆ Finset.Ioo i j)
    (hd : d + S.card = 0) :
    ((shiftFunctor R a).mapDGNerveSimplex x).coh i j S d hij hS hd =
      (a * d).negOnePow •
        (x.coh i j S d hij hS hd : Cochain (x.obj i) (x.obj j) d).shift a :=
  ((shiftFunctor R a).mapDGNerveSimplex_coh x i j S d hij hS hd).trans
    (dgMap_shiftFunctor R a _)

end CochainComplexDG

namespace KInjectiveDGCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]

/-- The cohomological DG shift of K-injective complexes, with the ambient signed action
on every Hom complex. -/
-- Restriction retains the computable object map needed by the homogeneous cochain formulas.
abbrev shiftFunctor (a : ℤ) :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ)
      (KInjectiveDGCategory A) (KInjectiveDGCategory A) :=
  DGFullSubcategory.restrict R (CochainComplexDG.shiftFunctor R a)
    (fun K h ↦ (CochainComplex.isKInjective_shift_iff K a).2 h)

/-- The underlying complex of the shifted K-injective object is the ordinary cochain shift. -/
theorem shiftFunctor_obj_obj (a : ℤ) (K : KInjectiveDGCategory A) :
    ((shiftFunctor R a).obj K).obj = K.obj⟦a⟧ := (rfl)

/-- Restriction to K-injectives retains the signed action on arbitrary homogeneous cochains. -/
theorem dgMap_shiftFunctor (a : ℤ) {K L : KInjectiveDGCategory A} {p : ℤ}
    (z : DGHom R p K L) :
    (shiftFunctor R a).dgMap p z =
      (a * p).negOnePow • (z : Cochain K.obj L.obj p).shift a := by
  rw [DGFullSubcategory.restrict_dgMap, CochainComplexDG.dgMap_shiftFunctor]

/-- A cochain map between K-injective complexes shifts without a sign. -/
theorem dgMap_shiftFunctor_ofHom (a : ℤ) {K L : KInjectiveDGCategory A}
    (f : K.obj ⟶ L.obj) :
    (shiftFunctor R a).dgMap 0 (Cochain.ofHom f) =
      Cochain.ofHom (F := K.obj⟦a⟧) (G := L.obj⟦a⟧) (f⟦a⟧') := by
  rw [dgMap_shiftFunctor]
  exact (CochainComplexDG.dgMap_shiftFunctor R a (Cochain.ofHom f)).symm.trans
    (CochainComplexDG.dgMap_shiftFunctor_ofHom R a f)

/-- The K-injective shift is the restriction of the ambient DG shift. -/
theorem shiftFunctor_comp_inclusion (a : ℤ) :
    (shiftFunctor (A := A) R a).comp _ (DGFullSubcategory.inclusion (R := R)) =
      (DGFullSubcategory.inclusion (R := R)).comp _ (CochainComplexDG.shiftFunctor R a) :=
  DGFullSubcategory.restrict_comp_inclusion R _ _

/-- The induced native dg-nerve shift agrees with the ambient shift after inclusion. -/
theorem shiftFunctor_mapDGNerve_comp_inclusion (a : ℤ) :
    (shiftFunctor (A := A) R a).mapDGNerve ≫
        (DGFullSubcategory.inclusion (R := R)).mapDGNerve =
      (DGFullSubcategory.inclusion (R := R)).mapDGNerve ≫
        (CochainComplexDG.shiftFunctor R a).mapDGNerve :=
  DGFullSubcategory.restrict_mapDGNerve_comp_inclusion _ _

variable [HasDerivedCategory.{w} A]

/-- On degree-zero homology, the DG shift of K-injective complexes is the ordinary
cohomological shift in the derived category. -/
def toDerivedCategoryShiftIso (a : ℤ) :
    (shiftFunctor (A := A) R a).mapDGHomotopyCategory ⋙ toDerivedCategory R A ≅
      toDerivedCategory R A ⋙ CategoryTheory.shiftFunctor (DerivedCategory A) a :=
  NatIso.ofComponents
    (fun X ↦ (((HomotopyCategory.quotient A (ComplexShape.up ℤ)) ⋙
      DerivedCategory.Qh).commShiftIso a).app (DGHomotopyCategory.underlying R X).obj)
    (fun {X Y} f ↦ by
      obtain ⟨K, rfl⟩ := DGHomotopyCategory.of_surjective R X
      obtain ⟨L, rfl⟩ := DGHomotopyCategory.of_surjective R Y
      have : K.obj.IsKInjective := K.property
      have : L.obj.IsKInjective := L.property
      obtain ⟨z, hz, rfl⟩ := DGHomotopyCategory.exists_homOf_eq R f
      have hz' : z ∈ dgCycles R K.obj L.obj :=
        (mem_dgCycles R).2 ((DGFullSubcategory.dgDifferential_eq R 0 z).symm.trans
          ((mem_dgCycles R).1 hz))
      obtain ⟨g, hg⟩ := (cochainHomLinearEquivDGCycles R K.obj L.obj).surjective ⟨z, hz'⟩
      have hg' : Cochain.ofHom g = (z : Cochain K.obj L.obj 0) :=
        (cochainHomLinearEquivDGCycles_apply_coe R g).symm.trans (congrArg Subtype.val hg)
      subst z
      have hmap : (shiftFunctor R a).mapDGHomotopyCategory.map
          (DGHomotopyCategory.homOf R (Cochain.ofHom g) hz) =
        DGHomotopyCategory.homOf R (Cochain.ofHom (g⟦a⟧'))
          (ofHom_mem_dgCycles R A (g⟦a⟧')) := by
        rw [EnrichedFunctor.mapDGHomotopyCategory_map_homOf]
        congr 1
        exact dgMap_shiftFunctor_ofHom R a g
      -- The shifted full-subcategory object has the same complex and proof as the canonical lift.
      erw [Functor.comp_map, hmap, toDerivedCategory_map_homOf]
      simp only [Functor.comp_map]
      -- `underlying (of K)` reduces to K in the homotopy-class representative.
      erw [toDerivedCategory_map_homOf]
      exact (((HomotopyCategory.quotient A (ComplexShape.up ℤ)) ⋙
        DerivedCategory.Qh).commShiftIso a).hom.naturality g)

/-- The hom component of the derived comparison is Mathlib's ordinary shift comparison. -/
@[simp]
theorem toDerivedCategoryShiftIso_hom_app (a : ℤ)
    (X : DGHomotopyCategory R (KInjectiveDGCategory A)) :
    (toDerivedCategoryShiftIso R a).hom.app X =
      (((HomotopyCategory.quotient A (ComplexShape.up ℤ)) ⋙
        DerivedCategory.Qh).commShiftIso a).hom.app
          (DGHomotopyCategory.underlying R X).obj := (rfl)

/-- The inv component of the derived comparison is Mathlib's ordinary shift comparison. -/
@[simp]
theorem toDerivedCategoryShiftIso_inv_app (a : ℤ)
    (X : DGHomotopyCategory R (KInjectiveDGCategory A)) :
    (toDerivedCategoryShiftIso R a).inv.app X =
      (((HomotopyCategory.quotient A (ComplexShape.up ℤ)) ⋙
        DerivedCategory.Qh).commShiftIso a).inv.app
          (DGHomotopyCategory.underlying R X).obj := (rfl)

/-- The shift on the native dg nerve of K-injectives corresponds to the derived shift
under the canonical equivalence of homotopy categories. -/
def dgNerveHomotopyCategoryEquivShiftIso [HasKInjectiveResolutions A] (a : ℤ) :
    SSet.mapHomotopyCategory (shiftFunctor (A := A) R a).mapDGNerve ⋙
        (dgNerveHomotopyCategoryEquiv R A).functor ≅
      (dgNerveHomotopyCategoryEquiv R A).functor ⋙
        CategoryTheory.shiftFunctor (DerivedCategory A) a :=
  Functor.isoWhiskerLeft _ (eqToIso (dgNerveHomotopyCategoryEquiv_functor R A)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso ((shiftFunctor R a).mapDGNerve_comp_fromHomotopyCategory)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (dgNerve.fromHomotopyCategory R (KInjectiveDGCategory A))
      (toDerivedCategoryShiftIso R a) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (dgNerveHomotopyCategoryEquiv_functor R A)).symm _

/-- The native homotopy-category comparison is the degree-zero comparison, transported
along the canonical equivalence and the naturality of the dg-nerve comparison. -/
@[simp]
theorem dgNerveHomotopyCategoryEquivShiftIso_hom_app [HasKInjectiveResolutions A] (a : ℤ)
    (X : (dgNerve R (KInjectiveDGCategory A)).HomotopyCategory) :
    (dgNerveHomotopyCategoryEquivShiftIso R a).hom.app X =
      eqToHom (Functor.congr_obj (dgNerveHomotopyCategoryEquiv_functor R A)
        ((SSet.mapHomotopyCategory (shiftFunctor R a).mapDGNerve).obj X)) ≫
      (toDerivedCategory R A).map (eqToHom (Functor.congr_obj
        ((shiftFunctor R a).mapDGNerve_comp_fromHomotopyCategory) X)) ≫
      (toDerivedCategoryShiftIso R a).hom.app
        ((dgNerve.fromHomotopyCategory R (KInjectiveDGCategory A)).obj X) ≫
      (CategoryTheory.shiftFunctor (DerivedCategory A) a).map
        (eqToHom (Functor.congr_obj (dgNerveHomotopyCategoryEquiv_functor R A).symm X)) := by
  simp [dgNerveHomotopyCategoryEquivShiftIso]

end KInjectiveDGCategory

end TauCeti
