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
theorem shiftFunctor_eq_comp_toCochainComplex (a : ℤ) :
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
  have hs := congr_arg_heq (fun G : EnrichedFunctor
      (CochainComplex (ModuleCat.{v} R) ℤ) (CochainComplex C ℤ) (CochainComplex C ℤ) ↦
        G.map K L) (congrArg (shiftFunctor (C := C) R) (zero_add a).symm)
  exact eq_of_heq ((comp_eqToHom_heq _ _).trans (hs.trans (heq_of_eq (h K L))))

/-- Shift by zero is DG naturally isomorphic to the identity. -/
def shiftZeroIso : (⟨shiftFunctor (C := C) R 0⟩ : DGFunctor R _ _) ≅
    ⟨EnrichedFunctor.id _ _⟩ :=
  DGFunctor.isoOfComponents
    (fun K ↦ (cochainComplexToDGClosed R C).mapIso
      ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).app K))
    (fun p z ↦ by
      dsimp only [Functor.mapIso_hom, Iso.app_hom]
      -- The closed-category object wrappers reduce to the shifted cochain endpoints.
      erw [dgClosedHom_cochainComplexToDGClosed_map, dgClosedHom_cochainComplexToDGClosed_map]
      simp only [cochainHomLinearEquivDGCycles_apply_coe]
      exact shiftZeroHom_naturality R p z)

/-- The component of the zero-shift comparison is Mathlib's cochain shift comparison. -/
@[simp]
theorem dgApp_shiftZeroIso_hom (K : CochainComplex C ℤ) :
    (shiftZeroIso (C := C) R).hom.dgApp K =
      Cochain.ofHom (F := K⟦(0 : ℤ)⟧) (G := K)
        ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K) := by
  unfold shiftZeroIso
  generalize_proofs
  -- The DGFunctor projections reduce to the concrete cochain functors at the endpoints.
  erw [DGFunctor.dgApp_isoOfComponents_hom]
  · dsimp only [Functor.mapIso_hom, Iso.app_hom]
    -- Identify the ordinary closed-category object with its underlying cochain complex.
    erw [dgClosedHom_cochainComplexToDGClosed_map]
    exact cochainHomLinearEquivDGCycles_apply_coe R _
  · assumption

/-- The inverse zero-shift comparison has the ordinary inverse component. -/
@[simp]
theorem dgApp_shiftZeroIso_inv (K : CochainComplex C ℤ) :
    (shiftZeroIso (C := C) R).inv.dgApp K =
      Cochain.ofHom (F := K) (G := K⟦(0 : ℤ)⟧)
        ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app K) := by
  unfold shiftZeroIso
  generalize_proofs
  -- The DGFunctor projections reduce to the concrete cochain functors at the endpoints.
  erw [DGFunctor.dgApp_isoOfComponents_inv]
  · dsimp only [Functor.mapIso_inv, Iso.app_inv]
    -- Identify the ordinary closed-category object with its underlying cochain complex.
    erw [dgClosedHom_cochainComplexToDGClosed_map]
    exact cochainHomLinearEquivDGCycles_apply_coe R _
  · assumption

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

/-- Shift by a sum is DG naturally isomorphic to the two successive shifts. -/
def shiftAddIso (a b : ℤ) : (⟨shiftFunctor (C := C) R (a + b)⟩ : DGFunctor R _ _) ≅
    ⟨(shiftFunctor R a).comp _ (shiftFunctor R b)⟩ :=
  DGFunctor.isoOfComponents
    (fun K ↦ (cochainComplexToDGClosed R C).mapIso
      ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).app K))
    (fun p z ↦ by
      dsimp only [Functor.mapIso_hom, Iso.app_hom]
      -- The closed-category object wrappers reduce to the shifted cochain endpoints.
      erw [dgClosedHom_cochainComplexToDGClosed_map, dgClosedHom_cochainComplexToDGClosed_map]
      simp only [cochainHomLinearEquivDGCycles_apply_coe]
      exact shiftAddHom_naturality R a b p z)

/-- The forward DG addition comparison has the ordinary cochain comparison as component. -/
@[simp]
theorem dgApp_shiftAddIso_hom (a b : ℤ) (K : CochainComplex C ℤ) :
    (shiftAddIso (C := C) R a b).hom.dgApp K =
      Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app K) := by
  unfold shiftAddIso
  generalize_proofs
  -- The DGFunctor projections reduce to the concrete cochain functors at the endpoints.
  erw [DGFunctor.dgApp_isoOfComponents_hom]
  · dsimp only [Functor.mapIso_hom, Iso.app_hom]
    -- Identify the ordinary closed-category object with its underlying cochain complex.
    erw [dgClosedHom_cochainComplexToDGClosed_map]
    exact cochainHomLinearEquivDGCycles_apply_coe R _
  · assumption

/-- The inverse DG addition comparison has the ordinary inverse cochain comparison as component. -/
@[simp]
theorem dgApp_shiftAddIso_inv (a b : ℤ) (K : CochainComplex C ℤ) :
    (shiftAddIso (C := C) R a b).inv.dgApp K =
      Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app K) := by
  unfold shiftAddIso
  generalize_proofs
  -- The DGFunctor projections reduce to the concrete cochain functors at the endpoints.
  erw [DGFunctor.dgApp_isoOfComponents_inv]
  · dsimp only [Functor.mapIso_inv, Iso.app_inv]
    -- Identify the ordinary closed-category object with its underlying cochain complex.
    erw [dgClosedHom_cochainComplexToDGClosed_map]
    exact cochainHomLinearEquivDGCycles_apply_coe R _
  · assumption

/-- Associativity of DG shift addition, with Mathlib's transport between the two sums. -/
theorem dgApp_shiftAddIso_hom_assoc (a b c : ℤ) (K : CochainComplex C ℤ) :
    dgCompZero R ((shiftAddIso R (a + b) c).hom.dgApp K)
        ((shiftFunctor R c).dgMap 0 ((shiftAddIso R a b).hom.dgApp K)) =
      dgCompZero R
        (Cochain.ofHom ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ)
          a (b + c) (a + b + c) (add_assoc a b c).symm).hom.app K))
        ((shiftAddIso R b c).hom.dgApp (K⟦a⟧)) := by
  -- Composite enriched objects reduce to successive ordinary shifts in the cochain endpoints.
  erw [dgApp_shiftAddIso_hom, dgApp_shiftAddIso_hom, dgApp_shiftAddIso_hom,
    dgMap_shiftFunctor_ofHom]
  -- Use concrete complexes to make the component compositions independent of enriched wrappers.
  change dgCompZero R (X := K⟦a + b + c⟧) (Y := K⟦a + b⟧⟦c⟧)
      (Z := K⟦a⟧⟦b⟧⟦c⟧)
      (Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) (a + b) c).hom.app K))
      (Cochain.ofHom (((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app K)⟦c⟧')) =
    dgCompZero R (X := K⟦a + b + c⟧) (Y := K⟦a⟧⟦b + c⟧) (Z := K⟦a⟧⟦b⟧⟦c⟧) _ _
  simp only [dgCompZero_ofHom]
  exact congrArg Cochain.ofHom
    (CategoryTheory.shiftFunctorAdd_assoc_hom_app a b c K)

/-- The left unit law for DG shift addition. -/
theorem dgApp_shiftAddIso_hom_zero_add (a : ℤ) (K : CochainComplex C ℤ) :
    (shiftAddIso R 0 a).hom.dgApp K =
      dgCompZero R
        (Cochain.ofHom (eqToHom (congrArg (fun n : ℤ ↦ K⟦n⟧) (zero_add a))))
        ((shiftFunctor R a).dgMap 0 ((shiftZeroIso R).inv.dgApp K)) := by
  -- The identity enriched functor's object reduces to the original complex.
  erw [dgApp_shiftAddIso_hom, dgApp_shiftZeroIso_inv, dgMap_shiftFunctor_ofHom]
  -- The source of the unit comparison is shifted by 0 + a.
  change Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) 0 a).hom.app K) =
    dgCompZero R (X := K⟦0 + a⟧) (Y := K⟦a⟧) (Z := K⟦(0 : ℤ)⟧⟦a⟧) _ _
  -- The equality transport and the shifted enriched endpoints are definitionally equal.
  erw [dgCompZero_ofHom]
  exact congrArg Cochain.ofHom
    (CategoryTheory.shiftFunctorAdd_zero_add_hom_app a K)

/-- The right unit law for DG shift addition. -/
theorem dgApp_shiftAddIso_hom_add_zero (a : ℤ) (K : CochainComplex C ℤ) :
    (shiftAddIso R a 0).hom.dgApp K =
      dgCompZero R
        (Cochain.ofHom (eqToHom (congrArg (fun n : ℤ ↦ K⟦n⟧) (add_zero a))))
        ((shiftZeroIso R).inv.dgApp (K⟦a⟧)) := by
  rw [dgApp_shiftAddIso_hom, dgApp_shiftZeroIso_inv]
  -- The source of the unit comparison is shifted by a + 0.
  change Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a 0).hom.app K) =
    dgCompZero R (X := K⟦a + 0⟧) (Y := K⟦a⟧) (Z := K⟦a⟧⟦(0 : ℤ)⟧) _ _
  simp only [dgCompZero_ofHom]
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
        rw [DGFullSubcategory.restrict_dgMap, CochainComplexDG.dgMap_shiftFunctor_ofHom]
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

/-- The inverse native comparison reverses the canonical transports and the derived comparison. -/
@[simp]
theorem dgNerveHomotopyCategoryEquivShiftIso_inv_app [HasKInjectiveResolutions A] (a : ℤ)
    (X : (dgNerve R (KInjectiveDGCategory A)).HomotopyCategory) :
    (dgNerveHomotopyCategoryEquivShiftIso R a).inv.app X =
      (CategoryTheory.shiftFunctor (DerivedCategory A) a).map
        (eqToHom (Functor.congr_obj (dgNerveHomotopyCategoryEquiv_functor R A) X)) ≫
      (toDerivedCategoryShiftIso R a).inv.app
        ((dgNerve.fromHomotopyCategory R (KInjectiveDGCategory A)).obj X) ≫
      (toDerivedCategory R A).map (eqToHom (Functor.congr_obj
        ((shiftFunctor R a).mapDGNerve_comp_fromHomotopyCategory).symm X)) ≫
      eqToHom (Functor.congr_obj (dgNerveHomotopyCategoryEquiv_functor R A).symm
        ((SSet.mapHomotopyCategory (shiftFunctor R a).mapDGNerve).obj X)) := by
  simp [dgNerveHomotopyCategoryEquivShiftIso]

end KInjectiveDGCategory

end TauCeti
