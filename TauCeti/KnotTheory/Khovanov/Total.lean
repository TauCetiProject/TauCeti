/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Computational
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Forgetting the quantum grading of the Khovanov complex

The ordinary complex is the native `GradedObject.total` of the quantum components.
Its degreewise enhanced-state coordinates have no quantum constraint: each enhanced state
belongs to exactly one quantum component. `quantumComplexDirectSumIso` identifies the ordinary
coefficient-vector complex with this total as actual cochain complexes, retaining the signed
saddle differential. In particular, maps, homotopies and homology can be transported along it
using the native homological-complex API.

The construction uses categorical coproducts, not products over quantum degrees, so its terms
remain finitely supported even without choosing a bound on quantum support.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §§2–3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.2.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n)

/-- Enhanced states in a fixed cochain degree, with the quantum grading forgotten. -/
abbrev TotalEnhancedStateAt (i : ℤ) :=
  {e : D.toPDCode.EnhancedState // D.stateCochainDegree e.1 = i}

/-- Every enhanced state in cochain degree `i` lies in exactly one quantum component. -/
def totalEnhancedStateAtEquiv (i : ℤ) :
    (Σ j : ℤ, D.EnhancedStateAt i j) ≃ D.TotalEnhancedStateAt i :=
  (Equiv.sigmaCongrRight fun j ↦ (D.enhancedStateAtEquiv i j).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun e ↦ D.stateCochainDegree e.1 = i)
      (fun e ↦ D.enhancedQuantumDegree e = j)).symm).trans
    (Equiv.sigmaFiberEquiv fun e : D.TotalEnhancedStateAt i ↦ D.enhancedQuantumDegree e.1)

/-- Forgetting the quantum index retains the underlying native enhanced state. -/
@[simp]
theorem totalEnhancedStateAtEquiv_apply_val (i j : ℤ) (e : D.EnhancedStateAt i j) :
    (D.totalEnhancedStateAtEquiv i ⟨j, e⟩).1 = e.toEnhancedState D := by
  exact D.enhancedStateAtEquiv_apply_val e

/-- The inverse recovers the intrinsic quantum degree of an enhanced state. -/
@[simp]
theorem totalEnhancedStateAtEquiv_symm_fst (i : ℤ) (e : D.TotalEnhancedStateAt i) :
    ((D.totalEnhancedStateAtEquiv i).symm e).1 = D.enhancedQuantumDegree e.1 := (rfl)

variable (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R]

/-- The ordinary Khovanov complex, obtained by taking the coproduct of the quantum components. -/
abbrev khovanovTotalComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  ∐ D.khovanovComplex hD R

/-- The ordinary complex is the native quantum total, not a product completion. -/
theorem khovanovTotalComplex_def :
    D.khovanovTotalComplex hD R =
      (GradedObject.total ℤ (CochainComplex (ModuleCat.{u} R) ℤ)).obj
        (D.khovanovComplex hD R) := by
  simp only [GradedObject.total, khovanovTotalComplex]

/-- Enhanced-state coordinates identify an ordinary term with finite coefficient vectors. -/
def quantumComplexDirectSumXIso (i : ℤ) :
    (D.khovanovTotalComplex hD R).X i ≅ ModuleCat.of R (D.TotalEnhancedStateAt i →₀ R) :=
  PreservesCoproduct.iso (eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i)
      (D.khovanovComplex hD R) ≪≫
    ModuleCat.coprodIsoDirectSum (fun j ↦ (D.khovanovComplex hD R j).X i) ≪≫
    ((DFinsupp.basis fun j ↦ D.khovanovEnhancedBasis hD R j i).repr.trans
      (Finsupp.lcongr (D.totalEnhancedStateAtEquiv i) (LinearEquiv.refl R R))).toModuleIso

/-- Including a homogeneous enhanced-state basis vector gives the corresponding ordinary
coefficient vector, with no extra quantum sign. -/
-- Apply before the circle-basis simp lemma expands the homogeneous basis vector.
@[simp↓]
theorem quantumComplexDirectSumXIso_hom_ι_basis (i j : ℤ) (e : D.EnhancedStateAt i j) :
    (D.quantumComplexDirectSumXIso hD R i).hom.hom
      (((Sigma.ι (D.khovanovComplex hD R) j).f i).hom
        (D.khovanovEnhancedBasis hD R j i e)) =
        Finsupp.single (D.totalEnhancedStateAtEquiv i ⟨j, e⟩) 1 := by
  classical
  have hι : (Sigma.ι (D.khovanovComplex hD R) j).f i ≫
      (PreservesCoproduct.iso (eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i)
        (D.khovanovComplex hD R)).hom =
      Sigma.ι (fun j ↦ (D.khovanovComplex hD R j).X i) j := by
    simpa only [← PreservesCoproduct.inv_hom, IsIso.Iso.inv_inv, eval_obj, eval_map] using
      map_ι_comp_inv_sigmaComparison
        (eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i) (D.khovanovComplex hD R) j
  simp only [quantumComplexDirectSumXIso, Iso.trans_hom, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom]
  have hιx := congrArg (fun f ↦ f.hom (D.khovanovEnhancedBasis hD R j i e)) hι
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hιx
  rw [hιx, ModuleCat.ι_coprodIsoDirectSum_hom_apply]
  -- Specify the unbundled direct-sum carrier: the categorical coproduct uses its bundled
  -- module instances, which prevent the DFinsupp simp lemmas from matching directly.
  change (Finsupp.lcongr (D.totalEnhancedStateAtEquiv i) (LinearEquiv.refl R R))
    ((DFinsupp.basis fun j ↦ D.khovanovEnhancedBasis hD R j i).repr
      (DFinsupp.single j (D.khovanovEnhancedBasis hD R j i e))) = _
  have hb : (DFinsupp.basis fun j ↦ D.khovanovEnhancedBasis hD R j i) ⟨j, e⟩ =
      DFinsupp.single j (D.khovanovEnhancedBasis hD R j i e) := by
    simp [DFinsupp.basis, Module.Basis.coe_ofRepr,
      DFinsupp.mapRange.linearEquiv_apply, -khovanovEnhancedBasis_apply]
  rw [← hb, Module.Basis.repr_self]
  simp

/-- Reconstructing a coefficient basis vector includes the corresponding homogeneous
circle-tensor basis vector in the quantum total. -/
@[simp↓]
theorem quantumComplexDirectSumXIso_inv_single (i j : ℤ) (e : D.EnhancedStateAt i j) :
    (D.quantumComplexDirectSumXIso hD R i).inv.hom
      (Finsupp.single (D.totalEnhancedStateAtEquiv i ⟨j, e⟩) 1) =
        ((Sigma.ι (D.khovanovComplex hD R) j).f i).hom
          (D.khovanovEnhancedBasis hD R j i e) := by
  rw [← D.quantumComplexDirectSumXIso_hom_ι_basis hD R i j e]
  exact ModuleCat.inv_hom_apply _ _

/-- The ordinary enhanced-state complex, with terms `TotalEnhancedStateAt i →₀ R` and
differential conjugate to the signed tensor differential. -/
-- Expose the body so term carriers elaborate as coefficient vectors in importing modules.
@[expose] def khovanovTotalEnhancedComplex : CochainComplex (ModuleCat.{u} R) ℤ where
  X i := ModuleCat.of R (D.TotalEnhancedStateAt i →₀ R)
  d i k := (D.quantumComplexDirectSumXIso hD R i).inv ≫
    (D.khovanovTotalComplex hD R).d i k ≫ (D.quantumComplexDirectSumXIso hD R k).hom
  shape i k hik := by simp [(D.khovanovTotalComplex hD R).shape i k hik]
  d_comp_d' i k l _ _ := by simp

/-- The ordinary coefficient differential is conjugate to the quantum-total differential. -/
theorem khovanovTotalEnhancedComplex_d (i k : ℤ) :
    (D.khovanovTotalEnhancedComplex hD R).d i k =
      (D.quantumComplexDirectSumXIso hD R i).inv ≫
        (D.khovanovTotalComplex hD R).d i k ≫
          (D.quantumComplexDirectSumXIso hD R k).hom := (rfl)

/-- Applying the coefficient differential reconstructs the tensor vector, differentiates,
and takes enhanced-state coordinates. -/
@[simp]
theorem khovanovTotalEnhancedComplex_d_apply (i k : ℤ) (x : D.TotalEnhancedStateAt i →₀ R) :
    ((D.khovanovTotalEnhancedComplex hD R).d i k).hom x =
      (D.quantumComplexDirectSumXIso hD R k).hom.hom
        (((D.khovanovTotalComplex hD R).d i k).hom
          ((D.quantumComplexDirectSumXIso hD R i).inv.hom x)) := (rfl)

/-- Every ordinary coefficient term is free, including the zero and empty-link terms. -/
instance (i : ℤ) : Module.Free R ((D.khovanovTotalEnhancedComplex hD R).X i) :=
  inferInstanceAs (Module.Free R (D.TotalEnhancedStateAt i →₀ R))

/-- Ordinary coefficient terms are finite because the native enhanced-state set is finite. -/
instance (i : ℤ) : Module.Finite R ((D.khovanovTotalEnhancedComplex hD R).X i) := by
  classical
  exact inferInstanceAs (Module.Finite R (D.TotalEnhancedStateAt i →₀ R))

/-- The actual cochain comparison from ordinary enhanced-state coefficients to the native
quantum total. It transports maps, homotopies and homology, not just ranks. -/
def quantumComplexDirectSumIso :
    D.khovanovTotalEnhancedComplex hD R ≅ D.khovanovTotalComplex hD R :=
  (HomologicalComplex.Hom.isoOfComponents (D.quantumComplexDirectSumXIso hD R)
    (by intros; simp [khovanovTotalEnhancedComplex])).symm

/-- The comparison from coefficients reconstructs each ordinary term. -/
@[simp]
theorem quantumComplexDirectSumIso_hom_f (i : ℤ) :
    (D.quantumComplexDirectSumIso hD R).hom.f i =
      (D.quantumComplexDirectSumXIso hD R i).inv := (rfl)

/-- The inverse comparison takes enhanced-state coordinates. -/
@[simp]
theorem quantumComplexDirectSumIso_inv_f (i : ℤ) :
    (D.quantumComplexDirectSumIso hD R).inv.f i =
      (D.quantumComplexDirectSumXIso hD R i).hom := (rfl)

/-- Include one quantum component in the ordinary enhanced-state complex by forgetting its
quantum constraint. -/
def khovanovTotalEnhancedComplexι (j : ℤ) :
    D.khovanovEnhancedComplex hD R j ⟶ D.khovanovTotalEnhancedComplex hD R :=
  (D.khovanovEnhancedComplexIso hD R j).inv ≫ Sigma.ι (D.khovanovComplex hD R) j ≫
    (D.quantumComplexDirectSumIso hD R).inv

/-- On terms, the homogeneous inclusion is the finite-support map forgetting quantum degree. -/
@[simp]
theorem khovanovTotalEnhancedComplexι_f (i j : ℤ) :
    (D.khovanovTotalEnhancedComplexι hD R j).f i =
      ModuleCat.ofHom (Finsupp.lmapDomain R R
        (fun e : D.EnhancedStateAt i j ↦ D.totalEnhancedStateAtEquiv i ⟨j, e⟩)) := by
  apply ModuleCat.hom_ext
  apply (Finsupp.basisSingleOne : Module.Basis (D.EnhancedStateAt i j) R _).ext
  intro e
  simp only [khovanovTotalEnhancedComplexι, comp_f, khovanovEnhancedComplexIso_inv_f,
    quantumComplexDirectSumIso_inv_f, Finsupp.coe_basisSingleOne]
  -- Identify the bundled complex terms with their coefficient carriers before applying
  -- the basis lemmas; simplification alone does not unfold these module instances.
  change (D.quantumComplexDirectSumXIso hD R i).hom.hom
    (((Sigma.ι (D.khovanovComplex hD R) j).f i).hom
      ((D.khovanovEnhancedBasis hD R j i).repr.symm (Finsupp.single e 1))) =
    Finsupp.lmapDomain R R
      (fun e : D.EnhancedStateAt i j ↦ D.totalEnhancedStateAtEquiv i ⟨j, e⟩)
      (Finsupp.single e 1)
  simpa only [Module.Basis.repr_symm_single_one, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single] using D.quantumComplexDirectSumXIso_hom_ι_basis hD R i j e

/-- The total comparison intertwines each native quantum inclusion with the corresponding
inclusion of enhanced-state complexes. -/
@[reassoc (attr := simp)]
theorem quantumComplexDirectSumIso_ι (j : ℤ) :
    Sigma.ι (D.khovanovComplex hD R) j ≫ (D.quantumComplexDirectSumIso hD R).inv =
      (D.khovanovEnhancedComplexIso hD R j).hom ≫
        D.khovanovTotalEnhancedComplexι hD R j := by
  simp [khovanovTotalEnhancedComplexι]

/-- The differential on a homogeneous ordinary basis vector is the original quantum-component
differential, included in the quantum total and then expressed in ordinary coordinates. -/
theorem khovanovTotalEnhancedComplex_d_single (i k j : ℤ) (e : D.EnhancedStateAt i j) :
    ((D.khovanovTotalEnhancedComplex hD R).d i k).hom
      (Finsupp.single (D.totalEnhancedStateAtEquiv i ⟨j, e⟩) 1) =
        (D.quantumComplexDirectSumXIso hD R k).hom.hom
          (((Sigma.ι (D.khovanovComplex hD R) j).f k).hom
            (((D.khovanovComplex hD R j).d i k).hom
              (D.khovanovEnhancedBasis hD R j i e))) := by
  rw [khovanovTotalEnhancedComplex_d_apply, quantumComplexDirectSumXIso_inv_single]
  congr 1
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
    congrArg (fun f ↦ f.hom (D.khovanovEnhancedBasis hD R j i e))
      (Hom.comm (Sigma.ι (D.khovanovComplex hD R) j) i k)

end TauCeti.OrientedPDCode
