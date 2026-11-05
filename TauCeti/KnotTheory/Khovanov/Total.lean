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
    apply (cancel_mono (PreservesCoproduct.iso
      (eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i) (D.khovanovComplex hD R)).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [PreservesCoproduct.inv_hom]
    simpa only [eval_obj, eval_map] using
      (ι_comp_sigmaComparison (eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i)
        (D.khovanovComplex hD R) j).symm
  simp only [quantumComplexDirectSumXIso, Iso.trans_hom, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom]
  have hιx := congrArg (fun f ↦ f.hom (D.khovanovEnhancedBasis hD R j i e)) hι
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hιx
  rw [hιx, ModuleCat.ι_coprodIsoDirectSum_hom_apply]
  dsimp only [DFinsupp.basis, LinearEquiv.trans_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, DirectSum.lof]
  -- `erw` identifies the concrete direct-sum carrier with the module coproduct carrier.
  erw [DFinsupp.lsingle_apply, DFinsupp.mapRange.linearEquiv_apply,
    DFinsupp.mapRange_single, Module.Basis.repr_self]
  have hs : sigmaFinsuppLequivDFinsupp R (Finsupp.single ⟨j, e⟩ (1 : R)) =
      DFinsupp.single j (Finsupp.single e 1) :=
    sigmaFinsuppEquivDFinsupp_single ⟨j, e⟩ 1
  rw [← hs, LinearEquiv.symm_apply_apply, Finsupp.lcongr_single]
  rfl

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

/-- The ordinary enhanced-state complex. Its differential is the signed tensor differential
in the coordinates of all enhanced states of each cochain degree. The body is exposed so the
term carriers elaborate as coefficient vectors in importing modules. -/
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

/-- Every ordinary coefficient term is finite free, including the zero and empty-link terms. -/
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

/-- On coefficient basis vectors the cochain comparison is the homogeneous state inclusion. -/
@[simp↓]
theorem quantumComplexDirectSumIso_hom_f_single (i j : ℤ) (e : D.EnhancedStateAt i j) :
    ((D.quantumComplexDirectSumIso hD R).hom.f i).hom
      (Finsupp.single (D.totalEnhancedStateAtEquiv i ⟨j, e⟩) 1) =
        ((Sigma.ι (D.khovanovComplex hD R) j).f i).hom
          (D.khovanovEnhancedBasis hD R j i e) := by
  rw [quantumComplexDirectSumIso_hom_f]
  exact D.quantumComplexDirectSumXIso_inv_single hD R i j e

/-- Taking ordinary coordinates of an included homogeneous basis vector gives its single
coefficient vector. Apply this before expanding the homogeneous circle basis. -/
@[simp↓]
theorem quantumComplexDirectSumIso_inv_f_ι_basis (i j : ℤ) (e : D.EnhancedStateAt i j) :
    ((D.quantumComplexDirectSumIso hD R).inv.f i).hom
      (((Sigma.ι (D.khovanovComplex hD R) j).f i).hom
        (D.khovanovEnhancedBasis hD R j i e)) =
      Finsupp.single (D.totalEnhancedStateAtEquiv i ⟨j, e⟩) 1 := by
  rw [quantumComplexDirectSumIso_inv_f]
  exact D.quantumComplexDirectSumXIso_hom_ι_basis hD R i j e

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
