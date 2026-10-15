/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Category
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Complex
public import TauCeti.CategoryTheory.DG.HomComplexData
public import TauCeti.CategoryTheory.DG.ClosedCategory

/-!
# The differential graded category of right A-infinity modules

Right `A∞` modules over a fixed algebra form a DG category. Its Hom complexes are the
homogeneous maps of cofree bar comodules, with differential the graded commutator with the
module bar differentials. The existing cochain composition and Leibniz rule supply the
enrichment through `DGCategoryData.ofKeller`.

The homogeneous calculus agrees with the cochain calculus. In Mathlib's enriched factor
order, composition of degrees `p` and `q` is `(-1)^(p*q)` times composition of bar maps
in reversed order. The closed degree-zero morphisms are exactly `AInfinityRightModuleHom`,
compatibly with identities and composition. The resulting functor from bundled modules to
Mathlib's underlying category of the enrichment is full and faithful.

The functor `toClosedCategory` exposes its object map so that the types of its target
morphisms reduce to those of the original objects of the enrichment.

Bundling allows independent universes for the base, algebra, and modules. The DG enrichment
uses a common universe, as required by `DGCategoryData` and its `ModuleCat R` Hom complexes.

The construction and transport interface follow
`TauCeti.Algebra.Homology.DG.Module.Right.DGCategory`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

open AInfinityRightModule

universe u

variable {R : Type u} {A : Type u} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A}

namespace AInfinityRightModuleCat

/-- The Hom complexes and Keller-ordered cochain composition of right `A∞` modules,
converted to Mathlib's enriched factor order. -/
noncomputable def homComplexData : DGCategoryData R (AInfinityRightModuleCat.{u, u, u} AA) :=
  DGCategoryData.ofKeller
    (fun M N ↦ homComplex M.str N.str)
    (fun {_ _ _} _ _ _ h ↦ homCochains.comp h)
    (fun M ↦ homCochains.id M.str)
    (fun {_ _ _ _ _ _} h g f ↦ by
      simp only [homComplex_d]
      exact homDifferential_comp h g f)
    (fun {_ _ _ _ _ _ _ _ _ _} hrq hqp h k g f ↦
      homCochains.comp_assoc hrq hqp (by omega) (by omega) k g f)
    (fun g ↦ homCochains.comp_id g)
    (fun f ↦ homCochains.id_comp f)

variable (M N P : AInfinityRightModuleCat.{u, u, u} AA)

/-- The explicit Hom complex is the morphism complex of the two modules. -/
@[simp]
theorem homComplexData_hom :
    (homComplexData (AA := AA)).hom M N = homComplex M.str N.str :=
  (rfl)

/-- The differential graded enrichment of right `A∞` modules over `AA`. -/
noncomputable instance instDGCategory : DGCategory R (AInfinityRightModuleCat.{u, u, u} AA) :=
  (homComplexData (AA := AA)).toDGCategory

/-- The enriched Hom complex is the module morphism complex. -/
@[simp↓]
theorem dgHomComplex_eq : dgHomComplex R M N = homComplex M.str N.str :=
  (rfl)

/-- Homogeneous DG morphisms identified with homogeneous bar-comodule maps. -/
noncomputable def dgHomLinearEquivCochains (n : ℤ) :
    DGHom R n M N ≃ₗ[R] homCochains M.str N.str n :=
  (eqToIso (congrArg (fun K : CochainComplex (ModuleCat R) ℤ ↦ K.X n)
    (dgHomComplex_eq M N))).toLinearEquiv

/-- The identification with cochains transports along the equality of Hom complexes. -/
theorem dgHomLinearEquivCochains_apply (n : ℤ) (f : DGHom R n M N) :
    dgHomLinearEquivCochains M N n f =
      (eqToHom (congrArg (fun K : CochainComplex (ModuleCat R) ℤ ↦ K.X n)
        (dgHomComplex_eq M N))).hom f :=
  Iso.toLinearEquiv_apply _ _

/-- Composition of the explicit data transports to cochain composition with the Koszul sign. -/
private theorem homComplexData_comp {p q n : ℤ} (hpq : p + q = n)
    (f : DGHom R p M N) (g : DGHom R q N P) :
    dgHomLinearEquivCochains M P n ((homComplexData (AA := AA)).comp p q n hpq f g) =
      (p * q).negOnePow • homCochains.comp (by omega)
        (dgHomLinearEquivCochains N P q g) (dgHomLinearEquivCochains M N p f) := by
  simp only [dgHomLinearEquivCochains_apply]
  unfold homComplexData
  generalize_proofs (config := { maxDepth := 0, abstract := false })
  erw [DGCategoryData.ofKeller_comp]
  all_goals first | rfl | assumption

/-- The identity of the explicit data transports to the identity cochain. -/
private theorem homComplexData_id :
    dgHomLinearEquivCochains M M 0 ((homComplexData (AA := AA)).id M) =
      homCochains.id M.str := by
  simp only [dgHomLinearEquivCochains_apply]
  unfold homComplexData
  generalize_proofs (config := { maxDepth := 0, abstract := false })
  erw [DGCategoryData.ofKeller_id]
  · erw [eqToHom_refl]
    exact ModuleCat.id_apply _ _
  all_goals assumption

/-- The differential transports to the graded commutator with the module bar differentials. -/
@[simp↓]
theorem dgDifferential_eq (n : ℤ) (f : DGHom R n M N) :
    dgHomLinearEquivCochains M N (n + 1) (dgDifferential R n f) =
      homDifferential M.str N.str n (dgHomLinearEquivCochains M N n f) := by
  rw [DGCategoryData.dgDifferential_toDGCategory]
  exact congrArg (fun φ : (homComplex M.str N.str).X n ⟶
      (homComplex M.str N.str).X (n + 1) ↦
      φ.hom (dgHomLinearEquivCochains M N n f)) (homComplex_d M.str N.str n)

/-- The DG identity transports to the identity cochain. -/
@[simp↓]
theorem dgId_eq :
    dgHomLinearEquivCochains M M 0 (dgId R M) = homCochains.id M.str :=
  (congrArg (dgHomLinearEquivCochains M M 0)
    (DGCategoryData.dgId_toDGCategory (homComplexData (AA := AA)) M)).trans
      (homComplexData_id M)

/-- DG composition transports to composition of cochains with the enriched-order Koszul sign. -/
@[simp↓]
theorem dgComp_eq {p q n : ℤ} (f : DGHom R p M N) (g : DGHom R q N P) (hpq : p + q = n) :
    dgHomLinearEquivCochains M P n (dgComp R f g hpq) =
      (p * q).negOnePow • homCochains.comp (by omega)
        (dgHomLinearEquivCochains N P q g) (dgHomLinearEquivCochains M N p f) :=
  (congrArg (dgHomLinearEquivCochains M P n)
    (DGCategoryData.dgComp_toDGCategory (homComplexData (AA := AA)) f g hpq)).trans
      (homComplexData_comp M N P hpq f g)

/-- DG cycles correspond to the kernel of the cochain differential. -/
theorem dgCycles_eq :
    dgCycles R M N = Submodule.comap (dgHomLinearEquivCochains M N 0).toLinearMap
      (LinearMap.ker (homDifferential M.str N.str 0)) := by
  ext f
  rw [mem_dgCycles, Submodule.mem_comap, LinearMap.mem_ker, LinearEquiv.coe_toLinearMap,
    ← dgDifferential_eq, LinearEquiv.map_eq_zero_iff]

/-- Module morphisms are exactly the closed degree-zero morphisms of the DG enrichment. -/
noncomputable def homEquivDGCycles : (M ⟶ N) ≃ dgCycles R M N :=
  (AInfinityRightModuleHom.equivZeroCocycles.trans
    ((dgHomLinearEquivCochains M N 0).ofSubmodule'
      (LinearMap.ker (homDifferential M.str N.str 0))).symm.toEquiv).trans
    (LinearEquiv.ofEq _ _ (dgCycles_eq M N).symm).toEquiv

variable {M N P}

/-- The cycle associated to a module morphism has its original bar map. -/
@[simp]
theorem coe_homEquivDGCycles_apply (f : M ⟶ N) :
    (dgHomLinearEquivCochains M N 0 (homEquivDGCycles M N f)).1 = f.barMap := by
  simp only [homEquivDGCycles, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofSubmodule'_symm_apply,
    LinearEquiv.apply_symm_apply]
  exact AInfinityRightModuleHom.coe_equivZeroCocycles f

/-- The morphism associated to a DG cycle has the cycle's bar map. -/
@[simp]
theorem barMap_homEquivDGCycles_symm (f : dgCycles R M N) :
    ((homEquivDGCycles M N).symm f).barMap = (dgHomLinearEquivCochains M N 0 f).1 := by
  simpa only [Equiv.apply_symm_apply] using
    (coe_homEquivDGCycles_apply ((homEquivDGCycles M N).symm f)).symm

/-- The categorical identity corresponds to the DG identity. -/
@[simp]
theorem homEquivDGCycles_id :
    (homEquivDGCycles M M (𝟙 M) : DGHom R 0 M M) = dgId R M := by
  apply (dgHomLinearEquivCochains M M 0).injective
  rw [dgId_eq]
  apply Subtype.ext
  rw [coe_homEquivDGCycles_apply, barMap_id, homCochains.coe_id]

/-- Composition of module morphisms corresponds to composition of DG cycles. -/
@[simp]
theorem homEquivDGCycles_comp (f : M ⟶ N) (g : N ⟶ P) :
    homEquivDGCycles M P (f ≫ g) =
      dgCyclesComp R M N P (homEquivDGCycles M N f) (homEquivDGCycles N P g) := by
  apply Subtype.ext
  apply (dgHomLinearEquivCochains M P 0).injective
  rw [coe_dgCyclesComp, dgCompZero_def, dgComp_eq, mul_zero, Int.negOnePow_zero, one_smul]
  apply Subtype.ext
  rw [coe_homEquivDGCycles_apply, barMap_comp, homCochains.coe_comp,
    coe_homEquivDGCycles_apply, coe_homEquivDGCycles_apply]

variable (AA)

/-- Identify module morphisms with the underlying morphisms of the DG enrichment. -/
@[expose]
noncomputable def toClosedCategory :
    AInfinityRightModuleCat.{u, u, u} AA ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (AInfinityRightModuleCat.{u, u, u} AA)
    where
  obj M := ForgetEnrichment.of _ M
  map {M N} f := dgClosedHomOf R (homEquivDGCycles M N f).1 (homEquivDGCycles M N f).2
  map_id M := by
    apply dgClosedHom_injective R
    rw [dgClosedHom_dgClosedHomOf, dgClosedHom_id]
    exact homEquivDGCycles_id
  map_comp {M N P} f g := by
    apply dgClosedHom_injective R
    simp only [dgClosedHom_dgClosedHomOf, dgClosedHom_comp]
    exact (congrArg Subtype.val (homEquivDGCycles_comp f g)).trans (coe_dgCyclesComp R _ _)

variable {AA}

/-- The comparison functor preserves the underlying module object. -/
@[simp]
theorem toClosedCategory_obj (M : AInfinityRightModuleCat.{u, u, u} AA) :
    (toClosedCategory AA).obj M = ForgetEnrichment.of _ M :=
  (rfl)

/-- Extracting the closed component recovers the cycle associated to the module morphism. -/
@[simp]
theorem dgClosedHom_toClosedCategory_map (f : M ⟶ N) :
    dgClosedHom R ((toClosedCategory AA).map f) = (homEquivDGCycles M N f).1 :=
  dgClosedHom_dgClosedHomOf R _ _

instance : (toClosedCategory AA).Faithful where
  map_injective := by
    intro M N f g h
    apply (homEquivDGCycles M N).injective
    apply Subtype.ext
    have hc := congrArg (dgClosedHom R) h
    -- Reduce the exposed functor so the type of the extracted component is `DGHom R 0 M N`.
    dsimp only [toClosedCategory] at hc
    simpa only [dgClosedHom_dgClosedHomOf] using hc

instance : (toClosedCategory AA).Full where
  map_surjective {M N} f := by
    refine ⟨(homEquivDGCycles M N).symm ((dgClosedHomEquiv R _ _) f), ?_⟩
    apply dgClosedHom_injective R
    simp only [dgClosedHom_toClosedCategory_map, Equiv.apply_symm_apply]
    exact dgClosedHomEquiv_apply_coe R f

end AInfinityRightModuleCat

end TauCeti
