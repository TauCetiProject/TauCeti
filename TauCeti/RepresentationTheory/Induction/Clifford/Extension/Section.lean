/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Independence of Clifford multiplicity modules from the section

Changing a normalized section of the canonical Clifford extension changes its
multiplicity algebra by the opposite inverse gauge isomorphism. Restricting scalars
along this isomorphism identifies the two multiplicity modules by the identity on
`Hom_N(A,W)`, naturally in the inertia representation `W`.

The inverse in the gauge coefficient is essential: kernel units act on multiplicities
by inverse precomposition. The comparison retains the full commutant `End A` and
requires neither scalar Schur nor semisimplicity, simplicity, or a finite quotient.

The construction uses the existing Clifford multiplicity action and the gauge
isomorphism of noncommutative crossed products.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace FDRep

open CategoryTheory MulOpposite TauCeti TauCeti.CliffordExtension TauCeti.GroupExtension

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)

variable (s t : (groupExtension A).Section) (hs : s 1 = 1) (ht : t 1 = 1)

/-- The multiplicity algebras of two normalized Clifford sections are isomorphic.
The comparison from the `t`-algebra to the `s`-algebra fixes coefficients and sends
`[q]` to `op (sectionDiff t s q)⁻¹ [q]`. -/
noncomputable def cliffordMultiplicityAlgebraEquiv :
    CrossedSystem.Algebra (cliffordCrossedSystem A t ht).opInv ≃ₐ[k]
      CrossedSystem.Algebra (cliffordCrossedSystem A s hs).opInv :=
  CrossedSystem.Algebra.opInvGaugeEquiv _ _ (sectionDiff t s)
    (t.sectionDiff_one s ht hs)
    (cliffordCrossedSystem_action_sectionDiff A s t hs ht)
    (cliffordCrossedSystem_factor_sectionDiff A s t hs ht)

/-- The multiplicity-algebra comparison fixes the opposite commutant. -/
@[simp]
theorem cliffordMultiplicityAlgebraEquiv_inc (d : (End A)ᵐᵒᵖ) :
    cliffordMultiplicityAlgebraEquiv A s t hs ht
      (CrossedSystem.Algebra.inc (cliffordCrossedSystem A t ht).opInv d) =
        CrossedSystem.Algebra.inc (cliffordCrossedSystem A s hs).opInv d := by
  simp [cliffordMultiplicityAlgebraEquiv]

/-- The multiplicity-algebra comparison uses the opposite inverse section difference. -/
@[simp]
theorem cliffordMultiplicityAlgebraEquiv_basis (q : Quotient A) :
    cliffordMultiplicityAlgebraEquiv A s t hs ht
      (CrossedSystem.Algebra.basis (cliffordCrossedSystem A t ht).opInv q) =
        op (↑(sectionDiff t s q)⁻¹ : End A) •
          CrossedSystem.Algebra.basis (cliffordCrossedSystem A s hs).opInv q := by
  simp [cliffordMultiplicityAlgebraEquiv]

/-- The inverse multiplicity-algebra comparison fixes the opposite commutant. -/
@[simp]
theorem cliffordMultiplicityAlgebraEquiv_symm_inc (d : (End A)ᵐᵒᵖ) :
    (cliffordMultiplicityAlgebraEquiv A s t hs ht).symm
      (CrossedSystem.Algebra.inc (cliffordCrossedSystem A s hs).opInv d) =
        CrossedSystem.Algebra.inc (cliffordCrossedSystem A t ht).opInv d := by
  simp [cliffordMultiplicityAlgebraEquiv]

/-- The inverse multiplicity-algebra comparison uses the opposite section difference. -/
@[simp]
theorem cliffordMultiplicityAlgebraEquiv_symm_basis (q : Quotient A) :
    (cliffordMultiplicityAlgebraEquiv A s t hs ht).symm
      (CrossedSystem.Algebra.basis (cliffordCrossedSystem A s hs).opInv q) =
        op (↑(sectionDiff t s q) : End A) •
          CrossedSystem.Algebra.basis (cliffordCrossedSystem A t ht).opInv q := by
  simp [cliffordMultiplicityAlgebraEquiv]

/-- The two multiplicity algebra actions agree through the section comparison. -/
theorem cliffordMultiplicitySemilinearAction_toAlgHom_section (W : FDRep k (inertia A)) :
    (cliffordMultiplicitySemilinearAction A t ht W).toAlgHom =
      (cliffordMultiplicitySemilinearAction A s hs W).toAlgHom.comp
        (cliffordMultiplicityAlgebraEquiv A s t hs ht).toAlgHom := by
  apply CrossedSystem.Algebra.algHom_ext
  · intro d
    simp
  · intro q
    ext f
    simp only [CrossedSystem.SemilinearAction.toAlgHom_basis, AlgHom.comp_apply,
      AlgEquiv.coe_toAlgHom, cliffordMultiplicityAlgebraEquiv_basis,
      CrossedSystem.SemilinearAction.toAlgHom_smul_basis,
      cliffordMultiplicitySemilinearAction_operator]
    rw [← cliffordMultiplicityRepresentation_gauge A W s (sectionDiff t s) q,
      GroupExtension.Section.gauge_sectionDiff]

local notation "E" => cliffordMultiplicityAlgebraEquiv A s t hs ht
local notation "Cs" => cliffordMultiplicityFunctor A s hs
local notation "Ct" => cliffordMultiplicityFunctor A t ht

private noncomputable def multiplicitySectionIsoApp (W : FDRep k (inertia A)) :
    (Ct).obj W ≅ (ModuleCat.restrictScalars (E).toRingHom).obj ((Cs).obj W) := by
  -- Supply the bundled module structures explicitly: both carriers are the same Hom
  -- space, but their algebra actions differ.
  let Mt := (Ct).obj W
  let Ms := (ModuleCat.restrictScalars (E).toRingHom).obj ((Cs).obj W)
  letI := Mt.isModule
  let e : @LinearEquiv _ _ _ _ (RingHom.id _) _ _ _ Mt Ms _ _ Mt.isModule Ms.isModule :=
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' a f := by
        refine (CrossedSystem.SemilinearAction.module_smul
          (cliffordMultiplicitySemilinearAction A t ht W) a f).trans ?_
        -- Compare the algebra actions, then interpret the result in the restricted module.
        refine (congrArg (fun F => F a f)
          (cliffordMultiplicitySemilinearAction_toAlgHom_section A s t hs ht W)).trans ?_
        refine (CrossedSystem.SemilinearAction.module_smul
          (cliffordMultiplicitySemilinearAction A s hs W) _ _).symm.trans ?_
        exact (ModuleCat.restrictScalars.smul_def
          (E).toRingHom (M := (Cs).obj W) a f).symm }
  exact e.toModuleIso

private theorem multiplicitySectionIsoApp_hom_apply (W : FDRep k (inertia A))
    (f : A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W) :
    (multiplicitySectionIsoApp A s t hs ht W).hom f = f := (rfl)

private theorem multiplicitySectionIsoApp_inv_apply (W : FDRep k (inertia A))
    (f : A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W) :
    (multiplicitySectionIsoApp A s t hs ht W).inv f = f := (rfl)

/-- Changing the normalized Clifford section leaves the multiplicity functor naturally
isomorphic after restriction along the opposite-inverse gauge algebra isomorphism.
Every component is the identity on the actual normal-subgroup intertwiner space. -/
noncomputable def cliffordMultiplicitySectionIso :
    (Ct) ≅ (Cs) ⋙ ModuleCat.restrictScalars (E).toRingHom :=
  NatIso.ofComponents (fun W => multiplicitySectionIsoApp A s t hs ht W)
    (by
      intro W W' g
      apply ConcreteCategory.ext_apply
      intro f
      simp only [Functor.comp_map]
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
        multiplicitySectionIsoApp_hom_apply, multiplicitySectionIsoApp_hom_apply]
      -- Keep the restriction-of-scalars formula typed to distinguish the stored module structures.
      simpa only [cliffordMultiplicityFunctor_map_apply A s hs g,
        cliffordMultiplicityFunctor_map_apply A t ht g] using
        (ModuleCat.restrictScalars.map_apply (E).toRingHom ((Cs).map g) f).symm)

/-- The section comparison is the identity on multiplicities. -/
@[simp]
theorem cliffordMultiplicitySectionIso_hom_app_apply (W : FDRep k (inertia A))
    (f : A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W) :
     dsimp% only [Functor.comp_obj, AlgEquiv.toRingEquiv_toRingHom, RingEquiv.toRingHom_eq_coe]
      (cliffordMultiplicitySectionIso A s t hs ht).hom.app W f = f :=
  (multiplicitySectionIsoApp_hom_apply A s t hs ht W f)

/-- The inverse section comparison is also the identity on multiplicities. -/
@[simp]
theorem cliffordMultiplicitySectionIso_inv_app_apply (W : FDRep k (inertia A))
    (f : A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W) :
     dsimp% only [Functor.comp_obj, AlgEquiv.toRingEquiv_toRingHom, RingEquiv.toRingHom_eq_coe]
      (cliffordMultiplicitySectionIso A s t hs ht).inv.app W f = f :=
  (multiplicitySectionIsoApp_inv_apply A s t hs ht W f)

end FDRep
