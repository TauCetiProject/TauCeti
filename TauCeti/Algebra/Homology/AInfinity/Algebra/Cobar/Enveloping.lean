/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Augmentation.UnitalHom
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar.Contraction
public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG.Cohomology

/-!
# The enveloping differential graded algebra of an augmented `A∞` algebra

For an augmented `A∞` algebra `(A, ε)`, `U(A) = Ω Tᶜ(sA⁺)` satisfies the universal property for
strictly unital and augmented `A∞` morphisms into DG algebras, is functorial, contracts onto `A`,
and yields the bar--cobar counit for any augmented DG algebra.

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Contemp. Math. 406 (2006), §4.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Springer (2012), Section 2.2 and Chapter 11.
-/

public section

open scoped TensorProduct
open TensorAlgebra

namespace TauCeti

open AInfinityAlgebra (differential_apply coe_cobarAugmentationIdealContraction_incl mem_cycles
  mem_boundaries)
open IsNonCounitalDGCoalgebra (coe_cobarReducedDifferential)
open DGAlgHom (toNonUnitalDGAlgHom_comp)
open NonUnitalDGAlgHom (toAInfinityStrictHom_comp)
open AInfinityStrictHom (toAInfinityHom_comp)

universe uR uA uB uC uD

namespace AInfinityAlgebra.Augmentation

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}

section SingleAugmentation

variable (ε : 𝒜.Augmentation)

/-- The underlying algebra carrier of the enveloping DG algebra `U(A) = Ω Tᶜ(sA⁺)`. -/
abbrev Enveloping := TensorAlgebra R (ReducedTensorWords R ε.augmentationIdeal)

/-- The internal `ℤ`-grading of the enveloping DG algebra `U(A) = Ω Tᶜ(sA⁺)`. -/
noncomputable abbrev envelopingGrading : ℤ → Submodule R ε.Enveloping :=
  tensorAlgebraPiece ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).shift (-1))

/-- The differential of the enveloping DG algebra `U(A) = Ω Tᶜ(sA⁺)`. -/
noncomputable abbrev envelopingDifferential : Module.End R ε.Enveloping :=
  cobarDifferential (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1))
    (ReducedTensorWords.deconcatenation R ε.augmentationIdeal) ε.reducedAlgebra.barDifferential

private abbrev barCoalg := ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar

/-- The enveloping DG algebra `U(A) = Ω Tᶜ(sA⁺)` is a differential graded algebra. -/
theorem isDGAlgebra_enveloping : IsDGAlgebra ε.envelopingGrading ε.envelopingDifferential :=
  ε.barCoalg.isDGAlgebra_cobarDifferential

/-- The canonical augmentation `U(A) ⟶ R` of the enveloping DG algebra. -/
noncomputable abbrev envelopingAugmentation : DGAlgAugmentation ε.isDGAlgebra_enveloping :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation

theorem envelopingAugmentation_ι (z : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingAugmentation (ι R z) = 0 := ε.barCoalg.cobarAugmentation_ι z

section UniversalProperty

variable [Ring D] [Algebra R D] {𝒟 : ℤ → Submodule R D} [GradedAlgebra 𝒟] {dD : D →ₗ[R] D}

/-- Strictly unital `A∞` morphisms `A ⟶ D` correspond to DG algebra morphisms `U(A) ⟶ D`. -/
noncomputable def envelopingHomEquiv (hD : IsDGAlgebra 𝒟 dD) :
    {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one} ≃
      DGAlgHom ε.isDGAlgebra_enveloping hD :=
  (ε.strictlyUnitalHomEquiv hD.strictUnit_one).trans (ε.reducedAlgebra.cobarBarHomEquiv hD)

@[simp] theorem envelopingHomEquiv_apply_ι (hD : IsDGAlgebra 𝒟 dD)
    (f : {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one})
    (z : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingHomEquiv hD f (ι R z) =
      -(InternalGrading.ofDecomposition 𝒟).koszulTwist 1
        ((f.1.comp ε.reducedInclusion.toAInfinityHom).taylor z) := by simp [envelopingHomEquiv]

/-- The canonical strictly unital `A∞` morphism `η : A ⟶ U(A)`. -/
noncomputable def toEnveloping :
    AInfinityHom 𝒜 ε.isDGAlgebra_enveloping.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  ((ε.envelopingHomEquiv ε.isDGAlgebra_enveloping).symm (DGAlgHom.id _)).1

/-- The canonical morphism `A ⟶ U(A)` is strictly unital. -/
theorem isStrictlyUnital_toEnveloping :
    ε.toEnveloping.IsStrictlyUnital ε.isStrictUnit ε.isDGAlgebra_enveloping.strictUnit_one :=
  ((ε.envelopingHomEquiv ε.isDGAlgebra_enveloping).symm (DGAlgHom.id _)).2

private theorem toEnveloping_eq :
    ε.toEnveloping = ((ε.strictlyUnitalHomEquiv ε.isDGAlgebra_enveloping.strictUnit_one).symm
      ε.reducedAlgebra.toCobarBar).1 := by
  rw [toEnveloping, envelopingHomEquiv, Equiv.symm_trans_apply,
    (Equiv.symm_apply_eq (ε.reducedAlgebra.cobarBarHomEquiv _)).2
      ε.reducedAlgebra.cobarBarHomEquiv_toCobarBar.symm]

@[simp] theorem envelopingHomEquiv_toEnveloping :
    ε.envelopingHomEquiv ε.isDGAlgebra_enveloping
      ⟨ε.toEnveloping, ε.isStrictlyUnital_toEnveloping⟩ = DGAlgHom.id _ :=
  Equiv.apply_symm_apply _ _

@[simp] theorem toEnveloping_comp_reducedInclusion :
    ε.toEnveloping.comp ε.reducedInclusion.toAInfinityHom = ε.reducedAlgebra.toCobarBar := by
  rw [toEnveloping_eq, ← strictlyUnitalHomEquiv_apply, Equiv.apply_symm_apply]

@[simp] theorem taylor_toEnveloping :
    ε.toEnveloping.taylor =
      ι R ∘ₗ (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1 ∘ₗ
          ReducedTensorWords.map (R := R) ε.reducedPart +
        LinearMap.toSpanSingleton R ε.Enveloping 1 ∘ₗ ε.toLinearMap ∘ₗ
          ReducedTensorWords.letter R A := by
  simp [toEnveloping_eq, AInfinityAlgebra.taylor_toCobarBar, LinearMap.comp_assoc]

theorem linearPart_toEnveloping_coe (x : ε.augmentationIdeal) :
    ε.toEnveloping.linearPart x = ε.reducedAlgebra.toCobarBar.linearPart x := by
  rw [toEnveloping_eq, linearPart_strictlyUnitalHomEquiv_symm_coe]

theorem linearPart_toEnveloping_unit : ε.toEnveloping.linearPart ε.unit = 1 :=
  ε.isStrictlyUnital_toEnveloping.map_unit

theorem linearPart_toEnveloping_apply (a : A) :
    ε.toEnveloping.linearPart a =
      algebraMap R ε.Enveloping (ε a) +
        ε.reducedAlgebra.toCobarBar.linearPart (ε.reducedPart a) := by
  simp [AInfinityHom.linearPart_apply, AInfinityAlgebra.taylor_toCobarBar,
    ReducedTensorWords.map_ofLetter, Algebra.algebraMap_eq_smul_one, add_comm]

/-- The canonical morphism `A ⟶ U(A)` commutes with the augmentations. -/
@[simp] theorem envelopingAugmentation_comp_toEnveloping :
    ε.envelopingAugmentation.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        ε.toEnveloping = ε.toAInfinityStrictHom.toAInfinityHom := by
  rw [← DGAlgAugmentation.toAInfinityAugmentation_toAInfinityStrictHom,
    ε.comp_toAInfinityStrictHom_eq_iff _ ⟨ε.toEnveloping,
      AInfinityHom.isStrictlyUnital_iff_of_strictUnit.2 ε.isStrictlyUnital_toEnveloping⟩]
  exact LinearMap.ext fun _ ↦ by simp [AInfinityAlgebra.taylor_toCobarBar]

theorem envelopingHomEquiv_symm_apply (hD : IsDGAlgebra 𝒟 dD)
    (φ : DGAlgHom ε.isDGAlgebra_enveloping hD) :
    ((ε.envelopingHomEquiv hD).symm φ).1 =
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping := by
  rw [envelopingHomEquiv, Equiv.symm_trans_apply, AInfinityAlgebra.cobarBarHomEquiv_symm_apply,
    ← DGAlgHom.toAInfinityStrictHom_toAInfinityStrictUnitalHom,
    ε.strictlyUnitalHomEquiv_symm_comp_strict _ hD.strictUnit_one φ.toAInfinityStrictUnitalHom,
    ← toEnveloping_eq]

/-- **The universal property of `U(A)` among strictly unital `A∞` morphisms.** -/
theorem bijective_comp_toEnveloping (hD : IsDGAlgebra 𝒟 dD) :
    Function.Bijective fun φ : DGAlgHom ε.isDGAlgebra_enveloping hD ↦
      (⟨φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping,
        φ.isStrictlyUnital_toAInfinityHom.comp ε.isStrictlyUnital_toEnveloping⟩ :
        {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
          f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one}) := by
  convert (ε.envelopingHomEquiv hD).symm.bijective using 1
  exact funext fun φ ↦ Subtype.ext (ε.envelopingHomEquiv_symm_apply hD φ).symm

/-- `envelopingHomEquiv hD f` preserves augmentations if and only if `f` does. -/
theorem comp_envelopingHomEquiv_eq_iff {hD : IsDGAlgebra 𝒟 dD} (eD : DGAlgAugmentation hD)
    (f : {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one}) :
    eD.comp (ε.envelopingHomEquiv hD f) = ε.envelopingAugmentation ↔
      eD.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp f.1 =
        ε.toAInfinityStrictHom.toAInfinityHom := by
  rw [ε.barCoalg.comp_eq_cobarAugmentation_iff eD,
    ← DGAlgAugmentation.toAInfinityAugmentation_toAInfinityStrictHom,
    ε.comp_toAInfinityStrictHom_eq_iff _
      ⟨f.1, AInfinityHom.isStrictlyUnital_iff_of_strictUnit.2 f.2⟩]
  simp [LinearMap.ext_iff]

/-- Strictly unital augmented `A∞` morphisms `A ⟶ D` correspond to augmented `U(A) ⟶ D`. -/
noncomputable def envelopingAugmentedHomEquiv {hD : IsDGAlgebra 𝒟 dD} (eD : DGAlgAugmentation hD) :
    {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one ∧
          eD.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp f =
            ε.toAInfinityStrictHom.toAInfinityHom} ≃
      {φ : DGAlgHom ε.isDGAlgebra_enveloping hD // eD.comp φ = ε.envelopingAugmentation} :=
  (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans <|
    (ε.envelopingHomEquiv hD).subtypeEquiv fun f ↦ (ε.comp_envelopingHomEquiv_eq_iff eD f).symm

/-- **The universal property of `U(A)` among strictly unital augmented `A∞` morphisms.** -/
theorem bijective_comp_toEnveloping_augmented {hD : IsDGAlgebra 𝒟 dD} (eD : DGAlgAugmentation hD) :
    Function.Bijective fun φ :
        {φ : DGAlgHom ε.isDGAlgebra_enveloping hD // eD.comp φ = ε.envelopingAugmentation} ↦
      (⟨φ.1.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping,
        φ.1.isStrictlyUnital_toAInfinityHom.comp ε.isStrictlyUnital_toEnveloping, by
          simp [← AInfinityHom.comp_assoc, ← toAInfinityHom_comp, ← toAInfinityStrictHom_comp,
            ← toNonUnitalDGAlgHom_comp, φ.2]⟩ :
        {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
          f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one ∧
            eD.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp f =
              ε.toAInfinityStrictHom.toAInfinityHom}) := by
  convert (ε.envelopingAugmentedHomEquiv eD).symm.bijective using 1
  exact funext fun φ ↦ Subtype.ext (ε.envelopingHomEquiv_symm_apply hD φ.1).symm

end UniversalProperty

private noncomputable abbrev redContr := ε.reducedAlgebra.cobarAugmentationIdealContraction

private theorem reducedPart_envelopingDifferential (z : ε.Enveloping) :
    ε.envelopingAugmentation.reducedPart (ε.envelopingDifferential z) =
      ε.barCoalg.cobarReducedDifferential (ε.envelopingAugmentation.reducedPart z) :=
  Subtype.ext <| by rw [DGAlgAugmentation.coe_reducedPart, ε.envelopingAugmentation.map_d]
                    simp [DGAlgAugmentation.coe_reducedPart, envelopingDifferential]

private theorem envelopingAugmentation_linearPart_toEnveloping (a : A) :
    ε.envelopingAugmentation (ε.toEnveloping.linearPart a) = ε a := by
  rw [ε.linearPart_toEnveloping_apply, map_add, ε.envelopingAugmentation.map_algebraMap,
    ← coe_cobarAugmentationIdealContraction_incl,
    ε.envelopingAugmentation.mem_augmentationIdeal.mp (ε.redContr.incl _).2, add_zero]

private theorem reducedPart_linearPart_toEnveloping (a : A) :
    ε.envelopingAugmentation.reducedPart (ε.toEnveloping.linearPart a) =
      ε.redContr.incl (ε.reducedPart a) := Subtype.ext <| by
  rw [DGAlgAugmentation.coe_reducedPart, ε.envelopingAugmentation_linearPart_toEnveloping,
    ε.linearPart_toEnveloping_apply, coe_cobarAugmentationIdealContraction_incl,
    add_sub_cancel_left]

/-- **The explicit special contraction of `U(A) = Ω Tᶜ(sA⁺)` onto `(A, m₁)`.** -/
noncomputable def envelopingContraction :
    LinearSpecialContraction ε.envelopingDifferential 𝒜.differential where
  incl := ε.toEnveloping.linearPart
  proj := ε.unitHom ∘ₗ ε.envelopingAugmentation.toGradedAlgHom.toAlgHom.toLinearMap +
    ε.augmentationIdeal.subtype ∘ₗ ε.redContr.proj ∘ₗ ε.envelopingAugmentation.reducedPart
  homotopy := ε.envelopingAugmentation.augmentationIdeal.toSubmodule.subtype ∘ₗ
    ε.redContr.homotopy ∘ₗ ε.envelopingAugmentation.reducedPart
  dM_comp_incl := LinearMap.ext fun a ↦ by
    simpa [differential_apply] using (ε.toEnveloping.linearPart_m_one a).symm
  proj_comp_dM := LinearMap.ext fun z ↦ by
    simp [-differential_apply, unitHom_apply, ε.envelopingAugmentation.map_d,
      ε.reducedPart_envelopingDifferential, LinearContraction.proj_dM_apply]
    simp only [differential_apply, ε.isStrictUnit.unary_eq_zero, smul_zero, zero_add]
    simpa only [coe_reducedInclusion] using ε.reducedInclusion.map_m_one _
  proj_comp_incl := LinearMap.ext fun a ↦ by
    simp [-AInfinityHom.linearPart_apply, unitHom_apply, ε.coe_reducedPart,
      ε.envelopingAugmentation_linearPart_toEnveloping, ε.reducedPart_linearPart_toEnveloping]
  dM_comp_homotopy_add_homotopy_comp_dM := LinearMap.ext fun z ↦ by
    simpa [-AInfinityHom.linearPart_apply, -reducedAlgebra_grading,
      DGAlgAugmentation.coe_reducedPart, ε.reducedPart_envelopingDifferential,
      ε.linearPart_toEnveloping_unit, ε.linearPart_toEnveloping_coe,
      Algebra.algebraMap_eq_smul_one, sub_add_eq_sub_sub] using
      congrArg Subtype.val <| LinearMap.congr_fun
        ε.redContr.dM_comp_homotopy_add_homotopy_comp_dM (ε.envelopingAugmentation.reducedPart z)
  homotopy_comp_incl := LinearMap.ext fun _ ↦ by
    simp [-AInfinityHom.linearPart_apply, ε.reducedPart_linearPart_toEnveloping]
  proj_comp_homotopy := LinearMap.ext fun _ ↦ by
    simp [ε.envelopingAugmentation.mem_augmentationIdeal.mp (ε.redContr.homotopy _).2]
  homotopy_comp_homotopy := LinearMap.ext fun _ ↦ by simp

@[simp] theorem envelopingContraction_incl :
    ε.envelopingContraction.incl = ε.toEnveloping.linearPart := (rfl)

/-- The projection of `envelopingContraction` splits into scalar and reduced parts. -/
@[simp] theorem envelopingContraction_proj_apply (z : ε.Enveloping) :
    ε.envelopingContraction.proj z =
      ε.envelopingAugmentation z • ε.unit +
        (ε.reducedAlgebra.cobarAugmentationIdealContraction.proj
          (ε.envelopingAugmentation.reducedPart z) : A) := by simp [envelopingContraction]

/-- The homotopy of `envelopingContraction` acts via the reduced homotopy on the reduced part. -/
@[simp] theorem envelopingContraction_homotopy_apply (z : ε.Enveloping) :
    ε.envelopingContraction.homotopy z =
      (ε.reducedAlgebra.cobarAugmentationIdealContraction.homotopy
        (ε.envelopingAugmentation.reducedPart z) : ε.Enveloping) := (rfl)

private theorem reducedPart_mem_cobarReducedGrading {p : ℤ} {z : ε.Enveloping}
    (hz : z ∈ ε.envelopingGrading p) :
    ε.envelopingAugmentation.reducedPart z ∈ ε.barCoalg.cobarReducedGrading.piece p :=
  ε.barCoalg.mem_cobarReducedGrading_piece.2 <| by
    simpa [-reducedAlgebra_grading] using
      ε.envelopingAugmentation.isHomogeneous_reducedPart.map_mem hz

theorem isHomogeneous_envelopingContraction_incl :
    LinearMap.IsHomogeneous ε.envelopingContraction.incl 𝒜.grading.piece ε.envelopingGrading 0 := by
  simpa [IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading] using
    ε.toEnveloping.isHomogeneous_linearPart

theorem isHomogeneous_envelopingContraction_proj :
    LinearMap.IsHomogeneous ε.envelopingContraction.proj ε.envelopingGrading 𝒜.grading.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun p _ hz ↦ by
    rw [add_zero, envelopingContraction_proj_apply]
    refine Submodule.add_mem _ (by
      rcases eq_or_ne p 0 with rfl | hp
      exacts [Submodule.smul_mem _ _ ε.isStrictUnit.degree_zero,
        by simp [ε.envelopingAugmentation.map_eq_zero_of_mem_ne_zero hz hp]]) <| by
      simpa [ε.reducedAlgebra_grading, ε.reducedGrading_piece] using
        ε.reducedAlgebra.isHomogeneous_cobarAugmentationIdealContraction_proj.map_mem
          (ε.reducedPart_mem_cobarReducedGrading hz)

theorem isHomogeneous_envelopingContraction_homotopy :
    LinearMap.IsHomogeneous ε.envelopingContraction.homotopy
      ε.envelopingGrading ε.envelopingGrading (-1) :=
  LinearMap.isHomogeneous_def.2 fun _ _ hz ↦ ε.barCoalg.mem_cobarReducedGrading_piece.1 <|
    ε.reducedAlgebra.isHomogeneous_cobarAugmentationIdealContraction_homotopy.map_mem
      (ε.reducedPart_mem_cobarReducedGrading hz)

/-- **The canonical `A∞` morphism `A ⟶ U(A)` is a quasi-isomorphism** over any commutative ring. -/
theorem isQuasiIso_toEnveloping : ε.toEnveloping.IsQuasiIso := by
  let c := ε.envelopingContraction
  refine (AInfinityHom.isQuasiIso_iff_forall_cycles _).2 ⟨fun y hy ↦ ?_, fun x _ hfx ↦ ?_⟩
  · have hy' : ε.envelopingDifferential y = 0 := by simpa [mem_cycles] using hy
    refine ⟨c.proj y, by rw [mem_cycles, ← differential_apply, ← c.proj_dM_apply, hy', map_zero],
      (mem_boundaries _).2 ⟨-c.homotopy y, by
        rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_one_apply, Matrix.cons_val_zero, map_neg,
          ← envelopingContraction_incl, c.toLinearContraction.incl_proj_apply, hy', map_zero,
          sub_zero]; abel⟩⟩
  · obtain ⟨w, hw⟩ := (mem_boundaries _).1 hfx
    exact (mem_boundaries _).2 ⟨c.proj w, by rw [← differential_apply, ← c.proj_dM_apply,
      show ε.envelopingDifferential w = c.incl x by simpa [c] using hw, c.proj_incl_apply]⟩

end SingleAugmentation

/-- The DG algebra morphism `U(f) : U(A) ⟶ U(B)` induced by a strictly unital `A∞` morphism `f`. -/
noncomputable def envelopingMap (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation)
    (f : AInfinityHom 𝒜 ℬ) (hf : f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit) :
    DGAlgHom εA.isDGAlgebra_enveloping εB.isDGAlgebra_enveloping :=
  εA.envelopingHomEquiv εB.isDGAlgebra_enveloping
    ⟨εB.toEnveloping.comp f, εB.isStrictlyUnital_toEnveloping.comp hf⟩

/-- On `ι R z`, `U(f)` applies the Koszul twist to the restricted Taylor map of `η_B ∘ f`. -/
@[simp] theorem envelopingMap_ι (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation)
    (f : AInfinityHom 𝒜 ℬ) (hf : f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit)
    (z : ReducedTensorWords R εA.augmentationIdeal) :
    εA.envelopingMap εB f hf (ι R z) =
      -(InternalGrading.ofDecomposition εB.envelopingGrading).koszulTwist 1
        (((εB.toEnveloping.comp f).comp εA.reducedInclusion.toAInfinityHom).taylor z) := by
  simp [envelopingMap]

@[simp] theorem envelopingMap_comp_toEnveloping (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation)
    (f : AInfinityHom 𝒜 ℬ) (hf : f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit) :
    (εA.envelopingMap εB f hf).toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        εA.toEnveloping = εB.toEnveloping.comp f := by
  rw [← εA.envelopingHomEquiv_symm_apply εB.isDGAlgebra_enveloping, envelopingMap,
    Equiv.symm_apply_apply]

@[simp] theorem envelopingMap_id (ε : 𝒜.Augmentation) :
    ε.envelopingMap ε (AInfinityHom.id 𝒜) (AInfinityHom.isStrictlyUnital_id ε.isStrictUnit) =
      DGAlgHom.id _ :=
  (ε.bijective_comp_toEnveloping ε.isDGAlgebra_enveloping).1 <| Subtype.ext <| by simp

theorem envelopingMap_comp (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation) (εC : 𝒞.Augmentation)
    {g : AInfinityHom ℬ 𝒞} {f : AInfinityHom 𝒜 ℬ}
    (hg : g.IsStrictlyUnital εB.isStrictUnit εC.isStrictUnit)
    (hf : f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit) :
    εA.envelopingMap εC (g.comp f) (hg.comp hf) =
      (εB.envelopingMap εC g hg).comp (εA.envelopingMap εB f hf) :=
  (εA.bijective_comp_toEnveloping εC.isDGAlgebra_enveloping).1 <| Subtype.ext <| by
    dsimp only; rw [envelopingMap_comp_toEnveloping, toNonUnitalDGAlgHom_comp,
      toAInfinityStrictHom_comp, toAInfinityHom_comp, AInfinityHom.comp_assoc,
      envelopingMap_comp_toEnveloping, ← AInfinityHom.comp_assoc _ εB.toEnveloping,
      envelopingMap_comp_toEnveloping, AInfinityHom.comp_assoc]

theorem comp_envelopingMap (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation)
    {f : AInfinityHom 𝒜 ℬ} (hf : f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit)
    (haug : εB.toAInfinityStrictHom.toAInfinityHom.comp f =
      εA.toAInfinityStrictHom.toAInfinityHom) :
    εB.envelopingAugmentation.comp (εA.envelopingMap εB f hf) = εA.envelopingAugmentation := by
  rw [envelopingMap, εA.comp_envelopingHomEquiv_eq_iff εB.envelopingAugmentation,
    ← AInfinityHom.comp_assoc, εB.envelopingAugmentation_comp_toEnveloping, haug]

/-- `U(f)` is a DG algebra quasi-isomorphism if and only if `f` is an `A∞` quasi-isomorphism. -/
theorem bijective_cohomologyMap_envelopingMap_iff (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation)
    (f : AInfinityHom 𝒜 ℬ) (hf : f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit) :
    Function.Bijective (εA.envelopingMap εB f hf).cohomologyMap ↔ f.IsQuasiIso := by
  rw [DGAlgHom.bijective_cohomologyMap_iff_isQuasiIso]
  have h := εA.envelopingMap_comp_toEnveloping εB f hf
  exact ⟨fun hU ↦ εB.isQuasiIso_toEnveloping.of_postcomp (h ▸ hU.comp εA.isQuasiIso_toEnveloping),
    fun hq ↦ εA.isQuasiIso_toEnveloping.of_precomp (h.symm ▸ εB.isQuasiIso_toEnveloping.comp hq)⟩

end AInfinityAlgebra.Augmentation

namespace DGAlgAugmentation

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B] {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

section SingleDGAugmentation

variable (e : DGAlgAugmentation hA)

/-- The canonical bar--cobar counit `U(A) ⟶ A` of an augmented DG algebra `(A, e)`. -/
noncomputable def fromEnveloping : DGAlgHom e.toAInfinityAugmentation.isDGAlgebra_enveloping hA :=
  e.toAInfinityAugmentation.envelopingHomEquiv hA
    ⟨AInfinityHom.id _, AInfinityHom.isStrictlyUnital_iff_of_strictUnit.2
      (AInfinityHom.isStrictlyUnital_id hA.strictUnit_one)⟩

@[simp] theorem fromEnveloping_ι
    (z : ReducedTensorWords R e.toAInfinityAugmentation.augmentationIdeal) :
    e.fromEnveloping (ι R z) = -(InternalGrading.ofDecomposition 𝒜).koszulTwist 1
      (ReducedTensorWords.letter R e.toAInfinityAugmentation.augmentationIdeal z : A) := by
  simp [fromEnveloping, AInfinityStrictHom.taylor_toAInfinityHom]

theorem fromEnveloping_ι_ofLetter (x : e.toAInfinityAugmentation.augmentationIdeal) :
    e.fromEnveloping (ι R (ReducedTensorWords.ofLetter R _ x)) =
      -(InternalGrading.ofDecomposition 𝒜).koszulTwist 1 (x : A) := by simp

@[simp] theorem comp_fromEnveloping :
    e.comp e.fromEnveloping = e.toAInfinityAugmentation.envelopingAugmentation := by
  rw [fromEnveloping, e.toAInfinityAugmentation.comp_envelopingHomEquiv_eq_iff e]; simp

@[simp] theorem fromEnveloping_comp_toEnveloping :
    e.fromEnveloping.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        e.toAInfinityAugmentation.toEnveloping = AInfinityHom.id _ := by
  rw [← e.toAInfinityAugmentation.envelopingHomEquiv_symm_apply hA, fromEnveloping,
    Equiv.symm_apply_apply]

theorem isQuasiIso_fromEnveloping :
    e.fromEnveloping.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsQuasiIso :=
  e.toAInfinityAugmentation.isQuasiIso_toEnveloping.of_precomp
    (by simp [AInfinityHom.isQuasiIso_id])

/-- The bar--cobar counit `U(A) ⟶ A` of an augmented DG algebra is a quasi-isomorphism. -/
theorem bijective_cohomologyMap_fromEnveloping :
    Function.Bijective e.fromEnveloping.cohomologyMap :=
  (DGAlgHom.bijective_cohomologyMap_iff_isQuasiIso e.fromEnveloping).2 e.isQuasiIso_fromEnveloping

end SingleDGAugmentation

/-- Naturality of the bar--cobar counit under DG algebra morphisms. -/
theorem fromEnveloping_naturality (eA : DGAlgAugmentation hA) (eB : DGAlgAugmentation hB)
    (g : DGAlgHom hA hB) :
    g.comp eA.fromEnveloping =
      eB.fromEnveloping.comp
        (eA.toAInfinityAugmentation.envelopingMap eB.toAInfinityAugmentation
          g.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom
          (AInfinityHom.isStrictlyUnital_iff_of_strictUnit.2 g.isStrictlyUnital_toAInfinityHom)) :=
  (eA.toAInfinityAugmentation.bijective_comp_toEnveloping hB).1 <| Subtype.ext <| by
    simp only [toNonUnitalDGAlgHom_comp, toAInfinityStrictHom_comp, toAInfinityHom_comp,
      AInfinityHom.comp_assoc, fromEnveloping_comp_toEnveloping, AInfinityHom.comp_id,
      AInfinityAlgebra.Augmentation.envelopingMap_comp_toEnveloping]
    rw [← AInfinityHom.comp_assoc, fromEnveloping_comp_toEnveloping, AInfinityHom.id_comp]

end DGAlgAugmentation

end TauCeti
