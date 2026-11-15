/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Bockstein.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Bockstein.Integral
import TauCeti.RepresentationTheory.Homological.ContCohomology.ConnectingMapComparison
import TauCeti.RepresentationTheory.Homological.ContCohomology.DeltaNaturality

/-!
# Cyclic Bocksteins in every degree

The coefficient sequence `0 → ℤ/n → ℤ/n² → ℤ/n → 0` defines the Bockstein on
canonical continuous cohomology of a compact group. The coefficients are lifted to the
universe of the group and carry the trivial action. `cyclicBockstein G 2 i` is the mod-two
Bockstein in degree `i`, using the `ℤ`-linear model of cohomology. Its degree-one comparison
with `explicitBockstein1` crosses the universe lift and recovers the cup-square calculation.

The cyclic Bockstein is the integral Bockstein followed by reduction modulo `n`.
Consequently its square vanishes: the integral connecting map kills the image of
reduction. This argument works for every nonzero modulus, not just for two.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.5.

The construction uses `DiscreteShortExact.delta` and the coefficient maps of
`integralBocksteinShortExact`. The integral comparison uses
`DiscreteShortExact.delta_naturality`, not a second cochain differential; its square-zero
consequence uses `DiscreteShortExact.coeffMap_proj_comp_delta`.
-/

public section

namespace TauCeti

open CategoryTheory ContCohomology TauCeti.ContinuousCohomology

universe u

attribute [local instance 2000] Ring.toAddCommGroup
attribute [local instance] trivialZModAction integralAction integralContinuousSMul
  bocksteinContinuousSMul

section Coefficients

variable (G : Type u) [Monoid G] (n : ℕ) [NeZero n]

/-- The trivial cyclic coefficient sequence, with multiplication by `n` into `ℤ/n²`
and reduction modulo `n`, lifted to the universe of the group. -/
def cyclicBocksteinShortExact :
    DiscreteShortExact G (ULift.{u} (ZMod n)) (ULift.{u} (ZMod (n * n)))
      (ULift.{u} (ZMod n)) where
  incl := (AddEquiv.ulift.symm.toAddMonoidHom.comp (ZMod.mulCastHom n rfl)).comp
    AddEquiv.ulift.toAddMonoidHom
  proj := (AddEquiv.ulift.symm.toAddMonoidHom.comp
    (ZMod.castHom (dvd_mul_right n n) (ZMod n)).toAddMonoidHom).comp
      AddEquiv.ulift.toAddMonoidHom
  incl_equivariant := fun _ _ ↦ rfl
  proj_equivariant := fun _ _ ↦ rfl
  incl_injective := AddEquiv.ulift.symm.injective.comp
    ((ZMod.mulCastHom_injective n rfl (NeZero.ne n)).comp AddEquiv.ulift.injective)
  proj_surjective := AddEquiv.ulift.symm.surjective.comp
    ((ZMod.castHom_surjective (dvd_mul_right n n)).comp AddEquiv.ulift.surjective)
  exact x := by
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (ZMod.exact_mulCastHom_castHom n rfl x.down).1
        (congrArg ULift.down hx)
      exact ⟨ULift.up y, ULift.ext hy⟩
    · rintro ⟨y, rfl⟩
      apply ULift.ext
      exact (ZMod.exact_mulCastHom_castHom n rfl _).2 ⟨y.down, rfl⟩

/-- The cyclic Bockstein inclusion multiplies by the modulus. -/
@[simp]
theorem cyclicBocksteinShortExact_incl_apply (x : ULift.{u} (ZMod n)) :
    (cyclicBocksteinShortExact G n).incl x = ULift.up (ZMod.mulCastHom n rfl x.down) :=
  (rfl)

/-- The cyclic Bockstein projection reduces modulo the modulus. -/
@[simp]
theorem cyclicBocksteinShortExact_proj_apply (x : ULift.{u} (ZMod (n * n))) :
    (cyclicBocksteinShortExact G n).proj x =
      ULift.up (ZMod.castHom (dvd_mul_right n n) (ZMod n) x.down) := (rfl)

end Coefficients

variable (G : Type u) [Group G]

/-- Restricting the cyclic coefficient sequence preserves its multiplication and reduction
maps. -/
@[simp]
theorem cyclicBocksteinShortExact_restrict (n : ℕ) [NeZero n] (U : Subgroup G) :
    (cyclicBocksteinShortExact G n).restrict U = cyclicBocksteinShortExact U n := by
  apply DiscreteShortExact.ext
  · rw [DiscreteShortExact.restrict_incl]
    rfl
  · rw [DiscreteShortExact.restrict_proj]
    rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

local instance cyclicBocksteinContinuousSMul (n : ℕ) : ContinuousSMul G (ULift.{u} (ZMod n)) :=
  ⟨continuous_snd⟩

variable [CompactSpace G] (n : ℕ) [NeZero n]

/-- The Bockstein for trivial `ℤ/n` coefficients in every degree, as the connecting map of
the multiplication-and-reduction sequence. -/
noncomputable def cyclicBockstein (i : ℕ) :
    continuousCohomology i (ofDiscreteModule ℤ G (ULift.{u} (ZMod n))) ⟶
      continuousCohomology (i + 1) (ofDiscreteModule ℤ G (ULift.{u} (ZMod n))) :=
  (cyclicBocksteinShortExact G n).delta i

/-- The cyclic Bockstein is the connecting map of its named coefficient sequence. -/
theorem cyclicBockstein_def (i : ℕ) :
    cyclicBockstein G n i = (cyclicBocksteinShortExact G n).delta i := (rfl)

/-- A cyclic Bockstein vanishes exactly on classes that lift to `ℤ/n²` coefficients. -/
theorem cyclicBockstein_eq_zero_iff (i : ℕ)
    (x : continuousCohomology i (ofDiscreteModule ℤ G (ULift.{u} (ZMod n)))) :
    cyclicBockstein G n i x = 0 ↔
      ∃ y : continuousCohomology i (ofDiscreteModule ℤ G (ULift.{u} (ZMod (n * n)))),
        coeffMap (ofDiscreteModuleMap (cyclicBocksteinShortExact G n).proj.toIntLinearMap
          (cyclicBocksteinShortExact G n).proj_equivariant) i y = x :=
  (cyclicBocksteinShortExact G n).longExact_exact₃ i x

/-- The cyclic Bockstein is the integral Bockstein followed by reduction modulo `n`. -/
theorem cyclicBockstein_eq_integralBockstein_comp_coeffMap (i : ℕ) :
    cyclicBockstein G n i = integralBockstein G n i ≫
      coeffMap (ofDiscreteModuleMap (integralBocksteinShortExact G n).proj.toIntLinearMap
        (integralBocksteinShortExact G n).proj_equivariant) (i + 1) := by
  -- Map the integral sequence to the cyclic sequence by reduction on its first two
  -- terms and the identity on its final term.
  let fA : ULift.{u} ℤ →+[G] ULift.{u} (ZMod n) :=
    { (integralBocksteinShortExact G n).proj with map_smul' := fun _ _ ↦ rfl }
  let fB : ULift.{u} ℤ →+[G] ULift.{u} (ZMod (n * n)) :=
    { (integralBocksteinShortExact G (n * n)).proj with map_smul' := fun _ _ ↦ rfl }
  let fC : ULift.{u} (ZMod n) →+[G] ULift.{u} (ZMod n) :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ ↦ rfl }
  have h := (integralBocksteinShortExact G n).delta_naturality
    (cyclicBocksteinShortExact G n) fA fB fC (fun a ↦ ?_) (fun b ↦ ?_) i
  · have hA : ofDiscreteModuleMap fA.toAddMonoidHom.toIntLinearMap
        (fun g a ↦ map_smul fA g a) =
        ofDiscreteModuleMap (integralBocksteinShortExact G n).proj.toIntLinearMap
          (integralBocksteinShortExact G n).proj_equivariant := by
      ext x
      rfl
    have hC : ofDiscreteModuleMap fC.toAddMonoidHom.toIntLinearMap
        (fun g c ↦ map_smul fC g c) = 𝟙 (ofDiscreteModule ℤ G (ULift.{u} (ZMod n))) := by
      ext x
      rfl
    rw [hA, hC, coeffMap_id, Category.id_comp] at h
    simpa only [cyclicBockstein_def, integralBockstein_def] using h.symm
  · -- The equivariant maps are the projections of the integral sequences; unfold only
    -- their structure coercions before using the public projection formulas.
    change (integralBocksteinShortExact G (n * n)).proj
        ((integralBocksteinShortExact G n).incl a) =
      (cyclicBocksteinShortExact G n).incl ((integralBocksteinShortExact G n).proj a)
    apply ULift.ext
    simp [nsmul_eq_mul, ZMod.mulCastHom_intCast, mul_comm]
  · -- As above, the local equivariant maps have exactly the underlying projection values.
    change (integralBocksteinShortExact G n).proj b =
      (cyclicBocksteinShortExact G n).proj ((integralBocksteinShortExact G (n * n)).proj b)
    apply ULift.ext
    simp

/-- Successive cyclic Bocksteins compose to zero in every degree. -/
@[reassoc (attr := simp)]
theorem cyclicBockstein_comp_cyclicBockstein (i : ℕ) :
    cyclicBockstein G n i ≫ cyclicBockstein G n (i + 1) = 0 := by
  rw [cyclicBockstein_eq_integralBockstein_comp_coeffMap,
    cyclicBockstein_eq_integralBockstein_comp_coeffMap, Category.assoc]
  simp [integralBockstein_def, ← Category.assoc]

/-- The cyclic Bockstein squares to zero on classes. -/
@[simp]
theorem cyclicBockstein_cyclicBockstein (i : ℕ)
    (x : continuousCohomology i (ofDiscreteModule ℤ G (ULift.{u} (ZMod n)))) :
    cyclicBockstein G n (i + 1) (cyclicBockstein G n i x) = 0 :=
  ConcreteCategory.congr_hom (cyclicBockstein_comp_cyclicBockstein G n i) x

/-- The cyclic Bockstein commutes with pullback along continuous homomorphisms of compact
groups, with the identity on the trivial cyclic coefficients. -/
@[reassoc]
theorem cyclicBockstein_map {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] (φ : H →ₜ* G) (i : ℕ) :
    cyclicBockstein G n i ≫ _root_.ContinuousCohomology.map φ
        (ofDiscreteModulePair (φ : H →* G) (AddMonoidHom.id (ULift.{u} (ZMod n))).toIntLinearMap
          (fun _ _ ↦ rfl)) (i + 1) =
      _root_.ContinuousCohomology.map φ
        (ofDiscreteModulePair (φ : H →* G) (AddMonoidHom.id (ULift.{u} (ZMod n))).toIntLinearMap
          (fun _ _ ↦ rfl)) i ≫ cyclicBockstein H n i := by
  rw [cyclicBockstein_def, cyclicBockstein_def]
  exact (cyclicBocksteinShortExact G n).delta_map (cyclicBocksteinShortExact H n) φ
    (AddMonoidHom.id _) (AddMonoidHom.id _) (AddMonoidHom.id _)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) i

/-- Restriction to a compact subgroup commutes with the cyclic Bockstein. -/
@[reassoc]
theorem cyclicBockstein_res (U : Subgroup G) [CompactSpace U] (i : ℕ) :
    cyclicBockstein G n i ≫ res U (ofDiscreteModule ℤ G (ULift.{u} (ZMod n))) (i + 1) =
      res U (ofDiscreteModule ℤ G (ULift.{u} (ZMod n))) i ≫ cyclicBockstein U n i := by
  simpa only [cyclicBockstein_def, cyclicBocksteinShortExact_restrict] using
    (cyclicBocksteinShortExact G n).delta_res U i

/-- Corestriction from an open finite-index subgroup commutes with the cyclic Bockstein. -/
@[reassoc]
theorem cyclicBockstein_corestriction [TotallyDisconnectedSpace G]
    (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G)) (i : ℕ) :
    haveI : CompactSpace U := isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
    corestriction U (ULift.{u} (ZMod n)) hU i ≫ cyclicBockstein G n i =
      cyclicBockstein U n i ≫ corestriction U (ULift.{u} (ZMod n)) hU (i + 1) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
  simpa only [cyclicBockstein_def, cyclicBocksteinShortExact_restrict] using
    ((cyclicBocksteinShortExact G n).delta_corestriction U hU i).symm

/-- In degree zero the cyclic Bockstein vanishes: every invariant cyclic coefficient has
an invariant lift, since all the actions are trivial. -/
@[simp]
theorem cyclicBockstein_zero : cyclicBockstein G n 0 = 0 := by
  apply ConcreteCategory.hom_ext
  intro x
  apply (cyclicBockstein_eq_zero_iff G n 0 x).2
  let S := cyclicBocksteinShortExact G n
  obtain ⟨a, ha⟩ := S.proj_surjective ((explicitH0IsoContinuousCohomology G
    (ULift.{u} (ZMod n))).inv x).val
  let b : H0 G (ULift.{u} (ZMod (n * n))) := ⟨a, fun _ ↦ rfl⟩
  refine ⟨(explicitH0IsoContinuousCohomology G _).hom b, ?_⟩
  rw [← S.ofDiscreteModuleMap_projDistribMulActionHom, explicitH0Iso_coeffMap]
  rw [← (explicitH0IsoContinuousCohomology G _).inv_hom_id_apply x]
  congr 1
  exact Subtype.ext (by
    simpa only [coe_explicitCoeff0, DiscreteShortExact.projDistribMulActionHom_apply] using ha)

/-- In degree one, the canonical cyclic Bockstein is the explicit connecting map of the
same lifted coefficient sequence. -/
theorem cyclicBockstein_one_explicit (x : H1 G (ULift.{u} (ZMod n))) :
    cyclicBockstein G n 1 (explicitH1AddEquivContinuousCohomology G _ x) =
      explicitH2AddEquivContinuousCohomology G _
        ((cyclicBocksteinShortExact G n).explicitDelta1 x) := by
  have h := (cyclicBocksteinShortExact G n).explicitIso_delta1
    ((discreteH1Equiv G _).symm x)
  rw [AddEquiv.apply_symm_apply] at h
  -- The categorical comparison formulas use morphism coercions, while the connecting-map
  -- comparison exposes their continuous-linear-map fields. Align only those coercions.
  change (cyclicBocksteinShortExact G n).delta 1
      ((explicitH1IsoContinuousCohomology G _).hom ((discreteH1Equiv G _).symm x)) =
    (explicitH2IsoContinuousCohomology G _).hom
      ((discreteH2Equiv G _).symm ((cyclicBocksteinShortExact G n).explicitDelta1 x)) at h
  rw [explicitH1IsoContinuousCohomology_hom_apply,
    explicitH2IsoContinuousCohomology_hom_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply] at h
  simpa only [cyclicBockstein_def] using h

/-- After forgetting the universe lift, the degree-one cyclic Bockstein at modulus two
agrees with `explicitBockstein1`, and hence with the existing cup-square calculation. -/
theorem cyclicBockstein_one_mod_two_eq_explicitBockstein1
    (x : continuousCohomology 1 (ofDiscreteModule ℤ G (ULift.{u} (ZMod 2)))) :
    explicitMap2 G (ULift.{u} (ZMod 2)) G (ZMod 2) (ContinuousMonoidHom.id G)
        AddEquiv.ulift.toAddMonoidHom continuous_of_discreteTopology (fun _ _ ↦ rfl)
        ((explicitH2AddEquivContinuousCohomology G _).symm (cyclicBockstein G 2 1 x)) =
      explicitBockstein1 G
        (explicitMap1 G (ULift.{u} (ZMod 2)) G (ZMod 2) (ContinuousMonoidHom.id G)
          AddEquiv.ulift.toAddMonoidHom continuous_of_discreteTopology (fun _ _ ↦ rfl)
          ((explicitH1AddEquivContinuousCohomology G _).symm x)) := by
  obtain ⟨y, rfl⟩ := (explicitH1AddEquivContinuousCohomology G _).surjective x
  rw [cyclicBockstein_one_explicit, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
    explicitBockstein1_def]
  apply (cyclicBocksteinShortExact G 2).explicitDelta1_naturality (bocksteinShortExact G)
    (ContinuousMonoidHom.id G) AddEquiv.ulift.toAddMonoidHom
    AddEquiv.ulift.toAddMonoidHom AddEquiv.ulift.toAddMonoidHom
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ ?_) (fun _ ↦ ?_) y
  · rw [cyclicBocksteinShortExact_incl_apply, bocksteinShortExact_incl]
    rfl
  · rw [cyclicBocksteinShortExact_proj_apply, bocksteinShortExact_proj]
    rfl

end TauCeti
