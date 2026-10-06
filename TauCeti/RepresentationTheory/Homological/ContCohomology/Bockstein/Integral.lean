/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.TrivialAction
public import TauCeti.Data.ZMod.MulCastHom
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.ConnectingMap
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.GroupTheory.Torsion

/-!
# Integral Bockstein maps and finite-order characters

For a compact group and `n ≠ 0`, the connecting map of the trivial coefficient sequence
`0 → ℤ → ℤ → ℤ/n → 0`, with multiplication by `n` followed by reduction, identifies
`H¹(G, ℤ/n)` with the `n`-torsion in `H²(G, ℤ)`. Indeed, a continuous character into the
integers is zero, and the long exact sequence identifies the image with the kernel of
multiplication by `n` on cohomology.

Consequently, for `p ≠ 0`, every `p`-primary class in `H²(G, ℤ)` comes from a finite-order
character.
This is the character interpretation of integral degree-two cohomology used to study
corestriction and the transfer. All coefficients are lifted to the universe of `G`, and
all cohomology groups are Mathlib's canonical continuous cohomology.

The formal construction uses `TauCeti.ContCohomology.DiscreteShortExact.delta` and its long
exact sequence, and the character identification uses
`TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology`.

Compactness is essential for injectivity: for the discrete infinite cyclic group,
`H¹(ℤ, ℤ/n)` is nonzero when `n > 1`, whereas `H²(ℤ, ℤ) = 0`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  the proof of (3.6.4), (i) ⇒ (ii), using the integral connecting maps.
-/

public section

namespace TauCeti

open CategoryTheory ContCohomology _root_.TauCeti.ContinuousCohomology

universe u

attribute [local instance 2000] Ring.toAddCommGroup
attribute [local instance] trivialZModAction

/-- The trivial action on the integers, viewed as `ZMod 0`. -/
local instance integralAction (G : Type u) [Monoid G] : DistribMulAction G ℤ :=
  trivialZModAction 0 G

local instance : IsAddTorsionFree (ULift.{u} ℤ) :=
  Function.Injective.isAddTorsionFree
    (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).toAddMonoidHom ULift.down_injective

section Coefficients

variable (G : Type u) [Monoid G]

/-- The trivial coefficient sequence `0 → ℤ → ℤ → ℤ/n → 0`, with multiplication by `n`
and reduction modulo `n`. The universe lifts make its canonical connecting maps available
over groups in any universe. -/
def integralBocksteinShortExact (n : ℕ) [NeZero n] :
    DiscreteShortExact G (ULift.{u} ℤ) (ULift.{u} ℤ) (ULift.{u} (ZMod n)) where
  incl := nsmulAddMonoidHom n
  proj := (AddEquiv.ulift.symm.toAddMonoidHom.comp (Int.castAddHom (ZMod n))).comp
    AddEquiv.ulift.toAddMonoidHom
  incl_equivariant := fun _ _ ↦ rfl
  proj_equivariant := fun _ _ ↦ rfl
  incl_injective := nsmul_right_injective (NeZero.ne n)
  proj_surjective := AddEquiv.ulift.symm.surjective.comp
    (ZMod.intCast_surjective.comp AddEquiv.ulift.surjective)
  exact x := by
    constructor
    · intro hx
      have hdiv : (n : ℤ) ∣ x.down := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
        (congrArg ULift.down hx)
      obtain ⟨a, ha⟩ := hdiv
      exact ⟨ULift.up a, ULift.ext (by simpa [nsmul_eq_mul] using ha.symm)⟩
    · rintro ⟨a, rfl⟩
      apply ULift.ext
      -- The projection is composed from the lift equivalences; expose its integer value
      -- to use the cast formula for multiplication by the modulus.
      change ((n • a.down : ℤ) : ZMod n) = 0
      simp

/-- The inclusion in the integral coefficient sequence is multiplication by `n`. -/
@[simp]
theorem integralBocksteinShortExact_incl (n : ℕ) [NeZero n] :
    (integralBocksteinShortExact G n).incl = nsmulAddMonoidHom n := (rfl)

/-- The projection in the integral coefficient sequence is reduction modulo `n`. -/
@[simp]
theorem integralBocksteinShortExact_proj_apply (n : ℕ) [NeZero n] (x : ULift.{u} ℤ) :
    (integralBocksteinShortExact G n).proj x = ULift.up (x.down : ZMod n) := (rfl)

end Coefficients

variable (G : Type u) [Group G]

/-- Restricting the integral coefficient sequence preserves its multiplication and reduction
maps. -/
@[simp]
theorem integralBocksteinShortExact_restrict (n : ℕ) [NeZero n] (U : Subgroup G) :
    (integralBocksteinShortExact G n).restrict U = integralBocksteinShortExact U n := by
  apply DiscreteShortExact.ext
  · simp
  · rw [DiscreteShortExact.restrict_proj]
    rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The trivial action on the lifted discrete integers is continuous. -/
local instance integralContinuousSMul : ContinuousSMul G (ULift.{u} ℤ) := ⟨continuous_snd⟩

/-- The trivial action on a lifted cyclic coefficient module is continuous. -/
local instance cyclicContinuousSMul (n : ℕ) : ContinuousSMul G (ULift.{u} (ZMod n)) :=
  ⟨continuous_snd⟩

variable [CompactSpace G]

/-- First continuous cohomology with trivial lifted integer coefficients vanishes for a
compact group. -/
theorem subsingleton_continuousCohomology_one_int :
    Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ G (ULift.{u} ℤ))) := by
  have := subsingleton_H1_of_isAddTorsionFree (G := G) (M := ULift.{u} ℤ) (fun _ _ ↦ rfl)
  exact (explicitH1AddEquivContinuousCohomology G (ULift.{u} ℤ)).symm.injective.subsingleton

/-- The integral Bockstein in degree `i`, defined by the canonical connecting map of
multiplication by `n` followed by reduction modulo `n`. -/
noncomputable def integralBockstein (n : ℕ) [NeZero n] (i : ℕ) :
    continuousCohomology i (ofDiscreteModule ℤ G (ULift.{u} (ZMod n))) ⟶
      continuousCohomology (i + 1) (ofDiscreteModule ℤ G (ULift.{u} ℤ)) :=
  (integralBocksteinShortExact G n).delta i

/-- The integral Bockstein is the connecting map of its named coefficient sequence. -/
theorem integralBockstein_def (n : ℕ) [NeZero n] (i : ℕ) :
    integralBockstein G n i = (integralBocksteinShortExact G n).delta i := (rfl)

/-- The degree-one integral Bockstein is injective: continuous integer-valued characters of a
compact group vanish. -/
theorem integralBockstein_one_injective (n : ℕ) [NeZero n] :
    Function.Injective (integralBockstein G n 1) := by
  have := subsingleton_continuousCohomology_one_int G
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := ((integralBocksteinShortExact G n).longExact_exact₃ 1 x).1 hx
  rw [Subsingleton.elim y 0, _root_.map_zero]

omit [CompactSpace G] in
/-- The coefficient inclusion in the integral sequence acts on canonical cohomology as
multiplication by `n`. -/
theorem coeffMap_integralBocksteinShortExact_incl (n : ℕ) [NeZero n] (i : ℕ) :
    coeffMap (ofDiscreteModuleMap (integralBocksteinShortExact G n).incl.toIntLinearMap
      (integralBocksteinShortExact G n).incl_equivariant) i =
      n • 𝟙 (continuousCohomology i (ofDiscreteModule ℤ G (ULift.{u} ℤ))) := by
  have h : ofDiscreteModuleMap (integralBocksteinShortExact G n).incl.toIntLinearMap
      (integralBocksteinShortExact G n).incl_equivariant =
      n • 𝟙 (ofDiscreteModule ℤ G (ULift.{u} ℤ)) := by
    ext x
    rfl
  rw [h]
  exact (continuousCohomologyFunctor ℤ G i).map_nsmul.trans
    (congrArg (n • ·) ((continuousCohomologyFunctor ℤ G i).map_id _))

/-- A class in integral degree `i + 1` comes from the integral Bockstein exactly when it is
annihilated by `n`. -/
theorem mem_range_integralBockstein_iff (n : ℕ) [NeZero n] (i : ℕ)
    (x : continuousCohomology (i + 1) (ofDiscreteModule ℤ G (ULift.{u} ℤ))) :
    x ∈ Set.range (integralBockstein G n i) ↔ n • x = 0 := by
  have h := (integralBocksteinShortExact G n).longExact_exact₁ i x
  rw [coeffMap_integralBocksteinShortExact_incl] at h
  simpa only [integralBockstein_def, TopModuleCat.hom_nsmul,
    ConcreteCategory.hom_ofHom, smul_apply,
    TopModuleCat.hom_id, ContinuousLinearMap.id_apply] using h.symm

section

variable (n : ℕ) [NeZero n] (i : ℕ)
    (x : continuousCohomology (i + 1) (ofDiscreteModule ℤ G (ULift.{u} ℤ)))

/-- A preimage under the integral Bockstein exists exactly for classes annihilated by `n`. -/
@[simp]
theorem exists_integralBockstein_eq_iff :
    (∃ y, integralBockstein G n i y = x) ↔ n • x = 0 := by
  simpa only [Set.mem_range] using mem_range_integralBockstein_iff G n i x

end

/-- The degree-one integral connecting map identifies `ℤ/n`-valued first cohomology with the
`n`-torsion subgroup of integral second cohomology. -/
noncomputable def integralBocksteinH1Equiv (n : ℕ) [NeZero n] :
    continuousCohomology 1 (ofDiscreteModule ℤ G (ULift.{u} (ZMod n))) ≃+
      (nsmulAddMonoidHom n :
        continuousCohomology 2 (ofDiscreteModule ℤ G (ULift.{u} ℤ)) →+ _).ker :=
  AddEquiv.ofBijective
    ((integralBockstein G n 1).hom.toLinearMap.toAddMonoidHom.codRestrict _ fun x ↦
      (mem_range_integralBockstein_iff G n 1 _).1 ⟨x, rfl⟩)
    ⟨fun _ _ h ↦ integralBockstein_one_injective G n (congrArg Subtype.val h),
      fun x ↦ by
        obtain ⟨y, hy⟩ := (mem_range_integralBockstein_iff G n 1 x).2 x.2
        exact ⟨y, Subtype.ext hy⟩⟩

/-- The torsion equivalence is induced by the named integral connecting map. -/
@[simp]
theorem integralBocksteinH1Equiv_apply (n : ℕ) [NeZero n]
    (x : continuousCohomology 1 (ofDiscreteModule ℤ G (ULift.{u} (ZMod n)))) :
    (integralBocksteinH1Equiv G n x).val = integralBockstein G n 1 x := (rfl)

/-- The inverse torsion equivalence lifts a class to a preimage under the integral Bockstein. -/
@[simp]
theorem integralBocksteinH1Equiv_symm_apply (n : ℕ) [NeZero n]
    (x : (nsmulAddMonoidHom n :
      continuousCohomology 2 (ofDiscreteModule ℤ G (ULift.{u} ℤ)) →+ _).ker) :
    integralBockstein G n 1 ((integralBocksteinH1Equiv G n).symm x) = x.val :=
  congrArg Subtype.val ((integralBocksteinH1Equiv G n).apply_symm_apply x)

/-- The `p`-primary part of integral second cohomology consists exactly of classes of
finite-order characters under the integral connecting maps for powers of `p`. -/
theorem mem_primaryComponent_iff_exists_integralBockstein (p : ℕ) [NeZero p]
    (x : continuousCohomology 2 (ofDiscreteModule ℤ G (ULift.{u} ℤ))) :
    x ∈ AddCommGroup.primaryComponent _ p ↔
      ∃ (k : ℕ) (y : continuousCohomology 1
        (ofDiscreteModule ℤ G (ULift.{u} (ZMod (p ^ k))))),
        integralBockstein G (p ^ k) 1 y = x := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨y, hy⟩ := (mem_range_integralBockstein_iff G (p ^ k) 1 x).2 hk
    exact ⟨k, y, hy⟩
  · rintro ⟨k, y, rfl⟩
    exact ⟨k, (mem_range_integralBockstein_iff G (p ^ k) 1 _).1 ⟨y, rfl⟩⟩

/-- For modulus one the integral Bockstein vanishes, in every degree. -/
@[simp]
theorem integralBockstein_modulus_one (i : ℕ) : integralBockstein G 1 i = 0 := by
  apply ConcreteCategory.hom_ext
  intro x
  have h := (mem_range_integralBockstein_iff G 1 i _).1 ⟨x, rfl⟩
  simpa using h

/-- The integral Bockstein in degree zero vanishes for trivial coefficients. -/
@[simp]
theorem integralBockstein_zero (n : ℕ) [NeZero n] : integralBockstein G n 0 = 0 := by
  have := subsingleton_continuousCohomology_one_int G
  apply ConcreteCategory.hom_ext
  intro x
  exact Subsingleton.elim _ _

/-- Increasing the modulus from `n` to `m = n * k` by multiplication by `k` on cyclic coefficients
preserves the integral connecting class. In particular, the character descriptions of the
`p`-primary part are compatible as the exponent increases. -/
theorem integralBockstein_mulCastHom (n k : ℕ) {m : ℕ} [NeZero n] [NeZero m] (h : n * k = m)
    (i : ℕ) :
    coeffMap (ofDiscreteModuleMap
      (((AddEquiv.ulift.symm.toAddMonoidHom.comp (ZMod.mulCastHom k h)).comp
        AddEquiv.ulift.toAddMonoidHom).toIntLinearMap) (fun _ _ ↦ rfl)) i ≫
      integralBockstein G m i = integralBockstein G n i := by
  subst h
  let fA : ULift.{u} ℤ →+[G] ULift.{u} ℤ :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ ↦ rfl }
  let fB : ULift.{u} ℤ →+[G] ULift.{u} ℤ :=
    { nsmulAddMonoidHom k with map_smul' := fun _ _ ↦ rfl }
  let fC : ULift.{u} (ZMod n) →+[G] ULift.{u} (ZMod (n * k)) :=
    { (AddEquiv.ulift.symm.toAddMonoidHom.comp (ZMod.mulCastHom k rfl)).comp
        AddEquiv.ulift.toAddMonoidHom with map_smul' := fun _ _ ↦ rfl }
  have hincl (a : ULift.{u} ℤ) :
      fB ((integralBocksteinShortExact G n).incl a) =
        (integralBocksteinShortExact G (n * k)).incl (fA a) := by
    -- Both equivariant maps are built from scalar multiplication; read their values.
    change k • (n • a) = (n * k) • a
    rw [mul_comm n k, mul_nsmul]
    exact smul_comm k n a
  have hproj (b : ULift.{u} ℤ) :
      fC ((integralBocksteinShortExact G n).proj b) =
        (integralBocksteinShortExact G (n * k)).proj (fB b) := by
    apply ULift.ext
    -- Read the lifted coefficient map on the underlying integer representative.
    change ZMod.mulCastHom k rfl (b.down : ZMod n) = ((k • b.down : ℤ) : ZMod (n * k))
    simp [mul_comm]
  have h := (integralBocksteinShortExact G n).delta_naturality
    (integralBocksteinShortExact G (n * k)) fA fB fC hincl hproj i
  have hid : ofDiscreteModuleMap fA.toAddMonoidHom.toIntLinearMap
      (fun g a ↦ _root_.map_smul fA g a) = 𝟙 (ofDiscreteModule ℤ G (ULift.{u} ℤ)) := by
    ext a
    rfl
  rw [hid, coeffMap_id, Category.comp_id] at h
  exact h.symm

/-- Restriction to a compact subgroup commutes with the integral Bockstein. -/
@[reassoc]
theorem integralBockstein_res (n : ℕ) [NeZero n] (U : Subgroup G) [CompactSpace U] (i : ℕ) :
    integralBockstein G n i ≫ res U (ofDiscreteModule ℤ G (ULift.{u} ℤ)) (i + 1) =
      res U (ofDiscreteModule ℤ G (ULift.{u} (ZMod n))) i ≫ integralBockstein U n i := by
  simpa only [integralBockstein_def, integralBocksteinShortExact_restrict] using
    (integralBocksteinShortExact G n).delta_res U i

/-- Corestriction from an open finite-index subgroup commutes with the integral Bockstein. -/
@[reassoc]
theorem integralBockstein_corestriction [TotallyDisconnectedSpace G] (n : ℕ) [NeZero n]
    (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G)) (i : ℕ) :
    haveI : CompactSpace U := isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
    corestriction U (ULift.{u} (ZMod n)) hU i ≫ integralBockstein G n i =
      integralBockstein U n i ≫ corestriction U (ULift.{u} ℤ) hU (i + 1) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
  simpa only [integralBockstein_def, integralBocksteinShortExact_restrict] using
    ((integralBocksteinShortExact G n).delta_corestriction U hU i).symm

/-- A nontrivial finite cyclic group has nonzero integral second continuous cohomology:
the integral Bockstein of its identity character is nonzero. -/
theorem nontrivial_continuousCohomology_two_int_cyclic (n : ℕ) [NeZero n]
    [Nontrivial (ZMod n)] :
    Nontrivial (continuousCohomology 2
      (ofDiscreteModule ℤ (Multiplicative (ULift.{u} (ZMod n))) (ULift.{u} ℤ))) := by
  let C := Multiplicative (ULift.{u} (ZMod n))
  let e := (H1EquivOfSmulEqSelf (G := C) (M := ULift.{u} (ZMod n))
    (fun _ _ ↦ rfl)).symm.trans
      (explicitH1AddEquivContinuousCohomology C (ULift.{u} (ZMod n)))
  let c := e (Additive.ofMul (ContinuousMonoidHom.id C))
  have hc : c ≠ 0 := by
    intro h
    have hid := e.injective (h.trans (_root_.map_zero e).symm)
    have hval := DFunLike.congr_fun (congrArg Additive.toMul hid)
      (Multiplicative.ofAdd (ULift.up (1 : ZMod n)))
    exact one_ne_zero (congrArg (fun x : C ↦ (Multiplicative.toAdd x).down) hval)
  have hδ : integralBockstein C n 1 c ≠ 0 :=
    fun h ↦ hc (integralBockstein_one_injective C n (h.trans (_root_.map_zero _).symm))
  exact ⟨⟨_, _, hδ⟩⟩

end TauCeti
