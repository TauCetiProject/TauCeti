/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SymmetricThree.CharTwo.Simple
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SymmetricThree.CharTwo
import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SymmetricThree.Alternating
import TauCeti.RepresentationTheory.Symmetric.Modular.Three.Alternating
import TauCeti.RingTheory.CompositionSeries.Regular
import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.PGroup

/-!
# The prime-to-two induction subgroup of S₃ over 𝔽₂

The classes induced from cyclic subgroups of odd order form exactly twice the exact
Grothendieck group of `𝔽₂[S₃]`. Induction from `A₃` alone has this image: its two simple
modules are the trivial line and the restriction of the standard plane, and their induced
classes are twice the corresponding simple S₃ classes.

The coefficient field matters. Over 𝔽₂ the standard plane stays simple on restriction to
A₃; over a field containing a primitive cube root of unity it splits into lines.
The proof identifies the regular A₃ class with the sum of these two simple classes,
then uses occurrence in the regular module to show that this list is exhaustive.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
* The simple-class basis `TauCeti.symmetricThreeCharTwoSimpleClassBasis`, the induction
  calculation `TauCeti.indK0_standardRepresentation_comp_alternatingGroup`, and
  `TauCeti.jordanHolderMultiplicity_regular_pos`.
-/

public noncomputable section

open scoped MonoidAlgebra

namespace TauCeti

local notation "k" => ZMod 2
local notation "G" => Equiv.Perm (Fin 3)
local notation "A" => alternatingGroup (Fin 3)
local notation "K₀" => ExactK0 (finiteModulesExactStructure k[G])
local notation "K₀A" => ExactK0 (finiteModulesExactStructure k[A])
local notation "I" => ⨆ (H : Subgroup G) (_ : IsCyclic H ∧ ¬ 2 ∣ Nat.card H),
  AddMonoidHom.range (indK0 k H)

local instance : IsArtinianRing k[A] := IsArtinianRing.of_finite k k[A]

local instance : Module.Finite k[A]
    (Representation.asModule ((standardRepresentation k (Fin 3)).comp
      (alternatingGroup (Fin 3)).subtype)) :=
  Module.Finite.of_restrictScalars_finite k _ _

private noncomputable def alternatingSimpleFamily (b : Bool) : FGModuleCat k[A] :=
  match b with
  | false => FGModuleCat.of k[A] (Representation.trivial k A k).asModule
  | true => FGModuleCat.of k[A]
      (Representation.asModule ((standardRepresentation k (Fin 3)).comp
        (alternatingGroup (Fin 3)).subtype))

private instance alternatingSimpleFamily_simple (b : Bool) :
    IsSimpleModule k[A] (alternatingSimpleFamily b) := by
  cases b
  · exact (Representation.irreducible_iff_isSimpleModule_asModule
      (Representation.trivial k A k)).mp inferInstance
  · exact (Representation.irreducible_iff_isSimpleModule_asModule
      ((standardRepresentation k (Fin 3)).comp (alternatingGroup (Fin 3)).subtype)).mp
      isIrreducible_standardRepresentation_comp_alternatingGroup_zmod_two

private theorem regular_alternating_class :
    (ExactK0.of (FGModuleCat.of k[A] k[A]) : K₀A) =
      ExactK0.of (alternatingSimpleFamily false) +
        ExactK0.of (alternatingSimpleFamily true) := by
  let e : A ≃ Fin 3 := Equiv.ofBijective (fun g ↦ (g : G) 0) (by decide)
  have he : ∀ (g h : A), e (g • h) = g • e h := fun _ _ ↦ rfl
  let : Module.Finite k[A] (Representation.ofMulAction k A A).asModule :=
    Module.Finite.of_restrictScalars_finite k _ _
  have hperm : permK0 k A (Fin 3) =
      resK0 k (alternatingGroup (Fin 3)).subtype (permK0 k G (Fin 3)) := by
    simp only [permK0_def, resK0_of_asModule]
    -- Restriction of a permutation representation retains its basis and composes its action.
    rfl
  calc
    _ = permK0 k A A := by
      rw [permK0_def]
      exact (ExactK0.of_congr
        Representation.ofMulActionSelfAsModuleEquiv.toFGModuleCatIso).symm
    _ = permK0 k A (Fin 3) := permK0_congr k e he
    _ = _ := by
      rw [hperm, permK0_eq_one_add_standard]
      simp [alternatingSimpleFamily, ← exactK0_one_eq_of_trivial]

private theorem alternatingSimpleFamily_exhaustive :
    IsExhaustiveSimpleFamily alternatingSimpleFamily := by
  rw [isExhaustiveSimpleFamily_iff]
  intro M hM
  by_contra! h
  have hzero (b : Bool) :
      jordanHolderCoordinate k[A] M (ExactK0.of (alternatingSimpleFamily b)) = 0 := by
    have := alternatingSimpleFamily_simple b
    exact jordanHolderCoordinate_eq_zero_of_isEmpty_linearEquiv k[A] M
      (T := (alternatingSimpleFamily b : Type)) ⟨fun e ↦ (h b).false e.symm⟩
  have hpos : 0 < jordanHolderCoordinate k[A] M
      (ExactK0.of (FGModuleCat.of k[A] k[A])) := by
    rw [jordanHolderCoordinate_of]
    exact_mod_cast jordanHolderMultiplicity_regular_pos k[A] M
  rw [regular_alternating_class, map_add, hzero, hzero] at hpos
  simp at hpos

private theorem alternatingSimpleFamily_pairwise :
    Pairwise fun b c ↦ IsEmpty ((alternatingSimpleFamily b : Type) ≃ₗ[k[A]]
      alternatingSimpleFamily c) := by
  intro b c hbc
  cases b <;> cases c
  · exact (hbc rfl).elim
  · refine ⟨fun e ↦ ?_⟩
    have he := (Representation.equivOfAsModuleLinearEquiv
      (ρ := Representation.trivial k A k)
      (σ := (standardRepresentation k (Fin 3)).comp (alternatingGroup (Fin 3)).subtype)
      e).toLinearEquiv.finrank_eq
    simp [finrank_augmentationSubrepresentation] at he
  · refine ⟨fun e ↦ ?_⟩
    have he := (Representation.equivOfAsModuleLinearEquiv
      (ρ := (standardRepresentation k (Fin 3)).comp (alternatingGroup (Fin 3)).subtype)
      (σ := Representation.trivial k A k) e).toLinearEquiv.finrank_eq
    simp [finrank_augmentationSubrepresentation] at he
  · exact (hbc rfl).elim

private noncomputable def alternatingSimpleBasis : Module.Basis Bool ℤ K₀A :=
  simpleClassBasis alternatingSimpleFamily alternatingSimpleFamily_pairwise
    alternatingSimpleFamily_exhaustive

private theorem alternatingSimpleBasis_ind (b : Bool) :
    indK0 k A (alternatingSimpleBasis b) =
      2 • symmetricThreeCharTwoSimpleClassBasis k b := by
  rw [alternatingSimpleBasis, simpleClassBasis_apply]
  cases b
  · simp [alternatingSimpleFamily, symmetricThreeCharTwoSimpleClassBasis_apply,
      ← exactK0_one_eq_of_trivial]
  · simp [alternatingSimpleFamily, symmetricThreeCharTwoSimpleClassBasis_apply]

/-- Over 𝔽₂, induction from A₃ has image exactly twice the exact Grothendieck group of S₃.
Equivalently, both integral simple composition multiplicities are even. -/
-- Apply before membership in a homomorphism range expands to an existential.
@[simp↓]
theorem mem_range_indK0_alternating_perm_fin_three_zmod_two_iff (x : K₀) :
    x ∈ (indK0 k A).range ↔ ∃ y : K₀, 2 • y = x := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨∑ b : Bool, alternatingSimpleBasis.repr z b •
      symmetricThreeCharTwoSimpleClassBasis k b, ?_⟩
    conv_rhs => rw [← alternatingSimpleBasis.sum_repr z]
    simp only [map_sum, map_zsmul, alternatingSimpleBasis_ind, Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ ↦ smul_comm _ _ _
  · rintro ⟨y, rfl⟩
    refine ⟨∑ b : Bool, (symmetricThreeCharTwoSimpleClassBasis k).repr y b •
      alternatingSimpleBasis b, ?_⟩
    simp only [map_sum, map_zsmul, alternatingSimpleBasis_ind, ← smul_comm (2 : ℕ),
      ← Finset.smul_sum, Module.Basis.sum_repr]

/-- Over 𝔽₂, induction from A₃ already supplies every class induced from a cyclic
subgroup of odd order in S₃. -/
theorem iSup_range_indK0_cyclic_coprime_perm_fin_three_zmod_two_eq_range_alternating :
    I = (indK0 k A).range := by
  apply le_antisymm
  · refine iSup_le fun H ↦ iSup_le fun hH ↦ ?_
    have hle : H ≤ A := by
      intro g hg
      by_contra h
      have hpow : ∀ g : G, Equiv.Perm.sign g ≠ 1 → g ^ 2 = 1 := by decide
      have hsign : Equiv.Perm.sign g ≠ 1 := h
      have hne : g ≠ 1 := by rintro rfl; simp at hsign
      have horder : orderOf g = 2 := orderOf_eq_prime (hpow g hsign) hne
      exact hH.2 (horder ▸ H.orderOf_dvd_natCard hg)
    have hcard : Nat.card H ∣ 3 := by
      simpa only [card_alternatingGroup_fin_three] using Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hcard with h | h
    · have hbot : H = ⊥ := Subgroup.card_eq_one.mp h
      subst H
      rintro x ⟨y, rfl⟩
      have hy := eq_finrankK0_smul_trivial_of_isPGroup 2
        (IsPGroup.of_subsingleton 2 (⊥ : Subgroup G)) y
      rw [← exactK0_one_eq_of_trivial] at hy
      rw [hy, map_zsmul, indK0_one_bot_eq_two_nsmul_stabilizer_fin_three k 0]
      apply (mem_range_indK0_alternating_perm_fin_three_zmod_two_iff _).mpr
      exact ⟨finrankK0 k k[(⊥ : Subgroup G)] y •
        indK0 k (MulAction.stabilizer G (0 : Fin 3)) 1, (smul_comm _ _ _).symm⟩
    · have hA : H = A := Subgroup.eq_of_le_of_card_ge hle (by
        rw [card_alternatingGroup_fin_three, h])
      rw [hA]
  · have hcyclic : IsCyclic A := isCyclic_of_prime_card (p := 3)
      card_alternatingGroup_fin_three
    exact le_iSup_of_le A (le_iSup_of_le ⟨hcyclic, by
      rw [card_alternatingGroup_fin_three]; decide⟩ le_rfl)

/-- The prime-to-two cyclic induction subgroup of S₃ over 𝔽₂ is precisely `2 · G₀`.
Here multiplication by two is in the integral Grothendieck group, not in the coefficient field. -/
-- Apply before simplification replaces nondivisibility by a remainder test.
@[simp↓]
theorem mem_iSup_range_indK0_cyclic_coprime_perm_fin_three_zmod_two_iff (x : K₀) :
    x ∈ I ↔ ∃ y : K₀, 2 • y = x := by
  rw [iSup_range_indK0_cyclic_coprime_perm_fin_three_zmod_two_eq_range_alternating,
    mem_range_indK0_alternating_perm_fin_three_zmod_two_iff]

end TauCeti
