/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Block
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.ResidueReduction
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# The last level and its character for a theta-lift chain

On the final definite unitary group, impose identity reduction at the chosen places and
block upper triangular reduction at the twist places. The character is the product of the
residue characters of the diagonal block determinants. Only the newly added blocks enter
this product: supply them as a finite set, omitting the initial block. The character is
trivial on the principal level of the product of all the chosen and twist primes.

The level and character follow `New.Data.lastLevel` and `New.Data.lastLevelChar` in
`grh/src/New/UpperBound/Objects/RowChain.lean` of [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/UpperBound/Objects/RowChain.lean
-/

public noncomputable section

open IsDedekindDomain Matrix NumberField
open TauCeti.integralAdelicUnitaryGroup (residue residue_eq_one_of_mem_principalUnitaryLevel)

namespace TauCeti.ThetaLift

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]

/-- The last level in a theta-lift chain. Its points are integral, with identity reduction
at the chosen places `C` and block upper triangular reduction for `b` at the twist places `Q`. -/
def lastLevel (C Q : Finset (HeightOneSpectrum (𝓞 E))) (b : ι → β) :
    Subgroup (finiteAdelicUnitaryGroup E ι) :=
  ((⨅ w : C, (residue w.val).ker) ⊓
    (⨅ w : Q, (blockTriangularGroup _ b).comap (residue w.val))).map
      (integralAdelicUnitaryGroup E ι).subtype

/-- Membership in the last level is equivalent to the two conditions on the reductions of the
integral point. -/
theorem mem_lastLevel_iff {C Q : Finset (HeightOneSpectrum (𝓞 E))} {b : ι → β}
    {g : finiteAdelicUnitaryGroup E ι} :
    g ∈ lastLevel C Q b ↔ ∃ h : integralAdelicUnitaryGroup E ι,
      (h : finiteAdelicUnitaryGroup E ι) = g ∧ (∀ w ∈ C, residue w h = 1) ∧
      ∀ w ∈ Q, (residue w h).val.BlockTriangular b := by
  simp only [lastLevel, Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_iInf,
    MonoidHom.mem_ker, Subgroup.mem_comap, mem_blockTriangularGroup_iff, Subgroup.coe_subtype,
    Subtype.forall]
  exact exists_congr fun h ↦ and_comm

/-- For an integral point, no choice of a lift to integral coordinates is needed to test
membership in the last level. -/
@[simp] theorem coe_mem_lastLevel_iff {C Q : Finset (HeightOneSpectrum (𝓞 E))} {b : ι → β}
    {g : integralAdelicUnitaryGroup E ι} :
    (g : finiteAdelicUnitaryGroup E ι) ∈ lastLevel C Q b ↔
      (∀ w ∈ C, residue w g = 1) ∧
      ∀ w ∈ Q, (residue w g).val.BlockTriangular b := by
  simp only [mem_lastLevel_iff, Subtype.coe_inj, exists_eq_left]

/-- The last level is contained in the integral subgroup. -/
theorem lastLevel_le_integral (C Q : Finset (HeightOneSpectrum (𝓞 E))) (b : ι → β) :
    lastLevel C Q b ≤ integralAdelicUnitaryGroup E ι := by
  rintro g hg
  obtain ⟨h, rfl, _⟩ := mem_lastLevel_iff.mp hg
  exact h.property

/-- Any principal level divisible by each chosen and twist prime is contained in the last level. -/
theorem principalUnitaryLevel_le_lastLevel {C Q : Finset (HeightOneSpectrum (𝓞 E))}
    (b : ι → β) {N : Ideal (𝓞 E)} (hC : ∀ w ∈ C, N ≤ w.asIdeal)
    (hQ : ∀ w ∈ Q, N ≤ w.asIdeal) : principalUnitaryLevel E ι N ≤ lastLevel C Q b := by
  intro g hg
  let h : integralAdelicUnitaryGroup E ι :=
    ⟨g, principalUnitaryLevel_le_integralAdelicUnitaryGroup E ι N hg⟩
  refine mem_lastLevel_iff.mpr ⟨h, rfl, fun w hw ↦
    residue_eq_one_of_mem_principalUnitaryLevel w (hC w hw) hg, fun w hw ↦ ?_⟩
  rw [residue_eq_one_of_mem_principalUnitaryLevel w (hQ w hw) (g := h) hg,
    GeneralLinearGroup.coe_one]
  exact blockTriangular_one

/-- The last level is an open subgroup of the integral adelic unitary group. -/
theorem isUnitaryLevel_lastLevel (C Q : Finset (HeightOneSpectrum (𝓞 E))) (b : ι → β) :
    IsUnitaryLevel (lastLevel C Q b) := by
  classical
  let N := ∏ w ∈ C ∪ Q, HeightOneSpectrum.asIdeal w
  have hN : N ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun w _ ↦ (Ideal.zero_eq_bot (R := 𝓞 E)) ▸ w.ne_bot
  have hle (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ C ∪ Q) : N ≤ w.asIdeal :=
    Ideal.prod_le_inf.trans (Finset.inf_le (f := HeightOneSpectrum.asIdeal) hw)
  exact ⟨lastLevel_le_integral C Q b, Subgroup.isOpen_mono
    (principalUnitaryLevel_le_lastLevel b (fun w hw ↦ hle w (Finset.mem_union_left _ hw))
      (fun w hw ↦ hle w (Finset.mem_union_right _ hw))) (isOpen_principalUnitaryLevel hN)⟩

/-- At a twist place, reduction of a last-level point lands in the block upper triangular
subgroup. -/
def lastLevelResidue {C Q : Finset (HeightOneSpectrum (𝓞 E))} {b : ι → β} (w : Q) :
    lastLevel C Q b →* blockTriangularGroup (IsLocalRing.ResidueField
      (w.val.adicCompletionIntegers E)) b :=
  ((residue w.val).comp (Subgroup.inclusion (lastLevel_le_integral C Q b))).codRestrict _ fun g ↦
    mem_blockTriangularGroup_iff.mpr ((coe_mem_lastLevel_iff.mp g.property).2 w.val w.property)

/-- The underlying general linear matrix is the ordinary residue matrix at the twist place. -/
@[simp] theorem coe_lastLevelResidue_apply {C Q : Finset (HeightOneSpectrum (𝓞 E))} {b : ι → β}
    (w : Q) (g : lastLevel C Q b) : (lastLevelResidue w g : GL ι _) =
      residue w.val (Subgroup.inclusion (lastLevel_le_integral C Q b) g) := (rfl)

/-- The last-level character evaluates the supplied residue characters on the diagonal block
unit determinants. Only blocks in `s` are used. Chosen places can be omitted from the product
because their reductions are the identity. -/
def lastLevelChar {A : Type*} [CommMonoid A]
    {C Q : Finset (HeightOneSpectrum (𝓞 E))} {b : ι → β} (s : Finset β)
    (χ : ∀ w : Q, s → (IsLocalRing.ResidueField (w.val.adicCompletionIntegers E))ˣ →* A) :
    lastLevel C Q b →* A :=
  ∏ w : Q, ∏ a : s,
    (χ w a).comp (GeneralLinearGroup.det.comp
      ((BlockTriangularGroup.diagBlock b a.val).comp (lastLevelResidue w)))

/-- The value of the last-level character is a product over the twist places and selected blocks. -/
theorem lastLevelChar_apply {A : Type*} [CommMonoid A]
    {C Q : Finset (HeightOneSpectrum (𝓞 E))} {b : ι → β} (s : Finset β)
    (χ : ∀ w : Q, s → (IsLocalRing.ResidueField (w.val.adicCompletionIntegers E))ˣ →* A)
    (g : lastLevel C Q b) :
    lastLevelChar s χ g = ∏ w : Q, ∏ a : s, χ w a
      (GeneralLinearGroup.det (BlockTriangularGroup.diagBlock b a.val (lastLevelResidue w g))) := by
  simp only [lastLevelChar, MonoidHom.coe_finsetProd, Finset.prod_apply, MonoidHom.comp_apply]

/-- With no twist places, the last-level character is trivial. -/
@[simp] theorem lastLevelChar_empty_twist {A : Type*} [CommMonoid A]
    {C : Finset (HeightOneSpectrum (𝓞 E))} {b : ι → β} (s : Finset β)
    (χ : ∀ w : (∅ : Finset (HeightOneSpectrum (𝓞 E))),
      s → (IsLocalRing.ResidueField (w.val.adicCompletionIntegers E))ˣ →* A) :
    lastLevelChar (C := C) (b := b) s χ = 1 := by
  ext g
  simp [lastLevelChar_apply]

/-- A last-level point that is principal at every twist prime has character value one. -/
theorem lastLevelChar_eq_one_of_mem_principalUnitaryLevel {A : Type*} [CommMonoid A]
    {C Q : Finset (HeightOneSpectrum (𝓞 E))} {b : ι → β} (s : Finset β)
    (χ : ∀ w : Q, s → (IsLocalRing.ResidueField (w.val.adicCompletionIntegers E))ˣ →* A)
    {N : Ideal (𝓞 E)} (hN : ∀ w ∈ Q, N ≤ w.asIdeal) (g : lastLevel C Q b)
    (hg : (g : finiteAdelicUnitaryGroup E ι) ∈ principalUnitaryLevel E ι N) :
    lastLevelChar s χ g = 1 := by
  have hw (w : Q) : lastLevelResidue w g = 1 := by
    apply Subtype.ext
    rw [coe_lastLevelResidue_apply, OneMemClass.coe_one]
    exact residue_eq_one_of_mem_principalUnitaryLevel w.val (hN w.val w.property) hg
  simp [lastLevelChar_apply, hw]

end TauCeti.ThetaLift
