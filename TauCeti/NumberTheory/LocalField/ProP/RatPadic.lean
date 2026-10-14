/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.OddDegree
public import TauCeti.NumberTheory.LocalField.ProP.Marked
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.D0.Basic

/-!
# The pro-`2` Galois group of `ℚ₂`

The absolute Galois group of `ℚ₂` has maximal pro-`2` quotient isomorphic to the standard
dyadic Demushkin group `D₀`.
-/

public section

namespace TauCeti

/-- `ℚ₂` contains the primitive square root of unity `-1`. -/
theorem ratPadicTwo_hasPrimitiveRoot : ∃ ζ : ℚ_[2], IsPrimitiveRoot ζ 2 :=
  ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩

/-- `ℚ₂` contains no primitive fourth root of unity, since its cyclotomic character is
surjective while a primitive fourth root would force its image into `1 + 4ℤ₂`. -/
theorem not_exists_isPrimitiveRoot_four_ratPadic :
    ¬ ∃ ζ : ℚ_[2], IsPrimitiveRoot ζ 4 := by
  intro hζ
  have hle : (localCyclotomicCharacter 2 ℚ_[2]).range ≤ unitsPrincipal 2 2 :=
    range_localCyclotomicCharacter_le_unitsPrincipal (by simpa using hζ)
  have htop : (-1 : ℤ_[2]ˣ) ∈ (localCyclotomicCharacter 2 ℚ_[2]).range := by
    rw [range_localCyclotomicCharacter_ratPadic 2]
    exact Subgroup.mem_top _
  have hneg := hle htop
  have hcontra : 2 ≤ 1 := neg_one_mem_unitsPrincipal_two_iff.mp hneg
  omega

/-- The group of `2`-power roots of unity in `ℚ₂` has order two. -/
theorem localRootOfUnityOrder_two_ratPadic :
    localRootOfUnityOrder 2 ℚ_[2]
      (finite_pPowerRootsOfUnity (p := 2) (K := ℚ_[2]) (by norm_num)) = 2 := by
  apply not_not.mp
  intro hne
  exact not_exists_isPrimitiveRoot_four_ratPadic
    ((localRootOfUnityOrder_ne_two_iff (by norm_num)).mp hne)

/-- `ℚ₂` is in the odd-degree dyadic case: its root-of-unity order is two and its degree is one. -/
theorem isDyadicOddCase_ratPadic : IsDyadicOddCase ℚ_[2] :=
  IsDyadicOddCase.mk ℚ_[2] localRootOfUnityOrder_two_ratPadic (by
    rw [Module.finrank_self]
    decide)

/-- **The maximal pro-`2` quotient of `G_{ℚ₂}` is `D₀`.** -/
theorem absoluteGaloisGroupProP_two_ratPadic :
    Nonempty (absoluteGaloisGroupProP 2 ℚ_[2] ≃ₜ* demushkinD0) := by
  obtain ⟨eWord, _, _, _⟩ :=
    absoluteGaloisGroupProP_two_marked_of_degree_odd ℚ_[2]
      ratPadicTwo_hasPrimitiveRoot (by rw [Module.finrank_self]; decide)
  have hrank : Module.finrank ℚ_[2] ℚ_[2] + 2 = 3 := by rw [Module.finrank_self]
  let eFin3 :
      absoluteGaloisGroupProP 2 ℚ_[2] ≃ₜ*
        presentedProP 2 (Fin 3) {demushkinWordTwoOdd 2 3 (freeProPGen 2 3)} := by
    rw [← hrank]
    exact eWord
  have hclosure :
      (Subgroup.normalClosure {demushkinWordTwoOdd 2 3 (freeProPGen 2 3)}).topologicalClosure =
        (Subgroup.normalClosure {d0Relator}).topologicalClosure := by
    rw [← d0Relator_eq_demushkinWordTwoOdd]
  let ePresentation :
      presentedProP 2 (Fin 3) {demushkinWordTwoOdd 2 3 (freeProPGen 2 3)} ≃ₜ* demushkinD0 :=
    presentedProP.congrOfClosureEq hclosure
  exact ⟨eFin3.trans ePresentation⟩

end TauCeti
