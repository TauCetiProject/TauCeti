/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.GaugeModuli.RelationModel.Basic
public import TauCeti.RepresentationTheory.SU2.BinaryDihedral
import TauCeti.Analysis.Matrix.UnitaryGroup.TwistedCommutator
import TauCeti.RepresentationTheory.SU2.Adjoint
import TauCeti.Topology.Algebra.GroupAction.Transitive

/-!
# Genus-one coprime `SU(r)` moduli and twisted commutator normal form

Let `ζ : ℂ` be a primitive `r`-th root of unity. At genus one, the twisted relation
`⁅A, B⁆ = ζ • 1` in `SU(r)` is equivalent to the Weyl commutation relation `A * B = ζ • (B * A)`
(`Matrix.coe_commutatorElement_eq_smul_one_iff`). By
`TauCeti.Analysis.Matrix.UnitaryGroup.TwistedCommutator`, this relation admits a solution in
`SU(r)` (`Matrix.exists_coe_commutatorElement_eq_smul_one`), and any two solutions in `SU(r)` are
simultaneously `SU(r)`-conjugate (`Matrix.exists_conj_eq_of_coe_commutatorElement_eq_smul_one`).
Consequently, the genus-one representation model `relationModuli r ζ 1` is a single point
(`TauCeti.GaugeModuli.relationModuli_genus_one`), hence simply connected, and the induced
`PSU(r)` action identifies `PSU(r)` homeomorphically with `relationSet r ζ 1`
(`TauCeti.GaugeModuli.psuOrbitHomeomorphGenusOne`).

As immediate consequences we also deduce nonemptiness of `relationSet r ζ g` and
`relationModuli r ζ g` for every positive genus `g ≥ 1`, triviality of the central-twist
`H¹(T²; μ_r)` action at genus one (`TauCeti.GaugeModuli.centerTwist_smul_relationModuli_genus_one`),
and hence non-freeness of the central-twist action for every `r ≥ 2` and primitive `ζ`
(`TauCeti.GaugeModuli.exists_ne_one_centerTwist_smul_eq_self_genus_one`). In contrast to the
coprime case `r = 2, ζ = -1` (whose relation set is nonempty by
`TauCeti.relationSet_two_neg_one_one_nonempty` and whose moduli is a point), at the non-coprime
parameter `r = 2`, `ζ = 1`, the moduli `relationModuli 2 1 1` is not a subsingleton
(`TauCeti.GaugeModuli.not_subsingleton_relationModuli_two_one_one`) and the `SU(2)` action admits
non-central stabilizers
(`TauCeti.GaugeModuli.exists_notMem_center_conjAct_smul_eq_self_relationSet_two_one`).

## Main definitions

* `TauCeti.GaugeModuli.psuOrbitHomeomorphGenusOne`: for a primitive `r`-th root of unity `ζ`
  and any basepoint `x₀ : relationSet r ζ 1`, the orbit homeomorphism
  `PSU(r) ≃ₜ relationSet r ζ 1`.

## Main results

* `TauCeti.GaugeModuli.nonempty_relationSet_genus_one` and
  `TauCeti.GaugeModuli.relationModuli_genus_one`: existence and uniqueness up to simultaneous
  `SU(r)`-conjugation of a solution to `⁅A, B⁆ = ζ • 1`.
* `TauCeti.GaugeModuli.simplyConnectedSpace_relationModuli_genus_one`: simple connectivity of the
  genus-one moduli.
* `TauCeti.GaugeModuli.nonempty_relationSet_of_pos` and
  `TauCeti.GaugeModuli.nonempty_relationModuli_of_pos`: nonemptiness of the relation set and moduli
  for every genus `g ≥ 1`.
* `TauCeti.GaugeModuli.centerTwist_smul_relationModuli_genus_one` and
  `TauCeti.GaugeModuli.exists_ne_one_centerTwist_smul_eq_self_genus_one`: the central-twist action
  is trivial at genus one, hence not free for any `r ≥ 2` and primitive `ζ`.
* `TauCeti.GaugeModuli.exists_notMem_center_conjAct_smul_eq_self_relationSet_two_one` and
  `TauCeti.GaugeModuli.not_subsingleton_relationModuli_two_one_one`: explicit rank-two checks
  for the non-coprime contrast `ζ = 1`.

## References

* Katrin Wehrheim and Chris T. Woodward, *Floer field theory for coprime rank and degree*,
  arXiv:1601.04924, §3 (Theorem 3.3.3(c) and Remark 3.3.7).
* Aliakbar Daemi, Kenji Fukaya, and Maksim Lipyanskiy, *Lagrangians, SO(3)-instantons and the
  Atiyah–Floer conjecture*, arXiv:2109.07032, Remark 2.2 and Lemma 2.43.
-/

public section

open Matrix Matrix.specialUnitaryGroup
open scoped commutatorElement

namespace TauCeti

namespace GaugeModuli

section GenusOneTheorems

/-- For every primitive `r`-th root of unity `ζ`, the genus-one twisted relation set
`relationSet r ζ 1` is nonempty. -/
theorem nonempty_relationSet_genus_one (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) :
    Nonempty (relationSet r ζ 1) := by
  obtain ⟨A, B, hAB⟩ :=
    Matrix.exists_coe_commutatorElement_eq_smul_one (n := Fin r) (by simpa using hζ)
  exact ⟨⟨fun _ => (A, B), by simpa [mem_relationSet_one_iff] using hAB⟩⟩

/-- **Genus-one representation model.** For a primitive `r`-th root of unity `ζ`, the twisted
relation `⁅A, B⁆ = ζ • 1` has a solution in `SU(r)`, unique up to simultaneous `SU(r)`-conjugation,
so the genus-one moduli space `relationModuli r ζ 1` is a single point. -/
theorem relationModuli_genus_one (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) :
    Nonempty (relationModuli r ζ 1) ∧ Subsingleton (relationModuli r ζ 1) := by
  obtain ⟨x⟩ := nonempty_relationSet_genus_one r ζ hζ
  refine ⟨⟨Quotient.mk _ x⟩, (MulAction.pretransitive_iff_subsingleton_quotient
    (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ 1)).mp ⟨fun y z => ?_⟩⟩
  obtain ⟨g, hg₁, hg₂⟩ := Matrix.exists_conj_eq_of_coe_commutatorElement_eq_smul_one
    (by simpa using hζ) (mem_relationSet_one_iff.mp y.property)
    (mem_relationSet_one_iff.mp z.property)
  refine ⟨ConjAct.toConjAct g, Subtype.ext <| funext fun j => ?_⟩
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simpa [ConjAct.smul_def, mul_assoc] using Prod.ext hg₁ hg₂

/-- At genus one, for a primitive `r`-th root of unity `ζ`, `relationModuli r ζ 1` is simply
connected. -/
theorem simplyConnectedSpace_relationModuli_genus_one (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) :
    SimplyConnectedSpace (relationModuli r ζ 1) := by
  -- `SimplyConnectedSpace.ofContractible` consumes both `Nonempty` and `Subsingleton` via
  -- Mathlib's `ContractibleSpace` instance.
  have h := relationModuli_genus_one r ζ hζ
  have : Nonempty (relationModuli r ζ 1) := h.1
  have : Subsingleton (relationModuli r ζ 1) := h.2
  exact SimplyConnectedSpace.ofContractible _

/-- At genus one, the `PSU(r)` action on `relationSet r ζ 1` is pretransitive. -/
private theorem isPretransitive_psu_relationSet_genus_one {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) :
    MulAction.IsPretransitive (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range (relationSet r ζ 1) := by
  have : MulAction.IsPretransitive (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationSet r ζ 1) :=
    (MulAction.pretransitive_iff_subsingleton_quotient _ _).mpr
      (relationModuli_genus_one r ζ hζ).2
  refine ⟨fun x y => ?_⟩
  obtain ⟨u, hu⟩ :=
    MulAction.exists_smul_eq (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) x y
  exact ⟨toPSL.rangeRestrict (ConjAct.ofConjAct u), by
    simpa [toPSL_rangeRestrict_smul_relationSet] using hu⟩

/-- **Genus-one orbit homeomorphism.** For a primitive `r`-th root of unity `ζ` and any basepoint
`x₀ : relationSet r ζ 1`, the induced `PSU(r)` action induces a homeomorphism
`PSU(r) ≃ₜ relationSet r ζ 1`. -/
noncomputable def psuOrbitHomeomorphGenusOne {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (x₀ : relationSet r ζ 1) :
    (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range ≃ₜ relationSet r ζ 1 :=
  letI : MulAction.IsPretransitive (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range (relationSet r ζ 1) :=
    isPretransitive_psu_relationSet_genus_one hζ
  have htriv : ∀ ⦃p q : (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range⦄,
      QuotientGroup.leftRel (MulAction.stabilizer _ x₀) p q → p = q := by
    intro p q hpq
    rw [QuotientGroup.leftRel_apply, stabilizer_psu_relationSet_eq_bot hζ x₀,
      Subgroup.mem_bot, inv_mul_eq_one] at hpq
    exact hpq
  (Homeomorph.quotientTrivial (QuotientGroup.leftRel (MulAction.stabilizer _ x₀)) htriv).symm.trans
    (TauCeti.quotientStabilizerHomeomorph _ x₀ (continuous_id.smul continuous_const))

/-- The genus-one orbit homeomorphism evaluates to the `PSU(r)` action on `x₀`. -/
@[simp]
theorem psuOrbitHomeomorphGenusOne_apply {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (x₀ : relationSet r ζ 1)
    (p : (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range) :
    psuOrbitHomeomorphGenusOne hζ x₀ p = p • x₀ := by
  have := isPretransitive_psu_relationSet_genus_one hζ
  dsimp only [psuOrbitHomeomorphGenusOne, Homeomorph.trans_apply,
    Homeomorph.quotientTrivial_symm_apply]
  exact TauCeti.quotientStabilizerHomeomorph_mk _ x₀ (continuous_id.smul continuous_const) p

/-- For every positive genus `g ≥ 1` and primitive `r`-th root of unity `ζ`, the twisted relation
set `relationSet r ζ g` is nonempty. -/
theorem nonempty_relationSet_of_pos (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (g : ℕ) (hg : 1 ≤ g) : Nonempty (relationSet r ζ g) := by
  obtain ⟨g', rfl⟩ := Nat.exists_eq_add_of_le' hg
  obtain ⟨⟨x₁, hx₁⟩⟩ := nonempty_relationSet_genus_one r ζ hζ
  let tuple : Fin (g' + 1) →
      Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ :=
    Fin.cons (x₁ 0) (fun _ : Fin g' => (1, 1))
  refine ⟨⟨tuple, ?_⟩⟩
  rw [mem_relationSet]
  have hprod : (List.ofFn fun j : Fin (g' + 1) => ⁅(tuple j).1, (tuple j).2⁆).prod =
      ⁅(x₁ 0).1, (x₁ 0).2⁆ := by
    rw [List.ofFn_succ, List.prod_cons]
    simp [tuple, List.ofFn_const]
  rw [hprod]
  exact mem_relationSet_one_iff.mp hx₁

/-- For every positive genus `g ≥ 1` and primitive `r`-th root of unity `ζ`, the representation
model `relationModuli r ζ g` is nonempty. -/
theorem nonempty_relationModuli_of_pos (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (g : ℕ) (hg : 1 ≤ g) : Nonempty (relationModuli r ζ g) := by
  obtain ⟨x⟩ := nonempty_relationSet_of_pos r ζ hζ g hg
  exact ⟨Quotient.mk _ x⟩

/-- At genus one, the central-twist `H¹(T²; μ_r)` action on `relationModuli r ζ 1` is trivial. -/
theorem centerTwist_smul_relationModuli_genus_one (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (ε : Fin 1 → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (q : relationModuli r ζ 1) : ε • q = q := by
  have := (relationModuli_genus_one r ζ hζ).2
  exact Subsingleton.elim _ _

/-- For every `r ≥ 2` and primitive `r`-th root of unity `ζ`, the central-twist `H¹(T²; μ_r)`
action on `relationModuli r ζ 1` is not free: the nontrivial twist `(ζ • 1, 1)` fixes the unique
point of `relationModuli r ζ 1`. -/
theorem exists_ne_one_centerTwist_smul_eq_self_genus_one {r : ℕ} (hr : 2 ≤ r) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) :
    ∃ (ε : Fin 1 → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (q : relationModuli r ζ 1), ε ≠ 1 ∧ ε • q = q := by
  let z : Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) :=
    Matrix.specialUnitaryGroup.scalarCenter (n := Fin r) (by simpa using hζ.pow_eq_one)
  let ε : Fin 1 → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) := fun _ => (z, 1)
  obtain ⟨q⟩ := nonempty_relationModuli_of_pos r ζ hζ 1 le_rfl
  refine ⟨ε, q, ?_, centerTwist_smul_relationModuli_genus_one r ζ hζ ε q⟩
  intro h
  have h0 : z = 1 := congrArg Prod.fst (congrFun h 0)
  have hval := congr_fun₂ (congrArg
    (fun c : Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) =>
      ((c : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) h0)
    ⟨0, by omega⟩ ⟨0, by omega⟩
  have hζ1 : ζ = 1 := by
    simpa [z, Matrix.specialUnitaryGroup.coe_scalarCenter, Matrix.scalar_apply] using hval
  exact hζ.ne_one (by omega) hζ1

end GenusOneTheorems

section RankTwoChecks

/-- At the non-coprime parameter `r = 2`, `ζ = 1`, the simultaneous `SU(2)`-conjugation action on
`relationSet 2 1 g` admits non-central stabilizers (for example
`TauCeti.SU2.binaryDihedralRotation 2` fixes the trivial tuple `1`). -/
theorem exists_notMem_center_conjAct_smul_eq_self_relationSet_two_one (g : ℕ) :
    ∃ (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) (x : relationSet 2 1 g),
      u ∉ Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
        ConjAct.toConjAct u • x = x := by
  refine ⟨TauCeti.SU2.binaryDihedralRotation 2, ⟨1, one_mem_relationSet 2 g⟩, ?_,
    Subtype.ext (smul_one _)⟩
  rw [TauCeti.SU2.mem_center_iff]
  intro hmem
  refine TauCeti.SU2.binaryDihedralRotation_pow_self_ne_one 2 ?_
  rcases hmem with h | h <;> exact Subtype.ext (by simp [sq, Submonoid.coe_mul, h])

/-- At the non-coprime parameter `r = 2`, `ζ = 1`, `g = 1`, the moduli space `relationModuli 2 1 1`
is not a subsingleton (distinguishing the classes of `(1, 1)` and
`(TauCeti.SU2.binaryDihedralRotation 2, 1)`). -/
theorem not_subsingleton_relationModuli_two_one_one : ¬ Subsingleton (relationModuli 2 1 1) := by
  intro hsub
  let x₁ : relationSet 2 1 1 := ⟨1, one_mem_relationSet 2 1⟩
  let x₂ : relationSet 2 1 1 := ⟨fun _ => (TauCeti.SU2.binaryDihedralRotation 2, 1), by
    rw [mem_relationSet_one_iff]
    simp⟩
  have heq : (Quotient.mk _ x₁ : relationModuli 2 1 1) = Quotient.mk _ x₂ :=
    Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := (quotient_mk_relationModuli_eq_iff x₁ x₂).mp heq
  have h0 : ConjAct.toConjAct u • (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) =
      TauCeti.SU2.binaryDihedralRotation 2 :=
    congrArg Prod.fst (congrFun hu 0)
  rw [smul_one] at h0
  refine TauCeti.SU2.binaryDihedralRotation_pow_self_ne_one 2 ?_
  rw [← h0, one_pow]

end RankTwoChecks

end GaugeModuli

end TauCeti
