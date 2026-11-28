/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Matrix.SurfaceRelationModuli.Basic
import TauCeti.Analysis.Matrix.UnitaryGroup.SpecialUnitary
import TauCeti.Analysis.Matrix.UnitaryGroup.TwistedCommutator
import TauCeti.GroupTheory.GroupAction.ConjAct

/-!
# Genus-one twisted `SU(r)` surface commutator relation moduli

This file studies the genus-one (`g = 1`) twisted `SU(r)` commutator relation moduli
`TauCeti.relationModuli r ζ 1`, proving nonemptiness whenever `ζ ^ r = 1` via
`Matrix.exists_coe_commutatorElement_eq_smul_one`, uniqueness up to `SU(r)`-conjugation in the
coprime case `IsPrimitiveRoot ζ r` via `Matrix.exists_conj_eq_of_coe_commutatorElement_eq_smul_one`,
and genus-one consequences and non-coprime counterexamples.

## Main definitions

* `TauCeti.uniqueRelationModuliOne`: when `IsPrimitiveRoot ζ r`, the genus-one moduli
  `relationModuli r ζ 1` has a `Unique` element.

## Main results

* `TauCeti.nonempty_relationSet_one` and `TauCeti.nonempty_relationModuli_one`: whenever
  `ζ ^ r = 1`, `relationSet r ζ 1` and `relationModuli r ζ 1` are nonempty.
* `TauCeti.subsingleton_relationModuli_one`, `TauCeti.contractibleSpace_relationModuli_one`, and
  `TauCeti.simplyConnectedSpace_relationModuli_one`: when `IsPrimitiveRoot ζ r`,
  `relationModuli r ζ 1` is a subsingleton, contractible, and simply connected.
* `TauCeti.exists_ne_one_smul_eq_self_relationModuli_one`: for `2 ≤ r` and `IsPrimitiveRoot ζ r`,
  a nontrivial central holonomy twist acts trivially on `relationModuli r ζ 1`, witnessing
  non-freeness of the central-twist action on the coarse quotient.
* `TauCeti.nontrivial_relationModuli_two_one_one` and
  `TauCeti.exists_notMem_center_commute_relationSet_two_one_one`: at the non-coprime parameters
  `r = 2`, `ζ = 1`, `g = 1`, neither uniqueness up to conjugation nor centrality of stabilizers
  holds.

## References

* M. F. Atiyah, R. Bott, *The Yang-Mills equations over Riemann surfaces*, Philos. Trans. Roy. Soc.
  London Ser. A **308** (1983), 523-615, §9.
* K. Wehrheim, C. T. Woodward, *Floer field theory for coprime rank and degree*, Geom. Topol.
  **20** (2016), 3135-3188, §3.3.
-/

public section

open Matrix Topology
open scoped commutatorElement

namespace TauCeti

/-! ### Genus-one existence, uniqueness, and simple connectivity -/

/-- Whenever `ζ ^ r = 1`, the genus-one twisted relation set `relationSet r ζ 1` is nonempty,
witnessed by a rescaled clock-and-shift pair in `SU(r)`. -/
theorem nonempty_relationSet_one {r : ℕ} {ζ : ℂ} (hζ : ζ ^ r = 1) :
    Nonempty (relationSet r ζ 1) := by
  obtain ⟨A, B, hAB⟩ := Matrix.exists_coe_commutatorElement_eq_smul_one (n := Fin r)
    (by simpa using hζ)
  exact ⟨⟨fun _ => (A, B), mem_relationSet_one_iff.mpr hAB⟩⟩

/-- Whenever `ζ ^ r = 1`, the genus-one twisted moduli `relationModuli r ζ 1` is nonempty. -/
theorem nonempty_relationModuli_one {r : ℕ} {ζ : ℂ} (hζ : ζ ^ r = 1) :
    Nonempty (relationModuli r ζ 1) :=
  (nonempty_relationSet_one hζ).map relationModuliMk

/-- When `ζ` is a primitive `r`-th root of unity, any two points of `relationModuli r ζ 1`
coincide. No positivity assumption on `r` is needed: for `r = 0`, `SU(0)` is trivial. -/
theorem subsingleton_relationModuli_one {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    Subsingleton (relationModuli r ζ 1) := by
  refine ⟨fun q₁ q₂ => ?_⟩
  obtain ⟨x₁, rfl⟩ := relationModuliMk_surjective r ζ 1 q₁
  obtain ⟨x₂, rfl⟩ := relationModuliMk_surjective r ζ 1 q₂
  obtain ⟨u, huA, huB⟩ := Matrix.exists_conj_eq_of_coe_commutatorElement_eq_smul_one
    (n := Fin r) (by simpa using hζ)
    (mem_relationSet_one_iff.mp x₂.property) (mem_relationSet_one_iff.mp x₁.property)
  refine (relationModuliMk_eq_iff x₁ x₂).mpr
    ⟨u, ConjAct.toConjAct_smul_pi_prod_eq_iff.mpr fun j => ?_⟩
  rw [Subsingleton.elim j 0]
  exact ⟨huA, huB⟩

/-- **Genus-one twisted `SU(r)` moduli is a single point.** When `ζ` is a primitive `r`-th root of
unity, `relationModuli r ζ 1` has a unique element. No positivity assumption on `r` is needed: for
`r = 0`, `SU(0)` is trivial and `Matrix (Fin 0) (Fin 0) ℂ` is a subsingleton. -/
@[instance_reducible]
noncomputable def uniqueRelationModuliOne {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    Unique (relationModuli r ζ 1) :=
  @uniqueOfSubsingleton _ (subsingleton_relationModuli_one hζ)
    (Classical.choice (nonempty_relationModuli_one hζ.pow_eq_one))

/-- When `IsPrimitiveRoot ζ r`, `relationModuli r ζ 1` is contractible. -/
theorem contractibleSpace_relationModuli_one {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    ContractibleSpace (relationModuli r ζ 1) := by
  let _ := uniqueRelationModuliOne hζ
  infer_instance

/-- When `IsPrimitiveRoot ζ r`, `relationModuli r ζ 1` is simply connected. -/
theorem simplyConnectedSpace_relationModuli_one {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    SimplyConnectedSpace (relationModuli r ζ 1) := by
  have := contractibleSpace_relationModuli_one hζ
  infer_instance

/-! ### Non-freeness of central twists at genus one and non-coprime counterexamples -/

/-- **Non-freeness of the central-twist action on the genus-one coprime moduli.** For `2 ≤ r` and
`IsPrimitiveRoot ζ r`, there is a nontrivial central twist `ε ≠ 1` that acts as the identity on
`relationModuli r ζ 1` (since `relationModuli r ζ 1` is a single point while `center(SU(r))` has
nontrivial element `ζ • 1`). -/
theorem exists_ne_one_smul_eq_self_relationModuli_one {r : ℕ} (hr : 2 ≤ r) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) :
    ∃ ε : Fin 1 → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ),
      ε ≠ 1 ∧ ∀ q : relationModuli r ζ 1, ε • q = q := by
  have hpow : ζ ^ Fintype.card (Fin r) = 1 := by simpa using hζ.pow_eq_one
  let zζ : Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) :=
    ⟨⟨scalar (Fin r) ζ, Matrix.specialUnitaryGroup.scalar_mem hpow⟩,
      Matrix.specialUnitaryGroup.mem_center_iff.mpr ⟨ζ, hpow, rfl⟩⟩
  refine ⟨fun _ => (zζ, 1), fun h => hζ.ne_one hr ?_, fun _ => ?_⟩
  · have h0 := congrArg (fun f => ((f 0).1.val : Matrix (Fin r) (Fin r) ℂ) ⟨0, by omega⟩
      ⟨0, by omega⟩) h
    simpa [zζ] using h0
  · exact (subsingleton_relationModuli_one hζ).elim _ _

/-- **Non-coprime counterexample (`r = 2`, `ζ = 1`, `g = 1`): non-uniqueness.** Without
`IsPrimitiveRoot ζ r`, the untwisted genus-one moduli `relationModuli 2 1 1` has distinct points
represented by `(1, 1)` and `(-1, 1)`. -/
theorem nontrivial_relationModuli_two_one_one :
    Nontrivial (relationModuli 2 1 1) := by
  let m1 : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    ⟨scalar (Fin 2) (-1), Matrix.specialUnitaryGroup.scalar_mem (by norm_num)⟩
  let x₁ : relationSet 2 1 1 := ⟨fun _ => (1, 1), by simp⟩
  let x₂ : relationSet 2 1 1 := ⟨fun _ => (m1, 1), by simp⟩
  refine ⟨relationModuliMk x₁, relationModuliMk x₂, fun h => ?_⟩
  obtain ⟨u, hu⟩ := (relationModuliMk_eq_iff x₁ x₂).mp h
  have hu0 : ConjAct.toConjAct u • m1 = 1 :=
    (ConjAct.toConjAct_smul_pi_prod_eq_iff.mp hu 0).1
  have hm1_cen : m1 ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    Matrix.specialUnitaryGroup.mem_center_iff.mpr ⟨-1, by norm_num, rfl⟩
  rw [ConjAct.smul_eq_self_of_mem_center _ hm1_cen] at hu0
  have h00 := congr_fun₂ (congrArg Subtype.val hu0) 0 0
  norm_num [m1] at h00

/-- **Non-coprime counterexample (`r = 2`, `ζ = 1`, `g = 1`): non-central stabilizer.** At
`r = 2`, `ζ = 1`, `g = 1`, any non-central element of `SU(2)` (such as `diag(I, -I)`) fixes
`(1, 1) ∈ relationSet` without lying in `Subgroup.center (SU(2))`. -/
theorem exists_notMem_center_commute_relationSet_two_one_one :
    ∃ (x : relationSet 2 1 1) (u : Matrix.specialUnitaryGroup (Fin 2) ℂ),
      (∀ j, Commute u (x.val j).1 ∧ Commute u (x.val j).2) ∧
      u ∉ Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  obtain ⟨u, hu⟩ := Matrix.specialUnitaryGroup.exists_notMem_center (n := Fin 2)
  exact ⟨⟨fun _ => (1, 1), by simp⟩, u, fun _ => ⟨Commute.one_right u, Commute.one_right u⟩, hu⟩

end TauCeti
