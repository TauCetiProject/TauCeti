/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Conilpotent
public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Basic

/-!
# Iterated reduced deconcatenation and conilpotence

The `n`-fold reduced coproduct `LinearMap.iteratedComul` of reduced deconcatenation takes values
in the `(n + 1)`-st tensor power of reduced tensor words. It vanishes on words of length at most
`n`. Since every element has bounded tensor length, this proves conilpotence of the reduced tensor
coalgebra (`TauCeti.ReducedTensorWords.isConilpotent_deconcatenation`).
The bound is sharp: projecting every output factor onto its single-letter component
recovers the input component of length `n + 1`. More generally, the kernel of the `n`-fold
coproduct is exactly the `n`-th tensor-length filtration step.

The bidegree calculation is
transported from the coaugmented tensor coalgebra, rather than reproving its cut
combinatorics. No flatness, field, or characteristic assumption is required.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

open scoped TensorProduct

namespace TauCeti.ReducedTensorWords

universe uR uM uN

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- An `n`-fold reduced coproduct vanishes on tensor words of length at most `n`. -/
theorem iteratedComul_deconcatenation_eq_zero_of_mem_filtration (n : ℕ)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    (deconcatenation R M).iteratedComul n z = 0 := by
  induction n generalizing z with
  | zero =>
      rw [filtration_zero, Submodule.mem_bot] at hz
      rw [hz, map_zero]
  | succ n ih =>
      have hzero := map_deconcatenation_eq_zero_of_mem_filtration R M
        (f := (deconcatenation R M).iteratedComul n)
        (g := (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).symm.toLinearMap)
        (a := n) (b := 0) (fun _ hz ↦ ih hz)
        (apply_eq_zero_of_mem_filtration_zero R M _) hz
      simp only [LinearMap.iteratedComul_succ, LinearMap.comp_apply, hzero, map_zero]

/-- Reduced tensor words form a conilpotent coalgebra: every element is killed by some
iterate of the reduced coproduct. -/
theorem isConilpotent_deconcatenation : (deconcatenation R M).IsConilpotent :=
  LinearMap.isConilpotent_iff.mpr fun z ↦
    (exists_mem_filtration R M z).imp fun n hn ↦
      iteratedComul_deconcatenation_eq_zero_of_mem_filtration R M n hn

/-- A pure input tensor of length at most the number of cuts is annihilated. -/
theorem iteratedComul_deconcatenation_of_eq_zero_of_le (n : ℕ) {k : {n : ℕ // 0 < n}}
    (hk : k.val ≤ n) (x : TensorPower R k.val M) :
    (deconcatenation R M).iteratedComul n (of R M k x) = 0 :=
  iteratedComul_deconcatenation_eq_zero_of_mem_filtration R M n (of_mem_filtration R M hk x)

/-- Projecting each factor of the `n`-fold reduced coproduct onto single letters recovers
exactly the input component of length `n + 1`. In particular, the conilpotence bound cannot
be lowered for an element with a nonzero component in that length. -/
theorem map_letter_comp_iteratedComul_deconcatenation (n : ℕ) :
    PiTensorProduct.map (fun _ : Fin (n + 1) ↦ letter R M) ∘ₗ
        (deconcatenation R M).iteratedComul n = component R M ⟨n + 1, n.succ_pos⟩ := by
  have hletter : PiTensorProduct.map (fun _ : Fin 1 ↦ letter R M) ∘ₗ
      (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).symm.toLinearMap =
        component R M 1 := by
    rw [← TauCeti.TensorPower.oneEquiv_symm_comp]
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, letter_apply,
      LinearEquiv.symm_apply_apply]
  induction n with
  | zero => rw [LinearMap.iteratedComul_zero]; exact hletter
  | succ n ih =>
      rw [LinearMap.iteratedComul_succ, ← LinearMap.comp_assoc,
        ← TauCeti.TensorPower.mulEquiv_comp_map_const]
      simp only [LinearMap.comp_assoc]
      rw [← LinearMap.comp_assoc (deconcatenation R M),
        ← TensorProduct.map_comp, ih, hletter, map_component_comp_deconcatenation]
      simp only [← LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.id_comp,
        Positive.val_one]

/-- The kernel of the `n`-fold reduced coproduct is exactly the `n`-th tensor-length
filtration step. -/
@[simp]
theorem iteratedComul_deconcatenation_eq_zero_iff_mem_filtration (n : ℕ)
    (z : ReducedTensorWords R M) :
    (deconcatenation R M).iteratedComul n z = 0 ↔ z ∈ filtration R M n := by
  constructor
  · intro hz
    cases n with
    | zero =>
        have hz' : z = 0 := (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).symm.injective
          (by simpa only [LinearMap.iteratedComul_zero, LinearEquiv.coe_coe, map_zero] using hz)
        simp only [hz', Submodule.zero_mem]
    | succ n =>
        apply (mem_filtration_iff R M (n + 1) z).2
        rintro ⟨k, hkpos⟩ hk
        obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hk)
        let p : {k : ℕ // 0 < k} := ⟨q, by dsimp only at hk; omega⟩
        -- Recover every longer component by reading `n + 1` letters on the left and
        -- an arbitrary positive-length component on the right of the last cut.
        have hsplit : TensorProduct.map ((deconcatenation R M).iteratedComul n)
            (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).symm.toLinearMap
              (deconcatenation R M z) = 0 := by
          apply TensorPower.mulEquiv.injective
          simpa only [LinearMap.iteratedComul_succ, LinearMap.comp_apply,
            LinearEquiv.coe_coe, map_zero] using hz
        have hc := congrArg (TensorProduct.map
          (PiTensorProduct.map (fun _ : Fin (n + 1) ↦ letter R M))
          (component R M p ∘ₗ
            (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).toLinearMap)) hsplit
        rw [map_zero, TensorProduct.map_map, map_letter_comp_iteratedComul_deconcatenation,
          LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.comp_id,
          ← LinearMap.comp_apply, map_component_comp_deconcatenation] at hc
        exact (TensorPower.mulEquiv (R := R) (M := M)).symm.injective
          (by simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero] using hc)
  · exact iteratedComul_deconcatenation_eq_zero_of_mem_filtration R M n

/-- A nonzero component of length `n + 1` prevents the `n`-fold reduced coproduct from
vanishing. This gives the sharp obstruction to a smaller conilpotence bound. -/
theorem iteratedComul_deconcatenation_ne_zero_of_component_ne_zero (n : ℕ)
    {z : ReducedTensorWords R M} (hz : component R M ⟨n + 1, n.succ_pos⟩ z ≠ 0) :
    (deconcatenation R M).iteratedComul n z ≠ 0 := by
  intro h
  apply hz
  have hc := LinearMap.congr_fun (map_letter_comp_iteratedComul_deconcatenation R M n) z
  simpa only [LinearMap.comp_apply, h, map_zero] using hc.symm

end TauCeti.ReducedTensorWords
