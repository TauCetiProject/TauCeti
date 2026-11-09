/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Basic

/-!
# Iterated reduced deconcatenation and conilpotence

The `n`-fold reduced coproduct takes values in the `(n + 1)`-st tensor power of
reduced tensor words. It vanishes on words of length at most `n`. Since every element
has bounded tensor length, this proves conilpotence of the reduced tensor coalgebra.
The bound is sharp: projecting every output factor onto its single-letter component
recovers the input component of length `n + 1`. More generally, the kernel of the `n`-fold
coproduct is exactly the `n`-th tensor-length filtration step.

The iterates are associated by repeatedly cutting the left factor and then using
Mathlib's tensor-power multiplication equivalence. The bidegree calculation is
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

/-- The `n`-fold reduced coproduct, with `n + 1` nonempty output factors. The zeroth
iterate is the canonical identification with the first tensor power. -/
noncomputable def iteratedDeconcatenation :
    (n : ℕ) → ReducedTensorWords R M →ₗ[R] TensorPower R (n + 1) (ReducedTensorWords R M)
  | 0 => (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).symm.toLinearMap
  | n + 1 => TensorPower.mulEquiv.toLinearMap ∘ₗ
      TensorProduct.map (iteratedDeconcatenation n)
        (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).symm.toLinearMap ∘ₗ
          deconcatenation R M

/-- The zeroth coproduct makes a single output factor. -/
@[simp]
theorem iteratedDeconcatenation_zero :
    iteratedDeconcatenation R M 0 =
      (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).symm.toLinearMap := (rfl)

/-- Each further coproduct cuts the left word once more, with the output factors flattened
by the tensor-power multiplication equivalence. -/
theorem iteratedDeconcatenation_succ (n : ℕ) :
    iteratedDeconcatenation R M (n + 1) = TensorPower.mulEquiv.toLinearMap ∘ₗ
      TensorProduct.map (iteratedDeconcatenation R M n)
        (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).symm.toLinearMap ∘ₗ
          deconcatenation R M := (rfl)

/-- An `n`-fold reduced coproduct vanishes on tensor words of length at most `n`. -/
theorem iteratedDeconcatenation_eq_zero_of_mem_filtration (n : ℕ)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    iteratedDeconcatenation R M n z = 0 := by
  induction n generalizing z with
  | zero =>
      rw [filtration_zero, Submodule.mem_bot] at hz
      rw [hz, map_zero]
  | succ n ih =>
      have hzero := map_deconcatenation_eq_zero_of_mem_filtration R M
        (f := iteratedDeconcatenation R M n)
        (g := (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).symm.toLinearMap)
        (a := n) (b := 0) (fun _ hz ↦ ih hz)
        (apply_eq_zero_of_mem_filtration_zero R M _) hz
      simp only [iteratedDeconcatenation_succ, LinearMap.comp_apply, hzero, map_zero]

/-- Reduced tensor words form a conilpotent coalgebra: every element is killed by some
iterate of the reduced coproduct. -/
theorem exists_iteratedDeconcatenation_eq_zero (z : ReducedTensorWords R M) :
    ∃ n, iteratedDeconcatenation R M n z = 0 := by
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  exact ⟨n, iteratedDeconcatenation_eq_zero_of_mem_filtration R M n hn⟩

/-- Every sufficiently high reduced coproduct of a fixed element vanishes. -/
theorem exists_forall_ge_iteratedDeconcatenation_eq_zero (z : ReducedTensorWords R M) :
    ∃ n, ∀ k, n ≤ k → iteratedDeconcatenation R M k z = 0 := by
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  exact ⟨n, fun k hk ↦ iteratedDeconcatenation_eq_zero_of_mem_filtration R M k
    (filtration_monotone R M hk hn)⟩

/-- A pure input tensor of length at most the number of cuts is annihilated. -/
theorem iteratedDeconcatenation_of_eq_zero (n : ℕ) {k : {n : ℕ // 0 < n}}
    (hk : k.1 ≤ n) (x : TensorPower R k.1 M) :
    iteratedDeconcatenation R M n (of R M k x) = 0 :=
  iteratedDeconcatenation_eq_zero_of_mem_filtration R M n (of_mem_filtration R M hk x)

/-- Projecting each factor of the `n`-fold reduced coproduct onto single letters recovers
exactly the input component of length `n + 1`. In particular, the conilpotence bound cannot
be lowered for an element with a nonzero component in that length. -/
theorem map_letter_comp_iteratedDeconcatenation (n : ℕ) :
    PiTensorProduct.map (fun _ : Fin (n + 1) ↦ letter R M) ∘ₗ
        iteratedDeconcatenation R M n = component R M ⟨n + 1, n.succ_pos⟩ := by
  have hletter : PiTensorProduct.map (fun _ : Fin 1 ↦ letter R M) ∘ₗ
      (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).symm.toLinearMap =
        component R M 1 := by
    rw [← TauCeti.TensorPower.oneEquiv_symm_comp]
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, letter_apply,
      LinearEquiv.symm_apply_apply]
  induction n with
  | zero => exact hletter
  | succ n ih =>
      rw [iteratedDeconcatenation_succ, ← LinearMap.comp_assoc,
        ← TauCeti.TensorPower.mulEquiv_comp_map_const]
      simp only [LinearMap.comp_assoc]
      rw [← LinearMap.comp_assoc (deconcatenation R M),
        ← TensorProduct.map_comp, ih, hletter, map_component_comp_deconcatenation]
      simp only [← LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.id_comp,
        Positive.val_one]

/-- The kernel of the `n`-fold reduced coproduct is exactly the `n`-th tensor-length
filtration step. -/
@[simp]
theorem iteratedDeconcatenation_eq_zero_iff_mem_filtration (n : ℕ)
    (z : ReducedTensorWords R M) :
    iteratedDeconcatenation R M n z = 0 ↔ z ∈ filtration R M n := by
  constructor
  · intro hz
    cases n with
    | zero =>
        have hz' : z = 0 := (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).symm.injective
          (by simpa only [iteratedDeconcatenation_zero, LinearEquiv.coe_coe, map_zero] using hz)
        simp only [hz', Submodule.zero_mem]
    | succ n =>
        apply (mem_filtration_iff R M (n + 1) z).2
        rintro ⟨k, hkpos⟩ hk
        obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hk)
        let p : {k : ℕ // 0 < k} := ⟨q, by dsimp only at hk; omega⟩
        -- Recover every longer component by reading `n + 1` letters on the left and
        -- an arbitrary positive-length component on the right of the last cut.
        have hsplit : TensorProduct.map (iteratedDeconcatenation R M n)
            (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).symm.toLinearMap
              (deconcatenation R M z) = 0 := by
          apply TensorPower.mulEquiv.injective
          simpa only [iteratedDeconcatenation_succ, LinearMap.comp_apply,
            LinearEquiv.coe_coe, map_zero] using hz
        have hc := congrArg (TensorProduct.map
          (PiTensorProduct.map (fun _ : Fin (n + 1) ↦ letter R M))
          (component R M p ∘ₗ
            (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).toLinearMap)) hsplit
        rw [map_zero, TensorProduct.map_map, map_letter_comp_iteratedDeconcatenation,
          LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.comp_id,
          ← LinearMap.comp_apply, map_component_comp_deconcatenation] at hc
        exact (TensorPower.mulEquiv (R := R) (M := M)).symm.injective
          (by simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero] using hc)
  · exact iteratedDeconcatenation_eq_zero_of_mem_filtration R M n

/-- A nonzero component of length `n + 1` prevents the `n`-fold reduced coproduct from
vanishing. This gives the sharp obstruction to a smaller conilpotence bound. -/
theorem iteratedDeconcatenation_ne_zero_of_component_ne_zero (n : ℕ)
    {z : ReducedTensorWords R M} (hz : component R M ⟨n + 1, n.succ_pos⟩ z ≠ 0) :
    iteratedDeconcatenation R M n z ≠ 0 := by
  intro h
  apply hz
  have hc := LinearMap.congr_fun (map_letter_comp_iteratedDeconcatenation R M n) z
  simpa only [LinearMap.comp_apply, h, map_zero] using hc.symm

variable {M} {N : Type uN} [AddCommMonoid N] [Module R N]

/-- Iterated reduced coproducts commute with a linear map applied to every letter. -/
theorem iteratedDeconcatenation_natural (f : M →ₗ[R] N) (n : ℕ) :
    iteratedDeconcatenation R N n ∘ₗ ReducedTensorWords.map R f =
      PiTensorProduct.map (fun _ : Fin (n + 1) ↦ ReducedTensorWords.map R f) ∘ₗ
        iteratedDeconcatenation R M n := by
  have hone :
      (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R N)).symm.toLinearMap ∘ₗ
          ReducedTensorWords.map R f =
        PiTensorProduct.map (fun _ : Fin 1 ↦ ReducedTensorWords.map R f) ∘ₗ
          (TauCeti.TensorPower.oneEquiv R (ReducedTensorWords R M)).symm.toLinearMap :=
    TauCeti.TensorPower.oneEquiv_symm_comp (ReducedTensorWords.map R f)
  induction n with
  | zero => simpa only [iteratedDeconcatenation_zero] using hone
  | succ n ih =>
      simp only [iteratedDeconcatenation_succ, LinearMap.comp_assoc,
        deconcatenation_natural]
      rw [← LinearMap.comp_assoc (deconcatenation R M), ← TensorProduct.map_comp, ih, hone]
      rw [TensorProduct.map_comp]
      simp only [← LinearMap.comp_assoc]
      rw [TauCeti.TensorPower.mulEquiv_comp_map_const]

end TauCeti.ReducedTensorWords
