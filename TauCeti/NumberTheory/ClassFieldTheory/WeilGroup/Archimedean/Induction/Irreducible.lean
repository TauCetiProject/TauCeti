/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.Induction.Basic
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Irreducibility of the two-dimensional inductions to `W_ℝ`

For a character `χ` of `W_ℂ = ℂˣ`, the induction `WeilGroupReal.induceCharacter χ` acts on `ℂ²`
by `z ↦ diag(χ z, χ (conj z))` and `j ↦ [[0, χ (-1)], [1, 0]]`. This file proves that this
two-dimensional representation is irreducible exactly when `χ ≠ χ ∘ conj`
(`TauCeti.ClassFieldTheory.WeilGroupReal.isIrreducible_induceRepresentation_iff`).

For the character `z ↦ z^p zbar^q`, the conjugate character is `z ↦ z^q zbar^p`, so the condition
is `p - q ≠ 0`. When `χ = χ ∘ conj`, `ℂˣ` acts by the scalar `χ z`, and an eigenline of the image of
`j` is a proper nonzero subrepresentation. When `χ z₀ ≠ χ (conj z₀)`, a nonzero subrepresentation
contains a basis vector, since the action of `z₀` has distinct eigenvalues on the two coordinates,
and the image of `j` interchanges the two coordinate lines.

## Main results

* `TauCeti.ClassFieldTheory.WeilGroupReal.isIrreducible_induceRepresentation_iff`: the induction of
  `χ` is irreducible if and only if `χ ∘ conj ≠ χ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.not_isIrreducible_induceRepresentation_of_comp_star_eq`:
  the induction of a conjugation-invariant character is reducible.

## References

* A. W. Knapp, *Local Langlands correspondence: the archimedean case*, in *Motives*,
  Proc. Sympos. Pure Math. 55, Part 2 (1994), §3.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open Matrix

namespace WeilGroupReal

variable (χ : WeilGroupComplex →* ℂˣ)

/-- **The induction of a conjugation-invariant character is reducible.** If `χ ∘ conj = χ`, then
`ℂˣ` acts on `ℂ²` by the scalar `χ z`, and the line through an eigenvector `(s, 1)` of the image
`[[0, χ (-1)], [1, 0]]` of `j`, where `s² = χ (-1)`, is a proper nonzero subrepresentation. -/
theorem not_isIrreducible_induceRepresentation_of_comp_star_eq
    (h : χ.comp (starMulAut : MulAut WeilGroupComplex).toMonoidHom = χ) :
    ¬ (induceRepresentation χ).IsIrreducible := by
  intro hirr
  have hstar (z : WeilGroupComplex) : χ (star z) = χ z := DFunLike.congr_fun h z
  obtain ⟨s, hs⟩ := IsAlgClosed.isSquare (χ (-1) : ℂ)
  set v : Fin 2 → ℂ := ![s, 1] with hv
  have hinv (w : WeilGroupReal) : ∃ t : ℂ, induceRepresentation χ w v = t • v := by
    rcases exists_includeComplex_or_j_mul w with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · refine ⟨χ z, ?_⟩
      ext i
      fin_cases i <;> simp [hv, hstar]
    · refine ⟨s * χ z, ?_⟩
      ext i
      fin_cases i <;>
        simp only [hv, map_mul, mul_apply_eq_comp, induceRepresentation_includeComplex,
          induceRepresentation_j, hstar, hs, cons_val_zero, cons_val_one, cons_val_fin_one, mul_one,
          Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one] <;>
        ring
  let σ := Subrepresentation.spanSingleton v hinv
  rcases hirr.eq_bot_or_eq_top σ with hσ | hσ
  · have hmem : v ∈ σ := Subrepresentation.self_mem_spanSingleton v hinv
    rw [hσ, Subrepresentation.mem_bot] at hmem
    simpa [hv] using congr_fun hmem 1
  · have hmem : (![1, 0] : Fin 2 → ℂ) ∈ σ := hσ ▸ Subrepresentation.mem_top
    obtain ⟨a, ha⟩ := Subrepresentation.mem_spanSingleton.mp hmem
    -- the second coordinate forces `a = 0`, and then the first coordinate reads `0 = 1`
    have ha0 : a = 0 := by simpa [hv] using congr_fun ha 1
    simpa [hv, ha0] using congr_fun ha 0

/-- In the induction of `χ`, a subrepresentation containing the first basis vector is everything:
the image of `j` carries the first basis vector to the second. -/
private theorem induceRepresentation_eq_top_of_single_zero_mem
    {σ : Subrepresentation (induceRepresentation χ)}
    (h : (Pi.single 0 1 : Fin 2 → ℂ) ∈ σ.toSubmodule) : σ = ⊤ := by
  have h' : (Pi.single 1 1 : Fin 2 → ℂ) ∈ σ.toSubmodule := by
    convert σ.apply_mem_toSubmodule j h using 1
    ext i
    fin_cases i <;> simp
  refine Subrepresentation.toSubmodule_injective ?_
  rw [Subrepresentation.toSubmodule_top, eq_top_iff]
  intro x _
  have hx : x = x 0 • (Pi.single 0 1 : Fin 2 → ℂ) + x 1 • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  rw [hx]
  exact σ.toSubmodule.add_mem (σ.toSubmodule.smul_mem _ h) (σ.toSubmodule.smul_mem _ h')

/-- In the induction of `χ`, if `χ z₀ ≠ χ (conj z₀)`, then the action of `z₀` separates the two
coordinates: a subrepresentation containing `v` contains each coordinate part `Pi.single i (v i)`,
obtained from the action of `z₀` minus the other eigenvalue. -/
private theorem induceRepresentation_single_mem_of_mem {z₀ : WeilGroupComplex}
    (hz₀ : (χ z₀ : ℂ) ≠ χ (star z₀)) {σ : Subrepresentation (induceRepresentation χ)}
    {v : Fin 2 → ℂ} (hv : v ∈ σ.toSubmodule) (i : Fin 2) :
    Pi.single i (v i) ∈ σ.toSubmodule := by
  have hzv := σ.apply_mem_toSubmodule (includeComplex z₀) hv
  have hab : (χ z₀ : ℂ) - χ (star z₀) ≠ 0 := sub_ne_zero.mpr hz₀
  -- subtracting one eigenvalue from the action of `z₀` leaves a multiple of the other coordinate
  have h0 : induceRepresentation χ (includeComplex z₀) v - (χ (star z₀) : ℂ) • v =
      ((χ z₀ : ℂ) - χ (star z₀)) • Pi.single 0 (v 0) := by
    ext k
    fin_cases k <;> simp [sub_mul]
  have h1 : (χ z₀ : ℂ) • v - induceRepresentation χ (includeComplex z₀) v =
      ((χ z₀ : ℂ) - χ (star z₀)) • Pi.single 1 (v 1) := by
    ext k
    fin_cases k <;> simp [sub_mul]
  rw [← σ.toSubmodule.smul_mem_iff hab]
  fin_cases i
  · exact h0 ▸ σ.toSubmodule.sub_mem hzv (σ.toSubmodule.smul_mem _ hv)
  · exact h1 ▸ σ.toSubmodule.sub_mem (σ.toSubmodule.smul_mem _ hv) hzv

/-- **Irreducibility of the induction.** The two-dimensional induction of a character `χ` of
`W_ℂ = ℂˣ` to `W_ℝ` is irreducible if and only if `χ ∘ conj ≠ χ`. For `χ(z) = z^p zbar^q` this is
the condition `p - q ≠ 0`. -/
theorem isIrreducible_induceRepresentation_iff :
    (induceRepresentation χ).IsIrreducible ↔
      χ.comp (starMulAut : MulAut WeilGroupComplex).toMonoidHom ≠ χ := by
  refine ⟨fun hirr h ↦ not_isIrreducible_induceRepresentation_of_comp_star_eq χ h hirr,
    fun h ↦ ⟨fun σ ↦ ?_⟩⟩
  obtain ⟨z₀, hz₀⟩ := DFunLike.ne_iff.mp h
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    starMulAut_apply] at hz₀
  have hz₀' : (χ z₀ : ℂ) ≠ χ (star z₀) := fun h ↦ hz₀ (Units.val_injective h.symm)
  by_cases hσ : σ.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective
      (hσ.trans Subrepresentation.toSubmodule_bot.symm))
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw0
  -- the coordinate part of `w` at `i` is a nonzero multiple of the basis vector at `i`
  have hsingle : (Pi.single i 1 : Fin 2 → ℂ) ∈ σ.toSubmodule := by
    refine (Submodule.smul_mem_iff _ hi).mp ?_
    simpa [← Pi.single_smul'] using induceRepresentation_single_mem_of_mem χ hz₀' hw i
  refine induceRepresentation_eq_top_of_single_zero_mem χ ?_
  fin_cases i
  · exact hsingle
  · -- the image of `j` carries the second basis vector to a multiple of the first
    refine (Submodule.smul_mem_iff _ (Units.ne_zero (χ (-1)))).mp ?_
    convert σ.apply_mem_toSubmodule j hsingle using 1
    ext k
    fin_cases k <;> simp

end WeilGroupReal

end TauCeti.ClassFieldTheory
