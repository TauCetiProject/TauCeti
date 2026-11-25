/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.Induction
public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
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

## Main definitions

* `TauCeti.ClassFieldTheory.WeilGroupReal.induceRepresentation`: the representation of `W_ℝ` on
  `ℂ²` given by `WeilGroupReal.induceCharacter χ` and the standard representation `TauCeti.stdRep`.

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

/-- The representation of `W_ℝ` on `ℂ²` given by the induction `induceCharacter χ` of a character
`χ` of `W_ℂ`. -/
def induceRepresentation : Representation ℂ WeilGroupReal (Fin 2 → ℂ) :=
  (stdRep ℂ 2).comp (induceCharacter χ)

/-- `z ∈ ℂˣ` acts on `ℂ²` in the induction of `χ` by `diag(χ z, χ (conj z))`. -/
theorem induceRepresentation_includeComplex (z : WeilGroupComplex) (v : Fin 2 → ℂ) :
    induceRepresentation χ (includeComplex z) v = ![(χ z : ℂ) * v 0, (χ (star z) : ℂ) * v 1] := by
  ext i
  fin_cases i <;> simp [induceRepresentation, mulVec_diagonal]

/-- `j` acts on `ℂ²` in the induction of `χ` by `[[0, χ (-1)], [1, 0]]`. -/
theorem induceRepresentation_j (v : Fin 2 → ℂ) :
    induceRepresentation χ j v = ![(χ (-1) : ℂ) * v 1, v 0] := by
  ext i
  fin_cases i <;> simp [induceRepresentation, mulVec, dotProduct, Fin.sum_univ_two]

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
      fin_cases i <;> simp [hv, induceRepresentation_includeComplex, hstar]
    · refine ⟨s * χ z, ?_⟩
      ext i
      fin_cases i <;>
        simp [hv, map_mul, induceRepresentation_includeComplex,
          induceRepresentation_j, hstar, hs] <;> ring
  let σ : Subrepresentation (induceRepresentation χ) :=
    { toSubmodule := Submodule.span ℂ {v}
      apply_mem_toSubmodule := fun w x hx ↦ by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        obtain ⟨t, ht⟩ := hinv w
        rw [map_smul, ht, smul_smul]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v) }
  rcases hirr.eq_bot_or_eq_top σ with hσ | hσ
  · have hmem : v ∈ (⊥ : Subrepresentation (induceRepresentation χ)).toSubmodule :=
      hσ ▸ Submodule.mem_span_singleton_self v
    rw [Subrepresentation.toSubmodule_bot, Submodule.mem_bot] at hmem
    simpa [hv] using congr_fun hmem 1
  · have hmem : (![1, 0] : Fin 2 → ℂ) ∈ σ.toSubmodule := by
      rw [hσ, Subrepresentation.toSubmodule_top]
      exact Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have h0 := congr_fun ha 0
    have h1 := congr_fun ha 1
    simp [hv] at h0 h1
    simp [h1] at h0

/-- A subrepresentation of the induction of `χ` containing the first basis vector is everything:
the image of `j` carries the first basis vector to the second. -/
theorem eq_top_of_single_zero_mem {σ : Subrepresentation (induceRepresentation χ)}
    (h : (![1, 0] : Fin 2 → ℂ) ∈ σ.toSubmodule) : σ = ⊤ := by
  have h' : (![0, 1] : Fin 2 → ℂ) ∈ σ.toSubmodule := by
    simpa [induceRepresentation_j] using σ.apply_mem_toSubmodule j h
  refine Subrepresentation.toSubmodule_injective ?_
  rw [Subrepresentation.toSubmodule_top, eq_top_iff]
  intro x _
  have hx : x = x 0 • (![1, 0] : Fin 2 → ℂ) + x 1 • ![0, 1] := by
    ext i
    fin_cases i <;> simp
  rw [hx]
  exact σ.toSubmodule.add_mem (σ.toSubmodule.smul_mem _ h) (σ.toSubmodule.smul_mem _ h')

/-- **Irreducibility of the induction.** The two-dimensional induction of a character `χ` of
`W_ℂ = ℂˣ` to `W_ℝ` is irreducible if and only if `χ ∘ conj ≠ χ`. For `χ(z) = z^p zbar^q` this is
the condition `p - q ≠ 0`. -/
theorem isIrreducible_induceRepresentation_iff :
    (induceRepresentation χ).IsIrreducible ↔
      χ.comp (starMulAut : MulAut WeilGroupComplex).toMonoidHom ≠ χ := by
  refine ⟨fun hirr h ↦ not_isIrreducible_induceRepresentation_of_comp_star_eq χ h hirr,
    fun h ↦ ?_⟩
  obtain ⟨z₀, hz₀⟩ := DFunLike.ne_iff.mp h
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    starMulAut_apply] at hz₀
  have hab : (χ z₀ : ℂ) - χ (star z₀) ≠ 0 :=
    sub_ne_zero.mpr fun hab ↦ hz₀ (Units.val_injective hab.symm)
  have hc : (χ (-1) : ℂ) ≠ 0 := Units.ne_zero _
  have hbot_ne_top : (⊥ : Subrepresentation (induceRepresentation χ)) ≠ ⊤ := fun hbt ↦ by
    have := congrArg Subrepresentation.toSubmodule hbt
    rw [Subrepresentation.toSubmodule_bot, Subrepresentation.toSubmodule_top] at this
    exact bot_ne_top this
  refine { toNontrivial := ⟨⊥, ⊤, hbot_ne_top⟩, eq_bot_or_eq_top := fun σ ↦ ?_ }
  by_cases hσ : σ.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective
      (hσ.trans Subrepresentation.toSubmodule_bot.symm))
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have hzw := σ.apply_mem_toSubmodule (includeComplex z₀) hw
  rw [induceRepresentation_includeComplex] at hzw
  -- the action of `z₀` minus each eigenvalue isolates one coordinate of `w`
  have h₀ : (![((χ z₀ : ℂ) - χ (star z₀)) * w 0, 0] : Fin 2 → ℂ) ∈ σ.toSubmodule := by
    convert σ.toSubmodule.sub_mem hzw (σ.toSubmodule.smul_mem (χ (star z₀) : ℂ) hw) using 1
    ext i
    fin_cases i <;> simp
    ring
  have h₁ : (![0, ((χ z₀ : ℂ) - χ (star z₀)) * w 1] : Fin 2 → ℂ) ∈ σ.toSubmodule := by
    convert σ.toSubmodule.sub_mem (σ.toSubmodule.smul_mem (χ z₀ : ℂ) hw) hzw using 1
    ext i
    fin_cases i <;> simp
    ring
  refine eq_top_of_single_zero_mem χ ?_
  by_cases hw₀ : w 0 = 0
  · have hw₁ : w 1 ≠ 0 := fun hw₁ ↦ hw0 (by ext i; fin_cases i <;> simp [hw₀, hw₁])
    have h2 : (![0, 1] : Fin 2 → ℂ) ∈ σ.toSubmodule := by
      convert σ.toSubmodule.smul_mem (((χ z₀ : ℂ) - χ (star z₀)) * w 1)⁻¹ h₁ using 1
      ext i
      fin_cases i <;> simp
      field_simp
    have hj := σ.apply_mem_toSubmodule j h2
    rw [induceRepresentation_j] at hj
    convert σ.toSubmodule.smul_mem (χ (-1) : ℂ)⁻¹ hj using 1
    ext i
    fin_cases i <;> simp [hc]
  · convert σ.toSubmodule.smul_mem (((χ z₀ : ℂ) - χ (star z₀)) * w 0)⁻¹ h₀ using 1
    ext i
    fin_cases i <;> simp
    field_simp

end WeilGroupReal

end TauCeti.ClassFieldTheory
