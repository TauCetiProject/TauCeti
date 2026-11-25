/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.Induction.Irreducible
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.IrreducibleDimension
public import TauCeti.RepresentationTheory.Irreducible

/-!
# The two-dimensional irreducible representations of `W_ℝ` are inductions

Every irreducible two-dimensional complex representation `ρ` of the Weil group
`W_ℝ = ℂˣ ⊔ jℂˣ` is isomorphic to the induction `WeilGroupReal.induceRepresentation χ` of a
character `χ` of `W_ℂ = ℂˣ` with `χ ∘ conj ≠ χ`. No continuity is needed.

Since `ℂˣ` is commutative, it has a common eigenvector `v` in `ρ`, with eigenvalues a character
`χ : ℂˣ →* ℂˣ`. The span of `v` and `j v` is stable under `W_ℝ`
(`WeilGroupReal.apply_mem_span_pair`), hence is everything, so `(v, j v)` is a basis. In it,
`z ∈ ℂˣ` acts by `diag(χ z, χ (conj z))` because `z j = j conj(z)`, and `j` acts by
`[[0, χ (-1)], [1, 0]]` because `j² = -1`: these are the matrices of `induceRepresentation χ`.
Irreducibility of the induction then forces `χ ∘ conj ≠ χ`
(`WeilGroupReal.isIrreducible_induceRepresentation_iff`). Since irreducible representations of
`W_ℝ` have dimension at most two (`WeilGroupReal.finrank_le_two_of_isIrreducible`), this
describes every irreducible representation of dimension other than one.

## Main results

* `TauCeti.ClassFieldTheory.WeilGroupReal.exists_equiv_induceRepresentation`: an irreducible
  two-dimensional complex representation of `W_ℝ` is isomorphic to `induceRepresentation χ` for a
  character `χ` of `ℂˣ` with `χ ∘ conj ≠ χ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.isIrreducible_and_finrank_eq_two_iff`: a complex
  representation of `W_ℝ` is irreducible of dimension two if and only if it is isomorphic to the
  induction of a character `χ` with `χ ∘ conj ≠ χ`.

## References

* A. W. Knapp, *Local Langlands correspondence: the archimedean case*, in *Motives*,
  Proc. Sympos. Pure Math. 55, Part 2 (1994), §3.
-/

public section

namespace TauCeti.ClassFieldTheory

namespace WeilGroupReal

open Module Representation

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The images of `ℂˣ` in a representation of `W_ℝ` commute. -/
private theorem pairwise_commute_comp_includeComplex (ρ : Representation ℂ WeilGroupReal V) :
    Pairwise fun a b ↦ Commute ((ρ.comp includeComplex) a) ((ρ.comp includeComplex) b) :=
  fun a b _ ↦ by simp only [Commute, SemiconjBy, ← map_mul, mul_comm a b]

/-- The basis `(v, j v)` of a two-dimensional irreducible representation, for a nonzero common
eigenvector `v` of `ℂˣ`. -/
private theorem linearIndependent_pair_and_span_eq_top (ρ : Representation ℂ WeilGroupReal V)
    (hρ : ρ.IsIrreducible) (h2 : finrank ℂ V = 2) {v : V} (hv₀ : v ≠ 0)
    (hv : ∀ z, ∃ c : ℂ, ρ (includeComplex z) v = c • v) :
    LinearIndependent ℂ ![v, ρ j v] ∧ ⊤ ≤ Submodule.span ℂ (Set.range ![v, ρ j v]) := by
  have : FiniteDimensional ℂ V := .of_finrank_pos (by omega)
  let σ : Subrepresentation ρ :=
    ⟨Submodule.span ℂ (Set.range ![v, ρ j v]), fun w _ hx ↦ apply_mem_span_pair ρ hv w hx⟩
  have hσ : σ = ⊤ := by
    refine (eq_bot_or_eq_top σ).resolve_left fun h ↦ hv₀ ?_
    have hmem : v ∈ σ.toSubmodule := Submodule.subset_span ⟨0, rfl⟩
    rwa [h, Subrepresentation.toSubmodule_bot, Submodule.mem_bot] at hmem
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ![v, ρ j v]) := by
    rw [← Subrepresentation.toSubmodule_top (ρ := ρ), ← hσ]
  exact ⟨linearIndependent_of_top_le_span_of_card_eq_finrank htop (by simp [h2]), htop⟩

/-- **The two-dimensional irreducible representations of `W_ℝ` are inductions.** An irreducible
two-dimensional complex representation of `W_ℝ` is isomorphic to the induction
`induceRepresentation χ` of a character `χ` of `W_ℂ = ℂˣ` with `χ ∘ conj ≠ χ`. -/
theorem exists_equiv_induceRepresentation (ρ : Representation ℂ WeilGroupReal V)
    (hρ : ρ.IsIrreducible) (h2 : finrank ℂ V = 2) :
    ∃ χ : WeilGroupComplex →* ℂˣ,
      χ.comp (starMulAut : MulAut WeilGroupComplex).toMonoidHom ≠ χ ∧
        Nonempty (ρ.Equiv (induceRepresentation χ)) := by
  have : FiniteDimensional ℂ V := .of_finrank_pos (by omega)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  obtain ⟨χ, v, hv₀, hv⟩ := exists_unitHom_jointEigenvector_of_pairwise_commute_of_isAlgClosed
    (ρ.comp includeComplex) (pairwise_commute_comp_includeComplex ρ)
  simp only [MonoidHom.coe_comp, Function.comp_apply] at hv
  obtain ⟨hli, hsp⟩ :=
    linearIndependent_pair_and_span_eq_top ρ hρ h2 hv₀ fun z ↦ ⟨_, hv z⟩
  let b : Basis (Fin 2) ℂ V := Basis.mk hli hsp
  have hb₀ : b 0 = v := Basis.mk_apply hli hsp 0
  have hb₁ : b 1 = ρ j v := Basis.mk_apply hli hsp 1
  -- the action on the basis `(v, j v)`
  have hz₀ (z : WeilGroupComplex) : ρ (includeComplex z) (b 0) = (χ z : ℂ) • b 0 := by
    rw [hb₀, hv]
  have hz₁ (z : WeilGroupComplex) : ρ (includeComplex z) (b 1) = (χ (star z) : ℂ) • b 1 := by
    rw [hb₁, ← mul_apply_eq_comp, ← map_mul, includeComplex_mul_j, map_mul, mul_apply_eq_comp,
      hv, map_smul]
  have hj₀ : ρ j (b 0) = b 1 := by rw [hb₀, hb₁]
  have hj₁ : ρ j (b 1) = (χ (-1) : ℂ) • b 0 := by
    rw [hb₁, hb₀, ← mul_apply_eq_comp, ← map_mul, j_mul_j, hv]
  -- the coordinates `b.equivFun` intertwine `ρ` with the induction on `ℂˣ` and at `j`
  have hz (z : WeilGroupComplex) : b.equivFun ∘ₗ ρ (includeComplex z) =
      induceRepresentation χ (includeComplex z) ∘ₗ b.equivFun.toLinearMap := by
    refine b.ext fun i ↦ ?_
    ext k
    fin_cases i <;> fin_cases k <;> simp [hz₀, hz₁]
  have hj : b.equivFun ∘ₗ ρ j = induceRepresentation χ j ∘ₗ b.equivFun.toLinearMap := by
    refine b.ext fun i ↦ ?_
    ext k
    fin_cases i <;> fin_cases k <;> simp [hj₀, hj₁]
  let e : ρ.Equiv (induceRepresentation χ) := .mk b.equivFun fun w ↦ by
    rcases exists_includeComplex_or_j_mul w with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact hz z
    · rw [map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc,
        hj, LinearMap.comp_assoc, hz, LinearMap.comp_assoc]
  exact ⟨χ, (isIrreducible_induceRepresentation_iff χ).mp (e.isIrreducible hρ), ⟨e⟩⟩

/-- **Classification of the two-dimensional irreducible representations of `W_ℝ`.** A complex
representation of `W_ℝ` is irreducible of dimension two if and only if it is isomorphic to the
induction of a character `χ` of `ℂˣ` with `χ ∘ conj ≠ χ`. -/
theorem isIrreducible_and_finrank_eq_two_iff (ρ : Representation ℂ WeilGroupReal V) :
    ρ.IsIrreducible ∧ finrank ℂ V = 2 ↔
      ∃ χ : WeilGroupComplex →* ℂˣ,
        χ.comp (starMulAut : MulAut WeilGroupComplex).toMonoidHom ≠ χ ∧
          Nonempty (ρ.Equiv (induceRepresentation χ)) := by
  refine ⟨fun h ↦ exists_equiv_induceRepresentation ρ h.1 h.2, ?_⟩
  rintro ⟨χ, hχ, ⟨e⟩⟩
  refine ⟨e.symm.isIrreducible ((isIrreducible_induceRepresentation_iff χ).mpr hχ), ?_⟩
  simpa using e.toLinearEquiv.finrank_eq

/-- An irreducible finite-dimensional complex representation of `W_ℝ` that is not a character is
isomorphic to the induction of a character `χ` of `ℂˣ` with `χ ∘ conj ≠ χ`. -/
theorem exists_equiv_induceRepresentation_of_finrank_ne_one [FiniteDimensional ℂ V]
    (ρ : Representation ℂ WeilGroupReal V) (hρ : ρ.IsIrreducible) (h1 : finrank ℂ V ≠ 1) :
    ∃ χ : WeilGroupComplex →* ℂˣ,
      χ.comp (starMulAut : MulAut WeilGroupComplex).toMonoidHom ≠ χ ∧
        Nonempty (ρ.Equiv (induceRepresentation χ)) := by
  have := hρ.finrank_pos
  have := finrank_le_two_of_isIrreducible ρ hρ
  exact exists_equiv_induceRepresentation ρ hρ (by omega)

end WeilGroupReal

end TauCeti.ClassFieldTheory
