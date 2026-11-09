/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.TotallyReflexive
public import TauCeti.Algebra.Module.AuslanderReiten.AuslanderBridgerSequence
public import TauCeti.Algebra.Module.Projective.FinitePresentation

/-!
# Totally reflexive modules and the transpose

Let `M` be a left module over a ring `A`, with a finite projective presentation `P₁ ⟶ P₀ ⟶ M ⟶ 0`
and transpose `Tr M`. Following Auslander and Bridger, `M` is totally reflexive exactly when
`Ext^i(M, A) = 0` and `Ext^i(Tr M, A) = 0` for all `i > 0`.

* Reflexivity of `M` is the vanishing of `Ext¹(Tr M, A)` and `Ext²(Tr M, A)`, by the
  Auslander–Bridger sequence (`TauCeti.opDualEval_bijective_iff_ext_eq_zero`).
* The dual `M*` is the kernel of `P₀* ⟶ P₁*`, whose cokernel is `Tr M`, so dimension shifting
  along the two short exact sequences `0 ⟶ M* ⟶ P₀* ⟶ K ⟶ 0` and `0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0` gives
  `Ext^{n+1}(M*, A) ≅ Ext^{n+3}(Tr M, A)`.

## Main results

* `TauCeti.isTotallyReflexive_of_ext_transpose_eq_zero`: vanishing of `Ext^{>0}(M, A)` and of
  `Ext^{>0}(Tr M, A)` makes `M` totally reflexive.
* `TauCeti.isTotallyReflexive_iff_ext_eq_zero_and_ext_transpose_eq_zero`: the converse holds as
  well.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969),
  Proposition (3.8), (b) ⇔ (c).
-/

public section

open CategoryTheory CategoryTheory.Abelian

universe u

namespace TauCeti

variable {A : Type u} [Ring A]

/-- **Auslander–Bridger**: a module `M` with a finite projective presentation `P` is totally
reflexive when `Ext^{>0}(M, A) = 0` and `Ext^{>0}(Tr M, A) = 0`, where `Tr M` is the transpose of
`P`. -/
theorem isTotallyReflexive_of_ext_transpose_eq_zero {M : ModuleCat.{u} A}
    (P : FiniteProjectivePresentation M)
    (hM : ∀ (n : ℕ) (e : Ext.{u} M (ModuleCat.of A A) (n + 1)), e = 0)
    (hT : ∀ (n : ℕ) (e : Ext.{u} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))
      (ModuleCat.of Aᵐᵒᵖ A) (n + 1)), e = 0) :
    IsTotallyReflexive A M where
  finite := Module.Finite.of_surjective P.π P.surjective
  bijective_opDualEval :=
    (opDualEval_bijective_iff_ext_eq_zero P.exact P.surjective).2 ⟨hT 0, hT 1⟩
  ext_eq_zero := hM
  ext_dual_eq_zero n e := by
    -- Dimension shifting along `0 ⟶ M* ⟶ P₀* ⟶ K ⟶ 0` and `0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0`.
    have h₁ := AuslanderReitenTranspose.shortComplex_shortExact P.p
    have h₂ := AuslanderReitenTranspose.dualShortComplex_shortExact P.exact P.surjective
    exact h₂.ext_X₁_eq_zero_of_ext_X₃_eq_zero
      (h₁.ext_X₁_eq_zero_of_ext_X₃_eq_zero (hT (n + 2))) e

/-- **Auslander–Bridger, Proposition (3.8), (b) ⇔ (c)**: a finitely generated module `M` is totally
reflexive exactly when `Ext^{>0}(M, A) = 0` and `Ext^{>0}(Tr M, A) = 0`, for the transpose `Tr M`
of any finite projective presentation `P` of `M`. -/
theorem isTotallyReflexive_iff_ext_eq_zero_and_ext_transpose_eq_zero {M : ModuleCat.{u} A}
    (P : FiniteProjectivePresentation M) :
    IsTotallyReflexive A M ↔
      (∀ (n : ℕ) (e : Ext.{u} M (ModuleCat.of A A) (n + 1)), e = 0) ∧
      ∀ (n : ℕ) (e : Ext.{u} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))
        (ModuleCat.of Aᵐᵒᵖ A) (n + 1)), e = 0 := by
  refine ⟨fun hM ↦ ⟨hM.ext_eq_zero, fun n e ↦ ?_⟩, fun ⟨hM, hT⟩ ↦
    isTotallyReflexive_of_ext_transpose_eq_zero P hM hT⟩
  obtain ⟨h1, h2⟩ := (opDualEval_bijective_iff_ext_eq_zero P.exact P.surjective).1
    hM.bijective_opDualEval
  have h₁ := AuslanderReitenTranspose.shortComplex_shortExact P.p
  have h₂ := AuslanderReitenTranspose.dualShortComplex_shortExact P.exact P.surjective
  match n with
  | 0 => exact h1 e
  | 1 => exact h2 e
  | n + 2 =>
    exact h₁.ext_X₃_eq_zero_of_ext_X₁_eq_zero
      (h₂.ext_X₃_eq_zero_of_ext_X₁_eq_zero (hM.ext_dual_eq_zero n)) e

end TauCeti
