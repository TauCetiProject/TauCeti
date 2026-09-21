/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.GL2.PrincipalSeries.Irreducible
import TauCeti.RepresentationTheory.Simple.Basic

/-!
# Isomorphism classes in the principal series of `GL₂(𝔽_q)`

For characters `α, β : Fˣ → ℂˣ`, the principal series is unchanged up to isomorphism when the
parameters are swapped. More precisely, two off-diagonal principal-series representations are
isomorphic exactly when their parameter pairs differ by that swap:

`Ind_B^GL₂(α ⊗ β) ≅ Ind_B^GL₂(γ ⊗ δ) ↔ (α, β) = (γ, δ) or (α, β) = (δ, γ)`.

This is the parameter classification behind the number `½(q - 1)(q - 2)` of irreducible
principal-series rows in the character table of `GL₂(𝔽_q)`. The proof uses the intertwining-number
formula and the two-cell Bruhat decomposition. The identity cell compares the two Borel characters
directly, while the Weyl cell compares the first with the swap of the second.

## Main results

* `TauCeti.GL2Borel.nonempty_iso_borelRep_iff`: two inducing Borel lines are isomorphic exactly
  when their ordered parameter pairs agree.
* `TauCeti.finrank_hom_GL2PrincipalSeries`: the dimension of the intertwining space between two
  principal-series representations is the sum of the two Kronecker deltas for equality and
  equality after swapping.
* `TauCeti.nonempty_iso_GL2PrincipalSeries_iff`: off the diagonal, two principal-series
  representations are isomorphic exactly when their parameters agree up to swap.
* `TauCeti.nonempty_iso_GL2PrincipalSeries_swap`: swapping the two inducing characters always
  gives an isomorphic principal-series representation.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 5.
-/

public section

open CategoryTheory Matrix

namespace TauCeti

namespace GL2Borel

variable {F : Type} [CommRing F]

/-- **The inducing Borel lines remember their ordered parameter pair.** Two representations
`α ⊗ β` and `γ ⊗ δ` of the Borel subgroup are isomorphic exactly when `α = γ` and `β = δ`. -/
@[simp]
theorem nonempty_iso_borelRep_iff (α β γ δ : Fˣ →* ℂˣ) :
    Nonempty (GL2BorelRep F α β ≅ GL2BorelRep F γ δ) ↔ α = γ ∧ β = δ := by
  rw [GL2BorelRep_def, GL2BorelRep_def, linearRep_def, linearRep_def,
    ← FDRep.ofLinearCharacter_def, ← FDRep.ofLinearCharacter_def,
    FDRep.nonempty_iso_ofLinearCharacter_iff, linearChar_inj]

end GL2Borel

section FiniteField

variable (F : Type) [Field F] [Fintype F]

omit [Fintype F] in
open Classical in
private theorem finrank_mackeyTerm_one (α β γ δ : Fˣ →* ℂˣ) :
    Module.finrank ℂ
        (resFDRep ((mackeySubgroup 1 (GL2Borel F) (GL2Borel F)).subgroupOf (GL2Borel F))
            (GL2BorelRep F α β) ⟶
          (Action.res (FGModuleCat ℂ)
            (mackeyToH 1 (GL2Borel F) (GL2Borel F))).obj (GL2BorelRep F γ δ)) =
      if α = γ ∧ β = δ then 1 else 0 := by
  rw [finrank_hom_res_mackeyToH_one]
  let _ : Simple (GL2BorelRep F α β) := by
    rw [GL2BorelRep_def, GL2Borel.linearRep_def, ← FDRep.ofLinearCharacter_def]
    infer_instance
  let _ : Simple (GL2BorelRep F γ δ) := by
    rw [GL2BorelRep_def, GL2Borel.linearRep_def, ← FDRep.ofLinearCharacter_def]
    infer_instance
  rw [FDRep.finrank_hom_simple_simple]
  congr 1
  exact propext (GL2Borel.nonempty_iso_borelRep_iff α β γ δ)

omit [Fintype F] in
open Classical in
private theorem finrank_mackeyTerm_weyl (α β γ δ : Fˣ →* ℂˣ) :
    Module.finrank ℂ
        (resFDRep ((mackeySubgroup (GL2WeylElement F) (GL2Borel F)
              (GL2Borel F)).subgroupOf (GL2Borel F)) (GL2BorelRep F α β) ⟶
          (Action.res (FGModuleCat ℂ)
            (mackeyToH (GL2WeylElement F) (GL2Borel F) (GL2Borel F))).obj
              (GL2BorelRep F γ δ)) =
      if α = δ ∧ β = γ then 1 else 0 := by
  let _ : Simple (resFDRep ((mackeySubgroup (GL2WeylElement F) (GL2Borel F)
      (GL2Borel F)).subgroupOf (GL2Borel F)) (GL2BorelRep F α β)) := by
    rw [GL2BorelRep_def, GL2Borel.linearRep_def, ← FDRep.ofLinearCharacter_def]
    change Simple ((Action.res (FGModuleCat ℂ)
      ((mackeySubgroup (GL2WeylElement F) (GL2Borel F)
        (GL2Borel F)).subgroupOf (GL2Borel F)).subtype).obj
          (FDRep.ofLinearCharacter (GL2Borel.linearChar α β)))
    rw [FDRep.actionRes_obj_ofLinearCharacter]
    infer_instance
  let _ : Simple ((Action.res (FGModuleCat ℂ)
      (mackeyToH (GL2WeylElement F) (GL2Borel F) (GL2Borel F))).obj
        (GL2BorelRep F γ δ)) := by
    rw [GL2BorelRep_def, GL2Borel.linearRep_def, ← FDRep.ofLinearCharacter_def,
      FDRep.actionRes_obj_ofLinearCharacter]
    infer_instance
  rw [FDRep.finrank_hom_simple_simple]
  congr 1
  exact propext (GL2Borel.nonempty_iso_mackey_weyl_iff α β γ δ)

open Classical in
/-- **The intertwining number between two principal-series representations.** Its dimension is
one for each way the ordered pairs `(α, β)` and `(γ, δ)` agree up to the Weyl-group swap. Thus it
is `0`, `1`, or `2`; the value `2` occurs precisely on the reducible diagonal boundary. -/
theorem finrank_hom_GL2PrincipalSeries (α β γ δ : Fˣ →* ℂˣ) :
    Module.finrank ℂ (GL2PrincipalSeries F γ δ ⟶ GL2PrincipalSeries F α β) =
      (if α = γ ∧ β = δ then 1 else 0) + (if α = δ ∧ β = γ then 1 else 0) := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (GL2Borel F : Set (GL (Fin 2) F))
    (GL2Borel F : Set (GL (Fin 2) F)))
  rw [GL2PrincipalSeries_def, GL2PrincipalSeries_def,
    finrank_hom_indFDRep_mackey]
  let oneCoset : DoubleCoset.Quotient (GL2Borel F : Set (GL (Fin 2) F))
      (GL2Borel F : Set (GL (Fin 2) F)) :=
    DoubleCoset.mk (GL2Borel F) (GL2Borel F) 1
  let weylCoset : DoubleCoset.Quotient (GL2Borel F : Set (GL (Fin 2) F))
      (GL2Borel F : Set (GL (Fin 2) F)) :=
    DoubleCoset.mk (GL2Borel F) (GL2Borel F) (GL2WeylElement F)
  rw [Fintype.sum_eq_add oneCoset weylCoset (by
    exact GL2Borel.doubleCosetMk_weyl_ne_one.symm) (fun D hD => by
      exfalso
      rcases GL2Borel.doubleCosetMk_eq_one_or_eq_weyl D.out with h | h
      · exact hD.1 ((DoubleCoset.out_eq' D).symm.trans h)
      · exact hD.2 ((DoubleCoset.out_eq' D).symm.trans h))]
  congr 1
  · obtain ⟨h₁, hh₁, h₂, hh₂, hout⟩ :=
      DoubleCoset.eq.mp (DoubleCoset.out_eq' oneCoset)
    rw [← finrank_hom_res_mackeyToH_mul_left_mul_right _ _ hh₁ hh₂, ← hout,
      finrank_mackeyTerm_one]
  · obtain ⟨h₁, hh₁, h₂, hh₂, hout⟩ :=
      DoubleCoset.eq.mp (DoubleCoset.out_eq' weylCoset)
    rw [← finrank_hom_res_mackeyToH_mul_left_mul_right _ _ hh₁ hh₂, ← hout,
      finrank_mackeyTerm_weyl]

/-- **The irreducible principal series are parametrized by unordered pairs of distinct
characters.** If both parameter pairs are off the diagonal, their induced representations are
isomorphic exactly when the ordered pairs agree directly or after applying the Weyl-group swap. -/
theorem nonempty_iso_GL2PrincipalSeries_iff {α β γ δ : Fˣ →* ℂˣ} (hαβ : α ≠ β)
    (hγδ : γ ≠ δ) :
    Nonempty (GL2PrincipalSeries F α β ≅ GL2PrincipalSeries F γ δ) ↔
      (α = γ ∧ β = δ) ∨ (α = δ ∧ β = γ) := by
  let _ : Simple (GL2PrincipalSeries F α β) :=
    (simple_GL2PrincipalSeries_iff F α β).mpr hαβ
  let _ : Simple (GL2PrincipalSeries F γ δ) :=
    (simple_GL2PrincipalSeries_iff F γ δ).mpr hγδ
  rw [← CategoryTheory.finrank_hom_simple_simple_eq_one_iff ℂ,
    finrank_hom_GL2PrincipalSeries]
  split_ifs <;> aesop

/-- **Swapping the two inducing characters does not change the principal series.** -/
theorem nonempty_iso_GL2PrincipalSeries_swap (α β : Fˣ →* ℂˣ) :
    Nonempty (GL2PrincipalSeries F α β ≅ GL2PrincipalSeries F β α) := by
  by_cases hαβ : α = β
  · subst β
    exact ⟨Iso.refl _⟩
  · exact (nonempty_iso_GL2PrincipalSeries_iff F hαβ (fun h => hαβ h.symm)).mpr
      (Or.inr ⟨rfl, rfl⟩)

end FiniteField

end TauCeti
