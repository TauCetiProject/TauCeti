/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational
import TauCeti.Algebra.BigOperators.Finset.PartialSum
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Equiv
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.Basic

/-!
# Distinct dominant weights give non-isomorphic rational Weyl modules

Over a field of characteristic zero the rational Weyl modules `TauCeti.rationalWeylRep` of the
dominant weights of `GL n` are irreducible (`TauCeti.isIrreducible_rationalWeylRep`).  This file
proves that they are **pairwise non-isomorphic**, so that `λ ↦ V_λ` is an injection from
`TauCeti.DominantWeight n` into the isomorphism classes of representations of `GL n k`
(`TauCeti.toSkeleton_rationalWeylFDRep_injective`).  Together with irreducibility this is the
injectivity half of the highest-weight classification; exhaustion — that every irreducible
rational representation occurs — is a separate statement and is not proved here.

## The weight of a weight

The proof is entirely about weights, and needs no character theory.  Two ingredients about the
Weyl module of a shape `μ` are already available: its weight `TauCeti.weightOfShape n μ` occurs in
it (`TauCeti.weightSpace_weylRepOfShape_weightOfShape_ne_bot`), and every weight that occurs is
dominated by that one, in the sense that its partial sums are no larger
(`TauCeti.sum_le_sum_weightOfShape_of_weightSpace_weylRepOfShape_ne_bot`).  Twisting by `det ^ λₙ`
translates every weight by the constant sequence `λₙ` (`TauCeti.weightSpace_rationalWeylRep`), so
both statements carry over to the rational Weyl module of a dominant weight `λ`, with `λ` itself
in the role of the shape weight.

An equivalence of representations preserves weight spaces
(`Representation.Equiv.weightSpace_eq_bot_iff`), so if `V_λ ≅ V_{λ'}` then `λ` occurs in `V_{λ'}`
and `λ'` occurs in `V_λ`, whence each of the two weights dominates the other.  Dominance is a
comparison of partial sums, and a sequence indexed by `Fin n` is determined by its partial sums,
so `λ = λ'`.  The same argument run on the shapes themselves separates the polynomial Weyl modules
of distinct Young diagrams with at most `n` rows, hence the Schur functors `𝕊^μ(ℂⁿ)`.

The row bounds in the polynomial statement are necessary and not merely convenient: the Weyl
module of a shape with more than `n` rows vanishes
(`TauCeti.weylModuleOfShape_eq_bot_iff`), and all those zero representations are isomorphic.

## Main results

* `TauCeti.weightSpace_rationalWeylRep_self_ne_bot` and
  `TauCeti.sum_le_sum_of_weightSpace_rationalWeylRep_ne_bot`: the dominant weight of a rational
  Weyl module occurs in it and dominates every weight that does.
* `TauCeti.nonempty_equiv_rationalWeylRep_iff`: **two rational Weyl modules are equivalent exactly
  when their dominant weights agree.**
* `TauCeti.nonempty_equiv_weylRepOfShape_iff` and
  `TauCeti.nonempty_iso_weylFDRepOfShape_iff`: the same for the polynomial Weyl modules of Young
  diagrams with at most `n` rows, hence for `TauCeti.schurFunctor`, which is
  `TauCeti.weylFDRepOfShape` over `ℂ`.
* `TauCeti.toSkeleton_rationalWeylFDRep_injective`: **`λ ↦ V_λ` is injective on isomorphism
  classes.**

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15, where the
  irreducible rational representations of `GL n` are classified by their highest weights.
-/

public section

open CategoryTheory Matrix

namespace TauCeti

universe u

variable {n : ℕ}

/-! ## The dominant weight of a rational Weyl module -/

section CommRing

variable (k : Type u) [CommRing k] [Algebra ℚ k] [Nontrivial k]

/-- **The dominant weight of a rational Weyl module occurs in it**: the weight space of
`TauCeti.rationalWeylRep k n λ` at `λ` is nonzero.  Under the determinant twist `λ` corresponds to
the weight of the polynomial part of `λ`, which has at most `n` rows. -/
theorem weightSpace_rationalWeylRep_self_ne_bot (l : DominantWeight n) :
    weightSpace (W := (weylModuleOfShape k n l.detShiftShape).toSubmodule)
      (rationalWeylRep k n l) (l : Fin n → ℤ) ≠ ⊥ := by
  rw [weightSpace_rationalWeylRep]
  have he : (l : Fin n → ℤ) - (fun _ => l.detShift) = (weightOfShape n l.detShiftShape).1 := by
    rw [DominantWeight.weightOfShape_detShiftShape]
    ext i
    simp [DominantWeight.shift_apply, sub_eq_add_neg]
  rw [he]
  exact weightSpace_weylRepOfShape_weightOfShape_ne_bot l.colLen_zero_detShiftShape_le

end CommRing

section Field

variable (k : Type u) [Field k] [CharZero k]

/-- **The dominant weight of a rational Weyl module dominates every weight occurring in it**: the
partial sums of such a weight are bounded by those of `λ`.  This is the determinant twist of the
dominance bound for the Weyl module of a shape, the twist shifting both sides by the same
multiple of `λₙ`. -/
theorem sum_le_sum_of_weightSpace_rationalWeylRep_ne_bot {l : DominantWeight n} {a : Fin n → ℤ}
    (ha : weightSpace (W := (weylModuleOfShape k n l.detShiftShape).toSubmodule)
      (rationalWeylRep k n l) a ≠ ⊥) (m : ℕ) :
    ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, a j ≤
      ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, l.1 j := by
  rw [weightSpace_rationalWeylRep] at ha
  have h := sum_le_sum_weightOfShape_of_weightSpace_weylRepOfShape_ne_bot (k := k) ha m
  rw [DominantWeight.weightOfShape_detShiftShape] at h
  simpa only [Pi.sub_apply, DominantWeight.shift_apply, sub_eq_add_neg,
    Finset.sum_add_distrib, add_le_add_iff_right] using h

/-! ## Distinctness -/

/-- **Equivalent rational Weyl modules have equal dominant weights.**  Each of the two weights
occurs in the other module, so each dominates the other, and a sequence is determined by its
partial sums. -/
theorem eq_of_nonempty_equiv_rationalWeylRep {l l' : DominantWeight n}
    (h : Nonempty ((rationalWeylRep k n l).Equiv (rationalWeylRep k n l'))) : l = l' := by
  obtain ⟨φ⟩ := h
  have hl : weightSpace (W := (weylModuleOfShape k n l'.detShiftShape).toSubmodule)
      (rationalWeylRep k n l') (l : Fin n → ℤ) ≠ ⊥ := by
    rw [Ne, Representation.Equiv.weightSpace_eq_bot_iff
      (V := (weylModuleOfShape k n l.detShiftShape).toSubmodule)
      (W := (weylModuleOfShape k n l'.detShiftShape).toSubmodule) φ]
    exact weightSpace_rationalWeylRep_self_ne_bot k l
  have hl' : weightSpace (W := (weylModuleOfShape k n l.detShiftShape).toSubmodule)
      (rationalWeylRep k n l) (l' : Fin n → ℤ) ≠ ⊥ := by
    rw [Ne, Representation.Equiv.weightSpace_eq_bot_iff
      (V := (weylModuleOfShape k n l'.detShiftShape).toSubmodule)
      (W := (weylModuleOfShape k n l.detShiftShape).toSubmodule) φ.symm]
    exact weightSpace_rationalWeylRep_self_ne_bot k l'
  exact Subtype.ext (eq_of_forall_sum_filter_lt_eq fun m => le_antisymm
    (sum_le_sum_of_weightSpace_rationalWeylRep_ne_bot k hl m)
    (sum_le_sum_of_weightSpace_rationalWeylRep_ne_bot k hl' m))

/-- **The rational Weyl modules of `GL n k` are equivalent exactly when their dominant weights
agree**, so the dominant weight is a complete invariant of the equivalence class. -/
@[simp]
theorem nonempty_equiv_rationalWeylRep_iff (l l' : DominantWeight n) :
    Nonempty ((rationalWeylRep k n l).Equiv (rationalWeylRep k n l')) ↔ l = l' :=
  ⟨eq_of_nonempty_equiv_rationalWeylRep k, fun hl => hl ▸ ⟨Representation.Equiv.refl _⟩⟩

/-- The bundled form: two rational Weyl modules are isomorphic in `FDRep k (GL n k)` exactly when
their dominant weights agree. -/
@[simp]
theorem nonempty_iso_rationalWeylFDRep_iff (l l' : DominantWeight n) :
    Nonempty (rationalWeylFDRep k n l ≅ rationalWeylFDRep k n l') ↔ l = l' := by
  rw [nonempty_fdRepIso_iff]
  simpa only [FDRep.of_ρ'] using nonempty_equiv_rationalWeylRep_iff k l l'

/-- **`λ ↦ V_λ` is injective on isomorphism classes**: the rational Weyl modules of distinct
dominant weights of `GL n` lie in distinct isomorphism classes of `FDRep k (GL n k)`.  With
`TauCeti.isIrreducible_rationalWeylRep` this is the injectivity half of the highest-weight
classification. -/
theorem toSkeleton_rationalWeylFDRep_injective :
    Function.Injective fun l : DominantWeight n => toSkeleton (rationalWeylFDRep k n l) :=
  fun _ _ hl => (nonempty_iso_rationalWeylFDRep_iff k _ _).mp
    (toSkeleton_eq_toSkeleton_iff.mp hl)

/-! ## The polynomial case -/

/-- **Equivalent Weyl modules of Young diagrams with at most `n` rows have equal shapes.**  The
row bounds cannot be dropped: taller diagrams have vanishing Weyl modules, which are all
isomorphic. -/
theorem eq_of_nonempty_equiv_weylRepOfShape {μ ν : YoungDiagram} (hμ : μ.colLen 0 ≤ n)
    (hν : ν.colLen 0 ≤ n)
    (h : Nonempty ((weylRepOfShape k n μ).Equiv (weylRepOfShape k n ν))) : μ = ν := by
  obtain ⟨φ⟩ := h
  have hμν : weightSpace (W := (weylModuleOfShape k n ν).toSubmodule)
      (weylRepOfShape k n ν) (weightOfShape n μ).1 ≠ ⊥ := by
    rw [Ne, Representation.Equiv.weightSpace_eq_bot_iff
      (V := (weylModuleOfShape k n μ).toSubmodule)
      (W := (weylModuleOfShape k n ν).toSubmodule) φ]
    exact weightSpace_weylRepOfShape_weightOfShape_ne_bot hμ
  have hνμ : weightSpace (W := (weylModuleOfShape k n μ).toSubmodule)
      (weylRepOfShape k n μ) (weightOfShape n ν).1 ≠ ⊥ := by
    rw [Ne, Representation.Equiv.weightSpace_eq_bot_iff
      (V := (weylModuleOfShape k n ν).toSubmodule)
      (W := (weylModuleOfShape k n μ).toSubmodule) φ.symm]
    exact weightSpace_weylRepOfShape_weightOfShape_ne_bot hν
  have hw : weightOfShape n μ = weightOfShape n ν :=
    Subtype.ext (eq_of_forall_sum_filter_lt_eq fun m => le_antisymm
      (sum_le_sum_weightOfShape_of_weightSpace_weylRepOfShape_ne_bot (k := k) hμν m)
      (sum_le_sum_weightOfShape_of_weightSpace_weylRepOfShape_ne_bot (k := k) hνμ m))
  rw [← shape_weightOfShape hμ, ← shape_weightOfShape hν, hw]

/-- **The Weyl modules of Young diagrams with at most `n` rows are equivalent exactly when the
diagrams agree**, so for such diagrams the shape is a complete invariant of the equivalence
class. -/
@[simp]
theorem nonempty_equiv_weylRepOfShape_iff {μ ν : YoungDiagram} (hμ : μ.colLen 0 ≤ n)
    (hν : ν.colLen 0 ≤ n) :
    Nonempty ((weylRepOfShape k n μ).Equiv (weylRepOfShape k n ν)) ↔ μ = ν :=
  ⟨eq_of_nonempty_equiv_weylRepOfShape k hμ hν,
    fun hμν => hμν ▸ ⟨Representation.Equiv.refl _⟩⟩

/-- The bundled form: the Weyl modules of Young diagrams with at most `n` rows are isomorphic in
`FDRep k (GL n k)` exactly when the diagrams agree.  Over `ℂ` this separates the Schur functors
`𝕊^μ(ℂⁿ)`, which are the bundled Weyl modules `TauCeti.weylFDRepOfShape` there. -/
@[simp]
theorem nonempty_iso_weylFDRepOfShape_iff {μ ν : YoungDiagram} (hμ : μ.colLen 0 ≤ n)
    (hν : ν.colLen 0 ≤ n) :
    Nonempty (weylFDRepOfShape k n μ ≅ weylFDRepOfShape k n ν) ↔ μ = ν := by
  rw [nonempty_fdRepIso_iff]
  simpa only [FDRep.of_ρ'] using nonempty_equiv_weylRepOfShape_iff k hμ hν

end Field

end TauCeti
