/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation
public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Basic

/-!
# Lazard delineations of families without nullification

Let `F k` be real polynomials in `X₀, …, Xₙ` with the last variable distinguished, and let
`S ⊆ ℝⁿ`. The ordinary fibre of `F k` over `x ∈ S` is the univariate polynomial
`(optionEquivLeft ℝ (Fin n) (rename finSuccEquivLast (F k))).map (eval x)`, whose value at `t` is
`F k` at `Fin.snoc x t`. A *delineation* (`TauCeti.Delineation`) is a common stack of the roots
of these fibres, and a *Lazard delineation* (`TauCeti.LazardDelineation`) a common stack of the
roots of the Lazard evaluations of the `F k` over the points of `S`.

The two notions differ only through nullification and degree drops. Where the ordinary fibre is
nonzero it is the Lazard evaluation, and no base exponent is removed
(`MvPolynomial.lazardEval_optionEquivRight_rename_finSuccEquivLast_eq_map`). So if no nonzero
member is nullified over `S`, the fibres and the Lazard evaluations coincide:

* a delineation of the fibres over a nonempty `S` is a Lazard delineation with the same root
  functions and multiplicities, and with removed base exponents `0`;
* conversely, over a preconnected `S`, a Lazard delineation is a delineation of the fibres when
  every fibre has constant degree on `S`.

The degree hypothesis cannot be dropped: over `S = [0, ∞) ⊆ ℝ`, the fibres of `X₀ X₁² + 1` have
no real roots and are nowhere zero, so the empty stack is a Lazard delineation, but their degree
drops from `2` to `0` at the origin, which a delineation forbids. Where members are nullified,
Lazard delineations exist even when the ordinary fibres vanish identically
(`TauCeti.lazardDelineationNullifiedExample`).

## Main results

* `TauCeti.Delineation.toLazardDelineation`: a delineation of the ordinary fibres of a family
  without nullified nonzero members is a Lazard delineation.
* `TauCeti.LazardDelineation.toDelineation`: over a preconnected base, a Lazard delineation of a
  family without nullified nonzero members and with fibres of constant degree is a delineation of
  the ordinary fibres.
* `TauCeti.nonempty_delineation_iff_nonempty_lazardDelineation`: under these hypotheses, the
  ordinary fibres are delineable exactly when the family is Lazard delineable.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 2 (Lazard
  delineability compared with ordinary delineability).
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {ι : Type*} {n : ℕ} {F : ι → MvPolynomial (Fin (n + 1)) ℝ} {S : Set (Fin n → ℝ)}

/-- Where no nonzero member is nullified at a point, its Lazard evaluation over that point is its
ordinary fibre. -/
private theorem lazardEval_eq_map_of_nullified {k : ι} {x : Fin n → ℝ}
    (hnull : (optionEquivLeft ℝ (Fin n) (rename finSuccEquivLast (F k))).map (eval x) = 0 →
      F k = 0) :
    (optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardEval (Polynomial.C ∘ x) =
      (optionEquivLeft ℝ (Fin n) (rename finSuccEquivLast (F k))).map (eval x) :=
  lazardEval_optionEquivRight_rename_finSuccEquivLast_eq_map_iff.2 ((ne_or_eq _ 0).imp_right hnull)

namespace Delineation

variable (D : Delineation fun k (x : S) ↦
    (optionEquivLeft ℝ (Fin n) (rename finSuccEquivLast (F k))).map (eval x.1))
  (hS : S.Nonempty)
  (hnull : ∀ k, (∀ x : S,
    (optionEquivLeft ℝ (Fin n) (rename finSuccEquivLast (F k))).map (eval x.1) = 0) → F k = 0)

include D hnull in
/-- If every member nullified everywhere on the base is zero, then so is every member nullified
at some point of the base, since a delineation has no partly nullified member. -/
private theorem eq_zero_of_map_eq_zero {k : ι} {x : S}
    (hx : (optionEquivLeft ℝ (Fin n) (rename finSuccEquivLast (F k))).map (eval x.1) = 0) :
    F k = 0 :=
  hnull k ((D.eq_zero_or_ne_zero k).resolve_right fun h ↦ h x hx)

include hS hnull

/-- **A delineation without nullification is a Lazard delineation.** Let `S` be nonempty, and
suppose every member of the family whose ordinary fibres all vanish on `S` is zero. Then a
delineation of the ordinary fibres is a Lazard delineation of the family over `S`, with the same
root functions and multiplicities, and with no base exponent removed. -/
def toLazardDelineation : LazardDelineation F S where
  nonempty := hS
  count := D.count
  root := D.root
  continuous_root := D.continuous_root
  strictMono_root := D.strictMono_root
  exponent _ := 0
  lazardExponent_eq k x := by
    obtain hk | hk := eq_or_ne (F k) 0
    · simp [hk]
    · refine lazardExponent_eq_zero_of_eval_ne_zero ?_
      rw [eval_optionEquivRight]
      exact fun hx ↦ hk (D.eq_zero_of_map_eq_zero hnull hx)
  multiplicity := D.multiplicity
  rootMultiplicity_root k i x := by
    rw [lazardEval_eq_map_of_nullified (D.eq_zero_of_map_eq_zero hnull (x := x))]
    exact D.rootMultiplicity_root k i x
  exists_root_eq k x hk t ht := by
    rw [lazardEval_eq_map_of_nullified (D.eq_zero_of_map_eq_zero hnull (x := x))] at ht
    exact D.exists_root_eq k x (fun hx ↦ hk (D.eq_zero_of_map_eq_zero hnull hx)) t ht
  exists_multiplicity_pos := D.exists_multiplicity_pos

/-- The Lazard delineation obtained from a delineation has the same number of sections. -/
@[simp]
theorem toLazardDelineation_count : (D.toLazardDelineation hS hnull).count = D.count := (rfl)

/-- The Lazard delineation obtained from a delineation has the same root functions. -/
@[simp]
theorem toLazardDelineation_root (i : Fin (D.toLazardDelineation hS hnull).count) (x : S) :
    (D.toLazardDelineation hS hnull).root i x =
      D.root (Fin.cast (D.toLazardDelineation_count hS hnull) i) x := (rfl)

/-- The Lazard delineation obtained from a delineation removes no base exponent. -/
@[simp]
theorem toLazardDelineation_exponent (k : ι) : (D.toLazardDelineation hS hnull).exponent k = 0 :=
  (rfl)

/-- The Lazard delineation obtained from a delineation has the same multiplicities. -/
@[simp]
theorem toLazardDelineation_multiplicity (k : ι)
    (i : Fin (D.toLazardDelineation hS hnull).count) :
    (D.toLazardDelineation hS hnull).multiplicity k i =
      D.multiplicity k (Fin.cast (D.toLazardDelineation_count hS hnull) i) := (rfl)

end Delineation

namespace LazardDelineation

variable (D : LazardDelineation F S) (hS : IsPreconnected S)
  (hnull : ∀ k (x : S),
    (optionEquivLeft ℝ (Fin n) (rename finSuccEquivLast (F k))).map (eval x.1) = 0 → F k = 0)
  (hdeg : ∀ k (x y : S),
    ((optionEquivLeft ℝ (Fin n) (rename finSuccEquivLast (F k))).map (eval x.1)).natDegree =
      ((optionEquivLeft ℝ (Fin n) (rename finSuccEquivLast (F k))).map (eval y.1)).natDegree)

/-- **A Lazard delineation without nullification is a delineation.** Over a preconnected base on
which no nonzero member of the family is nullified and every ordinary fibre has constant degree,
a Lazard delineation of the family is a delineation of its ordinary fibres, with the same root
functions and multiplicities. -/
def toDelineation : Delineation fun k (x : S) ↦
    (optionEquivLeft ℝ (Fin n) (rename finSuccEquivLast (F k))).map (eval x.1) where
  count := D.count
  root := D.root
  continuous_root := D.continuous_root
  strictMono_root := D.strictMono_root
  multiplicity := D.multiplicity
  rootMultiplicity_root k i x := by
    rw [← lazardEval_eq_map_of_nullified (hnull k x)]
    exact D.rootMultiplicity_root k i x
  exists_root_eq k x hx t ht := by
    rw [← lazardEval_eq_map_of_nullified (hnull k x)] at ht
    exact D.exists_root_eq k x (fun hk ↦ hx (by simp [hk])) t ht
  exists_multiplicity_pos := D.exists_multiplicity_pos
  eq_zero_or_ne_zero k := by
    obtain hk | hk := eq_or_ne (F k) 0
    · exact .inl fun _ ↦ by simp [hk]
    · exact .inr fun x hx ↦ hk (hnull k x hx)
  natDegree_eq := hdeg
  signInvariant_sectionSet k i := by
    simpa only [polynomial_eval_map_optionEquivLeft_rename_finSuccEquivLast] using
      D.signInvariant_sectionSet hS k i
  signInvariant_sectorSet k j := by
    simpa only [polynomial_eval_map_optionEquivLeft_rename_finSuccEquivLast] using
      D.signInvariant_sectorSet hS k j

/-- The delineation obtained from a Lazard delineation has the same number of sections. -/
@[simp]
theorem toDelineation_count : (D.toDelineation hS hnull hdeg).count = D.count := (rfl)

/-- The delineation obtained from a Lazard delineation has the same root functions. -/
@[simp]
theorem toDelineation_root (i : Fin (D.toDelineation hS hnull hdeg).count) (x : S) :
    (D.toDelineation hS hnull hdeg).root i x =
      D.root (Fin.cast (D.toDelineation_count hS hnull hdeg) i) x := (rfl)

/-- The delineation obtained from a Lazard delineation has the same multiplicities. -/
@[simp]
theorem toDelineation_multiplicity (k : ι) (i : Fin (D.toDelineation hS hnull hdeg).count) :
    (D.toDelineation hS hnull hdeg).multiplicity k i =
      D.multiplicity k (Fin.cast (D.toDelineation_count hS hnull hdeg) i) := (rfl)

end LazardDelineation

/-- **Lazard delineability without nullification.** Over a nonempty preconnected base on which no
nonzero member of the family is nullified and every ordinary fibre has constant degree, the
ordinary fibres have a delineation exactly when the family has a Lazard delineation. -/
theorem nonempty_delineation_iff_nonempty_lazardDelineation (hne : S.Nonempty)
    (hS : IsPreconnected S)
    (hnull : ∀ k (x : S),
      (optionEquivLeft ℝ (Fin n) (rename finSuccEquivLast (F k))).map (eval x.1) = 0 → F k = 0)
    (hdeg : ∀ k (x y : S),
      ((optionEquivLeft ℝ (Fin n) (rename finSuccEquivLast (F k))).map (eval x.1)).natDegree =
        ((optionEquivLeft ℝ (Fin n) (rename finSuccEquivLast (F k))).map (eval y.1)).natDegree) :
    Nonempty (Delineation fun k (x : S) ↦
        (optionEquivLeft ℝ (Fin n) (rename finSuccEquivLast (F k))).map (eval x.1)) ↔
      Nonempty (LazardDelineation F S) :=
  ⟨fun ⟨D⟩ ↦ ⟨D.toLazardDelineation hne fun k h ↦ hnull k ⟨_, hne.some_mem⟩ (h _)⟩,
    fun ⟨D⟩ ↦ ⟨D.toDelineation hS hnull hdeg⟩⟩

end TauCeti
