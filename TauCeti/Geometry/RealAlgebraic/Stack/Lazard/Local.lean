/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Basic
import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.Analysis.Polynomial.RealRoots.Common

/-!
# Gluing local Lazard delineations

Lazard delineations on ambient open neighborhoods glue over a nonempty preconnected base. The
increasing order of the real roots removes any permutation ambiguity on overlaps.  Consequently,
the number and multiplicities of the roots, as well as the exponent vectors removed by Lazard
evaluation, are globally constant.

Unlike gluing ordinary delineations, this argument does not require the ordinary fibers, or even
the degrees of the Lazard evaluations, to be locally constant.  It uses only the complete ordered
root lists and exponent data already contained in each local Lazard delineation.  This is the
local-to-global step used when analytic preparation constructs roots in charts of a connected
analytic submanifold.

The root lists are glued by `TauCeti.exists_roots_of_locally` from
`TauCeti.Analysis.Polynomial.RealRoots.Common`, which is shared with
`TauCeti.nonempty_delineation_of_locally`; the gluing of the removed exponent vectors adapts the
same locally-constant argument.

## Main result

* `TauCeti.nonempty_lazardDelineation_of_locally`: local Lazard delineations on ambient open
  neighborhoods glue to a Lazard delineation over a nonempty preconnected base.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5.2.
-/

public section

open Filter MvPolynomial Polynomial Set Topology

namespace TauCeti

variable {n : ℕ} {ι : Type*} {F : ι → MvPolynomial (Fin (n + 1)) ℝ}
  {S : Set (Fin n → ℝ)}

/-- Local Lazard delineations on ambient open neighborhoods glue over a nonempty preconnected
base. The local root counts, root multiplicities, and removed base-exponent vectors may depend
on the neighborhood; their global constancy is a conclusion. -/
theorem nonempty_lazardDelineation_of_locally (hS : IsPreconnected S) (hSne : S.Nonempty)
    (hlocal : ∀ x : S, ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x.1 ∈ U ∧
      Nonempty (LazardDelineation F (S ∩ U : Set (Fin n → ℝ)))) :
    Nonempty (LazardDelineation F S) := by
  classical
  let _ := isPreconnected_iff_preconnectedSpace.1 hS
  let _ : Nonempty S := hSne.to_subtype
  choose U hU hxU hD using hlocal
  let D (x : S) := (hD x).some
  let x₀ : S := ⟨hSne.some, hSne.some_mem⟩
  let P (k : ι) (x : S) :=
    (optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardEval
      (Polynomial.C ∘ x.1)
  let Z (x : S) : Set ℝ := {t | ∃ k, F k ≠ 0 ∧ (P k x).IsRoot t}
  have hmem (a : S) (y : (S ∩ U a : Set (Fin n → ℝ))) : y.1 ∈ S ∧ y.1 ∈ U a := by
    simpa only [mem_inter_iff] using y.2
  -- Every local ordered list enumerates the same intrinsic union of Lazard-evaluation roots.
  have hlocalRange (a : S) (y : (S ∩ U a : Set (Fin n → ℝ))) :
      range (fun i ↦ (D a).root i y) = Z ⟨y.1, (hmem a y).1⟩ := by
    ext t
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := (D a).exists_multiplicity_pos i
      have hmult : 0 < (P k ⟨y.1, (hmem a y).1⟩).rootMultiplicity
          ((D a).root i y) := by
        rw [(D a).rootMultiplicity_root]
        exact hk
      have hkF : F k ≠ 0 := by
        intro hk0
        have hzero : P k ⟨y.1, (hmem a y).1⟩ = 0 := by simp [P, hk0]
        rw [hzero, Polynomial.rootMultiplicity_zero] at hmult
        exact (Nat.not_lt_zero _ hmult)
      exact ⟨k, hkF, (Polynomial.rootMultiplicity_pos').mp hmult |>.2⟩
    · rintro ⟨k, hk, ht⟩
      exact (D a).exists_root_eq k y hk t ht
  -- Glue the ordered root lists on the neighborhoods `Subtype.val ⁻¹' U a` of the base.
  let θ (a : S) (i : Fin (D a).count) (y : (Subtype.val ⁻¹' U a : Set S)) :=
    (D a).root i ⟨y.1.1, y.1.2, y.2⟩
  have hθc (a : S) (i : Fin (D a).count) : Continuous (θ a i) :=
    (D a).continuous_root i |>.comp <| Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val) _
  obtain ⟨q, -, r, m, hrc, hrmono, hrrange, hm, -⟩ :=
    exists_roots_of_locally (P := P) (Z := Z) (fun a ↦ (hU a).preimage continuous_subtype_val)
      hxU hθc
      (fun a y ↦ (D a).strictMono_root _) (fun a y ↦ hlocalRange a ⟨y.1.1, y.1.2, y.2⟩)
      (fun a k i y ↦ (D a).rootMultiplicity_root k i ⟨y.1.1, y.1.2, y.2⟩)
  -- The local exponent vectors agree on overlaps, hence on the preconnected base.
  let e (k : ι) :=
    (optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardExponent
      (Polynomial.C ∘ x₀.1)
  have he (k : ι) (x : S) :
      (optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardExponent
          (Polynomial.C ∘ x.1) = e k := by
    have hloc : IsLocallyConstant fun y : S ↦
        (optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardExponent
          (Polynomial.C ∘ y.1) := by
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun a ↦ ?_
      filter_upwards [((hU a).preimage continuous_subtype_val).mem_nhds (hxU a)] with y hy
      exact ((D a).lazardExponent_eq k ⟨y.1, y.2, hy⟩).trans
        ((D a).lazardExponent_eq k ⟨a.1, a.2, hxU a⟩).symm
    exact (hloc.apply_eq_of_preconnectedSpace x x₀).trans rfl
  refine ⟨{
    nonempty := hSne
    count := q
    root := r
    continuous_root := hrc
    strictMono_root := hrmono
    exponent := e
    lazardExponent_eq := he
    multiplicity := m
    rootMultiplicity_root := hm
    exists_root_eq := fun k x hk t ht ↦ Set.mem_range.mp ((hrrange x).symm.le ⟨k, hk, ht⟩)
    exists_multiplicity_pos := fun i ↦ ?_ }⟩
  obtain ⟨k, hk, ht⟩ := (hrrange x₀).le (mem_range_self i)
  exact ⟨k, (hm k i x₀) ▸ (Polynomial.rootMultiplicity_pos
    (lazardEval_ne_zero
      (EmbeddingLike.map_ne_zero_iff.2
        ((map_ne_zero_iff _ (rename_injective _ finSuccEquivLast.injective)).2 hk)) _)).2 ht⟩

end TauCeti
