/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Basic
import Mathlib.Topology.LocallyConstant.Basic

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
  let c (x : S) := Nat.card (Z x)
  have hcard (a : S) (y : (S ∩ U a : Set (Fin n → ℝ))) :
      c ⟨y.1, (hmem a y).1⟩ = (D a).count := by
    -- Expose `c`; the two subtype values differ only in their proof of membership in `S`.
    change Nat.card (Z ⟨y.1, (hmem a y).1⟩) = (D a).count
    rw [← hlocalRange a y,
      Nat.card_range_of_injective ((D a).strictMono_root y).injective]
    simp
  have hclocal : IsLocallyConstant c := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun a ↦ ?_
    filter_upwards [((hU a).preimage continuous_subtype_val).mem_nhds (hxU a)] with y hy
    exact (hcard a ⟨y.1, y.2, hy⟩).trans (hcard a ⟨a.1, a.2, hxU a⟩).symm
  let q := c x₀
  have hc (a : S) : (D a).count = q :=
    (hcard a ⟨a.1, a.2, hxU a⟩).symm.trans
      (hclocal.apply_eq_of_preconnectedSpace a x₀)
  let r (i : Fin q) (x : S) :=
    (D x).root (Fin.cast (hc x).symm i) ⟨x.1, x.2, hxU x⟩
  have hrmono (x : S) : StrictMono fun i ↦ r i x :=
    ((D x).strictMono_root ⟨x.1, x.2, hxU x⟩).comp (Fin.cast_strictMono (hc x).symm)
  have hrrange (x : S) : range (fun i ↦ r i x) = Z x := by
    exact ((Fin.castOrderIso (hc x).symm).surjective.range_comp _).trans
      (hlocalRange x ⟨x.1, x.2, hxU x⟩)
  have hrU (a y : S) (hy : y.1 ∈ U a) (i : Fin q) :
      r i y = (D a).root (Fin.cast (hc a).symm i) ⟨y.1, y.2, hy⟩ := by
    have hmono := ((D a).strictMono_root ⟨y.1, y.2, hy⟩).comp
      (Fin.cast_strictMono (hc a).symm)
    apply congrFun (((hrmono y).range_inj_of_wellFoundedLT hmono).1 ?_) i
    exact (hrrange y).trans
      (((Fin.castOrderIso (hc a).symm).surjective.range_comp _).trans
        (hlocalRange a ⟨y.1, y.2, hy⟩)).symm
  have hrc (i : Fin q) : Continuous (r i) := by
    refine continuous_iff_continuousAt.2 fun a ↦ ?_
    have hcont : ContinuousOn (r i) (Subtype.val ⁻¹' U a) := by
      rw [continuousOn_iff_continuous_domRestrict]
      let f : (Subtype.val ⁻¹' U a : Set S) → (S ∩ U a : Set (Fin n → ℝ)) :=
        fun y ↦ ⟨y.1.1, by
          rw [mem_inter_iff]
          exact ⟨y.1.2, by exact y.2⟩⟩
      have hf : Continuous f :=
        Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
      exact ((D a).continuous_root _).comp hf |>.congr fun y ↦
        (hrU a y.1 (by exact y.2) i).symm
    exact ((hU a).preimage continuous_subtype_val).continuousOn_iff.mp hcont (hxU a)
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
  -- Agreement with the local ordered lists similarly globalizes every root multiplicity.
  let m (k : ι) (i : Fin q) := (P k x₀).rootMultiplicity (r i x₀)
  have hm (k : ι) (i : Fin q) (x : S) :
      (P k x).rootMultiplicity (r i x) = m k i := by
    have hloc : IsLocallyConstant fun y : S ↦ (P k y).rootMultiplicity (r i y) := by
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun a ↦ ?_
      filter_upwards [((hU a).preimage continuous_subtype_val).mem_nhds (hxU a)] with y hy
      rw [hrU a y hy i, hrU a a (hxU a) i,
        (D a).rootMultiplicity_root, (D a).rootMultiplicity_root]
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
