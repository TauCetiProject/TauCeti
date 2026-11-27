/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.NonTorsionDegree
public import TauCeti.LowDimTopology.Heegaard.Knot.Minus

import Mathlib.Algebra.Field.ZMod

/-!
# The invariant `τ` of a doubly pointed Heegaard diagram

Let `(Σ, α, β, w, z)` be a doubly pointed Heegaard diagram of a knot, recorded by region incidence
data `H : TauCeti.HeegaardRegionSystem`, with a knot grading `(M, A)`
(`TauCeti.HeegaardRegionSystem.IsKnotGrading`). When its minus knot differential squares to zero,
the minus knot Floer homology `HFK⁻` (`TauCeti.HeegaardRegionSystem.knotMinusHomology`) is a module
over `𝔽₂[U]`, graded by the Alexander grading, on which `U` lowers the degree by one. The invariant
`τ` is minus the largest Alexander degree of a homogeneous element of `HFK⁻` that is not
`𝔽₂[U]`-torsion (`TauCeti.HeegaardRegionSystem.IsKnotGrading.tau`). For a diagram of a knot in
`S³` whose domain counts are the holomorphic counts, with the symmetric Alexander normalization,
this is the concordance invariant `τ` of Ozsváth and Szabó, in the form used by Ozsváth, Stipsicz
and Szabó for grid homology, where it is read from `GH⁻` with the same conventions
(`TauCeti.GridDiagram.IsKnot.tau`); that identification is not formalized here.

The definition is through `TauCeti.InternalGrading.supNonTorsionDegree`. The Alexander degrees of
the nonzero chains are at most the largest Alexander grading of a generator, so the non-torsion
degrees are bounded above (`IsKnotGrading.nonTorsionDegrees_subset_Iic`); when `HFK⁻` is not a
torsion module the supremum is therefore attained, so `-τ` is the greatest non-torsion degree
(`IsKnotGrading.isGreatest_nonTorsionDegrees_neg_tau`). If `HFK⁻` were torsion, the supremum would
be that of the empty set, which Mathlib takes to be `0` (`IsKnotGrading.tau_eq_zero_of_isTorsion`).

The Alexander grading of a knot grading is determined only up to an overall shift. Shifting it by
`a` shifts every non-torsion degree by `a`, so `τ` decreases by `a`
(`IsKnotGrading.tau_add_const`); the symmetric normalization fixes the shift
(`TauCeti.HeegaardRegionSystem.IsKnotGrading.alexander_eq_of_invert_gradedEulerChar_eq`).

To compute `τ`, it suffices to find a generator `x₀` of largest Alexander grading which is a cycle
of `CFK⁻` none of whose multiples `U ^ k x₀` is a boundary: its class is homogeneous and not
torsion, so `τ = -A(x₀)` (`IsKnotGrading.tau_eq_neg_of_forall_le`). For the genus-zero diagram of
the unknot this gives `τ = 0` (`TauCeti.HeegaardRegionSystem.tau_genusZero`).

As for the other knot Floer constructions on `TauCeti.HeegaardRegionSystem`, the complex counts
domains rather than holomorphic disks, and `∂ ∘ ∂ = 0` is a hypothesis.

## Main definitions

* `TauCeti.HeegaardRegionSystem.IsKnotGrading.tau`: minus the maximal Alexander degree of a
  homogeneous non-torsion element of `HFK⁻`.

## Main results

* `TauCeti.HeegaardRegionSystem.IsKnotGrading.nonTorsionDegrees_subset_Iic`: an upper bound for the
  Alexander gradings of the generators bounds the non-torsion degrees.
* `TauCeti.HeegaardRegionSystem.IsKnotGrading.isGreatest_nonTorsionDegrees_neg_tau` and
  `TauCeti.HeegaardRegionSystem.IsKnotGrading.le_neg_tau`: `-τ` is the greatest non-torsion degree
  when `HFK⁻` is not torsion, and an upper bound for the non-torsion degrees in general.
* `TauCeti.HeegaardRegionSystem.IsKnotGrading.tau_eq_zero_of_isTorsion`: `τ = 0` when `HFK⁻` is
  torsion.
* `TauCeti.HeegaardRegionSystem.IsKnotGrading.tau_add_const`: shifting the Alexander grading by `a`
  lowers `τ` by `a`.
* `TauCeti.HeegaardRegionSystem.IsKnotGrading.tau_eq_neg_of_forall_le`: `τ = -A(x₀)` for a
  generator `x₀` of maximal Alexander grading that is a cycle with no multiple `U ^ k x₀` a
  boundary.

## References

* P. Ozsváth and Z. Szabó, *Knot Floer homology and the four-ball genus*, Geom. Topol. **7**
  (2003), [arXiv:math/0301149](https://arxiv.org/abs/math/0301149) (the invariant `τ`).
* P. Ozsváth, A. Stipsicz and Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical
  Surveys and Monographs 208, 2015, Chapter 6 (`τ` as minus the maximal Alexander grading of a
  homogeneous non-torsion element of the minus homology).
-/

public section

open Polynomial

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint}
  [Fintype Point] [DecidableEq Region] [Fintype Region]
  {χ : Region → ℤ} {w z : Basepoint} {M A : H.Generator → ℤ}
  {hd : H.knotMinusDifferential χ w z ∘ₗ H.knotMinusDifferential χ w z = 0}

namespace IsKnotGrading

variable (hd) in
/-- **The invariant `τ` of a doubly pointed Heegaard diagram**: minus the largest Alexander degree
of a homogeneous element of the minus knot Floer homology `HFK⁻` that is not `𝔽₂[U]`-torsion, for
the Alexander component `A` of a knot grading.

The supremum is attained as soon as `HFK⁻` is not a torsion module
(`isGreatest_nonTorsionDegrees_neg_tau`); if `HFK⁻` is torsion the value is `0`, the supremum of
the empty set. For a diagram of a knot in `S³` whose domain counts are the holomorphic counts,
with the symmetric Alexander normalization, this is the concordance invariant `τ` of Ozsváth and
Szabó. -/
noncomputable def tau (h : H.IsKnotGrading χ w z M A) : ℤ :=
  -(h.knotMinusHomologyAlexanderGrading hd).supNonTorsionDegree

theorem tau_def (h : H.IsKnotGrading χ w z M A) :
    h.tau hd = -(h.knotMinusHomologyAlexanderGrading hd).supNonTorsionDegree :=
  (rfl)

/-- `U` lowers the Alexander grading of `HFK⁻` by one, in the form used by the non-torsion degree
API. -/
private theorem X_smul_mem_piece_sub_one (h : H.IsKnotGrading χ w z M A) {p : ℤ}
    {y : H.knotMinusHomology χ w z hd} (hy : y ∈ (h.knotMinusHomologyAlexanderGrading hd).piece p) :
    (X : (ZMod 2)[X]) • y ∈ (h.knotMinusHomologyAlexanderGrading hd).piece (p - (1 : ℕ)) := by
  simpa using h.X_smul_mem_knotMinusHomologyAlexanderGrading_piece hy

/-- An upper bound `a₀` for the Alexander gradings of the generators bounds the non-torsion degrees
of `HFK⁻`: a nonzero class of degree `a` is the class of a nonzero cycle of degree `a`, which
involves a generator `x` with `a ≤ A(x)`. -/
theorem nonTorsionDegrees_subset_Iic (h : H.IsKnotGrading χ w z M A) {a₀ : ℤ}
    (ha₀ : ∀ x, A x ≤ a₀) :
    (h.knotMinusHomologyAlexanderGrading hd).nonTorsionDegrees ⊆ Set.Iic a₀ := by
  intro a ha
  obtain ⟨y, hy, hyt⟩ := InternalGrading.mem_nonTorsionDegrees.mp ha
  have hy0 : y ≠ 0 := fun hy0 => hyt (hy0 ▸ Submodule.zero_mem _)
  obtain ⟨c, hc, rfl⟩ := h.mem_knotMinusHomologyAlexanderGrading_piece_iff.mp hy
  have hc0 : (c : H.Generator →₀ (ZMod 2)[X]) ≠ 0 := by
    intro hc0
    rw [show c = 0 from Subtype.ext hc0, map_zero] at hy0
    exact hy0 rfl
  obtain ⟨x, hx⟩ := exists_le_of_mem_knotMinusAlexanderPiece hc hc0
  exact hx.trans (ha₀ x)

variable (hd) in
/-- The Alexander degrees of the homogeneous non-torsion classes of `HFK⁻` are bounded above. -/
theorem bddAbove_nonTorsionDegrees (h : H.IsKnotGrading χ w z M A) :
    BddAbove (h.knotMinusHomologyAlexanderGrading hd).nonTorsionDegrees := by
  obtain ⟨a₀, ha₀⟩ := (Set.finite_range A).bddAbove
  exact ⟨a₀, h.nonTorsionDegrees_subset_Iic fun x => ha₀ (Set.mem_range_self x)⟩

/-- Every Alexander degree of a homogeneous non-torsion class of `HFK⁻` is at most `-τ`. -/
theorem le_neg_tau (h : H.IsKnotGrading χ w z M A) {a : ℤ}
    (ha : a ∈ (h.knotMinusHomologyAlexanderGrading hd).nonTorsionDegrees) : a ≤ -h.tau hd := by
  rw [tau_def, neg_neg]
  exact InternalGrading.le_supNonTorsionDegree (h.bddAbove_nonTorsionDegrees hd) ha

/-- When `HFK⁻` is not a torsion `𝔽₂[U]`-module, `-τ` is the greatest Alexander degree of a
homogeneous non-torsion class: there is such a class in degree `-τ`, and none in any higher
degree. -/
theorem isGreatest_nonTorsionDegrees_neg_tau (h : H.IsKnotGrading χ w z M A)
    (hT : ¬Module.IsTorsion (ZMod 2)[X] (H.knotMinusHomology χ w z hd)) :
    IsGreatest (h.knotMinusHomologyAlexanderGrading hd).nonTorsionDegrees (-h.tau hd) := by
  rw [tau_def, neg_neg]
  exact InternalGrading.isGreatest_supNonTorsionDegree
    ((InternalGrading.nonTorsionDegrees_nonempty_iff _).mpr hT) (h.bddAbove_nonTorsionDegrees hd)

/-- If `HFK⁻` is a torsion `𝔽₂[U]`-module, then `τ = 0`: there is no homogeneous non-torsion
class, and the supremum of the empty set of degrees is `0`. -/
theorem tau_eq_zero_of_isTorsion (h : H.IsKnotGrading χ w z M A)
    (hT : Module.IsTorsion (ZMod 2)[X] (H.knotMinusHomology χ w z hd)) : h.tau hd = 0 := by
  rw [tau_def, InternalGrading.supNonTorsionDegree_def,
    Set.not_nonempty_iff_eq_empty.mp fun hne =>
      (InternalGrading.nonTorsionDegrees_nonempty_iff _).mp hne hT,
    Int.csSup_empty, neg_zero]

/-- Shifting the Alexander grading by `a` shifts the Alexander pieces of `HFK⁻` by `a`. -/
private theorem mem_knotMinusHomologyAlexanderGrading_add_const_piece_iff
    (h : H.IsKnotGrading χ w z M A) (m a : ℤ) {p : ℤ} {y : H.knotMinusHomology χ w z hd} :
    y ∈ ((h.add_const m a).knotMinusHomologyAlexanderGrading hd).piece p ↔
      y ∈ (h.knotMinusHomologyAlexanderGrading hd).piece (p - a) := by
  have hpiece (c : H.Generator →₀ (ZMod 2)[X]) :
      c ∈ H.knotMinusAlexanderPiece (fun x => A x + a) p ↔
        c ∈ H.knotMinusAlexanderPiece A (p - a) := by
    simp only [mem_knotMinusAlexanderPiece_iff]
    exact forall₃_congr fun x k _ => by omega
  rw [mem_knotMinusHomologyAlexanderGrading_piece_iff,
    mem_knotMinusHomologyAlexanderGrading_piece_iff]
  simp only [hpiece]

/-- **Shifting the Alexander grading by `a` lowers `τ` by `a`**, when `HFK⁻` is not torsion: every
non-torsion degree is shifted by `a`. -/
theorem tau_add_const (h : H.IsKnotGrading χ w z M A) (m a : ℤ)
    (hT : ¬Module.IsTorsion (ZMod 2)[X] (H.knotMinusHomology χ w z hd)) :
    (h.add_const m a).tau hd = h.tau hd - a := by
  have hdeg : ((h.add_const m a).knotMinusHomologyAlexanderGrading hd).nonTorsionDegrees =
      OrderIso.addRight a '' (h.knotMinusHomologyAlexanderGrading hd).nonTorsionDegrees := by
    ext p
    simp only [InternalGrading.mem_nonTorsionDegrees, Set.mem_image, OrderIso.addRight_apply]
    constructor
    · rintro ⟨y, hy, hyt⟩
      exact ⟨p - a, ⟨y, (h.mem_knotMinusHomologyAlexanderGrading_add_const_piece_iff m a).mp hy,
        hyt⟩, by omega⟩
    · rintro ⟨q, ⟨y, hy, hyt⟩, rfl⟩
      refine ⟨y, (h.mem_knotMinusHomologyAlexanderGrading_add_const_piece_iff m a).mpr ?_, hyt⟩
      rwa [add_sub_cancel_right]
  rw [tau_def, tau_def, InternalGrading.supNonTorsionDegree_def, hdeg,
    ← OrderIso.map_csSup' _ ((InternalGrading.nonTorsionDegrees_nonempty_iff _).mpr hT)
      (h.bddAbove_nonTorsionDegrees hd),
    OrderIso.addRight_apply, InternalGrading.supNonTorsionDegree_def]
  ring

/-- **`τ` from a cycle of maximal Alexander grading.** Let `x₀` be a generator of largest Alexander
grading that is a cycle of `CFK⁻`, with no multiple `U ^ k x₀` a boundary. Then the class of `x₀`
is a homogeneous non-torsion class of degree `A(x₀)`, the largest possible, so `τ = -A(x₀)`. -/
theorem tau_eq_neg_of_forall_le (h : H.IsKnotGrading χ w z M A) (x₀ : H.Generator)
    (hcyc : H.knotMinusDifferential χ w z (Finsupp.single x₀ 1) = 0)
    (hbd : ∀ k : ℕ,
      Finsupp.single x₀ (X ^ k : (ZMod 2)[X]) ∉ LinearMap.range (H.knotMinusDifferential χ w z))
    (hmax : ∀ x, A x ≤ A x₀) : h.tau hd = -A x₀ := by
  let c₀ : LinearMap.ker (H.knotMinusDifferential χ w z) := ⟨Finsupp.single x₀ 1, hcyc⟩
  have hc₀ : (H.knotMinusDifferential χ w z).homologyπ hd c₀ ∈
      (h.knotMinusHomologyAlexanderGrading hd).piece (A x₀) :=
    h.mem_knotMinusHomologyAlexanderGrading_piece_iff.mpr
      ⟨c₀, by simpa using single_X_pow_mem_knotMinusAlexanderPiece (A := A) x₀ 0, rfl⟩
  -- The class of `x₀` is not torsion: no power of `U` kills it.
  have hmem : A x₀ ∈ (h.knotMinusHomologyAlexanderGrading hd).nonTorsionDegrees := by
    refine InternalGrading.mem_nonTorsionDegrees.mpr ⟨_, hc₀, fun ht => ?_⟩
    obtain ⟨k, hk⟩ := (InternalGrading.mem_torsion_iff_exists_X_pow_smul_eq_zero one_ne_zero
      (fun _ _ hy => h.X_smul_mem_piece_sub_one hy) hc₀).mp ht
    rw [← map_smul, LinearMap.homologyπ_eq_zero_iff, Submodule.coe_smul] at hk
    exact hbd k (by simpa [c₀, Finsupp.smul_single] using hk)
  rw [tau_def, InternalGrading.supNonTorsionDegree_def,
    IsGreatest.csSup_eq ⟨hmem, fun a ha => h.nonTorsionDegrees_subset_Iic hmax ha⟩]

end IsKnotGrading

end HeegaardRegionSystem

end TauCeti
