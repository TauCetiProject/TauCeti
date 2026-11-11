/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ContinuousLog.AddCircle
public import TauCeti.Analysis.Sobolev.Circle.Exp
public import Mathlib.Topology.IsLocalHomeomorph
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Sobolev.Circle.Spectrum
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Nonvanishing boundary loops of winding number `d` in `H^s`, `s > 1/2`

Near a node `zw = b` of a plumbed Riemann surface, a boundary circle is mapped into the node by
its first branch coordinate `ξ`, a nowhere vanishing loop winding once around the origin. This file
describes, for `s > 1/2` and every integer `d`, the space of such loops `ξ ∈ H^s` of winding number
`d`, and its exponential coordinates `ξ = x^d e^F`, `F ∈ H^s`. These are the coordinates in which
the nonlinear Hardy graph of a node is solved, with `d = 1`
(`TauCeti.CircleSobolev.exists_analyticAt_hardyGraph`).

The space `CircleSobolev.windingLoops s d` is the range of the map
`CircleSobolev.windingExp d : F ↦ x^d e^F`, where `x^d` is the Fourier monomial `single d 1` and
`e^F` is the holomorphic Nemytskii map `nemytskii exp F`. Its elements are exactly the `ξ ∈ H^s`
whose continuous representative divided by `x^d` has a continuous logarithm
(`CircleSobolev.mem_windingLoops_iff`): the nowhere vanishing loops of winding number `d`.
The hard direction is that a continuous logarithm of an element of `H^s` lies itself in `H^s`
(`CircleSobolev.exists_toContinuousMap_eq_of_forall_exp_eq`, in
`TauCeti.Analysis.Sobolev.Circle.Exp`).

The map `windingExp d` is analytic, and its derivative at `F` is multiplication by the unit
`windingExp d F`, so it is a local homeomorphism (`CircleSobolev.isLocalHomeomorph_windingExp`) by
the inverse function theorem. Two exponents give the same loop exactly when they differ by a
constant in `2πiℤ` (`CircleSobolev.windingExp_eq_windingExp_iff`). Hence `windingLoops s d` is an
open subset of the Hilbert space `H^s`, that is, a Hilbert manifold modelled on `H^s`, on which the
local inverses of `windingExp d` serve as charts. The units of the algebra `H^s` are
the disjoint union of the open sets `windingLoops s d`, `d ∈ ℤ`
(`CircleSobolev.isUnit_iff_exists_mem_windingLoops`,
`CircleSobolev.pairwise_disjoint_windingLoops`).

## Main definitions

* `TauCeti.CircleSobolev.windingExp d F`: the loop `x^d e^F` in `H^s`, `s > 1/2`.
* `TauCeti.CircleSobolev.windingLoops s d`: the loops in `H^s` of the form `x^d e^F`.

## Main statements

* `TauCeti.CircleSobolev.mem_windingLoops_iff`: `ξ ∈ windingLoops s d` exactly when `ξ / x^d` has
  a continuous logarithm, that is, `ξ` is a nowhere vanishing loop of winding number `d`.
* `TauCeti.CircleSobolev.windingExp_eq_windingExp_iff`: `x^d e^F = x^{d'} e^G` exactly when
  `d = d'` and `G - F` is a constant in `2πiℤ`.
* `TauCeti.CircleSobolev.isLocalHomeomorph_windingExp`, `TauCeti.CircleSobolev.isOpen_windingLoops`:
  the exponential coordinates are a local homeomorphism, and the loops of winding number `d` form
  an open subset of `H^s`.
* `TauCeti.CircleSobolev.isUnit_iff_exists_mem_windingLoops`,
  `TauCeti.CircleSobolev.pairwise_disjoint_windingLoops`: every unit of `H^s` has exactly one
  winding number.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, §§9–12, for the Hilbert manifolds of boundary maps on
  which the Hardy decompositions of a cut Riemann surface are carried out.
-/

public section

noncomputable section

open Complex Set Topology

open scoped Real

namespace TauCeti

namespace CircleSobolev

variable {s : ℝ} [hs : Fact (1 / 2 < s)]

/-! ### Loops of winding number `d` -/

/-- The loop `x^d e^F` in `H^s`, `s > 1/2`: the product of the Fourier monomial `x^d = single d 1`
and the exponential `e^F = nemytskii exp F`. Its continuous representative is
`x ↦ fourier d x * exp (F x)` (`CircleSobolev.toContinuousMap_windingExp`). -/
def windingExp (d : ℤ) (F : CircleSobolev s ℂ) : CircleSobolev s ℂ :=
  single d 1 * nemytskii exp F

theorem windingExp_def (d : ℤ) (F : CircleSobolev s ℂ) :
    windingExp d F = single d 1 * nemytskii exp F :=
  (rfl)

variable (s) in
/-- The loops in `H^s`, `s > 1/2`, of the form `x^d e^F` with `F ∈ H^s`. These are exactly the
nowhere vanishing loops of winding number `d` (`CircleSobolev.mem_windingLoops_iff`). -/
def windingLoops (d : ℤ) : Set (CircleSobolev s ℂ) :=
  range (windingExp d)

theorem windingLoops_def (d : ℤ) : windingLoops s d = range (windingExp d) :=
  (rfl)

@[simp]
theorem toContinuousMap_windingExp (T : ℝ) [Fact (0 < T)] (d : ℤ) (F : CircleSobolev s ℂ)
    (x : AddCircle T) :
    toContinuousMap T hs.out (windingExp d F) x =
      fourier d x * exp (toContinuousMap T hs.out F x) := by
  simp [windingExp]

@[simp]
theorem windingExp_zero_left (F : CircleSobolev s ℂ) : windingExp 0 F = nemytskii exp F := by
  rw [windingExp, ← one_def, one_mul]

@[simp]
theorem windingExp_mem_windingLoops (d : ℤ) (F : CircleSobolev s ℂ) :
    windingExp d F ∈ windingLoops s d :=
  mem_range_self F

/-- Winding numbers add under multiplication: `x^d e^F · x^{d'} e^G = x^{d + d'} e^{F + G}`. -/
theorem windingExp_mul_windingExp (d d' : ℤ) (F G : CircleSobolev s ℂ) :
    windingExp d F * windingExp d' G = windingExp (d + d') (F + G) := by
  have h := single_mul_single (s := s) d d' (1 : ℂ) 1
  rw [mul_one] at h
  rw [windingExp, windingExp, windingExp, nemytskii_exp_add, ← h]
  ring

theorem mul_mem_windingLoops {d d' : ℤ} {ξ η : CircleSobolev s ℂ} (hξ : ξ ∈ windingLoops s d)
    (hη : η ∈ windingLoops s d') : ξ * η ∈ windingLoops s (d + d') := by
  obtain ⟨F, rfl⟩ := hξ
  obtain ⟨G, rfl⟩ := hη
  exact ⟨F + G, (windingExp_mul_windingExp d d' F G).symm⟩

/-- `x^d e^F` is a unit of `H^s`, with inverse `x^{-d} e^{-F}`. -/
@[simp]
theorem windingExp_mul_windingExp_neg (d : ℤ) (F : CircleSobolev s ℂ) :
    windingExp d F * windingExp (-d) (-F) = 1 := by
  rw [windingExp_mul_windingExp, add_neg_cancel, add_neg_cancel, windingExp_zero_left,
    nemytskii_zero, exp_zero, one_def]

/-- **The loops of winding number `d`.** For any circle `AddCircle T`, an element `ξ ∈ H^s` is of
the form `x^d e^F` with `F ∈ H^s` exactly when its continuous representative divided by the
monomial `fourier d` has a continuous logarithm, that is, when `ξ` is a nowhere vanishing loop of
winding number `d`. -/
theorem mem_windingLoops_iff (T : ℝ) [Fact (0 < T)] {d : ℤ} {ξ : CircleSobolev s ℂ} :
    ξ ∈ windingLoops s d ↔
      HasContinuousLogOn (fun x ↦ toContinuousMap T hs.out ξ x / fourier d x) univ := by
  constructor
  · rintro ⟨F, rfl⟩
    refine hasContinuousLogOn_iff.2 ⟨toContinuousMap T hs.out F,
      (toContinuousMap T hs.out F).continuous.continuousOn, fun x _ ↦ ?_⟩
    rw [toContinuousMap_windingExp, mul_div_cancel_left₀ _ (fourier_apply_ne_zero d x)]
  · intro h
    obtain ⟨L, hL, hLe⟩ := hasContinuousLogOn_iff.1 h
    rw [continuousOn_univ] at hL
    -- `L` is a continuous logarithm of `x^{-d} ξ`, so it is the representative of some `F ∈ H^s`.
    have hu (x : AddCircle T) : exp (L x) = toContinuousMap T hs.out (single (-d) 1 * ξ) x := by
      rw [hLe x (mem_univ x), div_eq_inv_mul,
        ← eq_inv_of_mul_eq_one_left (fourier_neg_mul_fourier d x)]
      simp
    obtain ⟨F, hF⟩ := exists_toContinuousMap_eq_of_forall_exp_eq (L := ⟨L, hL⟩) hu
    have hN : nemytskii exp F = single (-d) 1 * ξ :=
      nemytskii_eq_of_forall_toContinuousMap_apply T fun x ↦ by rw [← hu, hF, ContinuousMap.coe_mk]
    have h1 := single_mul_single (s := s) d (-d) (1 : ℂ) 1
    rw [mul_one, add_neg_cancel, ← one_def] at h1
    exact ⟨F, by rw [windingExp, hN, ← mul_assoc, h1, one_mul]⟩

/-- The loops of different winding numbers are disjoint. -/
theorem pairwise_disjoint_windingLoops :
    Pairwise (Function.onFun Disjoint (windingLoops s)) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  intro d d' hne
  refine disjoint_left.2 fun ξ hξ hξ' ↦ hne ?_
  exact eq_of_hasContinuousLogOn_div_fourier one_ne_zero ((mem_windingLoops_iff 1).1 hξ)
    ((mem_windingLoops_iff 1).1 hξ')

/-- **The exponential coordinates up to their deck transformations.** `x^d e^F = x^{d'} e^G`
exactly when `d = d'` and `G - F` is a constant in `2πiℤ`. -/
theorem windingExp_eq_windingExp_iff {d d' : ℤ} {F G : CircleSobolev s ℂ} :
    windingExp d F = windingExp d' G ↔ d = d' ∧ ∃ k : ℤ, G = F + single 0 (k * (2 * π * I)) := by
  constructor
  · intro h
    obtain rfl : d = d' := by
      by_contra hne
      exact disjoint_left.1 (pairwise_disjoint_windingLoops hne) (windingExp_mem_windingLoops d F)
        (h ▸ windingExp_mem_windingLoops d' G)
    refine ⟨rfl, nemytskii_exp_eq_nemytskii_exp_iff.1 ?_⟩
    have h1 := single_mul_single (s := s) (-d) d (1 : ℂ) 1
    rw [mul_one, neg_add_cancel, ← one_def] at h1
    rw [← one_mul (nemytskii exp F), ← one_mul (nemytskii exp G), ← h1, mul_assoc, mul_assoc]
    exact congrArg (single (-d) 1 * ·) h
  · rintro ⟨rfl, h⟩
    rw [windingExp, windingExp, nemytskii_exp_eq_nemytskii_exp_iff.2 h]

/-- Every unit of `H^s`, that is, every nowhere vanishing loop in `H^s`, has a winding number:
it lies in `windingLoops s d` for some integer `d`, which is unique by
`CircleSobolev.pairwise_disjoint_windingLoops`. -/
theorem isUnit_iff_exists_mem_windingLoops {ξ : CircleSobolev s ℂ} :
    IsUnit ξ ↔ ∃ d, ξ ∈ windingLoops s d := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  rw [isUnit_iff_forall_ne_zero 1]
  constructor
  · intro h
    obtain ⟨d, hd⟩ :=
      exists_hasContinuousLogOn_div_fourier (toContinuousMap 1 hs.out ξ).continuous h
    exact ⟨d, (mem_windingLoops_iff 1).2 hd⟩
  · rintro ⟨d, F, rfl⟩ x
    simp [exp_ne_zero]

/-! ### The exponential coordinates are a local homeomorphism -/

theorem analyticAt_windingExp (d : ℤ) (F : CircleSobolev s ℂ) : AnalyticAt ℂ (windingExp d) F :=
  ((convolution hs.out (.mul ℂ ℂ) (single d 1)).analyticAt _).comp
    (analyticAt_nemytskii differentiable_exp F)

/-- The derivative of `F ↦ x^d e^F` at `F` is multiplication by `x^d e^F`. -/
theorem hasFDerivAt_windingExp (d : ℤ) (F : CircleSobolev s ℂ) :
    HasFDerivAt (windingExp d) (convolution hs.out (.mul ℂ ℂ) (windingExp d F)) F := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hN := hasFDerivAt_nemytskii 1 isOpen_univ differentiable_exp.differentiableOn
    (u := F) fun _ ↦ mem_univ _
  rw [Complex.deriv_exp] at hN
  refine ((convolution hs.out (.mul ℂ ℂ) (single d 1)).hasFDerivAt.comp F hN).congr_fderiv
    (ContinuousLinearMap.ext fun G ↦ ?_)
  simp only [ContinuousLinearMap.comp_apply, ← mul_def, windingExp, mul_assoc]

/-- Multiplication by the unit `x^d e^F`, as a continuous linear automorphism of `H^s`. -/
private def mulWindingExpEquiv (d : ℤ) (F : CircleSobolev s ℂ) :
    CircleSobolev s ℂ ≃L[ℂ] CircleSobolev s ℂ :=
  .equivOfInverse (convolution hs.out (.mul ℂ ℂ) (windingExp d F))
    (convolution hs.out (.mul ℂ ℂ) (windingExp (-d) (-F)))
    (fun G ↦ by
      simp only [← mul_def]
      rw [← mul_assoc, mul_comm (windingExp (-d) (-F)), windingExp_mul_windingExp_neg, one_mul])
    (fun G ↦ by
      simp only [← mul_def]
      rw [← mul_assoc, windingExp_mul_windingExp_neg, one_mul])

/-- **The exponential coordinates are a local homeomorphism.** By the inverse function theorem,
`F ↦ x^d e^F` restricts to a homeomorphism from a neighbourhood of each `F ∈ H^s` onto a
neighbourhood of `x^d e^F`. -/
theorem isLocalHomeomorph_windingExp (d : ℤ) : IsLocalHomeomorph (windingExp (s := s) d) := by
  intro F
  have hf : HasStrictFDerivAt (windingExp d)
      ((mulWindingExpEquiv d F : CircleSobolev s ℂ ≃L[ℂ] _) : CircleSobolev s ℂ →L[ℂ] _) F := by
    have h := (analyticAt_windingExp d F).hasStrictFDerivAt
    rwa [(hasFDerivAt_windingExp d F).fderiv] at h
  exact ⟨hf.toOpenPartialHomeomorph _, hf.mem_toOpenPartialHomeomorph_source,
    hf.toOpenPartialHomeomorph_coe.symm⟩

/-- **The loops of winding number `d` form an open subset of `H^s`.** -/
theorem isOpen_windingLoops (d : ℤ) : IsOpen (windingLoops s d) :=
  (isLocalHomeomorph_windingExp d).isOpenMap.isOpen_range

end CircleSobolev

end TauCeti
