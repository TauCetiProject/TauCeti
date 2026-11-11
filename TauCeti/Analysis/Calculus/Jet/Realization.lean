/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Realization of finite symmetric jets

Over a normed field of characteristic zero, a finite family of symmetric continuous multilinear
maps is the derivative tuple of a smooth polynomial at any prescribed point. The construction
is the finite Taylor polynomial, with the derivative of order `k` divided by `k!`.
No finite-dimensionality or completeness assumption is needed for this polynomial realization.

The proof uses Mathlib's finite power series and
`HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum`, so the permutation multiplicities are
accounted for in every order, including order zero.

Over a finite-dimensional real base, the prescribed jet also has a smooth
representative with compact support in any prescribed neighborhood of its center.

## References

* Ian M. Anderson, *The Variational Bicomplex*, Chapter 1, §A.
* Ivan Kolář, Peter W. Michor and Jan Slovák, *Natural Operations in Differential Geometry*,
  Chapter 12.
-/

public section

open scoped ContDiff Topology
open Set

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The factorial-normalized finite Taylor sum associated with a tuple `A`, centered at `x`.
The tuple contains precisely the orders from zero through `r`. In characteristic zero,
`iteratedFDeriv_finiteJetPolynomial` realizes every symmetric tuple as its derivatives. -/
noncomputable def finiteJetPolynomial (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (x y : E) : F :=
  ∑ i : Fin (r + 1), (i.val.factorial : 𝕜)⁻¹ • A i (fun _ ↦ y - x)

/-- Evaluation of the finite jet polynomial as its finite Taylor sum. -/
theorem finiteJetPolynomial_apply (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (x y : E) :
    finiteJetPolynomial r A x y =
      ∑ i : Fin (r + 1), (i.val.factorial : 𝕜)⁻¹ • A i (fun _ ↦ y - x) := (rfl)

/-- The value of the finite Taylor polynomial at its center is its order-zero datum. -/
@[simp]
theorem finiteJetPolynomial_self (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (x : E) :
    finiteJetPolynomial r A x x = A ⟨0, Nat.zero_lt_succ r⟩ (fun _ ↦ 0) := by
  rw [finiteJetPolynomial_apply, Fin.sum_univ_succ]
  have hz (i : Fin r) : A i.succ (fun _ ↦ (0 : E)) = 0 :=
    (A i.succ).map_coord_zero ⟨0, Nat.zero_lt_succ i.val⟩ rfl
  simp only [sub_self, hz]
  simp
  rfl

/-- The finite Taylor polynomial is smooth (and in fact analytic). -/
theorem contDiff_finiteJetPolynomial (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (x : E) :
    ContDiff 𝕜 ω (finiteJetPolynomial r A x) := by
  apply ContDiff.sum
  intro i _
  exact ((A i).contDiff.comp (contDiff_pi.2 fun _ ↦
    contDiff_id.sub contDiff_const)).const_smul _

/-- Every prescribed symmetric derivative of the finite Taylor polynomial has the
specified value at its center. Symmetry is invariance under permutations of the slots. -/
theorem iteratedFDeriv_finiteJetPolynomial (r : ℕ)
    [CharZero 𝕜]
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (hA : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), A i (v ∘ σ) = A i v)
    (x : E) (i : Fin (r + 1)) :
    iteratedFDeriv 𝕜 i.val (finiteJetPolynomial r A x) x = A i := by
  let p : FormalMultilinearSeries 𝕜 E F := fun n ↦
    if h : n < r + 1 then (n.factorial : 𝕜)⁻¹ • A ⟨n, h⟩ else 0
  have hp : HasFiniteFPowerSeriesOnBall (finiteJetPolynomial r A x) p x (r + 1) ⊤ := by
    apply HasFiniteFPowerSeriesOnBall.mk' ?_ ENNReal.zero_lt_top ?_
    · intro n hn
      dsimp [p]
      rw [dite_eq_right (not_lt.mpr hn)]
    · intro y _
      rw [finiteJetPolynomial_apply, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro n _
      dsimp [p]
      rw [dite_eq_left n.isLt]
      simp
  ext v
  rw [hp.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum
    ((contDiff_finiteJetPolynomial r A x).contDiffOn.analyticOn)]
  simp only [p, dite_eq_left i.isLt, smul_apply, Fin.eta]
  have hsym (σ : Equiv.Perm (Fin i.val)) :
      A i (fun j ↦ v (σ j)) = A i v := hA i v σ
  simp_rw [hsym]
  simp [Fintype.card_perm, nsmul_eq_mul, ← smul_assoc,
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i.val)]

/-- A finite symmetric jet whose value belongs to a bundle-chart domain is realized
by a smooth polynomial whose graph stays in that domain near the center. -/
theorem exists_contDiff_iteratedFDeriv_eq_mem (r : ℕ) [CharZero 𝕜]
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (hA : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), A i (v ∘ σ) = A i v)
    (x : E) {u : Set (E × F)} (hu : IsOpen u)
    (hx : (x, A ⟨0, Nat.zero_lt_succ r⟩ (fun _ ↦ 0)) ∈ u) :
    ∃ f : E → F, ContDiff 𝕜 ∞ f ∧
      (∀ i : Fin (r + 1), iteratedFDeriv 𝕜 i.val f x = A i) ∧
      ∀ᶠ y in 𝓝 x, (y, f y) ∈ u := by
  refine ⟨finiteJetPolynomial r A x, (contDiff_finiteJetPolynomial r A x).of_le le_top,
    iteratedFDeriv_finiteJetPolynomial r A hA x, ?_⟩
  have hmem : (x, finiteJetPolynomial r A x x) ∈ u := by simpa using hx
  exact (continuousAt_id.prodMk
    (contDiff_finiteJetPolynomial r A x).continuous.continuousAt).eventually (hu.mem_nhds hmem)

/-- On a finite-dimensional real base, any finite symmetric jet is realized by a
smooth function with compact support in an arbitrarily prescribed neighborhood.
Multiplication by a cutoff equal to one nearby preserves every prescribed derivative. -/
theorem exists_contDiff_hasCompactSupport_iteratedFDeriv_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[ℝ] F)
    (hA : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), A i (v ∘ σ) = A i v)
    (x : E) {s : Set E} (hs : s ∈ 𝓝 x) :
    ∃ f : E → F, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ s ∧
      ∀ i : Fin (r + 1), iteratedFDeriv ℝ i.val f x = A i := by
  obtain ⟨χ, hχ, -, hχone, hχc, hχs⟩ :=
    (isCompact_singleton (x := x)).exists_contDiff_cutoff_eventuallyEq_one
      isOpen_interior (singleton_subset_iff.mpr (mem_interior_iff_mem_nhds.mpr hs))
  let p := finiteJetPolynomial r A x
  have heq : (fun y ↦ χ y • p y) =ᶠ[𝓝 x] p :=
    (hχone x (mem_singleton x)).mono fun y hy ↦ by simp [hy]
  refine ⟨fun y ↦ χ y • p y, hχ.smul ((contDiff_finiteJetPolynomial r A x).of_le le_top),
    hχc.smul_right, (tsupport_smul_subset_left _ _).trans (hχs.trans interior_subset), ?_⟩
  intro i
  exact ((heq.iteratedFDeriv ℝ i.val).eq_of_nhds).trans
    (iteratedFDeriv_finiteJetPolynomial r A hA x i)

end TauCeti
