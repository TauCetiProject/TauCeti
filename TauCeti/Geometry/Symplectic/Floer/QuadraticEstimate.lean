/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization
import TauCeti.Analysis.Calculus.FDeriv.Remainder

/-!
# The quadratic estimate for the Floer operator

Let `(V, ω)` be a finite-dimensional symplectic vector space, `J(z, y)` a domain-dependent family
of endomorphisms and `K = Ks ds + Kt dt` a domain-dependent Hamiltonian perturbation. The Floer
operator `F(u) = ∂s u - X_Ks(u) + J(u)(∂t u - X_Kt(u))` (`TauCeti.SymplecticForm.floerOperator`)
has linearization `D_w` at a map `w` (`TauCeti.SymplecticForm.floerLinearization`), and

`F(w + ξ) = F(w) + D_w ξ + N_w(ξ)`.

Gluing and transversality solve `F(w + ξ) = 0` near an approximate solution `w` by a Newton
iteration: with a right inverse `Q` of `D_w`, a solution is a fixed point of
`ξ ↦ -Q (F(w) + N_w(ξ))`. The iteration contracts once `N_w` is quadratically small in the sense
`‖N_w(ξ₁) - N_w(ξ₂)‖ ≲ (‖ξ₁‖ + ‖ξ₂‖) ‖ξ₁ - ξ₂‖`, which is the hypothesis of the abstract
theorem `TauCeti.exists_mem_range_norm_le_add_add_eq_zero`. This file proves the pointwise form of
that estimate, from which its Sobolev forms follow.

**The remainder depends only on first-order data.** The `∂s` terms of `F` are linear and cancel
from `N_w`, so at a domain point `z` the remainder is a function
`TauCeti.SymplecticForm.floerRemainder ω (J z) (Ks z) (Kt z) y v e d` of the coefficients frozen at
`z`, the value `y = w(z)` and slice velocity `v = ∂t w(z)` of the base map, and the value
`e = ξ(z)` and slice velocity `d = ∂t ξ(z)` of the increment
(`SymplecticForm.floerOperator_add_sub_floerOperator_sub_floerLinearization`). It vanishes for
`e = 0` (`TauCeti.SymplecticForm.floerRemainder_zero`). Being a function of values and slice
velocities, it also makes sense for increments with weak derivatives, and the estimates are
stated for it. The difference of two remainders splits into Taylor remainders of `X_Ks`, `J` and
`X_Kt` at `y`, and differences of `J` multiplied by first-order terms
(`TauCeti.SymplecticForm.floerRemainder_sub_floerRemainder`).

**The estimate.** Let the coefficients `J p`, `Ks p`, `Kt p` depend on a parameter `p` in a normed
space `P`. If `J` is jointly `C²` and `Ks`, `Kt` are jointly `C³` at the points of a compact set
`K` of pairs `(p, y)`, then there are `δ > 0` and `C` such that, whenever `(p, y) ∈ K` and
`‖e₁‖, ‖e₂‖ ≤ δ`,

`‖N(e₁, d₁) - N(e₂, d₂)‖ ≤ C (m (1 + ‖v - X_Kt(y)‖) ‖e₁ - e₂‖ + ‖e₁ - e₂‖ ‖d₁‖ + ‖e₂‖ ‖d₁ - d₂‖)`,

where `m = max ‖e₁‖ ‖e₂‖`
(`TauCeti.SymplecticForm.exists_pos_forall_norm_floerRemainder_sub_le`). Here `v - X_Kt(y)` is the
slice defect of the base map; for a Floer solution with `Ks = 0` and `J² = -1` it is `J ∂s w`.
For maps, and coefficients pulled back to the domain along any `φ : ℝ × ℝ → P`, this bounds
`F(w + ξ₁) - F(w + ξ₂) - D_w(ξ₁ - ξ₂)` at every point where `(φ z, w(z)) ∈ K`
(`exists_pos_forall_norm_floerOperator_sub_floerOperator_sub_floerLinearization_le`),
and for `ξ₂ = 0` it is the quadratic estimate
`‖F(w + ξ) - F(w) - D_w ξ‖ ≤ C (‖ξ‖² (1 + ‖∂t w - X_Kt(w)‖) + ‖ξ‖ ‖∂t ξ‖)`
(`exists_pos_forall_norm_floerOperator_add_sub_floerOperator_sub_floerLinearization_le`).
Taking `φ = id` gives domain-dependent coefficients over a compact part of the domain; taking
`φ z = z.2` gives `t`-dependent coefficients with constants uniform over a whole strip
`ℝ × [0, 1]`, as on the cylindrical ends used in gluing.
Since `W^{1,p}` embeds in `C⁰` for `p > 2` on a two-dimensional domain, integrating the pointwise
bound gives the `W^{1,p} → Lᵖ` estimate needed by the Newton iteration, provided the slice defect
of `w` is bounded.

The constants come from Taylor's theorem and the mean value inequality with uniform constants
over compact parameter sets (`IsCompact.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul`,
`IsCompact.exists_pos_forall_norm_sub_le_mul_norm_sub`). The domain is a coordinate patch
and the target a vector space; no Sobolev space is constructed here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.5, on the quadratic estimate and the implicit function theorem, and Chapter 10, on
  gluing.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), on gluing Floer trajectories.
-/

public section

namespace TauCeti.SymplecticForm

open ContinuousLinearMap Metric

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (ω : SymplecticForm V)

/-! ### The remainder as a function of first-order data -/

section Remainder

variable (J : V → V →L[ℝ] V) (Ks Kt : V → ℝ)

/-- The nonlinear remainder of the Floer operator with coefficients `J`, `Ks`, `Kt` frozen at a
domain point, as a function of the value `y` and slice velocity `v` of the base map and the value
`e` and slice velocity `d` of the increment: the pointwise Floer operator at `(y + e, v + d)`,
minus its value at `(y, v)`, minus the linearization at `y` applied to `(e, d)`. The `∂s` terms of
the operator are linear and do not appear. -/
noncomputable def floerRemainder (y v e d : V) : V :=
  (-ω.hamiltonianVectorField Ks (y + e) +
      J (y + e) (v + d - ω.hamiltonianVectorField Kt (y + e))) -
    (-ω.hamiltonianVectorField Ks y + J y (v - ω.hamiltonianVectorField Kt y)) -
    (-fderiv ℝ (ω.hamiltonianVectorField Ks) y e +
      fderiv ℝ J y e (v - ω.hamiltonianVectorField Kt y) +
      J y (d - fderiv ℝ (ω.hamiltonianVectorField Kt) y e))

/-- The coordinate expression of the remainder. -/
theorem floerRemainder_def (y v e d : V) :
    ω.floerRemainder J Ks Kt y v e d =
      (-ω.hamiltonianVectorField Ks (y + e) +
          J (y + e) (v + d - ω.hamiltonianVectorField Kt (y + e))) -
        (-ω.hamiltonianVectorField Ks y + J y (v - ω.hamiltonianVectorField Kt y)) -
        (-fderiv ℝ (ω.hamiltonianVectorField Ks) y e +
          fderiv ℝ J y e (v - ω.hamiltonianVectorField Kt y) +
          J y (d - fderiv ℝ (ω.hamiltonianVectorField Kt) y e)) :=
  (rfl)

/-- The remainder vanishes for the zero increment, whatever its slice velocity. -/
@[simp]
theorem floerRemainder_zero (y v d : V) :
    ω.floerRemainder J Ks Kt y v 0 d = 0 := by
  simp only [floerRemainder_def, add_zero, map_zero, zero_apply, sub_zero, map_add, map_sub]
  abel

/-- **The remainder of the Floer operator depends only on first-order data.** For maps `w` and
`ξ` differentiable at `z`, `F(w + ξ) - F(w) - D_w ξ` at `z` is the remainder, with the
coefficients frozen at `z`, at the values and slice velocities `∂t w(z)`, `∂t ξ(z)` of `w`
and `ξ`. -/
theorem floerOperator_add_sub_floerOperator_sub_floerLinearization
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (w ξ : ℝ × ℝ → V) {z : ℝ × ℝ}
    (hw : DifferentiableAt ℝ w z) (hξ : DifferentiableAt ℝ ξ z) :
    ω.floerOperator J Ks Kt (w + ξ) z - ω.floerOperator J Ks Kt w z -
        ω.floerLinearization J Ks Kt w ξ z =
      ω.floerRemainder (J z) (Ks z) (Kt z) (w z) (fderiv ℝ w z stdComplexLineImag) (ξ z)
        (fderiv ℝ ξ z stdComplexLineImag) := by
  simp only [floerOperator_def, floerLinearization_def, floerRemainder_def, fderiv_add hw hξ,
    add_apply, Pi.add_apply]
  abel

/-- **The difference of two remainders.** At a base point `y` with slice velocity `v`, the
difference of the remainders at `(e₁, d₁)` and `(e₂, d₂)` is the sum of

* minus the Taylor remainder of `X_Ks`, plus the Taylor remainder of `J` (applied to the slice
  defect `v - X_Kt(y)`), and minus `J(y)` applied to the Taylor remainder of `X_Kt`, all between
  `y + e₂` and `y + e₁`;
* `J(y + e₁) - J(y + e₂)` applied to `d₁ - (X_Kt(y + e₁) - X_Kt(y))`;
* `J(y + e₂) - J(y)` applied to `d₁ - d₂ - (X_Kt(y + e₁) - X_Kt(y + e₂))`.

Each of these is quadratically small in the increments and their slice velocities. -/
theorem floerRemainder_sub_floerRemainder (y v e₁ e₂ d₁ d₂ : V) :
    ω.floerRemainder J Ks Kt y v e₁ d₁ - ω.floerRemainder J Ks Kt y v e₂ d₂ =
      -(ω.hamiltonianVectorField Ks (y + e₁) - ω.hamiltonianVectorField Ks (y + e₂) -
          fderiv ℝ (ω.hamiltonianVectorField Ks) y (e₁ - e₂)) +
        (J (y + e₁) - J (y + e₂) - fderiv ℝ J y (e₁ - e₂))
          (v - ω.hamiltonianVectorField Kt y) +
        (J (y + e₁) - J (y + e₂))
          (d₁ - (ω.hamiltonianVectorField Kt (y + e₁) - ω.hamiltonianVectorField Kt y)) +
        (J (y + e₂) - J y)
          (d₁ - d₂ - (ω.hamiltonianVectorField Kt (y + e₁) -
            ω.hamiltonianVectorField Kt (y + e₂))) -
        J y (ω.hamiltonianVectorField Kt (y + e₁) -
          ω.hamiltonianVectorField Kt (y + e₂) -
            fderiv ℝ (ω.hamiltonianVectorField Kt) y (e₁ - e₂)) := by
  simp only [floerRemainder_def, sub_apply, map_sub, map_add]
  abel

/-! ### The quadratic estimate -/

/-- The quadratic estimate at one base point, from explicit bounds on the Taylor remainders and
increments of the coefficients. -/
private theorem norm_floerRemainder_sub_le_of_bounds {y v e₁ e₂ d₁ d₂ : V}
    {L Λ M : ℝ} (hL : 0 ≤ L) (hΛ : 0 ≤ Λ) (hM : ‖J y‖ ≤ M)
    (hs : ‖ω.hamiltonianVectorField Ks (y + e₁) - ω.hamiltonianVectorField Ks (y + e₂) -
      fderiv ℝ (ω.hamiltonianVectorField Ks) y (e₁ - e₂)‖ ≤
        L * max ‖e₁‖ ‖e₂‖ * ‖e₁ - e₂‖)
    (hj : ‖J (y + e₁) - J (y + e₂) - fderiv ℝ J y (e₁ - e₂)‖ ≤
      L * max ‖e₁‖ ‖e₂‖ * ‖e₁ - e₂‖)
    (ht : ‖ω.hamiltonianVectorField Kt (y + e₁) - ω.hamiltonianVectorField Kt (y + e₂) -
      fderiv ℝ (ω.hamiltonianVectorField Kt) y (e₁ - e₂)‖ ≤
        L * max ‖e₁‖ ‖e₂‖ * ‖e₁ - e₂‖)
    (hJ₁₂ : ‖J (y + e₁) - J (y + e₂)‖ ≤ Λ * ‖e₁ - e₂‖)
    (hJ₂ : ‖J (y + e₂) - J y‖ ≤ Λ * ‖e₂‖)
    (hX₁ : ‖ω.hamiltonianVectorField Kt (y + e₁) - ω.hamiltonianVectorField Kt y‖ ≤
      Λ * ‖e₁‖)
    (hX₁₂ : ‖ω.hamiltonianVectorField Kt (y + e₁) -
      ω.hamiltonianVectorField Kt (y + e₂)‖ ≤ Λ * ‖e₁ - e₂‖) :
    ‖ω.floerRemainder J Ks Kt y v e₁ d₁ - ω.floerRemainder J Ks Kt y v e₂ d₂‖ ≤
      (L * (1 + M) + 2 * Λ ^ 2 + Λ) *
        (max ‖e₁‖ ‖e₂‖ * (1 + ‖v - ω.hamiltonianVectorField Kt y‖) * ‖e₁ - e₂‖ +
          ‖e₁ - e₂‖ * ‖d₁‖ + ‖e₂‖ * ‖d₁ - d₂‖) := by
  set m := max ‖e₁‖ ‖e₂‖
  set a := ‖v - ω.hamiltonianVectorField Kt y‖
  set δe := ‖e₁ - e₂‖
  have hm₁ : ‖e₁‖ ≤ m := le_max_left _ _
  have hm₂ : ‖e₂‖ ≤ m := le_max_right _ _
  have hmd : 0 ≤ m * δe := mul_nonneg ((norm_nonneg _).trans hm₁) (norm_nonneg _)
  have ha : 0 ≤ a := norm_nonneg _
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  -- Bound the five terms of `floerRemainder_sub_floerRemainder` one by one.
  have h₂ : ‖(J (y + e₁) - J (y + e₂) - fderiv ℝ J y (e₁ - e₂))
      (v - ω.hamiltonianVectorField Kt y)‖ ≤ L * (m * δe) * a :=
    (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (by linarith) ha)
  have h₃ : ‖(J (y + e₁) - J (y + e₂))
      (d₁ - (ω.hamiltonianVectorField Kt (y + e₁) - ω.hamiltonianVectorField Kt y))‖ ≤
        Λ * δe * (‖d₁‖ + Λ * m) := by
    refine (le_opNorm _ _).trans (mul_le_mul hJ₁₂ ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
      (mul_nonneg hΛ (norm_nonneg _)))
    nlinarith
  have h₄ : ‖(J (y + e₂) - J y)
      (d₁ - d₂ - (ω.hamiltonianVectorField Kt (y + e₁) -
        ω.hamiltonianVectorField Kt (y + e₂)))‖ ≤ Λ * ‖e₂‖ * (‖d₁ - d₂‖ + Λ * δe) :=
    (le_opNorm _ _).trans (mul_le_mul hJ₂ ((norm_sub_le _ _).trans (by linarith))
      (norm_nonneg _) (mul_nonneg hΛ (norm_nonneg _)))
  have h₅ : ‖J y (ω.hamiltonianVectorField Kt (y + e₁) -
      ω.hamiltonianVectorField Kt (y + e₂) -
        fderiv ℝ (ω.hamiltonianVectorField Kt) y (e₁ - e₂))‖ ≤ M * (L * (m * δe)) :=
    (le_opNorm _ _).trans (mul_le_mul hM (by linarith) (norm_nonneg _) hM0)
  rw [floerRemainder_sub_floerRemainder]
  have h₁ : ‖-(ω.hamiltonianVectorField Ks (y + e₁) -
      ω.hamiltonianVectorField Ks (y + e₂) -
        fderiv ℝ (ω.hamiltonianVectorField Ks) y (e₁ - e₂))‖ ≤ L * (m * δe) := by
    rw [norm_neg, ← mul_assoc]
    exact hs
  -- Compare each term with its piece of the target, using `‖e₂‖ ≤ m` and `0 ≤ a`.
  have hX : m * δe ≤ m * (1 + a) * δe := by nlinarith [mul_nonneg hmd ha]
  have he₂X : ‖e₂‖ * δe ≤ m * (1 + a) * δe :=
    (mul_le_mul_of_nonneg_right hm₂ (norm_nonneg _)).trans hX
  have hpos : 0 ≤ Λ * (m * (1 + a) * δe) +
      (L * (1 + M) + 2 * Λ ^ 2) * (δe * ‖d₁‖ + ‖e₂‖ * ‖d₁ - d₂‖) :=
    add_nonneg (mul_nonneg hΛ (hmd.trans hX))
      (mul_nonneg (by positivity) (by positivity))
  calc _ ≤ L * (m * δe) + L * (m * δe) * a + Λ * δe * (‖d₁‖ + Λ * m) +
        Λ * ‖e₂‖ * (‖d₁ - d₂‖ + Λ * δe) + M * (L * (m * δe)) :=
      norm_sub_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le h₁ h₂) h₃) h₄) h₅
    _ = L * (m * (1 + a) * δe) + M * L * (m * δe) + Λ * (δe * ‖d₁‖) + Λ ^ 2 * (m * δe) +
        Λ * (‖e₂‖ * ‖d₁ - d₂‖) + Λ ^ 2 * (‖e₂‖ * δe) := by ring
    _ ≤ L * (m * (1 + a) * δe) + M * L * (m * (1 + a) * δe) + Λ * (δe * ‖d₁‖) +
        Λ ^ 2 * (m * (1 + a) * δe) + Λ * (‖e₂‖ * ‖d₁ - d₂‖) + Λ ^ 2 * (m * (1 + a) * δe) := by
      gcongr
    _ ≤ (L * (1 + M) + 2 * Λ ^ 2 + Λ) * (m * (1 + a) * δe + δe * ‖d₁‖ + ‖e₂‖ * ‖d₁ - d₂‖) := by
      linear_combination hpos

end Remainder

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {J : P → V → V →L[ℝ] V} {Ks Kt : P → V → ℝ} {K : Set (P × V)}

/-- **The quadratic estimate for the Floer remainder.** Let the coefficients depend on a parameter
`p`, and let `K` be a compact set of pairs `(p, y)` of a parameter and a target point at which `J`
is jointly `C²` and the Hamiltonians `Ks`, `Kt` are jointly `C³`. There are `δ > 0` and `C` such
that for every `(p, y) ∈ K`, every slice velocity `v` and all increments `e₁`, `e₂` of norm at
most `δ` with slice velocities `d₁`, `d₂`, the remainders with coefficients `J p`, `Ks p`, `Kt p`
differ by at most
`C (max ‖e₁‖ ‖e₂‖ (1 + ‖v - X_Kt(y)‖) ‖e₁ - e₂‖ + ‖e₁ - e₂‖ ‖d₁‖ + ‖e₂‖ ‖d₁ - d₂‖)`. -/
theorem exists_pos_forall_norm_floerRemainder_sub_le (hK : IsCompact K)
    (hJ : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry J) q)
    (hKs : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Ks) q)
    (hKt : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Kt) q) :
    ∃ δ > 0, ∃ C, ∀ p y, (p, y) ∈ K → ∀ v e₁ e₂ d₁ d₂ : V, ‖e₁‖ ≤ δ → ‖e₂‖ ≤ δ →
      ‖ω.floerRemainder (J p) (Ks p) (Kt p) y v e₁ d₁ -
          ω.floerRemainder (J p) (Ks p) (Kt p) y v e₂ d₂‖ ≤
        C * (max ‖e₁‖ ‖e₂‖ * (1 + ‖v - ω.hamiltonianVectorField (Kt p) y‖) * ‖e₁ - e₂‖ +
          ‖e₁ - e₂‖ * ‖d₁‖ + ‖e₂‖ * ‖d₁ - d₂‖) := by
  -- The coefficients as families over the pairs `q = (p, y)`, based at `y`.
  have hsnd : ContinuousOn (fun q : P × V ↦ q.2) K := continuous_snd.continuousOn
  have hFJ : ∀ q ∈ K,
      ContDiffAt ℝ 2 (Function.uncurry fun (q : P × V) (y : V) ↦ J q.1 y) (q, q.2) :=
    fun q hq ↦ (hJ q hq).comp (q, q.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hFS : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry fun (q : P × V) (y : V) ↦
      ω.hamiltonianVectorField (Ks q.1) y) (q, q.2) :=
    fun q hq ↦ (ω.contDiffAt_hamiltonianVectorField_uncurry (n := 2) (hKs q hq)).comp (q, q.2)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hFT : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry fun (q : P × V) (y : V) ↦
      ω.hamiltonianVectorField (Kt q.1) y) (q, q.2) :=
    fun q hq ↦ (ω.contDiffAt_hamiltonianVectorField_uncurry (n := 2) (hKt q hq)).comp (q, q.2)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  obtain ⟨δJ, hδJ, LJ, hLJ⟩ := hK.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul hFJ hsnd
  obtain ⟨δS, hδS, LS, hLS⟩ := hK.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul hFS hsnd
  obtain ⟨δT, hδT, LT, hLT⟩ := hK.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul hFT hsnd
  obtain ⟨δJ', hδJ', ΛJ, hΛJ⟩ := hK.exists_pos_forall_norm_sub_le_mul_norm_sub
    (fun q hq ↦ (hFJ q hq).of_le (by norm_num)) hsnd
  obtain ⟨δT', hδT', ΛT, hΛT⟩ := hK.exists_pos_forall_norm_sub_le_mul_norm_sub
    (fun q hq ↦ (hFT q hq).of_le (by norm_num)) hsnd
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (continuousOn_of_forall_continuousAt fun q hq ↦ (hJ q hq).continuousAt)
  -- Common radius and constants for the three Taylor remainders and the two Lipschitz bounds.
  set δ := min (min δJ (min δS δT)) (min δJ' δT')
  set L := max (max LJ LS) (max LT 0)
  set Λ := max (max ΛJ ΛT) 0
  have hδ : 0 < δ := lt_min (lt_min hδJ (lt_min hδS hδT)) (lt_min hδJ' hδT')
  have hL : 0 ≤ L := le_max_of_le_right (le_max_right _ _)
  have hΛ : 0 ≤ Λ := le_max_right _ _
  refine ⟨δ, hδ, L * (1 + M) + 2 * Λ ^ 2 + Λ, fun p y hpy v e₁ e₂ d₁ d₂ he₁ he₂ => ?_⟩
  have h₁ : ‖e₁‖ ≤ δ := he₁
  have h₂ : ‖e₂‖ ≤ δ := he₂
  have h0 : ‖(0 : V)‖ ≤ δ := by simpa using hδ.le
  have hδJ₁ : δ ≤ δJ := (min_le_left _ _).trans (min_le_left _ _)
  have hδS₁ : δ ≤ δS := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδT₁ : δ ≤ δT := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδJ₂ : δ ≤ δJ' := (min_le_right _ _).trans (min_le_left _ _)
  have hδT₂ : δ ≤ δT' := (min_le_right _ _).trans (min_le_right _ _)
  have hr : 0 ≤ max ‖e₁‖ ‖e₂‖ * ‖e₁ - e₂‖ :=
    mul_nonneg ((norm_nonneg _).trans (le_max_left _ _)) (norm_nonneg _)
  -- Raise each constant to the common one.
  have hquad {N L₀ : ℝ} (hL₀ : L₀ ≤ L) (hN : N ≤ L₀ * max ‖e₁‖ ‖e₂‖ * ‖e₁ - e₂‖) :
      N ≤ L * max ‖e₁‖ ‖e₂‖ * ‖e₁ - e₂‖ := by
    rw [mul_assoc] at hN ⊢
    exact hN.trans (mul_le_mul_of_nonneg_right hL₀ hr)
  have hlip {N Λ₀ r : ℝ} (hΛ₀ : Λ₀ ≤ Λ) (hr : 0 ≤ r) (hN : N ≤ Λ₀ * r) : N ≤ Λ * r :=
    hN.trans (mul_le_mul_of_nonneg_right hΛ₀ hr)
  have hΛJ₀ : ΛJ ≤ Λ := (le_max_left _ _).trans (le_max_left _ _)
  have hΛT₀ : ΛT ≤ Λ := (le_max_right _ _).trans (le_max_left _ _)
  refine norm_floerRemainder_sub_le_of_bounds ω (J p) (Ks p) (Kt p) hL hΛ (hM (p, y) hpy)
    (hquad ((le_max_right _ _).trans (le_max_left _ _))
      (hLS (p, y) hpy e₁ e₂ (h₁.trans hδS₁) (h₂.trans hδS₁)))
    (hquad ((le_max_left _ _).trans (le_max_left _ _))
      (hLJ (p, y) hpy e₁ e₂ (h₁.trans hδJ₁) (h₂.trans hδJ₁)))
    (hquad ((le_max_left _ _).trans (le_max_right _ _))
      (hLT (p, y) hpy e₁ e₂ (h₁.trans hδT₁) (h₂.trans hδT₁)))
    (hlip hΛJ₀ (norm_nonneg _) (hΛJ (p, y) hpy e₁ e₂ (h₁.trans hδJ₂) (h₂.trans hδJ₂)))
    (hlip hΛJ₀ (norm_nonneg _) (by
      simpa using hΛJ (p, y) hpy e₂ 0 (h₂.trans hδJ₂) (h0.trans hδJ₂)))
    (hlip hΛT₀ (norm_nonneg _) (by
      simpa using hΛT (p, y) hpy e₁ 0 (h₁.trans hδT₂) (h0.trans hδT₂)))
    (hlip hΛT₀ (norm_nonneg _) (hΛT (p, y) hpy e₁ e₂ (h₁.trans hδT₂) (h₂.trans hδT₂)))

/-- **The quadratic estimate for the Floer operator.** Let `K` be a compact set of pairs `(p, y)`
of a parameter and a target point at which `J` is jointly `C²` and the Hamiltonians `Ks`, `Kt`
are jointly `C³`. There are `δ > 0` and `C` such that for every parameter map `φ : ℝ × ℝ → P` and
maps `w`, `ξ₁`, `ξ₂` differentiable at a domain point `z` with `(φ z, w z) ∈ K` and
`‖ξ₁ z‖, ‖ξ₂ z‖ ≤ δ`, the Floer operator with coefficients `J (φ z)`, `Ks (φ z)`, `Kt (φ z)`
satisfies
`‖F(w + ξ₁) - F(w + ξ₂) - D_w(ξ₁ - ξ₂)‖ ≤ C (max ‖ξ₁‖ ‖ξ₂‖ (1 + ‖∂t w - X_Kt(w)‖) ‖ξ₁ - ξ₂‖
  + ‖ξ₁ - ξ₂‖ ‖∂t ξ₁‖ + ‖ξ₂‖ ‖∂t ξ₁ - ∂t ξ₂‖)` at `z`. This is the Lipschitz bound on the
nonlinear part of the Floer operator used by the Newton iteration. -/
theorem exists_pos_forall_norm_floerOperator_sub_floerOperator_sub_floerLinearization_le
    (hK : IsCompact K) (hJ : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry J) q)
    (hKs : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Ks) q)
    (hKt : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Kt) q) :
    ∃ δ > 0, ∃ C, ∀ (φ : ℝ × ℝ → P) (w ξ₁ ξ₂ : ℝ × ℝ → V) (z : ℝ × ℝ),
      DifferentiableAt ℝ w z → DifferentiableAt ℝ ξ₁ z → DifferentiableAt ℝ ξ₂ z →
      (φ z, w z) ∈ K → ‖ξ₁ z‖ ≤ δ → ‖ξ₂ z‖ ≤ δ →
      ‖ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₁) z -
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₂) z -
          ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w
            (ξ₁ - ξ₂) z‖ ≤
        C * (max ‖ξ₁ z‖ ‖ξ₂ z‖ *
            (1 + ‖fderiv ℝ w z stdComplexLineImag - ω.hamiltonianVectorField (Kt (φ z)) (w z)‖) *
            ‖ξ₁ z - ξ₂ z‖ +
          ‖ξ₁ z - ξ₂ z‖ * ‖fderiv ℝ ξ₁ z stdComplexLineImag‖ +
          ‖ξ₂ z‖ * ‖fderiv ℝ ξ₁ z stdComplexLineImag - fderiv ℝ ξ₂ z stdComplexLineImag‖) := by
  obtain ⟨δ, hδ, C, hC⟩ := ω.exists_pos_forall_norm_floerRemainder_sub_le hK hJ hKs hKt
  refine ⟨δ, hδ, C, fun φ w ξ₁ ξ₂ z hw hξ₁ hξ₂ hzw hξ₁δ hξ₂δ => ?_⟩
  have h₁ := ω.floerOperator_add_sub_floerOperator_sub_floerLinearization
    (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w ξ₁ hw hξ₁
  have h₂ := ω.floerOperator_add_sub_floerOperator_sub_floerLinearization
    (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w ξ₂ hw hξ₂
  rw [floerLinearization_sub ω _ _ _ w ξ₁ ξ₂ z hξ₁ hξ₂]
  convert hC (φ z) (w z) hzw _ (ξ₁ z) (ξ₂ z) _ _ hξ₁δ hξ₂δ using 2
  rw [← h₁, ← h₂]
  abel

/-- **The quadratic estimate for the Floer operator at a map.** Let `K` be a compact set of pairs
`(p, y)` of a parameter and a target point at which `J` is jointly `C²` and the Hamiltonians `Ks`,
`Kt` are jointly `C³`. There are `δ > 0` and `C` such that for every parameter map
`φ : ℝ × ℝ → P` and maps `w`, `ξ` differentiable at a domain point `z` with `(φ z, w z) ∈ K` and
`‖ξ z‖ ≤ δ`, the Floer operator with coefficients `J (φ z)`, `Ks (φ z)`, `Kt (φ z)` satisfies
`‖F(w + ξ) - F(w) - D_w ξ‖ ≤ C (‖ξ‖² (1 + ‖∂t w - X_Kt(w)‖) + ‖ξ‖ ‖∂t ξ‖)` at `z`. -/
theorem exists_pos_forall_norm_floerOperator_add_sub_floerOperator_sub_floerLinearization_le
    (hK : IsCompact K) (hJ : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry J) q)
    (hKs : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Ks) q)
    (hKt : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Kt) q) :
    ∃ δ > 0, ∃ C, ∀ (φ : ℝ × ℝ → P) (w ξ : ℝ × ℝ → V) (z : ℝ × ℝ), DifferentiableAt ℝ w z →
      DifferentiableAt ℝ ξ z → (φ z, w z) ∈ K → ‖ξ z‖ ≤ δ →
      ‖ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ) z -
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w z -
          ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w ξ z‖ ≤
        C * (‖ξ z‖ ^ 2 *
            (1 + ‖fderiv ℝ w z stdComplexLineImag - ω.hamiltonianVectorField (Kt (φ z)) (w z)‖) +
          ‖ξ z‖ * ‖fderiv ℝ ξ z stdComplexLineImag‖) := by
  obtain ⟨δ, hδ, C, hC⟩ := ω.exists_pos_forall_norm_floerRemainder_sub_le hK hJ hKs hKt
  refine ⟨δ, hδ, C, fun φ w ξ z hw hξ hzw hξδ => ?_⟩
  have h := hC (φ z) (w z) hzw (fderiv ℝ w z stdComplexLineImag) (ξ z) 0
    (fderiv ℝ ξ z stdComplexLineImag) 0 hξδ (by simpa using hδ.le)
  rw [floerRemainder_zero, sub_zero] at h
  rw [ω.floerOperator_add_sub_floerOperator_sub_floerLinearization
    (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w ξ hw hξ]
  convert h using 2
  simp only [norm_zero, max_eq_left (norm_nonneg _), sub_zero, zero_mul, add_zero]
  ring

end TauCeti.SymplecticForm
