/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.Analysis.Analytic.Complexification.Basic
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Polynomial.Monic.RootBound
import TauCeti.Analysis.Polynomial.Order
import TauCeti.Geometry.RealAlgebraic.Nash.Holomorphic
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Complex
import TauCeti.RingTheory.Polynomial.Monic.Roots

/-!
# The Nash Weierstrass preparation and division theorems

Let `f : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite,
and suppose that the vertical slice `t ↦ f (Sum.elim x₀ (fun _ ↦ t))` vanishes to finite order `d`
at `t₀`. By the real analytic Weierstrass preparation theorem
(`AnalyticAt.exists_weierstrassPreparation_real`), near `p₀` one can write
`f p = P_{p ∘ Sum.inl} (p (.inr ()) - t₀) * u p`, where `P_x` is the monic polynomial
`TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i x)` of degree `d` with real analytic lower
coefficients `c i` vanishing at `x₀`, and `u` is real analytic and nonvanishing at `p₀`. This file
proves that the coefficients `c i` and the unit `u` are Nash germs, and proves the corresponding
Nash Weierstrass division theorems.

## Mathematical overview

A single polynomial relation `Q(x, t, f(x, t)) = 0` for `f` does not directly cut out the
Weierstrass polynomial `P_x`: conjugate algebraic branches of `Q` may also vanish at `(x₀, t₀)`,
contributing extraneous factors to `Q(x, t, 0)` that are invisible to the analytic germ `f`.
Separating the roots belonging to the chosen analytic branch requires working in the complex domain
and isolating the local root cluster on a disk:

1. **Holomorphic-Nash extension.** Complexifying `f`, `c i`, and `u` gives a complex Weierstrass
   factorization `F (z, w) = P_z (w - w₀) * U (z, w)` near `(z₀, w₀)` in which `F` is
   holomorphic-Nash (`TauCeti.IsHolomorphicNashAt`, `TauCeti.IsNashAt.exists_isHolomorphicNashAt`),
   as are all iterated vertical derivatives of `F`
   (`TauCeti.IsHolomorphicNashAt.iteratedDeriv_vertical`).
2. **Root-cluster isolation and first-order characterization.** After translating `w₀` to `0`,
   choose a disk `ball 0 R ⊆ ℂ` on which `U (z, ·)` is nonvanishing and shrink the base
   neighbourhood `B_X` so that `‖c i z‖ ≤ (R / 4) ^ (d - i)`. By Fujiwara's root bound
   (`TauCeti.Polynomial.mem_ball_of_isRoot_monicOfCoeff`), every complex root of `P_z` lies in
   `ball 0 R`. Because `ℂ` is algebraically closed, a monic degree-`d` polynomial `monicOfCoeff a`
   coincides with `P_z` if and only if all of its roots lie in `ball 0 R` and, at every
   `w ∈ ball 0 R`, its Hasse derivatives below each order `k ≤ d` vanish simultaneously with the
   vertical derivatives of `F (z, ·)`
   (`TauCeti.Polynomial.eq_of_monicOfCoeff_forall_hasseDeriv_iff`).
3. **Elimination and exact division.** Universal quantifier elimination over the real and imaginary
   parts of `w` (`TauCeti.IsSemialgebraic.setOf_forall_sumElim`) makes the graph of `z ↦ c · z`
   semialgebraic on `B_X`, so the local holomorphic-Nash graph criterion
   (`TauCeti.forall_isHolomorphicNashAt_apply_iff_exists_isSemialgebraicOn`) upgrades each `c i`.
   Exact analytic division (`TauCeti.IsHolomorphicNashAt.of_mul_eventuallyEq`) then upgrades `U`.
   Weierstrass division is proved analogously: matching Taylor jets at every root of `P_z` inside
   `ball 0 R` characterizes the degree-`< d` remainder uniquely over `ℂ`
   (`TauCeti.Polynomial.eq_of_sum_monomial_forall_hasseDeriv_eq`).

## Main results

* `TauCeti.IsNashAt.of_weierstrassPreparation`, `TauCeti.IsNashAt.exists_weierstrassPreparation`:
  **Nash Weierstrass preparation.**
* `TauCeti.IsNashAt.of_weierstrassDivision_monicOfCoeff`,
  `TauCeti.IsNashAt.exists_weierstrassDivision_monicOfCoeff`,
  `TauCeti.IsNashAt.of_weierstrassDivision`,
  `TauCeti.IsNashAt.exists_weierstrassDivision`: **Nash Weierstrass division** by a Nash
  Weierstrass polynomial, and by any Nash germ whose vertical slice has finite order.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Section 8.1 (Nash functions) and Proposition 8.1.8.
* S. G. Krantz, H. R. Parks, *A Primer of Real Analytic Functions*, second edition, Birkhäuser,
  2002, Section 6.1.
* S. Łojasiewicz, *Introduction to Complex Analytic Geometry*, Birkhäuser, 1991.
-/

public section

open Filter Metric Polynomial Topology

namespace TauCeti

/-! ### Semialgebraicity of complex polynomial Hasse derivatives and jet intersections -/

section SemialgebraicComplexPoly

private theorem continuous_sumElim_const {σ : Type*} (z : σ → ℂ) :
    Continuous fun w : ℂ ↦ Sum.elim z (fun _ : Unit ↦ w) :=
  continuous_pi (Sum.rec (fun _ ↦ continuous_const) (fun _ ↦ continuous_id))

private theorem analyticAt_sumElim_const {σ : Type*} [Fintype σ] (z : σ → ℂ) (w₀ : ℂ) :
    AnalyticAt ℂ (fun w : ℂ ↦ Sum.elim z (fun _ : Unit ↦ w)) w₀ :=
  AnalyticAt.pi (Sum.rec (fun _ ↦ analyticAt_const) (fun _ ↦ analyticAt_id))

/-- Real coordinates `(x_ℝ, a_ℝ, w_ℝ)` for base `σ → ℂ`, coefficients `Fin d → ℂ`, and fiber `ℂ`. -/
private abbrev ElimCoord (σ : Type*) (d : ℕ) : Type _ :=
  ((σ ⊕ σ) ⊕ (Fin d ⊕ Fin d)) ⊕ (Unit ⊕ Unit) → ℝ

/-- The complex multivariate polynomial representing the `j`-th Hasse derivative of
`monicOfCoeff a` evaluated at `w`, in coordinates `Sum.elim a (fun _ : Unit ↦ w)`. -/
private noncomputable def hasseDerivMonicMvPoly (d j : ℕ) : MvPolynomial (Fin d ⊕ Unit) ℂ :=
  MvPolynomial.C (d.choose j : ℂ) * MvPolynomial.X (Sum.inr ()) ^ (d - j) +
    ∑ i : Fin d, MvPolynomial.C ((i : ℕ).choose j : ℂ) *
      MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr ()) ^ ((i : ℕ) - j)

private theorem eval_hasseDerivMonicMvPoly {d : ℕ} (j : ℕ) (a : Fin d → ℂ) (w : ℂ) :
    MvPolynomial.eval (Sum.elim a (fun _ : Unit ↦ w)) (hasseDerivMonicMvPoly d j) =
      (hasseDeriv j (Polynomial.monicOfCoeff a)).eval w := by
  have hXd : (_root_.Polynomial.X ^ d : ℂ[X]) = monomial d 1 := by
    rw [← C_mul_X_pow_eq_monomial, C_1, one_mul]
  rw [Polynomial.monicOfCoeff_def, hXd, map_add, map_sum, eval_add, eval_finsetSum]
  simp only [hasseDeriv_monomial, mul_one, eval_monomial, hasseDerivMonicMvPoly, map_add, map_mul,
    map_pow, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]

/-- The complex multivariate polynomial representing `j !` times the `j`-th Hasse derivative of
`∑ i : Fin d, monomial i (b i)` evaluated at `w`. -/
private noncomputable def factorialHasseDerivSumMvPoly (d j : ℕ) : MvPolynomial (Fin d ⊕ Unit) ℂ :=
  MvPolynomial.C (Nat.factorial j : ℂ) *
    ∑ i : Fin d, MvPolynomial.C ((i : ℕ).choose j : ℂ) *
      MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr ()) ^ ((i : ℕ) - j)

private theorem eval_factorialHasseDerivSumMvPoly {d : ℕ} (j : ℕ) (b : Fin d → ℂ) (w : ℂ) :
    MvPolynomial.eval (Sum.elim b (fun _ : Unit ↦ w)) (factorialHasseDerivSumMvPoly d j) =
      (Nat.factorial j : ℂ) *
        (hasseDeriv j (∑ i : Fin d, monomial (i : ℕ) (b i))).eval w := by
  rw [map_sum, eval_finsetSum, factorialHasseDerivSumMvPoly]
  simp only [hasseDeriv_monomial, eval_monomial, map_mul, map_pow, map_sum, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]

/-- The open disk `ball (0 : ℂ) R` read in `Unit ⊕ Unit → ℝ` coordinates via
`complexToRealPi Unit`. -/
private def realDiskSet (R : ℝ) : Set (Unit ⊕ Unit → ℝ) :=
  {w_ℝ | w_ℝ (Sum.inl ()) ^ 2 + w_ℝ (Sum.inr ()) ^ 2 < R ^ 2}

private theorem isSemialgebraic_realDiskSet (R : ℝ) : IsSemialgebraic (realDiskSet R) := by
  let p : MvPolynomial (Unit ⊕ Unit) ℝ :=
    MvPolynomial.X (Sum.inl ()) ^ 2 + MvPolynomial.X (Sum.inr ()) ^ 2
  convert isSemialgebraic_eval_lt p (MvPolynomial.C (R ^ 2)) using 1
  ext w_ℝ
  simp [realDiskSet, p]

private theorem mem_realDiskSet_iff {R : ℝ} (hR : 0 < R) (w_ℝ : Unit ⊕ Unit → ℝ) :
    w_ℝ ∈ realDiskSet R ↔ (complexToRealPi Unit).symm w_ℝ () ∈ ball (0 : ℂ) R := by
  set w : ℂ := (complexToRealPi Unit).symm w_ℝ ()
  have hsq : w_ℝ (Sum.inl ()) ^ 2 + w_ℝ (Sum.inr ()) ^ 2 = ‖w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [w, sq]
  rw [realDiskSet, Set.mem_ofPred, hsq, mem_ball_zero_iff, sq_lt_sq₀ (norm_nonneg w) hR.le]

private theorem complexToRealPi_unit_symm_const (w : ℂ) :
    (complexToRealPi Unit).symm (complexToRealPi Unit (fun _ ↦ w)) () = w := by
  simp

private theorem mem_ball_iff_complexToRealPi_mem_realDiskSet {R : ℝ} (hR : 0 < R) (w : ℂ) :
    w ∈ ball (0 : ℂ) R ↔ complexToRealPi Unit (fun _ ↦ w) ∈ realDiskSet R := by
  rw [mem_realDiskSet_iff hR, complexToRealPi_unit_symm_const]

/-- Regroup `ElimCoord σ d` onto the base-and-vertical real coordinates
`(σ ⊕ Unit) ⊕ (σ ⊕ Unit)`. -/
private def projXW (σ : Type*) (d : ℕ) :
    (σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ((σ ⊕ σ) ⊕ (Fin d ⊕ Fin d)) ⊕ (Unit ⊕ Unit)
  | .inl (.inl s) => .inl (.inl (.inl s))
  | .inl (.inr ()) => .inr (.inl ())
  | .inr (.inl s) => .inl (.inl (.inr s))
  | .inr (.inr ()) => .inr (.inr ())

/-- Regroup `ElimCoord σ d` onto the coefficient-and-vertical real coordinates
`(Fin d ⊕ Unit) ⊕ (Fin d ⊕ Unit)`. -/
private def projAW (σ : Type*) (d : ℕ) :
    (Fin d ⊕ Unit) ⊕ (Fin d ⊕ Unit) → ((σ ⊕ σ) ⊕ (Fin d ⊕ Fin d)) ⊕ (Unit ⊕ Unit)
  | .inl (.inl i) => .inl (.inr (.inl i))
  | .inl (.inr ()) => .inr (.inl ())
  | .inr (.inl i) => .inl (.inr (.inr i))
  | .inr (.inr ()) => .inr (.inr ())

private theorem symm_comp_projXW {σ : Type*} [Fintype σ] {d : ℕ} (u : ElimCoord σ d) :
    (complexToRealPi (σ ⊕ Unit)).symm (u ∘ projXW σ d) =
      Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
        (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ()) := by
  ext (_ | ⟨⟩) <;> simp [projXW]

private theorem symm_comp_projAW {σ : Type*} {d : ℕ} (u : ElimCoord σ d) :
    (complexToRealPi (Fin d ⊕ Unit)).symm (u ∘ projAW σ d) =
      Sum.elim ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr))
        (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ()) := by
  ext (_ | ⟨⟩) <;> simp [projAW]

/-- Cylinder inside `ElimCoord σ d` over `B_X : Set (σ ⊕ σ → ℝ)` and `realDiskSet R`. -/
private abbrev elimCylSet (σ : Type*) (d : ℕ) (B_X : Set (σ ⊕ σ → ℝ)) (R : ℝ) :
    Set (ElimCoord σ d) :=
  ((fun u ↦ u ∘ (Sum.inl ∘ Sum.inl)) ⁻¹' B_X) ∩ ((fun u ↦ u ∘ Sum.inr) ⁻¹' realDiskSet R)

private theorem isSemialgebraic_elimCylSet {σ : Type*} {d : ℕ} {B_X : Set (σ ⊕ σ → ℝ)}
    (hBX : IsSemialgebraic B_X) (R : ℝ) :
    IsSemialgebraic (elimCylSet σ d B_X R) :=
  (hBX.preimage_comp (Sum.inl ∘ Sum.inl)).inter
    ((isSemialgebraic_realDiskSet R).preimage_comp Sum.inr)

private theorem mem_elimCylSet_iff {σ : Type*} {d : ℕ} {B_X : Set (σ ⊕ σ → ℝ)} {R : ℝ}
    (u : ElimCoord σ d) :
    ((u ∘ Sum.inl) ∘ Sum.inl ∈ B_X ∧ u ∘ Sum.inr ∈ realDiskSet R) ↔
      u ∈ elimCylSet σ d B_X R := by
  simp [elimCylSet, Function.comp_def]

/-- Pulling an `IsSemialgebraicOn` map from `W` back to `elimCylSet σ d B_X R`. -/
private theorem isSemialgebraicOn_comp_projXW {σ : Type*} [Fintype σ] {d : ℕ}
    {H : (σ ⊕ Unit → ℂ) → ℂ} {W : Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ)}
    {B_X : Set (σ ⊕ σ → ℝ)} {R : ℝ}
    (hBX : IsSemialgebraic B_X)
    (hHW : IsSemialgebraicOn
      (fun q ↦ complexToRealPi Unit (fun _ ↦ H ((complexToRealPi (σ ⊕ Unit)).symm q))) W)
    (hsub : ∀ u : ElimCoord σ d,
      (u ∘ Sum.inl) ∘ Sum.inl ∈ B_X → u ∘ Sum.inr ∈ realDiskSet R → u ∘ projXW σ d ∈ W) :
    IsSemialgebraicOn
      (fun u : ElimCoord σ d ↦ complexToRealPi Unit
        (fun _ ↦ H (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
          (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ()))))
      (elimCylSet σ d B_X R) := by
  have hdom : IsSemialgebraic (elimCylSet σ d B_X R) := isSemialgebraic_elimCylSet hBX R
  have hproj : IsSemialgebraicOn (fun u ↦ u ∘ projXW σ d) (elimCylSet σ d B_X R) := by
    simpa [Function.comp_def] using
      isSemialgebraicOn_eval (fun t ↦ (MvPolynomial.X (projXW σ d t) : MvPolynomial _ ℝ)) hdom
  convert hHW.comp hproj (fun u hu ↦ hsub u hu.1 hu.2) using 1
  funext u
  simp only [Function.comp_apply, symm_comp_projXW]

/-- Pulling a complex polynomial on `Fin d ⊕ Unit → ℂ` back to any semialgebraic subset of
`ElimCoord σ d`. -/
private theorem isSemialgebraicOn_eval_comp_projAW {σ : Type*} {d : ℕ}
    (P : MvPolynomial (Fin d ⊕ Unit) ℂ) {S : Set (ElimCoord σ d)} (hS : IsSemialgebraic S) :
    IsSemialgebraicOn
      (fun u : ElimCoord σ d ↦ complexToRealPi Unit
        (fun _ ↦ MvPolynomial.eval
          (Sum.elim ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr))
            (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) P)) S := by
  have hproj : IsSemialgebraicMap (fun u : ElimCoord σ d ↦ u ∘ projAW σ d) := by
    simpa [Function.comp_def] using
      isSemialgebraicMap_eval (fun t ↦ (MvPolynomial.X (projAW σ d t) : MvPolynomial _ ℝ))
  convert ((isSemialgebraicMap_complexToRealPi_eval (fun _ : Unit ↦ P)).comp
    hproj).isSemialgebraicOn hS using 1
  funext u
  simp only [Function.comp_apply, symm_comp_projAW]

/-- Finite intersection over `j : Fin k` of the locus inside `U` where two `(d + 1)`-jets of
complex-valued functions agree at order `j`. -/
private def jetEqOnSet {κ : Type*} {d : ℕ} (U : Set (κ → ℝ))
    (L M : Fin (d + 1) → (κ → ℝ) → ℂ) (k : Fin (d + 1)) : Set (κ → ℝ) :=
  ⋂ j : Fin (k : ℕ), U ∩ {u | L ⟨j, j.2.trans k.2⟩ u = M ⟨j, j.2.trans k.2⟩ u}

private theorem isSemialgebraic_jetEqOnSet {κ : Type*} {d : ℕ} {U : Set (κ → ℝ)}
    {L M : Fin (d + 1) → (κ → ℝ) → ℂ}
    (hL : ∀ j, IsSemialgebraicOn (fun u ↦ complexToRealPi Unit (fun _ ↦ L j u)) U)
    (hM : ∀ j, IsSemialgebraicOn (fun u ↦ complexToRealPi Unit (fun _ ↦ M j u)) U)
    (k : Fin (d + 1)) :
    IsSemialgebraic (jetEqOnSet U L M k) := by
  refine .iInter fun j ↦ ?_
  let j' : Fin (d + 1) := ⟨j, j.2.trans k.2⟩
  convert (hL j').isSemialgebraic_inter_setOf_eq (hM j') using 1
  ext u
  simp [j', funext_iff, Complex.ext_iff]

private theorem forall_eq_iff_mem_jetEqOnSet {κ : Type*} {d : ℕ} {U : Set (κ → ℝ)}
    {L M : Fin (d + 1) → (κ → ℝ) → ℂ} {k : Fin (d + 1)} {u : κ → ℝ} (hu : u ∈ U) :
    (∀ j : Fin (k : ℕ), L ⟨j, j.2.trans k.2⟩ u = M ⟨j, j.2.trans k.2⟩ u) ↔
      u ∈ jetEqOnSet U L M k := by
  simp [jetEqOnSet, hu]

/-- Finite intersection over `j : Fin k` of the common zero locus inside `U` of a `(d + 1)`-jet of
complex-valued functions. -/
private def jetZeroOnSet {κ : Type*} {d : ℕ} (U : Set (κ → ℝ))
    (L : Fin (d + 1) → (κ → ℝ) → ℂ) (k : Fin (d + 1)) : Set (κ → ℝ) :=
  jetEqOnSet U L (fun _ _ ↦ 0) k

private theorem isSemialgebraic_jetZeroOnSet {κ : Type*} {d : ℕ} {U : Set (κ → ℝ)}
    {L : Fin (d + 1) → (κ → ℝ) → ℂ} (hU : IsSemialgebraic U)
    (hL : ∀ j, IsSemialgebraicOn (fun u ↦ complexToRealPi Unit (fun _ ↦ L j u)) U)
    (k : Fin (d + 1)) :
    IsSemialgebraic (jetZeroOnSet U L k) := by
  refine isSemialgebraic_jetEqOnSet hL (fun _ ↦ ?_) k
  convert isSemialgebraicOn_const (0 : Unit ⊕ Unit → ℝ) hU using 1
  ext _ (_ | _) <;> simp

private theorem forall_eq_zero_iff_mem_jetZeroOnSet {κ : Type*} {d : ℕ} {U : Set (κ → ℝ)}
    {L : Fin (d + 1) → (κ → ℝ) → ℂ} {k : Fin (d + 1)} {u : κ → ℝ} (hu : u ∈ U) :
    (∀ j : Fin (k : ℕ), L ⟨j, j.2.trans k.2⟩ u = 0) ↔ u ∈ jetZeroOnSet U L k := by
  simp [jetZeroOnSet, jetEqOnSet, hu]

end SemialgebraicComplexPoly

/-! ### Complex Weierstrass upgrading (`w₀ = 0` and general `w₀`) -/

section ComplexWeierstrassUpgrade

/-- A monic Weierstrass polynomial whose lower coefficients vanish at `z₀` does not vanish as a
germ at `Sum.elim z₀ 0`. -/
private theorem not_eventuallyEq_zero_eval_monicOfCoeff {σ : Type*} {d : ℕ}
    {c : Fin d → (σ → ℂ) → ℂ} {z₀ : σ → ℂ} (hc0 : ∀ i, c i z₀ = 0) :
    ¬ (fun p : σ ⊕ Unit → ℂ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ())))
      =ᶠ[𝓝 (Sum.elim z₀ 0)] (0 : (σ ⊕ Unit → ℂ) → ℂ) := by
  intro h0
  have hT : Tendsto (fun w : ℂ ↦ Sum.elim z₀ (fun _ : Unit ↦ w)) (𝓝 0) (𝓝 (Sum.elim z₀ 0)) :=
    (continuous_sumElim_const z₀).tendsto 0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ((hT.eventually h0).mono fun _ hw ↦ hw)
  have hmem : ((ε / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  have heval : (Polynomial.monicOfCoeff (fun i ↦ c i z₀)).eval ((ε / 2 : ℝ) : ℂ) = 0 := hball hmem
  rw [Polynomial.eval_monicOfCoeff] at heval
  simp only [hc0, zero_mul, Finset.sum_const_zero, add_zero] at heval
  exact pow_ne_zero d (Complex.ofReal_ne_zero.2 (by positivity)) heval

/-- Constructing a common isolating cylinder `(B_X, R)` around `(z₀, 0)` on which a finite family
of holomorphic-Nash functions `H : ι → (σ ⊕ Unit → ℂ) → ℂ` have semialgebraic realifications and
the Weierstrass polynomial coefficients satisfy Fujiwara's bound `‖c i x‖ ≤ (R / 4) ^ (d - i)`. -/
private theorem exists_isolating_cylinder {σ ι : Type*} [Fintype σ] [Finite ι] {d : ℕ}
    {z₀ : σ → ℂ} {c : Fin d → (σ → ℂ) → ℂ}
    (hc : ∀ i, AnalyticAt ℂ (c i) z₀) (hc0 : ∀ i, c i z₀ = 0)
    {H : ι → (σ ⊕ Unit → ℂ) → ℂ} (hH : ∀ k, IsHolomorphicNashAt (H k) (Sum.elim z₀ 0))
    {P : (σ ⊕ Unit → ℂ) → Prop} (hP : ∀ᶠ p in 𝓝 (Sum.elim z₀ 0), P p) :
    ∃ (R : ℝ) (B_X : Set (σ ⊕ σ → ℝ)),
      0 < R ∧ IsOpen B_X ∧ complexToRealPi σ z₀ ∈ B_X ∧ IsSemialgebraic B_X ∧
      (∀ x_ℝ ∈ B_X, ∀ i : Fin d,
        ‖c i ((complexToRealPi σ).symm x_ℝ)‖ ≤ (R / 4) ^ (d - (i : ℕ))) ∧
      (∀ x_ℝ ∈ B_X, ∀ w ∈ ball (0 : ℂ) R,
        P (Sum.elim ((complexToRealPi σ).symm x_ℝ) (fun _ ↦ w))) ∧
      ∃ W : Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ),
        (∀ k, IsSemialgebraicOn
          (fun q ↦ complexToRealPi Unit
            (fun _ ↦ H k ((complexToRealPi (σ ⊕ Unit)).symm q))) W) ∧
        (∀ u : ElimCoord σ d,
          (u ∘ Sum.inl) ∘ Sum.inl ∈ B_X → u ∘ Sum.inr ∈ realDiskSet R → u ∘ projXW σ d ∈ W) := by
  let eσ := complexToRealPi σ
  let e := complexToRealPi (σ ⊕ Unit)
  obtain ⟨W, hWo, hzW, -, hHW⟩ := exists_isSemialgebraicOn_of_forall_isHolomorphicNashAt hH
  obtain ⟨R, hR, hR_ball⟩ := Metric.mem_nhds_iff.1
    (inter_mem (e.continuousAt.preimage_mem_nhds (hWo.mem_nhds hzW)) hP)
  have hc_bound : ∀ᶠ x in 𝓝 z₀, ∀ i : Fin d, ‖c i x‖ ≤ (R / 4) ^ (d - (i : ℕ)) := by
    refine eventually_all.2 fun i ↦ ?_
    have hrad : 0 < (R / 4) ^ (d - (i : ℕ)) := by positivity
    have hlt := (hc i).continuousAt.tendsto (ball_mem_nhds (c i z₀) hrad)
    exact eventually_of_mem hlt fun x hx ↦ by simpa [hc0 i] using (mem_ball.1 hx).le
  have heσ : Tendsto eσ.symm (𝓝 (eσ z₀)) (𝓝 z₀) := by
    simpa only [eσ.symm_apply_apply] using eσ.symm.continuous.tendsto (eσ z₀)
  obtain ⟨δ, hδ, hδ_ball⟩ := Metric.mem_nhds_iff.1
    (heσ.eventually (inter_mem (ball_mem_nhds z₀ hR) hc_bound))
  refine ⟨R, ball (eσ z₀) δ, hR, isOpen_ball, mem_ball_self hδ,
    isSemialgebraic_ball (eσ z₀) δ, fun x_ℝ hx ↦ (hδ_ball hx).2, ?_, W, hHW, ?_⟩
  · intro x_ℝ hx w hw
    refine (hR_ball ?_).2
    rw [mem_ball, dist_pi_lt_iff hR]
    rintro (s | ⟨⟩)
    · exact (dist_pi_lt_iff hR).1 (mem_ball.1 (hδ_ball hx).1) s
    · exact mem_ball.1 hw
  · intro u hx hw
    have hp_mem : Sum.elim (eσ.symm ((u ∘ Sum.inl) ∘ Sum.inl))
        (fun _ : Unit ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ()) ∈
          ball (Sum.elim z₀ 0) R := by
      rw [mem_ball, dist_pi_lt_iff hR]
      rintro (s | ⟨⟩)
      · exact (dist_pi_lt_iff hR).1 (mem_ball.1 (hδ_ball hx).1) s
      · exact mem_ball.1 ((mem_realDiskSet_iff hR _).1 hw)
    have he_eq : e (Sum.elim (eσ.symm ((u ∘ Sum.inl) ∘ Sum.inl))
        (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) = u ∘ projXW σ d := by
      rw [← symm_comp_projXW, e.apply_symm_apply]
    exact he_eq ▸ (hR_ball hp_mem).1

/-- Evaluating the `j`-th Hasse derivative of `monicOfCoeff` at holomorphic-Nash coefficient germs
gives a holomorphic-Nash germ on `σ ⊕ Unit → ℂ`. -/
private theorem isHolomorphicNashAt_eval_hasseDeriv_monicOfCoeff {σ : Type*} [Fintype σ] {d : ℕ}
    {c : Fin d → (σ → ℂ) → ℂ} {z₀ : σ → ℂ} (hc : ∀ i, IsHolomorphicNashAt (c i) z₀) (j : ℕ) :
    IsHolomorphicNashAt
      (fun p : σ ⊕ Unit → ℂ ↦
        (hasseDeriv j (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl)))).eval (p (.inr ())))
      (Sum.elim z₀ 0) := by
  let Φ : (σ ⊕ Unit → ℂ) → (Fin d ⊕ Unit → ℂ) :=
    fun p ↦ Sum.elim (fun i ↦ c i (p ∘ Sum.inl)) (fun _ ↦ p (.inr ()))
  have hΦ : ∀ k, IsHolomorphicNashAt (fun p ↦ Φ p k) (Sum.elim z₀ 0) := by
    rintro (i | ⟨⟩)
    · exact (hc i).comp fun s ↦ isHolomorphicNashAt_apply (Sum.inl s)
    · exact isHolomorphicNashAt_apply (Sum.inr ())
  refine ((hasseDerivMonicMvPoly d j).isHolomorphicNashAt_eval.comp hΦ).congr
    (.of_forall fun p ↦ ?_)
  exact eval_hasseDerivMonicMvPoly j (fun i ↦ c i (p ∘ Sum.inl)) (p (.inr ()))

/-- Evaluating `monicOfCoeff` at holomorphic-Nash coefficient germs gives a holomorphic-Nash germ
on `σ ⊕ Unit → ℂ`. -/
private theorem isHolomorphicNashAt_eval_monicOfCoeff {σ : Type*} [Fintype σ] {d : ℕ}
    {c : Fin d → (σ → ℂ) → ℂ} {z₀ : σ → ℂ} (hc : ∀ i, IsHolomorphicNashAt (c i) z₀) :
    IsHolomorphicNashAt
      (fun p : σ ⊕ Unit → ℂ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ())))
      (Sum.elim z₀ 0) := by
  simpa only [hasseDeriv_zero, LinearMap.id_apply] using
    isHolomorphicNashAt_eval_hasseDeriv_monicOfCoeff hc 0

/-- Evaluating a polynomial remainder `∑ i : Fin d, r i (p ∘ Sum.inl) * p (.inr ()) ^ i` at
holomorphic-Nash coefficient germs gives a holomorphic-Nash germ on `σ ⊕ Unit → ℂ`. -/
private theorem isHolomorphicNashAt_sum_mul_pow {σ : Type*} [Fintype σ] {d : ℕ}
    {r : Fin d → (σ → ℂ) → ℂ} {z₀ : σ → ℂ} (hr : ∀ i, IsHolomorphicNashAt (r i) z₀) :
    IsHolomorphicNashAt
      (fun p : σ ⊕ Unit → ℂ ↦ ∑ i : Fin d, r i (p ∘ Sum.inl) * p (.inr ()) ^ (i : ℕ))
      (Sum.elim z₀ 0) :=
  Finset.fun_isHolomorphicNashAt_sum Finset.univ fun i _ ↦
    ((hr i).comp fun s ↦ isHolomorphicNashAt_apply (Sum.inl s)).fun_mul
      ((isHolomorphicNashAt_apply (Sum.inr ())).fun_pow (i : ℕ))

/-- Along a vertical slice where `F (x, w) = P.eval w * u (x, w)` and `u (x, w₀) ≠ 0`, the Hasse
derivatives of `P = monicOfCoeff c` below `k` vanish at `w₀` iff the iterated derivatives of `F`
below `k` vanish at `w₀`. -/
private theorem hasseDeriv_iff_iteratedDeriv_of_weierstrassPreparation {σ : Type*} [Fintype σ]
    {F u : (σ ⊕ Unit → ℂ) → ℂ} {x : σ → ℂ} {d : ℕ} {c : Fin d → ℂ} {w₀ : ℂ} {R : ℝ}
    (hw₀ : w₀ ∈ ball (0 : ℂ) R)
    (hF_an : AnalyticAt ℂ F (Sum.elim x (fun _ ↦ w₀)))
    (hu_an : AnalyticAt ℂ u (Sum.elim x (fun _ ↦ w₀)))
    (hu0 : u (Sum.elim x (fun _ ↦ w₀)) ≠ 0)
    (hfac : ∀ w ∈ ball (0 : ℂ) R,
      F (Sum.elim x (fun _ ↦ w)) = (Polynomial.monicOfCoeff c).eval w * u (Sum.elim x (fun _ ↦ w)))
    (k : Fin (d + 1)) :
    (∀ j : Fin (k : ℕ), (hasseDeriv (j : ℕ) (Polynomial.monicOfCoeff c)).eval w₀ = 0) ↔
      (∀ j : Fin (k : ℕ),
        iteratedDeriv (j : ℕ) (fun w ↦ F (Sum.elim x (fun _ ↦ w))) w₀ = 0) := by
  let P := Polynomial.monicOfCoeff c
  have hf_w : AnalyticAt ℂ (fun w ↦ F (Sum.elim x (fun _ ↦ w))) w₀ :=
    hF_an.comp_of_eq (analyticAt_sumElim_const x w₀) rfl
  have hu_w : AnalyticAt ℂ (fun w ↦ u (Sum.elim x (fun _ ↦ w))) w₀ :=
    hu_an.comp_of_eq (analyticAt_sumElim_const x w₀) rfl
  have hP_w : AnalyticAt ℂ (fun w ↦ P.eval w) w₀ :=
    (AnalyticOnNhd.eval_polynomial P) w₀ (Set.mem_univ w₀)
  have hfac_w : (fun w ↦ F (Sum.elim x (fun _ ↦ w))) =ᶠ[𝓝 w₀]
      (fun w ↦ P.eval w) * (fun w ↦ u (Sum.elim x (fun _ ↦ w))) :=
    eventually_of_mem (isOpen_ball.mem_nhds hw₀) hfac
  have hord : analyticOrderAt (fun w ↦ F (Sum.elim x (fun _ ↦ w))) w₀ =
      (P.rootMultiplicity w₀ : ℕ∞) := by
    rw [analyticOrderAt_congr hfac_w, analyticOrderAt_mul hP_w hu_w,
      hu_w.analyticOrderAt_eq_zero.2 hu0, add_zero,
      Polynomial.analyticOrderAt_eval (Polynomial.monic_monicOfCoeff _).ne_zero w₀]
  have hiff := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf_w (n := (k : ℕ))).symm
  rw [hord, Nat.cast_le,
    Polynomial.le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero
      (Polynomial.monic_monicOfCoeff _).ne_zero] at hiff
  exact ⟨fun h j ↦ (hiff.2 fun m hm ↦ h ⟨m, hm⟩) j j.2,
    fun h j ↦ (hiff.1 fun m hm ↦ h ⟨m, hm⟩) j j.2⟩

private theorem imp_iff_mem_compl_union {α : Type*} {A B : Set α} (u : α) :
    (u ∈ A → u ∈ B) ↔ u ∈ Aᶜ ∪ B := by
  classical
  exact ⟨fun h ↦ if ha : u ∈ A then .inr (h ha) else .inl ha,
    fun h ha ↦ h.resolve_left (Classical.not_not.2 ha)⟩

private theorem imp_forall_iff_mem_compl_union {α : Type*} {n : ℕ} {U : Set α}
    {P : Fin n → Prop} {S : Fin n → Set α} {u : α} (hS : u ∈ U → ∀ k, P k ↔ u ∈ S k) :
    (u ∈ U → ∀ k, P k) ↔ u ∈ Uᶜ ∪ ⋂ k, S k := by
  classical
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iInter]
  exact ⟨fun h ↦ if hu : u ∈ U then .inr fun k ↦ (hS hu k).1 (h hu k) else .inl hu,
    fun h hu k ↦ (hS hu k).2 ((h.resolve_left (Classical.not_not.2 hu)) k)⟩

/-- Semialgebraicity on `B_X` of a realified coefficient map via universal quantifier elimination
over the fiber coordinate `w_ℝ : Unit ⊕ Unit → ℝ`. -/
private theorem isSemialgebraicOn_complexToRealPi_of_forall_elimCoord {σ : Type*} [Fintype σ]
    {d : ℕ} {B_X : Set (σ ⊕ σ → ℝ)} {g : Fin d → (σ → ℂ) → ℂ}
    {S : Set (ElimCoord σ d)}
    (hBX : IsSemialgebraic B_X) (hS : IsSemialgebraic S)
    (hchar : ∀ v : (σ ⊕ σ) ⊕ (Fin d ⊕ Fin d) → ℝ, v ∘ Sum.inl ∈ B_X →
      ((fun i ↦ g i ((complexToRealPi σ).symm (v ∘ Sum.inl))) =
        (complexToRealPi (Fin d)).symm (v ∘ Sum.inr) ↔
          ∀ w_ℝ, Sum.elim v w_ℝ ∈ S)) :
    IsSemialgebraicOn
      (fun x_ℝ ↦ complexToRealPi (Fin d) (fun i ↦ g i ((complexToRealPi σ).symm x_ℝ))) B_X := by
  rw [isSemialgebraicOn_iff_graph]
  convert (hBX.preimage_comp Sum.inl).inter hS.setOf_forall_sumElim using 1
  ext v
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred]
  refine and_congr_right fun hvBX ↦ ?_
  rw [← ContinuousLinearEquiv.eq_symm_apply]
  exact hchar v hvBX

/-- Semialgebraicity of the fiberwise root-and-multiplicity relation cutting out the Weierstrass
polynomial coefficients before universal elimination of `w_ℝ`. -/
private theorem isSemialgebraic_prepElimSet {σ : Type*} [Fintype σ] {d : ℕ}
    {B_X : Set (σ ⊕ σ → ℝ)} {R : ℝ} {W : Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ)}
    {DF : Fin (d + 1) → (σ ⊕ Unit → ℂ) → ℂ}
    (hBX : IsSemialgebraic B_X)
    (hDF_W : ∀ j, IsSemialgebraicOn
      (fun q ↦ complexToRealPi Unit (fun _ ↦ DF j ((complexToRealPi (σ ⊕ Unit)).symm q))) W)
    (hsub : ∀ u : ElimCoord σ d,
      (u ∘ Sum.inl) ∘ Sum.inl ∈ B_X → u ∘ Sum.inr ∈ realDiskSet R → u ∘ projXW σ d ∈ W) :
    IsSemialgebraic
      {u : ElimCoord σ d |
        ((Polynomial.monicOfCoeff
            ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr))).eval
              ((complexToRealPi Unit).symm (u ∘ Sum.inr) ()) = 0 →
            u ∘ Sum.inr ∈ realDiskSet R) ∧
          ((u ∘ Sum.inl) ∘ Sum.inl ∈ B_X ∧ u ∘ Sum.inr ∈ realDiskSet R →
            ∀ k : Fin (d + 1),
              (∀ j : Fin (k : ℕ),
                (hasseDeriv (j : ℕ) (Polynomial.monicOfCoeff
                  ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr)))).eval
                    ((complexToRealPi Unit).symm (u ∘ Sum.inr) ()) = 0) ↔
              (∀ j : Fin (k : ℕ),
                DF ⟨j, j.2.trans k.2⟩
                  (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
                    (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) = 0))} := by
  let U_cyl := elimCylSet σ d B_X R
  have hU_cyl : IsSemialgebraic U_cyl := isSemialgebraic_elimCylSet hBX R
  -- First conjunct: every root of the candidate monic polynomial lies in `realDiskSet R`.
  let Z_P0 : Set (ElimCoord σ d) :=
    {u | (Polynomial.monicOfCoeff
      ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr))).eval
        ((complexToRealPi Unit).symm (u ∘ Sum.inr) ()) = 0}
  have hZ_P0 : IsSemialgebraic Z_P0 := by
    convert (isSemialgebraicOn_eval_comp_projAW (σ := σ) (hasseDerivMonicMvPoly d 0)
      isSemialgebraic_univ).isSemialgebraic_inter_setOf_eq
        (isSemialgebraicOn_const 0 isSemialgebraic_univ) using 1
    ext u
    simp [Z_P0, eval_hasseDerivMonicMvPoly, funext_iff, Complex.ext_iff]
  have hC1 : IsSemialgebraic (Z_P0ᶜ ∪ ((fun u : ElimCoord σ d ↦ u ∘ Sum.inr) ⁻¹' realDiskSet R)) :=
    hZ_P0.compl.union ((isSemialgebraic_realDiskSet R).preimage_comp Sum.inr)
  -- Second conjunct: on `U_cyl`, the Hasse jet of `monicOfCoeff` and the vertical derivative jet
  -- `DF` vanish below each order `k ≤ d` simultaneously.
  let P_jet (j : Fin (d + 1)) (u : ElimCoord σ d) : ℂ :=
    (hasseDeriv (j : ℕ) (Polynomial.monicOfCoeff
      ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr)))).eval
        ((complexToRealPi Unit).symm (u ∘ Sum.inr) ())
  let F_jet (j : Fin (d + 1)) (u : ElimCoord σ d) : ℂ :=
    DF j (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
      (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ()))
  have hP_jet (j : Fin (d + 1)) :
      IsSemialgebraicOn (fun u ↦ complexToRealPi Unit (fun _ ↦ P_jet j u)) U_cyl := by
    convert isSemialgebraicOn_eval_comp_projAW (σ := σ) (hasseDerivMonicMvPoly d (j : ℕ)) hU_cyl
      using 1
    funext u
    simp only [P_jet, eval_hasseDerivMonicMvPoly]
  have hF_jet (j : Fin (d + 1)) :
      IsSemialgebraicOn (fun u ↦ complexToRealPi Unit (fun _ ↦ F_jet j u)) U_cyl :=
    isSemialgebraicOn_comp_projXW hBX (hDF_W j) hsub
  have hAP (k : Fin (d + 1)) : IsSemialgebraic (jetZeroOnSet U_cyl P_jet k) :=
    isSemialgebraic_jetZeroOnSet hU_cyl hP_jet k
  have hAF (k : Fin (d + 1)) : IsSemialgebraic (jetZeroOnSet U_cyl F_jet k) :=
    isSemialgebraic_jetZeroOnSet hU_cyl hF_jet k
  have hC2 : IsSemialgebraic (U_cylᶜ ∪ ⋂ k : Fin (d + 1),
      ((jetZeroOnSet U_cyl P_jet k)ᶜ ∪ jetZeroOnSet U_cyl F_jet k) ∩
        ((jetZeroOnSet U_cyl F_jet k)ᶜ ∪ jetZeroOnSet U_cyl P_jet k)) :=
    hU_cyl.compl.union (.iInter fun k ↦
      ((hAP k).compl.union (hAF k)).inter ((hAF k).compl.union (hAP k)))
  convert hC1.inter hC2 using 1
  ext u
  rw [Set.mem_ofPred, Set.mem_inter_iff, mem_elimCylSet_iff]
  refine and_congr ?_ (imp_forall_iff_mem_compl_union fun hu k ↦ ?_)
  · simpa only [Z_P0, Set.mem_ofPred, Set.mem_preimage] using
      imp_iff_mem_compl_union (A := Z_P0) (B := (fun u ↦ u ∘ Sum.inr) ⁻¹' realDiskSet R) u
  · rw [forall_eq_zero_iff_mem_jetZeroOnSet (L := P_jet) hu,
      forall_eq_zero_iff_mem_jetZeroOnSet (L := F_jet) hu,
      Set.mem_inter_iff, ← imp_iff_mem_compl_union, ← imp_iff_mem_compl_union]
    exact iff_def

/-- Upgrading a complex Weierstrass preparation at `(z₀, 0)` to `IsHolomorphicNashAt`. -/
private theorem isHolomorphicNashAt_of_weierstrassPreparation_zero {σ : Type*} [Fintype σ]
    {F u : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ → ℂ} {d : ℕ} {c : Fin d → (σ → ℂ) → ℂ}
    (hF : IsHolomorphicNashAt F (Sum.elim z₀ 0))
    (hc : ∀ i, AnalyticAt ℂ (c i) z₀) (hc0 : ∀ i, c i z₀ = 0)
    (hu : AnalyticAt ℂ u (Sum.elim z₀ 0)) (hu0 : u (Sum.elim z₀ 0) ≠ 0)
    (hfac : F =ᶠ[𝓝 (Sum.elim z₀ 0)] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ())) * u p) :
    (∀ i, IsHolomorphicNashAt (c i) z₀) ∧ IsHolomorphicNashAt u (Sum.elim z₀ 0) := by
  let DF : Fin (d + 1) → (σ ⊕ Unit → ℂ) → ℂ := fun j p ↦
    iteratedDeriv (j : ℕ) (fun w ↦ F (Sum.elim (p ∘ Sum.inl) (fun _ ↦ w))) (p (.inr ()))
  -- Step 1: Shrink to a common isolating cylinder where the vertical derivatives `DF` are
  -- semialgebraic, `u` is nonvanishing, and Fujiwara's coefficient bound holds.
  obtain ⟨R, B_X, hR, hBX_open, hzBX, hBX_semi, hc_bound, hprop, W, hDF_W, hsub⟩ :=
    exists_isolating_cylinder (H := DF) hc hc0 (fun j ↦ hF.iteratedDeriv_vertical (j : ℕ))
      (((hF.analyticAt.eventually_analyticAt.and hu.eventually_analyticAt).and
        (hu.continuousAt.eventually_ne hu0)).and hfac)
  have h2R4 : 2 * (R / 4) < R := by linarith
  have horder (x_ℝ : σ ⊕ σ → ℝ) (hx : x_ℝ ∈ B_X) (w : ℂ) (hw : w ∈ ball (0 : ℂ) R)
      (k : Fin (d + 1)) :=
    hasseDeriv_iff_iteratedDeriv_of_weierstrassPreparation hw
      (hprop x_ℝ hx w hw).1.1.1 (hprop x_ℝ hx w hw).1.1.2 (hprop x_ℝ hx w hw).1.2
      (fun w' hw' ↦ by simpa only [Sum.elim_comp_inl, Sum.elim_inr] using (hprop x_ℝ hx w' hw').2) k
  -- Step 2: Show the realified coefficient map is semialgebraic on `B_X` by eliminating `w_ℝ`.
  have hc_semi : IsSemialgebraicOn
      (fun x_ℝ ↦ complexToRealPi (Fin d) (fun i ↦ c i ((complexToRealPi σ).symm x_ℝ))) B_X := by
    refine isSemialgebraicOn_complexToRealPi_of_forall_elimCoord hBX_semi
      (isSemialgebraic_prepElimSet hBX_semi hDF_W hsub) fun v hvBX ↦ ?_
    simp only [Set.mem_ofPred, Sum.elim_comp_inl, Sum.elim_comp_inr]
    refine ⟨fun hvc w_ℝ ↦ ?_, fun hall ↦ symm <|
      Polynomial.eq_of_monicOfCoeff_forall_hasseDeriv_iff
        (IsAlgClosed.splits _) (IsAlgClosed.splits _)
        (fun w hw ↦ ?_)
        (fun w hw ↦ Polynomial.mem_ball_of_isRoot_monicOfCoeff h2R4 (hc_bound _ hvBX) hw)
        (fun w hw k hk ↦ ?_)⟩
    · -- Forward direction: the true coefficients isolate all roots in `ball 0 R` by Fujiwara's
      -- bound and match the vanishing orders of `F` on `ball 0 R`.
      rw [hvc.symm]
      exact ⟨fun hw ↦ (mem_realDiskSet_iff hR w_ℝ).2
        (Polynomial.mem_ball_of_isRoot_monicOfCoeff h2R4 (hc_bound _ hvBX) hw),
        fun ⟨_, hwD⟩ k ↦ horder _ hvBX _ ((mem_realDiskSet_iff hR w_ℝ).1 hwD) k⟩
    · -- Converse root containment: instantiate `w_ℝ = complexToRealPi Unit (fun _ ↦ w)`.
      exact (mem_ball_iff_complexToRealPi_mem_realDiskSet hR w).2
        ((hall (complexToRealPi Unit (fun _ ↦ w))).1 (by simpa using hw))
    · -- Converse jet matching: compare both Hasse vanishing conditions through `DF` at `w`.
      have hwD := (mem_ball_iff_complexToRealPi_mem_realDiskSet hR w).1 hw
      have h2 := (hall (complexToRealPi Unit (fun _ ↦ w))).2 ⟨hvBX, hwD⟩ ⟨k, Nat.lt_succ_of_le hk⟩
      simp only [complexToRealPi_unit_symm_const] at h2
      simpa only [Fin.forall_iff] using h2.trans (horder _ hvBX w hw ⟨k, Nat.lt_succ_of_le hk⟩).symm
  -- Step 3: Upgrade the coefficients via the graph criterion, then upgrade `u` by exact division.
  have hc_nash : ∀ i, IsHolomorphicNashAt (c i) z₀ :=
    forall_isHolomorphicNashAt_apply_iff_exists_isSemialgebraicOn.mpr
      ⟨AnalyticAt.pi hc, B_X, hBX_open, hzBX, hc_semi⟩
  exact ⟨hc_nash, (isHolomorphicNashAt_eval_monicOfCoeff hc_nash).of_mul_eventuallyEq
    hF hu (not_eventuallyEq_zero_eval_monicOfCoeff hc0) hfac.symm⟩

/-- Along a vertical slice where `G = P * q + Rem`, vanishing of Hasse derivatives of `P` below `k`
forces the iterated derivatives of `G` below `k` to match `j !` times the Hasse derivatives of
`Rem`. -/
private theorem jet_eq_of_weierstrassDivision {σ : Type*} [Fintype σ]
    {G q : (σ ⊕ Unit → ℂ) → ℂ} {x : σ → ℂ} {d : ℕ} {c r : Fin d → ℂ} {w₀ : ℂ} {R : ℝ}
    (hw₀ : w₀ ∈ ball (0 : ℂ) R)
    (hG_an : AnalyticAt ℂ G (Sum.elim x (fun _ ↦ w₀)))
    (hq_an : AnalyticAt ℂ q (Sum.elim x (fun _ ↦ w₀)))
    (hdiv : ∀ w ∈ ball (0 : ℂ) R,
      G (Sum.elim x (fun _ ↦ w)) =
        (Polynomial.monicOfCoeff c).eval w * q (Sum.elim x (fun _ ↦ w)) +
          ∑ i : Fin d, r i * w ^ (i : ℕ))
    (k : Fin (d + 1))
    (hP0 : ∀ j : Fin (k : ℕ), (hasseDeriv (j : ℕ) (Polynomial.monicOfCoeff c)).eval w₀ = 0) :
    ∀ j : Fin (k : ℕ),
      iteratedDeriv (j : ℕ) (fun w ↦ G (Sum.elim x (fun _ ↦ w))) w₀ =
        (Nat.factorial (j : ℕ) : ℂ) *
          (hasseDeriv (j : ℕ) (∑ i : Fin d, monomial (i : ℕ) (r i))).eval w₀ := by
  let P := Polynomial.monicOfCoeff c
  let Rem : ℂ[X] := ∑ i : Fin d, monomial (i : ℕ) (r i)
  have hg_w : AnalyticAt ℂ (fun w ↦ G (Sum.elim x (fun _ ↦ w))) w₀ :=
    hG_an.comp_of_eq (analyticAt_sumElim_const x w₀) rfl
  have hq_w : AnalyticAt ℂ (fun w ↦ q (Sum.elim x (fun _ ↦ w))) w₀ :=
    hq_an.comp_of_eq (analyticAt_sumElim_const x w₀) rfl
  have hP_w : AnalyticAt ℂ (fun w ↦ P.eval w) w₀ :=
    (AnalyticOnNhd.eval_polynomial P) w₀ (Set.mem_univ w₀)
  have hR_w : AnalyticAt ℂ (fun w ↦ Rem.eval w) w₀ :=
    (AnalyticOnNhd.eval_polynomial Rem) w₀ (Set.mem_univ w₀)
  have hsub_eq : (fun w ↦ G (Sum.elim x (fun _ ↦ w)) - Rem.eval w) =ᶠ[𝓝 w₀]
      (fun w ↦ P.eval w) * (fun w ↦ q (Sum.elim x (fun _ ↦ w))) := by
    filter_upwards [isOpen_ball.mem_nhds hw₀] with w hw
    simp only [Rem, eval_finsetSum, eval_monomial]
    exact sub_eq_of_eq_add (hdiv w hw)
  have hk_le : (k : ℕ∞) ≤
      analyticOrderAt (fun w ↦ G (Sum.elim x (fun _ ↦ w)) - Rem.eval w) w₀ := by
    rw [analyticOrderAt_congr hsub_eq, analyticOrderAt_mul hP_w hq_w,
      Polynomial.analyticOrderAt_eval (Polynomial.monic_monicOfCoeff _).ne_zero w₀]
    refine le_trans ?_ le_self_add
    rw [Nat.cast_le, Polynomial.le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero
      (Polynomial.monic_monicOfCoeff _).ne_zero]
    exact fun m hm ↦ hP0 ⟨m, hm⟩
  have hzero :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hg_w.fun_sub hR_w)).1 hk_le
  intro j
  have hj := hzero (j : ℕ) j.2
  rw [iteratedDeriv_fun_sub hg_w.contDiffAt hR_w.contDiffAt, sub_eq_zero,
    Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv] at hj
  exact hj

/-- Semialgebraicity of the fiberwise Taylor-jet matching relation cutting out the Weierstrass
remainder coefficients before universal elimination of `w_ℝ`. -/
private theorem isSemialgebraic_divElimSet {σ : Type*} [Fintype σ] {d : ℕ}
    {B_X : Set (σ ⊕ σ → ℝ)} {R : ℝ} {W : Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ)}
    {DG HP : Fin (d + 1) → (σ ⊕ Unit → ℂ) → ℂ}
    (hBX : IsSemialgebraic B_X)
    (hHW : ∀ s : Fin (d + 1) ⊕ Fin (d + 1), IsSemialgebraicOn
      (fun q ↦ complexToRealPi Unit
        (fun _ ↦ Sum.elim DG HP s ((complexToRealPi (σ ⊕ Unit)).symm q))) W)
    (hsub : ∀ u : ElimCoord σ d,
      (u ∘ Sum.inl) ∘ Sum.inl ∈ B_X → u ∘ Sum.inr ∈ realDiskSet R → u ∘ projXW σ d ∈ W) :
    IsSemialgebraic
      {u : ElimCoord σ d |
        (u ∘ Sum.inl) ∘ Sum.inl ∈ B_X ∧ u ∘ Sum.inr ∈ realDiskSet R →
          ∀ k : Fin (d + 1),
            (∀ j : Fin (k : ℕ),
              HP ⟨j, j.2.trans k.2⟩
                (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
                  (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) = 0) →
            ∀ j : Fin (k : ℕ),
              DG ⟨j, j.2.trans k.2⟩
                (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
                  (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) =
                (Nat.factorial (j : ℕ) : ℂ) *
                  (hasseDeriv (j : ℕ) (∑ i : Fin d, monomial (i : ℕ)
                    ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr) i))).eval
                      ((complexToRealPi Unit).symm (u ∘ Sum.inr) ())} := by
  let U_cyl := elimCylSet σ d B_X R
  have hU_cyl : IsSemialgebraic U_cyl := isSemialgebraic_elimCylSet hBX R
  -- On `U_cyl`, express the vanishing of `HP` below `k` as `jetZeroOnSet` and the matching of
  -- `DG` with `j! * hasseDeriv j Rem` below `k` as `jetEqOnSet`.
  let HP_jet (j : Fin (d + 1)) (u : ElimCoord σ d) : ℂ :=
    HP j (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
      (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ()))
  let DG_jet (j : Fin (d + 1)) (u : ElimCoord σ d) : ℂ :=
    DG j (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
      (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ()))
  let Rem_jet (j : Fin (d + 1)) (u : ElimCoord σ d) : ℂ :=
    (Nat.factorial (j : ℕ) : ℂ) *
      (hasseDeriv (j : ℕ) (∑ i : Fin d, monomial (i : ℕ)
        ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr) i))).eval
          ((complexToRealPi Unit).symm (u ∘ Sum.inr) ())
  have hHP_jet (j : Fin (d + 1)) :
      IsSemialgebraicOn (fun u ↦ complexToRealPi Unit (fun _ ↦ HP_jet j u)) U_cyl :=
    isSemialgebraicOn_comp_projXW hBX (hHW (Sum.inr j)) hsub
  have hDG_jet (j : Fin (d + 1)) :
      IsSemialgebraicOn (fun u ↦ complexToRealPi Unit (fun _ ↦ DG_jet j u)) U_cyl :=
    isSemialgebraicOn_comp_projXW hBX (hHW (Sum.inl j)) hsub
  have hRem_jet (j : Fin (d + 1)) :
      IsSemialgebraicOn (fun u ↦ complexToRealPi Unit (fun _ ↦ Rem_jet j u)) U_cyl := by
    convert isSemialgebraicOn_eval_comp_projAW (σ := σ)
      (factorialHasseDerivSumMvPoly d (j : ℕ)) hU_cyl using 1
    funext u
    simp only [Rem_jet, eval_factorialHasseDerivSumMvPoly]
  have hAHP (k : Fin (d + 1)) : IsSemialgebraic (jetZeroOnSet U_cyl HP_jet k) :=
    isSemialgebraic_jetZeroOnSet hU_cyl hHP_jet k
  have hBDG (k : Fin (d + 1)) : IsSemialgebraic (jetEqOnSet U_cyl DG_jet Rem_jet k) :=
    isSemialgebraic_jetEqOnSet hDG_jet hRem_jet k
  convert hU_cyl.compl.union (.iInter fun k ↦ (hAHP k).compl.union (hBDG k)) using 1
  ext u
  rw [Set.mem_ofPred, mem_elimCylSet_iff]
  refine imp_forall_iff_mem_compl_union fun hu k ↦ ?_
  rw [forall_eq_zero_iff_mem_jetZeroOnSet (L := HP_jet) hu,
    forall_eq_iff_mem_jetEqOnSet (L := DG_jet) (M := Rem_jet) hu,
    imp_iff_mem_compl_union]

/-- Upgrading a complex Weierstrass division at `(z₀, 0)` to `IsHolomorphicNashAt`. -/
private theorem isHolomorphicNashAt_of_weierstrassDivision_zero {σ : Type*} [Fintype σ]
    {G q : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ → ℂ} {d : ℕ} {c r : Fin d → (σ → ℂ) → ℂ}
    (hG : IsHolomorphicNashAt G (Sum.elim z₀ 0))
    (hc : ∀ i, IsHolomorphicNashAt (c i) z₀) (hc0 : ∀ i, c i z₀ = 0)
    (hq : AnalyticAt ℂ q (Sum.elim z₀ 0)) (hr : ∀ i, AnalyticAt ℂ (r i) z₀)
    (hdiv : G =ᶠ[𝓝 (Sum.elim z₀ 0)] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ())) * q p +
        ∑ i : Fin d, r i (p ∘ Sum.inl) * p (.inr ()) ^ (i : ℕ)) :
    IsHolomorphicNashAt q (Sum.elim z₀ 0) ∧ ∀ i, IsHolomorphicNashAt (r i) z₀ := by
  let eσ := complexToRealPi σ
  let DG : Fin (d + 1) → (σ ⊕ Unit → ℂ) → ℂ := fun j p ↦
    iteratedDeriv (j : ℕ) (fun w ↦ G (Sum.elim (p ∘ Sum.inl) (fun _ ↦ w))) (p (.inr ()))
  let HP : Fin (d + 1) → (σ ⊕ Unit → ℂ) → ℂ := fun j p ↦
    (hasseDeriv (j : ℕ) (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl)))).eval (p (.inr ()))
  -- Step 1: Shrink to a common isolating cylinder where `DG` and `HP` are semialgebraic and
  -- Fujiwara's coefficient bound holds for `c`.
  obtain ⟨R, B_X, hR, hBX_open, hzBX, hBX_semi, hc_bound, hprop, W, hHW, hsub⟩ :=
    exists_isolating_cylinder (H := Sum.elim DG HP) (fun i ↦ (hc i).analyticAt) hc0
      (by
        rintro (j | j)
        · exact hG.iteratedDeriv_vertical (j : ℕ)
        · exact isHolomorphicNashAt_eval_hasseDeriv_monicOfCoeff hc (j : ℕ))
      ((hG.analyticAt.eventually_analyticAt.and hq.eventually_analyticAt).and hdiv)
  have h2R4 : 2 * (R / 4) < R := by linarith
  have hjet (x_ℝ : σ ⊕ σ → ℝ) (hx : x_ℝ ∈ B_X) (w : ℂ) (hw : w ∈ ball (0 : ℂ) R)
      (k : Fin (d + 1)) :=
    jet_eq_of_weierstrassDivision hw (hprop x_ℝ hx w hw).1.1 (hprop x_ℝ hx w hw).1.2
      (fun w' hw' ↦ by simpa only [Sum.elim_comp_inl, Sum.elim_inr] using (hprop x_ℝ hx w' hw').2) k
  -- Step 2: Show the realified remainder coefficient map is semialgebraic on `B_X` by eliminating
  -- `w_ℝ`.
  have hr_semi : IsSemialgebraicOn
      (fun x_ℝ ↦ complexToRealPi (Fin d) (fun i ↦ r i (eσ.symm x_ℝ))) B_X := by
    refine isSemialgebraicOn_complexToRealPi_of_forall_elimCoord hBX_semi
      (isSemialgebraic_divElimSet hBX_semi hHW hsub) fun v hvBX ↦ ?_
    simp only [Set.mem_ofPred, Sum.elim_comp_inl, Sum.elim_comp_inr]
    refine ⟨fun hvr w_ℝ ⟨_, hwD⟩ k hP0 j ↦ ?_,
      fun hall ↦ symm <| Polynomial.eq_of_sum_monomial_forall_hasseDeriv_eq
        (IsAlgClosed.splits _)
        (fun w hw ↦ Polynomial.mem_ball_of_isRoot_monicOfCoeff h2R4 (hc_bound _ hvBX) hw)
        (fun w hw k hk hP0 j hj ↦ ?_)⟩
    · -- Forward direction: the true remainder matches the Taylor jet of `G` wherever `P` vanishes
      -- to order `k`.
      have hvr' : ∀ i, (complexToRealPi (Fin d)).symm (v ∘ Sum.inr) i =
          r i (eσ.symm (v ∘ Sum.inl)) := fun i ↦ (congrFun hvr i).symm
      simp only [hvr']
      exact hjet _ hvBX _ ((mem_realDiskSet_iff hR w_ℝ).1 hwD) k hP0 j
    · -- Converse direction: any candidate remainder matching `DG` at every root of `P` inside
      -- `ball 0 R` has the same Hasse derivatives as `r` up to each root multiplicity, hence
      -- equals `r`.
      let k' : Fin (d + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
      let j' : Fin k := ⟨j, hj⟩
      have hP0' : ∀ m : Fin (k' : ℕ),
          (hasseDeriv (m : ℕ) (Polynomial.monicOfCoeff
            (fun i ↦ c i (eσ.symm (v ∘ Sum.inl))))).eval w = 0 := fun m ↦ hP0 m m.2
      have hwD := (mem_ball_iff_complexToRealPi_mem_realDiskSet hR w).1 hw
      have h2 := hall (complexToRealPi Unit (fun _ ↦ w)) ⟨hvBX, hwD⟩ k'
      simp only [complexToRealPi_unit_symm_const] at h2
      have hHP0 : ∀ m : Fin (k' : ℕ),
          HP ⟨m, m.2.trans k'.2⟩ (Sum.elim (eσ.symm (v ∘ Sum.inl)) (fun _ ↦ w)) = 0 :=
        fun m ↦ by simpa [HP] using hP0' m
      exact mul_left_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j))
        ((h2 hHP0 j').symm.trans (hjet _ hvBX w hw k' hP0' j'))
  -- Step 3: Upgrade `r` via the graph criterion, then upgrade `q` by exact holomorphic division.
  have hr_nash : ∀ i, IsHolomorphicNashAt (r i) z₀ :=
    forall_isHolomorphicNashAt_apply_iff_exists_isSemialgebraicOn.mpr
      ⟨AnalyticAt.pi hr, B_X, hBX_open, hzBX, hr_semi⟩
  exact ⟨(isHolomorphicNashAt_eval_monicOfCoeff hc).of_mul_eventuallyEq
    (hG.fun_sub (isHolomorphicNashAt_sum_mul_pow hr_nash)) hq
    (not_eventuallyEq_zero_eval_monicOfCoeff hc0) (hdiv.mono fun _ hp ↦ eq_sub_of_add_eq hp.symm),
    hr_nash⟩

/-! #### Vertical shift transport between `0` and `w₀` -/

/-- Vertical coordinate translation `p ↦ Sum.elim (p ∘ Sum.inl) (fun _ ↦ p (.inr ()) + c₀)`. -/
private def verticalShift {σ : Type*} (c₀ : ℂ) (p : σ ⊕ Unit → ℂ) : σ ⊕ Unit → ℂ :=
  Sum.elim (p ∘ Sum.inl) (fun _ ↦ p (.inr ()) + c₀)

private theorem isHolomorphicNashAt_verticalShift {σ : Type*} [Fintype σ]
    (c₀ : ℂ) (p₀ : σ ⊕ Unit → ℂ) (k : σ ⊕ Unit) :
    IsHolomorphicNashAt (fun p ↦ verticalShift c₀ p k) p₀ := by
  rcases k with s | ⟨⟩
  · exact isHolomorphicNashAt_apply (Sum.inl s)
  · exact (isHolomorphicNashAt_apply (Sum.inr ())).fun_add (isHolomorphicNashAt_const c₀)

private theorem analyticAt_verticalShift {σ : Type*} [Fintype σ]
    (c₀ : ℂ) (p₀ : σ ⊕ Unit → ℂ) :
    AnalyticAt ℂ (verticalShift c₀) p₀ :=
  AnalyticAt.pi fun k ↦ (isHolomorphicNashAt_verticalShift c₀ p₀ k).analyticAt

private theorem verticalShift_zero_right {σ : Type*} (z₀ : σ → ℂ) (w₀ : ℂ) :
    verticalShift w₀ (Sum.elim z₀ 0) = Sum.elim z₀ (fun _ ↦ w₀) := by
  ext (_ | ⟨⟩) <;> simp [verticalShift]

private theorem verticalShift_neg_self {σ : Type*} (z₀ : σ → ℂ) (w₀ : ℂ) :
    verticalShift (-w₀) (Sum.elim z₀ (fun _ ↦ w₀)) = Sum.elim z₀ 0 := by
  ext (_ | ⟨⟩) <;> simp [verticalShift]

private theorem verticalShift_neg_cancel {σ : Type*} (w₀ : ℂ) (p : σ ⊕ Unit → ℂ) :
    verticalShift w₀ (verticalShift (-w₀) p) = p := by
  ext (_ | ⟨⟩) <;> simp [verticalShift]

private theorem continuous_verticalShift {σ : Type*} (c₀ : ℂ) :
    Continuous (verticalShift (σ := σ) c₀) :=
  continuous_pi <| Sum.rec (fun s ↦ continuous_apply (Sum.inl s))
    (fun _ ↦ (continuous_apply (Sum.inr ())).add continuous_const)

private theorem tendsto_verticalShift_zero_right {σ : Type*} (z₀ : σ → ℂ) (w₀ : ℂ) :
    Tendsto (verticalShift w₀) (𝓝 (Sum.elim z₀ 0)) (𝓝 (Sum.elim z₀ (fun _ ↦ w₀))) :=
  verticalShift_zero_right z₀ w₀ ▸ (continuous_verticalShift w₀).tendsto (Sum.elim z₀ 0)

private theorem analyticAt_comp_verticalShift_zero_right {σ : Type*} [Fintype σ]
    {u : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ → ℂ} {w₀ : ℂ}
    (hu : AnalyticAt ℂ u (Sum.elim z₀ (fun _ ↦ w₀))) :
    AnalyticAt ℂ (u ∘ verticalShift w₀) (Sum.elim z₀ 0) :=
  hu.comp_of_eq (analyticAt_verticalShift w₀ (Sum.elim z₀ 0)) (verticalShift_zero_right z₀ w₀)

private theorem isHolomorphicNashAt_comp_verticalShift_iff {σ : Type*} [Fintype σ]
    {F : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ → ℂ} {w₀ : ℂ} :
    IsHolomorphicNashAt (F ∘ verticalShift w₀) (Sum.elim z₀ 0) ↔
      IsHolomorphicNashAt F (Sum.elim z₀ (fun _ ↦ w₀)) := by
  constructor
  · intro hF0
    have hcomp := ((verticalShift_neg_self z₀ w₀).symm ▸ hF0).comp
      (isHolomorphicNashAt_verticalShift (-w₀) (Sum.elim z₀ (fun _ ↦ w₀)))
    exact hcomp.congr (.of_forall fun _ ↦ by simp [verticalShift_neg_cancel])
  · intro hF
    exact ((verticalShift_zero_right z₀ w₀).symm ▸ hF).comp
      (isHolomorphicNashAt_verticalShift w₀ (Sum.elim z₀ 0))

/-- Upgrading a complex Weierstrass preparation at `Sum.elim z₀ (fun _ ↦ w₀)` to
`IsHolomorphicNashAt`. -/
private theorem isHolomorphicNashAt_of_weierstrassPreparation {σ : Type*} [Fintype σ]
    {F u : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ → ℂ} {w₀ : ℂ} {d : ℕ} {c : Fin d → (σ → ℂ) → ℂ}
    (hF : IsHolomorphicNashAt F (Sum.elim z₀ (fun _ ↦ w₀)))
    (hc : ∀ i, AnalyticAt ℂ (c i) z₀) (hc0 : ∀ i, c i z₀ = 0)
    (hu : AnalyticAt ℂ u (Sum.elim z₀ (fun _ ↦ w₀)))
    (hu0 : u (Sum.elim z₀ (fun _ ↦ w₀)) ≠ 0)
    (hfac : F =ᶠ[𝓝 (Sum.elim z₀ (fun _ ↦ w₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - w₀) * u p) :
    (∀ i, IsHolomorphicNashAt (c i) z₀) ∧ IsHolomorphicNashAt u (Sum.elim z₀ (fun _ ↦ w₀)) := by
  obtain ⟨hc_nash, hu0_nash⟩ := isHolomorphicNashAt_of_weierstrassPreparation_zero
    (isHolomorphicNashAt_comp_verticalShift_iff.2 hF) hc hc0
    (analyticAt_comp_verticalShift_zero_right hu)
    (by simpa only [Function.comp_apply, verticalShift_zero_right] using hu0)
    (((tendsto_verticalShift_zero_right z₀ w₀).eventually hfac).mono fun p hp ↦ by
      simpa [verticalShift, Function.comp_def] using hp)
  exact ⟨hc_nash, isHolomorphicNashAt_comp_verticalShift_iff.1 hu0_nash⟩

/-- Upgrading a complex Weierstrass division at `Sum.elim z₀ (fun _ ↦ w₀)` to
`IsHolomorphicNashAt`. -/
private theorem isHolomorphicNashAt_of_weierstrassDivision {σ : Type*} [Fintype σ]
    {G q : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ → ℂ} {w₀ : ℂ} {d : ℕ} {c r : Fin d → (σ → ℂ) → ℂ}
    (hG : IsHolomorphicNashAt G (Sum.elim z₀ (fun _ ↦ w₀)))
    (hc : ∀ i, IsHolomorphicNashAt (c i) z₀) (hc0 : ∀ i, c i z₀ = 0)
    (hq : AnalyticAt ℂ q (Sum.elim z₀ (fun _ ↦ w₀)))
    (hr : ∀ i, AnalyticAt ℂ (r i) z₀)
    (hdiv : G =ᶠ[𝓝 (Sum.elim z₀ (fun _ ↦ w₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - w₀) * q p +
        ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - w₀) ^ (i : ℕ)) :
    IsHolomorphicNashAt q (Sum.elim z₀ (fun _ ↦ w₀)) ∧ ∀ i, IsHolomorphicNashAt (r i) z₀ := by
  obtain ⟨hq0_nash, hr_nash⟩ := isHolomorphicNashAt_of_weierstrassDivision_zero
    (isHolomorphicNashAt_comp_verticalShift_iff.2 hG) hc hc0
    (analyticAt_comp_verticalShift_zero_right hq) hr
    (((tendsto_verticalShift_zero_right z₀ w₀).eventually hdiv).mono fun p hp ↦ by
      simpa [verticalShift, Function.comp_def] using hp)
  exact ⟨isHolomorphicNashAt_comp_verticalShift_iff.1 hq0_nash, hr_nash⟩

end ComplexWeierstrassUpgrade

/-! ### Real Nash Weierstrass preparation and division -/

section RealNashWeierstrass

private theorem complexify_analytic {τ : Type*} [Fintype τ] {f : (τ → ℝ) → ℝ} {x₀ : τ → ℝ}
    (hf : AnalyticAt ℝ f x₀) :
    ∃ F : (τ → ℂ) → ℂ, AnalyticAt ℂ F (fun j ↦ (x₀ j : ℂ)) ∧
      ∀ᶠ y in 𝓝 x₀, F (fun j ↦ (y j : ℂ)) = f y := by
  obtain ⟨r, hr, F, hF, hFf, _⟩ := hf.exists_complexification
  exact ⟨F, hF _ (mem_ball_self hr), eventually_of_mem (ball_mem_nhds x₀ hr) hFf⟩

private theorem ofReal_sumElim {σ : Type*} (x₀ : σ → ℝ) (t₀ : ℝ) :
    (fun k : σ ⊕ Unit ↦ ((Sum.elim x₀ (fun _ : Unit ↦ t₀) k : ℝ) : ℂ)) =
      Sum.elim (fun s ↦ (x₀ s : ℂ)) (fun _ ↦ (t₀ : ℂ)) := by
  ext (_ | ⟨⟩) <;> simp

private theorem ofReal_comp_inl {σ : Type*} (p : σ ⊕ Unit → ℝ) :
    ((fun k ↦ (p k : ℂ)) ∘ Sum.inl) = fun s ↦ ((p ∘ Sum.inl) s : ℂ) := by
  ext s; simp

private theorem eventually_forall_complex_comp_inl {σ ι : Type*} [Finite ι]
    {c : ι → (σ → ℝ) → ℝ} {C : ι → (σ → ℂ) → ℂ} {x₀ : σ → ℝ} (t₀ : ℝ)
    (hCc : ∀ i, ∀ᶠ x in 𝓝 x₀, C i (fun s ↦ (x s : ℂ)) = c i x) :
    ∀ᶠ p in 𝓝 (Sum.elim x₀ (fun _ : Unit ↦ t₀)),
      ∀ i, C i ((fun k ↦ (p k : ℂ)) ∘ Sum.inl) = c i (p ∘ Sum.inl) := by
  have hinl : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ p ∘ Sum.inl)
      (𝓝 (Sum.elim x₀ (fun _ : Unit ↦ t₀))) (𝓝 x₀) :=
    (continuous_pi fun s ↦ continuous_apply (Sum.inl s)).tendsto (Sum.elim x₀ (fun _ ↦ t₀))
  refine (hinl.eventually (eventually_all.2 hCc)).mono fun p hp i ↦ ?_
  rw [ofReal_comp_inl]
  exact hp i

variable {σ : Type*} [Fintype σ]

private theorem analyticAt_sum_mul_sub_pow_sumElim {d : ℕ} {B : Fin d → (σ → ℂ) → ℂ}
    {z₀ : σ → ℂ} {w₀ : ℂ} (hB : ∀ i, AnalyticAt ℂ (B i) z₀) :
    AnalyticAt ℂ (fun p : σ ⊕ Unit → ℂ ↦
      ∑ i : Fin d, B i (p ∘ Sum.inl) * (p (.inr ()) - w₀) ^ (i : ℕ))
      (Sum.elim z₀ (fun _ ↦ w₀)) := by
  have hw : AnalyticAt ℂ (fun p : σ ⊕ Unit → ℂ ↦ p (.inr ()) - w₀) (Sum.elim z₀ (fun _ ↦ w₀)) :=
    ((ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : σ ⊕ Unit ↦ ℂ) (Sum.inr ())).analyticAt _).fun_sub analyticAt_const
  have hsum : AnalyticAt ℂ
      (∑ i : Fin d, fun p : σ ⊕ Unit → ℂ ↦ B i (p ∘ Sum.inl) * (p (.inr ()) - w₀) ^ (i : ℕ))
      (Sum.elim z₀ (fun _ ↦ w₀)) :=
    Finset.sum_induction _ (fun g ↦ AnalyticAt ℂ g (Sum.elim z₀ (fun _ ↦ w₀)))
      (fun _ _ ↦ .add) analyticAt_const fun i _ ↦
        ((hB i).comp_of_eq (AnalyticAt.pi fun s ↦
          (ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : σ ⊕ Unit ↦ ℂ) (Sum.inl s)).analyticAt _)
          rfl).fun_mul (hw.fun_pow (i : ℕ))
  exact hsum.congr (.of_forall fun _ ↦ by simp)

private theorem analyticAt_eval_monicOfCoeff_sumElim {d : ℕ} {C : Fin d → (σ → ℂ) → ℂ}
    {z₀ : σ → ℂ} {w₀ : ℂ} (hC : ∀ i, AnalyticAt ℂ (C i) z₀) :
    AnalyticAt ℂ (fun p : σ ⊕ Unit → ℂ ↦
      (Polynomial.monicOfCoeff (fun i ↦ C i (p ∘ Sum.inl))).eval (p (.inr ()) - w₀))
      (Sum.elim z₀ (fun _ ↦ w₀)) := by
  have hw : AnalyticAt ℂ (fun p : σ ⊕ Unit → ℂ ↦ p (.inr ()) - w₀) (Sum.elim z₀ (fun _ ↦ w₀)) :=
    ((ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : σ ⊕ Unit ↦ ℂ) (Sum.inr ())).analyticAt _).fun_sub analyticAt_const
  exact ((hw.fun_pow d).fun_add (analyticAt_sum_mul_sub_pow_sumElim hC)).congr
    (.of_forall fun _ ↦ (Polynomial.eval_monicOfCoeff _ _).symm)

/-- **Nash upgrading of a real Weierstrass preparation.** If `f : (σ ⊕ Unit → ℝ) → ℝ` is a Nash
germ at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)` and `f = P_c * u` is a real analytic Weierstrass
preparation of `f` at `p₀`, then the coefficient germs `c i` are Nash at `x₀` and the unit `u` is
Nash at `p₀`. -/
theorem IsNashAt.of_weierstrassPreparation {f u : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ} {c : Fin d → (σ → ℝ) → ℝ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℝ u (Sum.elim x₀ (fun _ ↦ t₀)))
    (hu0 : u (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0)
    (hfac : f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * u p) :
    (∀ i, IsNashAt (c i) x₀) ∧ IsNashAt u (Sum.elim x₀ (fun _ ↦ t₀)) := by
  let z₀ : σ → ℂ := fun s ↦ (x₀ s : ℂ)
  have hp₀_eq := ofReal_sumElim x₀ t₀
  obtain ⟨F, hF, hFf⟩ := hf.exists_isHolomorphicNashAt
  obtain ⟨U, hU, hUu⟩ := complexify_analytic hu
  choose C hC hCc using fun i ↦ complexify_analytic (hc i)
  have hC0 (i : Fin d) : C i z₀ = 0 := by
    rw [(hCc i).self_of_nhds, hc0 i, Complex.ofReal_zero]
  have hU0 : U (Sum.elim z₀ (fun _ ↦ (t₀ : ℂ))) ≠ 0 := by
    rw [← hp₀_eq, hUu.self_of_nhds]; exact_mod_cast hu0
  have hfac_C : F =ᶠ[𝓝 (Sum.elim z₀ (fun _ ↦ (t₀ : ℂ)))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ C i (p ∘ Sum.inl))).eval
        (p (.inr ()) - (t₀ : ℂ)) * U p := by
    rw [← hp₀_eq]
    refine hF.analyticAt.eventuallyEq_of_eventually_real
      (hp₀_eq ▸ ((analyticAt_eval_monicOfCoeff_sumElim hC).fun_mul (hp₀_eq ▸ hU))) ?_
    filter_upwards [hFf, hfac, hUu, eventually_forall_complex_comp_inl t₀ hCc]
      with p hFp hp hUp hCp
    rw [hFp]
    simp only [Polynomial.eval_monicOfCoeff] at hp ⊢
    simp only [hCp, hUp]
    exact_mod_cast hp
  obtain ⟨hC_nash, hU_nash⟩ :=
    isHolomorphicNashAt_of_weierstrassPreparation (hp₀_eq ▸ hF) hC hC0 (hp₀_eq ▸ hU) hU0 hfac_C
  exact ⟨fun i ↦ (hC_nash i).isNashAt_of_eventually_real (hCc i),
    (hp₀_eq.symm ▸ hU_nash).isNashAt_of_eventually_real hUu⟩

/-! #### Coordinate transport between `σ ⊕ Unit → ℝ` and `(Fin n → ℝ) × ℝ` -/

private noncomputable def finJoin (q : (Fin (Fintype.card σ) → ℝ) × ℝ) : σ ⊕ Unit → ℝ :=
  Sum.elim (q.1 ∘ Fintype.equivFin σ) (fun _ ↦ q.2)

private noncomputable def finSplit (p : σ ⊕ Unit → ℝ) : (Fin (Fintype.card σ) → ℝ) × ℝ :=
  ((p ∘ Sum.inl) ∘ (Fintype.equivFin σ).symm, p (.inr ()))

private theorem analyticAt_finJoin (y₀ : Fin (Fintype.card σ) → ℝ) (t₀ : ℝ) :
    AnalyticAt ℝ (finJoin (σ := σ)) (y₀, t₀) :=
  AnalyticAt.pi fun k ↦ by
    rcases k with s | ⟨⟩
    · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ)
        (Fintype.equivFin σ s)).analyticAt _).comp_of_eq analyticAt_fst rfl
    · exact analyticAt_snd

private theorem analyticAt_finSplit (p₀ : σ ⊕ Unit → ℝ) :
    AnalyticAt ℝ (finSplit (σ := σ)) p₀ :=
  (AnalyticAt.pi fun j ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ Unit ↦ ℝ)
      (Sum.inl ((Fintype.equivFin σ).symm j))).analyticAt _).prod
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ Unit ↦ ℝ) (Sum.inr ())).analyticAt _)

private theorem finJoin_finSplit (p : σ ⊕ Unit → ℝ) : finJoin (finSplit p) = p := by
  ext (_ | ⟨⟩) <;> simp [finJoin, finSplit]

@[simp]
private theorem comp_equivFin_symm_comp_equivFin (x : σ → ℝ) :
    (x ∘ (Fintype.equivFin σ).symm) ∘ Fintype.equivFin σ = x := by
  ext; simp

private theorem finJoin_equivFin_symm (x₀ : σ → ℝ) (t : ℝ) :
    finJoin (x₀ ∘ (Fintype.equivFin σ).symm, t) = Sum.elim x₀ (fun _ ↦ t) := by
  ext (_ | ⟨⟩) <;> simp [finJoin]

private theorem analyticAt_comp_equivFin_symm {h : (Fin (Fintype.card σ) → ℝ) → ℝ} {x₀ : σ → ℝ}
    (hh : AnalyticAt ℝ h (x₀ ∘ (Fintype.equivFin σ).symm)) :
    AnalyticAt ℝ (fun x ↦ h (x ∘ (Fintype.equivFin σ).symm)) x₀ :=
  hh.comp_of_eq (AnalyticAt.pi fun j ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ↦ ℝ)
      ((Fintype.equivFin σ).symm j)).analyticAt x₀) rfl

private theorem analyticAt_comp_equivFin {h : (σ → ℝ) → ℝ} {x₀ : σ → ℝ}
    (hh : AnalyticAt ℝ h x₀) :
    AnalyticAt ℝ (fun y ↦ h (y ∘ Fintype.equivFin σ)) (x₀ ∘ (Fintype.equivFin σ).symm) :=
  hh.comp_of_eq (AnalyticAt.pi fun s ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ)
      (Fintype.equivFin σ s)).analyticAt _) (comp_equivFin_symm_comp_equivFin x₀)

private theorem eventuallyEq_of_comp_finJoin {f : (σ ⊕ Unit → ℝ) → ℝ}
    {H : (Fin (Fintype.card σ) → ℝ) × ℝ → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    (h : f ∘ finJoin =ᶠ[𝓝 (x₀ ∘ (Fintype.equivFin σ).symm, t₀)] H) :
    f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] H ∘ finSplit := by
  have hsplit : finSplit (Sum.elim x₀ (fun _ : Unit ↦ t₀)) =
      (x₀ ∘ (Fintype.equivFin σ).symm, t₀) := by
    simp [finSplit]
  have hT : Tendsto finSplit (𝓝 (Sum.elim x₀ (fun _ ↦ t₀)))
      (𝓝 (x₀ ∘ (Fintype.equivFin σ).symm, t₀)) :=
    hsplit ▸ (analyticAt_finSplit _).continuousAt.tendsto
  exact (hT.eventually h).mono fun p hp ↦ by simpa [Function.comp_apply, finJoin_finSplit] using hp

/-- **Nash Weierstrass preparation theorem.** Let `f : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite, and suppose the vertical slice
`t ↦ f (Sum.elim x₀ (fun _ ↦ t))` has finite order of vanishing `d` at `t₀`. Then there exist Nash
coefficient germs `c : Fin d → (σ → ℝ) → ℝ` vanishing at `x₀` and a Nash germ `u` nonvanishing at
`p₀` such that near `p₀`,
`f p = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval`
`  (p (.inr ()) - t₀) * u p`. -/
theorem IsNashAt.exists_weierstrassPreparation {f : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hd : analyticOrderAt (fun t ↦ f (Sum.elim x₀ (fun _ ↦ t))) t₀ = d) :
    ∃ (c : Fin d → (σ → ℝ) → ℝ) (u : (σ ⊕ Unit → ℝ) → ℝ),
      (∀ i, IsNashAt (c i) x₀) ∧ (∀ i, c i x₀ = 0) ∧
      IsNashAt u (Sum.elim x₀ (fun _ ↦ t₀)) ∧ u (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0 ∧
      f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * u p := by
  have hf_prod : AnalyticAt ℝ (f ∘ finJoin) (x₀ ∘ (Fintype.equivFin σ).symm, t₀) :=
    hf.analyticAt.comp_of_eq (analyticAt_finJoin _ t₀) (finJoin_equivFin_symm x₀ t₀)
  have hd_prod :
      analyticOrderAt (fun t ↦ (f ∘ finJoin) (x₀ ∘ (Fintype.equivFin σ).symm, t)) t₀ = d := by
    simpa only [Function.comp_apply, finJoin_equivFin_symm] using hd
  obtain ⟨c', u', hc', hc'0, hu', hu'0, hfac'⟩ := hf_prod.exists_weierstrassPreparation_real hd_prod
  let c : Fin d → (σ → ℝ) → ℝ := fun i x ↦ c' i (x ∘ (Fintype.equivFin σ).symm)
  let u : (σ ⊕ Unit → ℝ) → ℝ := u' ∘ finSplit
  have hfac : f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * u p :=
    (eventuallyEq_of_comp_finJoin hfac').mono fun p hp ↦ by simpa [c, u, finSplit] using hp
  obtain ⟨hc_nash, hu_nash⟩ := hf.of_weierstrassPreparation
    (fun i ↦ analyticAt_comp_equivFin_symm (hc' i)) (fun i ↦ hc'0 i)
    (hu'.comp_of_eq (analyticAt_finSplit _) rfl) hu'0 hfac
  exact ⟨c, u, hc_nash, fun i ↦ hc'0 i, hu_nash, hu'0, hfac⟩

/-- **Nash upgrading of a real Weierstrass division by a Weierstrass polynomial.** If
`g : (σ ⊕ Unit → ℝ) → ℝ` is a Nash germ at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, `c : Fin d → (σ → ℝ) →
ℝ` are Nash germs vanishing at `x₀`, and `g = P_c * q + ∑ i, r i * (t - t₀) ^ i` is a real analytic
Weierstrass division at `p₀`, then `q` is Nash at `p₀` and every `r i` is Nash at `x₀`. -/
theorem IsNashAt.of_weierstrassDivision_monicOfCoeff {g q : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ} {c r : Fin d → (σ → ℝ) → ℝ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, IsNashAt (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hq : AnalyticAt ℝ q (Sum.elim x₀ (fun _ ↦ t₀)))
    (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hdiv : g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p +
        ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)) :
    IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ ∀ i, IsNashAt (r i) x₀ := by
  let z₀ : σ → ℂ := fun s ↦ (x₀ s : ℂ)
  have hp₀_eq := ofReal_sumElim x₀ t₀
  obtain ⟨G, hG, hGg⟩ := hg.exists_isHolomorphicNashAt
  choose C hC hCc using fun i ↦ (hc i).exists_isHolomorphicNashAt
  obtain ⟨Q, hQ, hQq⟩ := complexify_analytic hq
  choose R hR hRr using fun i ↦ complexify_analytic (hr i)
  have hC0 (i : Fin d) : C i z₀ = 0 := by
    rw [(hCc i).self_of_nhds, hc0 i, Complex.ofReal_zero]
  have hdiv_C : G =ᶠ[𝓝 (Sum.elim z₀ (fun _ ↦ (t₀ : ℂ)))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ C i (p ∘ Sum.inl))).eval (p (.inr ()) - (t₀ : ℂ)) * Q p +
        ∑ i : Fin d, R i (p ∘ Sum.inl) * (p (.inr ()) - (t₀ : ℂ)) ^ (i : ℕ) := by
    rw [← hp₀_eq]
    refine hG.analyticAt.eventuallyEq_of_eventually_real
      (hp₀_eq ▸ (((analyticAt_eval_monicOfCoeff_sumElim fun i ↦ (hC i).analyticAt).fun_mul
        (hp₀_eq ▸ hQ)).fun_add (analyticAt_sum_mul_sub_pow_sumElim hR))) ?_
    filter_upwards [hGg, hdiv, hQq, eventually_forall_complex_comp_inl t₀ hCc,
      eventually_forall_complex_comp_inl t₀ hRr] with p hGp hp hQp hCp hRp
    rw [hGp]
    simp only [Polynomial.eval_monicOfCoeff] at hp ⊢
    simp only [hCp, hQp, hRp]
    exact_mod_cast hp
  obtain ⟨hQ_nash, hR_nash⟩ :=
    isHolomorphicNashAt_of_weierstrassDivision (hp₀_eq ▸ hG) hC hC0 (hp₀_eq ▸ hQ) hR hdiv_C
  exact ⟨(hp₀_eq.symm ▸ hQ_nash).isNashAt_of_eventually_real hQq,
    fun i ↦ (hR_nash i).isNashAt_of_eventually_real (hRr i)⟩

/-- **Nash Weierstrass division by a Weierstrass polynomial.** Let `c : Fin d → (σ → ℝ) → ℝ` be Nash
germs at `x₀` with `c i x₀ = 0`, with `σ` finite, and let `g : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ
at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`. Then there exist a Nash germ `q` at `p₀` and Nash germs
`r : Fin d → (σ → ℝ) → ℝ` at `x₀` such that near `p₀`,
`g p = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval`
`  (p (.inr ()) - t₀) * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)`. -/
theorem IsNashAt.exists_weierstrassDivision_monicOfCoeff {g : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ} {c : Fin d → (σ → ℝ) → ℝ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, IsNashAt (c i) x₀) (hc0 : ∀ i, c i x₀ = 0) :
    ∃ (q : (σ ⊕ Unit → ℝ) → ℝ) (r : Fin d → (σ → ℝ) → ℝ),
      IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ (∀ i, IsNashAt (r i) x₀) ∧
      g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p +
          ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ) := by
  have hg_prod : AnalyticAt ℝ (g ∘ finJoin) (x₀ ∘ (Fintype.equivFin σ).symm, t₀) :=
    hg.analyticAt.comp_of_eq (analyticAt_finJoin _ t₀) (finJoin_equivFin_symm x₀ t₀)
  have hc0_fin (i : Fin d) : c i ((x₀ ∘ (Fintype.equivFin σ).symm) ∘ Fintype.equivFin σ) = 0 := by
    rw [comp_equivFin_symm_comp_equivFin]; exact hc0 i
  obtain ⟨q', r', hq', hr', hdiv'⟩ :=
    hg_prod.exists_weierstrassDivision_monicOfCoeff_real
      (fun i ↦ analyticAt_comp_equivFin (hc i).analyticAt) hc0_fin
  let q : (σ ⊕ Unit → ℝ) → ℝ := q' ∘ finSplit
  let r : Fin d → (σ → ℝ) → ℝ := fun i x ↦ r' i (x ∘ (Fintype.equivFin σ).symm)
  have hdiv : g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p +
        ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ) :=
    (eventuallyEq_of_comp_finJoin hdiv').mono fun p hp ↦ by
      simpa only [Function.comp_apply, comp_equivFin_symm_comp_equivFin, q, r, finSplit] using hp
  obtain ⟨hq_nash, hr_nash⟩ := hg.of_weierstrassDivision_monicOfCoeff hc hc0
    (hq'.comp_of_eq (analyticAt_finSplit _) rfl)
    (fun i ↦ analyticAt_comp_equivFin_symm (hr' i)) hdiv
  exact ⟨q, r, hq_nash, hr_nash, hdiv⟩

/-- **Nash upgrading of a general real Weierstrass division.** Let `f, g : (σ ⊕ Unit → ℝ) → ℝ` be
Nash germs at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with vertical slice of `f` of finite order `d` at
`t₀`. If `g = f * q + ∑ i : Fin d, r i * (t - t₀) ^ i` is a real analytic Weierstrass division at
`p₀`, then `q` is Nash at `p₀` and every `r i` is Nash at `x₀`. -/
theorem IsNashAt.of_weierstrassDivision {f g q : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ} {r : Fin d → (σ → ℝ) → ℝ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hd : analyticOrderAt (fun t ↦ f (Sum.elim x₀ (fun _ ↦ t))) t₀ = d)
    (hq : AnalyticAt ℝ q (Sum.elim x₀ (fun _ ↦ t₀)))
    (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hdiv : g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      f p * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)) :
    IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ ∀ i, IsNashAt (r i) x₀ := by
  obtain ⟨c, u, hc, hc0, hu, hu0, hprep⟩ := hf.exists_weierstrassPreparation hd
  obtain ⟨huq, hr_nash⟩ := hg.of_weierstrassDivision_monicOfCoeff hc hc0 (hu.analyticAt.mul hq) hr
    (by filter_upwards [hdiv, hprep] with p hp hfp; rw [hp, hfp, mul_assoc, Pi.mul_apply])
  exact ⟨(huq.div hu hu0).congr ((hu.analyticAt.continuousAt.eventually_ne hu0).mono fun p hup ↦ by
    simp [mul_div_cancel_left₀ _ hup]), hr_nash⟩

/-- **Nash Weierstrass division theorem.** Let `f, g : (σ ⊕ Unit → ℝ) → ℝ` be Nash germs at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite, and suppose the vertical slice
`t ↦ f (Sum.elim x₀ (fun _ ↦ t))` has finite order of vanishing `d` at `t₀`. Then there exist a Nash
germ `q` at `p₀` and Nash germs `r : Fin d → (σ → ℝ) → ℝ` at `x₀` such that near `p₀`,
`g p = f p * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)`. -/
theorem IsNashAt.exists_weierstrassDivision {f g : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hd : analyticOrderAt (fun t ↦ f (Sum.elim x₀ (fun _ ↦ t))) t₀ = d) :
    ∃ (q : (σ ⊕ Unit → ℝ) → ℝ) (r : Fin d → (σ → ℝ) → ℝ),
      IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ (∀ i, IsNashAt (r i) x₀) ∧
      g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        f p * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ) := by
  obtain ⟨c, u, hc, hc0, hu, hu0, hprep⟩ := hf.exists_weierstrassPreparation hd
  obtain ⟨q₀, r, hq₀, hr, hdiv⟩ := hg.exists_weierstrassDivision_monicOfCoeff hc hc0
  refine ⟨q₀ / u, r, hq₀.div hu hu0, hr, ?_⟩
  filter_upwards [hprep, hdiv, hu.analyticAt.continuousAt.eventually_ne hu0] with p hp hgp hup
  simp only [Pi.div_apply, hgp, hp, mul_assoc, mul_div_cancel₀ _ hup]

end RealNashWeierstrass

end TauCeti
