/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.GroupTheory.Coxeter.CoxeterElement
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.CorootEval
public import TauCeti.RepresentationTheory.BaseChange
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.Data.List.Pairwise
import TauCeti.LinearAlgebra.Matrix.OfReal
import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange

/-!
# Coleman's Coxeter plane and regular primitive-root eigenvectors

Following Coleman and Steinberg (Humphreys, §§3.16–3.17), for a base `b` of a finite, reduced,
irreducible, crystallographic root pairing `P`, every Coxeter element is conjugate to a bipartite
Coxeter element (`CoxeterSystem.isConj_wordProd_bipartiteCoxeterElement`). In rank at least two,
splitting the positive Perron–Frobenius eigenvector of `(2 : ℝ) • 1 - Aᵀ` (`A = b.cartanMatrix`) by
colour class yields an adapted plane rotated by `2π / h` with open sector `(0, π / h)` in the open
dominant cone; complexifying (and treating rank at most one directly) gives a regular
`exp (2πi / h)`-eigenvector with trivial Weyl stabilizer in coordinates and in `ℂ ⊗[R] M`.

## Main results
* `RootPairing.Base.isIrreducible_two_smul_one_sub_transpose_cartanMatrix`: irreducibility of
  `(2 : ℝ) • 1 - Aᵀ` in rank at least two.
* `RootPairing.Base.exists_coxeterPlane_bipartiteCoxeterElement` and
  `RootPairing.Base.exists_coxeterPlane_bipartiteCoxeterElement_of_isFiniteType`: Coleman's Coxeter
  plane for a bipartite Coxeter element.
* `RootPairing.Base.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd` and
  `RootPairing.Base.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd_of_isFiniteType`:
  matrix-level regular `exp (2πi / h)`-eigenvectors.
* `RootPairing.Base.exists_eigenvector_baseChange_weylGroupRootRep_wordProd` and
  `RootPairing.Base.exists_regularWeight_eigenvector_wordProd`: regular `exp (2πi / h)`-eigenvector
  with trivial Weyl stabilizer in `ℂ ⊗[R] M` over any characteristic-zero domain `R` with
  `[Algebra R ℂ]`, and directly in `M` over `ℂ`.

## References
* A. J. Coleman, *The Betti numbers of the simple Lie groups*, Canad. J. Math. **10** (1958).
* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, §§ 3.16–3.17.
-/

public section

open Matrix Submodule TauCeti

namespace RootPairing.Base

/-! ### Irreducibility of `(2 : ℝ) • 1 - Aᵀ` -/

section MatrixIrreducibility

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

/-- When the Dynkin diagram of a base `b` of rank at least two is preconnected, the nonnegative
real matrix `(2 : ℝ) • 1 - Aᵀ` is irreducible. -/
theorem isIrreducible_two_smul_one_sub_transpose_cartanMatrix_of_preconnected
    (b : P.Base) [Nontrivial b.support] (hconn : (diagramGraph b.cartanMatrix).Preconnected) :
    ((2 : ℝ) • (1 : Matrix b.support b.support ℝ) -
      (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)).IsIrreducible := by
  refine Matrix.isIrreducible_of_preconnected (fun i j ↦ ?_) hconn fun {i j} h ↦ ?_
  · rcases eq_or_ne i j with rfl | hij
    · simp
    · simpa [hij] using b.cartanMatrix_le_zero_of_ne j i hij.symm
  · rw [diagramGraph_adj] at h
    simpa [h.1] using lt_of_le_of_ne (b.cartanMatrix_le_zero_of_ne j i h.1.symm) h.2.2

/-- **For an irreducible reduced crystallographic root pairing of rank at least two, the nonnegative
real matrix `(2 : ℝ) • 1 - Aᵀ` is irreducible.** -/
theorem isIrreducible_two_smul_one_sub_transpose_cartanMatrix [P.IsReduced] [P.IsIrreducible]
    (b : P.Base) [Nontrivial b.support] :
    ((2 : ℝ) • (1 : Matrix b.support b.support ℝ) -
      (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)).IsIrreducible :=
  b.isIrreducible_two_smul_one_sub_transpose_cartanMatrix_of_preconnected
    (preconnected_diagramGraph_cartanMatrix b)

end MatrixIrreducibility

/-! ### Coleman's Coxeter plane and the exact rotation angle `2π / h` -/

section CoxeterPlane

private theorem coprime_of_mul_eq_mul_pi {h : ℕ} (hh : 2 ≤ h) {θ : ℝ} {m : ℤ}
    (hmθ : (h : ℝ) * θ = (m : ℝ) * Real.pi)
    (hmin : ∀ h' : ℕ, 0 < h' → h' < h → ∀ m' : ℤ, (h' : ℝ) * θ ≠ (m' : ℝ) * Real.pi) :
    m.natAbs.Coprime h := by
  rw [Nat.Coprime]; by_contra hne1
  set d := m.natAbs.gcd h
  have hd_h : d ∣ h := Nat.gcd_dvd_right _ _
  have hd_m : (d : ℤ) ∣ m := Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
  have h1 : (d : ℝ) * ((h / d : ℕ) : ℝ) = h := by exact_mod_cast Nat.mul_div_cancel' hd_h
  have h2 : (d : ℝ) * ((m / (d : ℤ) : ℤ) : ℝ) = m := by exact_mod_cast Int.mul_ediv_cancel' hd_m
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right _ (by omega)
  refine hmin (h / d) (Nat.div_pos (Nat.le_of_dvd (by omega) hd_h) hd0)
    (Nat.div_lt_self (by omega) (Nat.lt_of_le_of_ne hd0 (Ne.symm hne1)))
    (m / (d : ℤ)) (mul_left_cancel₀ (by positivity : (d : ℝ) ≠ 0) ?_)
  linear_combination hmθ + θ * h1 - Real.pi * h2

private theorem eq_pi_div_of_cos_two_mul_eq_one {h : ℕ} (hh : 2 ≤ h) {θ : ℝ} (hθpos : 0 < θ)
    (hcos : Real.cos (2 * (h : ℝ) * θ) = 1)
    (hmin : ∀ h' : ℕ, 0 < h' → h' < h → ∀ m' : ℤ, (h' : ℝ) * θ ≠ (m' : ℝ) * Real.pi)
    (hwall : ∀ (n : ℕ) (q : ℤ),
      ¬ (0 < 2 * (n : ℝ) * θ + (q : ℝ) * Real.pi ∧ 2 * (n : ℝ) * θ + (q : ℝ) * Real.pi < θ)) :
    θ = Real.pi / (h : ℝ) := by
  have hhpos : (0 : ℝ) < h := by positivity
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff (2 * (h : ℝ) * θ)).mp hcos
  have hmθ : (h : ℝ) * θ = (m : ℝ) * Real.pi := by linarith
  have hmpos : 0 < m :=
    Int.cast_pos.mp (pos_of_mul_pos_left (hmθ ▸ mul_pos hhpos hθpos) Real.pi_pos.le)
  have hcop : m.natAbs.Coprime h := coprime_of_mul_eq_mul_pi hh hmθ hmin
  suffices m = 1 by rw [this, Int.cast_one, one_mul] at hmθ; rw [eq_div_iff hhpos.ne']; linarith
  by_contra hm1
  set g : ℕ := (2 * m).gcd (h : ℤ)
  have hg_h : g ∣ h := by simpa [g] using Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_right (2 * m) h)
  have hg_2 : g ∣ 2 := (hcop.coprime_dvd_right hg_h).symm.dvd_of_dvd_mul_right
    (by exact_mod_cast (by simpa [Int.natAbs_of_nonneg hmpos.le] using Int.gcd_dvd_left (2 * m) h :
      (g : ℤ) ∣ (2 * m.natAbs : ℤ)))
  have hg_pos : 0 < g := Int.gcd_pos_of_ne_zero_right _ (by omega)
  have hg_lt_m : (g : ℤ) < m := by
    rcases eq_or_lt_of_le (Nat.le_of_dvd (by norm_num) hg_2) with hg2 | hlt
    · have : m ≠ 2 := fun hm2 ↦ by
        have : 2 ∣ 1 := (by simpa [hm2] using hcop : (2 : ℕ).Coprime h) ▸
          Nat.dvd_gcd (dvd_refl 2) (hg2 ▸ hg_h)
        omega
      omega
    · omega
  set a := Int.gcdA (2 * m) (h : ℤ)
  set n : ℕ := (a % (h : ℤ)).toNat
  set q : ℤ := Int.gcdB (2 * m) (h : ℤ) + 2 * m * (a / (h : ℤ))
  have hcomb : 2 * m * (n : ℤ) + (h : ℤ) * q = (g : ℤ) := by
    linear_combination -Int.gcd_eq_gcd_ab (2 * m) (h : ℤ) + 2 * m * Int.mul_ediv_add_emod a h +
      2 * m * Int.toNat_of_nonneg (Int.emod_nonneg a (by omega : (h : ℤ) ≠ 0))
  have hcr : 2 * (m : ℝ) * n + h * q = g := by exact_mod_cast hcomb
  have hcomb_real : (h : ℝ) * (2 * (n : ℝ) * θ + (q : ℝ) * Real.pi) = (g : ℝ) * Real.pi := by
    linear_combination 2 * (n : ℝ) * hmθ + Real.pi * hcr
  refine hwall n q ⟨pos_of_mul_pos_right ?_ hhpos.le, lt_of_mul_lt_mul_left ?_ hhpos.le⟩
  · rw [hcomb_real]; exact mul_pos (by exact_mod_cast hg_pos) Real.pi_pos
  · rw [hcomb_real, hmθ]; exact mul_lt_mul_of_pos_right (by exact_mod_cast hg_lt_m) Real.pi_pos

private lemma cos_two_mul_eq_one_of_pow_eq_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix κ κ ℝ} {h : ℕ} {θ : ℝ} {e₁ e₂ : κ → ℝ}
    (hli : LinearIndependent ℝ ![e₁, e₂]) (hMh : M ^ h = 1)
    (hrot : (M ^ h) *ᵥ (Real.cos 0 • e₁ + Real.sin 0 • e₂) =
      Real.cos (0 + 2 * (h : ℝ) * θ) • e₁ + Real.sin (0 + 2 * (h : ℝ) * θ) • e₂) :
    Real.cos (2 * (h : ℝ) * θ) = 1 := by
  rw [hMh, one_mulVec, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero, zero_add]
    at hrot
  have hrel : (Real.cos (2 * (h : ℝ) * θ) - 1) • e₁ + Real.sin (2 * (h : ℝ) * θ) • e₂ = 0 := by
    ext i; have hi := congrFun hrot i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢; linarith
  simpa only [Matrix.cons_val_zero, sub_eq_zero] using Fintype.linearIndependent_iff.mp hli
    ![Real.cos (2 * (h : ℝ) * θ) - 1, Real.sin (2 * (h : ℝ) * θ)]
    (by simpa [Fin.sum_univ_two] using hrel) 0

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

@[simp] private def colorVec (b : P.Base) (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    (x : b.support → ℝ) (s : Bool) (i : b.support) : ℝ := if col i = s then x i else 0

private noncomputable def planeBasis₁ (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (θ : ℝ) (x : b.support → ℝ) :
    b.support → ℝ := Real.cos θ • b.colorVec col x true + b.colorVec col x false

private noncomputable def planeBasis₂ (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (θ : ℝ) (x : b.support → ℝ) :
    b.support → ℝ := Real.sin θ • b.colorVec col x true

private noncomputable def planePoint (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (θ : ℝ) (x : b.support → ℝ) (φ : ℝ) :
    b.support → ℝ := Real.cos φ • b.planeBasis₁ col θ x + Real.sin φ • b.planeBasis₂ col θ x

private theorem exists_mem_colorClass (b : P.Base) [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (s : Bool) :
    ∃ i : b.support, col i = s := by
  obtain ⟨i₀, j₀, hij⟩ := exists_pair_ne b.support
  by_cases hi : col i₀ = s
  · exact ⟨i₀, hi⟩
  · obtain ⟨w⟩ := hconn i₀ j₀
    cases w with
    | nil => exact (hij rfl).elim
    | @cons _ p _ hadj _ =>
      have hne := col.valid ((graph_coxeterMatrixOfBase P b).symm ▸ hadj)
      exact ⟨p, by cases hc1 : col i₀ <;> cases hc2 : col p <;> cases s <;> simp_all⟩

private theorem coxeterPlane_linearIndependent (b : P.Base) [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {θ : ℝ} {x : b.support → ℝ} (hx : ∀ i, 0 < x i) (hsinθ : 0 < Real.sin θ) :
    LinearIndependent ℝ ![b.planeBasis₁ col θ x, b.planeBasis₂ col θ x] := by
  rw [Fintype.linearIndependent_iff]; intro g hg; rw [Fin.sum_univ_two] at hg
  obtain ⟨i_t, hit⟩ := exists_mem_colorClass b hconn col true
  obtain ⟨i_f, hif⟩ := exists_mem_colorClass b hconn col false
  have hf0 : g 0 = 0 := by
    have h := congrFun hg i_f
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, planeBasis₁,
      planeBasis₂, colorVec, hif, Bool.false_eq_true, ↓reduceIte, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, mul_zero, zero_add, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (hx i_f).ne'
  have ht0 : g 1 = 0 := by
    have h := congrFun hg i_t; rw [hf0, zero_smul, zero_add] at h
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, planeBasis₂, colorVec, hit,
      ↓reduceIte, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero hsinθ.ne' (hx i_t).ne')
  intro k; fin_cases k <;> assumption

variable [DecidableEq ι]

omit [CharZero R] [IsDomain R] [Finite ι] in
private noncomputable abbrev twoSubCartan (b : P.Base) : Matrix b.support b.support ℝ :=
  (2 : ℝ) • 1 - (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)

omit [CharZero R] [IsDomain R] [Finite ι] in
private theorem perronEigenvalue_lt_two (b : P.Base) [Nonempty b.support]
    (hft : IsFiniteType b.cartanMatrix) {μ : ℝ} {x : b.support → ℝ} (hx : ∀ i, 0 < x i)
    (hBx : b.twoSubCartan *ᵥ x = μ • x) : μ < 2 := by
  obtain ⟨d, hd, hpd_rat⟩ := hft.exists_symmetrizer
  set S_rat : Matrix b.support b.support ℚ := Matrix.of fun i j ↦ d i * (b.cartanMatrix i j : ℚ)
  have hpd : (S_rat.map (Rat.cast : ℚ → ℝ)).PosDef :=
    TauCeti.Matrix.posDef_map_ratCast_iff.mpr hpd_rat
  have hd_pos (i : b.support) : 0 < (d i : ℝ) := by exact_mod_cast hd i
  let y : b.support → ℝ := fun i ↦ x i / (d i : ℝ)
  have hy_pos (i : b.support) : 0 < y i := div_pos (hx i) (hd_pos i)
  obtain ⟨i₀⟩ := ‹Nonempty b.support›
  have hM : (S_rat.map (Rat.cast : ℚ → ℝ)) *ᵥ y = (2 - μ) • x := by
    ext i; have hi := congrFun hBx i; rw [sub_mulVec, smul_mulVec, one_mulVec] at hi
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Matrix.map_apply,
      Int.coe_castRingHom, transpose_apply] at hi ⊢
    have hsum : ∑ j, (S_rat i j : ℝ) * y j = ∑ j, (b.cartanMatrix j i : ℝ) * x j :=
      Finset.sum_congr rfl fun j _ ↦ by
        have hsym := congrArg (Rat.cast : ℚ → ℝ) (hpd_rat.isHermitian.apply j i)
        simp only [S_rat, Matrix.of_apply, star_trivial, Rat.cast_mul, Rat.cast_intCast] at hsym ⊢
        rw [hsym, mul_comm (d j : ℝ), mul_assoc, mul_div_cancel₀ _ (hd_pos j).ne']
    linarith
  have hq := hpd.dotProduct_mulVec_pos (x := y) fun h ↦ (hy_pos i₀).ne' (congrFun h i₀)
  rw [hM, star_trivial, dotProduct_smul, smul_eq_mul] at hq
  linarith [pos_of_mul_pos_left hq
    (Finset.sum_pos (fun i _ ↦ mul_pos (hy_pos i) (hx i)) Finset.univ_nonempty).le]

private theorem corootEval_colorVec (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) {μ : ℝ} {x : b.support → ℝ}
    (hBx : b.twoSubCartan *ᵥ x = μ • x) (k : b.support) :
    b.corootEval ℝ (k : ι) (b.colorVec col x (col k)) = 2 * x k ∧
      b.corootEval ℝ (k : ι) (b.colorVec col x (!(col k))) = -μ * x k := by
  have hsame : b.corootEval ℝ (k : ι) (b.colorVec col x (col k)) = 2 * x k := by
    rw [corootEval_coe_support, Finset.sum_eq_single k (fun i _ hik ↦ ?_) (by simp)]; · simp
    simp only [colorVec]; split_ifs with hci <;>
      simp [hci, b.cartanMatrix_eq_zero_of_color_eq col hik]
  have hkB := congrFun hBx k; rw [sub_mulVec, smul_mulVec, one_mulVec] at hkB
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, transpose_apply,
    map_apply, Int.coe_castRingHom] at hkB
  have htot : ∑ i : b.support, (b.cartanMatrix i k : ℝ) * x i =
      b.corootEval ℝ (k : ι) (b.colorVec col x (col k)) +
        b.corootEval ℝ (k : ι) (b.colorVec col x (!(col k))) := by
    simp only [corootEval_coe_support, ← Finset.sum_add_distrib, colorVec]
    exact Finset.sum_congr rfl fun i _ ↦ by cases col i <;> cases col k <;> simp
  exact ⟨hsame, by linarith⟩

private theorem colorClassMatrix_mulVec_colorVec (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) {μ : ℝ} {x : b.support → ℝ}
    (hBx : b.twoSubCartan *ᵥ x = μ • x) (s : Bool) :
    let C := (b.colorClassMatrix col s).map (Int.castRingHom ℝ)
    C *ᵥ b.colorVec col x s = -b.colorVec col x s ∧
      C *ᵥ b.colorVec col x (!s) = b.colorVec col x (!s) + μ • b.colorVec col x s := by
  intro C
  have hrow (k : b.support) (t : Bool) : (C *ᵥ b.colorVec col x t) k = b.colorVec col x t k -
      if col k = s then b.corootEval ℝ (k : ι) (b.colorVec col x t) else 0 := by
    simp only [C, mulVec, dotProduct, map_apply, Int.coe_castRingHom, colorClassMatrix_apply,
      Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, sub_mul, Finset.sum_sub_distrib,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      corootEval_coe_support]
    congr 1; by_cases hck : col k = s <;> simp [hck]
  refine ⟨funext fun k ↦ ?_, funext fun k ↦ ?_⟩
  · rw [hrow k s, Pi.neg_apply]; obtain ⟨hsame, -⟩ := corootEval_colorVec b col hBx k
    by_cases hck : col k = s
    · subst hck; simp only [↓reduceIte, hsame, colorVec]; ring
    · simp [hck]
  · rw [hrow k (!s), Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨-, hopp⟩ := corootEval_colorVec b col hBx k
    by_cases hck : col k = s
    · subst hck; simp only [↓reduceIte, hopp, colorVec, show col k ≠ !(col k) by simp]; ring
    · simp [hck]

private theorem coxeterPlane_rotation (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) {μ θ : ℝ} {x : b.support → ℝ}
    (hμ_eq : μ = 2 * Real.cos θ) (hBx : b.twoSubCartan *ᵥ x = μ • x) :
    (b.bipartiteCoxeterMatrix col).map (Int.castRingHom ℝ) *ᵥ b.planeBasis₁ col θ x =
        Real.cos (2 * θ) • b.planeBasis₁ col θ x - Real.sin (2 * θ) • b.planeBasis₂ col θ x ∧
      (b.bipartiteCoxeterMatrix col).map (Int.castRingHom ℝ) *ᵥ b.planeBasis₂ col θ x =
        Real.sin (2 * θ) • b.planeBasis₁ col θ x + Real.cos (2 * θ) • b.planeBasis₂ col θ x ∧
      ∀ (k : ℕ) (φ : ℝ),
        (((b.colorClassMatrix col false * b.colorClassMatrix col true).map
          (Int.castRingHom ℝ)) ^ k) *ᵥ b.planePoint col θ x φ =
            b.planePoint col θ x (φ + 2 * (k : ℝ) * θ) := by
  set e₁ := b.planeBasis₁ col θ x with he₁; set e₂ := b.planeBasis₂ col θ x with he₂
  set W := (b.bipartiteCoxeterMatrix col).map (Int.castRingHom ℝ)
  set Winv := (b.colorClassMatrix col false * b.colorClassMatrix col true).map (Int.castRingHom ℝ)
  set C₁ := (b.colorClassMatrix col true).map (Int.castRingHom ℝ)
  set C₂ := (b.colorClassMatrix col false).map (Int.castRingHom ℝ)
  obtain ⟨hC₁t, hC₁f⟩ := colorClassMatrix_mulVec_colorVec b col hBx true
  obtain ⟨hC₂f, hC₂t⟩ := colorClassMatrix_mulVec_colorVec b col hBx false
  simp only [Bool.not_true] at hC₁f; simp only [Bool.not_false] at hC₂t
  have hsin2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith [Real.cos_sq_add_sin_sq θ]
  have hC₁_e₁ : C₁ *ᵥ e₁ = e₁ := by
    simp only [e₁, planeBasis₁, mulVec_add, mulVec_smul, C₁]; rw [hC₁t, hC₁f, hμ_eq]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring
  have hC₁_e₂ : C₁ *ᵥ e₂ = -e₂ := by
    simp only [e₂, planeBasis₂, mulVec_smul, C₁]; rw [hC₁t, smul_neg]
  have hC₂_e₁ : C₂ *ᵥ e₁ = Real.cos (2 * θ) • e₁ + Real.sin (2 * θ) • e₂ := by
    simp only [e₁, e₂, planeBasis₁, planeBasis₂, mulVec_add, mulVec_smul, C₂]
    rw [hC₂t, hC₂f, hμ_eq, Real.cos_two_mul, Real.sin_two_mul]; ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination -2 * (b.colorVec col x true i) * Real.cos θ * hsin2
  have hC₂_e₂ : C₂ *ᵥ e₂ = Real.sin (2 * θ) • e₁ - Real.cos (2 * θ) • e₂ := by
    simp only [e₁, e₂, planeBasis₁, planeBasis₂, mulVec_smul, C₂]
    rw [hC₂t, hμ_eq, Real.cos_two_mul, Real.sin_two_mul]
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hW : W = C₁ * C₂ := by simp only [W, C₁, C₂, b.bipartiteCoxeterMatrix_def, Matrix.map_mul]
  refine ⟨by rw [hW, ← mulVec_mulVec, hC₂_e₁, mulVec_add, mulVec_smul, mulVec_smul,
      hC₁_e₁, hC₁_e₂, smul_neg, sub_eq_add_neg],
    by rw [hW, ← mulVec_mulVec, hC₂_e₂, mulVec_sub, mulVec_smul, mulVec_smul,
      hC₁_e₁, hC₁_e₂, smul_neg, sub_neg_eq_add], fun k φ ↦ ?_⟩
  have hstep (ψ : ℝ) : Real.cos ψ • (Real.cos (2 * θ) • e₁ + Real.sin (2 * θ) • e₂) -
      Real.sin ψ • (Real.sin (2 * θ) • e₁ - Real.cos (2 * θ) • e₂) =
      b.planePoint col θ x (ψ + 2 * θ) := by
    simp only [planePoint, ← he₁, ← he₂, Real.cos_add, Real.sin_add]
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  induction k generalizing φ with
  | zero => simp [planePoint]
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, show Winv = C₂ * C₁ from Matrix.map_mul ..,
      ← mulVec_mulVec, planePoint, mulVec_add, mulVec_smul, mulVec_smul, ← he₁, ← he₂, hC₁_e₁,
      hC₁_e₂, smul_neg, ← sub_eq_add_neg, mulVec_sub, mulVec_smul, mulVec_smul, hC₂_e₁, hC₂_e₂,
      hstep, Nat.cast_succ, show φ + 2 * (k : ℝ) * θ + 2 * θ = φ + 2 * ((k : ℝ) + 1) * θ by ring]

private theorem coxeterPlane_corootEval (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) {μ θ : ℝ} {x : b.support → ℝ}
    (hμ_eq : μ = 2 * Real.cos θ) (hBx : b.twoSubCartan *ᵥ x = μ • x) (k : b.support) (φ : ℝ) :
    b.corootEval ℝ (k : ι) (b.planePoint col θ x φ) =
      2 * Real.sin θ * x k * if col k = true then Real.sin φ else Real.sin (θ - φ) := by
  have hsin2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith [Real.cos_sq_add_sin_sq θ]
  obtain ⟨hs, ho⟩ := corootEval_colorVec b col hBx k
  cases hck : col k
  · simp only [hck, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hs ho ⊢
    simp only [planePoint, planeBasis₁, planeBasis₂, map_add, map_smul, smul_eq_mul, hs, ho,
      hμ_eq, Real.sin_sub]
    linear_combination -2 * x k * Real.cos φ * hsin2
  · simp only [hck, ↓reduceIte, Bool.not_true] at hs ho ⊢
    simp only [planePoint, planeBasis₁, planeBasis₂, map_add, map_smul, smul_eq_mul, hs, ho,
      hμ_eq]; ring

private theorem coxeterPlane_corootEval_pos (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) {μ θ : ℝ} {x : b.support → ℝ}
    (hx : ∀ i, 0 < x i) (hθlt : θ < Real.pi / 2) (hμ_eq : μ = 2 * Real.cos θ)
    (hsinθ : 0 < Real.sin θ) (hBx : b.twoSubCartan *ᵥ x = μ • x)
    {φ : ℝ} (hφ0 : 0 < φ) (hφθ : φ < θ) (k : b.support) :
    0 < b.corootEval ℝ (k : ι) (b.planePoint col θ x φ) := by
  rw [coxeterPlane_corootEval b col hμ_eq hBx k φ]
  refine mul_pos (mul_pos (mul_pos two_pos hsinθ) (hx k)) ?_
  split_ifs <;> exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

variable [P.IsReduced]

omit [DecidableEq ι] in
private theorem eq_one_of_actsBy_fix_of_forall_pos (b : P.Base)
    {y₀ : b.support → ℝ} (hy₀ : ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) y₀)
    {g : P.weylGroup} {G : Matrix b.support b.support ℤ} (hG : b.ActsBy g G)
    (hGy₀ : (G.map (Int.castRingHom ℝ)) *ᵥ y₀ = y₀) : g = 1 := by
  refine inv_eq_one.mp (eq_one_of_mapsTo_posRoots (b := b) fun j hj ↦ ?_)
  rw [← b.corootEval_pos_iff_mem_posRoots hy₀, b.corootEval_weylGroupToPerm_inv hG ℝ j y₀, hGy₀]
  exact b.corootEval_pos_of_mem_posRoots hy₀ hj

private theorem coxeterPlane_exists_corootEval_zero (b : P.Base) [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) {μ θ : ℝ} {x : b.support → ℝ}
    (hμ_eq : μ = 2 * Real.cos θ) (hBx : b.twoSubCartan *ᵥ x = μ • x) (n : ℕ) (q : ℤ) :
    ∃ j : ι, b.corootEval ℝ j (b.planePoint col θ x (2 * (n : ℝ) * θ + (q : ℝ) * Real.pi)) = 0 := by
  set c := (weylCoxeterSystem P b).bipartiteCoxeterElement col
  let Winv := (b.colorClassMatrix col false * b.colorClassMatrix col true).map (Int.castRingHom ℝ)
  obtain ⟨i₁, hi₁⟩ := exists_mem_colorClass b hconn col true
  have hp_eq : b.planePoint col θ x (2 * (n : ℝ) * θ + (q : ℝ) * Real.pi) =
      ((-1 : ℝ) ^ q) • ((Winv ^ n) *ᵥ b.planePoint col θ x 0) := by
    rw [(coxeterPlane_rotation b col hμ_eq hBx).2.2 n 0]; ext i
    simp only [planePoint, zero_add, Real.cos_add_int_mul_pi, Real.sin_add_int_mul_pi,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hinv : P.weylGroupToPerm (c ^ n) (P.weylGroupToPerm (c ^ n)⁻¹ (i₁ : ι)) = i₁ := by
    simp [map_inv]
  have heq := b.corootEval_weylGroupToPerm_inv ((b.actsBy_bipartiteCoxeterElement_inv col).pow n) ℝ
    (P.weylGroupToPerm (c ^ n)⁻¹ (i₁ : ι)) (b.planePoint col θ x 0)
  rw [inv_pow, inv_inv, hinv, Matrix.map_pow] at heq
  refine ⟨P.weylGroupToPerm (c ^ n)⁻¹ (i₁ : ι), ?_⟩
  rw [hp_eq, map_smul, ← heq, coxeterPlane_corootEval b col hμ_eq hBx i₁ 0]; simp [hi₁]

private theorem coxeterPlane_angle_eq_pi_div_orderOf (b : P.Base) [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) {μ θ : ℝ} {x : b.support → ℝ}
    (hx : ∀ i, 0 < x i) (hθpos : 0 < θ) (hθlt : θ < Real.pi / 2) (hμ_eq : μ = 2 * Real.cos θ)
    (hsinθ : 0 < Real.sin θ) (hBx : b.twoSubCartan *ᵥ x = μ • x) :
    θ = Real.pi / (orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement col) : ℝ) := by
  have := P.finite_weylGroup_of_base b
  let c := (weylCoxeterSystem P b).bipartiteCoxeterElement col; let h := orderOf c
  let Winv := (b.colorClassMatrix col false * b.colorClassMatrix col true).map (Int.castRingHom ℝ)
  have hWinv_pow := (coxeterPlane_rotation b col hμ_eq hBx).2.2
  have hWinv_h : Winv ^ h = 1 := by
    have hpow := (b.actsBy_bipartiteCoxeterElement_inv col).pow h
    rw [inv_pow, pow_orderOf_eq_one, inv_one] at hpow
    rw [← Matrix.map_pow, hpow.unique b.actsBy_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine eq_pi_div_of_cos_two_mul_eq_one
    ((weylCoxeterSystem P b).one_lt_orderOf_bipartiteCoxeterElement col) hθpos
    (cos_two_mul_eq_one_of_pow_eq_one (coxeterPlane_linearIndependent b hconn col hx hsinθ)
      hWinv_h (hWinv_pow h 0)) (fun h' hh'0 hh'lt m' hm' ↦ ?_) (fun n q ⟨h0, hlt⟩ ↦ ?_)
  · have hy₀ := coxeterPlane_corootEval_pos b col hx hθlt hμ_eq hsinθ hBx
      (by linarith : 0 < θ / 2) (by linarith : θ / 2 < θ)
    have hfix : (Winv ^ h') *ᵥ b.planePoint col θ x (θ / 2) = b.planePoint col θ x (θ / 2) := by
      rw [hWinv_pow h' (θ / 2),
        show θ / 2 + 2 * (h' : ℝ) * θ = θ / 2 + (m' : ℝ) * (2 * Real.pi) by linarith]
      simp [planePoint, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
    have hc_inv : c⁻¹ ^ h' = 1 := eq_one_of_actsBy_fix_of_forall_pos b hy₀
      ((b.actsBy_bipartiteCoxeterElement_inv col).pow h') (by rwa [Matrix.map_pow])
    exact Nat.not_dvd_of_pos_of_lt hh'0 hh'lt
      (orderOf_dvd_iff_pow_eq_one.mpr (inv_eq_one.mp (inv_pow c h' ▸ hc_inv)))
  · obtain ⟨j, hj⟩ := coxeterPlane_exists_corootEval_zero b hconn col hμ_eq hBx n q
    exact b.corootEval_ne_zero_of_forall_pos
      (coxeterPlane_corootEval_pos b col hx hθlt hμ_eq hsinθ hBx h0 hlt) j hj

/-- **Coleman's Coxeter plane** for a base `b` of rank at least two whose Cartan matrix is of
finite type with preconnected Dynkin diagram (requiring neither spanning nor irreducibility). -/
theorem exists_coxeterPlane_bipartiteCoxeterElement_of_isFiniteType
    (b : P.Base) [Nontrivial b.support] (hft : IsFiniteType b.cartanMatrix)
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    let c := (weylCoxeterSystem P b).bipartiteCoxeterElement col
    let h := orderOf c
    let W := (b.bipartiteCoxeterMatrix col).map (Int.castRingHom ℝ)
    let Winv := (b.colorClassMatrix col false * b.colorClassMatrix col true).map (Int.castRingHom ℝ)
    ∃ e₁ e₂ : b.support → ℝ,
      LinearIndependent ℝ ![e₁, e₂] ∧
      W *ᵥ e₁ = Real.cos (2 * Real.pi / h) • e₁ - Real.sin (2 * Real.pi / h) • e₂ ∧
      W *ᵥ e₂ = Real.sin (2 * Real.pi / h) • e₁ + Real.cos (2 * Real.pi / h) • e₂ ∧
      (∀ (k : ℕ) (φ : ℝ),
        (Winv ^ k) *ᵥ (Real.cos φ • e₁ + Real.sin φ • e₂) =
          Real.cos (φ + 2 * Real.pi * k / h) • e₁ + Real.sin (φ + 2 * Real.pi * k / h) • e₂) ∧
      (∀ φ : ℝ, 0 < φ → φ < Real.pi / h →
        ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) (Real.cos φ • e₁ + Real.sin φ • e₂)) := by
  intro c h W Winv
  obtain ⟨μ, hμpos, x, hx, hBx⟩ :=
    (b.isIrreducible_two_smul_one_sub_transpose_cartanMatrix_of_preconnected
      hconn).exists_mulVec_eq_smul
  have hμlt : μ < 2 := perronEigenvalue_lt_two b hft hx hBx
  set θ : ℝ := Real.arccos (μ / 2)
  have hθpos : 0 < θ := Real.arccos_pos.mpr (by linarith)
  have hθlt : θ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr (by linarith)
  have hμ_eq : μ = 2 * Real.cos θ := by
    linarith [Real.cos_arccos (by linarith : -1 ≤ μ / 2) (by linarith : μ / 2 ≤ 1)]
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [Real.pi_pos])
  obtain ⟨hWe₁, hWe₂, hWinv_pow⟩ := coxeterPlane_rotation b col hμ_eq hBx
  have hθ_eq : θ = Real.pi / (h : ℝ) :=
    coxeterPlane_angle_eq_pi_div_orderOf b hconn col hx hθpos hθlt hμ_eq hsinθ hBx
  refine ⟨b.planeBasis₁ col θ x, b.planeBasis₂ col θ x,
    coxeterPlane_linearIndependent b hconn col hx hsinθ,
    by rw [hWe₁, hθ_eq, mul_div_assoc], by rw [hWe₂, hθ_eq, mul_div_assoc], fun k φ ↦ ?_,
    fun φ hφ0 hφh k ↦ coxeterPlane_corootEval_pos b col hx hθlt hμ_eq hsinθ hBx hφ0
      (hθ_eq.symm ▸ hφh) k⟩
  simpa only [planePoint, hθ_eq,
    show φ + 2 * (k : ℝ) * (Real.pi / h) = φ + 2 * Real.pi * k / h by ring] using hWinv_pow k φ

/-- **Coleman's Coxeter plane** for the bipartite Coxeter element of a finite, reduced,
irreducible, crystallographic root pairing of rank at least two: `(e₁, e₂)` is rotated by `-2π / h`
under `W` (and `+2π / h` under `Winv`), with open sector `(0, π / h)` in the open dominant cone. -/
theorem exists_coxeterPlane_bipartiteCoxeterElement [P.IsIrreducible]
    (b : P.Base) [Nontrivial b.support] (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    let c := (weylCoxeterSystem P b).bipartiteCoxeterElement col
    let h := orderOf c
    let W := (b.bipartiteCoxeterMatrix col).map (Int.castRingHom ℝ)
    let Winv := (b.colorClassMatrix col false * b.colorClassMatrix col true).map (Int.castRingHom ℝ)
    ∃ e₁ e₂ : b.support → ℝ,
      LinearIndependent ℝ ![e₁, e₂] ∧
      W *ᵥ e₁ = Real.cos (2 * Real.pi / h) • e₁ - Real.sin (2 * Real.pi / h) • e₂ ∧
      W *ᵥ e₂ = Real.sin (2 * Real.pi / h) • e₁ + Real.cos (2 * Real.pi / h) • e₂ ∧
      (∀ (k : ℕ) (φ : ℝ),
        (Winv ^ k) *ᵥ (Real.cos φ • e₁ + Real.sin φ • e₂) =
          Real.cos (φ + 2 * Real.pi * k / h) • e₁ + Real.sin (φ + 2 * Real.pi * k / h) • e₂) ∧
      (∀ φ : ℝ, 0 < φ → φ < Real.pi / h →
        ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) (Real.cos φ • e₁ + Real.sin φ • e₂)) := by
  obtain ⟨i₀, -⟩ := exists_pair_ne b.support
  have : Nonempty ι := ⟨i₀.1⟩; have : NeZero (2 : R) := ⟨by norm_num⟩
  exact b.exists_coxeterPlane_bipartiteCoxeterElement_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) col

end CoxeterPlane

/-! ### Regular primitive-root eigenvectors of arbitrary Coxeter elements -/

section RegularEigenvector

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic]

private def IsCoxeterEigenvector (b : P.Base) (c : P.weylGroup)
    (W : Matrix b.support b.support ℤ) (v : b.support → ℂ) : Prop :=
  v ≠ 0 ∧ (W.map (Int.castRingHom ℂ)) *ᵥ v = Complex.exp (2 * Real.pi * Complex.I / orderOf c) • v ∧
    (∀ j : ι, b.corootEval ℂ j v ≠ 0) ∧
    (∀ (g : P.weylGroup) (G : Matrix b.support b.support ℤ),
      b.ActsBy g G → (G.map (Int.castRingHom ℂ)) *ᵥ v = v → g = 1)

variable [CharZero R] [IsDomain R] [Finite ι] [P.IsReduced]

private theorem exists_eigenvector_subsingleton [Nonempty ι] (b : P.Base) [Subsingleton b.support]
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    ∃ v : b.support → ℂ, b.IsCoxeterEigenvector (wordProd P b l) W v := by
  classical
  set c := wordProd P b l
  obtain ⟨i₀⟩ : Nonempty b.support := b.support_nonempty.to_subtype
  have hl_eq : l = [i₀] := hnd.eq_singleton_of_mem (hall i₀)
  have hW_eq : W = -1 := by
    rw [hW.unique (by simpa [c, hl_eq, wordProd_cons, wordProd_nil] using b.actsBy_ofIdx i₀)]
    ext k j; rw [Subsingleton.elim k i₀, Subsingleton.elim j i₀]; simp [reflMatrix_apply]
  have hord : orderOf c = 2 := hW.orderOf_eq.trans <| hW_eq ▸
    orderOf_eq_prime (by simp) fun h1 ↦ by simpa using congrFun (congrFun h1 i₀) i₀
  set v : b.support → ℂ := fun _ ↦ 1
  have hv_re : ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) (fun _ ↦ (1 : ℝ)) := fun k ↦ by
    rw [Subsingleton.elim k i₀, corootEval_coe_support, Fintype.sum_subsingleton _ i₀,
      b.cartanMatrix_apply_same i₀]; norm_num
  refine ⟨v, fun h ↦ one_ne_zero (congrFun h i₀), ?_, fun j hj ↦ ?_, fun g G hG hGv ↦
    eq_one_of_actsBy_fix_of_forall_pos b hv_re hG
      (funext fun i ↦ by simpa [mulVec, dotProduct, v] using congrArg Complex.re (congrFun hGv i))⟩
  · rw [hW_eq, hord, show (2 : ℂ) * ↑Real.pi * Complex.I / (2 : ℕ) = ↑Real.pi * Complex.I by
      push_cast; ring, Complex.exp_pi_mul_I]
    ext k; rw [Subsingleton.elim k i₀, Matrix.map_neg _ (map_neg _),
      Matrix.map_one _ (map_zero _) (map_one _), neg_mulVec, one_mulVec]; simp [v]
  · exact b.corootEval_ne_zero_of_forall_pos hv_re j <| Complex.ofReal_eq_zero.mp <|
      (by simp [corootEval_apply, v] : (b.corootEval ℝ j (fun _ ↦ (1 : ℝ)) : ℂ) = _).trans hj

private theorem exists_eigenvector_bipartite_of_isFiniteType [DecidableEq ι] (b : P.Base)
    [Nontrivial b.support] (hft : IsFiniteType b.cartanMatrix)
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    ∃ v₀ : b.support → ℂ, b.IsCoxeterEigenvector
      ((weylCoxeterSystem P b).bipartiteCoxeterElement col) (b.bipartiteCoxeterMatrix col) v₀ := by
  have := P.finite_weylGroup_of_base b
  set h := orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement col); have hh_pos := orderOf_pos
    ((weylCoxeterSystem P b).bipartiteCoxeterElement col)
  obtain ⟨e₁, e₂, hli, hWe₁, hWe₂, -, hsector⟩ :=
    b.exists_coxeterPlane_bipartiteCoxeterElement_of_isFiniteType hft hconn col
  set v₀ : b.support → ℂ := fun i ↦ (e₁ i : ℂ) + Complex.I * (e₂ i : ℂ)
  set y₀ := Real.cos ((Real.pi / h) / 2) • e₁ + Real.sin ((Real.pi / h) / 2) • e₂
  have hy₀ : ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) y₀ :=
    hsector _ (by positivity) (half_lt_self (by positivity))
  refine ⟨v₀, fun hv0 ↦ hli.ne_zero 0 ?_, ?_, fun j hj0 ↦ ?_, fun g G hG hGv ↦ ?_⟩
  · ext i; simpa [v₀] using congrArg Complex.re (congrFun hv0 i)
  · rw [show (b.bipartiteCoxeterMatrix col).map (Int.castRingHom ℂ) =
        ((b.bipartiteCoxeterMatrix col).map (Int.castRingHom ℝ)).map ((↑) : ℝ → ℂ) by ext; simp,
      show (2 : ℂ) * ↑Real.pi * Complex.I / h = ↑(2 * Real.pi / (h : ℝ)) * Complex.I by
        push_cast; ring]
    exact map_ofReal_mulVec_of_rotation hWe₁ hWe₂
  · have hre : b.corootEval ℝ j e₁ = 0 := by simpa [corootEval_apply, v₀] using congrArg (·.re) hj0
    have him : b.corootEval ℝ j e₂ = 0 := by simpa [corootEval_apply, v₀] using congrArg (·.im) hj0
    exact b.corootEval_ne_zero_of_forall_pos hy₀ j (by simp [y₀, map_add, map_smul, hre, him])
  · have hGe₁ : (G.map (Int.castRingHom ℝ)) *ᵥ e₁ = e₁ := by
      ext i; simpa [mulVec, dotProduct, v₀] using congrArg Complex.re (congrFun hGv i)
    have hGe₂ : (G.map (Int.castRingHom ℝ)) *ᵥ e₂ = e₂ := by
      ext i; simpa [mulVec, dotProduct, v₀] using congrArg Complex.im (congrFun hGv i)
    exact eq_one_of_actsBy_fix_of_forall_pos b hy₀ hG
      (by rw [mulVec_add, mulVec_smul, mulVec_smul, hGe₁, hGe₂])

private theorem exists_eigenvector_of_isConj (b : P.Base)
    {c c₀ : P.weylGroup} {W W₀ : Matrix b.support b.support ℤ}
    (hW : b.ActsBy c W) (hW₀ : b.ActsBy c₀ W₀) (hconj : IsConj c c₀)
    {v₀ : b.support → ℂ} (hv₀ : b.IsCoxeterEigenvector c₀ W₀ v₀) :
    ∃ v : b.support → ℂ, b.IsCoxeterEigenvector c W v := by
  classical
  obtain ⟨hv₀_ne, hW₀_eigen, hv₀_reg, hv₀_stab⟩ := hv₀
  obtain ⟨u, hu⟩ := isConj_iff.mp hconj.symm; obtain ⟨cu, hcu⟩ := hconj
  obtain ⟨lu, hlu⟩ := exists_wordProd_eq P b u; obtain ⟨lu', hlu'⟩ := exists_wordProd_eq P b u⁻¹
  set U := (lu.map (reflMatrix b.cartanMatrix)).prod
  set Uinv := (lu'.map (reflMatrix b.cartanMatrix)).prod
  have hU : b.ActsBy u U := hlu ▸ b.actsBy_wordProd lu
  have hUinv : b.ActsBy u⁻¹ Uinv := hlu' ▸ b.actsBy_wordProd lu'
  have hUinvU_C : Uinv.map (Int.castRingHom ℂ) * U.map (Int.castRingHom ℂ) = 1 := by
    rw [← Matrix.map_mul,
      ((by simpa using hUinv.mul hU) : b.ActsBy 1 (Uinv * U)).unique b.actsBy_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hW_conj : W = U * W₀ * Uinv := hW.unique (hu ▸ (hU.mul hW₀).mul hUinv)
  refine ⟨(U.map (Int.castRingHom ℂ)) *ᵥ v₀, fun hv0 ↦ hv₀_ne ?_, ?_,
    fun j ↦ b.corootEval_weylGroupToPerm_inv hU ℂ j v₀ ▸ hv₀_reg _, fun g G hG hGv ↦ ?_⟩
  · simpa only [mulVec_mulVec, hUinvU_C, one_mulVec, mulVec_zero] using
      congrArg ((Uinv.map (Int.castRingHom ℂ)) *ᵥ ·) hv0
  · rw [hW_conj, hcu.orderOf_eq, Matrix.map_mul, Matrix.map_mul, mulVec_mulVec,
      Matrix.mul_assoc, hUinvU_C, Matrix.mul_one, ← mulVec_mulVec, hW₀_eigen, mulVec_smul]
  · have hfix : ((Uinv * G * U).map (Int.castRingHom ℂ)) *ᵥ v₀ = v₀ := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, ← mulVec_mulVec,
        ← mulVec_mulVec, hGv, mulVec_mulVec, hUinvU_C, one_mulVec]
    calc g = u * (u⁻¹ * g * u) * u⁻¹ := by group
      _ = 1 := by rw [hv₀_stab (u⁻¹ * g * u) (Uinv * G * U) ((hUinv.mul hG).mul hU) hfix]; group

/-- **Matrix-level regular primitive-root eigenvector** of any Coxeter element for a base whose
Cartan matrix is of finite type with preconnected Dynkin diagram. -/
theorem exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd_of_isFiniteType
    [Nonempty ι] (b : P.Base) (hft : IsFiniteType b.cartanMatrix)
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    let c := wordProd P b l
    ∃ v : b.support → ℂ,
      v ≠ 0 ∧ (W.map (Int.castRingHom ℂ)) *ᵥ v =
        Complex.exp (2 * Real.pi * Complex.I / orderOf c) • v ∧
      IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / orderOf c)) (orderOf c) ∧
      (∀ j : ι, b.corootEval ℂ j v ≠ 0) ∧
      (∀ (g : P.weylGroup) (G : Matrix b.support b.support ℤ),
        b.ActsBy g G → (G.map (Int.castRingHom ℂ)) *ᵥ v = v → g = 1) := by
  classical
  dsimp only; set c := wordProd P b l with hc
  have := P.finite_weylGroup_of_base b
  have hex : ∃ v : b.support → ℂ, b.IsCoxeterEigenvector c W v := by
    by_cases hnt : Nontrivial b.support
    · obtain ⟨col⟩ := nonempty_coloring_graph_coxeterMatrixOfBase_of_isFiniteType P b hft
      obtain ⟨v₀, hv₀⟩ := b.exists_eigenvector_bipartite_of_isFiniteType hft hconn col
      have hconj : IsConj c ((weylCoxeterSystem P b).bipartiteCoxeterElement col) := by
        rw [hc, ← weylCoxeterSystem_wordProd]; exact (weylCoxeterSystem P b
          ).isConj_wordProd_bipartiteCoxeterElement
            (isAcyclic_graph_coxeterMatrixOfBase_of_isFiniteType P b hft) col hnd hall
      exact b.exists_eigenvector_of_isConj hW (b.actsBy_bipartiteCoxeterElement col) hconj hv₀
    · have : Subsingleton b.support := not_nontrivial_iff_subsingleton.mp hnt
      exact exists_eigenvector_subsingleton b hnd hall hW
  obtain ⟨v, hv_ne, hv_eig, hv_reg, hv_stab⟩ := hex
  exact ⟨v, hv_ne, hv_eig, Complex.isPrimitiveRoot_exp _ (orderOf_pos c).ne', hv_reg, hv_stab⟩

/-- **Matrix-level regular primitive-root eigenvector of any Coxeter element** of a nonempty,
finite, reduced, irreducible, crystallographic root pairing over a characteristic-zero domain. -/
theorem exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd
    [Nonempty ι] [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    let c := wordProd P b l
    ∃ v : b.support → ℂ,
      v ≠ 0 ∧ (W.map (Int.castRingHom ℂ)) *ᵥ v =
        Complex.exp (2 * Real.pi * Complex.I / orderOf c) • v ∧
      IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / orderOf c)) (orderOf c) ∧
      (∀ j : ι, b.corootEval ℂ j v ≠ 0) ∧
      (∀ (g : P.weylGroup) (G : Matrix b.support b.support ℤ),
        b.ActsBy g G → (G.map (Int.castRingHom ℂ)) *ᵥ v = v → g = 1) := by
  have : NeZero (2 : R) := ⟨by norm_num⟩
  exact b.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall hW

end RegularEigenvector

/-! ### Complexified weight-space regular primitive-root eigenvector -/

section BaseChangeWeightSpace

open TensorProduct

variable {ι R M N : Type*} [CommRing R] [Algebra R ℂ]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}

private theorem baseChange_weylGroupRootRep_sum_tmul_root (b : P.Base) (y : b.support → ℂ)
    {g : P.weylGroup} {G : Matrix b.support b.support ℤ} (hG : b.ActsBy g G) :
    P.weylGroupRootRep.baseChange ℂ g (∑ i : b.support, y i ⊗ₜ[R] P.root i) =
      ∑ i : b.support, ((G.map (Int.castRingHom ℂ)) *ᵥ y) i ⊗ₜ[R] P.root i := by
  rw [map_sum, show ∑ j : b.support, P.weylGroupRootRep.baseChange ℂ g (y j ⊗ₜ[R] P.root j) =
      ∑ j : b.support, y j ⊗ₜ[R] ∑ i : b.support, G i j • P.root i from
    Finset.sum_congr rfl fun j _ ↦ by simp [RootPairing.weylGroupRootRep, actsBy_iff.mp hG j]]
  simp only [tmul_sum, mulVec, dotProduct, map_apply, Int.coe_castRingHom, sum_tmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
  rw [tmul_smul, smul_tmul', zsmul_eq_mul]

variable [P.IsCrystallographic]

private theorem liftBaseChange_coroot'_sum_tmul_root (b : P.Base) (j : ι) (y : b.support → ℂ) :
    LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.coroot' j)
      (∑ i : b.support, y i ⊗ₜ[R] P.root i) = b.corootEval ℂ j y := by
  rw [map_sum, corootEval_apply]; refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [LinearMap.liftBaseChange_tmul, LinearMap.coe_comp, Function.comp_apply,
    Algebra.linearMap_apply, root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ, eq_intCast,
    map_intCast, smul_eq_mul, mul_comm]

variable [CharZero R] [IsDomain R] [Finite ι] [P.IsReduced] [P.IsIrreducible]

private theorem exists_eigenvector_baseChange_isEmpty [IsEmpty ι] (b : P.Base)
    (l : List b.support) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : ℂ ⊗[R] M,
      v ≠ 0 ∧ P.weylGroupRootRep.baseChange ℂ c v = ζ • v ∧
      IsPrimitiveRoot ζ (orderOf c) ∧
      (∀ j : ι, LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.coroot' j) v ≠ 0) ∧
      (∀ g : P.weylGroup, P.weylGroupRootRep.baseChange ℂ g v = v → g = 1) := by
  dsimp only
  have : IsEmpty b.support := ⟨fun i ↦ IsEmpty.false i.1⟩
  have := IsIrreducible.nontrivial (P := P)
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  have hne_dual : P.toLinearMap m₀ ≠ 0 := fun h0 ↦
    hm₀ ((LinearMap.IsPerfPair.bijective_left P.toLinearMap).injective (h0.trans (map_zero _).symm))
  obtain ⟨n₀, hr₀⟩ : ∃ n₀ : N, P.toLinearMap m₀ n₀ ≠ 0 := by
    by_contra! h; exact hne_dual (LinearMap.ext h)
  set r₀ := P.toLinearMap m₀ n₀
  have hS_ne : LinearMap.range (LinearMap.lsmul R M r₀) ≠ ⊥ := fun hbot ↦ hr₀ <|
    mul_self_eq_zero.mp (by
      have hrm₀ : r₀ • m₀ = 0 := (Submodule.mem_bot R).mp
        (hbot ▸ LinearMap.mem_range_self (LinearMap.lsmul R M r₀) m₀)
      simpa [r₀] using congrArg (fun f ↦ f n₀) (congrArg P.toLinearMap hrm₀))
  have hS_top : LinearMap.range (LinearMap.lsmul R M r₀) = ⊤ :=
    IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P) _ (fun i ↦ (IsEmpty.false i).elim)
      hS_ne
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : M, r₀ • m₁ = m₀ := LinearMap.mem_range.mp (hS_top ▸ Submodule.mem_top)
  have hp₁ : P.toLinearMap m₁ n₀ = 1 := mul_left_cancel₀ hr₀ <| by
    simpa [hm₁] using (congrArg (fun f ↦ f n₀) (P.toLinearMap.map_smul r₀ m₁)).symm
  have hv_ne : (1 ⊗ₜ[R] m₁ : ℂ ⊗[R] M) ≠ 0 := fun hv0 ↦ one_ne_zero (α := ℂ) <| by
    simpa [hp₁] using (congrArg
      (LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.toLinearMap.flip n₀)) hv0).symm
  have hl_nil : ∀ lg : List b.support, lg = [] := fun _ ↦
    List.eq_nil_iff_forall_not_mem.mpr fun i _ ↦ IsEmpty.false i
  have hc : wordProd P b l = 1 := by simp [hl_nil l]
  refine ⟨1 ⊗ₜ[R] m₁, hv_ne, by simp [hc], ?_, fun j ↦ (IsEmpty.false j).elim, fun g _ ↦ ?_⟩
  · rw [hc, orderOf_one, Nat.cast_one, div_one, Complex.exp_two_pi_mul_I]; exact IsPrimitiveRoot.one
  · obtain ⟨lg, hlg⟩ := exists_wordProd_eq P b g; rw [← hlg, hl_nil lg, wordProd_nil]

/-- **Complexified weight-space regular primitive-root eigenvector**: for any finite, reduced,
irreducible, crystallographic root pairing `P` over a characteristic-zero domain `R` with an
`R`-algebra structure on `ℂ` (in particular `R = ℚ`, `ℝ`, or `ℂ`), every Coxeter element admits a
nonzero eigenvector `v : ℂ ⊗[R] M` for `P.weylGroupRootRep.baseChange ℂ` with primitive eigenvalue
`exp (2πi / h)`, nonvanishing on every complexified coroot hyperplane, and trivial Weyl
stabilizer. -/
theorem exists_eigenvector_baseChange_weylGroupRootRep_wordProd (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : ℂ ⊗[R] M,
      v ≠ 0 ∧ P.weylGroupRootRep.baseChange ℂ c v = ζ • v ∧
      IsPrimitiveRoot ζ (orderOf c) ∧
      (∀ j : ι, LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.coroot' j) v ≠ 0) ∧
      (∀ g : P.weylGroup, P.weylGroupRootRep.baseChange ℂ g v = v → g = 1) := by
  by_cases hne : Nonempty ι
  · classical
    dsimp only; set c := wordProd P b l
    have : Nonempty ι := hne
    have : NeZero (2 : R) := ⟨by norm_num⟩
    have hW : b.ActsBy c (l.map (reflMatrix b.cartanMatrix)).prod := b.actsBy_wordProd l
    obtain ⟨y, -, hy_eig, hprim, hy_reg, hy_stab⟩ :=
      b.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd hnd hall hW
    set v : ℂ ⊗[R] M := ∑ i : b.support, y i ⊗ₜ[R] P.root i
    have heval (j : ι) :
        LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.coroot' j) v = b.corootEval ℂ j y :=
      b.liftBaseChange_coroot'_sum_tmul_root j y
    obtain ⟨j₀⟩ := hne
    refine ⟨v, fun hv0 ↦ hy_reg j₀ (by rw [← heval j₀, hv0, map_zero]), ?_, hprim,
      fun j ↦ heval j ▸ hy_reg j, fun g hg ↦ ?_⟩
    · rw [b.baseChange_weylGroupRootRep_sum_tmul_root y hW, hy_eig]
      simp [c, v, Finset.smul_sum, smul_tmul']
    · obtain ⟨lg, hlg⟩ := exists_wordProd_eq P b g
      set G := (lg.map (reflMatrix b.cartanMatrix)).prod
      have hG : b.ActsBy g G := hlg ▸ b.actsBy_wordProd lg
      rw [b.baseChange_weylGroupRootRep_sum_tmul_root y hG] at hg
      set u : b.support → ℂ := (G.map (Int.castRingHom ℂ)) *ᵥ y - y
      have hu_ker : (b.cartanMatrixᵀ.map (Int.castRingHom ℂ)) *ᵥ u = 0 := funext fun k ↦ by
        have hk := congrArg
          (LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.coroot' (k : ι))) hg
        rw [b.liftBaseChange_coroot'_sum_tmul_root, b.liftBaseChange_coroot'_sum_tmul_root,
          corootEval_coe_support, corootEval_coe_support] at hk
        simpa [u, mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, sub_eq_zero] using hk
      have hdet : ((Int.castRingHom ℂ).mapMatrix b.cartanMatrixᵀ).det ≠ 0 := by
        rw [← RingHom.map_det, det_transpose, Int.coe_castRingHom]
        exact Int.cast_ne_zero.mpr (isFiniteType_cartanMatrix b).det_ne_zero
      have hu0 : u = 0 := Matrix.mulVec_injective_of_isUnit
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (by simpa using hdet)))
        (hu_ker.trans (mulVec_zero _).symm)
      exact hy_stab g G hG (sub_eq_zero.mp hu0)
  · have : IsEmpty ι := not_nonempty_iff.mp hne
    exact exists_eigenvector_baseChange_isEmpty b l

end BaseChangeWeightSpace

section ComplexRootSystem

open TensorProduct

variable {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  {P : RootPairing ι ℂ M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- **Every Coxeter element of an irreducible finite complex crystallographic reduced root pairing
has a regular primitive-root eigenvector with trivial Weyl stabilizer.** -/
theorem exists_regularWeight_eigenvector_wordProd (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : M,
      v ≠ 0 ∧ c • v = ζ • v ∧ IsPrimitiveRoot ζ (orderOf c) ∧
      P.IsRegularWeight v ∧ MulAction.stabilizer P.weylGroup v = ⊥ := by
  dsimp only
  obtain ⟨v₀, hv₀_ne, hv₀_eig, hprim, hv₀_reg, hv₀_stab⟩ :=
    b.exists_eigenvector_baseChange_weylGroupRootRep_wordProd hnd hall
  let e : ℂ ⊗[ℂ] M ≃ₗ[ℂ] M := TensorProduct.lid ℂ M
  have he_act (g : P.weylGroup) (x : ℂ ⊗[ℂ] M) :
      e (P.weylGroupRootRep.baseChange ℂ g x) = g • e x := by
    simpa [RootPairing.weylGroupRootRep] using LinearMap.congr_fun
      (TensorProduct.ext' fun a m ↦ by simp [e, RootPairing.weylGroupRootRep] :
        e.toLinearMap ∘ₗ P.weylGroupRootRep.baseChange ℂ g =
          P.weylGroupRootRep g ∘ₗ e.toLinearMap) x
  have he_cor_lin (j : ι) :
      LinearMap.liftBaseChange ℂ (Algebra.linearMap ℂ ℂ ∘ₗ P.coroot' j) =
        P.coroot' j ∘ₗ e.toLinearMap :=
    TensorProduct.ext' fun a m ↦ by simp [e]
  refine ⟨e v₀, fun h0 ↦ hv₀_ne (e.map_eq_zero_iff.mp h0),
    by rw [← he_act, hv₀_eig, map_smul], hprim,
    (isRegularWeight_iff P (e v₀)).mpr fun j ↦ LinearMap.congr_fun (he_cor_lin j) v₀ ▸ hv₀_reg j,
    eq_bot_iff.mpr fun g hg ↦ Subgroup.mem_bot.mpr (hv₀_stab g (e.injective ?_))⟩
  rw [he_act, MulAction.mem_stabilizer_iff.mp hg]

end ComplexRootSystem

end RootPairing.Base

end
