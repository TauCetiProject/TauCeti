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
public import TauCeti.LinearAlgebra.RootSystem.CorootEval
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Bipartite
public import TauCeti.RepresentationTheory.BaseChange
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Angle
import TauCeti.Data.List.Pairwise
import TauCeti.LinearAlgebra.Matrix.OfReal
import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Perron
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange

/-!
# Coleman's Coxeter plane and regular primitive-root eigenvectors

For a base `b` of a finite, reduced, irreducible, crystallographic root pairing `P` over a
characteristic-zero domain (or, more generally, a finite, reduced, crystallographic pairing whose
Cartan matrix `b.cartanMatrix` is of finite type with preconnected Dynkin diagram) and a Coxeter
element `c = wordProd P b l` of order `h = orderOf c`, we construct Coleman's real Coxeter plane
(rank ≥ 2) and Steinberg's regular `exp (2πi / h)`-eigenvector with trivial Weyl stabilizer
(assuming `[Nonempty ι]` in the coordinate and finite-type forms).

On `span {e₁, e₂} ⊆ (b.support → ℝ)`, the bipartite Coxeter matrix `W` rotates `(e₁, e₂)` by
`-2π / h` (`Winv` by `+2π / h`), with the open sector `(0, π / h)` in the open dominant cone.
Downstream, `TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Orbit` uses this for freeness of
`⟨c⟩`-orbits on roots and `|Φ| = r · h`; the regular eigenvector also serves Weyl degree formulas.

API guide: use `_of_isFiniteType` forms (only `IsFiniteType b.cartanMatrix` and preconnected
diagram, plus `[Nonempty ι]` for eigenvectors) for non-spanning pairings and `HasCartanType` bases,
and `[P.IsIrreducible]` corollaries (handling `IsEmpty ι` in weight-space forms) otherwise. Choose
`b.support → ℂ` over any char-0 domain `R`, `ℂ ⊗[R] M` with `[Algebra R ℂ]`, or `M` when `R = ℂ`.

## Main results
* `RootPairing.Base.isIrreducible_two_smul_one_sub_transpose_cartanMatrix` / `_of_preconnected`
* `RootPairing.Base.exists_coxeterPlane_bipartiteCoxeterElement` / `_of_isFiniteType`
* `RootPairing.Base.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd` / `_of_isFiniteType`
* `RootPairing.Base.exists_eigenvector_baseChange_weylGroupRootRep_wordProd` / `_of_isFiniteType`
* `RootPairing.Base.exists_isRegularWeight_eigenvector_wordProd` / `_of_isFiniteType`

## References
* A. J. Coleman, *The Betti numbers of the simple Lie groups*, Canad. J. Math. **10** (1958).
* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2;
  J. E. Humphreys, *Reflection Groups and Coxeter Groups*, §§ 3.16–3.17.
-/

public section

open Matrix Submodule TauCeti TensorProduct

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
  · exact (eq_or_ne i j).elim (by rintro rfl; simp) fun hij ↦ by
      simpa [hij] using b.cartanMatrix_le_zero_of_ne j i hij.symm
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

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

private theorem eq_one_of_actsBy_fix_of_forall_pos [P.IsReduced] (b : P.Base)
    {y₀ : b.support → ℝ} (hy₀ : ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) y₀)
    {g : P.weylGroup} {G : Matrix b.support b.support ℤ} (hG : b.ActsBy g G)
    (hGy₀ : (G.map (Int.castRingHom ℝ)) *ᵥ y₀ = y₀) : g = 1 :=
  inv_eq_one.mp <| eq_one_of_mapsTo_posRoots (b := b) fun j hj ↦ by
    rw [← b.corootEval_pos_iff_mem_posRoots hy₀, b.corootEval_weylGroupToPerm_inv hG ℝ j y₀, hGy₀]
    exact b.corootEval_pos_of_mem_posRoots hy₀ hj

section Helpers

variable (b : P.Base) (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)

@[simp] private def colorVec (x : b.support → ℝ) (s : Bool) (i : b.support) : ℝ :=
  if col i = s then x i else 0
private noncomputable def planeBasis₁ (θ : ℝ) (x : b.support → ℝ) : b.support → ℝ :=
  Real.cos θ • b.colorVec col x true + b.colorVec col x false
private noncomputable def planeBasis₂ (θ : ℝ) (x : b.support → ℝ) : b.support → ℝ :=
  Real.sin θ • b.colorVec col x true
private noncomputable def planePoint (θ : ℝ) (x : b.support → ℝ) (φ : ℝ) : b.support → ℝ :=
  Real.cos φ • b.planeBasis₁ col θ x + Real.sin φ • b.planeBasis₂ col θ x

private theorem exists_mem_colorClass [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected) (s : Bool) :
    ∃ i : b.support, col i = s := by
  obtain ⟨i₀, j₀, hij⟩ := exists_pair_ne b.support
  by_cases hi : col i₀ = s
  · exact ⟨i₀, hi⟩
  · match hconn i₀ j₀ with
    | ⟨.nil⟩ => exact (hij rfl).elim
    | ⟨@SimpleGraph.Walk.cons _ _ _ p _ hadj _⟩ =>
      have hne := col.valid ((graph_coxeterMatrixOfBase P b).symm ▸ hadj)
      exact ⟨p, by cases hc1 : col i₀ <;> cases hc2 : col p <;> cases s <;> simp_all⟩

private theorem coxeterPlane_linearIndependent [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected) {θ : ℝ} {x : b.support → ℝ}
    (hx : ∀ i, 0 < x i) (hsinθ : 0 < Real.sin θ) :
    LinearIndependent ℝ ![b.planeBasis₁ col θ x, b.planeBasis₂ col θ x] := by
  rw [Fintype.linearIndependent_iff]; intro g hg; rw [Fin.sum_univ_two] at hg
  obtain ⟨i_t, hit⟩ := exists_mem_colorClass b col hconn true
  obtain ⟨i_f, hif⟩ := exists_mem_colorClass b col hconn false
  have hf0 : g 0 = 0 := (mul_eq_zero.mp <| by
    simpa [planeBasis₁, planeBasis₂, hif] using congrFun hg i_f).resolve_right (hx i_f).ne'
  have ht0 : g 1 = 0 := (mul_eq_zero.mp <| by
    simpa [hf0, planeBasis₂, hit, mul_assoc] using congrFun hg i_t).resolve_right
      (mul_ne_zero hsinθ.ne' (hx i_t).ne')
  intro k; fin_cases k <;> assumption

variable [DecidableEq ι] {μ : ℝ} {x : b.support → ℝ}
  (hBx : ((2 : ℝ) • 1 - (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)) *ᵥ x = μ • x)
include hBx

private theorem corootEval_colorVec (k : b.support) :
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

private theorem colorClassMatrix_mulVec_colorVec (s : Bool) :
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
  refine ⟨funext fun k ↦ ?_, funext fun k ↦ ?_⟩ <;>
    obtain ⟨hsame, hopp⟩ := corootEval_colorVec b col hBx k <;>
    by_cases hck : col k = s
  · subst hck; simp [hrow, hsame]; ring
  · simp [hrow, hck]
  · subst hck; simp [hrow, hopp, Bool.eq_not_self]
  · simp [hrow, hck]

variable {θ : ℝ} (hμ_eq : μ = 2 * Real.cos θ)
include hμ_eq

private theorem coxeterPlane_rotation :
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
  simp only [Bool.not_true, Bool.not_false] at hC₁f hC₂t
  have hsin2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith [Real.cos_sq_add_sin_sq θ]
  have hC₁_e₁ : C₁ *ᵥ e₁ = e₁ := funext fun i ↦ by
    simp only [e₁, planeBasis₁, mulVec_add, mulVec_smul, C₁, hC₁t, hC₁f, hμ_eq, Pi.add_apply,
      Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring
  have hC₁_e₂ : C₁ *ᵥ e₂ = -e₂ := by rw [he₂, planeBasis₂, mulVec_smul, hC₁t, smul_neg]
  have hC₂_e₁ : C₂ *ᵥ e₁ = Real.cos (2 * θ) • e₁ + Real.sin (2 * θ) • e₂ := funext fun i ↦ by
    simp only [e₁, e₂, planeBasis₁, planeBasis₂, mulVec_add, mulVec_smul, C₂, hC₂t, hC₂f, hμ_eq,
      Real.cos_two_mul, Real.sin_two_mul, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination -2 * b.colorVec col x true i * Real.cos θ * hsin2
  have hC₂_e₂ : C₂ *ᵥ e₂ = Real.sin (2 * θ) • e₁ - Real.cos (2 * θ) • e₂ := funext fun i ↦ by
    simp only [e₁, e₂, planeBasis₁, planeBasis₂, mulVec_smul, C₂, hC₂t, hμ_eq, Real.cos_two_mul,
      Real.sin_two_mul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hW : W = C₁ * C₂ := (congrArg (Matrix.map · _) (b.bipartiteCoxeterMatrix_def col)).trans
    (Matrix.map_mul ..)
  refine ⟨by simp [hW, ← mulVec_mulVec, hC₂_e₁, mulVec_add, mulVec_smul, hC₁_e₁, hC₁_e₂,
      sub_eq_add_neg],
    by simp [hW, ← mulVec_mulVec, hC₂_e₂, mulVec_sub, mulVec_smul, hC₁_e₁, hC₁_e₂], fun k φ ↦ ?_⟩
  have hstep (ψ : ℝ) : Winv *ᵥ b.planePoint col θ x ψ = b.planePoint col θ x (ψ + 2 * θ) :=
    funext fun i ↦ by
      have hWinv : Winv = C₂ * C₁ := Matrix.map_mul ..
      simp only [hWinv, ← mulVec_mulVec, planePoint, ← he₁, ← he₂, mulVec_add, mulVec_smul,
        hC₁_e₁, hC₁_e₂, smul_neg, mulVec_neg, hC₂_e₁, hC₂_e₂, Real.cos_add, Real.sin_add,
        Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; ring
  induction k generalizing φ with
  | zero => simp [planePoint]
  | succ k ih => rw [pow_succ', ← mulVec_mulVec, ih, hstep, Nat.cast_succ]; congr 1; ring

private theorem coxeterPlane_corootEval (k : b.support) (φ : ℝ) :
    b.corootEval ℝ (k : ι) (b.planePoint col θ x φ) =
      2 * Real.sin θ * x k * if col k = true then Real.sin φ else Real.sin (θ - φ) := by
  have hsin2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith [Real.cos_sq_add_sin_sq θ]
  obtain ⟨hs, ho⟩ := corootEval_colorVec b col hBx k
  cases hck : col k <;>
    simp only [hck, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true] at hs ho ⊢ <;>
    simp only [planePoint, planeBasis₁, planeBasis₂, map_add, map_smul, smul_eq_mul, hs, ho, hμ_eq]
  · rw [Real.sin_sub]; linear_combination -2 * x k * Real.cos φ * hsin2
  · ring

private theorem coxeterPlane_corootEval_pos (hx : ∀ i, 0 < x i) (hθlt : θ < Real.pi / 2)
    (hsinθ : 0 < Real.sin θ) {φ : ℝ} (hφ0 : 0 < φ) (hφθ : φ < θ) (k : b.support) :
    0 < b.corootEval ℝ (k : ι) (b.planePoint col θ x φ) := by
  rw [coxeterPlane_corootEval b col hBx hμ_eq k φ]
  refine mul_pos (mul_pos (mul_pos two_pos hsinθ) (hx k)) ?_
  split_ifs <;> exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

variable [P.IsReduced]

private theorem coxeterPlane_exists_corootEval_zero [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected) (n : ℕ) (q : ℤ) :
    ∃ j : ι, b.corootEval ℝ j (b.planePoint col θ x (2 * (n : ℝ) * θ + (q : ℝ) * Real.pi)) = 0 := by
  set c := (weylCoxeterSystem P b).bipartiteCoxeterElement col
  let Winv := (b.colorClassMatrix col false * b.colorClassMatrix col true).map (Int.castRingHom ℝ)
  obtain ⟨i₁, hi₁⟩ := exists_mem_colorClass b col hconn true
  have hp_eq : b.planePoint col θ x (2 * (n : ℝ) * θ + (q : ℝ) * Real.pi) =
      ((-1 : ℝ) ^ q) • ((Winv ^ n) *ᵥ b.planePoint col θ x 0) := by
    rw [(coxeterPlane_rotation b col hBx hμ_eq).2.2 n 0]; ext i
    simp only [planePoint, zero_add, Real.cos_add_int_mul_pi, Real.sin_add_int_mul_pi,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have heq := b.corootEval_weylGroupToPerm_inv ((b.actsBy_bipartiteCoxeterElement_inv col).pow n) ℝ
    (P.weylGroupToPerm (c ^ n)⁻¹ (i₁ : ι)) (b.planePoint col θ x 0)
  rw [inv_pow, inv_inv, map_inv, Equiv.Perm.coe_inv, Equiv.apply_symm_apply, Matrix.map_pow] at heq
  refine ⟨(P.weylGroupToPerm (c ^ n)).symm (i₁ : ι), ?_⟩
  rw [hp_eq, map_smul]; dsimp only [Winv]
  rw [← heq, coxeterPlane_corootEval b col hBx hμ_eq i₁ 0]; simp [hi₁]

private theorem coxeterPlane_angle_eq_pi_div_orderOf [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected) (hx : ∀ i, 0 < x i) (hθpos : 0 < θ)
    (hθlt : θ < Real.pi / 2) (hsinθ : 0 < Real.sin θ) :
    θ = Real.pi / (orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement col) : ℝ) := by
  have := P.finite_weylGroup_of_base b
  have hWinv_pow := (coxeterPlane_rotation b col hBx hμ_eq).2.2
  let c := (weylCoxeterSystem P b).bipartiteCoxeterElement col; let h := orderOf c
  set Winv := (b.colorClassMatrix col false * b.colorClassMatrix col true).map (Int.castRingHom ℝ)
  have hWinv_h : Winv ^ h = 1 := by
    have hpow := (b.actsBy_bipartiteCoxeterElement_inv col).pow h
    rw [inv_pow, pow_orderOf_eq_one, inv_one] at hpow
    rw [← Matrix.map_pow, hpow.unique b.actsBy_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcos : Real.cos (2 * (h : ℝ) * θ) = 1 := by
    have hrot : b.planeBasis₁ col θ x = Real.cos (2 * (h : ℝ) * θ) • b.planeBasis₁ col θ x +
        Real.sin (2 * (h : ℝ) * θ) • b.planeBasis₂ col θ x := by
      simpa [planePoint, hWinv_h] using hWinv_pow h 0
    simpa [sub_eq_zero] using Fintype.linearIndependent_iff.mp
      (coxeterPlane_linearIndependent b col hconn hx hsinθ)
      ![Real.cos (2 * (h : ℝ) * θ) - 1, Real.sin (2 * (h : ℝ) * θ)]
      (by simp [Fin.sum_univ_two, sub_smul, sub_add_eq_add_sub, ← hrot]) 0
  refine eq_pi_div_of_cos_two_mul_eq_one (orderOf_pos c) hθpos hcos
    (fun h' hh'0 hh'lt hcos' ↦ ?_) fun n q ⟨h0, hlt⟩ ↦ ?_
  · obtain ⟨m', hm'⟩ := (Real.cos_eq_one_iff (2 * (h' : ℝ) * θ)).mp hcos'
    have hfix : (Winv ^ h') *ᵥ b.planePoint col θ x (θ / 2) = b.planePoint col θ x (θ / 2) := by
      have hangle : θ / 2 + 2 * (h' : ℝ) * θ = θ / 2 + (m' : ℝ) * (2 * Real.pi) := by linarith
      rw [hWinv_pow h' (θ / 2), hangle]
      simp [planePoint, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
    exact Nat.not_dvd_of_pos_of_lt hh'0 hh'lt <| orderOf_dvd_iff_pow_eq_one.mpr <| inv_eq_one.mp <|
      inv_pow c h' ▸ eq_one_of_actsBy_fix_of_forall_pos b
        (coxeterPlane_corootEval_pos b col hBx hμ_eq hx hθlt hsinθ (φ := θ / 2) (by linarith)
          (by linarith))
        ((b.actsBy_bipartiteCoxeterElement_inv col).pow h') (by rwa [Matrix.map_pow])
  · obtain ⟨j, hj⟩ := coxeterPlane_exists_corootEval_zero b col hBx hμ_eq hconn n q
    exact b.corootEval_ne_zero_of_forall_pos
      (coxeterPlane_corootEval_pos b col hBx hμ_eq hx hθlt hsinθ h0 hlt) j hj

end Helpers

variable [DecidableEq ι] [P.IsReduced]

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
  obtain ⟨κ, hκpos, hκlt, x, hx, hxC⟩ := hft.exists_pos_vecMul_eq_smul <|
    (Matrix.isIndecomposable_iff_reflTransGen b.cartanMatrix).2 fun i j ↦
      let ⟨w⟩ := hconn i j
      w.recOn .refl fun {_ _ _} hadj _ ih ↦ .head (diagramGraph_adj.mp hadj).2.1 ih
  set μ : ℝ := 2 - κ; set θ : ℝ := Real.arccos (μ / 2)
  have hBx : ((2 : ℝ) • 1 - (b.cartanMatrixᵀ).map (Int.castRingHom ℝ)) *ᵥ x = μ • x := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, Matrix.transpose_map, Matrix.mulVec_transpose,
      sub_smul]; exact congrArg (2 • x - ·) hxC
  have hθpos : 0 < θ := Real.arccos_pos.mpr (by linarith)
  have hθlt : θ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr (by linarith)
  have hμ_eq : μ = 2 * Real.cos θ := by rw [Real.cos_arccos (by linarith) (by linarith)]; ring
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [Real.pi_pos])
  obtain ⟨hWe₁, hWe₂, hWinv_pow⟩ := coxeterPlane_rotation b col hBx hμ_eq
  have hθ_eq : θ = Real.pi / (h : ℝ) :=
    coxeterPlane_angle_eq_pi_div_orderOf b col hBx hμ_eq hconn hx hθpos hθlt hsinθ
  refine ⟨b.planeBasis₁ col θ x, b.planeBasis₂ col θ x,
    coxeterPlane_linearIndependent b col hconn hx hsinθ,
    by rw [hWe₁, hθ_eq, mul_div_assoc], by rw [hWe₂, hθ_eq, mul_div_assoc], fun k φ ↦ by
      have hangle : φ + 2 * (k : ℝ) * (Real.pi / h) = φ + 2 * Real.pi * k / h := by ring
      simpa only [planePoint, hθ_eq, hangle] using hWinv_pow k φ,
    fun φ hφ0 hφh ↦ coxeterPlane_corootEval_pos b col hBx hμ_eq hx hθlt hsinθ hφ0
      (hθ_eq.symm ▸ hφh)⟩

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
  have : Nonempty ι := ⟨i₀.val⟩; have : NeZero (2 : R) := ⟨by norm_num⟩
  exact b.exists_coxeterPlane_bipartiteCoxeterElement_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) col

end CoxeterPlane

/-! ### Regular primitive-root eigenvectors of arbitrary Coxeter elements -/

section RegularEigenvector

private theorem map_intCast_complex_eq_map_ofReal {m n : Type*} (G : Matrix m n ℤ) :
    G.map (Int.castRingHom ℂ) = (G.map (Int.castRingHom ℝ)).map Complex.ofRealHom := by
  ext; simp

private theorem map_intCast_mulVec_ofReal {m : Type*} [Fintype m]
    (G : Matrix m m ℤ) (u : m → ℝ) :
    (G.map (Int.castRingHom ℂ)) *ᵥ (fun i ↦ (u i : ℂ)) =
      fun i ↦ (((G.map (Int.castRingHom ℝ)) *ᵥ u) i : ℂ) :=
  map_intCast_complex_eq_map_ofReal G ▸ funext fun i ↦ (Complex.ofRealHom.map_mulVec _ u i).symm

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic]

private theorem corootEval_complex_ofReal (b : P.Base) (j : ι) (u : b.support → ℝ) :
    b.corootEval ℂ j (fun i ↦ (u i : ℂ)) = (b.corootEval ℝ j u : ℂ) := by simp [corootEval_apply]

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
  set c := wordProd P b l; obtain ⟨i₀⟩ := b.support_nonempty.to_subtype; classical
  have hW_eq : W = -1 := by
    rw [hW.unique (by simpa [c, hnd.eq_singleton_of_mem (hall i₀)] using b.actsBy_ofIdx i₀)]
    ext k j; rw [Subsingleton.elim k i₀, Subsingleton.elim j i₀]; simp [reflMatrix_apply]
  have hord : orderOf c = 2 := hW.orderOf_eq.trans <| hW_eq ▸
    orderOf_eq_prime (by simp) fun h1 ↦ by simpa using congrFun (congrFun h1 i₀) i₀
  have hv_re (k : b.support) : 0 < b.corootEval ℝ (k : ι) (fun _ ↦ (1 : ℝ)) := by
    rw [Subsingleton.elim k i₀, corootEval_coe_support, Fintype.sum_subsingleton _ i₀,
      b.cartanMatrix_apply_same i₀]; norm_num
  have hangle : (2 : ℂ) * Real.pi * Complex.I / (2 : ℕ) = Real.pi * Complex.I := by push_cast; ring
  refine ⟨fun _ ↦ ((1 : ℝ) : ℂ), fun h ↦ by simpa using congrFun h i₀, ?_,
    fun j hj ↦ ?_, fun g G hG hGv ↦ eq_one_of_actsBy_fix_of_forall_pos b hv_re hG <| by
      rw [map_intCast_mulVec_ofReal] at hGv
      exact funext fun i ↦ Complex.ofReal_injective (congrFun hGv i)⟩
  · rw [hW_eq, hord, hangle, Complex.exp_pi_mul_I]
    ext k; rw [Subsingleton.elim k i₀, Matrix.map_neg _ (map_neg _),
      Matrix.map_one _ (map_zero _) (map_one _), neg_mulVec, one_mulVec]; simp
  · rw [corootEval_complex_ofReal, Complex.ofReal_eq_zero] at hj
    exact b.corootEval_ne_zero_of_forall_pos hv_re j hj

private theorem exists_eigenvector_bipartite_of_isFiniteType [DecidableEq ι] (b : P.Base)
    [Nontrivial b.support] (hft : IsFiniteType b.cartanMatrix)
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    ∃ v₀ : b.support → ℂ, b.IsCoxeterEigenvector
      ((weylCoxeterSystem P b).bipartiteCoxeterElement col) (b.bipartiteCoxeterMatrix col) v₀ := by
  have := P.finite_weylGroup_of_base b
  set c₀ := (weylCoxeterSystem P b).bipartiteCoxeterElement col; have hh_pos := orderOf_pos c₀
  obtain ⟨e₁, e₂, hli, hWe₁, hWe₂, -, hsector⟩ :=
    b.exists_coxeterPlane_bipartiteCoxeterElement_of_isFiniteType hft hconn col
  set v₀ : b.support → ℂ := (fun i ↦ (e₁ i : ℂ)) + Complex.I • (fun i ↦ (e₂ i : ℂ))
  have hy₀ := hsector ((Real.pi / orderOf c₀) / 2) (by positivity) (half_lt_self (by positivity))
  have hangle : (2 : ℂ) * ↑Real.pi * Complex.I / orderOf c₀ =
      ↑(2 * Real.pi / (orderOf c₀ : ℝ)) * Complex.I := by push_cast; ring
  refine ⟨v₀, fun hv0 ↦ hli.ne_zero (0 : Fin 2) (funext fun i ↦ by
      simpa [v₀] using congrArg Complex.re (congrFun hv0 i)),
    ?_, fun j hj0 ↦ ?_, fun g G hG hGv ↦ eq_one_of_actsBy_fix_of_forall_pos b hy₀ hG <| ?_⟩
  · rw [map_intCast_complex_eq_map_ofReal, hangle]; exact map_ofReal_mulVec_of_rotation hWe₁ hWe₂
  · rw [map_add, map_smul, smul_eq_mul, corootEval_complex_ofReal, corootEval_complex_ofReal] at hj0
    have hj₁ : b.corootEval ℝ j e₁ = 0 := by simpa using congrArg Complex.re hj0
    have hj₂ : b.corootEval ℝ j e₂ = 0 := by simpa using congrArg Complex.im hj0
    exact b.corootEval_ne_zero_of_forall_pos hy₀ j (by simp [hj₁, hj₂])
  · rw [mulVec_add, mulVec_smul, map_intCast_mulVec_ofReal, map_intCast_mulVec_ofReal] at hGv
    have he₁ : (G.map (Int.castRingHom ℝ)) *ᵥ e₁ = e₁ := funext fun i ↦ by
      simpa [v₀] using congrArg Complex.re (congrFun hGv i)
    have he₂ : (G.map (Int.castRingHom ℝ)) *ᵥ e₂ = e₂ := funext fun i ↦ by
      simpa [v₀] using congrArg Complex.im (congrFun hGv i)
    rw [mulVec_add, mulVec_smul, mulVec_smul, he₁, he₂]

private theorem exists_eigenvector_of_isConj (b : P.Base)
    {c c₀ : P.weylGroup} {W W₀ : Matrix b.support b.support ℤ}
    (hW : b.ActsBy c W) (hW₀ : b.ActsBy c₀ W₀) (hconj : IsConj c c₀)
    {v₀ : b.support → ℂ} (hv₀ : b.IsCoxeterEigenvector c₀ W₀ v₀) :
    ∃ v : b.support → ℂ, b.IsCoxeterEigenvector c W v := by
  obtain ⟨hv₀_ne, hW₀_eigen, hv₀_reg, hv₀_stab⟩ := hv₀; classical
  obtain ⟨u, hu⟩ := isConj_iff.mp hconj.symm; obtain ⟨_, hcu⟩ := hconj
  obtain ⟨lu, rfl⟩ := exists_wordProd_eq P b u
  obtain ⟨lu', hlu'⟩ := exists_wordProd_eq P b (wordProd P b lu)⁻¹
  set U := (lu.map (reflMatrix b.cartanMatrix)).prod; have hU := b.actsBy_wordProd lu
  set Uinv := (lu'.map (reflMatrix b.cartanMatrix)).prod
  have hUinv : b.ActsBy (wordProd P b lu)⁻¹ Uinv := hlu' ▸ b.actsBy_wordProd lu'
  have hUinvU (x : b.support → ℂ) :
      (Uinv.map (Int.castRingHom ℂ)) *ᵥ ((U.map (Int.castRingHom ℂ)) *ᵥ x) = x := by
    rw [mulVec_mulVec, ← Matrix.map_mul,
      ((by simpa using hUinv.mul hU) : b.ActsBy 1 (Uinv * U)).unique b.actsBy_one,
      Matrix.map_one _ (map_zero _) (map_one _), one_mulVec]
  have hW_conj : W = U * W₀ * Uinv := hW.unique (hu ▸ (hU.mul hW₀).mul hUinv)
  refine ⟨(U.map (Int.castRingHom ℂ)) *ᵥ v₀, fun hv0 ↦ hv₀_ne (by
      simpa only [hUinvU, mulVec_zero] using congrArg ((Uinv.map (Int.castRingHom ℂ)) *ᵥ ·) hv0),
    by simp only [hW_conj, hcu.orderOf_eq, Matrix.map_mul, ← mulVec_mulVec, hUinvU, hW₀_eigen,
      mulVec_smul],
    fun j ↦ b.corootEval_weylGroupToPerm_inv hU ℂ j v₀ ▸ hv₀_reg _, fun g G hG hGv ↦ ?_⟩
  have h1 := hv₀_stab ((wordProd P b lu)⁻¹ * g * wordProd P b lu) (Uinv * G * U)
    ((hUinv.mul hG).mul hU) (by simp only [Matrix.map_mul, ← mulVec_mulVec, hGv, hUinvU])
  simpa [mul_assoc] using congrArg (wordProd P b lu * · * (wordProd P b lu)⁻¹) h1

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
  dsimp only; set c := wordProd P b l with hc; have := P.finite_weylGroup_of_base b; classical
  obtain ⟨v, hv_ne, hv_eig, hv_reg, hv_stab⟩ :
      ∃ v : b.support → ℂ, b.IsCoxeterEigenvector c W v := by
    by_cases hnt : Nontrivial b.support
    · obtain ⟨col⟩ := nonempty_coloring_graph_coxeterMatrixOfBase_of_isFiniteType P b hft
      obtain ⟨v₀, hv₀⟩ := b.exists_eigenvector_bipartite_of_isFiniteType hft hconn col
      exact b.exists_eigenvector_of_isConj hW (b.actsBy_bipartiteCoxeterElement col)
        (by rw [hc, ← weylCoxeterSystem_wordProd]
            exact (weylCoxeterSystem P b).isConj_wordProd_bipartiteCoxeterElement
              (isAcyclic_graph_coxeterMatrixOfBase_of_isFiniteType P b hft) col hnd hall) hv₀
    · have : Subsingleton b.support := not_nontrivial_iff_subsingleton.mp hnt
      exact exists_eigenvector_subsingleton b hnd hall hW
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

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R] [Algebra R ℂ]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

private theorem exists_eigenvector_baseChange_isEmpty [P.IsIrreducible] [IsEmpty ι] (b : P.Base)
    (l : List b.support) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : ℂ ⊗[R] M,
      v ≠ 0 ∧ P.weylGroupRootRep.baseChange ℂ c v = ζ • v ∧ IsPrimitiveRoot ζ (orderOf c) ∧
      (∀ j : ι, LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.coroot' j) v ≠ 0) ∧
      (∀ g : P.weylGroup, P.weylGroupRootRep.baseChange ℂ g v = v → g = 1) := by
  dsimp only; have : IsEmpty b.support := ⟨fun i ↦ IsEmpty.false i.val⟩
  have := IsIrreducible.nontrivial (P := P); obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  obtain ⟨n₀, hr₀⟩ : ∃ n₀ : N, P.toLinearMap m₀ n₀ ≠ 0 := by_contra fun h ↦
    hm₀ ((LinearMap.IsPerfPair.bijective_left P.toLinearMap).injective
      ((LinearMap.ext fun n ↦ not_not.mp fun hn ↦ h ⟨n, hn⟩).trans (map_zero _).symm))
  set r₀ := P.toLinearMap m₀ n₀
  have hS_top : LinearMap.range (LinearMap.lsmul R M r₀) = ⊤ :=
    IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P) _ (fun i ↦ (IsEmpty.false i).elim)
      fun hbot ↦
        let h0 : r₀ • m₀ = 0 := (Submodule.mem_bot R).mp
          (hbot ▸ LinearMap.mem_range_self (LinearMap.lsmul R M r₀) m₀)
        hr₀ (mul_self_eq_zero.mp (by simpa [r₀] using congrArg (· n₀) (congrArg P.toLinearMap h0)))
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : M, r₀ • m₁ = m₀ := LinearMap.mem_range.mp (hS_top ▸ Submodule.mem_top)
  have hp₁ : P.toLinearMap m₁ n₀ = 1 := mul_left_cancel₀ hr₀ <| by
    simpa [hm₁] using (congrArg (fun f ↦ f n₀) (P.toLinearMap.map_smul r₀ m₁)).symm
  have hl_nil (lg : List b.support) : lg = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun i _ ↦ IsEmpty.false i
  refine ⟨1 ⊗ₜ[R] m₁, fun hv0 ↦ one_ne_zero (α := ℂ) <| by simpa [hp₁] using (congrArg
      (LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.toLinearMap.flip n₀)) hv0).symm,
    by simp [hl_nil l], by simp [hl_nil l], fun j ↦ (IsEmpty.false j).elim,
    fun g _ ↦ by obtain ⟨lg, rfl⟩ := exists_wordProd_eq P b g; simp [hl_nil lg]⟩

omit [CharZero R] [IsDomain R] [Finite ι] [P.IsReduced] in
private theorem sum_tmul_root_injective_of_isFiniteType (b : P.Base)
    (hft : IsFiniteType b.cartanMatrix) :
    Function.Injective (fun u : b.support → ℂ ↦ ∑ i : b.support, u i ⊗ₜ[R] P.root i) := by
  classical
  have hunit : IsUnit (b.cartanMatrixᵀ.map (Int.castRingHom ℂ)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr <| isUnit_iff_ne_zero.mpr <| by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_transpose]
      exact Int.cast_ne_zero (α := ℂ).mpr hft.det_ne_zero
  exact fun u₁ u₂ h ↦ Matrix.mulVec_injective_of_isUnit hunit (funext fun k ↦ by
    have hk := congrArg (LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.coroot' (k : ι))) h
    simp only [b.liftBaseChange_coroot'_sum_tmul_root, corootEval_coe_support] at hk
    simpa [mulVec, dotProduct] using hk)

/-- **Complexified weight-space regular primitive-root eigenvector** (Cartan-matrix form): for a
base `b` of a nonempty finite crystallographic reduced root pairing over a char-0 domain `R` with
`[Algebra R ℂ]`, when `b.cartanMatrix` is of finite type with preconnected Dynkin diagram, every
`c = wordProd P b l` of order `h = orderOf c` has a nonzero `exp (2πi / h)`-eigenvector
`v : ℂ ⊗[R] M` lying outside every complexified coroot hyperplane with trivial Weyl stabilizer. -/
theorem exists_eigenvector_baseChange_weylGroupRootRep_wordProd_of_isFiniteType
    [Nonempty ι] (b : P.Base) (hft : IsFiniteType b.cartanMatrix)
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : ℂ ⊗[R] M,
      v ≠ 0 ∧ P.weylGroupRootRep.baseChange ℂ c v = ζ • v ∧
      IsPrimitiveRoot ζ (orderOf c) ∧
      (∀ j : ι, LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.coroot' j) v ≠ 0) ∧
      (∀ g : P.weylGroup, P.weylGroupRootRep.baseChange ℂ g v = v → g = 1) := by
  dsimp only; set c := wordProd P b l; classical
  have hW := b.actsBy_wordProd l
  obtain ⟨y, -, hy_eig, hprim, hy_reg, hy_stab⟩ :=
    b.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd_of_isFiniteType hft hconn hnd hall hW
  let v : ℂ ⊗[R] M := ∑ i : b.support, y i ⊗ₜ[R] P.root i; obtain ⟨j₀⟩ := ‹Nonempty ι›
  refine ⟨v, fun hv0 ↦ hy_reg j₀ ((b.liftBaseChange_coroot'_sum_tmul_root j₀ y).symm.trans <|
      (congrArg _ hv0).trans (map_zero _)),
    by rw [Representation.baseChange_apply, hW.baseChange_weylGroupRootRep_sum_tmul_root y, hy_eig]
       simp [c, v, Finset.smul_sum, smul_tmul'],
    hprim, fun j ↦ b.liftBaseChange_coroot'_sum_tmul_root j y ▸ hy_reg j, fun g hg ↦ ?_⟩
  obtain ⟨lg, rfl⟩ := exists_wordProd_eq P b g; have hG := b.actsBy_wordProd lg
  rw [Representation.baseChange_apply, hG.baseChange_weylGroupRootRep_sum_tmul_root y] at hg
  exact hy_stab _ _ hG (b.sum_tmul_root_injective_of_isFiniteType hft hg)

/-- **Complexified weight-space regular primitive-root eigenvector**: for any finite, reduced,
irreducible, crystallographic root pairing `P` over a char-0 domain `R` with `[Algebra R ℂ]`, every
`c = wordProd P b l` of order `h = orderOf c` has a nonzero `exp (2πi / h)`-eigenvector
`v : ℂ ⊗[R] M` lying outside every complexified coroot hyperplane with trivial Weyl stabilizer. -/
theorem exists_eigenvector_baseChange_weylGroupRootRep_wordProd [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : ℂ ⊗[R] M,
      v ≠ 0 ∧ P.weylGroupRootRep.baseChange ℂ c v = ζ • v ∧
      IsPrimitiveRoot ζ (orderOf c) ∧
      (∀ j : ι, LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.coroot' j) v ≠ 0) ∧
      (∀ g : P.weylGroup, P.weylGroupRootRep.baseChange ℂ g v = v → g = 1) := by
  by_cases hne : Nonempty ι
  · have : NeZero (2 : R) := ⟨by norm_num⟩
    exact b.exists_eigenvector_baseChange_weylGroupRootRep_wordProd_of_isFiniteType
      (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall
  · have : IsEmpty ι := not_nonempty_iff.mp hne; exact exists_eigenvector_baseChange_isEmpty b l

end BaseChangeWeightSpace

section ComplexRootSystem

variable {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  {P : RootPairing ι ℂ M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

omit [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
private theorem exists_isRegularWeight_eigenvector_of_baseChange {c : P.weylGroup} {ζ : ℂ}
    (hex : ∃ v : ℂ ⊗[ℂ] M,
      v ≠ 0 ∧ P.weylGroupRootRep.baseChange ℂ c v = ζ • v ∧ IsPrimitiveRoot ζ (orderOf c) ∧
      (∀ j : ι, LinearMap.liftBaseChange ℂ (Algebra.linearMap ℂ ℂ ∘ₗ P.coroot' j) v ≠ 0) ∧
      (∀ g : P.weylGroup, P.weylGroupRootRep.baseChange ℂ g v = v → g = 1)) :
    ∃ v : M, v ≠ 0 ∧ c • v = ζ • v ∧ IsPrimitiveRoot ζ (orderOf c) ∧
      P.IsRegularWeight v ∧ MulAction.stabilizer P.weylGroup v = ⊥ := by
  obtain ⟨v₀, hv₀_ne, hv₀_eig, hprim, hv₀_reg, hv₀_stab⟩ := hex
  let e := TensorProduct.lid ℂ M
  have he_act (g : P.weylGroup) (x : ℂ ⊗[ℂ] M) :
      e (P.weylGroupRootRep.baseChange ℂ g x) = g • e x := by
    induction x using TensorProduct.inductionOn with
    | tmul r m => simp [e, Representation.baseChange_apply, weylGroupRootRep_apply, smul_comm]
    | add x y hx hy => rw [map_add, map_add, map_add, smul_add, hx, hy]
  have he_cor (j : ι) : LinearMap.liftBaseChange ℂ (Algebra.linearMap ℂ ℂ ∘ₗ P.coroot' j) =
      P.coroot' j ∘ₗ e.toLinearMap := TensorProduct.ext' fun _ _ ↦ by simp [e]
  refine ⟨e v₀, fun h0 ↦ hv₀_ne (e.map_eq_zero_iff.mp h0), by rw [← he_act, hv₀_eig, map_smul],
    hprim, (isRegularWeight_iff P (e v₀)).mpr fun j ↦ LinearMap.congr_fun (he_cor j) v₀ ▸ hv₀_reg j,
    eq_bot_iff.mpr fun g hg ↦ Subgroup.mem_bot.mpr
      (hv₀_stab g (e.injective (by rw [he_act, MulAction.mem_stabilizer_iff.mp hg])))⟩

/-- **Regular primitive-root eigenvector in `M`** (Cartan-matrix form): for a base `b` of a nonempty
finite complex crystallographic reduced root pairing whose Cartan matrix is of finite type with
preconnected Dynkin diagram, every Coxeter element `c = wordProd P b l` of order `h = orderOf c`
has a regular `exp (2πi / h)`-eigenvector in `M` with trivial Weyl stabilizer. -/
theorem exists_isRegularWeight_eigenvector_wordProd_of_isFiniteType [Nonempty ι] (b : P.Base)
    (hft : IsFiniteType b.cartanMatrix) (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : M, v ≠ 0 ∧ c • v = ζ • v ∧ IsPrimitiveRoot ζ (orderOf c) ∧
      P.IsRegularWeight v ∧ MulAction.stabilizer P.weylGroup v = ⊥ :=
  exists_isRegularWeight_eigenvector_of_baseChange
    (b.exists_eigenvector_baseChange_weylGroupRootRep_wordProd_of_isFiniteType hft hconn hnd hall)

/-- **Every Coxeter element of an irreducible finite complex crystallographic reduced root pairing
has a regular primitive-root eigenvector with trivial Weyl stabilizer.** -/
theorem exists_isRegularWeight_eigenvector_wordProd [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : M, v ≠ 0 ∧ c • v = ζ • v ∧ IsPrimitiveRoot ζ (orderOf c) ∧
      P.IsRegularWeight v ∧ MulAction.stabilizer P.weylGroup v = ⊥ :=
  exists_isRegularWeight_eigenvector_of_baseChange
    (b.exists_eigenvector_baseChange_weylGroupRootRep_wordProd hnd hall)

end ComplexRootSystem

end RootPairing.Base

end
