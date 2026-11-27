/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.GroupTheory.Coxeter.CoxeterElement
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.CorootEval
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Bipartite
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Angle
import TauCeti.Data.List.Pairwise
import TauCeti.LinearAlgebra.Matrix.OfReal
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Perron
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange

/-!
# Coleman's Coxeter plane and matrix-level regular primitive-root eigenvectors

For a base `b` of a finite, reduced, irreducible, crystallographic root pairing `P` over a
characteristic-zero domain (or a finite, reduced, crystallographic pairing whose Cartan matrix is of
finite type with preconnected Dynkin diagram) and a Coxeter element `c = wordProd P b l` of order
`h = orderOf c`, we construct Coleman's real Coxeter plane (rank ≥ 2) and a matrix-level regular
`exp (2πi / h)`-eigenvector in `b.support → ℂ` with trivial Weyl stabilizer. On `span {e₁, e₂}`,
the bipartite Coxeter matrix `W` rotates by `-2π / h` (`Winv` by `+2π / h`), and the open sector
`0 < φ < π / h` of the plane lies in the open dominant cone.

## Main results
* `RootPairing.Base.exists_coxeterPlane_bipartiteCoxeterElement` / `_of_isFiniteType`
* `RootPairing.Base.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd` / `_of_isFiniteType`

## References
* A. J. Coleman, *The Betti numbers of the simple Lie groups*, Canad. J. Math. **10** (1958).
* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2;
  J. E. Humphreys, *Reflection Groups and Coxeter Groups*, §§ 3.16–3.17.
-/

public section

open Matrix TauCeti

namespace RootPairing.Base

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

private def colorVec (x : b.support → ℝ) (s : Bool) : b.support → ℝ :=
  fun i ↦ if col i = s then x i else 0
private noncomputable def planeBasis₁ (θ : ℝ) (x : b.support → ℝ) : b.support → ℝ :=
  Real.cos θ • b.colorVec col x true + b.colorVec col x false
private noncomputable def planeBasis₂ (θ : ℝ) (x : b.support → ℝ) : b.support → ℝ :=
  Real.sin θ • b.colorVec col x true
private noncomputable def planePoint (θ : ℝ) (x : b.support → ℝ) (φ : ℝ) : b.support → ℝ :=
  Real.cos φ • b.planeBasis₁ col θ x + Real.sin φ • b.planeBasis₂ col θ x

private theorem exists_mem_colorClass [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected) (s : Bool) :
    ∃ i : b.support, col i = s :=
  let ⟨i₀, j₀, hij⟩ := exists_pair_ne b.support
  if hi : col i₀ = s then ⟨i₀, hi⟩ else match hconn i₀ j₀ with
  | ⟨.nil⟩ => (hij rfl).elim
  | ⟨@SimpleGraph.Walk.cons _ _ _ p _ hadj _⟩ =>
    have := col.valid ((graph_coxeterMatrixOfBase P b).symm ▸ hadj)
    ⟨p, by cases hc1 : col i₀ <;> cases hc2 : col p <;> cases s <;> simp_all⟩

private theorem coxeterPlane_linearIndependent [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected) {θ : ℝ} {x : b.support → ℝ}
    (hx : ∀ i, 0 < x i) (hsinθ : 0 < Real.sin θ) :
    LinearIndependent ℝ ![b.planeBasis₁ col θ x, b.planeBasis₂ col θ x] := by
  rw [Fintype.linearIndependent_iff]; intro g hg; rw [Fin.sum_univ_two] at hg
  obtain ⟨i_t, hit⟩ := exists_mem_colorClass b col hconn true
  obtain ⟨i_f, hif⟩ := exists_mem_colorClass b col hconn false
  have hf0 : g 0 = 0 := (mul_eq_zero.mp <| by
    simpa [planeBasis₁, planeBasis₂, colorVec, hif] using congrFun hg i_f).resolve_right
    (hx i_f).ne'
  have ht0 : g 1 = 0 := (mul_eq_zero.mp <| by
    simpa [hf0, planeBasis₂, colorVec, hit, mul_assoc] using congrFun hg i_t).resolve_right
    (mul_ne_zero hsinθ.ne' (hx i_t).ne')
  intro k; fin_cases k <;> assumption

private theorem cos_eq_one_of_planePoint_eq_zero [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected) {θ : ℝ} {x : b.support → ℝ}
    (hx : ∀ i, 0 < x i) (hsinθ : 0 < Real.sin θ) {t : ℝ}
    (ht : b.planePoint col θ x t = b.planePoint col θ x 0) : Real.cos t = 1 := by
  have hcomb : (Real.cos t - 1) • b.planeBasis₁ col θ x +
      Real.sin t • b.planeBasis₂ col θ x = 0 := by
    rw [← sub_eq_zero.mpr ht]; simp [planePoint, sub_smul]; abel
  have hg := Fintype.linearIndependent_iff.mp
    (coxeterPlane_linearIndependent b col hconn hx hsinθ) ![Real.cos t - 1, Real.sin t]
  rw [Fin.sum_univ_two] at hg; exact sub_eq_zero.mp (hg hcomb 0)

variable {κ : ℝ} {x : b.support → ℝ} (hxC : x ᵥ* b.cartanMatrix.map (Int.castRingHom ℝ) = κ • x)
  {θ : ℝ} (hμ_eq : 2 - κ = 2 * Real.cos θ)
include hxC hμ_eq

private theorem coxeterPlane_rotation [DecidableEq ι] :
    (b.bipartiteCoxeterMatrix col).map (Int.castRingHom ℝ) *ᵥ b.planeBasis₁ col θ x =
        Real.cos (2 * θ) • b.planeBasis₁ col θ x - Real.sin (2 * θ) • b.planeBasis₂ col θ x ∧
      (b.bipartiteCoxeterMatrix col).map (Int.castRingHom ℝ) *ᵥ b.planeBasis₂ col θ x =
        Real.sin (2 * θ) • b.planeBasis₁ col θ x + Real.cos (2 * θ) • b.planeBasis₂ col θ x ∧
      ∀ (k : ℕ) (φ : ℝ),
        (((b.colorClassMatrix col false * b.colorClassMatrix col true).map
          (Int.castRingHom ℝ)) ^ k) *ᵥ b.planePoint col θ x φ =
            b.planePoint col θ x (φ + 2 * (k : ℝ) * θ) := by
  set W := (b.bipartiteCoxeterMatrix col).map (Int.castRingHom ℝ)
  set Winv := (b.colorClassMatrix col false * b.colorClassMatrix col true).map (Int.castRingHom ℝ)
  have hWt : W *ᵥ b.colorVec col x true =
      ((2 - κ) ^ 2 - 1) • b.colorVec col x true + (2 - κ) • b.colorVec col x false :=
    b.bipartiteCoxeterMatrix_mulVec_ite_color_true col hxC
  have hWf : W *ᵥ b.colorVec col x false =
      -b.colorVec col x false - (2 - κ) • b.colorVec col x true :=
    b.bipartiteCoxeterMatrix_mulVec_ite_color_false col hxC
  have hsin2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith [Real.cos_sq_add_sin_sq θ]
  have hWe₁ : W *ᵥ b.planeBasis₁ col θ x =
      Real.cos (2 * θ) • b.planeBasis₁ col θ x - Real.sin (2 * θ) • b.planeBasis₂ col θ x :=
    funext fun i ↦ by
      simp only [planeBasis₁, planeBasis₂, mulVec_add, mulVec_smul, hWt, hWf, hμ_eq,
        Real.cos_two_mul, Real.sin_two_mul, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
        Pi.smul_apply, smul_eq_mul]
      linear_combination 2 * b.colorVec col x true i * Real.cos θ * hsin2
  have hWe₂ : W *ᵥ b.planeBasis₂ col θ x =
      Real.sin (2 * θ) • b.planeBasis₁ col θ x + Real.cos (2 * θ) • b.planeBasis₂ col θ x :=
    funext fun i ↦ by
      simp only [planeBasis₁, planeBasis₂, mulVec_smul, hWt, hμ_eq, Real.cos_two_mul,
        Real.sin_two_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hWinvW : Winv * W = 1 := by
    rw [← Matrix.map_mul, bipartiteCoxeterMatrix_def, mul_assoc (b.colorClassMatrix col false),
      ← mul_assoc (b.colorClassMatrix col true), colorClassMatrix_mul_self, one_mul,
      colorClassMatrix_mul_self, Matrix.map_one _ (map_zero _) (map_one _)]
  have hW_pt (ψ : ℝ) : W *ᵥ b.planePoint col θ x ψ = b.planePoint col θ x (ψ - 2 * θ) :=
    funext fun i ↦ by
      simp only [planePoint, mulVec_add, mulVec_smul, hWe₁, hWe₂, Real.cos_sub, Real.sin_sub,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hWinv_pt (ψ : ℝ) : Winv *ᵥ b.planePoint col θ x ψ = b.planePoint col θ x (ψ + 2 * θ) := by
    simpa [mulVec_mulVec, hWinvW] using (congrArg (Winv *ᵥ ·) (hW_pt (ψ + 2 * θ))).symm
  refine ⟨hWe₁, hWe₂, fun k φ ↦ ?_⟩
  induction k generalizing φ with
  | zero => simp [planePoint]
  | succ k ih => rw [pow_succ', ← mulVec_mulVec, ih, hWinv_pt]; congr 1; push_cast; ring

private theorem coxeterPlane_corootEval (k : b.support) (φ : ℝ) :
    b.corootEval ℝ (k : ι) (b.planePoint col θ x φ) =
      2 * Real.sin θ * x k * if col k = true then Real.sin φ else Real.sin (θ - φ) := by
  have hsin2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith [Real.cos_sq_add_sin_sq θ]
  have ht := b.corootEval_ite_color col hxC true k
  have hf := b.corootEval_ite_color col hxC false k
  have hκ2 : κ - 2 = -(2 * Real.cos θ) := by linarith
  cases hck : col k <;>
    simp only [hck, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at ht hf ⊢ <;>
    unfold planePoint planeBasis₁ planeBasis₂ colorVec <;>
    simp only [map_add, map_smul, smul_eq_mul, ht, hf, hκ2]
  · rw [Real.sin_sub]; linear_combination -2 * x k * Real.cos φ * hsin2
  · ring

private theorem coxeterPlane_corootEval_pos (hx : ∀ i, 0 < x i) (hθlt : θ < Real.pi / 2)
    (hsinθ : 0 < Real.sin θ) {φ : ℝ} (hφ0 : 0 < φ) (hφθ : φ < θ) (k : b.support) :
    0 < b.corootEval ℝ (k : ι) (b.planePoint col θ x φ) := by
  rw [coxeterPlane_corootEval b col hxC hμ_eq k φ]
  refine mul_pos (mul_pos (mul_pos two_pos hsinθ) (hx k)) ?_
  split_ifs <;> exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

variable [P.IsReduced]

private theorem coxeterPlane_exists_corootEval_zero [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected) (n : ℕ) (q : ℤ) :
    ∃ j : ι, b.corootEval ℝ j (b.planePoint col θ x (2 * (n : ℝ) * θ + (q : ℝ) * Real.pi)) = 0 := by
  classical
  set c := (weylCoxeterSystem P b).bipartiteCoxeterElement col
  obtain ⟨i₁, hi₁⟩ := exists_mem_colorClass b col hconn true
  have heq := b.corootEval_weylGroupToPerm_inv ((b.actsBy_bipartiteCoxeterElement_inv col).pow n) ℝ
    (P.weylGroupToPerm (c ^ n)⁻¹ (i₁ : ι)) (b.planePoint col θ x 0)
  rw [inv_pow, inv_inv, map_inv, Equiv.Perm.coe_inv, Equiv.apply_symm_apply, Matrix.map_pow] at heq
  refine ⟨(P.weylGroupToPerm (c ^ n)).symm (i₁ : ι), ?_⟩
  have hpt : b.planePoint col θ x (2 * (n : ℝ) * θ + (q : ℝ) * Real.pi) = ((-1 : ℝ) ^ q) •
      ((((b.colorClassMatrix col false * b.colorClassMatrix col true).map (Int.castRingHom ℝ)) ^
        n) *ᵥ b.planePoint col θ x 0) := by
    rw [(coxeterPlane_rotation b col hxC hμ_eq).2.2 n 0]; ext i
    simp [planePoint, Real.cos_add_int_mul_pi, Real.sin_add_int_mul_pi]; ring
  rw [hpt, map_smul, ← heq, coxeterPlane_corootEval b col hxC hμ_eq i₁ 0]; simp [hi₁]

private theorem coxeterPlane_angle_eq_pi_div_orderOf [Nontrivial b.support]
    (hconn : (diagramGraph b.cartanMatrix).Preconnected) (hx : ∀ i, 0 < x i) (hθpos : 0 < θ)
    (hθlt : θ < Real.pi / 2) (hsinθ : 0 < Real.sin θ) :
    θ = Real.pi / (orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement col) : ℝ) := by
  have := P.finite_weylGroup_of_base b; classical
  obtain ⟨-, -, hWinv_pow⟩ := coxeterPlane_rotation b col hxC hμ_eq
  let c := (weylCoxeterSystem P b).bipartiteCoxeterElement col; let h := orderOf c
  have hWinv_h : ((b.colorClassMatrix col false * b.colorClassMatrix col true).map
      (Int.castRingHom ℝ)) ^ h = 1 := by
    have h1 := (by simpa [h, c, pow_orderOf_eq_one] using
      (b.actsBy_bipartiteCoxeterElement_inv col).pow h : b.ActsBy 1 _).unique b.actsBy_one
    rw [← Matrix.map_pow, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcos : Real.cos (2 * (h : ℝ) * θ) = 1 :=
    cos_eq_one_of_planePoint_eq_zero b col hconn hx hsinθ <| by
      have hrot := hWinv_pow h 0; rw [hWinv_h, one_mulVec, zero_add] at hrot; exact hrot.symm
  refine Real.eq_pi_div_of_cos_two_mul_eq_one (orderOf_pos c) hθpos hcos
    (fun h' hh'0 hh'lt hcos' ↦ ?_) fun n q ⟨h0, hlt⟩ ↦
      let ⟨j, hj⟩ := coxeterPlane_exists_corootEval_zero b col hxC hμ_eq hconn n q
      b.corootEval_ne_zero_of_forall_pos
        (coxeterPlane_corootEval_pos b col hxC hμ_eq hx hθlt hsinθ h0 hlt) j hj
  obtain ⟨m', hm'⟩ := (Real.cos_eq_one_iff (2 * (h' : ℝ) * θ)).mp hcos'
  have hang : θ / 2 + 2 * (h' : ℝ) * θ = θ / 2 + m' * (2 * Real.pi) := by linarith
  exact Nat.not_dvd_of_pos_of_lt hh'0 hh'lt <| orderOf_dvd_iff_pow_eq_one.mpr <| inv_eq_one.mp <|
    inv_pow c h' ▸ eq_one_of_actsBy_fix_of_forall_pos b
      (coxeterPlane_corootEval_pos b col hxC hμ_eq hx hθlt hsinθ (φ := θ / 2) (by linarith)
        (by linarith)) ((b.actsBy_bipartiteCoxeterElement_inv col).pow h') (by
        rw [Matrix.map_pow, hWinv_pow h' (θ / 2), hang]
        simp [planePoint, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi])

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
    (Matrix.isIndecomposable_iff_reflTransGen b.cartanMatrix).2 fun i j ↦ let ⟨w⟩ := hconn i j
      w.recOn .refl fun {_ _ _} hadj _ ih ↦ .head (diagramGraph_adj.mp hadj).2.1 ih
  set θ : ℝ := Real.arccos ((2 - κ) / 2)
  have hθlt : θ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr (by linarith)
  have hμ_eq : 2 - κ = 2 * Real.cos θ := by rw [Real.cos_arccos (by linarith) (by linarith)]; ring
  have hsinθ : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr (by linarith)) (by linarith [Real.pi_pos])
  obtain ⟨hWe₁, hWe₂, hWinv_pow⟩ := coxeterPlane_rotation b col hxC hμ_eq
  have hθ_eq := coxeterPlane_angle_eq_pi_div_orderOf b col hxC hμ_eq hconn hx
    (Real.arccos_pos.mpr (by linarith)) hθlt hsinθ
  have hWinv_rw (k : ℕ) (φ : ℝ) : φ + 2 * (k : ℝ) * θ = φ + 2 * Real.pi * k / h := by
    rw [hθ_eq]; ring
  refine ⟨b.planeBasis₁ col θ x, b.planeBasis₂ col θ x,
    coxeterPlane_linearIndependent b col hconn hx hsinθ, by rw [hWe₁, hθ_eq, mul_div_assoc],
    by rw [hWe₂, hθ_eq, mul_div_assoc],
    fun k φ ↦ by simpa only [planePoint, Winv, hWinv_rw k φ] using hWinv_pow k φ,
    fun φ hφ0 hφh ↦ coxeterPlane_corootEval_pos b col hxC hμ_eq hx hθlt hsinθ hφ0
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
        ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) (Real.cos φ • e₁ + Real.sin φ • e₂)) :=
  (exists_pair_ne b.support).elim fun i₀ _ ↦
    have : Nonempty ι := ⟨i₀.val⟩; have : NeZero (2 : R) := ⟨by norm_num⟩
    b.exists_coxeterPlane_bipartiteCoxeterElement_of_isFiniteType
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
  obtain ⟨i₀⟩ := b.support_nonempty.to_subtype; classical
  have hW_eq : W = -1 := (hW.unique (by
    simpa [hnd.eq_singleton_of_mem (hall i₀)] using b.actsBy_ofIdx i₀)).trans <|
    Matrix.ext fun k j ↦ by simp [Subsingleton.elim k i₀, Subsingleton.elim j i₀, reflMatrix_apply]
  have hord : orderOf (wordProd P b l) = 2 := hW.orderOf_eq.trans <| hW_eq ▸
    orderOf_eq_prime (by simp) fun h1 ↦ by simpa using congrFun (congrFun h1 i₀) i₀
  have hv_re (k : b.support) : 0 < b.corootEval ℝ (k : ι) (fun _ ↦ (1 : ℝ)) := by
    rw [Subsingleton.elim k i₀, corootEval_coe_support, Fintype.sum_subsingleton _ i₀,
      b.cartanMatrix_apply_same i₀]; norm_num
  have harg : (2 : ℂ) * Real.pi * Complex.I / (2 : ℕ) = Real.pi * Complex.I := by
    push_cast; ring
  refine ⟨fun _ ↦ ((1 : ℝ) : ℂ), fun h ↦ by simpa using congrFun h i₀, by
      rw [hW_eq, hord, harg, Complex.exp_pi_mul_I]; simp [Matrix.map_neg, neg_mulVec, one_mulVec],
    fun j hj ↦ b.corootEval_ne_zero_of_forall_pos hv_re j
      (by simpa [corootEval_apply] using congrArg Complex.re hj),
    fun g G hG hGv ↦ eq_one_of_actsBy_fix_of_forall_pos b hv_re hG <| funext fun i ↦
      Complex.ofReal_injective (congrFun (map_intCast_mulVec_ofReal G _ ▸ hGv) i)⟩

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
  have hy₀ := hsector ((Real.pi / orderOf c₀) / 2) (by positivity) (half_lt_self (by positivity))
  have harg : (2 : ℂ) * ↑Real.pi * Complex.I / orderOf c₀ =
      ↑(2 * Real.pi / (orderOf c₀ : ℝ)) * Complex.I := by push_cast; ring
  refine ⟨(fun i ↦ (e₁ i : ℂ)) + Complex.I • (fun i ↦ (e₂ i : ℂ)), fun hv0 ↦
      hli.ne_zero (0 : Fin 2) (funext fun i ↦ by simpa using congrArg Complex.re (congrFun hv0 i)),
    by rw [map_intCast_complex_eq_map_ofReal, harg]
       exact map_ofReal_mulVec_of_rotation hWe₁ hWe₂,
    fun j hj0 ↦
      have hre : b.corootEval ℝ j e₁ = 0 := by
        simpa [corootEval_apply] using congrArg Complex.re hj0
      have him : b.corootEval ℝ j e₂ = 0 := by
        simpa [corootEval_apply] using congrArg Complex.im hj0
      b.corootEval_ne_zero_of_forall_pos hy₀ j (by simp [hre, him]),
    fun g G hG hGv ↦ eq_one_of_actsBy_fix_of_forall_pos b hy₀ hG <| funext fun i ↦ by
      rw [mulVec_add, mulVec_smul, map_intCast_mulVec_ofReal, map_intCast_mulVec_ofReal] at hGv
      have hre : ((G.map (Int.castRingHom ℝ)) *ᵥ e₁) i = e₁ i := by
        simpa using congrArg Complex.re (congrFun hGv i)
      have him : ((G.map (Int.castRingHom ℝ)) *ᵥ e₂) i = e₂ i := by
        simpa using congrArg Complex.im (congrFun hGv i)
      simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hre, him]⟩

private theorem exists_eigenvector_of_isConj (b : P.Base)
    {c c₀ : P.weylGroup} {W W₀ : Matrix b.support b.support ℤ}
    (hW : b.ActsBy c W) (hW₀ : b.ActsBy c₀ W₀) (hconj : IsConj c c₀)
    {v₀ : b.support → ℂ} (hv₀ : b.IsCoxeterEigenvector c₀ W₀ v₀) :
    ∃ v : b.support → ℂ, b.IsCoxeterEigenvector c W v := by
  obtain ⟨hv₀_ne, hW₀_eigen, hv₀_reg, hv₀_stab⟩ := hv₀; classical
  obtain ⟨u, hu⟩ := isConj_iff.mp hconj.symm; obtain ⟨lu, rfl⟩ := exists_wordProd_eq P b u
  obtain ⟨lu', hlu'⟩ := exists_wordProd_eq P b (wordProd P b lu)⁻¹
  set U := (lu.map (reflMatrix b.cartanMatrix)).prod
  have hU : b.ActsBy (wordProd P b lu) U := b.actsBy_wordProd lu
  set Uinv := (lu'.map (reflMatrix b.cartanMatrix)).prod
  have hUinv : b.ActsBy (wordProd P b lu)⁻¹ Uinv := hlu' ▸ b.actsBy_wordProd lu'
  have hActsOne : b.ActsBy 1 (Uinv * U) := inv_mul_cancel (wordProd P b lu) ▸ hUinv.mul hU
  have hUinvU (x : b.support → ℂ) :
      (Uinv.map (Int.castRingHom ℂ)) *ᵥ ((U.map (Int.castRingHom ℂ)) *ᵥ x) = x := by
    rw [mulVec_mulVec, ← Matrix.map_mul, hActsOne.unique b.actsBy_one]; simp
  refine ⟨(U.map (Int.castRingHom ℂ)) *ᵥ v₀, fun hv0 ↦ hv₀_ne (by
      simpa only [hUinvU, mulVec_zero] using congrArg ((Uinv.map (Int.castRingHom ℂ)) *ᵥ ·) hv0),
    by rw [hW.unique (hu ▸ (hU.mul hW₀).mul hUinv), hconj.choose_spec.orderOf_eq]
       simp only [Matrix.map_mul, ← mulVec_mulVec, hUinvU, hW₀_eigen, mulVec_smul],
    fun j ↦ b.corootEval_weylGroupToPerm_inv hU ℂ j v₀ ▸ hv₀_reg _, fun g G hG hGv ↦ by
      simpa [mul_assoc] using congrArg (wordProd P b lu * · * (wordProd P b lu)⁻¹) <|
        hv₀_stab ((wordProd P b lu)⁻¹ * g * wordProd P b lu) (Uinv * G * U)
          ((hUinv.mul hG).mul hU) (by simp only [Matrix.map_mul, ← mulVec_mulVec, hGv, hUinvU])⟩

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
  obtain ⟨v, hv⟩ : ∃ v, b.IsCoxeterEigenvector c W v :=
    (subsingleton_or_nontrivial b.support).elim
      (fun _ ↦ exists_eigenvector_subsingleton b hnd hall hW) fun _ ↦
        let ⟨col⟩ := nonempty_coloring_graph_coxeterMatrixOfBase_of_isFiniteType P b hft
        let ⟨_, hv₀⟩ := b.exists_eigenvector_bipartite_of_isFiniteType hft hconn col
        b.exists_eigenvector_of_isConj hW (b.actsBy_bipartiteCoxeterElement col)
          (by rw [hc, ← weylCoxeterSystem_wordProd]
              exact (weylCoxeterSystem P b).isConj_wordProd_bipartiteCoxeterElement
                (isAcyclic_graph_coxeterMatrixOfBase_of_isFiniteType P b hft) col hnd hall) hv₀
  exact ⟨v, hv.1, hv.2.1, Complex.isPrimitiveRoot_exp _ (orderOf_pos c).ne', hv.2.2.1, hv.2.2.2⟩

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
        b.ActsBy g G → (G.map (Int.castRingHom ℂ)) *ᵥ v = v → g = 1) :=
  have : NeZero (2 : R) := ⟨by norm_num⟩
  b.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall hW

end RegularEigenvector

end RootPairing.Base

end
