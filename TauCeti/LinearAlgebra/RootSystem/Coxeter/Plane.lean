/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.RootSystem.Irreducible
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import TauCeti.LinearAlgebra.RootSystem.BaseChange.Rational
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Conj
import TauCeti.LinearAlgebra.RootSystem.Coxeter.FixedPoints
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Basic
import TauCeti.LinearAlgebra.RootSystem.Weyl.Chamber
import TauCeti.LinearAlgebra.RootSystem.Weyl.Transport

/-!
# The Coxeter plane and regular eigenvectors of Coxeter elements

Let `P` be a finite irreducible reduced crystallographic root system over `ℝ` with base `b`, and
let `col` be a two-colouring of its Dynkin diagram
(`RootPairing.nonempty_coloring_graph_coxeterMatrixOfBase`). Let `c₁` and `c₂` be the
products of the simple reflections of each colour, so that `c₁` and `c₂` are involutions and
`c = c₁ c₂` is a bipartite Coxeter element of order `h = orderOf c`.

Normalizing each simple root `αᵢ` to a unit vector `uᵢ` with respect to the positive-definite
canonical bilinear form `P.RootForm`, the off-diagonal inner products satisfy
`2 P.RootForm uᵢ uⱼ = -Aᵢⱼ`, where `Aᵢⱼ = √(Cᵢⱼ Cⱼᵢ)` is the symmetric nonnegative weighted
adjacency matrix of the Dynkin diagram. For rank at least two, `A` is irreducible and
Perron–Frobenius (`Matrix.IsIrreducible.exists_mulVec_eq_smul`) supplies a strictly positive
eigenvector `a` with eigenvalue `λ > 0`; in rank one `A = 0` and `λ = 0`, `a = 1`. Splitting
`∑ aᵢ uᵢ = v₁ + v₂` by colour yields the **Steinberg–Coleman Coxeter plane**
`ℝ v₁ + ℝ v₂`:

* `v₁ + v₂ ∈ openDominantChamber P b`, whence `0 ≤ λ < 2`;
* `c₁ v₁ = -v₁`, `c₁ v₂ = v₂ + λ v₁`, `c₂ v₂ = -v₂`, and `c₂ v₁ = v₁ + λ v₂`.

Writing `λ = 2 cos θ` with `θ ∈ (0, π / 2]` and `μ = exp (θ I)`, the complex vector
`v = v₁ + μ v₂` is a regular eigenvector of `c` for `ζ⁻¹ = exp (-2 θ I)`. Freeness of the
Weyl-group action on the open dominant chamber shows that `ζ` is a primitive `h`-th root of unity;
cyclotomic conjugacy of the rational characteristic polynomial of `c` makes `exp (2 π I / h)` an
eigenvalue of `c`, and the Perron–Frobenius spectral bound (`Matrix.norm_le_of_mulVec_le_smul`)
applied to `A²` forces `cos (π / h) ≤ cos θ`, giving `θ = π / h` and `λ = 2 cos (π / h)`.

Extending scalars from the real coordinate model of `b.rationalModel` to `ℂ`, transporting along
`b.equivBaseChangeRationalModel`, and conjugating by `RootPairing.isConj_wordProd_of_perm` yields
a regular eigenvector of eigenvalue `exp (2 π I / orderOf c)⁻¹` for *every* Coxeter element of
*any* finite irreducible reduced crystallographic root system over `ℂ`.

## Main results

* `RootPairing.two_le_orderOf_wordProd`: every Coxeter element of a nontrivial finite root system
  has order at least `2`.
* `RootPairing.exists_coxeterPlane_bipartite`: over `ℝ`, constructs Steinberg–Coleman vectors
  `v₁, v₂` for a bipartite Coxeter element with `v₁ + v₂ ∈ openDominantChamber P b` and
  dihedral parameter `2 cos (π / orderOf (c₁ * c₂))`.
* `RootPairing.exists_isRegularWeight_smul_eq_exp_neg_wordProd`: over `ℂ`, every Coxeter element
  `wordProd P b l` of an irreducible finite reduced crystallographic root system admits a regular
  eigenvector with eigenvalue `exp (2 π I / orderOf (wordProd P b l))⁻¹`.

## References

* A. J. Coleman, *The Betti numbers of the simple Lie groups*, Canad. J. Math. **10** (1958),
  349–356.
* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.17–3.19.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2.
-/

public section

open Matrix Polynomial TauCeti

namespace RootPairing

section OrderLowerBound

variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsRootSystem]

/-- Every Coxeter element of a nontrivial finite root system has order at least `2`. -/
theorem two_le_orderOf_wordProd [Nontrivial M] (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    2 ≤ orderOf (wordProd P b l) := by
  have : Finite P.weylGroup := P.finite_weylGroup
  have hpos : 0 < orderOf (wordProd P b l) :=
    orderOf_pos_iff.2 (isOfFinOrder_of_finite _)
  have hne : orderOf (wordProd P b l) ≠ 1 := by
    intro h1
    have hcw : wordProd P b l = 1 := orderOf_eq_one_iff.1 h1
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    have hfix : wordProd P b l • x = x := by rw [hcw, one_smul]
    exact hx ((wordProd_smul_eq_self_iff_eq_zero b hl hall).1 hfix)
  omega

end OrderLowerBound

section SpectralHelpers

/-- Pure matrix step in Steinberg's eigenvalue bound: if `M₁C, M₂C` act on `ℂ`-vectors via a
bipartite adjacency matrix `AC = A.map Complex.ofReal` with `M₁C ^ 2 = 1`, then any complex
eigenvector `z` of `M₁C * M₂C` for `ω ≠ 0` is an eigenvector of `(A ^ 2).map Complex.ofReal`
for `(1 + ω) ^ 2 / ω`, so the Perron eigenvalue `lam` of `A` bounds
`‖(1 + ω) ^ 2 / ω‖ ≤ lam ^ 2`. -/
private lemma spectral_bound_of_bipartite_eigenvector {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix κ κ ℝ} {M₁C M₂C : Matrix κ κ ℂ} {col : κ → Bool} {a : κ → ℝ}
    {lam : ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hA_same : ∀ i j, col i = col j → A i j = 0)
    (ha_pos : ∀ i, 0 < a i) (ha_eig : A *ᵥ a = lam • a)
    (hM₁C_sq : M₁C * M₁C = 1)
    (hM₁C_mul : ∀ (z : κ → ℂ) (i : κ), (M₁C *ᵥ z) i =
      if col i = true then
        -z i + ∑ j : κ, (if col j = false then (A i j : ℂ) * z j else 0)
      else z i)
    (hM₂C_mul : ∀ (z : κ → ℂ) (i : κ), (M₂C *ᵥ z) i =
      if col i = false then
        -z i + ∑ j : κ, (if col j = true then (A i j : ℂ) * z j else 0)
      else z i)
    {ω : ℂ} {z : κ → ℂ} (hω : ω ≠ 0) (hz : z ≠ 0)
    (heig : (M₁C * M₂C) *ᵥ z = ω • z) :
    ‖(1 + ω) ^ 2 / ω‖ ≤ lam ^ 2 := by
  set AC : Matrix κ κ ℂ := A.map Complex.ofReal
  have hM₂_eq : M₂C *ᵥ z = ω • (M₁C *ᵥ z) := by
    have h1 := congrArg (M₁C *ᵥ ·) heig
    rw [mulVec_mulVec, ← Matrix.mul_assoc, hM₁C_sq, Matrix.one_mul, mulVec_smul] at h1
    exact h1
  set z₁ : κ → ℂ := fun i ↦ if col i = true then z i else 0
  set z₂ : κ → ℂ := fun i ↦ if col i = false then z i else 0
  have hz_split : z = z₁ + z₂ := by
    ext i; simp only [z₁, z₂, Pi.add_apply]; cases col i <;> simp
  have hAz_color (b0 : Bool) (i : κ) :
      (AC *ᵥ fun j ↦ if col j = b0 then z j else 0) i =
        if col i = !b0 then
          ∑ j : κ, (if col j = b0 then (A i j : ℂ) * z j else 0)
        else 0 := by
    simp only [mulVec, dotProduct, AC, Matrix.map_apply]
    by_cases hci : col i = !b0
    · rw [ite_eq_left hci]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      split_ifs <;> simp
    · rw [ite_eq_right hci]
      have hsame : col i = b0 := by cases h1 : col i <;> cases b0 <;> simp_all
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      split_ifs with hcj
      · simp [hA_same i j (hsame.trans hcj.symm)]
      · simp
  have heq₁ : (1 + ω) • z₁ = ω • (AC *ᵥ z₂) := by
    ext i
    have hi := congrFun hM₂_eq i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    rw [hM₂C_mul, hM₁C_mul] at hi
    have hAz₂ := hAz_color false i
    simp only [Bool.not_false] at hAz₂
    simp only [Pi.smul_apply, smul_eq_mul, z₁, z₂] at hi hAz₂ ⊢
    rw [hAz₂]
    by_cases hci : col i = true
    · have hcf : col i ≠ false := by simp [hci]
      rw [ite_eq_right hcf, ite_eq_left hci] at hi
      rw [ite_eq_left hci, ite_eq_left hci]
      linear_combination hi
    · rw [ite_eq_right hci, ite_eq_right hci, mul_zero, mul_zero]
  have heq₂ : AC *ᵥ z₁ = (1 + ω) • z₂ := by
    ext i
    have hi := congrFun hM₂_eq i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    rw [hM₂C_mul, hM₁C_mul] at hi
    have hAz₁ := hAz_color true i
    simp only [Bool.not_true] at hAz₁
    simp only [Pi.smul_apply, smul_eq_mul, z₁, z₂] at hi hAz₁ ⊢
    rw [hAz₁]
    by_cases hci : col i = false
    · have hct : col i ≠ true := by simp [hci]
      rw [ite_eq_left hci, ite_eq_right hct] at hi
      rw [ite_eq_left hci, ite_eq_left hci]
      linear_combination hi
    · rw [ite_eq_right hci, ite_eq_right hci, mul_zero]
  have hA2_eig : (A ^ 2).map Complex.ofReal *ᵥ z = ((1 + ω) ^ 2 / ω) • z := by
    have hA2_map : (A ^ 2).map Complex.ofReal = AC * AC := by
      ext i j; simp [AC, sq, Matrix.mul_apply]
    have h1 : ω • (AC *ᵥ (AC *ᵥ z₁)) = (1 + ω) ^ 2 • z₁ := by
      rw [heq₂, mulVec_smul, smul_comm, ← heq₁, smul_smul, sq]
    have h2 : ω • (AC *ᵥ (AC *ᵥ z₂)) = (1 + ω) ^ 2 • z₂ := by
      have := congrArg (AC *ᵥ ·) heq₁
      rw [mulVec_smul, mulVec_smul, heq₂, smul_smul, ← sq] at this
      exact this.symm
    have hsum : ω • ((AC * AC) *ᵥ z) = (1 + ω) ^ 2 • z := by
      rw [hz_split, mulVec_add, ← mulVec_mulVec, ← mulVec_mulVec, smul_add, h1, h2,
        ← smul_add]
    rw [hA2_map]
    ext i
    have hi := congrFun hsum i
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    apply mul_left_cancel₀ hω
    calc ω * ((AC * AC) *ᵥ z) i = (1 + ω) ^ 2 * z i := hi
      _ = ω * ((1 + ω) ^ 2 / ω * z i) := by field_simp [hω]
  have hA2_nonneg : ∀ i j, 0 ≤ (A ^ 2) i j := fun i j ↦ by
    rw [sq, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hA_nonneg i k) (hA_nonneg k j)
  have hA2_a : (A ^ 2) *ᵥ a = (lam ^ 2) • a := by
    rw [sq, ← mulVec_mulVec, ha_eig, mulVec_smul, ha_eig, smul_smul, sq]
  exact Matrix.norm_le_of_mulVec_le_smul hA2_nonneg ha_pos hA2_a.le hz hA2_eig

/-- Trigonometric identification of `lam = 2 cos (π / h)`: if `0 ≤ lam < 2`, `h ≥ 2`,
`exp (2 arccos (lam / 2) I)` is a primitive `h`-th root of unity, and
`‖(1 + exp (2 π I / h)) ^ 2 / exp (2 π I / h)‖ ≤ lam ^ 2`, then `lam = 2 cos (π / h)`. -/
private lemma eq_two_mul_cos_pi_div_of_spectral_bound {lam : ℝ} {h : ℕ}
    (hlam_nonneg : 0 ≤ lam) (hlam_lt : lam < 2) (h2le : 2 ≤ h)
    (hζ_pow : (Complex.exp ((Real.arccos (lam / 2) : ℂ) * Complex.I) ^ 2) ^ h = 1)
    (hbound : ‖(1 + Complex.exp (2 * Real.pi * Complex.I / h)) ^ 2 /
      Complex.exp (2 * Real.pi * Complex.I / h)‖ ≤ lam ^ 2) :
    lam = 2 * Real.cos (Real.pi / h) := by
  set θ : ℝ := Real.arccos (lam / 2)
  have hcosθ : Real.cos θ = lam / 2 := Real.cos_arccos (by linarith) (by linarith)
  have hθ_pos : 0 < θ := by
    have hlt : Real.arccos (1 : ℝ) < θ :=
      Real.arccos_lt_arccos (by linarith) (by linarith) (by norm_num)
    simpa [Real.arccos_one] using hlt
  have hθ_le : θ ≤ Real.pi / 2 := by
    have hle : θ ≤ Real.arccos (0 : ℝ) := Real.arccos_le_arccos (by linarith)
    simpa [Real.arccos_zero] using hle
  set ω₀ : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hval_ω₀ : (1 + ω₀) ^ 2 / ω₀ = (((2 * Real.cos (Real.pi / h)) ^ 2 : ℝ) : ℂ) := by
    set ξ : ℂ := Complex.exp (((Real.pi / h : ℝ) : ℂ) * Complex.I)
    have hξ_ne : ξ ≠ 0 := Complex.exp_ne_zero _
    have hω₀_eq : ω₀ = ξ ^ 2 := by
      simp only [ω₀, ξ, sq, ← Complex.exp_add]; congr 1; push_cast; ring
    have hξ_add : ξ + ξ⁻¹ = ((2 * Real.cos (Real.pi / h) : ℝ) : ℂ) := by
      have hinv : ξ⁻¹ = Complex.exp ((-(Real.pi / h : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_neg]; congr 1; ring
      rw [hinv]
      simp only [ξ, Complex.exp_mul_I]
      push_cast
      rw [Complex.cos_neg, Complex.sin_neg]
      ring
    rw [hω₀_eq]
    have hfrac : (1 + ξ ^ 2) ^ 2 / ξ ^ 2 = (ξ + ξ⁻¹) ^ 2 := by field_simp [hξ_ne]; ring
    rw [hfrac, hξ_add]
    push_cast
    ring
  rw [hval_ω₀, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at hbound
  have hh_pos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hpi_le_θ : Real.pi / h ≤ θ := by
    have hexp1 : Complex.exp (((2 * (h : ℝ) * θ : ℝ) : ℂ) * Complex.I) = 1 := by
      simp only [← Complex.exp_nat_mul] at hζ_pow
      convert hζ_pow using 2
      push_cast
      ring
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp1
    have hre : 2 * (h : ℝ) * θ = (m : ℝ) * (2 * Real.pi) := by
      have hm' : ((2 * (h : ℝ) * θ : ℝ) : ℂ) = ((m : ℝ) * (2 * Real.pi) : ℝ) := by
        apply mul_right_cancel₀ Complex.I_ne_zero
        simpa [mul_assoc] using hm
      exact Complex.ofReal_injective hm'
    have hm_pos : (0 : ℝ) < (m : ℝ) := by
      have : 0 < 2 * (h : ℝ) * θ := by positivity
      have : 0 < 2 * Real.pi := by positivity
      nlinarith
    have hm_ge : (1 : ℤ) ≤ m := by
      have : (0 : ℤ) < m := by exact_mod_cast hm_pos
      omega
    have hm_ge_real : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge
    have h2pi_le : 2 * Real.pi ≤ 2 * (h : ℝ) * θ := by nlinarith [Real.pi_pos]
    rw [div_le_iff₀ hh_pos]
    linarith
  have hcos_le : Real.cos (Real.pi / h) ≤ Real.cos θ := by
    have hcos_nonneg_pi : 0 ≤ Real.cos (Real.pi / h) := by
      refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
      · linarith [Real.pi_pos, show (0 : ℝ) ≤ Real.pi / h by positivity]
      · have h2 : (2 : ℝ) ≤ h := by exact_mod_cast h2le
        rw [div_le_div_iff₀ hh_pos (by norm_num)]
        nlinarith [Real.pi_pos]
    have hcos_nonneg_θ : 0 ≤ Real.cos θ := by linarith
    have _ : Real.cos (Real.pi / h) ^ 2 ≤ Real.cos θ ^ 2 := by
      have hlam_eq : lam = 2 * Real.cos θ := by linarith
      rw [hlam_eq] at hbound
      nlinarith
    nlinarith
  have hcos_ge : Real.cos θ ≤ Real.cos (Real.pi / h) :=
    Real.strictAntiOn_cos.antitoneOn
      ⟨by positivity, le_trans hpi_le_θ (le_trans hθ_le (by linarith [Real.pi_pos]))⟩
      ⟨hθ_pos.le, le_trans hθ_le (by linarith [Real.pi_pos])⟩ hpi_le_θ
  have _ : Real.cos θ = Real.cos (Real.pi / h) := le_antisymm hcos_ge hcos_le
  linarith

end SpectralHelpers

section RealCoxeterPlane

variable {ι M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  (P : RootPairing ι ℝ M N)

private lemma rootForm_root_pos [Fintype ι] (i : ι) :
    0 < P.RootForm (P.root i) (P.root i) :=
  P.rootForm_pos_of_ne_zero (Submodule.subset_span (Set.mem_range_self i)) (P.ne_zero i)

/-- Unit simple root `uᵢ = ‖αᵢ‖⁻¹ • αᵢ` with respect to `P.RootForm`. -/
private noncomputable def unitSimpleRoot [Fintype ι] (b : P.Base) (i : b.support) : M :=
  (Real.sqrt (P.RootForm (P.root i) (P.root i)))⁻¹ • P.root i

private lemma coroot'_smul_root_eq_unitSimpleRoot [Fintype ι] (b : P.Base) (k : b.support)
    (x : M) :
    P.coroot' k x • P.root k =
      (2 * P.RootForm x (P.unitSimpleRoot b k)) • P.unitSimpleRoot b k := by
  have hk : 0 < P.RootForm (P.root k) (P.root k) := P.rootForm_root_pos k
  set sk := Real.sqrt (P.RootForm (P.root k) (P.root k))
  have hsk2 : sk * sk = P.RootForm (P.root k) (P.root k) := Real.mul_self_sqrt hk.le
  unfold unitSimpleRoot
  rw [map_smul, smul_eq_mul, smul_smul]
  congr 1
  have h2 := P.toInvariantForm.two_mul_apply_root x k
  rw [P.toInvariantForm_form] at h2
  have hsk_ne : sk ≠ 0 := (Real.sqrt_pos.2 hk).ne'
  apply mul_right_cancel₀ hk.ne'
  rw [← h2]
  symm
  calc 2 * (sk⁻¹ * P.RootForm x (P.root k)) * sk⁻¹ * P.RootForm (P.root k) (P.root k)
      = 2 * P.RootForm x (P.root k) * (sk⁻¹ * sk⁻¹ * (sk * sk)) := by rw [← hsk2]; ring
    _ = 2 * P.RootForm x (P.root k) := by field_simp

variable [P.IsCrystallographic]

/-- Weighted symmetric adjacency matrix of the Dynkin diagram: `A i j = √(C i j * C j i)` off the
diagonal and `0` on the diagonal. -/
private noncomputable def weightedAdjMatrix [DecidableEq ι] (b : P.Base) :
    Matrix b.support b.support ℝ :=
  fun i j ↦ if i = j then 0 else Real.sqrt ((b.cartanMatrix i j * b.cartanMatrix j i : ℤ) : ℝ)

private lemma weightedAdjMatrix_nonneg [DecidableEq ι] (b : P.Base) (i j : b.support) :
    0 ≤ P.weightedAdjMatrix b i j := by
  unfold weightedAdjMatrix
  split_ifs
  · exact le_rfl
  · exact Real.sqrt_nonneg _

private lemma weightedAdjMatrix_symm [DecidableEq ι] (b : P.Base) (i j : b.support) :
    P.weightedAdjMatrix b i j = P.weightedAdjMatrix b j i := by
  unfold weightedAdjMatrix
  by_cases h : i = j
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), mul_comm]

private lemma coroot'_eq_zero_of_not_adj (b : P.Base) {i j : b.support}
    (hij : i ≠ j) (hnadj : ¬ (diagramGraph b.cartanMatrix).Adj i j) :
    P.coroot' j (P.root i) = 0 := by
  rw [diagramGraph_adj] at hnadj
  have hzero : b.cartanMatrix i j = 0 ∨ b.cartanMatrix j i = 0 := by
    by_contra h
    push Not at h
    exact hnadj ⟨hij, h.1, h.2⟩
  rw [P.root_coroot'_eq_pairing]
  rcases hzero with h | h
  · rw [← P.algebraMap_pairingIn ℤ]
    change algebraMap ℤ ℝ (b.cartanMatrix i j) = 0
    rw [h, map_zero]
  · rw [P.pairing_eq_zero_iff, ← P.algebraMap_pairingIn ℤ]
    change algebraMap ℤ ℝ (b.cartanMatrix j i) = 0
    rw [h, map_zero]

variable [Finite ι]

private lemma weightedAdjMatrix_pos_iff [DecidableEq ι] (b : P.Base) (i j : b.support) :
    0 < P.weightedAdjMatrix b i j ↔ (diagramGraph b.cartanMatrix).Adj i j := by
  unfold weightedAdjMatrix
  rw [diagramGraph_adj]
  by_cases hij : i = j
  · subst hij; simp
  · rw [ite_eq_right hij, Real.sqrt_pos, Int.cast_pos]
    have h1 : b.cartanMatrix i j ≤ 0 := b.cartanMatrix_le_zero_of_ne i j hij
    have h2 : b.cartanMatrix j i ≤ 0 := b.cartanMatrix_le_zero_of_ne j i (Ne.symm hij)
    constructor
    · intro hpos
      refine ⟨hij, ?_, ?_⟩
      · intro h0; simp [h0] at hpos
      · intro h0; simp [h0] at hpos
    · rintro ⟨-, h1', h2'⟩
      exact mul_pos_of_neg_of_neg (lt_of_le_of_ne h1 h1') (lt_of_le_of_ne h2 h2')

private lemma two_mul_rootForm_unitSimpleRoot [DecidableEq ι] [Fintype ι] (b : P.Base)
    (i j : b.support) :
    2 * P.RootForm (P.unitSimpleRoot b i) (P.unitSimpleRoot b j) =
      if i = j then 2 else -P.weightedAdjMatrix b i j := by
  have hi : 0 < P.RootForm (P.root i) (P.root i) := P.rootForm_root_pos i
  have hj : 0 < P.RootForm (P.root j) (P.root j) := P.rootForm_root_pos j
  set si := Real.sqrt (P.RootForm (P.root i) (P.root i))
  set sj := Real.sqrt (P.RootForm (P.root j) (P.root j))
  have hsi : 0 < si := Real.sqrt_pos.2 hi
  have hsj : 0 < sj := Real.sqrt_pos.2 hj
  have hsi2 : si * si = P.RootForm (P.root i) (P.root i) := Real.mul_self_sqrt hi.le
  have hsj2 : sj * sj = P.RootForm (P.root j) (P.root j) := Real.mul_self_sqrt hj.le
  unfold unitSimpleRoot weightedAdjMatrix
  rw [LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    have : si⁻¹ * (si⁻¹ * P.RootForm (P.root i) (P.root i)) = 1 := by
      rw [← mul_assoc, ← mul_inv, hsi2, inv_mul_cancel₀ hi.ne']
    linarith
  · rw [ite_eq_right hij, ite_eq_right hij]
    have h1 : 2 * P.RootForm (P.root i) (P.root j) =
        (b.cartanMatrix i j : ℝ) * P.RootForm (P.root j) (P.root j) := by
      have h := P.toInvariantForm.two_mul_apply_root (P.root i) j
      rw [P.toInvariantForm_form, P.root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ] at h
      exact h
    have h2 : 2 * P.RootForm (P.root j) (P.root i) =
        (b.cartanMatrix j i : ℝ) * P.RootForm (P.root i) (P.root i) := by
      have h := P.toInvariantForm.two_mul_apply_root (P.root j) i
      rw [P.toInvariantForm_form, P.root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ] at h
      exact h
    have hsym : P.RootForm (P.root j) (P.root i) = P.RootForm (P.root i) (P.root j) := by
      simpa using P.rootForm_symmetric.eq (P.root j) (P.root i)
    set t : ℝ := 2 * (si⁻¹ * (sj⁻¹ * P.RootForm (P.root i) (P.root j)))
    have ht_nonpos : t ≤ 0 := by
      have hle : (b.cartanMatrix i j : ℝ) ≤ 0 := by
        exact_mod_cast b.cartanMatrix_le_zero_of_ne i j hij
      have hrf : P.RootForm (P.root i) (P.root j) ≤ 0 := by
        have := mul_nonpos_of_nonpos_of_nonneg hle hj.le
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonneg_of_nonpos
          (by positivity) hrf))
    have ht_sq : t ^ 2 = ((b.cartanMatrix i j * b.cartanMatrix j i : ℤ) : ℝ) := by
      have hmul : (2 * P.RootForm (P.root i) (P.root j)) *
          (2 * P.RootForm (P.root j) (P.root i)) =
          ((b.cartanMatrix i j * b.cartanMatrix j i : ℤ) : ℝ) *
            (P.RootForm (P.root i) (P.root i) * P.RootForm (P.root j) (P.root j)) := by
        rw [h1, h2]
        push_cast
        ring
      rw [hsym] at hmul
      have hsi_ne : si ≠ 0 := hsi.ne'
      have hsj_ne : sj ≠ 0 := hsj.ne'
      have hdenom : P.RootForm (P.root i) (P.root i) * P.RootForm (P.root j) (P.root j) =
          si ^ 2 * sj ^ 2 := by
        rw [sq, sq, hsi2, hsj2]
      rw [hdenom] at hmul
      have ht_eq : t ^ 2 * (si ^ 2 * sj ^ 2) =
          (2 * P.RootForm (P.root i) (P.root j)) * (2 * P.RootForm (P.root i) (P.root j)) := by
        simp only [t]
        field_simp
      have hprod_ne : si ^ 2 * sj ^ 2 ≠ 0 := by positivity
      exact mul_right_cancel₀ hprod_ne (ht_eq.trans hmul)
    have : -t = Real.sqrt ((b.cartanMatrix i j * b.cartanMatrix j i : ℤ) : ℝ) := by
      rw [← ht_sq, Real.sqrt_sq_eq_abs, abs_of_nonpos ht_nonpos]
    linarith

omit [P.IsCrystallographic] [Finite ι] in
/-- A product of pairwise orthogonal simple reflections acts as the simultaneous reflection. -/
private lemma wordProd_smul_of_pairwise_orthogonal [DecidableEq ι] [Fintype ι] (b : P.Base)
    {l : List b.support} (hl : l.Nodup)
    (horth : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → P.coroot' j (P.root i) = 0) (x : M) :
    wordProd P b l • x =
      x - ∑ k ∈ l.toFinset,
        (2 * P.RootForm x (P.unitSimpleRoot b k)) • P.unitSimpleRoot b k := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨ha_not, ht_nodup⟩ := hl
    have ht_orth : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → P.coroot' j (P.root i) = 0 :=
      fun i hi j hj hij ↦ horth i (List.mem_cons_of_mem _ hi) j (List.mem_cons_of_mem _ hj) hij
    rw [wordProd_cons, mul_smul, ih ht_nodup ht_orth, weylGroup.ofIdx_smul, Equiv.reflection_smul,
      reflection_apply, map_sub, map_sum]
    have hkill : ∑ k ∈ t.toFinset, P.coroot' a
        ((2 * P.RootForm x (P.unitSimpleRoot b k)) • P.unitSimpleRoot b k) = 0 := by
      refine Finset.sum_eq_zero fun k hk ↦ ?_
      rw [List.mem_toFinset] at hk
      have hka : k ≠ a := fun h ↦ ha_not (h ▸ hk)
      rw [map_smul, smul_eq_mul]
      have hcor0 : P.coroot' a (P.unitSimpleRoot b k) = 0 := by
        unfold unitSimpleRoot
        rw [map_smul, smul_eq_mul,
          horth k (List.mem_cons_of_mem _ hk) a List.mem_cons_self hka, mul_zero]
      rw [hcor0, mul_zero]
    rw [hkill, sub_zero, P.coroot'_smul_root_eq_unitSimpleRoot b a x, List.toFinset_cons,
      Finset.sum_insert (by simpa using ha_not)]
    abel

private lemma wordProd_mul_self_of_pairwise_orthogonal (b : P.Base)
    {l : List b.support} (hl : l.Nodup)
    (horth : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → P.coroot' j (P.root i) = 0) :
    wordProd P b l * wordProd P b l = 1 := by
  classical
  let := Fintype.ofFinite ι
  refine weylGroup.ext fun x ↦ ?_
  rw [mul_smul, one_smul, P.wordProd_smul_of_pairwise_orthogonal b hl horth,
    P.wordProd_smul_of_pairwise_orthogonal b hl horth]
  have hinner : ∀ j ∈ l.toFinset,
      2 * P.RootForm (x - ∑ k ∈ l.toFinset,
        (2 * P.RootForm x (P.unitSimpleRoot b k)) • P.unitSimpleRoot b k) (P.unitSimpleRoot b j) =
        -(2 * P.RootForm x (P.unitSimpleRoot b j)) := by
    intro j hj
    rw [LinearMap.map_sub₂, LinearMap.map_sum₂]
    have hsum : ∑ k ∈ l.toFinset,
        P.RootForm ((2 * P.RootForm x (P.unitSimpleRoot b k)) • P.unitSimpleRoot b k)
          (P.unitSimpleRoot b j) = 2 * P.RootForm x (P.unitSimpleRoot b j) := by
      have hterm : ∀ k ∈ l.toFinset,
          P.RootForm ((2 * P.RootForm x (P.unitSimpleRoot b k)) • P.unitSimpleRoot b k)
            (P.unitSimpleRoot b j) =
            if k = j then 2 * P.RootForm x (P.unitSimpleRoot b j) else 0 := by
        intro k hk
        rw [LinearMap.map_smul₂, smul_eq_mul]
        have h2 := P.two_mul_rootForm_unitSimpleRoot b k j
        by_cases hkj : k = j
        · subst hkj
          rw [ite_eq_left rfl] at h2 ⊢
          have h1 : P.RootForm (P.unitSimpleRoot b k) (P.unitSimpleRoot b k) = 1 := by linarith
          rw [h1, mul_one]
        · rw [ite_eq_right hkj] at h2 ⊢
          have hk0 : P.coroot' j (P.root k) = 0 :=
            horth k (List.mem_toFinset.1 hk) j (List.mem_toFinset.1 hj) hkj
          have hrf0 : P.RootForm (P.root k) (P.root j) = 0 := by
            have := P.toInvariantForm.two_mul_apply_root (P.root k) j
            rw [P.toInvariantForm_form, hk0, zero_mul] at this
            linarith
          have : P.RootForm (P.unitSimpleRoot b k) (P.unitSimpleRoot b j) = 0 := by
            unfold unitSimpleRoot
            rw [LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, hrf0, mul_zero, mul_zero]
          rw [this, mul_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', ite_eq_left hj]
    rw [hsum]
    ring
  have hsum_neg : ∑ j ∈ l.toFinset,
      (2 * P.RootForm (x - ∑ k ∈ l.toFinset,
        (2 * P.RootForm x (P.unitSimpleRoot b k)) • P.unitSimpleRoot b k)
          (P.unitSimpleRoot b j)) • P.unitSimpleRoot b j =
      -∑ j ∈ l.toFinset,
        (2 * P.RootForm x (P.unitSimpleRoot b j)) • P.unitSimpleRoot b j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [hinner j hj, neg_smul]
  rw [hsum_neg, sub_neg_eq_add, sub_add_cancel]

/-- Action of a single colour's simple-reflection product on the unit simple roots. -/
private lemma wordProd_color_smul_unitSimpleRoot [DecidableEq ι] [Fintype ι] (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (b0 : Bool)
    {l : List b.support} (hl : l.Nodup) (hcol : ∀ i : b.support, i ∈ l ↔ col i = b0)
    (j : b.support) :
    wordProd P b l • P.unitSimpleRoot b j =
      if col j = b0 then -P.unitSimpleRoot b j
      else P.unitSimpleRoot b j +
        ∑ k : b.support, (if col k = b0 then P.weightedAdjMatrix b k j else 0) •
          P.unitSimpleRoot b k := by
  have hnot_adj : ∀ {u v : b.support}, col u = col v →
      ¬ (diagramGraph b.cartanMatrix).Adj u v := fun hsame hadj ↦
    col.valid (by rwa [graph_coxeterMatrixOfBase P b]) hsame
  have hA_same : ∀ {u v : b.support}, col u = col v → P.weightedAdjMatrix b u v = 0 :=
    fun {u v} hsame ↦ le_antisymm
      (not_lt.1 (mt (P.weightedAdjMatrix_pos_iff b u v).1 (hnot_adj hsame)))
      (P.weightedAdjMatrix_nonneg b u v)
  have horth : ∀ u ∈ l, ∀ v ∈ l, u ≠ v → P.coroot' v (P.root u) = 0 :=
    fun u hu v hv huv ↦ P.coroot'_eq_zero_of_not_adj b huv
      (hnot_adj (((hcol u).1 hu).trans ((hcol v).1 hv).symm))
  rw [P.wordProd_smul_of_pairwise_orthogonal b hl horth]
  by_cases hcj : col j = b0
  · rw [ite_eq_left hcj]
    have hj_mem : j ∈ l.toFinset := List.mem_toFinset.2 ((hcol j).2 hcj)
    have hterm : ∀ k ∈ l.toFinset,
        (2 * P.RootForm (P.unitSimpleRoot b j) (P.unitSimpleRoot b k)) • P.unitSimpleRoot b k =
          if k = j then (2 : ℝ) • P.unitSimpleRoot b j else 0 := fun k hk ↦ by
      rw [P.two_mul_rootForm_unitSimpleRoot]
      by_cases hjk : k = j
      · subst hjk; simp
      · rw [ite_eq_right (Ne.symm hjk), ite_eq_right hjk]
        have hck : col k = b0 := (hcol k).1 (List.mem_toFinset.1 hk)
        simp [hA_same (hcj.trans hck.symm)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', ite_eq_left hj_mem, two_smul]
    abel
  · rw [ite_eq_right hcj]
    have hsum_eq : ∑ k ∈ l.toFinset,
        (2 * P.RootForm (P.unitSimpleRoot b j) (P.unitSimpleRoot b k)) • P.unitSimpleRoot b k =
        -∑ k : b.support, (if col k = b0 then P.weightedAdjMatrix b k j else 0) •
          P.unitSimpleRoot b k := by
      have hite : ∀ k : b.support,
          -((if col k = b0 then P.weightedAdjMatrix b k j else 0) • P.unitSimpleRoot b k) =
            if col k = b0 then -(P.weightedAdjMatrix b k j • P.unitSimpleRoot b k) else 0 :=
        fun k ↦ by split_ifs <;> simp
      rw [← Finset.sum_neg_distrib]
      simp_rw [hite, ← Finset.sum_filter]
      have hfilt : Finset.univ.filter (fun k : b.support ↦ col k = b0) = l.toFinset := by
        ext k; simp [hcol]
      rw [hfilt]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hck : col k = b0 := (hcol k).1 (List.mem_toFinset.1 hk)
      have hjk : j ≠ k := fun h ↦ hcj (h ▸ hck)
      rw [P.two_mul_rootForm_unitSimpleRoot, ite_eq_right hjk, neg_smul, P.weightedAdjMatrix_symm]
    rw [hsum_eq, sub_neg_eq_add]

/-- Action of a single colour's simple-reflection product on the colour-split Perron vectors and on
complex coordinate vectors in the unit simple-root basis. -/
private lemma wordProd_color_action [DecidableEq ι] [Fintype ι] (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (b0 : Bool)
    {l : List b.support} (hl : l.Nodup) (hcol : ∀ i : b.support, i ∈ l ↔ col i = b0)
    {a : b.support → ℝ} {lam : ℝ} (ha_eig : P.weightedAdjMatrix b *ᵥ a = lam • a)
    (uBasis : Module.Basis b.support ℝ M) (hu : ∀ i, uBasis i = P.unitSimpleRoot b i) :
    let vSame : M := ∑ i : b.support, (if col i = b0 then a i else 0) • P.unitSimpleRoot b i
    let vOpp : M := ∑ i : b.support, (if col i = !b0 then a i else 0) • P.unitSimpleRoot b i
    let MC : Matrix b.support b.support ℂ :=
      (LinearMap.toMatrix uBasis uBasis (P.weylGroupRootRep (wordProd P b l))).map Complex.ofReal
    wordProd P b l • vSame = -vSame ∧
    wordProd P b l • vOpp = vOpp + lam • vSame ∧
    ∀ (z : b.support → ℂ) (i : b.support), (MC *ᵥ z) i =
      if col i = b0 then
        -z i + ∑ j : b.support,
          (if col j = !b0 then (P.weightedAdjMatrix b i j : ℂ) * z j else 0)
      else z i := by
  intro vSame vOpp MC
  set A := P.weightedAdjMatrix b
  set w := wordProd P b l
  have hnot_adj : ∀ {u v : b.support}, col u = col v →
      ¬ (diagramGraph b.cartanMatrix).Adj u v := fun hsame hadj ↦
    col.valid (by rwa [graph_coxeterMatrixOfBase P b]) hsame
  have hA_same : ∀ {u v : b.support}, col u = col v → A u v = 0 :=
    fun {u v} hsame ↦ le_antisymm
      (not_lt.1 (mt (P.weightedAdjMatrix_pos_iff b u v).1 (hnot_adj hsame)))
      (P.weightedAdjMatrix_nonneg b u v)
  have hwu := P.wordProd_color_smul_unitSimpleRoot b col b0 hl hcol
  refine ⟨?_, ?_, ?_⟩
  · simp only [vSame, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    change (P.weylGroupRootRep w) ((if col j = b0 then a j else 0) • P.unitSimpleRoot b j) = _
    rw [map_smul]
    change (if col j = b0 then a j else 0) • (w • P.unitSimpleRoot b j) = _
    by_cases hcj : col j = b0
    · rw [ite_eq_left hcj, hwu j, ite_eq_left hcj, smul_neg]
    · simp [hcj]
  · set aOpp : b.support → ℝ := fun j ↦ if col j = !b0 then a j else 0
    have hAaOpp : A *ᵥ aOpp = lam • fun k ↦ if col k = b0 then a k else 0 := by
      ext k
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, aOpp]
      by_cases hck : col k = b0
      · rw [ite_eq_left hck]
        have hsum : ∑ j : b.support, A k j * (if col j = !b0 then a j else 0) =
            ∑ j : b.support, A k j * a j := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          by_cases hcj : col j = !b0
          · simp [hcj]
          · have hsame : col k = col j := by cases h1 : col j <;> cases b0 <;> simp_all
            simp [hcj, hA_same hsame]
        rw [hsum]
        simpa [mulVec, dotProduct] using congrFun ha_eig k
      · rw [ite_eq_right hck, mul_zero]
        have hcopp : col k = !b0 := by cases h1 : col k <;> cases b0 <;> simp_all
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        split_ifs with hcj
        · simp [hA_same (hcopp.trans hcj.symm)]
        · simp
    have hcalc :
        w • vOpp = vOpp + ∑ k : b.support, ((A *ᵥ aOpp) k) • P.unitSimpleRoot b k := by
      have hstep : w • vOpp = ∑ j : b.support, aOpp j • (P.unitSimpleRoot b j +
          ∑ k : b.support, (if col k = b0 then A k j else 0) • P.unitSimpleRoot b k) := by
        simp only [vOpp, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        change (P.weylGroupRootRep w) (aOpp j • P.unitSimpleRoot b j) = _
        rw [map_smul]
        change aOpp j • (w • P.unitSimpleRoot b j) = _
        by_cases hcj : col j = !b0
        · have hne : col j ≠ b0 := by cases b0 <;> simp_all
          rw [hwu j, ite_eq_right hne]
        · simp [aOpp, hcj]
      rw [hstep]
      simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← Finset.sum_smul]
      congr 1
      simp only [mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases hck : col k = b0
      · rw [ite_eq_left hck, mul_comm]
      · rw [ite_eq_right hck, mul_zero]
        have hcopp : col k = !b0 := by cases h1 : col k <;> cases b0 <;> simp_all
        by_cases hcj : col j = !b0
        · simp [hA_same (hcopp.trans hcj.symm)]
        · simp [aOpp, hcj]
    rw [hcalc, hAaOpp]
    simp [vSame, Finset.smul_sum, smul_smul]
  · intro z i
    have hMC_entry (j : b.support) :
        MC i j = ((if col j = b0 then (if i = j then (-1 : ℝ) else 0)
          else if i = j then 1 else if col i = b0 then A i j else 0) : ℂ) := by
      change ((LinearMap.toMatrix uBasis uBasis (P.weylGroupRootRep w) i j : ℝ) : ℂ) = _
      have hcol_eq : LinearMap.toMatrix uBasis uBasis (P.weylGroupRootRep w) i j =
          uBasis.repr (w • P.unitSimpleRoot b j) i := by
        simp [LinearMap.toMatrix_apply, hu]
        rfl
      rw [hcol_eq, hwu j]
      by_cases hcj : col j = b0
      · rw [ite_eq_left hcj, ite_eq_left hcj, ← hu, map_neg, Finsupp.neg_apply, uBasis.repr_self]
        by_cases hij : i = j
        · subst hij; simp
        · simp [Finsupp.single_eq_of_ne hij, hij]
      · rw [ite_eq_right hcj, ite_eq_right hcj, map_add, map_sum, Finsupp.add_apply,
          Finset.sum_apply', ← hu j, uBasis.repr_self]
        have hsum : ∑ k : b.support,
            uBasis.repr ((if col k = b0 then A k j else 0) • P.unitSimpleRoot b k) i =
            if col i = b0 then A i j else 0 := by
          simp_rw [← hu, map_smul, uBasis.repr_self, Finsupp.smul_apply, smul_eq_mul,
            Finsupp.single_apply]
          simp
        rw [hsum]
        by_cases hij : i = j
        · subst hij; simp [hcj]
        · by_cases hci : col i = b0 <;> simp [Finsupp.single_eq_of_ne hij, hij, hci]
    simp only [mulVec, dotProduct]
    simp_rw [hMC_entry]
    by_cases hci : col i = b0
    · rw [ite_eq_left hci]
      have hterm : ∀ j : b.support,
          ((if col j = b0 then (if i = j then (-1 : ℝ) else 0)
            else if i = j then 1 else if col i = b0 then A i j else 0) : ℂ) * z j =
            (if i = j then -z i else 0) + (if col j = !b0 then (A i j : ℂ) * z j else 0) := by
        intro j
        by_cases hcj : col j = b0
        · have hne : col j ≠ !b0 := by cases b0 <;> simp_all
          rw [ite_eq_left hcj, ite_eq_right hne]
          by_cases hij : i = j
          · subst hij; simp
          · simp [hij]
        · have hopp : col j = !b0 := by cases h1 : col j <;> cases b0 <;> simp_all
          have hij : i ≠ j := fun h ↦ hcj (h ▸ hci)
          simp [hopp, hij, hci]
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ i)]
    · rw [ite_eq_right hci]
      have hterm : ∀ j : b.support,
          ((if col j = b0 then (if i = j then (-1 : ℝ) else 0)
            else if i = j then 1 else if col i = b0 then A i j else 0) : ℂ) * z j =
            if i = j then z i else 0 := by
        intro j
        by_cases hcj : col j = b0
        · have hij : i ≠ j := fun h ↦ hci (h ▸ hcj)
          simp [hcj, hij]
        · by_cases hij : i = j
          · subst hij; simp [hcj]
          · simp [hcj, hij, hci]
      simp_rw [hterm]
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ i)]

variable [P.IsReduced]

/-- Perron–Frobenius vector of the weighted adjacency matrix of an irreducible root system
(including the rank-1 case `λ = 0`, `a = 1`). -/
private lemma exists_perron_weightedAdjMatrix [DecidableEq ι] [P.IsIrreducible] (b : P.Base) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∃ a : b.support → ℝ,
      (∀ i, 0 < a i) ∧ P.weightedAdjMatrix b *ᵥ a = lam • a := by
  rcases subsingleton_or_nontrivial b.support with hsub | hnt
  · refine ⟨0, le_rfl, fun _ ↦ 1, fun _ ↦ zero_lt_one, ?_⟩
    ext i
    have h0 : ∀ j : b.support, P.weightedAdjMatrix b i j = 0 := fun j ↦ by
      rw [Subsingleton.elim j i]; simp [weightedAdjMatrix]
    simp [mulVec, dotProduct, h0]
  · have hirr : (P.weightedAdjMatrix b).IsIrreducible := by
      refine ⟨P.weightedAdjMatrix_nonneg b, fun i j ↦ ?_⟩
      let : Quiver b.support := Matrix.toQuiver (P.weightedAdjMatrix b)
      have walkToPath : ∀ {u v : b.support}, (diagramGraph b.cartanMatrix).Walk u v →
          Nonempty (Quiver.Path u v) := fun w ↦ by
        induction w with
        | nil => exact ⟨Quiver.Path.nil⟩
        | @cons u v w hadj _ ih =>
          obtain ⟨p⟩ := ih
          have hpos : 0 < P.weightedAdjMatrix b u v := (P.weightedAdjMatrix_pos_iff b u v).2 hadj
          exact ⟨(Quiver.Hom.toPath (PLift.up hpos)).comp p⟩
      have reachPos : ∀ {u v : b.support}, u ≠ v →
          ∃ p : Quiver.Path u v, 0 < p.length := fun {u v} huv ↦ by
        obtain ⟨w⟩ := preconnected_diagramGraph_cartanMatrix b u v
        cases w with
        | nil => exact (huv rfl).elim
        | cons hadj w' =>
          have hpos : 0 < P.weightedAdjMatrix b _ _ := (P.weightedAdjMatrix_pos_iff b _ _).2 hadj
          obtain ⟨p'⟩ := walkToPath w'
          exact ⟨(Quiver.Hom.toPath (PLift.up hpos)).comp p', by simp [Quiver.Path.length_comp]⟩
      by_cases hij : i = j
      · subst hij
        obtain ⟨k, hki⟩ := exists_ne i
        obtain ⟨p₁, hp₁⟩ := reachPos hki.symm
        obtain ⟨p₂, hp₂⟩ := reachPos hki
        exact ⟨p₁.comp p₂, by rw [Quiver.Path.length_comp]; omega⟩
      · exact reachPos hij
    obtain ⟨lam, hlam, a, ha, heig⟩ := hirr.exists_mulVec_eq_smul
    exact ⟨lam, hlam.le, a, ha, heig⟩

variable [P.IsRootSystem]

/-- Over `ℝ`, the Steinberg–Coleman Coxeter plane of a bipartite Coxeter element `c₁ * c₂` of
an irreducible finite reduced crystallographic root system: there exist `v₁, v₂ : M` such that
`v₁ + v₂` lies in the open dominant chamber and `c₁, c₂` act on `span {v₁, v₂}` by the
dihedral formulas with parameter `2 cos (π / orderOf (c₁ * c₂))`. -/
theorem exists_coxeterPlane_bipartite [P.IsIrreducible] (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {l₁ l₂ : List b.support} (hl₁ : l₁.Nodup) (hl₂ : l₂.Nodup)
    (hcol₁ : ∀ i : b.support, i ∈ l₁ ↔ col i = true)
    (hcol₂ : ∀ i : b.support, i ∈ l₂ ↔ col i = false) :
    ∃ v₁ v₂ : M,
      v₁ + v₂ ∈ openDominantChamber P b ∧
      wordProd P b l₁ • v₁ = -v₁ ∧
      wordProd P b l₁ • v₂ = v₂ +
        (2 * Real.cos (Real.pi / orderOf (wordProd P b l₁ * wordProd P b l₂))) • v₁ ∧
      wordProd P b l₂ • v₂ = -v₂ ∧
      wordProd P b l₂ • v₁ = v₁ +
        (2 * Real.cos (Real.pi / orderOf (wordProd P b l₁ * wordProd P b l₂))) • v₂ := by
  classical
  let := Fintype.ofFinite ι
  have := IsIrreducible.nontrivial P
  have hne_supp : Nonempty b.support := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact not_subsingleton M b.toWeightBasis.equivFun.subsingleton
  set A := P.weightedAdjMatrix b
  set c₁ := wordProd P b l₁
  set c₂ := wordProd P b l₂
  set c := c₁ * c₂
  have hc_word : c = wordProd P b (l₁ ++ l₂) := (wordProd_append b l₁ l₂).symm
  have hl_nodup : (l₁ ++ l₂).Nodup := by
    rw [List.nodup_append]
    refine ⟨hl₁, hl₂, fun i hi₁ j hi₂ hij ↦ ?_⟩
    subst hij
    have h1 := (hcol₁ i).1 hi₁
    have h2 := (hcol₂ i).1 hi₂
    simp [h1] at h2
  have hl_all : ∀ i : b.support, i ∈ l₁ ++ l₂ := fun i ↦ by
    rw [List.mem_append, hcol₁, hcol₂]
    cases col i <;> simp
  have h2le : 2 ≤ orderOf c := by
    rw [hc_word]
    exact P.two_le_orderOf_wordProd b hl_nodup hl_all
  set h : ℕ := orderOf c
  have hh_pos : 0 < h := by omega
  have hA_same : ∀ i j : b.support, col i = col j → A i j = 0 := fun i j hsame ↦
    le_antisymm
      (not_lt.1 (mt (P.weightedAdjMatrix_pos_iff b i j).1
        (fun hadj ↦ col.valid (by rwa [graph_coxeterMatrixOfBase P b]) hsame)))
      (P.weightedAdjMatrix_nonneg b i j)
  have horth₁ : ∀ i ∈ l₁, ∀ j ∈ l₁, i ≠ j → P.coroot' j (P.root i) = 0 :=
    fun i hi j hj hij ↦ P.coroot'_eq_zero_of_not_adj b hij fun hadj ↦
      col.valid (by rwa [graph_coxeterMatrixOfBase P b])
        (((hcol₁ i).1 hi).trans ((hcol₁ j).1 hj).symm)
  have hc₁_sq : c₁ * c₁ = 1 := P.wordProd_mul_self_of_pairwise_orthogonal b hl₁ horth₁
  -- Perron–Frobenius vector and unit simple-root basis.
  obtain ⟨lam, hlam_nonneg, a, ha_pos, ha_eig⟩ := P.exists_perron_weightedAdjMatrix b
  let uUnits : b.support → ℝˣ := fun i ↦
    Units.mk0 (Real.sqrt (P.RootForm (P.root i) (P.root i)))⁻¹
      (inv_ne_zero (Real.sqrt_pos.2 (P.rootForm_root_pos i)).ne')
  let uBasis : Module.Basis b.support ℝ M := b.toWeightBasis.unitsSMul uUnits
  have huBasis_apply (i : b.support) : uBasis i = P.unitSimpleRoot b i := by
    simp [uBasis, uUnits, unitSimpleRoot, Module.Basis.unitsSMul_apply]
  set a₁ : b.support → ℝ := fun i ↦ if col i = true then a i else 0
  set a₂ : b.support → ℝ := fun i ↦ if col i = false then a i else 0
  set v₁ : M := ∑ i : b.support, a₁ i • P.unitSimpleRoot b i
  set v₂ : M := ∑ i : b.support, a₂ i • P.unitSimpleRoot b i
  have hv_sum : v₁ + v₂ = ∑ i : b.support, a i • P.unitSimpleRoot b i := by
    simp only [v₁, v₂, ← Finset.sum_add_distrib, ← add_smul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [a₁, a₂]; cases col i <;> simp
  obtain ⟨hc₁_v₁, hc₁_v₂, hM₁C_mul⟩ :=
    P.wordProd_color_action b col true hl₁ hcol₁ ha_eig uBasis huBasis_apply
  obtain ⟨hc₂_v₂, hc₂_v₁, hM₂C_mul⟩ :=
    P.wordProd_color_action b col false hl₂ hcol₂ ha_eig uBasis huBasis_apply
  simp only [Bool.not_true] at hc₁_v₁ hc₁_v₂ hM₁C_mul
  simp only [Bool.not_false] at hc₂_v₂ hc₂_v₁ hM₂C_mul
  -- Positivity of `P.RootForm (v₁ + v₂) (v₁ + v₂)` gives `lam < 2` and dominance.
  have hpair_u (k : b.support) :
      2 * P.RootForm (v₁ + v₂) (P.unitSimpleRoot b k) = (2 - lam) * a k := by
    rw [hv_sum, LinearMap.map_sum₂, Finset.mul_sum]
    have hterm : ∀ j : b.support,
        2 * P.RootForm (a j • P.unitSimpleRoot b j) (P.unitSimpleRoot b k) =
          (if j = k then 2 * a k else 0) - A k j * a j := fun j ↦ by
      rw [LinearMap.map_smul₂, smul_eq_mul, mul_left_comm, P.two_mul_rootForm_unitSimpleRoot]
      by_cases hjk : j = k
      · subst hjk; simp [A, weightedAdjMatrix]; ring
      · rw [ite_eq_right hjk, ite_eq_right hjk, P.weightedAdjMatrix_symm]; ring
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hAk : ∑ j : b.support, A k j * a j = lam * a k := by
      simpa [mulVec, dotProduct] using congrFun ha_eig k
    rw [hAk]; ring
  have hv_ne : v₁ + v₂ ≠ 0 := by
    intro h0
    obtain ⟨i₀⟩ := hne_supp
    have hsum0 : ∑ i : b.support, a i • uBasis i = 0 := by
      simpa only [huBasis_apply, ← hv_sum] using h0
    exact (ha_pos i₀).ne' (Fintype.linearIndependent_iff.1 uBasis.linearIndependent a hsum0 i₀)
  have hlam_lt : lam < 2 := by
    have hmem : v₁ + v₂ ∈ P.rootSpan ℝ := by
      rw [rootSpan, IsRootSystem.span_root_eq_top]; trivial
    have hpos_form : 0 < P.RootForm (v₁ + v₂) (v₁ + v₂) :=
      P.rootForm_pos_of_ne_zero hmem hv_ne
    have hval :
        2 * P.RootForm (v₁ + v₂) (v₁ + v₂) = (2 - lam) * ∑ k : b.support, a k ^ 2 := by
      conv_lhs => arg 2; arg 2; rw [hv_sum]
      rw [map_sum, Finset.mul_sum]
      simp_rw [map_smul, smul_eq_mul, mul_left_comm (2 : ℝ), hpair_u]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ by ring
    obtain ⟨i₀⟩ := hne_supp
    have hsq_pos : 0 < ∑ k : b.support, a k ^ 2 :=
      Finset.sum_pos (fun k _ ↦ sq_pos_of_pos (ha_pos k)) ⟨i₀, Finset.mem_univ i₀⟩
    have : 0 < 2 - lam := pos_of_mul_pos_left (by linarith) hsq_pos.le
    linarith
  have hv_dom : v₁ + v₂ ∈ openDominantChamber P b := by
    rw [mem_openDominantChamber]
    intro i hi
    let k : b.support := ⟨i, hi⟩
    have hk_pos : 0 < P.RootForm (P.root k) (P.root k) := P.rootForm_root_pos k
    have hsk_pos : 0 < Real.sqrt (P.RootForm (P.root k) (P.root k)) := Real.sqrt_pos.2 hk_pos
    have hpair_pos : 0 < 2 * P.RootForm (v₁ + v₂) (P.unitSimpleRoot b k) := by
      rw [hpair_u k]; exact mul_pos (sub_pos.2 hlam_lt) (ha_pos k)
    have hrel : 2 * P.RootForm (v₁ + v₂) (P.unitSimpleRoot b k) =
        (Real.sqrt (P.RootForm (P.root k) (P.root k)))⁻¹ *
          (P.coroot' k (v₁ + v₂) * P.RootForm (P.root k) (P.root k)) := by
      unfold unitSimpleRoot
      have h2 := P.toInvariantForm.two_mul_apply_root (v₁ + v₂) k
      rw [P.toInvariantForm_form] at h2
      rw [map_smul, smul_eq_mul, ← h2]
      ring
    rw [hrel] at hpair_pos
    exact pos_of_mul_pos_left
      (pos_of_mul_pos_right hpair_pos (inv_nonneg.2 hsk_pos.le)) hk_pos.le
  -- Construct the complex eigenvector `z₀ = a₁ + μ • a₂` for `ζ⁻¹` in `uBasis`.
  set θ : ℝ := Real.arccos (lam / 2)
  have hcosθ : Real.cos θ = lam / 2 := Real.cos_arccos (by linarith) (by linarith)
  have hsinθ_pos : 0 < Real.sin θ := by
    have hθ_pos : 0 < θ := by
      have hlt : Real.arccos (1 : ℝ) < θ :=
        Real.arccos_lt_arccos (by linarith) (by linarith) (by norm_num)
      simpa [Real.arccos_one] using hlt
    have hθ_le : θ ≤ Real.pi / 2 := by
      have hle : θ ≤ Real.arccos (0 : ℝ) := Real.arccos_le_arccos (by linarith)
      simpa [Real.arccos_zero] using hle
    exact Real.sin_pos_of_pos_of_lt_pi hθ_pos (lt_of_le_of_lt hθ_le (by linarith [Real.pi_pos]))
  set μ : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  set ζ : ℂ := μ ^ 2
  have hμ_ne : μ ≠ 0 := Complex.exp_ne_zero _
  have hμ_add_inv : μ + μ⁻¹ = (lam : ℂ) := by
    have hinv : μ⁻¹ = Complex.exp ((-(θ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_neg]; congr 1; ring
    rw [hinv]
    simp only [μ, Complex.exp_mul_I]
    rw [Complex.cos_neg, Complex.sin_neg]
    have : (2 : ℂ) * Complex.cos (θ : ℂ) = (lam : ℂ) := by
      rw [← Complex.ofReal_cos, hcosθ]; push_cast; ring
    linear_combination this
  let M₁ : Matrix b.support b.support ℝ :=
    LinearMap.toMatrix uBasis uBasis (P.weylGroupRootRep c₁)
  let M₂ : Matrix b.support b.support ℝ :=
    LinearMap.toMatrix uBasis uBasis (P.weylGroupRootRep c₂)
  set M₁C : Matrix b.support b.support ℂ := M₁.map Complex.ofReal
  set M₂C : Matrix b.support b.support ℂ := M₂.map Complex.ofReal
  have hM_mul : M₁ * M₂ = LinearMap.toMatrix uBasis uBasis (P.weylGroupRootRep c) := by
    change LinearMap.toMatrix uBasis uBasis (P.weylGroupRootRep c₁) *
      LinearMap.toMatrix uBasis uBasis (P.weylGroupRootRep c₂) = _
    rw [← LinearMap.toMatrix_mul, ← map_mul]
  have hM₁C_sq : M₁C * M₁C = 1 := by
    have hM₁_sq : M₁ * M₁ = 1 := by
      simp only [M₁, ← LinearMap.toMatrix_mul, ← map_mul, hc₁_sq, map_one,
        LinearMap.toMatrix_one]
    have hmap : M₁C * M₁C = (M₁ * M₁).map Complex.ofReal := by
      ext i j; simp [M₁C, Matrix.mul_apply]
    rw [hmap, hM₁_sq]; ext i j; by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have hmulVec_ofReal (M : Matrix b.support b.support ℝ) (x : b.support → ℝ) :
      M.map Complex.ofReal *ᵥ (fun i ↦ (x i : ℂ)) = fun i ↦ ((M *ᵥ x) i : ℂ) := by
    ext i; simp [mulVec, dotProduct]
  have hrep_vec (x : b.support → ℝ) :
      (uBasis.repr (∑ i : b.support, x i • P.unitSimpleRoot b i) : b.support → ℝ) = x := by
    ext j; simp [← huBasis_apply, uBasis.repr_self, Finsupp.single_apply]
  have hM_apply (g : P.weylGroup) (x : b.support → ℝ) :
      LinearMap.toMatrix uBasis uBasis (P.weylGroupRootRep g) *ᵥ x =
        uBasis.repr (g • ∑ i : b.support, x i • P.unitSimpleRoot b i) := by
    have h1 := LinearMap.toMatrix_mulVec_repr uBasis uBasis (P.weylGroupRootRep g)
      (∑ i : b.support, x i • P.unitSimpleRoot b i)
    rw [hrep_vec] at h1
    exact h1
  have hM₁a₁ : M₁ *ᵥ a₁ = -a₁ := by
    rw [hM_apply c₁ a₁, show ∑ i : b.support, a₁ i • P.unitSimpleRoot b i = v₁ from rfl,
      hc₁_v₁, map_neg]
    ext i; exact congrArg (fun f : b.support → ℝ ↦ -f i) (hrep_vec a₁)
  have hM₁a₂ : M₁ *ᵥ a₂ = a₂ + lam • a₁ := by
    rw [hM_apply c₁ a₂, show ∑ i : b.support, a₂ i • P.unitSimpleRoot b i = v₂ from rfl,
      hc₁_v₂, map_add, map_smul]
    ext i
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show uBasis.repr v₁ i = a₁ i from congrFun (hrep_vec a₁) i,
      show uBasis.repr v₂ i = a₂ i from congrFun (hrep_vec a₂) i]
  have hM₂a₂ : M₂ *ᵥ a₂ = -a₂ := by
    rw [hM_apply c₂ a₂, show ∑ i : b.support, a₂ i • P.unitSimpleRoot b i = v₂ from rfl,
      hc₂_v₂, map_neg]
    ext i; exact congrArg (fun f : b.support → ℝ ↦ -f i) (hrep_vec a₂)
  have hM₂a₁ : M₂ *ᵥ a₁ = a₁ + lam • a₂ := by
    rw [hM_apply c₂ a₁, show ∑ i : b.support, a₁ i • P.unitSimpleRoot b i = v₁ from rfl,
      hc₂_v₁, map_add, map_smul]
    ext i
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show uBasis.repr v₁ i = a₁ i from congrFun (hrep_vec a₁) i,
      show uBasis.repr v₂ i = a₂ i from congrFun (hrep_vec a₂) i]
  set z₀ : b.support → ℂ := fun i ↦ (a₁ i : ℂ) + μ * (a₂ i : ℂ)
  have hz₀_ne : z₀ ≠ 0 := by
    intro h0
    obtain ⟨i₀⟩ := hne_supp
    have hi0 := congrFun h0 i₀
    simp only [z₀, Pi.zero_apply] at hi0
    cases hci : col i₀ with
    | true =>
      exact (ha_pos i₀).ne' (Complex.ofReal_eq_zero.1 (by simpa [a₁, a₂, hci] using hi0))
    | false =>
      have : μ * (a i₀ : ℂ) = 0 := by simpa [a₁, a₂, hci] using hi0
      exact (ha_pos i₀).ne' (Complex.ofReal_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hμ_ne))
  have hz₀_eig : (M₁C * M₂C) *ᵥ z₀ = ζ⁻¹ • z₀ := by
    have hstep₂ : M₂C *ᵥ z₀ = fun i ↦ (a₁ i : ℂ) + μ⁻¹ * (a₂ i : ℂ) := by
      have hz_eq : z₀ = (fun i ↦ (a₁ i : ℂ)) + μ • (fun i ↦ (a₂ i : ℂ)) := by
        ext i; simp [z₀]
      rw [hz_eq, mulVec_add, mulVec_smul, hmulVec_ofReal, hmulVec_ofReal, hM₂a₁, hM₂a₂]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Complex.ofReal_add,
        Complex.ofReal_mul, Complex.ofReal_neg]
      linear_combination (a₂ i : ℂ) * hμ_add_inv.symm
    rw [← mulVec_mulVec, hstep₂]
    have hstep₁ : (fun i ↦ (a₁ i : ℂ) + μ⁻¹ * (a₂ i : ℂ)) =
        (fun i ↦ (a₁ i : ℂ)) + μ⁻¹ • (fun i ↦ (a₂ i : ℂ)) := by ext i; simp
    rw [hstep₁, mulVec_add, mulVec_smul, hmulVec_ofReal, hmulVec_ofReal, hM₁a₁, hM₁a₂]
    ext i
    simp only [z₀, ζ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_neg]
    have hμinv : μ⁻¹ * (lam : ℂ) - 1 = (μ ^ 2)⁻¹ := by
      rw [← hμ_add_inv]; field_simp [hμ_ne]; ring
    have hμstep : (μ ^ 2)⁻¹ * μ = μ⁻¹ := by field_simp [hμ_ne]
    linear_combination (a₁ i : ℂ) * hμinv - (a₂ i : ℂ) * hμstep
  -- `ζ` is a primitive `h`-th root of unity.
  have hM_pow (k : ℕ) :
      (M₁ * M₂) ^ k = LinearMap.toMatrix uBasis uBasis (P.weylGroupRootRep (c ^ k)) := by
    induction k with
    | zero => simp [LinearMap.toMatrix_one]
    | succ k ih => rw [pow_succ, pow_succ, ih, hM_mul, ← LinearMap.toMatrix_mul, ← map_mul]
  have hM_mul_map : M₁C * M₂C = (M₁ * M₂).map Complex.ofReal := by
    ext i j; simp [M₁C, M₂C, Matrix.mul_apply]
  have hM_pow_map (k : ℕ) : (M₁C * M₂C) ^ k = ((M₁ * M₂) ^ k).map Complex.ofReal := by
    induction k with
    | zero => ext i j; by_cases hij : i = j <;> simp [hij]
    | succ k ih =>
      rw [pow_succ, pow_succ, ih, hM_mul_map]
      ext i j; simp [Matrix.mul_apply]
  have hM_pow_eig (k : ℕ) : ((M₁C * M₂C) ^ k) *ᵥ z₀ = (ζ⁻¹) ^ k • z₀ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hz₀_eig, smul_smul, mul_comm,
        ← pow_succ']
  have hζ_prim : IsPrimitiveRoot ζ h := by
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨?_, fun k hk ↦ ?_⟩
    · have hch : (M₁ * M₂) ^ h = 1 := by
        rw [hM_pow, pow_orderOf_eq_one, map_one, LinearMap.toMatrix_one]
      have hchC : (M₁C * M₂C) ^ h = 1 := by
        rw [hM_pow_map, hch]; ext i j; by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
      have h1 := hM_pow_eig h
      rw [hchC, one_mulVec] at h1
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hz₀_ne
      have hinv1 : (ζ⁻¹) ^ h = 1 :=
        mul_right_cancel₀ hi₀
          (by simpa [Pi.smul_apply, smul_eq_mul] using (congrFun h1 i₀).symm)
      rwa [inv_pow, inv_eq_one] at hinv1
    · have h1 := hM_pow_eig k
      rw [inv_pow, hk, inv_one, one_smul, hM_pow_map] at h1
      have hz_eq : z₀ = (fun i ↦ (a₁ i : ℂ)) + μ • (fun i ↦ (a₂ i : ℂ)) := by
        ext i; simp [z₀]
      rw [hz_eq, mulVec_add, mulVec_smul, hmulVec_ofReal, hmulVec_ofReal] at h1
      have ha₂_fix : ((M₁ * M₂) ^ k) *ᵥ a₂ = a₂ := by
        ext i
        have him := congrArg Complex.im (congrFun h1 i)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_im, Complex.ofReal_im,
          zero_add, Complex.mul_im, Complex.ofReal_re, mul_zero, μ, Complex.exp_mul_I,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin] at him
        exact mul_left_cancel₀ hsinθ_pos.ne' (by simpa using him)
      have ha₁_fix : ((M₁ * M₂) ^ k) *ᵥ a₁ = a₁ := by
        ext i
        have hre := congrArg Complex.re (congrFun h1 i)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero, ha₂_fix] at hre
        linarith
      have hck_fix : c ^ k • (v₁ + v₂) = v₁ + v₂ := by
        apply uBasis.repr.injective
        ext i
        have hact := congrFun (hM_apply (c ^ k) (a₁ + a₂)) i
        have hsum_vec :
            ∑ j : b.support, (a₁ + a₂) j • P.unitSimpleRoot b j = v₁ + v₂ := by
          simp [v₁, v₂, add_smul, Finset.sum_add_distrib]
        rw [← hM_pow, mulVec_add, ha₁_fix, ha₂_fix, hsum_vec] at hact
        have hrep_sum := congrFun (hrep_vec (a₁ + a₂)) i
        rw [hsum_vec] at hrep_sum
        exact hact.symm.trans hrep_sum.symm
      exact orderOf_dvd_of_pow_eq_one
        (eq_one_of_smul_eq_self_of_mem_openDominantChamber P b _ hv_dom hck_fix)
  -- Rationality of `(M₁C * M₂C).charpoly` gives an eigenvector for `ω₀ = exp (2 π I / h)`.
  have : Module.Finite ℝ M := Module.Finite.of_basis b.toWeightBasis
  let W : Matrix b.support b.support ℤ := ((l₁ ++ l₂).map (reflMatrix b.cartanMatrix)).prod
  have hW_mat : LinearMap.toMatrix b.toWeightBasis b.toWeightBasis (P.weylGroupRootRep c) =
      W.map (Int.castRingHom ℝ) := by
    ext i j
    rw [LinearMap.toMatrix_apply, b.toWeightBasis_apply]
    change b.toWeightBasis.repr (c • P.root j) i = (W i j : ℝ)
    rw [hc_word, (Base.actsBy_iff.1 (b.actsBy_wordProd (l₁ ++ l₂))) j]
    simp [W, map_sum, map_zsmul, Finsupp.single_apply]
  let p : ℚ[X] := (W.map (Int.castRingHom ℚ)).charpoly
  have hp_map : p.map (algebraMap ℚ ℂ) = (M₁C * M₂C).charpoly := by
    have hcp_real : (M₁ * M₂).charpoly = (W.map (Int.castRingHom ℝ)).charpoly := by
      rw [hM_mul, ← hW_mat, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]
    have hM_eq : M₁C * M₂C = (M₁ * M₂).map Complex.ofRealHom := hM_mul_map
    rw [hM_eq, Matrix.charpoly_map (M₁ * M₂) Complex.ofRealHom, hcp_real,
      ← Matrix.charpoly_map (W.map (Int.castRingHom ℝ)) Complex.ofRealHom,
      Matrix.map_map]
    dsimp only [p]
    rw [← Matrix.charpoly_map (W.map (Int.castRingHom ℚ)) (algebraMap ℚ ℂ), Matrix.map_map]
    congr 1
  set ω₀ : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hω₀_root : (M₁C * M₂C).charpoly.IsRoot ω₀ := by
    have hζinv_root : (p.map (algebraMap ℚ ℂ)).IsRoot ζ⁻¹ := by
      rw [hp_map, ← Matrix.charpoly_toLin' (M₁C * M₂C),
        ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
      exact Module.End.hasEigenvalue_of_hasEigenvector
        (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hz₀_eig, hz₀_ne⟩)
    rw [← hp_map]
    have : NeZero (h : ℚ) := ⟨Nat.cast_ne_zero.2 hh_pos.ne'⟩
    have hdiv : cyclotomic h ℚ ∣ p := by
      rw [hζ_prim.inv.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hh_pos)]
      exact minpoly.dvd ℚ ζ⁻¹
        (by simpa only [aeval_def, eval₂_eq_eval_map, IsRoot.def] using hζinv_root)
    obtain ⟨q, hq⟩ := hdiv
    rw [hq, Polynomial.map_mul, map_cyclotomic, IsRoot.def, eval_mul,
      ((Complex.isPrimitiveRoot_exp h hh_pos.ne').isRoot_cyclotomic hh_pos).eq_zero, zero_mul]
  rw [← Matrix.charpoly_toLin' (M₁C * M₂C),
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hω₀_root
  obtain ⟨z, hz⟩ := hω₀_root.exists_hasEigenvector
  have hbound : ‖(1 + ω₀) ^ 2 / ω₀‖ ≤ lam ^ 2 :=
    spectral_bound_of_bipartite_eigenvector (P.weightedAdjMatrix_nonneg b) hA_same ha_pos ha_eig
      hM₁C_sq hM₁C_mul hM₂C_mul (Complex.exp_ne_zero _) hz.2
      (Module.End.mem_eigenspace_iff.1 hz.1)
  have hlam_eq : lam = 2 * Real.cos (Real.pi / h) :=
    eq_two_mul_cos_pi_div_of_spectral_bound hlam_nonneg hlam_lt h2le hζ_prim.pow_eq_one hbound
  refine ⟨v₁, v₂, hv_dom, hc₁_v₁, ?_, hc₂_v₂, ?_⟩
  · rwa [← hlam_eq]
  · rwa [← hlam_eq]

end RealCoxeterPlane

section ComplexRegularEigenvector

/-- **Regular eigenvector of a Coxeter element over `ℂ`.** Every Coxeter element `wordProd P b l`
of a finite irreducible reduced crystallographic root system over `ℂ` admits a regular weight `v`
which is an eigenvector with eigenvalue
`(Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b l)))⁻¹`. -/
theorem exists_isRegularWeight_smul_eq_exp_neg_wordProd
    {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (P : RootPairing ι ℂ M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]
    [P.IsRootSystem] [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    ∃ v : M, IsRegularWeight P v ∧
      wordProd P b l • v =
        (Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b l)))⁻¹ • v := by
  classical
  let := Fintype.ofFinite ι
  set Q := b.rationalModel
  set hQ := b.rationalModel_toLinearMap
  set PR := rootPairingBaseChange ℝ Q hQ
  set PC := rootPairingBaseChange ℂ Q hQ
  let bR : PR.Base := rootPairingBaseChangeBase ℝ Q hQ b.rationalModelBase
  let bC : PC.Base := rootPairingBaseChangeBase ℂ Q hQ b.rationalModelBase
  -- Construct a bipartite Coxeter element on `PR`.
  obtain ⟨col⟩ := nonempty_coloring_graph_coxeterMatrixOfBase PR bR
  let l₁R : List bR.support := (Finset.univ.filter fun i : bR.support ↦ col i = true).toList
  let l₂R : List bR.support := (Finset.univ.filter fun i : bR.support ↦ col i = false).toList
  have hl₁R : l₁R.Nodup := Finset.nodup_toList _
  have hl₂R : l₂R.Nodup := Finset.nodup_toList _
  have hcol₁ : ∀ i : bR.support, i ∈ l₁R ↔ col i = true := fun i ↦ by simp [l₁R]
  have hcol₂ : ∀ i : bR.support, i ∈ l₂R ↔ col i = false := fun i ↦ by simp [l₂R]
  obtain ⟨v₁, v₂, hv_dom, hc₁_v₁, hc₁_v₂, hc₂_v₂, hc₂_v₁⟩ :=
    PR.exists_coxeterPlane_bipartite bR col hl₁R hl₂R hcol₁ hcol₂
  -- Match the supports of `bR`, `bC`, and `b`.
  let eRC : bR.support ≃ bC.support :=
    (supportEquivRootPairingBaseChangeBase ℝ Q hQ b.rationalModelBase).trans
      (supportEquivRootPairingBaseChangeBase ℂ Q hQ b.rationalModelBase).symm
  have heRC_coe (i : bR.support) : ((eRC i : ι)) = (i : ι) := by
    have h1 := coe_supportEquivRootPairingBaseChangeBase ℂ Q hQ b.rationalModelBase (eRC i)
    have h2 := coe_supportEquivRootPairingBaseChangeBase ℝ Q hQ b.rationalModelBase i
    simp only [eRC, _root_.Equiv.trans_apply, _root_.Equiv.apply_symm_apply] at h1
    exact h1.symm.trans h2
  let l₁C : List bC.support := l₁R.map eRC
  let l₂C : List bC.support := l₂R.map eRC
  set c₁R := wordProd PR bR l₁R
  set c₂R := wordProd PR bR l₂R
  set cR := c₁R * c₂R
  set c₁C := wordProd PC bC l₁C
  set c₂C := wordProd PC bC l₂C
  set cC := c₁C * c₂C
  -- Real-to-complex compatibility of coroots and simple-reflection words on `PR` and `PC`.
  let toC := Pi.algebraMap b.support ℝ ℂ
  have htoC_smul (r : ℝ) (x : b.support → ℝ) : toC (r • x) = (r : ℂ) • toC x := by
    ext k; simp [toC, piAlgebraMap_apply]
  have hcoroot'_ofReal (j : ι) (x : b.support → ℝ) :
      PC.coroot' j (toC x) = (PR.coroot' j x : ℂ) := by
    simp only [coroot', LinearMap.flip_apply,
      toLinearMap_rootPairingBaseChange, coroot_rootPairingBaseChange, piAlgebraMap_apply,
      dotProduct, toC, PC, PR]
    push_cast
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp
  have hofIdx_ofReal (j : ι) (x : b.support → ℝ) :
      weylGroup.ofIdx PC j • toC x = toC (weylGroup.ofIdx PR j • x) := by
    rw [weylGroup.ofIdx_smul, weylGroup.ofIdx_smul, Equiv.reflection_smul, Equiv.reflection_smul,
      reflection_apply, reflection_apply, hcoroot'_ofReal]
    ext k
    simp [toC, root_rootPairingBaseChange, piAlgebraMap_apply, PC, PR]
  have hword_ofReal (m : List bR.support) (x : b.support → ℝ) :
      wordProd PC bC (m.map eRC) • toC x = toC (wordProd PR bR m • x) := by
    induction m with
    | nil => simp
    | cons a t ih =>
      rw [List.map_cons, wordProd_cons, wordProd_cons, mul_smul, mul_smul, ih, heRC_coe,
        hofIdx_ofReal]
  -- `cR` and `cC` have the same order since `toC` is injective and intertwines their powers.
  have horder_eq : orderOf cC = orderOf cR := by
    have hc_ofReal (x : b.support → ℝ) : cC • toC x = toC (cR • x) := by
      simp only [cC, cR, c₁C, c₂C, c₁R, c₂R, l₁C, l₂C, mul_smul, hword_ofReal]
    have hpow_ofReal (k : ℕ) (x : b.support → ℝ) :
        cC ^ k • toC x = toC (cR ^ k • x) := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', pow_succ', mul_smul cC, mul_smul cR, ih, hc_ofReal]
    have hroot_ofReal (j : ι) : toC (PR.root j) = PC.root j := by
      ext k; simp [toC, root_rootPairingBaseChange, piAlgebraMap_apply, PC, PR]
    refine orderOf_eq_orderOf_iff.2 fun k ↦ ⟨fun hk ↦ ?_, fun hk ↦ ?_⟩
    · refine weylGroup.eq_one_of_forall_smul_root_eq fun j ↦ piAlgebraMap_injective ℂ ?_
      rw [← hpow_ofReal, hk, one_smul]
    · refine weylGroup.eq_one_of_forall_smul_root_eq fun j ↦ ?_
      rw [← hroot_ofReal, hpow_ofReal, hk, one_smul]
  set h : ℕ := orderOf cR
  have h2le : 2 ≤ h := by
    have := IsIrreducible.nontrivial PR
    have hnodup : (l₁R ++ l₂R).Nodup := by
      rw [List.nodup_append]
      refine ⟨hl₁R, hl₂R, fun i hi₁ j hi₂ hij ↦ ?_⟩
      subst hij
      have h1 := (hcol₁ i).1 hi₁
      have h2 := (hcol₂ i).1 hi₂
      simp [h1] at h2
    have hallR : ∀ i : bR.support, i ∈ l₁R ++ l₂R := fun i ↦ by
      rw [List.mem_append, hcol₁, hcol₂]; cases col i <;> simp
    change 2 ≤ orderOf cR
    rw [show cR = wordProd PR bR (l₁R ++ l₂R) from (wordProd_append bR l₁R l₂R).symm]
    exact PR.two_le_orderOf_wordProd bR hnodup hallR
  have _ : 0 < h := by omega
  set φ : ℝ := Real.pi / h
  set μ : ℂ := Complex.exp ((φ : ℂ) * Complex.I)
  have hsinφ_pos : 0 < Real.sin φ := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    have h2 : (2 : ℝ) ≤ h := by exact_mod_cast h2le
    have : Real.pi / h ≤ Real.pi / 2 :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) h2
    linarith [Real.pi_pos]
  have hμ_ne : μ ≠ 0 := Complex.exp_ne_zero _
  have hμ_add : μ + μ⁻¹ = ((2 * Real.cos φ : ℝ) : ℂ) := by
    have hinv : μ⁻¹ = Complex.exp ((-(φ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_neg]; congr 1; ring
    rw [hinv]
    simp only [μ, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
    push_cast
    ring
  have hμ_sq : μ ^ 2 = Complex.exp (2 * Real.pi * Complex.I / h) := by
    simp only [μ, φ, sq, ← Complex.exp_add]
    congr 1; push_cast; ring
  -- Regular eigenvector `vC = toC v₁ + μ • toC v₂` of `cC` on `PC`.
  set vC : b.support → ℂ := toC v₁ + μ • toC v₂
  have hvC_reg : IsRegularWeight PC vC := by
    rw [isRegularWeight_iff]
    intro j hj
    have hdom_reg : IsRegularWeight PR (v₁ + v₂) :=
      isRegularWeight_of_mem_openDominantChamber PR bR hv_dom
    simp only [vC, map_add, map_smul, smul_eq_mul, hcoroot'_ofReal] at hj
    have him : Real.sin φ * PR.coroot' j v₂ = 0 := by
      have := congrArg Complex.im hj
      simpa [μ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] using this
    have h2 : PR.coroot' j v₂ = 0 := (mul_eq_zero.1 him).resolve_left hsinφ_pos.ne'
    have h1 : PR.coroot' j v₁ = 0 := by
      have := congrArg Complex.re hj
      simpa [h2] using this
    exact (isRegularWeight_iff PR _).1 hdom_reg j (by simp [map_add, h1, h2])
  have hvC_eig : cC • vC = (Complex.exp (2 * Real.pi * Complex.I / orderOf cC))⁻¹ • vC := by
    have hc₂_vC : c₂C • vC = toC v₁ + μ⁻¹ • toC v₂ := by
      change (PC.weylGroupRootRep c₂C) (toC v₁ + μ • toC v₂) = _
      rw [map_add, map_smul]
      change c₂C • toC v₁ + μ • (c₂C • toC v₂) = _
      rw [hword_ofReal, hword_ofReal, hc₂_v₁, hc₂_v₂, map_add, htoC_smul, map_neg]
      ext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      linear_combination toC v₂ k * hμ_add.symm
    have hc₁_vC : c₁C • (toC v₁ + μ⁻¹ • toC v₂) = (μ ^ 2)⁻¹ • vC := by
      change (PC.weylGroupRootRep c₁C) (toC v₁ + μ⁻¹ • toC v₂) = _
      rw [map_add, map_smul]
      change c₁C • toC v₁ + μ⁻¹ • (c₁C • toC v₂) = _
      rw [hword_ofReal, hword_ofReal, hc₁_v₁, hc₁_v₂, map_add, htoC_smul, map_neg]
      ext k
      simp only [vC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      have hμinv : μ⁻¹ * ((2 * Real.cos φ : ℝ) : ℂ) - 1 = (μ ^ 2)⁻¹ := by
        rw [← hμ_add]; field_simp [hμ_ne]; ring
      have hμstep : (μ ^ 2)⁻¹ * μ = μ⁻¹ := by field_simp [hμ_ne]
      linear_combination toC v₁ k * hμinv - toC v₂ k * hμstep
    rw [show cC = c₁C * c₂C from rfl, mul_smul, hc₂_vC, hc₁_vC, horder_eq, ← hμ_sq]
  -- Transport `vC` from `PC` to `P` via `b.equivBaseChangeRationalModel`.
  let eqv := b.equivBaseChangeRationalModel
  let eCB : bC.support ≃ b.support :=
    (supportEquivRootPairingBaseChangeBase ℂ Q hQ b.rationalModelBase).trans
      b.supportEquivRationalModelBase
  have heCB_coe (i : bC.support) : ((eCB i : ι)) = (i : ι) :=
    (b.coe_supportEquivRationalModelBase _).trans
      (coe_supportEquivRootPairingBaseChangeBase ℂ Q hQ b.rationalModelBase i)
  let lBip : List b.support := (l₁C ++ l₂C).map eCB
  have hlBip_nodup : lBip.Nodup := by
    refine List.Nodup.map eCB.injective ?_
    rw [show l₁C ++ l₂C = (l₁R ++ l₂R).map eRC from List.map_append.symm]
    refine List.Nodup.map eRC.injective ?_
    rw [List.nodup_append]
    refine ⟨hl₁R, hl₂R, fun i hi₁ j hi₂ hij ↦ ?_⟩
    subst hij
    have h1 := (hcol₁ i).1 hi₁
    have h2 := (hcol₂ i).1 hi₂
    simp [h1] at h2
  have hlBip_all : ∀ i : b.support, i ∈ lBip := fun i ↦ by
    have hmem : eRC.symm (eCB.symm i) ∈ l₁R ++ l₂R := by
      rw [List.mem_append, hcol₁, hcol₂]
      cases col (eRC.symm (eCB.symm i)) <;> simp
    have hmemC : eCB.symm i ∈ l₁C ++ l₂C := by
      rw [show l₁C ++ l₂C = (l₁R ++ l₂R).map eRC from List.map_append.symm]
      exact List.mem_map.2 ⟨eRC.symm (eCB.symm i), hmem, eRC.apply_symm_apply _⟩
    exact List.mem_map.2 ⟨eCB.symm i, hmemC, eCB.apply_symm_apply i⟩
  have hword_eqv : eqv.weylGroupEquiv (wordProd P b lBip) = cC := by
    rw [show cC = wordProd PC bC (l₁C ++ l₂C) from (wordProd_append bC l₁C l₂C).symm]
    suffices ∀ m : List bC.support,
        eqv.weylGroupEquiv (wordProd P b (m.map eCB)) = wordProd PC bC m
      from this (l₁C ++ l₂C)
    intro m
    induction m with
    | nil => simp
    | cons a t ih =>
      rw [List.map_cons, wordProd_cons, wordProd_cons, map_mul, ih, Equiv.weylGroupEquiv_ofIdx,
        b.equivBaseChangeRationalModel_indexEquiv, _root_.Equiv.refl_apply, heCB_coe]
  set vBip : M := eqv.weightEquiv.symm vC
  have hvBip_reg : IsRegularWeight P vBip := by
    rw [isRegularWeight_iff]
    intro j hj
    have hcor : PC.coroot' j vC = P.coroot' j vBip := by
      have h := eqv.coroot'_weightEquiv j vBip
      rw [b.equivBaseChangeRationalModel_indexEquiv, _root_.Equiv.refl_apply] at h
      simpa [PC, Q, vBip, coroot', toLinearMap_rootPairingBaseChange,
        coroot_rootPairingBaseChange] using h
    exact (isRegularWeight_iff PC vC).1 hvC_reg j (hcor.trans hj)
  have horder_bip : orderOf (wordProd P b lBip) = orderOf cC :=
    (orderOf_injective eqv.weylGroupEquiv.toMonoidHom eqv.weylGroupEquiv.injective _).symm.trans
      (congrArg orderOf hword_eqv)
  have hvBip_eig : wordProd P b lBip • vBip =
      (Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b lBip)))⁻¹ • vBip := by
    apply eqv.weightEquiv.injective
    rw [← eqv.weylGroupEquiv_smul, hword_eqv, map_smul]
    simpa [vBip, horder_bip] using hvC_eig
  -- Conjugate from the bipartite Coxeter element `wordProd P b lBip` to `wordProd P b l`.
  have hperm : lBip.Perm l :=
    (List.perm_ext_iff_of_nodup hlBip_nodup hl).2 fun i ↦ by simp [hlBip_all, hall]
  obtain ⟨u, hu⟩ := P.isConj_wordProd_of_perm b hlBip_nodup hperm
  have hconj : (MulAut.conj (u : P.weylGroup)) (wordProd P b lBip) = wordProd P b l := by
    rw [MulAut.conj_apply, hu.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hord_conj : orderOf (wordProd P b l) = orderOf (wordProd P b lBip) := by
    rw [← hconj]
    exact orderOf_injective (MulAut.conj (u : P.weylGroup)).toMonoidHom
      (MulAut.conj (u : P.weylGroup)).injective _
  refine ⟨(u : P.weylGroup) • vBip,
    (isRegularWeight_smul P (u : P.weylGroup) vBip).2 hvBip_reg, ?_⟩
  rw [hord_conj, ← mul_smul, ← hu.eq, mul_smul, hvBip_eig]
  change (P.weylGroupRootRep (u : P.weylGroup)) _ = _
  rw [map_smul]
  rfl

end ComplexRegularEigenvector

end RootPairing
