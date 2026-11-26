/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.RingTheory.Isocrystal.CoefficientFrobenius
public import TauCeti.RingTheory.Isocrystal.StandardBlock
public import TauCeti.RingTheory.LaurentSeries.Ramified
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import TauCeti.FieldTheory.IsAlgClosed.FrobeniusFixedPoints
import TauCeti.FieldTheory.IsAlgClosed.PolynomialFixedPoint
import TauCeti.LinearAlgebra.FiniteDimensional.Semilinear
import TauCeti.LinearAlgebra.LinearIndependent.Iterate
import TauCeti.RingTheory.LaurentSeries.Basic

/-!
# Simplicity and existence of cyclic standard blocks

This file establishes the two key properties of simple cyclic blocks `D(s, r)` with `s` and `r`
coprime:

1. **Simplicity (`TauCeti.eq_bot_or_eq_top_of_standardBlockFrobenius_stable`).** Over any field `L`
   with an automorphism `σ` preserving a valuation `v` and fixing a nonzero element `π` whose
   valuation generates `v(Lˣ)`, `D(s, r)` has no proper nontrivial
   `standardBlockFrobenius σ π s r`-stable `L`-subspaces when `Nat.Coprime s.natAbs r`.
2. **Existence (`TauCeti.exists_inj_intertwines_standardBlock`).** Over `k((π))` with `k`
   algebraically closed of characteristic `p > 0` and `σ = coefficientFrobenius p f k`, every
   nontrivial finite isocrystal `(V, Φ)` admits an injective `k((π))`-linear intertwiner
   `D(s, r) ↪ V` for some coprime `s : ℤ`, `r : ℕ+`.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §8.2.3.
* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004), §§4.1–4.5.
-/

public section

open Finset Function Module
open scoped LaurentSeries PowerSeries

namespace TauCeti

/-! ### Simplicity of coprime standard blocks -/

section Simplicity

private theorem exists_col_submatrix_det_ne_zero {L : Type*} [Field L] {d r : ℕ}
    {M : Matrix (Fin d) (Fin r) L} (hrow : LinearIndependent L M.row) :
    ∃ c : Fin d → Fin r, (M.submatrix id c).det ≠ 0 := by
  obtain ⟨κ, a, _, hspan, hli⟩ := exists_linearIndependent' L M.col
  have hfin : Finite κ := hli.finite_of_isNoetherian
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = d := by
    rw [← finrank_span_eq_card hli, hspan, Matrix.finrank_span_range_col, hrow.rank_matrix,
      Fintype.card_fin]
  let e : Fin d ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have hcol : LinearIndependent L (M.submatrix id (a ∘ e)).col := by
    have hcomp : (M.submatrix id (a ∘ e)).col = (M.col ∘ a) ∘ e := rfl
    rw [hcomp]
    exact hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.linearIndependent_col_iff_isUnit.1 hcol)).ne_zero

private theorem det_basis_matrix_ne_zero_of_surjectiveₛₗ {L V : Type*} [Field L]
    [AddCommGroup V] [Module L V] {σ : L ≃+* L} {d : ℕ} (b : Basis (Fin d) L V)
    (Φ : V →ₛₗ[σ.toRingHom] V) (hΦ_surj : Surjective Φ) :
    (Matrix.of fun i k ↦ b.repr (Φ (b i)) k).det ≠ 0 := by
  let B : Matrix (Fin d) (Fin d) L := Matrix.of fun i k ↦ b.repr (Φ (b i)) k
  choose u hu using fun j : Fin d ↦ hΦ_surj (b j)
  let A : Matrix (Fin d) (Fin d) L := Matrix.of fun j i ↦ σ (b.repr (u j) i)
  have hAB : A * B = 1 := by
    ext j k
    have hrep := congrArg (fun x ↦ b.repr x k) (hu j)
    have hmap : Φ (u j) = ∑ i, σ (b.repr (u j) i) • Φ (b i) := by
      conv_lhs => rw [← b.sum_repr (u j)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smulₛₗ]
      rfl
    rw [hmap, map_sum] at hrep
    simp only [map_smul, Basis.repr_self, Finsupp.single_apply] at hrep
    simpa [A, B, Matrix.mul_apply, Matrix.one_apply, eq_comm] using hrep.symm
  have hdet := congrArg Matrix.det hAB
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  exact right_ne_zero_of_mul_eq_one hdet

private theorem basis_matrix_iterate_det_val {L Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] (σ : L ≃+* L) (π : L) (hσπ : σ π = π)
    (v : Valuation L Γ₀) (hv : ∀ x, v (σ x) = v x) {s : ℤ} {r d : ℕ}
    {U : Submodule L (Fin r → L)} (hU : ∀ x ∈ U, standardBlockFrobenius σ π s r x ∈ U)
    (b : Basis (Fin d) L U) :
    let B : Matrix (Fin d) (Fin d) L := Matrix.of fun i k ↦
      b.repr ⟨standardBlockFrobenius σ π s r (b i).val, hU (b i).val (b i).property⟩ k
    v B.det ^ r = v π ^ (s * (d : ℤ)) := by
  intro B
  let Φ := standardBlockFrobenius σ π s r
  have hΦ_b (i : Fin d) : Φ (b i).val = ∑ k, B i k • (b k).val := by
    have hrep := congrArg Subtype.val
      (b.sum_repr ⟨Φ (b i).val, hU (b i).val (b i).property⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hrep
    exact hrep.symm
  let C : ℕ → Matrix (Fin d) (Fin d) L := fun m ↦ Nat.rec 1 (fun _ P ↦ P.map σ * B) m
  have hC_eq (m : ℕ) (i : Fin d) : Φ^[m] (b i).val = ∑ k, C m i k • (b k).val := by
    induction m generalizing i with
    | zero => simp [C, Matrix.one_apply]
    | succ m ih =>
      rw [iterate_succ_apply', ih, map_sum]
      simp only [map_smulₛₗ, hΦ_b, smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [← Finset.sum_smul]
      simp [C, Matrix.mul_apply]
  have hvC (m : ℕ) : v (C m).det = v B.det ^ m := by
    induction m with
    | zero => simp [C]
    | succ m ih =>
      have hC_succ : C (m + 1) = (C m).map σ.toRingHom * B := rfl
      rw [hC_succ, Matrix.det_mul, map_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hv, ih, pow_succ]
  let M : Matrix (Fin d) (Fin r) L := Matrix.of fun i j ↦ (b i).val j
  obtain ⟨c, hc⟩ := exists_col_submatrix_det_ne_zero
    (b.linearIndependent.map' U.subtype (Submodule.ker_subtype U))
  let M₀ : Matrix (Fin d) (Fin d) L := M.submatrix id c
  -- Compare `Φ^[r]` via the basis matrix `C r` against `π ^ s • σ^[r]` on coordinates.
  have hCrM : C r * M₀ = π ^ s • M₀.map (σ^[r] : L → L) := by
    ext i j
    have h1 : Φ^[r] (b i).val (c j) = (C r * M₀) i j := by
      rw [hC_eq r i]
      simp [M₀, M, Matrix.mul_apply]
    have h2 : Φ^[r] (b i).val (c j) = π ^ s * σ^[r] (M₀ i j) :=
      standardBlockFrobenius_iterate_rank_apply hσπ (b i).val (c j)
    rw [← h1, h2]
    rfl
  have hdet_eq := congrArg (fun X ↦ v X.det) hCrM
  have hv_iter (x : L) : v (σ^[r] x) = v x := congrFun (iterate_invariant (funext hv) r) x
  have hdet_map : v (M₀.map (σ^[r] : L → L)).det = v M₀.det := by
    let σr : L ≃+* L := σ ^ r
    have hσr : (σ^[r] : L → L) = σr.toRingHom := by ext x; simp [σr]
    rw [hσr, ← RingHom.mapMatrix_apply, ← RingHom.map_det, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe]
    simpa [σr] using hv_iter M₀.det
  rw [Matrix.det_mul, Matrix.det_smul, map_mul, map_mul, hvC, map_pow, map_zpow₀, hdet_map]
    at hdet_eq
  have hmul := mul_right_cancel₀ ((map_ne_zero v).2 hc) hdet_eq
  simpa [← zpow_natCast, ← zpow_mul] using hmul

/-- **Simplicity of coprime standard blocks.** Let `σ` be an automorphism of a field `L` fixing a
nonzero element `π` and preserving a valuation `v` with `v π ≠ 1` whose values on `Lˣ` lie in
`⟨v π⟩`. Then for coprime `s` and `r`, the standard block `D(s, r)` has no proper nontrivial
`standardBlockFrobenius σ π s r`-stable `L`-subspaces. -/
theorem eq_bot_or_eq_top_of_standardBlockFrobenius_stable
    {L Γ₀ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ₀]
    (σ : L ≃+* L) (π : L) (hπ : π ≠ 0) (hσπ : σ π = π)
    (v : Valuation L Γ₀) (hv : ∀ x, v (σ x) = v x) (hvπ : v π ≠ 1)
    (hgen : ∀ x : L, x ≠ 0 → ∃ n : ℤ, v x = v π ^ n)
    {s : ℤ} {r : ℕ} (hcop : s.natAbs.Coprime r)
    {U : Submodule L (Fin r → L)}
    (hU : ∀ x ∈ U, standardBlockFrobenius σ π s r x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  rw [or_iff_not_imp_left]
  intro hU0
  have : RingHomSurjective σ.toRingHom := ⟨σ.surjective⟩
  set d := Module.finrank L U
  have hd_pos : 0 < d := Nat.pos_of_ne_zero fun hd ↦ hU0 (Submodule.finrank_eq_zero.1 hd)
  have hd_le : d ≤ r := by simpa [d] using Submodule.finrank_le U
  let b : Basis (Fin d) L U := Module.finBasis L U
  let Φ_U : U →ₛₗ[σ.toRingHom] U :=
    { toFun x := ⟨standardBlockFrobenius σ π s r x.val, hU x.val x.property⟩
      map_add' x y := Subtype.ext (map_add (standardBlockFrobenius σ π s r) x.val y.val)
      map_smul' c x := Subtype.ext (map_smulₛₗ (standardBlockFrobenius σ π s r) c x.val) }
  have hΦ_U_inj : Injective Φ_U := fun x y hxy ↦ Subtype.ext <|
    (standardBlockFrobenius_bijective hπ).injective (congrArg Subtype.val hxy)
  have hΦ_U_surj : Surjective Φ_U := LinearMap.surjective_of_injectiveₛₗ hΦ_U_inj
  let B : Matrix (Fin d) (Fin d) L := Matrix.of fun i k ↦ b.repr (Φ_U (b i)) k
  have hB_det : B.det ≠ 0 := det_basis_matrix_ne_zero_of_surjectiveₛₗ b Φ_U hΦ_U_surj
  have hvB_pow : v B.det ^ r = v π ^ (s * (d : ℤ)) :=
    basis_matrix_iterate_det_val σ π hσπ v hv hU b
  obtain ⟨k, hk⟩ := hgen B.det hB_det
  have hk_exp : v π ^ (k * (r : ℤ)) = v π ^ (s * (d : ℤ)) := by
    rw [zpow_mul, zpow_natCast, ← hk, hvB_pow]
  have hvπ0 : 0 < v π := pos_iff_ne_zero.2 ((map_ne_zero v).2 hπ)
  have hkr : k * (r : ℤ) = s * (d : ℤ) := zpow_right_injective₀ hvπ0 hvπ hk_exp
  have hdvd : r ∣ s.natAbs * d := by
    have h1 : (r : ℤ) ∣ s * (d : ℤ) := ⟨k, hkr.symm.trans (mul_comm k (r : ℤ))⟩
    have h2 : ((r : ℕ) : ℤ) ∣ ((s.natAbs * d : ℕ) : ℤ) := by
      simpa [Int.natAbs_mul] using Int.dvd_natAbs.2 h1
    exact Int.ofNat_dvd.1 h2
  have hrd : r ∣ d := hcop.symm.dvd_of_dvd_mul_left hdvd
  have hdr : d = r := le_antisymm hd_le (Nat.le_of_dvd hd_pos hrd)
  exact Submodule.eq_top_of_finrank_eq (by simpa [d] using hdr)

end Simplicity

/-! ### Finding a simple standard-block sub-isocrystal -/

section SubBlock

private theorem ringEquiv_toRingHom_apply {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (e : R ≃+* S) (x : R) : e.toRingHom x = e x := by simp

private def shiftVecEquiv (L V : Type*) [Field L] [AddCommGroup V] [Module L V]
    (π : L) (hπ : π ≠ 0) (r : ℕ+) : (Fin r → V) ≃ₗ[L] (Fin r → V) where
  toFun w i := (if (i : ℕ) = 0 then π else 1) • w ((finRotate r).symm i)
  invFun w j := (if (finRotate r j : ℕ) = 0 then π⁻¹ else 1) • w (finRotate r j)
  left_inv w := by
    ext j
    simp only [Equiv.symm_apply_apply]
    split_ifs <;> simp [smul_smul, hπ]
  right_inv w := by
    ext i
    simp only [Equiv.apply_symm_apply]
    split_ifs <;> simp [smul_smul, hπ]
  map_add' x y := by ext i; simp [smul_add]
  map_smul' c x := by ext i; simp [smul_comm c]

private theorem shiftVecEquiv_apply {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    (π : L) (hπ : π ≠ 0) (r : ℕ+) (w : Fin r → V) (i : Fin r) :
    shiftVecEquiv L V π hπ r w i =
      (if (i : ℕ) = 0 then π else 1) • w ((finRotate r).symm i) := rfl

section ShiftIterate

open Fin.NatCast

private theorem shiftVecEquiv_iterate_apply {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    (π : L) (hπ : π ≠ 0) (r : ℕ+) (k : ℕ) (w : Fin r → V) (i : Fin r) :
    (shiftVecEquiv L V π hπ r)^[k] w i =
      (∏ t ∈ Finset.range k, if ((i - (t : Fin r) : Fin r) : ℕ) = 0 then π else 1) •
        w (i - (k : Fin r)) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    have hidx (t : ℕ) : i - 1 - (t : Fin r) = i - ((t + 1 : ℕ) : Fin r) := by
      push_cast; abel
    rw [iterate_succ_apply', shiftVecEquiv_apply, finRotate_symm_apply, ih,
      Finset.prod_range_succ', ← smul_assoc, smul_eq_mul, mul_comm]
    simp only [hidx, Nat.cast_zero, sub_zero]

private theorem shiftVecEquiv_iterate_rank_apply {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] (π : L) (hπ : π ≠ 0) (r : ℕ+) (w : Fin r → V) :
    (shiftVecEquiv L V π hπ r)^[r] w = π • w := by
  ext i
  rw [shiftVecEquiv_iterate_apply, Fin.natCast_self, sub_zero, Pi.smul_apply]
  rw [Finset.prod_eq_single (i : ℕ)]
  · simp
  · intro t ht hti
    rw [ite_eq_right_iff]
    intro h
    rw [Fin.val_eq_zero_iff, sub_eq_zero] at h
    exact (hti (by rw [h, Fin.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 ht)])).elim
  · simp

end ShiftIterate

private theorem shiftVecEquiv_zpow_mul_rank {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] (π : L) (hπ : π ≠ 0) (r : ℕ+) (z : ℤ) (w : Fin r → V) :
    (shiftVecEquiv L V π hπ r ^ ((r : ℤ) * z)) w = π ^ z • w := by
  let E : (Fin r → V) ≃ₗ[L] (Fin r → V) := shiftVecEquiv L V π hπ r ^ (r : ℕ)
  have hE (u : Fin r → V) : E u = π • u := by
    dsimp only [E]
    rw [pow_apply_eq_iterate, shiftVecEquiv_iterate_rank_apply]
  have hE_symm (u : Fin r → V) : E.symm u = π⁻¹ • u :=
    E.symm_apply_eq.2 (by rw [hE, smul_smul, mul_inv_cancel₀ hπ, one_smul])
  rw [zpow_mul, zpow_natCast]
  induction z using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show (k : ℤ) + 1 = 1 + k by ring, zpow_add, zpow_one, mul_apply_eq_comp, ih, hE,
      smul_smul, mul_comm π, ← zpow_add_one₀ hπ, add_comm]
  | pred k ih =>
    rw [show (-k : ℤ) - 1 = -1 + -k by ring, zpow_add, zpow_neg_one, mul_apply_eq_comp, ih,
      show E⁻¹ = E.symm from rfl, hE_symm, smul_smul, mul_comm π⁻¹, ← zpow_sub_one₀ hπ,
      sub_eq_add_neg, add_comm]

private theorem shiftVecEquiv_contract {k : Type*} [Field k] (r : ℕ+) (f : k⸨X⸩) :
    shiftVecEquiv k⸨X⸩ k⸨X⸩ (HahnSeries.single 1 1)
        (HahnSeries.single_ne_zero one_ne_zero) r (_root_.LaurentSeries.contract r f) =
      _root_.LaurentSeries.contract r (HahnSeries.single 1 1 * f) := by
  ext i m
  rw [shiftVecEquiv_apply, _root_.LaurentSeries.coeff_contract, HahnSeries.coeff_single_mul,
    one_mul]
  by_cases hi : (i : ℕ) = 0
  · have hi0 : i = 0 := Fin.ext hi
    subst hi0
    have hrot0 : (finRotate r).symm 0 = ⟨(r : ℕ) - 1, Nat.sub_lt r.pos one_pos⟩ := by
      rw [(finRotate r).symm_apply_eq]
      by_cases hr1 : (r : ℕ) = 1
      · exact Fin.ext (by simp [hr1])
      · apply Fin.ext
        have h1 : ((1 : Fin r) : ℕ) = 1 % (r : ℕ) := rfl
        have hsub_add : (r : ℕ) - 1 + 1 = r := Nat.sub_add_cancel r.pos
        rw [Fin.val_zero, finRotate_apply, Fin.val_add, Fin.val_mk, h1,
          Nat.mod_eq_of_lt (by omega : 1 < (r : ℕ)), hsub_add, Nat.mod_self]
    simp only [Fin.val_zero, ↓reduceIte, smul_eq_mul, HahnSeries.coeff_single_mul, one_mul,
      _root_.LaurentSeries.coeff_contract, hrot0]
    congr 1
    have hsub : (((r : ℕ) - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
    rw [hsub]
    ring
  · have hrot : ((finRotate r).symm i : ℕ) + 1 = i := by
      rw [coe_finRotate_symm_of_ne_zero (Fin.val_ne_zero_iff.1 hi)]
      have : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi
      omega
    simp only [hi, ↓reduceIte, one_smul, _root_.LaurentSeries.coeff_contract]
    congr 1
    omega

private theorem shiftVecEquiv_zpow_contract {k : Type*} [Field k] (r : ℕ+) (z : ℤ)
    (f : k⸨X⸩) :
    (shiftVecEquiv k⸨X⸩ k⸨X⸩ (HahnSeries.single 1 1)
          (HahnSeries.single_ne_zero one_ne_zero) r ^ z)
        (_root_.LaurentSeries.contract r f) =
      _root_.LaurentSeries.contract r (HahnSeries.single z 1 * f) := by
  set S := shiftVecEquiv k⸨X⸩ k⸨X⸩ (HahnSeries.single 1 1)
    (HahnSeries.single_ne_zero one_ne_zero) r
  have hS_symm (g : k⸨X⸩) : S.symm (_root_.LaurentSeries.contract r g) =
      _root_.LaurentSeries.contract r (HahnSeries.single (-1) 1 * g) := by
    rw [LinearEquiv.symm_apply_eq, shiftVecEquiv_contract, ← mul_assoc,
      HahnSeries.single_mul_single, add_neg_cancel, mul_one, HahnSeries.single_zero_one, one_mul]
  induction z using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [show (n : ℤ) + 1 = 1 + n by ring, zpow_add, zpow_one, mul_apply_eq_comp, ih,
      shiftVecEquiv_contract, ← mul_assoc, HahnSeries.single_mul_single, one_mul]
  | pred n ih =>
    rw [show (-n : ℤ) - 1 = -1 + -n by ring, zpow_add, zpow_neg_one, mul_apply_eq_comp, ih,
      show S⁻¹ = S.symm from rfl, hS_symm, ← mul_assoc, HahnSeries.single_mul_single, one_mul]

private noncomputable def companionMatrixMap {k : Type*} [Field k] {p f : ℕ} [Fact p.Prime]
    [CharP k p] [IsAlgClosed k] (n : ℕ) (b₀ : Fin (n + 1) → k) :
    (Fin (n + 1) → k) →ₛₗ[_root_.iterateFrobenius k p f] (Fin (n + 1) → k) where
  toFun d := Fin.cases (b₀ 0 * d (Fin.last n) ^ p ^ f)
    (fun j ↦ d j.castSucc ^ p ^ f + b₀ j.succ * d (Fin.last n) ^ p ^ f)
  map_add' x y := by
    have : ExpChar k p := expChar_prime k p
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
    · simp only [Fin.cases_zero, Fin.cases_succ, Pi.add_apply, add_pow_char_pow]
      ring
  map_smul' c x := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
    · simp only [Fin.cases_zero, Fin.cases_succ, Pi.smul_apply, smul_eq_mul, mul_pow,
        _root_.iterateFrobenius_def]
      ring

private theorem companionMatrixMap_iterate_single_zero {k : Type*} [Field k] {p f : ℕ}
    [Fact p.Prime] [CharP k p] [IsAlgClosed k] (n : ℕ) (b₀ : Fin (n + 1) → k) :
    (companionMatrixMap (p := p) (f := f) n b₀)^[n + 1] (Pi.single 0 1) = b₀ := by
  have hcast : ∀ m (hm : m ≤ n),
      (companionMatrixMap (p := p) (f := f) n b₀)^[m] (Pi.single 0 1) =
        Pi.single ⟨m, Nat.lt_succ_of_le hm⟩ (1 : k) := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [iterate_succ_apply', ih (Nat.le_of_succ_le hm)]
      ext i
      have hne_last :
          (Fin.last n : Fin (n + 1)) ≠ ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩ := by
        simp [Fin.ext_iff]; omega
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · dsimp only [companionMatrixMap, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Fin.cases_zero, Pi.single_eq_of_ne hne_last,
          zero_pow (pow_ne_zero f (Fact.out : p.Prime).ne_zero), mul_zero,
          Pi.single_eq_of_ne (by simp [Fin.ext_iff])]
      · dsimp only [companionMatrixMap, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Fin.cases_succ, Pi.single_eq_of_ne hne_last,
          zero_pow (pow_ne_zero f (Fact.out : p.Prime).ne_zero), mul_zero, add_zero]
        by_cases hj : (j : ℕ) = m
        · have hj1 : j.castSucc = ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩ := Fin.ext hj
          have hj2 : j.succ = ⟨m + 1, Nat.lt_succ_of_le hm⟩ := Fin.ext (by simp [hj])
          rw [hj1, hj2, Pi.single_eq_same, Pi.single_eq_same, one_pow]
        · have hj1 : j.castSucc ≠ ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩ :=
            fun h ↦ hj (congrArg Fin.val h)
          have hj2 : j.succ ≠ ⟨m + 1, Nat.lt_succ_of_le hm⟩ := fun h ↦
            hj (Nat.succ.inj (by simpa [Fin.val_succ] using congrArg Fin.val h))
          rw [Pi.single_eq_of_ne hj1, Pi.single_eq_of_ne hj2,
            zero_pow (pow_ne_zero f (Fact.out : p.Prime).ne_zero)]
  rw [iterate_succ_apply', hcast n le_rfl]
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [companionMatrixMap, Fin.last]
  · simp [companionMatrixMap, Pi.single_apply, Fin.ext_iff, j.isLt.ne,
      zero_pow (pow_ne_zero f (Fact.out : p.Prime).ne_zero)]

private theorem exists_powerSeries_companion_solution {k : Type*} [Field k] {p f : ℕ}
    [Fact p.Prime] [CharP k p] [IsAlgClosed k] (hf : f ≠ 0) (n : ℕ)
    (b : Fin (n + 1) → k⟦X⟧) (hb : ∃ i, PowerSeries.constantCoeff (b i) ≠ 0) :
    ∃ x : Fin (n + 1) → k⟦X⟧,
      (∃ i, x i ≠ 0) ∧
      x 0 = b 0 * PowerSeries.map (_root_.iterateFrobenius k p f) (x (Fin.last n)) ∧
      ∀ j : Fin n, x j.succ = PowerSeries.map (_root_.iterateFrobenius k p f) (x j.castSucc) +
        b j.succ * PowerSeries.map (_root_.iterateFrobenius k p f) (x (Fin.last n)) := by
  have : ExpChar k p := expChar_prime k p
  let σk := _root_.iterateFrobenius k p f
  let b₀ : Fin (n + 1) → k := fun i ↦ PowerSeries.constantCoeff (b i)
  let Ψ := companionMatrixMap (p := p) (f := f) n b₀
  -- Step 1: solve constant term `Ψ d₀ = d₀` (`d₀ ≠ 0`) and set up Artin–Schreier lifting.
  have hΨ_ne : Ψ^[finrank k (Fin (n + 1) → k)] (Pi.single 0 1) ≠ 0 := by
    rw [Module.finrank_pi, Fintype.card_fin, companionMatrixMap_iterate_single_zero]
    exact fun h ↦ hb.choose_spec (congrFun h hb.choose)
  obtain ⟨d₀, hd₀_ne, hd₀_fix⟩ :=
    LinearMap.exists_ne_zero_isFixedPt_of_iterate_ne_zero_iterateFrobenius hf hΨ_ne
  have hsurj := LinearMap.surjective_sub_id_of_iterateFrobenius hf Ψ
  -- Step 2: define coefficients `d t` recursively via Artin–Schreier surjectivity of `Ψ - id`.
  let residual : (t : ℕ) → (∀ u < t, Fin (n + 1) → k) → (Fin (n + 1) → k)
    | 0, _ => 0
    | t + 1, prev => fun i ↦ ∑ u ∈ Finset.range (t + 1),
      (b i).coeff (u + 1) * σk (prev (t - u) (by omega) (Fin.last n))
  let step : (t : ℕ) → (∀ u < t, Fin (n + 1) → k) → (Fin (n + 1) → k)
    | 0, _ => d₀
    | t + 1, prev => Classical.choose (hsurj (-residual (t + 1) prev))
  let d : ℕ → (Fin (n + 1) → k) := WellFounded.fix Nat.lt_wfRel.wf step
  have hd_zero : d 0 = d₀ := WellFounded.fix_eq Nat.lt_wfRel.wf step 0
  have hd_succ (t : ℕ) : Ψ (d (t + 1)) - d (t + 1) = -residual (t + 1) (fun u _ ↦ d u) := by
    have hfix : d (t + 1) = step (t + 1) (fun u _ ↦ d u) :=
      WellFounded.fix_eq Nat.lt_wfRel.wf step (t + 1)
    rw [hfix]
    exact Classical.choose_spec (hsurj (-residual (t + 1) fun u _ ↦ d u))
  -- Step 3: assemble `x i = ∑ d t i X^t` and verify coefficients at `0` and `t + 1`.
  let x : Fin (n + 1) → k⟦X⟧ := fun i ↦ PowerSeries.mk fun t ↦ d t i
  have hmul_coeff (i : Fin (n + 1)) (t : ℕ) :
      (b i * PowerSeries.map σk (x (Fin.last n))).coeff (t + 1) =
        b₀ i * σk (d (t + 1) (Fin.last n)) +
          ∑ u ∈ Finset.range (t + 1), (b i).coeff (u + 1) * σk (d (t - u) (Fin.last n)) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun u v ↦ (b i).coeff u * (PowerSeries.map σk (x (Fin.last n))).coeff v),
      Finset.sum_range_succ']
    simp only [Nat.sub_zero, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_mk, b₀, x]
    rw [add_comm]
    refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun u _ ↦ ?_)
    rw [Nat.add_sub_add_right]
  refine ⟨x, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hd₀_ne
    exact ⟨i, fun hxi ↦ hi (by simpa [x, hd_zero] using congrArg (PowerSeries.coeff 0) hxi)⟩
  · ext t
    rcases t with _ | t
    · rw [PowerSeries.coeff_mk, hd_zero, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply (PowerSeries.map σk _),
        PowerSeries.coeff_map, PowerSeries.coeff_mk, hd_zero]
      simpa [Ψ, companionMatrixMap, b₀, σk, _root_.iterateFrobenius_def] using
        (congrFun hd₀_fix.eq 0).symm
    · have ht := congrFun (hd_succ t) 0
      simp only [Pi.sub_apply, Pi.neg_apply] at ht
      have hdt : d (t + 1) 0 = (Ψ (d (t + 1))) 0 + residual (t + 1) (fun u _ ↦ d u) 0 := by
        linear_combination -ht
      rw [PowerSeries.coeff_mk, hmul_coeff 0 t, hdt]
      simp [Ψ, companionMatrixMap, residual, σk, _root_.iterateFrobenius_def]
  · intro j
    ext t
    rcases t with _ | t
    · rw [PowerSeries.coeff_mk, hd_zero, PowerSeries.coeff_zero_eq_constantCoeff, map_add, map_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply (PowerSeries.map σk (x j.castSucc)),
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply (PowerSeries.map σk (x (Fin.last n))),
        PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
        hd_zero]
      simpa [Ψ, companionMatrixMap, b₀, σk, _root_.iterateFrobenius_def] using
        (congrFun hd₀_fix.eq j.succ).symm
    · have ht := congrFun (hd_succ t) j.succ
      simp only [Pi.sub_apply, Pi.neg_apply] at ht
      have hdt : d (t + 1) j.succ =
          (Ψ (d (t + 1))) j.succ + residual (t + 1) (fun u _ ↦ d u) j.succ := by
        linear_combination -ht
      rw [PowerSeries.coeff_mk, map_add, hmul_coeff j.succ t, hdt]
      simp [Ψ, companionMatrixMap, residual, σk, _root_.iterateFrobenius_def, x, add_assoc]

private theorem exists_min_slope_coeffs {k : Type*} [Field k] {n : ℕ}
    {a : Fin (n + 1) → LaurentSeries k} (ha0 : a 0 ≠ 0) :
    ∃ (s : ℤ) (r : ℕ+), s.natAbs.Coprime r ∧
      ∃ b : Fin (n + 1) → k⟦X⟧,
        (∃ i, PowerSeries.constantCoeff (b i) ≠ 0) ∧
        ∀ i : Fin (n + 1), (b i : LaurentSeries k) =
          HahnSeries.single (-s * (n + 1 - i.val : ℤ)) 1 *
            _root_.LaurentSeries.expand k r (-a i) := by
  classical
  -- Step 1: minimize the Newton-polygon slope `ord(a i) / (n + 1 - i)` over nonzero `a i`.
  let S : Finset (Fin (n + 1)) := Finset.univ.filter fun i ↦ a i ≠ 0
  have hS : S.Nonempty := ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ 0, ha0⟩⟩
  obtain ⟨i₀, hi₀S, hi₀_min⟩ :=
    Finset.exists_min_image S (fun i ↦ ((a i).order : ℚ) / (n + 1 - i.val : ℕ)) hS
  have hi₀_ne : a i₀ ≠ 0 := (Finset.mem_filter.1 hi₀S).2
  set q₀ : ℚ := ((a i₀).order : ℚ) / (n + 1 - i₀.val : ℕ)
  set s : ℤ := q₀.num
  set r : ℕ+ := ⟨q₀.den, q₀.den_pos⟩
  have hq_eq : (s : ℚ) / (r : ℕ) = q₀ := Rat.num_div_den q₀
  have hord_le (i : Fin (n + 1)) (hi : a i ≠ 0) :
      s * (n + 1 - i.val : ℤ) ≤ (r : ℤ) * (a i).order := by
    have hle := hi₀_min i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)
    have hden_pos : (0 : ℚ) < (n + 1 - i.val : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt i.isLt
    have hr_pos : (0 : ℚ) < r := by exact_mod_cast r.pos
    rw [← hq_eq, div_le_div_iff₀ hr_pos hden_pos] at hle
    have hnat : ((n + 1 - i.val : ℕ) : ℤ) = (n : ℤ) + 1 - i.val := by omega
    rw [← hnat]
    exact_mod_cast show (s : ℚ) * ((n + 1 - i.val : ℕ) : ℤ) ≤ (r : ℤ) * (a i).order by
      push_cast; linarith
  have hord_eq : s * (n + 1 - i₀.val : ℤ) = (r : ℤ) * (a i₀).order := by
    have hden_pos : (0 : ℚ) < (n + 1 - i₀.val : ℕ) := by
      exact_mod_cast Nat.sub_pos_of_lt i₀.isLt
    have hr_pos : (0 : ℚ) < r := by exact_mod_cast r.pos
    have h := hq_eq
    rw [div_eq_div_iff hr_pos.ne' hden_pos.ne'] at h
    have hnat : ((n + 1 - i₀.val : ℕ) : ℤ) = (n : ℤ) + 1 - i₀.val := by omega
    rw [← hnat]
    exact_mod_cast show ((s * ((n + 1 - i₀.val : ℕ) : ℤ) : ℤ) : ℚ) =
        (((r : ℤ) * (a i₀).order : ℤ) : ℚ) by
      push_cast; linarith
  -- Step 2: after ramifying by `r` and shifting by `-s * (n + 1 - i)`, entries lie in `k⟦X⟧`.
  let B_ser : Fin (n + 1) → LaurentSeries k := fun i ↦
    HahnSeries.single (-s * (n + 1 - i.val : ℤ)) 1 * _root_.LaurentSeries.expand k r (-a i)
  have hB_mem (i : Fin (n + 1)) : B_ser i ∈ Set.range (HahnSeries.ofPowerSeries ℤ k) := by
    rw [TauCeti.LaurentSeries.mem_range_ofPowerSeries_iff]
    intro m hm
    by_cases hi : a i = 0
    · simp [B_ser, hi]
    · rw [HahnSeries.coeff_single_mul, one_mul]
      apply HahnSeries.coeff_eq_zero_of_lt_order
      rw [_root_.LaurentSeries.order_expand, HahnSeries.order_neg]
      linarith [hord_le i hi]
  choose b hb using hB_mem
  refine ⟨s, r, q₀.reduced, b, ⟨i₀, ?_⟩, fun i ↦ hb i⟩
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h0 : (b i₀ : LaurentSeries k).coeff 0 = (B_ser i₀).coeff 0 :=
    congrArg (fun g : LaurentSeries k ↦ g.coeff 0) (hb i₀)
  rw [PowerSeries.coeff_coe, ite_eq_right (fun h ↦ absurd h (lt_irrefl _)),
    Int.natAbs_zero] at h0
  rw [h0]
  simp only [B_ser, HahnSeries.coeff_single_mul, one_mul, zero_sub, neg_mul, neg_neg]
  have hord_neg : (-a i₀).order = (a i₀).order := HahnSeries.order_neg
  rw [show s * ((n : ℤ) + 1 - i₀.val) = (r : ℤ) * (-a i₀).order by rw [hord_neg, hord_eq],
    _root_.LaurentSeries.coeff_expand_mul]
  exact HahnSeries.coeff_order_eq_zero.not.2 (neg_ne_zero.2 hi₀_ne)

private theorem exists_laurent_companion_solution {p : ℕ} [Fact p.Prime] {f : ℕ+}
    {k : Type*} [Field k] [CharP k p] [IsAlgClosed k] {n : ℕ} (s : ℤ) (r : ℕ+)
    (a : Fin (n + 1) → LaurentSeries k) (b : Fin (n + 1) → k⟦X⟧)
    (hb0 : ∃ i, PowerSeries.constantCoeff (b i) ≠ 0)
    (hb : ∀ i : Fin (n + 1), (b i : LaurentSeries k) =
      HahnSeries.single (-s * (n + 1 - i.val : ℤ)) 1 * _root_.LaurentSeries.expand k r (-a i)) :
    ∃ z : Fin (n + 1) → LaurentSeries k,
      (∃ i, z i ≠ 0) ∧
      HahnSeries.single s 1 * z 0 =
        _root_.LaurentSeries.expand k r (-a 0) * coefficientFrobenius p f k (z (Fin.last n)) ∧
      ∀ j : Fin n, HahnSeries.single s 1 * z j.succ =
        coefficientFrobenius p f k (z j.castSucc) +
          _root_.LaurentSeries.expand k r (-a j.succ) *
            coefficientFrobenius p f k (z (Fin.last n)) := by
  have : ExpChar k p := expChar_prime k p
  let σ := coefficientFrobenius p f k
  -- Step 1: solve the power-series system `x`, then rescale `z i = X ^ (-s * i) * x i`.
  obtain ⟨x, ⟨i₁, hi₁⟩, hx0, hxs⟩ :=
    exists_powerSeries_companion_solution f.ne_zero n b hb0
  let z : Fin (n + 1) → LaurentSeries k :=
    fun i ↦ HahnSeries.single (-s * (i.val : ℤ)) 1 * (x i : LaurentSeries k)
  have hcoe_map (g : k⟦X⟧) :
      ((PowerSeries.map (_root_.iterateFrobenius k p f) g : k⟦X⟧) : LaurentSeries k) =
        σ g := by
    ext m
    by_cases hm : m < 0
    · simp [σ, PowerSeries.coeff_coe, hm, zero_pow (pow_ne_zero f (Fact.out : p.Prime).ne_zero)]
    · simp [σ, PowerSeries.coeff_coe, hm, PowerSeries.coeff_map, _root_.iterateFrobenius_def]
  -- Step 2: check nonvanishing and translate the recurrence for `x` to `z`.
  refine ⟨z, ⟨i₁, mul_ne_zero (HahnSeries.single_ne_zero one_ne_zero)
    ((map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).2 hi₁)⟩, ?_, ?_⟩
  · have hx0' := congrArg (HahnSeries.ofPowerSeries ℤ k) hx0
    rw [map_mul, HahnSeries.ofPowerSeries_apply] at hx0'
    have hx0_coe : (x 0 : LaurentSeries k) = (b 0 : LaurentSeries k) * σ (x (Fin.last n)) := by
      simpa [HahnSeries.ofPowerSeries_apply, hcoe_map] using hx0'
    rw [hb 0] at hx0_coe
    have hx0'' := congrArg (HahnSeries.single s 1 * ·) hx0_coe
    simp only [z, Fin.val_zero, Nat.cast_zero, mul_zero, HahnSeries.single_zero_one, one_mul,
      sub_zero, map_mul, coefficientFrobenius_single, one_pow] at hx0'' ⊢
    rw [hx0'']
    simp only [← mul_assoc, HahnSeries.single_mul_single, one_mul]
    rw [mul_comm (HahnSeries.single (s + -s * (n + 1 : ℤ)) 1), Fin.val_last, mul_assoc,
      show s + -s * (n + 1 : ℤ) = -s * (n : ℤ) by ring, ← mul_assoc]
  · intro j
    have hxs' := congrArg (HahnSeries.ofPowerSeries ℤ k) (hxs j)
    rw [map_add, map_mul] at hxs'
    have hxs_coe : (x j.succ : LaurentSeries k) =
        σ (x j.castSucc) + (b j.succ : LaurentSeries k) * σ (x (Fin.last n)) := by
      simpa [HahnSeries.ofPowerSeries_apply, hcoe_map] using hxs'
    rw [hb j.succ] at hxs_coe
    have hxs'' := congrArg (HahnSeries.single (-s * (j.val : ℤ)) 1 * ·) hxs_coe
    have hlhs : HahnSeries.single s 1 * z j.succ =
        HahnSeries.single (-s * (j.val : ℤ)) 1 * (x j.succ : LaurentSeries k) := by
      simp only [z, Fin.val_succ, Nat.cast_add, Nat.cast_one, ← mul_assoc,
        HahnSeries.single_mul_single, one_mul]
      rw [show s + -s * ((j.val : ℤ) + 1) = -s * (j.val : ℤ) by ring]
    rw [hlhs, hxs'', mul_add]
    congr 1
    · simp [z, Fin.val_castSucc, map_mul, coefficientFrobenius_single]; rfl
    · simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one, map_mul, coefficientFrobenius_single,
        one_pow, z, Fin.val_last, ← mul_assoc, HahnSeries.single_mul_single, one_mul]
      rw [mul_comm (HahnSeries.single _ 1), mul_assoc,
        show -s * (j.val : ℤ) + -s * ((n : ℤ) + 1 - (↑j + 1)) = -s * (n : ℤ) by ring,
        ← mul_assoc]

private theorem shiftVecEquiv_zpow_smulVec {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    (π : L) (hπ : π ≠ 0) (r : ℕ+) (z : ℤ) (g : Fin r → L) (v : V) :
    (shiftVecEquiv L V π hπ r ^ z) (fun l ↦ g l • v) =
      fun l ↦ ((shiftVecEquiv L L π hπ r ^ z) g l) • v := by
  let S_V := shiftVecEquiv L V π hπ r
  let S_L := shiftVecEquiv L L π hπ r
  let smulVec : (Fin r → L) → V → (Fin r → V) := fun g v l ↦ g l • v
  have h1 (g' : Fin r → L) : S_V (smulVec g' v) = smulVec (S_L g') v := by
    ext l; simp only [S_V, S_L, shiftVecEquiv_apply, smulVec, smul_eq_mul, mul_smul]
  induction z using Int.induction_on with
  | zero => simp
  | succ m ih =>
    simp_rw [show (m : ℤ) + 1 = 1 + m by ring, zpow_add, zpow_one, mul_apply_eq_comp]
    rw [ih]
    exact h1 ((S_L ^ (m : ℤ)) g)
  | pred m ih =>
    simp_rw [show (-m : ℤ) - 1 = -1 + -m by ring, zpow_add, zpow_neg_one, mul_apply_eq_comp]
    rw [ih]
    have hinvV : S_V⁻¹ = S_V.symm := rfl
    have hinvL : S_L⁻¹ = S_L.symm := rfl
    rw [hinvV, hinvL, LinearEquiv.symm_apply_eq, h1, LinearEquiv.apply_symm_apply]

private theorem map_pi_comm_shiftVecEquiv_zpow {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[σ.toRingHom] V} (π : L) (hπ : π ≠ 0)
    (hσπ : σ π = π) (r : ℕ+) (z : ℤ) (u : Fin r → V) :
    (fun l ↦ Φ ((shiftVecEquiv L V π hπ r ^ z) u l)) =
      (shiftVecEquiv L V π hπ r ^ z) (fun l ↦ Φ (u l)) := by
  let S_V := shiftVecEquiv L V π hπ r
  let T : (Fin r → V) → (Fin r → V) := fun w l ↦ Φ (w l)
  have h1 (w : Fin r → V) : T (S_V w) = S_V (T w) := by
    ext l
    simp only [T, S_V, shiftVecEquiv_apply]
    split_ifs
    · rw [map_smulₛₗ, ringEquiv_toRingHom_apply, hσπ]
    · simp
  have hsymm (w : Fin r → V) : T (S_V.symm w) = S_V.symm (T w) := by
    rw [LinearEquiv.eq_symm_apply, ← h1, LinearEquiv.apply_symm_apply]
  induction z using Int.induction_on with
  | zero => simp
  | succ m ih =>
    simp_rw [show (m : ℤ) + 1 = 1 + m by ring, zpow_add, zpow_one, mul_apply_eq_comp]
    exact (h1 ((S_V ^ (m : ℤ)) u)).trans (congrArg S_V ih)
  | pred m ih =>
    simp_rw [show (-m : ℤ) - 1 = -1 + -m by ring, zpow_add, zpow_neg_one, mul_apply_eq_comp]
    have hinvV : S_V⁻¹ = S_V.symm := rfl
    rw [hinvV]
    exact (hsymm ((S_V ^ (-m : ℤ)) u)).trans (congrArg S_V.symm ih)

private theorem eigenvector_of_laurent_companion_solution {p : ℕ} [Fact p.Prime] {f : ℕ+}
    {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module (LaurentSeries k) V]
    {Φ : V →ₛₗ[(coefficientFrobenius p f k).toRingHom] V}
    {v₀ : V} {n : ℕ}
    (hli : LinearIndependent (LaurentSeries k) fun i : Fin (n + 1) ↦ Φ^[i.val] v₀)
    {a : Fin (n + 1) → LaurentSeries k}
    (hrel : Φ^[n + 1] v₀ + ∑ i : Fin (n + 1), a i • Φ^[i.val] v₀ = 0)
    (s : ℤ) (r : ℕ+) (z : Fin (n + 1) → LaurentSeries k) (hz_ne : ∃ i, z i ≠ 0)
    (hz0 : HahnSeries.single s 1 * z 0 =
      _root_.LaurentSeries.expand k r (-a 0) * coefficientFrobenius p f k (z (Fin.last n)))
    (hzs : ∀ j : Fin n, HahnSeries.single s 1 * z j.succ =
      coefficientFrobenius p f k (z j.castSucc) +
        _root_.LaurentSeries.expand k r (-a j.succ) *
          coefficientFrobenius p f k (z (Fin.last n))) :
    ∃ w₀ : V, w₀ ≠ 0 ∧
      Φ^[r] w₀ = (HahnSeries.single 1 1 : LaurentSeries k) ^ s • w₀ := by
  let L := LaurentSeries k
  let σ := coefficientFrobenius p f k
  let π : L := HahnSeries.single 1 1
  have hπ : π ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  have hσπ : σ π = π := coefficientFrobenius_single_one 1
  let y : Fin (n + 1) → Fin r → L := fun i l ↦ _root_.LaurentSeries.contract r (z i) l
  let w : Fin r → V := fun l ↦ ∑ i : Fin (n + 1), y i l • Φ^[i.val] v₀
  -- Step 1: pick a coordinate `l₀` with `w l₀ ≠ 0` by linear independence of `Φ^[i] v₀`.
  have hw_ne : ∃ l₀, w l₀ ≠ 0 := by
    obtain ⟨i₁, hi₁⟩ := hz_ne
    have hl₀ : ∃ l₀, y i₁ l₀ ≠ 0 := by
      by_contra! hall
      apply hi₁
      rw [← _root_.LaurentSeries.sum_single_mul_expand_contract r (z i₁)]
      exact Finset.sum_eq_zero fun l _ ↦ by simp [y, hall l]
    obtain ⟨l₀, hl₀⟩ := hl₀
    exact ⟨l₀, fun hw0 ↦
      hl₀ (Fintype.linearIndependent_iff.1 hli (fun i ↦ y i l₀) hw0 i₁)⟩
  obtain ⟨l₀, hl₀⟩ := hw_ne
  let S_V := shiftVecEquiv L V π hπ r
  let smulVec : (Fin r → L) → V → (Fin r → V) := fun g v l ↦ g l • v
  let T : (Fin r → V) → (Fin r → V) := fun u l ↦ Φ (u l)
  -- Step 2: show `Φ` acts coordinatewise on `w` as the shifted vector operator `S_V ^ s`.
  have hTw : T w = (S_V ^ s) w := by
    have hT_eq : T w = ∑ i : Fin (n + 1),
        smulVec (_root_.LaurentSeries.contract r (σ (z i))) (Φ^[i.val + 1] v₀) := by
      ext l
      dsimp only [T, w, smulVec]
      rw [map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smulₛₗ, ringEquiv_toRingHom_apply, ← iterate_succ_apply' Φ]
      dsimp only [y]
      rw [← contract_coefficientFrobenius]
    have hS_eq : (S_V ^ s) w = ∑ i : Fin (n + 1),
        smulVec (_root_.LaurentSeries.contract r (HahnSeries.single s 1 * z i))
          (Φ^[i.val] v₀) := by
      have hw_vec : w = ∑ i : Fin (n + 1), smulVec (y i) (Φ^[i.val] v₀) := by
        ext l; simp [w, smulVec]
      rw [hw_vec, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [shiftVecEquiv_zpow_smulVec π hπ r s (y i) (Φ^[i.val] v₀),
        shiftVecEquiv_zpow_contract r s (z i)]
    have hΦlast : Φ^[n + 1] v₀ = ∑ j : Fin (n + 1), (-a j) • Φ^[j.val] v₀ := by
      rw [eq_neg_of_add_eq_zero_left hrel, ← Finset.sum_neg_distrib]
      simp [neg_smul]
    have hlast_split :
        smulVec (_root_.LaurentSeries.contract r (σ (z (Fin.last n))))
          (∑ j : Fin (n + 1), (-a j) • Φ^[j.val] v₀) =
        ∑ j : Fin (n + 1), smulVec (_root_.LaurentSeries.contract r
          (_root_.LaurentSeries.expand k r (-a j) * σ (z (Fin.last n)))) (Φ^[j.val] v₀) := by
      ext l
      simp only [smulVec, Finset.smul_sum, Finset.sum_apply, smul_smul, mul_comm (-a _),
        _root_.LaurentSeries.contract_expand_mul]
    rw [hT_eq, hS_eq, Fin.sum_univ_castSucc, Fin.val_last, hΦlast, hlast_split, Fin.sum_univ_succ
      (f := fun j : Fin (n + 1) ↦ smulVec (_root_.LaurentSeries.contract r
        (_root_.LaurentSeries.expand k r (-a j) * σ (z (Fin.last n)))) (Φ^[j.val] v₀)),
      Fin.sum_univ_succ (f := fun j : Fin (n + 1) ↦
        smulVec (_root_.LaurentSeries.contract r (HahnSeries.single s 1 * z j)) (Φ^[j.val] v₀)),
      add_left_comm, ← Finset.sum_add_distrib]
    congr 1
    · rw [Fin.val_zero, hz0]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      ext l
      simp only [smulVec, Pi.add_apply, ← add_smul, Fin.val_castSucc, Fin.val_succ]
      rw [← _root_.LaurentSeries.contract_add, ← hzs j]
  -- Step 3: iterate `r` times; since `S_V ^ (r * s) = π ^ s • id`, `w l₀` is an eigenvector.
  have hcomm : Function.Commute T ⇑(S_V ^ s) :=
    fun u ↦ map_pi_comm_shiftVecEquiv_zpow π hπ hσπ r s u
  have hTiter : ∀ m : ℕ, T^[m] w = (S_V ^ s)^[m] w := fun m ↦ by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [iterate_succ_apply', ih, hcomm.iterate_right m w, hTw, ← iterate_succ_apply]
  have hT_coord (m : ℕ) (l : Fin r) : T^[m] w l = Φ^[m] (w l) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [iterate_succ_apply']
      dsimp only [T]
      rw [ih, ← iterate_succ_apply' Φ]
  refine ⟨w l₀, hl₀, ?_⟩
  have hr_eq := congrFun (hTiter r) l₀
  rw [hT_coord r l₀, ← pow_apply_eq_iterate (S_V ^ s) (r : ℕ), ← zpow_natCast, ← zpow_mul,
    mul_comm s (r : ℤ), shiftVecEquiv_zpow_mul_rank] at hr_eq
  exact hr_eq

private theorem exists_eigenvector_of_minimal_relation {p : ℕ} [Fact p.Prime] {f : ℕ+}
    {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module (LaurentSeries k) V]
    {Φ : V →ₛₗ[(coefficientFrobenius p f k).toRingHom] V}
    {v₀ : V} {n : ℕ}
    (hli : LinearIndependent (LaurentSeries k) fun i : Fin (n + 1) ↦ Φ^[i.val] v₀)
    {a : Fin (n + 1) → LaurentSeries k}
    (hrel : Φ^[n + 1] v₀ + ∑ i : Fin (n + 1), a i • Φ^[i.val] v₀ = 0) (ha0 : a 0 ≠ 0) :
    ∃ (s : ℤ) (r : ℕ+), s.natAbs.Coprime r ∧ ∃ w₀ : V, w₀ ≠ 0 ∧
      Φ^[r] w₀ = (HahnSeries.single 1 1 : LaurentSeries k) ^ s • w₀ := by
  obtain ⟨s, r, hcop, b, hb0, hb⟩ := exists_min_slope_coeffs ha0
  obtain ⟨z, hz_ne, hz0, hzs⟩ :=
    exists_laurent_companion_solution (p := p) (f := f) s r a b hb0 hb
  obtain ⟨w₀, hw₀, hΦw₀⟩ :=
    eigenvector_of_laurent_companion_solution hli hrel s r z hz_ne hz0 hzs
  exact ⟨s, r, hcop, w₀, hw₀, hΦw₀⟩

/-- Standard basis vector `e_j` with `j + 1 ≠ r` maps to `e_(j+1)` under
`standardBlockFrobenius`. -/
theorem standardBlockFrobenius_single_of_val_add_one_ne {L : Type*} [Field L] {σ : L ≃+* L}
    {π : L} {s : ℤ} {r : ℕ+} {j : Fin r} (hj : j.val + 1 ≠ r) :
    standardBlockFrobenius σ π s r (Pi.single j 1) = Pi.single (finRotate r j) 1 := by
  have hrot_val : (finRotate r j : ℕ) = j.val + 1 := by
    have hlt : j.val + 1 < (r : ℕ) := lt_of_le_of_ne j.isLt hj
    have h1 : ((1 : Fin r) : ℕ) = 1 % (r : ℕ) := rfl
    rw [finRotate_apply, Fin.val_add, h1, Nat.mod_eq_of_lt (by omega : 1 < (r : ℕ)),
      Nat.mod_eq_of_lt hlt]
  ext l
  rw [standardBlockFrobenius_apply]
  by_cases h1 : (finRotate r).symm l = j
  · have hl : l = finRotate r j := (finRotate r).symm_apply_eq.1 h1
    have hl0 : (l : ℕ) ≠ 0 := by rw [hl, hrot_val]; omega
    rw [h1, Pi.single_eq_same, ite_eq_right hl0, hl, Pi.single_eq_same, map_one, mul_one]
  · have hl : l ≠ finRotate r j := fun h ↦ h1 ((finRotate r).symm_apply_eq.2 h)
    rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne hl, map_zero, mul_zero]

/-- The last standard basis vector `e_(r-1)` maps to `π ^ s • e_0` under
`standardBlockFrobenius`. -/
theorem standardBlockFrobenius_single_of_val_add_one_eq {L : Type*} [Field L] {σ : L ≃+* L}
    {π : L} {s : ℤ} {r : ℕ+} {j : Fin r} (hj : j.val + 1 = r) :
    standardBlockFrobenius σ π s r (Pi.single j 1) = π ^ s • Pi.single (finRotate r j) 1 := by
  have hrot : finRotate r j = 0 := by
    apply Fin.ext
    by_cases hr1 : (r : ℕ) = 1
    · have := (finRotate r j).isLt; omega
    · have h1 : ((1 : Fin r) : ℕ) = 1 % (r : ℕ) := rfl
      rw [finRotate_apply, Fin.val_add, h1, Nat.mod_eq_of_lt (by omega : 1 < (r : ℕ)), hj,
        Nat.mod_self]
      rfl
  ext l
  rw [hrot, standardBlockFrobenius_apply]
  by_cases h1 : (finRotate r).symm l = j
  · have hl : l = 0 := hrot ▸ (finRotate r).symm_apply_eq.1 h1
    have hl0 : (l : ℕ) = 0 := by rw [hl, Fin.val_zero]
    rw [h1, Pi.single_eq_same, ite_eq_left hl0, hl, Pi.smul_apply, Pi.single_eq_same, map_one,
      mul_one, smul_eq_mul, mul_one]
  · have hl : l ≠ 0 := fun h ↦ h1 ((finRotate r).symm_apply_eq.2 (h.trans hrot.symm))
    rw [Pi.single_eq_of_ne h1, Pi.smul_apply, Pi.single_eq_of_ne hl, map_zero, mul_zero,
      smul_zero]

private noncomputable def cyclicBlockHom {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    {σ : L ≃+* L} {Φ : V →ₛₗ[σ.toRingHom] V} {r : ℕ+}
    (v₀ : V) : (Fin r → L) →ₗ[L] V where
  toFun x := ∑ j : Fin r, x j • Φ^[j.val] v₀
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

private theorem cyclicBlockHom_apply_single {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[σ.toRingHom] V} {r : ℕ+}
    (v₀ : V) (j : Fin r) :
    cyclicBlockHom (σ := σ) (Φ := Φ) (r := r) v₀ (Pi.single j 1) = Φ^[j.val] v₀ := by
  simp [cyclicBlockHom, Pi.single_apply]

private theorem cyclicBlockHom_intertwines {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    {σ : L ≃+* L} {Φ : V →ₛₗ[σ.toRingHom] V} {π : L} {s : ℤ} {r : ℕ+} {v₀ : V}
    (hv₀ : Φ^[r] v₀ = π ^ s • v₀) (x : Fin r → L) :
    cyclicBlockHom (σ := σ) (Φ := Φ) (r := r) v₀ (standardBlockFrobenius σ π s r x) =
      Φ (cyclicBlockHom (σ := σ) (Φ := Φ) (r := r) v₀ x) := by
  have hbasis (j : Fin r) :
      cyclicBlockHom (σ := σ) (Φ := Φ) (r := r) v₀
          (standardBlockFrobenius σ π s r (Pi.single j 1)) =
        Φ (cyclicBlockHom (σ := σ) (Φ := Φ) (r := r) v₀ (Pi.single j 1)) := by
    by_cases hj : j.val + 1 = r
    · have hrot : finRotate r j = 0 := by
        apply Fin.ext
        by_cases hr1 : (r : ℕ) = 1
        · have := (finRotate r j).isLt; omega
        · have h1 : ((1 : Fin r) : ℕ) = 1 % (r : ℕ) := rfl
          rw [finRotate_apply, Fin.val_add, h1, Nat.mod_eq_of_lt (by omega : 1 < (r : ℕ)), hj,
            Nat.mod_self]
          rfl
      rw [standardBlockFrobenius_single_of_val_add_one_eq hj, map_smul,
        cyclicBlockHom_apply_single, cyclicBlockHom_apply_single, hrot, Fin.val_zero, iterate_zero,
        id_eq, ← iterate_succ_apply' Φ, Nat.succ_eq_add_one, hj, hv₀]
    · have hrot_val : (finRotate r j : ℕ) = j.val + 1 := by
        have hlt : j.val + 1 < (r : ℕ) := lt_of_le_of_ne j.isLt hj
        have h1 : ((1 : Fin r) : ℕ) = 1 % (r : ℕ) := rfl
        rw [finRotate_apply, Fin.val_add, h1, Nat.mod_eq_of_lt (by omega : 1 < (r : ℕ)),
          Nat.mod_eq_of_lt hlt]
      rw [standardBlockFrobenius_single_of_val_add_one_ne hj, cyclicBlockHom_apply_single,
        cyclicBlockHom_apply_single, hrot_val, ← iterate_succ_apply' Φ]
  have hx : x = ∑ j : Fin r, x j • Pi.single j (1 : L) := by
    ext l; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx, map_sum, map_sum]
  conv_rhs => rw [hx, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smulₛₗ, map_smul, map_smul, map_smulₛₗ, RingHom.coe_coe,
    ringEquiv_toRingHom_apply, hbasis j]

private theorem exists_minimal_orbit_relation {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] [FiniteDimensional L V] {σ : L ≃+* L} {Φ : V →ₛₗ[σ.toRingHom] V}
    (hΦ : Injective Φ) {v₀ : V} (hv₀ : v₀ ≠ 0) :
    ∃ (n : ℕ) (a : Fin (n + 1) → L),
      LinearIndependent L (fun i : Fin (n + 1) ↦ Φ^[i.val] v₀) ∧
      Φ^[n + 1] v₀ + ∑ i : Fin (n + 1), a i • Φ^[i.val] v₀ = 0 ∧
      a 0 ≠ 0 := by
  obtain ⟨n, hli, hmem⟩ := Function.exists_linearIndependent_iterate_mem_span (K := L) Φ hv₀
  have hneg :
      -Φ^[n + 1] v₀ ∈ Submodule.span L (Set.range fun i : Fin (n + 1) ↦ Φ^[i.val] v₀) :=
    Submodule.neg_mem _ hmem
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hneg
  obtain ⟨c, hc⟩ := hneg
  let a : Fin (n + 1) → L := fun i ↦ c i
  have hrel : Φ^[n + 1] v₀ + ∑ i : Fin (n + 1), a i • Φ^[i.val] v₀ = 0 := by
    rw [Finsupp.sum_fintype c (fun i x ↦ x • Φ^[i.val] v₀) (fun i ↦ zero_smul L _)] at hc
    dsimp only [a]
    rw [hc, add_neg_cancel]
  refine ⟨n, a, hli, hrel, fun ha0 ↦ ?_⟩
  have hsplit : ∑ i : Fin (n + 1), a i • Φ^[i.val] v₀ =
      ∑ j : Fin n, a j.succ • Φ^[j.val + 1] v₀ := by
    rw [Fin.sum_univ_succ, ha0, zero_smul, zero_add]
    rfl
  have hΦeq : Φ (Φ^[n] v₀ + ∑ j : Fin n, σ.symm (a j.succ) • Φ^[j.val] v₀) = 0 := by
    rw [map_add, map_sum, ← iterate_succ_apply' Φ]
    have hsum : (∑ j : Fin n, Φ (σ.symm (a j.succ) • Φ^[j.val] v₀)) =
        ∑ j : Fin n, a j.succ • Φ^[j.val + 1] v₀ := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_smulₛₗ, ringEquiv_toRingHom_apply, σ.apply_symm_apply,
        ← iterate_succ_apply' Φ]
    rw [hsum, ← hsplit]
    exact hrel
  have hinner : Φ^[n] v₀ + ∑ j : Fin n, σ.symm (a j.succ) • Φ^[j.val] v₀ = 0 :=
    hΦ (hΦeq.trans (map_zero Φ).symm)
  let c' : Fin (n + 1) → L := Fin.snoc (fun j : Fin n ↦ σ.symm (a j.succ)) 1
  have hsum' : ∑ i : Fin (n + 1), c' i • Φ^[i.val] v₀ = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [c', Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, one_smul]
    rw [add_comm, hinner]
  have hc' := Fintype.linearIndependent_iff.1 hli c' hsum' (Fin.last n)
  simp [c'] at hc'

/-- **Existence of a simple standard-block sub-isocrystal.** Every nontrivial finite isocrystal
`(V, Φ)` over `k((π))` contains a coprime cyclic block `D(s, r)` via a Frobenius-equivariant
`k((π))`-linear embedding. -/
theorem exists_inj_intertwines_standardBlock {p : ℕ} [Fact p.Prime] {f : ℕ+}
    {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module (LaurentSeries k) V]
    [FiniteDimensional (LaurentSeries k) V] [Nontrivial V]
    {Φ : V →ₛₗ[(coefficientFrobenius p f k).toRingHom] V} (hΦ : Bijective Φ) :
    ∃ (s : ℤ) (r : ℕ+), s.natAbs.Coprime r ∧
      ∃ ι : (Fin r → LaurentSeries k) →ₗ[LaurentSeries k] V,
        Injective ι ∧
        ∀ x, ι (standardBlockFrobenius (coefficientFrobenius p f k)
          (HahnSeries.single 1 1) s r x) = Φ (ι x) := by
  have : ExpChar k p := expChar_prime k p
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨n, a, hli, hrel, ha0⟩ := exists_minimal_orbit_relation hΦ.injective hv₀
  obtain ⟨s, r, hcop, w₀, hw₀, hΦw₀⟩ :=
    exists_eigenvector_of_minimal_relation hli hrel ha0
  let ι := cyclicBlockHom (σ := coefficientFrobenius p f k) (Φ := Φ) (r := r) w₀
  have hinter : ∀ x, ι (standardBlockFrobenius (coefficientFrobenius p f k)
      (HahnSeries.single 1 1) s r x) = Φ (ι x) :=
    fun x ↦ cyclicBlockHom_intertwines hΦw₀ x
  have hstab : ∀ x ∈ LinearMap.ker ι,
      standardBlockFrobenius (coefficientFrobenius p f k) (HahnSeries.single 1 1) s r x ∈
        LinearMap.ker ι := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hinter x, hx, map_zero]
  have hker_ne_top : LinearMap.ker ι ≠ ⊤ := by
    intro htop
    have hmem : Pi.single 0 1 ∈ LinearMap.ker ι := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, cyclicBlockHom_apply_single, Fin.val_zero, iterate_zero, id_eq] at hmem
    exact hw₀ hmem
  have hvπ : Valued.v (HahnSeries.single (1 : ℤ) (1 : k)) ≠ 1 := by
    simp [_root_.LaurentSeries.valuation_single_zpow]
  have hgen : ∀ x : LaurentSeries k, x ≠ 0 →
      ∃ n : ℤ, Valued.v x = Valued.v (HahnSeries.single (1 : ℤ) (1 : k)) ^ n := by
    intro x hx
    refine ⟨x.order, ?_⟩
    rw [TauCeti.LaurentSeries.valuation_eq_exp_neg_order hx,
      _root_.LaurentSeries.valuation_single_zpow, ← WithZero.exp_zsmul, zsmul_eq_mul, mul_neg_one]
    rfl
  have hker_bot : LinearMap.ker ι = ⊥ :=
    (eq_bot_or_eq_top_of_standardBlockFrobenius_stable (coefficientFrobenius p f k)
      (HahnSeries.single 1 1) (HahnSeries.single_ne_zero one_ne_zero)
      (coefficientFrobenius_single_one 1) Valued.v valuation_coefficientFrobenius hvπ hgen
      hcop hstab).resolve_right hker_ne_top
  exact ⟨s, r, hcop, ι, LinearMap.ker_eq_bot.1 hker_bot, hinter⟩

end SubBlock

end TauCeti
