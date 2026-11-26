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
public import TauCeti.RingTheory.Isocrystal.CyclicBlock
public import TauCeti.RingTheory.Isocrystal.StandardBlock
import Mathlib.Data.Rat.Lemmas
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic
import TauCeti.LinearAlgebra.FiniteDimensional.Semilinear

/-!
# Equal-characteristic Dieudonné–Manin classification

Over `L = k((π))` with `k` an algebraically closed field of characteristic `p > 0` and
`σ = coefficientFrobenius p f k` the arithmetic `p^f`-Frobenius acting on coefficients and fixing
`π = X`, every finite isocrystal `(V, Φ)` admits a basis decomposed into simple standard blocks
`D(s, r)` of coprime slopes `s / r`, and the resulting multiset of block slopes is unique.

## Main definitions

* `TauCeti.CyclicSlopeDecomposition`: a basis of `V` partitioned into coprime standard blocks
  `D(s, r)`.
* `TauCeti.CyclicSlopeDecomposition.slopes`: the multiset of slopes `s / r` of the blocks.

## Main results

* `TauCeti.CyclicSlopeDecomposition.exists`: every finite isocrystal over `k((π))` admits a coprime
  cyclic slope decomposition.
* `TauCeti.CyclicSlopeDecomposition.slopes_eq_of_valuation`: uniqueness of the slope multiset for
  arbitrary valued fields `(L, σ, π, v)`.
* `TauCeti.dieudonneManinEqualChar`: existence and slope uniqueness for finite isocrystals over
  `k((π))`.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §8.2.3.
* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004), §§4.1–4.5.
-/

public section

open Finset Function Module
open scoped LaurentSeries

namespace TauCeti

/-! ### Slope decompositions and splitting of extensions -/

section Splitting

/-- A basis of `V` partitioned into coprime cyclic Frobenius blocks `D(s, r)`.
The last vector of each block maps to `π ^ s` times its first vector. -/
structure CyclicSlopeDecomposition {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    {σ : L ≃+* L} (Φ : V →ₛₗ[σ.toRingHom] V) (π : L) where
  blocks : ℕ
  rank : Fin blocks → ℕ+
  exponent : Fin blocks → ℤ
  coprime : ∀ i, (exponent i).natAbs.Coprime (rank i)
  basis : Module.Basis (Σ i, Fin (rank i)) L V
  frobenius_basis : ∀ i j, Φ (basis ⟨i, j⟩) =
    (if j.val + 1 = rank i then π ^ exponent i else 1) •
      basis ⟨i, finRotate (rank i) j⟩

/-- The multiset of simple-block slopes, counting each block once. -/
def CyclicSlopeDecomposition.slopes {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[σ.toRingHom] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) : Multiset ℚ :=
  (List.ofFn fun i ↦ (D.exponent i : ℚ) / (D.rank i : ℕ) : List ℚ)

/-- The number of slopes in a decomposition equals the number of blocks. -/
@[simp]
theorem CyclicSlopeDecomposition.card_slopes {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[σ.toRingHom] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) :
    D.slopes.card = D.blocks := by
  simp [CyclicSlopeDecomposition.slopes]

/-- The multiplicity of `q` in `D.slopes` equals the number of blocks of slope `q`. -/
theorem CyclicSlopeDecomposition.count_slopes {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[σ.toRingHom] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) (q : ℚ) :
    D.slopes.count q =
      (Finset.univ.filter fun i : Fin D.blocks ↦
        (D.exponent i : ℚ) / (D.rank i : ℕ) = q).card := by
  rw [CyclicSlopeDecomposition.slopes, Multiset.coe_count, List.count_ofFn]

/-- The ranks of the blocks in a cyclic slope decomposition sum to the dimension of `V`. -/
theorem CyclicSlopeDecomposition.sum_rank_eq_finrank {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[σ.toRingHom] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) :
    (∑ i : Fin D.blocks, (D.rank i : ℕ)) = Module.finrank L V := by
  rw [Module.finrank_eq_card_basis D.basis, Fintype.card_sigma]
  simp

private theorem ringEquiv_toRingHom_apply {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (e : R ≃+* S) (x : R) : e.toRingHom x = e x := by simp

private theorem bijective_semilinear_symm_add {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    {τ : L →+* L} (Φ : V →ₛₗ[τ] V) (hΦ : Bijective Φ) (x y : V) :
    (Equiv.ofBijective Φ hΦ).symm (x + y) =
      (Equiv.ofBijective Φ hΦ).symm x + (Equiv.ofBijective Φ hΦ).symm y := by
  let e := Equiv.ofBijective Φ hΦ
  apply e.injective
  rw [e.apply_symm_apply, Equiv.ofBijective_apply, map_add, ← Equiv.ofBijective_apply Φ hΦ,
    ← Equiv.ofBijective_apply Φ hΦ, e.apply_symm_apply, e.apply_symm_apply]

private theorem bijective_semilinear_symm_smul {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    {σ : L ≃+* L} {τ : L →+* L} (hτ : τ = (σ : L →+* L)) (Φ : V →ₛₗ[τ] V)
    (hΦ : Bijective Φ) (c : L) (x : V) :
    (Equiv.ofBijective Φ hΦ).symm (c • x) =
      σ.symm c • (Equiv.ofBijective Φ hΦ).symm x := by
  let e := Equiv.ofBijective Φ hΦ
  apply e.injective
  have hτc : τ (σ.symm c) = σ (σ.symm c) := congrArg (fun f ↦ f (σ.symm c)) hτ
  rw [e.apply_symm_apply, Equiv.ofBijective_apply, map_smulₛₗ, hτc,
    σ.apply_symm_apply, ← Equiv.ofBijective_apply Φ hΦ, e.apply_symm_apply]

private noncomputable def semilinearConjAddHom {L V₁ V₂ : Type*} [Field L]
    [AddCommGroup V₁] [Module L V₁] [AddCommGroup V₂] [Module L V₂] {σ : L ≃+* L}
    (Φ₁ : V₁ →ₛₗ[(σ : L →+* L)] V₁) (hΦ₁ : Bijective Φ₁)
    (Φ₂ : V₂ →ₛₗ[(σ : L →+* L)] V₂) :
    (V₁ →ₗ[L] V₂) →+ (V₁ →ₗ[L] V₂) where
  toFun h :=
    { toFun x := Φ₂ (h ((Equiv.ofBijective Φ₁ hΦ₁).symm x))
      map_add' x y := by rw [bijective_semilinear_symm_add Φ₁ hΦ₁, map_add, map_add]
      map_smul' c x := by
        rw [bijective_semilinear_symm_smul rfl Φ₁ hΦ₁, map_smul, map_smulₛₗ,
          RingHom.coe_coe, σ.apply_symm_apply]
        rfl }
  map_zero' := by ext; exact map_zero Φ₂
  map_add' _ _ := by ext; exact map_add Φ₂ _ _

private theorem semilinearConjAddHom_apply {L V₁ V₂ : Type*} [Field L]
    [AddCommGroup V₁] [Module L V₁] [AddCommGroup V₂] [Module L V₂] {σ : L ≃+* L}
    (Φ₁ : V₁ →ₛₗ[(σ : L →+* L)] V₁) (hΦ₁ : Bijective Φ₁)
    (Φ₂ : V₂ →ₛₗ[(σ : L →+* L)] V₂) (h : V₁ →ₗ[L] V₂) (x : V₁) :
    semilinearConjAddHom Φ₁ hΦ₁ Φ₂ h x =
      Φ₂ (h ((Equiv.ofBijective Φ₁ hΦ₁).symm x)) :=
  rfl

private theorem semilinearConjAddHom_iterate {L V₁ V₂ : Type*} [Field L]
    [AddCommGroup V₁] [Module L V₁] [AddCommGroup V₂] [Module L V₂] {σ : L ≃+* L}
    (Φ₁ : V₁ →ₛₗ[(σ : L →+* L)] V₁) (hΦ₁ : Bijective Φ₁)
    (Φ₂ : V₂ →ₛₗ[(σ : L →+* L)] V₂) (m : ℕ) (h : V₁ →ₗ[L] V₂) (x : V₁) :
    ((semilinearConjAddHom Φ₁ hΦ₁ Φ₂)^[m] h) x =
      Φ₂^[m] (h ((Equiv.ofBijective Φ₁ hΦ₁).symm^[m] x)) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [iterate_succ_apply', semilinearConjAddHom_apply, ih, ← iterate_succ_apply' Φ₂,
      ← iterate_succ_apply]

private theorem equivariant_symm_iterate {α : Type*} (e : α ≃ α) (m : ℕ) (x : α) :
    e.symm^[m] (e^[m] x) = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [iterate_succ_apply, iterate_succ_apply', e.symm_apply_apply, ih]

private theorem surjective_hom_standardBlockFrobenius_sub_id {p : ℕ} [Fact p.Prime] {f : ℕ}
    (hf : f ≠ 0) {k : Type*} [Field k] [CharP k p] [IsAlgClosed k] (s s' : ℤ) (r r' : ℕ+) :
    ∀ u : (Fin r' → LaurentSeries k) →ₗ[LaurentSeries k] (Fin r → LaurentSeries k),
      ∃ h : (Fin r' → LaurentSeries k) →ₗ[LaurentSeries k] (Fin r → LaurentSeries k),
        ∀ x, standardBlockFrobenius (coefficientFrobenius p f k)
            (HahnSeries.single 1 1) s r (h x) -
          h (standardBlockFrobenius (coefficientFrobenius p f k)
            (HahnSeries.single 1 1) s' r' x) =
          u (standardBlockFrobenius (coefficientFrobenius p f k)
            (HahnSeries.single 1 1) s' r' x) := by
  have : ExpChar k p := expChar_prime k p
  let L := LaurentSeries k
  let σ : L ≃+* L := coefficientFrobenius p f k
  let π : L := HahnSeries.single 1 1
  have hπ : π ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  have hσπ : σ π = π := coefficientFrobenius_single_one 1
  let Φ := standardBlockFrobenius σ π s r
  let Φ' := standardBlockFrobenius σ π s' r'
  have hΦ' : Bijective Φ' := standardBlockFrobenius_bijective hπ
  let e := Equiv.ofBijective Φ' hΦ'
  let T := semilinearConjAddHom (σ := σ) Φ' hΦ' Φ
  let N : ℕ+ := r * r'
  let d : ℤ := s * (r' : ℤ) - s' * (r : ℤ)
  -- Step 1: compute the `N`-th iterate `T^[N]` entrywise as `X^d * σ^[N]`.
  have he_symm (j : Fin r') :
      e.symm^[N] (Pi.single j (1 : L)) = π ^ (-(s' * (r : ℤ))) • Pi.single j 1 := by
    have hfwd : e^[N] (π ^ (-(s' * (r : ℤ))) • Pi.single j (1 : L)) = Pi.single j 1 := by
      refine funext fun l ↦ ?_
      have hN_eq : (N : ℕ) = (r' : ℕ) * (r : ℕ) := mul_comm (r : ℕ) (r' : ℕ)
      have hiter : e^[N] (π ^ (-(s' * (r : ℤ))) • Pi.single j (1 : L)) =
          Φ'^[r' * r] (π ^ (-(s' * (r : ℤ))) • Pi.single j 1) := by
        rw [← hN_eq]; rfl
      dsimp only [Φ'] at hiter
      rw [hiter, standardBlockFrobenius_iterate_rank_mul_apply hσπ]
      have hσπz : σ^[r' * r] (π ^ (-(s' * (r : ℤ)))) = π ^ (-(s' * (r : ℤ))) :=
        iterate_fixed (by rw [map_zpow₀, hσπ]) _
      rw [Pi.smul_apply, smul_eq_mul, iterate_map_mul, hσπz, zpow_neg]
      by_cases hj : l = j
      · subst hj; simp [mul_inv_cancel₀ (zpow_ne_zero _ hπ)]
      · simp [hj]
    have hinv := equivariant_symm_iterate e N (π ^ (-(s' * (r : ℤ))) • Pi.single j 1)
    rwa [hfwd] at hinv
  have hTN (h₀ : (Fin r' → L) →ₗ[L] (Fin r → L)) (j : Fin r') (i : Fin r) :
      (T^[N] h₀) (Pi.single j 1) i =
        HahnSeries.single d 1 * σ^[N] (h₀ (Pi.single j 1) i) := by
    dsimp only [T]
    rw [semilinearConjAddHom_iterate, he_symm, map_smul,
      show (N : ℕ) = (r : ℕ) * (r' : ℕ) from rfl]
    dsimp only [Φ]
    rw [standardBlockFrobenius_iterate_rank_mul_apply hσπ]
    have hσπz : σ^[r * r'] (π ^ (-(s' * (r : ℤ)))) = π ^ (-(s' * (r : ℤ))) :=
      iterate_fixed (by rw [map_zpow₀, hσπ]) _
    rw [Pi.smul_apply, smul_eq_mul, iterate_map_mul, hσπz]
    have hsingle : (HahnSeries.single d (1 : k) : L) =
        π ^ (s * (r' : ℤ)) * π ^ (-(s' * (r : ℤ))) := by
      rw [← zpow_add₀ hπ]
      dsimp only [π, d]
      rw [← TauCeti.LaurentSeries.val_unitX, ← Units.val_zpow_eq_zpow_val,
        TauCeti.LaurentSeries.val_unitX_zpow, sub_eq_add_neg]
    rw [hsingle]
    ring
  -- Step 2: solve `(T^[N] - id) k₀ = u` entrywise, then telescope `h = ∑ m < N, T^[m] k₀`.
  intro u
  choose k_coeff hk_coeff using fun (j : Fin r') (i : Fin r) ↦
    surjective_iterate_coefficientFrobenius_sub (p := p) hf N d (u (Pi.single j 1) i)
  let k₀ : (Fin r' → L) →ₗ[L] (Fin r → L) :=
    (Pi.basisFun L (Fin r')).constr L fun j i ↦ k_coeff j i
  have hkN : T^[N] k₀ - k₀ = u := by
    refine (Pi.basisFun L (Fin r')).ext fun j ↦ funext fun i ↦ ?_
    rw [LinearMap.sub_apply, Pi.sub_apply, Pi.basisFun_apply, hTN]
    dsimp only [k₀]
    rw [← Pi.basisFun_apply L (Fin r') j, Basis.constr_basis]
    simpa [σ] using hk_coeff j i
  let h : (Fin r' → L) →ₗ[L] (Fin r → L) := ∑ m ∈ Finset.range N, T^[m] k₀
  have hTh : T h - h = u := by
    have hmap : T h = ∑ m ∈ Finset.range N, T^[m + 1] k₀ := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ ↦ (iterate_succ_apply' T m k₀).symm
    rw [hmap, ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun m ↦ T^[m] k₀), iterate_zero,
      id_eq, hkN]
  refine ⟨h, fun x ↦ ?_⟩
  have hx := LinearMap.congr_fun hTh (Φ' x)
  rw [LinearMap.sub_apply] at hx
  dsimp only [T] at hx
  have heq : (Equiv.ofBijective (⇑Φ') hΦ').symm (Φ' x) = x := e.symm_apply_apply x
  rw [semilinearConjAddHom_apply, heq] at hx
  exact hx

private theorem cyclicSlopeDecomposition_intertwiner {L V : Type*} [Field L]
    [AddCommGroup V] [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[σ.toRingHom] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) (b : Fin D.blocks) :
    let e_b : (Fin (D.rank b) → L) →ₗ[L] V :=
      (Pi.basisFun L (Fin (D.rank b))).constr L fun j ↦ D.basis ⟨b, j⟩
    ∀ z, e_b (standardBlockFrobenius σ π (D.exponent b) (D.rank b) z) = Φ (e_b z) := by
  intro e_b z
  have hbasis (j : Fin (D.rank b)) :
      e_b (standardBlockFrobenius σ π (D.exponent b) (D.rank b) (Pi.single j 1)) =
        Φ (e_b (Pi.single j 1)) := by
    have he_b (l : Fin (D.rank b)) : e_b (Pi.single l 1) = D.basis ⟨b, l⟩ := by
      rw [← Pi.basisFun_apply L (Fin (D.rank b)), Basis.constr_basis]
    by_cases hj : j.val + 1 = D.rank b
    · rw [standardBlockFrobenius_single_of_val_add_one_eq hj, map_smul, he_b, he_b,
        D.frobenius_basis]
      simp [hj]
    · rw [standardBlockFrobenius_single_of_val_add_one_ne hj, he_b, he_b, D.frobenius_basis]
      simp [hj]
  have hz : z = ∑ j : Fin (D.rank b), z j • Pi.single j (1 : L) := by
    ext l; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hz, map_sum, map_sum]
  conv_rhs => rw [hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smulₛₗ, map_smul, map_smul, map_smulₛₗ, RingHom.coe_coe,
    ringEquiv_toRingHom_apply, hbasis j]

private noncomputable def semilinearQuotientMap {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {σ : L ≃+* L} (Φ : V →ₛₗ[σ.toRingHom] V) (W : Submodule L V)
    (hW : ∀ w ∈ W, Φ w ∈ W) : (V ⧸ W) →ₛₗ[σ.toRingHom] (V ⧸ W) :=
  W.liftQ (W.mkQ.comp Φ) fun w hw ↦ by
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hW w hw

private theorem semilinearQuotientMap_mkQ {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {σ : L ≃+* L} (Φ : V →ₛₗ[σ.toRingHom] V) (W : Submodule L V)
    (hW : ∀ w ∈ W, Φ w ∈ W) (v : V) :
    semilinearQuotientMap Φ W hW (W.mkQ v) = W.mkQ (Φ v) :=
  W.liftQ_apply (W.mkQ.comp Φ) v

private theorem semilinearSplittingSection {p : ℕ} [Fact p.Prime] {f : ℕ+}
    {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module (LaurentSeries k) V]
    (Φ : V →ₛₗ[(coefficientFrobenius p f k).toRingHom] V) (hΦ : Bijective Φ)
    {s : ℤ} {r : ℕ+}
    (ι : (Fin r → LaurentSeries k) →ₗ[LaurentSeries k] V) (hι : Injective ι)
    (hinter : ∀ x, ι (standardBlockFrobenius (coefficientFrobenius p f k)
      (HahnSeries.single 1 1) s r x) = Φ (ι x))
    (hW : ∀ w ∈ LinearMap.range ι, Φ w ∈ LinearMap.range ι)
    (D_Q : CyclicSlopeDecomposition (semilinearQuotientMap Φ (LinearMap.range ι) hW)
      (HahnSeries.single 1 1)) :
    ∃ sec : (V ⧸ LinearMap.range ι) →ₗ[LaurentSeries k] V,
      (∀ y, (LinearMap.range ι).mkQ (sec y) = y) ∧
      (∀ y, Φ (sec y) = sec (semilinearQuotientMap Φ (LinearMap.range ι) hW y)) := by
  classical
  let L := LaurentSeries k
  let σ := coefficientFrobenius p f k
  let π : L := HahnSeries.single 1 1
  let Φ_Q := semilinearQuotientMap Φ (LinearMap.range ι) hW
  have hΦ_Q : Bijective Φ_Q := by
    have hsurj : Surjective Φ_Q := fun y ↦ by
      obtain ⟨v, rfl⟩ := (LinearMap.range ι).mkQ_surjective y
      obtain ⟨u, rfl⟩ := hΦ.surjective v
      exact ⟨(LinearMap.range ι).mkQ u, semilinearQuotientMap_mkQ Φ (LinearMap.range ι) hW u⟩
    have : RingHomSurjective σ.toRingHom := ⟨σ.surjective⟩
    have : FiniteDimensional L (V ⧸ LinearMap.range ι) := Module.Finite.of_basis D_Q.basis
    exact ⟨LinearMap.injective_of_surjectiveₛₗ hsurj, hsurj⟩
  let e_Q := Equiv.ofBijective Φ_Q hΦ_Q
  -- Step 1: pick an initial `L`-linear section `sec₀` and measure its failure `u : Q → L^r`.
  let sec₀ : (V ⧸ LinearMap.range ι) →ₗ[L] V :=
    D_Q.basis.constr L fun ij ↦
      Classical.choose ((LinearMap.range ι).mkQ_surjective (D_Q.basis ij))
  have hsec₀_comp : (LinearMap.range ι).mkQ.comp sec₀ = LinearMap.id :=
    D_Q.basis.ext fun ij ↦ by
      simpa [sec₀] using
        Classical.choose_spec ((LinearMap.range ι).mkQ_surjective (D_Q.basis ij))
  have hsec₀ (y : V ⧸ LinearMap.range ι) : (LinearMap.range ι).mkQ (sec₀ y) = y :=
    LinearMap.congr_fun hsec₀_comp y
  let eW : (Fin r → L) ≃ₗ[L] LinearMap.range ι := LinearEquiv.ofInjective ι hι
  let u_V : (V ⧸ LinearMap.range ι) →ₗ[L] V :=
    { toFun y := Φ (sec₀ (e_Q.symm y)) - sec₀ y
      map_add' x y := by rw [bijective_semilinear_symm_add, map_add, map_add, map_add]; abel
      map_smul' c x := by
        have hsmul : e_Q.symm (c • x) = σ.symm c • e_Q.symm x :=
          bijective_semilinear_symm_smul (σ := σ) rfl Φ_Q hΦ_Q c x
        rw [hsmul, map_smul, map_smulₛₗ, ringEquiv_toRingHom_apply, σ.apply_symm_apply,
          map_smul]
        simp only [smul_sub]
        rfl }
  have hu_mem (y : V ⧸ LinearMap.range ι) : u_V y ∈ LinearMap.range ι := by
    rw [← Submodule.Quotient.mk_eq_zero (LinearMap.range ι), ← Submodule.mkQ_apply]
    dsimp only [u_V, LinearMap.coe_mk, AddHom.coe_mk]
    rw [map_sub, ← semilinearQuotientMap_mkQ Φ (LinearMap.range ι) hW, hsec₀, hsec₀]
    exact sub_eq_zero.2 (e_Q.apply_symm_apply y)
  let u : (V ⧸ LinearMap.range ι) →ₗ[L] (Fin r → L) :=
    { toFun y := eW.symm ⟨u_V y, hu_mem y⟩
      map_add' x y := by apply eW.injective; ext1; simp [eW, map_add]
      map_smul' c x := by apply eW.injective; ext1; simp [eW, map_smul] }
  have hιu (y : V ⧸ LinearMap.range ι) : ι (u y) = Φ (sec₀ (e_Q.symm y)) - sec₀ y :=
    congrArg Subtype.val (eW.apply_symm_apply ⟨u_V y, hu_mem y⟩)
  -- Step 2: solve `Φ_W ∘ h - h ∘ Φ_Q = u ∘ Φ_Q` blockwise on `Q` using `D_Q`.
  let e_b (b : Fin D_Q.blocks) : (Fin (D_Q.rank b) → L) →ₗ[L] (V ⧸ LinearMap.range ι) :=
    (Pi.basisFun L (Fin (D_Q.rank b))).constr L fun j ↦ D_Q.basis ⟨b, j⟩
  choose h_b hh_b using fun b : Fin D_Q.blocks ↦
    surjective_hom_standardBlockFrobenius_sub_id f.ne_zero s (D_Q.exponent b) r (D_Q.rank b)
      (u.comp (e_b b))
  let h : (V ⧸ LinearMap.range ι) →ₗ[L] (Fin r → L) :=
    D_Q.basis.constr L fun ⟨b, j⟩ ↦ h_b b (Pi.single j 1)
  have h_eb (b : Fin D_Q.blocks) : h.comp (e_b b) = h_b b :=
    (Pi.basisFun L (Fin (D_Q.rank b))).ext fun j ↦ by simp [e_b, h]
  -- Modify the splitting `sec₀` by `-ι ∘ h` so it intertwines `Φ_Q` and `Φ`.
  have hh_Q (y : V ⧸ LinearMap.range ι) :
      standardBlockFrobenius σ π s r (h y) - h (Φ_Q y) = u (Φ_Q y) := by
    have hbas (b : Fin D_Q.blocks) (j : Fin (D_Q.rank b)) :
        standardBlockFrobenius σ π s r (h (D_Q.basis ⟨b, j⟩)) -
          h (Φ_Q (D_Q.basis ⟨b, j⟩)) = u (Φ_Q (D_Q.basis ⟨b, j⟩)) := by
      have hbd : D_Q.basis ⟨b, j⟩ = e_b b (Pi.single j 1) := by simp [e_b]
      have heb (z) : h (e_b b z) = h_b b z := LinearMap.congr_fun (h_eb b) z
      rw [hbd, heb, ← cyclicSlopeDecomposition_intertwiner D_Q b, heb]
      have hres := hh_b b (Pi.single j 1)
      rw [LinearMap.comp_apply] at hres
      exact hres
    conv_lhs => rw [← D_Q.basis.sum_repr y]
    conv_rhs => rw [← D_Q.basis.sum_repr y]
    rw [map_sum, map_sum, map_sum, map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ⟨b, j⟩ _ ↦ ?_
    have hσc : (σ : L →+* L) ((D_Q.basis.repr y) ⟨b, j⟩) =
        (coefficientFrobenius p (↑f) k).toRingHom ((D_Q.basis.repr y) ⟨b, j⟩) := rfl
    rw [map_smul, map_smulₛₗ, map_smulₛₗ, map_smul, map_smul, hσc, ← smul_sub, hbas b j]
  refine ⟨sec₀ - ι.comp h, fun y ↦ ?_, fun y ↦ ?_⟩
  · simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hsec₀]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero (LinearMap.range ι)).2 ⟨h y, rfl⟩,
      sub_zero]
  · have h1 := congrArg ι (hh_Q y)
    have he_eq : e_Q.symm (Φ_Q y) = y := e_Q.symm_apply_apply y
    rw [map_sub, hinter, hιu, he_eq] at h1
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
    rw [sub_eq_sub_iff_add_eq_add] at h1 ⊢
    rw [add_comm (sec₀ (Φ_Q y))]
    exact h1.symm

private noncomputable def cyclicSlopeDecomposition_cons {L V : Type*} [Field L]
    [AddCommGroup V] [Module L V] {σ : L ≃+* L} (Φ : V →ₛₗ[σ.toRingHom] V) (π : L)
    {s : ℤ} {r : ℕ+} (hcop : s.natAbs.Coprime r)
    (ι : (Fin r → L) →ₗ[L] V) (hι : Injective ι)
    (hinter : ∀ x, ι (standardBlockFrobenius σ π s r x) = Φ (ι x))
    (hW : ∀ w ∈ LinearMap.range ι, Φ w ∈ LinearMap.range ι)
    (D_Q : CyclicSlopeDecomposition (semilinearQuotientMap Φ (LinearMap.range ι) hW) π)
    (sec : (V ⧸ LinearMap.range ι) →ₗ[L] V)
    (hq_sec : ∀ y, (LinearMap.range ι).mkQ (sec y) = y)
    (hΦ_sec : ∀ y, Φ (sec y) = sec (semilinearQuotientMap Φ (LinearMap.range ι) hW y)) :
    CyclicSlopeDecomposition Φ π :=
  let eW : (Fin r → L) ≃ₗ[L] LinearMap.range ι := LinearEquiv.ofInjective ι hι
  have hmem_ker (z : V) : z - sec ((LinearMap.range ι).mkQ z) ∈ LinearMap.range ι := by
    rw [← Submodule.Quotient.mk_eq_zero (LinearMap.range ι), ← Submodule.mkQ_apply]
    rw [map_sub, hq_sec, sub_self]
  have hq_add (x : Fin r → L) (y : V ⧸ LinearMap.range ι) :
      (LinearMap.range ι).mkQ (ι x + sec y) = y := by
    rw [map_add, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero (LinearMap.range ι)).2 ⟨x, rfl⟩, zero_add, hq_sec]
  let e_V : ((Fin r → L) × (V ⧸ LinearMap.range ι)) ≃ₗ[L] V :=
    { toFun p := ι p.1 + sec p.2
      invFun z := (eW.symm ⟨z - sec ((LinearMap.range ι).mkQ z), hmem_ker z⟩,
        (LinearMap.range ι).mkQ z)
      left_inv p := by
        ext1
        · apply eW.injective
          rw [eW.apply_symm_apply]
          ext1
          simp [eW, hq_add]
        · exact hq_add p.1 p.2
      right_inv z := by
        have hspec : ι (eW.symm ⟨z - sec ((LinearMap.range ι).mkQ z), hmem_ker z⟩) =
            z - sec ((LinearMap.range ι).mkQ z) :=
          congrArg Subtype.val (eW.apply_symm_apply _)
        dsimp only
        rw [hspec, sub_add_cancel]
      map_add' p₁ p₂ := by simp [map_add]; abel
      map_smul' c p := by simp [map_smul] }
  let rank : Fin (D_Q.blocks + 1) → ℕ+ := Fin.cases r D_Q.rank
  let exponent : Fin (D_Q.blocks + 1) → ℤ := Fin.cases s D_Q.exponent
  have hrank0 : (rank 0 : ℕ) = (r : ℕ) := by simp [rank]
  have hrank_succ (i : Fin D_Q.blocks) : (rank i.succ : ℕ) = (D_Q.rank i : ℕ) := by simp [rank]
  let e_to : Fin r ⊕ (Σ i : Fin D_Q.blocks, Fin (D_Q.rank i)) →
      Σ i : Fin (D_Q.blocks + 1), Fin (rank i) :=
    Sum.elim (fun j ↦ ⟨0, j.cast hrank0.symm⟩)
      (fun ij ↦ ⟨ij.1.succ, ij.2.cast (hrank_succ ij.1).symm⟩)
  let e_inv : (Σ i : Fin (D_Q.blocks + 1), Fin (rank i)) →
      Fin r ⊕ (Σ i : Fin D_Q.blocks, Fin (D_Q.rank i)) := fun ij ↦
    Fin.cases (motive := fun i ↦ Fin (rank i) →
        Fin r ⊕ (Σ i' : Fin D_Q.blocks, Fin (D_Q.rank i')))
      (fun j ↦ Sum.inl (j.cast hrank0))
      (fun i j ↦ Sum.inr ⟨i, j.cast (hrank_succ i)⟩) ij.1 ij.2
  -- Assemble the combined basis via `(L^r × (V / range ι)) ≃ₗ V` and verify Frobenius action.
  let e_idx : Fin r ⊕ (Σ i : Fin D_Q.blocks, Fin (D_Q.rank i)) ≃
      Σ i : Fin (D_Q.blocks + 1), Fin (rank i) :=
    { toFun := e_to
      invFun := e_inv
      left_inv := by rintro (j | ⟨i, j⟩) <;> simp [e_to, e_inv]
      right_inv := by
        rintro ⟨i, j⟩
        refine Fin.cases
          (motive := fun i ↦ ∀ j : Fin (rank i), e_to (e_inv ⟨i, j⟩) = ⟨i, j⟩)
          (fun j ↦ by simp [e_to, e_inv]) (fun i j ↦ by simp [e_to, e_inv]) i j }
  let bas : Basis (Σ i : Fin (D_Q.blocks + 1), Fin (rank i)) L V :=
    (((Pi.basisFun L (Fin r)).prod D_Q.basis).map e_V).reindex e_idx
  { blocks := D_Q.blocks + 1
    rank := rank
    exponent := exponent
    coprime := Fin.cases (motive := fun i ↦ (exponent i).natAbs.Coprime (rank i))
      (by simpa [rank, exponent] using hcop)
      (fun i ↦ by simpa [rank, exponent] using D_Q.coprime i)
    basis := bas
    frobenius_basis := fun i j ↦ by
      refine Fin.cases (motive := fun i ↦ ∀ j : Fin (rank i),
        Φ (bas ⟨i, j⟩) = (if j.val + 1 = rank i then π ^ exponent i else 1) •
          bas ⟨i, finRotate (rank i) j⟩) (fun j ↦ ?_) (fun i j ↦ ?_) i j
      · have hbas : bas ⟨0, j⟩ = ι (Pi.single (j.cast hrank0) 1) := by
          simp [bas, e_idx, e_inv, e_V]
        have hrot_cast : (finRotate (rank 0) j).cast hrank0 = finRotate r (j.cast hrank0) := by
          have h1 : ∀ n : ℕ+, ((1 : Fin n) : ℕ) = 1 % (n : ℕ) := fun _ ↦ rfl
          ext; simp only [Fin.val_cast, finRotate_apply, Fin.val_add, h1, hrank0]
        have hbas_rot : bas ⟨0, finRotate (rank 0) j⟩ =
            ι (Pi.single (finRotate r (j.cast hrank0)) 1) := by
          have h0 : bas ⟨0, finRotate (rank 0) j⟩ =
              ι (Pi.single ((finRotate (rank 0) j).cast hrank0) 1) := by
            simp [bas, e_idx, e_inv, e_V]
          rw [h0, hrot_cast]
        rw [hbas, hbas_rot, ← hinter, ← map_smul]
        congr 1
        by_cases hj : j.val + 1 = rank 0
        · have hj' : (j.cast hrank0).val + 1 = r := by simpa [hrank0] using hj
          simp only [hj, ↓reduceIte, exponent, Fin.cases_zero]
          exact standardBlockFrobenius_single_of_val_add_one_eq hj'
        · have hj' : (j.cast hrank0).val + 1 ≠ r := by simpa [hrank0] using hj
          simp only [hj, ↓reduceIte, one_smul]
          exact standardBlockFrobenius_single_of_val_add_one_ne hj'
      · have hbas : bas ⟨i.succ, j⟩ = sec (D_Q.basis ⟨i, j.cast (hrank_succ i)⟩) := by
          simp [bas, e_idx, e_inv, e_V]
        have hrot_cast : (finRotate (rank i.succ) j).cast (hrank_succ i) =
            finRotate (D_Q.rank i) (j.cast (hrank_succ i)) := by
          have h1 : ∀ n : ℕ+, ((1 : Fin n) : ℕ) = 1 % (n : ℕ) := fun _ ↦ rfl
          ext; simp only [Fin.val_cast, finRotate_apply, Fin.val_add, h1, hrank_succ]
        have hbas_rot : bas ⟨i.succ, finRotate (rank i.succ) j⟩ =
            sec (D_Q.basis ⟨i, finRotate (D_Q.rank i) (j.cast (hrank_succ i))⟩) := by
          have h0 : bas ⟨i.succ, finRotate (rank i.succ) j⟩ =
              sec (D_Q.basis ⟨i, (finRotate (rank i.succ) j).cast (hrank_succ i)⟩) := by
            simp [bas, e_idx, e_inv, e_V]
          rw [h0, hrot_cast]
        rw [hbas, hbas_rot, hΦ_sec, D_Q.frobenius_basis, map_smul]
        simp only [hrank_succ, Fin.val_cast, exponent, Fin.cases_succ] }

/-- **Existence of cyclic slope decompositions.** Every finite isocrystal `(V, Φ)` over `k((π))`
(with `k` algebraically closed of characteristic `p > 0` and `f > 0`) admits a decomposition into
coprime cyclic standard blocks `D(s, r)`. -/
theorem CyclicSlopeDecomposition.exists {p : ℕ} [Fact p.Prime] (f : ℕ+)
    (k : Type*) [Field k] [CharP k p] [IsAlgClosed k]
    (V : Type*) [AddCommGroup V] [Module (LaurentSeries k) V]
    [FiniteDimensional (LaurentSeries k) V]
    (Φ : V →ₛₗ[(coefficientFrobenius p f k).toRingHom] V)
    (hΦ : Bijective Φ) :
    Nonempty (CyclicSlopeDecomposition Φ (HahnSeries.single 1 1)) := by
  classical
  induction hfin : Module.finrank (LaurentSeries k) V using Nat.strong_induction_on
      generalizing V with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · have : Subsingleton V := Module.finrank_zero_iff.1 hfin
      exact ⟨⟨0, Fin.elim0, Fin.elim0, fun i ↦ i.elim0, Basis.empty V, fun i ↦ i.elim0⟩⟩
    have : Nontrivial V := Module.finrank_pos_iff.1 (hfin ▸ Nat.pos_of_ne_zero hn)
    obtain ⟨s, r, hcop, ι, hι, hinter⟩ := exists_inj_intertwines_standardBlock hΦ
    let W := LinearMap.range ι
    have hW : ∀ w ∈ W, Φ w ∈ W := by rintro _ ⟨x, rfl⟩; exact ⟨_, hinter x⟩
    let Φ_Q := semilinearQuotientMap Φ W hW
    have hΦ_Q : Bijective Φ_Q := by
      have hsurj : Surjective Φ_Q := fun y ↦ by
        obtain ⟨v, rfl⟩ := W.mkQ_surjective y
        obtain ⟨u, rfl⟩ := hΦ.surjective v
        exact ⟨W.mkQ u, semilinearQuotientMap_mkQ Φ W hW u⟩
      have : RingHomSurjective (coefficientFrobenius p f k).toRingHom :=
        ⟨(coefficientFrobenius p f k).surjective⟩
      exact ⟨LinearMap.injective_of_surjectiveₛₗ hsurj, hsurj⟩
    have hfinW : 0 < Module.finrank (LaurentSeries k) W := by
      have : Nontrivial W := ⟨⟨⟨ι (Pi.single (0 : Fin r) 1), ⟨_, rfl⟩⟩, 0, fun h ↦ by
        have h0 : Pi.single (0 : Fin r) (1 : LaurentSeries k) = 0 :=
          hι ((congrArg Subtype.val h).trans (map_zero ι).symm)
        simpa using congrFun h0 0⟩⟩
      exact Module.finrank_pos (R := LaurentSeries k)
    have hlt : Module.finrank (LaurentSeries k) (V ⧸ W) < n := by
      have hadd := Submodule.finrank_quotient_add_finrank W
      omega
    obtain ⟨D_Q⟩ := ih (Module.finrank (LaurentSeries k) (V ⧸ W)) hlt (V ⧸ W) Φ_Q hΦ_Q rfl
    obtain ⟨sec, hq_sec, hΦ_sec⟩ := semilinearSplittingSection Φ hΦ ι hι hinter hW D_Q
    exact ⟨cyclicSlopeDecomposition_cons Φ (HahnSeries.single 1 1) hcop ι hι hinter hW D_Q sec
      hq_sec hΦ_sec⟩

end Splitting

/-! ### Uniqueness of slopes -/

section Uniqueness

private noncomputable def CyclicSlopeDecomposition.blockEquiv {L V : Type*} [Field L]
    [AddCommGroup V] [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[σ.toRingHom] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) :
    V ≃ₗ[L] (∀ i : Fin D.blocks, Fin (D.rank i) → L) :=
  D.basis.equivFun.trans
    { toFun f i j := f ⟨i, j⟩
      invFun g ij := g ij.1 ij.2
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

private theorem CyclicSlopeDecomposition.blockEquiv_basis {L V : Type*} [Field L]
    [AddCommGroup V] [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[σ.toRingHom] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) (b : Fin D.blocks) (j : Fin (D.rank b)) :
    D.blockEquiv (D.basis ⟨b, j⟩) = Pi.single b (Pi.single j 1) := by
  ext k l
  by_cases hk : k = b
  · subst hk
    simp [CyclicSlopeDecomposition.blockEquiv, Pi.single_apply, Finsupp.single_apply, eq_comm]
  · simp [CyclicSlopeDecomposition.blockEquiv, hk]

private theorem CyclicSlopeDecomposition.blockEquiv_intertwines {L V : Type*} [Field L]
    [AddCommGroup V] [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[σ.toRingHom] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) (v : V) (i : Fin D.blocks) :
    D.blockEquiv (Φ v) i =
      standardBlockFrobenius σ π (D.exponent i) (D.rank i) (D.blockEquiv v i) := by
  have hbas (b : Fin D.blocks) (j : Fin (D.rank b)) :
      D.blockEquiv (Φ (D.basis ⟨b, j⟩)) i =
        standardBlockFrobenius σ π (D.exponent i) (D.rank i)
          (D.blockEquiv (D.basis ⟨b, j⟩) i) := by
    rw [D.frobenius_basis, map_smul, Pi.smul_apply, D.blockEquiv_basis, D.blockEquiv_basis]
    by_cases hib : i = b
    · subst hib
      rw [Pi.single_eq_same, Pi.single_eq_same]
      by_cases hj : j.val + 1 = D.rank i
      · simp [hj, standardBlockFrobenius_single_of_val_add_one_eq hj]
      · simp [hj, standardBlockFrobenius_single_of_val_add_one_ne hj]
    · simp [Pi.single_eq_of_ne hib]
  conv_lhs => rw [← D.basis.sum_repr v]
  conv_rhs => rw [← D.basis.sum_repr v]
  rw [map_sum, map_sum, Finset.sum_apply, map_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun ⟨b, j⟩ _ ↦ ?_
  rw [map_smulₛₗ, map_smul, Pi.smul_apply, map_smul, Pi.smul_apply, map_smulₛₗ,
    ringEquiv_toRingHom_apply, RingHom.coe_coe, hbas]

private theorem isotypic_component_zero {L V Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] [AddCommGroup V] [Module L V] {σ : L ≃+* L}
    {Φ : V →ₛₗ[σ.toRingHom] V} {π : L} {v : Valuation L Γ₀}
    (hv : ∀ x, v (σ x) = v x) (hπ : π ≠ 0) (hvπ : v π ≠ 1) (hσπ : σ π = π)
    (D₁ D₂ : CyclicSlopeDecomposition Φ π) (i₁ : Fin D₁.blocks) (i₂ : Fin D₂.blocks)
    (hslope : (D₁.exponent i₁ : ℚ) / (D₁.rank i₁ : ℕ) ≠
      (D₂.exponent i₂ : ℚ) / (D₂.rank i₂ : ℕ))
    (x : Fin (D₁.rank i₁) → L) :
    D₂.blockEquiv (D₁.blockEquiv.symm (Pi.single i₁ x)) i₂ = 0 := by
  let f : (Fin (D₁.rank i₁) → L) →ₗ[L] (Fin (D₂.rank i₂) → L) :=
    { toFun y := D₂.blockEquiv (D₁.blockEquiv.symm (Pi.single i₁ y)) i₂
      map_add' y₁ y₂ := by simp [Pi.single_add, map_add]
      map_smul' c y := by simp [Pi.single_smul, map_smul] }
  have hf : ∀ y, f (standardBlockFrobenius σ π (D₁.exponent i₁) (D₁.rank i₁) y) =
      standardBlockFrobenius σ π (D₂.exponent i₂) (D₂.rank i₂) (f y) := by
    intro y
    let v₀ : V := D₁.blockEquiv.symm (Pi.single i₁ y)
    have hv₀ : D₁.blockEquiv (Φ v₀) =
        Pi.single i₁ (standardBlockFrobenius σ π (D₁.exponent i₁) (D₁.rank i₁) y) := by
      ext k l
      rw [D₁.blockEquiv_intertwines]
      by_cases hk : k = i₁
      · subst hk; simp [v₀]
      · have hzero : D₁.blockEquiv v₀ k = 0 := by simp [v₀, hk]
        simp [hzero, hk]
    have hMΦ : D₂.blockEquiv (D₁.blockEquiv.symm
        (Pi.single i₁ (standardBlockFrobenius σ π (D₁.exponent i₁) (D₁.rank i₁) y))) =
        D₂.blockEquiv (Φ v₀) :=
      congrArg D₂.blockEquiv (D₁.blockEquiv.symm_apply_eq.2 hv₀.symm)
    have hf' := congrFun hMΦ i₂
    rw [D₂.blockEquiv_intertwines] at hf'
    simpa [f, v₀] using hf'
  have hzero := eq_zero_of_intertwines_standardBlock hv hπ hvπ hσπ hslope hf
  exact LinearMap.congr_fun hzero x

private noncomputable def isotypicBlockEquiv {L V Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] [AddCommGroup V] [Module L V] {σ : L ≃+* L}
    {Φ : V →ₛₗ[σ.toRingHom] V} {π : L} {v : Valuation L Γ₀}
    (hv : ∀ x, v (σ x) = v x) (hπ : π ≠ 0) (hvπ : v π ≠ 1) (hσπ : σ π = π)
    (D D' : CyclicSlopeDecomposition Φ π) (q : ℚ) :
    (∀ i : {i : Fin D.blocks // (D.exponent i : ℚ) / (D.rank i : ℕ) = q},
      Fin (D.rank i.val) → L) ≃ₗ[L]
    (∀ i' : {i' : Fin D'.blocks // (D'.exponent i' : ℚ) / (D'.rank i' : ℕ) = q},
      Fin (D'.rank i'.val) → L) :=
  -- Extend slope-`q` coordinates by zero to the full decomposition, then apply `M = D' ∘ D⁻¹`.
  let M := D.blockEquiv.symm.trans D'.blockEquiv
  let extD (x : ∀ i : {i : Fin D.blocks // (D.exponent i : ℚ) / (D.rank i : ℕ) = q},
      Fin (D.rank i.val) → L) : ∀ i : Fin D.blocks, Fin (D.rank i) → L :=
    fun i ↦ if hi : (D.exponent i : ℚ) / (D.rank i : ℕ) = q then x ⟨i, hi⟩ else 0
  let extD' (y : ∀ i' : {i' : Fin D'.blocks // (D'.exponent i' : ℚ) / (D'.rank i' : ℕ) = q},
      Fin (D'.rank i'.val) → L) : ∀ i' : Fin D'.blocks, Fin (D'.rank i') → L :=
    fun i' ↦ if hi' : (D'.exponent i' : ℚ) / (D'.rank i' : ℕ) = q then y ⟨i', hi'⟩ else 0
  { toFun x i' := M (extD x) i'.val
    invFun y i := M.symm (extD' y) i.val
    left_inv x := by
      -- Cross-slope components vanish by `isotypic_component_zero`, so `M (extD x)` lands in `q`.
      ext ⟨i, hi⟩ l
      have hzero : extD' (fun i' ↦ M (extD x) i'.val) = M (extD x) := by
        ext i' m
        by_cases hi' : (D'.exponent i' : ℚ) / (D'.rank i' : ℕ) = q
        · simp [extD', hi']
        · simp only [extD', hi', ↓reduceDIte, Pi.zero_apply]
          have hsum : extD x = ∑ j : Fin D.blocks, Pi.single j (extD x j) :=
            (Finset.univ_sum_single _).symm
          rw [hsum, map_sum, Finset.sum_apply, Finset.sum_apply]
          refine (Finset.sum_eq_zero fun j _ ↦ ?_).symm
          by_cases hj : (D.exponent j : ℚ) / (D.rank j : ℕ) = q
          · have hne : (D.exponent j : ℚ) / (D.rank j : ℕ) ≠
                (D'.exponent i' : ℚ) / (D'.rank i' : ℕ) :=
              hj.symm ▸ (Ne.symm hi')
            exact congrFun (isotypic_component_zero hv hπ hvπ hσπ D D' j i' hne (extD x j)) m
          · simp [extD, hj]
      dsimp only
      rw [hzero, M.symm_apply_apply]
      simp [extD, hi]
    right_inv y := by
      ext ⟨i', hi'⟩ l
      have hzero : extD (fun i ↦ M.symm (extD' y) i.val) = M.symm (extD' y) := by
        ext i m
        by_cases hi : (D.exponent i : ℚ) / (D.rank i : ℕ) = q
        · simp [extD, hi]
        · simp only [extD, hi, ↓reduceDIte, Pi.zero_apply]
          have hsum : extD' y = ∑ j' : Fin D'.blocks, Pi.single j' (extD' y j') :=
            (Finset.univ_sum_single _).symm
          rw [hsum, map_sum, Finset.sum_apply, Finset.sum_apply]
          refine (Finset.sum_eq_zero fun j' _ ↦ ?_).symm
          by_cases hj' : (D'.exponent j' : ℚ) / (D'.rank j' : ℕ) = q
          · have hne : (D'.exponent j' : ℚ) / (D'.rank j' : ℕ) ≠
                (D.exponent i : ℚ) / (D.rank i : ℕ) :=
              hj'.symm ▸ (Ne.symm hi)
            exact congrFun (isotypic_component_zero hv hπ hvπ hσπ D' D j' i hne (extD' y j')) m
          · simp [extD', hj']
      dsimp only
      rw [hzero, M.apply_symm_apply]
      simp [extD', hi']
    map_add' x₁ x₂ := by
      ext i' m
      have hadd : extD (x₁ + x₂) = extD x₁ + extD x₂ := by
        ext i l
        by_cases hi : (D.exponent i : ℚ) / (D.rank i : ℕ) = q <;> simp [extD, hi]
      simp [hadd, map_add]
    map_smul' c x := by
      ext i' m
      have hsmul : extD (c • x) = c • extD x := by
        ext i l
        by_cases hi : (D.exponent i : ℚ) / (D.rank i : ℕ) = q <;> simp [extD, hi]
      simp [hsmul, map_smul] }

/-- **Uniqueness of slopes for arbitrary valued fields.** If `σ` fixes `π ≠ 0` and preserves a
valuation `v` with `v π ≠ 1`, then any two coprime cyclic slope decompositions of the same
isocrystal `(V, Φ)` have the same multiset of slopes. -/
theorem CyclicSlopeDecomposition.slopes_eq_of_valuation {L V Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] [AddCommGroup V] [Module L V] {σ : L ≃+* L}
    {Φ : V →ₛₗ[σ.toRingHom] V} {π : L} (v : Valuation L Γ₀) (hv : ∀ x, v (σ x) = v x)
    (hπ : π ≠ 0) (hvπ : v π ≠ 1) (hσπ : σ π = π)
    (D D' : CyclicSlopeDecomposition Φ π) : D.slopes = D'.slopes := by
  classical
  refine Multiset.ext.2 fun q ↦ ?_
  have heq := (isotypicBlockEquiv hv hπ hvπ hσπ D D' q).finrank_eq
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at heq
  have hden (D₀ : CyclicSlopeDecomposition Φ π)
      (i : {i : Fin D₀.blocks // (D₀.exponent i : ℚ) / (D₀.rank i : ℕ) = q}) :
      Module.finrank L (Fin (D₀.rank i.val) → L) = q.den := by
    rw [Module.finrank_pi, Fintype.card_fin]
    have hcop :
        Nat.Coprime (D₀.exponent i.val).natAbs ((D₀.rank i.val : ℕ) : ℤ).natAbs := by
      simpa using D₀.coprime i.val
    have hr_pos : (0 : ℤ) < (D₀.rank i.val : ℕ) := by exact_mod_cast (D₀.rank i.val).pos
    have hq := Rat.den_div_eq_of_coprime hr_pos hcop
    rw [← Int.natCast_inj]
    simpa [i.property] using hq.symm
  simp_rw [hden D, hden D', Finset.sum_const, Finset.card_univ, Fintype.card_subtype,
    smul_eq_mul] at heq
  rw [D.count_slopes, D'.count_slopes]
  exact Nat.eq_of_mul_eq_mul_right q.den_pos heq

/-- **Dieudonné–Manin classification in equal characteristic.** Over `k((π))` with `k` an
algebraically closed field of characteristic `p > 0` and arithmetic `p^f`-Frobenius (`f > 0`),
every finite isocrystal admits a coprime cyclic block decomposition, and its multiset of block
slopes is unique. -/
theorem dieudonneManinEqualChar (p : ℕ) [Fact p.Prime] (f : ℕ+)
    (k : Type*) [Field k] [CharP k p] [IsAlgClosed k]
    (V : Type*) [AddCommGroup V] [Module (LaurentSeries k) V]
    [FiniteDimensional (LaurentSeries k) V]
    (Φ : V →ₛₗ[(coefficientFrobenius p f k).toRingHom] V)
    (hΦ : Function.Bijective Φ) :
    ∃ D : CyclicSlopeDecomposition Φ (HahnSeries.single 1 1),
      ∀ D' : CyclicSlopeDecomposition Φ (HahnSeries.single 1 1), D.slopes = D'.slopes := by
  have : ExpChar k p := expChar_prime k p
  obtain ⟨D⟩ := CyclicSlopeDecomposition.exists f k V Φ hΦ
  have hvπ : Valued.v (HahnSeries.single (1 : ℤ) (1 : k)) ≠ 1 := by
    simp [_root_.LaurentSeries.valuation_single_zpow]
  exact ⟨D, fun D' ↦ CyclicSlopeDecomposition.slopes_eq_of_valuation Valued.v
    valuation_coefficientFrobenius (HahnSeries.single_ne_zero one_ne_zero) hvπ
    (coefficientFrobenius_single_one 1) D D'⟩

end Uniqueness

end TauCeti
