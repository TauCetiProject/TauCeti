/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.Exact
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Character.Image
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Equiv
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ElementaryAutomorphism
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CrossedHom
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.PadicModule
public import TauCeti.NumberTheory.Padics.TwistedUnits

/-!
# Labute's normal form for the dyadic Demushkin groups of even rank with image `{±1} × U^(f)`

Let `G` be a Demushkin group at `p = 2` of even rank `n ≥ 4` whose canonical character has image
`V^(f) = {±1} × U^(f)` for a finite `f ≥ 2`. Labute's Theorem 6 says that `G` is presented on
`n` generators by the single relator `x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`, the
normal-form word `TauCeti.demushkinWordTwoEven 0 f n`; in particular two such groups with the same
rank and the same `f` are topologically isomorphic. This file proves that theorem, from the exact
normal form of the dyadic relators of even rank
(`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.Exact`), the values of
the canonical character forced by that normal form, the symplectic transvection pair
`TauCeti.freeProP.symplecticTransvection` of
`TauCeti.Topology.Algebra.Group.Profinite.Free.ElementaryAutomorphism`, which adjusts the
character value at `x₂`, and the constrained successive approximation of
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.Approximation`.

## Main results

* `TauCeti.freeProP.gradedMap_symplecticTransvection_gradedMk_demushkinWordNeTwo`: the symplectic
  transvection pair `x₂ ↦ x₂ x₄^c`, `x₃ ↦ x₃ x₁^{-c}` fixes the class of
  `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` in `gr_1(F)`.
* `TauCeti.freeProP.apply_eq_of_forall_isCrossedHom_eq_zero_padicPow_mul_labuteComm_mul`: the
  values of a character of `F` all of whose continuous crossed homomorphisms kill the exact
  normal-form relator `x₁^{2+α} (x₁, x₂) x₃^{q} (x₃, x₄) ⋯ (x_{n-1}, x_n)`.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_demushkinWordTwoEven_of_range_eq`:
  **Labute's Theorem 6, relator form**: a relator of `F` presenting a Demushkin group of even rank
  `n ≥ 4` whose canonical character has image `{±1} × U^(f)` is carried to
  `x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` by a continuous automorphism of `F`.
* `TauCeti.freeProP.exists_continuousMulEquiv_presentedProP_demushkinWordTwoEven_of_range_eq`
  and its intrinsic form
  `TauCeti.IsDemushkin.exists_continuousMulEquiv_presentedProP_demushkinWordTwoEven_of_range_eq`:
  such a Demushkin group is topologically isomorphic to
  `⟨x₁, …, x_n ∣ x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)⟩` on `n = demushkinRank hG`
  generators.
* `TauCeti.IsDemushkin.nonempty_continuousMulEquiv_of_even_demushkinRank_of_range_eq_unitsPlusMinus`
  is **uniqueness**: two Demushkin groups at `p = 2` of the same even rank `n ≥ 4` whose canonical
  characters have the same image `{±1} × U^(f)` are topologically isomorphic.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §4,
  Theorem 6.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.9.19).
-/

public section

namespace TauCeti

open Subgroup

universe u v

variable {n : ℕ}

namespace freeProP

/-! ### The symplectic transvection pair and the normal-form word -/

section SymplecticTransvection

variable {p : ℕ} [Fact p.Prime] (hn3 : 3 < n) (c : ℤ_[p])

/-- **The symplectic transvection pair fixes the class of the normal-form word**
`x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` in `gr_1(F)`, for `n ≥ 4` and `p ∣ q`. -/
theorem gradedMap_symplecticTransvection_gradedMk_demushkinWordNeTwo {q : ℕ} (hq : p ∣ q) :
    gradedMap p
        (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
        (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 1
        (gradedMk p (freeProP p (Fin n)) 1 ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) =
      gradedMk p (freeProP p (Fin n)) 1 ⟨demushkinWordNeTwo q n (freeProPGen p n),
        demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩ := by
  -- The pair fixes `x₁`, so the `p`-power term is unchanged, and the commutator terms
  -- `[ξ₁, c ξ₄]` it creates from `(x₁, x₂)` and `[-c ξ₁, ξ₄]` from `(x₃, x₄)` cancel.
  obtain ⟨k, hk⟩ : ∃ k, n / 2 = k + 2 := ⟨n / 2 - 2, by omega⟩
  have hσ : ∀ m, m ≠ 1 → m ≠ 2 →
      (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
        (freeProPGen p n m) = freeProPGen p n m :=
    fun m hm₁ hm₂ ↦ symplecticTransvection_freeProPGen_of_ne hn3 c m hm₁ hm₂
  have hσ₁ : (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
      (freeProPGen p n 1) =
      freeProPGen p n 1 * (isProP_freeProP p (Fin n)).padicPow (freeProPGen p n 3) c :=
    symplecticTransvection_freeProPGen_one hn3 c
  have hσ₂ : (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
      (freeProPGen p n 2) =
      freeProPGen p n 2 * (isProP_freeProP p (Fin n)).padicPow (freeProPGen p n 0) (-c) :=
    symplecticTransvection_freeProPGen_two hn3 c
  rw [gradedMk_demushkinWordNeTwo hq, map_add, map_nsmul, map_sum, gradedMap_gradedPow,
    gradedMap_gradedMkZero, hσ 0 (by omega) (by omega)]
  congr 1
  -- The bracket lands in `gr_{0+0+1}`, which is `gr_1` only up to defeq; restate naturality
  -- at the degree `1` the sum is written in.
  have key (x y : gradedPiece p (freeProP p (Fin n)) 0) :
      gradedMap p
        (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
        (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 1
        (gradedBracket p (freeProP p (Fin n)) 0 0 x y) =
      gradedBracket p (freeProP p (Fin n)) 0 0
        (gradedMap p
          (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
          (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 0 x)
        (gradedMap p
          (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
          (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 0
          y) :=
    gradedMap_gradedBracket _ _ x y
  simp only [key, gradedMap_gradedMkZero]
  rw [hk, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ',
    Finset.sum_range_succ']
  have hrest : ∀ i ∈ Finset.range k,
      gradedBracket p (freeProP p (Fin n)) 0 0
        (gradedMkZero p _
          ((symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
            (freeProPGen p n (2 * (i + 1 + 1)))))
        (gradedMkZero p _
          ((symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
            (freeProPGen p n (2 * (i + 1 + 1) + 1)))) =
      gradedBracket p (freeProP p (Fin n)) 0 0
        (gradedMkZero p _ (freeProPGen p n (2 * (i + 1 + 1))))
        (gradedMkZero p _ (freeProPGen p n (2 * (i + 1 + 1) + 1))) := fun i _ ↦ by
    rw [hσ _ (by omega) (by omega), hσ _ (by omega) (by omega)]
  rw [Finset.sum_congr rfl hrest]
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, hσ₁, hσ₂, gradedMkZero_mul,
    hσ 0 (by omega) (by omega), hσ 3 (by omega) (by omega), map_add, AddMonoidHom.add_apply]
  have hkey := (isProP_freeProP p (Fin n)).gradedBracket_gradedMkZero_padicPow_neg_add p
    (freeProPGen p n 0) (freeProPGen p n 3) c
  rw [show ∀ S A B C D : gradedPiece p (freeProP p (Fin n)) (0 + 0 + 1),
      S + (A + B) + (C + D) = S + A + C + (B + D) from fun _ _ _ _ _ ↦ by abel, hkey, add_zero]

end SymplecticTransvection

/-! ### The character values forced by the exact normal form -/

/-- **The character values forced by the exact dyadic relator of even rank** (Labute, Theorem 4,
read on the exact normal form). Let `n ≥ 4` be even and let `χ` be a continuous character of the
free pro-`2` group on `n` generators all of whose continuous crossed homomorphisms kill
`x₁^{2+α} (x₁, x₂) x₃^{q} (x₃, x₄) ⋯ (x_{n-1}, x_n)`, with `α ∈ ℤ₂` and `q : ℕ`. Then
`χ(x₂) (1 + α) = -1`, `χ(x₄) (1 - q) = 1`, and `χ(x_i) = 1` for every other generator. -/
theorem apply_eq_of_forall_isCrossedHom_eq_zero_padicPow_mul_labuteComm_mul (hn : Even n)
    (hn3 : 3 < n) (χ : freeProP 2 (Fin n) →ₜ* ℤ_[2]ˣ) (α : ℤ_[2]) (q : ℕ)
    (hkill : ∀ D : freeProP 2 (Fin n) → ℤ_[2], Continuous D → IsCrossedHom χ D →
      D ((isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 0) (2 + α) *
        labuteComm (freeProPGen 2 n 0) (freeProPGen 2 n 1) *
        demushkinWordNeTwo q (n - 2) fun i ↦ freeProPGen 2 n (i + 2)) = 0) :
    (∀ j : ℕ, j ≠ 1 → j ≠ 3 → χ (freeProPGen 2 n j) = 1) ∧
      (χ (freeProPGen 2 n 1) : ℤ_[2]) * (1 + α) = -1 ∧
      (χ (freeProPGen 2 n 3) : ℤ_[2]) * (1 - q) = 1 := by
  set x := freeProPGen 2 n with hx
  set P := (isProP_freeProP 2 (Fin n)).padicPow (x 0) (2 + α) with hP
  set C := labuteComm (x 0) (x 1)
  set T := demushkinWordNeTwo q (n - 2) (fun i ↦ x (i + 2)) with hT
  obtain ⟨m, hm⟩ := hn
  -- The Kronecker crossed homomorphisms `D_k`, with `D_k (x_j) = δ_{kj}`: `D_k` at the partner
  -- `x_k` of `x_i` in its commutator factor forces `χ(x_i) = 1`, and `D₁`, `D₃` then read off the
  -- two marked values.
  have hD : ∀ (k : ℕ) (hk : k < n), IsCrossedHom χ (crossedHom χ (Pi.single (⟨k, hk⟩ : Fin n) 1)) :=
    fun k hk ↦ isCrossedHom_crossedHom χ _
  have hDc : ∀ (k : ℕ) (hk : k < n), Continuous (crossedHom χ (Pi.single (⟨k, hk⟩ : Fin n) 1)) :=
    fun k hk ↦ continuous_crossedHom χ _
  have hDv : ∀ (k : ℕ) (hk : k < n) (j : ℕ),
      crossedHom χ (Pi.single (⟨k, hk⟩ : Fin n) 1) (x j) = if j = k then 1 else 0 :=
    fun k hk j ↦ crossedHom_single_freeProPGen χ ⟨k, hk⟩ j
  have hDv0 : ∀ (k : ℕ) (hk : k < n) (j : ℕ), j ≠ k →
      crossedHom χ (Pi.single (⟨k, hk⟩ : Fin n) 1) (x j) = 0 := fun k hk j hj ↦ by
    rw [hDv, ite_eq_right hj]
  have hDv1 : ∀ (k : ℕ) (hk : k < n),
      crossedHom χ (Pi.single (⟨k, hk⟩ : Fin n) 1) (x k) = 1 := fun k hk ↦ by
    rw [hDv, ite_eq_left rfl]
  -- Cancelling units.
  have hunit : ∀ (u v : ℤ_[2]ˣ) (a : ℤ_[2]), (u : ℤ_[2]) * v * a = 0 → a = 0 := fun u v a h ↦
    (mul_eq_zero.1 h).resolve_left (mul_ne_zero (Units.ne_zero u) (Units.ne_zero v))
  have hpow : ∀ (u : ℤ_[2]ˣ) (a : ℤ_[2]), (u : ℤ_[2]) ^ q * a = 0 → a = 0 := fun u a h ↦
    (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ (Units.ne_zero u))
  -- The value of a crossed homomorphism on the relator, in terms of its three factors.
  have hexp : ∀ F : freeProP 2 (Fin n) → ℤ_[2], IsCrossedHom χ F →
      F (P * C * T) = (χ P : ℤ_[2]) * χ C * F T + ((χ P : ℤ_[2]) * F C + F P) :=
    fun F hF ↦ by rw [hF.map_mul, hF.map_mul, map_mul, Units.val_mul]
  -- A crossed homomorphism vanishing at `x₁` vanishes at `x₁^{2+α}`.
  have hFP : ∀ F : freeProP 2 (Fin n) → ℤ_[2], IsCrossedHom χ F → Continuous F → F (x 0) = 0 →
      F P = 0 := fun F hF hFc h ↦
    hF.map_padicPow_eq_zero_of_eq_zero hFc (isProP_freeProP 2 (Fin n)) h _
  -- A crossed homomorphism vanishing at `x₁` and `x₂` vanishes at `(x₁, x₂)`.
  have hFC : ∀ F : freeProP 2 (Fin n) → ℤ_[2], IsCrossedHom χ F → F (x 0) = 0 → F (x 1) = 0 →
      F C = 0 := fun F hF h₀ h₁ ↦ hF.map_labuteComm_eq_zero_of_eq_zero h₀ h₁
  -- A crossed homomorphism vanishing at `x₃, …, x_n` vanishes on the tail.
  have hFT0 : ∀ F : freeProP 2 (Fin n) → ℤ_[2], IsCrossedHom χ F →
      (∀ j, 2 ≤ j → F (x j) = 0) → F T = 0 := fun F hF h ↦ by
    simp only [hT, hF.map_demushkinWordNeTwo]
    rw [Finset.sum_eq_zero fun i _ ↦
      hF.map_labuteComm_eq_zero_of_eq_zero (h _ (by omega)) (h _ (by omega)), mul_zero,
      h 2 le_rfl, mul_zero, add_zero]
  -- A crossed homomorphism vanishing at `x₃, …, x_n` except on the pair `(x_{2i+3}, x_{2i+4})`
  -- sees only that commutator factor and the `q`-th power of `x₃` on the tail.
  have hFT1 : ∀ i₀, i₀ < (n - 2) / 2 → ∀ F : freeProP 2 (Fin n) → ℤ_[2], IsCrossedHom χ F →
      (∀ j, 2 ≤ j → j ≠ 2 * i₀ + 2 → j ≠ 2 * i₀ + 3 → F (x j) = 0) →
      F T = (χ (x 2) : ℤ_[2]) ^ q * F (labuteComm (x (2 * i₀ + 2)) (x (2 * i₀ + 3))) +
        (∑ j ∈ Finset.range q, (χ (x 2) : ℤ_[2]) ^ j) * F (x 2) := fun i₀ hi₀ F hF h ↦ by
    simp only [hT, hF.map_demushkinWordNeTwo]
    rw [Finset.sum_eq_single i₀ (fun i _ hi ↦ hF.map_labuteComm_eq_zero_of_eq_zero
      (h _ (by omega) (by omega) (by omega)) (h _ (by omega) (by omega) (by omega)))
      fun h' ↦ absurd (Finset.mem_range.2 hi₀) h']
  -- `D_2` forces `χ(x₁) = 1`.
  have h0 : χ (x 0) = 1 := by
    have h := hkill _ (hDc 1 (by omega)) (hD 1 (by omega))
    rw [hexp _ (hD 1 (by omega)),
      hFP _ (hD 1 (by omega)) (hDc 1 (by omega)) (hDv0 _ _ 0 (by omega)),
      hFT0 _ (hD 1 (by omega)) (fun j hj ↦ hDv0 _ _ j (by omega))] at h
    simp only [mul_zero, zero_add, add_zero] at h
    exact (hD 1 (by omega)).eq_one_of_map_labuteComm_eq_zero_right (hDv0 _ _ 0 (by omega))
      (hDv1 1 (by omega)) ((Units.mul_right_eq_zero _).1 h)
  -- `D_4` forces `χ(x₃) = 1`.
  have h2 : χ (x 2) = 1 := by
    have h := hkill _ (hDc 3 hn3) (hD 3 hn3)
    rw [hexp _ (hD 3 hn3), hFP _ (hD 3 hn3) (hDc 3 hn3) (hDv0 _ _ 0 (by omega)),
      hFC _ (hD 3 hn3) (hDv0 _ _ 0 (by omega)) (hDv0 _ _ 1 (by omega)),
      hFT1 0 (by omega) _ (hD 3 hn3) (fun j _ _ _ ↦ hDv0 _ _ j (by omega)),
      hDv0 _ _ 2 (by omega)] at h
    simp only [Nat.zero_add, mul_zero, add_zero] at h
    exact (hD 3 hn3).eq_one_of_map_labuteComm_eq_zero_right (hDv0 _ _ _ (by omega))
      (hDv1 3 hn3) (hpow _ _ (hunit _ _ _ h))
  -- `D_k` at the partner `x_k` of `x_j` in its commutator factor forces `χ(x_j) = 1`, `j ≥ 5`.
  have hval : ∀ j, 4 ≤ j → j < n → χ (x j) = 1 := by
    intro j hj₄ hjn
    rcases Nat.even_or_odd' j with ⟨i, hj | hj⟩
    · -- `x_j = x_{2i+1}`, with partner `x_{2i+2}`.
      have hk : 2 * i + 1 < n := by omega
      have h := hkill _ (hDc _ hk) (hD _ hk)
      have hT' := hFT1 (i - 1) (by omega) _ (hD _ hk) fun j' _ _ _ ↦ hDv0 _ hk j' (by omega)
      rw [show 2 * (i - 1) + 2 = 2 * i by omega, show 2 * (i - 1) + 3 = 2 * i + 1 by omega,
        hDv0 _ hk 2 (by omega), mul_zero, add_zero] at hT'
      rw [hexp _ (hD _ hk), hFP _ (hD _ hk) (hDc _ hk) (hDv0 _ _ 0 (by omega)),
        hFC _ (hD _ hk) (hDv0 _ _ 0 (by omega)) (hDv0 _ _ 1 (by omega)), hT'] at h
      simp only [mul_zero, add_zero] at h
      rw [hj]
      exact (hD _ hk).eq_one_of_map_labuteComm_eq_zero_right (hDv0 _ hk _ (by omega))
        (hDv1 _ hk) (hpow _ _ (hunit _ _ _ h))
    · -- `x_j = x_{2i+2}`, with partner `x_{2i+1}`.
      have hk : 2 * i < n := by omega
      have h := hkill _ (hDc _ hk) (hD _ hk)
      have hT' := hFT1 (i - 1) (by omega) _ (hD _ hk) fun j' _ _ _ ↦ hDv0 _ hk j' (by omega)
      rw [show 2 * (i - 1) + 2 = 2 * i by omega, show 2 * (i - 1) + 3 = 2 * i + 1 by omega,
        hDv0 _ hk 2 (by omega), mul_zero, add_zero] at hT'
      rw [hexp _ (hD _ hk), hFP _ (hD _ hk) (hDc _ hk) (hDv0 _ _ 0 (by omega)),
        hFC _ (hD _ hk) (hDv0 _ _ 0 (by omega)) (hDv0 _ _ 1 (by omega)), hT'] at h
      simp only [mul_zero, add_zero] at h
      rw [hj]
      exact (hD _ hk).eq_one_of_map_labuteComm_eq_zero_left (hDv1 _ hk)
        (hDv0 _ hk _ (by omega)) (hpow _ _ (hunit _ _ _ h))
  refine ⟨fun j hj₁ hj₃ ↦ ?_, ?_, ?_⟩
  · by_cases hjn : j < n
    · rcases Nat.lt_or_ge j 4 with hj₄ | hj₄
      · rcases (by omega : j = 0 ∨ j = 2) with rfl | rfl
        · exact h0
        · exact h2
      · exact hval j hj₄ hjn
    · rw [hx, freeProPGen_eq_one_of_le 2 (not_lt.1 hjn), map_one]
  · -- `D_1`: `(2 + α) + χ(x₂)⁻¹ - 1 = 0`.
    have h := hkill _ (hDc 0 (by omega)) (hD 0 (by omega))
    have hχP : χ P = 1 := by
      have e : χ P = isProP_units_padicInt_two.padicPow (χ (x 0)) (2 + α) :=
        (isProP_freeProP 2 (Fin n)).map_padicPow isProP_units_padicInt_two
          (χ : freeProP 2 (Fin n) →* ℤ_[2]ˣ) χ.continuous (x 0) (2 + α)
      rw [e, h0, IsProP.one_padicPow]
    have hDP : crossedHom χ (Pi.single (⟨0, by omega⟩ : Fin n) 1) P = 2 + α := by
      rw [hP, (hD 0 (by omega)).map_padicPow_of_eq_one (hDc 0 (by omega))
        (isProP_freeProP 2 (Fin n)) h0, hDv1 0 (by omega), mul_one]
    have hc := (hD 0 (by omega)).mul_mul_map_labuteComm (x 0) (x 1)
    rw [h0, Units.val_one, one_mul, sub_self, zero_mul, add_zero, hDv1 0 (by omega), mul_one] at hc
    rw [hexp _ (hD 0 (by omega)), hFT0 _ (hD 0 (by omega)) (fun j hj ↦ hDv0 _ _ j (by omega)),
      hDP, hχP] at h
    simp only [Units.val_one, one_mul, mul_zero, zero_add] at h
    linear_combination (χ (x 1) : ℤ_[2]) * h - hc
  · -- `D_3`: `q + χ(x₄)⁻¹ - 1 = 0`.
    have h := hkill _ (hDc 2 (by omega)) (hD 2 (by omega))
    have hc := (hD 2 (by omega)).mul_mul_map_labuteComm (x 2) (x 3)
    rw [h2, Units.val_one, one_mul, sub_self, zero_mul, add_zero, hDv1 2 (by omega), mul_one] at hc
    rw [hexp _ (hD 2 (by omega)),
      hFP _ (hD 2 (by omega)) (hDc 2 (by omega)) (hDv0 _ _ 0 (by omega)),
      hFC _ (hD 2 (by omega)) (hDv0 _ _ 0 (by omega)) (hDv0 _ _ 1 (by omega)),
      hFT1 0 (by omega) _ (hD 2 (by omega)) (fun j _ _ _ ↦ hDv0 _ _ j (by omega)),
      hDv1 2 (by omega), h2] at h
    simp only [Nat.zero_add, Units.val_one, one_pow, one_mul, mul_one, mul_zero, add_zero,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    have h' := hunit _ _ _ h
    linear_combination hc - (χ (x 3) : ℤ_[2]) * h'

/-! ### Labute's Theorem 6 -/

/-- **Labute's normal form for the dyadic Demushkin groups of even rank with image `{±1} × U^(f)`**
(Labute, Theorem 6). Let `r ∈ Φ(F)` be a relator of the free pro-`2` group on an even number
`n ≥ 4` of generators presenting a Demushkin group `G = ⟨x₁, …, x_n ∣ r⟩` whose canonical character
has image `V^(f) = {±1} × U^(f)` for a finite `f ≥ 2`. Then a continuous automorphism of `F`
carries `r` to `x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem exists_continuousMulEquiv_apply_eq_demushkinWordTwoEven_of_range_eq
    {r : freeProP 2 (Fin n)} (hr : r ∈ proPFrattini 2 (freeProP 2 (Fin n)))
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r})) (hn : Even n) (hn3 : 3 < n) {f : ℕ}
    (hf : 2 ≤ f) (hA : (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f) :
    ∃ e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n),
      e r = demushkinWordTwoEven 0 f n (freeProPGen 2 n) := by
  have hn2 : 2 ≤ n := by omega
  -- Step 0: `q(G) = 2`, because `-1 ∉ 1 + 4ℤ_2` is a value of the canonical character.
  have hq : demushkinQ hG = 2 := by
    by_contra hq
    have hle := (demushkinQ_ne_two_iff_range_demushkinCharacter_le hG).1 hq rfl
    have := neg_one_mem_unitsPrincipal_two_iff.1 (hle (hA ▸ neg_one_mem_unitsPlusMinus f))
    omega
  -- Step 1: the exact normal form `x₁^{2+α} (x₁, x₂) x₃^{q} (x₃, x₄) ⋯` of the relator.
  obtain ⟨e₀, α, q, hα, hq', he₀⟩ :=
    hG.exists_continuousMulEquiv_apply_eq_padicPow_mul_labuteComm_mul_demushkinWordNeTwo hn hr hq
  set rex := (isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 0) (2 + α) *
    labuteComm (freeProPGen 2 n 0) (freeProPGen 2 n 1) *
    demushkinWordNeTwo q (n - 2) (fun i ↦ freeProPGen 2 n (i + 2)) with hrex
  have hr₁ : r ∈ pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1 :=
    (pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two).symm.le hr
  have hrex₁ : rex ∈ pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1 := he₀ ▸
    (e₀ : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom.map_pLowerCentralSeries_le
      (e₀ : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous 1 ⟨r, hr₁, rfl⟩
  have hrexΦ : rex ∈ proPFrattini 2 (freeProP 2 (Fin n)) :=
    (pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two).le hrex₁
  -- Step 2: the presented group on `rex` is Demushkin with the same image of the canonical
  -- character; `χ₁` is its canonical character read on `F`, and every continuous crossed
  -- homomorphism for `χ₁` kills `rex`.
  have hG₁ : IsDemushkin 2 (presentedProP 2 (Fin n) {rex}) :=
    IsDemushkin.of_equiv 2 hG (presentedProP.congrSingleton e₀ he₀)
  have hA₁ : (demushkinCharacter hG₁).toMonoidHom.range = unitsPlusMinus f := by
    rw [range_demushkinCharacter_of_equiv hG hG₁ (presentedProP.congrSingleton e₀ he₀), hA]
  set χ₁ : freeProP 2 (Fin n) →ₜ* ℤ_[2]ˣ :=
    (demushkinCharacter hG₁).comp (presentedProP.mk 2 {rex}) with hχ₁
  have hχ₁apply : ∀ g, χ₁ g = demushkinCharacter hG₁ (presentedProP.mk 2 {rex} g) := fun g ↦ by
    rw [hχ₁, ContinuousMonoidHom.coe_comp, Function.comp_apply]
  have hkill₁ : ∀ D : freeProP 2 (Fin n) → ℤ_[2], Continuous D → IsCrossedHom χ₁ D →
      D rex = 0 := fun D hDc hD ↦
    (presentedProP.hasPrescriptionProperty_iff_forall_isCrossedHom_eq_zero
      (Set.singleton_subset_iff.2 hrexΦ) _).1 (hasPrescriptionProperty_demushkinCharacter hG₁) D hDc
      hD _ rfl
  have hχ₁rex : χ₁ rex = 1 := by
    rw [hχ₁apply, presentedProP.mk_relator _ (Set.mem_singleton _), map_one]
  -- Step 3: the values of `χ₁` on the generators.
  obtain ⟨hv, h₁, h₃⟩ :=
    apply_eq_of_forall_isCrossedHom_eq_zero_padicPow_mul_labuteComm_mul hn hn3 χ₁ α q hkill₁
  -- The image of `χ₁` is `V^(f)`, and it is the closure of the subgroup generated by `χ₁(x₂)` and
  -- `χ₁(x₄)`.
  have hrange : χ₁.toMonoidHom.range = (demushkinCharacter hG₁).toMonoidHom.range := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨g, rfl⟩
      exact ⟨presentedProP.mk 2 {rex} g, (hχ₁apply g).symm⟩
    · rintro _ ⟨y, rfl⟩
      obtain ⟨g, rfl⟩ := presentedProP.mk_surjective 2 {rex} y
      exact ⟨g, hχ₁apply g⟩
  have hV : (zpowers (χ₁ (freeProPGen 2 n 1)) ⊔
      zpowers (χ₁ (freeProPGen 2 n 3))).topologicalClosure = unitsPlusMinus f := by
    rw [← hA₁, ← hrange]
    refine (MonoidHom.range_eq_topologicalClosure_of_topologicalClosure_closure_eq_top
      (topologicalClosure_closure_range_of_eq_top 2 (Fin n)) χ₁.continuous
      (MonoidHom.isClosed_range_of_continuous χ₁.continuous) ?_
      (sup_le (zpowers_le.2 ⟨_, rfl⟩) (zpowers_le.2 ⟨_, rfl⟩))).symm
    rintro _ ⟨j, rfl⟩
    rw [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass, ← freeProPGen_val]
    by_cases hj₁ : (j : ℕ) = 1
    · rw [hj₁]
      exact le_topologicalClosure _ (mem_sup_left (mem_zpowers _))
    by_cases hj₃ : (j : ℕ) = 3
    · rw [hj₃]
      exact le_topologicalClosure _ (mem_sup_right (mem_zpowers _))
    rw [hv j hj₁ hj₃]
    exact one_mem _
  -- `-χ₁(x₂) ∈ U^(f)`: it lies in `1 + 4ℤ_2` since `4 ∣ α`, and `χ₁(x₂) ∈ V^(f)`.
  have hneg₂ : -χ₁ (freeProPGen 2 n 1) ∈ unitsPrincipal 2 2 :=
    (neg_mem_unitsPrincipal_iff_of_val_mul_one_add_eq_neg_one h₁).2
      (by rw [show (2 : ℤ_[2]) ^ 2 = 4 by norm_num]; exact hα)
  have hnegf : -χ₁ (freeProPGen 2 n 1) ∈ unitsPrincipal 2 f := by
    have hmem : χ₁ (freeProPGen 2 n 1) ∈ unitsPlusMinus f :=
      hV ▸ le_topologicalClosure _ (mem_sup_left (mem_zpowers _))
    rcases mem_unitsPlusMinus_iff.1 hmem with h | h
    · exact absurd (unitsPrincipal_antitone 2 hf h)
        (notMem_unitsPrincipal_two_of_neg_mem le_rfl hneg₂)
    · exact h
  -- The level of `χ₁(x₄)` is `f`: it is not `∞`, since `V^(f)` is not procyclic, ...
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h3 : χ₁ (freeProPGen 2 n 3) = 1 := by simpa using h₃
    rw [h3, zpowers_one_eq_bot, sup_bot_eq] at hV
    exact not_exists_topologicalClosure_zpowers_eq_unitsPlusMinus hf ⟨_, hV⟩
  obtain ⟨g, hg, rfl⟩ : ∃ g, 2 ≤ g ∧ q = 2 ^ g := hq'.resolve_left hq0
  have h₃g : (χ₁ (freeProPGen 2 n 3) : ℤ_[2]) * (1 - ((2 : ℕ) : ℤ_[2]) ^ g) = 1 := by
    push_cast at h₃ ⊢
    exact h₃
  have hmem₃ : ∀ k, χ₁ (freeProPGen 2 n 3) ∈ unitsPrincipal 2 k ↔ k ≤ g := fun k ↦
    mem_unitsPrincipal_iff_of_val_mul_one_sub_pow_eq_one h₃g
  -- ... it is at least `f`, since `χ₁(x₄)` lies in the even part `U^(f)` of `V^(f)`, ...
  have hfg : f ≤ g := by
    have hmem : χ₁ (freeProPGen 2 n 3) ∈ unitsPlusMinus f ⊓ unitsPrincipal 2 2 :=
      mem_inf.2 ⟨hV ▸ le_topologicalClosure _ (mem_sup_right (mem_zpowers _)), (hmem₃ 2).2 hg⟩
    rw [unitsPlusMinus_inf_unitsPrincipal_two hf] at hmem
    exact (hmem₃ f).1 hmem
  -- ... and it is at most `f`: otherwise the image would lie in `V^(f+1)`, or in the twisted
  -- subgroup generated by `χ₁(x₂)`, which does not contain `-1`.
  have hgf : g = f := by
    by_contra hne
    have h3f : χ₁ (freeProPGen 2 n 3) ∈ unitsPrincipal 2 (f + 1) := (hmem₃ _).2 (by omega)
    by_cases hneg' : -χ₁ (freeProPGen 2 n 1) ∈ unitsPrincipal 2 (f + 1)
    · have hle : unitsPlusMinus f ≤ unitsPlusMinus (f + 1) := by
        rw [← hV]
        exact topologicalClosure_minimal _
          (sup_le (zpowers_le.2 (mem_unitsPlusMinus_iff.2 (Or.inr hneg')))
            (zpowers_le.2 (unitsPrincipal_le_unitsPlusMinus _ h3f))) (isClosed_unitsPlusMinus _)
      have := (unitsPlusMinus_inj hf (by omega)).1
        (le_antisymm hle (unitsPlusMinus_antitone (Nat.le_succ f)))
      omega
    · have hle : unitsPlusMinus f ≤ (zpowers (χ₁ (freeProPGen 2 n 1))).topologicalClosure := by
        rw [← hV]
        exact topologicalClosure_minimal _ (sup_le (le_topologicalClosure _) (zpowers_le.2
          (unitsPrincipal_succ_le_topologicalClosure_zpowers_two hf hnegf hneg' h3f)))
          (isClosed_topologicalClosure _)
      exact neg_one_notMem_topologicalClosure_zpowers_two hf hnegf hneg'
        (hle (neg_one_mem_unitsPlusMinus f))
  subst hgf
  have h₃' : (χ₁ (freeProPGen 2 n 3) : ℤ_[2]) * (1 - (2 : ℤ_[2]) ^ g) = 1 := by
    have h := h₃g
    push_cast at h
    exact h
  -- `χ₁(x₄)` topologically generates `U^(f)`, so `(-χ₁(x₂))⁻¹ ∈ U^(f)` is a `2`-adic power of it.
  have hgen : (zpowers (χ₁ (freeProPGen 2 n 3))).topologicalClosure = unitsPrincipal 2 g :=
    topologicalClosure_zpowers_eq_unitsPrincipal_of_val_mul_one_sub_pow_eq_one (by omega)
      (fun _ ↦ hg) h₃g
  obtain ⟨d, hd⟩ : ∃ d : ℤ_[2], isProP_units_padicInt_two.padicPow (χ₁ (freeProPGen 2 n 3)) d =
      (-χ₁ (freeProPGen 2 n 1))⁻¹ := by
    rw [← isProP_units_padicInt_two.mem_topologicalClosure_closure_singleton_iff,
      ← zpowers_eq_closure, hgen]
    exact inv_mem hnegf
  -- Step 4: the symplectic transvection pair `x₂ ↦ x₂ x₄^d`, `x₃ ↦ x₃ x₁^{-d}` makes `χ(x₂) = -1`.
  set χ₂ : freeProP 2 (Fin n) →ₜ* ℤ_[2]ˣ :=
    χ₁.comp (symplecticTransvection hn3 d : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)) with hχ₂
  have hχ₂apply : ∀ y, χ₂ y = χ₁ (symplecticTransvection hn3 d y) := fun y ↦ by
    rw [hχ₂, ContinuousMonoidHom.coe_comp, Function.comp_apply, ContinuousMonoidHom.coe_coe]
  have hχ₂₁ : χ₂ (freeProPGen 2 n 1) = -1 := by
    have e : χ₁ ((isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 3) d) =
        isProP_units_padicInt_two.padicPow (χ₁ (freeProPGen 2 n 3)) d :=
      (isProP_freeProP 2 (Fin n)).map_padicPow isProP_units_padicInt_two
        (χ₁ : freeProP 2 (Fin n) →* ℤ_[2]ˣ) χ₁.continuous (freeProPGen 2 n 3) d
    rw [hχ₂apply, symplecticTransvection_freeProPGen_one, map_mul, e, hd, mul_inv_eq_iff_eq_mul,
      neg_one_mul, neg_neg]
  have hχ₂₂ : χ₂ (freeProPGen 2 n 2) = 1 := by
    have e : χ₁ ((isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 0) (-d)) =
        isProP_units_padicInt_two.padicPow (χ₁ (freeProPGen 2 n 0)) (-d) :=
      (isProP_freeProP 2 (Fin n)).map_padicPow isProP_units_padicInt_two
        (χ₁ : freeProP 2 (Fin n) →* ℤ_[2]ˣ) χ₁.continuous (freeProPGen 2 n 0) (-d)
    rw [hχ₂apply, symplecticTransvection_freeProPGen_two, map_mul, e, hv 0 (by omega) (by omega),
      hv 2 (by omega) (by omega), IsProP.one_padicPow, mul_one]
  have hχ₂₃ : χ₂ (freeProPGen 2 n 3) = χ₁ (freeProPGen 2 n 3) := by
    rw [hχ₂apply, symplecticTransvection_freeProPGen_of_ne hn3 d 3 (by omega) (by omega)]
  have hχ₂ne : ∀ j : ℕ, j ≠ 1 → j ≠ 3 → χ₂ (freeProPGen 2 n j) = 1 := fun j hj₁ hj₃ ↦ by
    by_cases hj₂ : j = 2
    · exact hj₂ ▸ hχ₂₂
    · rw [hχ₂apply, symplecticTransvection_freeProPGen_of_ne hn3 d j hj₁ hj₂]
      exact hv j hj₁ hj₃
  -- The relator `r₂` in the new basis: every crossed homomorphism for `χ₂` kills it.
  set r₂ := (symplecticTransvection hn3 d).symm rex
  have hr₂₁ : r₂ ∈ pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1 :=
    MonoidHom.map_pLowerCentralSeries_le
      ((symplecticTransvection hn3 d).symm : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom
      ((symplecticTransvection hn3 d).symm : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous
      1 ⟨rex, hrex₁, rfl⟩
  have hkill₂ : ∀ D : freeProP 2 (Fin n) → ℤ_[2], Continuous D → IsCrossedHom χ₂ D →
      D r₂ = 0 := fun D hDc hD ↦
    hkill₁ _ (hDc.comp ((symplecticTransvection hn3 d).symm :
        freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous)
      (hD.comp ((symplecticTransvection hn3 d).symm : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n))
        fun y ↦ by
          rw [hχ₂apply, ContinuousMonoidHom.coe_coe,
            (symplecticTransvection hn3 d).apply_symm_apply])
  -- `r₂` has the class of the normal-form word in `gr_1(F)`.
  have hw₀ : demushkinWordNeTwo 2 n (freeProPGen 2 n) ∈
      pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1 :=
    demushkinWordNeTwo_mem_pLowerCentralSeries_one dvd_rfl n _
  have hcls : gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨rex, hrex₁⟩ =
      gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordNeTwo 2 n (freeProPGen 2 n), hw₀⟩ := by
    rw [gradedMk_eq_gradedMk_iff]
    have hx0 : freeProPGen 2 n 0 = of ⟨0, by omega⟩ := freeProPGen_of_lt 2 (by omega)
    have hx2 : freeProPGen 2 n 2 = of ⟨2, by omega⟩ := freeProPGen_of_lt 2 (by omega)
    have hPα : ((isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 0) α :
        freeProP 2 (Fin n) ⧸ pLowerCentralSeries 2 (freeProP 2 (Fin n)) (1 + 1)) = 1 := by
      rw [QuotientGroup.eq_one_iff, hx0, padicPow_mem_pLowerCentralSeries_iff,
        show ((2 : ℕ) : ℤ_[2]) ^ (1 + 1) = 4 by norm_num]
      exact hα
    have hT2 : ((freeProPGen 2 n 2 ^ 2 ^ g : freeProP 2 (Fin n)) :
        freeProP 2 (Fin n) ⧸ pLowerCentralSeries 2 (freeProP 2 (Fin n)) (1 + 1)) = 1 := by
      rw [QuotientGroup.eq_one_iff, ← (isProP_freeProP 2 (Fin n)).padicPow_natCast, hx2,
        padicPow_mem_pLowerCentralSeries_iff, Nat.cast_pow, Nat.cast_ofNat]
      exact pow_dvd_pow 2 (by omega)
    dsimp only
    rw [hrex, (isProP_freeProP 2 (Fin n)).padicPow_add, (isProP_freeProP 2 (Fin n)).padicPow_ofNat,
      demushkinWordNeTwo_eq_pow_mul_labuteComm_mul 2 hn2, demushkinWordNeTwo_def (2 ^ g),
      demushkinWordNeTwo_def 0, pow_zero, one_mul]
    simp only [QuotientGroup.mk_mul, hPα, hT2, mul_one, one_mul]
  have hw_f : demushkinWordTwoEven 0 g n (freeProPGen 2 n) ∈
      pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1 :=
    demushkinWordTwoEven_mem_pLowerCentralSeries_one (dvd_zero 2) (by omega) n _
  have hcls₂ : gradedMk 2 (freeProP 2 (Fin n)) 1
      ⟨demushkinWordTwoEven 0 g n (freeProPGen 2 n), hw_f⟩ =
      gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨r₂, hr₂₁⟩ := by
    -- Apply the graded map of the transvection pair, which is injective and fixes the class of
    -- the normal-form word.
    have hinj : Function.Injective (gradedMap 2
        (symplecticTransvection hn3 d : freeProP 2 (Fin n) →* freeProP 2 (Fin n))
        (map_continuous (symplecticTransvection hn3 d)) 1) :=
      fun a b hab ↦ by
        rw [← gradedMap_symm_gradedMap (symplecticTransvection hn3 d) 1 a,
          ← gradedMap_symm_gradedMap (symplecticTransvection hn3 d) 1 b, hab]
    have h : gradedMap 2
        (symplecticTransvection hn3 d : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom
        (symplecticTransvection hn3 d : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous 1
          (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨r₂, hr₂₁⟩) =
        gradedMap 2
        (symplecticTransvection hn3 d : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom
        (symplecticTransvection hn3 d : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous 1
          (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordNeTwo 2 n (freeProPGen 2 n), hw₀⟩) := by
      rw [gradedMap_symplecticTransvection_gradedMk_demushkinWordNeTwo hn3 d dvd_rfl,
        gradedMap_gradedMk, ← hcls]
      congr 1
      exact Subtype.ext ((symplecticTransvection hn3 d).apply_symm_apply rex)
    exact (gradedMk_demushkinWordTwoEven_eq_gradedMk_demushkinWordNeTwo (dvd_zero 2) hg hn2 _).trans
      (hinj h).symm
  -- `r₂` lies in the kernel of the exponent sum at `x₄`: it is killed by `χ₂²`, whose kernel is
  -- that exponent-sum kernel.
  have hr₂X : r₂ ∈ exponentSumKer 2 (Fin n) ⟨3, hn3⟩ := by
    have hker : exponentSumKer 2 (Fin n) ⟨3, hn3⟩ = (χ₂ ^ 2).toMonoidHom.ker := by
      refine (χ₂ ^ 2).exponentSumKer_eq_ker (fun j hj ↦ ?_) ?_
      · rw [ContinuousMonoidHom.pow_apply, ← freeProPGen_val]
        by_cases hj₁ : (j : ℕ) = 1
        · rw [hj₁, hχ₂₁]
          norm_num
        · rw [hχ₂ne j hj₁ fun h ↦ hj (Fin.ext h), one_pow]
      · rw [ContinuousMonoidHom.pow_apply, ← freeProPGen_val, hχ₂₃]
        have hmem : χ₁ (freeProPGen 2 n 3) ^ 2 ∈ unitsPrincipal 2 (g + 1) := by
          simpa using pow_pow_mem_unitsPrincipal (by omega) ((hmem₃ g).2 le_rfl) 1
        have hnmem : χ₁ (freeProPGen 2 n 3) ^ 2 ∉ unitsPrincipal 2 (g + 1 + 1) := by
          simpa using pow_pow_notMem_unitsPrincipal (by omega) (fun _ ↦ hg) ((hmem₃ g).2 le_rfl)
            (fun h ↦ by have := (hmem₃ _).1 h; omega) 1
        exact not_isOfFinOrder_of_mem_unitsPrincipal (by omega) (fun _ ↦ by omega) hmem
          fun h ↦ hnmem (h ▸ one_mem _)
    rw [hker, MonoidHom.mem_ker, ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass,
      ContinuousMonoidHom.pow_apply, hχ₂apply, (symplecticTransvection hn3 d).apply_symm_apply,
      hχ₁rex, one_pow]
  -- Step 5: the constrained successive approximation inside the exponent-sum kernel.
  obtain ⟨e₃, -, he₃⟩ :=
    exists_continuousMulEquiv_apply_demushkinWordTwoEven_zero_eq_of_forall_crossedHom_eq_zero hn
      hn3 hg (by rw [← freeProPGen_val]; exact hχ₂₁)
      (by rw [← freeProPGen_val]; exact hχ₂₃ ▸ h₃')
      (fun j hj₁ hj₃ ↦ by
        rw [← freeProPGen_val]
        exact hχ₂ne j (fun h ↦ hj₁ (Fin.ext h)) fun h ↦ hj₃ (Fin.ext h))
      ⟨r₂, hr₂₁⟩ hcls₂ hr₂X
      fun i _ ↦ hkill₂ _ (continuous_crossedHom χ₂ _) (isCrossedHom_crossedHom χ₂ _)
  refine ⟨(e₀.trans (symplecticTransvection hn3 d).symm).trans e₃.symm, ?_⟩
  rw [ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.trans_apply, he₀, e₃.symm_apply_eq]
  exact he₃.symm

/-- **Labute's normal form for a one-relator dyadic Demushkin group of even rank with image
`{±1} × U^(f)`.** Let `r ∈ Φ(F)` be a relator of the free pro-`2` group on an even number `n ≥ 4`
of generators presenting a Demushkin group whose canonical character has image `V^(f)`, `f ≥ 2`
finite. Then `⟨x₁, …, x_n ∣ r⟩` is topologically isomorphic to
`⟨x₁, …, x_n ∣ x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)⟩`. -/
theorem exists_continuousMulEquiv_presentedProP_demushkinWordTwoEven_of_range_eq
    {r : freeProP 2 (Fin n)} (hr : r ∈ proPFrattini 2 (freeProP 2 (Fin n)))
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r})) (hn : Even n) (hn3 : 3 < n) {f : ℕ}
    (hf : 2 ≤ f) (hA : (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f) :
    Nonempty (presentedProP 2 (Fin n) {r} ≃ₜ*
      presentedProP 2 (Fin n) {demushkinWordTwoEven 0 f n (freeProPGen 2 n)}) := by
  obtain ⟨e, he⟩ :=
    exists_continuousMulEquiv_apply_eq_demushkinWordTwoEven_of_range_eq hr hG hn hn3 hf hA
  exact ⟨presentedProP.congrSingleton e he⟩

end freeProP

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **Labute's normal form for a dyadic Demushkin group of even rank with image `{±1} × U^(f)`,
intrinsic form** (Labute, Theorem 6). A Demushkin group `G` at `p = 2` of even rank `n ≥ 4` whose
canonical character has image `V^(f) = {±1} × U^(f)` for a finite `f ≥ 2` is topologically
isomorphic to `⟨x₁, …, x_n ∣ x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)⟩` on
`n = demushkinRank hG` generators. -/
theorem IsDemushkin.exists_continuousMulEquiv_presentedProP_demushkinWordTwoEven_of_range_eq
    (hG : IsDemushkin 2 G) (hn : Even (demushkinRank hG)) (hn3 : 3 < demushkinRank hG) {f : ℕ}
    (hf : 2 ≤ f) (hA : (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f) :
    Nonempty (G ≃ₜ* presentedProP 2 (Fin (demushkinRank hG))
      {demushkinWordTwoEven 0 f (demushkinRank hG) (freeProPGen 2 (demushkinRank hG))}) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hG.exists_mem_proPFrattini_continuousMulEquiv_presentedProP_fin
  have : Nonempty (Fin (demushkinRank hG)) := ⟨⟨0, hG.demushkinRank_pos⟩⟩
  have hG' : IsDemushkin 2 (presentedProP 2 (Fin (demushkinRank hG)) {r}) :=
    isDemushkin_of_nondegenerate_degreeOneForm hr (ContinuousMulEquiv.refl _)
      (hG.nondegenerate_degreeOneForm hr e)
  have hA' : (demushkinCharacter hG').toMonoidHom.range = unitsPlusMinus f := by
    rw [range_demushkinCharacter_of_equiv hG hG' e.symm, hA]
  obtain ⟨e'⟩ :=
    freeProP.exists_continuousMulEquiv_presentedProP_demushkinWordTwoEven_of_range_eq hr hG' hn
      hn3 hf hA'
  exact ⟨e.symm.trans e'⟩

/-- **Uniqueness of the dyadic Demushkin groups of even rank with image `{±1} × U^(f)`** (Labute,
Theorem 6). Two Demushkin groups at `p = 2` of the same even rank `n ≥ 4` whose canonical
characters have the same image `V^(f) = {±1} × U^(f)`, `f ≥ 2` finite, are topologically
isomorphic. -/
theorem IsDemushkin.nonempty_continuousMulEquiv_of_even_demushkinRank_of_range_eq_unitsPlusMinus
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [TotallyDisconnectedSpace H] (hG : IsDemushkin 2 G) (hH : IsDemushkin 2 H)
    (hn : demushkinRank hG = demushkinRank hH) (heven : Even (demushkinRank hG))
    (hn3 : 3 < demushkinRank hG) {f : ℕ} (hf : 2 ≤ f)
    (hA : (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f)
    (hB : (demushkinCharacter hH).toMonoidHom.range = unitsPlusMinus f) :
    Nonempty (G ≃ₜ* H) := by
  obtain ⟨e⟩ :=
    hG.exists_continuousMulEquiv_presentedProP_demushkinWordTwoEven_of_range_eq heven hn3 hf hA
  obtain ⟨e'⟩ :=
    hH.exists_continuousMulEquiv_presentedProP_demushkinWordTwoEven_of_range_eq (hn ▸ heven)
      (hn ▸ hn3) hf hB
  rw [hn] at e
  exact ⟨e.trans e'.symm⟩

end TauCeti
