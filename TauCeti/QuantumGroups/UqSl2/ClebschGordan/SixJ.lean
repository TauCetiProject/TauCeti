/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Recoupling

/-!
# Quantum 6j change-of-decomposition matrices

At a generic parameter `q`, the module-level recoupling equivalence `clebschGordanRecouplingEquiv`
identifies the left-first and right-first Clebsch–Gordan decompositions of the triple tensor
product `L_m^ε ⊗ L_n^δ ⊗ L_p^ζ` through the coproduct tensor associator `BialgebraModule.assoc`.
Because the signed ladder modules are simple and pairwise non-isomorphic across distinct highest
weights and signs, each pair of a left channel `(i, j)` and a right channel `(r, s)` determines a
single complex scalar `recouplingCoeff` (and inverse scalar `invRecouplingCoeff`), vanishing
whenever the two total highest weights `m + n - 2i + p - 2j` and `m + (n + p - 2r) - 2s` differ.

By Schur's lemma (`LadderModule.apply_vec_eq_schurScalar_smul`), the same scalar matrix governs
the change of decomposition under `BialgebraModule.assoc` both on the `α₀ = 1` highest-weight
vectors (`vec q _ _ 0`) and on every vector of the normalized `F`-ladder basis
`v_l = F^l w / ([1]_q ⋯ [l]_q)` (`vec q _ _ l`).

Indexing channels by their intermediate highest weights `u` (inside `L_m^ε ⊗ L_n^δ`) and `v`
(inside `L_n^δ ⊗ L_p^ζ`) at a fixed total highest weight `k` yields the six-weight quantum 6j
function `sixJ` (extended by `0` outside admissible Clebsch–Gordan channels) and the square
change-of-decomposition matrices `sixJMatrix` and `invSixJMatrix`, which are two-sided matrix
inverses.

## Main definitions

* `TauCeti.UqSl2.IsClebschGordanChannel`: admissibility predicate `k = m + n - 2j` (`j ≤ min m n`)
  for a binary Clebsch–Gordan summand `L_k` inside `L_m ⊗ L_n`, with constructive index
  `IsClebschGordanChannel.index`.
* `TauCeti.UqSl2.clebschGordanLeftInclusion`, `clebschGordanRightInclusion`,
  `clebschGordanLeftProjection`, `clebschGordanRightProjection`: triple-product channel inclusions
  and projections.
* `TauCeti.UqSl2.recouplingHom`, `invRecouplingHom`, `recouplingCoeff`, `invRecouplingCoeff`:
  channel-pair recoupling intertwiners and their Schur scalars.
* `TauCeti.UqSl2.sixJ`, `invSixJ`: the six-weight quantum 6j change-of-decomposition scalars on
  `L_m^ε ⊗ L_n^δ ⊗ L_p^ζ`.
* `TauCeti.UqSl2.LeftSixJChannel`, `RightSixJChannel`, `sixJMatrix`, `invSixJMatrix`: the
  change-of-decomposition matrices at fixed total highest weight `k`.

## Main results

* `TauCeti.UqSl2.isClebschGordanChannel_iff`: triangle and parity characterization of admissible
  binary channels.
* `TauCeti.UqSl2.assoc_clebschGordanLeftInclusion_vec`,
  `assoc_symm_clebschGordanRightInclusion_vec`: explicit triple-product change of decomposition in
  both the `α₀ = 1` (`l = 0`) and normalized `F`-ladder (`0 ≤ l ≤ k`) bases.
* `TauCeti.UqSl2.sum_invSixJ_mul_sixJ`, `sum_sixJ_mul_invSixJ`,
  `invSixJMatrix_mul_sixJMatrix`, `sixJMatrix_mul_invSixJMatrix`: orthogonality and matrix
  invertibility of the 6j matrices.
* `TauCeti.UqSl2.sixJ_add_add`, `sixJ_zero_left`, `sixJ_zero_right`: explicit boundary values,
  exhibiting the sign factor `ζ^((m + n - k) / 2)` when `p = 0`.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapters VII and XII.
* A. N. Kirillov and N. Yu. Reshetikhin, *Representations of the algebra `U_q(sl(2))`,
  `q`-orthogonal polynomials and invariants of links*, in *Infinite-Dimensional Lie Algebras and
  Groups*, World Scientific, 1989, pp. 285--339.
-/

public noncomputable section

namespace TauCeti.UqSl2

open BialgebraModule LadderModule

/-! ### Admissible Clebsch–Gordan channels -/

/-- `IsClebschGordanChannel m n k` holds when `L_k` occurs in the binary Clebsch–Gordan
decomposition of `L_m ⊗ L_n`, i.e., `k = m + n - 2j` for some `j ≤ min m n`. -/
def IsClebschGordanChannel (m n k : ℕ) : Prop :=
  ∃ j : Fin (min m n + 1), m + n - 2 * (j : ℕ) = k

/-- Definitional characterization of `IsClebschGordanChannel`. -/
theorem isClebschGordanChannel_def {m n k : ℕ} :
    IsClebschGordanChannel m n k ↔ ∃ j : Fin (min m n + 1), m + n - 2 * (j : ℕ) = k :=
  Iff.rfl

instance (m n : ℕ) : DecidablePred (IsClebschGordanChannel m n) :=
  fun _ => decidable_of_iff _ isClebschGordanChannel_def.symm

/-- Every Clebsch–Gordan channel of `L_m ⊗ L_n` has highest weight at most `m + n`. -/
theorem IsClebschGordanChannel.le_add {m n k : ℕ} (h : IsClebschGordanChannel m n k) :
    k ≤ m + n := by
  rcases h with ⟨j, rfl⟩
  omega

/-- Triangle and parity characterization of admissible binary Clebsch–Gordan channels. -/
theorem isClebschGordanChannel_iff {m n k : ℕ} :
    IsClebschGordanChannel m n k ↔
      k ≤ m + n ∧ m ≤ n + k ∧ n ≤ m + k ∧ Even (m + n - k) := by
  constructor
  · rintro ⟨j, rfl⟩
    have hj := j.isLt
    exact ⟨by omega, by omega, by omega, ⟨j, by omega⟩⟩
  · rintro ⟨hkm, hmn, hnm, r, hr⟩
    refine ⟨⟨r, by omega⟩, ?_⟩
    dsimp only
    omega

/-- The unique summand index `j : Fin (min m n + 1)` witnessing `k = m + n - 2j`, computed
explicitly as `(m + n - k) / 2`. -/
def IsClebschGordanChannel.index {m n k : ℕ} (h : IsClebschGordanChannel m n k) :
    Fin (min m n + 1) :=
  ⟨(m + n - k) / 2, by
    rcases h with ⟨j, rfl⟩
    have := j.isLt
    omega⟩

/-- The constructive index of an admissible channel recovers its highest weight `k`. -/
@[simp]
theorem IsClebschGordanChannel.sub_two_mul_index {m n k : ℕ}
    (h : IsClebschGordanChannel m n k) :
    m + n - 2 * (h.index : ℕ) = k := by
  rcases h with ⟨j, rfl⟩
  have := j.isLt
  simp only [index]
  omega

/-- Given `hu₁ : IsClebschGordanChannel m n u` and `hu₂ : IsClebschGordanChannel u p k`,
`hu₂.leftIndex hu₁` views `hu₂.index` in `Fin (min (m + n - 2 * ↑hu₁.index) p + 1)`. -/
def IsClebschGordanChannel.leftIndex {m n p u k : ℕ}
    (hu₂ : IsClebschGordanChannel u p k) (hu₁ : IsClebschGordanChannel m n u) :
    Fin (min (m + n - 2 * (hu₁.index : ℕ)) p + 1) :=
  ⟨hu₂.index, by rw [hu₁.sub_two_mul_index]; exact hu₂.index.isLt⟩

/-- Given `hv₁ : IsClebschGordanChannel n p v` and `hv₂ : IsClebschGordanChannel m v k`,
`hv₂.rightIndex hv₁` views `hv₂.index` in `Fin (min m (n + p - 2 * ↑hv₁.index) + 1)`. -/
def IsClebschGordanChannel.rightIndex {m n p v k : ℕ}
    (hv₂ : IsClebschGordanChannel m v k) (hv₁ : IsClebschGordanChannel n p v) :
    Fin (min m (n + p - 2 * (hv₁.index : ℕ)) + 1) :=
  ⟨hv₂.index, by rw [hv₁.sub_two_mul_index]; exact hv₂.index.isLt⟩

/-- `hu₂.leftIndex hu₁` has the same underlying natural-number value as `hu₂.index`. -/
@[simp]
theorem IsClebschGordanChannel.val_leftIndex {m n p u k : ℕ}
    (hu₂ : IsClebschGordanChannel u p k) (hu₁ : IsClebschGordanChannel m n u) :
    ((hu₂.leftIndex hu₁) : ℕ) = (hu₂.index : ℕ) :=
  (rfl)

/-- `hv₂.rightIndex hv₁` has the same underlying natural-number value as `hv₂.index`. -/
@[simp]
theorem IsClebschGordanChannel.val_rightIndex {m n p v k : ℕ}
    (hv₂ : IsClebschGordanChannel m v k) (hv₁ : IsClebschGordanChannel n p v) :
    ((hv₂.rightIndex hv₁) : ℕ) = (hv₂.index : ℕ) :=
  (rfl)

/-- Uniqueness of the Clebsch–Gordan summand index for a given channel weight `k`. -/
theorem IsClebschGordanChannel.index_eq_of_eq {m n k : ℕ} (h : IsClebschGordanChannel m n k)
    {j : Fin (min m n + 1)} (hj : m + n - 2 * (j : ℕ) = k) :
    h.index = j := by
  ext
  have := j.isLt
  simp only [index, ← hj]
  omega

/-- `h.index = j` holds exactly when `m + n - 2j = k`. -/
@[simp]
theorem IsClebschGordanChannel.index_eq_iff {m n k : ℕ} (h : IsClebschGordanChannel m n k)
    (j : Fin (min m n + 1)) :
    h.index = j ↔ m + n - 2 * (j : ℕ) = k :=
  ⟨fun hj => hj ▸ h.sub_two_mul_index, h.index_eq_of_eq⟩

/-- Every summand index `j : Fin (min m n + 1)` gives an admissible Clebsch–Gordan channel. -/
theorem isClebschGordanChannel_sub_two_mul {m n : ℕ} (j : Fin (min m n + 1)) :
    IsClebschGordanChannel m n (m + n - 2 * (j : ℕ)) :=
  ⟨j, rfl⟩

/-- The constructive index of `m + n - 2j` is `j`. -/
@[simp]
theorem IsClebschGordanChannel.index_sub_two_mul {m n : ℕ} (j : Fin (min m n + 1)) :
    (isClebschGordanChannel_sub_two_mul j).index = j :=
  (isClebschGordanChannel_sub_two_mul j).index_eq_of_eq rfl

/-- The leading channel `m + n` (`j = 0`) is always admissible. -/
theorem isClebschGordanChannel_add (m n : ℕ) : IsClebschGordanChannel m n (m + n) :=
  ⟨0, by simp⟩

/-- Tensoring with `L_0` on the left has `n` as its unique admissible channel. -/
@[simp]
theorem isClebschGordanChannel_zero_left {n k : ℕ} :
    IsClebschGordanChannel 0 n k ↔ k = n := by
  constructor
  · rintro ⟨j, rfl⟩
    have := j.isLt
    omega
  · rintro rfl
    exact ⟨0, by simp⟩

/-- Tensoring with `L_0` on the right has `m` as its unique admissible channel. -/
@[simp]
theorem isClebschGordanChannel_zero_right {m k : ℕ} :
    IsClebschGordanChannel m 0 k ↔ k = m := by
  constructor
  · rintro ⟨j, rfl⟩
    have := j.isLt
    omega
  · rintro rfl
    exact ⟨0, by simp⟩

/-- Admissible left intermediate highest weights `u` in `(L_m ⊗ L_n) ⊗ L_p` coupling to total
highest weight `k`. -/
abbrev LeftSixJChannel (m n p k : ℕ) : Type :=
  {u : ℕ // IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k}

/-- Admissible right intermediate highest weights `v` in `L_m ⊗ (L_n ⊗ L_p)` coupling to total
highest weight `k`. -/
abbrev RightSixJChannel (m n p k : ℕ) : Type :=
  {v : ℕ // IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k}

instance (m n p k : ℕ) : Fintype (LeftSixJChannel m n p k) :=
  Fintype.ofFinset
    (p := {u : ℕ | IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k})
    ((Finset.range (m + n + 1)).filter fun u =>
      IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k)
    fun _ => by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le h.1.le_add, h⟩⟩

instance (m n p k : ℕ) : Fintype (RightSixJChannel m n p k) :=
  Fintype.ofFinset
    (p := {v : ℕ | IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k})
    ((Finset.range (n + p + 1)).filter fun v =>
      IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k)
    fun _ => by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le h.1.le_add, h⟩⟩

/-! ### Triple-product channel inclusions, projections, and recoupling intertwiners -/

section TripleMaps

variable {q : ℂ} [Fact (q ≠ 0)] {m n p : ℕ} {ε δ ζ : ℤˣ}

/-- The leading Clebsch–Gordan highest vector `w₀` is the pure tensor `v₀ ⊗ v₀`. -/
@[simp]
theorem clebschGordanVector_zero (m : ℕ) (ε : ℤˣ) (n : ℕ) (δ : ℤˣ) :
    clebschGordanVector q m ε n δ 0 = tmul ℂ (UqSl2 q) (vec q m ε 0) (vec q n δ 0) := by
  simp [clebschGordanVector_def]

/-- Inclusion of the `(i, j)` left-associated channel into `(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ`. -/
def clebschGordanLeftInclusion (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q)
        (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ))
        (LadderModule q p ζ) :=
  (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i) LinearMap.id).comp
    (clebschGordanInclusion hq j)

/-- Definitional composite formula for `clebschGordanLeftInclusion`. -/
theorem clebschGordanLeftInclusion_def (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    clebschGordanLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) hq i j =
      (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i) LinearMap.id).comp
        (clebschGordanInclusion hq j) :=
  (rfl)

/-- Inclusion of the `(r, s)` right-associated channel into `L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)`. -/
def clebschGordanRightInclusion (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ)) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q) (LadderModule q m ε)
        (Tensor ℂ (UqSl2 q) (LadderModule q n δ) (LadderModule q p ζ)) :=
  (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq r)).comp
    (clebschGordanInclusion hq s)

/-- Definitional composite formula for `clebschGordanRightInclusion`. -/
theorem clebschGordanRightInclusion_def (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    clebschGordanRightInclusion (ε := ε) (δ := δ) (ζ := ζ) hq r s =
      (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq r)).comp
        (clebschGordanInclusion hq s) :=
  (rfl)

/-- Projection of `(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ` onto its `(i, j)` left-associated channel. -/
def clebschGordanLeftProjection (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    Tensor ℂ (UqSl2 q)
        (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ))
        (LadderModule q p ζ) →ₗ[UqSl2 q]
      LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ) :=
  (clebschGordanProjection hq j).comp
    (tensorMap ℂ (UqSl2 q) (clebschGordanProjection hq i) LinearMap.id)

/-- Definitional composite formula for `clebschGordanLeftProjection`. -/
theorem clebschGordanLeftProjection_def (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    clebschGordanLeftProjection (ε := ε) (δ := δ) (ζ := ζ) hq i j =
      (clebschGordanProjection hq j).comp
        (tensorMap ℂ (UqSl2 q) (clebschGordanProjection hq i) LinearMap.id) :=
  (rfl)

/-- Projection of `L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)` onto its `(r, s)` right-associated channel. -/
def clebschGordanRightProjection (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    Tensor ℂ (UqSl2 q) (LadderModule q m ε)
        (Tensor ℂ (UqSl2 q) (LadderModule q n δ) (LadderModule q p ζ)) →ₗ[UqSl2 q]
      LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ)) :=
  (clebschGordanProjection hq s).comp
    (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanProjection hq r))

/-- Definitional composite formula for `clebschGordanRightProjection`. -/
theorem clebschGordanRightProjection_def (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    clebschGordanRightProjection (ε := ε) (δ := δ) (ζ := ζ) hq r s =
      (clebschGordanProjection hq s).comp
        (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanProjection hq r)) :=
  (rfl)

/-- `clebschGordanLeftInclusion` agrees with `clebschGordanLeftEquiv` on a single channel. -/
theorem clebschGordanLeftInclusion_eq_single (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (x : LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ)) :
    clebschGordanLeftInclusion hq i j x =
      clebschGordanLeftEquiv hq (Pi.single i (Pi.single j x)) :=
  (clebschGordanLeftEquiv_single hq i j x).symm

/-- `clebschGordanRightInclusion` agrees with `clebschGordanRightEquiv` on a single channel. -/
theorem clebschGordanRightInclusion_eq_single (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (x : LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ))) :
    clebschGordanRightInclusion hq r s x =
      clebschGordanRightEquiv hq (Pi.single r (Pi.single s x)) :=
  (clebschGordanRightEquiv_single hq r s x).symm

/-- `clebschGordanLeftProjection` extracts the `(i, j)` coordinate of
`(clebschGordanLeftEquiv).symm`. -/
theorem clebschGordanLeftProjection_eq_symm (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (x : Tensor ℂ (UqSl2 q)
      (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)) (LadderModule q p ζ)) :
    clebschGordanLeftProjection hq i j x = (clebschGordanLeftEquiv hq).symm x i j :=
  (clebschGordanLeftEquiv_symm_apply hq x i j).symm

/-- `clebschGordanRightProjection` extracts the `(r, s)` coordinate of
`(clebschGordanRightEquiv).symm`. -/
theorem clebschGordanRightProjection_eq_symm (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (x : Tensor ℂ (UqSl2 q) (LadderModule q m ε)
      (Tensor ℂ (UqSl2 q) (LadderModule q n δ) (LadderModule q p ζ))) :
    clebschGordanRightProjection hq r s x = (clebschGordanRightEquiv hq).symm x r s :=
  (clebschGordanRightEquiv_symm_apply hq x r s).symm

/-- `clebschGordanLeftInclusion` sends `v₀` to the left-coupled `α₀ = 1` highest-weight vector. -/
@[simp]
theorem clebschGordanLeftInclusion_vec_zero (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    clebschGordanLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) hq i j (vec q _ _ 0) =
      tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i) LinearMap.id
        (clebschGordanVector q (m + n - 2 * (i : ℕ)) (ε * δ) p ζ j) := by
  simp [clebschGordanLeftInclusion]

/-- `clebschGordanRightInclusion` sends `v₀` to the right-coupled `α₀ = 1` highest-weight vector. -/
@[simp]
theorem clebschGordanRightInclusion_vec_zero (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    clebschGordanRightInclusion (ε := ε) (δ := δ) (ζ := ζ) hq r s (vec q _ _ 0) =
      tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq r)
        (clebschGordanVector q m ε (n + p - 2 * (r : ℕ)) (δ * ζ) s) := by
  simp [clebschGordanRightInclusion]

/-- `clebschGordanLeftInclusion` sends `v_l` to the normalized `F`-ladder lowering string of its
coupled highest-weight vector. -/
theorem clebschGordanLeftInclusion_vec (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (l : ℕ) :
    clebschGordanLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) hq i j (vec q _ _ l) =
      (∏ c ∈ Finset.range l, quantumInteger q (c + 1))⁻¹ •
        f q ^ l • clebschGordanLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) hq i j (vec q _ _ 0) := by
  conv_lhs =>
    rw [clebschGordanLeftInclusion, LinearMap.comp_apply, clebschGordanInclusion_vec,
      LinearMap.map_smul_of_tower, map_smul]
  rw [clebschGordanLeftInclusion_vec_zero]

/-- `clebschGordanRightInclusion` sends `v_l` to the normalized `F`-ladder lowering string of its
coupled highest-weight vector. -/
theorem clebschGordanRightInclusion_vec (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (l : ℕ) :
    clebschGordanRightInclusion (ε := ε) (δ := δ) (ζ := ζ) hq r s (vec q _ _ l) =
      (∏ c ∈ Finset.range l, quantumInteger q (c + 1))⁻¹ •
        f q ^ l • clebschGordanRightInclusion (ε := ε) (δ := δ) (ζ := ζ) hq r s (vec q _ _ 0) := by
  conv_lhs =>
    rw [clebschGordanRightInclusion, LinearMap.comp_apply, clebschGordanInclusion_vec,
      LinearMap.map_smul_of_tower, map_smul]
  rw [clebschGordanRightInclusion_vec_zero]

/-- Left channel projection is a left inverse to left channel inclusion. -/
@[simp]
theorem clebschGordanLeftProjection_inclusion_self (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (x : LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ)) :
    clebschGordanLeftProjection hq i j (clebschGordanLeftInclusion hq i j x) = x := by
  rw [clebschGordanLeftInclusion_eq_single, clebschGordanLeftProjection_eq_symm,
    LinearEquiv.symm_apply_apply]
  simp

/-- Right channel projection is a left inverse to right channel inclusion. -/
@[simp]
theorem clebschGordanRightProjection_inclusion_self (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (x : LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ))) :
    clebschGordanRightProjection hq r s (clebschGordanRightInclusion hq r s x) = x := by
  rw [clebschGordanRightInclusion_eq_single, clebschGordanRightProjection_eq_symm,
    LinearEquiv.symm_apply_apply]
  simp

/-- The channel-to-channel recoupling intertwiner from left channel `(i, j)` to right channel
`(r, s)` through `BialgebraModule.assoc`. -/
def recouplingHom (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ) →ₗ[UqSl2 q]
      LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ)) :=
  (clebschGordanRightProjection hq r s).comp
    ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
        (LadderModule q p ζ)).toLinearMap.comp
      (clebschGordanLeftInclusion hq i j))

/-- Definitional composite formula for `recouplingHom`. -/
theorem recouplingHom_def (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    recouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq i j r s =
      (clebschGordanRightProjection hq r s).comp
        ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
            (LadderModule q p ζ)).toLinearMap.comp
          (clebschGordanLeftInclusion hq i j)) :=
  (rfl)

/-- The inverse channel-to-channel recoupling intertwiner from right channel `(r, s)` to left
channel `(i, j)` through `(BialgebraModule.assoc).symm`. -/
def invRecouplingHom (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ)) →ₗ[UqSl2 q]
      LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ) :=
  (clebschGordanLeftProjection hq i j).comp
    ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
        (LadderModule q p ζ)).symm.toLinearMap.comp
      (clebschGordanRightInclusion hq r s))

/-- Definitional composite formula for `invRecouplingHom`. -/
theorem invRecouplingHom_def (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    invRecouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq r s i j =
      (clebschGordanLeftProjection hq i j).comp
        ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
            (LadderModule q p ζ)).symm.toLinearMap.comp
          (clebschGordanRightInclusion hq r s)) :=
  (rfl)

/-- `recouplingHom` agrees with the `(r, s)` coordinate of `clebschGordanRecouplingEquiv` on a
single left channel. -/
theorem recouplingHom_apply (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (x : LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ)) :
    recouplingHom hq i j r s x =
      clebschGordanRecouplingEquiv hq (Pi.single i (Pi.single j x)) r s :=
  (clebschGordanRecouplingEquiv_single_apply hq i j r s x).symm

/-- `invRecouplingHom` agrees with the `(i, j)` coordinate of `(clebschGordanRecouplingEquiv).symm`
on a single right channel. -/
theorem invRecouplingHom_apply (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (x : LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ))) :
    invRecouplingHom hq r s i j x =
      (clebschGordanRecouplingEquiv hq).symm (Pi.single r (Pi.single s x)) i j :=
  (clebschGordanRecouplingEquiv_symm_single_apply hq i j r s x).symm

end TripleMaps

/-! ### Recoupling scalars and triple-product basis expansions -/

section RecouplingScalars

variable {q : ℂ} {m n p : ℕ}

/-- The scalar recoupling coefficient from left channel `(i, j)` to right channel `(r, s)` on
`L_m^ε ⊗ L_n^δ ⊗ L_p^ζ`. -/
def recouplingCoeff (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) : ℂ :=
  letI : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  schurScalar (recouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq i j r s)

/-- Definitional Schur-scalar formula for `recouplingCoeff`. -/
theorem recouplingCoeff_def [Fact (q ≠ 0)] (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    recouplingCoeff hq ε δ ζ i j r s =
      schurScalar (recouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq i j r s) :=
  (rfl)

/-- The inverse scalar recoupling coefficient from right channel `(r, s)` to left channel `(i, j)`
on `L_m^ε ⊗ L_n^δ ⊗ L_p^ζ`. -/
def invRecouplingCoeff (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) : ℂ :=
  letI : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  schurScalar (invRecouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq r s i j)

/-- Definitional Schur-scalar formula for `invRecouplingCoeff`. -/
theorem invRecouplingCoeff_def [Fact (q ≠ 0)] (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    invRecouplingCoeff hq ε δ ζ r s i j =
      schurScalar (invRecouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq r s i j) :=
  (rfl)

/-- Congruence of `recouplingCoeff` along equality of underlying natural-number indices. -/
theorem recouplingCoeff_congr (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {i₁ i₂ : Fin (min m n + 1)}
    {j₁ : Fin (min (m + n - 2 * (i₁ : ℕ)) p + 1)}
    {j₂ : Fin (min (m + n - 2 * (i₂ : ℕ)) p + 1)}
    {r₁ r₂ : Fin (min n p + 1)}
    {s₁ : Fin (min m (n + p - 2 * (r₁ : ℕ)) + 1)}
    {s₂ : Fin (min m (n + p - 2 * (r₂ : ℕ)) + 1)}
    (hi : (i₁ : ℕ) = (i₂ : ℕ)) (hj : (j₁ : ℕ) = (j₂ : ℕ))
    (hr : (r₁ : ℕ) = (r₂ : ℕ)) (hs : (s₁ : ℕ) = (s₂ : ℕ)) :
    recouplingCoeff hq ε δ ζ i₁ j₁ r₁ s₁ = recouplingCoeff hq ε δ ζ i₂ j₂ r₂ s₂ := by
  obtain rfl : i₁ = i₂ := Fin.ext hi
  obtain rfl : j₁ = j₂ := Fin.ext hj
  obtain rfl : r₁ = r₂ := Fin.ext hr
  obtain rfl : s₁ = s₂ := Fin.ext hs
  rfl

/-- Congruence of `invRecouplingCoeff` along equality of underlying natural-number indices. -/
theorem invRecouplingCoeff_congr (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {r₁ r₂ : Fin (min n p + 1)}
    {s₁ : Fin (min m (n + p - 2 * (r₁ : ℕ)) + 1)}
    {s₂ : Fin (min m (n + p - 2 * (r₂ : ℕ)) + 1)}
    {i₁ i₂ : Fin (min m n + 1)}
    {j₁ : Fin (min (m + n - 2 * (i₁ : ℕ)) p + 1)}
    {j₂ : Fin (min (m + n - 2 * (i₂ : ℕ)) p + 1)}
    (hr : (r₁ : ℕ) = (r₂ : ℕ)) (hs : (s₁ : ℕ) = (s₂ : ℕ))
    (hi : (i₁ : ℕ) = (i₂ : ℕ)) (hj : (j₁ : ℕ) = (j₂ : ℕ)) :
    invRecouplingCoeff hq ε δ ζ r₁ s₁ i₁ j₁ = invRecouplingCoeff hq ε δ ζ r₂ s₂ i₂ j₂ := by
  obtain rfl : r₁ = r₂ := Fin.ext hr
  obtain rfl : s₁ = s₂ := Fin.ext hs
  obtain rfl : i₁ = i₂ := Fin.ext hi
  obtain rfl : j₁ = j₂ := Fin.ext hj
  rfl

/-- `recouplingCoeff` vanishes whenever the left and right channels have distinct total highest
weights. -/
theorem recouplingCoeff_eq_zero_of_ne (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {i : Fin (min m n + 1)} {j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)}
    {r : Fin (min n p + 1)} {s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)}
    (hne : m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) ≠
      m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) :
    recouplingCoeff hq ε δ ζ i j r s = 0 := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  exact schurScalar_eq_zero_of_ne hq (.inl hne) _

/-- `invRecouplingCoeff` vanishes whenever the right and left channels have distinct total highest
weights. -/
theorem invRecouplingCoeff_eq_zero_of_ne (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {r : Fin (min n p + 1)} {s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)}
    {i : Fin (min m n + 1)} {j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)}
    (hne : m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) ≠
      m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) :
    invRecouplingCoeff hq ε δ ζ r s i j = 0 := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  exact schurScalar_eq_zero_of_ne hq (.inl hne) _

end RecouplingScalars

section BasisExpansions

variable {q : ℂ} [Fact (q ≠ 0)] {m n p : ℕ} {ε δ ζ : ℤˣ}

/-- `recouplingHom` acts on every ladder vector `v_l` (`l = 0` as well as the normalized `F`-ladder
basis `0 ≤ l ≤ k`) by multiplication by `recouplingCoeff`. -/
@[simp]
theorem recouplingHom_vec (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (l : ℤ) :
    recouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq i j r s (vec q _ _ l) =
      recouplingCoeff hq ε δ ζ i j r s • vec q _ _ l :=
  apply_vec_eq_schurScalar_smul hq _ l

/-- `invRecouplingHom` acts on every ladder vector `v_l` by multiplication by
`invRecouplingCoeff`. -/
@[simp]
theorem invRecouplingHom_vec (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (l : ℤ) :
    invRecouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq r s i j (vec q _ _ l) =
      invRecouplingCoeff hq ε δ ζ r s i j • vec q _ _ l :=
  apply_vec_eq_schurScalar_smul hq _ l

/-- Action of `clebschGordanRecouplingEquiv` on every ladder vector `v_l` of a left channel. -/
@[simp]
theorem clebschGordanRecouplingEquiv_single_vec (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (l : ℤ) :
    clebschGordanRecouplingEquiv (ε := ε) (δ := δ) (ζ := ζ) hq
        (Pi.single i (Pi.single j (vec q _ _ l))) r s =
      recouplingCoeff hq ε δ ζ i j r s • vec q _ _ l := by
  rw [← recouplingHom_apply, recouplingHom_vec]

/-- Action of `(clebschGordanRecouplingEquiv).symm` on every ladder vector `v_l` of a right
channel. -/
@[simp]
theorem clebschGordanRecouplingEquiv_symm_single_vec (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (l : ℤ) :
    (clebschGordanRecouplingEquiv (ε := ε) (δ := δ) (ζ := ζ) hq).symm
        (Pi.single r (Pi.single s (vec q _ _ l))) i j =
      invRecouplingCoeff hq ε δ ζ r s i j • vec q _ _ l := by
  rw [← invRecouplingHom_apply, invRecouplingHom_vec]

/-- **Triple-product recoupling expansion.** Under the actual coproduct associator
`BialgebraModule.assoc`, every ladder vector `v_l` of left channel `(i, j)` expands in the
right-channel ladder vectors `v_l` with coefficients `recouplingCoeff`. For `l = 0` this is the
change of decomposition on the `α₀ = 1` highest-weight vectors; for `0 ≤ l ≤ k` it is the same
matrix on the normalized `F`-ladder basis. -/
theorem assoc_clebschGordanLeftInclusion_vec (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (l : ℤ) :
    assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ) (LadderModule q p ζ)
        (clebschGordanLeftInclusion hq i j (vec q _ _ l)) =
      ∑ r : Fin (min n p + 1), ∑ s : Fin (min m (n + p - 2 * (r : ℕ)) + 1),
        recouplingCoeff hq ε δ ζ i j r s •
          clebschGordanRightInclusion hq r s (vec q _ _ l) := by
  rw [clebschGordanLeftInclusion_eq_single, ← clebschGordanRightEquiv_recoupling hq]
  set z := clebschGordanRecouplingEquiv (ε := ε) (δ := δ) (ζ := ζ) hq
    (Pi.single i (Pi.single j (vec q _ _ l)))
  have hz : z = ∑ r, ∑ s, Pi.single r (Pi.single s (z r s)) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    refine Finset.sum_congr rfl fun r _ => ?_
    conv_lhs => rw [← Finset.univ_sum_single (z r), ← AddMonoidHom.single_apply, map_sum]
    simp only [AddMonoidHom.single_apply]
  conv_lhs => rw [hz]
  simp only [z, map_sum, ← clebschGordanRightInclusion_eq_single,
    clebschGordanRecouplingEquiv_single_vec, LinearMap.map_smul_of_tower]

/-- **Inverse triple-product recoupling expansion.** Under `(BialgebraModule.assoc).symm`, every
ladder vector `v_l` of right channel `(r, s)` expands in the left-channel ladder vectors `v_l` with
coefficients `invRecouplingCoeff`, covering both `l = 0` (`α₀ = 1` highest-weight vectors) and
`0 ≤ l ≤ k` (the normalized `F`-ladder basis). -/
theorem assoc_symm_clebschGordanRightInclusion_vec (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (l : ℤ) :
    (assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ) (LadderModule q p ζ)).symm
        (clebschGordanRightInclusion hq r s (vec q _ _ l)) =
      ∑ i : Fin (min m n + 1), ∑ j : Fin (min (m + n - 2 * (i : ℕ)) p + 1),
        invRecouplingCoeff hq ε δ ζ r s i j •
          clebschGordanLeftInclusion hq i j (vec q _ _ l) := by
  rw [clebschGordanRightInclusion_eq_single, ← clebschGordanLeftEquiv_recoupling_symm hq]
  set z := (clebschGordanRecouplingEquiv (ε := ε) (δ := δ) (ζ := ζ) hq).symm
    (Pi.single r (Pi.single s (vec q _ _ l)))
  have hz : z = ∑ i, ∑ j, Pi.single i (Pi.single j (z i j)) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [← Finset.univ_sum_single (z i), ← AddMonoidHom.single_apply, map_sum]
    simp only [AddMonoidHom.single_apply]
  conv_lhs => rw [hz]
  simp only [z, map_sum, ← clebschGordanLeftInclusion_eq_single,
    clebschGordanRecouplingEquiv_symm_single_vec, LinearMap.map_smul_of_tower]

/-- Operator-level triple-product recoupling expansion of `BialgebraModule.assoc` composed with
`clebschGordanLeftInclusion`. -/
theorem assoc_comp_clebschGordanLeftInclusion (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    (assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
        (LadderModule q p ζ)).toLinearMap.comp (clebschGordanLeftInclusion hq i j) =
      ∑ r : Fin (min n p + 1), ∑ s : Fin (min m (n + p - 2 * (r : ℕ)) + 1),
        (clebschGordanRightInclusion hq r s).comp (recouplingHom hq i j r s) := by
  ext x
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, clebschGordanLeftInclusion_eq_single,
    ← clebschGordanRightEquiv_recoupling hq]
  set z := clebschGordanRecouplingEquiv (ε := ε) (δ := δ) (ζ := ζ) hq (Pi.single i (Pi.single j x))
  have hz : z = ∑ r, ∑ s, Pi.single r (Pi.single s (z r s)) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    refine Finset.sum_congr rfl fun r _ => ?_
    conv_lhs => rw [← Finset.univ_sum_single (z r), ← AddMonoidHom.single_apply, map_sum]
    simp only [AddMonoidHom.single_apply]
  conv_lhs => rw [hz]
  simp only [z, map_sum, LinearMap.sum_apply, LinearMap.comp_apply,
    ← clebschGordanRightInclusion_eq_single, recouplingHom_apply]

/-- Operator-level inverse triple-product recoupling expansion of `(BialgebraModule.assoc).symm`
composed with `clebschGordanRightInclusion`. -/
theorem assoc_symm_comp_clebschGordanRightInclusion (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    (assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
        (LadderModule q p ζ)).symm.toLinearMap.comp (clebschGordanRightInclusion hq r s) =
      ∑ i : Fin (min m n + 1), ∑ j : Fin (min (m + n - 2 * (i : ℕ)) p + 1),
        (clebschGordanLeftInclusion hq i j).comp (invRecouplingHom hq r s i j) := by
  ext x
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, clebschGordanRightInclusion_eq_single,
    ← clebschGordanLeftEquiv_recoupling_symm hq]
  set z := (clebschGordanRecouplingEquiv (ε := ε) (δ := δ) (ζ := ζ) hq).symm
    (Pi.single r (Pi.single s x))
  have hz : z = ∑ i, ∑ j, Pi.single i (Pi.single j (z i j)) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [← Finset.univ_sum_single (z i), ← AddMonoidHom.single_apply, map_sum]
    simp only [AddMonoidHom.single_apply]
  conv_lhs => rw [hz]
  simp only [z, map_sum, LinearMap.sum_apply, LinearMap.comp_apply,
    ← clebschGordanLeftInclusion_eq_single, invRecouplingHom_apply]

end BasisExpansions

/-! ### Six-weight quantum 6j symbols and change-of-decomposition matrices -/

section SixJ

variable {q : ℂ}

/-- The six-weight quantum 6j change-of-decomposition scalar for `L_m^ε ⊗ L_n^δ ⊗ L_p^ζ` at total
highest weight `k`, from left intermediate channel `u` (in `L_m^ε ⊗ L_n^δ`) to right intermediate
channel `v` (in `L_n^δ ⊗ L_p^ζ`). Extended by `0` when any of the four binary couplings is
inadmissible. -/
def sixJ (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k u v : ℕ) : ℂ :=
  if h : (IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k) ∧
      (IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k) then
    recouplingCoeff hq ε δ ζ h.1.1.index (h.1.2.leftIndex h.1.1)
      h.2.1.index (h.2.2.rightIndex h.2.1)
  else 0

/-- The inverse six-weight quantum 6j change-of-decomposition scalar for `L_m^ε ⊗ L_n^δ ⊗ L_p^ζ`
at total highest weight `k`, from right intermediate channel `v` to left intermediate channel `u`.
Extended by `0` outside admissible channels. -/
def invSixJ (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k v u : ℕ) : ℂ :=
  if h : (IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k) ∧
      (IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k) then
    invRecouplingCoeff hq ε δ ζ h.1.1.index (h.1.2.rightIndex h.1.1)
      h.2.1.index (h.2.2.leftIndex h.2.1)
  else 0

/-- `sixJ` on admissible left and right channels equals the corresponding `recouplingCoeff`. -/
theorem sixJ_eq_recouplingCoeff (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p k u v : ℕ}
    (hu : IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k)
    (hv : IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k) :
    sixJ hq ε δ ζ m n p k u v =
      recouplingCoeff hq ε δ ζ hu.1.index (hu.2.leftIndex hu.1)
        hv.1.index (hv.2.rightIndex hv.1) := by
  simp [sixJ, hu, hv]

/-- `invSixJ` on admissible right and left channels equals the corresponding
`invRecouplingCoeff`. -/
theorem invSixJ_eq_invRecouplingCoeff (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p k v u : ℕ}
    (hv : IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k)
    (hu : IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k) :
    invSixJ hq ε δ ζ m n p k v u =
      invRecouplingCoeff hq ε δ ζ hv.1.index (hv.2.rightIndex hv.1)
        hu.1.index (hu.2.leftIndex hu.1) := by
  simp [invSixJ, hv, hu]

/-- `sixJ` vanishes when any of its four binary channel conditions fails. -/
theorem sixJ_eq_zero_of_not (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p k u v : ℕ}
    (h : ¬ ((IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k) ∧
      (IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k))) :
    sixJ hq ε δ ζ m n p k u v = 0 := by
  simp [sixJ, h]

/-- `invSixJ` vanishes when any of its four binary channel conditions fails. -/
theorem invSixJ_eq_zero_of_not (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p k v u : ℕ}
    (h : ¬ ((IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k) ∧
      (IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k))) :
    invSixJ hq ε δ ζ m n p k v u = 0 := by
  simp [invSixJ, h]

/-- `recouplingCoeff` equals `sixJ` when the left and right total highest weights agree, and `0`
otherwise. -/
theorem recouplingCoeff_eq_ite (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p : ℕ}
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    recouplingCoeff hq ε δ ζ i j r s =
      if m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) = m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) then
        sixJ hq ε δ ζ m n p (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ))
          (m + n - 2 * (i : ℕ)) (n + p - 2 * (r : ℕ))
      else 0 := by
  split_ifs with h
  · have hu₁ : IsClebschGordanChannel m n (m + n - 2 * (i : ℕ)) :=
      isClebschGordanChannel_sub_two_mul i
    have hu₂ : IsClebschGordanChannel (m + n - 2 * (i : ℕ)) p
        (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) :=
      isClebschGordanChannel_sub_two_mul j
    have hv₁ : IsClebschGordanChannel n p (n + p - 2 * (r : ℕ)) :=
      isClebschGordanChannel_sub_two_mul r
    have hv₂ : IsClebschGordanChannel m (n + p - 2 * (r : ℕ))
        (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) := ⟨s, h.symm⟩
    rw [sixJ_eq_recouplingCoeff hq ε δ ζ ⟨hu₁, hu₂⟩ ⟨hv₁, hv₂⟩]
    exact recouplingCoeff_congr hq ε δ ζ
      (congrArg Fin.val (hu₁.index_eq_of_eq rfl)).symm
      (congrArg Fin.val (hu₂.index_eq_of_eq rfl)).symm
      (congrArg Fin.val (hv₁.index_eq_of_eq rfl)).symm
      (congrArg Fin.val (hv₂.index_eq_of_eq h.symm)).symm
  · exact recouplingCoeff_eq_zero_of_ne hq ε δ ζ h

/-- `invRecouplingCoeff` equals `invSixJ` when the right and left total highest weights agree, and
`0` otherwise. -/
theorem invRecouplingCoeff_eq_ite (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p : ℕ}
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    invRecouplingCoeff hq ε δ ζ r s i j =
      if m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) = m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) then
        invSixJ hq ε δ ζ m n p (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ))
          (n + p - 2 * (r : ℕ)) (m + n - 2 * (i : ℕ))
      else 0 := by
  split_ifs with h
  · have hv₁ : IsClebschGordanChannel n p (n + p - 2 * (r : ℕ)) :=
      isClebschGordanChannel_sub_two_mul r
    have hv₂ : IsClebschGordanChannel m (n + p - 2 * (r : ℕ))
        (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) :=
      isClebschGordanChannel_sub_two_mul s
    have hu₁ : IsClebschGordanChannel m n (m + n - 2 * (i : ℕ)) :=
      isClebschGordanChannel_sub_two_mul i
    have hu₂ : IsClebschGordanChannel (m + n - 2 * (i : ℕ)) p
        (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) := ⟨j, h.symm⟩
    rw [invSixJ_eq_invRecouplingCoeff hq ε δ ζ ⟨hv₁, hv₂⟩ ⟨hu₁, hu₂⟩]
    exact invRecouplingCoeff_congr hq ε δ ζ
      (congrArg Fin.val (hv₁.index_eq_of_eq rfl)).symm
      (congrArg Fin.val (hv₂.index_eq_of_eq rfl)).symm
      (congrArg Fin.val (hu₁.index_eq_of_eq rfl)).symm
      (congrArg Fin.val (hu₂.index_eq_of_eq h.symm)).symm
  · exact invRecouplingCoeff_eq_zero_of_ne hq ε δ ζ h

/-- The quantum 6j change-of-decomposition matrix at fixed total highest weight `k`, mapping
`LeftSixJChannel m n p k` columns to `RightSixJChannel m n p k` rows. -/
def sixJMatrix (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k : ℕ) :
    Matrix (RightSixJChannel m n p k) (LeftSixJChannel m n p k) ℂ :=
  fun v u => sixJ hq ε δ ζ m n p k u.1 v.1

/-- The inverse quantum 6j change-of-decomposition matrix at fixed total highest weight `k`,
mapping `RightSixJChannel m n p k` columns to `LeftSixJChannel m n p k` rows. -/
def invSixJMatrix (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k : ℕ) :
    Matrix (LeftSixJChannel m n p k) (RightSixJChannel m n p k) ℂ :=
  fun u v => invSixJ hq ε δ ζ m n p k v.1 u.1

/-- Entry formula for `sixJMatrix`. -/
@[simp]
theorem sixJMatrix_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k : ℕ)
    (v : RightSixJChannel m n p k) (u : LeftSixJChannel m n p k) :
    sixJMatrix hq ε δ ζ m n p k v u = sixJ hq ε δ ζ m n p k u.1 v.1 :=
  (rfl)

/-- Entry formula for `invSixJMatrix`. -/
@[simp]
theorem invSixJMatrix_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k : ℕ)
    (u : LeftSixJChannel m n p k) (v : RightSixJChannel m n p k) :
    invSixJMatrix hq ε δ ζ m n p k u v = invSixJ hq ε δ ζ m n p k v.1 u.1 :=
  (rfl)

/-! ### Orthogonality and matrix invertibility -/

/-- Channel-summed left orthogonality of `invRecouplingCoeff` and `recouplingCoeff`. -/
theorem sum_invRecouplingCoeff_mul_recouplingCoeff (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p : ℕ}
    (i₁ i₂ : Fin (min m n + 1))
    (j₁ : Fin (min (m + n - 2 * (i₁ : ℕ)) p + 1))
    (j₂ : Fin (min (m + n - 2 * (i₂ : ℕ)) p + 1)) :
    (∑ r : Fin (min n p + 1), ∑ s : Fin (min m (n + p - 2 * (r : ℕ)) + 1),
      invRecouplingCoeff hq ε δ ζ r s i₁ j₁ * recouplingCoeff hq ε δ ζ i₂ j₂ r s) =
      if (i₁ : ℕ) = (i₂ : ℕ) ∧ (j₁ : ℕ) = (j₂ : ℕ) then 1 else 0 := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  set e := clebschGordanRecouplingEquiv (m := m) (n := n) (p := p) (ε := ε) (δ := δ) (ζ := ζ) hq
  set x : ClebschGordanLeft q m n p ε δ ζ := Pi.single i₂ (Pi.single j₂ (vec q _ _ 0))
  have h := congrArg (fun z => (basis q _ _).repr (z i₁ j₁) 0) (e.symm_apply_apply x)
  have hex_sum : e x = ∑ r, ∑ s, Pi.single r (Pi.single s (e x r s)) := by
    conv_lhs => rw [← Finset.univ_sum_single (e x)]
    refine Finset.sum_congr rfl fun r _ => ?_
    conv_lhs => rw [← Finset.univ_sum_single (e x r), ← AddMonoidHom.single_apply, map_sum]
    simp only [AddMonoidHom.single_apply]
  conv_lhs at h =>
    rw [hex_sum]
    simp only [map_sum, Finset.sum_apply, Finsupp.finsetSum_apply]
  have hterm (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
      (basis q _ _).repr
          (e.symm (Pi.single r (Pi.single s (e x r s))) i₁ j₁) 0 =
        invRecouplingCoeff hq ε δ ζ r s i₁ j₁ * recouplingCoeff hq ε δ ζ i₂ j₂ r s := by
    have hex : e x r s = recouplingCoeff hq ε δ ζ i₂ j₂ r s • vec q _ _ 0 :=
      clebschGordanRecouplingEquiv_single_vec hq i₂ j₂ r s 0
    rw [hex,
      Pi.single_smul (f := fun s' : Fin (min m (n + p - 2 * (r : ℕ)) + 1) =>
        LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s' : ℕ)) (ε * (δ * ζ))),
      Pi.single_smul (f := fun r' : Fin (min n p + 1) =>
        ∀ s' : Fin (min m (n + p - 2 * (r' : ℕ)) + 1),
          LadderModule q (m + (n + p - 2 * (r' : ℕ)) - 2 * (s' : ℕ)) (ε * (δ * ζ))),
      ← e.symm.coe_toLinearMap, LinearMap.map_smul_of_tower,
      e.symm.coe_toLinearMap, Pi.smul_apply, Pi.smul_apply,
      clebschGordanRecouplingEquiv_symm_single_vec, smul_smul, map_smul, Finsupp.smul_apply,
      basis_repr_vec]
    simp [mul_comm]
  simp only [hterm] at h
  rw [h]
  by_cases hi : i₁ = i₂
  · subst hi
    simp only [x, Pi.single_eq_same, true_and]
    by_cases hj : j₁ = j₂
    · subst hj
      simp
    · have hjv : (j₁ : ℕ) ≠ (j₂ : ℕ) := Fin.val_ne_of_ne hj
      rw [Pi.single_eq_of_ne hj]
      simp [hjv]
  · have hiv : (i₁ : ℕ) ≠ (i₂ : ℕ) := Fin.val_ne_of_ne hi
    simp [x, Pi.single_eq_of_ne hi, hiv]

/-- Channel-summed right orthogonality of `recouplingCoeff` and `invRecouplingCoeff`. -/
theorem sum_recouplingCoeff_mul_invRecouplingCoeff (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p : ℕ}
    (r₁ r₂ : Fin (min n p + 1))
    (s₁ : Fin (min m (n + p - 2 * (r₁ : ℕ)) + 1))
    (s₂ : Fin (min m (n + p - 2 * (r₂ : ℕ)) + 1)) :
    (∑ i : Fin (min m n + 1), ∑ j : Fin (min (m + n - 2 * (i : ℕ)) p + 1),
      recouplingCoeff hq ε δ ζ i j r₁ s₁ * invRecouplingCoeff hq ε δ ζ r₂ s₂ i j) =
      if (r₁ : ℕ) = (r₂ : ℕ) ∧ (s₁ : ℕ) = (s₂ : ℕ) then 1 else 0 := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  set e := clebschGordanRecouplingEquiv (m := m) (n := n) (p := p) (ε := ε) (δ := δ) (ζ := ζ) hq
  set y : ClebschGordanRight q m n p ε δ ζ := Pi.single r₂ (Pi.single s₂ (vec q _ _ 0))
  have h := congrArg (fun z => (basis q _ _).repr (z r₁ s₁) 0) (e.apply_symm_apply y)
  have hey_sum : e.symm y = ∑ i, ∑ j, Pi.single i (Pi.single j (e.symm y i j)) := by
    conv_lhs => rw [← Finset.univ_sum_single (e.symm y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [← Finset.univ_sum_single (e.symm y i), ← AddMonoidHom.single_apply, map_sum]
    simp only [AddMonoidHom.single_apply]
  conv_lhs at h =>
    rw [hey_sum]
    simp only [map_sum, Finset.sum_apply, Finsupp.finsetSum_apply]
  have hterm (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
      (basis q _ _).repr
          (e (Pi.single i (Pi.single j (e.symm y i j))) r₁ s₁) 0 =
        recouplingCoeff hq ε δ ζ i j r₁ s₁ * invRecouplingCoeff hq ε δ ζ r₂ s₂ i j := by
    have hey : e.symm y i j = invRecouplingCoeff hq ε δ ζ r₂ s₂ i j • vec q _ _ 0 :=
      clebschGordanRecouplingEquiv_symm_single_vec hq r₂ s₂ i j 0
    rw [hey,
      Pi.single_smul (f := fun j' : Fin (min (m + n - 2 * (i : ℕ)) p + 1) =>
        LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j' : ℕ)) ((ε * δ) * ζ)),
      Pi.single_smul (f := fun i' : Fin (min m n + 1) =>
        ∀ j' : Fin (min (m + n - 2 * (i' : ℕ)) p + 1),
          LadderModule q (m + n - 2 * (i' : ℕ) + p - 2 * (j' : ℕ)) ((ε * δ) * ζ)),
      ← e.coe_toLinearMap, LinearMap.map_smul_of_tower,
      e.coe_toLinearMap, Pi.smul_apply, Pi.smul_apply,
      clebschGordanRecouplingEquiv_single_vec, smul_smul, map_smul, Finsupp.smul_apply,
      basis_repr_vec]
    simp [mul_comm]
  simp only [hterm] at h
  rw [h]
  by_cases hr : r₁ = r₂
  · subst hr
    simp only [y, Pi.single_eq_same, true_and]
    by_cases hs : s₁ = s₂
    · subst hs
      simp
    · have hsv : (s₁ : ℕ) ≠ (s₂ : ℕ) := Fin.val_ne_of_ne hs
      rw [Pi.single_eq_of_ne hs]
      simp [hsv]
  · have hrv : (r₁ : ℕ) ≠ (r₂ : ℕ) := Fin.val_ne_of_ne hr
    simp [y, Pi.single_eq_of_ne hr, hrv]

/-- Orthogonality of `invSixJ` and `sixJ` summed over all right intermediate weights
`v ∈ Finset.range (n + p + 1)`. -/
theorem sum_invSixJ_mul_sixJ (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p k u₁ u₂ : ℕ}
    (hu₁ : IsClebschGordanChannel m n u₁ ∧ IsClebschGordanChannel u₁ p k)
    (hu₂ : IsClebschGordanChannel m n u₂ ∧ IsClebschGordanChannel u₂ p k) :
    ∑ v ∈ Finset.range (n + p + 1),
        invSixJ hq ε δ ζ m n p k v u₁ * sixJ hq ε δ ζ m n p k u₂ v =
      if u₁ = u₂ then 1 else 0 := by
  have horth := sum_invRecouplingCoeff_mul_recouplingCoeff hq ε δ ζ
    hu₁.1.index hu₂.1.index (hu₁.2.leftIndex hu₁.1) (hu₂.2.leftIndex hu₂.1)
  have hk₂ : m + n - 2 * (hu₂.1.index : ℕ) + p - 2 * ((hu₂.2.leftIndex hu₂.1) : ℕ) = k := by
    rw [hu₂.2.val_leftIndex, hu₂.1.sub_two_mul_index, hu₂.2.sub_two_mul_index]
  have hinner (r : Fin (min n p + 1)) :
      (∑ s : Fin (min m (n + p - 2 * (r : ℕ)) + 1),
        invRecouplingCoeff hq ε δ ζ r s hu₁.1.index (hu₁.2.leftIndex hu₁.1) *
          recouplingCoeff hq ε δ ζ hu₂.1.index (hu₂.2.leftIndex hu₂.1) r s) =
        invSixJ hq ε δ ζ m n p k (n + p - 2 * (r : ℕ)) u₁ *
          sixJ hq ε δ ζ m n p k u₂ (n + p - 2 * (r : ℕ)) := by
    have hvr : IsClebschGordanChannel n p (n + p - 2 * (r : ℕ)) :=
      isClebschGordanChannel_sub_two_mul r
    by_cases hmv : IsClebschGordanChannel m (n + p - 2 * (r : ℕ)) k
    · rw [Finset.sum_eq_single hmv.index]
      · rw [invSixJ_eq_invRecouplingCoeff hq ε δ ζ ⟨hvr, hmv⟩ hu₁,
          sixJ_eq_recouplingCoeff hq ε δ ζ hu₂ ⟨hvr, hmv⟩]
        have hr : (hvr.index : ℕ) = (r : ℕ) := congrArg Fin.val (hvr.index_eq_of_eq rfl)
        exact congrArg₂ (· * ·)
          (invRecouplingCoeff_congr hq ε δ ζ hr.symm rfl rfl rfl)
          (recouplingCoeff_congr hq ε δ ζ rfl rfl hr.symm rfl)
      · intro s _ hs
        have hne : m + n - 2 * (hu₂.1.index : ℕ) + p - 2 * ((hu₂.2.leftIndex hu₂.1) : ℕ) ≠
            m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) := by
          rw [hk₂]
          exact fun heq => hs (hmv.index_eq_of_eq heq.symm).symm
        rw [recouplingCoeff_eq_zero_of_ne hq ε δ ζ hne, mul_zero]
      · simp
    · rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hmv h.2.2), mul_zero]
      refine Finset.sum_eq_zero fun s _ => ?_
      have hne : m + n - 2 * (hu₂.1.index : ℕ) + p - 2 * ((hu₂.2.leftIndex hu₂.1) : ℕ) ≠
          m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) := by
        rw [hk₂]
        exact fun heq => hmv ⟨s, heq.symm⟩
      rw [recouplingCoeff_eq_zero_of_ne hq ε δ ζ hne, mul_zero]
  simp_rw [hinner] at horth
  have hbij : (∑ r : Fin (min n p + 1),
      invSixJ hq ε δ ζ m n p k (n + p - 2 * (r : ℕ)) u₁ *
        sixJ hq ε δ ζ m n p k u₂ (n + p - 2 * (r : ℕ))) =
      ∑ v ∈ (Finset.range (n + p + 1)).filter (IsClebschGordanChannel n p),
        invSixJ hq ε δ ζ m n p k v u₁ * sixJ hq ε δ ζ m n p k u₂ v := by
    refine Finset.sum_bij (fun (r : Fin (min n p + 1)) _ => n + p - 2 * (r : ℕ)) ?_ ?_ ?_ ?_
    · intro r _
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, isClebschGordanChannel_sub_two_mul r⟩
    · intro r₁ _ r₂ _ heq
      have h₁ := r₁.isLt
      have h₂ := r₂.isLt
      ext
      omega
    · intro v hv
      rw [Finset.mem_filter] at hv
      exact ⟨hv.2.index, Finset.mem_univ _, hv.2.sub_two_mul_index⟩
    · intro _ _
      rfl
  have hfilter : (∑ v ∈ (Finset.range (n + p + 1)).filter (IsClebschGordanChannel n p),
      invSixJ hq ε δ ζ m n p k v u₁ * sixJ hq ε δ ζ m n p k u₂ v) =
      ∑ v ∈ Finset.range (n + p + 1),
        invSixJ hq ε δ ζ m n p k v u₁ * sixJ hq ε δ ζ m n p k u₂ v := by
    refine Finset.sum_filter_of_ne fun v _ hfv => ?_
    by_contra hnp
    exact hfv (by rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hnp h.2.1), mul_zero])
  rw [← hfilter, ← hbij, horth]
  have hiff : ((hu₁.1.index : ℕ) = (hu₂.1.index : ℕ) ∧
      ((hu₁.2.leftIndex hu₁.1) : ℕ) = ((hu₂.2.leftIndex hu₂.1) : ℕ)) ↔ u₁ = u₂ := by
    constructor
    · rintro ⟨hi, _⟩
      rw [← hu₁.1.sub_two_mul_index, ← hu₂.1.sub_two_mul_index, hi]
    · rintro rfl
      exact ⟨rfl, rfl⟩
  simp only [hiff]

/-- Orthogonality of `sixJ` and `invSixJ` summed over all left intermediate weights
`u ∈ Finset.range (m + n + 1)`. -/
theorem sum_sixJ_mul_invSixJ (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p k v₁ v₂ : ℕ}
    (hv₁ : IsClebschGordanChannel n p v₁ ∧ IsClebschGordanChannel m v₁ k)
    (hv₂ : IsClebschGordanChannel n p v₂ ∧ IsClebschGordanChannel m v₂ k) :
    ∑ u ∈ Finset.range (m + n + 1),
        sixJ hq ε δ ζ m n p k u v₁ * invSixJ hq ε δ ζ m n p k v₂ u =
      if v₁ = v₂ then 1 else 0 := by
  have horth := sum_recouplingCoeff_mul_invRecouplingCoeff hq ε δ ζ
    hv₁.1.index hv₂.1.index (hv₁.2.rightIndex hv₁.1) (hv₂.2.rightIndex hv₂.1)
  have hk₂ : m + (n + p - 2 * (hv₂.1.index : ℕ)) - 2 * ((hv₂.2.rightIndex hv₂.1) : ℕ) = k := by
    rw [hv₂.2.val_rightIndex, hv₂.1.sub_two_mul_index, hv₂.2.sub_two_mul_index]
  have hinner (i : Fin (min m n + 1)) :
      (∑ j : Fin (min (m + n - 2 * (i : ℕ)) p + 1),
        recouplingCoeff hq ε δ ζ i j hv₁.1.index (hv₁.2.rightIndex hv₁.1) *
          invRecouplingCoeff hq ε δ ζ hv₂.1.index (hv₂.2.rightIndex hv₂.1) i j) =
        sixJ hq ε δ ζ m n p k (m + n - 2 * (i : ℕ)) v₁ *
          invSixJ hq ε δ ζ m n p k v₂ (m + n - 2 * (i : ℕ)) := by
    have hui : IsClebschGordanChannel m n (m + n - 2 * (i : ℕ)) :=
      isClebschGordanChannel_sub_two_mul i
    by_cases hup : IsClebschGordanChannel (m + n - 2 * (i : ℕ)) p k
    · rw [Finset.sum_eq_single hup.index]
      · rw [sixJ_eq_recouplingCoeff hq ε δ ζ ⟨hui, hup⟩ hv₁,
          invSixJ_eq_invRecouplingCoeff hq ε δ ζ hv₂ ⟨hui, hup⟩]
        have hi : (hui.index : ℕ) = (i : ℕ) := congrArg Fin.val (hui.index_eq_of_eq rfl)
        exact congrArg₂ (· * ·)
          (recouplingCoeff_congr hq ε δ ζ hi.symm rfl rfl rfl)
          (invRecouplingCoeff_congr hq ε δ ζ rfl rfl hi.symm rfl)
      · intro j _ hj
        have hne : m + (n + p - 2 * (hv₂.1.index : ℕ)) - 2 * ((hv₂.2.rightIndex hv₂.1) : ℕ) ≠
            m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) := by
          rw [hk₂]
          exact fun heq => hj (hup.index_eq_of_eq heq.symm).symm
        rw [invRecouplingCoeff_eq_zero_of_ne hq ε δ ζ hne, mul_zero]
      · simp
    · rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hup h.1.2), zero_mul]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hne : m + (n + p - 2 * (hv₂.1.index : ℕ)) - 2 * ((hv₂.2.rightIndex hv₂.1) : ℕ) ≠
          m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) := by
        rw [hk₂]
        exact fun heq => hup ⟨j, heq.symm⟩
      rw [invRecouplingCoeff_eq_zero_of_ne hq ε δ ζ hne, mul_zero]
  simp_rw [hinner] at horth
  have hbij : (∑ i : Fin (min m n + 1),
      sixJ hq ε δ ζ m n p k (m + n - 2 * (i : ℕ)) v₁ *
        invSixJ hq ε δ ζ m n p k v₂ (m + n - 2 * (i : ℕ))) =
      ∑ u ∈ (Finset.range (m + n + 1)).filter (IsClebschGordanChannel m n),
        sixJ hq ε δ ζ m n p k u v₁ * invSixJ hq ε δ ζ m n p k v₂ u := by
    refine Finset.sum_bij (fun (i : Fin (min m n + 1)) _ => m + n - 2 * (i : ℕ)) ?_ ?_ ?_ ?_
    · intro i _
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, isClebschGordanChannel_sub_two_mul i⟩
    · intro i₁ _ i₂ _ heq
      have h₁ := i₁.isLt
      have h₂ := i₂.isLt
      ext
      omega
    · intro u hu
      rw [Finset.mem_filter] at hu
      exact ⟨hu.2.index, Finset.mem_univ _, hu.2.sub_two_mul_index⟩
    · intro _ _
      rfl
  have hfilter : (∑ u ∈ (Finset.range (m + n + 1)).filter (IsClebschGordanChannel m n),
      sixJ hq ε δ ζ m n p k u v₁ * invSixJ hq ε δ ζ m n p k v₂ u) =
      ∑ u ∈ Finset.range (m + n + 1),
        sixJ hq ε δ ζ m n p k u v₁ * invSixJ hq ε δ ζ m n p k v₂ u := by
    refine Finset.sum_filter_of_ne fun u _ hfu => ?_
    by_contra hmn
    exact hfu (by rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hmn h.1.1), zero_mul])
  rw [← hfilter, ← hbij, horth]
  have hiff : ((hv₁.1.index : ℕ) = (hv₂.1.index : ℕ) ∧
      ((hv₁.2.rightIndex hv₁.1) : ℕ) = ((hv₂.2.rightIndex hv₂.1) : ℕ)) ↔ v₁ = v₂ := by
    constructor
    · rintro ⟨hr, _⟩
      rw [← hv₁.1.sub_two_mul_index, ← hv₂.1.sub_two_mul_index, hr]
    · rintro rfl
      exact ⟨rfl, rfl⟩
  simp only [hiff]

/-- `invSixJMatrix` is a left inverse to `sixJMatrix`. -/
@[simp]
theorem invSixJMatrix_mul_sixJMatrix (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (m n p k : ℕ) :
    invSixJMatrix hq ε δ ζ m n p k * sixJMatrix hq ε δ ζ m n p k = 1 := by
  ext u₁ u₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hsub : (∑ v : RightSixJChannel m n p k,
      invSixJ hq ε δ ζ m n p k v.1 u₁.1 * sixJ hq ε δ ζ m n p k u₂.1 v.1) =
      ∑ v ∈ (Finset.range (n + p + 1)).filter
        (fun v => IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k),
        invSixJ hq ε δ ζ m n p k v u₁.1 * sixJ hq ε δ ζ m n p k u₂.1 v := by
    refine Finset.sum_bij (fun (v : RightSixJChannel m n p k) _ => v.1) ?_ ?_ ?_ ?_
    · intro v _
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le v.2.1.le_add, v.2⟩
    · intro _ _ _ _ h
      exact Subtype.ext h
    · intro v hv
      rw [Finset.mem_filter] at hv
      exact ⟨⟨v, hv.2⟩, Finset.mem_univ _, rfl⟩
    · intro _ _
      rfl
  have hfilter : (∑ v ∈ (Finset.range (n + p + 1)).filter
      (fun v => IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k),
      invSixJ hq ε δ ζ m n p k v u₁.1 * sixJ hq ε δ ζ m n p k u₂.1 v) =
      ∑ v ∈ Finset.range (n + p + 1),
        invSixJ hq ε δ ζ m n p k v u₁.1 * sixJ hq ε δ ζ m n p k u₂.1 v := by
    refine Finset.sum_filter_of_ne fun v _ hfv => ?_
    by_contra hv
    exact hfv (by rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hv h.2), mul_zero])
  simp only [invSixJMatrix_apply, sixJMatrix_apply]
  rw [hsub, hfilter, sum_invSixJ_mul_sixJ hq ε δ ζ u₁.2 u₂.2]
  simp [Subtype.ext_iff]

/-- `invSixJMatrix` is a right inverse to `sixJMatrix`. -/
@[simp]
theorem sixJMatrix_mul_invSixJMatrix (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (m n p k : ℕ) :
    sixJMatrix hq ε δ ζ m n p k * invSixJMatrix hq ε δ ζ m n p k = 1 := by
  ext v₁ v₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hsub : (∑ u : LeftSixJChannel m n p k,
      sixJ hq ε δ ζ m n p k u.1 v₁.1 * invSixJ hq ε δ ζ m n p k v₂.1 u.1) =
      ∑ u ∈ (Finset.range (m + n + 1)).filter
        (fun u => IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k),
        sixJ hq ε δ ζ m n p k u v₁.1 * invSixJ hq ε δ ζ m n p k v₂.1 u := by
    refine Finset.sum_bij (fun (u : LeftSixJChannel m n p k) _ => u.1) ?_ ?_ ?_ ?_
    · intro u _
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le u.2.1.le_add, u.2⟩
    · intro _ _ _ _ h
      exact Subtype.ext h
    · intro u hu
      rw [Finset.mem_filter] at hu
      exact ⟨⟨u, hu.2⟩, Finset.mem_univ _, rfl⟩
    · intro _ _
      rfl
  have hfilter : (∑ u ∈ (Finset.range (m + n + 1)).filter
      (fun u => IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k),
      sixJ hq ε δ ζ m n p k u v₁.1 * invSixJ hq ε δ ζ m n p k v₂.1 u) =
      ∑ u ∈ Finset.range (m + n + 1),
        sixJ hq ε δ ζ m n p k u v₁.1 * invSixJ hq ε δ ζ m n p k v₂.1 u := by
    refine Finset.sum_filter_of_ne fun u _ hfu => ?_
    by_contra hu
    exact hfu (by rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hu h.1), zero_mul])
  simp only [sixJMatrix_apply, invSixJMatrix_apply]
  rw [hsub, hfilter, sum_sixJ_mul_invSixJ hq ε δ ζ v₁.2 v₂.2]
  simp [Subtype.ext_iff]

/-! ### Explicit boundary evaluations -/

/-- On the leading stretched channel `k = m + n + p` (`u = m + n`, `v = n + p`), the quantum 6j
coefficient is `1` for all highest weights and signs. -/
@[simp]
theorem sixJ_add_add (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p : ℕ) :
    sixJ hq ε δ ζ m n p (m + n + p) (m + n) (n + p) = 1 := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have hu₁ : IsClebschGordanChannel m n (m + n) := isClebschGordanChannel_add m n
  have hu₂ : IsClebschGordanChannel (m + n) p (m + n + p) := isClebschGordanChannel_add (m + n) p
  have hv₁ : IsClebschGordanChannel n p (n + p) := isClebschGordanChannel_add n p
  have hv₂ : IsClebschGordanChannel m (n + p) (m + n + p) := by
    rw [Nat.add_assoc]
    exact isClebschGordanChannel_add m (n + p)
  rw [sixJ_eq_recouplingCoeff hq ε δ ζ ⟨hu₁, hu₂⟩ ⟨hv₁, hv₂⟩]
  trans recouplingCoeff (m := m) (n := n) (p := p) hq ε δ ζ 0 0 0 0
  · exact recouplingCoeff_congr hq ε δ ζ
      (congrArg Fin.val (hu₁.index_eq_of_eq (by simp)))
      (congrArg Fin.val (hu₂.index_eq_of_eq (by simp)))
      (congrArg Fin.val (hv₁.index_eq_of_eq (by simp)))
      (congrArg Fin.val (hv₂.index_eq_of_eq (by simp [Nat.add_assoc])))
  refine schurScalar_eq_of_apply_vec_zero ?_
  rw [recouplingHom, LinearMap.comp_apply, LinearMap.comp_apply,
    clebschGordanLeftInclusion_vec_zero]
  have hleft : tensorMap ℂ (UqSl2 q) (clebschGordanInclusion (m := m) (n := n)
        (ε := ε) (δ := δ) hq 0) LinearMap.id
      (clebschGordanVector q (m + n - 2 * ↑(0 : Fin (min m n + 1))) (ε * δ) p ζ
        ↑(0 : Fin (min (m + n - 2 * ↑(0 : Fin (min m n + 1))) p + 1))) =
      tmul ℂ (UqSl2 q) (tmul ℂ (UqSl2 q) (vec q m ε 0) (vec q n δ 0)) (vec q p ζ 0) := by
    rw [Fin.val_zero (n := min (m + n - 2 * ↑(0 : Fin (min m n + 1))) p + 1),
      clebschGordanVector_zero, tensorMap_tmul, LinearMap.id_apply,
      clebschGordanInclusion_vec_zero, Fin.val_zero, clebschGordanVector_zero]
  have hright : tmul ℂ (UqSl2 q) (vec q m ε 0)
        (tmul ℂ (UqSl2 q) (vec q n δ 0) (vec q p ζ 0)) =
      clebschGordanRightInclusion (m := m) (n := n) (p := p) (ε := ε) (δ := δ) (ζ := ζ)
        hq 0 0 (vec q _ _ 0) := by
    rw [clebschGordanRightInclusion_vec_zero,
      Fin.val_zero (n := min m (n + p - 2 * ↑(0 : Fin (min n p + 1))) + 1),
      clebschGordanVector_zero, tensorMap_tmul, LinearMap.id_apply,
      clebschGordanInclusion_vec_zero, Fin.val_zero, clebschGordanVector_zero]
  rw [hleft, LinearEquiv.coe_toLinearMap, assoc_tmul, hright,
    clebschGordanRightProjection_inclusion_self, one_smul]

private theorem clebschGordanInclusion_zero_left_vec [Fact (q ≠ 0)]
    (hq : IsGenericQuantumParameter q) (ε : ℤˣ) (n : ℕ) (δ : ℤˣ) (a : ℕ) :
    clebschGordanInclusion (m := 0) (n := n) (ε := ε) (δ := δ) hq 0 (vec q _ _ a) =
      tmul ℂ (UqSl2 q) (vec q 0 ε 0) (vec q n δ a) := by
  induction a with
  | zero =>
    rw [Nat.cast_zero, clebschGordanInclusion_vec_zero]
    simp
  | succ a ih =>
    have hqa : quantumInteger q ((a : ℤ) + 1) ≠ 0 := quantumInteger_ne_zero hq (by omega)
    apply smul_right_injective _ hqa
    dsimp only
    have hfv : quantumInteger q ((a : ℤ) + 1) •
        clebschGordanInclusion (m := 0) (n := n) (ε := ε) (δ := δ) hq 0
          (vec q _ _ ((a : ℕ) + 1)) =
        f q • clebschGordanInclusion (m := 0) (n := n) (ε := ε) (δ := δ) hq 0 (vec q _ _ a) := by
      rw [← LinearMap.map_smul_of_tower, ← f_smul_vec, map_smul]
    rw [Nat.cast_succ, hfv, ih, f_smul_tmul]
    have hf0 : f q • vec q 0 ε 0 = 0 := by simp
    rw [hf0, zero_tmul, zero_add, f_smul_vec, tmul_smul]

/-- When the first factor is `L_0^ε`, the quantum 6j coefficient on any admissible channel `k` of
`L_n^δ ⊗ L_p^ζ` equals `1`. -/
theorem sixJ_zero_left (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {n p k : ℕ}
    (hk : IsClebschGordanChannel n p k) :
    sixJ hq ε δ ζ 0 n p k n k = 1 := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have hu₁ : IsClebschGordanChannel 0 n n := isClebschGordanChannel_zero_left.mpr rfl
  have hv₂ : IsClebschGordanChannel 0 k k := isClebschGordanChannel_zero_left.mpr rfl
  set j₀ : Fin (min (0 + n - 2 * ↑(0 : Fin (min 0 n + 1))) p + 1) :=
    ⟨hk.index, by have := hk.index.isLt; simp; omega⟩
  rw [sixJ_eq_recouplingCoeff hq ε δ ζ ⟨hu₁, hk⟩ ⟨hk, hv₂⟩]
  trans recouplingCoeff (m := 0) (n := n) (p := p) hq ε δ ζ 0 j₀ hk.index 0
  · exact recouplingCoeff_congr hq ε δ ζ (by simp) rfl rfl (by simp)
  refine schurScalar_eq_of_apply_vec_zero ?_
  rw [recouplingHom, LinearMap.comp_apply, LinearMap.comp_apply,
    clebschGordanLeftInclusion_vec_zero]
  have hvec : tensorMap ℂ (UqSl2 q)
        (clebschGordanInclusion (m := 0) (n := n) (ε := ε) (δ := δ) hq 0) LinearMap.id
        (clebschGordanVector q (0 + n - 2 * ↑(0 : Fin (min 0 n + 1))) (ε * δ) p ζ j₀) =
      ∑ a ∈ Finset.range ((hk.index : ℕ) + 1),
        clebschGordanCoeff q n p ζ hk.index a •
          tmul ℂ (UqSl2 q)
            (tmul ℂ (UqSl2 q) (vec q 0 ε 0) (vec q n δ a))
            (vec q p ζ ((hk.index : ℤ) - a)) := by
    rw [clebschGordanVector_def, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [LinearMap.map_smul_of_tower, tensorMap_tmul, LinearMap.id_apply]
    have hcoeff : clebschGordanCoeff q (0 + n - 2 * ↑(0 : Fin (min 0 n + 1))) p ζ hk.index a =
        clebschGordanCoeff q n p ζ hk.index a := by
      congr 1
      simp
    have hj₀ : (j₀ : ℕ) = (hk.index : ℕ) := rfl
    rw [hj₀, hcoeff, clebschGordanInclusion_zero_left_vec hq ε n δ a]
  have hright : assoc ℂ (UqSl2 q) (LadderModule q 0 ε) (LadderModule q n δ) (LadderModule q p ζ)
        (∑ a ∈ Finset.range ((hk.index : ℕ) + 1),
          clebschGordanCoeff q n p ζ hk.index a •
            tmul ℂ (UqSl2 q)
              (tmul ℂ (UqSl2 q) (vec q 0 ε 0) (vec q n δ a))
              (vec q p ζ ((hk.index : ℤ) - a))) =
      clebschGordanRightInclusion (m := 0) (n := n) (p := p) (ε := ε) (δ := δ) (ζ := ζ)
        hq hk.index 0 (vec q _ _ 0) := by
    rw [map_sum]
    have htmul_sum : tmul ℂ (UqSl2 q) (vec q 0 ε 0) (clebschGordanVector q n δ p ζ hk.index) =
        ∑ a ∈ Finset.range ((hk.index : ℕ) + 1),
          tmul ℂ (UqSl2 q) (vec q 0 ε 0)
            (clebschGordanCoeff q n p ζ hk.index a •
              tmul ℂ (UqSl2 q) (vec q n δ a) (vec q p ζ ((hk.index : ℤ) - a))) := by
      rw [clebschGordanVector_def]
      apply (tensorEquiv ℂ (UqSl2 q) _ _).injective
      simp [TensorProduct.tmul_sum]
    have hsum : (∑ a ∈ Finset.range ((hk.index : ℕ) + 1),
        (assoc ℂ (UqSl2 q) (LadderModule q 0 ε) (LadderModule q n δ) (LadderModule q p ζ))
          (clebschGordanCoeff q n p ζ hk.index a •
            tmul ℂ (UqSl2 q) (tmul ℂ (UqSl2 q) (vec q 0 ε 0) (vec q n δ a))
              (vec q p ζ ((hk.index : ℤ) - a)))) =
        tmul ℂ (UqSl2 q) (vec q 0 ε 0) (clebschGordanVector q n δ p ζ hk.index) := by
      rw [htmul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← LinearEquiv.coe_toLinearMap, LinearMap.map_smul_of_tower, LinearEquiv.coe_toLinearMap,
        assoc_tmul, tmul_smul]
    rw [hsum, clebschGordanRightInclusion_vec_zero]
    simp
  rw [hvec, LinearEquiv.coe_toLinearMap, hright, clebschGordanRightProjection_inclusion_self,
    one_smul]

private theorem clebschGordanInclusion_zero_right_vec [Fact (q ≠ 0)]
    (hq : IsGenericQuantumParameter q) (n : ℕ) (δ ζ : ℤˣ) (b : ℕ) :
    clebschGordanInclusion (m := n) (n := 0) (ε := δ) (δ := ζ) hq 0 (vec q _ _ b) =
      ((ζ : ℂ) ^ b) • tmul ℂ (UqSl2 q) (vec q n δ b) (vec q 0 ζ 0) := by
  induction b with
  | zero =>
    rw [Nat.cast_zero, clebschGordanInclusion_vec_zero]
    simp
  | succ b ih =>
    have hqb : quantumInteger q ((b : ℤ) + 1) ≠ 0 := quantumInteger_ne_zero hq (by omega)
    apply smul_right_injective _ hqb
    dsimp only
    have hfv : quantumInteger q ((b : ℤ) + 1) •
        clebschGordanInclusion (m := n) (n := 0) (ε := δ) (δ := ζ) hq 0
          (vec q _ _ ((b : ℕ) + 1)) =
        f q • clebschGordanInclusion (m := n) (n := 0) (ε := δ) (δ := ζ) hq 0 (vec q _ _ b) := by
      rw [← LinearMap.map_smul_of_tower, ← f_smul_vec, map_smul]
    rw [Nat.cast_succ, hfv, ih, smul_comm, f_smul_tmul]
    have hf0 : f q • vec q 0 ζ 0 = 0 := by simp
    have hk0 : kInv q • vec q 0 ζ 0 = (ζ : ℂ) • vec q 0 ζ 0 := by simp
    rw [hf0, tmul_zero, add_zero, hk0, f_smul_vec, ← smul_tmul', tmul_smul,
      smul_smul, smul_smul, smul_smul, pow_succ]
    congr 1
    ring

private theorem clebschGordanCoeff_mul_sign (q : ℂ) (m n : ℕ) (δ ζ : ℤˣ) (i a : ℕ) :
    clebschGordanCoeff q m n (δ * ζ) i a =
      (ζ : ℂ) ^ a * clebschGordanCoeff q m n δ i a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [clebschGordanCoeff_succ, clebschGordanCoeff_succ, ih, pow_succ, Units.val_mul,
      Int.cast_mul]
    ring

/-- When the third factor is `L_0^ζ`, the quantum 6j coefficient on an admissible channel `k` of
`L_m^ε ⊗ L_n^δ` equals `ζ^((m + n - k) / 2)`, reflecting the `K⁻¹` factor in
`ΔF = F ⊗ K⁻¹ + 1 ⊗ F`. -/
theorem sixJ_zero_right (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {m n k : ℕ}
    (hk : IsClebschGordanChannel m n k) :
    sixJ hq ε δ ζ m n 0 k k n = (ζ : ℂ) ^ ((m + n - k) / 2) := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have hu₂ : IsClebschGordanChannel k 0 k := isClebschGordanChannel_zero_right.mpr rfl
  have hv₁ : IsClebschGordanChannel n 0 n := isClebschGordanChannel_zero_right.mpr rfl
  set s₀ : Fin (min m (n + 0 - 2 * ↑(0 : Fin (min n 0 + 1))) + 1) :=
    ⟨hk.index, by have := hk.index.isLt; simp; omega⟩
  rw [sixJ_eq_recouplingCoeff hq ε δ ζ ⟨hk, hu₂⟩ ⟨hv₁, hk⟩]
  trans recouplingCoeff (m := m) (n := n) (p := 0) hq ε δ ζ hk.index 0 0 s₀
  · exact recouplingCoeff_congr hq ε δ ζ rfl (by simp) (by simp) rfl
  refine schurScalar_eq_of_apply_vec_zero ?_
  rw [recouplingHom, LinearMap.comp_apply, LinearMap.comp_apply,
    clebschGordanLeftInclusion_vec_zero]
  have hleft : assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ) (LadderModule q 0 ζ)
      (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq hk.index) LinearMap.id
        (clebschGordanVector q (m + n - 2 * (hk.index : ℕ)) (ε * δ) 0 ζ
          ↑(0 : Fin (min (m + n - 2 * (hk.index : ℕ)) 0 + 1)))) =
      ∑ a ∈ Finset.range ((hk.index : ℕ) + 1),
        clebschGordanCoeff q m n δ hk.index a •
          tmul ℂ (UqSl2 q) (vec q m ε a)
            (tmul ℂ (UqSl2 q) (vec q n δ ((hk.index : ℤ) - a)) (vec q 0 ζ 0)) := by
    have hsum_tmul : tmul ℂ (UqSl2 q) (clebschGordanVector q m ε n δ hk.index) (vec q 0 ζ 0) =
        ∑ a ∈ Finset.range ((hk.index : ℕ) + 1),
          tmul ℂ (UqSl2 q)
            (clebschGordanCoeff q m n δ hk.index a •
              tmul ℂ (UqSl2 q) (vec q m ε a) (vec q n δ ((hk.index : ℤ) - a)))
            (vec q 0 ζ 0) := by
      rw [clebschGordanVector_def]
      apply (tensorEquiv ℂ (UqSl2 q) _ _).injective
      simp [TensorProduct.sum_tmul]
    rw [Fin.val_zero, clebschGordanVector_zero, tensorMap_tmul, LinearMap.id_apply,
      clebschGordanInclusion_vec_zero, hsum_tmul, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← smul_tmul', ← LinearEquiv.coe_toLinearMap, LinearMap.map_smul_of_tower,
      LinearEquiv.coe_toLinearMap, assoc_tmul]
  have hright : clebschGordanRightInclusion (m := m) (n := n) (p := 0) (ε := ε) (δ := δ) (ζ := ζ)
        hq 0 s₀ (vec q _ _ 0) =
      ((ζ : ℂ) ^ (hk.index : ℕ)) •
        ∑ a ∈ Finset.range ((hk.index : ℕ) + 1),
          clebschGordanCoeff q m n δ hk.index a •
            tmul ℂ (UqSl2 q) (vec q m ε a)
              (tmul ℂ (UqSl2 q) (vec q n δ ((hk.index : ℤ) - a)) (vec q 0 ζ 0)) := by
    rw [clebschGordanRightInclusion_vec_zero, clebschGordanVector_def, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_range] at ha
    have hs₀ : (s₀ : ℕ) = (hk.index : ℕ) := rfl
    rw [hs₀] at ha ⊢
    have hsub : ((hk.index : ℤ) - a) = (((hk.index : ℕ) - a : ℕ) : ℤ) := by omega
    have hn0 : n + 0 - 2 * ↑(0 : Fin (min n 0 + 1)) = n := by simp
    rw [LinearMap.map_smul_of_tower, tensorMap_tmul, LinearMap.id_apply, hsub,
      clebschGordanInclusion_zero_right_vec hq n δ ζ ((hk.index : ℕ) - a), hn0,
      clebschGordanCoeff_mul_sign q m n δ ζ hk.index a, tmul_smul, smul_smul, smul_smul]
    congr 1
    rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le (by omega)]
  have hζsq : ((ζ : ℂ) ^ (hk.index : ℕ)) * ((ζ : ℂ) ^ (hk.index : ℕ)) = 1 := by
    rw [← mul_pow]
    rcases Int.units_eq_one_or ζ with rfl | rfl <;> simp
  have hlhs_eq : ∑ a ∈ Finset.range ((hk.index : ℕ) + 1),
        clebschGordanCoeff q m n δ hk.index a •
          tmul ℂ (UqSl2 q) (vec q m ε a)
            (tmul ℂ (UqSl2 q) (vec q n δ ((hk.index : ℤ) - a)) (vec q 0 ζ 0)) =
      ((ζ : ℂ) ^ (hk.index : ℕ)) •
        clebschGordanRightInclusion (m := m) (n := n) (p := 0) (ε := ε) (δ := δ) (ζ := ζ)
          hq 0 s₀ (vec q _ _ 0) := by
    rw [hright, smul_smul, hζsq, one_smul]
  rw [LinearEquiv.coe_toLinearMap, hleft, hlhs_eq, LinearMap.map_smul_of_tower,
    clebschGordanRightProjection_inclusion_self]
  rfl

end SixJ

end TauCeti.UqSl2
