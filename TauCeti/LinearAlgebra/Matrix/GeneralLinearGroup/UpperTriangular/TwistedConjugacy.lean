/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `DoubleCoset.doubleCoset` states membership in the double coset `I₁ * diagGL t * I₁`.
public import Mathlib.GroupTheory.DoubleCoset
-- `MulArchimedean` forces off-diagonal entries bounded by all integer powers to vanish.
public import Mathlib.Algebra.Order.Archimedean.Basic
-- `Valued` supplies the valuation topology on `K`, `Matrix m m K`, and `GL m K`.
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
-- `Matrix.GeneralLinearGroup` topology and `Continuous.generalLinearGroup_map`.
public import Mathlib.Topology.Algebra.Group.Matrix
-- `TauCeti.mem_map_iwahoriOne_iff` characterizes membership in `I₁` by entry valuations.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.IwasawaBruhat
-- `IsClosed.mem_of_mapClusterPt` and `exists_clusterPt_of_compactSpace`.
import Mathlib.Topology.Compactness.Compact
-- `Valued.t2Space` or `IsTopologicalAddGroup.t2Space_of_zero_sep`.
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Twisted conjugacy in pro-`p` Iwahori double cosets of `GL_m`

Let `K` be a valued field with valuation `v : Valuation K Γ₀` whose value group is rank one
(`[MulArchimedean Γ₀ˣ]`) and whose valuation subring `𝒪` is compact. Let `m` be a finite linearly
ordered index type, and let `I₁ ⊆ GL_m(K)` be the image of the pro-`p` Iwahori subgroup
`TauCeti.iwahoriOne m 𝒪` of `GL_m(𝒪)`: the integral invertible matrices that are upper
unitriangular modulo the maximal ideal.

Given a continuous ring endomorphism `σ : K →+* K` preserving the valuation and acting surjectively
on `GL_m(K)` (including `σ = RingHom.id K`), and a diagonal element `t : m → Kˣ` whose diagonal
entries have strictly increasing valuations `v (t i) < v (t j)` for `i < j`, every element `g` of
the double coset `I₁ · diag(t) · I₁` is `σ`-conjugate by an element of `I₁` to `diag(t * d)` for
some diagonal `d` with `diag(d) ∈ I₁`:

`k⁻¹ * g * σ(k) = diag(t * d)`.

## Method of proof

Writing `X k := diag(t)⁻¹ * (k⁻¹ * g * σ(k))` and `H j := diag(t)⁻ʲ I₁ diag(t)ʲ`, the proof
proceeds by successive approximation:

* Starting from `g = k₀ * diag(t) * k₁` with `k₀, k₁ ∈ I₁`, we have `X k₀ ∈ H 0`.
* Using the Iwahori factorization `I₁ = U₁ · L₁` from
  `TauCeti.exists_mem_upperUnitriangularGroup_isLowerTriangular_inv_mul`, upper-triangular elements
  of `I₁` stay in `H j` for all `j ≥ 0` while lower-triangular elements of `I₁` are contracted into
  `H (-1)` by `diag(t)⁻¹ (·) diag(t)`. This widens the range `[0, b]` to `[0, b + 1]`.
* Multiplying `k` on the right by `diag(t) * X k * diag(t)⁻¹ ∈ I₁` shifts the range `[-a, b + 1]`
  down to `[-(a + 1), b]`.
* Thus for every `a, b : ℕ` there exists `k ∈ I₁` with `X k ∈ H j` for all `-a ≤ j ≤ b`.
* Since `I₁` is open (hence closed) and compact in `GL_m(K)`, a cluster point `k ∈ I₁` satisfies
  `X k ∈ H j` for every `j : ℤ`.
* By `MulArchimedean Γ₀ˣ` and strict monotonicity of `i ↦ v (t i)`, the intersection `⋂ j : ℤ, H j`
  consists solely of diagonal matrices in `I₁`.

## Main results

* `TauCeti.diagGL_mem_map_iwahoriOne_iff`: a diagonal matrix lies in `I₁` iff each diagonal entry
  is congruent to `1` modulo the maximal ideal.
* `TauCeti.isOpen_map_iwahoriOne` and `TauCeti.isCompact_map_iwahoriOne`: topological properties
  of `I₁` in `GL_m(K)`.
* `TauCeti.exists_inv_mul_mul_map_eq_diagGL_mul`: `σ`-conjugacy in `I₁ · diag(t) · I₁` to
  `diag(t * d)` with `diag(d) ∈ I₁`.

## References

* U. Görtz, T. J. Haines, R. E. Kottwitz, and D. C. Reuman, *Affine Deligne–Lusztig varieties in
  affine flag varieties*, Compositio Math. 146 (2010), Theorem 1.1.5.
* The proof route follows [grh-lean](https://github.com/lsernau/grh-lean) (Apache 2.0),
  `grh/src/Lib/LocalGL/Iwahori/ParahoricStructure.lean`
  (`New.exists_inv_mul_mul_map_eq_diagGL_mul`); the formalization here is independent and works for
  arbitrary finite linearly ordered index types and rank-one valued fields.
-/

public section

namespace TauCeti

open Matrix Filter

section ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K) {m : Type*} [Fintype m] [LinearOrder m]

/-- The image of the pro-`p` Iwahori subgroup `iwahoriOne m A` inside `GL m K`. -/
private abbrev mapIwahoriOne : Subgroup (GL m K) :=
  (iwahoriOne m A).map (Matrix.GeneralLinearGroup.map (algebraMap A K))

/-- A diagonal matrix lies in the pro-`p` Iwahori subgroup of `GL m K` exactly when every diagonal
entry satisfies `v (t i - 1) < 1`. -/
theorem diagGL_mem_map_iwahoriOne_iff {t : m → Kˣ} :
    diagGL t ∈ (iwahoriOne m A).map (Matrix.GeneralLinearGroup.map (algebraMap A K)) ↔
      ∀ i : m, A.valuation ((t i : K) - 1) < 1 := by
  rw [mem_map_iwahoriOne_iff]
  constructor
  · rintro ⟨-, -, hdiag⟩
    simpa [diagGL_coe] using hdiag
  · intro hdiag
    refine ⟨fun i j ↦ ?_, fun i j hji ↦ ?_, fun i ↦ by simpa [diagGL_coe] using hdiag i⟩
    · simp only [diagGL_coe, diagonal_apply]
      split_ifs with hij
      · subst hij
        have h1 : A.valuation ((t i : K) - 1 + 1) = A.valuation (1 : K) :=
          Valuation.map_add_eq_of_lt_right A.valuation (by simpa using hdiag i)
        simpa using h1.le
      · simp
    · simp [hji.ne']

/-- Conjugating an upper-triangular element of `I₁` by a dominant diagonal matrix keeps it in
`I₁`. -/
private lemma diagGL_mul_inv_mem_mapIwahoriOne_of_isUpperTriangular {t : m → Kˣ}
    (ht : Monotone fun i ↦ A.valuation (t i : K)) {u : GL m K}
    (hu : u ∈ mapIwahoriOne A) (hutri : ∀ ⦃i j : m⦄, j < i → (u : Matrix m m K) i j = 0) :
    diagGL t * u * (diagGL t)⁻¹ ∈ mapIwahoriOne A := by
  obtain ⟨h1, -, hdiag⟩ := (mem_map_iwahoriOne_iff A).mp hu
  rw [mem_map_iwahoriOne_iff]
  refine ⟨fun i j ↦ ?_, fun i j hji ↦ ?_, fun i ↦ ?_⟩
  · rw [diagGL_mul_mul_inv_apply]
    rcases lt_or_ge j i with hji | hij
    · simp [hutri hji]
    · rw [Units.val_inv_eq_inv_val, map_mul, map_mul, map_inv₀]
      have hpos : 0 < A.valuation (t j : K) := pos_iff_ne_zero.mpr (by simp)
      have hratio : A.valuation (t i : K) * (A.valuation (t j : K))⁻¹ ≤ 1 :=
        (mul_inv_le_iff₀ hpos).mpr (by simpa using ht hij)
      calc A.valuation (t i : K) * A.valuation (u i j) * (A.valuation (t j : K))⁻¹
          = A.valuation (t i : K) * (A.valuation (t j : K))⁻¹ * A.valuation (u i j) :=
            mul_right_comm _ _ _
        _ ≤ 1 * 1 := mul_le_mul' hratio (h1 i j)
        _ = 1 := one_mul 1
  · rw [diagGL_mul_mul_inv_apply, hutri hji]
    simp
  · rw [diagGL_mul_mul_inv_apply]
    simpa [mul_comm, mul_assoc] using hdiag i

/-- Conjugating a lower-triangular element of `I₁` by the inverse of a dominant diagonal matrix
keeps it in `I₁`. -/
private lemma diagGL_inv_mul_mem_mapIwahoriOne_of_isLowerTriangular {t : m → Kˣ}
    (ht : Monotone fun i ↦ A.valuation (t i : K)) {l : GL m K}
    (hl : l ∈ mapIwahoriOne A) (hltri : ∀ ⦃i j : m⦄, i < j → (l : Matrix m m K) i j = 0) :
    (diagGL t)⁻¹ * l * diagGL t ∈ mapIwahoriOne A := by
  obtain ⟨h1, hlow, hdiag⟩ := (mem_map_iwahoriOne_iff A).mp hl
  have hinv : (diagGL t)⁻¹ = diagGL t⁻¹ := (map_inv diagGL t).symm
  rw [hinv, show diagGL t = (diagGL t⁻¹)⁻¹ by simp, mem_map_iwahoriOne_iff]
  refine ⟨fun i j ↦ ?_, fun i j hji ↦ ?_, fun i ↦ ?_⟩
  · rw [diagGL_mul_mul_inv_apply]
    rcases lt_or_ge i j with hij | hji
    · simp [hltri hij]
    · rw [Pi.inv_apply, Pi.inv_apply, inv_inv, Units.val_inv_eq_inv_val, map_mul, map_mul,
        map_inv₀]
      have hpos : 0 < A.valuation (t i : K) := pos_iff_ne_zero.mpr (by simp)
      have hratio : (A.valuation (t i : K))⁻¹ * A.valuation (t j : K) ≤ 1 :=
        (inv_mul_le_iff₀ hpos).mpr (by simpa using ht hji)
      calc (A.valuation (t i : K))⁻¹ * A.valuation (l i j) * A.valuation (t j : K)
          = (A.valuation (t i : K))⁻¹ * A.valuation (t j : K) * A.valuation (l i j) :=
            mul_right_comm _ _ _
        _ ≤ 1 * 1 := mul_le_mul' hratio (h1 i j)
        _ = 1 := one_mul 1
  · rw [diagGL_mul_mul_inv_apply, Pi.inv_apply, Pi.inv_apply, inv_inv, Units.val_inv_eq_inv_val,
      map_mul, map_mul, map_inv₀]
    have hpos : 0 < A.valuation (t i : K) := pos_iff_ne_zero.mpr (by simp)
    have hratio : (A.valuation (t i : K))⁻¹ * A.valuation (t j : K) ≤ 1 :=
      (inv_mul_le_iff₀ hpos).mpr (by simpa using ht hji.le)
    calc (A.valuation (t i : K))⁻¹ * A.valuation (l i j) * A.valuation (t j : K)
        = (A.valuation (t i : K))⁻¹ * A.valuation (t j : K) * A.valuation (l i j) :=
          mul_right_comm _ _ _
      _ ≤ 1 * A.valuation (l i j) := mul_le_mul_of_nonneg_right hratio zero_le
      _ = A.valuation (l i j) := one_mul _
      _ < 1 := hlow hji
  · rw [diagGL_mul_mul_inv_apply]
    simpa [Pi.inv_apply, Units.val_inv_eq_inv_val, mul_comm, mul_assoc] using hdiag i

/-- Every element `x ∈ I₁` factors as `x = u * l` with `u ∈ I₁` upper triangular and
`diag(t)⁻¹ * l * diag(t) ∈ I₁` whenever `t` is dominant. -/
private lemma exists_upperTriangular_mul_conj_mem_mapIwahoriOne {t : m → Kˣ}
    (ht : Monotone fun i ↦ A.valuation (t i : K)) {x : GL m K} (hx : x ∈ mapIwahoriOne A) :
    ∃ u ∈ mapIwahoriOne A, (∀ ⦃i j : m⦄, j < i → (u : Matrix m m K) i j = 0) ∧
      (diagGL t)⁻¹ * (u⁻¹ * x) * diagGL t ∈ mapIwahoriOne A := by
  rcases Subgroup.mem_map.mp hx with ⟨xA, hxA, rfl⟩
  have hjac : IsLocalRing.maximalIdeal A ≤ Ring.jacobson A := by
    intro a ha
    rw [Ring.mem_jacobson_iff]
    intro y
    by_contra hnu
    have h1 : a * y + 1 ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h2 : a * y ∈ IsLocalRing.maximalIdeal A := Ideal.mul_mem_right y _ ha
    have h3 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by simpa using sub_mem h1 h2
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h3 isUnit_one)
  obtain ⟨uA, huA_ut, hlA_lt⟩ :=
    exists_mem_upperUnitriangularGroup_isLowerTriangular_inv_mul (m := m) hjac
      ((iwahoriOne_le_iwahori : iwahoriOne m A ≤ iwahori m A) hxA)
  have huA_tri := UpperUnitriangularGroup.mem_iff.mp huA_ut
  let f := Matrix.GeneralLinearGroup.map (n := m) (algebraMap A K)
  have huA_I1 : uA ∈ iwahoriOne m A := by
    rw [iwahoriOne, mem_upperUnitriangularCongruenceSubgroup_iff]
    refine ⟨fun i j hji ↦ ?_, fun i ↦ ?_⟩
    · simp [huA_tri.isUpperTriangular hji]
    · simp [huA_tri.apply_diag i]
  refine ⟨f uA, Subgroup.mem_map_of_mem f huA_I1, fun i j hji ↦ ?_, ?_⟩
  · simp [f, huA_tri.isUpperTriangular hji]
  · have hl_mem : (f uA)⁻¹ * f xA ∈ mapIwahoriOne A := by
      rw [← map_inv, ← map_mul]
      exact Subgroup.mem_map_of_mem f (Subgroup.mul_mem _ (Subgroup.inv_mem _ huA_I1) hxA)
    refine diagGL_inv_mul_mem_mapIwahoriOne_of_isLowerTriangular A ht hl_mem fun i j hij ↦ ?_
    rw [← map_inv, ← map_mul, Matrix.GeneralLinearGroup.map_apply]
    simp [hlA_lt hij]

end ValuationSubring

section ValuedField

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable {m : Type*} [Fintype m] [LinearOrder m]

private abbrev valSubring (K : Type*) [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] : ValuationSubring K :=
  (Valued.v (R := K)).valuationSubring

private abbrev I1 (K : Type*) [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (m : Type*) [Fintype m] [LinearOrder m] : Subgroup (GL m K) :=
  (iwahoriOne m (valSubring K)).map (Matrix.GeneralLinearGroup.map (algebraMap (valSubring K) K))

private lemma valSubring_le_one_iff {x : K} :
    (valSubring K).valuation x ≤ 1 ↔ Valued.v x ≤ (1 : Γ₀) :=
  ValuationSubring.valuation_le_one_iff (valSubring K) x

private lemma valSubring_lt_one_iff {x : K} :
    (valSubring K).valuation x < 1 ↔ Valued.v x < (1 : Γ₀) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hpos1 : 0 < (valSubring K).valuation x := pos_iff_ne_zero.mpr (by simp [hx])
    have hpos2 : 0 < Valued.v x := pos_iff_ne_zero.mpr (by simp [hx])
    have h1 : (valSubring K).valuation x < 1 ↔ ¬ (valSubring K).valuation x⁻¹ ≤ 1 := by
      rw [map_inv₀, not_le, one_lt_inv₀ hpos1]
    have h2 : Valued.v x < (1 : Γ₀) ↔ ¬ Valued.v x⁻¹ ≤ (1 : Γ₀) := by
      rw [map_inv₀, not_le, one_lt_inv₀ hpos2]
    rw [h1, h2, valSubring_le_one_iff]

private lemma mem_I1_iff {g : GL m K} :
    g ∈ I1 K m ↔
      (∀ i j, Valued.v (g i j) ≤ 1) ∧ (∀ ⦃i j⦄, j < i → Valued.v (g i j) < 1) ∧
        ∀ i, Valued.v (g i i - 1) < 1 := by
  simp only [I1, mem_map_iwahoriOne_iff, valSubring_le_one_iff, valSubring_lt_one_iff]

/-- The conjugated subgroup `diag(t)⁻ʲ I₁ diag(t)ʲ`. -/
private abbrev conjI1 (t : m → Kˣ) (j : ℤ) : Subgroup (GL m K) :=
  (MulAut.conj (diagGL t) ^ j).comapSubgroup (I1 K m)

/-- The shifted twisted conjugate `diag(t)⁻¹ * (k⁻¹ * g * σ(k))`. -/
private abbrev twistedConj (t : m → Kˣ) (g : GL m K) (σ : K →+* K) (k : I1 K m) : GL m K :=
  (diagGL t)⁻¹ * ((k : GL m K)⁻¹ * g * Matrix.GeneralLinearGroup.map σ (k : GL m K))

private lemma conjI1_mem_iff {t : m → Kˣ} {j : ℤ} {x : GL m K} :
    x ∈ conjI1 t j ↔ diagGL (t ^ j) * x * (diagGL (t ^ j))⁻¹ ∈ I1 K m := by
  change (MulAut.conj (diagGL t) ^ j) x ∈ I1 K m ↔ _
  rw [← map_zpow, MulAut.conj_apply, map_zpow]

private lemma map_mem_conjI1_iff {t : m → Kˣ} {σ : K →+* K}
    (hσ : ∀ x : K, Valued.v (σ x) = Valued.v x) {j : ℤ} {x : GL m K} :
    Matrix.GeneralLinearGroup.map σ x ∈ conjI1 t j ↔ x ∈ conjI1 t j := by
  simp only [conjI1_mem_iff, mem_I1_iff, diagGL_mul_mul_inv_apply,
    Matrix.GeneralLinearGroup.map_apply]
  have hentry (a b : m) :
      Valued.v (((t ^ j) a : K) * σ (x a b) * (((t ^ j) b)⁻¹ : Kˣ)) =
        Valued.v (((t ^ j) a : K) * x a b * (((t ^ j) b)⁻¹ : Kˣ)) := by
    simp [map_mul, hσ]
  have hdiag (a : m) :
      Valued.v (((t ^ j) a : K) * σ (x a a) * (((t ^ j) a)⁻¹ : Kˣ) - 1) =
        Valued.v (((t ^ j) a : K) * x a a * (((t ^ j) a)⁻¹ : Kˣ) - 1) := by
    have hmul : ∀ c : K, ((t ^ j) a : K) * c * (((t ^ j) a)⁻¹ : Kˣ) = c := fun c ↦ by
      rw [Units.val_inv_eq_inv_val, mul_comm _ c, mul_assoc, mul_inv_cancel₀ (Units.ne_zero _),
        mul_one]
    rw [hmul, hmul]
    conv_lhs => rw [← map_one σ, ← map_sub, hσ]
  simp only [hentry, hdiag]

omit [Fintype m] in
private lemma monotone_valSubring_of_monotone_valued {t : m → Kˣ}
    (ht : Monotone fun i : m ↦ Valued.v (t i : K)) :
    Monotone fun i : m ↦ (valSubring K).valuation (t i : K) := by
  intro i j hij
  have hdiv : Valued.v ((t i : K) * ((t j : K))⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀]
    exact (mul_inv_le_iff₀ (pos_iff_ne_zero.mpr (by simp))).mpr (by simpa using ht hij)
  have hdivA : (valSubring K).valuation ((t i : K) * ((t j : K))⁻¹) ≤ 1 :=
    valSubring_le_one_iff.mpr hdiv
  rw [map_mul, map_inv₀] at hdivA
  simpa using (mul_inv_le_iff₀ (pos_iff_ne_zero.mpr (by simp))).mp hdivA

private lemma widen_twistedConj {t : m → Kˣ}
    (htA : Monotone fun i : m ↦ (valSubring K).valuation (t i : K))
    {σ : K →+* K} (hσ : ∀ x : K, Valued.v (σ x) = Valued.v x)
    (hσ_surj : Function.Surjective (Matrix.GeneralLinearGroup.map (n := m) σ))
    {g : GL m K} (b : ℕ) (k : I1 K m)
    (hk : ∀ j : ℤ, 0 ≤ j → j ≤ b → twistedConj t g σ k ∈ conjI1 t j) :
    ∃ k' : I1 K m, ∀ j : ℤ, 0 ≤ j → j ≤ b + 1 → twistedConj t g σ k' ∈ conjI1 t j := by
  obtain ⟨u, hu, hutri, hu_conj⟩ :=
    exists_upperTriangular_mul_conj_mem_mapIwahoriOne (valSubring K) htA (hk 0 le_rfl (by omega))
  obtain ⟨z, hz⟩ := hσ_surj (u⁻¹ * twistedConj t g σ k)
  have hu_mem (j : ℕ) : u ∈ conjI1 t j := by
    have htpow : Monotone fun i : m ↦ (valSubring K).valuation ((t ^ j) i : K) := by
      intro i₁ i₂ hle
      simp only [Pi.pow_apply, Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_pow_left' (htA hle) j
    have hres :=
      diagGL_mul_inv_mem_mapIwahoriOne_of_isUpperTriangular (valSubring K) htpow hu hutri
    rw [conjI1_mem_iff]
    simpa [zpow_natCast] using hres
  have hz_mem (j : ℕ) (hj : j ≤ b + 1) : z ∈ conjI1 t (j + -1) := by
    rw [← map_mem_conjI1_iff hσ, hz]
    cases j with
    | zero => simpa [conjI1_mem_iff] using hu_conj
    | succ j =>
      rw [Nat.cast_succ, add_neg_cancel_right]
      exact (conjI1 t j).mul_mem ((conjI1 t j).inv_mem (hu_mem j)) (hk j (by omega) (by omega))
  refine ⟨k * ⟨z, hz_mem 1 (by omega)⟩⁻¹, fun j hj₀ hj ↦ ?_⟩
  lift j to ℕ using hj₀
  have hmul : twistedConj t g σ (k * ⟨z, hz_mem 1 (by omega)⟩⁻¹) =
      ((diagGL t)⁻¹ * z * diagGL t) * u := by
    simp only [twistedConj, Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev,
      MonoidHom.map_mul, MonoidHom.map_inv, hz]
    group
  rw [hmul]
  have hz' : (diagGL t)⁻¹ * z * diagGL t ∈ conjI1 t j := by
    rw [conjI1_mem_iff]
    have hz0 := (conjI1_mem_iff).mp (hz_mem j (by omega))
    rw [_root_.zpow_add, _root_.zpow_neg_one, MonoidHom.map_mul, MonoidHom.map_inv,
      _root_.mul_inv_rev, inv_inv] at hz0
    simpa [mul_assoc] using hz0
  exact (conjI1 t j).mul_mem hz' (hu_mem j)

private lemma shift_twistedConj {t : m → Kˣ} {σ : K →+* K}
    (hσ : ∀ x : K, Valued.v (σ x) = Valued.v x) {g : GL m K} (a b : ℕ) (k : I1 K m)
    (hk : ∀ j : ℤ, -(a : ℤ) ≤ j → j ≤ b + 1 → twistedConj t g σ k ∈ conjI1 t j) :
    ∃ k' : I1 K m, ∀ j : ℤ, -((a + 1 : ℕ) : ℤ) ≤ j → j ≤ b →
      twistedConj t g σ k' ∈ conjI1 t j := by
  let y : I1 K m :=
    ⟨(MulAut.conj (diagGL t) ^ (1 : ℤ)) (twistedConj t g σ k), hk 1 (by omega) (by omega)⟩
  refine ⟨k * y, fun j hj₀ hj ↦ ?_⟩
  have hy : (y : GL m K) ∈ conjI1 t j := by
    rw [conjI1_mem_iff]
    have hk1 := (conjI1_mem_iff).mp (hk (j + 1) (by omega) (by omega))
    rw [_root_.zpow_add, zpow_one, MonoidHom.map_mul, _root_.mul_inv_rev] at hk1
    simpa [y, MulAut.conj_apply, mul_assoc] using hk1
  have hmul : twistedConj t g σ (k * y) = Matrix.GeneralLinearGroup.map σ (y : GL m K) := by
    simp [twistedConj, y, MulAut.conj_apply, mul_assoc]
  rw [hmul]
  exact (map_mem_conjI1_iff hσ).mpr hy

private lemma exists_twistedConj_mem_conjI1 {t : m → Kˣ}
    (ht : Monotone fun i : m ↦ Valued.v (t i : K))
    {σ : K →+* K} (hσ : ∀ x : K, Valued.v (σ x) = Valued.v x)
    (hσ_surj : Function.Surjective (Matrix.GeneralLinearGroup.map (n := m) σ))
    {g : GL m K} (hg : g ∈ DoubleCoset.doubleCoset (diagGL t) (I1 K m) (I1 K m))
    (a b : ℕ) :
    ∃ k : I1 K m, ∀ j : ℤ, -(a : ℤ) ≤ j → j ≤ b → twistedConj t g σ k ∈ conjI1 t j := by
  have htA := monotone_valSubring_of_monotone_valued ht
  have h_start : ∃ k : I1 K m, twistedConj t g σ k ∈ conjI1 t 0 := by
    obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    exact ⟨⟨k, hk⟩, by
      simpa [twistedConj, mul_assoc] using
        (conjI1 t 0).mul_mem hk' ((map_mem_conjI1_iff hσ).mpr hk)⟩
  induction a generalizing b with
  | succ a ih => exact (ih (b + 1)).elim (shift_twistedConj hσ a b)
  | zero =>
    induction b with
    | succ b ih => exact ih.elim (widen_twistedConj htA hσ hσ_surj b)
    | zero => exact h_start.imp fun k hk j hj₀ hj ↦ by rwa [show j = 0 by omega]

private lemma isDiag_of_forall_mem_conjI1 [MulArchimedean Γ₀ˣ] {t : m → Kˣ}
    (ht : Function.Injective fun i : m ↦ Valued.v (t i : K))
    {x : GL m K} (hx : ∀ j : ℤ, x ∈ conjI1 t j) :
    (x : Matrix m m K).IsDiag := by
  intro i j hij
  by_contra hne
  have hvx : Valued.v (x i j) ≠ 0 := by simp [hne]
  have hti : Valued.v (t i : K) ≠ 0 := by simp
  have htj : Valued.v (t j : K) ≠ 0 := by simp
  let r : Γ₀ˣ := Units.mk0 (Valued.v (t i : K) / Valued.v (t j : K)) (div_ne_zero hti htj)
  let u : Γ₀ˣ := Units.mk0 (Valued.v (x i j)) hvx
  have hbound (n : ℤ) : ((r ^ n * u : Γ₀ˣ) : Γ₀) ≤ 1 := by
    obtain ⟨h1, -, -⟩ := mem_I1_iff.mp (conjI1_mem_iff.mp (hx n))
    have h := h1 i j
    rw [diagGL_mul_mul_inv_apply, Units.val_inv_eq_inv_val, map_mul, map_mul, map_inv₀] at h
    have hti_z : ((t ^ n) i : K) = (t i : K) ^ n := Units.val_zpow_eq_zpow_val (t i) n
    have htj_z : ((t ^ n) j : K) = (t j : K) ^ n := Units.val_zpow_eq_zpow_val (t j) n
    rw [hti_z, htj_z, map_zpow₀, map_zpow₀] at h
    have hru : ((r ^ n * u : Γ₀ˣ) : Γ₀) =
        Valued.v (t i : K) ^ n * Valued.v (x i j) * (Valued.v (t j : K) ^ n)⁻¹ := by
      simp [r, u, div_eq_mul_inv, mul_zpow, mul_right_comm]
    exact hru ▸ h
  have hr_ne : r ≠ 1 := by
    intro hr1
    apply hij (ht ((div_eq_one_iff_eq htj).mp (congrArg Units.val hr1)))
  rcases lt_or_gt_of_ne hr_ne with hr_lt | hr_gt
  · obtain ⟨n, hn⟩ := MulArchimedean.arch u⁻¹ (one_lt_inv'.mpr hr_lt)
    have h1 : (1 : Γ₀ˣ) < r ^ (-((n + 1 : ℕ) : ℤ)) * u := by
      rw [← inv_lt_iff_one_lt_mul, _root_.zpow_neg, zpow_natCast, ← inv_pow, pow_succ]
      exact lt_of_le_of_lt hn (lt_mul_of_one_lt_right' _ (one_lt_inv'.mpr hr_lt))
    exact not_lt_of_ge (hbound (-((n + 1 : ℕ) : ℤ))) (by exact_mod_cast h1)
  · obtain ⟨n, hn⟩ := MulArchimedean.arch u⁻¹ hr_gt
    have h1 : (1 : Γ₀ˣ) < r ^ ((n + 1 : ℕ) : ℤ) * u := by
      rw [← inv_lt_iff_one_lt_mul, zpow_natCast, pow_succ]
      exact lt_of_le_of_lt hn (lt_mul_of_one_lt_right' _ hr_gt)
    exact not_lt_of_ge (hbound ((n + 1 : ℕ) : ℤ)) (by exact_mod_cast h1)

/-- The open unit ball `{x : K | v x < 1}` is open in a valued field. -/
private lemma isOpen_lt_one : IsOpen {x : K | Valued.v x < (1 : Γ₀)} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [Valued.mem_nhds]
  refine ⟨(1 : (Valued.v (R := K)).ValueGroup₀ˣ), fun y hy ↦ ?_⟩
  have hsub : Valued.v (y - x) < 1 := by
    have hy' : (Valued.v (R := K)).restrict (y - x) < (Valued.v (R := K)).restrict 1 := by
      simpa using hy
    simpa using (Valuation.restrict_lt_iff (Valued.v (R := K))).mp hy'
  calc Valued.v y = Valued.v ((y - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (Valued.v (y - x)) (Valued.v x) := Valued.v.map_add _ _
    _ < 1 := max_lt hsub hx

/-- The pro-`p` Iwahori subgroup `I₁` is an open subgroup of `GL m K`. -/
theorem isOpen_map_iwahoriOne :
    IsOpen ((iwahoriOne m (Valued.v (R := K)).valuationSubring).map
      (Matrix.GeneralLinearGroup.map (algebraMap _ K)) : Set (GL m K)) := by
  have hopen_le : IsOpen {x : K | Valued.v x ≤ (1 : Γ₀)} := Valued.isOpen_integer K
  have hopen_lt : IsOpen {x : K | Valued.v x < (1 : Γ₀)} := isOpen_lt_one
  have hset : ((I1 K m : Subgroup (GL m K)) : Set (GL m K)) =
      (⋂ i : m, ⋂ j : m, {g : GL m K | Valued.v (g i j) ≤ 1}) ∩
      (⋂ i : m, ⋂ j : m, ⋂ (_ : j < i), {g : GL m K | Valued.v (g i j) < 1}) ∩
      (⋂ i : m, {g : GL m K | Valued.v (g i i - 1) < 1}) := by
    ext g
    simp only [SetLike.mem_coe, mem_I1_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq, and_assoc]
  rw [show ((iwahoriOne m (Valued.v (R := K)).valuationSubring).map
      (Matrix.GeneralLinearGroup.map (algebraMap _ K)) : Set (GL m K)) = (I1 K m : Set (GL m K))
      from rfl, hset]
  have hcont (i j : m) : Continuous fun g : GL m K ↦ (g : Matrix m m K) i j := by fun_prop
  refine (IsOpen.inter ?_ ?_).inter ?_
  · refine isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦ ?_
    exact hopen_le.preimage (hcont i j)
  · refine isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
      isOpen_iInter_of_finite fun _ ↦ ?_
    exact hopen_lt.preimage (hcont i j)
  · refine isOpen_iInter_of_finite fun i ↦ ?_
    exact hopen_lt.preimage ((hcont i i).sub continuous_const)

private lemma compactSpace_GL_valSubring [CompactSpace (Valued.v (R := K)).valuationSubring] :
    CompactSpace (GL m (valSubring K)) := by
  have : IsTopologicalRing (valSubring K) := Subring.instIsTopologicalRing (valSubring K).toSubring
  have : CompactSpace (Matrix m m (valSubring K)) := Pi.compactSpace
  have : CompactSpace (Matrix m m (valSubring K))ᵐᵒᵖ :=
    isCompact_univ_iff.mp <| by
      have hsurj : Set.range (MulOpposite.op : Matrix m m (valSubring K) → _) = Set.univ :=
        Set.range_eq_univ.mpr MulOpposite.op_surjective
      rw [← hsurj, ← Set.image_univ]
      exact isCompact_univ.image MulOpposite.continuous_op
  have hclosed : IsClosed (Set.range (Units.embedProduct (Matrix m m (valSubring K)))) := by
    have hset : Set.range (Units.embedProduct (Matrix m m (valSubring K))) =
        {p : Matrix m m (valSubring K) × (Matrix m m (valSubring K))ᵐᵒᵖ |
          p.1 * MulOpposite.unop p.2 = 1 ∧ MulOpposite.unop p.2 * p.1 = 1} := by
      ext ⟨M, N⟩
      refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun ⟨h1, h2⟩ ↦ ⟨⟨M, MulOpposite.unop N, h1, h2⟩, by simp⟩⟩
      rw [← hg]
      exact ⟨g.val_inv, g.inv_val⟩
    rw [hset]
    have h1 : Continuous fun p : Matrix m m (valSubring K) × (Matrix m m (valSubring K))ᵐᵒᵖ ↦
        p.1 * MulOpposite.unop p.2 :=
      continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)
    have h2 : Continuous fun p : Matrix m m (valSubring K) × (Matrix m m (valSubring K))ᵐᵒᵖ ↦
        MulOpposite.unop p.2 * p.1 :=
      (MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst
    exact (isClosed_eq h1 continuous_const).inter (isClosed_eq h2 continuous_const)
  have hcomp_range : IsCompact (Set.range (Units.embedProduct (Matrix m m (valSubring K)))) :=
    isCompact_univ.of_isClosed_subset hclosed (Set.subset_univ _)
  exact isCompact_univ_iff.mp
    ((Units.isInducing_embedProduct (M := Matrix m m (valSubring K))).isCompact_iff.mpr
      ((Set.image_univ (f := Units.embedProduct (Matrix m m (valSubring K)))).symm ▸ hcomp_range))

/-- When the valuation subring of `K` is compact, the pro-`p` Iwahori subgroup `I₁` is compact in
`GL m K`. -/
theorem isCompact_map_iwahoriOne [CompactSpace (Valued.v (R := K)).valuationSubring] :
    IsCompact ((iwahoriOne m (Valued.v (R := K)).valuationSubring).map
      (Matrix.GeneralLinearGroup.map (algebraMap _ K)) : Set (GL m K)) := by
  have : CompactSpace (GL m (valSubring K)) := compactSpace_GL_valSubring
  have hclosed_I1 : IsClosed (iwahoriOne m (valSubring K) : Set (GL m (valSubring K))) := by
    have hpre : (iwahoriOne m (valSubring K) : Set (GL m (valSubring K))) =
        Matrix.GeneralLinearGroup.map (algebraMap (valSubring K) K) ⁻¹'
          (I1 K m : Set (GL m K)) := by
      ext g
      simp only [Set.mem_preimage, SetLike.mem_coe, I1, Subgroup.mem_map]
      refine ⟨fun hg ↦ ⟨g, hg, rfl⟩, fun ⟨g', hg', hgg'⟩ ↦ ?_⟩
      have heq : g' = g := Units.ext (Matrix.ext fun i j ↦ Subtype.ext (by
        have h := congrFun (congrFun (congrArg (fun u : GL m K ↦ (u : Matrix m m K)) hgg') i) j
        simpa [Matrix.GeneralLinearGroup.map_apply] using h))
      rwa [← heq]
    rw [hpre]
    have hcont : Continuous
        (Matrix.GeneralLinearGroup.map (n := m) (algebraMap (valSubring K) K)) :=
      Continuous.generalLinearGroup_map continuous_subtypeVal
    exact ((I1 K m).isClosed_of_isOpen isOpen_map_iwahoriOne).preimage hcont
  have hcompact_I1A : IsCompact (iwahoriOne m (valSubring K) : Set (GL m (valSubring K))) :=
    hclosed_I1.isCompact
  have hcont : Continuous
      (Matrix.GeneralLinearGroup.map (n := m) (algebraMap (valSubring K) K)) :=
    Continuous.generalLinearGroup_map continuous_subtypeVal
  simpa [I1, Subgroup.coe_map] using hcompact_I1A.image hcont

/-- **Twisted conjugacy in `I₁ · diag(t) · I₁`.** Let `σ : K →+* K` be a continuous ring
endomorphism preserving the valuation and acting surjectively on `GL_m(K)`, and let `t : m → Kˣ`
have strictly increasing valuations `v (t i) < v (t j)` for `i < j`. When the valuation subring of
`K` is compact and the value group is rank one, every `g` in the double coset `I₁ · diag(t) · I₁`
satisfies `k⁻¹ * g * σ(k) = diag(t * d)` for some `k ∈ I₁` and diagonal `d` with `diag(d) ∈ I₁`. -/
theorem exists_inv_mul_mul_map_eq_diagGL_mul [MulArchimedean Γ₀ˣ]
    [CompactSpace (Valued.v (R := K)).valuationSubring]
    {t : m → Kˣ} (ht : StrictMono fun i : m ↦ Valued.v (t i : K))
    (σ : K →+* K) (hσ : ∀ x : K, Valued.v (σ x) = Valued.v x) (hσ_cont : Continuous σ)
    (hσ_surj : Function.Surjective (Matrix.GeneralLinearGroup.map (n := m) σ))
    {g : GL m K}
    (hg : g ∈ DoubleCoset.doubleCoset (diagGL t)
      ((iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (Matrix.GeneralLinearGroup.map (algebraMap _ K)))
      ((iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (Matrix.GeneralLinearGroup.map (algebraMap _ K)))) :
    ∃ k ∈ (iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (Matrix.GeneralLinearGroup.map (algebraMap _ K)),
      ∃ d : m → Kˣ,
        diagGL d ∈ (iwahoriOne m (Valued.v (R := K)).valuationSubring).map
          (Matrix.GeneralLinearGroup.map (algebraMap _ K)) ∧
        k⁻¹ * g * Matrix.GeneralLinearGroup.map σ k = diagGL (t * d) := by
  have : CompactSpace (I1 K m) := isCompact_iff_compactSpace.mp isCompact_map_iwahoriOne
  choose f hf using exists_twistedConj_mem_conjI1 ht.monotone hσ hσ_surj hg
  obtain ⟨k, hk⟩ : ∃ k : I1 K m, ClusterPt k (atTop.map fun n ↦ f n n) :=
    exists_clusterPt_of_compactSpace _
  have h_all (j : ℤ) : twistedConj t g σ k ∈ conjI1 t j := by
    have hmap : Continuous (Matrix.GeneralLinearGroup.map (n := m) σ) :=
      Continuous.generalLinearGroup_map hσ_cont
    have h_cont : Continuous fun x : I1 K m ↦
        diagGL (t ^ j) * twistedConj t g σ x * (diagGL (t ^ j))⁻¹ := by
      refine ((continuous_const.mul ?_).mul continuous_const)
      refine continuous_const.mul (((continuous_subtypeVal.inv.mul continuous_const).mul
        (hmap.comp continuous_subtypeVal)))
    have h_closed : IsClosed (twistedConj t g σ ⁻¹' conjI1 t j) := by
      have hpre : twistedConj t g σ ⁻¹' conjI1 t j =
          (fun x : I1 K m ↦ diagGL (t ^ j) * twistedConj t g σ x * (diagGL (t ^ j))⁻¹) ⁻¹'
            (I1 K m : Set (GL m K)) := by
        ext x
        exact conjI1_mem_iff
      rw [hpre]
      exact ((I1 K m).isClosed_of_isOpen isOpen_map_iwahoriOne).preimage h_cont
    refine h_closed.mem_of_mapClusterPt hk ?_
    filter_upwards [mem_atTop j.natAbs] with n hn using hf n n j (by omega) (by omega)
  have hX_mem : twistedConj t g σ k ∈ I1 K m := by simpa using h_all 0
  obtain ⟨-, -, hX_diag⟩ := mem_I1_iff.mp hX_mem
  have h_unit (i : m) : (twistedConj t g σ k : Matrix m m K) i i ≠ 0 := by
    intro h0
    have hlt := hX_diag i
    rw [h0, zero_sub, Valuation.map_neg, map_one] at hlt
    exact lt_irrefl _ hlt
  let d (i : m) : Kˣ := Units.mk0 ((twistedConj t g σ k : Matrix m m K) i i) (h_unit i)
  have hX : diagGL d = twistedConj t g σ k := by
    apply Units.ext
    rw [diagGL_coe]
    exact (isDiag_of_forall_mem_conjI1 ht.injective h_all).diagonal_diag
  refine ⟨k, k.prop, d, ?_, ?_⟩
  · rw [diagGL_mem_map_iwahoriOne_iff]
    intro i
    exact valSubring_lt_one_iff.mpr (by simpa [d] using hX_diag i)
  · rw [map_mul, hX, twistedConj, mul_inv_cancel_left]

end ValuedField

end TauCeti
