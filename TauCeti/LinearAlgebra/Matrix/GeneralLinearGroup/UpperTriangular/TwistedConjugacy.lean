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
-- `TauCeti.mem_map_iwahoriOne_iff` and `TauCeti.diagGL_mem_map_iwahoriOne_iff`.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.IwasawaBruhat
-- `TauCeti.mem_map_iwahoriOne_iff_valued`, `isOpen_map_iwahoriOne`, `isCompact_map_iwahoriOne`.
import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Iwahori
-- `TauCeti.Valued.continuous_of_valuation_eq`.
import TauCeti.Topology.Algebra.Valued.RingHom
-- `Valuation.map_mul_mul_inv_le`.
import TauCeti.RingTheory.Valuation.Basic
-- `Matrix.GeneralLinearGroup.map_surjective`.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Lift
-- `IsClosed.mem_of_mapClusterPt` and `exists_clusterPt_of_compactSpace`.
import Mathlib.Topology.Compactness.Compact
-- `Continuous.generalLinearGroup_map`.
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Twisted conjugacy in pro-`p` Iwahori double cosets of `GL_m`

Let `K` be a valued field with valuation `v : Valuation K Γ₀` whose value group is rank one
(`[MulArchimedean Γ₀ˣ]`) and whose valuation subring `𝒪` is compact. Let `m` be a finite linearly
ordered index type, and let `I₁ ⊆ GL_m(K)` be the image of the pro-`p` Iwahori subgroup
`TauCeti.iwahoriOne m 𝒪` of `GL_m(𝒪)`: the integral invertible matrices that are upper
unitriangular modulo the maximal ideal.

Given a surjective ring endomorphism `σ : K →+* K` preserving the valuation (including
`σ = RingHom.id K` and Frobenius automorphisms), and a diagonal element `t : m → Kˣ` whose diagonal
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
  (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K))

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
    · rw [Units.val_inv_eq_inv_val]
      exact (A.valuation.map_mul_mul_inv_le (ht hij)).trans (h1 i j)
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
  have hstep (i j : m) (hji : j ≤ i) :
      A.valuation (((t⁻¹ i : Kˣ) : K) * l i j * ((t⁻¹ j)⁻¹ : Kˣ)) ≤ A.valuation (l i j) := by
    have heq : ((t⁻¹ i : Kˣ) : K) * l i j * ((t⁻¹ j)⁻¹ : Kˣ) = (t j : K) * l i j * (t i : K)⁻¹ := by
      simp [Pi.inv_apply, Units.val_inv_eq_inv_val]
      ring
    rw [heq]
    exact A.valuation.map_mul_mul_inv_le (ht hji)
  refine ⟨fun i j ↦ ?_, fun i j hji ↦ ?_, fun i ↦ ?_⟩
  · rw [diagGL_mul_mul_inv_apply]
    rcases lt_or_ge i j with hij | hji
    · simp [hltri hij]
    · exact (hstep i j hji).trans (h1 i j)
  · rw [diagGL_mul_mul_inv_apply]
    exact (hstep i j hji.le).trans_lt (hlow hji)
  · rw [diagGL_mul_mul_inv_apply]
    simpa [Pi.inv_apply, Units.val_inv_eq_inv_val, mul_comm, mul_assoc] using hdiag i

/-- Every element `x ∈ I₁` factors as `x = u * l` with `u ∈ I₁` upper triangular and
`diag(t)⁻¹ * l * diag(t) ∈ I₁` whenever `t` is dominant. -/
private lemma exists_upperTriangular_mul_conj_mem_mapIwahoriOne {t : m → Kˣ}
    (ht : Monotone fun i ↦ A.valuation (t i : K)) {x : GL m K} (hx : x ∈ mapIwahoriOne A) :
    ∃ u ∈ mapIwahoriOne A, (∀ ⦃i j : m⦄, j < i → (u : Matrix m m K) i j = 0) ∧
      (diagGL t)⁻¹ * (u⁻¹ * x) * diagGL t ∈ mapIwahoriOne A := by
  rcases Subgroup.mem_map.mp hx with ⟨xA, hxA, rfl⟩
  obtain ⟨uA, huA_ut, hlA_lt⟩ :=
    exists_mem_upperUnitriangularGroup_isLowerTriangular_inv_mul (m := m)
      (IsLocalRing.ringJacobson_eq_maximalIdeal A).ge
      ((iwahoriOne_le_iwahori : iwahoriOne m A ≤ iwahori m A) hxA)
  have huA_tri := UpperUnitriangularGroup.mem_iff.mp huA_ut
  let f := GeneralLinearGroup.map (n := m) (algebraMap A K)
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
    rw [← map_inv, ← map_mul, GeneralLinearGroup.map_apply]
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
  (iwahoriOne m (valSubring K)).map (GeneralLinearGroup.map (algebraMap (valSubring K) K))

/-- The conjugated subgroup `diag(t)⁻ʲ I₁ diag(t)ʲ`. -/
private abbrev conjI1 (t : m → Kˣ) (j : ℤ) : Subgroup (GL m K) :=
  (I1 K m).comap (MulAut.conj (diagGL t) ^ j).toMonoidHom

/-- The shifted twisted conjugate `diag(t)⁻¹ * (k⁻¹ * g * σ(k))`. -/
private abbrev twistedConj (t : m → Kˣ) (g : GL m K) (σ : K →+* K) (k : I1 K m) : GL m K :=
  (diagGL t)⁻¹ * ((k : GL m K)⁻¹ * g * GeneralLinearGroup.map σ (k : GL m K))

private lemma conjI1_mem_iff {t : m → Kˣ} {j : ℤ} {x : GL m K} :
    x ∈ conjI1 t j ↔ diagGL (t ^ j) * x * (diagGL (t ^ j))⁻¹ ∈ I1 K m := by
  rw [conjI1, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, ← map_zpow, MulAut.conj_apply, map_zpow]

private lemma conjI1_add_one_iff {t : m → Kˣ} {j : ℤ} {x : GL m K} :
    x ∈ conjI1 t (j + 1) ↔ diagGL t * x * (diagGL t)⁻¹ ∈ conjI1 t j := by
  simp only [conjI1_mem_iff, _root_.zpow_add, zpow_one, MonoidHom.map_mul, _root_.mul_inv_rev,
    mul_assoc]

private lemma map_mem_conjI1_iff {t : m → Kˣ} {σ : K →+* K}
    (hσ : ∀ x : K, Valued.v (σ x) = Valued.v x) {j : ℤ} {x : GL m K} :
    GeneralLinearGroup.map σ x ∈ conjI1 t j ↔ x ∈ conjI1 t j := by
  simp only [conjI1_mem_iff, mem_map_iwahoriOne_iff_valued, diagGL_mul_mul_inv_apply,
    GeneralLinearGroup.map_apply]
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

private lemma widen_twistedConj {t : m → Kˣ}
    (htA : Monotone fun i : m ↦ (valSubring K).valuation (t i : K))
    {σ : K →+* K} (hσ : ∀ x : K, Valued.v (σ x) = Valued.v x)
    (hσ_surj : Function.Surjective (GeneralLinearGroup.map (n := m) σ))
    {g : GL m K} (b : ℕ) (k : I1 K m)
    (hk : ∀ j : ℤ, 0 ≤ j → j ≤ b → twistedConj t g σ k ∈ conjI1 t j) :
    ∃ k' : I1 K m, ∀ j : ℤ, 0 ≤ j → j ≤ b + 1 → twistedConj t g σ k' ∈ conjI1 t j := by
  obtain ⟨u, hu, hutri, hu_conj⟩ :=
    exists_upperTriangular_mul_conj_mem_mapIwahoriOne (valSubring K) htA (hk 0 le_rfl (by omega))
  obtain ⟨z, hz⟩ := hσ_surj (u⁻¹ * twistedConj t g σ k)
  have hu_mem (j : ℕ) : u ∈ conjI1 t j := by
    have htpow : Monotone fun i : m ↦ (valSubring K).valuation ((t ^ j) i : K) := fun _ _ hle ↦ by
      simpa [Pi.pow_apply, Units.val_pow_eq_pow_val, map_pow] using pow_le_pow_left' (htA hle) j
    have hres :=
      diagGL_mul_inv_mem_mapIwahoriOne_of_isUpperTriangular (valSubring K) htpow hu hutri
    rw [conjI1_mem_iff]
    simpa [zpow_natCast] using hres
  have hz_mem (j : ℕ) (hj : j ≤ b + 1) : z ∈ conjI1 t (j - 1) := by
    rw [← map_mem_conjI1_iff hσ, hz]
    cases j with
    | zero => simpa [conjI1_mem_iff] using hu_conj
    | succ j =>
      rw [Nat.cast_succ, add_sub_cancel_right]
      exact (conjI1 t j).mul_mem ((conjI1 t j).inv_mem (hu_mem j)) (hk j (by omega) (by omega))
  refine ⟨k * ⟨z, by simpa using hz_mem 1 (by omega)⟩⁻¹, fun j hj₀ hj ↦ ?_⟩
  lift j to ℕ using hj₀
  have hmul : twistedConj t g σ (k * ⟨z, by simpa using hz_mem 1 (by omega)⟩⁻¹) =
      ((diagGL t)⁻¹ * z * diagGL t) * u := by
    simp only [twistedConj, Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev,
      MonoidHom.map_mul, MonoidHom.map_inv, hz]
    group
  rw [hmul]
  have hz' : (diagGL t)⁻¹ * z * diagGL t ∈ conjI1 t j := by
    have h1 : (diagGL t)⁻¹ * z * diagGL t ∈ conjI1 t ((j - 1 : ℤ) + 1) ↔
        diagGL t * ((diagGL t)⁻¹ * z * diagGL t) * (diagGL t)⁻¹ ∈ conjI1 t (j - 1) :=
      conjI1_add_one_iff
    rw [sub_add_cancel] at h1
    exact h1.mpr (by simpa [mul_assoc] using hz_mem j (by omega))
  exact (conjI1 t j).mul_mem hz' (hu_mem j)

private lemma shift_twistedConj {t : m → Kˣ} {σ : K →+* K}
    (hσ : ∀ x : K, Valued.v (σ x) = Valued.v x) {g : GL m K} (a b : ℕ) (k : I1 K m)
    (hk : ∀ j : ℤ, -(a : ℤ) ≤ j → j ≤ b + 1 → twistedConj t g σ k ∈ conjI1 t j) :
    ∃ k' : I1 K m, ∀ j : ℤ, -((a + 1 : ℕ) : ℤ) ≤ j → j ≤ b →
      twistedConj t g σ k' ∈ conjI1 t j := by
  let y : I1 K m :=
    ⟨diagGL t * twistedConj t g σ k * (diagGL t)⁻¹, by
      simpa [conjI1_mem_iff] using hk 1 (by omega) (by omega)⟩
  refine ⟨k * y, fun j hj₀ hj ↦ ?_⟩
  have hy : (y : GL m K) ∈ conjI1 t j :=
    conjI1_add_one_iff.mp (hk (j + 1) (by omega) (by omega))
  have hmul : twistedConj t g σ (k * y) = GeneralLinearGroup.map σ (y : GL m K) := by
    simp [twistedConj, y, mul_assoc]
  rw [hmul]
  exact (map_mem_conjI1_iff hσ).mpr hy

private lemma exists_twistedConj_mem_conjI1 {t : m → Kˣ}
    (ht : Monotone fun i : m ↦ Valued.v (t i : K))
    {σ : K →+* K} (hσ : ∀ x : K, Valued.v (σ x) = Valued.v x)
    (hσ_surj : Function.Surjective σ)
    {g : GL m K} (hg : g ∈ DoubleCoset.doubleCoset (diagGL t) (I1 K m) (I1 K m))
    (a b : ℕ) :
    ∃ k : I1 K m, ∀ j : ℤ, -(a : ℤ) ≤ j → j ≤ b → twistedConj t g σ k ∈ conjI1 t j := by
  have htA : Monotone fun i : m ↦ (valSubring K).valuation (t i : K) := fun i j hij ↦
    (Valuation.isEquiv_valuation_valuationSubring Valued.v).le_iff_le.mp (ht hij)
  have h_start : ∃ k : I1 K m, twistedConj t g σ k ∈ conjI1 t 0 := by
    obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    exact ⟨⟨k, hk⟩, by
      simpa [twistedConj, mul_assoc] using
        (conjI1 t 0).mul_mem hk' ((map_mem_conjI1_iff hσ).mpr hk)⟩
  induction a generalizing b with
  | succ a ih => exact (ih (b + 1)).elim (shift_twistedConj hσ a b)
  | zero =>
    induction b with
    | succ b ih =>
      exact ih.elim (widen_twistedConj htA hσ (GeneralLinearGroup.map_surjective σ hσ_surj) b)
    | zero => exact h_start.imp fun k hk j hj₀ hj ↦ by rwa [show j = 0 by omega]

private lemma exists_one_lt_zpow_mul {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    [MulArchimedean G] {r : G} (hr : r ≠ 1) (u : G) : ∃ n : ℤ, 1 < r ^ n * u := by
  have hgt (s : G) (hs : 1 < s) : ∃ n : ℕ, 1 < s ^ (n + 1) * u := by
    obtain ⟨n, hn⟩ := MulArchimedean.arch u⁻¹ hs
    refine ⟨n, ?_⟩
    rw [← inv_lt_iff_one_lt_mul, pow_succ]
    exact hn.trans_lt (lt_mul_of_one_lt_right' _ hs)
  rcases lt_or_gt_of_ne hr with hr_lt | hr_gt
  · obtain ⟨n, hn⟩ := hgt r⁻¹ (one_lt_inv'.mpr hr_lt)
    exact ⟨-((n + 1 : ℕ) : ℤ), by rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow]⟩
  · obtain ⟨n, hn⟩ := hgt r hr_gt
    exact ⟨((n + 1 : ℕ) : ℤ), by rwa [zpow_natCast]⟩

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
  have hr_ne : r ≠ 1 := fun hr1 ↦
    hij (ht ((div_eq_one_iff_eq htj).mp (congrArg Units.val hr1)))
  obtain ⟨n, hn⟩ := exists_one_lt_zpow_mul hr_ne u
  obtain ⟨h1, -, -⟩ := mem_map_iwahoriOne_iff_valued.mp (conjI1_mem_iff.mp (hx n))
  have h := h1 i j
  rw [diagGL_mul_mul_inv_apply] at h
  have hbound : ((r ^ n * u : Γ₀ˣ) : Γ₀) ≤ 1 := by
    simpa [r, u, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, div_eq_mul_inv,
      mul_zpow, mul_right_comm] using h
  exact not_lt_of_ge hbound (by exact_mod_cast hn)

/-- **Twisted conjugacy in `I₁ · diag(t) · I₁`.** Let `σ : K →+* K` be a surjective ring
endomorphism preserving the valuation, and let `t : m → Kˣ` have strictly increasing valuations
`v (t i) < v (t j)` for `i < j`. When the valuation subring of `K` is compact and the value group
is rank one, every `g` in the double coset `I₁ · diag(t) · I₁` satisfies
`k⁻¹ * g * σ(k) = diag(t * d)` for some `k ∈ I₁` and diagonal `d` with `diag(d) ∈ I₁`. -/
theorem exists_inv_mul_mul_map_eq_diagGL_mul [MulArchimedean Γ₀ˣ]
    [CompactSpace (Valued.v (R := K)).valuationSubring]
    {t : m → Kˣ} (ht : StrictMono fun i : m ↦ Valued.v (t i : K))
    (σ : K →+* K) (hσ : ∀ x : K, Valued.v (σ x) = Valued.v x) (hσ_surj : Function.Surjective σ)
    {g : GL m K}
    (hg : g ∈ DoubleCoset.doubleCoset (diagGL t)
      ((iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (GeneralLinearGroup.map (algebraMap _ K)))
      ((iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (GeneralLinearGroup.map (algebraMap _ K)))) :
    ∃ k ∈ (iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (GeneralLinearGroup.map (algebraMap _ K)),
      ∃ d : m → Kˣ,
        diagGL d ∈ (iwahoriOne m (Valued.v (R := K)).valuationSubring).map
          (GeneralLinearGroup.map (algebraMap _ K)) ∧
        k⁻¹ * g * GeneralLinearGroup.map σ k = diagGL (t * d) := by
  have : CompactSpace (I1 K m) := isCompact_iff_compactSpace.mp isCompact_map_iwahoriOne
  choose f hf using exists_twistedConj_mem_conjI1 ht.monotone hσ hσ_surj hg
  obtain ⟨k, hk⟩ : ∃ k : I1 K m, ClusterPt k (atTop.map fun n ↦ f n n) :=
    exists_clusterPt_of_compactSpace _
  have hmap : Continuous (GeneralLinearGroup.map (n := m) σ) :=
    Continuous.generalLinearGroup_map (Valued.continuous_of_valuation_eq hσ)
  have h_all (j : ℤ) : twistedConj t g σ k ∈ conjI1 t j := by
    have h_cont : Continuous fun x : I1 K m ↦
        diagGL (t ^ j) * twistedConj t g σ x * (diagGL (t ^ j))⁻¹ := by
      refine ((continuous_const.mul ?_).mul continuous_const)
      exact continuous_const.mul ((continuous_subtypeVal.inv.mul continuous_const).mul
        (hmap.comp continuous_subtypeVal))
    have h_closed : IsClosed (twistedConj t g σ ⁻¹' conjI1 t j) := by
      have hpre : twistedConj t g σ ⁻¹' conjI1 t j =
          (fun x : I1 K m ↦ diagGL (t ^ j) * twistedConj t g σ x * (diagGL (t ^ j))⁻¹) ⁻¹'
            (I1 K m : Set (GL m K)) := by
        ext x; exact conjI1_mem_iff
      rw [hpre]
      exact ((I1 K m).isClosed_of_isOpen isOpen_map_iwahoriOne).preimage h_cont
    refine h_closed.mem_of_mapClusterPt hk ?_
    filter_upwards [mem_atTop j.natAbs] with n hn using hf n n j (by omega) (by omega)
  have hX_mem : twistedConj t g σ k ∈ I1 K m := by simpa using h_all 0
  obtain ⟨-, -, hX_diag⟩ := mem_map_iwahoriOne_iff_valued.mp hX_mem
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
    exact (Valuation.isEquiv_valuation_valuationSubring Valued.v).lt_one_iff_lt_one.mp
      (by simpa [d] using hX_diag i)
  · rw [map_mul, hX, twistedConj, mul_inv_cancel_left]

end ValuedField

end TauCeti
