/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Cartan.DiscreteValuationRing
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CongruenceLevel
import TauCeti.GroupTheory.Coset.Basic
import TauCeti.GroupTheory.DoubleCoset.Identity
import TauCeti.GroupTheory.DoubleCoset.Inv
import TauCeti.GroupTheory.DoubleCoset.Map
import TauCeti.GroupTheory.DoubleCoset.Orbits
import TauCeti.GroupTheory.QuotientGroup.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Bruhat
import TauCeti.RingTheory.DiscreteValuationRing.FractionRing

/-!
# The Cartan decomposition of `PGL₂` over a discretely valued field

Let `R` be a discrete valuation ring with fraction field `K`, `ϖ` a uniformizer of `R` and `π` its
image in `Kˣ`. Write `Γ ≤ PGL₂(K)` for the image of `GL₂(R)`. Passing the Cartan decomposition of
`GL₂(K)` (`TauCeti.existsUnique_monotone_mem_doubleCoset_diagGL_zpow`) to the quotient by the
scalars gives

```text
PGL₂(K) = ⊔_{k ≥ 0} Γ · diag(1, πᵏ) · Γ,
```

a disjoint union, whose `k = 0` term is `Γ` itself. So every element of `PGL₂(K)` outside `Γ` lies
in the double coset of `diag(1, πᵏ)` for exactly one `k ≥ 1`. For `K = ℚ_p` these are the
double cosets `PGL₂(ℤ_p) diag(1, pᵏ) PGL₂(ℤ_p)`.

When the residue field of `R` is finite with `q` elements, the double coset of `diag(1, πᵏ)` with
`k ≥ 1` is a union of `qᵏ⁻¹ (q + 1)` left cosets `gΓ`, and of as many right cosets `Γg`. The left
cosets are the orbit of `diag(1, πᵏ) Γ` under `Γ`, whose stabilizer is the image of the congruence
level `K₀(𝔭ᵏ)` (`TauCeti.GL2K0`), of index `qᵏ⁻¹ (q + 1)` in `GL₂(R)`. Inversion exchanges left and
right cosets and preserves each of these double cosets, since `diag(1, πᵏ)⁻¹` is conjugate under
the Weyl element of `GL₂(R)` to a scalar multiple of `diag(1, πᵏ)`.

## Main results

* `TauCeti.existsUnique_mem_doubleCoset_mk_diagGL_pow`: every element of `PGL₂(K)` lies in the
  double coset of `diag(1, πᵏ)` for exactly one `k : ℕ`; its halves are
  `TauCeti.exists_mem_doubleCoset_mk_diagGL_pow` and `TauCeti.eq_of_mem_doubleCoset_mk_diagGL_pow`.
* `TauCeti.doubleCoset_mk_diagGL_pow_zero`: the double coset for `k = 0` is `Γ`.
* `TauCeti.comap_conj_smul_range_eq_GL2K0`: the stabilizer in `GL₂(R)` of the coset
  `diag(1, πᵏ) Γ` is the congruence level `K₀(𝔭ᵏ)`.
* `TauCeti.natCard_image_mk_doubleCoset_mk_diagGL_pow`: for `k ≥ 1` the double coset contains
  `qᵏ⁻¹ (q + 1)` left cosets of `Γ`.
* `TauCeti.natCard_image_mk_rightRel_doubleCoset_mk_diagGL_pow`: it contains as many right cosets.

## References

* J.-P. Serre, *Trees*, Springer (1980), Chapter II, §1.
* I. G. Macdonald, *Spherical Functions on a Group of p-adic Type*, Ramanujan Institute (1971),
  Chapter II, §2.6, and Chapter III, §3.2.
-/

public section

open Matrix DoubleCoset MulAction IsLocalRing
open scoped MatrixGroups Pointwise

namespace TauCeti

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R} {π : Kˣ}

/-- An element of `GL₂(K)` whose class lies in the image of `GL₂(R)` in `PGL₂(K)`, and whose
determinant is the image of a unit of `R`, lies in the image of `GL₂(R)` in `GL₂(K)`. -/
private theorem mem_range_map_of_mk_mem {M : GL (Fin 2) K}
    (hM : ProjGenLinGroup.mk M ∈
      (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range)
    {w : Rˣ} (hw : (GeneralLinearGroup.det M : K) = algebraMap R K w) :
    M ∈ (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  obtain ⟨y, hy⟩ := hM
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hy
  have hdet := congrArg (fun g : GL (Fin 2) K ↦ (GeneralLinearGroup.det g : K)) hu
  simp only [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_mul,
    Units.val_pow_eq_pow_val, hw, GeneralLinearGroup.map_det, Units.coe_map,
    MonoidHom.coe_ofClass] at hdet
  obtain ⟨v, hv⟩ := IsDiscreteValuationRing.exists_algebraMap_eq_of_pow_eq_algebraMap two_ne_zero
    (x := (u : K)) (w := w * (GeneralLinearGroup.det y)⁻¹)
    (by
      simp only [Units.val_mul, map_mul, map_units_inv, ← hdet, mul_right_comm _ (_ ^ 2),
        mul_inv_cancel₀ ((GeneralLinearGroup.det y).isUnit.map (algebraMap R K)).ne_zero, one_mul])
  refine ⟨y * GeneralLinearGroup.scalar (Fin 2) v, ?_⟩
  rw [map_mul, GeneralLinearGroup.map_scalar, ← hu]
  congr 2
  exact Units.ext hv

/-- **The stabilizer of a Cartan coset.** In `PGL₂(K)`, conjugating the class of `x ∈ GL₂(R)` by
`diag(1, πᵏ)⁻¹` stays in the image `Γ` of `GL₂(R)` exactly when `x` lies in the congruence level
`K₀(𝔭ᵏ)`: the preimage of `Γ ∩ diag(1, πᵏ) Γ diag(1, πᵏ)⁻¹` in `GL₂(R)` is `K₀(𝔭ᵏ)`. -/
theorem comap_conj_smul_range_eq_GL2K0 (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π)
    (k : ℕ) :
    (MulAut.conj (ProjGenLinGroup.mk (diagGL ![1, π ^ k])) •
        (ProjGenLinGroup.mk.comp
          (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range).comap
      (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))) =
      GL2K0 (maximalIdeal R ^ k) := by
  ext x
  have hπk : ((π ^ k : Kˣ) : K) = algebraMap R K (ϖ ^ k) := by
    rw [Units.val_pow_eq_pow_val, map_pow, hπ]
  have hmax : maximalIdeal R ^ k = Ideal.span {ϖ ^ k} := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow]
  -- the entries of `diag(1, πᵏ)⁻¹ x diag(1, πᵏ)`
  have hentry (i j : Fin 2) : ((diagGL ![1, π ^ k])⁻¹ *
      GeneralLinearGroup.map (algebraMap R K) x * diagGL ![1, π ^ k] : GL (Fin 2) K) i j =
        ((![1, π ^ k] i)⁻¹ : Kˣ) * algebraMap R K (x i j) * (![1, π ^ k] j : Kˣ) := by
    rw [← map_inv]
    simp only [Units.val_mul, diagGL_coe, mul_diagonal, diagonal_mul, GeneralLinearGroup.map_apply,
      Pi.inv_apply]
  rw [Subgroup.mem_comap, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  simp only [MulAut.smul_def, MulAut.conj_apply, inv_inv, MonoidHom.comp_apply,
    ← map_inv ProjGenLinGroup.mk, ← map_mul ProjGenLinGroup.mk, GL2K0.mem_iff, hmax,
    Ideal.mem_span_singleton]
  constructor
  · intro hmem
    obtain ⟨y, hy⟩ := mem_range_map_of_mk_mem hmem (w := GeneralLinearGroup.det x)
      (by simp [GeneralLinearGroup.map_det, mul_comm])
    have h10 := hentry 1 0
    rw [← hy, GeneralLinearGroup.map_apply] at h10
    refine ⟨y 1 0, IsFractionRing.injective R K ?_⟩
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Units.val_one, mul_one,
      Units.val_inv_eq_inv_val, hπk] at h10
    rw [map_mul, h10, ← mul_assoc, mul_inv_cancel₀ ((map_ne_zero_iff _
      (IsFractionRing.injective R K)).mpr (pow_ne_zero _ hϖ.ne_zero)), one_mul]
  · rintro ⟨c, hc⟩
    have hY : IsUnit (!![x 0 0, ϖ ^ k * x 0 1; c, x 1 1] : Matrix (Fin 2) (Fin 2) R).det := by
      have := (GeneralLinearGroup.det x).isUnit
      rw [GeneralLinearGroup.val_det_apply, det_fin_two, hc] at this
      rw [det_fin_two_of]
      convert this using 1
      ring
    have hϖ0 : algebraMap R K ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hϖ.ne_zero
    refine ⟨nonsingInvUnit _ hY, congrArg ProjGenLinGroup.mk (Units.ext ?_)⟩
    ext i j
    rw [hentry]
    fin_cases i <;> fin_cases j <;>
      simp [hπk, hc, GeneralLinearGroup.map_apply, nonsingInvUnit, ← mul_assoc] <;>
      field_simp

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- `diag(1, πᵏ)`, as a diagonal matrix of powers of `π` with exponents `(0, k)`. -/
private theorem diagGL_pow_eq_diagGL_zpow (k : ℕ) :
    diagGL ![1, π ^ k] = diagGL fun i ↦ π ^ (![0, (k : ℤ)] i) := by
  congr 1
  ext i : 1
  fin_cases i <;> simp

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- A diagonal matrix `diag(π^c, π^(c + k))` of powers of `π` is the scalar `π^c` times
`diag(1, πᵏ)`. -/
private theorem diagGL_zpow_eq_scalar_mul_diagGL_pow {a : Fin 2 → ℤ} {c : ℤ} {k : ℕ}
    (h0 : a 0 = c) (h1 : a 1 = c + k) :
    (diagGL fun i ↦ π ^ a i) = GeneralLinearGroup.scalar (Fin 2) (π ^ c) * diagGL ![1, π ^ k] := by
  rw [← diagGL_const_mul]
  congr 1
  ext i : 1
  fin_cases i <;> simp [h0, h1, ← zpow_natCast, ← _root_.zpow_add]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The double coset of `diag(1, π⁰) = 1` is `Γ` itself. -/
theorem doubleCoset_mk_diagGL_pow_zero :
    doubleCoset (ProjGenLinGroup.mk (diagGL ![1, π ^ 0]))
        (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range
        (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range =
      (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range := by
  have h1 : diagGL ![1, π ^ 0] = 1 := by
    rw [← map_one diagGL]
    congr 1
    ext i : 1
    fin_cases i <;> simp
  rw [h1, map_one, doubleCoset_one_self]

/-- **Existence in the Cartan decomposition of `PGL₂(K)`.** Every element of `PGL₂(K)` lies in the
double coset `Γ diag(1, πᵏ) Γ` for some `k : ℕ`, where `Γ` is the image of `GL₂(R)`. -/
theorem exists_mem_doubleCoset_mk_diagGL_pow (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π)
    (g : PGL(2, K)) :
    ∃ k : ℕ, g ∈ doubleCoset (ProjGenLinGroup.mk (diagGL ![1, π ^ k]))
      (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range
      (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range := by
  set f := ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))
  have himage : (ProjGenLinGroup.mk : GL (Fin 2) K →* PGL(2, K)) ''
      ((GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range : Set (GL (Fin 2) K)) =
        (f.range : Set PGL(2, K)) := by
    rw [← Subgroup.coe_map, MonoidHom.map_range]
  induction g using ProjGenLinGroup.induction_on with | mk M => ?_
  -- push the Cartan decomposition of `M` in `GL₂(K)` down to `PGL₂(K)`
  obtain ⟨a, ha, hM⟩ := exists_monotone_mem_doubleCoset_diagGL_zpow hϖ hπ M
  have ha01 : a 0 ≤ a 1 := ha (Fin.zero_le 1)
  refine ⟨(a 1 - a 0).toNat, ?_⟩
  have hmk : ProjGenLinGroup.mk (diagGL fun i ↦ π ^ a i) =
      ProjGenLinGroup.mk (diagGL ![1, π ^ (a 1 - a 0).toNat]) := by
    have hD : (diagGL fun i ↦ π ^ a i) = GeneralLinearGroup.scalar (Fin 2) (π ^ a 0) *
        diagGL ![1, π ^ (a 1 - a 0).toNat] :=
      diagGL_zpow_eq_scalar_mul_diagGL_pow rfl (by omega)
    rw [hD, map_mul, ProjGenLinGroup.mk_scalar, one_mul]
  have h := Set.mem_image_of_mem ProjGenLinGroup.mk hM
  rwa [DoubleCoset.image_doubleCoset, himage, hmk] at h

/-- **Uniqueness in the Cartan decomposition of `PGL₂(K)`.** The double cosets `Γ diag(1, πᵏ) Γ`
of `PGL₂(K)` for distinct `k : ℕ` are disjoint, where `Γ` is the image of `GL₂(R)`. -/
theorem eq_of_mem_doubleCoset_mk_diagGL_pow (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π)
    {g : PGL(2, K)} {k l : ℕ}
    (hk : g ∈ doubleCoset (ProjGenLinGroup.mk (diagGL ![1, π ^ k]))
        (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range
        (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range)
    (hl : g ∈ doubleCoset (ProjGenLinGroup.mk (diagGL ![1, π ^ l]))
        (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range
        (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range) :
    k = l := by
  set f := ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))
  -- two such double cosets meet only if their exponents agree, by uniqueness in `GL₂(K)`
  have hkl : ProjGenLinGroup.mk (diagGL ![1, π ^ k]) ∈
      doubleCoset (ProjGenLinGroup.mk (diagGL ![1, π ^ l])) f.range f.range := by
    rw [← doubleCoset_eq_of_mem hl, doubleCoset_eq_of_mem hk]
    exact mem_doubleCoset_self _ _ _
  obtain ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, hxy⟩ := mem_doubleCoset.mp hkl
  simp only [f, MonoidHom.comp_apply, ← map_mul] at hxy
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hxy.symm
  obtain ⟨j, v, hv⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (K := K) hϖ u.ne_zero
  have huv : u = Units.map (algebraMap R K : R →* K) v * π ^ j := Units.ext <| by
    rw [hv, hπ, Units.smul_def, Algebra.smul_def, Units.val_mul, Units.coe_map,
      MonoidHom.coe_ofClass, Units.val_zpow_eq_zpow_val]
  have hmem : (diagGL fun i ↦ π ^ (![0, (k : ℤ)] i)) ∈
      doubleCoset (diagGL fun i ↦ π ^ (![j, (l : ℤ) + j] i))
        (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range
        (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
    refine mem_doubleCoset.mpr
      ⟨_, ⟨x, rfl⟩, _, ⟨y * GeneralLinearGroup.scalar (Fin 2) v, rfl⟩, ?_⟩
    have hD : (diagGL fun i ↦ π ^ (![j, (l : ℤ) + j] i)) =
        GeneralLinearGroup.scalar (Fin 2) (π ^ j) * diagGL ![1, π ^ l] :=
      diagGL_zpow_eq_scalar_mul_diagGL_pow (by simp) (by simp [add_comm])
    rw [← diagGL_pow_eq_diagGL_zpow, ← hu, huv, hD]
    simp only [map_mul, GeneralLinearGroup.map_scalar, mul_assoc]
    congr 1
    rw [GeneralLinearGroup.scalar_commute (π ^ j)]
    simp only [mul_assoc]
  have hmono (c d : ℤ) (hcd : c ≤ d) : Monotone ![c, d] := fun i i' hii' ↦ by
    fin_cases i <;> fin_cases i' <;> simp_all
  have hab := eq_of_monotone_of_mem_doubleCoset_diagGL_zpow hϖ hπ
    (hmono 0 k (by positivity)) (hmono j (l + j) (by omega)) (mem_doubleCoset_self _ _ _) hmem
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  omega

/-- **The Cartan decomposition of `PGL₂(K)`.** Every element of `PGL₂(K)` lies in the double coset
`Γ diag(1, πᵏ) Γ` for exactly one `k : ℕ`, where `Γ` is the image of `GL₂(R)` and `π` the image of
a uniformizer of the discrete valuation ring `R` in its fraction field `K`. By
`TauCeti.doubleCoset_mk_diagGL_pow_zero`, `k = 0` exactly for the elements of `Γ`. -/
theorem existsUnique_mem_doubleCoset_mk_diagGL_pow (hϖ : Irreducible ϖ)
    (hπ : algebraMap R K ϖ = π) (g : PGL(2, K)) :
    ∃! k : ℕ, g ∈ doubleCoset (ProjGenLinGroup.mk (diagGL ![1, π ^ k]))
      (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range
      (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range :=
  let ⟨k, hk⟩ := exists_mem_doubleCoset_mk_diagGL_pow hϖ hπ g
  ⟨k, hk, fun _ hl ↦ (eq_of_mem_doubleCoset_mk_diagGL_pow hϖ hπ hk hl).symm⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- `diag(1, πᵏ)⁻¹` lies in the double coset of `diag(1, πᵏ)`: up to a scalar, it is the conjugate
of `diag(1, πᵏ)` by the Weyl element. -/
private theorem inv_mem_doubleCoset_mk_diagGL_pow (k : ℕ) :
    (ProjGenLinGroup.mk (diagGL ![1, π ^ k]))⁻¹ ∈
      doubleCoset (ProjGenLinGroup.mk (diagGL ![1, π ^ k]))
        (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range
        (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range := by
  refine mem_doubleCoset.mpr ⟨_, ⟨GL2WeylElement R, rfl⟩, _, ⟨GL2WeylElement R, rfl⟩, ?_⟩
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, ← map_inv, ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨π ^ k, Units.ext ?_⟩
  rw [← map_inv]
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, diagGL_coe,
    GeneralLinearGroup.val_map_apply, coe_gl2WeylElement]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, -Units.val_pow_eq_pow_val]

/-- **The coset counts of the Cartan double cosets of `PGL₂`, for left cosets.** If the residue
field of `R` has `q` elements and `k ≥ 1`, the double coset `Γ diag(1, πᵏ) Γ` in `PGL₂(K)`, where
`Γ` is the image of `GL₂(R)`, is the union of `qᵏ⁻¹ (q + 1)` left cosets `gΓ`. -/
theorem natCard_image_mk_doubleCoset_mk_diagGL_pow [Finite (ResidueField R)]
    (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) {k : ℕ} (hk : k ≠ 0) :
    Nat.card ((QuotientGroup.mk :
        PGL(2, K) → PGL(2, K) ⧸
          (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range) ''
        doubleCoset (ProjGenLinGroup.mk (diagGL ![1, π ^ k]))
          (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range
          (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range) =
      Nat.card (ResidueField R) ^ (k - 1) * (Nat.card (ResidueField R) + 1) := by
  set f := ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))
  set C := MulAut.conj (ProjGenLinGroup.mk (diagGL ![1, π ^ k])) • f.range
  -- the left cosets form the `Γ`-orbit of `diag(1, πᵏ) Γ`, whose stabilizer is `Γ ∩ C`
  rw [← preimage_orbit_eq_doubleCoset, Set.image_preimage_eq _ QuotientGroup.mk_surjective,
    Subgroup.card_orbit_quotientGroup_mk_eq_relIndex_inf]
  calc (f.range ⊓ C).relIndex f.range
      = ((C.comap f).map f).relIndex ((⊤ : Subgroup (GL (Fin 2) R)).map f) := by
        rw [Subgroup.map_comap_eq, ← f.range_eq_map]
    _ = (C.comap f).index := by
        rw [Subgroup.relIndex_map_map, sup_eq_left.mpr (Subgroup.ker_le_comap f C), top_sup_eq,
          Subgroup.relIndex_top_right]
    _ = _ := by
        rw [comap_conj_smul_range_eq_GL2K0 hϖ hπ, GL2K0.index_maximalIdeal_pow hk]

/-- **The coset counts of the Cartan double cosets of `PGL₂`, for right cosets.** If the residue
field of `R` has `q` elements and `k ≥ 1`, the double coset `Γ diag(1, πᵏ) Γ` in `PGL₂(K)`, where
`Γ` is the image of `GL₂(R)`, is the union of `qᵏ⁻¹ (q + 1)` right cosets `Γg`. -/
theorem natCard_image_mk_rightRel_doubleCoset_mk_diagGL_pow [Finite (ResidueField R)]
    (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) {k : ℕ} (hk : k ≠ 0) :
    Nat.card (Quotient.mk (QuotientGroup.rightRel
        (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range) ''
        doubleCoset (ProjGenLinGroup.mk (diagGL ![1, π ^ k]))
          (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range
          (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range) =
      Nat.card (ResidueField R) ^ (k - 1) * (Nat.card (ResidueField R) + 1) := by
  set Γ := (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))).range
  set S := doubleCoset (ProjGenLinGroup.mk (diagGL ![1, π ^ k])) (Γ : Set PGL(2, K)) Γ
  -- inversion exchanges right and left cosets, and preserves `S`
  have hS : S⁻¹ = S := by
    rw [doubleCoset_inv]
    exact doubleCoset_eq_of_mem (inv_mem_doubleCoset_mk_diagGL_pow k)
  have himage : QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ ''
      (Quotient.mk (QuotientGroup.rightRel Γ) '' S) = (QuotientGroup.mk : _ → _ ⧸ Γ) '' S := by
    rw [Set.image_image]
    conv_rhs => rw [← hS, ← Set.image_inv_eq_inv, Set.image_image]
    exact Set.image_congr fun x _ ↦ QuotientGroup.quotientRightRelEquivQuotientLeftRel_mk x
  rw [← Nat.card_image_of_injective (Equiv.injective _), himage,
    natCard_image_mk_doubleCoset_mk_diagGL_pow hϖ hπ hk]

end TauCeti
