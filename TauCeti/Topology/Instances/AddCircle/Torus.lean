/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Topology.Path
public import TauCeti.Topology.Algebra.Module.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import TauCeti.Algebra.AddCircle
import TauCeti.GroupTheory.QuotientGroup.KerEquiv
import TauCeti.LinearAlgebra.FreeModule.Int
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.LinearAlgebra.Matrix.MulVec

/-!
# Integer matrices acting on tori, and straight loops

A torus is a product `∀ i, AddCircle (p i)` of additive circles. An integer matrix
`A : Matrix κ ι ℤ` acts by the continuous additive map `Matrix.smulVecHom A (AddCircle p)` from
`ι → AddCircle p` to `κ → AddCircle p`, sending `x` to `k ↦ ∑ i, A k i • x i`. For `p = 1` these
are Mathlib's tori `UnitAddTorus ι = ℝⁱ / ℤⁱ`, and this is the map induced by the linear map
`A : ℝⁱ → ℝᵏ`.

For `n : ι → ℤ`, the straight loop `TauCeti.torusLoop p n` is the image in the torus of the
segment from `0` to `(n i • p i)ᵢ`: it winds `n i` times around the `i`-th circle. Integer
matrices act on these loops through `Matrix.mulVec` (`Matrix.smulVecHom_comp_torusLoop`). They are
the representatives used to compute the fundamental group and first homology of a torus
naturally in the matrix.

The covering map `(ι → K) → (ι → AddCircle p)`, for a period `p` in a topological ring `K`,
intertwines `Matrix.smulVecHom A` with multiplication of vectors by `A`
(`Matrix.smulVecHom_coe_pi`), so `[t]` lies in the kernel of `Matrix.smulVecHom A` exactly when
`A t` has its coordinates in `pℤ` (`Matrix.coe_mem_ker_smulVecHom_iff`). The kernel is stated for
the coercion of `Matrix.smulVecHom A` to an additive monoid homomorphism, the simp-normal form of
`(Matrix.smulVecHom A).toAddMonoidHom`. Over a topological field `K` of characteristic zero, such
as `ℝ`, and for `p ≠ 0`, the kernel of a square integer matrix `A` acting on the torus
`ι → AddCircle p` has `Nat.card` equal to `|det A|` (`Matrix.natCard_ker_smulVecHom`). When
`det A ≠ 0` the kernel is `A⁻¹ (p ℤⁱ) / p ℤⁱ`, a finite group with `|det A|` elements isomorphic
to `ℤⁱ / A ℤⁱ` (`Matrix.quotientRangeEquivKerSmulVecHom`). When `det A = 0` it contains the image
of a line `K` and is infinite, `Nat.card` then taking the junk value `0`; for every `p` the kernel
is finite exactly when `det A ≠ 0`
(`Matrix.finite_ker_smulVecHom_iff`). For a `1 × 1` matrix `n` the count is
`AddCircle.natCard_torsionBy`, the number of points of the `n`-torsion of the circle. Applied to
`1 - A`, it counts the fixed points of the toral automorphism induced by `A`
(`AddCircle.nat_card_fixedPoints_generalLinearGroup_smul`).
-/

public section

noncomputable section

open unitInterval

namespace TauCeti

variable {ι : Type*}

/-- The straight loop in the torus `∀ i, AddCircle (p i)` winding `n i` times around the `i`-th
circle: the image of the segment from `0` to `(n i • p i)ᵢ` in `ι → ℝ`. -/
def torusLoop (p : ι → ℝ) (n : ι → ℤ) : Path (0 : ∀ i, AddCircle (p i)) 0 where
  toFun t i := ((t * (n i • p i) : ℝ) : AddCircle (p i))
  continuous_toFun := by fun_prop
  source' := by ext i; simp
  target' := by ext i; simp [AddCircle.coe_period]

@[simp]
theorem torusLoop_apply (p : ι → ℝ) (n : ι → ℤ) (t : I) (i : ι) :
    torusLoop p n t i = ((t * (n i • p i) : ℝ) : AddCircle (p i)) :=
  (rfl)

end TauCeti

namespace Matrix

section Ring

variable {ι κ K : Type*} [Fintype ι] (A : Matrix κ ι ℤ) [Ring K] [TopologicalSpace K]
  [IsTopologicalAddGroup K] (p : K)

/-- The covering map `(ι → K) → (ι → AddCircle p)` intertwines the map of tori induced by an integer
matrix `A` with multiplication of vectors by `A`. -/
theorem smulVecHom_coe_pi (t : ι → K) :
    A.smulVecHom (AddCircle p) (fun i ↦ (t i : AddCircle p)) =
      fun k ↦ ((A.map ((↑) : ℤ → K) *ᵥ t) k : AddCircle p) := by
  ext k
  simp only [smulVecHom_apply, mulVec, dotProduct, map_apply, ← zsmul_eq_mul,
    QuotientAddGroup.mk_sum, AddCircle.coe_zsmul]

/-- **Kernel of an integer matrix through the covering map.** A point `[t]` of the torus lies in the
kernel of the map induced by an integer matrix `A` exactly when every coordinate of `A t` is an
integer multiple of `p`. -/
theorem coe_mem_ker_smulVecHom_iff (t : ι → K) :
    (fun i ↦ (t i : AddCircle p)) ∈
        (A.smulVecHom (AddCircle p) : (ι → AddCircle p) →+ (κ → AddCircle p)).ker ↔
      ∃ v : κ → ℤ, A.map ((↑) : ℤ → K) *ᵥ t = fun k ↦ (v k : K) * p := by
  rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass, smulVecHom_coe_pi,
    AddCircle.pi_coe_eq_zero_iff]
  simp only [zsmul_eq_mul, eq_comm]

end Ring

variable {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℤ) (p : ℝ)

/-- An integer matrix sends the straight loop of `n` to the straight loop of `A *ᵥ n`. -/
theorem smulVecHom_comp_torusLoop (n : ι → ℤ) :
    (A.smulVecHom (AddCircle p) : C(ι → AddCircle p, κ → AddCircle p)).comp
        (TauCeti.torusLoop (fun _ ↦ p) n).toContinuousMap =
      (TauCeti.torusLoop (fun _ ↦ p) (A *ᵥ n)).toContinuousMap := by
  ext t k
  -- The straight loop of `n` at time `t` is the image of the real vector `(t p) n`.
  have hn : TauCeti.torusLoop (fun _ ↦ p) n t =
      fun i ↦ (((t * p : ℝ) • (n · : ι → ℝ)) i : AddCircle p) :=
    funext fun i ↦ by
      rw [TauCeti.torusLoop_apply, Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, mul_comm (n i : ℝ),
        mul_assoc]
  simp only [ContinuousMap.comp_apply, Path.coe_toContinuousMap, ContinuousMap.coe_ofClass, hn,
    smulVecHom_coe_pi, mulVec_smul, map_intCast_mulVec]
  simp only [TauCeti.torusLoop_apply, Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
  congr 1
  ring

end Matrix

/-! ### The kernel of a square integer matrix -/

namespace Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] (p : K)

omit [Fintype ι] [DecidableEq ι] in
private theorem smul_intCast_eq (v : ι → ℤ) : p • (v · : ι → K) = fun i ↦ (v i : K) * p :=
  funext fun _ ↦ mul_comm _ _

/-- The map `n ↦ [A⁻¹ (p n)]` from `ℤⁱ` to the torus `ι → AddCircle p`, for an integer matrix `A`.
-/
private def invMulVecHom (A : Matrix ι ι ℤ) : (ι → ℤ) →+ (ι → AddCircle p) :=
  ((QuotientAddGroup.mk' (AddSubgroup.zmultiples p)).compLeft ι).comp <|
    ((A.map ((↑) : ℤ → K))⁻¹.mulVecLin ∘ₗ (p • LinearMap.id)).toAddMonoidHom.comp
      ((Int.castAddHom K).compLeft ι)

private theorem invMulVecHom_apply (A : Matrix ι ι ℤ) (n : ι → ℤ) :
    invMulVecHom p A n =
      fun i ↦ (((A.map ((↑) : ℤ → K))⁻¹ *ᵥ (p • (n · : ι → K))) i : AddCircle p) := by
  have hcast : (Int.castAddHom K).compLeft ι n = (n · : ι → K) := funext fun _ ↦ by simp
  funext i
  simp [invMulVecHom, hcast, mulVec_smul]

variable [CharZero K]

/-- For an integer matrix `A` with nonzero determinant and `p ≠ 0`, the point `[A⁻¹ (p n)]` of the
torus vanishes exactly when the integer vector `n` lies in the image of `A`. -/
private theorem coe_inv_mulVec_eq_zero_iff {A : Matrix ι ι ℤ}
    (hA : IsUnit (A.map ((↑) : ℤ → K)).det) (hp : p ≠ 0) (n : ι → ℤ) :
    (fun i ↦ (((A.map ((↑) : ℤ → K))⁻¹ *ᵥ (p • (n · : ι → K))) i : AddCircle p)) = 0 ↔
      ∃ m, A *ᵥ m = n := by
  set B := A.map ((↑) : ℤ → K)
  have hcast (m : ι → ℤ) : B *ᵥ (m · : ι → K) = fun x ↦ ((A *ᵥ m) x : K) := map_intCast_mulVec A m
  rw [AddCircle.pi_coe_eq_zero_iff]
  simp only [zsmul_eq_mul, ← smul_intCast_eq, eq_comm (b := B⁻¹ *ᵥ _)]
  constructor
  · rintro ⟨m, hm⟩
    have hv := congrArg (B *ᵥ ·) hm
    simp only [mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec, mulVec_smul, hcast] at hv
    exact ⟨m, funext fun k ↦ Int.cast_injective (α := K)
      (congrFun (smul_right_injective _ hp hv) k).symm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, by rw [← hcast, ← mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec]⟩

variable [TopologicalSpace K] [IsTopologicalAddGroup K]

omit [CharZero K] in
/-- For `det A ≠ 0`, the map `n ↦ [A⁻¹ (p n)]` takes values in the kernel of the map of the torus
induced by `A`. -/
private theorem invMulVecHom_mem_ker {A : Matrix ι ι ℤ} (hA : IsUnit (A.map ((↑) : ℤ → K)).det)
    (n : ι → ℤ) :
    invMulVecHom p A n ∈
      (A.smulVecHom (AddCircle p) : (ι → AddCircle p) →+ (ι → AddCircle p)).ker := by
  rw [invMulVecHom_apply, coe_mem_ker_smulVecHom_iff]
  exact ⟨n, by rw [mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec, smul_intCast_eq]⟩

omit [CharZero K] in
/-- For `det A ≠ 0`, every point of the kernel of the map of the torus induced by `A` is of the form
`[A⁻¹ (p n)]`: if `[t]` lies in the kernel, then `A t = p n` for an integer vector `n`. -/
private theorem exists_invMulVecHom_eq {A : Matrix ι ι ℤ} (hA : IsUnit (A.map ((↑) : ℤ → K)).det)
    {x : ι → AddCircle p}
    (hx : x ∈ (A.smulVecHom (AddCircle p) : (ι → AddCircle p) →+ (ι → AddCircle p)).ker) :
    ∃ n, invMulVecHom p A n = x := by
  obtain ⟨t, rfl⟩ := AddCircle.exists_pi_coe_eq x
  obtain ⟨n, hn⟩ := (coe_mem_ker_smulVecHom_iff A p t).1 hx
  have := invertibleOfIsUnitDet _ hA
  exact ⟨n, by rw [invMulVecHom_apply, smul_intCast_eq, ← hn, inv_mulVec_eq_vec rfl]⟩

/-- **The kernel of an integer matrix acting on a torus.** For `p ≠ 0` and a square integer matrix
`A` with `det A ≠ 0`, the map `n ↦ [A⁻¹ (p n)]` identifies `ℤⁱ / A ℤⁱ` with the kernel of the map
of the torus `ι → AddCircle p` induced by `A` (`Matrix.coe_quotientRangeEquivKerSmulVecHom_mk`). -/
def quotientRangeEquivKerSmulVecHom (A : Matrix ι ι ℤ) (hA : A.det ≠ 0) (hp : p ≠ 0) :
    (ι → ℤ) ⧸ (LinearMap.range A.mulVecLin).toAddSubgroup ≃+
      (A.smulVecHom (AddCircle p) : (ι → AddCircle p) →+ (ι → AddCircle p)).ker :=
  let ψ := (invMulVecHom p A).codRestrict _ (invMulVecHom_mem_ker p (isUnit_det_map_intCast hA))
  have hψ : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := exists_invMulVecHom_eq p (isUnit_det_map_intCast hA) hx
    refine ⟨n, Subtype.ext ?_⟩
    rw [AddMonoidHom.codRestrict_apply, Subtype.coe_mk, Subtype.coe_mk, hn]
  have hker : (LinearMap.range A.mulVecLin).toAddSubgroup = ψ.ker := by
    ext n
    rw [AddMonoidHom.ker_codRestrict, AddMonoidHom.mem_ker, invMulVecHom_apply,
      coe_inv_mulVec_eq_zero_iff p (isUnit_det_map_intCast hA) hp, Submodule.mem_toAddSubgroup,
      LinearMap.mem_range]
    simp only [mulVecLin_apply]
  (QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ)

/-- The identification `ℤⁱ / A ℤⁱ ≃ ker A` sends the class of `n` to `[A⁻¹ (p n)]`. -/
@[simp]
theorem coe_quotientRangeEquivKerSmulVecHom_mk (A : Matrix ι ι ℤ) (hA : A.det ≠ 0) (hp : p ≠ 0)
    (n : ι → ℤ) :
    (quotientRangeEquivKerSmulVecHom p A hA hp n : ι → AddCircle p) =
      fun i ↦ (((A.map ((↑) : ℤ → K))⁻¹ *ᵥ (p • (n · : ι → K))) i : AddCircle p) := by
  rw [quotientRangeEquivKerSmulVecHom, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk, ← invMulVecHom_apply]
  -- The first isomorphism theorem sends the class of `n` to the corestriction of
  -- `invMulVecHom p A` at `n`, whose underlying point is `invMulVecHom p A n`.
  exact congrArg Subtype.val (TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk _ _ n)

/-- A square integer matrix `A` with `det A = 0` kills infinitely many points of the torus
`ι → AddCircle p`: for a nonzero integer null vector `m` of `A`, the kernel contains the image of
`t ↦ [t m]`, `t ∈ K`, a copy of `AddCircle p` for `p ≠ 0` and of `K` for `p = 0`. -/
theorem infinite_ker_smulVecHom {A : Matrix ι ι ℤ} (hA : A.det = 0) :
    Infinite (A.smulVecHom (AddCircle p) : (ι → AddCircle p) →+ (ι → AddCircle p)).ker := by
  obtain ⟨m, hm, hAm⟩ := exists_mulVec_eq_zero_iff.2 hA
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hm
  have hBm : A.map ((↑) : ℤ → K) *ᵥ (m · : ι → K) = 0 := by
    rw [map_intCast_mulVec, hAm]
    exact funext fun _ ↦ Int.cast_zero
  have hmem (t : K) : (fun j ↦ ((t * m j : K) : AddCircle p)) ∈
      (A.smulVecHom (AddCircle p) : (ι → AddCircle p) →+ (ι → AddCircle p)).ker := by
    have ht : (fun j ↦ t * (m j : K)) = t • (m · : ι → K) :=
      funext fun j ↦ by rw [Pi.smul_apply, smul_eq_mul]
    rw [coe_mem_ker_smulVecHom_iff, ht, mulVec_smul, hBm, smul_zero]
    exact ⟨0, funext fun k ↦ by rw [Pi.zero_apply, Pi.zero_apply, Int.cast_zero, zero_mul]⟩
  -- The `i`-th coordinate of `t ↦ [t m]` covers the infinite group `AddCircle p`.
  refine Infinite.of_surjective (fun x ↦ x.val i) fun y ↦ ?_
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective y
  exact ⟨⟨_, hmem (s / m i)⟩, by simp [div_mul_cancel₀ s (Int.cast_ne_zero.2 hi)]⟩

/-- **The number of points of the kernel of an integer matrix acting on a torus.** For `p ≠ 0`, the
kernel of the map of the torus `ι → AddCircle p` induced by a square integer matrix `A` has
`Nat.card` equal to `|det A|`. When `det A ≠ 0` it is a finite group with `|det A|` elements,
isomorphic to `ℤⁱ / A ℤⁱ` (`Matrix.quotientRangeEquivKerSmulVecHom`); when `det A = 0` it is
infinite (`Matrix.infinite_ker_smulVecHom`) and `Nat.card` takes the junk value `0`. -/
theorem natCard_ker_smulVecHom (A : Matrix ι ι ℤ) (hp : p ≠ 0) :
    Nat.card (A.smulVecHom (AddCircle p) : (ι → AddCircle p) →+ (ι → AddCircle p)).ker =
      A.det.natAbs := by
  by_cases hA : A.det = 0
  · have := infinite_ker_smulVecHom p hA
    rw [hA, Int.natAbs_zero, Nat.card_eq_zero_of_infinite]
  have hindex : (LinearMap.range A.mulVecLin).toAddSubgroup.index = A.det.natAbs := by
    rw [← toLin'_apply', LinearMap.index_range_eq_natAbs_det_toMatrix (Pi.basisFun ℤ ι)
      (Pi.basisFun ℤ ι), LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  rw [← Nat.card_congr (quotientRangeEquivKerSmulVecHom p A hA hp).toEquiv, ← AddSubgroup.index,
    hindex]

/-- A square integer matrix `A` kills finitely many points of the torus `ι → AddCircle p` exactly
when `det A ≠ 0`. -/
theorem finite_ker_smulVecHom_iff (A : Matrix ι ι ℤ) :
    Finite (A.smulVecHom (AddCircle p) : (ι → AddCircle p) →+ (ι → AddCircle p)).ker ↔
      A.det ≠ 0 := by
  refine ⟨fun h hA ↦ not_finite_iff_infinite.2 (infinite_ker_smulVecHom p hA) h, fun hA ↦ ?_⟩
  rcases eq_or_ne p 0 with rfl | hp
  · -- For `p = 0` every kernel point is `[A⁻¹ (0 • n)] = 0`.
    suffices Subsingleton
        (A.smulVecHom (AddCircle (0 : K)) : (ι → AddCircle (0 : K)) →+ (ι → AddCircle (0 : K))).ker
      from inferInstance
    refine subsingleton_of_forall_eq 0 fun ⟨x, hx⟩ ↦ ?_
    obtain ⟨n, rfl⟩ := exists_invMulVecHom_eq 0 (isUnit_det_map_intCast hA) hx
    ext i
    simp [invMulVecHom_apply]
  · exact Nat.finite_of_card_ne_zero <| by
      rw [natCard_ker_smulVecHom p A hp]
      exact Int.natAbs_ne_zero.2 hA

end Matrix
