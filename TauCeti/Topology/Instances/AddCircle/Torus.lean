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
import TauCeti.LinearAlgebra.FreeModule.Int

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

The covering map `(ι → ℝ) → (ι → AddCircle p)` intertwines `Matrix.smulVecHom A` with
multiplication of real vectors by `A` (`Matrix.smulVecHom_coe_pi`). Consequently a square integer
matrix `A` kills exactly `|det A|` points of the torus `ι → AddCircle p`, for `p ≠ 0`
(`Matrix.natCard_ker_smulVecHom`): when `det A ≠ 0` the kernel is `A⁻¹ (p ℤⁱ) / p ℤⁱ`, isomorphic to
`ℤⁱ / A ℤⁱ`, and when `det A = 0` it contains a circle and is infinite, `Nat.card` then taking the
junk value `0`. For a `1 × 1` matrix `n` this is the count `AddCircle.natCard_torsionBy` of the
`n`-torsion of the circle. Applied to `1 - A`, it counts the fixed points of the toral
automorphism induced by `A` (`AddCircle.nat_card_fixedPoints_generalLinearGroup_smul`).
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

variable {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℤ) (p : ℝ)

/-- An integer matrix sends the straight loop of `n` to the straight loop of `A *ᵥ n`. -/
theorem smulVecHom_comp_torusLoop (n : ι → ℤ) :
    (A.smulVecHom (AddCircle p) : C(ι → AddCircle p, κ → AddCircle p)).comp
        (TauCeti.torusLoop (fun _ ↦ p) n).toContinuousMap =
      (TauCeti.torusLoop (fun _ ↦ p) (A *ᵥ n)).toContinuousMap := by
  ext t k
  simp only [ContinuousMap.comp_apply, Path.coe_toContinuousMap, TauCeti.torusLoop_apply,
    mulVec, dotProduct]
  have h : (t * (∑ i, A k i * n i) • p : ℝ) = ∑ i, A k i • (t * (n i • p) : ℝ) := by
    simp only [Finset.sum_smul, Finset.mul_sum, mul_smul, mul_smul_comm]
  rw [h, ← QuotientAddGroup.mk'_apply, map_sum]
  simp

/-- The covering map `(ι → ℝ) → (ι → AddCircle p)` intertwines the map of tori induced by an integer
matrix `A` with multiplication of real vectors by `A`. -/
theorem smulVecHom_coe_pi (t : ι → ℝ) :
    A.smulVecHom (AddCircle p) (fun i ↦ (t i : AddCircle p)) =
      fun k ↦ ((A.map ((↑) : ℤ → ℝ) *ᵥ t) k : AddCircle p) := by
  ext k
  simp only [smulVecHom_apply, mulVec, dotProduct, map_apply, ← zsmul_eq_mul,
    QuotientAddGroup.mk_sum, AddCircle.coe_zsmul]

end Matrix

/-! ### The kernel of a square integer matrix -/

namespace Matrix

variable {ι : Type*} [Fintype ι] (p : ℝ)

/-- A point `[t]` of the torus lies in the kernel of the map induced by an integer matrix `A`
exactly when `A t` has integer multiples of `p` as coordinates. -/
private theorem coe_mem_ker_smulVecHom_iff (A : Matrix ι ι ℤ) (t : ι → ℝ) :
    (fun i ↦ (t i : AddCircle p)) ∈ (A.smulVecHom (AddCircle p)).toAddMonoidHom.ker ↔
      (fun k ↦ ((A.map ((↑) : ℤ → ℝ) *ᵥ t) k : AddCircle p)) = 0 := by
  rw [AddMonoidHom.mem_ker, ContinuousAddMonoidHom.coe_toAddMonoidHom, AddMonoidHom.coe_ofClass,
    smulVecHom_coe_pi]

variable [DecidableEq ι] {B : Matrix ι ι ℝ}

/-- A point of the torus killed by an invertible real matrix `B` lifts to `B⁻¹ (p n)` for an integer
vector `n`. -/
private theorem exists_eq_coe_inv_mulVec (hB : IsUnit B.det) {t : ι → ℝ}
    (ht : (fun k ↦ ((B *ᵥ t) k : AddCircle p)) = 0) :
    ∃ n : ι → ℤ, t = B⁻¹ *ᵥ (p • (n · : ι → ℝ)) := by
  choose n hn using fun k ↦ (AddCircle.coe_eq_zero_iff p).1 (congrFun ht k)
  refine ⟨n, ?_⟩
  have : B *ᵥ t = p • (n · : ι → ℝ) := funext fun k ↦ by simp [← hn k, zsmul_eq_mul, mul_comm]
  rw [← this, mulVec_mulVec, nonsing_inv_mul _ hB, one_mulVec]

/-- For an integer matrix `A` with nonzero determinant and `p ≠ 0`, the point `[A⁻¹ (p n)]` of the
torus vanishes exactly when the integer vector `n` lies in the image of `A`. -/
private theorem coe_inv_mulVec_eq_zero_iff {A : Matrix ι ι ℤ}
    (hA : IsUnit (A.map ((↑) : ℤ → ℝ)).det) (hp : p ≠ 0) (n : ι → ℤ) :
    (fun i ↦ (((A.map ((↑) : ℤ → ℝ))⁻¹ *ᵥ (p • (n · : ι → ℝ))) i : AddCircle p)) = 0 ↔
      ∃ m, A *ᵥ m = n := by
  set B := A.map ((↑) : ℤ → ℝ)
  have hcast (m : ι → ℤ) : B *ᵥ (m · : ι → ℝ) = fun x ↦ ((A *ᵥ m) x : ℝ) :=
    funext fun x ↦ (RingHom.map_mulVec (Int.castRingHom ℝ) A m x).symm
  constructor
  · intro h
    choose m hm using fun i ↦ (AddCircle.coe_eq_zero_iff p).1 (congrFun h i)
    have hv : B⁻¹ *ᵥ (p • (n · : ι → ℝ)) = p • (m · : ι → ℝ) :=
      funext fun i ↦ by simp [← hm i, zsmul_eq_mul, mul_comm]
    have hv' := congrArg (B *ᵥ ·) hv
    simp only [mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec, mulVec_smul, hcast] at hv'
    exact ⟨m, funext fun k ↦ Int.cast_injective (α := ℝ)
      (congrFun (smul_right_injective _ hp hv') k).symm⟩
  · rintro ⟨m, rfl⟩
    ext i
    rw [← hcast, ← mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec]
    exact (AddCircle.coe_eq_zero_iff p).2 ⟨m i, by rw [zsmul_eq_mul, mul_comm]; rfl⟩

/-- A square integer matrix `A` with `det A = 0` kills infinitely many points of the torus
`ι → AddCircle p`: for an integer null vector `m` of `A`, the kernel contains the circle
`t ↦ [t m]`. -/
theorem infinite_ker_smulVecHom {A : Matrix ι ι ℤ} (hA : A.det = 0) :
    Infinite (A.smulVecHom (AddCircle p)).toAddMonoidHom.ker := by
  obtain ⟨m, hm, hAm⟩ := exists_mulVec_eq_zero_iff.2 hA
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hm
  have hBm : A.map ((↑) : ℤ → ℝ) *ᵥ (m · : ι → ℝ) = 0 := funext fun k ↦
    (RingHom.map_mulVec (Int.castRingHom ℝ) A m k).symm.trans (by simp [hAm])
  have hmem (t : ℝ) : (fun j ↦ ((t * m j : ℝ) : AddCircle p)) ∈
      (A.smulVecHom (AddCircle p)).toAddMonoidHom.ker := by
    rw [coe_mem_ker_smulVecHom_iff,
      show (fun j ↦ t * (m j : ℝ)) = t • (m · : ι → ℝ) from rfl, mulVec_smul, hBm]
    simp only [smul_zero, Pi.zero_apply, QuotientAddGroup.mk_zero]
    rfl
  have : Infinite (AddCircle p) := by
    rcases eq_or_ne p 0 with rfl | hp
    · -- `AddCircle 0` is `ℝ`.
      refine Infinite.of_injective (fun t : ℝ ↦ (t : AddCircle (0 : ℝ))) fun a b h ↦ ?_
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (0 : ℝ)).1
        (by rw [AddCircle.coe_sub, sub_eq_zero]; exact h : ((a - b : ℝ) : AddCircle (0 : ℝ)) = 0)
      rw [smul_zero] at hn
      linarith
    · have : NeZero p := ⟨hp⟩
      infer_instance
  -- The `i`-th coordinate of the circle `t ↦ [t m]` covers the infinite group `AddCircle p`.
  refine Infinite.of_surjective (fun x ↦ x.1 i) fun y ↦ ?_
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective y
  exact ⟨⟨_, hmem (s / m i)⟩, by simp [div_mul_cancel₀ s (Int.cast_ne_zero.2 hi)]⟩

/-- **The kernel of an integer matrix acting on a torus.** For `p ≠ 0`, a square integer matrix `A`
kills exactly `|det A|` points of the torus `ι → AddCircle p`. When `det A ≠ 0` the kernel is
isomorphic to `ℤⁱ / A ℤⁱ`; when `det A = 0` it is infinite (`Matrix.infinite_ker_smulVecHom`) and
`Nat.card` takes the junk value `0`. -/
theorem natCard_ker_smulVecHom (A : Matrix ι ι ℤ) (hp : p ≠ 0) :
    Nat.card (A.smulVecHom (AddCircle p)).toAddMonoidHom.ker = A.det.natAbs := by
  by_cases hA : A.det = 0
  · have := infinite_ker_smulVecHom p hA
    rw [hA, Int.natAbs_zero, Nat.card_eq_zero_of_infinite]
  set B : Matrix ι ι ℝ := A.map ((↑) : ℤ → ℝ) with hB
  have hBu : IsUnit B.det := by
    rw [hB, ← Int.cast_det]
    exact (Int.cast_ne_zero.2 hA).isUnit
  -- `n ↦ [B⁻¹ (p n)]` maps `ℤⁱ` onto the kernel, with kernel `A ℤⁱ`.
  let ψ : (ι → ℤ) →+ (A.smulVecHom (AddCircle p)).toAddMonoidHom.ker :=
    { toFun n := ⟨fun i ↦ ((B⁻¹ *ᵥ (p • (n · : ι → ℝ))) i : AddCircle p), by
        rw [coe_mem_ker_smulVecHom_iff, ← hB, mulVec_mulVec, mul_nonsing_inv _ hBu, one_mulVec]
        exact funext fun k ↦
          (AddCircle.coe_eq_zero_iff p).2 ⟨n k, by simp [zsmul_eq_mul, mul_comm]⟩⟩
      map_zero' := by
        ext i
        simp only [Pi.zero_apply, Int.cast_zero, ← Pi.zero_def, smul_zero, mulVec_zero]
        rfl
      map_add' n m := by
        ext i
        simp only [Pi.add_apply, Int.cast_add]
        rw [show (fun x ↦ (n x : ℝ) + m x) = (fun x ↦ (n x : ℝ)) + fun x ↦ (m x : ℝ) from rfl,
          smul_add, mulVec_add]
        rfl }
  have hψ : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    choose t ht using fun i ↦ QuotientAddGroup.mk_surjective (x i)
    obtain rfl : x = fun i ↦ (t i : AddCircle p) := funext fun i ↦ (ht i).symm
    rw [coe_mem_ker_smulVecHom_iff] at hx
    obtain ⟨n, rfl⟩ := exists_eq_coe_inv_mulVec p hBu hx
    exact ⟨n, rfl⟩
  have hker : ψ.ker = (LinearMap.range A.mulVecLin).toAddSubgroup := by
    ext n
    simpa [Subtype.ext_iff, ψ] using coe_inv_mulVec_eq_zero_iff p hBu hp n
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv, hker,
    ← AddSubgroup.index, LinearMap.index_range_eq_natAbs_det_toMatrix (Pi.basisFun ℤ ι)
      (Pi.basisFun ℤ ι), LinearMap.toMatrix_eq_toMatrix', ← Matrix.toLin'_apply',
    LinearMap.toMatrix'_toLin']

end Matrix
