/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Topology.Path
public import TauCeti.Topology.Algebra.Module.Matrix

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

A torus of rank `r` has at most `n ^ r` points of order dividing `n`
(`TauCeti.natCard_torsion_pi_le_of_isSMulRegular`), since these points are the families of such
points of its circles (`TauCeti.torsionPiEquiv`): there are at most `n` on each circle. For
`n = 2` this bounds the elementary abelian `2`-subgroups that a torus can contain.
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

/-! ### Points of finite order -/

section Torsion

variable {𝕜 : Type*} [AddCommGroup 𝕜] (p : ι → 𝕜) (n : ℕ)

/-- The points of order dividing `n` of a torus are the families of such points of its circles. -/
def torsionPiEquiv :
    {x : ∀ i, AddCircle (p i) // n • x = 0} ≃ ∀ i, {y : AddCircle (p i) // n • y = 0} :=
  (Equiv.subtypeEquivRight fun _ ↦ by simp [funext_iff]).trans Equiv.subtypePiEquivPi

@[simp]
theorem coe_torsionPiEquiv_apply (x : {x : ∀ i, AddCircle (p i) // n • x = 0}) (i : ι) :
    (torsionPiEquiv p n x i : AddCircle (p i)) = (x : ∀ i, AddCircle (p i)) i :=
  (rfl)

@[simp]
theorem coe_torsionPiEquiv_symm_apply (y : ∀ i, {y : AddCircle (p i) // n • y = 0}) :
    ((torsionPiEquiv p n).symm y : ∀ i, AddCircle (p i)) = fun i ↦ (y i : AddCircle (p i)) :=
  (rfl)

/-- A torus with finitely many circles has finitely many points of order dividing `n`, when
multiplication by `n` is injective on the coefficients, as it is on `ℝ` for `n ≠ 0`. -/
theorem finite_torsion_pi_of_isSMulRegular [Finite ι] (hn : IsSMulRegular 𝕜 n) :
    Finite {x : ∀ i, AddCircle (p i) // n • x = 0} :=
  have (i : ι) := (AddCircle.finite_torsion_of_isSMulRegular (p i) n hn).to_subtype
  .of_equiv _ (torsionPiEquiv p n).symm

/-- **A torus of rank `r` has at most `n ^ r` points of order dividing `n`**, when `n ≠ 0` and
multiplication by `n` is injective on the coefficients. Each circle has at most `n` such points
(`AddCircle.card_torsion_le_of_isSMulRegular`). -/
theorem natCard_torsion_pi_le_of_isSMulRegular [Fintype ι] (h0 : n ≠ 0)
    (hn : IsSMulRegular 𝕜 n) :
    Nat.card {x : ∀ i, AddCircle (p i) // n • x = 0} ≤ n ^ Fintype.card ι := by
  have hle (i : ι) : Nat.card {y : AddCircle (p i) // n • y = 0} ≤ n := by
    have h := AddCircle.card_torsion_le_of_isSMulRegular (p i) n h0 hn
    rwa [← (AddCircle.finite_torsion_of_isSMulRegular (p i) n hn).cast_ncard_eq, Nat.cast_le,
      ← Nat.card_coe_set_eq] at h
  rw [Nat.card_congr (torsionPiEquiv p n), Nat.card_pi]
  exact (Finset.prod_le_prod fun i _ ↦ hle i).trans_eq (by simp)

end Torsion

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

end Matrix
