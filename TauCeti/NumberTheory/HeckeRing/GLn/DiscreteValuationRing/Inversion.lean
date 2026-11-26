/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.NumberTheory.HeckeRing.GLn.DiscreteValuationRing.Minuscule
public import TauCeti.NumberTheory.HeckeRing.Normalizer
public import TauCeti.RingTheory.DiscreteValuationRing.Basic

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# The central coset and the inversion formula in the local Hecke ring of `GL_n`

Let `R` be a domain with fraction field `K` whose quotients by nonzero ideals are finite, such
as a discrete valuation ring with finite residue field, let `π ∈ Kˣ` (in the application, the
image of a uniformizer), and `η_j = diag(π^{(j)}, 1^{(n - j)})` (`HeckeRing.GLn.minusculeDiag`).
In the Hecke ring `H = 𝕋 ⊤ GL_n(R) S` of `(GL_n(K), GL_n(R))`, over any coefficient semiring
`S`, write `T^{(j)} = [K η_j K]`.

* The operator `T^{(n)}` is the single coset of the central element `π`, and it is a unit of `H`
  with inverse the coset of `π⁻¹` (`HeckeRing.GLn.scalarCosetUnit`).
* **Inversion.** For `0 ≤ j ≤ n`, `T^{(n)} [K η_j⁻¹ K] = T^{(n - j)}`
  (`HeckeRing.GLn.single_minusculeCoset_self_mul_single_inv`). Indeed `π η_j⁻¹ =
  diag(1^{(j)}, π^{(n - j)})` is conjugate to `η_{n - j}` by the permutation matrix of
  `i ↦ n - 1 - i`, which lies in `GL_n(R)`, and the central coset multiplies with coefficient one
  (`HeckeCosetModule.single_mul_single_of_mem_normalizer`). Hence
  `[K η_j⁻¹ K] = (T^{(n)})⁻¹ T^{(n - j)}` (`HeckeRing.GLn.single_inv_minusculeDiag_eq`), which is
  how the slash operators of the inverse elements are expressed through the operators
  `T^{(j)}`; at a split place `v = w w^c` of a unitary group the operators at `w^c` are of this
  form.

## Main definitions

* `HeckeRing.GLn.scalarCosetUnit R S π n`: the unit `[K π K]` of the local Hecke ring.

## Main results

* `HeckeRing.GLn.single_minusculeCoset_self_mul_single_inv`: `T^{(n)} [K η_j⁻¹ K] = T^{(n - j)}`.
* `HeckeRing.GLn.single_inv_minusculeDiag_eq`: `[K η_j⁻¹ K] = (T^{(n)})⁻¹ T^{(n - j)}`.

## References

* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, Princeton
  University Press (1971), §3.2.
* M. Emerton and T. Gee, *A geometric perspective on the Breuil–Mézard conjecture*, J. Inst.
  Math. Jussieu 13 (2014), §5.3.

The inversion formula is adapted from grh-lean (<https://github.com/lsernau/grh-lean>, Apache
2.0, Copyright 2026 Anthropic PBC), `Lib/Weil/Unramified/HeckeGL.lean`, declarations
`New.heckeGL_dual` and `New.scalar_mul_mem_basicDoubleCoset_iff`, where it is stated for the
action of the Hecke operators on `GL_n(O_w)`-fixed vectors of a representation.
-/

public section

open Matrix DoubleCoset HeckeCosetModule TauCeti
open scoped HeckeCosetModule

namespace HeckeRing.GLn

variable {K : Type*} [Field K] {n : ℕ}

/-- `η_n` is the scalar matrix `π`, which is central in `GL_n(K)`. -/
theorem minusculeDiag_self_mem_center (π : Kˣ) (n : ℕ) :
    minusculeDiag π n n ∈ Subgroup.center (GL (Fin n) K) := by
  rw [minusculeDiag_of_le π le_rfl, GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨π, rfl⟩

/-- `η_n η_j⁻¹ = diag(1^{(j)}, π^{(n - j)})` is the conjugate of `η_{n - j}` by the permutation
matrix of the reversal `i ↦ n - 1 - i`. -/
theorem minusculeDiag_self_mul_inv_eq (π : Kˣ) {j : ℕ} (hj : j ≤ n) :
    minusculeDiag π n n * (minusculeDiag π n j)⁻¹ =
      (permutationGL (k := K) Fin.revPerm)⁻¹ * minusculeDiag π n (n - j) *
        permutationGL (k := K) Fin.revPerm := by
  set p := permutationGL (k := K) (Fin.revPerm : Equiv.Perm (Fin n))
  have h : p * (minusculeDiag π n n * (minusculeDiag π n j)⁻¹) * p⁻¹ =
      minusculeDiag π n (n - j) := by
    rw [minusculeDiag_def, minusculeDiag_def, minusculeDiag_def, ← map_inv, ← map_mul,
      permutationGL_mul_diagGL_mul_inv]
    congr 1
    funext i
    have hi := i.isLt
    have hrev : ((Fin.revPerm⁻¹ i : Fin n) : ℕ) = n - (i + 1) := by
      rw [Equiv.Perm.inv_def, Fin.revPerm_symm, Fin.revPerm_apply, Fin.val_rev]
    by_cases h : (i : ℕ) < n - j
    · simp only [Pi.mul_apply, Pi.inv_apply, hrev, show n - (i + 1) < n by omega, ite_true,
        show ¬ n - (i + 1) < j by omega, ite_false, inv_one, _root_.mul_one, h]
    · simp only [Pi.mul_apply, Pi.inv_apply, hrev, show n - (i + 1) < n by omega, ite_true,
        show n - (i + 1) < j by omega, mul_inv_cancel, h, ite_false]
  rw [← h]
  group

variable {R : Type*} [CommRing R] [Algebra R K]

/-- The permutation matrices lie in `GL_n(R)`. -/
theorem permutationGL_mem_integralGL (σ : Equiv.Perm (Fin n)) :
    permutationGL (k := K) σ ∈ integralGL R K (Fin n) :=
  ⟨permutationGL σ, map_permutationGL _ σ⟩

/-- `η_n η_j⁻¹` lies in the double coset of `η_{n - j}`. -/
theorem minusculeDiag_self_mul_inv_mem_doubleCoset (π : Kˣ) {j : ℕ} (hj : j ≤ n) :
    minusculeDiag π n n * (minusculeDiag π n j)⁻¹ ∈
      doubleCoset (minusculeDiag π n (n - j)) (integralGL R K (Fin n))
        (integralGL R K (Fin n)) := by
  rw [minusculeDiag_self_mul_inv_eq π hj]
  exact mem_doubleCoset.mpr ⟨_, inv_mem (permutationGL_mem_integralGL _), _,
    permutationGL_mem_integralGL _, rfl⟩

section Units

variable [IsFractionRing R K] [Ring.HasFiniteQuotients R] (S : Type*) [Semiring S]

variable (R) in
/-- **The central coset is a unit of the local Hecke ring.** The double coset
`[K π K] = T^{(n)}` of the central element `η_n = π` is a unit of the Hecke ring of
`(GL_n(K), GL_n(R))` over any coefficient semiring `S`, with inverse `[K π⁻¹ K]`. -/
noncomputable def scalarCosetUnit (π : Kˣ) (n : ℕ) :
    (𝕋 (⊤ : Submonoid (GL (Fin n) K)) (integralGL R K (Fin n)) S)ˣ :=
  unitOfMemNormalizer S (Submonoid.mem_top _) (Submonoid.mem_top _)
    (Subgroup.center_le_normalizer _ (minusculeDiag_self_mem_center π n))

/-- The underlying element of `scalarCosetUnit` is `T^{(n)} = [K η_n K]`. -/
@[simp]
theorem val_scalarCosetUnit (π : Kˣ) :
    (scalarCosetUnit R S π n : 𝕋 (⊤ : Submonoid (GL (Fin n) K)) (integralGL R K (Fin n)) S) =
      single S (minusculeCoset R π n n) 1 := by
  rw [scalarCosetUnit, val_unitOfMemNormalizer, minusculeCoset_def]

/-- The inverse of `scalarCosetUnit` is the coset `[K π⁻¹ K]`. -/
@[simp]
theorem val_inv_scalarCosetUnit (π : Kˣ) :
    (↑(scalarCosetUnit R S π n)⁻¹ :
        𝕋 (⊤ : Submonoid (GL (Fin n) K)) (integralGL R K (Fin n)) S) =
      single S (HeckeCoset.mk _ _ ⟨(minusculeDiag π n n)⁻¹, Submonoid.mem_top _⟩) 1 :=
  by rw [scalarCosetUnit, val_inv_unitOfMemNormalizer]

/-- **The inversion formula** `T^{(n)} [K η_j⁻¹ K] = T^{(n - j)}` for `0 ≤ j ≤ n`, in the Hecke
ring of `(GL_n(K), GL_n(R))` over any coefficient semiring. -/
theorem single_minusculeCoset_self_mul_single_inv (π : Kˣ) {j : ℕ} (hj : j ≤ n) :
    single S (minusculeCoset R π n n) 1 *
        single S (HeckeCoset.mk (integralGL R K (Fin n)) (integralGL R K (Fin n))
          ⟨(minusculeDiag π n j)⁻¹, Submonoid.mem_top _⟩) 1 =
      single S (minusculeCoset R π n (n - j)) 1 := by
  rw [minusculeCoset_def, minusculeCoset_def, single_mul_single_of_mem_normalizer S
    (Subgroup.center_le_normalizer _ (minusculeDiag_self_mem_center π n))]
  exact congrArg (single S · 1)
    (HeckeCoset.mk_eq_mk_of_mem (minusculeDiag_self_mul_inv_mem_doubleCoset π hj))

/-- **The coset of `η_j⁻¹` through the operators `T^{(j)}`**:
`[K η_j⁻¹ K] = (T^{(n)})⁻¹ T^{(n - j)}` for `0 ≤ j ≤ n`. -/
theorem single_inv_minusculeDiag_eq (π : Kˣ) {j : ℕ} (hj : j ≤ n) :
    single S (HeckeCoset.mk (integralGL R K (Fin n)) (integralGL R K (Fin n))
        ⟨(minusculeDiag π n j)⁻¹, Submonoid.mem_top _⟩) 1 =
      ↑(scalarCosetUnit R S π n)⁻¹ * single S (minusculeCoset R π n (n - j)) 1 := by
  rw [← single_minusculeCoset_self_mul_single_inv S π hj, ← _root_.mul_assoc,
    ← val_scalarCosetUnit, Units.inv_mul, _root_.one_mul]

end Units

end HeckeRing.GLn
