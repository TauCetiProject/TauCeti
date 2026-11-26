/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DeterminantK1
import TauCeti.RingTheory.Length.Determinant

/-!
# The order of vanishing on algebraic `K₁` of a fraction field

Let `A` be a Noetherian domain of Krull dimension at most one with fraction field `K`, for
instance a discrete valuation ring or the local ring of a curve at a closed point. The order of
vanishing `Ring.ordFrac A : K →*₀ ℤᵐ⁰` of Mathlib is multiplicative, so composing it with the
determinant `K₁(K) →* Kˣ` gives a homomorphism

  `AlgebraicK1.ordFrac A : K₁(K) →* Multiplicative ℤ`,  `[g] ↦ ord_A (det g)`.

The value on the class of an invertible matrix `g` over `K` is computed by clearing denominators:
if `s ≠ 0` in `A` and `α` is a matrix over `A` with image `s • g` in `K`, then

  `ord_A (det g) = length_A (Aⁿ / α Aⁿ) - n · length_A (A / s A)`.

In particular the right-hand side does not depend on the choice of `s` and `α`, and an
integral matrix `α` invertible over `K` has value the length of its cokernel. The sign convention
makes the cokernel of an injective integral matrix count positively. When `A` is local, this is
expected to agree with the localization boundary `K₁(K) → K₀` of finite-length `A`-modules,
measured by length; that comparison is not formalized here.

Units of `A` have order zero, so `K₁(A) → K₁(K) → ℤ` is trivial. For a discrete valuation ring
`O` with fraction field `L` the sequence

  `1 → K₁(O) → K₁(L) → ℤ → 0`

is exact: `K₁(O) = Oˣ` and `K₁(L) = Lˣ` through the determinant, the order of vanishing is the
normalized valuation, its kernel is `Oˣ`, and a uniformizer `π` has value `1`. Injectivity of
`K₁(O) → K₁(L)` is the semilocal case `TauCeti.AlgebraicK1.map_algebraMap_injective`.

## Main definitions

* `TauCeti.AlgebraicK1.ordFrac`: the homomorphism `K₁(K) →* Multiplicative ℤ`, `x ↦ ord_A (det x)`.

## Main results

* `TauCeti.AlgebraicK1.coe_ordFrac`: the characterization by the determinant.
* `TauCeti.AlgebraicK1.ordFrac_mk_of_map_eq_smul`: the denominator-clearing length formula.
* `TauCeti.AlgebraicK1.ordFrac_mk_of_map_eq`: an integral matrix invertible over `K` has value
  the length of its cokernel.
* `TauCeti.AlgebraicK1.ordFrac_map_algebraMap`: classes coming from `K₁(A)` have value `1`.
* `TauCeti.AlgebraicK1.ordFrac_ofUnits_of_irreducible`, `TauCeti.AlgebraicK1.ordFrac_surjective`,
  `TauCeti.AlgebraicK1.range_map_algebraMap_eq_ker_ordFrac`: exactness of
  `1 → K₁(O) → K₁(L) → ℤ → 0` for a discrete valuation ring `O`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Lemma 3.1, Corollary 3.1.1 and Example 3.1.2 (the
  localization sequence and its boundary for a discrete valuation ring).
* W. Fulton, *Intersection Theory*, Appendix A.2 (the order of a determinant as a length).
-/

public section

noncomputable section

open Matrix
open scoped WithZero

namespace TauCeti

namespace AlgebraicK1

section KrullDimLE

variable (A : Type*) {K : Type*} [CommRing A] [Nontrivial A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- The **order of vanishing** on algebraic `K₁` of the fraction field `K` of a Noetherian domain
`A` of dimension at most one: the order `ord_A (det x)` of the determinant of a class `x`. On the
class of an integral matrix it is the length of the cokernel
(`TauCeti.AlgebraicK1.ordFrac_mk_of_map_eq`). -/
def ordFrac : AlgebraicK1 K →* Multiplicative ℤ :=
  (WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (Ring.ordFrac A : K →*₀ ℤᵐ⁰).toMonoidHom)).comp (det K)

variable {A}

/-- The order of vanishing of a class of `K₁(K)` is the order of its determinant. -/
@[simp]
theorem coe_ordFrac (x : AlgebraicK1 K) :
    (ordFrac A x : ℤᵐ⁰) = Ring.ordFrac A (det K x : K) := by
  simp [ordFrac]

/-- The order of vanishing of a class equals `z` exactly when the order of its determinant is
`z`. -/
theorem ordFrac_eq_iff {x : AlgebraicK1 K} {z : Multiplicative ℤ} :
    ordFrac A x = z ↔ Ring.ordFrac A (det K x : K) = z := by
  rw [← coe_ordFrac, WithZero.coe_inj]

/-- The order of vanishing of the class of an invertible matrix over `K` is the order of its
determinant. -/
theorem coe_ordFrac_mk {n : ℕ} (g : GL (Fin n) K) :
    (ordFrac A (mk K n g) : ℤᵐ⁰) = Ring.ordFrac A (g : Matrix (Fin n) (Fin n) K).det := by
  simp [GeneralLinearGroup.val_det_apply]

/-- Classes coming from `K₁(A)` have trivial order of vanishing: their determinants are units of
`A`. -/
@[simp]
theorem ordFrac_map_algebraMap (x : AlgebraicK1 A) :
    ordFrac A (map (algebraMap A K) x) = 1 := by
  have := (IsFractionRing.injective A K).isDomain
  rw [ordFrac_eq_iff, WithZero.coe_one, det_map]
  exact Ring.ordFrac_of_isUnit (det A x).isUnit

/-- **Clearing denominators.** Let `g` be an invertible matrix over `K`, and let `α` be a matrix
over `A` whose image in `K` is `s • g` for some nonzero `s : A`. Then the order of vanishing of
the class of `g` is the length of the cokernel of `α` on `Aⁿ` minus `n` times the length of
`A ⧸ s A`. In particular this difference depends only on `g`. -/
theorem ordFrac_mk_of_map_eq_smul {n : ℕ} (g : GL (Fin n) K) {s : A} (hs : s ≠ 0)
    {α : Matrix (Fin n) (Fin n) A}
    (hα : α.map (algebraMap A K) = algebraMap A K s • (g : Matrix (Fin n) (Fin n) K))
    {ℓ m : ℕ} (hℓ : Module.length A ((Fin n → A) ⧸ LinearMap.range α.mulVecLin) = ℓ)
    (hm : Ring.ord A s = m) :
    ordFrac A (mk K n g) = Multiplicative.ofAdd ((ℓ : ℤ) - n * m) := by
  have := (IsFractionRing.injective A K).isDomain
  have hdet : algebraMap A K α.det =
      algebraMap A K s ^ n * (g : Matrix (Fin n) (Fin n) K).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hα, det_smul, Fintype.card_fin]
  have hα0 : α.det ≠ 0 := by
    refine fun h ↦ (g.isUnit.map Matrix.detMonoidHom).ne_zero ?_
    have hs' : algebraMap A K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hs
    simpa [h, hs'] using hdet.symm
  have hord : Ring.ord A α.det = ℓ := by
    rw [← hℓ, Matrix.length_quotient_range_mulVecLin_eq_ord_det α hα0]
  have key := congrArg (Ring.ordFrac A) hdet
  simp only [map_mul, map_pow, Ring.ordFrac_eq_ord, ← coe_ordFrac_mk,
    Ring.ordMonoidWithZeroHom_eq_coe A (mem_nonZeroDivisors_of_ne_zero hα0) hord,
    Ring.ordMonoidWithZeroHom_eq_coe A (mem_nonZeroDivisors_of_ne_zero hs) hm] at key
  norm_cast at key
  apply Multiplicative.toAdd.injective
  have := congrArg Multiplicative.toAdd key
  simp only [toAdd_ofAdd, toAdd_mul, toAdd_pow, nsmul_eq_mul] at this ⊢
  linarith

/-- An integral matrix `α` whose image `g` in `K` is invertible has order of vanishing the length
of the cokernel of `α` on `Aⁿ`. With this sign convention the cokernel of an injective integral
matrix counts positively. -/
theorem ordFrac_mk_of_map_eq {n : ℕ} (g : GL (Fin n) K) {α : Matrix (Fin n) (Fin n) A}
    (hα : α.map (algebraMap A K) = g) {ℓ : ℕ}
    (hℓ : Module.length A ((Fin n → A) ⧸ LinearMap.range α.mulVecLin) = ℓ) :
    ordFrac A (mk K n g) = Multiplicative.ofAdd (ℓ : ℤ) := by
  have hord : Ring.ord A (1 : A) = (0 : ℕ) := by simp
  simpa using ordFrac_mk_of_map_eq_smul g one_ne_zero (by simpa using hα) hℓ hord

end KrullDimLE

/-! ## Discrete valuation rings -/

section IsDiscreteValuationRing

variable {O L : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L]
  [Algebra O L] [IsFractionRing O L]

/-- A uniformizer `π` of a discrete valuation ring `O`, as a unit of the fraction field, has
order of vanishing `1`. -/
theorem ordFrac_ofUnits_of_irreducible {π : O} (hπ : Irreducible π) (u : Lˣ)
    (hu : (u : L) = algebraMap O L π) :
    ordFrac O (ofUnits L u) = Multiplicative.ofAdd 1 := by
  rw [ordFrac_eq_iff, det_ofUnits, hu, Ring.ordFrac_irreducible hπ, WithZero.exp_eq_coe_ofAdd]

/-- The order of vanishing `K₁(L) →* Multiplicative ℤ` of a discrete valuation ring `O` with
fraction field `L` is surjective. -/
theorem ordFrac_surjective : Function.Surjective (ordFrac O : AlgebraicK1 L →* _) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ0 : algebraMap O L π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O L)).2 hπ.ne_zero
  have h1 := ordFrac_ofUnits_of_irreducible hπ (Units.mk0 _ hπ0) rfl
  intro z
  refine ⟨ofUnits L (Units.mk0 _ hπ0) ^ z.toAdd, ?_⟩
  simp [h1, ← ofAdd_zsmul]

/-- **Exactness at `K₁(L)`.** For a discrete valuation ring `O` with fraction field `L`, the image
of `K₁(O) → K₁(L)` is the kernel of the order of vanishing. -/
theorem range_map_algebraMap_eq_ker_ordFrac :
    (map (algebraMap O L)).range = (ordFrac O : AlgebraicK1 L →* _).ker := by
  refine le_antisymm (fun _ ⟨x, hx⟩ ↦ hx ▸ ordFrac_map_algebraMap x) fun x hx ↦ ?_
  have hx' : Ring.ordFrac O (det L x : L) = 1 := by
    rw [← coe_ordFrac, MonoidHom.mem_ker.1 hx, WithZero.coe_one]
  obtain ⟨a, ha, hax⟩ : (det L x : L) ∈ (IsUnit.submonoid O).map (algebraMap O L) := by
    rw [← Ring.mker_ordFrac_eq_isUnitSubmonoid]
    exact MonoidHom.mem_mker.2 hx'
  obtain ⟨u, rfl⟩ := (IsUnit.mem_submonoid_iff a).1 ha
  refine ⟨ofUnits O u, det_injective_of_specialAlgebraicK1_eq_bot
    (specialAlgebraicK1_eq_bot_of_euclideanDomain L) ?_⟩
  ext
  simpa using hax

end IsDiscreteValuationRing

end AlgebraicK1

end TauCeti
