/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.NatAntidiagonal
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
public import TauCeti.RingTheory.HochschildCohomology.Bimodule
import TauCeti.Algebra.BigOperators.NatAntidiagonal
import TauCeti.Order.Monotone.Splice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Tactic.FinCases

/-!
# Obstructions to extending formal deformations of an algebra and `HH³(A, A)`

Let `A` be an associative algebra over a commutative ring `R`. Following Gerstenhaber, a formal
deformation of `A` is a multiplication `μₜ = μ + t φ₁ + t² φ₂ + ⋯` on `A⟦t⟧`, extended
`R⟦t⟧`-bilinearly from Hochschild `2`-cochains `φᵢ` of `A` with coefficients in `A`, which is
associative. For `2`-cochains `f` and `g` write

`(f ∘ g)(a, b, c) = f(g(a, b), c) - f(a, g(b, c))`                    (`gerstenhaberComp`)

for Gerstenhaber's composition, a `3`-cochain. The associator of `μₜ` at `a, b, c ∈ A` is
`∑ₖ tᵏ ∑_{i + j = k} (φᵢ ∘ φⱼ)(a, b, c)` with `φ₀ = μ`, so `μₜ` is associative modulo `tⁿ⁺¹`
exactly when the coefficients

`∑_{i + j = k} φᵢ ∘ φⱼ`                                         (`deformationAssociator`)

vanish for `k ≤ n`. A family `φ` with `φ₀ = μ` satisfying these equations is a **deformation of
order `n`** (`IsAlgebraDeformationOfOrder`), and a **formal deformation**
(`IsFormalAlgebraDeformation`) when it is a deformation of every order. Only the coefficients
`φ₀, …, φₙ` matter for a deformation of order `n`, and the definition needs no division, so it
makes sense over every commutative ring.

Since `μ ∘ ψ + ψ ∘ μ = -δψ` for the Hochschild coboundary `δ`, the coefficient of `tⁿ⁺¹` is

`∑_{i + j = n + 1} φᵢ ∘ φⱼ = Oₙ - δφₙ₊₁`                     (`deformationAssociator_succ`)

where the **obstruction** `Oₙ = ∑_{i + j = n + 1, 1 ≤ i, j ≤ n} φᵢ ∘ φⱼ`
(`algebraDeformationObstruction`) only involves `φ₁, …, φₙ`. So the prescribed coefficient
`φₙ₊₁` extends a deformation of order `n` to order `n + 1` exactly when `δφₙ₊₁ = Oₙ`
(`IsAlgebraDeformationOfOrder.isAlgebraDeformationOfOrder_succ_iff`). For `n = 0` the obstruction
vanishes, and the deformations of order one are the Hochschild `2`-cocycles
(`isAlgebraDeformationOfOrder_one_iff`).

The obstruction of a deformation of order `n` is a Hochschild `3`-cocycle
(`IsAlgebraDeformationOfOrder.algebraDeformationObstruction_mem_hochschildBimoduleCocycles`).
This follows from the Teichmüller identity
`a [b, c, d] - [ab, c, d] + [a, bc, d] - [a, b, cd] + [a, b, c] d = 0` for the associator of an
arbitrary bilinear multiplication, in its coefficientwise form, applied to
`μ + t φ₁ + ⋯ + tⁿ φₙ`, whose associator is `tⁿ⁺¹ Oₙ` modulo `tⁿ⁺²`. So the obstruction has a
class in `HH³(A, A)` (`IsAlgebraDeformationOfOrder.obstructionClass`), and the deformation
extends to order `n + 1`, after changing only `φₙ₊₁`, exactly when this class vanishes
(`IsAlgebraDeformationOfOrder.obstructionClass_eq_zero_iff`). In particular, if `HH³(A, A) = 0`
then every deformation of order `n` extends to a formal deformation
(`IsAlgebraDeformationOfOrder.exists_isFormalAlgebraDeformation`).

The `A∞` form of this obstruction theory, with braces of suspended Hochschild cochains, is
`TauCeti.Algebra.Homology.AInfinity.Algebra.Deformation`. The classification of the deformations
of order one up to equivalence by `HH²(A, A)` is the infinitesimal half of the same theory.

Gerstenhaber's composition, the associator coefficients and the obstruction are defined for
`2`-cochains on any `R`-module `A`, since they only use the cochains themselves; the algebra
structure enters through `φ₀ = μ` and the Hochschild differential.

## Main definitions

* `MultilinearMap.gerstenhaberComp`: Gerstenhaber's composition of two `2`-cochains.
* `TauCeti.deformationAssociator`: the coefficient `∑_{i + j = k} φᵢ ∘ φⱼ` of `tᵏ` in the
  associator of `μₜ`.
* `TauCeti.IsAlgebraDeformationOfOrder`: a deformation of order `n` of `A`.
* `TauCeti.IsFormalAlgebraDeformation`: a formal deformation of `A`.
* `TauCeti.algebraDeformationObstruction`: the obstruction `Oₙ`.
* `TauCeti.IsAlgebraDeformationOfOrder.obstructionClass`: its class in `HH³(A, A)`.

## Main results

* `TauCeti.deformationAssociator_succ`: the coefficient of `tⁿ⁺¹` is `Oₙ - δφₙ₊₁`.
* `TauCeti.IsAlgebraDeformationOfOrder.isAlgebraDeformationOfOrder_succ_iff`: a deformation of
  order `n` is one of order `n + 1` exactly when `δφₙ₊₁ = Oₙ`.
* `TauCeti.isAlgebraDeformationOfOrder_one_iff`: deformations of order one are Hochschild
  `2`-cocycles.
* `TauCeti.IsAlgebraDeformationOfOrder.algebraDeformationObstruction_mem_hochschildBimoduleCocycles`
  : the obstruction is a Hochschild `3`-cocycle.
* `TauCeti.IsAlgebraDeformationOfOrder.obstructionClass_eq_zero_iff`: a deformation of order `n`
  extends to order `n + 1` exactly when its obstruction class vanishes.
* `TauCeti.IsAlgebraDeformationOfOrder.exists_isFormalAlgebraDeformation`: if `HH³(A, A) = 0`,
  every deformation of order `n` extends to a formal deformation.

## References

* M. Gerstenhaber, *On the deformation of rings and algebras*, Annals of Mathematics 79 (1964),
  59--103, Sections 1.1--1.4.
-/

public section

noncomputable section

namespace TauCeti

section Bilinear

variable {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]

/-- A `2`-cochain as a biadditive map, `a ↦ b ↦ f(a, b)`. -/
private def bilAdd (f : (Fin 2 → A) →ₘₗ[R] A) : A →+ A →+ A :=
  LinearMap.toAddMonoidHom'.comp f.toBilinMap.toAddMonoidHom

private theorem bilAdd_apply (f : (Fin 2 → A) →ₘₗ[R] A) (a b : A) :
    bilAdd f a b = f ![a, b] :=
  f.toBilinMap_apply a b

end Bilinear

section Composition

variable {R A : Type*} [CommSemiring R] [AddCommGroup A] [Module R A]

/-- **Gerstenhaber's composition** of two Hochschild `2`-cochains of `A` with coefficients in
`A`: the `3`-cochain `(f ∘ g)(a, b, c) = f(g(a, b), c) - f(a, g(b, c))`. -/
def _root_.MultilinearMap.gerstenhaberComp (f g : (Fin 2 → A) →ₘₗ[R] A) : (Fin 3 → A) →ₘₗ[R] A :=
  MultilinearMap.mk' (fun v ↦ f.toBilinMap (g.toBilinMap (v 0) (v 1)) (v 2) -
      f.toBilinMap (v 0) (g.toBilinMap (v 1) (v 2)))
    (fun v i x y ↦ by
      fin_cases i <;> simp [-MultilinearMap.toBilinMap_apply] <;> abel)
    (fun v i r x ↦ by
      fin_cases i <;> simp [-MultilinearMap.toBilinMap_apply, smul_sub])

/-- Evaluating Gerstenhaber's composition. -/
@[simp]
theorem _root_.MultilinearMap.gerstenhaberComp_apply (f g : (Fin 2 → A) →ₘₗ[R] A)
    (v : Fin 3 → A) :
    f.gerstenhaberComp g v = f ![g ![v 0, v 1], v 2] - f ![v 0, g ![v 1, v 2]] := by
  simp [MultilinearMap.gerstenhaberComp]


/-! ### The associator coefficients and the obstruction of a family of cochains -/

/-- Gerstenhaber's composition vanishes when its first argument does. -/
@[simp]
theorem _root_.MultilinearMap.gerstenhaberComp_zero_left (g : (Fin 2 → A) →ₘₗ[R] A) :
    (0 : (Fin 2 → A) →ₘₗ[R] A).gerstenhaberComp g = 0 := by
  ext v
  simp [MultilinearMap.gerstenhaberComp_apply]

/-- Gerstenhaber's composition vanishes when its second argument does. -/
@[simp]
theorem _root_.MultilinearMap.gerstenhaberComp_zero_right (f : (Fin 2 → A) →ₘₗ[R] A) :
    f.gerstenhaberComp 0 = 0 := by
  ext v
  have h : ∀ x : A, f ![0, x] = 0 := fun x ↦ f.map_coord_zero 0 rfl
  have h' : ∀ x : A, f ![x, 0] = 0 := fun x ↦ f.map_coord_zero 1 rfl
  simp [MultilinearMap.gerstenhaberComp_apply, h, h']

/-- Gerstenhaber's composition is additive in its first argument. -/
@[simp]
theorem _root_.MultilinearMap.gerstenhaberComp_add_left (f f' g : (Fin 2 → A) →ₘₗ[R] A) :
    (f + f').gerstenhaberComp g = f.gerstenhaberComp g + f'.gerstenhaberComp g := by
  ext v
  simp only [MultilinearMap.gerstenhaberComp_apply, add_apply]
  abel

/-- Gerstenhaber's composition is additive in its second argument. -/
@[simp]
theorem _root_.MultilinearMap.gerstenhaberComp_add_right (f g g' : (Fin 2 → A) →ₘₗ[R] A) :
    f.gerstenhaberComp (g + g') = f.gerstenhaberComp g + f.gerstenhaberComp g' := by
  ext v
  simp only [MultilinearMap.gerstenhaberComp_apply, add_apply, ← MultilinearMap.toBilinMap_apply,
    map_add, LinearMap.add_apply]
  abel

/-- Gerstenhaber's composition is `R`-linear in its first argument. -/
@[simp]
theorem _root_.MultilinearMap.gerstenhaberComp_smul_left (c : R)
    (f g : (Fin 2 → A) →ₘₗ[R] A) :
    (c • f).gerstenhaberComp g = c • f.gerstenhaberComp g := by
  ext v
  simp only [MultilinearMap.gerstenhaberComp_apply, smul_apply, smul_sub]

/-- Gerstenhaber's composition is `R`-linear in its second argument. -/
@[simp]
theorem _root_.MultilinearMap.gerstenhaberComp_smul_right (c : R)
    (f g : (Fin 2 → A) →ₘₗ[R] A) :
    f.gerstenhaberComp (c • g) = c • f.gerstenhaberComp g := by
  ext v
  simp only [MultilinearMap.gerstenhaberComp_apply, smul_apply, ← MultilinearMap.toBilinMap_apply,
    map_smul, LinearMap.smul_apply, smul_sub]

/-- The coefficient `∑_{i + j = k} φᵢ ∘ φⱼ` of `tᵏ` in the associator of the multiplication
`μₜ = ∑ tⁱ φᵢ`, Gerstenhaber's composition `∘` being `MultilinearMap.gerstenhaberComp`. -/
def deformationAssociator (φ : ℕ → (Fin 2 → A) →ₘₗ[R] A) (k : ℕ) : (Fin 3 → A) →ₘₗ[R] A :=
  ∑ x ∈ Finset.antidiagonal k, MultilinearMap.gerstenhaberComp (φ x.1) (φ x.2)

/-- Unfolding `TauCeti.deformationAssociator`. -/
theorem deformationAssociator_def (φ : ℕ → (Fin 2 → A) →ₘₗ[R] A) (k : ℕ) :
    deformationAssociator φ k =
      ∑ x ∈ Finset.antidiagonal k, (φ x.1).gerstenhaberComp (φ x.2) :=
  (rfl)

/-- Evaluating the coefficients of the associator. -/
theorem deformationAssociator_apply (φ : ℕ → (Fin 2 → A) →ₘₗ[R] A) (k : ℕ) (v : Fin 3 → A) :
    deformationAssociator φ k v = ∑ x ∈ Finset.antidiagonal k,
      (φ x.1 ![φ x.2 ![v 0, v 1], v 2] - φ x.1 ![v 0, φ x.2 ![v 1, v 2]]) := by
  simp [deformationAssociator_def, MultilinearMap.gerstenhaberComp_apply]

/-- The coefficient of `tᵏ` only depends on the coefficients `φ 0, …, φ k`. -/
theorem deformationAssociator_congr {φ ψ : ℕ → (Fin 2 → A) →ₘₗ[R] A} {k : ℕ}
    (h : ∀ i ≤ k, φ i = ψ i) : deformationAssociator φ k = deformationAssociator ψ k := by
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [h x.1 (by omega), h x.2 (by omega)]

/-- The **obstruction** to extending a deformation of order `n` to order `n + 1`: the
coefficient `∑_{i + j = n + 1, 1 ≤ i, j ≤ n} φᵢ ∘ φⱼ` of `tⁿ⁺¹` in the associator of the
truncated multiplication `∑_{i ≤ n} tⁱ φᵢ`. -/
def algebraDeformationObstruction (φ : ℕ → (Fin 2 → A) →ₘₗ[R] A) (n : ℕ) :
    (Fin 3 → A) →ₘₗ[R] A :=
  deformationAssociator (fun i ↦ if i ≤ n then φ i else 0) (n + 1)

/-- Unfolding `TauCeti.algebraDeformationObstruction`. -/
theorem algebraDeformationObstruction_def (φ : ℕ → (Fin 2 → A) →ₘₗ[R] A) (n : ℕ) :
    algebraDeformationObstruction φ n =
      deformationAssociator (fun i ↦ if i ≤ n then φ i else 0) (n + 1) :=
  (rfl)

/-- The obstruction only depends on the coefficients `φ 1, …, φ n`. -/
theorem algebraDeformationObstruction_congr {φ ψ : ℕ → (Fin 2 → A) →ₘₗ[R] A} {n : ℕ}
    (h : ∀ i, 1 ≤ i → i ≤ n → φ i = ψ i) :
    algebraDeformationObstruction φ n = algebraDeformationObstruction ψ n := by
  rw [algebraDeformationObstruction_def, algebraDeformationObstruction_def]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finset.mem_antidiagonal] at hx
  by_cases h₁ : x.1 = 0
  · have h₂ : ¬ x.2 ≤ n := by omega
    simp [h₂]
  by_cases h₂ : x.2 = 0
  · have h₁' : ¬ x.1 ≤ n := by omega
    simp [h₁']
  have h₁' : x.1 ≤ n := by omega
  have h₂' : x.2 ≤ n := by omega
  simp only [h₁', h₂', ite_true]
  rw [h x.1 (by omega) h₁', h x.2 (by omega) h₂']

/-- The obstruction `O₀` vanishes: a deformation of order zero meets no obstruction to extending
to order one. -/
@[simp]
theorem algebraDeformationObstruction_zero (φ : ℕ → (Fin 2 → A) →ₘₗ[R] A) :
    algebraDeformationObstruction φ 0 = 0 := by
  simp [algebraDeformationObstruction_def, deformationAssociator_def,
    Finset.Nat.sum_antidiagonal_succ]

end Composition

open MultilinearMap (gerstenhaberComp gerstenhaberComp_apply gerstenhaberComp_zero_left
  gerstenhaberComp_zero_right)


/-- **The Teichmüller identity, coefficientwise.** Let `μₜ = ∑ tⁱ ψᵢ` be a power series of
biadditive operations on `M`, and let `Φ q` be the coefficient of `t^q` in its associator
`[x, y, z] = μₜ(μₜ(x, y), z) - μₜ(x, μₜ(y, z))`. Then the coefficient of `t^N` in
`a [b, c, d] - [ab, c, d] + [a, bc, d] - [a, b, cd] + [a, b, c] d` vanishes. -/
private theorem sum_antidiagonal_teichmuller {M : Type*} [AddCommGroup M] (ψ : ℕ → M →+ M →+ M)
    (Φ : ℕ → M → M → M → M)
    (hΦ : ∀ q x y z, Φ q x y z =
      ∑ w ∈ Finset.antidiagonal q, (ψ w.1 (ψ w.2 x y) z - ψ w.1 x (ψ w.2 y z)))
    (N : ℕ) (a b c d : M) :
    ∑ x ∈ Finset.antidiagonal N, (ψ x.1 a (Φ x.2 b c d) - Φ x.2 (ψ x.1 a b) c d +
      Φ x.2 a (ψ x.1 b c) d - Φ x.2 a b (ψ x.1 c d) + ψ x.1 (Φ x.2 a b c) d) = 0 := by
  simp only [hΦ, map_sum, map_sub, AddMonoidHom.finsetSum_apply, AddMonoidHom.sub_apply,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- The ten triple sums cancel in pairs after permuting their indices.
  have e₁ := Finset.Nat.sum_antidiagonal_sum_antidiagonal_cycle N
    fun p i j ↦ ψ p a (ψ i (ψ j b c) d)
  have e₂ := Finset.Nat.sum_antidiagonal_sum_antidiagonal_cycle N
    fun p i j ↦ ψ p a (ψ i b (ψ j c d))
  have e₃ := Finset.Nat.sum_antidiagonal_sum_antidiagonal_cycle N
    fun p i j ↦ ψ p (ψ i (ψ j a b) c) d
  have e₄ := Finset.Nat.sum_antidiagonal_sum_antidiagonal_cycle N
    fun p i j ↦ ψ p (ψ i a (ψ j b c)) d
  have e₅ := Finset.Nat.sum_antidiagonal_sum_antidiagonal_cycle N
    fun p i j ↦ ψ i (ψ p a b) (ψ j c d)
  have e₆ := Finset.Nat.sum_antidiagonal_sum_antidiagonal_swap N
    fun p i j ↦ ψ i (ψ j a b) (ψ p c d)
  rw [e₁, e₂, e₃, e₄, ← e₅, e₆]
  abel

section Coboundary

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]


/-- The coboundary of a `2`-cochain with coefficients in `A`:
`(δψ)(a, b, c) = a ψ(b, c) - ψ(ab, c) + ψ(a, bc) - ψ(a, b) c`. -/
private theorem coboundary_two_apply (ψ : (Fin 2 → A) →ₘₗ[R] A) (a b c : A) :
    hochschildBimoduleCoboundary R A A 2 ψ ![a, b, c] =
      a * ψ ![b, c] - ψ ![a * b, c] + ψ ![a, b * c] - ψ ![a, b] * c := by
  have h₀ : Fin.contractNth 0 (· * ·) ![a, b, c] = ![a * b, c] := by
    ext i
    fin_cases i <;> simp [Fin.contractNth]
  have h₁ : Fin.contractNth 1 (· * ·) ![a, b, c] = ![a, b * c] := by
    ext i
    fin_cases i <;> simp [Fin.contractNth]
  have h₂ : Fin.init ![a, b, c] = ![a, b] := by
    ext i
    fin_cases i <;> simp [Fin.init]
  rw [hochschildBimoduleCoboundary_apply_eq_add_sum_add, Fin.sum_univ_two]
  simp [h₀, h₁, h₂, sub_eq_add_neg, add_assoc]

end Coboundary

section Deformation

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- Composing with the multiplication on either side gives minus the Hochschild coboundary:
`μ ∘ ψ + ψ ∘ μ = -δψ`. -/
theorem _root_.MultilinearMap.mkPiAlgebraFin_gerstenhaberComp_add_gerstenhaberComp_mkPiAlgebraFin
    (ψ : (Fin 2 → A) →ₘₗ[R] A) :
    gerstenhaberComp (MultilinearMap.mkPiAlgebraFin R 2 A) ψ +
        gerstenhaberComp ψ (MultilinearMap.mkPiAlgebraFin R 2 A) =
      -hochschildBimoduleCoboundary R A A 2 ψ := by
  ext v
  rw [show v = ![v 0, v 1, v 2] from (FinVec.etaExpand_eq v).symm, neg_apply,
    coboundary_two_apply]
  simp [gerstenhaberComp_apply]
  abel

variable (R A) in
/-- The family `φ` is a **deformation of order `n`** of the algebra `A`: the multiplication
`μₜ = ∑ tⁱ φᵢ`, extended bilinearly to `A⟦t⟧`, reduces to the multiplication of `A` modulo `t`
and is associative modulo `tⁿ⁺¹`. Only the coefficients `φ 0, …, φ n` matter
(`IsAlgebraDeformationOfOrder.congr`). -/
structure IsAlgebraDeformationOfOrder (n : ℕ) (φ : ℕ → (Fin 2 → A) →ₘₗ[R] A) : Prop where
  /-- The constant term is the multiplication of `A`. -/
  zero_eq : φ 0 = MultilinearMap.mkPiAlgebraFin R 2 A
  /-- The multiplication `μₜ` is associative modulo `tⁿ⁺¹`. -/
  deformationAssociator_eq_zero : ∀ k ≤ n, deformationAssociator φ k = 0

variable (R A) in
/-- The family `φ` is a **formal deformation** of the algebra `A`: the multiplication
`μₜ = ∑ tⁱ φᵢ` on `A⟦t⟧` reduces to the multiplication of `A` modulo `t` and is associative. -/
def IsFormalAlgebraDeformation (φ : ℕ → (Fin 2 → A) →ₘₗ[R] A) : Prop :=
  ∀ n, IsAlgebraDeformationOfOrder R A n φ

/-- Unfolding `TauCeti.IsFormalAlgebraDeformation`. -/
theorem isFormalAlgebraDeformation_iff {φ : ℕ → (Fin 2 → A) →ₘₗ[R] A} :
    IsFormalAlgebraDeformation R A φ ↔ ∀ n, IsAlgebraDeformationOfOrder R A n φ :=
  Iff.rfl

/-- A deformation of order `n` is one of every smaller order. -/
theorem IsAlgebraDeformationOfOrder.mono {n n' : ℕ} {φ : ℕ → (Fin 2 → A) →ₘₗ[R] A}
    (h : IsAlgebraDeformationOfOrder R A n' φ) (hn : n ≤ n') :
    IsAlgebraDeformationOfOrder R A n φ :=
  ⟨h.zero_eq, fun k hk ↦ h.deformationAssociator_eq_zero k (hk.trans hn)⟩

/-- Being a deformation of order `n` only depends on the coefficients `φ 0, …, φ n`. -/
theorem IsAlgebraDeformationOfOrder.congr {n : ℕ} {φ ψ : ℕ → (Fin 2 → A) →ₘₗ[R] A}
    (h : IsAlgebraDeformationOfOrder R A n φ) (hφψ : ∀ i ≤ n, φ i = ψ i) :
    IsAlgebraDeformationOfOrder R A n ψ :=
  ⟨hφψ 0 (Nat.zero_le n) ▸ h.zero_eq, fun k hk ↦ by
    rw [← deformationAssociator_congr fun i hi ↦ hφψ i (hi.trans hk)]
    exact h.deformationAssociator_eq_zero k hk⟩

/-- A deformation of order zero is a family with constant term `μ`: modulo `t`, the
associativity of `μₜ` is that of `μ`. -/
@[simp]
theorem isAlgebraDeformationOfOrder_zero_iff {φ : ℕ → (Fin 2 → A) →ₘₗ[R] A} :
    IsAlgebraDeformationOfOrder R A 0 φ ↔ φ 0 = MultilinearMap.mkPiAlgebraFin R 2 A := by
  refine ⟨fun h ↦ h.zero_eq, fun h ↦ ⟨h, fun k hk ↦ ?_⟩⟩
  rw [Nat.le_zero.1 hk]
  ext v
  simp [deformationAssociator_apply, h, mul_assoc]

/-- **The coefficient of `tⁿ⁺¹` in the associator** of `μₜ` is the obstruction of the
truncation at order `n` minus the Hochschild coboundary of `φ (n + 1)`. -/
theorem deformationAssociator_succ {φ : ℕ → (Fin 2 → A) →ₘₗ[R] A}
    (h₀ : φ 0 = MultilinearMap.mkPiAlgebraFin R 2 A) (n : ℕ) :
    deformationAssociator φ (n + 1) =
      algebraDeformationObstruction φ n - hochschildBimoduleCoboundary R A A 2 (φ (n + 1)) := by
  -- Only the two extreme terms `μ ∘ φ (n + 1)` and `φ (n + 1) ∘ μ` involve `φ (n + 1)`.
  have key : ∀ x ∈ Finset.antidiagonal (n + 1), gerstenhaberComp (φ x.1) (φ x.2) =
      gerstenhaberComp (if x.1 ≤ n then φ x.1 else 0) (if x.2 ≤ n then φ x.2 else 0) +
        ((if x = (0, n + 1) then gerstenhaberComp (φ 0) (φ (n + 1)) else 0) +
          (if x = (n + 1, 0) then gerstenhaberComp (φ (n + 1)) (φ 0) else 0)) := by
    rintro ⟨a, b⟩ hx
    rw [Finset.mem_antidiagonal] at hx
    dsimp only
    by_cases ha : a = 0
    · obtain rfl : b = n + 1 := by omega
      simp [ha]
    by_cases hb : b = 0
    · obtain rfl : a = n + 1 := by omega
      simp [hb]
    · have ha' : a ≤ n := by omega
      have hb' : b ≤ n := by omega
      simp [ha, hb, ha', hb']
  rw [deformationAssociator_def, Finset.sum_congr rfl key, Finset.sum_add_distrib,
    Finset.sum_add_distrib, algebraDeformationObstruction_def, deformationAssociator_def,
    sub_eq_add_neg,
    ← MultilinearMap.mkPiAlgebraFin_gerstenhaberComp_add_gerstenhaberComp_mkPiAlgebraFin, ← h₀]
  simp

/-- **Extending a deformation by one order.** A deformation of order `n` is a deformation of
order `n + 1` exactly when the Hochschild coboundary of `φ (n + 1)` is the obstruction. -/
theorem IsAlgebraDeformationOfOrder.isAlgebraDeformationOfOrder_succ_iff {n : ℕ}
    {φ : ℕ → (Fin 2 → A) →ₘₗ[R] A} (h : IsAlgebraDeformationOfOrder R A n φ) :
    IsAlgebraDeformationOfOrder R A (n + 1) φ ↔
      hochschildBimoduleCoboundary R A A 2 (φ (n + 1)) = algebraDeformationObstruction φ n := by
  refine ⟨fun h' ↦ ?_, fun hd ↦ ⟨h.zero_eq, fun k hk ↦ ?_⟩⟩
  · rw [eq_comm, ← sub_eq_zero, ← deformationAssociator_succ h.zero_eq]
    exact h'.deformationAssociator_eq_zero (n + 1) le_rfl
  · rcases Nat.lt_or_eq_of_le hk with hk | rfl
    · exact h.deformationAssociator_eq_zero k (Nat.lt_succ_iff.1 hk)
    · rw [deformationAssociator_succ h.zero_eq, hd, sub_self]

/-- **Deformations of order one are Hochschild cocycles.** A family is a deformation of order
one exactly when its constant term is `μ` and `φ 1` is a Hochschild `2`-cocycle. -/
theorem isAlgebraDeformationOfOrder_one_iff {φ : ℕ → (Fin 2 → A) →ₘₗ[R] A} :
    IsAlgebraDeformationOfOrder R A 1 φ ↔
      φ 0 = MultilinearMap.mkPiAlgebraFin R 2 A ∧ φ 1 ∈ hochschildBimoduleCocycles R A A 2 := by
  refine ⟨fun h ↦ ⟨h.zero_eq, ?_⟩, fun ⟨h₀, h₁⟩ ↦ ?_⟩
  · have := (isAlgebraDeformationOfOrder_zero_iff.2 h.zero_eq).isAlgebraDeformationOfOrder_succ_iff
    rw [mem_hochschildBimoduleCocycles_iff, ← algebraDeformationObstruction_zero φ]
    exact this.1 h
  · refine ((isAlgebraDeformationOfOrder_zero_iff.2 h₀).isAlgebraDeformationOfOrder_succ_iff).2 ?_
    rwa [algebraDeformationObstruction_zero, ← mem_hochschildBimoduleCocycles_iff]

/-- **The obstruction is a Hochschild cocycle.** For a deformation of order `n`, the obstruction
to extending it to order `n + 1` is a Hochschild `3`-cocycle. -/
theorem IsAlgebraDeformationOfOrder.algebraDeformationObstruction_mem_hochschildBimoduleCocycles
    {n : ℕ} {φ : ℕ → (Fin 2 → A) →ₘₗ[R] A} (h : IsAlgebraDeformationOfOrder R A n φ) :
    algebraDeformationObstruction φ n ∈ hochschildBimoduleCocycles R A A 3 := by
  -- We apply the Teichmüller identity to the truncated multiplication `∑_{i ≤ n} tⁱ φᵢ`, whose
  -- associator vanishes modulo `tⁿ⁺¹` and has coefficient `Oₙ` at `tⁿ⁺¹`.
  set φ' : ℕ → (Fin 2 → A) →ₘₗ[R] A := fun i ↦ if i ≤ n then φ i else 0 with hφ'
  set Φ : ℕ → A → A → A → A := fun q x y z ↦ deformationAssociator φ' q ![x, y, z] with hΦ
  have hzero {q : ℕ} (hq : q ≤ n) (x y z : A) : Φ q x y z = 0 := by
    simp only [hΦ]
    rw [deformationAssociator_congr (ψ := φ) fun i hi ↦ by simp [hφ', hi.trans hq],
      h.deformationAssociator_eq_zero q hq, zero_apply]
  have key := sum_antidiagonal_teichmuller (fun i ↦ bilAdd (φ' i)) Φ
    (fun q x y z ↦ by simp [hΦ, deformationAssociator_apply, bilAdd_apply]) (n + 1)
  rw [mem_hochschildBimoduleCocycles_iff]
  ext v
  have hv : v = ![v 0, v 1, v 2, v 3] := (FinVec.etaExpand_eq v).symm
  have e := key (v 0) (v 1) (v 2) (v 3)
  rw [Finset.Nat.sum_antidiagonal_succ, Finset.sum_eq_zero fun x hx ↦ by
    have hx2 : x.2 ≤ n := by rw [Finset.mem_antidiagonal] at hx; omega
    simp [hzero hx2], add_zero] at e
  rw [hv, hochschildBimoduleCoboundary_three_apply, zero_apply, ← e]
  simp [bilAdd_apply, hφ', hΦ, h.zero_eq, algebraDeformationObstruction_def,
    smul_eq_mul]

end Deformation

section Cohomology

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The **obstruction class** of a deformation of order `n`: the class in `HH³(A, A)` of the
obstruction to extending it to order `n + 1`. -/
def IsAlgebraDeformationOfOrder.obstructionClass {n : ℕ} {φ : ℕ → (Fin 2 → A) →ₘₗ[R] A}
    (h : IsAlgebraDeformationOfOrder R A n φ) : hochschildBimoduleCohomology R A A 3 :=
  hochschildBimoduleCohomology.mk R A A 3
    ⟨_, h.algebraDeformationObstruction_mem_hochschildBimoduleCocycles⟩

/-- Unfolding `TauCeti.IsAlgebraDeformationOfOrder.obstructionClass`. -/
theorem IsAlgebraDeformationOfOrder.obstructionClass_def {n : ℕ}
    {φ : ℕ → (Fin 2 → A) →ₘₗ[R] A} (h : IsAlgebraDeformationOfOrder R A n φ) :
    h.obstructionClass = hochschildBimoduleCohomology.mk R A A 3
      ⟨_, h.algebraDeformationObstruction_mem_hochschildBimoduleCocycles⟩ :=
  (rfl)

/-- **The obstruction class is the obstruction to extension.** A deformation of order `n`
extends to a deformation of order `n + 1` with the same coefficients up to order `n` exactly
when its obstruction class in `HH³(A, A)` vanishes. -/
theorem IsAlgebraDeformationOfOrder.obstructionClass_eq_zero_iff {n : ℕ}
    {φ : ℕ → (Fin 2 → A) →ₘₗ[R] A} (h : IsAlgebraDeformationOfOrder R A n φ) :
    h.obstructionClass = 0 ↔
      ∃ ψ, IsAlgebraDeformationOfOrder R A (n + 1) (Function.update φ (n + 1) ψ) := by
  have hagree (ψ : (Fin 2 → A) →ₘₗ[R] A) :
      ∀ i ≤ n, φ i = Function.update φ (n + 1) ψ i := fun i hi ↦
    (Function.update_of_ne (a' := n + 1) (by omega) ψ φ).symm
  simp_rw [fun ψ ↦ (h.congr (hagree ψ)).isAlgebraDeformationOfOrder_succ_iff,
    Function.update_self, ← algebraDeformationObstruction_congr fun i _ hi ↦ hagree _ i hi]
  rw [obstructionClass_def, hochschildBimoduleCohomology.mk_eq_zero_iff]
  exact mem_hochschildBimoduleCoboundaries_succ_iff (n := 2)

/-- **Unobstructedness.** If `HH³(A, A)` vanishes, every deformation of order `n` extends to a
formal deformation with the same coefficients up to order `n`. -/
theorem IsAlgebraDeformationOfOrder.exists_isFormalAlgebraDeformation
    [Subsingleton (hochschildBimoduleCohomology R A A 3)] {n : ℕ}
    {φ : ℕ → (Fin 2 → A) →ₘₗ[R] A} (h : IsAlgebraDeformationOfOrder R A n φ) :
    ∃ φ', IsFormalAlgebraDeformation R A φ' ∧ ∀ i ≤ n, φ' i = φ i := by
  -- Every deformation of order `m` extends by one order without changing its coefficients up to
  -- order `m`, since its obstruction class vanishes.
  have step (m : ℕ) (χ : {χ // IsAlgebraDeformationOfOrder R A m χ}) :
      ∃ χ', IsAlgebraDeformationOfOrder R A (m + 1) χ' ∧ ∀ i ≤ m, χ' i = χ.val i := by
    obtain ⟨ψ, hψ⟩ := (χ.property.obstructionClass_eq_zero_iff).1 (Subsingleton.elim _ _)
    exact ⟨_, hψ, fun i hi ↦ Function.update_of_ne (a' := m + 1) (by omega) ψ χ.val⟩
  choose next hnext hagree using step
  -- Extend `φ` one order at a time.
  let seq : (j : ℕ) → {χ // IsAlgebraDeformationOfOrder R A (n + j) χ} :=
    fun j ↦ Nat.rec ⟨φ, h⟩ (fun j χ ↦ ⟨next (n + j) χ, hnext (n + j) χ⟩) j
  -- The stages agree on ever longer initial segments, so they splice into one sequence.
  obtain ⟨φ', hφ'⟩ := exists_forall_lt_eq_of_strictMono (fun j ↦ (seq j).val)
    (N := fun j ↦ n + j + 1) (fun _ _ hj ↦ by dsimp only; omega)
    fun j i hi ↦ hagree _ _ i (by omega)
  refine ⟨φ', fun m ↦ ?_, fun i hi ↦ hφ' 0 i (by omega)⟩
  exact ((seq m).property.mono (by omega)).congr fun i hi ↦ (hφ' m i (by omega)).symm

end Cohomology

end TauCeti
