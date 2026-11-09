/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Algebra.Order.Star.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.Algebra.Ring.Hom

/-!
# The standard sesquilinear form with a specified twist

For a ring endomorphism `σ`, the form `sesquilinearForm σ` is linear in its first argument and
`σ`-semilinear in its second: `h(x,y) = ∑ i, x i * σ (y i)`. It is nondegenerate when `σ` is
injective, and for an automorphism `σ` it identifies the second coordinate space semilinearly
with the dual of the first. When `σ` is involutive, the form has Hermitian symmetry. This
orientation is useful for Hermitian duals of codes over finite fields.

This identification with the dual gives a nondegenerate pairing for studying orthogonality
in finite coordinate spaces.

The API is in `RingHom`: use `σ.sesquilinearForm`, or `RingHom.sesquilinearForm σ`. Results that
need an automorphism are in `RingEquiv`.

For a module with a finite basis `b`, Mathlib's `Matrix.toLinearMapₛₗ₂ σ b b 1` is the
sesquilinear form, `σ`-semilinear in its first argument, for which `b` is orthonormal. In
coordinates it is `∑ i, σ (x i) * y i` (`Matrix.toLinearMapₛₗ₂_one_apply`). For complex
conjugation, or any star ring, it is Hermitian (`Matrix.star_toLinearMapₛₗ₂_one_apply`), and over
a star-ordered ring without zero divisors it is positive definite
(`Matrix.toLinearMapₛₗ₂_one_self_nonneg`, `Matrix.toLinearMapₛₗ₂_one_self_eq_zero_iff`). This is
the Hermitian metric making a chosen basis orthonormal, for instance the increasing wedge basis of
an exterior algebra.

More generally, for a ring endomorphism `σ` and a Gram matrix `Q`, write
`B(x, y) = σ(x)ᵀ Q y` for the coordinate form `(σ ∘ x) ⬝ᵥ (Q *ᵥ y)`. A matrix `g` with
`σ(g)ᵀ Q g = Q` preserves it (`Matrix.comp_mulVec_dotProduct_mulVec_mulVec`), and if `σ` is an
involution and `σ(Q)ᵀ = ε Q`, it is `ε`-Hermitian, `σ(B(x, y)) = ε B(y, x)`
(`Matrix.apply_comp_dotProduct_mulVec`). With `ε * ε = 1`, this gives `B(y, x) = ε σ(B(x, y))`
(`Matrix.comp_dotProduct_mulVec_swap`) and a formula for `B(u + c x, u + c x)` when `x` is
isotropic (`Matrix.comp_add_smul_dotProduct_mulVec_add_smul`).

Over a field, if the trace `t ↦ t + ε σ(t)` is onto the elements `s` with `σ(s) = ε s`, a vector
`u` with `B(u, x) ≠ 0` corrects to an isotropic `u + c x`
(`Matrix.exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero`). For invertible `Q`, any two
nonzero vectors pair nontrivially with a common vector
(`Matrix.exists_comp_dotProduct_mulVec_ne_zero_pair`). If moreover the trace has a nonzero kernel
element and some nonzero vector is isotropic, a matrix scaling every isotropic vector is scalar
(`Matrix.exists_eq_scalar_of_forall_mulVec_eq_smul`).
-/

public section

namespace RingHom

open Matrix

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- The standard sesquilinear form, linear in the first argument and twisted by `σ`
in the second. It is Hermitian when `σ` is involutive. -/
noncomputable def sesquilinearForm (σ : R →+* R) :
    (ι → R) →ₗ[R] (ι → R) →ₛₗ[σ] R := by
  classical
  exact Matrix.toLinearMapₛₗ₂' R (RingHom.id R) σ 1

/-- The standard sesquilinear form evaluates as the coordinate sum `∑ i, x i * σ (y i)`. -/
@[simp]
theorem sesquilinearForm_apply (σ : R →+* R) (x y : ι → R) :
    sesquilinearForm σ x y = ∑ i, x i * σ (y i) := by
  classical
  unfold sesquilinearForm
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp [Matrix.one_apply, smul_eq_mul]

/-- For an involutive endomorphism, swapping the arguments conjugates the value. -/
theorem sesquilinearForm_swap (σ : R →+* R) (hσ : Function.Involutive σ) (x y : ι → R) :
    sesquilinearForm σ y x = σ (sesquilinearForm σ x y) := by
  simp [hσ _, mul_comm]

/-- The standard sesquilinear form is nondegenerate over any commutative semiring when the
twist is injective. -/
theorem nondegenerate_sesquilinearForm (σ : R →+* R) (hσ : Function.Injective σ) :
    (sesquilinearForm σ (ι := ι)).Nondegenerate := by
  classical
  constructor
  · intro x hx
    ext i
    simpa [Pi.single_apply] using hx (Pi.single i 1)
  · intro y hy
    ext i
    refine hσ ((?_ : σ (y i) = 0).trans σ.map_zero.symm)
    simpa [Pi.single_apply] using hy (Pi.single i 1)

end RingHom

namespace RingEquiv

open Matrix

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- Swapping the arguments and inverting the automorphism applies the inverse automorphism
to the value of the standard sesquilinear form. -/
theorem sesquilinearForm_symm_swap (σ : R ≃+* R) (x y : ι → R) :
    (σ.symm : R →+* R).sesquilinearForm y x = σ.symm ((σ : R →+* R).sesquilinearForm x y) := by
  simp [mul_comm]

/-- The second argument of the standard sesquilinear form identifies the coordinate space
with its dual. -/
theorem sesquilinearForm_flip_bijective (σ : R ≃+* R) :
    Function.Bijective ((σ : R →+* R).sesquilinearForm (ι := ι)).flip := by
  classical
  constructor
  · intro x y h
    ext i
    apply σ.injective
    simpa [Pi.single_apply] using LinearMap.congr_fun h (Pi.single i 1)
  · intro f
    obtain ⟨y, rfl⟩ := (dotProductEquiv R ι).surjective f
    refine ⟨fun i ↦ σ.symm (y i), ?_⟩
    ext x
    simp [dotProduct, mul_comm]

end RingEquiv

namespace Matrix

section GramMatrix

variable {R n : Type*} [CommSemiring R] [Fintype n] {Q : Matrix n n R} {σ : R →+* R}

/-- **A matrix preserving the form preserves its values.** For the `σ`-sesquilinear form
`B(x, y) = σ(x)ᵀ Q y` of Gram matrix `Q`, if `σ(g)ᵀ Q g = Q`, then `B(g x, g y) = B(x, y)`. -/
theorem comp_mulVec_dotProduct_mulVec_mulVec {g : Matrix n n R} (hg : (g.map σ)ᵀ * Q * g = Q)
    (x y : n → R) :
    (σ ∘ (g *ᵥ x)) ⬝ᵥ (Q *ᵥ (g *ᵥ y)) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y) := by
  rw [(funext (σ.map_mulVec g x) : σ ∘ (g *ᵥ x) = _), ← vecMul_transpose, mulVec_mulVec,
    dotProduct_mulVec, vecMul_vecMul, ← Matrix.mul_assoc, hg, ← dotProduct_mulVec]

/-- **An `ε`-Hermitian form.** For the `σ`-sesquilinear form `B(x, y) = σ(x)ᵀ Q y` of Gram matrix
`Q`, if `σ` is an involution and `σ(Q)ᵀ = ε Q`, then `σ(B(x, y)) = ε B(y, x)`. -/
theorem apply_comp_dotProduct_mulVec (hσ : Function.Involutive σ) {ε : R}
    (hQ : (Q.map σ)ᵀ = ε • Q) (x y : n → R) :
    σ ((σ ∘ x) ⬝ᵥ (Q *ᵥ y)) = ε * ((σ ∘ y) ⬝ᵥ (Q *ᵥ x)) := by
  rw [RingHom.map_dotProduct, (funext (σ.map_mulVec Q y) : σ ∘ (Q *ᵥ y) = _),
    ← Function.comp_assoc, hσ.comp_self, Function.id_comp, dotProduct_mulVec, ← mulVec_transpose,
    hQ, smul_mulVec, smul_dotProduct, smul_eq_mul, dotProduct_comm]

/-- The form is additive in its first argument. -/
theorem comp_add_dotProduct_mulVec (u v w : n → R) :
    (σ ∘ (u + v)) ⬝ᵥ (Q *ᵥ w) = (σ ∘ u) ⬝ᵥ (Q *ᵥ w) + (σ ∘ v) ⬝ᵥ (Q *ᵥ w) := by
  rw [← add_dotProduct]
  exact congrArg (· ⬝ᵥ (Q *ᵥ w)) (funext fun i ↦ map_add σ _ _)

/-- With `ε * ε = 1`, the form is `ε`-Hermitian in the form `B(y, x) = ε σ(B(x, y))`. -/
theorem comp_dotProduct_mulVec_swap (hσ : Function.Involutive σ) {ε : R}
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (x y : n → R) :
    (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = ε * σ ((σ ∘ x) ⬝ᵥ (Q *ᵥ y)) := by
  rw [apply_comp_dotProduct_mulVec hσ hQ, ← mul_assoc, hε, one_mul]

/-- The value of the form at `u + c • x` for an isotropic `x`. -/
theorem comp_add_smul_dotProduct_mulVec_add_smul (hσ : Function.Involutive σ) {ε : R}
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {x : n → R} (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0)
    (u : n → R) (c : R) :
    (σ ∘ (u + c • x)) ⬝ᵥ (Q *ᵥ (u + c • x)) = (σ ∘ u) ⬝ᵥ (Q *ᵥ u) +
      (c * ((σ ∘ u) ⬝ᵥ (Q *ᵥ x)) + ε * σ (c * ((σ ∘ u) ⬝ᵥ (Q *ᵥ x)))) := by
  rw [comp_add_dotProduct_mulVec, TauCeti.map_comp_smul, mulVec_add, mulVec_smul, dotProduct_add,
    dotProduct_add, smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, hx,
    comp_dotProduct_mulVec_swap hσ hQ hε u x, map_mul]
  simp only [smul_eq_mul, mul_zero]
  ring

end GramMatrix

section Field

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

omit [DecidableEq n] in
/-- **Correcting a vector to an isotropic one.** If the trace `t ↦ t + ε σ(t)` is onto the
elements `s` with `σ(s) = ε s`, then for isotropic `x` and `B(u, x) ≠ 0` some `u + c • x` is
isotropic. -/
theorem exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) {x : n → K}
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) {u : n → K} (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    ∃ c : K, (σ ∘ (u + c • x)) ⬝ᵥ (Q *ᵥ (u + c • x)) = 0 := by
  obtain ⟨t, ht⟩ := htr (-((σ ∘ u) ⬝ᵥ (Q *ᵥ u))) <| by
    rw [map_neg, apply_comp_dotProduct_mulVec hσ hQ, mul_neg]
  refine ⟨t / (σ ∘ u) ⬝ᵥ (Q *ᵥ x), ?_⟩
  rw [comp_add_smul_dotProduct_mulVec_add_smul hσ hQ hε hx, div_mul_cancel₀ _ hux, ht,
    add_neg_cancel]

/-- For an invertible `Q`, two nonzero vectors pair nontrivially with a common vector. -/
theorem exists_comp_dotProduct_mulVec_ne_zero_pair (hdet : Q.det ≠ 0) {x y : n → K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ u : n → K, (σ ∘ u) ⬝ᵥ (Q *ᵥ x) ≠ 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ y) ≠ 0 := by
  -- A coordinate vector pairs with `x` as the corresponding coordinate of `Q x`.
  have hsingle (i : n) (w : n → K) : (σ ∘ Pi.single i 1) ⬝ᵥ (Q *ᵥ w) = (Q *ᵥ w) i := by
    have : σ ∘ Pi.single i (1 : K) = Pi.single i 1 := funext fun j ↦ by
      by_cases hj : j = i <;> simp [hj]
    rw [this, single_one_dotProduct]
  have hne {w : n → K} (hw : w ≠ 0) : ∃ u : n → K, (σ ∘ u) ⬝ᵥ (Q *ᵥ w) ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp fun h ↦ hdet (exists_mulVec_eq_zero_iff.mp ⟨w, hw, h⟩)
    exact ⟨Pi.single i 1, by rwa [hsingle]⟩
  obtain ⟨v, hv⟩ := hne hx
  obtain ⟨w, hw⟩ := hne hy
  by_cases hvy : (σ ∘ v) ⬝ᵥ (Q *ᵥ y) = 0
  · by_cases hwx : (σ ∘ w) ⬝ᵥ (Q *ᵥ x) = 0
    · exact ⟨v + w, by rwa [comp_add_dotProduct_mulVec, hwx, add_zero],
        by rwa [comp_add_dotProduct_mulVec, hvy, zero_add]⟩
    · exact ⟨w, hwx, hw⟩
  · exact ⟨v, hv, hvy⟩

/-- **A matrix scaling every isotropic vector is scalar.** Let `σ` be an involution and `Q` an
invertible `ε`-Hermitian matrix with `ε * ε = 1`, and suppose that the trace `t ↦ t + ε σ(t)` is
onto the elements `s` with `σ(s) = ε s` and has a nonzero kernel element. If some nonzero vector
is isotropic and `M` maps every isotropic vector to a multiple of itself, then `M` is a scalar
matrix. -/
theorem exists_eq_scalar_of_forall_mulVec_eq_smul (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {x₀ : n → K} (hx₀ : x₀ ≠ 0) (hx₀iso : (σ ∘ x₀) ⬝ᵥ (Q *ᵥ x₀) = 0) (M : Matrix n n K)
    (hM : ∀ v, (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0 → ∃ c : K, M *ᵥ v = c • v) :
    ∃ c : K, M = scalar n c := by
  obtain ⟨α, hα⟩ := hM x₀ hx₀iso
  -- Every isotropic `v` has the eigenvalue `α`: compare `x₀` with an isotropic `x₀ + c v`.
  have hiso {v : n → K} (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) : M *ᵥ v = α • v := by
    obtain ⟨β, hβ⟩ := hM v hv
    by_cases hdep : ∃ a : K, a • x₀ = v
    · obtain ⟨a, rfl⟩ := hdep
      rw [mulVec_smul, hα, smul_comm]
    have hind := (LinearIndependent.pair_iff' hx₀).mpr fun a ha ↦ hdep ⟨a, ha⟩
    -- A nonzero `c` with `x₀ + c v` isotropic.
    obtain ⟨c, hc, hcv⟩ : ∃ c ≠ (0 : K), (σ ∘ (x₀ + c • v)) ⬝ᵥ (Q *ᵥ (x₀ + c • v)) = 0 := by
      by_cases h0 : (σ ∘ x₀) ⬝ᵥ (Q *ᵥ v) = 0
      · refine ⟨1, one_ne_zero, ?_⟩
        rw [comp_add_smul_dotProduct_mulVec_add_smul hσ hQ hε hv, hx₀iso, h0]
        simp
      · obtain ⟨d, hd, hdε⟩ := hadm
        refine ⟨d / (σ ∘ x₀) ⬝ᵥ (Q *ᵥ v), div_ne_zero hd h0, ?_⟩
        rw [comp_add_smul_dotProduct_mulVec_add_smul hσ hQ hε hv, hx₀iso, div_mul_cancel₀ _ h0,
          hdε, add_zero]
    obtain ⟨γ, hγ⟩ := hM _ hcv
    rw [mulVec_add, mulVec_smul, hα, hβ] at hγ
    -- `(α - γ) x₀ + c (β - γ) v = 0`, so `α = γ = β`.
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hind (α - γ) (c * (β - γ)) <| by
      linear_combination (norm := module) hγ
    rw [hβ, show β = α by
      linear_combination (mul_eq_zero.mp h2).resolve_left hc - h1]
  -- Every vector `u` with `B(u, x₀) ≠ 0` is an isotropic vector minus a multiple of `x₀`.
  have hpair {u : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ x₀) ≠ 0) : M *ᵥ u = α • u := by
    obtain ⟨c, hc⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ hε htr
      hx₀iso hu
    have h := hiso hc
    rw [mulVec_add, mulVec_smul, hα, smul_add, smul_comm α c] at h
    exact add_right_cancel h
  -- Any other vector is a difference of two of those.
  obtain ⟨w, hw, -⟩ := exists_comp_dotProduct_mulVec_ne_zero_pair (σ := σ) hdet hx₀ hx₀
  refine ⟨α, mulVec_injective (funext fun u ↦ ?_)⟩
  rw [scalar_apply, ← smul_one_eq_diagonal, smul_mulVec, one_mulVec]
  by_cases hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ x₀) = 0
  · have h := hpair (u := u + w) (by rwa [comp_add_dotProduct_mulVec, hu, zero_add])
    rw [mulVec_add, hpair hw, smul_add] at h
    exact add_right_cancel h
  · exact hpair hu

end Field

variable {R M n : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype n]
  [DecidableEq n] (b : Module.Basis n R M)

/-- **The sesquilinear form of the identity matrix in coordinates**: for a basis `b`,
`toLinearMapₛₗ₂ σ b b 1 x y = ∑ i, σ (x i) * y i`, the form for which `b` is orthonormal. -/
theorem toLinearMapₛₗ₂_one_apply (σ : R →+* R) (x y : M) :
    toLinearMapₛₗ₂ σ b b (1 : Matrix n n R) x y = ∑ i, σ (b.repr x i) * b.repr y i := by
  simp [toLinearMapₛₗ₂_apply, Matrix.one_apply, smul_eq_mul]

/-- For the form making a basis orthonormal, the functional attached to a basis vector is its
coordinate functional. -/
theorem toLinearMapₛₗ₂_one_basis_eq_coord (σ : R →+* R) (i : n) :
    toLinearMapₛₗ₂ σ b b (1 : Matrix n n R) (b i) = b.coord i := by
  refine b.ext fun j ↦ ?_
  simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]

variable [StarRing R]

/-- **The orthonormal-basis form is Hermitian**: for complex conjugation, or the star of any star
ring, swapping the arguments of `toLinearMapₛₗ₂ (starRingEnd R) b b 1` conjugates its value. -/
theorem star_toLinearMapₛₗ₂_one_apply (x y : M) :
    star (toLinearMapₛₗ₂ (starRingEnd R) b b (1 : Matrix n n R) x y) =
      toLinearMapₛₗ₂ (starRingEnd R) b b (1 : Matrix n n R) y x := by
  simp only [toLinearMapₛₗ₂_one_apply, star_sum, star_mul, starRingEnd_apply, star_star]

/-- **The orthonormal-basis form is positive semidefinite** over a star-ordered ring. -/
theorem toLinearMapₛₗ₂_one_self_nonneg [PartialOrder R] [StarOrderedRing R] (x : M) :
    0 ≤ toLinearMapₛₗ₂ (starRingEnd R) b b (1 : Matrix n n R) x x := by
  rw [toLinearMapₛₗ₂_one_apply]
  exact Finset.sum_nonneg fun i _ ↦ star_mul_self_nonneg _

/-- **The orthonormal-basis form is definite** over a star-ordered ring without zero divisors:
`toLinearMapₛₗ₂ (starRingEnd R) b b 1 x x = 0` only for `x = 0`. -/
theorem toLinearMapₛₗ₂_one_self_eq_zero_iff [PartialOrder R] [StarOrderedRing R]
    [NoZeroDivisors R] {x : M} :
    toLinearMapₛₗ₂ (starRingEnd R) b b (1 : Matrix n n R) x x = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ b.ext_elem fun i ↦ ?_, fun hx ↦ by simp [hx]⟩
  simp only [toLinearMapₛₗ₂_one_apply, starRingEnd_apply] at hx
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ star_mul_self_nonneg _] at hx
  simpa using hx i (Finset.mem_univ i)

end Matrix
