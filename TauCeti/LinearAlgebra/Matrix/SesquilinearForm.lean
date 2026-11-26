/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.Algebra.Group.Pi.Lemmas
import TauCeti.Algebra.Ring.Hom
import TauCeti.LinearAlgebra.Matrix.Nondegenerate
import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec
import TauCeti.LinearAlgebra.Span.Basic
import TauCeti.Logic.Function.Basic

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
`B(x, y) = σ(x)ᵀ Q y` for the coordinate form `(σ ∘ x) ⬝ᵥ (Q *ᵥ y)`. A nonzero value `B(x, y) ≠ 0`
(in particular `B(x, y) = 1` over a nontrivial semiring) forces `x ≠ 0` and `y ≠ 0`
(`Matrix.left_ne_zero_of_comp_dotProduct_mulVec_ne_zero`,
`Matrix.right_ne_zero_of_comp_dotProduct_mulVec_ne_zero`,
`Matrix.left_ne_zero_of_comp_dotProduct_mulVec_eq_one`,
`Matrix.right_ne_zero_of_comp_dotProduct_mulVec_eq_one`). A matrix `g` with `σ(g)ᵀ Q g = Q`
intertwines the row covectors `σ(x)ᵀ Q` (`Matrix.comp_mulVec_vecMul_vecMul`) and
hence preserves `B` (`Matrix.comp_mulVec_dotProduct_mulVec_mulVec`), while orthogonality to `u`
extends from `S` and `x` to `S ⊔ (R ∙ x)`
(`Matrix.forall_mem_sup_span_singleton_comp_dotProduct_mulVec_eq_zero`). If `σ` is an involution and
`σ(Q)ᵀ = ε Q`, then `(σ(ε) ε) • Q = Q` (`Matrix.map_mul_self_smul_eq_self`) and `B` is
`ε`-Hermitian, `σ(B(x, y)) = ε B(y, x)` (`Matrix.apply_comp_dotProduct_mulVec`), with symmetric
orthogonality (`Matrix.comp_dotProduct_mulVec_eq_zero_comm`,
`Matrix.comp_dotProduct_mulVec_ne_zero_comm`) and transposed conjugate rank-one update
`σ(x (σ(y)ᵀ Q))ᵀ = ε (Q y) σ(x)ᵀ` (`Matrix.transpose_map_vecMulVec_vecMul`). With `ε * ε = 1`,
this gives `σ(ε) = ε` when `Q ≠ 0` over a domain (`Matrix.map_eq_self_of_mul_self_eq_one`,
`Matrix.map_eq_self_of_mul_self_eq_one_of_det_ne_zero`), `B(y, x) = ε σ(B(x, y))`
(`Matrix.comp_dotProduct_mulVec_swap`, `Matrix.comp_dotProduct_mulVec_eq_of_eq_one`), and a formula
for `B(u + c x, u + c x)` when `x` is isotropic (`Matrix.comp_add_smul_dotProduct_mulVec_add_smul`).

Over a field, if the trace `t ↦ t + ε σ(t)` is onto the elements `s` with `σ(s) = ε s` (which
forces `ε * ε = 1` when `Q ≠ 0` or `Q` is invertible over a nonempty index type,
`Matrix.mul_self_eq_one_of_trace` and `Matrix.mul_self_eq_one_of_trace_of_det_ne_zero`), a vector
`u` with `B(u, x) ≠ 0` corrects to an isotropic `u + c x`
(`Matrix.exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero`). For invertible `Q`, one or two
vectors outside a line `K ∙ u` are separated from `u` by the form when `σ` is surjective
(`Matrix.exists_comp_dotProduct_mulVec_eq_zero_and_ne_zero`,
`Matrix.exists_comp_dotProduct_mulVec_eq_zero_and_ne_zero_pair`), and when `u` is isotropic with
`B(u, x) = 0` and `u ∉ K ∙ x` this yields an isotropic vector orthogonal to `x` and not to `u`
(`Matrix.exists_comp_dotProduct_mulVec_self_eq_zero_and_eq_zero_and_ne_zero`); any two nonzero
vectors also pair nontrivially with a common vector
(`Matrix.exists_comp_dotProduct_mulVec_ne_zero_pair`). If moreover the trace
has a nonzero kernel element and some nonzero vector is isotropic, a matrix scaling every isotropic
vector is scalar (`Matrix.exists_eq_scalar_of_forall_mulVec_eq_smul`).

Conversely, preserving `B` implies `σ(g)ᵀ Q g = Q` (`Matrix.transpose_map_mul_mul_eq_self`), and
`Q.det ≠ 0` with injective `σ` yields `(Q u) (σ(u)ᵀ Q) ≠ 0`
(`Matrix.vecMulVec_mulVec_comp_vecMul_ne_zero`). Hyperbolic and anisotropic splits
(`Matrix.exists_eq_add_and_comp_dotProduct_mulVec_eq_zero`,
`Matrix.exists_comp_dotProduct_mulVec_eq_zero_and_eq_add_smul`,
`Matrix.exists_comp_dotProduct_mulVec_eq_zero_and_eq_one`,
`Matrix.exists_comp_dotProduct_mulVec_eq_zero_and_eq_one_of_notMem_span`) together with the
hyperbolic rescaling matrix `Matrix.hyperbolicRescaling` (`Matrix.hyperbolicRescaling_mulVec`,
`Matrix.det_hyperbolicRescaling`, `Matrix.transpose_map_hyperbolicRescaling_mul_mul_self`) yield
extensionality and `det` formulas (`Matrix.eq_of_mulVec_eq_of_comp_dotProduct_mulVec_eq_zero`,
`Matrix.det_eq_mul_of_mulVec_eq_smul`, `Matrix.det_eq_mul_mul_of_mulVec_eq_smul`).
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

/-- Acting by `g` on the left covector of `Q` pulls back `Q` to `(g.map σ)ᵀ * Q * g`. -/
theorem comp_mulVec_vecMul_vecMul_eq (g : Matrix n n R) (x : n → R) :
    (σ ∘ (g *ᵥ x)) ᵥ* Q ᵥ* g = (σ ∘ x) ᵥ* ((g.map σ)ᵀ * Q * g) := by
  rw [(funext (σ.map_mulVec g x) : σ ∘ (g *ᵥ x) = _), ← vecMul_transpose, vecMul_vecMul,
    vecMul_vecMul, ← Matrix.mul_assoc]

/-- **A matrix preserving the form intertwines its row covectors.** If `σ(g)ᵀ Q g = Q`, then
`(σ(g x)ᵀ Q) g = σ(x)ᵀ Q`. -/
theorem comp_mulVec_vecMul_vecMul {g : Matrix n n R} (hg : (g.map σ)ᵀ * Q * g = Q)
    (x : n → R) :
    (σ ∘ (g *ᵥ x)) ᵥ* Q ᵥ* g = (σ ∘ x) ᵥ* Q := by
  rw [comp_mulVec_vecMul_vecMul_eq, hg]

/-- **A matrix preserving the form preserves its values.** For the `σ`-sesquilinear form
`B(x, y) = σ(x)ᵀ Q y` of Gram matrix `Q`, if `σ(g)ᵀ Q g = Q`, then `B(g x, g y) = B(x, y)`. -/
theorem comp_mulVec_dotProduct_mulVec_mulVec {g : Matrix n n R} (hg : (g.map σ)ᵀ * Q * g = Q)
    (x y : n → R) :
    (σ ∘ (g *ᵥ x)) ⬝ᵥ (Q *ᵥ (g *ᵥ y)) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y) := by
  rw [dotProduct_mulVec, dotProduct_mulVec, comp_mulVec_vecMul_vecMul hg, ← dotProduct_mulVec]

/-- **A matrix preserving all values of the form preserves its Gram matrix.** For the
`σ`-sesquilinear form `B(x, y) = σ(x)ᵀ Q y` of Gram matrix `Q`, if `B(g x, g y) = B(x, y)` for all
`x, y`, then `σ(g)ᵀ Q g = Q`. -/
theorem transpose_map_mul_mul_eq_self {g : Matrix n n R}
    (hg : ∀ x y : n → R, (σ ∘ (g *ᵥ x)) ⬝ᵥ (Q *ᵥ (g *ᵥ y)) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)) :
    (g.map σ)ᵀ * Q * g = Q := by
  classical
  refine mulVec_injective (funext fun y ↦ funext fun i ↦ ?_)
  have hi := hg (Pi.single i 1) y
  rw [dotProduct_mulVec, dotProduct_mulVec, comp_mulVec_vecMul_vecMul_eq, ← dotProduct_mulVec,
    TauCeti.map_comp_single, map_one] at hi
  simpa using hi

/-- A matrix `g` satisfies `σ(g)ᵀ Q g = Q` if and only if it preserves all values of the
`σ`-sesquilinear form `B(x, y) = σ(x)ᵀ Q y`. -/
theorem transpose_map_mul_mul_eq_self_iff {g : Matrix n n R} :
    (g.map σ)ᵀ * Q * g = Q ↔
      ∀ x y : n → R, (σ ∘ (g *ᵥ x)) ⬝ᵥ (Q *ᵥ (g *ᵥ y)) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y) :=
  ⟨comp_mulVec_dotProduct_mulVec_mulVec, transpose_map_mul_mul_eq_self⟩

/-- Applying `σ(Q)ᵀ = ε Q` twice for an involutive `σ` gives `(σ(ε) * ε) • Q = Q`. -/
theorem map_mul_self_smul_eq_self {R n : Type*} [Semiring R] {Q : Matrix n n R} {σ : R →+* R}
    (hσ : Function.Involutive σ) {ε : R} (hQ : (Q.map σ)ᵀ = ε • Q) :
    (σ ε * ε) • Q = Q :=
  calc
    (σ ε * ε) • Q = σ ε • (Q.map σ)ᵀ := by rw [hQ, smul_smul]
    _ = ((ε • Q).map σ)ᵀ := by rw [map_smul' _ _ _ (map_mul σ), transpose_smul]
    _ = Q := by rw [← hQ, transpose_map, transpose_transpose, map_map, hσ.comp_self, map_id]

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
  rw [map_comp_add, add_dotProduct]

/-- If `B(x, y) ≠ 0`, then `x ≠ 0`. -/
theorem left_ne_zero_of_comp_dotProduct_mulVec_ne_zero {x y : n → R}
    (h : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) ≠ 0) : x ≠ 0 := by
  rintro rfl
  exact h (by simp)

/-- If `B(x, y) ≠ 0`, then `y ≠ 0`. -/
theorem right_ne_zero_of_comp_dotProduct_mulVec_ne_zero {x y : n → R}
    (h : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) ≠ 0) : y ≠ 0 := by
  rintro rfl
  exact h (by simp)

/-- Over a nontrivial semiring, `B(x, y) = 1` implies `x ≠ 0`. -/
theorem left_ne_zero_of_comp_dotProduct_mulVec_eq_one [Nontrivial R] {x y : n → R}
    (h : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 1) : x ≠ 0 :=
  left_ne_zero_of_comp_dotProduct_mulVec_ne_zero (ne_zero_of_eq_one h)

/-- Over a nontrivial semiring, `B(x, y) = 1` implies `y ≠ 0`. -/
theorem right_ne_zero_of_comp_dotProduct_mulVec_eq_one [Nontrivial R] {x y : n → R}
    (h : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 1) : y ≠ 0 :=
  right_ne_zero_of_comp_dotProduct_mulVec_ne_zero (ne_zero_of_eq_one h)

/-- For an involutive `σ` and `σ(Q)ᵀ = ε Q`, the transposed conjugate of `x (σ(y)ᵀ Q)` is
`ε (Q y) σ(x)ᵀ`. -/
theorem transpose_map_vecMulVec_vecMul (hσ : Function.Involutive σ) {ε : R}
    (hQ : (Q.map σ)ᵀ = ε • Q) (x y : n → R) :
    ((vecMulVec x ((σ ∘ y) ᵥ* Q)).map σ)ᵀ = ε • vecMulVec (Q *ᵥ y) (σ ∘ x) := by
  have hσy : σ ∘ ((σ ∘ y) ᵥ* Q) = y ᵥ* Q.map σ := funext fun i ↦ by
    rw [Function.comp_apply, RingHom.map_vecMul, ← Function.comp_assoc, hσ.comp_self,
      Function.id_comp]
  have hmap : (vecMulVec x ((σ ∘ y) ᵥ* Q)).map σ = vecMulVec (σ ∘ x) (σ ∘ ((σ ∘ y) ᵥ* Q)) := by
    ext i j
    simp [vecMulVec_apply]
  rw [hmap, transpose_vecMulVec, hσy, ← mulVec_transpose, hQ, smul_mulVec, smul_vecMulVec]

/-- With `ε * ε = 1`, the form is `ε`-Hermitian in the form `B(y, x) = ε σ(B(x, y))`. -/
theorem comp_dotProduct_mulVec_swap (hσ : Function.Involutive σ) {ε : R}
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (x y : n → R) :
    (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = ε * σ ((σ ∘ x) ⬝ᵥ (Q *ᵥ y)) := by
  rw [apply_comp_dotProduct_mulVec hσ hQ, ← mul_assoc, hε, one_mul]

/-- With `ε * ε = 1` and `(Q.map σ)ᵀ = ε • Q` for involutive `σ`, `B(x, y) = 1` implies
`B(y, x) = ε`. -/
theorem comp_dotProduct_mulVec_eq_of_eq_one (hσ : Function.Involutive σ) {ε : R}
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {x y : n → R}
    (hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 1) : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = ε := by
  rw [comp_dotProduct_mulVec_swap hσ hQ hε, hxy, map_one, mul_one]

/-- For an involutive `σ` and `σ(Q)ᵀ = ε Q`, orthogonality `B(x, y) = 0` is symmetric. -/
theorem comp_dotProduct_mulVec_eq_zero_comm (hσ : Function.Involutive σ) {ε : R}
    (hQ : (Q.map σ)ᵀ = ε • Q) {x y : n → R} :
    (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0 ↔ (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = 0 := by
  have aux {u v : n → R} (h : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 0) : (σ ∘ v) ⬝ᵥ (Q *ᵥ u) = 0 := by
    rw [← hσ ((σ ∘ v) ⬝ᵥ (Q *ᵥ u)), apply_comp_dotProduct_mulVec hσ hQ, h, mul_zero, map_zero]
  exact ⟨aux, aux⟩

/-- For an involutive `σ` and `σ(Q)ᵀ = ε Q`, non-orthogonality `B(x, y) ≠ 0` is symmetric. -/
theorem comp_dotProduct_mulVec_ne_zero_comm (hσ : Function.Involutive σ) {ε : R}
    (hQ : (Q.map σ)ᵀ = ε • Q) {x y : n → R} :
    (σ ∘ x) ⬝ᵥ (Q *ᵥ y) ≠ 0 ↔ (σ ∘ y) ⬝ᵥ (Q *ᵥ x) ≠ 0 :=
  (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).not

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

/-- If `u` is left-orthogonal to every vector of `S` and to `x` for `Q`, then `u` is
left-orthogonal to every vector of `S ⊔ (R ∙ x)`. -/
theorem forall_mem_sup_span_singleton_comp_dotProduct_mulVec_eq_zero
    {S : Submodule R (n → R)} {u x : n → R}
    (hS : ∀ s ∈ S, (σ ∘ u) ⬝ᵥ (Q *ᵥ s) = 0) (hx : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) :
    ∀ s ∈ S ⊔ (R ∙ x), (σ ∘ u) ⬝ᵥ (Q *ᵥ s) = 0 :=
  S.forall_mem_sup_span_singleton hS hx fun _ _ _ h₁ h₂ ↦ by
    simp [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, h₁, h₂]

end GramMatrix

/-- For an involutive `σ` and a nonzero `ε`-Hermitian matrix `Q` over a commutative ring without
zero divisors, `ε * ε = 1` implies `σ ε = ε`. -/
theorem map_eq_self_of_mul_self_eq_one {R n : Type*} [CommRing R] [NoZeroDivisors R]
    {Q : Matrix n n R} {σ : R →+* R} {ε : R} (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hQ0 : Q ≠ 0) : σ ε = ε := by
  obtain ⟨i, j, hij⟩ : ∃ i j, Q i j ≠ 0 := by
    by_contra! h
    exact hQ0 (Matrix.ext h)
  have h1 : (σ ε * ε - 1) * Q i j = 0 := by
    simpa [sub_mul] using sub_eq_zero.mpr (Matrix.ext_iff.mpr (map_mul_self_smul_eq_self hσ hQ) i j)
  linear_combination ((mul_eq_zero.mp h1).resolve_right hij) * ε - σ ε * hε

section CommRing

variable {R n : Type*} [CommRing R] [Fintype n] {Q : Matrix n n R} {σ : R →+* R} {ε : R}

/-- Subtracting `(ε * B(f, x)) • e` makes `x` left-orthogonal to `f` when `B(f, e) = ε`. -/
theorem comp_dotProduct_mulVec_sub_smul_eq_zero (hε : ε * ε = 1) {e f : n → R}
    (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) (x : n → R) :
    (σ ∘ f) ⬝ᵥ (Q *ᵥ (x - (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ x))) • e)) = 0 := by
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hfe]
  linear_combination -((σ ∘ f) ⬝ᵥ (Q *ᵥ x)) * hε

/-- **Orthogonal decomposition along a hyperbolic pair** `(e, f)`. -/
theorem exists_eq_add_and_comp_dotProduct_mulVec_eq_zero (hε : ε * ε = 1) {e f : n → R}
    (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0)
    (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) (x : n → R) :
    ∃ w : n → R, (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0 ∧
      x = (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ x))) • e + ((σ ∘ e) ⬝ᵥ (Q *ᵥ x)) • f + w :=
  ⟨x - (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ x))) • e - ((σ ∘ e) ⬝ᵥ (Q *ᵥ x)) • f,
    by simp [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, he, hef],
    by rw [mulVec_sub, dotProduct_sub, comp_dotProduct_mulVec_sub_smul_eq_zero hε hfe, mulVec_smul,
      dotProduct_smul, hf, smul_zero, sub_zero], by module⟩

/-- Matrices agreeing on a hyperbolic pair `(e, f)` and on `{e, f}ᗮ` are equal. -/
theorem eq_of_mulVec_eq_of_comp_dotProduct_mulVec_eq_zero {A B : Matrix n n R} (hε : ε * ε = 1)
    {e f : n → R} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0)
    (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) (he_eq : A *ᵥ e = B *ᵥ e)
    (hf_eq : A *ᵥ f = B *ᵥ f) (hw_eq : ∀ w : n → R, (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0 →
      (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0 → A *ᵥ w = B *ᵥ w) : A = B :=
  mulVec_injective <| funext fun x ↦ by
    obtain ⟨w, hew, hfw, hx⟩ := exists_eq_add_and_comp_dotProduct_mulVec_eq_zero hε he hf hef hfe x
    rw [hx]; simp [mulVec_add, mulVec_smul, he_eq, hf_eq, hw_eq w hew hfw]

/-- **Hyperbolic rescaling matrix**
`1 + ((c₁ - 1) * ε) • e (σ(f)ᵀ Q) + (c₂ - 1) • f (σ(e)ᵀ Q)` for the `σ`-sesquilinear form
`B(x, y) = σ(x)ᵀ Q y`. On a hyperbolic pair `(e, f)` (`B(e, e) = B(f, f) = 0`, `B(e, f) = 1`,
`B(f, e) = ε` with `ε * ε = 1`), it rescales `e` by `c₁`, `f` by `c₂`, and fixes `{e, f}ᗮ`. -/
def hyperbolicRescaling [DecidableEq n] (Q : Matrix n n R) (σ : R →+* R) (ε : R) (e f : n → R)
    (c₁ c₂ : R) : Matrix n n R :=
  1 + ((c₁ - 1) * ε) • vecMulVec e ((σ ∘ f) ᵥ* Q) + (c₂ - 1) • vecMulVec f ((σ ∘ e) ᵥ* Q)

/-- Explicit matrix formula for `Matrix.hyperbolicRescaling`. -/
theorem hyperbolicRescaling_def [DecidableEq n] (Q : Matrix n n R) (σ : R →+* R) (ε : R)
    (e f : n → R) (c₁ c₂ : R) :
    Q.hyperbolicRescaling σ ε e f c₁ c₂ =
      1 + ((c₁ - 1) * ε) • vecMulVec e ((σ ∘ f) ᵥ* Q) +
        (c₂ - 1) • vecMulVec f ((σ ∘ e) ᵥ* Q) :=
  (rfl)

/-- Rescaling both vectors by `1` gives the identity matrix. -/
@[simp]
theorem hyperbolicRescaling_one_one [DecidableEq n] (e f : n → R) :
    Q.hyperbolicRescaling σ ε e f 1 1 = 1 := by
  simp [hyperbolicRescaling_def]

/-- When `e = 0`, `Matrix.hyperbolicRescaling` is the identity matrix. -/
@[simp]
theorem hyperbolicRescaling_zero_left [DecidableEq n] (f : n → R) (c₁ c₂ : R) :
    Q.hyperbolicRescaling σ ε 0 f c₁ c₂ = 1 := by
  simp [hyperbolicRescaling_def]

/-- When `f = 0`, `Matrix.hyperbolicRescaling` is the identity matrix. -/
@[simp]
theorem hyperbolicRescaling_zero_right [DecidableEq n] (e : n → R) (c₁ c₂ : R) :
    Q.hyperbolicRescaling σ ε e 0 c₁ c₂ = 1 := by
  simp [hyperbolicRescaling_def]

/-- `Matrix.hyperbolicRescaling` sends `x` to
`x + ((c₁ - 1) * ε * B(f, x)) • e + ((c₂ - 1) * B(e, x)) • f`. -/
theorem hyperbolicRescaling_mulVec [DecidableEq n] (e f : n → R) (c₁ c₂ : R) (x : n → R) :
    Q.hyperbolicRescaling σ ε e f c₁ c₂ *ᵥ x =
      x + (((c₁ - 1) * ε) * ((σ ∘ f) ⬝ᵥ (Q *ᵥ x))) • e +
        ((c₂ - 1) * ((σ ∘ e) ⬝ᵥ (Q *ᵥ x))) • f := by
  simp [hyperbolicRescaling_def, add_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec,
    smul_smul]

/-- When `ε * ε = 1`, `B(e, e) = 0`, and `B(f, e) = ε`, `Matrix.hyperbolicRescaling` rescales `e`
by `c₁`. -/
theorem hyperbolicRescaling_mulVec_left [DecidableEq n] (hε : ε * ε = 1) {e f : n → R}
    (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) (c₁ c₂ : R) :
    Q.hyperbolicRescaling σ ε e f c₁ c₂ *ᵥ e = c₁ • e := by
  rw [hyperbolicRescaling_mulVec]
  simp [he, hfe, mul_assoc, hε, sub_smul]

/-- When `B(f, f) = 0` and `B(e, f) = 1`, `Matrix.hyperbolicRescaling` rescales `f` by `c₂`. -/
theorem hyperbolicRescaling_mulVec_right [DecidableEq n] {e f : n → R}
    (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (c₁ c₂ : R) :
    Q.hyperbolicRescaling σ ε e f c₁ c₂ *ᵥ f = c₂ • f := by
  rw [hyperbolicRescaling_mulVec]
  simp [hf, hef, sub_smul]

/-- `Matrix.hyperbolicRescaling` fixes every vector `w` with `B(e, w) = 0` and `B(f, w) = 0`. -/
theorem hyperbolicRescaling_mulVec_eq_self [DecidableEq n] {e f w : n → R} (c₁ c₂ : R)
    (hew : (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0) (hfw : (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0) :
    Q.hyperbolicRescaling σ ε e f c₁ c₂ *ᵥ w = w := by
  rw [hyperbolicRescaling_mulVec]
  simp [hew, hfw]

/-- **Two-factor product for an isotropic `f`.** When `B(f, f) = 0`, `Matrix.hyperbolicRescaling`
factors into two rank-one perturbations of the identity. -/
theorem hyperbolicRescaling_eq_mul [DecidableEq n] {e f : n → R}
    (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (c₁ c₂ : R) :
    Q.hyperbolicRescaling σ ε e f c₁ c₂ =
      (1 + ((c₁ - 1) * ε) • vecMulVec e ((σ ∘ f) ᵥ* Q)) *
        (1 + (c₂ - 1) • vecMulVec f ((σ ∘ e) ᵥ* Q)) := by
  have hprod : vecMulVec e ((σ ∘ f) ᵥ* Q) * vecMulVec f ((σ ∘ e) ᵥ* Q) = 0 := by
    simp [vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, hf]
  simp only [hyperbolicRescaling_def, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, smul_mul_assoc, mul_smul_comm, hprod, smul_zero, add_zero]

/-- **Determinant of `Matrix.hyperbolicRescaling`**: when `ε * ε = 1`, `B(f, f) = 0`,
`B(e, f) = 1`, and `B(f, e) = ε`, `det(hyperbolicRescaling Q σ ε e f c₁ c₂) = c₁ * c₂`. -/
theorem det_hyperbolicRescaling [DecidableEq n] (hε : ε * ε = 1) {e f : n → R}
    (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1)
    (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) (c₁ c₂ : R) :
    (Q.hyperbolicRescaling σ ε e f c₁ c₂).det = c₁ * c₂ := by
  have hd₁ : (1 + ((c₁ - 1) * ε) • vecMulVec e ((σ ∘ f) ᵥ* Q)).det = c₁ := by
    rw [← sub_neg_eq_add, ← neg_smul, ← smul_vecMulVec, TauCeti.det_one_sub_vecMulVec,
      dotProduct_smul, ← dotProduct_mulVec, hfe, smul_eq_mul]
    linear_combination (c₁ - 1) * hε
  have hd₂ : (1 + (c₂ - 1) • vecMulVec f ((σ ∘ e) ᵥ* Q)).det = c₂ := by
    rw [← sub_neg_eq_add, ← neg_smul, ← smul_vecMulVec, TauCeti.det_one_sub_vecMulVec,
      dotProduct_smul, ← dotProduct_mulVec, hef, smul_eq_mul]
    ring
  rw [hyperbolicRescaling_eq_mul hf, det_mul, hd₁, hd₂]

/-- Multiplying two hyperbolic rescalings on a hyperbolic pair multiplies their scalars. -/
theorem hyperbolicRescaling_mul_hyperbolicRescaling [DecidableEq n] (hε : ε * ε = 1)
    {e f : n → R} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0)
    (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) (c₁ c₂ d₁ d₂ : R) :
    Q.hyperbolicRescaling σ ε e f c₁ c₂ * Q.hyperbolicRescaling σ ε e f d₁ d₂ =
      Q.hyperbolicRescaling σ ε e f (c₁ * d₁) (c₂ * d₂) :=
  eq_of_mulVec_eq_of_comp_dotProduct_mulVec_eq_zero hε he hf hef hfe
    (by simp [← mulVec_mulVec, hyperbolicRescaling_mulVec_left hε he hfe, mulVec_smul, smul_smul,
      mul_comm])
    (by simp [← mulVec_mulVec, hyperbolicRescaling_mulVec_right hf hef, mulVec_smul, smul_smul,
      mul_comm])
    fun w hew hfw ↦ by simp [← mulVec_mulVec, hyperbolicRescaling_mulVec_eq_self _ _ hew hfw]

/-- **Conjugation law for `Matrix.hyperbolicRescaling`.** A matrix `g` preserving `Q` carries
`hyperbolicRescaling Q σ ε e f c₁ c₂` to `hyperbolicRescaling Q σ ε (g *ᵥ e) (g *ᵥ f) c₁ c₂`. -/
theorem mul_hyperbolicRescaling [DecidableEq n] {g : Matrix n n R}
    (hg : (g.map σ)ᵀ * Q * g = Q) (e f : n → R) (c₁ c₂ : R) :
    g * Q.hyperbolicRescaling σ ε e f c₁ c₂ =
      Q.hyperbolicRescaling σ ε (g *ᵥ e) (g *ᵥ f) c₁ c₂ * g := by
  simp [hyperbolicRescaling_def, Matrix.mul_add, Matrix.add_mul, mul_vecMulVec, vecMulVec_mul,
    comp_mulVec_vecMul_vecMul hg]

/-- **Hyperbolic rescaling is an isometry when `c₁ * σ c₂ = 1`.** -/
theorem transpose_map_hyperbolicRescaling_mul_mul_self [DecidableEq n]
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {e f : n → R}
    (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0)
    (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) {c₁ c₂ : R} (hc : c₁ * σ c₂ = 1) :
    ((Q.hyperbolicRescaling σ ε e f c₁ c₂).map σ)ᵀ * Q *
      Q.hyperbolicRescaling σ ε e f c₁ c₂ = Q := by
  have hfe := comp_dotProduct_mulVec_eq_of_eq_one hσ hQ hε hef
  have hσε : σ ε = ε := by simpa [hfe, hef] using apply_comp_dotProduct_mulVec hσ hQ f e
  have hc' : σ c₁ * c₂ = 1 := by simpa [map_mul, hσ c₂] using congrArg σ hc
  refine transpose_map_mul_mul_eq_self fun x y ↦ ?_
  rw [hyperbolicRescaling_mulVec, hyperbolicRescaling_mulVec]
  simp only [map_comp_add, TauCeti.map_comp_smul, map_mul, map_sub, map_one, hσε,
    comp_dotProduct_mulVec_swap hσ hQ hε e x, comp_dotProduct_mulVec_swap hσ hQ hε f x,
    add_dotProduct, smul_dotProduct, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul,
    smul_eq_mul, he, hf, hef, hfe]
  linear_combination
    ((σ ∘ f) ⬝ᵥ (Q *ᵥ y)) * σ ((σ ∘ e) ⬝ᵥ (Q *ᵥ x)) * (c₁ - 1) * σ c₂ * hε +
    ((σ ∘ f) ⬝ᵥ (Q *ᵥ y)) * σ ((σ ∘ e) ⬝ᵥ (Q *ᵥ x)) * hc +
    ((σ ∘ e) ⬝ᵥ (Q *ᵥ y)) * σ ((σ ∘ f) ⬝ᵥ (Q *ᵥ x)) * ε * hc'

/-- **Determinant of a matrix rescaling a hyperbolic pair** `(e, f)` by `c₁, c₂` and fixing
`{e, f}ᗮ`. -/
theorem det_eq_mul_of_mulVec_eq_smul [DecidableEq n] {A : Matrix n n R} (hε : ε * ε = 1)
    {e f : n → R} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0)
    (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) {c₁ c₂ : R}
    (hAe : A *ᵥ e = c₁ • e) (hAf : A *ᵥ f = c₂ • f)
    (hAw : ∀ w : n → R, (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0 → A *ᵥ w = w) :
    A.det = c₁ * c₂ := by
  have hA : A = Q.hyperbolicRescaling σ ε e f c₁ c₂ :=
    eq_of_mulVec_eq_of_comp_dotProduct_mulVec_eq_zero hε he hf hef hfe
      (hAe.trans (hyperbolicRescaling_mulVec_left hε he hfe c₁ c₂).symm)
      (hAf.trans (hyperbolicRescaling_mulVec_right hf hef c₁ c₂).symm)
      fun w hew hfw ↦
        (hAw w hew hfw).trans (hyperbolicRescaling_mulVec_eq_self c₁ c₂ hew hfw).symm
  rw [hA, det_hyperbolicRescaling hε hf hef hfe]

/-- Over a domain, `Q.det ≠ 0`, injective `σ`, and `u ≠ 0` imply
`vecMulVec (Q *ᵥ u) ((σ ∘ u) ᵥ* Q) ≠ 0`. -/
theorem vecMulVec_mulVec_comp_vecMul_ne_zero [IsDomain R] [DecidableEq n]
    (hσ : Function.Injective σ) (hdet : Q.det ≠ 0) {u : n → R} (hu0 : u ≠ 0) :
    vecMulVec (Q *ᵥ u) ((σ ∘ u) ᵥ* Q) ≠ 0 :=
  vecMulVec_eq_zero.not.mpr <| not_or.mpr
    ⟨fun h0 ↦ hdet (exists_mulVec_eq_zero_iff.mp ⟨u, hu0, h0⟩),
      fun h0 ↦ hdet (exists_vecMul_eq_zero_iff.mp
        ⟨σ ∘ u, fun h ↦ hu0 (funext fun i ↦ hσ ((congrFun h i).trans (map_zero σ).symm)), h0⟩)⟩

end CommRing

section Field

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

omit [DecidableEq n] [Fintype n] in
/-- If `σ` is an involution, `Q` is a nonzero `ε`-Hermitian matrix, and the trace `t ↦ t + ε σ(t)`
is onto the elements `s` with `σ(s) = ε s`, then `ε * ε = 1`. -/
theorem mul_self_eq_one_of_trace (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hQ0 : Q ≠ 0) : ε * ε = 1 := by
  -- `σ ε * ε = 1`, by applying `(σ ε * ε) • Q = Q` to a nonzero entry of `Q`.
  obtain ⟨i, j, hij⟩ : ∃ i j, Q i j ≠ 0 := by
    by_contra h
    exact hQ0 (Matrix.ext fun i j ↦ not_not.mp fun h' ↦ h ⟨i, j, h'⟩)
  have hε' : σ ε * ε = 1 :=
    mul_right_cancel₀ hij <| by simpa using Matrix.ext_iff.mpr (map_mul_self_smul_eq_self hσ hQ) i j
  -- `s = 1 + σ ε` satisfies `σ s = ε s`, so `s = t + ε σ t`, whence `ε σ s = s`.
  obtain ⟨t, ht⟩ := htr (1 + σ ε) <| by
    rw [map_add, map_one, hσ]
    linear_combination -hε'
  have h2 : σ (1 + σ ε) = σ t + σ ε * t := by
    rw [← ht, map_add, map_mul, hσ]
  have h1 : ε * σ (1 + σ ε) = 1 + σ ε := by
    rw [h2, ← ht]
    linear_combination t * hε'
  by_cases hs : 1 + σ ε = 0
  · have hε1 : ε = -1 := by
      rw [← hσ ε, show σ ε = -1 by linear_combination hs, map_neg, map_one]
    rw [hε1]
    norm_num
  · rw [map_add, map_one, hσ] at h1
    refine mul_right_cancel₀ hs ?_
    linear_combination h1 + ε * hε'

/-- Over a nonempty index type, an invertible `ε`-Hermitian matrix whose trace `t ↦ t + ε σ(t)` is
onto the elements `s` with `σ(s) = ε s` satisfies `ε * ε = 1`. -/
theorem mul_self_eq_one_of_trace_of_det_ne_zero [Nonempty n] (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) : ε * ε = 1 := by
  refine mul_self_eq_one_of_trace hσ hQ htr ?_
  rintro rfl
  exact hdet det_zero

/-- Over a nonempty index type, an invertible `ε`-Hermitian matrix with `ε * ε = 1` satisfies
`σ ε = ε`. -/
theorem map_eq_self_of_mul_self_eq_one_of_det_ne_zero [Nonempty n] (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0) (hε : ε * ε = 1) : σ ε = ε :=
  map_eq_self_of_mul_self_eq_one hσ hQ hε fun h0 ↦ hdet (h0 ▸ det_zero)

omit [DecidableEq n] in
/-- **Correcting a vector to an isotropic one.** If the trace `t ↦ t + ε σ(t)` is onto the
elements `s` with `σ(s) = ε s`, then for isotropic `x` and `B(u, x) ≠ 0` some `u + c • x` is
isotropic. -/
theorem exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) {x : n → K}
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) {u : n → K} (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    ∃ c : K, (σ ∘ (u + c • x)) ⬝ᵥ (Q *ᵥ (u + c • x)) = 0 := by
  have hε : ε * ε = 1 := by
    refine mul_self_eq_one_of_trace hσ hQ htr ?_
    rintro rfl
    simp at hux
  obtain ⟨t, ht⟩ := htr (-((σ ∘ u) ⬝ᵥ (Q *ᵥ u))) <| by
    rw [map_neg, apply_comp_dotProduct_mulVec hσ hQ, mul_neg]
  refine ⟨t / (σ ∘ u) ⬝ᵥ (Q *ᵥ x), ?_⟩
  rw [comp_add_smul_dotProduct_mulVec_add_smul hσ hQ hε hx, div_mul_cancel₀ _ hux, ht,
    add_neg_cancel]

/-- **Separating two vectors from a line by a sesquilinear form.** If `σ` is surjective, `Q` is
invertible, and neither `x` nor `y` lies on the line `K ∙ u`, then some vector `v` satisfies
`B(v, u) = 0`, `B(v, x) ≠ 0`, and `B(v, y) ≠ 0`. -/
theorem exists_comp_dotProduct_mulVec_eq_zero_and_ne_zero_pair (hσ : Function.Surjective σ)
    (hdet : Q.det ≠ 0) {u x y : n → K} (hx : x ∉ K ∙ u) (hy : y ∉ K ∙ u) :
    ∃ v : n → K, (σ ∘ v) ⬝ᵥ (Q *ᵥ u) = 0 ∧ (σ ∘ v) ⬝ᵥ (Q *ᵥ x) ≠ 0 ∧
      (σ ∘ v) ⬝ᵥ (Q *ᵥ y) ≠ 0 := by
  obtain ⟨w, hwu, hwx, hwy⟩ := (Matrix.Nondegenerate.of_det_ne_zero hdet).separatingRight
    |>.separatingLeft_transpose.exists_ortho_and_not_ortho_pair_of_notMem_span hx hy
  rw [dotProduct_transpose_mulVec] at hwu hwx hwy
  obtain ⟨v, rfl⟩ := hσ.comp_left w
  exact ⟨v, hwu, hwx, hwy⟩

/-- **Separating a vector from a line by a sesquilinear form.** If `σ` is surjective, `Q` is
invertible, and `x` does not lie on the line `K ∙ u`, then some vector `v` satisfies
`B(v, u) = 0` and `B(v, x) ≠ 0`. -/
theorem exists_comp_dotProduct_mulVec_eq_zero_and_ne_zero (hσ : Function.Surjective σ)
    (hdet : Q.det ≠ 0) {u x : n → K} (hx : x ∉ K ∙ u) :
    ∃ v : n → K, (σ ∘ v) ⬝ᵥ (Q *ᵥ u) = 0 ∧ (σ ∘ v) ⬝ᵥ (Q *ᵥ x) ≠ 0 :=
  (exists_comp_dotProduct_mulVec_eq_zero_and_ne_zero_pair hσ hdet hx hx).imp fun _ ⟨hu, hx, _⟩ ↦
    ⟨hu, hx⟩

/-- **An isotropic vector orthogonal to `x` and not to an isotropic `u`.** Let `σ` be an
involution, let `Q` be an invertible `ε`-Hermitian matrix, and suppose that the trace
`t ↦ t + ε σ(t)` is onto the elements `s` with `σ(s) = ε s`. If `u` is isotropic, `u ∉ K ∙ x`, and
`B(u, x) = 0`, then some isotropic vector `s` satisfies `B(x, s) = 0` and `B(u, s) ≠ 0`. -/
theorem exists_comp_dotProduct_mulVec_self_eq_zero_and_eq_zero_and_ne_zero
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) {u x : n → K}
    (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hu_span : u ∉ K ∙ x)
    (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) :
    ∃ s : n → K, (σ ∘ s) ⬝ᵥ (Q *ᵥ s) = 0 ∧ (σ ∘ x) ⬝ᵥ (Q *ᵥ s) = 0 ∧
      (σ ∘ u) ⬝ᵥ (Q *ᵥ s) ≠ 0 := by
  obtain ⟨v, hvx, hvu⟩ :=
    exists_comp_dotProduct_mulVec_eq_zero_and_ne_zero hσ.surjective hdet hu_span
  obtain ⟨c, hs⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hu hvu
  refine ⟨v + c • u, hs, ?_, ?_⟩
  · rw [comp_dotProduct_mulVec_eq_zero_comm hσ hQ]
    simp [hvx, hux]
  · rw [comp_dotProduct_mulVec_ne_zero_comm hσ hQ]
    simpa [hu] using hvu

/-- For an invertible `Q`, two nonzero vectors pair nontrivially with a common vector. -/
theorem exists_comp_dotProduct_mulVec_ne_zero_pair (hdet : Q.det ≠ 0) {x y : n → K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ u : n → K, (σ ∘ u) ⬝ᵥ (Q *ᵥ x) ≠ 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ y) ≠ 0 := by
  -- A coordinate vector pairs with `x` as the corresponding coordinate of `Q x`.
  have hne {w : n → K} (hw : w ≠ 0) : ∃ u : n → K, (σ ∘ u) ⬝ᵥ (Q *ᵥ w) ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp fun h ↦ hdet (exists_mulVec_eq_zero_iff.mp ⟨w, hw, h⟩)
    exact ⟨Pi.single i 1, by rwa [TauCeti.map_comp_single, map_one, single_one_dotProduct]⟩
  obtain ⟨v, hv⟩ := hne hx
  obtain ⟨w, hw⟩ := hne hy
  by_cases hvy : (σ ∘ v) ⬝ᵥ (Q *ᵥ y) = 0
  · by_cases hwx : (σ ∘ w) ⬝ᵥ (Q *ᵥ x) = 0
    · exact ⟨v + w, by rwa [comp_add_dotProduct_mulVec, hwx, add_zero],
        by rwa [comp_add_dotProduct_mulVec, hvy, zero_add]⟩
    · exact ⟨w, hwx, hw⟩
  · exact ⟨v, hv, hvy⟩

/-- **A matrix scaling every isotropic vector is scalar.** Let `σ` be an involution and `Q` an
invertible `ε`-Hermitian matrix, and suppose that the trace `t ↦ t + ε σ(t)` is onto the
elements `s` with `σ(s) = ε s` and has a nonzero kernel element (surjectivity of the trace already
forces `ε * ε = 1`, `Matrix.mul_self_eq_one_of_trace`). If some nonzero vector
is isotropic and `M` maps every isotropic vector to a multiple of itself, then `M` is a scalar
matrix. -/
theorem exists_eq_scalar_of_forall_mulVec_eq_smul (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {x₀ : n → K} (hx₀ : x₀ ≠ 0) (hx₀iso : (σ ∘ x₀) ⬝ᵥ (Q *ᵥ x₀) = 0) (M : Matrix n n K)
    (hM : ∀ v, (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0 → ∃ c : K, M *ᵥ v = c • v) :
    ∃ c : K, M = scalar n c := by
  have := Function.nonempty_of_ne hx₀
  have hε := mul_self_eq_one_of_trace_of_det_ne_zero hσ hQ hdet htr
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
    obtain ⟨c, hc⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hx₀iso hu
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

omit [DecidableEq n] in
/-- If `g` preserves `Q` and sends `u` to a nonzero multiple of `e`, then `g` sends any vector
orthogonal to `u` to a vector orthogonal to `e`. -/
theorem comp_dotProduct_mulVec_mulVec_eq_zero_of_mulVec_eq_smul {g : Matrix n n K}
    (hg : (g.map σ)ᵀ * Q * g = Q) {u e x : n → K} {c : K} (hc : c ≠ 0) (hgu : g *ᵥ u = c • e)
    (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) : (σ ∘ e) ⬝ᵥ (Q *ᵥ (g *ᵥ x)) = 0 := by
  have h := (comp_mulVec_dotProduct_mulVec_mulVec hg u x).trans hux
  rw [hgu, TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left ((map_ne_zero σ).mpr hc)

omit [DecidableEq n] in
/-- Subtracting `(B(v, v)⁻¹ * B(v, x)) • v` makes `x` orthogonal to an anisotropic vector `v`. -/
theorem comp_dotProduct_mulVec_sub_inv_mul_smul_eq_zero {v : n → K}
    (hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) ≠ 0) (x : n → K) :
    (σ ∘ v) ⬝ᵥ (Q *ᵥ (x - (((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v)) = 0 := by
  simp [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul]; field_simp; ring

omit [DecidableEq n] in
/-- **Orthogonal decomposition along an anisotropic vector** `v`, preserving left-orthogonality. -/
theorem exists_comp_dotProduct_mulVec_eq_zero_and_eq_add_smul {v : n → K}
    (hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) ≠ 0) (x : n → K) :
    ∃ w : n → K, (σ ∘ v) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (∀ u : n → K, (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 0 →
      (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0 → (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) ∧
      x = w + (((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v :=
  ⟨x - (((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v,
    comp_dotProduct_mulVec_sub_inv_mul_smul_eq_zero hvv x,
    fun _ huv hux ↦ by simp [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, huv, hux],
    (sub_add_cancel _ _).symm⟩

/-- **Extending a nonzero isotropic vector to a hyperbolic pair.** For involutive `σ` and
invertible `ε`-Hermitian `Q` with surjective `ε`-trace, any nonzero isotropic `e` pairs with some
nonzero isotropic `f` satisfying `B(e, f) = 1` and `B(f, e) = ε`. -/
theorem exists_comp_dotProduct_mulVec_eq_zero_and_eq_one (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) {e : n → K} (he₀ : e ≠ 0)
    (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) :
    ∃ f : n → K, f ≠ 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0 ∧ (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1 ∧
      (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε := by
  obtain ⟨u, hue, -⟩ := exists_comp_dotProduct_mulVec_ne_zero_pair (σ := σ) hdet he₀ he₀
  obtain ⟨c, hf₀⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr he hue
  set f₀ := u + c • e; have := Function.nonempty_of_ne he₀
  have hε := mul_self_eq_one_of_trace_of_det_ne_zero hσ hQ hdet htr
  have hef₀ : (σ ∘ e) ⬝ᵥ (Q *ᵥ f₀) ≠ 0 :=
    (comp_dotProduct_mulVec_ne_zero_comm hσ hQ).mpr (by simpa [f₀, he] using hue)
  let f := ((σ ∘ e) ⬝ᵥ (Q *ᵥ f₀))⁻¹ • f₀
  have hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1 := by simp [f, mulVec_smul, inv_mul_cancel₀ hef₀]
  exact ⟨f, right_ne_zero_of_comp_dotProduct_mulVec_eq_one hef,
    by simp [f, TauCeti.map_comp_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, hf₀], hef,
    comp_dotProduct_mulVec_eq_of_eq_one hσ hQ hε hef⟩

omit [DecidableEq n] in
private theorem exists_isotropic_ne_zero_in_ortho (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {e f : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
    (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) {u w : n → K} (hu₀ : u ≠ 0) (hw_span : w ∉ K ∙ u)
    (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hw : (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0)
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) :
    ∃ u₀ : n → K, u₀ ≠ 0 ∧ (σ ∘ e) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧
      (σ ∘ u₀) ⬝ᵥ (Q *ᵥ u₀) = 0 := by
  have hwu := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp huw
  obtain ⟨w₁, hw₁_span, hew₁, hw₁⟩ :
      ∃ w₁, w₁ ∉ K ∙ e ∧ (σ ∘ e) ⬝ᵥ (Q *ᵥ w₁) = 0 ∧ (σ ∘ w₁) ⬝ᵥ (Q *ᵥ w₁) = 0 := by
    by_cases heu : (σ ∘ e) ⬝ᵥ (Q *ᵥ u) = 0
    · by_cases hue : u ∈ K ∙ e
      · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hue; have hc := left_ne_zero_of_smul hu₀
        exact ⟨w, fun hwe ↦ hw_span (by rwa [Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]),
          by simpa [TauCeti.map_comp_smul, smul_dotProduct, (map_ne_zero σ).mpr hc] using huw, hw⟩
      · exact ⟨u, hue, heu, hu⟩
    · set α := ((σ ∘ e) ⬝ᵥ (Q *ᵥ u))⁻¹ * ((σ ∘ e) ⬝ᵥ (Q *ᵥ w)); set w₁ := w - α • u
      have huw₁ : (σ ∘ u) ⬝ᵥ (Q *ᵥ w₁) = 0 := by simp [w₁, mulVec_sub, mulVec_smul, huw, hu]
      exact ⟨w₁, notMem_span_of_dotProduct_mulVec_of_ne_zero huw₁
          ((comp_dotProduct_mulVec_ne_zero_comm hσ hQ).mpr heu)
          fun h0 ↦ hw_span (Submodule.mem_span_singleton.mpr ⟨α, (sub_eq_zero.mp h0).symm⟩),
        by simp [w₁, α, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul]; field_simp; ring,
        by simp [w₁, map_comp_sub, TauCeti.map_comp_smul, sub_dotProduct, smul_dotProduct,
          mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hw, hu, huw, hwu]⟩
  set u₀ := w₁ - (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ w₁))) • e
  have hw₁e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hew₁
  exact ⟨u₀, fun h0 ↦ hw₁_span <| Submodule.mem_span_singleton.mpr ⟨_, (sub_eq_zero.mp h0).symm⟩,
    by simp [u₀, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hew₁, he],
    comp_dotProduct_mulVec_sub_smul_eq_zero hε hfe w₁,
    by simp [u₀, map_comp_sub, TauCeti.map_comp_smul, sub_dotProduct, smul_dotProduct, mulVec_sub,
      mulVec_smul, dotProduct_sub, dotProduct_smul, hw₁, he, hew₁, hw₁e]⟩

/-- **A hyperbolic pair orthogonal to `(e, f)` in Witt index at least two.** -/
theorem exists_comp_dotProduct_mulVec_eq_zero_and_eq_one_of_notMem_span
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) {e f : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
    (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) {u w : n → K} (hu₀ : u ≠ 0)
    (hw_span : w ∉ K ∙ u) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hw : (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0)
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) :
    ∃ u₀ y₀ : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧
      (σ ∘ e) ⬝ᵥ (Q *ᵥ y₀) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ y₀) = 0 ∧
      (σ ∘ u₀) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧ (σ ∘ y₀) ⬝ᵥ (Q *ᵥ y₀) = 0 ∧
      (σ ∘ u₀) ⬝ᵥ (Q *ᵥ y₀) = 1 ∧ (σ ∘ y₀) ⬝ᵥ (Q *ᵥ u₀) = ε := by
  have := Function.nonempty_of_ne hu₀
  have hε := mul_self_eq_one_of_trace_of_det_ne_zero hσ hQ hdet htr
  have hσε := map_eq_self_of_mul_self_eq_one_of_det_ne_zero hσ hQ hdet hε
  have hfe := comp_dotProduct_mulVec_eq_of_eq_one hσ hQ hε hef
  obtain ⟨u₀, hu₀_ne, heu₀, hfu₀, hu₀_iso⟩ :=
    exists_isotropic_ne_zero_in_ortho hσ hQ hε he hfe hu₀ hw_span hu hw huw
  obtain ⟨z, -, -, -, hzu₀⟩ := exists_comp_dotProduct_mulVec_eq_zero_and_eq_one hσ hQ hdet htr
    hu₀_ne hu₀_iso
  obtain ⟨z₀, hez₀, hfz₀, hz_eq⟩ := exists_eq_add_and_comp_dotProduct_mulVec_eq_zero hε he hf hef
    hfe z
  have hz₀u₀ : (σ ∘ z₀) ⬝ᵥ (Q *ᵥ u₀) = ε := by
    rw [hz_eq] at hzu₀; simpa [TauCeti.map_comp_smul, smul_dotProduct, heu₀, hfu₀] using hzu₀
  obtain ⟨t, hy₀⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hu₀_iso
    (hz₀u₀ ▸ left_ne_zero_of_mul_eq_one hε)
  exact ⟨u₀, z₀ + t • u₀, heu₀, hfu₀,
    by simp [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hez₀, heu₀],
    by simp [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hfz₀, hfu₀], hu₀_iso, hy₀,
    by rw [comp_dotProduct_mulVec_swap hσ hQ hε]; simp [TauCeti.map_comp_smul, smul_dotProduct,
      hz₀u₀, hu₀_iso, hσε, hε],
    by simp [TauCeti.map_comp_smul, smul_dotProduct, hz₀u₀, hu₀_iso]⟩

/-- **Determinant of a matrix rescaling a hyperbolic pair and an orthogonal anisotropic vector.**
For involutive `σ` and `ε`-Hermitian `Q` with `ε * ε = 1`, if `A` rescales `(e, f)` by `c₁, c₂` and
an orthogonal anisotropic `v` by `c₃`, and fixes `{e, f, v}ᗮ`, then `A.det = c₁ * c₂ * c₃`. -/
theorem det_eq_mul_mul_of_mulVec_eq_smul {A : Matrix n n K} (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {e f v : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
    (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0)
    (hfv : (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0) (hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) ≠ 0) {c₁ c₂ c₃ : K}
    (hAe : A *ᵥ e = c₁ • e) (hAf : A *ᵥ f = c₂ • f) (hAv : A *ᵥ v = c₃ • v)
    (hAw : ∀ w : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0 →
      (σ ∘ v) ⬝ᵥ (Q *ᵥ w) = 0 → A *ᵥ w = w) : A.det = c₁ * c₂ * c₃ := by
  have hfe := comp_dotProduct_mulVec_eq_of_eq_one hσ hQ hε hef
  by_cases hc₃ : c₃ = 0
  · simp [hc₃, exists_mulVec_eq_zero_iff.mp
      ⟨v, left_ne_zero_of_comp_dotProduct_mulVec_ne_zero hvv, by simpa [hc₃] using hAv⟩]
  let M₃ : Matrix n n K := 1 - vecMulVec ((1 - c₃⁻¹) • v) (((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ • ((σ ∘ v) ᵥ* Q))
  have hM₃ {u} (hu : (σ ∘ v) ⬝ᵥ (Q *ᵥ u) = 0) : M₃ *ᵥ u = u := by
    rw [TauCeti.one_sub_vecMulVec_mulVec]; simp [← dotProduct_mulVec, hu]
  have hd₃ : M₃.det = c₃⁻¹ := by
    rw [TauCeti.det_one_sub_vecMulVec, smul_dotProduct, dotProduct_smul, ← dotProduct_mulVec,
      smul_eq_mul, smul_eq_mul]; field_simp; ring
  have hAM₃_v : (A * M₃) *ᵥ v = v := by
    rw [← mulVec_mulVec, TauCeti.one_sub_vecMulVec_mulVec]
    simp [← dotProduct_mulVec, hvv, mulVec_sub, mulVec_smul, hAv, smul_smul, sub_mul,
      inv_mul_cancel₀ hc₃]; module
  have hAM₃_w (w : n → K) (hew : (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0) (hfw : (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0) :
      (A * M₃) *ᵥ w = w := by
    obtain ⟨w₀, hvw₀, hw₀_ortho, hw_eq⟩ := exists_comp_dotProduct_mulVec_eq_zero_and_eq_add_smul hvv
      w
    rw [hw_eq, mulVec_add, mulVec_smul, hAM₃_v, ← mulVec_mulVec, hM₃ hvw₀,
      hAw w₀ (hw₀_ortho _ hev hew) (hw₀_ortho _ hfv hfw) hvw₀]
  rw [← inv_mul_cancel_right₀ hc₃ A.det, ← hd₃, ← det_mul, det_eq_mul_of_mulVec_eq_smul hε he hf
    hef hfe (by rw [← mulVec_mulVec, hM₃ ((comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hev), hAe])
    (by rw [← mulVec_mulVec, hM₃ ((comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hfv), hAf]) hAM₃_w]

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
