/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Algebra.Lie.Coadjoint
public import TauCeti.Algebra.Lie.InvariantForm.Basic

/-!
# Root planes and the coadjoint orbit through a torus element

Let `L` be a Lie algebra with an invariant bilinear form `B`, so that `p ↦ B p` identifies the
adjoint orbit of `p ∈ L` with the coadjoint orbit of `ν = B p ∈ L*`. For a compact Lie algebra, a
maximal abelian subalgebra `t` splits the rest of `L` into **root planes**: real planes `E_α`,
one for each pair of roots `±α`, carrying a rotation `J_α` with `J_α² = -1`, skew for `B`, such
that every `H ∈ t` acts on `E_α` by `ad H = α(H) J_α`
(`TauCeti.IsRootPlane B t α E J`). This file computes, on one such plane and for `p ∈ t`, the
quantities that determine the symplectic form and the height functions of the orbit through `p`.

Write `q_p A = ⁅A, p⁆` for the derivative at the identity of the orbit map `g ↦ Ad_g p`. Through
`B` it is the algebraic orbit derivative `⁅A, ν⁆ = B ⁅A, p⁆` of the coadjoint orbit
(`LinearMap.BilinForm.lieInvariant.lie_apply_eq`). On a root plane:

* `q_p = -α(p) J` (`TauCeti.IsRootPlane.lie_left`);
* the Kirillov–Kostant–Souriau form is `ω_ν([A], [C]) = α(p) B(J A, C)`
  (`TauCeti.IsRootPlane.kksForm_mk`), and in the tangent vectors `x = q_p A`, `y = q_p C` it reads
  `α(p) ω_ν = B(J x, y)`, that is `ω_ν(x, y) = B(J x, y) / α(p)`
  (`TauCeti.IsRootPlane.mul_kksForm_mk`);
* for `X ∈ t`, the form `B(q_p A, q_X C) = α(p) α(X) B(A, C)`
  (`TauCeti.IsRootPlane.apply_lie_lie`). With `X = p` this is the quotient-coordinate congruence
  `B(q_p A, q_p C) = α(p)² B(A, C)`, so in tangent vectors `x = q_p A`, `y = q_p C`,
  `α(p) B(q_p A, q_X C) = α(X) B(x, y)` (`TauCeti.IsRootPlane.mul_apply_lie_lie`).

These are formulas for `B(q_p A, q_X C)`. They read as the Hessian of the height `f_X = B(·, X)`
along the orbit at `p` when `B` is invariant and `⁅X, p⁆ = 0` (for instance when `t` is abelian):
then `p` is a critical point of `f_X` on its orbit, and `-B(q_p A, q_X A)` is the second derivative
of `t ↦ B(Ad_(exp tA) p, X)` at `t = 0`, computed in
`TauCeti.Geometry.Lie.Adjoint.Exponential.Height`. Polarization gives the Hessian bilinear form
`Hess_p f_X(q_p A, q_p C) = -α(X) α(p) B(A, C)`, that is `Hess_p f_X(x, y) = -α(X) B(x, y) / α(p)`
in tangent vectors. This needs no symmetry of `B`: for an invariant `B` with `⁅X, p⁆ = 0` the form
`(A, C) ↦ B(q_p A, q_X C)` is already symmetric
(`LinearMap.BilinForm.lieInvariant.apply_lie_lie_comm`).

For an invariant form, root planes whose roots satisfy `α(H)² ≠ α'(H)²` for some `H ∈ t` are
orthogonal (`TauCeti.IsRootPlane.le_orthogonal`), and two root planes that are orthogonal for `B`
contribute no cross terms to either form (`TauCeti.IsRootPlane.apply_lie_eq_zero_of_le_orthogonal`,
`TauCeti.IsRootPlane.apply_lie_lie_eq_zero_of_le_orthogonal`). For a nondegenerate form a root
plane is a tangent direction of the orbit through `p` exactly when `α(p) ≠ 0`: its nonzero vectors
stabilize `ν` exactly when `α(p) = 0` (`TauCeti.IsRootPlane.mem_lieAnnihilator_iff`), so a plane
with `α(p) ≠ 0` injects into the algebraic tangent model `L ⧸ L_ν`, while a plane with `α(p) = 0`
lies in the stabilizer (`TauCeti.IsRootPlane.le_lieAnnihilator`, which needs only invariance).

The formulas themselves are linear algebra over a commutative ring and need neither symmetry nor
positivity of `B`, and their reading as a Hessian bilinear form needs only invariance; the absence
of zero divisors and nondegeneracy enter only the orthogonality and stabilizer statements.

The root plane of `so(3)` and its height Hessian are worked out in
`TauCeti.Algebra.Lie.Orthogonal.CrossProduct.RootPlane`. Summing these formulas over a
decomposition of `L` into a torus and orthogonal root planes gives the indices of the height
Hessian (`TauCeti.Algebra.Lie.Coadjoint.Height`) and the dimension of the orbit
(`TauCeti.Algebra.Lie.Coadjoint.Height.TangentModel`).

## Main definitions

* `TauCeti.IsRootPlane B t α E J`: `J` is a `B`-skew complex structure on `E` and every `H ∈ t`
  acts on `E` by `α(H) J`.

## Main results

* `TauCeti.IsRootPlane.kksForm_mk`, `TauCeti.IsRootPlane.mul_kksForm_mk`: the KKS form on a root
  plane.
* `TauCeti.IsRootPlane.apply_lie_lie`, `TauCeti.IsRootPlane.mul_apply_lie_lie`: the form
  `B(q_p A, q_X C)` behind the height Hessian on a root plane, in quotient and in tangent
  coordinates.
* `TauCeti.IsRootPlane.le_orthogonal`: for an invariant form, root planes with
  `α(H)² ≠ α'(H)²` for some `H ∈ t` are orthogonal.
* `TauCeti.IsRootPlane.apply_eq_zero_of_forall_lie_eq_zero`: for an invariant form, a root plane
  with a nonzero root is orthogonal to every element commuting with `t`.
* `TauCeti.lie_mem_of_lie_eq_smul`: if every `H ∈ t` rotates a pair `x, y` by `α(H)`
  (`⁅H, x⁆ = α(H) y`, `⁅H, y⁆ = -α(H) x`, as `v, J v` on a root plane) and `t` contains every
  element commuting with it, then `⁅x, y⁆ ∈ t`; an invariant form pairs `H ∈ t` with `⁅x, y⁆` to
  `α(H) B(y, y)` (`LinearMap.BilinForm.lieInvariant.apply_lie_eq_mul_of_lie_eq_smul`).
* `LinearMap.BilinForm.lieInvariant.iIsOrtho_of_lie_eq_smul`,
  `LinearMap.BilinForm.lieInvariant.root_apply_lie_pos_of_lie_eq_smul`: for `α ≠ 0`, the triple
  `x, y, ⁅x, y⁆` is orthogonal for a symmetric invariant form, and `α(⁅x, y⁆) > 0` when the form is
  positive definite and `x ≠ 0`.
* `LinearMap.BilinForm.lieInvariant.lie_eq_smul_of_lie_eq_smul`: for a symmetric positive
  definite invariant form, `⁅x, y⁆ = B(y, y) • a` when `⁅x, y⁆ ∈ t` and `a ∈ t` represents `α`.
* `TauCeti.IsRootPlane.mem_lieAnnihilator_iff`: a root plane meets the stabilizer of `B p` only
  in `0` when `α(p) ≠ 0`, and lies in it when `α(p) = 0`.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281.
* M. Audin, *Torus Actions on Symplectic Manifolds*, 2nd ed., Progress in Mathematics 93,
  Birkhäuser, 2004, Chapter II (coadjoint orbits and their height functions).
-/

public section

open Module (Dual)

namespace TauCeti

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- `E` is a **root plane** of `t` for the bilinear form `B`, with rotation `J` and root `α`:
`J` is a complex structure on `E` (`J² = -1`) which is skew for `B`, and every `H ∈ t` acts on
`E` by `ad H = α(H) J`. For a compact Lie algebra with a positive invariant form and a maximal
abelian subalgebra `t`, these are the real planes of the root decomposition, one for each pair of
roots `±α`. -/
structure IsRootPlane (B : LinearMap.BilinForm R L) (t : Submodule R L) (α : Dual R t)
    (E : Submodule R L) (J : Module.End R E) : Prop where
  /-- The rotation is a complex structure: `J (J v) = -v`. -/
  apply_apply (v : E) : J (J v) = -v
  /-- The rotation is skew for `B`. -/
  apply_left (v w : E) : B (J v) w = -B v (J w)
  /-- Every `H ∈ t` acts on the plane by `α(H) J`. -/
  lie_apply (H : t) (v : E) : ⁅(H : L), (v : L)⁆ = α H • (J v : L)

/-! ### Root pairs -/

section RootPair

variable {t : Submodule R L} {α : Dual R t} {x y : L}

/-- If every `H ∈ t` rotates the pair `x, y` by `α(H)`, then `⁅x, y⁆` commutes with `t`. -/
theorem lie_lie_eq_zero_of_lie_eq_smul (hx : ∀ H : t, ⁅(H : L), x⁆ = α H • y)
    (hy : ∀ H : t, ⁅(H : L), y⁆ = -(α H • x)) (H : t) : ⁅(H : L), ⁅x, y⁆⁆ = 0 := by
  rw [leibniz_lie, hx, hy]
  simp

/-- If every `H ∈ t` rotates the pair `x, y` by `α(H)`, and `t` contains every element commuting
with it, then `⁅x, y⁆ ∈ t`. -/
theorem lie_mem_of_lie_eq_smul (ht : ∀ z : L, (∀ H : t, ⁅(H : L), z⁆ = 0) → z ∈ t)
    (hx : ∀ H : t, ⁅(H : L), x⁆ = α H • y) (hy : ∀ H : t, ⁅(H : L), y⁆ = -(α H • x)) :
    ⁅x, y⁆ ∈ t :=
  ht _ (lie_lie_eq_zero_of_lie_eq_smul hx hy)

end RootPair

namespace IsRootPlane

variable {B : LinearMap.BilinForm R L} {t : Submodule R L} {α : Dual R t} {E : Submodule R L}
  {J : Module.End R E}

/-- The rotation of a root plane preserves `B`: `B (J v) (J w) = B v w`. -/
theorem apply_map_map (h : IsRootPlane B t α E J) (v w : E) :
    B (J v) (J w) = B v w := by
  rw [h.apply_left, h.apply_apply, Submodule.coe_neg, map_neg, neg_neg]

/-- The rotation of a root plane is injective. -/
theorem injective (h : IsRootPlane B t α E J) : Function.Injective J := fun v w hvw ↦ by
  rw [← neg_neg v, ← h.apply_apply v, hvw, h.apply_apply, neg_neg]

/-- **The orbit derivative on a root plane.** The derivative `q_p A = ⁅A, p⁆` at the identity
of the orbit map through `p ∈ t` is `-α(p) J` on a root plane. -/
theorem lie_left (h : IsRootPlane B t α E J) (v : E) (H : t) :
    ⁅(v : L), (H : L)⁆ = -(α H • (J v : L)) := by
  rw [← lie_skew, h.lie_apply]

/-- The Kirillov form of `B p`, for `p ∈ t`, with one argument in a root plane:
`B p ⁅A, C⁆ = α(p) B(J A, C)` for `A` in the plane and any `C`. -/
theorem apply_lie (h : IsRootPlane B t α E J) (hB : B.lieInvariant L) (p : t) (v : E) (w : L) :
    B p ⁅(v : L), w⁆ = α p * B (J v) w := by
  have hinv := hB (v : L) (p : L) (w : L)
  rw [h.lie_left, map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul]
    at hinv
  linear_combination hinv

/-- **The Kirillov–Kostant–Souriau form on a root plane.** For `p ∈ t` and `ν = B p`, the KKS
form on the algebraic tangent model `L ⧸ L_ν` of the coadjoint orbit through `ν` is
`ω_ν([A], [C]) = α(p) B(J A, C)` on the root plane. -/
theorem kksForm_mk (h : IsRootPlane B t α E J) (hB : B.lieInvariant L) (p : t) (v w : E) :
    Dual.kksForm (B p) (Submodule.Quotient.mk (v : L)) (Submodule.Quotient.mk (w : L)) =
      α p * B (J v) w := by
  rw [Dual.kksForm_mk, h.apply_lie hB]

/-- **The Kirillov–Kostant–Souriau form in tangent vectors.** Let `x = q_p A` and `y = q_p C`
be the tangent vectors at `p` of the orbit generated by `A, C` in a root plane, so that
`x = ⁅A, p⁆` and `y = ⁅C, p⁆` (these lie in the plane by `TauCeti.IsRootPlane.lie_left`). Then
`α(p) ω_ν([A], [C]) = B(J x, y)`; when `α(p)` is invertible, `ω_ν(x, y) = B(J x, y) / α(p)`. -/
theorem mul_kksForm_mk (h : IsRootPlane B t α E J) (hB : B.lieInvariant L) (p : t)
    {v w x y : E} (hx : (x : L) = ⁅(v : L), (p : L)⁆) (hy : (y : L) = ⁅(w : L), (p : L)⁆) :
    α p * Dual.kksForm (B p) (Submodule.Quotient.mk (v : L)) (Submodule.Quotient.mk (w : L)) =
      B (J x) y := by
  -- The orbit derivative `⁅u, p⁆ = -(α(p) • J u)` (`lie_left`), read in the plane `E`.
  have hq {u z : E} (hz : (z : L) = ⁅(u : L), (p : L)⁆) : z = -(α p • J u) :=
    Subtype.ext (by rw [hz, h.lie_left, Submodule.coe_neg, Submodule.coe_smul])
  have hJx : J x = α p • v := by
    rw [hq hx, map_neg, map_smul, h.apply_apply, smul_neg, neg_neg]
  rw [h.kksForm_mk hB, hJx, hq hy]
  simp only [Submodule.coe_neg, Submodule.coe_smul, map_neg, map_smul, LinearMap.smul_apply,
    smul_eq_mul, h.apply_left v w]
  ring

/-- **The form behind the height Hessian on a root plane.** For `p, X ∈ t` and `A, C` in a root
plane, `B(q_p A, q_X C) = α(p) α(X) B(A, C)`. When `B` is invariant and
`⁅X, p⁆ = 0` (for instance when `t` is abelian), its negative `-B(⁅A, p⁆, ⁅C, X⁆)` is the Hessian
at the critical point `p` of the height `f_X = B(·, X)` along the orbit through `p`, so
`Hess_p f_X(q_p A, q_p C) = -α(X) α(p) B(A, C)`. -/
theorem apply_lie_lie (h : IsRootPlane B t α E J) (p X : t) (v w : E) :
    B ⁅(v : L), (p : L)⁆ ⁅(w : L), (X : L)⁆ = α p * α X * B v w := by
  rw [h.lie_left, h.lie_left]
  simp only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul,
    h.apply_map_map]
  ring

/-- **The quotient-coordinate congruence.** For `p ∈ t` and `A, C` in a root plane, the tangent
vectors `q_p A = ⁅A, p⁆` and `q_p C = ⁅C, p⁆` satisfy `B(q_p A, q_p C) = α(p)² B(A, C)`. -/
theorem apply_lie_lie_self (h : IsRootPlane B t α E J) (p : t) (v w : E) :
    B ⁅(v : L), (p : L)⁆ ⁅(w : L), (p : L)⁆ = α p ^ 2 * B v w := by
  rw [h.apply_lie_lie, sq]

/-- **The height Hessian in tangent vectors.** For `p, X ∈ t` and the tangent vectors
`x = q_p A`, `y = q_p C` of the orbit at `p`, `α(p) (-B(⁅A, p⁆, ⁅C, X⁆)) = -α(X) B(x, y)`. When
`B` is invariant and `⁅X, p⁆ = 0`, the factor `-B(⁅A, p⁆, ⁅C, X⁆)` is
`Hess_p f_X(x, y)` (`TauCeti.IsRootPlane.apply_lie_lie`), so when `α(p)` is also invertible,
`Hess_p f_X(x, y) = -α(X) B(x, y) / α(p)`. -/
theorem mul_apply_lie_lie (h : IsRootPlane B t α E J) (p X : t) (v w : E) :
    α p * -B ⁅(v : L), (p : L)⁆ ⁅(w : L), (X : L)⁆ =
      -(α X * B ⁅(v : L), (p : L)⁆ ⁅(w : L), (p : L)⁆) := by
  rw [h.apply_lie_lie, h.apply_lie_lie_self]
  ring

/-! #### Orthogonal root planes -/

section Orthogonal

variable {α' : Dual R t} {E' : Submodule R L} {J' : Module.End R E'}

/-- **Root planes with distinct roots are orthogonal.** For an invariant form `B`, if
`α(H)² ≠ α'(H)²` for some `H ∈ t` (so `α ≠ ±α'`), the root planes of `α` and `α'` are orthogonal
for `B`. -/
theorem le_orthogonal [NoZeroDivisors R] (h : IsRootPlane B t α E J)
    (h' : IsRootPlane B t α' E' J') (hB : B.lieInvariant L) {H : t} (hH : α H ^ 2 ≠ α' H ^ 2) :
    E' ≤ B.orthogonal E := by
  -- Invariance under `H`: `α(H) B(J v, w) = -α'(H) B(v, J' w)`.
  have key (v : E) (w : E') : α H * B (J v) w = -(α' H * B v (J' w)) := by
    have hinv := hB (H : L) (v : L) (w : L)
    rwa [h.lie_apply, h'.lie_apply, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
      smul_eq_mul] at hinv
  intro w hw v hv
  have h₁ := key (J ⟨v, hv⟩) ⟨w, hw⟩
  have h₂ := key ⟨v, hv⟩ (J' ⟨w, hw⟩)
  rw [h.apply_apply, Submodule.coe_neg, map_neg, LinearMap.neg_apply] at h₁
  rw [h'.apply_apply, Submodule.coe_neg, map_neg] at h₂
  have hzero : (α H ^ 2 - α' H ^ 2) * B v w = 0 := by
    linear_combination (-α H) * h₁ + α' H * h₂
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hH)

/-- **No cross terms in the KKS form.** If two root planes are orthogonal for `B` (for instance
by `TauCeti.IsRootPlane.le_orthogonal`), the Kirillov form of `B p`, `p ∈ t`, pairs them to
zero. -/
theorem apply_lie_eq_zero_of_le_orthogonal (h : IsRootPlane B t α E J) (hB : B.lieInvariant L)
    (horth : E' ≤ B.orthogonal E) (p : t) (v : E) (w : E') :
    B p ⁅(v : L), (w : L)⁆ = 0 := by
  rw [h.apply_lie hB, show B (J v) w = 0 from horth w.property _ (J v).property, mul_zero]

/-- **No cross terms in the height Hessian.** If two root planes are orthogonal for `B` (for
instance by `TauCeti.IsRootPlane.le_orthogonal`), then `B(q_p A, q_X C) = 0` for `p, X ∈ t`, `A`
in the first plane and `C` in the second. -/
theorem apply_lie_lie_eq_zero_of_le_orthogonal (h : IsRootPlane B t α E J)
    (h' : IsRootPlane B t α' E' J') (horth : E' ≤ B.orthogonal E) (p X : t) (v : E) (w : E') :
    B ⁅(v : L), (p : L)⁆ ⁅(w : L), (X : L)⁆ = 0 := by
  have hzero : B (J v) (J' w) = 0 := horth (J' w).property _ (J v).property
  rw [h.lie_left, h'.lie_left]
  simp [hzero]

/-- **A root plane is orthogonal to the centralizer of `t`.** For an invariant form `B` and a root
plane with a nonzero root, `B(H, v) = 0` for every `H` commuting with `t` and every `v` in the
plane. In particular a root plane is orthogonal to an abelian `t`. -/
theorem apply_eq_zero_of_forall_lie_eq_zero [NoZeroDivisors R] (h : IsRootPlane B t α E J)
    (hB : B.lieInvariant L) (hα : α ≠ 0) {H : L} (hH : ∀ H' : t, ⁅(H' : L), H⁆ = 0) (v : E) :
    B H v = 0 := by
  obtain ⟨H', hH'⟩ : ∃ H' : t, α H' ≠ 0 := by
    by_contra! h'
    exact hα (LinearMap.ext h')
  -- Invariance under `H'`: `α(H') B(H, J w) = B(H, ⁅H', w⁆) = -B(⁅H', H⁆, w) = 0`.
  have key (w : E) : α H' * B H (J w) = 0 := by
    have hinv := hB (H' : L) H (w : L)
    rw [hH H', map_zero, LinearMap.zero_apply, h.lie_apply, map_smul, smul_eq_mul] at hinv
    linear_combination hinv
  -- Every `v` is `-J (J v)`.
  have hv := key (J v)
  rw [h.apply_apply, Submodule.coe_neg, map_neg, mul_neg, neg_eq_zero] at hv
  exact (mul_eq_zero.mp hv).resolve_left hH'

end Orthogonal

/-! #### Root planes and the stabilizer -/

/-- A root plane with `α(p) = 0` lies in the stabilizer of `B p`. -/
theorem le_lieAnnihilator (h : IsRootPlane B t α E J) (hB : B.lieInvariant L) {p : t}
    (hp : α p = 0) : E ≤ (lieAnnihilator R L (B p)).toSubmodule := fun v hv ↦ by
  rw [LieSubalgebra.mem_toSubmodule, hB.mem_lieAnnihilator_iff, h.lie_left ⟨v, hv⟩ p, hp,
    zero_smul, neg_zero, map_zero]

section Stabilizer

variable [IsDomain R]

/-- An element `H ∈ t` commutes with a vector `v` of a root plane exactly when `α(H) = 0` or
`v = 0`. -/
theorem lie_eq_zero_iff [Module.IsTorsionFree R L] (h : IsRootPlane B t α E J) (H : t) (v : E) :
    ⁅(H : L), (v : L)⁆ = 0 ↔ α H = 0 ∨ v = 0 := by
  rw [h.lie_apply]
  simp [map_eq_zero_iff J h.injective]

/-- **Root planes and the coadjoint stabilizer.** For a separating invariant form `B` and
`p ∈ t`, a vector `A` of a root plane stabilizes `ν = B p` exactly when `α(p) = 0` or `A = 0`.
So a root plane with `α(p) = 0` lies in the stabilizer `L_ν`, and one with `α(p) ≠ 0` meets it
only in `0`: it is a plane of tangent directions of the orbit through `ν`. -/
theorem mem_lieAnnihilator_iff (h : IsRootPlane B t α E J) (hB : B.lieInvariant L)
    (hsep : B.SeparatingLeft) (p : t) (v : E) :
    (v : L) ∈ lieAnnihilator R L (B p) ↔ α p = 0 ∨ v = 0 := by
  have hinj : Function.Injective B :=
    LinearMap.ker_eq_bot.mp ((LinearMap.separatingLeft_iff_ker_eq_bot).mp hsep)
  rw [hB.mem_lieAnnihilator_iff, h.lie_left]
  simp [map_eq_zero_iff B hinj, map_eq_zero_iff J h.injective]

/-- A root plane with `α(p) ≠ 0` meets the stabilizer of `B p` only in `0`, so it injects into
the algebraic tangent model `L ⧸ L_ν` of the coadjoint orbit through `ν = B p`. -/
theorem disjoint_lieAnnihilator (h : IsRootPlane B t α E J) (hB : B.lieInvariant L)
    (hsep : B.SeparatingLeft) {p : t} (hp : α p ≠ 0) :
    Disjoint E (lieAnnihilator R L (B p)).toSubmodule := by
  rw [Submodule.disjoint_def]
  intro v hv hv'
  have := (h.mem_lieAnnihilator_iff hB hsep p ⟨v, hv⟩).mp hv'
  simpa [hp] using this

end Stabilizer

end IsRootPlane

end TauCeti

namespace LinearMap.BilinForm.lieInvariant

variable {R L : Type*} [LieRing L]

section CommRing

variable [CommRing R] [LieAlgebra R L] {B : LinearMap.BilinForm R L} {t : Submodule R L}
  {α : Dual R t} {x y : L}

/-- If every `H ∈ t` rotates the pair `x, y` by `α(H)`, then an invariant form pairs `H` with
`⁅x, y⁆` to `α(H) B(y, y)`. -/
theorem apply_lie_eq_mul_of_lie_eq_smul (hB : B.lieInvariant L)
    (hx : ∀ H : t, ⁅(H : L), x⁆ = α H • y) (H : t) : B H ⁅x, y⁆ = α H * B y y := by
  have h := hB x H y
  simp [← lie_skew x (H : L), hx] at h
  exact h.symm

/-- If every `H ∈ t` rotates the pair `x, y` by a nonzero `α`, then `x`, `y` and `⁅x, y⁆` are
orthogonal for a symmetric invariant form. -/
theorem iIsOrtho_of_lie_eq_smul [NoZeroDivisors R] [NeZero (2 : R)] (hB : B.lieInvariant L)
    (hBs : B.IsSymm) (hα : α ≠ 0) (hx : ∀ H : t, ⁅(H : L), x⁆ = α H • y) :
    B.iIsOrtho ![x, y, ⁅x, y⁆] := by
  obtain ⟨H₀, hH₀⟩ : ∃ H₀, α H₀ ≠ 0 := by simpa using DFunLike.ne_iff.mp hα
  -- `B(x, y) = -B(y, x)` by invariance under `H₀`, and `B` is symmetric.
  have hxy : B x y = 0 := by
    have h : α H₀ * B x y = -(α H₀ * B x y) := by simpa [hx, hBs.eq y x] using hB H₀ x x
    have h2 : 2 * (α H₀ * B x y) = 0 := by linear_combination h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left two_ne_zero)).resolve_left hH₀
  -- `B(⁅x, y⁆, x) = -B(y, ⁅x, x⁆)` and `B(⁅y, x⁆, y) = -B(x, ⁅y, y⁆)` vanish.
  have hZx : B ⁅x, y⁆ x = 0 := by simpa using hB x y x
  have hZy : B ⁅x, y⁆ y = 0 := by
    rw [← lie_skew, map_neg, LinearMap.neg_apply, neg_eq_zero]
    simpa using hB y x y
  rw [iIsOrtho_def]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [hxy, hZx, hZy, hBs.eq y x, hBs.eq x ⁅x, y⁆, hBs.eq y ⁅x, y⁆] at hij ⊢

end CommRing

section OrderedCommRing

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [LieAlgebra R L]
  {B : LinearMap.BilinForm R L} {t : Submodule R L} {α : Dual R t} {x y : L}

/-- If every `H ∈ t` rotates the pair `x ≠ 0, y` by a nonzero `α`, and `⁅x, y⁆ ∈ t`, then
`α(⁅x, y⁆) > 0` for a positive definite invariant form, since
`B(⁅x, y⁆, ⁅x, y⁆) = α(⁅x, y⁆) B(y, y)`. This is the positivity that normalizes the coroot of
`α`. -/
theorem root_apply_lie_pos_of_lie_eq_smul (hB : B.lieInvariant L) (hBp : B.toQuadraticMap.PosDef)
    (hα : α ≠ 0) (hx0 : x ≠ 0) (hx : ∀ H : t, ⁅(H : L), x⁆ = α H • y)
    (hy : ∀ H : t, ⁅(H : L), y⁆ = -(α H • x)) (hxy : ⁅x, y⁆ ∈ t) :
    0 < α ⟨⁅x, y⁆, hxy⟩ := by
  obtain ⟨H₀, hH₀⟩ : ∃ H₀, α H₀ ≠ 0 := by simpa using DFunLike.ne_iff.mp hα
  have hpos (v : L) (hv : v ≠ 0) : 0 < B v v := by simpa using hBp v hv
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h := hy H₀
    rw [lie_zero, eq_comm, neg_eq_zero] at h
    have h₀ : α H₀ * B x x = 0 := by simpa using congr(B $h x)
    exact (mul_ne_zero hH₀ (hpos x hx0).ne') h₀
  have hBZ := hB.apply_lie_eq_mul_of_lie_eq_smul hx
  have hZ0 : ⁅x, y⁆ ≠ 0 := by
    intro h
    have h₀ := hBZ H₀
    rw [h, map_zero, eq_comm] at h₀
    exact (mul_ne_zero hH₀ (hpos y hy0).ne') h₀
  exact (pos_iff_pos_of_mul_pos (hBZ _ ▸ hpos _ hZ0)).mpr (hpos y hy0)

omit [IsStrictOrderedRing R] in
/-- If every `H ∈ t` rotates the pair `x, y` by `α(H)`, `⁅x, y⁆ ∈ t`, and `a ∈ t` represents `α`
through a symmetric positive definite invariant form `B`, then `⁅x, y⁆ = B(y, y) • a`: the
bracket points in the coroot direction of `α`. -/
theorem lie_eq_smul_of_lie_eq_smul (hB : B.lieInvariant L) (hBs : B.IsSymm)
    (hBp : B.toQuadraticMap.PosDef) (hx : ∀ H : t, ⁅(H : L), x⁆ = α H • y) (hxy : ⁅x, y⁆ ∈ t)
    {a : t} (ha : ∀ H : t, B a H = α H) : ⁅x, y⁆ = B y y • (a : L) := by
  -- `d = ⁅x, y⁆ - B(y, y) • a ∈ t` pairs with itself to `α(d) B(y, y) - B(y, y) α(d) = 0`.
  set d : t := ⟨⁅x, y⁆, hxy⟩ - B y y • a
  have h₁ : B d ⁅x, y⁆ = α d * B y y := hB.apply_lie_eq_mul_of_lie_eq_smul hx d
  have h₂ : B d a = α d := by rw [← ha, hBs.eq]
  have hd : (d : L) = 0 := by
    refine hBp.anisotropic _ ?_
    simp only [LinearMap.BilinMap.toQuadraticMap_apply]
    calc B (d : L) d = B d ⁅x, y⁆ - B y y * B d a := by simp [d, map_sub]
      _ = 0 := by rw [h₁, h₂]; ring
  exact sub_eq_zero.mp hd

end OrderedCommRing

end LinearMap.BilinForm.lieInvariant
