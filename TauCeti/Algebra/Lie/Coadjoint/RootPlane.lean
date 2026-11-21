/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical
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

The **height Hessian** `B.heightHessian p X` is the quadratic form `A ↦ -B(⁅A, p⁆, ⁅A, X⁆)` on
`L` (`LinearMap.BilinForm.heightHessian`); on a root plane it is `-α(p) α(X) B(A, A)`
(`TauCeti.IsRootPlane.heightHessian_apply`). For an invariant form and `⁅X, p⁆ = 0` its polar form
is `-2 B(⁅A, p⁆, ⁅C, X⁆)` (`LinearMap.BilinForm.polar_heightHessian`), and the stabilizer `L_ν`
of `ν = B p` lies in its radical (`LinearMap.BilinForm.lieAnnihilator_le_radical_heightHessian`),
so it descends to a quadratic form on `L ⧸ L_ν` (`LinearMap.BilinForm.liftHeightHessian`), the
Hessian of `f_X` at `p` read in the quotient coordinates `[A] ↦ ⁅A, p⁆`.

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
decomposition of `L` into a torus and orthogonal root planes, which gives the indices of the
height Hessian and the dimension of the orbit, is done in
`TauCeti.Algebra.Lie.Coadjoint.RootPlane.Decomposition`.

## Main definitions

* `TauCeti.IsRootPlane B t α E J`: `J` is a `B`-skew complex structure on `E` and every `H ∈ t`
  acts on `E` by `α(H) J`.
* `LinearMap.BilinForm.heightHessian B p X`: the quadratic form `A ↦ -B(⁅A, p⁆, ⁅A, X⁆)`.
* `LinearMap.BilinForm.liftHeightHessian`: the height Hessian on the tangent model `L ⧸ L_ν`.

## Main results

* `TauCeti.IsRootPlane.kksForm_mk`, `TauCeti.IsRootPlane.mul_kksForm_mk`: the KKS form on a root
  plane.
* `TauCeti.IsRootPlane.apply_lie_lie`, `TauCeti.IsRootPlane.mul_apply_lie_lie`: the form
  `B(q_p A, q_X C)` behind the height Hessian on a root plane, in quotient and in tangent
  coordinates.
* `LinearMap.BilinForm.lieAnnihilator_le_radical_heightHessian`: the height Hessian descends to
  the tangent model `L ⧸ L_ν`.
* `TauCeti.IsRootPlane.le_orthogonal`: for an invariant form, root planes with
  `α(H)² ≠ α'(H)²` for some `H ∈ t` are orthogonal.
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

namespace LinearMap.BilinForm

open QuadraticMap

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The **height Hessian** of `B` at `p` in the direction `X`: the quadratic form
`A ↦ -B(⁅A, p⁆, ⁅A, X⁆)` on `L`. When `B` is invariant and `⁅X, p⁆ = 0`, its value at `A` is the
second derivative at `t = 0` of the height `B(·, X)` along the adjoint orbit curve
`t ↦ Ad_(exp tA) p`, so it is the Hessian at the critical point `p` of the height on the orbit,
read in the quotient coordinate `A ↦ ⁅A, p⁆`. -/
def heightHessian (B : LinearMap.BilinForm R L) (p X : L) : QuadraticForm R L :=
  -LinearMap.BilinMap.toQuadraticMap (B.compl₁₂ (LieAlgebra.ad R L p) (LieAlgebra.ad R L X))

@[simp]
theorem heightHessian_apply (B : LinearMap.BilinForm R L) (p X A : L) :
    B.heightHessian p X A = -B ⁅A, p⁆ ⁅A, X⁆ := by
  simp only [heightHessian, _root_.neg_apply, LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.compl₁₂_apply, LieAlgebra.ad_apply, ← lie_skew A, map_neg, LinearMap.neg_apply,
    neg_neg]

/-- Negating the direction negates the height Hessian. -/
@[simp]
theorem heightHessian_neg_right (B : LinearMap.BilinForm R L) (p X : L) :
    B.heightHessian p (-X) = -B.heightHessian p X := by
  ext A
  simp only [heightHessian_apply, lie_neg, map_neg, neg_neg, _root_.neg_apply]

variable {B : LinearMap.BilinForm R L} {p X : L}

/-- **The polar form of the height Hessian.** For an invariant form and commuting `p` and `X`,
the symmetric bilinear form of the height Hessian is `(A, C) ↦ -B(⁅A, p⁆, ⁅C, X⁆)` (symmetric by
`LinearMap.BilinForm.lieInvariant.apply_lie_lie_comm`), so its polar
form is twice that. -/
theorem polar_heightHessian (hB : B.lieInvariant L) (hXp : ⁅X, p⁆ = 0) (A C : L) :
    polar (B.heightHessian p X) A C = -(2 * B ⁅A, p⁆ ⁅C, X⁆) := by
  simp only [polar, heightHessian_apply, add_lie, map_add, LinearMap.add_apply,
    hB.apply_lie_lie_comm hXp C A]
  ring

/-- **The height Hessian descends to the tangent model.** For an invariant form and commuting `p`
and `X`, the stabilizer `L_ν` of `ν = B p` lies in the radical of the height Hessian, which is
therefore induced by a quadratic form on the algebraic tangent model `L ⧸ L_ν` of the coadjoint
orbit through `ν` (`LinearMap.BilinForm.liftHeightHessian`). -/
theorem lieAnnihilator_le_radical_heightHessian (hB : B.lieInvariant L) (hXp : ⁅X, p⁆ = 0) :
    (TauCeti.lieAnnihilator R L (B p)).toSubmodule ≤ (B.heightHessian p X).radical := by
  intro A hA
  rw [LieSubalgebra.mem_toSubmodule, hB.mem_lieAnnihilator_iff] at hA
  refine mem_radical_iff'.mpr ⟨by simp [hA], fun C ↦ ?_⟩
  have hAC : B ⁅C, p⁆ ⁅A, X⁆ = 0 := by rw [← hB.apply_lie_lie_comm hXp, hA, LinearMap.zero_apply]
  simp only [heightHessian_apply, add_lie, map_add, LinearMap.add_apply, hA, hAC,
    LinearMap.zero_apply]
  ring

/-- **The height Hessian on the tangent model.** For an invariant form and commuting `p` and `X`,
the quadratic form on the algebraic tangent model `L ⧸ L_ν` of the coadjoint orbit through
`ν = B p` induced by the height Hessian
(`LinearMap.BilinForm.lieAnnihilator_le_radical_heightHessian`). -/
@[expose] def liftHeightHessian (hB : B.lieInvariant L) (hXp : ⁅X, p⁆ = 0) :
    QuadraticForm R (L ⧸ (TauCeti.lieAnnihilator R L (B p)).toSubmodule) :=
  (B.heightHessian p X).lift _ (lieAnnihilator_le_radical_heightHessian hB hXp)

@[simp]
theorem liftHeightHessian_mk (hB : B.lieInvariant L) (hXp : ⁅X, p⁆ = 0) (A : L) :
    liftHeightHessian hB hXp (Submodule.Quotient.mk A) = B.heightHessian p X A :=
  lift_mk _ A

end LinearMap.BilinForm

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

/-- **The height Hessian on a root plane.** For `p, X ∈ t` and `A` in a root plane with root `α`,
the height Hessian is `-α(p) α(X) B(A, A)`. -/
theorem heightHessian_apply (h : IsRootPlane B t α E J) (p X : t) (v : E) :
    B.heightHessian p X v = -(α p * α X * B v v) := by
  rw [LinearMap.BilinForm.heightHessian_apply, h.apply_lie_lie]

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

end Orthogonal

/-! #### Root planes and the stabilizer -/

/-- A root plane with `α(p) = 0` lies in the stabilizer of `B p`. -/
theorem le_lieAnnihilator (h : IsRootPlane B t α E J) (hB : B.lieInvariant L) {p : t}
    (hp : α p = 0) : E ≤ (lieAnnihilator R L (B p)).toSubmodule := fun v hv ↦ by
  rw [LieSubalgebra.mem_toSubmodule, hB.mem_lieAnnihilator_iff, h.lie_left ⟨v, hv⟩ p, hp,
    zero_smul, neg_zero, map_zero]

section Stabilizer

variable [IsDomain R]

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
