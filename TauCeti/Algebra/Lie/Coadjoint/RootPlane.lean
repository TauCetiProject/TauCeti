/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint
public import TauCeti.Algebra.Lie.InvariantForm.Basic
public import TauCeti.Algebra.Lie.Orthogonal.CrossProduct

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
  (`TauCeti.IsRootPlane.apply_lie_lie`). Its negative is the Hessian of the height
  `f_X = B(·, X)` along the orbit at `p`, the second derivative of `t ↦ B(Ad_(exp tA) p, X)`
  computed in `TauCeti.Geometry.Lie.Adjoint.Exponential.Height`:
  `Hess_p f_X(q_p A, q_p C) = -α(X) α(p) B(A, C)`. With `X = p` the identity is the
  quotient-coordinate congruence `B(q_p A, q_p C) = α(p)² B(A, C)`, so in tangent vectors
  `Hess_p f_X(x, y) = -α(X) B(x, y) / α(p)` (`TauCeti.IsRootPlane.mul_apply_lie_lie`).

Two root planes that are orthogonal for `B` contribute no cross terms to either form
(`TauCeti.IsRootPlane.apply_lie_eq_zero_of_le_orthogonal`,
`TauCeti.IsRootPlane.apply_lie_lie_eq_zero_of_le_orthogonal`). For a nondegenerate form a root
plane is a tangent direction of the orbit through `p` exactly when `α(p) ≠ 0`: its nonzero vectors
stabilize `ν` exactly when `α(p) = 0` (`TauCeti.IsRootPlane.mem_lieAnnihilator_iff`), so a plane
with `α(p) ≠ 0` injects into the algebraic tangent model `L ⧸ L_ν`, while a plane with `α(p) = 0`
lies in the stabilizer.

All of this is linear algebra over a commutative ring and needs neither symmetry nor positivity
of `B`; nondegeneracy and the absence of zero divisors enter only the stabilizer statements.

As an example, `so(3) ≅ (R³, ⨯₃)` with the dot product (`TauCeti.soThreeForm`) has the root plane
`E = ẑ^⊥` of `t = R ẑ`, where `ẑ` is the hat matrix of the third standard basis vector, with
rotation `J = ad ẑ` and root `α(c ẑ) = c` (`TauCeti.isRootPlane_soThree`). For `p = r ẑ` and
`X = a ẑ` the formulas above give the Hessian `-a B / r` of the height on the tangent plane of the
coadjoint sphere of radius `r` (`TauCeti.soThreeForm_lie_lie_smul_soThreeZ`).

## Main definitions

* `TauCeti.IsRootPlane B t α E J`: `J` is a `B`-skew complex structure on `E` and every `H ∈ t`
  acts on `E` by `α(H) J`.
* `TauCeti.soThreeForm`: the dot product on `so(3)`, read through the hat map.

## Main results

* `TauCeti.IsRootPlane.kksForm_mk`, `TauCeti.IsRootPlane.mul_kksForm_mk`: the KKS form on a root
  plane.
* `TauCeti.IsRootPlane.apply_lie_lie`, `TauCeti.IsRootPlane.mul_apply_lie_lie`: the height
  Hessian on a root plane, in quotient and in tangent coordinates.
* `TauCeti.IsRootPlane.mem_lieAnnihilator_iff`: a root plane meets the stabilizer of `B p` only
  in `0` when `α(p) ≠ 0`, and lies in it when `α(p) = 0`.
* `TauCeti.isRootPlane_soThree`: the root plane of `so(3)`, and
  `TauCeti.soThreeForm_lie_lie_smul_soThreeZ`: its height Hessian.

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

/-- The Kirillov form of `B p`, for `p ∈ t`, on a root plane: `B p ⁅A, C⁆ = α(p) B(J A, C)`. -/
theorem apply_lie (h : IsRootPlane B t α E J) (hB : B.lieInvariant L) (p : t) (v w : E) :
    B p ⁅(v : L), (w : L)⁆ = α p * B (J v) w := by
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
  have hJx : J x = α p • v := by
    rw [show x = -(α p • J v) from Subtype.ext (by rw [hx, h.lie_left]; rfl), map_neg, map_smul,
      h.apply_apply, smul_neg, neg_neg]
  have hy' : y = -(α p • J w) := Subtype.ext (by rw [hy, h.lie_left]; rfl)
  rw [h.kksForm_mk hB, hJx, hy']
  simp only [Submodule.coe_neg, Submodule.coe_smul, map_neg, map_smul, LinearMap.smul_apply,
    smul_eq_mul, h.apply_left v w]
  ring

/-- **The height Hessian on a root plane.** For `p, X ∈ t` and `A, C` in a root plane,
`B(q_p A, q_X C) = α(p) α(X) B(A, C)`. Its negative `-B(⁅A, p⁆, ⁅C, X⁆)` is the Hessian at `p` of
the height `f_X = B(·, X)` along the orbit through `p`, so
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
`x = q_p A`, `y = q_p C` of the orbit at `p`, `α(p) Hess_p f_X(x, y) = -α(X) B(x, y)`, where
`Hess_p f_X(q_p A, q_p C) = -B(⁅A, p⁆, ⁅C, X⁆)`; when `α(p)` is invertible,
`Hess_p f_X(x, y) = -α(X) B(x, y) / α(p)`. -/
theorem mul_apply_lie_lie (h : IsRootPlane B t α E J) (p X : t) (v w : E) :
    α p * -B ⁅(v : L), (p : L)⁆ ⁅(w : L), (X : L)⁆ =
      -(α X * B ⁅(v : L), (p : L)⁆ ⁅(w : L), (p : L)⁆) := by
  rw [h.apply_lie_lie, h.apply_lie_lie_self]
  ring

/-! #### Orthogonal root planes -/

section Orthogonal

variable {α' : Dual R t} {E' : Submodule R L} {J' : Module.End R E'}

/-- **No cross terms in the KKS form.** If two root planes are orthogonal for `B`, the Kirillov
form of `B p`, `p ∈ t`, pairs them to zero. -/
theorem apply_lie_eq_zero_of_le_orthogonal (h : IsRootPlane B t α E J) (hB : B.lieInvariant L)
    (horth : E' ≤ B.orthogonal E) (p : t) (v : E) (w : E') :
    B p ⁅(v : L), (w : L)⁆ = 0 := by
  have hinv := hB (v : L) (p : L) (w : L)
  have hzero : B (J v) w = 0 := horth w.2 _ (J v).2
  rw [h.lie_left, map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, hzero,
    smul_zero, neg_zero] at hinv
  exact neg_eq_zero.mp hinv.symm

/-- **No cross terms in the height Hessian.** If two root planes are orthogonal for `B`, then
`B(q_p A, q_X C) = 0` for `p, X ∈ t`, `A` in the first plane and `C` in the second. -/
theorem apply_lie_lie_eq_zero_of_le_orthogonal (h : IsRootPlane B t α E J)
    (h' : IsRootPlane B t α' E' J') (horth : E' ≤ B.orthogonal E) (p X : t) (v : E) (w : E') :
    B ⁅(v : L), (p : L)⁆ ⁅(w : L), (X : L)⁆ = 0 := by
  have hzero : B (J v) (J' w) = 0 := horth (J' w).2 _ (J v).2
  rw [h.lie_left, h'.lie_left]
  simp [hzero]

end Orthogonal

/-! #### Root planes and the stabilizer -/

section Stabilizer

variable [IsDomain R] [Module.IsTorsionFree R L]

/-- **Root planes and the coadjoint stabilizer.** For a separating invariant form `B` and
`p ∈ t`, a vector `A` of a root plane stabilizes `ν = B p` exactly when `α(p) = 0` or `A = 0`.
So a root plane with `α(p) = 0` lies in the stabilizer `L_ν`, and one with `α(p) ≠ 0` meets it
only in `0`: it is a plane of tangent directions of the orbit through `ν`. -/
theorem mem_lieAnnihilator_iff (h : IsRootPlane B t α E J) (hB : B.lieInvariant L)
    (hsep : B.SeparatingLeft) (p : t) (v : E) :
    (v : L) ∈ lieAnnihilator R L (B p) ↔ α p = 0 ∨ v = 0 := by
  rw [mem_lieAnnihilator, hB.lie_apply_eq, ← LinearMap.mem_ker,
    (LinearMap.separatingLeft_iff_ker_eq_bot).mp hsep, Submodule.mem_bot, h.lie_left, neg_eq_zero,
    smul_eq_zero, ZeroMemClass.coe_eq_zero, map_eq_zero_iff J h.injective]

/-- A root plane with `α(p) = 0` lies in the stabilizer of `B p`. -/
theorem le_lieAnnihilator (h : IsRootPlane B t α E J) (hB : B.lieInvariant L)
    (hsep : B.SeparatingLeft) {p : t} (hp : α p = 0) :
    E ≤ (lieAnnihilator R L (B p)).toSubmodule := fun v hv ↦
  (h.mem_lieAnnihilator_iff hB hsep p ⟨v, hv⟩).mpr (.inl hp)

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

/-! ### Example: the root plane of `so(3)` -/

section SoThree

open Matrix LieAlgebra.Orthogonal

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R] [NoZeroDivisors R] [NeZero (2 : R)]

/-- The dot product on `so(3)`, read through the hat map: `B(û, v̂) = u ⬝ᵥ v`. -/
def soThreeForm : LinearMap.BilinForm R (so (Fin 3) R) :=
  (soThreeDualEquiv R).toLinearMap ∘ₗ (soThreeEquiv R).symm.toLinearMap

variable {R}

@[simp]
theorem soThreeForm_apply_soThreeEquiv (u v : Fin 3 → R) :
    soThreeForm R (soThreeEquiv R u) (soThreeEquiv R v) = u ⬝ᵥ v := by
  simp [soThreeForm]

/-- The dot product on `so(3)` is invariant: `(u ⨯₃ v) ⬝ᵥ w = -(v ⬝ᵥ (u ⨯₃ w))`. -/
theorem lieInvariant_soThreeForm : (soThreeForm R).lieInvariant (so (Fin 3) R) := by
  intro x y z
  obtain ⟨u, rfl⟩ := (soThreeEquiv R).surjective x
  obtain ⟨v, rfl⟩ := (soThreeEquiv R).surjective y
  obtain ⟨w, rfl⟩ := (soThreeEquiv R).surjective z
  simp only [lie_soThreeEquiv, soThreeForm_apply_soThreeEquiv, cross_apply, dotProduct,
    Fin.sum_univ_three]
  simp
  ring

/-- The dot product on `so(3)` is nondegenerate. -/
theorem separatingLeft_soThreeForm : (soThreeForm R).SeparatingLeft := by
  intro x hx
  obtain ⟨u, rfl⟩ := (soThreeEquiv R).surjective x
  have h (i : Fin 3) : u i = 0 := by
    simpa [dotProduct, Fin.sum_univ_three, Pi.single_apply] using
      hx (soThreeEquiv R (Pi.single i 1))
  rw [show u = 0 from funext h, map_zero]

variable (R) in
/-- The generator `ẑ ∈ so(3)` of the rotations about the third axis. -/
abbrev soThreeZ : so (Fin 3) R := soThreeEquiv R ![0, 0, 1]

/-- The rotation `ad ẑ` preserves the plane `ẑ^⊥`. -/
theorem lie_soThreeZ_mem_ker {x : so (Fin 3) R}
    (hx : x ∈ LinearMap.ker (soThreeForm R (soThreeZ R))) :
    ⁅soThreeZ R, x⁆ ∈ LinearMap.ker (soThreeForm R (soThreeZ R)) := by
  obtain ⟨u, rfl⟩ := (soThreeEquiv R).surjective x
  simp only [LinearMap.mem_ker, lie_soThreeEquiv, soThreeForm_apply_soThreeEquiv] at hx ⊢
  exact dot_self_cross _ _

variable (R) in
/-- The rotation `J = ad ẑ` of the plane `ẑ^⊥` of `so(3)`. -/
def soThreeRotation : Module.End R (LinearMap.ker (soThreeForm R (soThreeZ R))) :=
  (LieAlgebra.ad R (so (Fin 3) R) (soThreeZ R)).restrict fun _ ↦ lie_soThreeZ_mem_ker

@[simp]
theorem coe_soThreeRotation_apply (v : LinearMap.ker (soThreeForm R (soThreeZ R))) :
    (soThreeRotation R v : so (Fin 3) R) = ⁅soThreeZ R, (v : so (Fin 3) R)⁆ :=
  (rfl)

/-- **The root plane of `so(3)`.** For the dot product, the plane `ẑ^⊥` is a root plane of the
line `t = R ẑ`, with rotation `ad ẑ` and root `α(c ẑ) = c`, the restriction of `B ẑ` to `t`. -/
theorem isRootPlane_soThree :
    IsRootPlane (soThreeForm R) (R ∙ soThreeZ R) ((soThreeForm R (soThreeZ R)).domRestrict _)
      (LinearMap.ker (soThreeForm R (soThreeZ R))) (soThreeRotation R) where
  apply_apply v := by
    obtain ⟨x, hx⟩ := v
    obtain ⟨u, rfl⟩ := (soThreeEquiv R).surjective x
    have hu : u 2 = 0 := by simpa [dotProduct, Fin.sum_univ_three] using hx
    refine Subtype.ext ?_
    simp only [coe_soThreeRotation_apply, lie_soThreeEquiv, Submodule.coe_neg, ← map_neg]
    congr 1
    ext i
    fin_cases i <;> simp [cross_apply, hu]
  apply_left v w := by
    obtain ⟨x, -⟩ := v
    obtain ⟨y, -⟩ := w
    obtain ⟨u, rfl⟩ := (soThreeEquiv R).surjective x
    obtain ⟨w, rfl⟩ := (soThreeEquiv R).surjective y
    simp only [coe_soThreeRotation_apply, lie_soThreeEquiv, soThreeForm_apply_soThreeEquiv,
      cross_apply, dotProduct, Fin.sum_univ_three]
    simp
  lie_apply H v := by
    obtain ⟨H, hH⟩ := H
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hH
    simp [dotProduct, Fin.sum_univ_three]

/-- **The height Hessian of the coadjoint sphere of `so(3)`.** For `p = r ẑ`, `X = a ẑ` and
`u, w ⊥ e₃`, `B(q_p û, q_X ŵ) = r a (u ⬝ᵥ w)`. So the Hessian at `p` of the height `B(·, X)` on the
orbit of `p` is `-r a B` in the coordinates `û, ŵ` of `ẑ^⊥`, and `-a B / r` in the tangent vectors
`q_p û, q_p ŵ` (`TauCeti.IsRootPlane.mul_apply_lie_lie`). -/
theorem soThreeForm_lie_lie_smul_soThreeZ (r a : R) {u w : Fin 3 → R} (hu : u 2 = 0)
    (hw : w 2 = 0) :
    soThreeForm R ⁅soThreeEquiv R u, r • soThreeZ R⁆ ⁅soThreeEquiv R w, a • soThreeZ R⁆ =
      r * a * (u ⬝ᵥ w) := by
  have hmem (c : R) : c • soThreeZ R ∈ R ∙ soThreeZ R := Submodule.smul_mem _ c
    (Submodule.mem_span_singleton_self _)
  have hker {v : Fin 3 → R} (hv : v 2 = 0) :
      soThreeEquiv R v ∈ LinearMap.ker (soThreeForm R (soThreeZ R)) := by
    simp [dotProduct, Fin.sum_univ_three, hv]
  have h := isRootPlane_soThree.apply_lie_lie ⟨r • soThreeZ R, hmem r⟩ ⟨a • soThreeZ R, hmem a⟩
    ⟨soThreeEquiv R u, hker hu⟩ ⟨soThreeEquiv R w, hker hw⟩
  simpa [dotProduct, Fin.sum_univ_three] using h

end SoThree

end TauCeti
