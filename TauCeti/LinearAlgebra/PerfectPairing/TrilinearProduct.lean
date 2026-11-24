/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PerfectPairing.Basis

/-!
# The product of a trilinear form through a perfect pairing

Let `p : M × N → R` be a perfect pairing over a commutative semiring `R`, and let
`I : V × W × N → R` be a trilinear form. Since `p` identifies `M` with the dual of `N`, there is a
unique bilinear map `⋆ : V × W → M` with

`p (a ⋆ b) c = I a b c` for all `a`, `b`, `c`,

the product `LinearMap.trilinearProduct p I`. Conversely every bilinear map `V × W → M` is the
product of exactly one trilinear form, `(a, b, c) ↦ p (a ⋆ b) c`; so `trilinearProduct p` is a
linear equivalence between trilinear forms and bilinear maps into `M`.

This is how the small quantum product is read off from three-point Gromov–Witten invariants: for
the Poincaré pairing `p(x, y) = ∫ x ⌣ y` on the cohomology of a closed symplectic manifold,
extended to Novikov coefficients, and the three-point correlator
`I(a, b, c) = ∑_A q^A ⟨a, b, c⟩_(0,3,A)`, the quantum product is `trilinearProduct p I`. The same
construction recovers the multiplication of a Frobenius algebra from its trilinear form
`(a, b, c) ↦ φ (a b c)`. No basis enters the definition, so the product does not depend on one.
This file develops the algebra that relates properties of `I` to properties of `⋆`.

* **The left-dual reconstruction.** For a finite basis `e` of `N`, the *left dual basis*
  `e^j = LinearMap.leftDualBasis p e j` of `M` is characterised by `p (e^i) (e_j) = δ_ij`. Every
  `x ∈ M` is `x = ∑_j p(x, e_j) e^j` (`LinearMap.sum_apply_smul_leftDualBasis`), and hence
  `a ⋆ b = ∑_j I(a, b, e_j) e^j` (`LinearMap.trilinearProduct_apply_eq_sum`). The dual basis sits
  in the left slot of `p`. When `p` is not symmetric, as for the Poincaré pairing on odd classes,
  the right dual basis, with `p (e_j) (e^i) = δ_ij`, is a different basis, and the reconstruction
  formula holds for the left one. For the intersection pairing on the first cohomology of the
  two-torus, with `p(α, β) = 1`, the left duals of `(α, β)` are `(-β, α)`, as the example at the
  end of this file checks. Mathlib's `LinearMap.BilinForm.dualBasis` is the
  case of a nondegenerate bilinear form on a finite-dimensional vector space; here the scalars
  form any commutative semiring, such as a Novikov ring, which need not be a field.
* **Commutativity.** If exchanging the first two arguments of `I` multiplies it by `ε`, then
  `a ⋆ b = ε (b ⋆ a)` (`LinearMap.trilinearProduct_apply_eq_smul`). For homogeneous classes of
  degrees `|a|` and `|b|` and the graded symmetry of the correlator, `ε = (-1)^(|a| |b|)`.
* **Units.** If `I(a, u, c) = p(a, c)` for all `a` and `c` then `u` is a right unit, and if
  `I(u, b, c) = p(b, c)` for all `b` and `c` then `u` is a left unit
  (`LinearMap.trilinearProduct_apply_eq_self_right`,
  `LinearMap.trilinearProduct_apply_eq_self_left`).
* **Associativity.** The product on `M` defined by `I : M × M × N → R` is associative exactly
  when `I((a ⋆ b), c, d) = I(a, (b ⋆ c), d)` for all `a`, `b`, `c`, `d`
  (`LinearMap.trilinearProduct_assoc_iff`). In a finite basis `e` of `N` with left dual basis `e^j`
  this
  is the identity

  `∑_j I(a, b, e_j) I(e^j, c, d) = ∑_j I(b, c, e_j) I(a, e^j, d)`

  (`LinearMap.trilinearProduct_assoc_iff_sum`). For the Gromov–Witten correlator this is the WDVV
  equation, the form in which associativity of the quantum product is derived from the splitting
  axiom on the moduli space of four-pointed stable genus-zero curves.

## References

* M. Kontsevich and Yu. Manin, *Gromov–Witten classes, quantum cohomology, and enumerative
  geometry*, Comm. Math. Phys. **164** (1994), 525–562, Theorem-Definition 4.5.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 11.1,
  on the quantum product defined through the Poincaré pairing and the proof of its associativity.
-/

public section

noncomputable section

namespace LinearMap

open Module

variable {R M N V W : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

section Pairing

variable (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair]

/-- **The product of a trilinear form through a perfect pairing.** For a perfect pairing
`p : M × N → R` and a trilinear form `I : V × W × N → R`, the bilinear map `⋆ : V × W → M`
characterised by `p (a ⋆ b) c = I a b c` (`LinearMap.apply_trilinearProduct`). It is a linear
equivalence: every bilinear map `V × W → M` is the product of the trilinear form
`(a, b, c) ↦ p (a ⋆ b) c` (`LinearMap.trilinearProduct_symm_apply`). -/
def trilinearProduct : (V →ₗ[R] W →ₗ[R] N →ₗ[R] R) ≃ₗ[R] (V →ₗ[R] W →ₗ[R] M) :=
  LinearEquiv.congrRight (LinearEquiv.congrRight p.toPerfPair.symm)

/-- The defining property of the product of a trilinear form: `p (a ⋆ b) c = I a b c`. -/
@[simp]
theorem apply_trilinearProduct (I : V →ₗ[R] W →ₗ[R] N →ₗ[R] R) (a : V) (b : W) (c : N) :
    p (p.trilinearProduct I a b) c = I a b c := by
  simp [trilinearProduct]

/-- The trilinear form of a bilinear map `⋆ : V × W → M` is `(a, b, c) ↦ p (a ⋆ b) c`. -/
@[simp]
theorem trilinearProduct_symm_apply (m : V →ₗ[R] W →ₗ[R] M) (a : V) (b : W) (c : N) :
    p.trilinearProduct.symm m a b c = p (m a b) c := by
  conv_rhs => rw [← p.trilinearProduct.apply_symm_apply m]
  rw [apply_trilinearProduct]

/-- An element of `M` is the product `a ⋆ b` exactly when it pairs with every `c` to `I a b c`. -/
theorem eq_trilinearProduct_apply_iff {I : V →ₗ[R] W →ₗ[R] N →ₗ[R] R} {a : V} {b : W} {x : M} :
    x = p.trilinearProduct I a b ↔ ∀ c, p x c = I a b c := by
  refine ⟨fun h c ↦ h ▸ p.apply_trilinearProduct I a b c, fun h ↦ ?_⟩
  refine (IsPerfPair.bijective_left p).injective (LinearMap.ext fun c ↦ ?_)
  rw [h, apply_trilinearProduct]

/-- **Commutativity of the product.** If exchanging the first two arguments of `I` at `a` and `b`
multiplies it by `ε`, then `a ⋆ b = ε • (b ⋆ a)`. For the graded symmetry of a correlator on
homogeneous classes `ε` is the Koszul sign `(-1)^(|a| |b|)`. -/
theorem trilinearProduct_apply_eq_smul {I : V →ₗ[R] V →ₗ[R] N →ₗ[R] R} {a b : V} {ε : R}
    (h : ∀ c, I a b c = ε * I b a c) :
    p.trilinearProduct I a b = ε • p.trilinearProduct I b a := by
  rw [eq_comm, eq_trilinearProduct_apply_iff]
  intro c
  rw [map_smul₂, apply_trilinearProduct, smul_eq_mul, h]

/-- **Right units.** If `I(a, u, c) = p(a, c)` for all `a` and `c`, then `a ⋆ u = a`. -/
theorem trilinearProduct_apply_eq_self_right (I : M →ₗ[R] W →ₗ[R] N →ₗ[R] R) {u : W}
    (h : ∀ a c, I a u c = p a c) (a : M) :
    p.trilinearProduct I a u = a := by
  rw [eq_comm, eq_trilinearProduct_apply_iff]
  exact fun c ↦ (h a c).symm

/-- **Left units.** If `I(u, b, c) = p(b, c)` for all `b` and `c`, then `u ⋆ b = b`. -/
theorem trilinearProduct_apply_eq_self_left (I : V →ₗ[R] M →ₗ[R] N →ₗ[R] R) {u : V}
    (h : ∀ b c, I u b c = p b c) (b : M) :
    p.trilinearProduct I u b = b := by
  rw [eq_comm, eq_trilinearProduct_apply_iff]
  exact fun c ↦ (h b c).symm

/-- **Associativity of the product.** The product of `I` is associative exactly when
`I(a ⋆ b, c, d) = I(a, b ⋆ c, d)` for all `a`, `b`, `c` and `d`. -/
theorem trilinearProduct_assoc_iff (I : M →ₗ[R] M →ₗ[R] N →ₗ[R] R) :
    (∀ a b c, p.trilinearProduct I (p.trilinearProduct I a b) c =
        p.trilinearProduct I a (p.trilinearProduct I b c)) ↔
      ∀ a b c d, I (p.trilinearProduct I a b) c d = I a (p.trilinearProduct I b c) d := by
  refine ⟨fun h a b c d ↦ ?_, fun h a b c ↦ ?_⟩
  · rw [← apply_trilinearProduct p I, h, apply_trilinearProduct]
  · rw [eq_trilinearProduct_apply_iff]
    intro d
    rw [apply_trilinearProduct, h]

section DualBasis

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- **The product in a basis.** The product of a trilinear form is
`a ⋆ b = ∑_j I(a, b, e_j) e^j`, for the left dual basis `e^j` of a finite basis `e` of `N`. -/
theorem trilinearProduct_apply_eq_sum (e : Basis ι R N)
    (I : V →ₗ[R] W →ₗ[R] N →ₗ[R] R) (a : V) (b : W) :
    p.trilinearProduct I a b = ∑ j, I a b (e j) • p.leftDualBasis e j := by
  simp_rw [← apply_trilinearProduct p I a b]
  exact (p.sum_apply_smul_leftDualBasis e _).symm

/-- **Associativity in a basis: the WDVV identity.** For a finite basis `e` of `N` with left dual
basis `e^j`, the product of `I` is associative exactly when

`∑_j I(a, b, e_j) I(e^j, c, d) = ∑_j I(b, c, e_j) I(a, e^j, d)`

for all `a`, `b`, `c` and `d`. -/
theorem trilinearProduct_assoc_iff_sum (e : Basis ι R N) (I : M →ₗ[R] M →ₗ[R] N →ₗ[R] R) :
    (∀ a b c, p.trilinearProduct I (p.trilinearProduct I a b) c =
        p.trilinearProduct I a (p.trilinearProduct I b c)) ↔
      ∀ a b c d, ∑ j, I a b (e j) * I (p.leftDualBasis e j) c d =
        ∑ j, I b c (e j) * I a (p.leftDualBasis e j) d := by
  rw [trilinearProduct_assoc_iff]
  simp only [p.trilinearProduct_apply_eq_sum e, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]

end DualBasis

end Pairing

/-! The left duals of the torus basis: if a basis `(α, β)` of `M` satisfies `p α α = p β β = 0`,
`p α β = 1` and `p β α = -1`, as the intersection pairing does on the first cohomology of the
two-torus, then its left dual basis is `(-β, α)`. The right dual basis, with
`p (e_j) (e^i) = δ_ij`, would be `(β, -α)` instead. -/
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (p : M →ₗ[R] M →ₗ[R] R)
    [p.IsPerfPair] (e : Basis (Fin 2) R M) (h₀₀ : p (e 0) (e 0) = 0) (h₁₁ : p (e 1) (e 1) = 0)
    (h₀₁ : p (e 0) (e 1) = 1) (h₁₀ : p (e 1) (e 0) = -1) :
    ⇑(p.leftDualBasis e) = ![-e 1, e 0] := by
  refine ((p.eq_leftDualBasis_iff e).2 ?_).symm
  simp [Fin.forall_fin_two, h₀₀, h₁₁, h₀₁, h₁₀]

end LinearMap
