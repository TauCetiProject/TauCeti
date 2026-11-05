/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Killing.BaseChange
public import TauCeti.Algebra.Lie.NormTwoShell.Basic

/-!
# The Killing form of the signed shell Lie algebra

Let `B : Matrix I I ℤ` be positive definite with even diagonal, with pairing
`⟪a, b⟫ = a ⬝ᵥ B *ᵥ b` on `Q = I → ℤ`, and let `Φ = B.normTwoShell` be its finite set of vectors of
norm two. The signed shell Lie algebra `Matrix.ShellLieAlgebra B` is free of finite rank over `ℤ`,
with integral basis the Cartan vectors `H_(αᵢ)` and the root vectors `x_a`, `a ∈ Φ`, so its Killing
form `κ(x, y) = tr (ad x ∘ ad y)` is the trace form of a finite free module. Finiteness of `Φ`,
automatic for positive definite `B` (`Matrix.PosDef.finite_normTwoShell`), is taken as an instance
argument only by the Cartan formula, whose statement sums over `Φ`; the other results derive it from
positive definiteness. This file computes `κ` on that basis:

* `κ(H_h, H_k) = ∑_(a ∈ Φ) ⟪h, a⟫ ⟪k, a⟫`, since `ad H_h ∘ ad H_k` kills the Cartan vectors and
  scales `x_a` by `⟪h, a⟫ ⟪k, a⟫`;
* `κ(H_h, x_a) = 0`;
* `κ(x_a, x_b) = 0` unless `a + b = 0`;
* `2 κ(x_a, x_(-a)) = ε(a, -a) κ(H_a, H_a)`, where `ε` is the ordered sign of the bracket
  `⁅x_a, x_(-a)⁆ = ε(a, -a) H_a`.

All but the first follow from the invariance `κ(⁅x, y⁆, z) = κ(x, ⁅y, z⁆)` and the weights of the
basis vectors, with no division by `2`: for instance `2 κ(H_h, x_a) = κ(H_h, ⁅H_a, x_a⁆)`
`= κ(⁅H_h, H_a⁆, x_a) = 0`, and `ℤ` is torsion free. Since `⟪a, a⟫ = 2`, the Cartan value
`κ(H_a, H_a)` is at least `4`, so each opposite pairing `κ(x_a, x_(-a))` is nonzero.

When `Φ` spans `Q`, for instance when the diagonal entries of `B` are `2` and `B` is the Cartan
matrix of a simply laced Dynkin diagram, the restriction of `κ` to the Cartan vectors is positive
definite: `κ(H_h, H_h) = ∑_(a ∈ Φ) ⟪h, a⟫²` vanishes only if `⟪h, -⟫` vanishes on `Φ`, hence on
`Q`, hence `⟪h, h⟫ = 0`. Together with the nonzero opposite pairings this shows that `κ` is
nondegenerate over `ℤ`: `Matrix.ShellLieAlgebra B` is a Killing Lie algebra over `ℤ`
(`Matrix.ShellLieAlgebra.isKilling`). Nondegeneracy over `ℤ` does not make `κ` unimodular: for
`A₁` the Gram matrix of `κ` on the basis `H, x_α, x_(-α)` has determinant `-128`. It does pass to
every scalar extension to an integral domain of characteristic zero, in particular to `ℚ`
(`Matrix.ShellLieAlgebra.isKilling_baseChange`), since the Killing form of the scalar extension is
the scalar extension of `κ`; over a field this makes the scalar extension semisimple
(`LieAlgebra.IsKilling.instSemisimple`).

## Main results

* `Matrix.ShellLieAlgebra.killingForm_cartan_cartan`: `κ(H_h, H_k) = ∑_(a ∈ Φ) ⟪h, a⟫ ⟪k, a⟫`.
* `Matrix.ShellLieAlgebra.killingForm_cartan_root_eq_zero`: `κ(H_h, x_a) = 0`.
* `Matrix.ShellLieAlgebra.killingForm_root_root_eq_zero_of_add_ne_zero`: `κ(x_a, x_b) = 0` for
  `a + b ≠ 0`.
* `Matrix.ShellLieAlgebra.two_mul_killingForm_root_root_of_add_eq_zero`: the opposite pairing
  `2 κ(x_a, x_b) = ε(a, b) κ(H_a, H_a)` for `a + b = 0`.
* `Matrix.ShellLieAlgebra.killingForm_root_root_ne_zero_of_add_eq_zero`: the opposite pairings are
  nonzero.
* `Matrix.ShellLieAlgebra.killingForm_cartan_self_pos`: positive definiteness on the Cartan
  vectors when the shell spans.
* `Matrix.ShellLieAlgebra.isKilling`: the Killing form is nondegenerate when the shell spans.
* `Matrix.ShellLieAlgebra.isKilling_baseChange`: so is that of its scalar extension to an integral
  domain of characteristic zero.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §2.2 and §7.8.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §8.2.
-/

public section

namespace Matrix.ShellLieAlgebra

open LieAlgebra Module TensorProduct

variable {I : Type*} [Fintype I] [LinearOrder I] {B : Matrix I I ℤ}

/-- **The Killing form on Cartan vectors** of the signed shell Lie algebra of a positive definite
`B` with even diagonal: `κ(H_h, H_k) = ∑_(a ∈ Φ) ⟪h, a⟫ ⟪k, a⟫`. -/
theorem killingForm_cartan_cartan [Fintype B.normTwoShell] (hB : B.PosDef)
    (hev : ∀ i, Even (B i i)) (h k : I → ℤ) :
    letI := lieRing hB hev
    killingForm ℤ (ShellLieAlgebra B) (cartan B h) (cartan B k) =
      ∑ a : B.normTwoShell, (h ⬝ᵥ B *ᵥ (a : I → ℤ)) * (k ⬝ᵥ B *ᵥ (a : I → ℤ)) := by
  let _ := lieRing hB hev
  classical
  rw [killingForm_apply_apply, LinearMap.trace_eq_matrix_trace ℤ (basis B), Matrix.trace,
    Fintype.sum_sum_type]
  simp [LinearMap.toMatrix_apply, mul_comm]

/-- **Cartan vectors are Killing orthogonal to root vectors**: `κ(H_h, x_a) = 0`. -/
@[simp]
theorem killingForm_cartan_root_eq_zero (hB : B.PosDef)
    (hev : ∀ i, Even (B i i)) (h : I → ℤ) (a : B.normTwoShell) :
    letI := lieRing hB hev
    killingForm ℤ (ShellLieAlgebra B) (cartan B h) (root B a) = 0 := by
  let _ := lieRing hB hev
  -- Invariance: `κ(⁅H_h, H_a⁆, x_a) = κ(H_h, ⁅H_a, x_a⁆) = 2 κ(H_h, x_a)`, as `⟪a, a⟫ = 2`.
  have key : killingForm ℤ (ShellLieAlgebra B) ⁅cartan B h, cartan B a⁆ (root B a) =
      killingForm ℤ (ShellLieAlgebra B) (cartan B h) ⁅cartan B a, root B a⁆ :=
    LieModule.traceForm_apply_lie_apply ℤ _ _ _ _ _
  rw [cartan_lie_cartan, cartan_lie_root, mem_normTwoShell.mp a.2] at key
  simp only [map_zero, LinearMap.zero_apply, map_smul, smul_eq_mul] at key
  omega

/-- **Root vectors are Killing orthogonal to Cartan vectors**: `κ(x_a, H_h) = 0`. -/
@[simp]
theorem killingForm_root_cartan_eq_zero (hB : B.PosDef)
    (hev : ∀ i, Even (B i i)) (a : B.normTwoShell) (h : I → ℤ) :
    letI := lieRing hB hev
    killingForm ℤ (ShellLieAlgebra B) (root B a) (cartan B h) = 0 := by
  let _ := lieRing hB hev
  rw [LieModule.traceForm_comm, killingForm_cartan_root_eq_zero]

/-- **Root vectors of non-opposite roots are Killing orthogonal**: `κ(x_a, x_b) = 0` for
`a + b ≠ 0`. -/
@[simp]
theorem killingForm_root_root_eq_zero_of_add_ne_zero (hB : B.PosDef)
    (hev : ∀ i, Even (B i i)) {a b : B.normTwoShell} (hab : (a : I → ℤ) + b ≠ 0) :
    letI := lieRing hB hev
    killingForm ℤ (ShellLieAlgebra B) (root B a) (root B b) = 0 := by
  let _ := lieRing hB hev
  -- With `c = a + b`, invariance gives `⟪c, a + b⟫ κ(x_a, x_b) = 0`, and `⟪c, c⟫ > 0`.
  set c : I → ℤ := (a : I → ℤ) + b
  have hc : 0 < c ⬝ᵥ B *ᵥ c := by simpa using hB.dotProduct_mulVec_pos hab
  -- Invariance: `⟪c, a⟫ κ(x_a, x_b) = κ(⁅H_c, x_a⁆, x_b) = -κ(x_a, ⁅H_c, x_b⁆)`
  -- `= -⟪c, b⟫ κ(x_a, x_b)`.
  have key : killingForm ℤ (ShellLieAlgebra B) ⁅cartan B c, root B a⁆ (root B b) =
      -killingForm ℤ (ShellLieAlgebra B) (root B a) ⁅cartan B c, root B b⁆ :=
    LieModule.traceForm_apply_lie_apply' ℤ _ _ _ _ _
  rw [cartan_lie_root, cartan_lie_root] at key
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at key
  have hcab : c ⬝ᵥ B *ᵥ c = c ⬝ᵥ B *ᵥ (a : I → ℤ) + c ⬝ᵥ B *ᵥ (b : I → ℤ) := by
    rw [← dotProduct_add, ← mulVec_add]
  refine (mul_eq_zero.mp (?_ : c ⬝ᵥ B *ᵥ c * _ = 0)).resolve_left hc.ne'
  rw [hcab]
  linear_combination key

/-- **The opposite Killing pairing**: for `a + b = 0`, `2 κ(x_a, x_b) = ε(a, b) κ(H_a, H_a)`,
where `⁅x_a, x_b⁆ = ε(a, b) H_a`. -/
theorem two_mul_killingForm_root_root_of_add_eq_zero (hB : B.PosDef)
    (hev : ∀ i, Even (B i i)) {a b : B.normTwoShell} (hab : (a : I → ℤ) + b = 0) :
    letI := lieRing hB hev
    2 * killingForm ℤ (ShellLieAlgebra B) (root B a) (root B b) =
      (B.orderedSignForm a b).negOnePow *
        killingForm ℤ (ShellLieAlgebra B) (cartan B a) (cartan B a) := by
  let _ := lieRing hB hev
  have hp : (a : I → ℤ) ⬝ᵥ B *ᵥ (b : I → ℤ) = -2 := by
    rw [eq_neg_of_add_eq_zero_right hab, mulVec_neg, dotProduct_neg, mem_normTwoShell.mp a.2]
  have key : killingForm ℤ (ShellLieAlgebra B) ⁅root B a, root B b⁆ (cartan B a) =
      killingForm ℤ (ShellLieAlgebra B) (root B a) ⁅root B b, cartan B a⁆ :=
    LieModule.traceForm_apply_lie_apply ℤ _ _ _ _ _
  rw [root_lie_root, rootBracket_of_add_eq_zero hab, root_lie_cartan, hp] at key
  simp only [Units.smul_def, neg_smul, neg_neg, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at key
  exact key.symm

/-- The Killing form of a Cartan vector of a norm-two vector with itself is at least `4`: the
term `⟪a, a⟫² = 4` occurs in `κ(H_a, H_a) = ∑_(b ∈ Φ) ⟪a, b⟫²`. -/
private theorem four_le_killingForm_cartan_root_self (hB : B.PosDef)
    (hev : ∀ i, Even (B i i)) (a : B.normTwoShell) :
    letI := lieRing hB hev
    4 ≤ killingForm ℤ (ShellLieAlgebra B) (cartan B a) (cartan B a) := by
  let _ := lieRing hB hev
  have : Finite B.normTwoShell := hB.finite_normTwoShell.to_subtype
  have := Fintype.ofFinite B.normTwoShell
  rw [killingForm_cartan_cartan hB hev,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a), mem_normTwoShell.mp a.2]
  have := Finset.sum_nonneg fun (b : B.normTwoShell) (_ : b ∈ Finset.univ.erase a) ↦
    mul_self_nonneg ((a : I → ℤ) ⬝ᵥ B *ᵥ (b : I → ℤ))
  omega

/-- **The opposite Killing pairings are nonzero**: `κ(x_a, x_b) ≠ 0` for `a + b = 0`. -/
theorem killingForm_root_root_ne_zero_of_add_eq_zero (hB : B.PosDef)
    (hev : ∀ i, Even (B i i)) {a b : B.normTwoShell} (hab : (a : I → ℤ) + b = 0) :
    letI := lieRing hB hev
    killingForm ℤ (ShellLieAlgebra B) (root B a) (root B b) ≠ 0 := by
  let _ := lieRing hB hev
  intro h0
  have key := two_mul_killingForm_root_root_of_add_eq_zero hB hev hab
  have h4 := four_le_killingForm_cartan_root_self hB hev a
  rw [h0, mul_zero, eq_comm, mul_eq_zero] at key
  exact key.elim (Units.ne_zero _) (by omega)

/-- **The Killing form is positive definite on the Cartan vectors** when the norm-two shell spans
the lattice: `κ(H_h, H_h) > 0` for `h ≠ 0`. -/
theorem killingForm_cartan_self_pos (hB : B.PosDef)
    (hev : ∀ i, Even (B i i)) (hspan : Submodule.span ℤ B.normTwoShell = ⊤) {h : I → ℤ}
    (hh : h ≠ 0) :
    letI := lieRing hB hev
    0 < killingForm ℤ (ShellLieAlgebra B) (cartan B h) (cartan B h) := by
  let _ := lieRing hB hev
  have : Finite B.normTwoShell := hB.finite_normTwoShell.to_subtype
  have := Fintype.ofFinite B.normTwoShell
  rw [killingForm_cartan_cartan hB hev]
  refine lt_of_le_of_ne (Finset.sum_nonneg fun a _ ↦ mul_self_nonneg _) fun h0 ↦ hh ?_
  have hz : ∀ a : B.normTwoShell, h ⬝ᵥ B *ᵥ (a : I → ℤ) = 0 := fun a ↦
    mul_self_eq_zero.mp <| (Finset.sum_eq_zero_iff_of_nonneg fun b _ ↦ mul_self_nonneg _).mp
      h0.symm a (Finset.mem_univ a)
  -- The functional `⟪h, -⟫` vanishes on the spanning set `Φ`, so in particular `⟪h, h⟫ = 0`.
  have hker : Submodule.span ℤ B.normTwoShell ≤ LinearMap.ker (toBilin' B h) :=
    Submodule.span_le.mpr fun a ha ↦ by simpa [toBilin'_apply'] using hz ⟨a, ha⟩
  have hhh : h ⬝ᵥ B *ᵥ h = 0 := by
    simpa [toBilin'_apply'] using hker (hspan ▸ Submodule.mem_top : h ∈ _)
  by_contra hne
  exact (hB.dotProduct_mulVec_pos hne).ne' (by simpa using hhh)

/-- **The signed shell Lie algebra is a Killing Lie algebra over `ℤ`** when its norm-two shell
spans the lattice, for instance for the Cartan matrix of a simply laced Dynkin diagram: its Killing
form is nondegenerate. -/
theorem isKilling (hB : B.PosDef) (hev : ∀ i, Even (B i i))
    (hspan : Submodule.span ℤ B.normTwoShell = ⊤) :
    letI := lieRing hB hev
    IsKilling ℤ (ShellLieAlgebra B) := by
  let _ := lieRing hB hev
  have : Finite B.normTwoShell := hB.finite_normTwoShell.to_subtype
  have := Fintype.ofFinite B.normTwoShell
  refine ⟨(LieSubmodule.eq_bot_iff _).mpr fun x hx ↦ ?_⟩
  have hx' (y : ShellLieAlgebra B) : killingForm ℤ (ShellLieAlgebra B) x y = 0 := by
    rw [LieModule.traceForm_comm]
    exact (LieIdeal.mem_killingCompl ℤ (ShellLieAlgebra B) ⊤).mp hx y (LieSubmodule.mem_top y)
  -- A vector Killing orthogonal to everything has zero coefficient on each root vector `x_a`, by
  -- pairing with `x_(-a)`, and its Cartan part `H_h` then satisfies `κ(H_h, H_h) = 0`.
  have hsum := (cartan_add_sum_root_eq B x).symm
  set h := (equivProd B x).1
  have hroot (a : B.normTwoShell) : (equivProd B x).2 a = 0 := by
    let a' : B.normTwoShell := ⟨-a, neg_mem_normTwoShell.mpr a.2⟩
    have hne := killingForm_root_root_ne_zero_of_add_eq_zero hB hev (b := a')
      (add_neg_cancel (a : I → ℤ))
    have key := hx' (root B a')
    rw [hsum, map_add, LinearMap.add_apply, killingForm_cartan_root_eq_zero hB hev, zero_add,
      map_sum, LinearMap.sum_apply, Finset.sum_eq_single a] at key
    · rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at key
      exact (mul_eq_zero.mp key).resolve_right hne
    · intro b _ hb
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul,
        killingForm_root_root_eq_zero_of_add_ne_zero hB hev, mul_zero]
      exact fun hba ↦ hb (Subtype.ext (add_neg_eq_zero.mp hba))
    · simp
  have hcart : x = cartan B h := by
    conv_lhs => rw [hsum, Finset.sum_eq_zero fun a _ ↦ by rw [hroot a, zero_smul], add_zero]
  by_contra hx0
  have hh : h ≠ 0 := fun h0 ↦ hx0 (by rw [hcart, h0, map_zero])
  have := killingForm_cartan_self_pos hB hev hspan hh
  rw [← hcart, hx'] at this
  exact this.false

/-- **The signed shell Lie algebra is Killing over any integral domain of characteristic zero**,
in particular over `ℚ`, when its norm-two shell spans the lattice: the Killing form of the scalar
extension is the scalar extension of the integral Killing form, which is nondegenerate by
`Matrix.ShellLieAlgebra.isKilling`. -/
theorem isKilling_baseChange (A : Type*) [CommRing A] [IsDomain A] [CharZero A]
    (hB : B.PosDef) (hev : ∀ i, Even (B i i))
    (hspan : Submodule.span ℤ B.normTwoShell = ⊤) :
    letI := lieRing hB hev
    IsKilling A (A ⊗[ℤ] ShellLieAlgebra B) := by
  let _ := lieRing hB hev
  have : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective ℤ A).mpr Int.cast_injective
  have : Finite B.normTwoShell := hB.finite_normTwoShell.to_subtype
  have := isKilling hB hev hspan
  exact (TauCeti.isKilling_baseChange_iff ℤ A _).mpr this

end Matrix.ShellLieAlgebra
