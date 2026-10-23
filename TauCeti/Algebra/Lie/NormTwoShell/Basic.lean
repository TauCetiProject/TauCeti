/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.StdBasis
public import TauCeti.LinearAlgebra.Matrix.NormTwoShell
public import TauCeti.LinearAlgebra.Matrix.OrderedSignCover
import Mathlib.Tactic.Module
import TauCeti.LinearAlgebra.Matrix.Symmetric

/-!
# The signed Lie algebra of the norm-two shell of an even lattice

Let `B : Matrix I I ℤ` be the Gram matrix of the lattice `Q = I → ℤ`, with pairing
`⟪a, b⟫ = a ⬝ᵥ B *ᵥ b`, and let `Φ = B.normTwoShell` be its vectors of norm two. When `B` is the
Cartan matrix of a simply laced Dynkin diagram, possibly disconnected, `Φ` is its root system and
the construction below is the Frenkel--Kac construction of the corresponding simply laced Lie
algebra over `ℤ`; no comparison with other constructions of that Lie algebra is made here. Its
carrier `ShellLieAlgebra B` is `Q × (Φ →₀ ℤ)`: a Cartan vector `H_h` for each
`h : Q` (`ShellLieAlgebra.cartan`) and a root vector `x_a` for each `a ∈ Φ`
(`ShellLieAlgebra.root`), which together give an integral basis (`ShellLieAlgebra.basis`). The
bracket (`ShellLieAlgebra.bracketBilin`) is the bilinear map with
`⁅H_h, H_k⁆ = 0`, `⁅H_h, x_a⁆ = ⟪h, a⟫ x_a`, and on root vectors
(`ShellLieAlgebra.rootBracket`)

* `⁅x_a, x_b⁆ = ε(a, b) x_(a + b)` if `a + b ∈ Φ`,
* `⁅x_a, x_b⁆ = ε(a, b) H_a` if `a + b = 0`,
* `⁅x_a, x_b⁆ = 0` otherwise,

where `ε(a, b) = (-1) ^ (B.orderedSignForm a b)` is the ordered sign of `Matrix.SignCover B`.

The sign `ε` uses only the strictly lower triangular part of `B`, so `ε(a, a)` is not normalized
to `(-1) ^ (⟪a, a⟫ / 2)`. Correspondingly the opposite bracket `⁅x_a, x_(-a)⁆` is `ε(a, -a) H_a`,
not `-H_a`: the vector `x_(-a)` indexed by `-a ∈ Φ` is a section vector, not the vector of the
inverse lift of `a` to the cover.

The bracket is antisymmetric and alternating as soon as `B` is symmetric with even diagonal
(`ShellLieAlgebra.lie_skew`, `ShellLieAlgebra.lie_self`): interchanging `a` and `b` changes
`ε` by `(-1) ^ ⟪a, b⟫`. For `B` positive definite with even diagonal it satisfies the Jacobi
identity over `ℤ` (`ShellLieAlgebra.lie_jacobi`), so it is a Lie ring
(`ShellLieAlgebra.lieRing`) and hence a Lie algebra over `ℤ`. Positive definiteness confines the
pairing of two roots that are neither equal nor opposite to `{-1, 0, 1}`, and the proof is a case
analysis on these pairings for three root vectors, in which no division by `2` occurs.

## Main definitions

* `Matrix.ShellLieAlgebra B`: the carrier `Q × (Φ →₀ ℤ)`.
* `Matrix.ShellLieAlgebra.basis`: its integral basis indexed by `I ⊕ Φ`.
* `Matrix.ShellLieAlgebra.rootBracket`: the bracket of two root vectors.
* `Matrix.ShellLieAlgebra.bracketBilin`: the bracket, as a bilinear map.
* `Matrix.ShellLieAlgebra.lieRing`: the Lie ring structure, for positive definite `B` with even
  diagonal.

## Main results

* `Matrix.ShellLieAlgebra.cartan_lie_root`, `Matrix.ShellLieAlgebra.root_lie_root`: the
  bracket on Cartan and root vectors.
* `Matrix.ShellLieAlgebra.cartan_lie_rootBracket`: `⁅x_a, x_b⁆` has weight `a + b`.
* `Matrix.ShellLieAlgebra.rootBracket_eq_zero_of_nonneg`: root vectors whose roots have nonnegative
  pairing commute, for symmetric `B`.
* `Matrix.ShellLieAlgebra.lie_skew`: antisymmetry, for symmetric `B` with even diagonal.
* `Matrix.ShellLieAlgebra.lie_jacobi`: the Jacobi identity, for positive definite `B` with even
  diagonal.

## References

* I. B. Frenkel and V. G. Kac, *Basic representations of affine Lie algebras and dual resonance
  models*, Invent. Math. **62** (1980), 23--66.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.8.
-/

public section

namespace Matrix

open Module

variable {I : Type*} [Fintype I] (B : Matrix I I ℤ)

/-- The carrier `Q × (Φ →₀ ℤ)` of the signed Lie algebra of the norm-two shell `Φ` of an integer
Gram matrix `B` on `Q = I → ℤ`: a Cartan part `Q` and a free root part with basis indexed by
`Φ`. The bracket is `Matrix.ShellLieAlgebra.bracketBilin`. -/
def ShellLieAlgebra : Type _ :=
  (I → ℤ) × (B.normTwoShell →₀ ℤ)

namespace ShellLieAlgebra

noncomputable instance : AddCommGroup (ShellLieAlgebra B) :=
  inferInstanceAs (AddCommGroup ((I → ℤ) × (B.normTwoShell →₀ ℤ)))

/-- The identification of `ShellLieAlgebra B` with the product `Q × (Φ →₀ ℤ)` defining it. -/
noncomputable def equivProd : ShellLieAlgebra B ≃ₗ[ℤ] (I → ℤ) × (B.normTwoShell →₀ ℤ) :=
  LinearEquiv.refl ℤ _

/-- The Cartan vector `H_h` of a lattice vector `h`, as a linear map `Q →ₗ[ℤ] ShellLieAlgebra B`. -/
noncomputable def cartan : (I → ℤ) →ₗ[ℤ] ShellLieAlgebra B :=
  (equivProd B).symm.toLinearMap ∘ₗ LinearMap.inl ℤ (I → ℤ) (B.normTwoShell →₀ ℤ)

/-- The root vector `x_a` of a vector `a` of the norm-two shell. -/
noncomputable def root (a : B.normTwoShell) : ShellLieAlgebra B :=
  (equivProd B).symm (0, Finsupp.single a 1)

@[simp]
theorem equivProd_cartan (h : I → ℤ) : equivProd B (cartan B h) = (h, 0) := by
  simp [cartan]

@[simp]
theorem equivProd_root (a : B.normTwoShell) :
    equivProd B (root B a) = (0, Finsupp.single a 1) := by
  simp [root]

/-- The integral basis of `ShellLieAlgebra B`: the Cartan vectors `H_(αᵢ)` of the coordinate
vectors `αᵢ = Pi.single i 1`, followed by the root vectors `x_a`. -/
noncomputable def basis : Basis (I ⊕ B.normTwoShell) ℤ (ShellLieAlgebra B) :=
  ((Pi.basisFun ℤ I).prod Finsupp.basisSingleOne).map (equivProd B).symm

@[simp]
theorem basis_inl [DecidableEq I] (i : I) : basis B (.inl i) = cartan B (Pi.single i 1) := by
  simp [basis, cartan, Basis.prod_apply]

@[simp]
theorem basis_inr (a : B.normTwoShell) : basis B (.inr a) = root B a := by
  simp [basis, root, Basis.prod_apply]

variable [LinearOrder I]

/-- The bracket `⁅x_a, x_b⁆` of two root vectors: `ε(a, b) x_(a + b)` if `a + b` is in the norm-two
shell, `ε(a, b) H_a` if `a + b = 0`, and `0` otherwise, where `ε(a, b)` is the ordered sign
`(B.orderedSignForm a b).negOnePow`. -/
noncomputable def rootBracket (a b : B.normTwoShell) : ShellLieAlgebra B := by
  classical
  exact (B.orderedSignForm a b).negOnePow •
    if h : (a : I → ℤ) + b ∈ B.normTwoShell then root B ⟨_, h⟩
    else if (a : I → ℤ) + b = 0 then cartan B a else 0

variable {B} in
/-- The bracket of two root vectors whose sum is in the norm-two shell. -/
@[simp]
theorem rootBracket_of_mem {a b : B.normTwoShell} (h : (a : I → ℤ) + b ∈ B.normTwoShell) :
    rootBracket B a b = (B.orderedSignForm a b).negOnePow • root B ⟨_, h⟩ := by
  rw [rootBracket, dite_eq_left h]

variable {B} in
/-- The bracket of two opposite root vectors. -/
@[simp]
theorem rootBracket_of_add_eq_zero {a b : B.normTwoShell} (h : (a : I → ℤ) + b = 0) :
    rootBracket B a b = (B.orderedSignForm a b).negOnePow • cartan B a := by
  have hm : (a : I → ℤ) + b ∉ B.normTwoShell := h ▸ fun h0 ↦ ne_zero_of_mem_normTwoShell h0 rfl
  rw [rootBracket, dite_eq_right hm, ite_eq_left h]

variable {B} in
/-- Two root vectors whose sum is neither in the norm-two shell nor zero have bracket zero. -/
@[simp]
theorem rootBracket_of_notMem_of_add_ne_zero {a b : B.normTwoShell}
    (h : (a : I → ℤ) + b ∉ B.normTwoShell) (h' : (a : I → ℤ) + b ≠ 0) :
    rootBracket B a b = 0 := by
  rw [rootBracket, dite_eq_right h, ite_eq_right h', smul_zero]

variable {B} in
/-- For a symmetric `B`, two root vectors whose roots have nonnegative pairing have bracket zero:
the sum of the roots then has norm at least `4`. -/
theorem rootBracket_eq_zero_of_nonneg (hB : B.IsSymm) {a b : B.normTwoShell}
    (h : 0 ≤ (a : I → ℤ) ⬝ᵥ B *ᵥ b) : rootBracket B a b = 0 := by
  refine rootBracket_of_notMem_of_add_ne_zero (fun hm ↦ ?_) fun hz ↦ ?_
  · have := (hB.add_mem_normTwoShell_iff a.2 b.2).1 hm
    omega
  · rw [eq_neg_of_add_eq_zero_right hz, mulVec_neg, dotProduct_neg, mem_normTwoShell.mp a.2] at h
    omega

/-- The bracket on basis vectors. -/
private noncomputable def basisBracket :
    I ⊕ B.normTwoShell → I ⊕ B.normTwoShell → ShellLieAlgebra B
  | .inl _, .inl _ => 0
  | .inl i, .inr b => (Pi.single i 1 ⬝ᵥ B *ᵥ (b : I → ℤ)) • root B b
  | .inr a, .inl j => -((Pi.single j 1 ⬝ᵥ B *ᵥ (a : I → ℤ)) • root B a)
  | .inr a, .inr b => rootBracket B a b

/-- The bracket of `ShellLieAlgebra B`, as the bilinear map determined on the integral basis by
`⁅H_h, H_k⁆ = 0`, `⁅H_h, x_b⁆ = ⟪h, b⟫ x_b`, `⁅x_a, H_k⁆ = -⟪k, a⟫ x_a` and
`⁅x_a, x_b⁆ = rootBracket B a b`. -/
noncomputable def bracketBilin :
    ShellLieAlgebra B →ₗ[ℤ] ShellLieAlgebra B →ₗ[ℤ] ShellLieAlgebra B :=
  (basis B).constr ℤ fun i ↦ (basis B).constr ℤ (basisBracket B i)

/-- The bracket of `ShellLieAlgebra B` is `Matrix.ShellLieAlgebra.bracketBilin`. It is a Lie bracket
for positive definite `B` with even diagonal, see `Matrix.ShellLieAlgebra.lieRing`. -/
noncomputable instance : Bracket (ShellLieAlgebra B) (ShellLieAlgebra B) :=
  ⟨fun x y ↦ bracketBilin B x y⟩

@[simp]
theorem bracketBilin_apply_apply (x y : ShellLieAlgebra B) : bracketBilin B x y = ⁅x, y⁆ :=
  (rfl)

private theorem lie_basis_basis (i j : I ⊕ B.normTwoShell) :
    ⁅basis B i, basis B j⁆ = basisBracket B i j := by
  rw [← bracketBilin_apply_apply, bracketBilin, Basis.constr_basis, Basis.constr_basis]

variable {B}

@[simp]
protected theorem add_lie (x y z : ShellLieAlgebra B) : ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := by
  simp only [← bracketBilin_apply_apply, map_add, LinearMap.add_apply]

@[simp]
protected theorem lie_add (x y z : ShellLieAlgebra B) : ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ := by
  simp only [← bracketBilin_apply_apply, map_add]

@[simp]
protected theorem smul_lie (n : ℤ) (x y : ShellLieAlgebra B) : ⁅n • x, y⁆ = n • ⁅x, y⁆ := by
  simp only [← bracketBilin_apply_apply, map_smul, LinearMap.smul_apply]

@[simp]
protected theorem lie_smul (n : ℤ) (x y : ShellLieAlgebra B) : ⁅x, n • y⁆ = n • ⁅x, y⁆ := by
  simp only [← bracketBilin_apply_apply, map_smul]

/-- Cartan vectors commute. -/
@[simp]
theorem cartan_lie_cartan (h k : I → ℤ) : ⁅cartan B h, cartan B k⁆ = 0 := by
  have key : (bracketBilin B).compl₁₂ (cartan B) (cartan B) = 0 :=
    (Pi.basisFun ℤ I).ext fun i ↦ (Pi.basisFun ℤ I).ext fun j ↦ by
      simpa [← basis_inl, basisBracket] using lie_basis_basis B (.inl i) (.inl j)
  simpa using congr($key h k)

/-- The Cartan vector `H_h` acts on the root vector `x_b` by the pairing `⟪h, b⟫`. -/
@[simp]
theorem cartan_lie_root (h : I → ℤ) (b : B.normTwoShell) :
    ⁅cartan B h, root B b⁆ = (h ⬝ᵥ B *ᵥ (b : I → ℤ)) • root B b := by
  have key : (bracketBilin B).flip (root B b) ∘ₗ cartan B =
      ((toBilin' B).flip b).smulRight (root B b) :=
    (Pi.basisFun ℤ I).ext fun i ↦ by
      simpa [← basis_inl, ← basis_inr, toBilin'_apply', basisBracket] using
        lie_basis_basis B (.inl i) (.inr b)
  simpa [toBilin'_apply'] using congr($key h)

/-- The bracket `⁅x_a, H_k⁆ = -⟪k, a⟫ x_a`. -/
@[simp]
theorem root_lie_cartan (a : B.normTwoShell) (k : I → ℤ) :
    ⁅root B a, cartan B k⁆ = -((k ⬝ᵥ B *ᵥ (a : I → ℤ)) • root B a) := by
  have key : bracketBilin B (root B a) ∘ₗ cartan B =
      -((toBilin' B).flip a).smulRight (root B a) :=
    (Pi.basisFun ℤ I).ext fun i ↦ by
      simpa [← basis_inl, ← basis_inr, toBilin'_apply', basisBracket] using
        lie_basis_basis B (.inr a) (.inl i)
  simpa [toBilin'_apply'] using congr($key k)

/-- The bracket of two root vectors is their root bracket. -/
@[simp]
theorem root_lie_root (a b : B.normTwoShell) : ⁅root B a, root B b⁆ = rootBracket B a b := by
  simpa [basisBracket] using lie_basis_basis B (.inr a) (.inr b)

@[simp]
protected theorem zero_lie (y : ShellLieAlgebra B) : ⁅(0 : ShellLieAlgebra B), y⁆ = 0 := by
  simp only [← bracketBilin_apply_apply, map_zero, LinearMap.zero_apply]

@[simp]
protected theorem lie_zero (x : ShellLieAlgebra B) : ⁅x, (0 : ShellLieAlgebra B)⁆ = 0 := by
  simp only [← bracketBilin_apply_apply, map_zero]

@[simp]
protected theorem neg_lie (x y : ShellLieAlgebra B) : ⁅-x, y⁆ = -⁅x, y⁆ := by
  simp only [← bracketBilin_apply_apply, map_neg, LinearMap.neg_apply]

@[simp]
protected theorem lie_neg (x y : ShellLieAlgebra B) : ⁅x, -y⁆ = -⁅x, y⁆ := by
  simp only [← bracketBilin_apply_apply, map_neg]

@[simp]
protected theorem units_smul_lie (u : ℤˣ) (x y : ShellLieAlgebra B) : ⁅u • x, y⁆ = u • ⁅x, y⁆ := by
  simp only [Units.smul_def, ShellLieAlgebra.smul_lie]

@[simp]
protected theorem lie_units_smul (u : ℤˣ) (x y : ShellLieAlgebra B) : ⁅x, u • y⁆ = u • ⁅x, y⁆ := by
  simp only [Units.smul_def, ShellLieAlgebra.lie_smul]

/-- **The Cartan weight of a root bracket.** The bracket of two root vectors has weight the sum of
their roots. -/
@[simp]
theorem cartan_lie_rootBracket (h : I → ℤ) (a b : B.normTwoShell) :
    ⁅cartan B h, rootBracket B a b⁆ = (h ⬝ᵥ B *ᵥ ((a : I → ℤ) + b)) • rootBracket B a b := by
  by_cases hm : (a : I → ℤ) + b ∈ B.normTwoShell
  · rw [rootBracket_of_mem hm, ShellLieAlgebra.lie_units_smul, cartan_lie_root, smul_comm]
  by_cases hz : (a : I → ℤ) + b = 0
  · rw [rootBracket_of_add_eq_zero hz, ShellLieAlgebra.lie_units_smul, cartan_lie_cartan, hz]
    simp
  · simp [rootBracket_of_notMem_of_add_ne_zero hm hz]

/-- **Antisymmetry of the root bracket**, for a symmetric `B` with even diagonal: interchanging the
two roots changes the ordered sign exactly when the roots pair to an odd integer. -/
theorem rootBracket_swap (hB : B.IsSymm) (hdiag : ∀ i, Even (B i i)) (a b : B.normTwoShell) :
    rootBracket B b a = -rootBracket B a b := by
  have hpar := even_orderedSignForm_add_orderedSignForm_swap_sub B hB hdiag a b
  rw [Int.even_iff] at hpar
  by_cases hm : (a : I → ℤ) + b ∈ B.normTwoShell
  · have hm' : (b : I → ℤ) + a ∈ B.normTwoShell := by rwa [add_comm]
    have hp := (hB.add_mem_normTwoShell_iff a.2 b.2).1 hm
    have hsign : (B.orderedSignForm b a).negOnePow = -(B.orderedSignForm a b).negOnePow := by
      rw [← Int.negOnePow_succ, Int.negOnePow_eq_iff, Int.even_iff]
      omega
    -- The two brackets land on the same root `b + a = a + b`, packaged with different proofs.
    have hroot : (⟨_, hm'⟩ : B.normTwoShell) = ⟨_, hm⟩ := Subtype.ext (add_comm _ _)
    rw [rootBracket_of_mem hm, rootBracket_of_mem hm', hsign, Units.neg_smul, hroot]
  by_cases hz : (a : I → ℤ) + b = 0
  · have hb : (b : I → ℤ) = -a := eq_neg_of_add_eq_zero_right hz
    have hp : (a : I → ℤ) ⬝ᵥ B *ᵥ b = -2 := by
      rw [hb, mulVec_neg, dotProduct_neg, mem_normTwoShell.mp a.2]
    have hsign : (B.orderedSignForm b a).negOnePow = (B.orderedSignForm a b).negOnePow := by
      rw [Int.negOnePow_eq_iff, Int.even_iff]
      omega
    have hcartan : cartan B b = -cartan B a := by rw [hb, map_neg]
    rw [rootBracket_of_add_eq_zero hz, rootBracket_of_add_eq_zero (by rwa [add_comm]), hsign,
      hcartan, smul_neg]
  · rw [rootBracket_of_notMem_of_add_ne_zero hm hz,
      rootBracket_of_notMem_of_add_ne_zero (by rwa [add_comm]) (by rwa [add_comm]), neg_zero]

/-- **Antisymmetry of the bracket**, for a symmetric `B` with even diagonal. -/
protected theorem lie_skew (hB : B.IsSymm) (hdiag : ∀ i, Even (B i i)) (x y : ShellLieAlgebra B) :
    ⁅y, x⁆ = -⁅x, y⁆ := by
  have key : (bracketBilin B).flip = -bracketBilin B :=
    (basis B).ext fun i ↦ (basis B).ext fun j ↦ by
      simp only [LinearMap.flip_apply, LinearMap.neg_apply, bracketBilin_apply_apply,
        lie_basis_basis]
      rcases i with i | a <;> rcases j with j | b
      · simp [basisBracket]
      · simp [basisBracket]
      · simp [basisBracket]
      · exact rootBracket_swap hB hdiag a b
  simpa using congr($key x y)

/-- **The bracket is alternating**, for a symmetric `B` with even diagonal. -/
protected theorem lie_self (hB : B.IsSymm) (hdiag : ∀ i, Even (B i i)) (x : ShellLieAlgebra B) :
    ⁅x, x⁆ = 0 := by
  have h := ShellLieAlgebra.lie_skew hB hdiag x x
  refine (basis B).repr.injective (Finsupp.ext fun i ↦ ?_)
  have hi := congr((basis B).repr $h i)
  simp only [map_neg, Finsupp.neg_apply] at hi
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  omega

/-! ### The Jacobi identity -/

/-- The root vector of a lattice vector, or zero if it is not in the norm-two shell. -/
private noncomputable def rootOf (B : Matrix I I ℤ) (v : I → ℤ) : ShellLieAlgebra B := by
  classical
  exact if h : v ∈ B.normTwoShell then root B ⟨v, h⟩ else 0

omit [LinearOrder I] in
private theorem rootOf_coe (a : B.normTwoShell) : rootOf B a = root B a := by
  rw [rootOf, dite_eq_left a.2]

omit [LinearOrder I] in
private theorem rootOf_of_notMem {v : I → ℤ} (h : v ∉ B.normTwoShell) : rootOf B v = 0 := by
  rw [rootOf, dite_eq_right h]

omit [LinearOrder I] in
private theorem rootOf_zero : rootOf B 0 = 0 :=
  rootOf_of_notMem fun h ↦ ne_zero_of_mem_normTwoShell h rfl

/-- The root bracket in a form uniform in the three cases. -/
private theorem rootBracket_eq_rootOf (a b : B.normTwoShell) :
    rootBracket B a b = (B.orderedSignForm a b).negOnePow •
      (rootOf B (a + b) + if (a : I → ℤ) + b = 0 then cartan B a else 0) := by
  by_cases hm : (a : I → ℤ) + b ∈ B.normTwoShell
  · have hz : (a : I → ℤ) + b ≠ 0 := ne_zero_of_mem_normTwoShell hm
    rw [rootBracket_of_mem hm, ite_eq_right hz, add_zero, rootOf, dite_eq_left hm]
  by_cases hz : (a : I → ℤ) + b = 0
  · rw [rootBracket_of_add_eq_zero hz, ite_eq_left hz, hz, rootOf_zero, zero_add]
  · rw [rootBracket_of_notMem_of_add_ne_zero hm hz, rootOf_of_notMem hm, ite_eq_right hz,
      add_zero, smul_zero]

open scoped Classical in
/-- The double bracket `⁅x_a, ⁅x_b, x_c⁆⁆` when `b + c ≠ 0`. -/
private theorem root_lie_rootBracket {a b c : B.normTwoShell} (hbc : (b : I → ℤ) + c ≠ 0) :
    ⁅root B a, rootBracket B b c⁆ = if (b : I → ℤ) + c ∈ B.normTwoShell then
      ((B.orderedSignForm b c).negOnePow * (B.orderedSignForm a (b + c)).negOnePow) •
        (rootOf B (a + b + c) + if (a : I → ℤ) + b + c = 0 then cartan B a else 0)
    else 0 := by
  rw [rootBracket_eq_rootOf b c, ite_eq_right hbc, add_zero, ShellLieAlgebra.lie_units_smul]
  by_cases hm : (b : I → ℤ) + c ∈ B.normTwoShell
  · rw [rootOf, dite_eq_left hm, ite_eq_left hm, root_lie_root, rootBracket_eq_rootOf,
      mul_smul]
    simp only [add_assoc]
  · rw [rootOf_of_notMem hm, ite_eq_right hm, ShellLieAlgebra.lie_zero, smul_zero]

/-- The Jacobi identity for three root vectors, none two of which are equal or opposite. -/
private theorem jacobi_root_root_root_of_ne (hB : B.PosDef) (hdiag : ∀ i, Even (B i i))
    {a b c : B.normTwoShell} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hab' : (a : I → ℤ) + b ≠ 0) (hbc' : (b : I → ℤ) + c ≠ 0) (hca' : (c : I → ℤ) + a ≠ 0) :
    ⁅root B a, rootBracket B b c⁆ + ⁅root B b, rootBracket B c a⁆ +
      ⁅root B c, rootBracket B a b⁆ = 0 := by
  have hS := hB.isHermitian.isSymm
  have ha := a.2
  have hb := b.2
  have hc := c.2
  -- The three pairings lie in `{-1, 0, 1}`, and decide which pairwise sums are roots.
  have bound {x y : B.normTwoShell} (hxy : x ≠ y) (hxy' : (x : I → ℤ) + y ≠ 0) :
      -1 ≤ (x : I → ℤ) ⬝ᵥ B *ᵥ y ∧ (x : I → ℤ) ⬝ᵥ B *ᵥ y ≤ 1 :=
    ⟨hB.neg_one_le_dotProduct_mulVec hdiag x.2 y.2 fun h ↦ hxy' (by rw [h, neg_add_cancel]),
      hB.dotProduct_mulVec_le_one hdiag x.2 y.2 (Subtype.coe_injective.ne hxy)⟩
  have hp := bound hab hab'
  have hq := bound hbc hbc'
  have hr := bound hca hca'
  have hmab := hS.add_mem_normTwoShell_iff ha hb
  have hmbc := hS.add_mem_normTwoShell_iff hb hc
  have hmca := hS.add_mem_normTwoShell_iff hc ha
  have hac : (a : I → ℤ) ⬝ᵥ B *ᵥ c = (c : I → ℤ) ⬝ᵥ B *ᵥ a := hS.dotProduct_mulVec_comm
  -- The parities of the ordered forms.
  have pab := even_orderedSignForm_add_orderedSignForm_swap_sub B hS hdiag a b
  have pbc := even_orderedSignForm_add_orderedSignForm_swap_sub B hS hdiag b c
  have pca := even_orderedSignForm_add_orderedSignForm_swap_sub B hS hdiag c a
  rw [Int.even_iff] at pab pbc pca
  have sign_eq (w x y z : ℤ) (h : (w + x - (y + z)) % 2 = 0) :
      w.negOnePow * x.negOnePow = y.negOnePow * z.negOnePow := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff, Int.even_iff]
    exact h
  have sign_neg (w x y z : ℤ) (h : (w + x - (y + z + 1)) % 2 = 0) :
      w.negOnePow * x.negOnePow = -(y.negOnePow * z.negOnePow) := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_succ, Int.negOnePow_eq_iff,
      Int.even_iff]
    exact h
  -- The norm of `a + b + c`.
  have hnorm : ((a : I → ℤ) + (b : I → ℤ) + (c : I → ℤ)) ⬝ᵥ
      B *ᵥ ((a : I → ℤ) + (b : I → ℤ) + (c : I → ℤ)) =
      6 + 2 * ((a : I → ℤ) ⬝ᵥ B *ᵥ b + (b : I → ℤ) ⬝ᵥ B *ᵥ c + (c : I → ℤ) ⬝ᵥ B *ᵥ a) := by
    rw [hS.add_dotProduct_mulVec_add, hS.add_dotProduct_mulVec_add, add_dotProduct,
      mem_normTwoShell.mp ha, mem_normTwoShell.mp hb, mem_normTwoShell.mp hc, hac]
    ring
  -- Each double bracket lands on the same lattice vector `a + b + c`, in a rotated order.
  have hbca : (b : I → ℤ) + c + a = (a : I → ℤ) + b + c := by abel
  have hcab : (c : I → ℤ) + a + b = (a : I → ℤ) + b + c := by abel
  rw [root_lie_rootBracket hbc', root_lie_rootBracket hca', root_lie_rootBracket hab',
    hbca, hcab]
  simp only [map_add]
  by_cases hd : (a : I → ℤ) + b + c = 0
  · -- All three pairings are `-1`, and the terms are multiples of `H_a`, `H_b` and `H_c`.
    rw [hd, mulVec_zero, dotProduct_zero] at hnorm
    rw [ite_eq_left (hmbc.2 (by omega)), ite_eq_left (hmca.2 (by omega)),
      ite_eq_left (hmab.2 (by omega)),
      sign_eq (B.orderedSignForm c a) (B.orderedSignForm b c + B.orderedSignForm b a)
        (B.orderedSignForm b c) (B.orderedSignForm a b + B.orderedSignForm a c) (by omega),
      sign_eq (B.orderedSignForm a b) (B.orderedSignForm c a + B.orderedSignForm c b)
        (B.orderedSignForm b c) (B.orderedSignForm a b + B.orderedSignForm a c) (by omega)]
    simp only [hd, rootOf_zero, ↓reduceIte, zero_add]
    rw [← smul_add, ← smul_add, ← map_add (cartan B), ← map_add (cartan B), hd, map_zero,
      smul_zero]
  simp only [ite_eq_right hd, add_zero]
  by_cases hdm : (a : I → ℤ) + b + c ∈ B.normTwoShell
  · -- Exactly two pairings are `-1`, and the two surviving terms cancel.
    rw [mem_normTwoShell, hnorm] at hdm
    rcases (by omega : (a : I → ℤ) ⬝ᵥ B *ᵥ b = 0 ∧ (b : I → ℤ) ⬝ᵥ B *ᵥ c = -1 ∧
        (c : I → ℤ) ⬝ᵥ B *ᵥ a = -1 ∨ (a : I → ℤ) ⬝ᵥ B *ᵥ b = -1 ∧ (b : I → ℤ) ⬝ᵥ B *ᵥ c = 0 ∧
        (c : I → ℤ) ⬝ᵥ B *ᵥ a = -1 ∨ (a : I → ℤ) ⬝ᵥ B *ᵥ b = -1 ∧
        (b : I → ℤ) ⬝ᵥ B *ᵥ c = -1 ∧ (c : I → ℤ) ⬝ᵥ B *ᵥ a = 0) with
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [ite_eq_left (hmbc.2 h2), ite_eq_left (hmca.2 h3), ite_eq_right (by rw [hmab]; omega),
        sign_neg (B.orderedSignForm c a) (B.orderedSignForm b c + B.orderedSignForm b a)
          (B.orderedSignForm b c) (B.orderedSignForm a b + B.orderedSignForm a c) (by omega)]
      simp
    · rw [ite_eq_right (by rw [hmbc]; omega), ite_eq_left (hmca.2 h3), ite_eq_left (hmab.2 h1),
        sign_neg (B.orderedSignForm a b) (B.orderedSignForm c a + B.orderedSignForm c b)
          (B.orderedSignForm c a) (B.orderedSignForm b c + B.orderedSignForm b a) (by omega)]
      simp
    · rw [ite_eq_left (hmbc.2 h2), ite_eq_right (by rw [hmca]; omega), ite_eq_left (hmab.2 h1),
        sign_neg (B.orderedSignForm a b) (B.orderedSignForm c a + B.orderedSignForm c b)
          (B.orderedSignForm b c) (B.orderedSignForm a b + B.orderedSignForm a c) (by omega)]
      simp
  · simp [rootOf_of_notMem hdm]

/-- The Jacobi identity for three root vectors, the first two of which are opposite. -/
private theorem jacobi_root_root_root_of_add_eq_zero (hB : B.PosDef) (hdiag : ∀ i, Even (B i i))
    {a b c : B.normTwoShell} (hab : (a : I → ℤ) + b = 0) (hca : c ≠ a) (hcb : c ≠ b) :
    ⁅root B a, rootBracket B b c⁆ + ⁅root B b, rootBracket B c a⁆ +
      ⁅root B c, rootBracket B a b⁆ = 0 := by
  have hS := hB.isHermitian.isSymm
  have hbv : (b : I → ℤ) = -a := eq_neg_of_add_eq_zero_right hab
  have hc0 : (c : I → ℤ) ≠ 0 := ne_zero_of_mem_normTwoShell c.2
  have hbc : (b : I → ℤ) + c ≠ 0 := fun h ↦
    hca (Subtype.ext (neg_add_eq_zero.mp (hbv ▸ h)).symm)
  have hca' : (c : I → ℤ) + a ≠ 0 := fun h ↦
    hcb (Subtype.ext ((eq_neg_of_add_eq_zero_left h).trans hbv.symm))
  -- The pairing `d = ⟪a, c⟫` lies in `{-1, 0, 1}` and decides which of the two sums is a root.
  have hle := hB.dotProduct_mulVec_le_one hdiag a.2 c.2 (Subtype.coe_injective.ne hca.symm)
  have hge := hB.neg_one_le_dotProduct_mulVec hdiag a.2 c.2 fun h ↦
    hcb (Subtype.ext (by rw [hbv, h, neg_neg]))
  have hmbc : (b : I → ℤ) + c ∈ B.normTwoShell ↔ (a : I → ℤ) ⬝ᵥ B *ᵥ c = 1 := by
    rw [hS.add_mem_normTwoShell_iff b.2 c.2, hbv, neg_dotProduct, neg_inj]
  have hmca : (c : I → ℤ) + a ∈ B.normTwoShell ↔ (a : I → ℤ) ⬝ᵥ B *ᵥ c = -1 := by
    rw [hS.add_mem_normTwoShell_iff c.2 a.2, hS.dotProduct_mulVec_comm]
  have pca := even_orderedSignForm_add_orderedSignForm_swap_sub B hS hdiag c a
  rw [Int.even_iff, hS.dotProduct_mulVec_comm] at pca
  -- Since `a + b = 0`, both nonzero double brackets land on the root `c`.
  have habc : (a : I → ℤ) + b + c = c := by rw [hab, zero_add]
  have hbca : (b : I → ℤ) + c + a = c := by rw [hbv]; abel
  rw [root_lie_rootBracket hbc, root_lie_rootBracket hca', rootBracket_of_add_eq_zero hab,
    ShellLieAlgebra.lie_units_smul, root_lie_cartan, habc, hbca, rootOf_coe]
  simp only [hc0, ↓reduceIte, add_zero]
  rcases (by omega : (a : I → ℤ) ⬝ᵥ B *ᵥ c = -1 ∨ (a : I → ℤ) ⬝ᵥ B *ᵥ c = 0 ∨
      (a : I → ℤ) ⬝ᵥ B *ᵥ c = 1) with hd | hd | hd
  · have hsign : (B.orderedSignForm c a).negOnePow * (B.orderedSignForm b (c + a)).negOnePow =
        -(B.orderedSignForm a b).negOnePow := by
      rw [← Int.negOnePow_add, ← Int.negOnePow_succ, Int.negOnePow_eq_iff, Int.even_iff]
      simp only [hbv, map_add, map_neg, LinearMap.neg_apply]
      omega
    rw [ite_eq_right (by rw [hmbc]; omega), ite_eq_left (hmca.2 hd), hsign, hd]
    simp
  · rw [ite_eq_right (by rw [hmbc]; omega), ite_eq_right (by rw [hmca]; omega), hd]
    simp
  · have hsign : (B.orderedSignForm b c).negOnePow * (B.orderedSignForm a (b + c)).negOnePow =
        (B.orderedSignForm a b).negOnePow := by
      rw [← Int.negOnePow_add, Int.negOnePow_eq_iff, Int.even_iff]
      simp only [hbv, map_add, map_neg, LinearMap.neg_apply]
      omega
    rw [ite_eq_left (hmbc.2 hd), ite_eq_right (by rw [hmca]; omega), hsign, hd]
    simp

/-- The Jacobi identity for three root vectors. -/
private theorem jacobi_root_root_root (hB : B.PosDef) (hdiag : ∀ i, Even (B i i))
    (a b c : B.normTwoShell) :
    ⁅root B a, ⁅root B b, root B c⁆⁆ + ⁅root B b, ⁅root B c, root B a⁆⁆ +
      ⁅root B c, ⁅root B a, root B b⁆⁆ = 0 := by
  have hS := hB.isHermitian.isSymm
  -- A repeated root: the identity follows from antisymmetry and alternation.
  have repeated (x z : ShellLieAlgebra B) : ⁅x, ⁅x, z⁆⁆ + ⁅x, ⁅z, x⁆⁆ + ⁅z, ⁅x, x⁆⁆ = 0 := by
    rw [ShellLieAlgebra.lie_skew hS hdiag x z, ShellLieAlgebra.lie_self hS hdiag,
      ShellLieAlgebra.lie_neg, ShellLieAlgebra.lie_zero, add_zero, add_neg_cancel]
  by_cases hab : a = b
  · subst hab
    exact repeated _ _
  by_cases hbc : b = c
  · subst hbc
    rw [add_rotate]
    exact repeated _ _
  by_cases hca : c = a
  · subst hca
    rw [add_rotate, add_rotate]
    exact repeated _ _
  simp only [root_lie_root]
  -- Two opposite roots.
  by_cases hab' : (a : I → ℤ) + b = 0
  · exact jacobi_root_root_root_of_add_eq_zero hB hdiag hab' hca (Ne.symm hbc)
  by_cases hbc' : (b : I → ℤ) + c = 0
  · rw [add_rotate]
    exact jacobi_root_root_root_of_add_eq_zero hB hdiag hbc' hab (Ne.symm hca)
  by_cases hca' : (c : I → ℤ) + a = 0
  · rw [add_rotate, add_rotate]
    exact jacobi_root_root_root_of_add_eq_zero hB hdiag hca' hbc (Ne.symm hab)
  exact jacobi_root_root_root_of_ne hB hdiag hab hbc hca hab' hbc' hca'

/-- The Jacobi identity for two Cartan vectors and a root vector. -/
private theorem jacobi_cartan_cartan_root (h k : I → ℤ) (c : B.normTwoShell) :
    ⁅cartan B h, ⁅cartan B k, root B c⁆⁆ + ⁅cartan B k, ⁅root B c, cartan B h⁆⁆ +
      ⁅root B c, ⁅cartan B h, cartan B k⁆⁆ = 0 := by
  simp only [cartan_lie_root, root_lie_cartan, cartan_lie_cartan, ShellLieAlgebra.lie_smul,
    ShellLieAlgebra.lie_neg, ShellLieAlgebra.lie_zero]
  module

/-- The Jacobi identity for a Cartan vector and two root vectors. -/
private theorem jacobi_cartan_root_root (hB : B.IsSymm) (hdiag : ∀ i, Even (B i i)) (h : I → ℤ)
    (b c : B.normTwoShell) :
    ⁅cartan B h, ⁅root B b, root B c⁆⁆ + ⁅root B b, ⁅root B c, cartan B h⁆⁆ +
      ⁅root B c, ⁅cartan B h, root B b⁆⁆ = 0 := by
  simp only [root_lie_root, cartan_lie_rootBracket, root_lie_cartan, cartan_lie_root,
    ShellLieAlgebra.lie_smul, ShellLieAlgebra.lie_neg, rootBracket_swap hB hdiag b c, mulVec_add,
    dotProduct_add]
  module

/-- The Jacobi identity on the integral basis. -/
private theorem jacobi_basis (hB : B.PosDef) (hdiag : ∀ i, Even (B i i))
    (i j k : I ⊕ B.normTwoShell) :
    ⁅basis B i, ⁅basis B j, basis B k⁆⁆ + ⁅basis B j, ⁅basis B k, basis B i⁆⁆ +
      ⁅basis B k, ⁅basis B i, basis B j⁆⁆ = 0 := by
  have hS := hB.isHermitian.isSymm
  rcases i with i | a <;> rcases j with j | b <;> rcases k with k | c <;>
    simp only [basis_inl, basis_inr]
  · simp
  · exact jacobi_cartan_cartan_root _ _ _
  · rw [add_rotate, add_rotate]
    exact jacobi_cartan_cartan_root _ _ _
  · exact jacobi_cartan_root_root hS hdiag _ _ _
  · rw [add_rotate]
    exact jacobi_cartan_cartan_root _ _ _
  · rw [add_rotate]
    exact jacobi_cartan_root_root hS hdiag _ _ _
  · rw [add_rotate, add_rotate]
    exact jacobi_cartan_root_root hS hdiag _ _ _
  · exact jacobi_root_root_root hB hdiag _ _ _

/-- **The Jacobi identity**, for a positive definite `B` with even diagonal. -/
protected theorem lie_jacobi (hB : B.PosDef) (hdiag : ∀ i, Even (B i i))
    (x y z : ShellLieAlgebra B) :
    ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
  -- Each side is linear in each variable, so it suffices to check it on the basis, one variable
  -- at a time.
  have h₁ (i j : I ⊕ B.normTwoShell) (z : ShellLieAlgebra B) :
      ⁅basis B i, ⁅basis B j, z⁆⁆ + ⁅basis B j, ⁅z, basis B i⁆⁆ +
        ⁅z, ⁅basis B i, basis B j⁆⁆ = 0 := by
    have key : bracketBilin B (basis B i) ∘ₗ bracketBilin B (basis B j) +
        bracketBilin B (basis B j) ∘ₗ (bracketBilin B).flip (basis B i) +
        (bracketBilin B).flip (bracketBilin B (basis B i) (basis B j)) = 0 :=
      (basis B).ext fun k ↦ by simpa using jacobi_basis hB hdiag i j k
    simpa using congr($key z)
  have h₂ (i : I ⊕ B.normTwoShell) (y z : ShellLieAlgebra B) :
      ⁅basis B i, ⁅y, z⁆⁆ + ⁅y, ⁅z, basis B i⁆⁆ + ⁅z, ⁅basis B i, y⁆⁆ = 0 := by
    have key : bracketBilin B (basis B i) ∘ₗ (bracketBilin B).flip z +
        (bracketBilin B).flip (bracketBilin B z (basis B i)) +
        bracketBilin B z ∘ₗ bracketBilin B (basis B i) = 0 :=
      (basis B).ext fun j ↦ by simpa using h₁ i j z
    simpa using congr($key y)
  have key : (bracketBilin B).flip (bracketBilin B y z) + bracketBilin B y ∘ₗ bracketBilin B z +
      bracketBilin B z ∘ₗ (bracketBilin B).flip y = 0 :=
    (basis B).ext fun i ↦ by simpa using h₂ i y z
  simpa using congr($key x)

/-- **The Leibniz form of the Jacobi identity**, for a positive definite `B` with even
diagonal. -/
protected theorem leibniz_lie (hB : B.PosDef) (hdiag : ∀ i, Even (B i i))
    (x y z : ShellLieAlgebra B) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  have hS := hB.isHermitian.isSymm
  rw [ShellLieAlgebra.lie_skew hS hdiag z ⁅x, y⁆, ShellLieAlgebra.lie_skew hS hdiag z x,
    ShellLieAlgebra.lie_neg, ← sub_eq_zero, ← ShellLieAlgebra.lie_jacobi hB hdiag x y z]
  abel

/-- **The signed Lie ring of the norm-two shell** of a positive definite integer matrix `B` with
even diagonal. It is not an instance, since it depends on these two hypotheses; install it
locally when needed. -/
@[expose, instance_reducible]
noncomputable def lieRing (hB : B.PosDef) (hdiag : ∀ i, Even (B i i)) :
    LieRing (ShellLieAlgebra B) where
  add_lie := ShellLieAlgebra.add_lie
  lie_add := ShellLieAlgebra.lie_add
  lie_self := ShellLieAlgebra.lie_self hB.isHermitian.isSymm hdiag
  leibniz_lie := ShellLieAlgebra.leibniz_lie hB hdiag

end ShellLieAlgebra

end Matrix
