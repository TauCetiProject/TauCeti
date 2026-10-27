/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Basic

/-!
# The signed shell Lie algebra over a full Cartan lattice

Let `B : Matrix I I ℤ` be the Gram matrix of the lattice `Q = I → ℤ`, with norm-two shell `Φ`.
The Lie ring `Matrix.ShellLieAlgebra B` has Cartan part `Q` itself. For the Lie algebra of a
reductive group whose roots are the vectors of `Φ`, the Cartan part should instead be the full
cocharacter lattice `Y`: it can be larger than the span of the coroots, as for `GLₙ`, and it need
not split off the coroot lattice integrally. This file replaces `Q` by an arbitrary abelian group
`Y` equipped with

* root weights `⟨a, -⟩ : Y →ₗ[ℤ] ℤ`, linear in `a : Q`, and
* a coroot map `a ↦ a∨ : Q →ₗ[ℤ] Y`,

subject to `⟨a, b∨⟩ = ⟪a, b⟫`, where `⟪a, b⟫ = a ⬝ᵥ B *ᵥ b`. This is a
`Matrix.ShellCartanDatum B Y`. The carrier `Matrix.FullShellLieAlgebra D` is `Y × (Φ →₀ ℤ)`, with
a Cartan vector `H_y` for each `y : Y` and a root vector `x_a` for each `a ∈ Φ`, and the bracket is

* `⁅H_y, H_z⁆ = 0` and `⁅H_y, x_a⁆ = ⟨a, y⟩ x_a`,
* `⁅x_a, x_b⁆ = ε(a, b) x_(a + b)` if `a + b ∈ Φ`,
* `⁅x_a, x_b⁆ = ε(a, b) H_(a∨)` if `a + b = 0`,
* `⁅x_a, x_b⁆ = 0` otherwise,

with the ordered sign `ε` of `Matrix.SignCover B`, as in `Matrix.ShellLieAlgebra`. Only the
coroot of an opposite bracket is moved into `Y`; no central or derived summand of `Y` is chosen.

The map `Matrix.FullShellLieAlgebra.toFull`, `H_h ↦ H_(h∨)` and `x_a ↦ x_a`, from
`Matrix.ShellLieAlgebra B` preserves the bracket for symmetric `B`
(`Matrix.FullShellLieAlgebra.toFull_lie`). Every root bracket of the full algebra is the image of
the corresponding root bracket of the shell algebra, so the antisymmetry and the Jacobi identity
for root vectors are transported from `Matrix.ShellLieAlgebra`; the remaining cases only use that
`⟨-, y⟩` is additive. For `B` positive definite with even diagonal the bracket is therefore a Lie
ring (`Matrix.FullShellLieAlgebra.lieRing`). As in the shell case nothing is divided by `2`, and
`Y` may have torsion. For the datum `Matrix.ShellCartanDatum.rootLattice B`, with `Y = Q`, the
map `toFull` is a linear equivalence (`Matrix.FullShellLieAlgebra.toFullEquiv`), so for
symmetric `B` the shell algebra is the special case of the coroot lattice. When `Φ` is empty, as
for a torus, the full algebra is the abelian Lie ring `Y`.

## Main definitions

* `Matrix.ShellCartanDatum B Y`: root weights and coroots in `Y` compatible with `B`.
* `Matrix.ShellCartanDatum.rootLattice B`: the datum with `Y = Q` and identity coroot map.
* `Matrix.FullShellLieAlgebra D`: the carrier `Y × (Φ →₀ ℤ)`.
* `Matrix.FullShellLieAlgebra.toFull`: the map `H_h ↦ H_(h∨)`, `x_a ↦ x_a` from the shell
  algebra.
* `Matrix.FullShellLieAlgebra.toFullEquiv B`: `toFull` as a linear equivalence for the datum
  `Matrix.ShellCartanDatum.rootLattice B`.
* `Matrix.FullShellLieAlgebra.rootBracket`: the bracket of two root vectors.
* `Matrix.FullShellLieAlgebra.bracketBilin`: the bracket, as a bilinear map.
* `Matrix.FullShellLieAlgebra.lieRing`: the Lie ring structure, for positive definite `B` with
  even diagonal.

## Main results

* `Matrix.FullShellLieAlgebra.cartan_lie_root`, `Matrix.FullShellLieAlgebra.root_lie_root`: the
  bracket on Cartan and root vectors.
* `Matrix.FullShellLieAlgebra.rootBracket_of_add_eq_zero`: `⁅x_a, x_(-a)⁆ = ε(a, -a) H_(a∨)`.
* `Matrix.FullShellLieAlgebra.toFull_lie`: `toFull` preserves the bracket, for symmetric `B`.
* `Matrix.FullShellLieAlgebra.lie_skew`, `Matrix.FullShellLieAlgebra.lie_self`: antisymmetry and
  alternation, for symmetric `B` with even diagonal.
* `Matrix.FullShellLieAlgebra.lie_jacobi`: the Jacobi identity, for positive definite `B` with
  even diagonal.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, second edition, American Mathematical
  Society (2003), Part II, Chapter 1, for the decomposition of the Lie algebra of a split reductive
  group into the Lie algebra of its maximal torus and the root spaces.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.8.
-/

public section

namespace Matrix

open Module

variable {I : Type*} [Fintype I]

/-- **A full Cartan lattice** for the norm-two shell of an integer Gram matrix `B` on `Q = I → ℤ`:
an abelian group `Y` with root weights `⟨a, -⟩ = weight a : Y →ₗ[ℤ] ℤ`, linear in `a : Q`, and a
coroot map `coroot : Q →ₗ[ℤ] Y`, such that `⟨a, b∨⟩ = a ⬝ᵥ B *ᵥ b`. For a reductive root datum
whose roots, in simple-root coordinates, are the norm-two shell of `B`, `Y` is the cocharacter
lattice and `⟨a, -⟩` is the pairing with the character of `a`. -/
@[ext]
structure ShellCartanDatum (B : Matrix I I ℤ) (Y : Type*) [AddCommGroup Y] where
  /-- The root weight `⟨a, -⟩ : Y →ₗ[ℤ] ℤ` of a lattice vector `a`. -/
  weight : (I → ℤ) →ₗ[ℤ] Y →ₗ[ℤ] ℤ
  /-- The coroot `a∨ : Y` of a lattice vector `a`. -/
  coroot : (I → ℤ) →ₗ[ℤ] Y
  /-- Root weights of coroots are given by the Gram matrix: `⟨a, b∨⟩ = a ⬝ᵥ B *ᵥ b`. -/
  weight_coroot (a b : I → ℤ) : weight a (coroot b) = a ⬝ᵥ B *ᵥ b

namespace ShellCartanDatum

variable (B : Matrix I I ℤ)

/-- The coroot lattice as a full Cartan lattice: `Y = Q`, the identity coroot map, and root
weights `⟨a, y⟩ = a ⬝ᵥ B *ᵥ y`. -/
noncomputable def rootLattice : ShellCartanDatum B (I → ℤ) where
  weight := LinearMap.mk₂ ℤ (fun a y ↦ a ⬝ᵥ B *ᵥ y) (fun _ _ _ ↦ add_dotProduct ..)
    (fun _ _ _ ↦ smul_dotProduct ..) (fun _ _ _ ↦ by rw [mulVec_add, dotProduct_add])
    (fun _ _ _ ↦ by rw [mulVec_smul, dotProduct_smul])
  coroot := LinearMap.id
  weight_coroot _ _ := rfl

@[simp]
theorem rootLattice_weight_apply (a y : I → ℤ) : (rootLattice B).weight a y = a ⬝ᵥ B *ᵥ y :=
  (rfl)

@[simp]
theorem rootLattice_coroot : (rootLattice B).coroot = LinearMap.id :=
  (rfl)

end ShellCartanDatum

variable {B : Matrix I I ℤ} {Y : Type*} [AddCommGroup Y]

/-- The carrier `Y × (Φ →₀ ℤ)` of the signed Lie algebra of the norm-two shell `Φ` of `B` over the
full Cartan lattice `Y` of `D`. The bracket is `Matrix.FullShellLieAlgebra.bracketBilin`. -/
def FullShellLieAlgebra (_D : ShellCartanDatum B Y) : Type _ :=
  Y × (B.normTwoShell →₀ ℤ)

namespace FullShellLieAlgebra

variable (D : ShellCartanDatum B Y)

noncomputable instance : AddCommGroup (FullShellLieAlgebra D) :=
  inferInstanceAs (AddCommGroup (Y × (B.normTwoShell →₀ ℤ)))

/-- The identification of `FullShellLieAlgebra D` with the product `Y × (Φ →₀ ℤ)` defining it. -/
noncomputable def equivProd : FullShellLieAlgebra D ≃ₗ[ℤ] Y × (B.normTwoShell →₀ ℤ) :=
  LinearEquiv.refl ℤ _

/-- The Cartan vector `H_y` of `y : Y`, as a linear map `Y →ₗ[ℤ] FullShellLieAlgebra D`. -/
noncomputable def cartan : Y →ₗ[ℤ] FullShellLieAlgebra D :=
  (equivProd D).symm.toLinearMap ∘ₗ LinearMap.inl ℤ Y (B.normTwoShell →₀ ℤ)

/-- The root vector `x_a` of a vector `a` of the norm-two shell. -/
noncomputable def root (a : B.normTwoShell) : FullShellLieAlgebra D :=
  (equivProd D).symm (0, Finsupp.single a 1)

@[simp]
theorem equivProd_cartan (y : Y) : equivProd D (cartan D y) = (y, 0) := by
  simp [cartan]

@[simp]
theorem equivProd_root (a : B.normTwoShell) :
    equivProd D (root D a) = (0, Finsupp.single a 1) := by
  simp [root]

variable {D} in
/-- Two linear maps out of `FullShellLieAlgebra D` agree once they agree on all Cartan vectors and
on all root vectors. -/
theorem linearMap_ext {N : Type*} [AddCommGroup N] {f g : FullShellLieAlgebra D →ₗ[ℤ] N}
    (hc : ∀ y, f (cartan D y) = g (cartan D y)) (hr : ∀ a, f (root D a) = g (root D a)) :
    f = g := by
  have key : f ∘ₗ (equivProd D).symm.toLinearMap = g ∘ₗ (equivProd D).symm.toLinearMap :=
    LinearMap.prod_ext (LinearMap.ext hc) (Finsupp.lhom_ext' fun a ↦ LinearMap.ext_ring (hr a))
  simpa using congr($key ∘ₗ (equivProd D).toLinearMap)

/-- The map `H_h ↦ H_(h∨)`, `x_a ↦ x_a` from the signed Lie algebra of the norm-two shell, with
Cartan part `Q`, to the one over the full Cartan lattice of `D`. -/
noncomputable def toFull : ShellLieAlgebra B →ₗ[ℤ] FullShellLieAlgebra D :=
  (equivProd D).symm.toLinearMap ∘ₗ D.coroot.prodMap LinearMap.id ∘ₗ
    (ShellLieAlgebra.equivProd B).toLinearMap

@[simp]
theorem toFull_cartan (h : I → ℤ) : toFull D (ShellLieAlgebra.cartan B h) = cartan D (D.coroot h) :=
  (equivProd D).injective (by simp [toFull])

@[simp]
theorem toFull_root (a : B.normTwoShell) : toFull D (ShellLieAlgebra.root B a) = root D a :=
  (equivProd D).injective (by simp [toFull])

/-- For the coroot lattice `Y = Q`, `toFull` is a linear equivalence
(`Matrix.FullShellLieAlgebra.toFullEquiv_apply`); for symmetric `B` it preserves the bracket by
`Matrix.FullShellLieAlgebra.toFull_lie`. -/
noncomputable def toFullEquiv (B : Matrix I I ℤ) :
    ShellLieAlgebra B ≃ₗ[ℤ] FullShellLieAlgebra (ShellCartanDatum.rootLattice B) :=
  (ShellLieAlgebra.equivProd B).trans (equivProd (ShellCartanDatum.rootLattice B)).symm

@[simp]
theorem toFullEquiv_apply (B : Matrix I I ℤ) (x : ShellLieAlgebra B) :
    toFullEquiv B x = toFull (ShellCartanDatum.rootLattice B) x := by
  have key : (toFullEquiv B).toLinearMap = toFull (ShellCartanDatum.rootLattice B) :=
    (ShellLieAlgebra.basis B).ext fun i ↦ by rcases i with i | a <;> simp [toFullEquiv, toFull]
  exact congr($key x)

variable [LinearOrder I]

/-- The bracket `⁅x_a, x_b⁆` of two root vectors: `ε(a, b) x_(a + b)` if `a + b` is in the norm-two
shell, `ε(a, b) H_(a∨)` if `a + b = 0`, and `0` otherwise, where `ε(a, b)` is the ordered sign
`(B.orderedSignForm a b).negOnePow`. It is the image under `toFull` of the root bracket of the
shell algebra. -/
noncomputable def rootBracket (a b : B.normTwoShell) : FullShellLieAlgebra D :=
  toFull D (ShellLieAlgebra.rootBracket B a b)

@[simp]
theorem toFull_rootBracket (a b : B.normTwoShell) :
    toFull D (ShellLieAlgebra.rootBracket B a b) = rootBracket D a b :=
  (rfl)

variable {D} in
/-- The bracket of two root vectors whose sum is in the norm-two shell. -/
@[simp]
theorem rootBracket_of_mem {a b : B.normTwoShell} (h : (a : I → ℤ) + b ∈ B.normTwoShell) :
    rootBracket D a b = (B.orderedSignForm a b).negOnePow • root D ⟨_, h⟩ := by
  rw [rootBracket, ShellLieAlgebra.rootBracket_of_mem h, LinearMap.map_smul_of_tower, toFull_root]

variable {D} in
/-- The bracket of two opposite root vectors is a multiple of the coroot of the first. -/
@[simp]
theorem rootBracket_of_add_eq_zero {a b : B.normTwoShell} (h : (a : I → ℤ) + b = 0) :
    rootBracket D a b = (B.orderedSignForm a b).negOnePow • cartan D (D.coroot a) := by
  rw [rootBracket, ShellLieAlgebra.rootBracket_of_add_eq_zero h, LinearMap.map_smul_of_tower,
    toFull_cartan]

variable {D} in
/-- Two root vectors whose sum is neither in the norm-two shell nor zero have bracket zero. -/
@[simp]
theorem rootBracket_of_notMem_of_add_ne_zero {a b : B.normTwoShell}
    (h : (a : I → ℤ) + b ∉ B.normTwoShell) (h' : (a : I → ℤ) + b ≠ 0) :
    rootBracket D a b = 0 := by
  rw [rootBracket, ShellLieAlgebra.rootBracket_of_notMem_of_add_ne_zero h h', map_zero]

/-- The action `y ↦ (x_b ↦ ⟨b, y⟩ x_b)` of the Cartan lattice on the root part. -/
private noncomputable def cartanAction :
    Y →ₗ[ℤ] (B.normTwoShell →₀ ℤ) →ₗ[ℤ] FullShellLieAlgebra D :=
  (Finsupp.linearCombination ℤ fun b : B.normTwoShell ↦
    (D.weight b).smulRight (root D b)).flip

/-- The root bracket, extended bilinearly to the root part. -/
private noncomputable def rootPart :
    (B.normTwoShell →₀ ℤ) →ₗ[ℤ] (B.normTwoShell →₀ ℤ) →ₗ[ℤ] FullShellLieAlgebra D :=
  Finsupp.linearCombination ℤ fun a ↦ Finsupp.linearCombination ℤ fun b ↦ rootBracket D a b

/-- The bracket of `FullShellLieAlgebra D`, as the bilinear map determined by `⁅H_y, H_z⁆ = 0`,
`⁅H_y, x_b⁆ = ⟨b, y⟩ x_b`, `⁅x_a, H_z⁆ = -⟨a, z⟩ x_a` and `⁅x_a, x_b⁆ = rootBracket D a b`. -/
noncomputable def bracketBilin :
    FullShellLieAlgebra D →ₗ[ℤ] FullShellLieAlgebra D →ₗ[ℤ] FullShellLieAlgebra D :=
  let fst := LinearMap.fst ℤ Y (B.normTwoShell →₀ ℤ) ∘ₗ (equivProd D).toLinearMap
  let snd := LinearMap.snd ℤ Y (B.normTwoShell →₀ ℤ) ∘ₗ (equivProd D).toLinearMap
  (cartanAction D).compl₁₂ fst snd - ((cartanAction D).compl₁₂ fst snd).flip +
    (rootPart D).compl₁₂ snd snd

/-- The bracket of `FullShellLieAlgebra D` is `Matrix.FullShellLieAlgebra.bracketBilin`. It is a
Lie bracket for positive definite `B` with even diagonal, see `Matrix.FullShellLieAlgebra.lieRing`.
-/
noncomputable instance : Bracket (FullShellLieAlgebra D) (FullShellLieAlgebra D) :=
  ⟨fun x y ↦ bracketBilin D x y⟩

@[simp]
theorem bracketBilin_apply_apply (x y : FullShellLieAlgebra D) : bracketBilin D x y = ⁅x, y⁆ :=
  (rfl)

variable {D}

@[simp]
protected theorem add_lie (x y z : FullShellLieAlgebra D) : ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := by
  simp only [← bracketBilin_apply_apply, map_add, LinearMap.add_apply]

@[simp]
protected theorem lie_add (x y z : FullShellLieAlgebra D) : ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ := by
  simp only [← bracketBilin_apply_apply, map_add]

@[simp]
protected theorem smul_lie (n : ℤ) (x y : FullShellLieAlgebra D) : ⁅n • x, y⁆ = n • ⁅x, y⁆ := by
  simp only [← bracketBilin_apply_apply, map_smul, LinearMap.smul_apply]

@[simp]
protected theorem lie_smul (n : ℤ) (x y : FullShellLieAlgebra D) : ⁅x, n • y⁆ = n • ⁅x, y⁆ := by
  simp only [← bracketBilin_apply_apply, map_smul]

@[simp]
protected theorem zero_lie (y : FullShellLieAlgebra D) : ⁅(0 : FullShellLieAlgebra D), y⁆ = 0 := by
  simp only [← bracketBilin_apply_apply, map_zero, LinearMap.zero_apply]

@[simp]
protected theorem lie_zero (x : FullShellLieAlgebra D) : ⁅x, (0 : FullShellLieAlgebra D)⁆ = 0 := by
  simp only [← bracketBilin_apply_apply, map_zero]

@[simp]
protected theorem neg_lie (x y : FullShellLieAlgebra D) : ⁅-x, y⁆ = -⁅x, y⁆ := by
  simp only [← bracketBilin_apply_apply, map_neg, LinearMap.neg_apply]

@[simp]
protected theorem lie_neg (x y : FullShellLieAlgebra D) : ⁅x, -y⁆ = -⁅x, y⁆ := by
  simp only [← bracketBilin_apply_apply, map_neg]

/-- Cartan vectors commute. -/
@[simp]
theorem cartan_lie_cartan (y z : Y) : ⁅cartan D y, cartan D z⁆ = 0 := by
  simp [← bracketBilin_apply_apply, bracketBilin]

/-- The Cartan vector `H_y` acts on the root vector `x_b` by the root weight `⟨b, y⟩`. -/
@[simp]
theorem cartan_lie_root (y : Y) (b : B.normTwoShell) :
    ⁅cartan D y, root D b⁆ = D.weight b y • root D b := by
  simp [← bracketBilin_apply_apply, bracketBilin, cartanAction]

/-- The bracket `⁅x_a, H_z⁆ = -⟨a, z⟩ x_a`. -/
@[simp]
theorem root_lie_cartan (a : B.normTwoShell) (z : Y) :
    ⁅root D a, cartan D z⁆ = -(D.weight a z • root D a) := by
  simp [← bracketBilin_apply_apply, bracketBilin, cartanAction]

/-- The bracket of two root vectors is their root bracket. -/
@[simp]
theorem root_lie_root (a b : B.normTwoShell) : ⁅root D a, root D b⁆ = rootBracket D a b := by
  simp [← bracketBilin_apply_apply, bracketBilin, rootPart]

@[simp]
protected theorem units_smul_lie (u : ℤˣ) (x y : FullShellLieAlgebra D) :
    ⁅u • x, y⁆ = u • ⁅x, y⁆ := by
  simp only [Units.smul_def, FullShellLieAlgebra.smul_lie]

@[simp]
protected theorem lie_units_smul (u : ℤˣ) (x y : FullShellLieAlgebra D) :
    ⁅x, u • y⁆ = u • ⁅x, y⁆ := by
  simp only [Units.smul_def, FullShellLieAlgebra.lie_smul]

/-- **`toFull` preserves the bracket**, for a symmetric `B`. -/
theorem toFull_lie (hB : B.IsSymm) (x y : ShellLieAlgebra B) :
    toFull D ⁅x, y⁆ = ⁅toFull D x, toFull D y⁆ := by
  -- The weight of a coroot is symmetric in the two lattice vectors.
  have hw (h : I → ℤ) (b : B.normTwoShell) : D.weight b (D.coroot h) = h ⬝ᵥ B *ᵥ (b : I → ℤ) := by
    rw [D.weight_coroot, hB.dotProduct_mulVec_comm]
  have key : (ShellLieAlgebra.bracketBilin B).compr₂ (toFull D) =
      (bracketBilin D).compl₁₂ (toFull D) (toFull D) :=
    LinearMap.ext_basis (ShellLieAlgebra.basis B) (ShellLieAlgebra.basis B) fun i j ↦ by
      rcases i with i | a <;> rcases j with j | b <;> simp [hw]
  simpa using congr($key x y)

/-- **The Cartan weight of a root bracket.** The bracket of two root vectors has root weight the
sum of the weights of their roots. -/
@[simp]
theorem cartan_lie_rootBracket (y : Y) (a b : B.normTwoShell) :
    ⁅cartan D y, rootBracket D a b⁆ = D.weight ((a : I → ℤ) + b) y • rootBracket D a b := by
  by_cases hm : (a : I → ℤ) + b ∈ B.normTwoShell
  · rw [rootBracket_of_mem hm, FullShellLieAlgebra.lie_units_smul, cartan_lie_root, smul_comm]
  by_cases hz : (a : I → ℤ) + b = 0
  · rw [rootBracket_of_add_eq_zero hz, FullShellLieAlgebra.lie_units_smul, cartan_lie_cartan, hz]
    simp
  · simp [rootBracket_of_notMem_of_add_ne_zero hm hz]

/-- **Antisymmetry of the root bracket**, for a symmetric `B` with even diagonal. -/
theorem rootBracket_swap (hB : B.IsSymm) (hdiag : ∀ i, Even (B i i)) (a b : B.normTwoShell) :
    rootBracket D b a = -rootBracket D a b := by
  rw [rootBracket, ShellLieAlgebra.rootBracket_swap hB hdiag, map_neg, toFull_rootBracket]

/-- **Antisymmetry of the bracket**, for a symmetric `B` with even diagonal. -/
protected theorem lie_skew (hB : B.IsSymm) (hdiag : ∀ i, Even (B i i))
    (x y : FullShellLieAlgebra D) : ⁅y, x⁆ = -⁅x, y⁆ := by
  have key : (bracketBilin D).flip = -bracketBilin D := by
    refine linearMap_ext (fun y ↦ linearMap_ext (fun z ↦ ?_) fun b ↦ ?_)
      fun a ↦ linearMap_ext (fun z ↦ ?_) fun b ↦ ?_ <;>
      simp only [LinearMap.flip_apply, LinearMap.neg_apply, bracketBilin_apply_apply]
    · simp
    · simp
    · simp
    · rw [root_lie_root, root_lie_root, rootBracket_swap hB hdiag]
  simpa using congr($key x y)

/-- **The bracket is alternating**, for a symmetric `B` with even diagonal. The group `Y` may have
`2`-torsion, so this is not a consequence of antisymmetry alone. -/
protected theorem lie_self (hB : B.IsSymm) (hdiag : ∀ i, Even (B i i))
    (x : FullShellLieAlgebra D) : ⁅x, x⁆ = 0 := by
  -- By antisymmetry `x ↦ ⁅x, x⁆` is additive, so it suffices to check it on generators.
  let q : FullShellLieAlgebra D →+ FullShellLieAlgebra D :=
    { toFun x := ⁅x, x⁆
      map_zero' := FullShellLieAlgebra.zero_lie 0
      map_add' x y := by
        simp only [FullShellLieAlgebra.add_lie, FullShellLieAlgebra.lie_add,
          FullShellLieAlgebra.lie_skew hB hdiag x y]
        abel }
  have key : q.toIntLinearMap = 0 := linearMap_ext (by simp [q]) fun a ↦ by
    simpa [q] using congr(toFull D $(ShellLieAlgebra.lie_self hB hdiag (ShellLieAlgebra.root B a)))
  exact congr($key x)

/-! ### The Jacobi identity -/

/-- The Jacobi identity for three root vectors, transported from the shell algebra. -/
private theorem jacobi_root_root_root (hB : B.PosDef) (hdiag : ∀ i, Even (B i i))
    (a b c : B.normTwoShell) :
    ⁅root D a, ⁅root D b, root D c⁆⁆ + ⁅root D b, ⁅root D c, root D a⁆⁆ +
      ⁅root D c, ⁅root D a, root D b⁆⁆ = 0 := by
  have hS := hB.isHermitian.isSymm
  simpa [toFull_lie hS] using congr(toFull D $(ShellLieAlgebra.lie_jacobi hB hdiag
    (ShellLieAlgebra.root B a) (ShellLieAlgebra.root B b) (ShellLieAlgebra.root B c)))

/-- The Jacobi identity for two Cartan vectors and a root vector. -/
private theorem jacobi_cartan_cartan_root (y z : Y) (c : B.normTwoShell) :
    ⁅cartan D y, ⁅cartan D z, root D c⁆⁆ + ⁅cartan D z, ⁅root D c, cartan D y⁆⁆ +
      ⁅root D c, ⁅cartan D y, cartan D z⁆⁆ = 0 := by
  simp only [cartan_lie_root, root_lie_cartan, cartan_lie_cartan, FullShellLieAlgebra.lie_smul,
    FullShellLieAlgebra.lie_neg, FullShellLieAlgebra.lie_zero]
  module

/-- The Jacobi identity for a Cartan vector and two root vectors. -/
private theorem jacobi_cartan_root_root (hB : B.IsSymm) (hdiag : ∀ i, Even (B i i)) (y : Y)
    (b c : B.normTwoShell) :
    ⁅cartan D y, ⁅root D b, root D c⁆⁆ + ⁅root D b, ⁅root D c, cartan D y⁆⁆ +
      ⁅root D c, ⁅cartan D y, root D b⁆⁆ = 0 := by
  simp only [root_lie_root, cartan_lie_rootBracket, root_lie_cartan, cartan_lie_root,
    FullShellLieAlgebra.lie_smul, FullShellLieAlgebra.lie_neg, rootBracket_swap hB hdiag b c,
    map_add, LinearMap.add_apply]
  module

/-- The Jacobi identity with the first two arguments Cartan or root vectors. -/
private theorem jacobi_gen_gen (hB : B.PosDef) (hdiag : ∀ i, Even (B i i))
    (u v : Y ⊕ B.normTwoShell) (z : FullShellLieAlgebra D) :
    let gen : Y ⊕ B.normTwoShell → FullShellLieAlgebra D := Sum.elim (cartan D) (root D)
    ⁅gen u, ⁅gen v, z⁆⁆ + ⁅gen v, ⁅z, gen u⁆⁆ + ⁅z, ⁅gen u, gen v⁆⁆ = 0 := by
  intro gen
  have hS := hB.isHermitian.isSymm
  have key : bracketBilin D (gen u) ∘ₗ bracketBilin D (gen v) +
      bracketBilin D (gen v) ∘ₗ (bracketBilin D).flip (gen u) +
      (bracketBilin D).flip (bracketBilin D (gen u) (gen v)) = 0 := by
    refine linearMap_ext (fun y ↦ ?_) fun c ↦ ?_ <;>
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.flip_apply,
        bracketBilin_apply_apply, LinearMap.zero_apply] <;>
      rcases u with x | a <;> rcases v with x' | b <;> simp only [gen, Sum.elim_inl, Sum.elim_inr]
    · simp
    · rw [add_rotate, add_rotate]
      exact jacobi_cartan_cartan_root _ _ _
    · rw [add_rotate]
      exact jacobi_cartan_cartan_root _ _ _
    · rw [add_rotate, add_rotate]
      exact jacobi_cartan_root_root hS hdiag _ _ _
    · exact jacobi_cartan_cartan_root _ _ _
    · exact jacobi_cartan_root_root hS hdiag _ _ _
    · rw [add_rotate]
      exact jacobi_cartan_root_root hS hdiag _ _ _
    · exact jacobi_root_root_root hB hdiag _ _ _
  simpa using congr($key z)

/-- **The Jacobi identity**, for a positive definite `B` with even diagonal. -/
protected theorem lie_jacobi (hB : B.PosDef) (hdiag : ∀ i, Even (B i i))
    (x y z : FullShellLieAlgebra D) :
    ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
  -- Each side is linear in each variable, so it suffices to check it on Cartan and root vectors,
  -- one variable at a time.
  have h₂ (u : Y ⊕ B.normTwoShell) (y z : FullShellLieAlgebra D) :
      ⁅Sum.elim (cartan D) (root D) u, ⁅y, z⁆⁆ + ⁅y, ⁅z, Sum.elim (cartan D) (root D) u⁆⁆ +
        ⁅z, ⁅Sum.elim (cartan D) (root D) u, y⁆⁆ = 0 := by
    have key : bracketBilin D (Sum.elim (cartan D) (root D) u) ∘ₗ (bracketBilin D).flip z +
        (bracketBilin D).flip (bracketBilin D z (Sum.elim (cartan D) (root D) u)) +
        bracketBilin D z ∘ₗ bracketBilin D (Sum.elim (cartan D) (root D) u) = 0 :=
      linearMap_ext (fun y ↦ by simpa using jacobi_gen_gen hB hdiag u (.inl y) z)
        fun b ↦ by simpa using jacobi_gen_gen hB hdiag u (.inr b) z
    simpa using congr($key y)
  have key : (bracketBilin D).flip (bracketBilin D y z) + bracketBilin D y ∘ₗ bracketBilin D z +
      bracketBilin D z ∘ₗ (bracketBilin D).flip y = 0 :=
    linearMap_ext (fun x ↦ by simpa using h₂ (.inl x) y z) fun a ↦ by simpa using h₂ (.inr a) y z
  simpa using congr($key x)

/-- **The Leibniz form of the Jacobi identity**, for a positive definite `B` with even
diagonal. -/
protected theorem leibniz_lie (hB : B.PosDef) (hdiag : ∀ i, Even (B i i))
    (x y z : FullShellLieAlgebra D) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  have hS := hB.isHermitian.isSymm
  rw [FullShellLieAlgebra.lie_skew hS hdiag z ⁅x, y⁆, FullShellLieAlgebra.lie_skew hS hdiag z x,
    FullShellLieAlgebra.lie_neg, ← sub_eq_zero, ← FullShellLieAlgebra.lie_jacobi hB hdiag x y z]
  abel

variable (D) in
/-- **The signed Lie ring of the norm-two shell over a full Cartan lattice**, for a positive
definite integer matrix `B` with even diagonal. It is not an instance, since it depends on these
two hypotheses; install it locally when needed. -/
@[expose, instance_reducible]
noncomputable def lieRing (hB : B.PosDef) (hdiag : ∀ i, Even (B i i)) :
    LieRing (FullShellLieAlgebra D) where
  add_lie := FullShellLieAlgebra.add_lie
  lie_add := FullShellLieAlgebra.lie_add
  lie_self := FullShellLieAlgebra.lie_self hB.isHermitian.isSymm hdiag
  leibniz_lie := FullShellLieAlgebra.leibniz_lie hB hdiag

end FullShellLieAlgebra

end Matrix
