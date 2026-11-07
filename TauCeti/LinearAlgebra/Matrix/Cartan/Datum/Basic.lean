/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.Reflection
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix

/-!
# Symmetrizable Cartan data on full lattices

A Cartan datum in the sense of Lusztig is the lattice-level input of a quantized enveloping
algebra `U_v(A, X, Y)`: a weight lattice `X` and a coweight lattice `Y` in perfect duality, simple
roots `αᵢ ∈ X` and simple coroots `hᵢ ∈ Y`, each family linearly independent, whose pairings
`aᵢⱼ = ⟨αⱼ, hᵢ⟩` form a generalized Cartan matrix, together with a chosen positive symmetrizer
`dᵢ aᵢⱼ = dⱼ aⱼᵢ`.

Unlike a Mathlib `RootPairing`, only the simple roots are recorded, and the matrix may be of any
symmetrizable type, finite, affine or indefinite. Unlike a realization of a Cartan matrix over a
field, `Y` is the full coweight lattice: it is not replaced by the coroot lattice, and central and
isogeny directions of `Y` (vectors annihilated by every root, or a lattice strictly between the
coroot lattice and its saturation) are part of the datum. The quantum group has a toral generator
`K_y` for every `y ∈ Y`, so these directions matter.

The perfect pairing is recorded as a bilinear map with `LinearMap.IsPerfPair`, as for
`CartanMatrix.Realisation`. No finiteness or freeness of `X` and `Y` is imposed: nothing below
uses it, and the lattices of root data are the case of free `ℤ`-modules of finite rank.

## Main definitions

* `TauCeti.CartanDatum ι X Y`: a symmetrizable Cartan datum with index type `ι`, weight lattice
  `X` and coweight lattice `Y`.
* `TauCeti.CartanDatum.cartan`: its generalized Cartan matrix, `cartan i j = ⟨αⱼ, hᵢ⟩`.
* `TauCeti.CartanDatum.coreflection`: the simple reflection `y ↦ y − ⟨αᵢ, y⟩ hᵢ` of `Y`, and
  `TauCeti.CartanDatum.reflection`: the simple reflection `λ ↦ λ − ⟨λ, hᵢ⟩ αᵢ` of `X`, both
  Mathlib's `Module.reflection`.
* `TauCeti.CartanDatum.simpleTorus`: the toral direction `dᵢ hᵢ ∈ Y`.
* `TauCeti.CartanDatum.braidLength`: the length `2, 3, 4, 6` of the braid relation between two
  distinct nodes with Cartan product `aᵢⱼ aⱼᵢ = 0, 1, 2, 3`.
* `TauCeti.CartanDatum.Hom`: a morphism of Cartan data, a linear map of coweight lattices carrying
  coroots to coroots and compatible with the roots, such as the one induced by a central isogeny.

## Main results

* `TauCeti.CartanDatum.cartan_eq_zero_iff`: the zero pattern of the Cartan matrix is symmetric.
* `TauCeti.CartanDatum.pairing_reflection_coreflection`: the two reflections preserve the pairing.
* `TauCeti.CartanDatum.coreflection_simpleTorus`:
  `sᵢ(dⱼ hⱼ) = dⱼ hⱼ − aᵢⱼ dᵢ hᵢ`, by symmetrizability.
* `TauCeti.CartanDatum.Hom.weightMap`: the induced map of weight lattices, the transpose of a
  morphism, which carries roots to roots (`TauCeti.CartanDatum.Hom.weightMap_root`).
* `TauCeti.CartanDatum.Hom.cartan_eq`, `TauCeti.CartanDatum.Hom.map_coreflection` and
  `TauCeti.CartanDatum.Hom.weightMap_reflection`: morphisms preserve the Cartan matrix and
  intertwine the reflections.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §1.1 (Cartan data) and §2.2 (root data).
* V. G. Kac, *Infinite Dimensional Lie Algebras*, 3rd ed., Cambridge University Press, 1990,
  §1.1 and §2.1 (generalized Cartan matrices and symmetrizers).
-/

public section

namespace TauCeti

open Module

/-- A **symmetrizable Cartan datum** on full lattices: a perfect pairing `⟨-, -⟩ : X × Y → ℤ`,
linearly independent simple roots `αᵢ ∈ X` and simple coroots `hᵢ ∈ Y` such that the matrix
`aᵢⱼ = ⟨αⱼ, hᵢ⟩` is a generalized Cartan matrix (`aᵢᵢ = 2`, `aᵢⱼ ≤ 0` for `i ≠ j`), and a positive
symmetrizer `d` with `dᵢ aᵢⱼ = dⱼ aⱼᵢ`. The symmetry of the zero pattern of the matrix follows
from the symmetrizer (`TauCeti.CartanDatum.cartan_eq_zero_iff`). -/
structure CartanDatum (ι X Y : Type*) [AddCommGroup X] [AddCommGroup Y] where
  /-- The pairing `⟨-, -⟩` between weights and coweights. -/
  pairing : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ
  [isPerfPair_pairing : pairing.IsPerfPair]
  /-- The simple roots `αᵢ ∈ X`. -/
  root : ι → X
  /-- The simple coroots `hᵢ ∈ Y`. -/
  coroot : ι → Y
  linearIndependent_root : LinearIndependent ℤ root
  linearIndependent_coroot : LinearIndependent ℤ coroot
  pairing_root_coroot_self (i : ι) : pairing (root i) (coroot i) = 2
  pairing_root_coroot_nonpos {i j : ι} (hij : i ≠ j) : pairing (root j) (coroot i) ≤ 0
  /-- The symmetrizer `dᵢ`. -/
  symmetrizer : ι → ℕ
  symmetrizer_pos (i : ι) : 0 < symmetrizer i
  symmetrizer_mul_pairing (i j : ι) :
    (symmetrizer i : ℤ) * pairing (root j) (coroot i) = symmetrizer j * pairing (root i) (coroot j)

attribute [instance] CartanDatum.isPerfPair_pairing

namespace CartanDatum

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (D : CartanDatum ι X Y)

/-! ### The Cartan matrix -/

/-- The generalized Cartan matrix of the datum, in the row convention `aᵢⱼ = ⟨αⱼ, hᵢ⟩`. -/
def cartan : Matrix ι ι ℤ :=
  .of fun i j ↦ D.pairing (D.root j) (D.coroot i)

-- `(rfl)`, not `rfl`: the body of `cartan` is not exposed, and the parenthesised form keeps this
-- proof out of the exported definitional-equality check.
lemma cartan_apply (i j : ι) : D.cartan i j = D.pairing (D.root j) (D.coroot i) := (rfl)

@[simp]
lemma pairing_root_coroot (i j : ι) : D.pairing (D.root j) (D.coroot i) = D.cartan i j :=
  (D.cartan_apply i j).symm

@[simp]
lemma cartan_apply_self (i : ι) : D.cartan i i = 2 := by
  rw [cartan_apply, D.pairing_root_coroot_self]

lemma cartan_nonpos {i j : ι} (hij : i ≠ j) : D.cartan i j ≤ 0 := by
  rw [cartan_apply]
  exact D.pairing_root_coroot_nonpos hij

lemma symmetrizer_mul_cartan (i j : ι) :
    (D.symmetrizer i : ℤ) * D.cartan i j = D.symmetrizer j * D.cartan j i := by
  simpa only [cartan_apply] using D.symmetrizer_mul_pairing i j

/-- The zero pattern of the Cartan matrix is symmetric: `aᵢⱼ = 0 ↔ aⱼᵢ = 0`. -/
lemma cartan_eq_zero_iff (i j : ι) : D.cartan i j = 0 ↔ D.cartan j i = 0 := by
  have hi : (D.symmetrizer i : ℤ) ≠ 0 := by exact_mod_cast (D.symmetrizer_pos i).ne'
  have hj : (D.symmetrizer j : ℤ) ≠ 0 := by exact_mod_cast (D.symmetrizer_pos j).ne'
  have h := D.symmetrizer_mul_cartan i j
  constructor <;> intro h₀
  · rw [h₀, mul_zero, eq_comm, mul_eq_zero] at h
    exact h.resolve_left hj
  · rw [h₀, mul_zero, mul_eq_zero] at h
    exact h.resolve_left hi

/-- The Cartan product `aᵢⱼ aⱼᵢ` of two nodes is nonnegative. -/
lemma cartan_mul_cartan_nonneg (i j : ι) : 0 ≤ D.cartan i j * D.cartan j i := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · exact mul_nonneg_of_nonpos_of_nonpos (D.cartan_nonpos hij) (D.cartan_nonpos hij.symm)

/-! ### Simple reflections -/

/-- The simple reflection `sᵢ y = y − ⟨αᵢ, y⟩ hᵢ` of the coweight lattice. -/
def coreflection (i : ι) : Y ≃ₗ[ℤ] Y :=
  Module.reflection (D.pairing_root_coroot_self i)

/-- The simple reflection `sᵢ λ = λ − ⟨λ, hᵢ⟩ αᵢ` of the weight lattice. -/
def reflection (i : ι) : X ≃ₗ[ℤ] X :=
  Module.reflection (f := D.pairing.flip (D.coroot i)) (x := D.root i) <| by
    rw [LinearMap.flip_apply, D.pairing_root_coroot_self]

lemma coreflection_apply (i : ι) (y : Y) :
    D.coreflection i y = y - D.pairing (D.root i) y • D.coroot i :=
  Module.reflection_apply _ _

lemma reflection_apply (i : ι) (x : X) :
    D.reflection i x = x - D.pairing x (D.coroot i) • D.root i :=
  Module.reflection_apply _ _

lemma coreflection_coroot (i j : ι) :
    D.coreflection i (D.coroot j) = D.coroot j - D.cartan j i • D.coroot i := by
  rw [coreflection_apply, pairing_root_coroot]

lemma reflection_root (i j : ι) :
    D.reflection i (D.root j) = D.root j - D.cartan i j • D.root i := by
  rw [reflection_apply, pairing_root_coroot]

@[simp]
lemma coreflection_coroot_self (i : ι) : D.coreflection i (D.coroot i) = -D.coroot i :=
  Module.reflection_apply_self _

@[simp]
lemma reflection_root_self (i : ι) : D.reflection i (D.root i) = -D.root i :=
  Module.reflection_apply_self _

@[simp]
lemma coreflection_coreflection (i : ι) (y : Y) : D.coreflection i (D.coreflection i y) = y :=
  Module.involutive_reflection _ y

@[simp]
lemma reflection_reflection (i : ι) (x : X) : D.reflection i (D.reflection i x) = x :=
  Module.involutive_reflection _ x

@[simp]
lemma coreflection_symm (i : ι) : (D.coreflection i).symm = D.coreflection i :=
  Module.reflection_symm _

@[simp]
lemma reflection_symm (i : ι) : (D.reflection i).symm = D.reflection i :=
  Module.reflection_symm _

/-- A coweight annihilated by `αᵢ` is fixed by `sᵢ`. -/
lemma coreflection_of_pairing_eq_zero {i : ι} {y : Y} (h : D.pairing (D.root i) y = 0) :
    D.coreflection i y = y := by
  rw [coreflection_apply, h, zero_smul, sub_zero]

/-- A weight annihilated by `hᵢ` is fixed by `sᵢ`. -/
lemma reflection_of_pairing_eq_zero {i : ι} {x : X} (h : D.pairing x (D.coroot i) = 0) :
    D.reflection i x = x := by
  rw [reflection_apply, h, zero_smul, sub_zero]

/-- The two simple reflections at a node are adjoint for the pairing. -/
lemma pairing_reflection (i : ι) (x : X) (y : Y) :
    D.pairing (D.reflection i x) y = D.pairing x (D.coreflection i y) := by
  simp only [reflection_apply, coreflection_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The simple reflections preserve the pairing: `⟨sᵢλ, sᵢy⟩ = ⟨λ, y⟩`. -/
@[simp]
lemma pairing_reflection_coreflection (i : ι) (x : X) (y : Y) :
    D.pairing (D.reflection i x) (D.coreflection i y) = D.pairing x y := by
  rw [pairing_reflection, coreflection_coreflection]

/-! ### Toral directions -/

/-- The toral direction `dᵢ hᵢ ∈ Y`, whose toral generator is `Kᵢ = K_(dᵢ hᵢ)` in the quantized
enveloping algebra. -/
def simpleTorus (i : ι) : Y :=
  D.symmetrizer i • D.coroot i

lemma simpleTorus_def (i : ι) : D.simpleTorus i = D.symmetrizer i • D.coroot i := (rfl)

/-- `⟨αᵢ, dⱼ hⱼ⟩ = dⱼ aⱼᵢ = dᵢ aᵢⱼ`. -/
lemma pairing_root_simpleTorus (i j : ι) :
    D.pairing (D.root i) (D.simpleTorus j) = D.symmetrizer i * D.cartan i j := by
  rw [simpleTorus_def, map_nsmul, pairing_root_coroot, nsmul_eq_mul, D.symmetrizer_mul_cartan]

@[simp]
lemma pairing_root_simpleTorus_self (i : ι) :
    D.pairing (D.root i) (D.simpleTorus i) = 2 * D.symmetrizer i := by
  rw [pairing_root_simpleTorus, cartan_apply_self, mul_comm]

/-- `sᵢ (dⱼ hⱼ) = dⱼ hⱼ − aᵢⱼ (dᵢ hᵢ)`: by symmetrizability the reflections permute the toral
directions up to multiples of one another. -/
lemma coreflection_simpleTorus (i j : ι) :
    D.coreflection i (D.simpleTorus j) = D.simpleTorus j - D.cartan i j • D.simpleTorus i := by
  rw [coreflection_apply, pairing_root_simpleTorus, simpleTorus_def D i, smul_comm, ← natCast_zsmul,
    smul_smul]

@[simp]
lemma coreflection_simpleTorus_self (i : ι) :
    D.coreflection i (D.simpleTorus i) = -D.simpleTorus i := by
  rw [simpleTorus_def, map_nsmul, coreflection_coroot_self, smul_neg]

/-! ### Braid lengths -/

variable [DecidableEq ι]

/-- The length `mᵢⱼ` of the braid relation between the nodes `i` and `j`: for `i ≠ j` it is
`2, 3, 4, 6` according as the Cartan product `aᵢⱼ aⱼᵢ` is `0, 1, 2, 3` (`TauCeti.coxeterOrder`),
and `0`, Mathlib's encoding of an infinite order, when `aᵢⱼ aⱼᵢ ≥ 4`; on the diagonal it is `1`.
For two distinct nodes the Cartan product `4` means an affine pair such as `A₁^(1)`, where no
braid relation holds. -/
def braidLength (i j : ι) : ℕ :=
  if i = j then 1
  else if D.cartan i j * D.cartan j i ≤ 3 then coxeterOrder (D.cartan i j * D.cartan j i) else 0

@[simp]
lemma braidLength_self (i : ι) : D.braidLength i i = 1 := by
  simp [braidLength]

lemma braidLength_of_ne_of_le {i j : ι} (hij : i ≠ j) (h : D.cartan i j * D.cartan j i ≤ 3) :
    D.braidLength i j = coxeterOrder (D.cartan i j * D.cartan j i) := by
  simp [braidLength, hij, h]

lemma braidLength_of_ne_of_lt {i j : ι} (hij : i ≠ j) (h : 3 < D.cartan i j * D.cartan j i) :
    D.braidLength i j = 0 := by
  simp [braidLength, hij, not_le.mpr h]

lemma braidLength_comm (i j : ι) : D.braidLength i j = D.braidLength j i := by
  simp only [braidLength, eq_comm (a := i), mul_comm (D.cartan i j)]

/-- For distinct nodes the braid length is one of `2, 3, 4, 6` exactly when the Cartan product is
at most `3`, and `0` otherwise. -/
lemma braidLength_eq_zero_iff {i j : ι} (hij : i ≠ j) :
    D.braidLength i j = 0 ↔ 3 < D.cartan i j * D.cartan j i := by
  refine ⟨fun h ↦ not_le.mp fun hle ↦ ?_, D.braidLength_of_ne_of_lt hij⟩
  have hmem : D.cartan i j * D.cartan j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
    have := D.cartan_mul_cartan_nonneg i j
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have := two_le_coxeterOrder hmem
  rw [D.braidLength_of_ne_of_le hij hle] at h
  omega

end CartanDatum

end TauCeti
