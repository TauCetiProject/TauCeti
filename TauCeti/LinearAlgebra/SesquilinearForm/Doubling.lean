/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.BilinearForm.Prod
public import TauCeti.LinearAlgebra.Prod

/-!
# The doubled space of a sesquilinear form

For a sesquilinear form `B` on an `R`-module `M`, the *doubled form* `B.doubled` on `W = M × M`
is the orthogonal sum `B ⊕ (-B)`:
`B.doubled (x, y) (x', y') = B x x' - B y y'`.
For a bilinear form this is the product form `LinearMap.BilinForm.prod B (-B)`; the definition
here allows both arguments to be semilinear, which hermitian forms need.
For a hermitian form `h` on a space `V` over a quadratic étale algebra this is the doubled
hermitian space `V ⊕ (-V)` of the doubling method of Piatetski-Shapiro and Rallis, on which
`U(V) × U(-V)` acts blockwise and whose Siegel parabolic is the stabilizer of the diagonal.
Its geometry is governed by two subspaces, which we write as graphs:

* the diagonal `D = {(x, x)}`, which is `(LinearMap.id : M →ₗ[R] M).graph`;
* the antidiagonal `A = {(x, -x)}`, which is `(-LinearMap.id : M →ₗ[R] M).graph`.

More generally the graph of `φ` is isotropic exactly when `φ` is an isometry of `B`, and the
graph of an invertible isometry equals its own orthogonal exactly when `B` is right-separating.
Taking `φ = ±LinearMap.id`, both `D` and `A` are isotropic for every `B`, and for a nondegenerate
form both are maximal isotropic.

When `2` is invertible in `R`, the map `(x, y) ↦ (x, -x) + (y, y)` is a linear automorphism of
`M × M` (`TauCeti.antidiagDiagEquiv`, in `TauCeti.LinearAlgebra.Prod`) with inverse
`(u, v) ↦ ((u - v) / 2, (u + v) / 2)`; it carries the two coordinate axes onto `A` and `D`, so
`W = A ⊕ D` (`TauCeti.isCompl_graph_neg_id_graph_id`), and a linear map or a sesquilinear form on
`W` is determined by its values on `A` and `D` (`TauCeti.linearMap_ext_antidiag_diag`,
`TauCeti.linearMap_ext₂_antidiag_diag`). These polarization coordinates do not involve `B`; in
them the doubled form becomes twice the hyperbolic pairing between `A` and `D`. In particular
`B.doubled (x, -x) (y, y) = 2 • B x y`.

The forms are semilinear in both arguments with respect to arbitrary ring endomorphisms
`I₁ I₂ : R →+* R`. This covers hermitian forms over a field with involution, and also over a
split quadratic algebra `F × F` with the coordinate swap, where no field structure is available.

## Main definitions

* `LinearMap.doubled`: the doubled form `B ⊕ (-B)` on `M × M`.

## Main results

* `LinearMap.toMatrix₂_prod_doubled`: in a basis of the form `b.prod b` the Gram matrix of the
  doubled form is `Matrix.fromBlocks H 0 0 (-H)`.
* `LinearMap.graph_le_orthogonalBilin_doubled_iff`: the graph of `φ` is isotropic exactly when
  `φ` is an isometry of `B`.
* `LinearMap.orthogonalBilin_graph_doubled_eq_iff`: the graph of a surjective isometry is its own
  orthogonal if and only if `B` is right-separating.
* `LinearMap.orthogonalBilin_graph_id_doubled_eq_iff`,
  `LinearMap.orthogonalBilin_graph_neg_id_doubled_eq_iff`: the diagonal and the antidiagonal are
  their own orthogonals if and only if `B` is right-separating.
* `LinearMap.doubled_antidiagDiagEquiv`: the doubled form in polarization coordinates.
* `LinearMap.forall_doubled_prodMap_eq_smul_iff`: `f × g` scales the doubled forms by `c` if and
  only if `f` and `g` both scale the original forms by the same `c`; for `c = 1` this is the
  blockwise embedding of isometries.
* `LinearMap.BilinForm.doubled_eq_prod_neg`: for a bilinear form, `B.doubled` is the product
  form `B.prod (-B)`.

A surjective map acting diagonally on `M × M` carries `D` onto `D` and `A` onto `A`; this is the
special case `ψ = φ = ±LinearMap.id` of `LinearMap.map_prodMap_graph`.

## References

* S. Gelbart, I. Piatetski-Shapiro and S. Rallis, *Explicit constructions of automorphic
  L-functions*, Lecture Notes in Math. 1254 (1987), Part A.
* E. Eischen, M. Harris, J.-S. Li and C. Skinner, *p-adic L-functions for unitary groups*,
  Forum Math. Pi 8 (2020), §4.1.1.
-/

public section

open Module Submodule

namespace LinearMap

variable {R M M' N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N] [Module R N] {I₁ I₂ : R →+* R}

/-- The doubled form `B ⊕ (-B)` on `M × M`, given by
`B.doubled (x, y) (x', y') = B x x' - B y y'`. -/
def doubled (B : M →ₛₗ[I₁] M →ₛₗ[I₂] N) : M × M →ₛₗ[I₁] M × M →ₛₗ[I₂] N :=
  (B.comp (fst R M M)).compl₂ (fst R M M) - (B.comp (snd R M M)).compl₂ (snd R M M)

variable (B : M →ₛₗ[I₁] M →ₛₗ[I₂] N)

@[simp]
theorem doubled_apply (u v : M × M) : B.doubled u v = B u.1 v.1 - B u.2 v.2 := (rfl)

/-- Flipping the doubled form doubles the flipped form. -/
@[simp]
theorem flip_doubled : B.doubled.flip = B.flip.doubled := by
  ext u v
  simp

/-! ### Values on the diagonal and the antidiagonal -/

/-- An antidiagonal vector pairs with a diagonal vector through twice the original form. -/
theorem doubled_apply_antidiag_diag (x y : M) : B.doubled (x, -x) (y, y) = 2 • B x y := by
  simp [two_nsmul]

/-- A diagonal vector pairs with an antidiagonal vector through twice the original form. -/
theorem doubled_apply_diag_antidiag (x y : M) : B.doubled (x, x) (y, -y) = 2 • B x y := by
  simp [two_nsmul]

/-! ### Nondegeneracy and symmetry -/

/-- The doubled form is left-separating exactly when the original form is. -/
@[simp]
theorem separatingLeft_doubled_iff : B.doubled.SeparatingLeft ↔ B.SeparatingLeft := by
  refine ⟨fun h x hx ↦ ?_, fun h u hu ↦ Prod.ext (h u.1 fun y ↦ ?_) (h u.2 fun y ↦ ?_)⟩
  · simpa using congrArg Prod.fst (h (x, 0) fun v ↦ by simp [hx])
  · simpa using hu (y, 0)
  · simpa using hu (0, y)

/-- The doubled form is right-separating exactly when the original form is. -/
@[simp]
theorem separatingRight_doubled_iff : B.doubled.SeparatingRight ↔ B.SeparatingRight := by
  rw [← flip_separatingLeft, flip_doubled, separatingLeft_doubled_iff, flip_separatingLeft]

/-- The doubled form is nondegenerate exactly when the original form is. -/
@[simp]
theorem nondegenerate_doubled_iff : B.doubled.Nondegenerate ↔ B.Nondegenerate :=
  and_congr B.separatingLeft_doubled_iff B.separatingRight_doubled_iff

/-- The doubled form of a hermitian form is hermitian, and conversely. -/
@[simp]
theorem isSymm_doubled_iff {I : R →+* R} {B : M →ₛₗ[I] M →ₗ[R] R} :
    B.doubled.IsSymm ↔ B.IsSymm := by
  refine ⟨fun h ↦ isSymm_def.2 fun x y ↦ by simpa using h.eq (x, 0) (y, 0),
    fun h ↦ isSymm_def.2 fun u v ↦ ?_⟩
  simp [h.eq]

/-! ### Graphs of isometries; the diagonal and the antidiagonal are maximal isotropic -/

/-- The graph of `φ` is isotropic for the doubled form exactly when `φ` is an isometry of `B`. -/
theorem graph_le_orthogonalBilin_doubled_iff (φ : M →ₗ[R] M) :
    φ.graph ≤ φ.graph.orthogonalBilin B.doubled ↔ ∀ x y, B (φ x) (φ y) = B x y := by
  refine ⟨fun h x y ↦ ?_, fun h ⟨x, y⟩ hv ⟨x', y'⟩ hu ↦ ?_⟩
  · have := h (by simp : (y, φ y) ∈ φ.graph) (x, φ x) (by simp)
    rw [doubled_apply, sub_eq_zero] at this
    exact this.symm
  · simp only [mem_graph_iff] at hu hv
    simp [hu, hv, h]

/-- The graph of a surjective isometry `φ` of `B` is its own orthogonal for the doubled form
exactly when `B` is right-separating. -/
theorem orthogonalBilin_graph_doubled_eq_iff (φ : M →ₗ[R] M) (hφs : Function.Surjective φ)
    (hφ : ∀ x y, B (φ x) (φ y) = B x y) :
    φ.graph.orthogonalBilin B.doubled = φ.graph ↔ B.SeparatingRight := by
  refine ⟨fun h y hy ↦ ?_, fun h ↦ le_antisymm (fun ⟨x, y⟩ hxy ↦ ?_)
    ((B.graph_le_orthogonalBilin_doubled_iff φ).2 hφ)⟩
  · have hmem : ((0, y) : M × M) ∈ φ.graph.orthogonalBilin B.doubled := by
      intro u _
      simp [hy]
    rw [h, mem_graph_iff] at hmem
    simpa using hmem
  · rw [mem_graph_iff, eq_comm, ← sub_eq_zero]
    refine h _ fun z ↦ ?_
    obtain ⟨x', rfl⟩ := hφs z
    have := hxy (x', φ x') (by simp)
    rw [doubled_apply, sub_eq_zero, ← hφ x' x] at this
    simpa [sub_eq_zero] using this

/-- The diagonal is isotropic for the doubled form. -/
theorem graph_id_le_orthogonalBilin_doubled :
    (LinearMap.id : M →ₗ[R] M).graph ≤ (LinearMap.id.graph).orthogonalBilin B.doubled :=
  (B.graph_le_orthogonalBilin_doubled_iff _).2 fun _ _ ↦ rfl

/-- The antidiagonal is isotropic for the doubled form. -/
theorem graph_neg_id_le_orthogonalBilin_doubled :
    (-LinearMap.id : M →ₗ[R] M).graph ≤ ((-LinearMap.id).graph).orthogonalBilin B.doubled :=
  (B.graph_le_orthogonalBilin_doubled_iff _).2 fun _ _ ↦ by simp

/-- The diagonal is its own orthogonal for the doubled form exactly when `B` is
right-separating. -/
theorem orthogonalBilin_graph_id_doubled_eq_iff :
    (LinearMap.id.graph).orthogonalBilin B.doubled = (LinearMap.id : M →ₗ[R] M).graph ↔
      B.SeparatingRight :=
  B.orthogonalBilin_graph_doubled_eq_iff _ Function.surjective_id fun _ _ ↦ rfl

/-- The antidiagonal is its own orthogonal for the doubled form exactly when `B` is
right-separating. -/
theorem orthogonalBilin_graph_neg_id_doubled_eq_iff :
    ((-LinearMap.id).graph).orthogonalBilin B.doubled = (-LinearMap.id : M →ₗ[R] M).graph ↔
      B.SeparatingRight :=
  B.orthogonalBilin_graph_doubled_eq_iff _ neg_surjective fun _ _ ↦ by simp

/-! ### Similitudes acting blockwise -/

/-- A blockwise map `f × g` scales the doubled forms by `c` exactly when `f` and `g` both scale
the original forms by the same `c`. -/
theorem forall_doubled_prodMap_eq_smul_iff (B' : M' →ₛₗ[I₁] M' →ₛₗ[I₂] N)
    (f g : M →ₗ[R] M') (c : R) :
    (∀ u v, B'.doubled (f.prodMap g u) (f.prodMap g v) = c • B.doubled u v) ↔
      (∀ x y, B' (f x) (f y) = c • B x y) ∧ ∀ x y, B' (g x) (g y) = c • B x y := by
  refine ⟨fun h ↦ ⟨fun x y ↦ by simpa using h (x, 0) (y, 0),
    fun x y ↦ by simpa [smul_sub] using h (0, x) (0, y)⟩, fun ⟨hf, hg⟩ u v ↦ ?_⟩
  simp [hf, hg, smul_sub]

/-- A blockwise map `f × g` is an isometry of the doubled forms exactly when `f` and `g` are
isometries of the original forms. -/
theorem forall_doubled_prodMap_eq_iff (B' : M' →ₛₗ[I₁] M' →ₛₗ[I₂] N) (f g : M →ₗ[R] M') :
    (∀ u v, B'.doubled (f.prodMap g u) (f.prodMap g v) = B.doubled u v) ↔
      (∀ x y, B' (f x) (f y) = B x y) ∧ ∀ x y, B' (g x) (g y) = B x y := by
  simpa using B.forall_doubled_prodMap_eq_smul_iff B' f g 1

/-- For a bilinear form, the doubled form is the product form `B ⊕ (-B)`. -/
theorem BilinForm.doubled_eq_prod_neg (B : LinearMap.BilinForm R M) :
    B.doubled = B.prod (-B) :=
  ext₂ fun u v ↦ by simp [sub_eq_add_neg]

/-! ### Gram matrices -/

/-- In the basis `b.prod b` of `M × M`, the Gram matrix of the doubled form is the block
diagonal matrix with blocks the Gram matrix `H` of `B` and `-H`. -/
theorem toMatrix₂_prod_doubled {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι R M) :
    toMatrix₂ (b.prod b) (b.prod b) B.doubled =
      Matrix.fromBlocks (toMatrix₂ b b B) 0 0 (-toMatrix₂ b b B) := by
  ext (i | i) (j | j) <;> simp [Basis.prod_apply]

/-! ### Polarization coordinates -/

section Polarization

open TauCeti

variable [Invertible (2 : R)]

/-- In polarization coordinates the doubled form is twice the hyperbolic pairing of the
antidiagonal with the diagonal. -/
theorem doubled_antidiagDiagEquiv (p q : M × M) :
    B.doubled (antidiagDiagEquiv R M p) (antidiagDiagEquiv R M q) =
      2 • (B p.1 q.2 + B p.2 q.1) := by
  simp only [doubled_apply, antidiagDiagEquiv_apply, map_add, map_sub,
    LinearMap.add_apply, LinearMap.sub_apply]
  abel

end Polarization

end LinearMap
