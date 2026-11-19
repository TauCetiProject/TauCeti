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
`M × M` (`TauCeti.doublingPolarizationEquiv`) with inverse `(u, v) ↦ ((u - v) / 2, (u + v) / 2)`;
it carries the two coordinate axes onto `A` and `D`, so `W = A ⊕ D`, and in these coordinates the
doubled form becomes twice the hyperbolic pairing between `A` and `D`. In particular
`B.doubled (x, -x) (y, y) = 2 • B x y`.

The forms are semilinear in both arguments with respect to arbitrary ring endomorphisms
`I₁ I₂ : R →+* R`. This covers hermitian forms over a field with involution, and also over a
split quadratic algebra `F × F` with the coordinate swap, where no field structure is available.

## Main definitions

* `LinearMap.doubled`: the doubled form `B ⊕ (-B)` on `M × M`.
* `TauCeti.doublingPolarizationEquiv`: the polarization coordinates `A ⊕ D ≃ W`.

## Main results

* `LinearMap.toMatrix₂_prod_doubled`: in a basis of the form `b.prod b` the Gram matrix of the
  doubled form is `Matrix.fromBlocks H 0 0 (-H)`.
* `LinearMap.graph_le_orthogonalBilin_doubled_iff`: the graph of `φ` is isotropic exactly when
  `φ` is an isometry of `B`.
* `LinearMap.orthogonalBilin_graph_doubled_eq_iff`: the graph of an invertible isometry is its own
  orthogonal if and only if `B` is right-separating.
* `LinearMap.orthogonalBilin_graph_id_doubled_eq_iff`,
  `LinearMap.orthogonalBilin_graph_neg_id_doubled_eq_iff`: the diagonal and the antidiagonal are
  their own orthogonals if and only if `B` is right-separating.
* `TauCeti.isCompl_graph_neg_id_graph_id`: `W = A ⊕ D` when `2` is invertible.
* `LinearMap.doubled_doublingPolarizationEquiv`: the doubled form in polarization coordinates.
* `TauCeti.linearMap_ext_antidiag_diag`, `TauCeti.linearMap_ext₂_antidiag_diag`: a linear map,
  respectively a sesquilinear form, on `W` is determined by its values on `A` and `D`.
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

/-- The graph of an isometry `φ` of `B` is its own orthogonal for the doubled form exactly when
`B` is right-separating. -/
theorem orthogonalBilin_graph_doubled_eq_iff (φ : M ≃ₗ[R] M)
    (hφ : ∀ x y, B (φ x) (φ y) = B x y) :
    (φ : M →ₗ[R] M).graph.orthogonalBilin B.doubled = (φ : M →ₗ[R] M).graph ↔
      B.SeparatingRight := by
  refine ⟨fun h y hy ↦ ?_, fun h ↦ le_antisymm (fun ⟨x, y⟩ hxy ↦ ?_)
    ((B.graph_le_orthogonalBilin_doubled_iff φ).2 hφ)⟩
  · have hmem : ((y, 0) : M × M) ∈ (φ : M →ₗ[R] M).graph.orthogonalBilin B.doubled := by
      intro u _
      simp [hy]
    rw [h, mem_graph_iff] at hmem
    simpa using hmem.symm
  · rw [mem_graph_iff, eq_comm, ← sub_eq_zero]
    refine h _ fun z ↦ ?_
    obtain ⟨x', rfl⟩ := φ.surjective z
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
  B.orthogonalBilin_graph_doubled_eq_iff (LinearEquiv.refl R M) fun _ _ ↦ rfl

/-- The antidiagonal is its own orthogonal for the doubled form exactly when `B` is
right-separating. -/
theorem orthogonalBilin_graph_neg_id_doubled_eq_iff :
    ((-LinearMap.id).graph).orthogonalBilin B.doubled = (-LinearMap.id : M →ₗ[R] M).graph ↔
      B.SeparatingRight :=
  B.orthogonalBilin_graph_doubled_eq_iff (LinearEquiv.neg R) fun _ _ ↦ by simp

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

end LinearMap

/-! ### Polarization coordinates -/

namespace TauCeti

open LinearMap

variable (R M : Type*) [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

/-- The polarization coordinates of the doubled space: the linear automorphism of `M × M`
sending `(x, y)` to `(x, -x) + (y, y) = (x + y, y - x)`, that is, the first factor to the
antidiagonal and the second to the diagonal. Its inverse is
`(u, v) ↦ ((u - v) / 2, (u + v) / 2)`. -/
def doublingPolarizationEquiv : (M × M) ≃ₗ[R] M × M where
  toFun p := (p.1 + p.2, p.2 - p.1)
  invFun q := ((⅟2 : R) • (q.1 - q.2), (⅟2 : R) • (q.1 + q.2))
  map_add' p q := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' c p := by
    ext <;> simp [smul_add, smul_sub]
  left_inv p := by
    ext <;> dsimp only
    · rw [show p.1 + p.2 - (p.2 - p.1) = (2 : R) • p.1 by module, invOf_smul_smul]
    · rw [show p.1 + p.2 + (p.2 - p.1) = (2 : R) • p.2 by module, invOf_smul_smul]
  right_inv q := by
    ext <;> dsimp only
    · rw [← smul_add, show q.1 - q.2 + (q.1 + q.2) = (2 : R) • q.1 by module, invOf_smul_smul]
    · rw [← smul_sub, show q.1 + q.2 - (q.1 - q.2) = (2 : R) • q.2 by module, invOf_smul_smul]

variable {R M}

/-- The polarization coordinates send `(x, y)` to `(x + y, y - x)`. -/
@[simp]
theorem doublingPolarizationEquiv_apply (p : M × M) :
    doublingPolarizationEquiv R M p = (p.1 + p.2, p.2 - p.1) := (rfl)

/-- The inverse of the polarization coordinates sends `(u, v)` to
`((u - v) / 2, (u + v) / 2)`. -/
@[simp]
theorem doublingPolarizationEquiv_symm_apply (q : M × M) :
    (doublingPolarizationEquiv R M).symm q =
      ((⅟2 : R) • (q.1 - q.2), (⅟2 : R) • (q.1 + q.2)) := (rfl)

/-- The polarization coordinates decompose a vector as an antidiagonal plus a diagonal vector. -/
theorem doublingPolarizationEquiv_apply_eq_add (x y : M) :
    doublingPolarizationEquiv R M (x, y) = (x, -x) + (y, y) := by
  ext <;> simp [sub_eq_neg_add]

/-- The polarization coordinates carry the first axis `M × 0` onto the antidiagonal. -/
theorem map_doublingPolarizationEquiv_range_inl :
    (range (inl R M M)).map (doublingPolarizationEquiv R M : (M × M) →ₗ[R] M × M) =
      (-LinearMap.id : M →ₗ[R] M).graph := by
  ext ⟨a, b⟩
  simp only [mem_map, mem_range, inl_apply, mem_graph_iff, LinearMap.neg_apply, id_apply]
  refine ⟨?_, fun h ↦ ⟨(a, 0), ⟨a, rfl⟩, by simp [h]⟩⟩
  rintro ⟨_, ⟨x, rfl⟩, h⟩
  simp only [LinearEquiv.coe_coe, doublingPolarizationEquiv_apply, add_zero, zero_sub,
    Prod.mk.injEq] at h
  rw [← h.1, ← h.2]

/-- The polarization coordinates carry the second axis `0 × M` onto the diagonal. -/
theorem map_doublingPolarizationEquiv_range_inr :
    (range (inr R M M)).map (doublingPolarizationEquiv R M : (M × M) →ₗ[R] M × M) =
      (LinearMap.id : M →ₗ[R] M).graph := by
  ext ⟨a, b⟩
  simp only [mem_map, mem_range, inr_apply, mem_graph_iff, id_apply]
  refine ⟨?_, fun h ↦ ⟨(0, a), ⟨a, rfl⟩, by simp [h]⟩⟩
  rintro ⟨_, ⟨x, rfl⟩, h⟩
  simp only [LinearEquiv.coe_coe, doublingPolarizationEquiv_apply, zero_add, sub_zero,
    Prod.mk.injEq] at h
  rw [← h.1, ← h.2]

/-- When `2` is invertible, `M × M` is the direct sum of the antidiagonal and the diagonal. -/
theorem isCompl_graph_neg_id_graph_id :
    IsCompl (-LinearMap.id : M →ₗ[R] M).graph (LinearMap.id : M →ₗ[R] M).graph := by
  rw [← map_doublingPolarizationEquiv_range_inl, ← map_doublingPolarizationEquiv_range_inr]
  exact (orderIsoMapComap (doublingPolarizationEquiv R M)).isCompl_iff.1 isCompl_range_inl_inr

/-- The polarization coordinates commute with any linear map acting diagonally. -/
theorem doublingPolarizationEquiv_prodMap {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (p : M × M) :
    doublingPolarizationEquiv R M' (f.prodMap f p) =
      f.prodMap f (doublingPolarizationEquiv R M p) := by
  simp

/-- A semilinear map on `M × M` is determined by its values on the antidiagonal and on the
diagonal. -/
theorem linearMap_ext_antidiag_diag {S P : Type*} [Semiring S] [AddCommMonoid P] [Module S P]
    {σ : R →+* S} {f g : M × M →ₛₗ[σ] P} (hA : ∀ x, f (x, -x) = g (x, -x))
    (hD : ∀ x, f (x, x) = g (x, x)) : f = g :=
  ext_on_codisjoint isCompl_graph_neg_id_graph_id.codisjoint
    (fun ⟨x, y⟩ hp ↦ by rw [show y = -x by simpa using hp]; exact hA x)
    fun ⟨x, y⟩ hp ↦ by rw [show y = x by simpa using hp]; exact hD x

/-- A sesquilinear form on `M × M` is determined by its four blocks with respect to the
antidiagonal and the diagonal. -/
theorem linearMap_ext₂_antidiag_diag {N : Type*} [AddCommGroup N] [Module R N] {I₁ I₂ : R →+* R}
    {C C' : M × M →ₛₗ[I₁] M × M →ₛₗ[I₂] N}
    (hAA : ∀ x y, C (x, -x) (y, -y) = C' (x, -x) (y, -y))
    (hAD : ∀ x y, C (x, -x) (y, y) = C' (x, -x) (y, y))
    (hDA : ∀ x y, C (x, x) (y, -y) = C' (x, x) (y, -y))
    (hDD : ∀ x y, C (x, x) (y, y) = C' (x, x) (y, y)) : C = C' :=
  linearMap_ext_antidiag_diag (fun x ↦ linearMap_ext_antidiag_diag (hAA x) (hAD x))
    fun x ↦ linearMap_ext_antidiag_diag (hDA x) (hDD x)

end TauCeti

namespace LinearMap

open TauCeti

variable {R M N : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {I₁ I₂ : R →+* R} (B : M →ₛₗ[I₁] M →ₛₗ[I₂] N)

/-- In polarization coordinates the doubled form is twice the hyperbolic pairing of the
antidiagonal with the diagonal. -/
theorem doubled_doublingPolarizationEquiv (p q : M × M) :
    B.doubled (doublingPolarizationEquiv R M p) (doublingPolarizationEquiv R M q) =
      2 • (B p.1 q.2 + B p.2 q.1) := by
  simp only [doubled_apply, doublingPolarizationEquiv_apply, map_add, map_sub,
    LinearMap.add_apply, LinearMap.sub_apply]
  abel

end LinearMap
