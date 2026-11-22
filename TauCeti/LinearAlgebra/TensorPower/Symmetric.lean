/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import TauCeti.LinearAlgebra.PiTensorProduct.Basis.Basic
public import TauCeti.LinearAlgebra.TensorPower.Basic

/-!
# Symmetric tensors

For a module `M` over a commutative semiring `R` and `n : ℕ`, the symmetric tensors of degree `n`
are the tensors in `⨂[R]^n M` fixed by every permutation of the `n` factors. They form the
submodule `TensorPower.symmetricTensors R M n`, the intersection over `σ : Equiv.Perm (Fin n)` of
the fixed submodules of the reindexing equivalences; over a ring this is the intersection of the
kernels of `reindex σ - id`.

These are the invariants of the symmetric group acting on `⨂[R]^n M`, not the coinvariants: the
latter are Mathlib's symmetric power `Sym[R]^n M`, a quotient of `⨂[R]^n M`. The two differ
integrally: for `M = ℤ e ⊕ ℤ f`, the symmetric tensors of degree `2` are spanned by `e ⊗ e`,
`e ⊗ f + f ⊗ e` and `f ⊗ f`, whose images in `Sym[ℤ]^2 M` do not span the class of `e ⊗ f`.
For the binary tensor product `M ⊗[R] M`, the tensors fixed by the flip are
`TauCeti.symmetricTensors`.

For a basis `b` of `M`, the coordinates of a tensor in the product basis `b ⊗ ⋯ ⊗ b` are indexed
by words `w : Fin n → κ`, and a tensor is symmetric exactly when its coordinates are invariant under
reindexing the words (`TensorPower.mem_symmetricTensors_iff_repr`). This rests on
`Basis.piTensorProduct_repr_reindex`: reindexing the factors of a tensor reindexes its coordinates.
In particular the pure tensor `b (w 0) ⊗ ⋯ ⊗ b (w (n - 1))` is symmetric only when the word `w` is
constant, so over a nontrivial ring `e₀ ⊗ e₁` is not symmetric.

In degrees zero and one there is no nontrivial permutation, so every tensor is symmetric, and the
symmetric tensors are identified with the scalars and with `M` respectively.

A linear map `f : M → N` induces `TensorPower.mapSymmetricTensors f n`, applying `f` to every
factor. This is functorial, sends `m ⊗ ⋯ ⊗ m` to `f m ⊗ ⋯ ⊗ f m`, and is homogeneous of degree `n`
in `f`: in degree zero every `f` induces the identity of the scalars, while in positive degree the
zero map induces zero.

## Main declarations

* `TensorPower.symmetricTensors R M n`: the submodule of symmetric tensors, with membership
  criterion `TensorPower.mem_symmetricTensors`.
* `TensorPower.tprod_const_mem_symmetricTensors`: the tensor `m ⊗ ⋯ ⊗ m` is symmetric.
* `TensorPower.mem_symmetricTensors_iff_repr`: symmetric tensors are those whose coordinates in a
  product basis are invariant under permutations of the words.
* `TensorPower.tprod_basis_mem_symmetricTensors_iff`: a pure tensor of basis vectors is symmetric
  exactly when all its letters agree.
* `TensorPower.symmetricTensors_eq_top_of_le_one`, `TensorPower.symmetricTensorsZeroEquiv`,
  `TensorPower.symmetricTensorsOneEquiv`: the symmetric tensors of degree zero and one.
* `TensorPower.mapSymmetricTensors f n`: the map induced by a linear map `f`, with
  `TensorPower.mapSymmetricTensors_id`, `TensorPower.mapSymmetricTensors_comp` and
  `TensorPower.mapSymmetricTensors_smul`.

## References

* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963), III §5][Roby-1963]
-/

public section

open PiTensorProduct Module
open scoped TensorProduct

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace TensorPower

variable (R M) in
/-- The symmetric tensors of degree `n`: the tensors in `⨂[R]^n M` fixed by every permutation of
the factors. -/
def symmetricTensors (n : ℕ) : Submodule R (⨂[R]^n M) :=
  ⨅ σ : Equiv.Perm (Fin n), (reindex R (fun _ ↦ M) σ).toLinearMap.fixedSubmodule

variable {n : ℕ}

/-- A tensor is symmetric exactly when it is fixed by every permutation of the factors. -/
@[simp]
theorem mem_symmetricTensors {t : ⨂[R]^n M} :
    t ∈ symmetricTensors R M n ↔ ∀ σ : Equiv.Perm (Fin n), reindex R (fun _ ↦ M) σ t = t := by
  simp [symmetricTensors, LinearMap.mem_fixedSubmodule_iff]

/-- The tensor `m ⊗ ⋯ ⊗ m` is symmetric. -/
theorem tprod_const_mem_symmetricTensors (m : M) :
    (tprod R fun _ : Fin n ↦ m) ∈ symmetricTensors R M n :=
  mem_symmetricTensors.mpr fun σ ↦ by rw [reindex_tprod]

/-- A tensor is symmetric exactly when its coordinates in the product basis of a basis `b` of `M`
are invariant under reindexing the words by permutations. -/
theorem mem_symmetricTensors_iff_repr {κ : Type*} (b : Basis κ R M) {t : ⨂[R]^n M} :
    t ∈ symmetricTensors R M n ↔ ∀ (σ : Equiv.Perm (Fin n)) (w : Fin n → κ),
      (Basis.piTensorProduct fun _ ↦ b).repr t (w ∘ σ) =
        (Basis.piTensorProduct fun _ ↦ b).repr t w := by
  rw [mem_symmetricTensors]
  refine ⟨fun h σ w ↦ ?_, fun h σ ↦ (Basis.piTensorProduct fun _ ↦ b).repr.injective ?_⟩
  · rw [← Basis.piTensorProduct_repr_reindex, h σ]
  · ext w
    rw [Basis.piTensorProduct_repr_reindex, h]

/-- A pure tensor of basis vectors is symmetric exactly when all of its letters agree. -/
theorem tprod_basis_mem_symmetricTensors_iff [Nontrivial R] {κ : Type*} (b : Basis κ R M)
    (w : Fin n → κ) :
    (tprod R fun i ↦ b (w i)) ∈ symmetricTensors R M n ↔ ∀ i j, w i = w j := by
  refine ⟨fun h i j ↦ ?_, fun h ↦ mem_symmetricTensors.mpr fun σ ↦ ?_⟩
  · have hw := (mem_symmetricTensors_iff_repr b).mp h (Equiv.swap i j) w
    by_contra hij
    simp only [Basis.piTensorProduct_repr_tprod_apply, Basis.repr_self, Function.comp_apply,
      Finsupp.single_eq_same, Finset.prod_const_one] at hw
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hij])] at hw
    exact zero_ne_one hw
  · rw [reindex_tprod]
    exact congrArg (tprod R) (funext fun i ↦ congrArg b (h _ _))

/-- In degrees zero and one every tensor is symmetric, since there is no nontrivial permutation
of the factors. -/
@[simp]
theorem symmetricTensors_eq_top_of_le_one (hn : n ≤ 1) : symmetricTensors R M n = ⊤ := by
  have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
  refine eq_top_iff.mpr fun t _ ↦ mem_symmetricTensors.mpr fun σ ↦ ?_
  rw [Subsingleton.elim σ (Equiv.refl _), reindex_refl, LinearEquiv.refl_apply]

variable (R M) in
/-- The symmetric tensors of degree zero are the scalars: every tensor of degree zero is
symmetric, and `⨂[R]^0 M` is identified with `R` by `TensorPower.algebraMap₀`. -/
def symmetricTensorsZeroEquiv : symmetricTensors R M 0 ≃ₗ[R] R :=
  (LinearEquiv.ofTop _ (symmetricTensors_eq_top_of_le_one zero_le_one)).trans algebraMap₀.symm

/-- The scalar of a symmetric tensor of degree zero is its scalar as a tensor of degree zero. -/
theorem symmetricTensorsZeroEquiv_apply (t : symmetricTensors R M 0) :
    symmetricTensorsZeroEquiv R M t = algebraMap₀.symm (t : ⨂[R]^0 M) :=
  (rfl)

/-- The symmetric tensor of degree zero with scalar `r` is the tensor `algebraMap₀ r`. -/
@[simp]
theorem coe_symmetricTensorsZeroEquiv_symm_apply (r : R) :
    ((symmetricTensorsZeroEquiv R M).symm r : ⨂[R]^0 M) = algebraMap₀ r :=
  (rfl)

variable (R M) in
/-- The symmetric tensors of degree one are the vectors: every tensor of degree one is
symmetric, and `⨂[R]^1 M` is identified with `M` by `TauCeti.TensorPower.oneEquiv`. -/
noncomputable def symmetricTensorsOneEquiv : symmetricTensors R M 1 ≃ₗ[R] M :=
  (LinearEquiv.ofTop _ (symmetricTensors_eq_top_of_le_one le_rfl)).trans
    (TauCeti.TensorPower.oneEquiv R M)

/-- The vector of a symmetric tensor of degree one is its letter as a tensor of degree one. -/
theorem symmetricTensorsOneEquiv_apply (t : symmetricTensors R M 1) :
    symmetricTensorsOneEquiv R M t = TauCeti.TensorPower.oneEquiv R M (t : ⨂[R]^1 M) :=
  (rfl)

/-- The symmetric tensor of degree one attached to a vector is the one-letter pure tensor. -/
@[simp]
theorem coe_symmetricTensorsOneEquiv_symm_apply (m : M) :
    ((symmetricTensorsOneEquiv R M).symm m : ⨂[R]^1 M) = tprod R fun _ ↦ m :=
  TauCeti.TensorPower.oneEquiv_symm_apply R M m

/-! ### Functoriality -/

section map

variable {N P : Type*} [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- Applying a linear map to every tensor factor sends symmetric tensors to symmetric tensors. -/
theorem map_mem_symmetricTensors (f : M →ₗ[R] N) {t : ⨂[R]^n M}
    (ht : t ∈ symmetricTensors R M n) :
    PiTensorProduct.map (fun _ ↦ f) t ∈ symmetricTensors R N n :=
  mem_symmetricTensors.mpr fun σ ↦ by
    rw [← map_reindex (fun _ ↦ f) σ t, mem_symmetricTensors.mp ht σ]

/-- A linear map `f : M → N` induces the linear map between symmetric tensors of degree `n` that
applies `f` to every tensor factor. -/
def mapSymmetricTensors (f : M →ₗ[R] N) (n : ℕ) :
    symmetricTensors R M n →ₗ[R] symmetricTensors R N n :=
  (PiTensorProduct.map fun _ ↦ f).restrict fun _ ↦ map_mem_symmetricTensors f

/-- The map on symmetric tensors is the restriction of the tensor-power map. -/
@[simp]
theorem coe_mapSymmetricTensors_apply (f : M →ₗ[R] N) (t : symmetricTensors R M n) :
    (mapSymmetricTensors f n t : ⨂[R]^n N) = PiTensorProduct.map (fun _ ↦ f) (t : ⨂[R]^n M) :=
  LinearMap.coe_restrict_apply _ t

/-- The map on symmetric tensors sends the diagonal tensor `m ⊗ ⋯ ⊗ m` to `f m ⊗ ⋯ ⊗ f m`. -/
@[simp]
theorem mapSymmetricTensors_tprod_const (f : M →ₗ[R] N) (m : M) :
    mapSymmetricTensors f n ⟨tprod R fun _ ↦ m, tprod_const_mem_symmetricTensors m⟩ =
      ⟨tprod R fun _ ↦ f m, tprod_const_mem_symmetricTensors (f m)⟩ := by
  ext
  simp

/-- The identity linear map induces the identity on symmetric tensors. -/
@[simp]
theorem mapSymmetricTensors_id :
    mapSymmetricTensors (LinearMap.id : M →ₗ[R] M) n = LinearMap.id := by
  ext t
  simp [PiTensorProduct.map_id]

/-- Maps on symmetric tensors respect composition. -/
@[simp]
theorem mapSymmetricTensors_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) (n : ℕ) :
    (mapSymmetricTensors g n).comp (mapSymmetricTensors f n) =
      mapSymmetricTensors (g.comp f) n := by
  ext t
  simp [PiTensorProduct.map_comp]

/-- Scaling a linear map by `c` scales the induced map on symmetric tensors of degree `n` by
`c ^ n`. -/
theorem mapSymmetricTensors_smul (c : R) (f : M →ₗ[R] N) (n : ℕ) :
    mapSymmetricTensors (c • f) n = c ^ n • mapSymmetricTensors f n := by
  ext t
  have h := (mapMultilinear R (fun _ : Fin n ↦ M) fun _ ↦ N).map_smul_univ (fun _ ↦ c)
    fun _ ↦ f
  simp only [mapMultilinear_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  simp [h]

/-- The zero map induces zero on symmetric tensors of every positive degree. In degree zero it
induces the identity instead (`symmetricTensorsZeroEquiv_mapSymmetricTensors`). -/
theorem mapSymmetricTensors_zero (hn : n ≠ 0) :
    mapSymmetricTensors (0 : M →ₗ[R] N) n = 0 := by
  rw [← zero_smul R (0 : M →ₗ[R] N), mapSymmetricTensors_smul, zero_pow hn, zero_smul]

/-- In degree zero every linear map induces the identity of the scalars. -/
@[simp]
theorem symmetricTensorsZeroEquiv_mapSymmetricTensors (f : M →ₗ[R] N)
    (t : symmetricTensors R M 0) :
    symmetricTensorsZeroEquiv R N (mapSymmetricTensors f 0 t) =
      symmetricTensorsZeroEquiv R M t := by
  have h : (algebraMap₀ (M := N)).symm.toLinearMap ∘ₗ PiTensorProduct.map (fun _ ↦ f) =
      (algebraMap₀ (M := M)).symm.toLinearMap := by
    ext
    simp [algebraMap₀]
  simpa [symmetricTensorsZeroEquiv_apply] using congr($h (t : ⨂[R]^0 M))

/-- In degree one the induced map is `f`, through the identification with the vectors. -/
@[simp]
theorem symmetricTensorsOneEquiv_mapSymmetricTensors (f : M →ₗ[R] N)
    (t : symmetricTensors R M 1) :
    symmetricTensorsOneEquiv R N (mapSymmetricTensors f 1 t) =
      f (symmetricTensorsOneEquiv R M t) := by
  have h : (TauCeti.TensorPower.oneEquiv R N).toLinearMap ∘ₗ PiTensorProduct.map (fun _ ↦ f) =
      f ∘ₗ (TauCeti.TensorPower.oneEquiv R M).toLinearMap := by
    ext
    simp
  simpa [symmetricTensorsOneEquiv_apply] using congr($h (t : ⨂[R]^1 M))

end map

end TensorPower
