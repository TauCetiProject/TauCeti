/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule
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

Applying a linear map `f : M →ₗ[R] N` to every factor commutes with permuting the factors, so it
restricts to a linear map `TensorPower.symmetricTensorsMap n f` between the symmetric tensors; this
is functorial in `f` and sends the diagonal tensor `v ⊗ ⋯ ⊗ v` to `f v ⊗ ⋯ ⊗ f v`. In degrees `0`
and `1` every tensor is symmetric: the degree-zero map is the identity of `R` (for every `f`,
including `f = 0`) and the degree-one map is `f` itself, while in every positive degree the zero
map induces the zero map.

## Main declarations

* `TensorPower.symmetricTensors R M n`: the submodule of symmetric tensors, with membership
  criterion `TensorPower.mem_symmetricTensors`.
* `TensorPower.tprod_const_mem_symmetricTensors`: the tensor `m ⊗ ⋯ ⊗ m` is symmetric.
* `TensorPower.mem_symmetricTensors_iff_repr`: symmetric tensors are those whose coordinates in a
  product basis are invariant under permutations of the words.
* `TensorPower.symmetricTensors_eq_top_of_le_one`: in degrees `0` and `1` every tensor is
  symmetric.
* `TensorPower.symmetricTensorsMap n f`: the map induced on symmetric tensors by a linear map `f`,
  with `TensorPower.symmetricTensorsMap_id` and `TensorPower.symmetricTensorsMap_comp`.
* `TensorPower.symmetricTensorsMap_zero`: in every positive degree the zero map induces the zero
  map. In degrees `0` and `1`, `TensorPower.coe_symmetricTensorsMap_apply` reduces the induced map
  to the tensor-power map, which `TensorPower.algebraMap₀_symm_map` and
  `TauCeti.TensorPower.oneEquiv_map` identify with the identity of `R` and with `f`.

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

variable (R M) in
/-- In degrees `0` and `1` there is only the identity permutation, so every tensor is
symmetric. -/
theorem symmetricTensors_eq_top_of_le_one (hn : n ≤ 1) : symmetricTensors R M n = ⊤ := by
  have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
  refine eq_top_iff.mpr fun t _ ↦ mem_symmetricTensors.mpr fun σ ↦ ?_
  rw [Subsingleton.elim σ (Equiv.refl _), reindex_refl, LinearEquiv.refl_apply]

/-! ### Functoriality -/

variable {N P : Type*} [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- Applying a linear map to every factor of a symmetric tensor gives a symmetric tensor, since it
commutes with permuting the factors. -/
theorem map_mem_symmetricTensors (f : M →ₗ[R] N) {t : ⨂[R]^n M}
    (ht : t ∈ symmetricTensors R M n) :
    PiTensorProduct.map (fun _ ↦ f) t ∈ symmetricTensors R N n := by
  rw [mem_symmetricTensors] at ht ⊢
  intro σ
  rw [← map_reindex (fun _ : Fin n ↦ f) σ t, ht σ]

variable (n) in
/-- The linear map between the symmetric tensors of degree `n` induced by a linear map `f`, which
applies `f` to every factor. -/
def symmetricTensorsMap (f : M →ₗ[R] N) :
    symmetricTensors R M n →ₗ[R] symmetricTensors R N n :=
  (PiTensorProduct.map fun _ ↦ f).restrict fun _ ↦ map_mem_symmetricTensors f

/-- The induced map applies `f` to every factor. -/
@[simp]
theorem coe_symmetricTensorsMap_apply (f : M →ₗ[R] N) (t : symmetricTensors R M n) :
    (symmetricTensorsMap n f t : ⨂[R]^n N) = PiTensorProduct.map (fun _ ↦ f) t :=
  (rfl)

/-- The induced map sends the diagonal tensor `v ⊗ ⋯ ⊗ v` to `f v ⊗ ⋯ ⊗ f v`. -/
@[simp]
theorem symmetricTensorsMap_mk_tprod_const (f : M →ₗ[R] N) (v : M) :
    symmetricTensorsMap n f ⟨tprod R fun _ ↦ v, tprod_const_mem_symmetricTensors v⟩ =
      ⟨tprod R fun _ ↦ f v, tprod_const_mem_symmetricTensors (f v)⟩ :=
  Subtype.ext <| by simp

/-- The identity map induces the identity on symmetric tensors. -/
@[simp]
theorem symmetricTensorsMap_id :
    symmetricTensorsMap n (LinearMap.id : M →ₗ[R] M) = LinearMap.id :=
  LinearMap.ext fun t ↦ Subtype.ext <| by simp [PiTensorProduct.map_id]

/-- The map induced by a composite is the composite of the induced maps. -/
@[simp]
theorem symmetricTensorsMap_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    symmetricTensorsMap n (g ∘ₗ f) = symmetricTensorsMap n g ∘ₗ symmetricTensorsMap n f := by
  simp only [symmetricTensorsMap, PiTensorProduct.map_comp]
  exact LinearMap.restrict_comp _ _

/-- In every positive degree the zero map induces the zero map. -/
@[simp]
theorem symmetricTensorsMap_zero (hn : n ≠ 0) :
    symmetricTensorsMap n (0 : M →ₗ[R] N) = 0 := by
  obtain ⟨k⟩ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  refine LinearMap.ext fun t ↦ Subtype.ext ?_
  simp [TauCeti.PiTensorProduct.map_eq_zero_of_eq_zero (fun _ : Fin n ↦ (0 : M →ₗ[R] N)) (k := k)
    rfl]

end TensorPower
