/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Density.Basic
public import TauCeti.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Densities on a product of vector spaces

Let `V` and `W` be finite-dimensional real vector spaces, of dimensions `m` and `n`. A
top-dimensional density `μ` on `V` and a top-dimensional density `ν` on `W` have a product
`μ.prod ν`, a top-dimensional density on `V × W` (`TauCeti.Density.prod`). It is characterized
by its values on the tuples that list `m` vectors of `V × {0}` and then `n` vectors of `{0} × W`:

`μ.prod ν ((v₁, 0), …, (v_m, 0), (0, w₁), …, (0, w_n)) = μ (v₁, …, v_m) * ν (w₁, …, w_n)`

(`TauCeti.Density.prod_apply_sumElim`), in whatever order the `m + n` vectors are listed, since
a density does not see the order of its arguments. On the product `(b.prod c)` of bases of `V`
and `W` it takes the value `μ b * ν c` (`TauCeti.Density.prod_apply_reindex_prod`). This is the
change of variables behind Fubini's theorem: the parallelepiped spanned by `(vᵢ, 0)` and
`(0, wⱼ)` is the product of those spanned by the `vᵢ` and by the `wⱼ`.

The product is bilinear, and since the three spaces of densities are lines, it identifies the
tensor product of the density lines of `V` and `W` with the density line of `V × W`
(`TauCeti.Density.tensorProductEquiv`):

`Density V (finrank ℝ V) ⊗[ℝ] Density W (finrank ℝ W) ≃ₗ[ℝ] Density (V × W) (finrank ℝ (V × W))`,

where `finrank ℝ (V × W) = m + n` holds propositionally (`Module.finrank_prod`), not by definition.

Fibrewise over a product of manifolds, this identifies the density line of `M × N` with the
external tensor product of the density lines of `M` and `N`, which is how a distributional
kernel with coefficients in a bundle of densities on `M × N` splits into its two variables.

## Main definitions

* `TauCeti.Density.prod μ ν`: the product of a density on `V` and a density on `W`, a density on
  `V × W`.
* `TauCeti.Density.tensorProductEquiv`: the linear equivalence
  `Density V (finrank ℝ V) ⊗[ℝ] Density W (finrank ℝ W) ≃ₗ[ℝ] Density (V × W) (finrank ℝ (V × W))`
  sending `μ ⊗ ν` to `μ.prod ν`.

## Main results

* `TauCeti.Density.prod_apply_sumElim`, `TauCeti.Density.prod_apply_reindex_prod`: the values of
  the product on tuples adapted to `V × W`.
* `TauCeti.Density.prod_apply_prodCongr_comp`: its values on the images of tuples under products
  of linear equivalences, such as the frames of a product of vector bundles.
* `Module.Basis.density_prod_density`: the product of the densities with values `s` and `t` on
  bases `b` and `c` is the density with value `s * t` on the product basis.
* `TauCeti.Density.prod_eq_zero_iff`: the product vanishes only when a factor does.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities.
-/

public section

noncomputable section

open Module TensorProduct

namespace TauCeti.Density

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

/-- The product of the standard bases of `V` and `W`, indexed by `Fin (finrank ℝ (V × W))`. -/
private def prodFinBasis : Basis (Fin (finrank ℝ (V × W))) ℝ (V × W) :=
  ((finBasis ℝ V).prod (finBasis ℝ W)).reindex
    (finSumFinEquiv.trans (finCongr (finrank_prod (R := ℝ) (M := V) (M' := W)).symm))

/-- The **product** of a top-dimensional density `μ` on `V` and a top-dimensional density `ν` on
`W`: the density on `V × W` with value `μ v * ν w` on the tuple listing the vectors `(vᵢ, 0)` and
then `(0, wⱼ)` (`TauCeti.Density.prod_apply_sumElim`). -/
def prod (μ : Density V (finrank ℝ V)) (ν : Density W (finrank ℝ W)) :
    Density (V × W) (finrank ℝ (V × W)) :=
  prodFinBasis.density (μ (finBasis ℝ V) * ν (finBasis ℝ W))

/-- **The value of a product of densities.** On the tuple listing the vectors `(vᵢ, 0)` and then
`(0, wⱼ)`, in any order `e`, the product `μ.prod ν` takes the value `μ v * ν w`. -/
theorem prod_apply_sumElim (μ : Density V (finrank ℝ V)) (ν : Density W (finrank ℝ W))
    (e : Fin (finrank ℝ V) ⊕ Fin (finrank ℝ W) ≃ Fin (finrank ℝ (V × W)))
    (v : Fin (finrank ℝ V) → V) (w : Fin (finrank ℝ W) → W) :
    μ.prod ν (Sum.elim (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)) ∘ e.symm) = μ v * ν w := by
  -- The product basis listed in the order `e` is a reordering of `prodFinBasis`.
  have hperm : (((finBasis ℝ V).prod (finBasis ℝ W)).reindex e : Fin (finrank ℝ (V × W)) → V × W) =
      (prodFinBasis : Fin (finrank ℝ (V × W)) → V × W) ∘
        (e.symm.trans (finSumFinEquiv.trans (finCongr finrank_prod.symm))) := by
    funext k
    simp [prodFinBasis, Basis.reindex_apply]
  -- The tuple is the image of that basis under the product of the maps `constr v`, `constr w`.
  have himage : Sum.elim (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)) ∘ e.symm =
      (((finBasis ℝ V).constr ℝ v).prodMap ((finBasis ℝ W).constr ℝ w) : V × W → V × W) ∘
        (((finBasis ℝ V).prod (finBasis ℝ W)).reindex e) := by
    rw [Basis.coe_reindex, ← Function.comp_assoc, Basis.prodMap_constr_comp_prod]
  -- So the product takes the value `|det (constr v)| * |det (constr w)| * μ b * ν c` on it.
  have hvalue : μ.prod ν (Sum.elim (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)) ∘ e.symm) =
      |LinearMap.det ((finBasis ℝ V).constr ℝ v)| * |LinearMap.det ((finBasis ℝ W).constr ℝ w)| *
        (μ (finBasis ℝ V) * ν (finBasis ℝ W)) := by
    rw [himage, comp_apply, hperm, apply_comp_perm _ prodFinBasis, prod,
      Basis.density_apply_self, LinearMap.det_prodMap, abs_mul]
  -- These factors are the values of `μ` on `v` and of `ν` on `w`.
  have hv : μ v = |LinearMap.det ((finBasis ℝ V).constr ℝ v)| * μ (finBasis ℝ V) := by
    rw [← comp_apply]
    exact congrArg μ (funext ((finBasis ℝ V).constr_basis ℝ v)).symm
  have hw : ν w = |LinearMap.det ((finBasis ℝ W).constr ℝ w)| * ν (finBasis ℝ W) := by
    rw [← comp_apply]
    exact congrArg ν (funext ((finBasis ℝ W).constr_basis ℝ w)).symm
  rw [hvalue, hv, hw]
  ring

/-- On the product `b.prod c` of bases of `V` and `W`, listed in any order, the product `μ.prod ν`
takes the value `μ b * ν c`. -/
theorem prod_apply_reindex_prod (μ : Density V (finrank ℝ V)) (ν : Density W (finrank ℝ W))
    (b : Basis (Fin (finrank ℝ V)) ℝ V) (c : Basis (Fin (finrank ℝ W)) ℝ W)
    (e : Fin (finrank ℝ V) ⊕ Fin (finrank ℝ W) ≃ Fin (finrank ℝ (V × W))) :
    μ.prod ν ((b.prod c).reindex e) = μ b * ν c := by
  rw [← prod_apply_sumElim μ ν e b c]
  congr 1
  funext k
  obtain ⟨i | j, rfl⟩ := e.surjective k <;> simp

/-- **The product density on a product frame.** Let `A : V₀ ≃ V` and `B : W₀ ≃ W` be linear
equivalences, for instance inverse charts of two vector bundles, and let `b₀`, `c₀` be bases of
`V₀` and `W₀`. On the image of a tuple `u` of `V₀ × W₀` under `A × B`, the product `μ.prod ν` is
the absolute determinant of `u` in the product basis, times the values of `μ` and `ν` on the
images `A b₀` and `B c₀` of the two bases. -/
theorem prod_apply_prodCongr_comp {V₀ W₀ : Type*} [AddCommGroup V₀] [Module ℝ V₀]
    [AddCommGroup W₀] [Module ℝ W₀] (μ : Density V (finrank ℝ V)) (ν : Density W (finrank ℝ W))
    (A : V₀ ≃ₗ[ℝ] V) (B : W₀ ≃ₗ[ℝ] W) (b₀ : Basis (Fin (finrank ℝ V)) ℝ V₀)
    (c₀ : Basis (Fin (finrank ℝ W)) ℝ W₀)
    (e : Fin (finrank ℝ V) ⊕ Fin (finrank ℝ W) ≃ Fin (finrank ℝ (V × W)))
    (u : Fin (finrank ℝ (V × W)) → V₀ × W₀) :
    μ.prod ν ((A.prodCongr B : V₀ × W₀ → V × W) ∘ u) =
      |((b₀.prod c₀).reindex e).det u| * (μ (A ∘ b₀) * ν (B ∘ c₀)) := by
  -- Evaluate on the image of the product basis of `V₀ × W₀`, a basis of `V × W`.
  set β := ((b₀.prod c₀).reindex e).map (A.prodCongr B)
  have hβ : (β : Fin (finrank ℝ (V × W)) → V × W) =
      Sum.elim (fun i ↦ ((A ∘ b₀) i, 0)) (fun j ↦ (0, (B ∘ c₀) j)) ∘ e.symm := by
    funext k
    obtain ⟨i | j, rfl⟩ := e.surjective k <;> simp [β]
  have hu : ((A.prodCongr B).symm : V × W → V₀ × W₀) ∘ (A.prodCongr B) ∘ u = u :=
    funext fun k ↦ (A.prodCongr B).symm_apply_apply (u k)
  rw [apply_eq_abs_det_mul _ β, Basis.det_map, hu, hβ, prod_apply_sumElim]

/-- The tensor product of the density lines of `V` and `W` is the density line of `V × W`, the
pure tensor `μ ⊗ ν` corresponding to the product density `μ.prod ν`
(`TauCeti.Density.tensorProductEquiv_tmul`). -/
def tensorProductEquiv :
    Density V (finrank ℝ V) ⊗[ℝ] Density W (finrank ℝ W) ≃ₗ[ℝ]
      Density (V × W) (finrank ℝ (V × W)) :=
  (TensorProduct.congr (finBasis ℝ V).densityEquiv (finBasis ℝ W).densityEquiv ≪≫ₗ
    TensorProduct.lid ℝ ℝ) ≪≫ₗ prodFinBasis.densityEquiv.symm

@[simp]
theorem tensorProductEquiv_tmul (μ : Density V (finrank ℝ V)) (ν : Density W (finrank ℝ W)) :
    tensorProductEquiv (μ ⊗ₜ ν) = μ.prod ν := by
  simp [tensorProductEquiv, prod, smul_eq_mul]

@[simp]
theorem tensorProductEquiv_symm_prod (μ : Density V (finrank ℝ V))
    (ν : Density W (finrank ℝ W)) : tensorProductEquiv.symm (μ.prod ν) = μ ⊗ₜ ν := by
  rw [← tensorProductEquiv_tmul, LinearEquiv.symm_apply_apply]

@[simp]
theorem add_prod (μ μ' : Density V (finrank ℝ V)) (ν : Density W (finrank ℝ W)) :
    (μ + μ').prod ν = μ.prod ν + μ'.prod ν := by
  simp only [← tensorProductEquiv_tmul, add_tmul, map_add]

@[simp]
theorem prod_add (μ : Density V (finrank ℝ V)) (ν ν' : Density W (finrank ℝ W)) :
    μ.prod (ν + ν') = μ.prod ν + μ.prod ν' := by
  simp only [← tensorProductEquiv_tmul, tmul_add, map_add]

@[simp]
theorem smul_prod (a : ℝ) (μ : Density V (finrank ℝ V)) (ν : Density W (finrank ℝ W)) :
    (a • μ).prod ν = a • μ.prod ν := by
  rw [← tensorProductEquiv_tmul, ← tensorProductEquiv_tmul, ← map_smul, smul_tmul']

@[simp]
theorem prod_smul (a : ℝ) (μ : Density V (finrank ℝ V)) (ν : Density W (finrank ℝ W)) :
    μ.prod (a • ν) = a • μ.prod ν := by
  rw [← tensorProductEquiv_tmul, ← tensorProductEquiv_tmul, ← map_smul, tmul_smul]

@[simp]
theorem zero_prod (ν : Density W (finrank ℝ W)) : (0 : Density V (finrank ℝ V)).prod ν = 0 := by
  simp only [← tensorProductEquiv_tmul, zero_tmul, map_zero]

@[simp]
theorem prod_zero (μ : Density V (finrank ℝ V)) : μ.prod (0 : Density W (finrank ℝ W)) = 0 := by
  simp only [← tensorProductEquiv_tmul, tmul_zero, map_zero]

/-- The product of two densities vanishes only when one of them does. -/
@[simp]
theorem prod_eq_zero_iff {μ : Density V (finrank ℝ V)} {ν : Density W (finrank ℝ W)} :
    μ.prod ν = 0 ↔ μ = 0 ∨ ν = 0 := by
  refine ⟨fun h ↦ ?_, by rintro (rfl | rfl) <;> simp⟩
  have h' := congrArg (· prodFinBasis) h
  simp only [prod, Basis.density_apply_self, zero_apply, mul_eq_zero,
    apply_basis_eq_zero_iff] at h'
  exact h'

end TauCeti.Density

namespace Module.Basis

open TauCeti

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

/-- The product of the densities with values `s` on `b` and `t` on `c` is the density with value
`s * t` on the product basis. -/
theorem density_prod_density (b : Basis (Fin (finrank ℝ V)) ℝ V) (c : Basis (Fin (finrank ℝ W)) ℝ W)
    (e : Fin (finrank ℝ V) ⊕ Fin (finrank ℝ W) ≃ Fin (finrank ℝ (V × W))) (s t : ℝ) :
    (b.density s).prod (c.density t) = ((b.prod c).reindex e).density (s * t) := by
  apply ((b.prod c).reindex e).density_ext
  rw [Density.prod_apply_reindex_prod, density_apply_self, density_apply_self, density_apply_self]

end Module.Basis
