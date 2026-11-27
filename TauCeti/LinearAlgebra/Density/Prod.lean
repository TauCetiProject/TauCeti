/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Density.Basic
public import TauCeti.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.Basis.Fin

/-!
# Densities on products of vector spaces

A density `μ` on a real vector space `V` with a basis of `m` vectors and a density `ν` on `W`
with a basis of `n` vectors have a **product** `μ.prod ν`, a density on `V × W` in degree
`m + n`. It is determined by its value on the ordered product `(b × c)` of bases `b` of `V` and
`c` of `W`, the basis `(b 0, 0), …, (b (m - 1), 0), (0, c 0), …, (0, c (n - 1))`:

`(μ.prod ν) (b × c) = μ b * ν c`

(`TauCeti.Density.prod_apply_reindex_prod`), and more generally
`(μ.prod ν) (v × w) = μ v * ν w` for all tuples `v` of `V` and `w` of `W`
(`TauCeti.Density.prod_apply_append`). The right side does not depend on the choice of the bases,
because a change of product bases has the product determinant (`Module.Basis.det_prod`). The
product is bilinear (`TauCeti.Density.prodₗ`), and on top-dimensional densities it identifies the
tensor product of the density lines of `V` and `W` with the density line of `V × W`
(`TauCeti.Density.prodTensorEquiv`). This is the linear algebra behind the identification of the
density bundle of a product manifold with the external tensor product of the density bundles of
its factors.

Densities are transported along linear equivalences by `TauCeti.Density.map`, the analogue of
`Orientation.map`, and the product is natural for this transport
(`TauCeti.Density.map_prod_map`).

Following `LinearMap.det`, the product is defined to be `0` when `V` or `W` has no basis of the
prescribed size or the degrees do not add up; then there is no top-dimensional density to
multiply.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16,
  Densities.
-/

public section

noncomputable section

open Module
open scoped TensorProduct

namespace TauCeti.Density

variable {V V' W W' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']
  [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W'] {m n k : ℕ}

/-! ### Transport along linear equivalences -/

/-- The density `v ↦ μ (e⁻¹ ∘ v)` on `V'`, the underlying function of `TauCeti.Density.map`. -/
private def mapAux (e : V ≃ₗ[ℝ] V') (μ : Density V m) : Density V' m :=
  ⟨fun v ↦ μ (e.symm ∘ v), fun T v ↦ by
    -- `e⁻¹ ∘ T = (e⁻¹ T e) ∘ e⁻¹`, and conjugation does not change the determinant.
    have h : ⇑e.symm ∘ (⇑T ∘ v) =
        ⇑((e.symm : V' →ₗ[ℝ] V) ∘ₗ T ∘ₗ (e : V →ₗ[ℝ] V')) ∘ (⇑e.symm ∘ v) := by
      funext i
      simp
    rw [h, comp_apply, ← LinearMap.det_conj T e.symm, LinearEquiv.symm_symm]⟩

/-- The transport `e_* μ` of a density along a linear equivalence `e : V ≃ V'`, a density on `V'`
with `(e_* μ) v = μ (e⁻¹ ∘ v)`. -/
def map (e : V ≃ₗ[ℝ] V') : Density V m ≃ₗ[ℝ] Density V' m where
  toFun := mapAux e
  invFun := mapAux e.symm
  left_inv μ := by
    ext v
    simp [mapAux, Function.comp_def]
  right_inv μ := by
    ext v
    simp [mapAux, Function.comp_def]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem map_apply (e : V ≃ₗ[ℝ] V') (μ : Density V m) (v : Fin m → V') :
    map e μ v = μ (e.symm ∘ v) :=
  (rfl)

@[simp]
theorem map_symm (e : V ≃ₗ[ℝ] V') : (map e).symm = (map e.symm : Density V' m ≃ₗ[ℝ] _) :=
  (rfl)

/-- Transport along a linear equivalence evaluates a density on the transported basis. -/
theorem map_apply_basis_map (e : V ≃ₗ[ℝ] V') (μ : Density V m) (b : Basis (Fin m) ℝ V) :
    map e μ (b.map e) = μ b := by
  rw [map_apply]
  congr 1
  funext i
  simp

/-! ### The product of two densities -/

open Classical in
/-- The **product** of a density `μ` on `V` and a density `ν` on `W`: the density on `V × W` in
degree `k = m + n` whose value on the ordered product of bases `b` of `V` and `c` of `W` is
`μ b * ν c` (`TauCeti.Density.prod_apply_reindex_prod`). It is defined through one choice of such
bases, and does not depend on it (`TauCeti.Density.prod_eq_density`). It is `0` when `V` or `W`
has no basis of the prescribed size, or when `m + n ≠ k`. -/
def prod (μ : Density V m) (ν : Density W n) : Density (V × W) k :=
  if h : Nonempty (Basis (Fin m) ℝ V) ∧ Nonempty (Basis (Fin n) ℝ W) ∧ m + n = k then
    ((h.1.some.prod h.2.1.some).reindex (finSumFinEquiv.trans (finCongr h.2.2))).density
      (μ h.1.some * ν h.2.1.some)
  else 0

/-- Changing the factor bases changes the product basis by the product of the two determinants,
so the density with value `μ b * ν c` on the product of `b` and `c` does not depend on `b`
and `c`. -/
private theorem density_reindex_prod_eq (μ : Density V m) (ν : Density W n)
    (b b' : Basis (Fin m) ℝ V) (c c' : Basis (Fin n) ℝ W) (h : m + n = k) :
    ((b.prod c).reindex (finSumFinEquiv.trans (finCongr h))).density (μ b * ν c) =
      ((b'.prod c').reindex (finSumFinEquiv.trans (finCongr h))).density (μ b' * ν c') := by
  set e := finSumFinEquiv.trans (finCongr h)
  apply ((b'.prod c').reindex e).density_ext
  have he : ((b'.prod c').reindex e : Fin k → V × W) ∘ e = b'.prod c' := by
    funext i
    simp
  rw [Basis.density_apply, Basis.density_apply_self, Basis.det_reindex, he, Basis.det_prod,
    μ.apply_eq_abs_det_mul b b', ν.apply_eq_abs_det_mul c c', abs_mul]
  ring

/-- The product of densities is the density with value `μ b * ν c` on the ordered product of any
two bases `b` of `V` and `c` of `W`. -/
theorem prod_eq_density (μ : Density V m) (ν : Density W n) (b : Basis (Fin m) ℝ V)
    (c : Basis (Fin n) ℝ W) (h : m + n = k) :
    μ.prod ν = ((b.prod c).reindex (finSumFinEquiv.trans (finCongr h))).density (μ b * ν c) := by
  have hne : Nonempty (Basis (Fin m) ℝ V) ∧ Nonempty (Basis (Fin n) ℝ W) ∧ m + n = k :=
    ⟨⟨b⟩, ⟨c⟩, h⟩
  rw [prod, dite_eq_left hne]
  exact density_reindex_prod_eq μ ν _ b _ c h

/-- Without bases of the prescribed sizes, or when the degrees do not add up, the product is
`0`. -/
theorem prod_of_not (μ : Density V m) (ν : Density W n)
    (h : ¬(Nonempty (Basis (Fin m) ℝ V) ∧ Nonempty (Basis (Fin n) ℝ W) ∧ m + n = k)) :
    (μ.prod ν : Density (V × W) k) = 0 := by
  rw [prod, dite_eq_right h]

/-- The value of a product density on an arbitrary tuple, through bases of the two factors. -/
theorem prod_apply_eq_abs_det_mul (μ : Density V m) (ν : Density W n) (b : Basis (Fin m) ℝ V)
    (c : Basis (Fin n) ℝ W) (h : m + n = k) (u : Fin k → V × W) :
    μ.prod ν u = |((b.prod c).reindex (finSumFinEquiv.trans (finCongr h))).det u| *
      (μ b * ν c) := by
  rw [prod_eq_density μ ν b c h, Basis.density_apply]

/-- **The product density on product bases.** On the ordered product of bases `b` of `V` and `c`
of `W`, the product density takes the value `μ b * ν c`. -/
theorem prod_apply_reindex_prod (μ : Density V m) (ν : Density W n) (b : Basis (Fin m) ℝ V)
    (c : Basis (Fin n) ℝ W) (h : m + n = k) :
    μ.prod ν ((b.prod c).reindex (finSumFinEquiv.trans (finCongr h))) = μ b * ν c := by
  rw [prod_eq_density μ ν b c h, Basis.density_apply_self]

/-- **The product density on product tuples.** For tuples `v` of `V` and `w` of `W`, the product
density takes the value `μ v * ν w` on `(v 0, 0), …, (v (m - 1), 0), (0, w 0), …, (0, w (n - 1))`,
indexed by `Fin k` for `m + n = k`. -/
theorem prod_apply_append [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] (μ : Density V m)
    (ν : Density W n) (hm : finrank ℝ V = m) (hn : finrank ℝ W = n) (h : m + n = k)
    (v : Fin m → V) (w : Fin n → W) :
    μ.prod ν (fun r ↦ Fin.append (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)) (Fin.cast h.symm r)) =
      μ v * ν w := by
  let b := finBasisOfFinrankEq ℝ V hm
  let c := finBasisOfFinrankEq ℝ W hn
  -- The tuple is the image of the product basis under the product of the linear maps sending
  -- `b` to `v` and `c` to `w`.
  have hT : (fun r ↦ Fin.append (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)) (Fin.cast h.symm r)) =
      ⇑((b.constr ℝ v).prodMap (c.constr ℝ w)) ∘
        ⇑((b.prod c).reindex (finSumFinEquiv.trans (finCongr h))) := by
    rw [Basis.coe_prod_reindex_finSumFinEquiv_trans_finCongr]
    funext r
    obtain ⟨s, rfl⟩ : ∃ s, r = Fin.cast h s := ⟨Fin.cast h.symm r, by simp⟩
    induction s using Fin.addCases <;> simp
  have hv : v = ⇑(b.constr ℝ v) ∘ ⇑b := by
    funext i
    simp
  have hw : w = ⇑(c.constr ℝ w) ∘ ⇑c := by
    funext j
    simp
  rw [hT, comp_apply, prod_apply_reindex_prod, LinearMap.det_prodMap, abs_mul, hv, hw,
    comp_apply, comp_apply, ← hv, ← hw]
  ring

/-- The product of densities is natural for transport along linear equivalences of the two
factors. -/
theorem map_prod_map (e : V ≃ₗ[ℝ] V') (f : W ≃ₗ[ℝ] W') (μ : Density V m) (ν : Density W n) :
    (map e μ).prod (map f ν) = (map (e.prodCongr f) (μ.prod ν) : Density (V' × W') k) := by
  by_cases h : Nonempty (Basis (Fin m) ℝ V) ∧ Nonempty (Basis (Fin n) ℝ W) ∧ m + n = k
  · obtain ⟨⟨b⟩, ⟨c⟩, h⟩ := h
    let g := finSumFinEquiv.trans (finCongr h)
    apply (((b.map e).prod (c.map f)).reindex g).density_ext
    have hb : ⇑(e.prodCongr f).symm ∘ ⇑(((b.map e).prod (c.map f)).reindex g) =
        ⇑((b.prod c).reindex g) := by
      funext r
      obtain ⟨i, rfl⟩ := g.surjective r
      cases i <;> simp
    rw [prod_apply_reindex_prod, map_apply_basis_map, map_apply_basis_map, map_apply, hb,
      prod_apply_reindex_prod]
  · rw [prod_of_not _ _ h, map_zero, prod_of_not]
    rintro ⟨⟨b⟩, ⟨c⟩, hk⟩
    exact h ⟨⟨b.map e.symm⟩, ⟨c.map f.symm⟩, hk⟩

/-! ### Bilinearity and the tensor product of density lines -/

theorem add_prod (μ μ' : Density V m) (ν : Density W n) :
    ((μ + μ').prod ν : Density (V × W) k) = μ.prod ν + μ'.prod ν := by
  by_cases h : Nonempty (Basis (Fin m) ℝ V) ∧ Nonempty (Basis (Fin n) ℝ W) ∧ m + n = k
  · obtain ⟨⟨b⟩, ⟨c⟩, h⟩ := h
    apply ((b.prod c).reindex (finSumFinEquiv.trans (finCongr h))).density_ext
    simp only [add_apply, prod_apply_reindex_prod, add_mul]
  · simp [prod_of_not _ _ h]

theorem prod_add (μ : Density V m) (ν ν' : Density W n) :
    (μ.prod (ν + ν') : Density (V × W) k) = μ.prod ν + μ.prod ν' := by
  by_cases h : Nonempty (Basis (Fin m) ℝ V) ∧ Nonempty (Basis (Fin n) ℝ W) ∧ m + n = k
  · obtain ⟨⟨b⟩, ⟨c⟩, h⟩ := h
    apply ((b.prod c).reindex (finSumFinEquiv.trans (finCongr h))).density_ext
    simp only [add_apply, prod_apply_reindex_prod, mul_add]
  · simp [prod_of_not _ _ h]

theorem smul_prod (a : ℝ) (μ : Density V m) (ν : Density W n) :
    ((a • μ).prod ν : Density (V × W) k) = a • μ.prod ν := by
  by_cases h : Nonempty (Basis (Fin m) ℝ V) ∧ Nonempty (Basis (Fin n) ℝ W) ∧ m + n = k
  · obtain ⟨⟨b⟩, ⟨c⟩, h⟩ := h
    apply ((b.prod c).reindex (finSumFinEquiv.trans (finCongr h))).density_ext
    simp only [smul_apply, prod_apply_reindex_prod, smul_eq_mul, mul_assoc]
  · simp [prod_of_not _ _ h]

theorem prod_smul (a : ℝ) (μ : Density V m) (ν : Density W n) :
    (μ.prod (a • ν) : Density (V × W) k) = a • μ.prod ν := by
  by_cases h : Nonempty (Basis (Fin m) ℝ V) ∧ Nonempty (Basis (Fin n) ℝ W) ∧ m + n = k
  · obtain ⟨⟨b⟩, ⟨c⟩, h⟩ := h
    apply ((b.prod c).reindex (finSumFinEquiv.trans (finCongr h))).density_ext
    simp only [smul_apply, prod_apply_reindex_prod, smul_eq_mul]
    ring
  · simp [prod_of_not _ _ h]

variable (V W m n k) in
/-- The product of densities as a bilinear map. -/
def prodₗ : Density V m →ₗ[ℝ] Density W n →ₗ[ℝ] Density (V × W) k :=
  LinearMap.mk₂ ℝ prod add_prod smul_prod prod_add prod_smul

@[simp]
theorem prodₗ_apply (μ : Density V m) (ν : Density W n) : prodₗ V W m n k μ ν = μ.prod ν :=
  (rfl)

/-- **The density line of a product.** For finite-dimensional `V` and `W` of dimensions `m` and
`n` and `m + n = k`, the product of densities is a linear equivalence from the tensor product of
the density lines of `V` and `W` onto the density line of `V × W`, sending `μ ⊗ ν` to
`μ.prod ν` (`TauCeti.Density.prodTensorEquiv_tmul`). -/
def prodTensorEquiv [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] (hm : finrank ℝ V = m)
    (hn : finrank ℝ W = n) (h : m + n = k) :
    Density V m ⊗[ℝ] Density W n ≃ₗ[ℝ] Density (V × W) k :=
  TensorProduct.congr (finBasisOfFinrankEq ℝ V hm).densityEquiv
      (finBasisOfFinrankEq ℝ W hn).densityEquiv ≪≫ₗ TensorProduct.lid ℝ ℝ ≪≫ₗ
    (((finBasisOfFinrankEq ℝ V hm).prod (finBasisOfFinrankEq ℝ W hn)).reindex
      (finSumFinEquiv.trans (finCongr h))).densityEquiv.symm

@[simp]
theorem prodTensorEquiv_tmul [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (hm : finrank ℝ V = m) (hn : finrank ℝ W = n) (h : m + n = k) (μ : Density V m)
    (ν : Density W n) : prodTensorEquiv hm hn h (μ ⊗ₜ ν) = μ.prod ν := by
  rw [prod_eq_density μ ν (finBasisOfFinrankEq ℝ V hm) (finBasisOfFinrankEq ℝ W hn) h]
  simp [prodTensorEquiv]

/-- The inverse of `TauCeti.Density.prodTensorEquiv` on a product of densities. -/
@[simp]
theorem prodTensorEquiv_symm_prod [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (hm : finrank ℝ V = m) (hn : finrank ℝ W = n) (h : m + n = k) (μ : Density V m)
    (ν : Density W n) : (prodTensorEquiv hm hn h).symm (μ.prod ν) = μ ⊗ₜ ν := by
  rw [LinearEquiv.symm_apply_eq, prodTensorEquiv_tmul]

end TauCeti.Density
