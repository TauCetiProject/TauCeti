/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import TauCeti.Algebra.Cellular.CellModule
public import TauCeti.Algebra.Cellular.Matrix

/-!
# Classification of simple modules of a cellular algebra

Over a field `K`, Graham and Lehrer classify the simple left modules of a cellular `K`-algebra `B`
in terms of its cell modules `d.CellModule μ` and the radicals `d.cellRadical μ` of their canonical
bilinear forms `d.cellForm μ`:

* **Scalar endomorphisms (Proposition 2.6):** whenever `d.cellForm μ ≠ 0`, every `B`-linear
  endomorphism of the simple quotient `L(μ) = d.CellModule μ ⧸ d.cellRadical μ` is given by scalar
  multiplication from `K` (`TauCeti.CellularBasis.endCellModuleQuotientAlgEquiv`), without assuming
  that `K` is algebraically closed.
* **Triangularity of homomorphisms (Proposition 3.2):** a nonzero `B`-linear map from
  `d.CellModule ν` into `L(μ)` (with `d.cellForm μ ≠ 0`) forces `ν = μ ∨ ν < μ`
  (`TauCeti.CellularBasis.eq_or_lt_of_linearMap_cellModule_quotient_ne_zero`).
* **Pairwise non-isomorphism (Theorem 3.4(i)):** for cells with nonzero form, `L(μ)` and `L(ν)` are
  `B`-linearly equivalent if and only if `μ = ν`
  (`TauCeti.CellularBasis.nonempty_cellModule_quotient_linearEquiv_iff`), and the hom space between
  distinct simple cell quotients is a subsingleton.
* **Exhaustiveness (Theorem 3.4(ii)):** when `<` on `Λ` is well-founded (in particular for any
  finite cell preorder), every simple `B`-module is `B`-linearly equivalent to `L(μ)` for a unique
  cell `μ` with `d.cellForm μ ≠ 0`
  (`TauCeti.CellularBasis.existsUnique_cellForm_ne_zero_and_nonempty_linearEquiv`), and its
  `B`-endomorphism algebra is isomorphic to `K`
  (`TauCeti.CellularBasis.endAlgEquivOfIsSimpleModule`).

The field hypothesis is essential: `Matrix Unit Unit ℤ` (isomorphic to `ℤ`) has one cell with unit
Gram matrix `(1)` and trivial radical, yet its radical quotient is `ℤ`, which is not a simple
module (`TauCeti.CellularBasis.not_isSimpleModule_matrix_int_cellModule_quotient`).

## Main definitions

* `TauCeti.CellularBasis.cellModuleHom`: the `A`-linear evaluation map `c.CellModule μ →ₗ[A] S`
  sending `c.cellBasis μ s` to `c.basis ⟨μ, s, t₀⟩ • x₀` for `x₀ : S` annihilated by
  `c.lowerSpan μ`.
* `TauCeti.CellularBasis.endCellModuleQuotientAlgEquiv`: the `K`-algebra isomorphism
  `Module.End B (d.CellModule μ ⧸ d.cellRadical μ) ≃ₐ[K] K` for a cell with `d.cellForm μ ≠ 0`.
* `TauCeti.CellularBasis.endAlgEquivOfIsSimpleModule`: the `K`-algebra isomorphism
  `Module.End B S ≃ₐ[K] K` for any simple `B`-module `S` when `[WellFoundedLT Λ]`.

## Main results

* `TauCeti.CellularBasis.cellRep_basis_of_ne`, `TauCeti.CellularBasis.basis_smul_eq_zero_of_ne`:
  basis vectors of a cell `ν ≠ μ` with `¬ μ < ν` annihilate `c.CellModule μ`.
* `TauCeti.CellularBasis.eq_or_lt_of_linearMap_cellModule_quotient_ne_zero`: a nonzero map
  `d.CellModule ν →ₗ[B] d.CellModule μ ⧸ d.cellRadical μ` with `d.cellForm μ ≠ 0` implies
  `ν = μ ∨ ν < μ`.
* `TauCeti.CellularBasis.nonempty_cellModule_quotient_linearEquiv_iff`: simple cell quotients at
  `μ` and `ν` are isomorphic if and only if `μ = ν`.
* `TauCeti.CellularBasis.existsUnique_cellForm_ne_zero_and_nonempty_linearEquiv`: every simple
  `B`-module is isomorphic to a unique `d.CellModule μ ⧸ d.cellRadical μ` with `d.cellForm μ ≠ 0`.
* `TauCeti.CellularBasis.finrank_end_eq_one_of_isSimpleModule`: every simple `B`-module has
  one-dimensional endomorphism algebra over `K`.

## References

* J. J. Graham and G. I. Lehrer, *Cellular algebras*, Invent. Math. 123 (1996), 1–34,
  Proposition 2.6, Proposition 3.2, and Theorem 3.4.
-/

public section

open Module Submodule
open scoped Matrix

namespace TauCeti.CellularBasis

section CommRing

variable {R A Λ : Type*} [CommRing R] [Ring A] [Algebra R A] [Preorder Λ]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] [∀ μ, DecidableEq (M μ)]
  (c : CellularBasis R A M)

/-- The matrix of `c.cellForm μ` in the standard cell basis `c.cellBasis μ` is `c.gramMatrix μ`. -/
@[simp]
theorem toMatrix_cellBasis_cellForm (μ : Λ) :
    LinearMap.BilinForm.toMatrix (c.cellBasis μ) (c.cellForm μ) = c.gramMatrix μ := by
  ext s t
  simp

/-- The cell bilinear form vanishes if and only if its Gram matrix vanishes. -/
theorem cellForm_eq_zero_iff (μ : Λ) : c.cellForm μ = 0 ↔ c.gramMatrix μ = 0 := by
  rw [← (LinearMap.BilinForm.toMatrix (c.cellBasis μ)).map_eq_zero_iff,
    toMatrix_cellBasis_cellForm]

/-- A cell with nonzero bilinear form has a nonzero entry in its Gram matrix. -/
theorem exists_gramMatrix_ne_zero {μ : Λ} (h : c.cellForm μ ≠ 0) :
    ∃ s t : M μ, c.gramMatrix μ s t ≠ 0 := by
  have hg : c.gramMatrix μ ≠ 0 := mt (c.cellForm_eq_zero_iff μ).mpr h
  by_contra! h0
  exact hg (Matrix.ext fun s t ↦ h0 s t)

/-- A cellular basis vector from a cell `ν ≠ μ` not strictly above `μ` acts by zero in the cell
representation at `μ`. -/
theorem cellRep_basis_of_ne {μ ν : Λ} (hne : ν ≠ μ) (hnlt : ¬ μ < ν) (x y : M ν) :
    c.cellRep μ (c.basis ⟨ν, x, y⟩) = 0 := by
  have hsum (r : M ν → R) (u s : M μ) :
      c.basis.repr (∑ v, r v • c.basis ⟨ν, x, v⟩) ⟨μ, u, s⟩ = 0 := by
    simp [hne]
  ext u s
  rw [Matrix.zero_apply, cellRep_apply]
  have hsub := c.basis_mul_sub_sum_mem (c.basis ⟨μ, s, s⟩) ν x y
  have hzero := c.mem_lowerSpan_iff.1 hsub ⟨μ, u, s⟩ hnlt
  rw [map_sub, Finsupp.sub_apply, sub_eq_zero] at hzero
  exact hzero.trans (hsum _ u s)

/-- A cellular basis vector from a cell `ν ≠ μ` not strictly above `μ` annihilates
`c.CellModule μ`. -/
theorem basis_smul_eq_zero_of_ne {μ ν : Λ} (hne : ν ≠ μ) (hnlt : ¬ μ < ν) (x y : M ν)
    (w : c.CellModule μ) : c.basis ⟨ν, x, y⟩ • w = 0 := by
  apply (c.cellModuleEquiv μ).injective
  rw [cellModuleEquiv_smul, c.cellRep_basis_of_ne hne hnlt, Matrix.zero_mulVec, map_zero]

/-- Given a left `A`-module `S`, an index `t₀ : M μ`, and a vector `x₀ : S` annihilated by
`c.lowerSpan μ`, standard coordinates induce an `A`-linear homomorphism `c.CellModule μ →ₗ[A] S`
sending `c.cellBasis μ u` to `c.basis ⟨μ, u, t₀⟩ • x₀`. -/
noncomputable def cellModuleHom {S : Type*} [AddCommGroup S] [Module A S] {μ : Λ} (t₀ : M μ)
    (x₀ : S) (hlow : ∀ z ∈ c.lowerSpan μ, z • x₀ = 0) : c.CellModule μ →ₗ[A] S where
  toFun w := ∑ u, algebraMap R A (c.cellModuleEquiv μ w u) • (c.basis ⟨μ, u, t₀⟩ • x₀)
  map_add' w₁ w₂ := by
    simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a w := by
    have hstep (u : M μ) : (a * c.basis ⟨μ, u, t₀⟩) • x₀ =
        ∑ q, algebraMap R A (c.cellRep μ a q u) • (c.basis ⟨μ, q, t₀⟩ • x₀) := by
      have hmem := hlow _ (c.mul_basis_sub_sum_mem a μ u t₀)
      rw [sub_smul, sub_eq_zero] at hmem
      rw [hmem, Finset.sum_smul]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [Algebra.smul_def, mul_smul]
    rw [RingHom.id_apply, Finset.smul_sum]
    have lhs_eq : ∑ u, a • (algebraMap R A (c.cellModuleEquiv μ w u) •
        (c.basis ⟨μ, u, t₀⟩ • x₀)) =
        ∑ u, ∑ q, (algebraMap R A (c.cellModuleEquiv μ w u) *
          algebraMap R A (c.cellRep μ a q u)) • (c.basis ⟨μ, q, t₀⟩ • x₀) := by
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      calc a • (algebraMap R A (c.cellModuleEquiv μ w u) • (c.basis ⟨μ, u, t₀⟩ • x₀))
          = (algebraMap R A (c.cellModuleEquiv μ w u) * a) • (c.basis ⟨μ, u, t₀⟩ • x₀) := by
              rw [← mul_smul, Algebra.commutes]
        _ = algebraMap R A (c.cellModuleEquiv μ w u) • ((a * c.basis ⟨μ, u, t₀⟩) • x₀) := by
              rw [mul_smul, mul_smul]
        _ = _ := by
              rw [hstep u, Finset.smul_sum]
              exact Finset.sum_congr rfl fun q _ ↦ (mul_smul _ _ _).symm
    rw [lhs_eq, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [cellModuleEquiv_smul, Matrix.mulVec, dotProduct, map_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun u _ ↦
      congrArg (· • (c.basis ⟨μ, q, t₀⟩ • x₀))
        ((congrArg (algebraMap R A) (mul_comm _ _)).trans (map_mul _ _ _))

/-- `cellModuleHom` sends the standard basis vector `c.cellBasis μ s` to
`c.basis ⟨μ, s, t₀⟩ • x₀`. -/
@[simp]
theorem cellModuleHom_cellBasis {S : Type*} [AddCommGroup S] [Module A S] {μ : Λ} (t₀ : M μ)
    (x₀ : S) (hlow : ∀ z ∈ c.lowerSpan μ, z • x₀ = 0) (s : M μ) :
    c.cellModuleHom t₀ x₀ hlow (c.cellBasis μ s) = c.basis ⟨μ, s, t₀⟩ • x₀ := by
  simp [cellModuleHom, Pi.single_apply]

end CommRing

section PartialOrder

variable {R A Λ : Type*} [CommRing R] [Ring A] [Algebra R A] [PartialOrder Λ]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] [∀ μ, DecidableEq (M μ)]
  (c : CellularBasis R A M)

/-- Over a partial order of cells, `c.basis ⟨ν, x, y⟩` acts as zero at `μ` whenever `¬ μ ≤ ν`. -/
theorem cellRep_basis_of_not_le {μ ν : Λ} (h : ¬ μ ≤ ν) (x y : M ν) :
    c.cellRep μ (c.basis ⟨ν, x, y⟩) = 0 :=
  c.cellRep_basis_of_ne (fun hEq ↦ h hEq.ge) (fun hlt ↦ h hlt.le) x y

/-- Over a partial order of cells, `c.basis ⟨ν, x, y⟩` annihilates `c.CellModule μ` whenever
`¬ μ ≤ ν`. -/
theorem basis_smul_eq_zero_of_not_le {μ ν : Λ} (h : ¬ μ ≤ ν) (x y : M ν)
    (w : c.CellModule μ) : c.basis ⟨ν, x, y⟩ • w = 0 :=
  c.basis_smul_eq_zero_of_ne (fun hEq ↦ h hEq.ge) (fun hlt ↦ h hlt.le) x y w

end PartialOrder

section Field

variable {K B Λ : Type*} [Field K] [Ring B] [Algebra K B] [Preorder Λ]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] [∀ μ, DecidableEq (M μ)]
  (d : CellularBasis K B M)

/-- **Graham–Lehrer Proposition 2.6 (scalar endomorphisms).** Over any field `K`, if
`d.cellForm μ ≠ 0`, the structure map `K → Module.End B (d.CellModule μ ⧸ d.cellRadical μ)` is
bijective: every `B`-linear endomorphism of the simple cell quotient is scalar multiplication. -/
theorem algebraMap_end_cellModule_quotient_bijective {μ : Λ} (h : d.cellForm μ ≠ 0) :
    Function.Bijective (algebraMap K (Module.End B (d.CellModule μ ⧸ d.cellRadical μ))) := by
  let Q := d.CellModule μ ⧸ d.cellRadical μ
  have hsimple : IsSimpleModule B Q := (d.isSimpleModule_cellModule_quotient_iff μ).mpr h
  have : Nontrivial Q := IsSimpleModule.nontrivial B Q
  refine ⟨(algebraMap K (Module.End B Q)).injective, fun f ↦ ?_⟩
  obtain ⟨s, t, hst⟩ := d.exists_gramMatrix_ne_zero h
  have ht : d.cellBasis μ t ∉ d.cellRadical μ := fun hrad ↦
    hst (by rw [← d.cellForm_cellBasis, (d.isSymm_cellForm μ).eq, (d.mem_cellRadical μ _).mp hrad])
  let q : Q := Submodule.Quotient.mk (d.cellBasis μ t)
  have hq : q ≠ 0 := mt (Submodule.Quotient.mk_eq_zero (d.cellRadical μ)).mp ht
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (d.cellRadical μ) (f q)
  let r : K := (d.gramMatrix μ s t)⁻¹ * d.cellForm μ (d.cellBasis μ s) y
  have hfq : f q = r • q := by
    have hact : d.basis ⟨μ, t, s⟩ • f q = d.basis ⟨μ, t, s⟩ • Submodule.Quotient.mk y :=
      congrArg (d.basis ⟨μ, t, s⟩ • ·) hy.symm
    rw [← map_smul, ← Submodule.Quotient.mk_smul, d.basis_smul, d.cellForm_cellBasis,
      Submodule.Quotient.mk_smul, LinearMap.map_smul_of_tower, ← Submodule.Quotient.mk_smul,
      d.basis_smul, Submodule.Quotient.mk_smul] at hact
    simpa [r, q, smul_smul, hst] using congrArg ((d.gramMatrix μ s t)⁻¹ • ·) hact
  refine ⟨r, ?_⟩
  have hker : ¬ Function.Injective (f - algebraMap K (Module.End B Q) r) := fun hinj ↦
    hq (hinj (by simp [hfq, Algebra.algebraMap_eq_smul_one]))
  rcases (f - algebraMap K (Module.End B Q) r).bijective_or_eq_zero with ⟨hinj, -⟩ | hzero
  · exact (hker hinj).elim
  · exact (sub_eq_zero.mp hzero).symm

/-- The `K`-algebra equivalence `Module.End B (d.CellModule μ ⧸ d.cellRadical μ) ≃ₐ[K] K` given by
`algebraMap_end_cellModule_quotient_bijective` when `d.cellForm μ ≠ 0`. -/
noncomputable def endCellModuleQuotientAlgEquiv {μ : Λ} (h : d.cellForm μ ≠ 0) :
    Module.End B (d.CellModule μ ⧸ d.cellRadical μ) ≃ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K (Module.End B (d.CellModule μ ⧸ d.cellRadical μ)))
    (d.algebraMap_end_cellModule_quotient_bijective h)).symm

/-- The inverse of `endCellModuleQuotientAlgEquiv` is `algebraMap`. -/
@[simp]
theorem endCellModuleQuotientAlgEquiv_symm_apply {μ : Λ} (h : d.cellForm μ ≠ 0) (k : K) :
    (d.endCellModuleQuotientAlgEquiv h).symm k =
      algebraMap K (Module.End B (d.CellModule μ ⧸ d.cellRadical μ)) k :=
  (rfl)

/-- Every `B`-linear endomorphism of `d.CellModule μ ⧸ d.cellRadical μ` acts by its image under
`endCellModuleQuotientAlgEquiv`. -/
@[simp]
theorem endCellModuleQuotientAlgEquiv_smul {μ : Λ} (h : d.cellForm μ ≠ 0)
    (f : Module.End B (d.CellModule μ ⧸ d.cellRadical μ))
    (x : d.CellModule μ ⧸ d.cellRadical μ) :
    d.endCellModuleQuotientAlgEquiv h f • x = f x := by
  conv_rhs => rw [← (d.endCellModuleQuotientAlgEquiv h).symm_apply_apply f]
  rw [endCellModuleQuotientAlgEquiv_symm_apply, Module.algebraMap_end_apply]

/-- Over a field `K`, the `B`-endomorphism algebra of `d.CellModule μ ⧸ d.cellRadical μ` has
dimension `1` whenever `d.cellForm μ ≠ 0`. -/
theorem finrank_end_cellModule_quotient {μ : Λ} (h : d.cellForm μ ≠ 0) :
    Module.finrank K (Module.End B (d.CellModule μ ⧸ d.cellRadical μ)) = 1 := by
  rw [(d.endCellModuleQuotientAlgEquiv h).toLinearEquiv.finrank_eq, Module.finrank_self]

/-- **Graham–Lehrer Proposition 3.2 (ordering of homomorphisms).** If `d.cellForm μ ≠ 0` and
`f : d.CellModule ν →ₗ[B] d.CellModule μ ⧸ d.cellRadical μ` is nonzero, then `ν = μ ∨ ν < μ`. -/
theorem eq_or_lt_of_linearMap_cellModule_quotient_ne_zero {μ ν : Λ} (hμ : d.cellForm μ ≠ 0)
    {f : d.CellModule ν →ₗ[B] d.CellModule μ ⧸ d.cellRadical μ} (hf : f ≠ 0) :
    ν = μ ∨ ν < μ := by
  have : IsSimpleModule B (d.CellModule μ ⧸ d.cellRadical μ) :=
    (d.isSimpleModule_cellModule_quotient_iff μ).mpr hμ
  obtain ⟨s, t, hst⟩ := d.exists_gramMatrix_ne_zero hμ
  have ht : d.cellBasis μ t ∉ d.cellRadical μ := fun hrad ↦
    hst (by rw [← d.cellForm_cellBasis, (d.isSymm_cellForm μ).eq, (d.mem_cellRadical μ _).mp hrad])
  let q : d.CellModule μ ⧸ d.cellRadical μ := Submodule.Quotient.mk (d.cellBasis μ t)
  have hq : q ≠ 0 := mt (Submodule.Quotient.mk_eq_zero (d.cellRadical μ)).mp ht
  obtain ⟨w, hw⟩ := f.surjective_of_ne_zero hf q
  by_contra! h
  have hact : f (d.basis ⟨μ, t, s⟩ • w) = d.gramMatrix μ s t • q := by
    rw [map_smul, hw, ← Submodule.Quotient.mk_smul, d.basis_smul, d.cellForm_cellBasis,
      Submodule.Quotient.mk_smul]
  rw [d.basis_smul_eq_zero_of_ne h.1.symm h.2, map_zero] at hact
  exact (smul_ne_zero hst hq) hact.symm

/-- There is no `B`-linear equivalence between `d.CellModule μ ⧸ d.cellRadical μ` and
`d.CellModule ν ⧸ d.cellRadical ν` when `d.cellForm μ ≠ 0` and `μ ≠ ν`. -/
theorem isEmpty_cellModule_quotient_linearEquiv_of_ne {μ ν : Λ} (hμ : d.cellForm μ ≠ 0)
    (hne : μ ≠ ν) :
    IsEmpty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B] (d.CellModule ν ⧸ d.cellRadical ν)) := by
  refine ⟨fun e ↦ ?_⟩
  have hsm : IsSimpleModule B (d.CellModule μ ⧸ d.cellRadical μ) :=
    (d.isSimpleModule_cellModule_quotient_iff μ).mpr hμ
  have hsn : IsSimpleModule B (d.CellModule ν ⧸ d.cellRadical ν) := IsSimpleModule.congr e.symm
  have hν : d.cellForm ν ≠ 0 := (d.isSimpleModule_cellModule_quotient_iff ν).mp hsn
  have hf₁ : e.toLinearMap ∘ₗ (d.cellRadical μ).mkQ ≠ 0 := by
    have : Nontrivial (d.CellModule ν ⧸ d.cellRadical ν) := IsSimpleModule.nontrivial B _
    exact LinearMap.ne_zero_of_surjective (e.surjective.comp (Submodule.Quotient.mk_surjective _))
  have hf₂ : e.symm.toLinearMap ∘ₗ (d.cellRadical ν).mkQ ≠ 0 := by
    have : Nontrivial (d.CellModule μ ⧸ d.cellRadical μ) := IsSimpleModule.nontrivial B _
    exact LinearMap.ne_zero_of_surjective
      (e.symm.surjective.comp (Submodule.Quotient.mk_surjective _))
  have h₁ := (d.eq_or_lt_of_linearMap_cellModule_quotient_ne_zero hν hf₁).resolve_left hne
  have h₂ := (d.eq_or_lt_of_linearMap_cellModule_quotient_ne_zero hμ hf₂).resolve_left hne.symm
  exact lt_asymm h₁ h₂

/-- **Graham–Lehrer Theorem 3.4(i) (pairwise non-isomorphism).** For `d.cellForm μ ≠ 0`, the simple
quotient `d.CellModule μ ⧸ d.cellRadical μ` is `B`-linearly equivalent to
`d.CellModule ν ⧸ d.cellRadical ν` if and only if `μ = ν`. -/
theorem nonempty_cellModule_quotient_linearEquiv_iff {μ ν : Λ} (hμ : d.cellForm μ ≠ 0) :
    Nonempty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B] (d.CellModule ν ⧸ d.cellRadical ν)) ↔
      μ = ν := by
  refine ⟨fun ⟨e⟩ ↦ by_contra fun hne ↦
    (d.isEmpty_cellModule_quotient_linearEquiv_of_ne hμ hne).false e, ?_⟩
  rintro rfl
  exact ⟨LinearEquiv.refl B _⟩

/-- For distinct cells with nonzero bilinear forms, every `B`-linear map between their simple
quotients is zero. -/
theorem subsingleton_linearMap_cellModule_quotient_of_ne {μ ν : Λ}
    (hν : d.cellForm ν ≠ 0) (hμ : d.cellForm μ ≠ 0) (hne : ν ≠ μ) :
    Subsingleton ((d.CellModule ν ⧸ d.cellRadical ν) →ₗ[B] (d.CellModule μ ⧸ d.cellRadical μ)) := by
  have : IsSimpleModule B (d.CellModule ν ⧸ d.cellRadical ν) :=
    (d.isSimpleModule_cellModule_quotient_iff ν).mpr hν
  have : IsSimpleModule B (d.CellModule μ ⧸ d.cellRadical μ) :=
    (d.isSimpleModule_cellModule_quotient_iff μ).mpr hμ
  refine ⟨fun f g ↦ sub_eq_zero.mp ?_⟩
  rcases (f - g).bijective_or_eq_zero with hbij | hzero
  · exact ((d.isEmpty_cellModule_quotient_linearEquiv_of_ne hν hne).false
      (LinearEquiv.ofBijective (f - g) hbij)).elim
  · exact hzero

section WellFounded

variable [WellFoundedLT Λ]

omit [∀ μ, DecidableEq (M μ)] in
/-- In a cellular algebra with well-founded cell order, any nontrivial `B`-module `S` admits a
minimal cell acting nontrivially on `S`, whose lower span `d.lowerSpan μ` annihilates `S`. -/
private theorem exists_minimal_basis_smul_ne_zero (S : Type*) [AddCommGroup S] [Module B S]
    [Nontrivial S] :
    ∃ (μ : Λ) (s t : M μ) (x : S), d.basis ⟨μ, s, t⟩ • x ≠ 0 ∧
      ∀ z ∈ d.lowerSpan μ, ∀ y : S, z • y = 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : S)
  have hex : ∃ μ : Λ, ∃ (s t : M μ) (y : S), d.basis ⟨μ, s, t⟩ • y ≠ 0 := by
    by_contra! h0
    apply hx
    calc x = (1 : B) • x := (one_smul B x).symm
      _ = (Finsupp.linearCombination K d.basis (d.basis.repr 1)) • x := by
          rw [d.basis.linearCombination_repr]
      _ = 0 := by
          rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_smul]
          refine Finset.sum_eq_zero fun i _ ↦ ?_
          rw [Algebra.smul_def, mul_smul, h0 i.1 i.2.1 i.2.2 x, smul_zero]
  obtain ⟨μ, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun μ ↦ ∃ (s t : M μ) (y : S), d.basis ⟨μ, s, t⟩ • y ≠ 0) hex
  obtain ⟨s, t, x₀, hx₀⟩ := hmin.prop
  refine ⟨μ, s, t, x₀, hx₀, fun z hz y ↦ ?_⟩
  rw [lowerSpan_def] at hz
  induction hz using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨⟨ν, u, v⟩, hν : ν < μ, rfl⟩ := hb
    by_contra hne
    exact hmin.not_prop_of_lt hν ⟨u, v, y, hne⟩
  | zero => exact zero_smul B y
  | add b₁ b₂ _ _ ih₁ ih₂ => rw [add_smul, ih₁, ih₂, add_zero]
  | smul r b _ ih => rw [Algebra.smul_def, mul_smul, ih, smul_zero]

/-- **Graham–Lehrer Theorem 3.4(ii) (exhaustiveness).** Over a field `K`, when `<` on `Λ` is
well-founded (in particular when `Λ` is finite), every simple `B`-module is `B`-linearly equivalent
to `d.CellModule μ ⧸ d.cellRadical μ` for some cell `μ` with `d.cellForm μ ≠ 0`. -/
theorem exists_cellForm_ne_zero_and_nonempty_linearEquiv (S : Type*) [AddCommGroup S]
    [Module B S] [IsSimpleModule B S] :
    ∃ μ : Λ, d.cellForm μ ≠ 0 ∧ Nonempty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B] S) := by
  have : Nontrivial S := IsSimpleModule.nontrivial B S
  obtain ⟨μ, s₀, t₀, x₀, hx₀, hlow⟩ := d.exists_minimal_basis_smul_ne_zero S
  let f : d.CellModule μ →ₗ[B] S := d.cellModuleHom t₀ x₀ fun z hz ↦ hlow z hz x₀
  have hf_ne : f ≠ 0 := fun h0 ↦ hx₀ <| by
    simpa [f] using LinearMap.congr_fun h0 (d.cellBasis μ s₀)
  have hsurj : Function.Surjective f := f.surjective_of_ne_zero hf_ne
  obtain ⟨w₀, hw₀⟩ := hsurj x₀
  have hform : d.cellForm μ ≠ 0 := fun h0 ↦ hx₀ <| by
    rw [← hw₀, ← map_smul, d.basis_smul, h0, LinearMap.zero_apply, LinearMap.zero_apply,
      zero_smul, map_zero]
  have hcoatom : IsCoatom (LinearMap.ker f) := f.isCoatom_ker_of_surjective hsurj
  have hle : LinearMap.ker f ≤ d.cellRadical μ :=
    d.le_cellRadical_of_ne_top μ (LinearMap.ker f) hcoatom.1
  have hrad_ne : d.cellRadical μ ≠ ⊤ := mt (d.cellRadical_eq_top_iff μ).mp hform
  have hker_eq : LinearMap.ker f = d.cellRadical μ :=
    hle.eq_of_not_lt fun hlt ↦ hrad_ne (hcoatom.2 _ hlt)
  exact ⟨μ, hform, ⟨((d.cellRadical μ).quotEquivOfEq (LinearMap.ker f) hker_eq.symm).trans
    (f.quotKerEquivOfSurjective hsurj)⟩⟩

/-- **Graham–Lehrer Theorem 3.4 (classification of simple modules).** Over a field `K`, when `<` on
`Λ` is well-founded, every simple `B`-module is `B`-linearly equivalent to
`d.CellModule μ ⧸ d.cellRadical μ` for a unique cell `μ` with `d.cellForm μ ≠ 0`. -/
theorem existsUnique_cellForm_ne_zero_and_nonempty_linearEquiv (S : Type*) [AddCommGroup S]
    [Module B S] [IsSimpleModule B S] :
    ∃! μ : Λ, d.cellForm μ ≠ 0 ∧ Nonempty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B] S) := by
  obtain ⟨μ, hμ, ⟨e⟩⟩ := d.exists_cellForm_ne_zero_and_nonempty_linearEquiv S
  refine ⟨μ, ⟨hμ, ⟨e⟩⟩, fun ν ⟨hν, ⟨e'⟩⟩ ↦ ?_⟩
  exact (d.nonempty_cellModule_quotient_linearEquiv_iff hν).1 ⟨e'.trans e.symm⟩

omit [∀ μ, DecidableEq (M μ)] in
/-- Every simple module over a cellular `K`-algebra (with well-founded cell order) is absolutely
simple: the structure map `K → Module.End B S` is bijective, without any algebraic-closure
assumption on `K`. -/
theorem algebraMap_end_bijective_of_isSimpleModule (d : CellularBasis K B M) (S : Type*)
    [AddCommGroup S] [Module K S] [Module B S] [IsScalarTower K B S] [IsSimpleModule B S] :
    Function.Bijective (algebraMap K (Module.End B S)) := by
  classical
  obtain ⟨μ, hμ, ⟨e⟩⟩ := d.exists_cellForm_ne_zero_and_nonempty_linearEquiv S
  have hcomp : algebraMap K (Module.End B S) =
      (e.conjAlgEquiv K) ∘ algebraMap K (Module.End B (d.CellModule μ ⧸ d.cellRadical μ)) := by
    ext k s
    exact ((e.conjAlgEquiv K).commutes k).symm ▸ rfl
  rw [hcomp]
  exact (e.conjAlgEquiv K).bijective.comp (d.algebraMap_end_cellModule_quotient_bijective hμ)

omit [∀ μ, DecidableEq (M μ)] in
/-- The canonical `K`-algebra equivalence `Module.End B S ≃ₐ[K] K` for any simple module `S` over a
cellular `K`-algebra with well-founded cell order. -/
noncomputable def endAlgEquivOfIsSimpleModule (d : CellularBasis K B M) (S : Type*)
    [AddCommGroup S] [Module K S] [Module B S] [IsScalarTower K B S] [IsSimpleModule B S] :
    Module.End B S ≃ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K (Module.End B S))
    (d.algebraMap_end_bijective_of_isSimpleModule S)).symm

omit [∀ μ, DecidableEq (M μ)] in
/-- The inverse of `endAlgEquivOfIsSimpleModule` is `algebraMap`. -/
@[simp]
theorem endAlgEquivOfIsSimpleModule_symm_apply (d : CellularBasis K B M) {S : Type*}
    [AddCommGroup S] [Module K S] [Module B S] [IsScalarTower K B S] [IsSimpleModule B S] (k : K) :
    (d.endAlgEquivOfIsSimpleModule S).symm k = algebraMap K (Module.End B S) k :=
  (rfl)

omit [∀ μ, DecidableEq (M μ)] in
/-- Every `B`-linear endomorphism of `S` acts as scalar multiplication by its image under
`endAlgEquivOfIsSimpleModule`. -/
@[simp]
theorem endAlgEquivOfIsSimpleModule_smul (d : CellularBasis K B M) {S : Type*} [AddCommGroup S]
    [Module K S] [Module B S] [IsScalarTower K B S] [IsSimpleModule B S]
    (f : Module.End B S) (s : S) :
    d.endAlgEquivOfIsSimpleModule S f • s = f s := by
  conv_rhs => rw [← (d.endAlgEquivOfIsSimpleModule S).symm_apply_apply f]
  rw [endAlgEquivOfIsSimpleModule_symm_apply, Module.algebraMap_end_apply]

omit [∀ μ, DecidableEq (M μ)] in
/-- Every simple module `S` over a cellular `K`-algebra (with well-founded cell order) satisfies
`Module.finrank K (Module.End B S) = 1`. -/
theorem finrank_end_eq_one_of_isSimpleModule (d : CellularBasis K B M) (S : Type*) [AddCommGroup S]
    [Module K S] [Module B S] [IsScalarTower K B S] [IsSimpleModule B S] :
    Module.finrank K (Module.End B S) = 1 := by
  rw [(d.endAlgEquivOfIsSimpleModule S).toLinearEquiv.finrank_eq, Module.finrank_self]

end WellFounded

end Field

section FieldPartialOrder

variable {K B Λ : Type*} [Field K] [Ring B] [Algebra K B] [PartialOrder Λ]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] [∀ μ, DecidableEq (M μ)]
  (d : CellularBasis K B M)

/-- Partial-order form of `eq_or_lt_of_linearMap_cellModule_quotient_ne_zero`: a nonzero `B`-linear
map `d.CellModule ν →ₗ[B] d.CellModule μ ⧸ d.cellRadical μ` with `d.cellForm μ ≠ 0` implies
`ν ≤ μ`. -/
theorem le_of_linearMap_cellModule_quotient_ne_zero {μ ν : Λ} (hμ : d.cellForm μ ≠ 0)
    {f : d.CellModule ν →ₗ[B] d.CellModule μ ⧸ d.cellRadical μ} (hf : f ≠ 0) :
    ν ≤ μ := by
  rcases d.eq_or_lt_of_linearMap_cellModule_quotient_ne_zero hμ hf with rfl | hlt
  · exact le_rfl
  · exact hlt.le

end FieldPartialOrder

section Matrix

/-- The single cell of `CellularBasis.matrix R n` has trivial cell radical over any commutative
ring `R`. -/
@[simp]
theorem cellRadical_matrix {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] :
    (CellularBasis.matrix R n).cellRadical () = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  apply ((CellularBasis.matrix R n).cellModuleEquiv ()).injective
  ext i
  have h0 := ((CellularBasis.matrix R n).mem_cellRadical () x).mp hx
    ((CellularBasis.matrix R n).cellBasis () i)
  simpa [cellForm_apply, dotProduct, Matrix.one_apply] using h0

/-- Over a nontrivial commutative ring `R` and nonempty finite index type `n`, the single cell of
`CellularBasis.matrix R n` has nonzero bilinear form. -/
theorem cellForm_matrix_ne_zero {R n : Type*} [CommRing R] [Nontrivial R] [Fintype n]
    [DecidableEq n] [Nonempty n] :
    (CellularBasis.matrix R n).cellForm () ≠ 0 := by
  rw [ne_eq, (CellularBasis.matrix R n).cellForm_eq_zero_iff, gramMatrix_matrix]
  exact one_ne_zero

/-- **Sharpness of the field hypothesis.** For `CellularBasis.matrix ℤ Unit` (whose cell form is
nonzero by `cellForm_matrix_ne_zero` and whose cell radical is `⊥` by `cellRadical_matrix`), the
radical quotient is isomorphic to `ℤ` and is not a simple module. -/
theorem not_isSimpleModule_matrix_int_cellModule_quotient :
    ¬ IsSimpleModule (Matrix Unit Unit ℤ)
      ((CellularBasis.matrix ℤ Unit).CellModule () ⧸
        (CellularBasis.matrix ℤ Unit).cellRadical ()) := by
  let c := CellularBasis.matrix ℤ Unit
  intro hsimple
  have hcoatom : IsCoatom (c.cellRadical ()) := isSimpleModule_iff_isCoatom.mp hsimple
  let v := c.cellBasis () () + c.cellBasis () ()
  let N : Submodule (Matrix Unit Unit ℤ) (c.CellModule ()) :=
    Submodule.span (Matrix Unit Unit ℤ) {v}
  have hne_zero : v ≠ 0 := fun h0 ↦ by
    have := congrFun (congrArg (c.cellModuleEquiv ()) h0) ()
    simp [v] at this
  have hlt : c.cellRadical () < N := by
    rw [cellRadical_matrix, bot_lt_iff_ne_bot, Submodule.ne_bot_iff]
    exact ⟨v, Submodule.subset_span (Set.mem_singleton _), hne_zero⟩
  have hmem : c.cellBasis () () ∈ N := hcoatom.2 N hlt ▸ Submodule.mem_top
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨m, hm⟩ := hmem
  have hcoord := congrFun (congrArg (c.cellModuleEquiv ()) hm) ()
  simp only [c, v, cellModuleEquiv_smul, cellRep_matrix, map_add, cellModuleEquiv_cellBasis,
    Matrix.mulVec, dotProduct, Fintype.univ_punit, Finset.sum_singleton, Pi.add_apply,
    Pi.single_eq_same] at hcoord
  have : m () () * (1 + 1) = 1 := hcoord
  omega

end Matrix

end TauCeti.CellularBasis
