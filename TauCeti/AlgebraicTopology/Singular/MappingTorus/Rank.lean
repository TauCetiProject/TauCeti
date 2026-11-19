/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Wang
public import TauCeti.AlgebraicTopology.Singular.Coefficients.BaseChange
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# The first Betti number of a mapping torus

Let `φ : F ≃ₜ F` be a homeomorphism of a path-connected space and `T_φ` its mapping torus. The
monodromy acts trivially on `H₀(F)`, so the Wang sequence ends with
`H₁(F) ⟶ H₁(F) ⟶ H₁(T_φ) ⟶ H₀(F) ⟶ 0`, with maps `𝟙 - φ_*`, the fibre inclusion and the
Wang connecting morphism (`TauCeti.MappingTorus.epi_wangδ_zero`).

With coefficients in a field `k`, the image of the fibre is the cokernel of `𝟙 - φ_*`
(`TauCeti.MappingTorus.wangCokernelEquiv`) and `H₀(F; k) ≅ k`, so
`rank H₁(T_φ; k) = rank coker (𝟙 - φ_*) + 1`. When `H₁(F; k)` is finite-dimensional, the
kernel and cokernel of the endomorphism `𝟙 - φ_*` have the same dimension, which gives
`b₁(T_φ; k) = dim ker (𝟙 - φ_*) + 1`. In particular the first Betti number of the mapping torus
is `1` exactly when `det (𝟙 - φ_*) ≠ 0` on `H₁(F; k)`, that is, when `φ_*` has no eigenvalue
one.

This is the criterion used for surface mapping tori `Y_φ` with `b₁(Y_φ) = 1`, and two further
forms of it are proved here.

* **Integral form.** Over a field `k` of characteristic zero, `H₁(F; k) ≅ k ⊗ H₁(F; ℤ)` by flat
  base change (`TopCat.singularHomologyBaseChangeEquiv`), and `φ_*` corresponds to the base change
  of its integral action. So if `H₁(F; ℤ)` is free, the determinant of `𝟙 - φ_*` over `k` is the
  image of the integral determinant, and when `H₁(F; ℤ)` also has finite rank, `b₁(T_φ; k) = 1`
  exactly when the integral determinant `det (𝟙 - φ_*)` is nonzero. So the condition
  `b₁(T_φ; k) = 1` is the same for all fields of characteristic zero, and it is the hypothesis of
  the integral results `TauCeti.MappingTorus.card_torsion_homology_one_eq_natAbs_det` and
  `TauCeti.MappingTorus.cohomologyOneEquiv`.
* **Cohomological form.** By the universal coefficient theorem over a field, `φ^*` on `H¹(F; k)`
  is the transpose of `φ_*` on `H₁(F; k)`, so the two endomorphisms `𝟙 - φ^*` and `𝟙 - φ_*` have
  the same determinant, and `dim H¹(T_φ; k) = 1` exactly when `𝟙 - φ^*` is invertible on
  `H¹(F; k)`.

## Main results

* `TauCeti.MappingTorus.rank_homology_one`: `rank H₁(T_φ; k) = rank coker (𝟙 - φ_*) + 1`.
* `TauCeti.MappingTorus.finrank_homology_one`: `b₁(T_φ; k) = dim ker (𝟙 - φ_*) + 1` when
  `H₁(F; k)` is finite-dimensional.
* `TauCeti.MappingTorus.finrank_homology_one_eq_one_iff`: `b₁(T_φ; k) = 1` if and only if
  `det (𝟙 - φ_*) ≠ 0`.
* `TauCeti.MappingTorus.det_id_sub_homologyMap_monodromyChainMap_eq_algebraMap`: the determinant
  of `𝟙 - φ_*` over a flat `R`-algebra `S` is the image of its determinant over `R`.
* `TauCeti.MappingTorus.finrank_homology_one_eq_one_iff_det_int_ne_zero`: if `H₁(F; ℤ)` is free
  of finite rank and `k` has characteristic zero, `b₁(T_φ; k) = 1` if and only if the integral
  determinant of `𝟙 - φ_*` is nonzero.
* `TauCeti.MappingTorus.det_id_sub_singularCohomologyMap_eq`: `𝟙 - φ^*` on `Hⁿ(F; k)` and
  `𝟙 - φ_*` on `Hₙ(F; k)` have the same determinant.
* `TauCeti.MappingTorus.finrank_cohomology_one_eq_one_iff`: `dim H¹(T_φ; k) = 1` if and only if
  `det (𝟙 - φ^*) ≠ 0` on `H¹(F; k)`.

See A. Hatcher, *Algebraic Topology*, Section 2.2, Example 2.48, for the Wang sequence of a
mapping torus.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Module

universe w

namespace TauCeti.MappingTorus

section Field

variable {k : Type w} [Field k] {F : Type w} [TopologicalSpace F] [PathConnectedSpace F]
  (φ : F ≃ₜ F)

/-- **The rank of the first homology of a mapping torus.** For a path-connected fibre and
coefficients in a field, `rank H₁(T_φ) = rank coker (𝟙 - φ_*) + 1`, with `𝟙 - φ_*` acting on
`H₁(F)`. -/
theorem rank_homology_one :
    Module.rank k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology 1) =
      Module.rank k (((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of F)).homology 1) ⧸ LinearMap.range
          (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom)) + 1 := by
  -- `H₀(F; k) ≅ k` through the augmentation; `singularHomologyFunctor` is by definition the
  -- homology of `singularChainComplexFunctor`.
  have h₀ : Module.rank k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 0) = 1 :=
    (asIso ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k))).toLinearEquiv.rank_eq.trans
      (rank_self k)
  have hδ : Function.Surjective (wangδ φ (ModuleCat.of k k) 0).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  rw [LinearMap.rank_eq_of_surjective hδ, h₀, ← range_homologyMap_fibreInclusionChainMap,
    (wangCokernelEquiv φ 1).rank_eq, add_comm]

/-- If the first homology of a path-connected fibre is finite-dimensional, so is that of the
mapping torus. -/
instance finiteDimensional_homology_one
    [FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)] :
    FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology 1) := by
  refine Module.rank_lt_aleph0_iff.1 ?_
  rw [rank_homology_one]
  exact Cardinal.add_lt_aleph0 (rank_lt_aleph0 k _) Cardinal.one_lt_aleph0

/-- **The first Betti number of a mapping torus.** For a path-connected fibre whose first homology
is finite-dimensional over a field, `b₁(T_φ) = dim ker (𝟙 - φ_*) + 1`, with `𝟙 - φ_*` acting
on `H₁(F)`. -/
theorem finrank_homology_one
    [FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)] :
    finrank k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology 1) =
      finrank k (LinearMap.ker
        (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom)) + 1 := by
  set f := LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom
  have h : finrank k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology 1) =
      finrank k (((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of F)).homology 1) ⧸ LinearMap.range f) + 1 := by
    have := rank_homology_one φ (k := k)
    rw [← finrank_eq_rank, ← finrank_eq_rank] at this
    exact_mod_cast this
  -- The kernel and cokernel of the endomorphism `f` have the same dimension.
  have hq := (LinearMap.range f).finrank_quotient_add_finrank
  have hr := f.finrank_range_add_finrank_ker
  omega

/-- **The first Betti number of a mapping torus is one exactly when the monodromy has no fixed
homology class**: for a path-connected fibre whose first homology is finite-dimensional over a
field, `b₁(T_φ) = 1` if and only if `det (𝟙 - φ_*) ≠ 0` on `H₁(F)`. -/
theorem finrank_homology_one_eq_one_iff
    [FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)] :
    finrank k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology 1) = 1 ↔
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0 := by
  rw [finrank_homology_one, Nat.add_eq_right, Submodule.finrank_eq_zero, ne_eq,
    LinearMap.det_eq_zero_iff_ker_ne_bot, not_not]

end Field

section BaseChange

open scoped TensorProduct

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- **The Wang determinant under flat base change.** If `S` is a flat `R`-algebra and `Hₙ(F; R)` is
free, the determinant of `𝟙 - φ_*` on `Hₙ(F; S)` is the image in `S` of its determinant on
`Hₙ(F; R)`. (When `Hₙ(F; R)` has infinite rank, both determinants are `1` by convention.) -/
theorem det_id_sub_homologyMap_monodromyChainMap_eq_algebraMap (R S : Type w) [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] (n : ℕ)
    [Module.Free R ((((singularChainComplexFunctor (ModuleCat.{w} R)).obj
      (ModuleCat.of R R)).obj (TopCat.of F)).homology n)] :
    (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of S S)) n).hom).det =
      algebraMap R S
        (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of R R)) n).hom).det := by
  -- `singularHomologyFunctor` is by definition the homology of the singular chain complex.
  let e : (((singularChainComplexFunctor (ModuleCat.{w} S)).obj (ModuleCat.of S S)).obj
      (TopCat.of F)).homology n ≃ₗ[S] S ⊗[R] (((singularChainComplexFunctor (ModuleCat.{w} R)).obj
        (ModuleCat.of R R)).obj (TopCat.of F)).homology n :=
    TopCat.singularHomologyBaseChangeEquiv R S (TopCat.of F) n
  -- Under `Hₙ(F; S) ≃ S ⊗[R] Hₙ(F; R)` the endomorphism `𝟙 - φ_*` becomes its base change.
  have h : LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of S S)) n).hom =
      (e.symm : _ →ₗ[S] _) ∘ₗ (LinearMap.id -
        (homologyMap (monodromyChainMap φ (ModuleCat.of R R)) n).hom).baseChange S ∘ₗ
          (e.symm.symm : _ →ₗ[S] _) := by
    refine LinearMap.ext fun x ↦ e.injective ?_
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, map_sub,
      LinearMap.baseChange_sub, LinearMap.baseChange_id, ← singularHomologyMap_monodromy_eq]
    exact congrArg (e x - ·) (TopCat.singularHomologyBaseChangeEquiv_naturality _ n x)
  nontriviality S
  by_cases hfin : Module.Finite R ((((singularChainComplexFunctor (ModuleCat.{w} R)).obj
    (ModuleCat.of R R)).obj (TopCat.of F)).homology n)
  · rw [h, LinearMap.det_conj, LinearMap.det_baseChange]
  · -- A free module whose base change to the nontrivial ring `S` is finite is finite.
    rw [LinearMap.det_eq_one_of_not_module_finite hfin, map_one]
    refine LinearMap.det_eq_one_of_not_module_finite (fun hS ↦ hfin ?_) _
    let b := Module.Free.chooseBasis R ((((singularChainComplexFunctor (ModuleCat.{w} R)).obj
      (ModuleCat.of R R)).obj (TopCat.of F)).homology n)
    have := Module.Finite.equiv e
    have := Module.Finite.finite_basis (Algebra.TensorProduct.basis S b)
    exact Module.Finite.of_basis b

end BaseChange

section Integral

open scoped TensorProduct

/-- **The first Betti number of a mapping torus from integral homology.** If `H₁(F; ℤ)` is free of
finite rank, then over every field `k` of characteristic zero, such as `ℚ` or `ℝ`,
`b₁(T_φ; k) = 1` if and only if the integral determinant `det (𝟙 - φ_*)` on `H₁(F; ℤ)` is nonzero.
-/
theorem finrank_homology_one_eq_one_iff_det_int_ne_zero {F : Type} [TopologicalSpace F]
    [PathConnectedSpace F] (φ : F ≃ₜ F) (k : Type) [Field k] [CharZero k]
    [Module.Free ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
    [Module.Finite ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)] :
    finrank k ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology 1) = 1 ↔
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0 := by
  have : FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 1) :=
    -- `singularHomologyFunctor` is by definition the homology of the singular chain complex.
    Module.Finite.equiv (R := k) (M := k ⊗[ℤ] (((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)
        (TopCat.singularHomologyBaseChangeEquiv ℤ k (TopCat.of F) 1).symm
  rw [finrank_homology_one_eq_one_iff, det_id_sub_homologyMap_monodromyChainMap_eq_algebraMap φ ℤ k,
    ne_eq, ne_eq, map_eq_zero_iff _ (algebraMap ℤ k).injective_int]

end Integral

section Cohomology

variable {k : Type w} [Field k] {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- **The Wang determinant in cohomology.** Over a field, the determinant of `𝟙 - φ^*` on
`Hⁿ(F; k)` equals the determinant of `𝟙 - φ_*` on `Hₙ(F; k)`: the universal coefficient theorem
identifies `φ^*` with the transpose of `φ_*`. (When `Hₙ(F; k)` is infinite-dimensional, so is
`Hⁿ(F; k)`, and both determinants are `1` by convention.) -/
theorem det_id_sub_singularCohomologyMap_eq (n : ℕ) :
    (LinearMap.id - (TopCat.singularCohomologyMap (R := ModuleCat.of k k) (k := k)
        (M := ModuleCat.of k k) (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F))) n).hom).det =
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom).det := by
  -- `singularHomologyFunctor` is by definition the homology of the singular chain complex.
  let e : (TopCat.of F).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) n ≃ₗ[k]
      Dual k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
        (TopCat.of F)).homology n) :=
    (TopCat.of F).singularCohomologyDualEquiv n
  -- Under `Hⁿ(F; k) ≃ Dual k Hₙ(F; k)` the endomorphism `𝟙 - φ^*` becomes the transpose of
  -- `𝟙 - φ_*`.
  have h : LinearMap.id - (TopCat.singularCohomologyMap (R := ModuleCat.of k k) (k := k)
      (M := ModuleCat.of k k) (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F))) n).hom =
      (e.symm : _ →ₗ[k] _) ∘ₗ (LinearMap.id -
        (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom).dualMap ∘ₗ
          (e.symm.symm : _ →ₗ[k] _) := by
    refine LinearMap.ext fun α ↦ e.injective ?_
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, map_sub,
      LinearMap.dualMap_apply', LinearMap.comp_sub, LinearMap.comp_id,
      ← singularHomologyMap_monodromy_eq]
    exact congrArg (e α - ·) ((TopCat.singularCohomologyDualEquiv_singularCohomologyMap _ n α).trans
      (Dual.transpose_apply _ _))
  by_cases hfin : Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
    (ModuleCat.of k k)).obj (TopCat.of F)).homology n)
  · rw [h, LinearMap.det_conj, LinearMap.det_dualMap]
  · rw [LinearMap.det_eq_one_of_not_module_finite hfin, LinearMap.det_eq_one_of_not_module_finite]
    exact fun hc ↦ hfin (((TopCat.of F).finite_singularCohomology_iff n).1 hc)

/-- **The first Betti number of a mapping torus in cohomology.** For a path-connected fibre whose
first homology is finite-dimensional over a field `k`, `dim H¹(T_φ; k) = 1` if and only if
`det (𝟙 - φ^*) ≠ 0` on `H¹(F; k)`, that is, if and only if `𝟙 - φ^*` is invertible on
`H¹(F; k)`. -/
theorem finrank_cohomology_one_eq_one_iff [PathConnectedSpace F]
    [FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)] :
    finrank k ((TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k
        (ModuleCat.of k k) 1) = 1 ↔
      (LinearMap.id - (TopCat.singularCohomologyMap (R := ModuleCat.of k k) (k := k)
        (M := ModuleCat.of k k) (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F))) 1).hom).det ≠ 0 := by
  rw [TopCat.finrank_singularCohomology, det_id_sub_singularCohomologyMap_eq]
  exact finrank_homology_one_eq_one_iff φ

end Cohomology

end TauCeti.MappingTorus
