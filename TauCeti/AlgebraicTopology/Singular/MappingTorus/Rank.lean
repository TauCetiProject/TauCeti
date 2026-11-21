/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Wang
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.AlgebraicTopology.Singular.Coefficients.BaseChange

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
one. This is the criterion used for surface mapping tori `Y_φ` with `b₁(Y_φ) = 1`, where
`1 - φ_*` is then invertible over `ℚ` or `ℝ`.

The same criterion holds in cohomology: `dim H¹(T_φ; k) = 1` exactly when `𝟙 - φ^*` is
invertible on `H¹(F; k)`, because over a field `φ^*` is the transpose of `φ_*` and `H¹` and `H₁`
have the same dimension. For a surface mapping torus with `b₁(Y_φ) = 1` this is the invertibility
of `I - P`, with `P = φ^*` the monodromy on `H¹(F; ℝ)`.

When `H₁(F; ℤ)` is free of finite rank, as for a closed orientable surface, the criterion can be
read off the integral monodromy: for a field `k` of characteristic zero, `H₁(F; k)` is
`k ⊗ H₁(F; ℤ)` compatibly with `φ_*` (`TopCat.singularHomologyBaseChangeEquiv`), so the
determinant over `k` is the image of the integral determinant, and `b₁(T_φ; k) = 1` exactly when
the integral `det (𝟙 - φ_*)` is nonzero. Under this condition the integral results apply:
`H¹(T_φ; ℤ) ≅ ℤ` (`TauCeti.MappingTorus.cohomologyOneEquiv`) and the torsion of `H₁(T_φ; ℤ)`
has order `|det (𝟙 - φ_*)|` (`TauCeti.MappingTorus.card_torsion_homology_one_eq_natAbs_det`).

## Main results

* `TauCeti.MappingTorus.rank_homology_one`: `rank H₁(T_φ; k) = rank coker (𝟙 - φ_*) + 1`.
* `TauCeti.MappingTorus.finrank_homology_one`: `b₁(T_φ; k) = dim ker (𝟙 - φ_*) + 1` when
  `H₁(F; k)` is finite-dimensional.
* `TauCeti.MappingTorus.finrank_homology_one_eq_one_iff`: `b₁(T_φ; k) = 1` if and only if
  `det (𝟙 - φ_*) ≠ 0`.
* `TauCeti.MappingTorus.finrank_cohomology_one_eq_one_iff`: `dim H¹(T_φ; k) = 1` if and only if
  `det (𝟙 - φ^*) ≠ 0` on `H¹(F; k)`.
* `TauCeti.MappingTorus.finrank_homology_one_eq_one_iff_det_int_ne_zero`: for `H₁(F; ℤ)` free of
  finite rank and `k` of characteristic zero, `b₁(T_φ; k) = 1` if and only if the integral
  determinant `det (𝟙 - φ_*)` is nonzero.

See A. Hatcher, *Algebraic Topology*, Section 2.2, Example 2.48, for the Wang sequence of a
mapping torus, and Sections 3.1 and 3.A for the universal coefficient theorems.
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

/-- **The first Betti number of a mapping torus in cohomology**: for a path-connected fibre whose
first homology is finite-dimensional over a field, `dim H¹(T_φ) = 1` if and only if
`det (𝟙 - φ^*) ≠ 0` on `H¹(F)`, that is, when `φ^*` fixes no nonzero class of `H¹(F)`. -/
theorem finrank_cohomology_one_eq_one_iff
    [FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)] :
    finrank k ((TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k
        (ModuleCat.of k k) 1) = 1 ↔
      (LinearMap.id - (TopCat.singularCohomologyMap (R := ModuleCat.of k k) (k := k)
        (M := ModuleCat.of k k) (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F))) 1).hom).det ≠ 0 := by
  -- `singularHomologyFunctor` is by definition the homology of the singular chain complex.
  have : FiniteDimensional k (((singularHomologyFunctor (ModuleCat.{w} k) 1).obj
    (ModuleCat.of k k)).obj (TopCat.of F)) := ‹_›
  rw [TopCat.finrank_singularCohomology, TopCat.det_id_sub_singularCohomologyMap]
  have h := finrank_homology_one_eq_one_iff (k := k) φ
  rw [monodromyChainMap_def] at h
  exact h

end Field

section Integral

variable {F : Type} [TopologicalSpace F] [PathConnectedSpace F] (φ : F ≃ₜ F)
  (k : Type) [Field k] [CharZero k]

/-- **The rational first Betti number of a mapping torus from the integral monodromy**: if
`H₁(F; ℤ)` is free of finite rank, then for every field `k` of characteristic zero,
`b₁(T_φ; k) = 1` if and only if the integral determinant `det (𝟙 - φ_*)` on `H₁(F; ℤ)` is
nonzero. The determinant over `k` is the image of the integral one, since
`H₁(F; k) ≅ k ⊗ H₁(F; ℤ)` compatibly with `φ_*`. -/
theorem finrank_homology_one_eq_one_iff_det_int_ne_zero
    [Module.Free ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
    [Module.Finite ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)] :
    finrank k ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology 1) = 1 ↔
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0 := by
  -- `singularHomologyFunctor` is by definition the homology of the singular chain complex.
  have : Module.Free ℤ (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)) := ‹_›
  have : Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)) := ‹_›
  have : FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 1) :=
    Module.Finite.equiv (TopCat.singularHomologyBaseChangeEquiv ℤ k (TopCat.of F) 1)
  rw [finrank_homology_one_eq_one_iff (k := k) φ]
  have h := TopCat.det_id_sub_singularHomologyMap_eq_algebraMap (R := ℤ) (S := k)
    (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F))) 1
  -- `homologyMap (monodromyChainMap φ R) 1` is by definition the singular homology functor
  -- applied to `φ`.
  rw [monodromyChainMap_def, monodromyChainMap_def]
  exact h ▸ (map_ne_zero_iff _ (algebraMap ℤ k).injective_int)

end Integral

end TauCeti.MappingTorus
