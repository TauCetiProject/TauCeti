/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Wang
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.AlgebraicTopology.Singular.Coefficients.ExtendScalars
import Mathlib.RingTheory.Flat.TorsionFree

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

The computations of `H¹(T_φ; ℤ)` and of the torsion of `H₁(T_φ; ℤ)` through the Wang sequence
assume instead that the integral determinant `det (𝟙 - φ_*)` on `H₁(F; ℤ)` is nonzero. When
`H₁(F; ℤ)` is free of finite rank, as for a closed orientable surface, the two conditions agree:
for a field `K` of characteristic zero, `H₁(F; K) ≅ K ⊗ H₁(F; ℤ)` compatibly with `φ_*`, so the
determinant over `K` is the image of the integral one
(`RingHom.Flat.det_id_sub_singularHomologyMap_eq`), and `b₁(T_φ; K) = 1` if and only if the integral
determinant is nonzero.

## Main results

* `TauCeti.MappingTorus.rank_homology_one`: `rank H₁(T_φ; k) = rank coker (𝟙 - φ_*) + 1`.
* `TauCeti.MappingTorus.finrank_homology_one`: `b₁(T_φ; k) = dim ker (𝟙 - φ_*) + 1` when
  `H₁(F; k)` is finite-dimensional.
* `TauCeti.MappingTorus.finrank_homology_one_eq_one_iff`: `b₁(T_φ; k) = 1` if and only if
  `det (𝟙 - φ_*) ≠ 0`.
* `TauCeti.MappingTorus.finrank_homology_one_eq_one_iff_det_int_ne_zero`: for a field `K` of
  characteristic zero and `H₁(F; ℤ)` free of finite rank, `b₁(T_φ; K) = 1` if and only if the
  integral determinant `det (𝟙 - φ_*)` on `H₁(F; ℤ)` is nonzero.

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

section Integral

variable {F : Type} [TopologicalSpace F] [PathConnectedSpace F] (φ : F ≃ₜ F)

/-- **The first Betti number of a mapping torus through the integral determinant**: for a
path-connected fibre whose first integral homology is free of finite rank and a field `K` of
characteristic zero, `b₁(T_φ; K) = 1` if and only if `det (𝟙 - φ_*) ≠ 0` on `H₁(F; ℤ)`. -/
theorem finrank_homology_one_eq_one_iff_det_int_ne_zero (K : Type) [Field K] [CharZero K]
    [Module.Free ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
    [Module.Finite ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)] :
    finrank K ((((singularChainComplexFunctor (ModuleCat.{0} K)).obj
        (ModuleCat.of K K)).obj (TopCat.of (MappingTorus φ))).homology 1) = 1 ↔
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0 := by
  have hf : (Int.castRingHom K).Flat := by
    rw [← algebraMap_int_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have := hf.finite_singularHomology (TopCat.of F) 1
  rw [finrank_homology_one_eq_one_iff, monodromyChainMap_def, monodromyChainMap_def,
    hf.det_id_sub_singularHomologyMap_eq, eq_intCast, Int.cast_ne_zero]

end Integral

end TauCeti.MappingTorus
