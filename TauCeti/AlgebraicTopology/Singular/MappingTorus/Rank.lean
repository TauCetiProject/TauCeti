/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Wang
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Finite
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.AlgebraicTopology.Singular.Coefficients.BaseChange
import TauCeti.LinearAlgebra.Exact

/-!
# The Betti numbers of a mapping torus

Let `φ : F ≃ₜ F` be a homeomorphism and `T_φ` its mapping torus. With coefficients in a field `k`,
the Wang short exact sequence
`0 ⟶ Hₙ₊₁(F) ⧸ range (𝟙 - φ_*) ⟶ Hₙ₊₁(T_φ) ⟶ ker (𝟙 - φ_*) ⟶ 0`
(`TauCeti.MappingTorus.wangKernelShortComplex_shortExact`) computes the Betti numbers in every
positive degree: if the homology of the fibre is finite-dimensional in degrees `n` and `n + 1`, so
is `Hₙ₊₁(T_φ)` (`TauCeti.MappingTorus.finite_singularHomology_succ`), and since the kernel and
cokernel of an endomorphism of a finite-dimensional space have the same dimension,
`bₙ₊₁(T_φ) = dim ker (𝟙 - φ_*) + dim ker (𝟙 - φ_*)`, with `𝟙 - φ_*` acting on `Hₙ₊₁(F)` and on
`Hₙ(F)` respectively (`TauCeti.MappingTorus.finrank_homology_succ`).

**Degree one.** Let the fibre `F` be path-connected. The monodromy acts trivially on `H₀(F)`, so
the Wang sequence ends with
`H₁(F) ⟶ H₁(F) ⟶ H₁(T_φ) ⟶ H₀(F) ⟶ 0`, with maps `𝟙 - φ_*`, the fibre inclusion and the
Wang connecting morphism (`TauCeti.MappingTorus.epi_wangδ_zero`).

With coefficients in a field `k`, the image of the fibre is the cokernel of `𝟙 - φ_*`
(`TauCeti.MappingTorus.wangCokernelEquiv`) and `H₀(F; k) ≅ k`, so
`rank H₁(T_φ; k) = rank coker (𝟙 - φ_*) + 1`. When `H₁(F; k)` is finite-dimensional, the
kernel and cokernel of the endomorphism `𝟙 - φ_*` have the same dimension, which gives
`b₁(T_φ; k) = dim ker (𝟙 - φ_*) + 1`, the case `n = 0` of the formula above. In particular the
first Betti number of the mapping torus is `1` exactly when `det (𝟙 - φ_*) ≠ 0` on `H₁(F; k)`,
that is, when `φ_*` has no eigenvalue one. This is the criterion used for surface mapping tori
`Y_φ` with `b₁(Y_φ) = 1`.

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

* `TauCeti.MappingTorus.finrank_homology_succ`:
  `bₙ₊₁(T_φ; k) = dim ker (𝟙 - φ_*)|Hₙ₊₁(F) + dim ker (𝟙 - φ_*)|Hₙ(F)`.
* `TauCeti.MappingTorus.rank_homology_one`: `rank H₁(T_φ; k) = rank coker (𝟙 - φ_*) + 1`.
* `TauCeti.MappingTorus.finrank_homology_one`: `b₁(T_φ; k) = dim ker (𝟙 - φ_*) + 1` when
  `H₁(F; k)` is finite-dimensional.
* `TauCeti.MappingTorus.finrank_homology_one_eq_one_iff`: `b₁(T_φ; k) = 1` if and only if
  `det (𝟙 - φ_*) ≠ 0`.
* `TauCeti.MappingTorus.det_id_sub_homologyMap_monodromyChainMap_eq_algebraMap`: if `Hₙ(F; R)`
  is free, the determinant of `𝟙 - φ_*` over a flat `R`-algebra `S` is the image of its
  determinant over `R`.
* `TauCeti.MappingTorus.finrank_homology_one_eq_one_iff_det_int_ne_zero`: for `H₁(F; ℤ)` free of
  finite rank and `k` of characteristic zero, `b₁(T_φ; k) = 1` if and only if the integral
  determinant `det (𝟙 - φ_*)` is nonzero.
* `TauCeti.MappingTorus.det_id_sub_singularCohomologyMap_eq`: `𝟙 - φ^*` on `Hⁿ(F; k)` and
  `𝟙 - φ_*` on `Hₙ(F; k)` have the same determinant.
* `TauCeti.MappingTorus.finrank_cohomology_one_eq_one_iff`: `dim H¹(T_φ; k) = 1` if and only if
  `det (𝟙 - φ^*) ≠ 0` on `H¹(F; k)`.

See A. Hatcher, *Algebraic Topology*, Section 2.2, Example 2.48, for the Wang sequence of a
mapping torus, and Sections 3.1 and 3.A for the universal coefficient theorems.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Module

universe w

namespace TauCeti.MappingTorus

section Betti

variable {k : Type w} [Field k] {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F) (n : ℕ)

/-- **The Betti numbers of a mapping torus.** If the homology of the fibre is finite-dimensional
over a field in degrees `n` and `n + 1`, then
`bₙ₊₁(T_φ) = dim ker (𝟙 - φ_*) + dim ker (𝟙 - φ_*)`, with `𝟙 - φ_*` acting on `Hₙ₊₁(F)` and on
`Hₙ(F)` respectively. -/
theorem finrank_homology_succ
    [FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1))]
    [FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology n)] :
    finrank k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1)) =
      finrank k (LinearMap.ker
          (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 1)).hom)) +
        finrank k (LinearMap.ker
          (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom)) := by
  set f := LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 1)).hom
  -- `singularHomologyFunctor` is by definition the homology of the singular chain complex.
  have : Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) (n + 1)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)) := ‹_›
  have : Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj
      (ModuleCat.of k k)).obj (TopCat.of F)) := ‹_›
  have : FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1)) :=
    finite_singularHomology_succ φ (ModuleCat.of k k) n
  have hS := wangKernelShortComplex_shortExact (k := k) φ n
  have h : finrank k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1)) =
      finrank k (((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1)) ⧸ LinearMap.range f) +
        finrank k (LinearMap.ker
          (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom)) :=
    Function.Exact.finrank_eq_add (N := ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1)))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS.exact)
      hS.moduleCat_injective_f hS.moduleCat_surjective_g
  -- The kernel and cokernel of the endomorphism `f` have the same dimension.
  have hq := (LinearMap.range f).finrank_quotient_add_finrank
  have hr := f.finrank_range_add_finrank_ker
  omega

end Betti

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
  -- `H₀(F; k) ≅ k` through the augmentation, and `φ_*` is the identity of `H₀(F)`, so the
  -- kernel of `𝟙 - φ_*` on `H₀(F)` is all of `H₀(F)`, of dimension one.
  have e := (asIso ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k))).toLinearEquiv
  have : FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 0) := e.symm.finiteDimensional
  rw [finrank_homology_succ φ 0, homologyMap_monodromyChainMap_zero, ModuleCat.hom_id, sub_self,
    LinearMap.ker_zero, finrank_top]
  exact congrArg (_ + ·) (e.finrank_eq.trans (finrank_self k))

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

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- **The Wang determinant under flat base change.** If `S` is a flat `R`-algebra and `Hₙ(F; R)` is
free, the determinant of `𝟙 - φ_*` on `Hₙ(F; S)` is the image in `S` of its determinant on
`Hₙ(F; R)`. (When `Hₙ(F; R)` has infinite rank, both determinants are `1` by convention.) This is
`TopCat.det_id_sub_singularHomologyMap_eq_algebraMap` for the monodromy. -/
theorem det_id_sub_homologyMap_monodromyChainMap_eq_algebraMap (R S : Type w) [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] (n : ℕ)
    [Module.Free R ((((singularChainComplexFunctor (ModuleCat.{w} R)).obj
      (ModuleCat.of R R)).obj (TopCat.of F)).homology n)] :
    (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of S S)) n).hom).det =
      algebraMap R S
        (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of R R)) n).hom).det := by
  -- `singularHomologyFunctor` is by definition the homology of the singular chain complex.
  have : Module.Free R (((singularHomologyFunctor (ModuleCat.{w} R) n).obj
    (ModuleCat.of R R)).obj (TopCat.of F)) := ‹_›
  rw [monodromyChainMap_def, monodromyChainMap_def]
  exact TopCat.det_id_sub_singularHomologyMap_eq_algebraMap _ n

end BaseChange

section Integral

variable {F : Type} [TopologicalSpace F] [PathConnectedSpace F] (φ : F ≃ₜ F)
  (k : Type) [Field k] [CharZero k]

/-- **The rational first Betti number of a mapping torus from the integral monodromy**: if
`H₁(F; ℤ)` is free of finite rank, then for every field `k` of characteristic zero, such as `ℚ`
or `ℝ`, `b₁(T_φ; k) = 1` if and only if the integral determinant `det (𝟙 - φ_*)` on `H₁(F; ℤ)` is
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
  have : Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)) := ‹_›
  have : FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 1) :=
    Module.Finite.equiv (TopCat.singularHomologyBaseChangeEquiv ℤ k (TopCat.of F) 1)
  rw [finrank_homology_one_eq_one_iff, det_id_sub_homologyMap_monodromyChainMap_eq_algebraMap φ ℤ k,
    ne_eq, ne_eq, map_eq_zero_iff _ (algebraMap ℤ k).injective_int]

end Integral

section Cohomology

variable {k : Type w} [Field k] {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- **The Wang determinant in cohomology.** Over a field, the determinant of `𝟙 - φ^*` on
`Hⁿ(F; k)` equals the determinant of `𝟙 - φ_*` on `Hₙ(F; k)`: the universal coefficient theorem
identifies `φ^*` with the transpose of `φ_*`. (When `Hₙ(F; k)` is infinite-dimensional, so is
`Hⁿ(F; k)`, and both determinants are `1` by convention.) This is
`TopCat.det_id_sub_singularCohomologyMap` for the monodromy. -/
theorem det_id_sub_singularCohomologyMap_eq (n : ℕ) :
    (LinearMap.id - (TopCat.singularCohomologyMap (R := ModuleCat.of k k) (k := k)
        (M := ModuleCat.of k k) (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F))) n).hom).det =
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom).det :=
  -- Rewriting with `singularHomologyMap_monodromy_eq` would change the module in which `𝟙` and
  -- the determinant are taken, so the right side is transported through `congrArg` instead.
  (TopCat.det_id_sub_singularCohomologyMap (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F))) n).trans
    (congrArg (fun f ↦ (LinearMap.id - f.hom).det)
      (singularHomologyMap_monodromy_eq φ (ModuleCat.of k k) n))

/-- **The first Betti number of a mapping torus in cohomology**: for a path-connected fibre whose
first homology is finite-dimensional over a field, `dim H¹(T_φ) = 1` if and only if
`det (𝟙 - φ^*) ≠ 0` on `H¹(F)`, that is, when `φ^*` fixes no nonzero class of `H¹(F)`. -/
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
