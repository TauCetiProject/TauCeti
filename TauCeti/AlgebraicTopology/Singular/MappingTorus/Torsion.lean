/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Wang
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.LinearAlgebra.FreeModule.CardQuotient
public import TauCeti.LinearAlgebra.Determinant.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Int

/-!
# The torsion of the homology of a mapping torus

Let `φ : F ≃ₜ F` be a homeomorphism and `T_φ` its mapping torus, with singular homology taken
with coefficients in a commutative ring `k`. The Wang sequence

  `Hₙ₊₁(F) ⟶ Hₙ₊₁(F) ⟶ Hₙ₊₁(T_φ) ⟶ Hₙ(F) ⟶ Hₙ(F)`,

with maps `𝟙 - φ_*`, the fibre inclusion and the Wang connecting morphism, identifies the image of
the fibre in `Hₙ₊₁(T_φ)` with the cokernel of `𝟙 - φ_*` on `Hₙ₊₁(F)`
(`TauCeti.MappingTorus.wangCokernelEquiv`).

Suppose `k` is a domain, `Hₙ₊₁(F)` is free of finite rank, `det (𝟙 - φ_*) ≠ 0` on it, and
`Hₙ(F)` is torsion-free. The cokernel of `𝟙 - φ_*` is then killed by `det (𝟙 - φ_*)`, while the
quotient of `Hₙ₊₁(T_φ)` by the image of the fibre embeds in `Hₙ(F)`. Hence the image of the fibre
is exactly the torsion submodule of `Hₙ₊₁(T_φ)`. Over a principal ideal domain its `Nat.card`
equals that of `k ⧸ (det (𝟙 - φ_*))`, and over `ℤ` it is finite of order `|det (𝟙 - φ_*)|`.

In degree one the torsion-freeness hypothesis always holds, since `H₀(F)` is free on the path
components of `F`. When `H₁(F; ℤ)` is free of finite rank, as for a closed orientable surface, and
`φ_*` has no eigenvalue one on it, this computes the torsion subgroup of `H₁(T_φ; ℤ)` as the
cokernel of `1 - φ_*`, and its order as `|det (1 - φ_*)|`.

## Main results

* `TauCeti.MappingTorus.torsion_homology_eq_range_homologyMap_fibreInclusionChainMap`: the
  torsion submodule of `Hₙ₊₁(T_φ)` is the image of the fibre, under the hypotheses above.
* `TauCeti.MappingTorus.card_torsion_homology_eq_card_quotient_span_det`: over a principal ideal
  domain, this torsion submodule has the same `Nat.card` as `k ⧸ (det (𝟙 - φ_*))`.
* `TauCeti.MappingTorus.card_torsion_homology_one_eq_natAbs_det`: the integral Wang
  torsion order, `#(H₁(T_φ; ℤ))_tors = |det (1 - φ_*)|`.

See A. Hatcher, *Algebraic Topology*, Section 2.2, for the Wang sequence of a mapping torus.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

universe w

namespace TauCeti.MappingTorus

variable {k : Type w} [CommRing k] {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- The zeroth homology of the singular chain complex is free on path components.
Mathlib's `singularHomologyFunctor` is the composite of the singular-chain functor with
`HomologicalComplex.homologyFunctor`; evaluating that composite gives this chain-homology
module by definitional equality. -/
instance free_singularChainComplex_homology_zero :
    Module.Free k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 0) :=
  inferInstanceAs (Module.Free k
    (((singularHomologyFunctor (ModuleCat.{w} k) 0).obj (ModuleCat.of k k)).obj (TopCat.of F)))

/-- If `Hₙ(F)` is torsion-free, every torsion class of `Hₙ₊₁(T_φ)` comes from the fibre: the Wang
connecting morphism sends it to a torsion class of `Hₙ(F)`, hence to zero. -/
theorem torsion_homology_le_range_homologyMap_fibreInclusionChainMap (n : ℕ)
    [Module.IsTorsionFree k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology n)] :
    Submodule.torsion k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1)) ≤
      LinearMap.range (homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) (n + 1)).hom := by
  rintro x ⟨a, hax⟩
  rw [range_homologyMap_fibreInclusionChainMap, LinearMap.mem_ker]
  apply (isRegular_iff_mem_nonZeroDivisors.mpr a.2).isSMulRegular
  dsimp only
  rw [smul_zero, ← map_smul, ← Submonoid.smul_def, hax, map_zero]

variable [IsDomain k]

/-- If `Hₙ(F)` is free of finite rank and `det (𝟙 - φ_*) ≠ 0` on it, the image of the fibre in
`Hₙ(T_φ)` is torsion: it is killed by `det (𝟙 - φ_*)`. -/
theorem range_homologyMap_fibreInclusionChainMap_le_torsion_homology (n : ℕ)
    [Module.Free k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology n)]
    [Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology n)]
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom).det ≠ 0) :
    LinearMap.range (homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) n).hom ≤
      Submodule.torsion k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology n) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨⟨_, mem_nonZeroDivisors_of_ne_zero hdet⟩, ?_⟩
  rw [Submonoid.smul_def, ← map_smul, ← LinearMap.mem_ker,
    ker_homologyMap_fibreInclusionChainMap]
  exact LinearMap.det_smul_mem_range _ y

/-- **The torsion of the homology of a mapping torus.** If `Hₙ₊₁(F)` is free of finite rank,
`det (𝟙 - φ_*) ≠ 0` on it and `Hₙ(F)` is torsion-free, the torsion submodule of `Hₙ₊₁(T_φ)` is the
image of the fibre, which `wangCokernelEquiv` identifies with the cokernel of `𝟙 - φ_*`. -/
theorem torsion_homology_eq_range_homologyMap_fibreInclusionChainMap (n : ℕ)
    [Module.Free k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1))]
    [Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1))]
    [Module.IsTorsionFree k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology n)]
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 1)).hom).det ≠ 0) :
    Submodule.torsion k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1)) =
      LinearMap.range (homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) (n + 1)).hom :=
  (torsion_homology_le_range_homologyMap_fibreInclusionChainMap φ n).antisymm
    (range_homologyMap_fibreInclusionChainMap_le_torsion_homology φ (n + 1) hdet)

/-- **The order of the torsion of the homology of a mapping torus** over a principal ideal domain:
under the hypotheses of `torsion_homology_eq_range_homologyMap_fibreInclusionChainMap`, the
torsion submodule of `Hₙ₊₁(T_φ)` has the same `Nat.card` as `k ⧸ (det (𝟙 - φ_*))`. Both sides
are `0` when these modules are infinite. -/
theorem card_torsion_homology_eq_card_quotient_span_det [IsPrincipalIdealRing k] (n : ℕ)
    [Module.Free k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1))]
    [Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1))]
    [Module.IsTorsionFree k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology n)]
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 1)).hom).det ≠ 0) :
    Nat.card (Submodule.torsion k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1))) =
      Nat.card (k ⧸ Ideal.span {(LinearMap.id -
        (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 1)).hom).det}) := by
  rw [torsion_homology_eq_range_homologyMap_fibreInclusionChainMap φ n hdet,
    ← Nat.card_congr (wangCokernelEquiv φ (n + 1)).toEquiv,
    LinearMap.card_quotient_range_eq_card_quotient_span_det hdet]

/-- In degree one, the torsion of `H₁(T_φ)` is the image of the fibre whenever `H₁(F)` is free of
finite rank and `det (𝟙 - φ_*) ≠ 0` on it; no hypothesis on `H₀(F)` is needed, since it is free. -/
theorem torsion_homology_one_eq_range_homologyMap_fibreInclusionChainMap
    [Module.Free k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)]
    [Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)]
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0) :
    Submodule.torsion k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology 1) =
      LinearMap.range (homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) 1).hom :=
  torsion_homology_eq_range_homologyMap_fibreInclusionChainMap φ 0 hdet

/-- **The integral Wang torsion order.** If `H₁(F; ℤ)` is free of finite rank and
`det (1 - φ_*) ≠ 0` on it, the torsion subgroup of `H₁(T_φ; ℤ)` has order `|det (1 - φ_*)|`. -/
theorem card_torsion_homology_one_eq_natAbs_det {F : Type} [TopologicalSpace F]
    (φ : F ≃ₜ F)
    [Module.Free ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
    [Module.Finite ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    Nat.card (Submodule.torsion ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (MappingTorus φ))).homology 1)) =
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det.natAbs := by
  rw [card_torsion_homology_eq_card_quotient_span_det φ 0 hdet, ← Int.span_natAbs,
    Int.card_ideal_quot]

end TauCeti.MappingTorus
