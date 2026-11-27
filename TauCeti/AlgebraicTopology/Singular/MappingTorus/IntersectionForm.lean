/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.CupPairing
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.CircleProduct
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.QuadraticForm.Signature

import TauCeti.LinearAlgebra.BilinearForm.HyperbolicPair

/-!
# The intersection form of `(ℝ / pℤ) × Y_φ` has `b₂⁺ = b₂⁻ = 1`

Let `F` be a closed connected oriented surface and `φ : F ≃ₜ F` a homeomorphism with
`det (1 - φ_*) ≠ 0` on `H₁(F; ℤ)`, so that the mapping torus `Y_φ` has `b₁(Y_φ) = 1`. Let `v` be a
class of `H²(Y_φ; ℤ)` pairing to one with the fibre class `i_*[F]`, and `[dt] ∈ H¹(Y_φ; ℤ)` the
base class, which generates `H¹(Y_φ; ℤ)` (`TauCeti.MappingTorus.exists_eq_zsmul_baseClass`). The
fundamental class of `Y_φ` is taken from a closed oriented three-manifold `N` homeomorphic to it by
`g : N ≃ₜ Y_φ`, as `[Y_φ] = g_*[N]_ℤ` with chain coefficients `ℤ`
(`TauCeti.HomologicalOrientation.intFundamentalClass`); for a diffeomorphism `φ` of a smooth
surface, `N` can be the smooth mapping torus of `φ⁻¹`
(`TauCeti.SmoothMappingTorus.homeomorphMappingTorus`).

By Poincaré duality on `N`
(`TauCeti.HomologicalOrientation.exists_forall_singularCupPairing_eq_singularKronecker`) the
fibre class has a dual class `a` with `⟨a ⌣ w, [Y_φ]⟩ = ⟨w, i_*[F]⟩` for every `w ∈ H²(Y_φ; ℤ)`.
Writing `a = k [dt]` gives `k ⟨v ⌣ [dt], [Y_φ]⟩ = ⟨v, i_*[F]⟩ = 1`, hence

`⟨v ⌣ [dt], [Y_φ]⟩ = ±1`

(`TauCeti.MappingTorus.singularCupPairing_baseClass_eq_one_or_eq_neg_one`); the sign depends on
the orientations. So the generator `a = ±[dt]` of `H¹(Y_φ; ℤ)` satisfies `⟨v ⌣ a, [Y_φ]⟩ = 1`
(`TauCeti.MappingTorus.exists_forall_eq_zsmul_and_singularCupPairing_eq_one`).

On `X = (ℝ / pℤ) × Y_φ`, with the cup pairing on `[ℝ / pℤ] × [Y_φ]`, the classes `pr₂^* v` and
`t = θ_p ⌣ pr₂^* a` therefore form a hyperbolic pair: `v · v = t · t = 0`
(`TopCat.singularCupPairing_snd_snd_addCircle_singularHomologyCross`,
`TopCat.singularCupPairing_fst_snd_fst_snd_addCircle_singularHomologyCross`) and
`v · t = t · v = ⟨v ⌣ a, [Y_φ]⟩ = 1`
(`TopCat.singularCupPairing_snd_fst_snd_addCircle_singularHomologyCross`,
`TopCat.singularCupPairing_fst_snd_snd_addCircle_singularHomologyCross`). They span `H²(X; ℤ)`
modulo torsion (`TauCeti.MappingTorus.exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd`),
so the real extension of the pairing has both indices of inertia equal to one
(`TauCeti.MappingTorus.sigPos_eq_one_and_sigNeg_eq_one_singularCupPairing_addCircleProd`). For
`p = 1` and the symplectic suspension `X = (ℝ / ℤ)_s × Y_φ` of an area-preserving `φ`, with
`ℝ ⊗[ℤ] H²(X; ℤ) = H²(X; ℝ)` and `[ℝ / ℤ] × [Y_φ]` the fundamental class of `X` (neither is proved
here), this says `b₂⁺(X) = b₂⁻(X) = 1`. The evenness of the pairing
(`TopCat.even_singularCupPairing_self_addCircle_singularHomologyCross`) excludes classes of
square `-1`.

## Main results

* `TauCeti.MappingTorus.singularCupPairing_baseClass_eq_one_or_eq_neg_one`:
  `⟨v ⌣ [dt], [Y_φ]⟩ = ±1`.
* `TauCeti.MappingTorus.exists_forall_eq_zsmul_and_singularCupPairing_eq_one`: a generator `a` of
  `H¹(Y_φ; ℤ)` with `⟨v ⌣ a, [Y_φ]⟩ = 1`.
* `TauCeti.MappingTorus.sigPos_eq_one_and_sigNeg_eq_one_singularCupPairing_addCircleProd`: the cup
  pairing on `H²((ℝ / pℤ) × Y_φ; ℤ)` against `[ℝ / pℤ] × [Y_φ]` has `b₂⁺ = b₂⁻ = 1`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 3.30 (Poincaré duality) and Example 2.48 (the Wang sequence of a mapping torus).
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127–158.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex Module
open scoped TensorProduct

attribute [local instance 1100] ModuleCat.instLinear

namespace TauCeti.MappingTorus

variable {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F)
  [Module.Free ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
  [Module.Finite ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
  {E : Type} [T2Space F] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E F] [CompactSpace F] [ConnectedSpace F]
  (o : HomologicalOrientation F E 2) (hn : finrank ℝ E = 2)
  {N E' : Type} [TopologicalSpace N] [T2Space N] [CompactSpace N] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' N]
  (o' : HomologicalOrientation N E' 3) (hn' : finrank ℝ E' = 3) (g : N ≃ₜ MappingTorus φ)

/-- **`v ⌣ [dt]` evaluates to `±1` on the fundamental class.** Let `φ` be a homeomorphism
of a closed connected oriented surface `F` with `det (1 - φ_*) ≠ 0` on `H₁(F; ℤ)`, and `v` a class
of `H²(Y_φ; ℤ)` pairing to one with the fibre class `i_*[F]`. For the fundamental class
`[Y_φ] = g_*[N]_ℤ` carried by a homeomorphism `g : N ≃ₜ Y_φ` from a closed oriented
three-manifold, `⟨v ⌣ [dt], [Y_φ]⟩ = ±1`. -/
theorem singularCupPairing_baseClass_eq_one_or_eq_neg_one
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    {v : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℤ) 2}
    (hv : o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) (incl φ)
      ((TopCat.of (MappingTorus φ)).singularCohomologyChainCoefficientMap ℤ (ModuleCat.of ℤ ℤ)
        uliftIntIso.hom 2 v) = 1) :
    (TopCat.of (MappingTorus φ)).singularCupPairing ℤ (p := 2) (q := 1) (n := 3) rfl
        ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 3).obj (𝟙_ (ModuleCat.{0} ℤ))).map
          (TopCat.ofHom ⟨g, g.continuous⟩)).hom
          (o'.intFundamentalClass hn'))
        v (baseClass φ) = 1 ∨
      (TopCat.of (MappingTorus φ)).singularCupPairing ℤ (p := 2) (q := 1) (n := 3) rfl
        ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 3).obj (𝟙_ (ModuleCat.{0} ℤ))).map
          (TopCat.ofHom ⟨g, g.continuous⟩)).hom
          (o'.intFundamentalClass hn'))
        v (baseClass φ) = -1 := by
  have := ChartedSpace.locallyPathConnectedSpace E F
  have : PathConnectedSpace F := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  set G : TopCat.of N ⟶ TopCat.of (MappingTorus φ) := TopCat.ofHom ⟨g, g.continuous⟩
  have : IsIso G := (TopCat.isoOfHomeo (X := TopCat.of N) (Y := TopCat.of (MappingTorus φ))
    g).isIso_hom
  -- The fibre class `i_*[F]` with chain coefficients `ℤ`, on which `v` evaluates to one.
  set x := (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).map uliftIntIso.hom).app
    (TopCat.of (MappingTorus φ))).hom (o.mapFundamentalClass hn (incl φ))
  have hvx : ((TopCat.of (MappingTorus φ)).singularKronecker ℤ 2 v).hom x = 1 :=
    (o.evalFundamentalClass_singularCohomologyChainCoefficientMap_eq_singularKronecker hn (incl φ)
      v).symm.trans hv
  obtain ⟨xN, hxN⟩ := (ConcreteCategory.bijective_of_isIso
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (𝟙_ (ModuleCat.{0} ℤ))).map G)).2 x
  obtain ⟨α, hα⟩ := o'.exists_forall_singularCupPairing_eq_singularKronecker hn'
    (p := 1) (q := 2) rfl xN
  have : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{0} ℤ)) (k := ℤ)
      (M := 𝟙_ (ModuleCat.{0} ℤ)) G 1) :=
    (TauCeti.singularCohomologyFunctor (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 1).map_isIso
      G.op
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso
    (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{0} ℤ)) (k := ℤ)
      (M := 𝟙_ (ModuleCat.{0} ℤ)) G 1)).2 α
  -- `⟨a ⌣ v, g_*[N]⟩ = ⟨g^* a ⌣ g^* v, [N]⟩ = ⟨g^* v, x_N⟩ = ⟨v, x⟩ = 1`.
  have h₁ : (TopCat.of (MappingTorus φ)).singularCupPairing ℤ (p := 1) (q := 2) (n := 3) rfl
      ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 3).obj (𝟙_ (ModuleCat.{0} ℤ))).map G).hom
        (o'.intFundamentalClass hn')) a v = 1 := by
    rw [← TopCat.singularCupPairing_naturality, ha, hα, TopCat.singularKronecker_naturality,
      ModuleCat.hom_comp, LinearMap.comp_apply, hxN, hvx]
  have h₂ := TopCat.singularCupPairing_gradedComm (TopCat.of (MappingTorus φ)) ℤ
    (p := 1) (q := 2) (n := 3) rfl rfl
    ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 3).obj (𝟙_ (ModuleCat.{0} ℤ))).map G).hom
        (o'.intFundamentalClass hn')) a v
  rw [h₁, mul_one, show (-1 : ℤ) ^ (1 * 2) = 1 by norm_num] at h₂
  obtain ⟨k, rfl⟩ := exists_eq_zsmul_baseClass φ hdet a
  rw [LinearMap.map_smul_of_tower, smul_eq_mul] at h₂
  exact Int.eq_one_or_neg_one_of_mul_eq_one ((mul_comm _ _).trans h₂)

/-- **The partner of `v` in `H¹(Y_φ; ℤ)`.** Under the hypotheses of
`TauCeti.MappingTorus.singularCupPairing_baseClass_eq_one_or_eq_neg_one`, there is a generator `a`
of `H¹(Y_φ; ℤ)`, one of `±[dt]`, with `⟨v ⌣ a, [Y_φ]⟩ = 1`. With `t = θ_p ⌣ pr₂^* a`, the classes
`pr₂^* v` and `t` are then a hyperbolic pair of the cup pairing on `(ℝ / pℤ) × Y_φ` against
`[ℝ / pℤ] × [Y_φ]`. -/
theorem exists_forall_eq_zsmul_and_singularCupPairing_eq_one
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    {v : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℤ) 2}
    (hv : o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) (incl φ)
      ((TopCat.of (MappingTorus φ)).singularCohomologyChainCoefficientMap ℤ (ModuleCat.of ℤ ℤ)
        uliftIntIso.hom 2 v) = 1) :
    ∃ a : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
        (ModuleCat.of ℤ ℤ) 1, (∀ c, ∃ m : ℤ, c = m • a) ∧
      (TopCat.of (MappingTorus φ)).singularCupPairing ℤ (p := 2) (q := 1) (n := 3) rfl
        ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 3).obj (𝟙_ (ModuleCat.{0} ℤ))).map
          (TopCat.ofHom ⟨g, g.continuous⟩)).hom
          (o'.intFundamentalClass hn')) v a = 1 := by
  have := ChartedSpace.locallyPathConnectedSpace E F
  have : PathConnectedSpace F := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  obtain ⟨ε, hε, hεε⟩ : ∃ ε : ℤ, (TopCat.of (MappingTorus φ)).singularCupPairing ℤ (p := 2)
      (q := 1) (n := 3) rfl
        ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 3).obj (𝟙_ (ModuleCat.{0} ℤ))).map
          (TopCat.ofHom ⟨g, g.continuous⟩)).hom
          (o'.intFundamentalClass hn')) v (baseClass φ) = ε ∧ ε * ε = 1 := by
    rcases singularCupPairing_baseClass_eq_one_or_eq_neg_one φ o hn o' hn' g hdet hv with h | h
    exacts [⟨1, h, rfl⟩, ⟨-1, h, rfl⟩]
  refine ⟨ε • baseClass φ, fun c ↦ ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := exists_eq_zsmul_baseClass φ hdet c
    exact ⟨m * ε, by rw [smul_smul, mul_assoc, hεε, mul_one]⟩
  · rw [LinearMap.map_smul_of_tower, smul_eq_mul, hε, hεε]

/-- **`b₂⁺ = b₂⁻ = 1` for `(ℝ / pℤ) × Y_φ`.** Let `φ` be an orientation-preserving homeomorphism
of a closed connected oriented surface with `det (1 - φ_*) ≠ 0` on `H₁(F; ℤ)`, and let
`[Y_φ] = g_*[N]_ℤ` be the fundamental class carried by a homeomorphism `g : N ≃ₜ Y_φ` from a closed
oriented three-manifold. Then the real extension of the cup pairing on
`H²((ℝ / pℤ) × Y_φ; ℤ)` against `[ℝ / pℤ] × [Y_φ]` has positive and negative index of inertia
one. -/
theorem sigPos_eq_one_and_sigNeg_eq_one_singularCupPairing_addCircleProd (p : ℝ) [Fact (0 < p)]
    (hφ : o.mapFundamentalClass hn ⟨φ, φ.continuous⟩ = o.fundamentalClass hn)
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    sigPos (LinearMap.BilinForm.baseChange ℝ
        ((TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCupPairing ℤ
        (p := 2) (q := 2) (n := 4) rfl
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) 4).map (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
          (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ))
          (TopCat.singularHomologyCross (TopCat.of (AddCircle p)) (TopCat.of (MappingTorus φ))
            (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ)) 1 3 4 rfl
            (AddCircle.fundamentalClass p ⊗ₜ
              (((singularHomologyFunctor (ModuleCat.{0} ℤ) 3).obj (𝟙_ (ModuleCat.{0} ℤ))).map
                (TopCat.ofHom ⟨g, g.continuous⟩)).hom
                (o'.intFundamentalClass hn')))))).toQuadraticMap = 1 ∧
      sigNeg (LinearMap.BilinForm.baseChange ℝ
        ((TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCupPairing ℤ
        (p := 2) (q := 2) (n := 4) rfl
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) 4).map (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
          (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ))
          (TopCat.singularHomologyCross (TopCat.of (AddCircle p)) (TopCat.of (MappingTorus φ))
            (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ)) 1 3 4 rfl
            (AddCircle.fundamentalClass p ⊗ₜ
              (((singularHomologyFunctor (ModuleCat.{0} ℤ) 3).obj (𝟙_ (ModuleCat.{0} ℤ))).map
                (TopCat.ofHom ⟨g, g.continuous⟩)).hom
                (o'.intFundamentalClass hn')))))).toQuadraticMap = 1 := by
  -- A class `v` pairing to one with the fibre class, read with chain coefficients `ℤ`.
  obtain ⟨w, hw⟩ := surjective_evalFundamentalClass_incl hφ
    (injective_id_sub_homologyMap_monodromyChainMap_ulift φ hdet) (ModuleCat.of ℤ ℤ) 1
  obtain ⟨v, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((TopCat.of (MappingTorus φ)).singularCohomologyChainCoefficientIso ℤ (ModuleCat.of ℤ ℤ)
      uliftIntIso 2).hom).2 w
  have hv := hw
  rw [TopCat.singularCohomologyChainCoefficientIso_hom] at hv
  obtain ⟨a, ha, hva⟩ :=
    exists_forall_eq_zsmul_and_singularCupPairing_eq_one φ o hn o' hn' g hdet hv
  have hvt := (TopCat.singularCupPairing_snd_fst_snd_addCircle_singularHomologyCross (p := p) _ v
    a).trans hva
  have htv := (TopCat.singularCupPairing_fst_snd_snd_addCircle_singularHomologyCross (p := p) _ v
    a).trans hva
  have hspan := exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd (p := p) φ o hn hφ hdet hv ha
  refine ⟨LinearMap.BilinForm.sigPos_toQuadraticMap_baseChange_eq_one_of_isOfFinAddOrder_span
      ?vv ?tt hvt htv hspan,
    LinearMap.BilinForm.sigNeg_toQuadraticMap_baseChange_eq_one_of_isOfFinAddOrder_span
      ?vv ?tt hvt htv hspan⟩
  exacts [TopCat.singularCupPairing_snd_snd_addCircle_singularHomologyCross _ v v,
    TopCat.singularCupPairing_fst_snd_fst_snd_addCircle_singularHomologyCross _ a a]

end TauCeti.MappingTorus
