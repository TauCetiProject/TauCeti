/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Valuation.ValuationRing
public import TauCeti.LinearAlgebra.TensorProduct.Tower
public import TauCeti.RingTheory.Grassmannian.Basic

/-!
# Points of the Grassmannian over a valuation ring

Let `M` be a module over a commutative ring `R`, let `V` be a valuation ring which is an
`R`-algebra, and let `K` be its field of fractions. This file proves that, when `V ⊗[R] M` is a
finite `V`-module (for instance when `M` is a finite `R`-module), every point
`N ∈ G(k, K ⊗[R] M; K)` is the base change of a point of `G(k, V ⊗[R] M; V)`
(`Module.Grassmannian.exists_map_eq_of_valuationRing`). Together with uniqueness, which holds over
every domain (`Module.Grassmannian.map_injective`), this is the algebraic content of the
valuative criterion of properness for the Grassmannian scheme.

## Main results

* `Module.Grassmannian.exists_map_eq_of_valuationRing`: for `V ⊗[R] M` finite, every point over
  the fraction field of a valuation ring is the base change of a point over the valuation ring.

## References

* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
* [The Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539), for flatness of
  torsion-free modules over valuation rings.
-/

public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
  {V K : Type w} [CommRing V] [Field K] [Algebra R V] [Algebra R K] [Algebra V K]
  [IsScalarTower R V K]

section Saturation

variable (V) in
/-- The vectors of `V ⊗[R] M` whose image in `K ⊗[R] M` lies in `N`. -/
private def saturation (N : G(k, K ⊗[R] M; K)) : Submodule V (V ⊗[R] M) :=
  (N.toSubmodule.restrictScalars V).comap
    (AlgebraTensorModule.rTensor R M (Algebra.linearMap V K))

variable [IsFractionRing V K]

/-- For `t` a nonzero element of `V`, `t • x` lies in the saturation exactly when `x` does. -/
private theorem smul_mem_saturation_iff {N : G(k, K ⊗[R] M; K)} {x : V ⊗[R] M}
    {t : V} (ht : t ∈ nonZeroDivisors V) : t • x ∈ saturation V N ↔ x ∈ saturation V N := by
  simpa only [saturation, Submodule.mem_comap, Submodule.restrictScalars_mem, map_smul,
    Submonoid.smul_def] using
    (IsLocalization.smul_mem_iff (S := nonZeroDivisors V) (s := ⟨t, ht⟩)
      (N' := N.toSubmodule))

/-- The base change of the saturation of `N` to `K` is `N`. -/
private theorem ker_baseChangeMkQ_saturation (N : G(k, K ⊗[R] M; K)) :
    LinearMap.ker (baseChangeMkQ K (saturation V N)) = N.toSubmodule := by
  -- Localizing the inverse image recovers every submodule over the localization.
  rw [ker_baseChangeMkQ]
  have hmap : ⇑(AlgebraTensorModule.rTensor R M (Algebra.linearMap V K)) =
      ⇑((IsScalarTower.toAlgHom R V K).toLinearMap.rTensor M) :=
    funext fun x ↦ AlgebraTensorModule.rTensor_linearMap_apply x
  simpa only [saturation, Submodule.localized'_eq_span, hmap] using
    (Submodule.localized'gi K (nonZeroDivisors V)
      (AlgebraTensorModule.rTensor R M (Algebra.linearMap V K))).l_u_eq N.toSubmodule

/-- The quotient by the saturation is torsion-free. -/
private theorem torsion_quotient_saturation (N : G(k, K ⊗[R] M; K)) :
    Submodule.torsion V ((V ⊗[R] M) ⧸ saturation V N) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun q hq ↦ ?_
  obtain ⟨⟨t, ht⟩, htq⟩ := (Submodule.mem_torsion_iff q).mp hq
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at htq
  exact (Submodule.Quotient.mk_eq_zero _).mpr ((smul_mem_saturation_iff ht).mp htq)

end Saturation

variable [IsDomain V] [ValuationRing V] [IsFractionRing V K]

/-- **Points over the fraction field of a valuation ring extend.** Let `V` be a valuation ring
with field of fractions `K` such that `V ⊗[R] M` is a finite `V`-module. Every point
`N ∈ G(k, K ⊗[R] M; K)` is the base change of a point of `G(k, V ⊗[R] M; V)`. -/
theorem exists_map_eq_of_valuationRing [Module.Finite V (V ⊗[R] M)] (N : G(k, K ⊗[R] M; K)) :
    ∃ N₀ : G(k, V ⊗[R] M; V), map (IsScalarTower.toAlgHom R V K) N₀ = N := by
  let Q := (V ⊗[R] M) ⧸ saturation V N
  have : Module.Flat V Q :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr (torsion_quotient_saturation N)
  have : Module.Free V Q := Module.free_of_flat_of_isLocalRing
  -- the base change of `Q` to `K` is the quotient by `N`
  let e : ((K ⊗[R] M) ⧸ N.toSubmodule) ≃ₗ[K] K ⊗[V] Q :=
    Submodule.quotEquivOfEq _ _ (ker_baseChangeMkQ_saturation N).symm ≪≫ₗ
      baseChangeMkQEquiv (saturation V N)
  have hrank (p : PrimeSpectrum V) : rankAtStalk (R := V) Q p = k := by
    -- the rank of the free module `Q` is constant, so it is read off at the generic point
    let p₀ : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
    have hconst : rankAtStalk (R := V) Q p = rankAtStalk (R := V) Q
        (PrimeSpectrum.comap (algebraMap V K) p₀) := by
      simp
    rw [hconst, ← rankAtStalk_baseChange, ← rankAtStalk_eq_of_equiv e]
    exact N.rankAtStalk_eq p₀
  refine ⟨{ toSubmodule := saturation V N
            finite_quotient := inferInstance
            projective_quotient := inferInstance
            rankAtStalk_eq := hrank }, ?_⟩
  ext : 1
  rw [map_toAlgHom_toSubmodule]
  exact ker_baseChangeMkQ_saturation N

end Module.Grassmannian
