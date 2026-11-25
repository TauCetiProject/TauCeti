/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.Jacobian.Locus
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.Flat
import TauCeti.RingTheory.FittingIdeal.KaehlerDifferential
import TauCeti.RingTheory.Kaehler.UnramifiedBase

/-!
# The exponent of an étale local node chart

Let `S` be an `R`-algebra and `q` a prime of `S` in the singular locus
`Sing = Spec S ⧸ Fitt₁(Ω[S⁄R])`. The ideal of `R` cut out at `q` by the singular locus is the
kernel of `R → 𝒪_{Sing, q}`, which is

  `((Fitt₁(Ω[S⁄R])).map (S → S_q)).comap (R → S_q)`.

It depends only on `S` and `q`. This file shows that it can be read off from any étale local
chart of `S` at `q` in the shape of the local normal form of a node: if an étale neighbourhood
`T` of `q` maps étale to the node chart `R'[u, v] ⧸ (uv - a)` over a local, formally unramified
and faithfully flat extension `R'` of `R`, sending the point above `q` to the origin over the
closed point of `R'`, then the ideal is `(a)`.

Over a discrete valuation ring `R` with uniformizer `π`, the local normal form gives such charts
with `a = 0` or `a = πⁿ` and `n > 0`
(`Algebra.Presentation.exists_etale_nodeAlgebra_hom_of_isDiscreteValuationRing`). The ideals
`(πⁿ)` are pairwise distinct and nonzero, so the exponent `n`, and whether `a = 0`, is an
invariant of the point `q`: every étale local chart of `S` at `q` has the same exponent.
The chart `R[u, v] ⧸ (uv - πⁿ)` itself has exponent `n` at its origin. Over a ramified extension
`R''` with uniformizer `ϖ` and `π = ϖ²`, which the local normal form excludes, its base change
is the chart `uv = ϖ²ⁿ` of exponent `2n`, so the exponent is attached to the étale chart and
changes under ramified base change.

The proof computes the ideal on the chart `R'[u, v] ⧸ (uv - a)` itself, whose singular locus is
`R' ⧸ (a)` (`TauCeti.NodeAlgebra.jacobianQuotientEquiv`), and transports it along the étale
maps. The first Fitting ideal of the differentials is compatible with formally étale maps of
the source and with formally unramified changes of the base, and the local homomorphisms
between the localizations are faithfully flat, so the ideal does not change.

## Main results

* `TauCeti.NodeAlgebra.comap_map_fittingIdeal_localization_eq_span`: on the chart
  `R[u, v] ⧸ (uv - a)` over a local ring `R`, at a point of the singular locus over the closed
  point, the ideal is `(a)`.
* `TauCeti.NodeAlgebra.comap_map_fittingIdeal_localization_eq_span_of_etale`: the same ideal for
  an algebra with an étale local node chart.
* `TauCeti.NodeAlgebra.comap_map_fittingIdeal_localization_eq_span_pow_iff`: for an étale local
  chart `uv = πⁿ` with `π` a nonzero nonunit, `n` is the unique `m` for which the ideal is
  `(πᵐ)`; so all such charts at the same point have the same exponent.

## References

* [Stacks Project, Lemma 55.14.2, Tag 0CDD](https://stacks.math.columbia.edu/tag/0CDD): the
  étale local structure of a node over a discrete valuation ring.
-/

public section

noncomputable section

open IsLocalRing

namespace TauCeti.NodeAlgebra

variable {R : Type*} [CommRing R]

/-- On the node chart `R[u, v] ⧸ (uv - a)` over a local ring `R`, at a point `P` of the singular
locus lying over the closed point, the ideal of `R` cut out by the singular locus is `(a)`. -/
theorem comap_map_fittingIdeal_localization_eq_span [IsLocalRing R] (a : R)
    (P : Ideal (NodeAlgebra R a)) [P.IsPrime]
    (hP : fittingIdeal (NodeAlgebra R a) Ω[NodeAlgebra R a⁄R] 1 ≤ P)
    (hPR : P.comap (algebraMap R (NodeAlgebra R a)) = maximalIdeal R) :
    ((fittingIdeal (NodeAlgebra R a) Ω[NodeAlgebra R a⁄R] 1).map
        (algebraMap (NodeAlgebra R a) (Localization.AtPrime P))).comap
      (algebraMap R (Localization.AtPrime P)) = Ideal.span {a} := by
  rw [fittingIdeal_differential_one, ← jacobianIdeal_def] at hP ⊢
  -- Elements outside `P` evaluate to units of `R ⧸ (a)` at the origin.
  have hunit {x : NodeAlgebra R a} (hx : x ∉ P) : IsUnit (evalZero a x) := by
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (evalZero a x)
    have hcx : x - algebraMap R _ c ∈ P := hP <| by
      rw [jacobianIdeal_eq_ker_evalZero, RingHom.mem_ker]
      simp [← hc, Ideal.Quotient.algebraMap_eq]
    have hc' : c ∉ maximalIdeal R := fun h ↦ by
      have hcP : algebraMap R _ c ∈ P := by rwa [← Ideal.mem_comap, hPR]
      exact hx <| by simpa using P.add_mem hcx hcP
    rw [← hc]
    exact (IsLocalRing.notMem_maximalIdeal.mp hc').map _
  apply le_antisymm
  · intro r hr
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R (NodeAlgebra R a),
      IsLocalization.mem_map_algebraMap_iff P.primeCompl] at hr
    obtain ⟨⟨⟨j, hj⟩, ⟨s, hs⟩⟩, h⟩ := hr
    rw [← map_mul, IsLocalization.eq_iff_exists P.primeCompl] at h
    obtain ⟨⟨t, ht⟩, h⟩ := h
    have h := congrArg (evalZero a) h
    rw [jacobianIdeal_eq_ker_evalZero, RingHom.mem_ker] at hj
    simp only [map_mul, AlgHom.commutes, Ideal.Quotient.algebraMap_eq] at h
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hj
    rw [hj, mul_zero, (hunit ht).mul_right_eq_zero, (hunit hs).mul_left_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact h
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap,
      IsScalarTower.algebraMap_apply R (NodeAlgebra R a)]
    refine Ideal.mem_map_of_mem _ ?_
    rw [← coord_zero_mul_coord_one]
    exact Ideal.mul_mem_right _ _ (coord_mem_jacobianIdeal a 0)

/-- **The singular locus at a point with an étale local node chart.** Let `R'` be a local,
formally unramified and faithfully flat `R`-algebra, let `T` be a flat, formally étale
`S`-algebra which is also an `R'`-algebra, and let `φ : R'[u, v] ⧸ (uv - a) → T` be a flat,
formally étale `R'`-algebra map for some `a ∈ R`. If a prime `Q` of `T` lies over the closed point
of `R'` and contains the images of both coordinates, then the ideal of `R` cut out by the singular
locus of `S` at the prime `q = Q ∩ S` is `(a)`. -/
theorem comap_map_fittingIdeal_localization_eq_span_of_etale {R' S T : Type*} [CommRing R']
    [CommRing S] [CommRing T] [Algebra R R'] [Algebra.FormallyUnramified R R']
    [Module.FaithfullyFlat R R'] [IsLocalRing R'] [Algebra R S] [Module.Finite S Ω[S⁄R]]
    [Algebra S T] [Algebra.FormallyEtale S T] [Module.Flat S T] [Algebra R' T] [Algebra R T]
    [IsScalarTower R S T] [IsScalarTower R R' T] (a : R)
    (φ : NodeAlgebra R' (algebraMap R R' a) →ₐ[R'] T) (hφ : φ.toRingHom.FormallyEtale)
    (hφ' : φ.toRingHom.Flat) (Q : Ideal T) [Q.IsPrime]
    (hQ : Q.comap (algebraMap R' T) = maximalIdeal R')
    (h₀ : φ (coord _ 0) ∈ Q) (h₁ : φ (coord _ 1) ∈ Q) (q : Ideal S) [q.IsPrime]
    (hqQ : q = Q.comap (algebraMap S T)) :
    ((fittingIdeal S Ω[S⁄R] 1).map (algebraMap S (Localization.AtPrime q))).comap
      (algebraMap R (Localization.AtPrime q)) = Ideal.span {a} := by
  subst hqQ
  set N := NodeAlgebra R' (algebraMap R R' a)
  -- Move from `S` at `q` to `T` at `Q`, along the formally étale and flat map `S → T`.
  have : Module.Finite T Ω[T⁄R] :=
    .equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T)
  rw [comap_map_fittingIdeal_localization_comap_eq]
  -- Over the formally unramified extension `R'`, the differentials of `T` do not change.
  have : Module.Finite T Ω[T⁄R'] :=
    .equiv (KaehlerDifferential.equivOfFormallyUnramifiedBase R R' T)
  rw [fittingIdeal_congr (KaehlerDifferential.equivOfFormallyUnramifiedBase R R' T) 1,
    IsScalarTower.algebraMap_eq R R' (Localization.AtPrime Q), ← Ideal.comap_comap]
  -- Move from `T` at `Q` to the chart at `P = Q ∩ N`, along the formally étale and flat `φ`.
  let : Algebra N T := φ.toRingHom.toAlgebra
  have : IsScalarTower R' N T := .of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  have : Algebra.FormallyEtale N T := hφ
  have : Module.Flat N T := hφ'
  have hP : fittingIdeal N Ω[N⁄R'] 1 ≤ Q.comap (algebraMap N T) := by
    rw [fittingIdeal_differential_one, Ideal.span_le]
    rintro _ (rfl | rfl)
    exacts [h₀, h₁]
  have hPR : (Q.comap (algebraMap N T)).comap (algebraMap R' N) = maximalIdeal R' := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, hQ]
  rw [← comap_map_fittingIdeal_localization_comap_eq (S := N),
    comap_map_fittingIdeal_localization_eq_span _ _ hP hPR,
    ← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_eq_self_of_faithfullyFlat]

/-- **The exponent of an étale local node chart is an invariant of the point.** Let `π` be a
nonzero nonunit of a domain `R`. Suppose that `S` has at the prime `q = Q ∩ S` an étale local
chart `uv = πⁿ` over `R'`, as in `comap_map_fittingIdeal_localization_eq_span_of_etale`. Then `n`
is the unique `m` such that the singular locus of `S` cuts out the ideal `(πᵐ)` of `R` at `q`. In
particular, any two such charts of `S` at `q`, over possibly different extensions `R'`, have the
same exponent. -/
theorem comap_map_fittingIdeal_localization_eq_span_pow_iff [IsDomain R] {π : R}
    (hπ₀ : π ≠ 0) (hπ : ¬IsUnit π) {R' S T : Type*} [CommRing R'] [CommRing S] [CommRing T]
    [Algebra R R'] [Algebra.FormallyUnramified R R'] [Module.FaithfullyFlat R R'] [IsLocalRing R']
    [Algebra R S]
    [Module.Finite S Ω[S⁄R]] [Algebra S T] [Algebra.FormallyEtale S T] [Module.Flat S T]
    [Algebra R' T] [Algebra R T] [IsScalarTower R S T] [IsScalarTower R R' T] (n : ℕ)
    (φ : NodeAlgebra R' (algebraMap R R' π ^ n) →ₐ[R'] T) (hφ : φ.toRingHom.FormallyEtale)
    (hφ' : φ.toRingHom.Flat) (Q : Ideal T) [Q.IsPrime]
    (hQ : Q.comap (algebraMap R' T) = maximalIdeal R')
    (h₀ : φ (coord _ 0) ∈ Q) (h₁ : φ (coord _ 1) ∈ Q) (q : Ideal S) [q.IsPrime]
    (hqQ : q = Q.comap (algebraMap S T)) (m : ℕ) :
    ((fittingIdeal S Ω[S⁄R] 1).map (algebraMap S (Localization.AtPrime q))).comap
      (algebraMap R (Localization.AtPrime q)) = Ideal.span {π ^ m} ↔
      n = m := by
  generalize hb : algebraMap R R' π ^ n = b at φ h₀ h₁
  rw [← map_pow] at hb
  subst hb
  rw [comap_map_fittingIdeal_localization_eq_span_of_etale (π ^ n) φ hφ hφ' Q hQ h₀ h₁ q hqQ]
  refine ⟨fun h ↦ le_antisymm ?_ ?_, fun h ↦ h ▸ rfl⟩
  · rw [← pow_dvd_pow_iff hπ₀ hπ, ← Ideal.span_singleton_le_span_singleton]
    exact h.ge
  · rw [← pow_dvd_pow_iff hπ₀ hπ, ← Ideal.span_singleton_le_span_singleton]
    exact h.le

end TauCeti.NodeAlgebra
