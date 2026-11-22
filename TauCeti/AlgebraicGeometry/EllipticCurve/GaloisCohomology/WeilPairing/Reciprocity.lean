/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Archimedean
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula

/-!
# Global reciprocity for the Weil cup product

For a number field `K`, two global classes in `H¹(K, E[m])`, or a pair of global classes in
`H¹(K, E₁[φ])` and `H¹(K, E₂[φ̂])` for an isogeny `φ : E₁ → E₂`, give local classes at every
place. The finite-place terms are their local Tate pairings embedded in `ℚ/ℤ` by `k ↦ k/m`
(respectively `k ↦ k/deg φ`); the archimedean terms are the archimedean Brauer invariants of
their Weil cup product (and for `[m]`-torsion, equivalently the archimedean local Tate pairings
embedded in `ℚ/ℤ` by `k ↦ k/m`). The sum of these terms is zero, both in `ℚ/ℤ` and for
`[m]`-torsion directly in `ZMod m`
(`WeierstrassCurve.finsum_localTateWeilPairing_add_sum_infiniteTateWeilPairing_eq_zero`).
The finite-place pairings vanish at all but finitely many places, so the finite sum over all
finite places is an honest sum rather than the junk value of `finsum` on an infinitely supported
function. The archimedean terms vanish at complex places but need not vanish at real places.

This is the reciprocity input for comparing global Selmer conditions with their orthogonals, in
particular in Cassels' comparison of `Sel_φ(E₁/K)` and `Sel_φ̂(E₂/K)`. It follows by localizing
the Brauer class of the global Weil cup product and applying the Brauer sum formula.

## Main results

* `WeierstrassCurve.finiteInvAt_torsionWeilBrauerPairing`,
  `WeierstrassCurve.infiniteInvAt_torsionWeilBrauerPairing`,
  `WeierstrassCurve.hasFiniteSupport_localTateWeilPairing_torsionRes`,
  `WeierstrassCurve.finsum_toRatAddCircle_localTateWeilPairing_add_sum_infiniteInvMap_eq_zero`,
  and `WeierstrassCurve.finsum_localTateWeilPairing_add_sum_infiniteTateWeilPairing_eq_zero`:
  global reciprocity for `[m]`-torsion.
* `TauCeti.Isogeny.finiteInvAt_kerWeilBrauerPairing`,
  `TauCeti.Isogeny.finite_setOf_localTateKerWeilPairing_kerRes_ne_zero`,
  `TauCeti.Isogeny.hasFiniteSupport_toRatAddCircle_localTateKerWeilPairing_kerRes`,
  `TauCeti.Isogeny.finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteInvMap_eq_zero`,
  `TauCeti.Isogeny.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero`, and
  `TauCeti.Isogeny.sum_ringEquivCongr_localTateKerWeilPairing_eq_zero`:
  global reciprocity for the isogeny Weil cup product on `H¹(K, E₁[φ]) × H¹(K, E₂[φ̂])`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, §§2 and 4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

open IsDedekindDomain NumberField

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic]
  (m : ℕ) (hm : IsUnit (m : K))
  (a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m))

/-- At a finite place, the local invariant of the global Weil cup product is the local Tate
pairing of its restrictions, embedded in `ℚ/ℤ` by `k ↦ k/m`. No prime-to-residue-characteristic
hypothesis is required. -/
theorem finiteInvAt_torsionWeilBrauerPairing (v : HeightOneSpectrum (𝓞 K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :
    finiteInvAt K v (W.torsionWeilBrauerPairing m hm a b) =
      ZMod.toRatAddCircle m
        ((W⁄(v.adicCompletion K)).localTateWeilPairing m
          (by simpa using hm.map (algebraMap K (v.adicCompletion K)))
          (W.torsionRes τ m a) (W.torsionRes τ m b)) := by
  rw [finiteInvAt_apply, W.brBaseChange_torsionWeilBrauerPairing m hm τ]
  exact ((W⁄(v.adicCompletion K)).toRatAddCircle_localTateWeilPairing m _ _ _).symm

omit [NumberField K] in
/-- At an infinite place, the local invariant of the global Weil cup product is the archimedean
local Tate pairing of its restrictions, embedded in `ℚ/ℤ` by `k ↦ k/m`. -/
theorem infiniteInvAt_torsionWeilBrauerPairing (w : InfinitePlace K)
    (τ' : SeparableClosure K →ₐ[K] SeparableClosure w.Completion) :
    have := hm.neZero_natCast
    infiniteInvAt K w (W.torsionWeilBrauerPairing m hm a b) =
      ZMod.toRatAddCircle m
        ((W⁄w.Completion).infiniteTateWeilPairing m
          (W.torsionRes τ' m a) (W.torsionRes τ' m b)) := by
  have := hm.neZero_natCast
  rw [infiniteInvAt_apply, W.brBaseChange_torsionWeilBrauerPairing m hm τ']
  exact ((W⁄w.Completion).toRatAddCircle_infiniteTateWeilPairing m
    (by simpa using hm.map (algebraMap K w.Completion)) _ _).symm

/-- The local Tate pairings of restrictions of two global classes vanish at all but finitely
many finite places. -/
theorem hasFiniteSupport_localTateWeilPairing_torsionRes
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :
    (fun v : HeightOneSpectrum (𝓞 K) ↦
      (W⁄(v.adicCompletion K)).localTateWeilPairing m
        (by simpa using hm.map (algebraMap K (v.adicCompletion K)))
        (W.torsionRes (τ v) m a) (W.torsionRes (τ v) m b)).HasFiniteSupport := by
  have := hm.neZero_natCast
  refine (hasFiniteSupport_finiteInvAt K (W.torsionWeilBrauerPairing m hm a b)).subset ?_
  intro v hv
  rw [Function.mem_support, W.finiteInvAt_torsionWeilBrauerPairing m hm a b v (τ v)]
  exact fun h ↦ hv (ZMod.toRatAddCircle_injective m (h.trans (map_zero _).symm))

/-- **Global reciprocity for the Weil cup product (`ℚ/ℤ` form).** The finite-place local Tate
pairings of two global torsion-cohomology classes, embedded in `ℚ/ℤ` by `k ↦ k/m`, together with
the archimedean Brauer invariants of their Weil cup product, sum to zero.
The finite-place sum has finite support by
`hasFiniteSupport_localTateWeilPairing_torsionRes`. All choices of embeddings of separable
closures are allowed, independently at each place. -/
theorem finsum_toRatAddCircle_localTateWeilPairing_add_sum_infiniteInvMap_eq_zero
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion) :
    (∑ᶠ v : HeightOneSpectrum (𝓞 K), ZMod.toRatAddCircle m
      ((W⁄(v.adicCompletion K)).localTateWeilPairing m
        (by simpa using hm.map (algebraMap K (v.adicCompletion K)))
        (W.torsionRes (τ v) m a) (W.torsionRes (τ v) m b))) +
      ∑ w : InfinitePlace K, infiniteInvMap w
        ((W⁄w.Completion).torsionWeilBrauerPairing m
          (by simpa using hm.map (algebraMap K w.Completion))
          (W.torsionRes (τ' w) m a) (W.torsionRes (τ' w) m b)) = 0 := by
  have hsum := finsum_finiteInvAt_add_sum_infiniteInvAt_eq_zero K
    (W.torsionWeilBrauerPairing m hm a b)
  simp_rw [← W.finiteInvAt_torsionWeilBrauerPairing m hm a b _ (τ _)]
  refine (congrArg _ (Finset.sum_congr rfl fun w _ ↦ ?_)).trans hsum
  rw [infiniteInvAt_apply, W.brBaseChange_torsionWeilBrauerPairing m hm (τ' w)]

/-- **Global reciprocity for the Weil cup product (`ZMod m` form).** For two global classes in
`H¹(K, E[m])`, the finite-place `ZMod m`-valued local Tate pairings and the infinite-place
`ZMod m`-valued archimedean local Tate pairings sum to zero in `ZMod m`. -/
theorem finsum_localTateWeilPairing_add_sum_infiniteTateWeilPairing_eq_zero
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion) :
    have := hm.neZero_natCast
    (∑ᶠ v : HeightOneSpectrum (𝓞 K),
      (W⁄(v.adicCompletion K)).localTateWeilPairing m
        (by simpa using hm.map (algebraMap K (v.adicCompletion K)))
        (W.torsionRes (τ v) m a) (W.torsionRes (τ v) m b)) +
      ∑ w : InfinitePlace K,
        (W⁄w.Completion).infiniteTateWeilPairing m
          (W.torsionRes (τ' w) m a) (W.torsionRes (τ' w) m b) = 0 := by
  have := hm.neZero_natCast
  apply ZMod.toRatAddCircle_injective m
  rw [map_zero, map_add,
    (ZMod.toRatAddCircle m).map_finsum
      (W.hasFiniteSupport_localTateWeilPairing_torsionRes m hm a b τ),
    map_sum]
  convert W.finsum_toRatAddCircle_localTateWeilPairing_add_sum_infiniteInvMap_eq_zero
    m hm a b τ τ' using 2
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  exact (W⁄w.Completion).toRatAddCircle_infiniteTateWeilPairing m
    (by simpa using hm.map (algebraMap K w.Completion)) _ _
end WeierstrassCurve

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open Hom (ofIsogeny kerH1Congr)

variable {K : Type} [Field K] [NumberField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

section

variable
  (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
  (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff)

/-- At a finite place, the local invariant of the global isogeny Weil cup product is the local
Tate pairing of the restricted kernel classes, embedded in `ℚ/ℤ` by `k ↦ k/deg φ`. No
prime-to-residue-characteristic hypothesis is required. -/
theorem finiteInvAt_kerWeilBrauerPairing
    (v : HeightOneSpectrum (𝓞 K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :
    finiteInvAt K v (φ.kerWeilBrauerPairing φ.isUnit_degree a b) =
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K))
          (φ.kerRes τ a)
          (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
            (φ.dual.kerRes τ b))) :=
  (finiteInvAt_apply K v _).trans <|
    (congrArg (invMap (v.adicCompletion K))
      (φ.brBaseChange_kerWeilBrauerPairing φ.isUnit_degree τ a b)).trans <|
    ((φ.baseChange (v.adicCompletion K)).toRatAddCircle_localTateKerWeilPairing _ _ _).symm

/-- The `ℚ/ℤ`-valued local Tate pairings of the restrictions of two global kernel-cohomology
classes have finite support over the finite places of `K`. -/
theorem hasFiniteSupport_toRatAddCircle_localTateKerWeilPairing_kerRes
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :
    (fun v : HeightOneSpectrum (𝓞 K) ↦
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K))
          (φ.kerRes (τ v) a)
          (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
            (φ.dual.kerRes (τ v) b)))).HasFiniteSupport := by
  refine (hasFiniteSupport_finiteInvAt K (φ.kerWeilBrauerPairing φ.isUnit_degree a b)).subset ?_
  intro v hv
  rwa [Function.mem_support, φ.finiteInvAt_kerWeilBrauerPairing a b v (τ v)]

/-- The local Tate pairings of the restrictions of two global kernel-cohomology classes are
nonzero at only finitely many finite places of `K`. -/
theorem finite_setOf_localTateKerWeilPairing_kerRes_ne_zero
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :
    {v : HeightOneSpectrum (𝓞 K) |
      (φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
        (φ.isUnit_degree_baseChange (v.adicCompletion K))
        (φ.kerRes (τ v) a)
        (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
          (φ.dual.kerRes (τ v) b)) ≠ 0}.Finite := by
  refine (φ.hasFiniteSupport_toRatAddCircle_localTateKerWeilPairing_kerRes a b τ).subset ?_
  intro v hv
  rw [Function.mem_support, ne_eq, ZMod.toRatAddCircle_eq_zero]
  exact hv

/-- **Global reciprocity for the isogeny Weil cup product.** For an isogeny `φ : E₁ → E₂` over a
number field `K`, the finite-place local Tate pairings of `a ∈ H¹(K, E₁[φ])` and
`b ∈ H¹(K, E₂[φ̂])`, embedded in `ℚ/ℤ` by `k ↦ k/deg φ`, together with the archimedean Brauer
invariants of their isogeny Weil cup product, sum to zero. The finite-place sum has finite
support by `hasFiniteSupport_toRatAddCircle_localTateKerWeilPairing_kerRes`. All choices of
embeddings of separable closures are allowed, independently at each place. -/
theorem finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteInvMap_eq_zero
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion) :
    (∑ᶠ v : HeightOneSpectrum (𝓞 K),
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K))
          (φ.kerRes (τ v) a)
          (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
            (φ.dual.kerRes (τ v) b)))) +
      ∑ w : InfinitePlace K, infiniteInvMap w
        ((φ.baseChange w.Completion).kerWeilBrauerPairing
          (φ.isUnit_degree_baseChange w.Completion)
          (φ.kerRes (τ' w) a)
          (kerH1Congr (φ.ofIsogeny_dual_baseChange w.Completion)
            (φ.dual.kerRes (τ' w) b))) = 0 := by
  let x := φ.kerWeilBrauerPairing φ.isUnit_degree a b
  have hfin : (∑ᶠ v : HeightOneSpectrum (𝓞 K),
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K))
          (φ.kerRes (τ v) a)
          (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
            (φ.dual.kerRes (τ v) b)))) =
      ∑ᶠ v : HeightOneSpectrum (𝓞 K), finiteInvAt K v x :=
    finsum_congr fun v ↦ (φ.finiteInvAt_kerWeilBrauerPairing a b v (τ v)).symm
  have hinf : (∑ w : InfinitePlace K, infiniteInvMap w
      ((φ.baseChange w.Completion).kerWeilBrauerPairing
        (φ.isUnit_degree_baseChange w.Completion)
        (φ.kerRes (τ' w) a)
        (kerH1Congr (φ.ofIsogeny_dual_baseChange w.Completion)
          (φ.dual.kerRes (τ' w) b)))) =
      ∑ w : InfinitePlace K, infiniteInvAt K w x :=
    Finset.sum_congr rfl fun w _ ↦
      ((infiniteInvAt_apply K w x).trans
        (congrArg (infiniteInvMap w)
          (φ.brBaseChange_kerWeilBrauerPairing φ.isUnit_degree (τ' w) a b))).symm
  exact (congrArg₂ (· + ·) hfin hinf).trans
    (finsum_finiteInvAt_add_sum_infiniteInvAt_eq_zero K x)

end

/-- **Finite-`S` global reciprocity in `ℚ/ℤ`.** Let `S` be a finite set of finite places of `K`.
If `a ∈ H¹(K, E₁[φ])` and `b ∈ H¹(K, E₂[φ̂])` satisfy their respective local Selmer conditions at
every finite place `v ∉ S` and at every real infinite place `w`, then the finite sum over `v ∈ S`
of their `ℚ/ℤ`-valued local Tate pairings is zero. -/
theorem sum_toRatAddCircle_localTateKerWeilPairing_eq_zero
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (hfin : ∀ v ∉ S,
      φ.kerRes (τ v) a ∈
        (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange (v.adicCompletion K))).kerCoeffIncl
          continuous_of_discreteTopology).ker ∧
      φ.dual.kerRes (τ v) b ∈
        (explicitCoeff1 _ _ (ofIsogeny (φ.dual.baseChange (v.adicCompletion K))).kerCoeffIncl
          continuous_of_discreteTopology).ker)
    (hinf : ∀ w : InfinitePlace K, w.IsReal →
      φ.kerRes (τ' w) a ∈
        (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange w.Completion)).kerCoeffIncl
          continuous_of_discreteTopology).ker ∧
      φ.dual.kerRes (τ' w) b ∈
        (explicitCoeff1 _ _ (ofIsogeny (φ.dual.baseChange w.Completion)).kerCoeffIncl
          continuous_of_discreteTopology).ker) :
    ∑ v ∈ S,
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K))
          (φ.kerRes (τ v) a)
          (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
            (φ.dual.kerRes (τ v) b))) = 0 := by
  have hrec := φ.finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteInvMap_eq_zero
    a b τ τ'
  have harch : ∑ w : InfinitePlace K, infiniteInvMap w
      ((φ.baseChange w.Completion).kerWeilBrauerPairing
        (φ.isUnit_degree_baseChange w.Completion)
        (φ.kerRes (τ' w) a)
        (kerH1Congr (φ.ofIsogeny_dual_baseChange w.Completion)
          (φ.dual.kerRes (τ' w) b))) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    exact w.isReal_or_isComplex.elim
      (fun hw ↦ (φ.baseChange w.Completion).infiniteInvMap_kerWeilBrauerPairing_eq_zero_of_mem_ker
        w _ (hinf w hw).1
        ((Hom.mem_ker_explicitCoeff1_kerCoeffIncl_kerH1Congr_iff _).mpr (hinf w hw).2))
      (fun hw ↦ infiniteInvMap_eq_zero_of_isComplex w hw _)
  have hsupp : (∑ᶠ v : HeightOneSpectrum (𝓞 K),
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K))
          (φ.kerRes (τ v) a)
          (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
            (φ.dual.kerRes (τ v) b)))) =
      ∑ v ∈ S,
        ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
          ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
            (φ.isUnit_degree_baseChange (v.adicCompletion K))
            (φ.kerRes (τ v) a)
            (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
              (φ.dual.kerRes (τ v) b))) := by
    refine finsum_eq_sum_of_support_subset _ fun v hv ↦ ?_
    by_contra hvS
    apply hv
    have hv₀ : ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
        (φ.isUnit_degree_baseChange (v.adicCompletion K))
        (φ.kerRes (τ v) a)
        (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
          (φ.dual.kerRes (τ v) b))) = 0 :=
      (φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing_eq_zero_of_mem_ker _
        (hfin v hvS).1
        ((Hom.mem_ker_explicitCoeff1_kerCoeffIncl_kerH1Congr_iff _).mpr (hfin v hvS).2)
    exact (congrArg (ZMod.toRatAddCircle _) hv₀).trans (map_zero _)
  exact ((add_zero _).symm.trans ((congrArg₂ (· + ·) hsupp.symm harch.symm).trans hrec))

/-- **Finite-`S` global reciprocity in `ℤ/(deg φ)ℤ`.** Under the same local hypotheses outside `S`
and at real infinite places, the finite sum over `v ∈ S` of the local Tate pairings, transported
from `ZMod (deg (φ.baseChange K_v))` to `ZMod (deg φ)` along `φ.degree_baseChange K_v`,
is zero. -/
theorem sum_ringEquivCongr_localTateKerWeilPairing_eq_zero
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (hfin : ∀ v ∉ S,
      φ.kerRes (τ v) a ∈
        (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange (v.adicCompletion K))).kerCoeffIncl
          continuous_of_discreteTopology).ker ∧
      φ.dual.kerRes (τ v) b ∈
        (explicitCoeff1 _ _ (ofIsogeny (φ.dual.baseChange (v.adicCompletion K))).kerCoeffIncl
          continuous_of_discreteTopology).ker)
    (hinf : ∀ w : InfinitePlace K, w.IsReal →
      φ.kerRes (τ' w) a ∈
        (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange w.Completion)).kerCoeffIncl
          continuous_of_discreteTopology).ker ∧
      φ.dual.kerRes (τ' w) b ∈
        (explicitCoeff1 _ _ (ofIsogeny (φ.dual.baseChange w.Completion)).kerCoeffIncl
          continuous_of_discreteTopology).ker) :
    ∑ v ∈ S,
      ZMod.ringEquivCongr (φ.degree_baseChange (v.adicCompletion K))
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K))
          (φ.kerRes (τ v) a)
          (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
            (φ.dual.kerRes (τ v) b))) = 0 := by
  apply ZMod.toRatAddCircle_injective φ.degree
  rw [map_zero, map_sum]
  simp_rw [ZMod.toRatAddCircle_ringEquivCongr]
  exact φ.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero τ τ' S hfin hinf

end TauCeti.Isogeny

end
