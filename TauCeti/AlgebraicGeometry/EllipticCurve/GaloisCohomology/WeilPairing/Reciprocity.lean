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

For a number field `K`, two global classes in `H¹(K, E[m])` give local classes at every place.
The finite-place terms are their local Tate pairings embedded in `ℚ/ℤ` by `k ↦ k/m`;
the archimedean terms are the archimedean local Tate pairings embedded in `ℚ/ℤ` by `k ↦ k/m`
(equivalently, the archimedean Brauer invariants of their Weil cup product).
The sum of these terms is zero, both in `ℚ/ℤ` and directly in `ZMod m`
(`WeierstrassCurve.finsum_localTateWeilPairing_add_sum_infiniteTateWeilPairing_eq_zero`).
The finite-place pairings have finite support, so the finite sum over all finite places is an
honest sum, not the junk value of `finsum` on an infinitely supported function. The archimedean
terms vanish at complex places but need not vanish at real places.

The same holds for an isogeny `φ : E₁ → E₂` of degree `n`: for global classes
`a ∈ H¹(K, E₁[φ])` and `b ∈ H¹(K, E₂[φ̂])`, the local Tate pairings of their restrictions, for the
base change of `φ` and its dual, embedded in `ℚ/ℤ` by `k ↦ k/n`, together with the archimedean
invariants, sum to zero
(`TauCeti.Isogeny.finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteInvMap_eq_zero`).
These isogeny results follow the proofs of their torsion counterparts in this file:
`WeierstrassCurve.finiteInvAt_torsionWeilBrauerPairing`,
`WeierstrassCurve.infiniteInvAt_torsionWeilBrauerPairing`,
`WeierstrassCurve.hasFiniteSupport_localTateWeilPairing_torsionRes` and
`WeierstrassCurve.finsum_toRatAddCircle_localTateWeilPairing_add_sum_infiniteInvMap_eq_zero`.
At a place where both classes satisfy the Selmer local conditions, their local pairing vanishes
(`TauCeti.Isogeny.kerWeilBrauerPairing_kerRes_dualKerRes_eq_zero`, in `WeilPairing/Orthogonality`).
So if `a` and `b` satisfy them at every place outside a finite set `S` of finite places, the
pairings at the places of `S` sum to zero
(`TauCeti.Isogeny.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero`).

This is the reciprocity input for comparing global Selmer conditions with their orthogonals, as in
Cassels' formula for the ratio of the Selmer groups of `φ` and `φ̂`. It follows by localizing the
Brauer class of the global cup product and applying the Brauer sum formula
(`TauCeti.ClassFieldTheory.finsum_finiteInvAt_add_sum_infiniteInvAt_eq_zero`).

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, §§2 and 4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open IsDedekindDomain NumberField

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
  simp_rw [← W.finiteInvAt_torsionWeilBrauerPairing m hm a b _ (τ _),
    ← W.brBaseChange_torsionWeilBrauerPairing m hm (τ' _), ← infiniteInvAt_apply]
  exact finsum_finiteInvAt_add_sum_infiniteInvAt_eq_zero K _

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

open WeierstrassCurve TauCeti.ContCohomology TauCeti.ClassFieldTheory Hom
open _root_.IsDedekindDomain _root_.NumberField

variable {K : Type} [Field K] [NumberField K] {W₁ W₂ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)
  (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
  (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff)

/-- At a finite place, the local invariant of the global isogeny Weil cup product is the local
Tate pairing of the restrictions, for the base change of `φ` and its dual, embedded in `ℚ/ℤ`.
No prime-to-residue-characteristic hypothesis is required. -/
theorem finiteInvAt_kerWeilBrauerPairing (v : HeightOneSpectrum (𝓞 K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :
    finiteInvAt K v (φ.kerWeilBrauerPairing (isUnit_natCast_of_ne_zero φ.degree_ne_zero) a b) =
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (isUnit_natCast_of_ne_zero (φ.baseChange _).degree_ne_zero)
          (φ.kerRes τ a) (φ.dualKerRes τ b)) := by
  rw [finiteInvAt_apply, φ.brBaseChange_kerWeilBrauerPairing _ τ]
  exact ((φ.baseChange _).toRatAddCircle_localTateKerWeilPairing _ _ _).symm

omit [NumberField K] in
/-- At an infinite place, the local invariant of the global isogeny Weil cup product is the
archimedean local Tate pairing of the restrictions, embedded in `ℚ/ℤ`. -/
theorem infiniteInvAt_kerWeilBrauerPairing (w : InfinitePlace K)
    (τ' : SeparableClosure K →ₐ[K] SeparableClosure w.Completion) :
    infiniteInvAt K w (φ.kerWeilBrauerPairing
        (have := w.embedding.charZero; isUnit_natCast_of_ne_zero φ.degree_ne_zero) a b) =
      ZMod.toRatAddCircle (φ.baseChange w.Completion).degree
        ((φ.baseChange w.Completion).infiniteTateKerWeilPairing
          (φ.kerRes τ' a) (φ.dualKerRes τ' b)) := by
  rw [infiniteInvAt_apply, φ.brBaseChange_kerWeilBrauerPairing _ τ',
    (φ.baseChange _).toRatAddCircle_infiniteTateKerWeilPairing]

/-- The local Tate pairings, embedded in `ℚ/ℤ`, of the restrictions of two global classes for an
isogeny and its dual vanish at all but finitely many finite places. -/
theorem hasFiniteSupport_toRatAddCircle_localTateKerWeilPairing_kerRes
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :
    (fun v : HeightOneSpectrum (𝓞 K) ↦
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (isUnit_natCast_of_ne_zero (φ.baseChange _).degree_ne_zero)
          (φ.kerRes (τ v) a) (φ.dualKerRes (τ v) b))).HasFiniteSupport := by
  simp_rw [← φ.finiteInvAt_kerWeilBrauerPairing a b _ (τ _)]
  exact hasFiniteSupport_finiteInvAt K _

/-- **Global reciprocity for the isogeny Weil cup product.** For an isogeny `φ : E₁ → E₂` of
degree `n` over a number field, and global classes `a ∈ H¹(K, E₁[φ])` and
`b ∈ H¹(K, E₂[φ̂])`, the local Tate pairings of their restrictions at the finite places, for the
base change of `φ` and its dual and embedded in `ℚ/ℤ` by `k ↦ k/n`, together with the archimedean
Brauer invariants of their isogeny Weil cup product, sum to zero. The finite-place sum has finite
support by `hasFiniteSupport_toRatAddCircle_localTateKerWeilPairing_kerRes`. All choices of
embeddings of separable closures are allowed, independently at each place. -/
theorem finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteInvMap_eq_zero
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion) :
    (∑ᶠ v : HeightOneSpectrum (𝓞 K),
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (isUnit_natCast_of_ne_zero (φ.baseChange _).degree_ne_zero)
          (φ.kerRes (τ v) a) (φ.dualKerRes (τ v) b))) +
      ∑ w : InfinitePlace K, infiniteInvMap w
        ((φ.baseChange w.Completion).kerWeilBrauerPairing
          (isUnit_natCast_of_ne_zero (φ.baseChange _).degree_ne_zero)
          (φ.kerRes (τ' w) a) (φ.dualKerRes (τ' w) b)) = 0 := by
  simp_rw [← φ.finiteInvAt_kerWeilBrauerPairing a b _ (τ _),
    ← φ.brBaseChange_kerWeilBrauerPairing (isUnit_natCast_of_ne_zero φ.degree_ne_zero) (τ' _),
    ← infiniteInvAt_apply]
  exact finsum_finiteInvAt_add_sum_infiniteInvAt_eq_zero K _

/-- **Orthogonality of global classes satisfying the Selmer local conditions outside `S`.** Let
`a ∈ H¹(K, E₁[φ])` and `b ∈ H¹(K, E₂[φ̂])` be global classes whose images in `H¹(K, E₁)` and
`H¹(K, E₂)` are locally trivial at every infinite place and at every finite place outside a
finite set `S`. Then the local Tate pairings of their restrictions at the places of `S`, embedded
in `ℚ/ℤ`, sum to zero. This is the orthogonality half of global duality for the localisations of
the Selmer groups of `φ` and `φ̂` relaxed at `S`. -/
theorem sum_toRatAddCircle_localTateKerWeilPairing_eq_zero
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ha : ∀ v ∉ S, W₁.pointRes (τ v)
      (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology a) = 0)
    (hb : ∀ v ∉ S, W₂.pointRes (τ v)
      (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl continuous_of_discreteTopology b) = 0)
    (ha' : ∀ w, W₁.pointRes (τ' w)
      (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology a) = 0)
    (hb' : ∀ w, W₂.pointRes (τ' w)
      (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl continuous_of_discreteTopology b) = 0) :
    ∑ v ∈ S, ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
      ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
        (isUnit_natCast_of_ne_zero (φ.baseChange _).degree_ne_zero)
        (φ.kerRes (τ v) a) (φ.dualKerRes (τ v) b)) = 0 := by
  have h := φ.finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteInvMap_eq_zero
    a b τ τ'
  rwa [Finset.sum_eq_zero fun w _ ↦ by
      rw [φ.kerWeilBrauerPairing_kerRes_dualKerRes_eq_zero _ _ (ha' w) (hb' w), map_zero],
    add_zero, finsum_eq_sum_of_support_subset _ (s := S) fun v hv ↦ by_contra fun hvS ↦ hv <| by
      rw [toRatAddCircle_localTateKerWeilPairing,
        φ.kerWeilBrauerPairing_kerRes_dualKerRes_eq_zero _ _ (ha v hvS) (hb v hvS),
        map_zero]] at h

end TauCeti.Isogeny
