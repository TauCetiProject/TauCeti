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

The same holds for an isogeny `φ : E₁ → E₂` over `K` of degree `n` and its dual `φ̂`: for
`a ∈ H¹(K, E₁[φ])` and `b ∈ H¹(K, E₂[φ̂])`, the local Tate pairings
`H¹(K_v, E₁[φ]) × H¹(K_v, E₂[φ̂]) → ℤ/n` of their restrictions at all places, embedded in `ℚ/ℤ`
by `k ↦ k/n`, sum to zero (in the namespace `TauCeti.Isogeny`,
`finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteTateKerWeilPairing_eq_zero`).
Here `b` is restricted into the kernel of the dual of the base change of `φ`
(`TauCeti.Isogeny.dualKerRes`), on which the local pairings of the base change are defined. The
degree of the base change of `φ` to `K_v` equals `n` only propositionally, so this form is stated
in `ℚ/ℤ` only.

This is the reciprocity input for comparing global Selmer conditions with their orthogonals; in
the isogeny form it is the global duality input of Cassels' comparison of the `φ`- and
`φ̂`-Selmer groups. Both forms follow by localizing the Brauer class of the global cup product and
applying the Brauer sum formula.

## Main results

* `WeierstrassCurve.finsum_toRatAddCircle_localTateWeilPairing_add_sum_infiniteInvMap_eq_zero`
  and `WeierstrassCurve.finsum_localTateWeilPairing_add_sum_infiniteTateWeilPairing_eq_zero`:
  global reciprocity for the Weil cup product on `H¹(K, E[m])`.
* `TauCeti.Isogeny.finiteInvAt_kerWeilBrauerPairing` and
  `TauCeti.Isogeny.infiniteInvAt_kerWeilBrauerPairing`: the local invariants of the Brauer class of
  the isogeny Weil cup product are the local Tate pairings of the restricted classes.
* `finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteTateKerWeilPairing_eq_zero`,
  in the namespace `TauCeti.Isogeny`: global reciprocity for the isogeny Weil cup product.

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
  classical
  let x := W.torsionWeilBrauerPairing m hm a b
  have hsum := sumLocalInv_brLocalization_eq_zero K x
  rw [sumLocalInv_brLocalization K x (S := brauerSupport K x) (fun _ hv ↦ hv)] at hsum
  simp_rw [← W.finiteInvAt_torsionWeilBrauerPairing m hm a b _ (τ _)]
  rw [finsum_eq_sum_of_support_subset _ (s := brauerSupport K x)
    (fun v hv ↦ (mem_brauerSupport K).2 hv)]
  convert hsum using 1
  congr 1
  apply Finset.sum_congr rfl
  intro w _
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

open WeierstrassCurve TauCeti.ContCohomology TauCeti.ClassFieldTheory Hom
open IsDedekindDomain _root_.NumberField

variable {K : Type} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
  (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff)

/-- At an infinite place, the local invariant of the global isogeny Weil cup product is the
archimedean local Tate pairing of the restrictions, embedded in `ℚ/ℤ` by `k ↦ k/n`,
`n = deg φ`. The second class is restricted into the kernel of the dual of the base change of
`φ` (`TauCeti.Isogeny.dualKerRes`). -/
theorem infiniteInvAt_kerWeilBrauerPairing (hn : IsUnit (φ.degree : K)) (w : InfinitePlace K)
    (τ' : SeparableClosure K →ₐ[K] SeparableClosure w.Completion) :
    infiniteInvAt K w (φ.kerWeilBrauerPairing hn a b) =
      ZMod.toRatAddCircle (φ.baseChange w.Completion).degree
        ((φ.baseChange w.Completion).infiniteTateKerWeilPairing (φ.kerRes τ' a)
          (φ.dualKerRes τ' b)) := by
  have hnw : IsUnit ((φ.baseChange w.Completion).degree : w.Completion) :=
    isUnit_natCast_of_ne_zero (φ.baseChange w.Completion).degree_ne_zero
  rw [infiniteInvAt_apply, φ.brBaseChange_kerWeilBrauerPairing τ' hn hnw]
  exact ((φ.baseChange w.Completion).toRatAddCircle_infiniteTateKerWeilPairing hnw _ _).symm

variable [NumberField K]

/-- At a finite place, the local invariant of the global isogeny Weil cup product is the local
Tate pairing of the restrictions, embedded in `ℚ/ℤ` by `k ↦ k/n`, `n = deg φ`. The second class
is restricted into the kernel of the dual of the base change of `φ`
(`TauCeti.Isogeny.dualKerRes`). No prime-to-residue-characteristic hypothesis is required. -/
theorem finiteInvAt_kerWeilBrauerPairing (v : HeightOneSpectrum (𝓞 K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :
    finiteInvAt K v (φ.kerWeilBrauerPairing (isUnit_natCast_of_ne_zero φ.degree_ne_zero) a b) =
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (isUnit_natCast_of_ne_zero (φ.baseChange (v.adicCompletion K)).degree_ne_zero)
          (φ.kerRes τ a) (φ.dualKerRes τ b)) := by
  rw [finiteInvAt_apply, φ.brBaseChange_kerWeilBrauerPairing τ _
    (isUnit_natCast_of_ne_zero (φ.baseChange (v.adicCompletion K)).degree_ne_zero)]
  exact ((φ.baseChange (v.adicCompletion K)).toRatAddCircle_localTateKerWeilPairing _ _ _).symm

/-- The local Tate pairings of the restrictions of two global classes, for an isogeny and its
dual, vanish at all but finitely many finite places. -/
theorem hasFiniteSupport_localTateKerWeilPairing_kerRes
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :
    (fun v : HeightOneSpectrum (𝓞 K) ↦ ZMod.toRatAddCircle
      (φ.baseChange (v.adicCompletion K)).degree
      ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
        (isUnit_natCast_of_ne_zero (φ.baseChange (v.adicCompletion K)).degree_ne_zero)
        (φ.kerRes (τ v) a) (φ.dualKerRes (τ v) b))).HasFiniteSupport := by
  refine (hasFiniteSupport_finiteInvAt K
    (φ.kerWeilBrauerPairing (isUnit_natCast_of_ne_zero φ.degree_ne_zero) a b)).subset ?_
  intro v hv
  rwa [Function.mem_support, φ.finiteInvAt_kerWeilBrauerPairing a b v (τ v)]

/-- **Global reciprocity for the isogeny Weil cup product.** Let `φ : E₁ → E₂` be an isogeny of
elliptic curves over a number field `K`, of degree `n`, and let `a ∈ H¹(K, E₁[φ])` and
`b ∈ H¹(K, E₂[φ̂])`. The local Tate pairings of their restrictions at the finite places and the
archimedean local Tate pairings at the infinite places, each embedded in `ℚ/ℤ` by `k ↦ k/n`, sum
to zero. The finite-place sum has finite support by
`TauCeti.Isogeny.hasFiniteSupport_localTateKerWeilPairing_kerRes`. All choices of embeddings of
separable closures are allowed, independently at each place. -/
theorem finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteTateKerWeilPairing_eq_zero
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion) :
    (∑ᶠ v : HeightOneSpectrum (𝓞 K), ZMod.toRatAddCircle
      (φ.baseChange (v.adicCompletion K)).degree
      ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
        (isUnit_natCast_of_ne_zero (φ.baseChange (v.adicCompletion K)).degree_ne_zero)
        (φ.kerRes (τ v) a) (φ.dualKerRes (τ v) b))) +
      ∑ w : InfinitePlace K, ZMod.toRatAddCircle (φ.baseChange w.Completion).degree
        ((φ.baseChange w.Completion).infiniteTateKerWeilPairing (φ.kerRes (τ' w) a)
          (φ.dualKerRes (τ' w) b)) = 0 := by
  classical
  let x := φ.kerWeilBrauerPairing (isUnit_natCast_of_ne_zero φ.degree_ne_zero) a b
  have hsum := sumLocalInv_brLocalization_eq_zero K x
  rw [sumLocalInv_brLocalization K x (S := brauerSupport K x) (fun _ hv ↦ hv)] at hsum
  simp only [← φ.finiteInvAt_kerWeilBrauerPairing a b _ (τ _),
    ← φ.infiniteInvAt_kerWeilBrauerPairing a b (isUnit_natCast_of_ne_zero φ.degree_ne_zero) _
      (τ' _)]
  rwa [finsum_eq_sum_of_support_subset _ (s := brauerSupport K x)
    (fun v hv ↦ (mem_brauerSupport K).2 hv)]

end TauCeti.Isogeny

