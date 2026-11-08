/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.BaseChange
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula

/-!
# Global reciprocity for the Weil cup product

For a number field `K`, two global classes in `H¹(K, E[m])` give local classes at every place.
The sum of their local Tate pairings, read in `ℚ/ℤ`, is zero. The finite-place pairings have
finite support, so the finite sum over all finite places is an honest sum, not the junk value
of `finsum` on an infinitely supported function. The archimedean terms are included: they vanish
at complex places but need not vanish at real places.

This is the reciprocity input for comparing global Selmer conditions with their orthogonals.
It follows by localizing the Brauer class of the global Weil cup product and applying the
Brauer sum formula. It does not assert orthogonality of local Kummer images or exactness of a
global duality sequence.

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

/-- The local Tate pairings of restrictions of two global classes vanish at all but finitely
many finite places. This also holds for the `ZMod m`-valued pairings, before embedding in `ℚ/ℤ`. -/
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

/-- **Global reciprocity for the Weil cup product.** The invariants of the local Tate pairings
of two global torsion-cohomology classes sum to zero over every finite and infinite place.
The finite-place sum has finite support by
`hasFiniteSupport_localTateWeilPairing_torsionRes`. All choices of embeddings of separable
closures are allowed, independently at each place. -/
theorem sum_localTateWeilPairing_torsionRes_eq_zero
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

end WeierstrassCurve
