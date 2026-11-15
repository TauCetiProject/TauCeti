/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula

/-!
# Global reciprocity for the Weil cup product

For a number field `K`, two global classes in `H¹(K, E[m])` — or a class in `H¹(K, E₁[φ])` and a
class in `H¹(K, E₂[φ̂])` for an isogeny `φ : E₁ → E₂` — give local classes at every place.
The finite-place terms are their local Tate pairings embedded in `ℚ/ℤ` by `k ↦ k/m` (respectively
`k ↦ k/deg φ`); the archimedean terms are the archimedean Brauer invariants of their Weil cup
product. The sum of these terms is zero. The finite-place pairings have finite support, so the
finite sum over all finite places is an honest sum, not the junk value of `finsum` on an infinitely
supported function. The archimedean terms vanish at complex places, and vanish at real places as
well whenever both classes lie in the local Kummer conditions (see `Selmer.Isogeny.Reciprocity`).

This is the reciprocity input for comparing global Selmer conditions with their orthogonals in
Cassels' proof of the isogeny invariance of the Birch–Swinnerton-Dyer quotient. It follows by
localizing the Brauer class of the global Weil cup product and applying the Brauer sum formula.

## Main results

* `WeierstrassCurve.finiteInvAt_torsionWeilBrauerPairing`,
  `WeierstrassCurve.hasFiniteSupport_localTateWeilPairing_torsionRes`, and
  `WeierstrassCurve.finsum_toRatAddCircle_localTateWeilPairing_add_sum_infiniteInvMap_eq_zero`:
  finite-place invariant formula, finite support, and global reciprocity for `E[m]`.
* `TauCeti.Isogeny.finiteInvAt_kerWeilBrauerPairing`,
  `TauCeti.Isogeny.hasFiniteSupport_toRatAddCircle_localTateKerWeilPairing_kerRes`,
  `TauCeti.Isogeny.eventually_localTateKerWeilPairing_kerRes_eq_zero`, and
  `TauCeti.Isogeny.finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteInvMap_eq_zero`:
  the corresponding results for `E₁[φ]` and `E₂[φ̂]`.

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

/-- **Global reciprocity for the Weil cup product.** The finite-place local Tate pairings of
two global torsion-cohomology classes, embedded in `ℚ/ℤ` by `k ↦ k/m`, together with the
archimedean Brauer invariants of their Weil cup product, sum to zero.
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

end WeierstrassCurve

section
open WeierstrassCurve TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open IsDedekindDomain NumberField

namespace TauCeti.Isogeny

open Hom (ofIsogeny)

variable {K : Type} [Field K] [NumberField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))
  (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
  (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff)

/-- At a finite place, the local invariant of the global isogeny Weil cup product is the local Tate
pairing of its restrictions, embedded in `ℚ/ℤ` by `k ↦ k/deg φ`. No prime-to-residue-characteristic
hypothesis is required. -/
theorem finiteInvAt_kerWeilBrauerPairing (v : HeightOneSpectrum (𝓞 K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :
    finiteInvAt K v (φ.kerWeilBrauerPairing hn a b) =
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K) hn)
          (φ.kerRes τ a) (φ.dualKerRes τ b)) :=
  (finiteInvAt_apply K v (φ.kerWeilBrauerPairing hn a b)).trans <|
    (congrArg (invMap (v.adicCompletion K))
      (φ.brBaseChange_kerWeilBrauerPairing hn (L := v.adicCompletion K) τ
        (φ.isUnit_degree_baseChange (v.adicCompletion K) hn) a b)).trans
      ((φ.baseChange (v.adicCompletion K)).toRatAddCircle_localTateKerWeilPairing _ _ _).symm

/-- The `ℚ/ℤ`-valued local Tate pairings of the restrictions of two global kernel-cohomology
classes have finite support over all finite places. -/
theorem hasFiniteSupport_toRatAddCircle_localTateKerWeilPairing_kerRes
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :
    (fun v : HeightOneSpectrum (𝓞 K) ↦
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K) hn)
          (φ.kerRes (τ v) a) (φ.dualKerRes (τ v) b))).HasFiniteSupport := by
  refine (hasFiniteSupport_finiteInvAt K (φ.kerWeilBrauerPairing hn a b)).subset ?_
  intro v hv
  rwa [Function.mem_support, ← φ.finiteInvAt_kerWeilBrauerPairing hn a b v (τ v)] at hv

/-- For all but finitely many finite places, the `ZMod`-valued local Tate pairing of the
restrictions of two global kernel-cohomology classes vanishes. -/
theorem eventually_localTateKerWeilPairing_kerRes_eq_zero
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :
    ∀ᶠ v in Filter.cofinite,
      (φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
        (φ.isUnit_degree_baseChange (v.adicCompletion K) hn)
        (φ.kerRes (τ v) a) (φ.dualKerRes (τ v) b) = 0 := by
  refine Filter.eventually_cofinite.2 <|
    (φ.hasFiniteSupport_toRatAddCircle_localTateKerWeilPairing_kerRes hn a b τ).subset ?_
  intro v hv
  rw [Function.mem_support]
  exact fun h ↦ hv ((ZMod.toRatAddCircle_eq_zero _).1 h)

/-- **Global reciprocity for the isogeny Weil cup product.** The finite-place local Tate pairings
of `a ∈ H¹(K, E₁[φ])` and `b ∈ H¹(K, E₂[φ̂])`, embedded in `ℚ/ℤ` by `k ↦ k/deg φ`, together with
the archimedean Brauer invariants of their Weil cup product, sum to zero. The finite-place sum has
finite support by `hasFiniteSupport_toRatAddCircle_localTateKerWeilPairing_kerRes`. -/
theorem finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteInvMap_eq_zero
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion) :
    (∑ᶠ v : HeightOneSpectrum (𝓞 K),
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K) hn)
          (φ.kerRes (τ v) a) (φ.dualKerRes (τ v) b))) +
      ∑ w : InfinitePlace K, infiniteInvMap w
        ((φ.baseChange w.Completion).kerWeilBrauerPairing
          (φ.isUnit_degree_baseChange w.Completion hn)
          (φ.kerRes (τ' w) a) (φ.dualKerRes (τ' w) b)) = 0 := by
  classical
  let x := φ.kerWeilBrauerPairing hn a b
  have hfin :
      (∑ᶠ v : HeightOneSpectrum (𝓞 K),
        ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
          ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
            (φ.isUnit_degree_baseChange (v.adicCompletion K) hn)
            (φ.kerRes (τ v) a) (φ.dualKerRes (τ v) b))) =
        ∑ v ∈ brauerSupport K x, finiteInvAt K v x :=
    (congrArg finsum (funext fun v ↦
      (φ.finiteInvAt_kerWeilBrauerPairing hn a b v (τ v)).symm)).trans
      (finsum_eq_sum_of_support_subset (fun v ↦ finiteInvAt K v x) (s := brauerSupport K x)
        fun v hv ↦ (mem_brauerSupport K).2 hv)
  have hinf :
      (∑ w : InfinitePlace K, infiniteInvMap w
        ((φ.baseChange w.Completion).kerWeilBrauerPairing
          (φ.isUnit_degree_baseChange w.Completion hn)
          (φ.kerRes (τ' w) a) (φ.dualKerRes (τ' w) b))) =
        ∑ w : InfinitePlace K, infiniteInvAt K w x :=
    Finset.sum_congr rfl fun w _ ↦
      (congrArg (infiniteInvMap w)
        (φ.brBaseChange_kerWeilBrauerPairing hn (L := w.Completion) (τ' w)
          (φ.isUnit_degree_baseChange w.Completion hn) a b)).symm.trans
        (infiniteInvAt_apply K w x).symm
  exact (congrArg₂ (· + ·) hfin hinf).trans <|
    (sumLocalInv_brLocalization K x fun _ hv ↦ hv).symm.trans
      (sumLocalInv_brLocalization_eq_zero K x)

end TauCeti.Isogeny

end
