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

For a number field `K`, two global classes in `H¹(K, E[m])`, or a pair of global classes in
`H¹(K, E₁[φ])` and `H¹(K, E₂[φ̂])` for an isogeny `φ : E₁ → E₂`, give local classes at every
place. The finite-place terms are their local Tate pairings embedded in `ℚ/ℤ` by `k ↦ k/m`
(respectively `k ↦ k/deg φ`); the archimedean terms are the archimedean Brauer invariants of
their Weil cup product. The sum of these terms is zero. The finite-place pairings vanish at all
but finitely many places, so the finite sum over all finite places is an honest sum rather than
the junk value of `finsum` on an infinitely supported function. The archimedean terms vanish at
complex places but need not vanish at real places.

This is the reciprocity input for comparing global Selmer conditions with their orthogonals, in
particular in Cassels' comparison of `Sel_φ(E₁/K)` and `Sel_φ̂(E₂/K)`. It follows by localizing
the Brauer class of the global Weil cup product and applying the Brauer sum formula.

## Main results

* `WeierstrassCurve.finiteInvAt_torsionWeilBrauerPairing`,
  `WeierstrassCurve.hasFiniteSupport_localTateWeilPairing_torsionRes`, and
  `WeierstrassCurve.finsum_toRatAddCircle_localTateWeilPairing_add_sum_infiniteInvMap_eq_zero`:
  global reciprocity for `[m]`-torsion.
* `TauCeti.Isogeny.finiteInvAt_kerWeilBrauerPairing`,
  `TauCeti.Isogeny.finite_setOf_localTateKerWeilPairing_kerRes_ne_zero`,
  `TauCeti.Isogeny.hasFiniteSupport_toRatAddCircle_localTateKerWeilPairing_kerRes`, and
  `TauCeti.Isogeny.finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteInvMap_eq_zero`:
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

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open Hom (ofIsogeny kerH1Congr)

variable {K : Type} [Field K] [NumberField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
  (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff)

/-- At a finite place, the local invariant of the global isogeny Weil cup product is the local
Tate pairing of the restricted kernel classes, embedded in `ℚ/ℤ` by `k ↦ k/deg φ`. No
prime-to-residue-characteristic hypothesis is required. -/
theorem finiteInvAt_kerWeilBrauerPairing (hn : IsUnit (φ.degree : K))
    (v : HeightOneSpectrum (𝓞 K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :
    finiteInvAt K v (φ.kerWeilBrauerPairing hn a b) =
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K))
          (φ.kerRes τ a)
          (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
            (φ.dual.kerRes τ b))) :=
  (finiteInvAt_apply K v _).trans <|
    (congrArg (invMap (v.adicCompletion K))
      (φ.brBaseChange_kerWeilBrauerPairing hn τ a b)).trans <|
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
  rwa [Function.mem_support, φ.finiteInvAt_kerWeilBrauerPairing a b φ.isUnit_degree v (τ v)]

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
  have : NeZero (φ.baseChange (v.adicCompletion K)).degree :=
    ⟨(φ.baseChange (v.adicCompletion K)).degree_pos.ne'⟩
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
  classical
  let x := φ.kerWeilBrauerPairing φ.isUnit_degree a b
  have hsum := sumLocalInv_brLocalization_eq_zero K x
  rw [sumLocalInv_brLocalization K x (S := brauerSupport K x) (fun _ hv ↦ hv)] at hsum
  have hfin : (∑ᶠ v : HeightOneSpectrum (𝓞 K),
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K))
          (φ.kerRes (τ v) a)
          (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
            (φ.dual.kerRes (τ v) b)))) =
      ∑ v ∈ brauerSupport K x, finiteInvAt K v x := by
    have hfun : (fun v : HeightOneSpectrum (𝓞 K) ↦
        ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
          ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
            (φ.isUnit_degree_baseChange (v.adicCompletion K))
            (φ.kerRes (τ v) a)
            (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
              (φ.dual.kerRes (τ v) b)))) =
        fun v ↦ finiteInvAt K v x :=
      funext fun v ↦ (φ.finiteInvAt_kerWeilBrauerPairing a b φ.isUnit_degree v (τ v)).symm
    rw [hfun]
    exact finsum_eq_sum_of_support_subset _ fun v hv ↦ (mem_brauerSupport K).2 hv
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
  exact (congrArg₂ (· + ·) hfin hinf).trans hsum

end TauCeti.Isogeny

end
