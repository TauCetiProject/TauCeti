/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Orthogonality
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Reciprocity
public import TauCeti.NumberTheory.NumberField.Global.Places.Completion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SelmerStructure.Comparison

/-!
# Global reciprocity for isogeny Selmer groups

For an isogeny `φ : E₁ → E₂` of elliptic curves over a number field `K` and its dual `φ̂ : E₂ → E₁`,
global reciprocity for the isogeny Weil cup product
(`TauCeti.Isogeny.finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteInvMap_eq_zero`)
turns local orthogonality of the Selmer conditions into global orthogonality between relaxed
`φ`-Selmer classes and `φ̂`-Selmer classes:

* Over a nonarchimedean local field in which `deg φ` is invertible, local orthogonality of the
  `φ`- and `φ̂`-Selmer conditions descends the local Tate pairing to a pairing between the local
  `φ`-Selmer quotient `H¹(K, E₁[φ]) ⧸ H¹_φ(K)` and the local `φ̂`-Selmer condition `H¹_φ̂(K)`
  (`TauCeti.Isogeny.localTateKerWeilQuotientPairing`).
* Over a number field `K`, at every archimedean place `w` (real or complex), two local classes
  lying in the `φ`- and `φ̂`-Selmer kernels pair to `0` in `Br K_w`, so their archimedean Brauer
  invariant vanishes (`TauCeti.Isogeny.infiniteInvMap_kerWeilBrauerPairing_eq_zero_of_mem_ker`).
* Consequently, if `a ∈ H¹(K, E₁[φ])` satisfies the local `φ`-Selmer condition outside a finite
  set `S` of finite places (and at every infinite place) while `b ∈ H¹(K, E₂[φ̂])` satisfies the
  local `φ̂`-Selmer condition everywhere outside `S` (and at every infinite place), then the finite
  sum over `v ∈ S` of their local Tate pairings vanishes both in `ℚ/ℤ` and in `ℤ/(deg φ)ℤ`
  (`TauCeti.Isogeny.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero`,
  `TauCeti.Isogeny.sum_ringEquivCongr_localTateKerWeilPairing_eq_zero`).
* Specialised to the `S`-relaxed `φ`-Selmer structure against `Sel_φ̂(E₂/K)`, every `S`-relaxed
  `φ`-Selmer class pairs to zero summed over `S` with every global `φ̂`-Selmer class
  (`TauCeti.Isogeny.sum_ringEquivCongr_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax`).
  In particular, for a single finite place `v₀`, any `{Sum.inl v₀}`-relaxed `φ`-Selmer class is
  locally orthogonal at `v₀` to every global `φ̂`-Selmer class
  (`TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax_singleton`).

This is the global reciprocity half of the Poitou–Tate / Greenberg–Wiles comparison between
`Sel_φ(E₁/K)` and `Sel_φ̂(E₂/K)` used in Cassels' theorem on the isogeny invariance of the
Birch–Swinnerton-Dyer quotient.

## Main definitions

* `TauCeti.Isogeny.localTateKerWeilQuotientPairing`: the local Tate pairing descended to
  `(H¹(K, E₁[φ]) ⧸ H¹_φ(K)) →+ H¹_φ̂(K) →+ ZMod (deg φ)`.

## Main results

* `TauCeti.Isogeny.infiniteInvMap_kerWeilBrauerPairing_eq_zero_of_mem_ker`: archimedean Brauer
  invariants vanish on the local Selmer kernels at both real and complex places.
* `TauCeti.Isogeny.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero` and
  `TauCeti.Isogeny.sum_ringEquivCongr_localTateKerWeilPairing_eq_zero`: finite-`S` global
  reciprocity in `AddCircle (1 : ℚ)` and in `ZMod φ.degree`.
* `TauCeti.Isogeny.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax`,
  `TauCeti.Isogeny.sum_ringEquivCongr_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax`,
  and `TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax_singleton`: global
  orthogonality of `S`-relaxed `φ`-Selmer classes against `Sel_φ̂(E₂/K)`.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, §4.
* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press,
  2000, I.7.
-/

public section

noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open Hom (ofIsogeny kerH1Congr)

/-- Transporting `ZMod m` to `ZMod n` along `m = n` commutes with `ZMod.toRatAddCircle`. -/
private theorem toRatAddCircle_ringEquivCongr {m n : ℕ} (h : m = n) (z : ZMod m) :
    ZMod.toRatAddCircle n (ZMod.ringEquivCongr h z) = ZMod.toRatAddCircle m z := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  subst h
  simp

/-! ### Local quotient pairing -/

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

/-- **The local Tate pairing on the local Selmer quotient.** Because the local Selmer kernels of
`φ` and `φ̂` are orthogonal under `localTateKerWeilPairing`, restricting the second variable to the
local `φ̂`-Selmer kernel descends the first variable to the quotient by the local `φ`-Selmer
kernel. -/
def localTateKerWeilQuotientPairing :
    (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff ⧸
      (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology).ker) →+
    (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl continuous_of_discreteTopology).ker →+
    ZMod φ.degree :=
  QuotientAddGroup.lift _
    { toFun := fun a ↦ (φ.localTateKerWeilPairing hn a).comp
        (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
          continuous_of_discreteTopology).ker.subtype
      map_zero' := by ext; simp
      map_add' := fun _ _ ↦ by ext; simp }
    fun a ha ↦ AddMonoidHom.ext fun b ↦ φ.localTateKerWeilPairing_eq_zero_of_mem_ker hn ha b.2

/-- Evaluating `localTateKerWeilQuotientPairing` on a quotient class computes
`localTateKerWeilPairing`. -/
@[simp]
theorem localTateKerWeilQuotientPairing_mk
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
      continuous_of_discreteTopology).ker) :
    φ.localTateKerWeilQuotientPairing hn (QuotientAddGroup.mk a) b =
      φ.localTateKerWeilPairing hn a b :=
  (rfl)

end Local

/-! ### Global reciprocity over a number field -/

section Global

variable {K : Type} [Field K] [NumberField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- At every infinite place `w` of `K` (real or complex), the archimedean Brauer invariant of the
isogeny Weil cup product vanishes whenever the two local classes lie in the `φ`- and `φ̂`-Selmer
kernels over `w.Completion`. -/
theorem infiniteInvMap_kerWeilBrauerPairing_eq_zero_of_mem_ker (w : InfinitePlace K)
    {a : H1 (AbsoluteGaloisGroup w.Completion) (ofIsogeny (φ.baseChange w.Completion)).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup w.Completion)
      (ofIsogeny (φ.baseChange w.Completion).dual).KerCoeff}
    (ha : a ∈ (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange w.Completion)).kerCoeffIncl
      continuous_of_discreteTopology).ker)
    (hb : b ∈ (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange w.Completion).dual).kerCoeffIncl
      continuous_of_discreteTopology).ker) :
    infiniteInvMap w
      ((φ.baseChange w.Completion).kerWeilBrauerPairing
        (φ.isUnit_degree_baseChange w.Completion) a b) = 0 :=
  (congrArg (infiniteInvMap w)
    ((φ.baseChange w.Completion).kerWeilBrauerPairing_eq_zero_of_mem_ker _ ha hb)).trans
    (map_zero _)

/-- **Finite-`S` global reciprocity in `ℚ/ℤ`.** Let `S` be a finite set of finite places of `K`.
If `a ∈ H¹(K, E₁[φ])` and `b ∈ H¹(K, E₂[φ̂])` satisfy their respective local Selmer conditions at
every finite place `v ∉ S` and at every infinite place `w`, then the finite sum over `v ∈ S` of
their `ℚ/ℤ`-valued local Tate pairings is zero. -/
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
    (hinf : ∀ w : InfinitePlace K,
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
    exact φ.infiniteInvMap_kerWeilBrauerPairing_eq_zero_of_mem_ker w (hinf w).1
      ((Hom.mem_ker_explicitCoeff1_kerCoeffIncl_kerH1Congr_iff _).mpr (hinf w).2)
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
and at infinity, the finite sum over `v ∈ S` of the local Tate pairings, transported from
`ZMod (deg (φ.baseChange K_v))` to `ZMod (deg φ)` along `φ.degree_baseChange K_v`, is zero. -/
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
    (hinf : ∀ w : InfinitePlace K,
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
  have : NeZero φ.degree := ⟨φ.degree_pos.ne'⟩
  apply ZMod.toRatAddCircle_injective φ.degree
  rw [map_zero, map_sum]
  refine (Finset.sum_congr rfl fun v _ ↦
    toRatAddCircle_ringEquivCongr (φ.degree_baseChange (v.adicCompletion K)) _).trans ?_
  exact φ.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero τ τ' S hfin hinf

/-! ### Global orthogonality of relaxed `φ`-Selmer groups and `Sel_φ̂` -/

/-- **Global Selmer reciprocity in `ℚ/ℤ`.** If `a` belongs to the `S`-relaxed `φ`-Selmer group
(local conditions relaxed at the finite places in `S` and kept outside `S` and at every infinite
place) and `b ∈ Sel_φ̂(E₂/K)`, then the sum over `v ∈ S` of their `ℚ/ℤ`-valued local Tate pairings
vanishes. -/
theorem sum_toRatAddCircle_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax
    (τ : ∀ p : GlobalNumberFields.Place K, SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ ((φ.selmerStructure τ).relax
      (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))))).selmerGroup)
    (hb : b ∈ φ.dual.selmerGroup τ) :
    ∑ v ∈ S,
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K))
          (φ.kerRes (τ (.inl v)) a)
          (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
            (φ.dual.kerRes (τ (.inl v)) b))) = 0 := by
  rw [SelmerStructure.mem_selmerGroup_relax_iff] at ha
  rw [φ.dual.mem_selmerGroup_iff, mem_shafarevichTateGroup_iff] at hb
  refine φ.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero
    (fun v ↦ τ (.inl v)) (fun w ↦ τ (.inr w)) S (fun v hv ↦ ⟨?_, ?_⟩) (fun w ↦ ⟨?_, ?_⟩)
  · simpa using ha (.inl v) (by simpa using hv)
  · simpa [AddMonoidHom.mem_ker, ← pointRes_kerCoeffIncl] using hb (.inl v)
  · simpa using ha (.inr w) (by simp)
  · simpa [AddMonoidHom.mem_ker, ← pointRes_kerCoeffIncl] using hb (.inr w)

/-- **Global Selmer reciprocity in `ℤ/(deg φ)ℤ`.** If `a` belongs to the `S`-relaxed `φ`-Selmer
group and `b ∈ Sel_φ̂(E₂/K)`, then the sum over `v ∈ S` of their local Tate pairings in
`ZMod φ.degree` vanishes. -/
theorem sum_ringEquivCongr_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax
    (τ : ∀ p : GlobalNumberFields.Place K, SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ ((φ.selmerStructure τ).relax
      (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))))).selmerGroup)
    (hb : b ∈ φ.dual.selmerGroup τ) :
    ∑ v ∈ S,
      ZMod.ringEquivCongr (φ.degree_baseChange (v.adicCompletion K))
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K))
          (φ.kerRes (τ (.inl v)) a)
          (kerH1Congr (φ.ofIsogeny_dual_baseChange (v.adicCompletion K))
            (φ.dual.kerRes (τ (.inl v)) b))) = 0 := by
  have : NeZero φ.degree := ⟨φ.degree_pos.ne'⟩
  apply ZMod.toRatAddCircle_injective φ.degree
  rw [map_zero, map_sum]
  refine (Finset.sum_congr rfl fun v _ ↦
    toRatAddCircle_ringEquivCongr (φ.degree_baseChange (v.adicCompletion K)) _).trans ?_
  exact φ.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax τ S ha hb

/-- **Single-place Selmer orthogonality.** A global class `a ∈ H¹(K, E₁[φ])` satisfying the local
`φ`-Selmer condition at every place except possibly a single finite place `v₀` is locally
orthogonal at `v₀` to every `b ∈ Sel_φ̂(E₂/K)`. -/
theorem localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax_singleton
    (τ : ∀ p : GlobalNumberFields.Place K, SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (v₀ : HeightOneSpectrum (𝓞 K))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ ((φ.selmerStructure τ).relax {Sum.inl v₀}).selmerGroup)
    (hb : b ∈ φ.dual.selmerGroup τ) :
    (φ.baseChange (v₀.adicCompletion K)).localTateKerWeilPairing
      (φ.isUnit_degree_baseChange (v₀.adicCompletion K))
      (φ.kerRes (τ (.inl v₀)) a)
      (kerH1Congr (φ.ofIsogeny_dual_baseChange (v₀.adicCompletion K))
        (φ.dual.kerRes (τ (.inl v₀)) b)) = 0 := by
  have ha' : a ∈ ((φ.selmerStructure τ).relax
      (Sum.inl '' (({v₀} : Finset (HeightOneSpectrum (𝓞 K))) :
        Set (HeightOneSpectrum (𝓞 K))))).selmerGroup := by
    simpa using ha
  have hsum :=
    φ.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax τ {v₀} ha' hb
  rw [Finset.sum_singleton] at hsum
  have : NeZero (φ.baseChange (v₀.adicCompletion K)).degree :=
    ⟨(φ.baseChange (v₀.adicCompletion K)).degree_pos.ne'⟩
  exact (ZMod.toRatAddCircle_eq_zero _).mp hsum

end Global

end TauCeti.Isogeny

end
