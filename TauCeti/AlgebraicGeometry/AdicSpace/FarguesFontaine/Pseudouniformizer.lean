/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.Quotient
public import TauCeti.RingTheory.WittVector.AdicTopology

/-!
# Independence of the pseudouniformiser

The space `𝒴 = D(p) ∩ D([ϖ]) ⊆ Spa(𝕎 R, 𝕎 R)`, its Frobenius action and the orbit space
`𝒳 = 𝒴 / φ^ℤ` are defined in terms of a chosen element `ϖ : R`, which for `R = 𝒪_F` is a
pseudouniformiser of a complete perfect nonarchimedean field `F` of characteristic `p`. None of
these depends on that choice. Let `ϖ, ϖ' : R` generate ideals with the same radical, as any two
pseudouniformisers of `𝒪_F` do (`Valuation.Integers.radical_span_singleton_eq_of_norm_lt_one`).
Then the ideals `(p, [ϖ])` and `(p, [ϖ'])` define the same adic topology on `𝕎 R`
(`TauCeti.WittVector.isAdic_span_p_teichmuller_iff`), and this file shows the following.

* The subsets `𝒴` defined by `ϖ` and by `ϖ'` coincide, since a prime ideal contains `[ϖ]` exactly
  when it contains `[ϖ']`.
* The Frobenius actions on them agree, since both are pullback along the Witt-vector Frobenius.
* Consequently the two orbit spaces `𝒳` are homeomorphic, compatibly with the projections
  from `𝒴`.

## Main results

* `TauCeti.FarguesFontaine.spaY_eq_of_radical_eq` : `𝒴` depends only on the radical of `(ϖ)`.
* `TauCeti.FarguesFontaine.frobeniusHomeomorph_zpow_apply_val_eq` : the integer powers of
  Frobenius on `𝒴` do not depend on the element used to define `𝒴`.
* `TauCeti.FarguesFontaine.spaXCongr` : the homeomorphism between the orbit spaces defined by two
  elements with the same `𝒴`.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018).
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017, §3.1.
-/

public section

noncomputable section

namespace TauCeti.FarguesFontaine

open TauCeti.ValuationSpectrum _root_.WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] {ϖ ϖ' : R}

/-- If `ϖ` lies in the radical of `(ϖ')`, then every prime ideal of `𝕎 R` containing `[ϖ']`
contains `[ϖ]`. -/
private theorem teichmuller_mem_supp_of_mem_radical (h : ϖ ∈ (Ideal.span {ϖ'}).radical)
    {v : Spv (WittVector p R)} (hv : teichmuller p ϖ' ∈ v.supp) : teichmuller p ϖ ∈ v.supp :=
  (Ideal.IsPrime.radical_le_iff inferInstance).mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv)
    (teichmuller_mem_radical_span_singleton h)

variable [TopologicalSpace (WittVector p R)]

/-- **`𝒴` depends only on the radical of `(ϖ)`.** If `ϖ` and `ϖ'` generate ideals with the same
radical, for instance if they are two pseudouniformisers of `𝒪_F`, then
`D(p) ∩ D([ϖ]) = D(p) ∩ D([ϖ'])` in `Spa(𝕎 R, 𝕎 R)`. -/
theorem spaY_eq_of_radical_eq (h : (Ideal.span {ϖ}).radical = (Ideal.span {ϖ'}).radical) :
    spaY p ϖ = spaY p ϖ' := by
  have hϖ : ϖ ∈ (Ideal.span {ϖ'}).radical :=
    h.le (Ideal.le_radical (Ideal.mem_span_singleton_self ϖ))
  have hϖ' : ϖ' ∈ (Ideal.span {ϖ}).radical :=
    h.ge (Ideal.le_radical (Ideal.mem_span_singleton_self ϖ'))
  ext v
  simp only [mem_spaY_iff]
  exact and_congr_right' <| and_congr_right' <|
    not_congr ⟨teichmuller_mem_supp_of_mem_radical hϖ', teichmuller_mem_supp_of_mem_radical hϖ⟩

variable [CharP R p] [PerfectRing R p]

/-- **The Frobenius actions on `𝒴` do not depend on the pseudouniformiser.** For points of the
subsets `𝒴` defined by `ϖ` and by `ϖ'` with the same underlying valuation, every integer power of
Frobenius gives the same valuation: on either subset, Frobenius is pullback along the Witt-vector
Frobenius. -/
theorem frobeniusHomeomorph_zpow_apply_val_eq
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'})) (n : ℤ)
    {v : spaY p ϖ} {w : spaY p ϖ'} (h : v.val = w.val) :
    ((frobeniusHomeomorph hI ^ n) v).val = ((frobeniusHomeomorph hI' ^ n) w).val := by
  induction n using Int.induction_on generalizing v w with
  | zero => simpa using h
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, Homeomorph.mul_apply, Homeomorph.mul_apply]
    exact ih (by simp [h])
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, Homeomorph.mul_apply, Homeomorph.mul_apply]
    exact ih (by simp [h])

/-- The map of orbit spaces induced by the identity of `𝒴`, when `ϖ` and `ϖ'` define the same
subset `𝒴`. It is well defined because the two Frobenius actions agree. -/
private def spaXMap (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))
    (h : spaY p ϖ = spaY p ϖ') : spaX hI → spaX hI' :=
  spaX.lift hI (fun v ↦ quotientMap hI' ⟨v.val, h ▸ v.property⟩) fun n _ ↦
    (quotientMap_eq_iff hI' _ _).mpr
      ⟨n, Subtype.ext (frobeniusHomeomorph_zpow_apply_val_eq hI' hI n rfl)⟩

private theorem spaXMap_quotientMap
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))
    (h : spaY p ϖ = spaY p ϖ') (v : spaY p ϖ) :
    spaXMap hI hI' h (quotientMap hI v) = quotientMap hI' ⟨v.val, h ▸ v.property⟩ :=
  spaX.lift_quotientMap hI _ _ v

private theorem continuous_spaXMap
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))
    (h : spaY p ϖ = spaY p ϖ') : Continuous (spaXMap hI hI' h) := by
  rw [(isOpenQuotientMap_quotientMap hI).isQuotientMap.continuous_iff]
  have : spaXMap hI hI' h ∘ quotientMap hI =
      fun v ↦ quotientMap hI' ⟨v.val, h ▸ v.property⟩ :=
    funext (spaXMap_quotientMap hI hI' h)
  rw [this]
  exact (isOpenQuotientMap_quotientMap hI').continuous.comp
    (continuous_subtype_val.subtype_mk _)

private theorem spaXMap_spaXMap
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))
    (h : spaY p ϖ = spaY p ϖ') (x : spaX hI) :
    spaXMap hI' hI h.symm (spaXMap hI hI' h x) = x := by
  induction x using spaX.inductionOn with
  | h v => rw [spaXMap_quotientMap, spaXMap_quotientMap]

/-- **The orbit spaces `𝒴 / φ^ℤ` for two pseudouniformisers are homeomorphic.** If `ϖ` and `ϖ'`
define the same subset `𝒴` of `Spa(𝕎 R, 𝕎 R)`, as they do when they generate ideals with the same
radical (`spaY_eq_of_radical_eq`), then the identity of `𝒴` descends to a homeomorphism of the
Frobenius orbit spaces, because the two Frobenius actions agree. -/
def spaXCongr (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))
    (h : spaY p ϖ = spaY p ϖ') : spaX hI ≃ₜ spaX hI' where
  toFun := spaXMap hI hI' h
  invFun := spaXMap hI' hI h.symm
  left_inv := spaXMap_spaXMap hI hI' h
  right_inv := spaXMap_spaXMap hI' hI h.symm
  continuous_toFun := continuous_spaXMap hI hI' h
  continuous_invFun := continuous_spaXMap hI' hI h.symm

/-- The homeomorphism of orbit spaces sends the orbit of a point of `𝒴` to its orbit. -/
@[simp]
theorem spaXCongr_quotientMap
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))
    (h : spaY p ϖ = spaY p ϖ') (v : spaY p ϖ) :
    spaXCongr hI hI' h (quotientMap hI v) = quotientMap hI' ⟨v.val, h ▸ v.property⟩ :=
  spaXMap_quotientMap hI hI' h v

/-- The inverse of the homeomorphism of orbit spaces is the homeomorphism in the other direction. -/
@[simp]
theorem spaXCongr_symm
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))
    (h : spaY p ϖ = spaY p ϖ') : (spaXCongr hI hI' h).symm = spaXCongr hI' hI h.symm := (rfl)

end TauCeti.FarguesFontaine
