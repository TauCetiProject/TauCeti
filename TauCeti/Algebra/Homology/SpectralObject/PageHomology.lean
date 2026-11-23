/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.Stabilization
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
-- The statement of `SpectralObject.spectralSequence_iso` refers to private auxiliary proofs of
-- this file, so that it may only be used with access to its private declarations.
import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# The passage from a page of a spectral sequence to the next page, on cycles

Let `X` be a spectral object in an abelian category, and `data` a recipe for spectral sequences
with `X.HasSpectralSequence data`. The object at `pq` on page `r` of `X.spectralSequence data` is
`E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃)`, and on page `r' = r + 1` it is `E^n(i₀' ≤ i₁ ≤ i₂ ≤ i₃')`, with
`i₀' ≤ i₀` and `i₃ ≤ i₃'`. Mathlib identifies the homology of page `r` at `pq` with the object at
`pq` on page `r'` (`(X.spectralSequence data).iso r r' pq`) through a homology data whose cycles
are `E^n(i₀' ≤ i₁ ≤ i₂ ≤ i₃)`
(`CategoryTheory.Abelian.SpectralObject.spectralSequenceHomologyData`).
This file records what the identification does to these cycles. The canonical map
`E^n(i₀' ≤ i₁ ≤ i₂ ≤ i₃) ⟶ E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃)` to page `r` lands in the cycles
(`mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv_d`), its lift to the cycles is an isomorphism
(`isIso_liftCycles_mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv`), inverse to the identification
of the cycles of page `r` with those of the homology data
(`liftCycles_cyclesIsoSc'_hom_cyclesIso_hom`), and the class in the homology of page `r` of
its lift is sent to the canonical map `E^n(i₀' ≤ i₁ ≤ i₂ ≤ i₃) ⟶ E^n(i₀' ≤ i₁ ≤ i₂ ≤ i₃')` to
page `r'` (`liftCycles_homologyπ_spectralSequence_iso_hom`).

For a spectral object indexed by `EInt` and its `E₂` cohomological spectral sequence, suppose that
`H^{n+1}(⊥ ≤ q - r + 2)` and `H^{n+1}(⊥ ≤ q - r' + 2)` vanish, where `n = p + q`, as happens for
large `r` for a filtration bounded below. Then the map `X.spectralSequencePageXToPageX r r'` from
the object at `(p, q)` on page `r` to the object on page `r'`, induced by the canonical map
`E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ q + r' - 1)`
(`TauCeti.Algebra.Homology.SpectralObject.Stabilization`), is the map of the spectral sequence:
on cycles it is the projection onto the homology of page `r` followed by Mathlib's identification
of that homology with page `r'` (`iCycles_spectralSequencePageXToPageX`). So the direct limit of
the pages along the maps `spectralSequencePageXToPageX`, which is the graded piece of the abutment
for an exhaustive filtration bounded below
(`TauCeti.Algebra.Homology.SpectralSequence.Filtered.BoundedBelow`), is the direct limit along the
maps `E_r ⟶ E_{r+1}` of the spectral sequence itself.

## Main results

* `CategoryTheory.Abelian.SpectralObject.liftCycles_homologyπ_spectralSequence_iso_hom`: the
  identification of the homology of a page with the next page, on the cycles
  `E^n(i₀' ≤ i₁ ≤ i₂ ≤ i₃)`.
* `CategoryTheory.Abelian.SpectralObject.iCycles_spectralSequencePageXToPageX`: the canonical
  maps between pages of `X.spectralSequence coreE₂Cohomological` are the maps of the spectral
  sequence.

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Definition 5.2.11 and Theorem 5.5.1.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press,
  2001, §2.2.
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows Limits

section General

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι] {c : ℤ → ComplexShape κ}
  {r₀ : ℤ} (X : SpectralObject C ι) (data : SpectralSequenceDataCore ι c r₀)
  [X.HasSpectralSequence data]

-- Mathlib's `SpectralSequence.HomologyData.kf_w` is stated for the auxiliary pages from which the
-- sealed `spectralSequence` is built; this restates it for the pages of `X.spectralSequence data`.
unseal spectralSequence in
/-- The canonical map `E^n(i₀' ≤ i₁ ≤ i₂ ≤ i₃) ⟶ E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃)` to the object at `pq` on
page `r`, where `i₀'` is the lowest index of the object at `pq` on page `r' = r + 1`, is a cycle of
page `r`. -/
@[reassoc]
lemma mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv_d (r r' : ℤ) (hrr' : r + 1 = r')
    (hr : r₀ ≤ r) (pq pq'' : κ) (i₀' i₀ i₁ i₂ i₃ : ι) (hi₀' : i₀' = data.i₀ r' pq)
    (hi₀ : i₀ = data.i₀ r pq) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (hi₃ : i₃ = data.i₃ r pq) (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (data.i₀_le' hrr' hr pq hi₀' hi₀)
        (data.le₀₁' r hr pq hi₀ hi₁) (data.le₁₂' pq hi₁ hi₂) (data.le₂₃' r hr pq hi₂ hi₃)
        n₀ n₁ n₂ ≫
      (X.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁').inv) ≫
      ((X.spectralSequence data).page r).d pq pq'' = 0 :=
  SpectralSequence.HomologyData.kf_w X data r r' hrr' hr pq pq'' i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂
    hi₃ n₀ n₁ n₂ hn₁'

/-- The lift to the cycles of page `r` of the cycle
`E^n(i₀' ≤ i₁ ≤ i₂ ≤ i₃) ⟶ E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃)` of
`mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv_d` is inverse to the identification of these
cycles with the cycles `E^n(i₀' ≤ i₁ ≤ i₂ ≤ i₃)` of `X.spectralSequenceHomologyData`. -/
@[reassoc]
lemma liftCycles_cyclesIsoSc'_hom_cyclesIso_hom (r r' : ℤ) (hrr' : r + 1 = r')
    (hr : r₀ ≤ r) (pq pq'' : κ) (hpq : (c r).next pq = pq'')
    (i₀' i₀ i₁ i₂ i₃ i₃' : ι) (hi₀' : i₀' = data.i₀ r' pq) (hi₀ : i₀ = data.i₀ r pq)
    (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq) (hi₃ : i₃ = data.i₃ r pq)
    (hi₃' : i₃' = data.i₃ r' pq) (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ((X.spectralSequence data).page r).liftCycles
        (X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (data.i₀_le' hrr' hr pq hi₀' hi₀)
          (data.le₀₁' r hr pq hi₀ hi₁) (data.le₁₂' pq hi₁ hi₂) (data.le₂₃' r hr pq hi₂ hi₃)
          n₀ n₁ n₂ ≫
          (X.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁').inv)
        pq'' hpq (X.mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv_d data r r' hrr' hr pq pq''
          i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁') ≫
      (((X.spectralSequence data).page r).cyclesIsoSc' _ pq pq'' rfl hpq).hom ≫
        (X.spectralSequenceHomologyData data r r' hrr' hr _ pq pq'' rfl hpq
          i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').left.cyclesIso.hom =
      𝟙 _ := by
  refine (cancel_mono (X.spectralSequenceHomologyData data r r' hrr' hr _ pq pq'' rfl hpq
    i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').left.i).1 ?_
  rw [Category.assoc, Category.assoc, ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles, HomologicalComplex.liftCycles_i]
  exact ((Category.id_comp _).trans (X.spectralSequenceHomologyData_left_i data r r' hrr' hr _
    pq pq'' rfl hpq i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁')).symm

/-- The lift to the cycles of page `r` of the cycle
`E^n(i₀' ≤ i₁ ≤ i₂ ≤ i₃) ⟶ E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃)` of
`mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv_d` is an isomorphism. -/
lemma isIso_liftCycles_mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv (r r' : ℤ)
    (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq pq'' : κ) (hpq : (c r).next pq = pq'')
    (i₀' i₀ i₁ i₂ i₃ : ι) (hi₀' : i₀' = data.i₀ r' pq) (hi₀ : i₀ = data.i₀ r pq)
    (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq) (hi₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (((X.spectralSequence data).page r).liftCycles
      (X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (data.i₀_le' hrr' hr pq hi₀' hi₀)
        (data.le₀₁' r hr pq hi₀ hi₁) (data.le₁₂' pq hi₁ hi₂) (data.le₂₃' r hr pq hi₂ hi₃)
        n₀ n₁ n₂ ≫
        (X.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁').inv)
      pq'' hpq (X.mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv_d data r r' hrr' hr pq pq''
        i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁')) :=
  -- These morphisms are stated between objects that are only definitionally equal to those of
  -- the isomorphisms they come from, so instance search does not find their `IsIso` instances.
  @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ (IsIso.comp_isIso' (Iso.isIso_hom _) (Iso.isIso_hom _))
    (IsIso.id _) (X.liftCycles_cyclesIsoSc'_hom_cyclesIso_hom data r r' hrr' hr pq pq'' hpq
      i₀' i₀ i₁ i₂ i₃ _ hi₀' hi₀ hi₁ hi₂ hi₃ rfl n₀ n₁ n₂ hn₁')

/-- The identification `(X.spectralSequence data).iso r r' pq` of the homology at `pq` of page `r`
with the object at `pq` on page `r' = r + 1`, on cycles: the class of the cycle
`E^n(i₀' ≤ i₁ ≤ i₂ ≤ i₃) ⟶ E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃)` is the canonical map
`E^n(i₀' ≤ i₁ ≤ i₂ ≤ i₃) ⟶ E^n(i₀' ≤ i₁ ≤ i₂ ≤ i₃')`, where `i₀ ≤ i₁ ≤ i₂ ≤ i₃` and
`i₀' ≤ i₁ ≤ i₂ ≤ i₃'` are the indices of the objects at `pq` on pages `r` and `r'`. -/
@[reassoc]
lemma liftCycles_homologyπ_spectralSequence_iso_hom (r r' : ℤ) (hrr' : r + 1 = r')
    (hr : r₀ ≤ r) (pq pq'' : κ) (hpq : (c r).next pq = pq'')
    (i₀' i₀ i₁ i₂ i₃ i₃' : ι) (hi₀' : i₀' = data.i₀ r' pq) (hi₀ : i₀ = data.i₀ r pq)
    (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq) (hi₃ : i₃ = data.i₃ r pq)
    (hi₃' : i₃' = data.i₃ r' pq) (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ((X.spectralSequence data).page r).liftCycles
        (X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (data.i₀_le' hrr' hr pq hi₀' hi₀)
          (data.le₀₁' r hr pq hi₀ hi₁) (data.le₁₂' pq hi₁ hi₂) (data.le₂₃' r hr pq hi₂ hi₃)
          n₀ n₁ n₂ ≫
          (X.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁').inv)
        pq'' hpq (X.mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv_d data r r' hrr' hr pq pq''
          i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁') ≫
      ((X.spectralSequence data).page r).homologyπ pq ≫
        ((X.spectralSequence data).iso r r' pq hrr' hr).hom =
    X.mapFourδ₄Toδ₃' i₀' i₁ i₂ i₃ i₃' ((data.i₀_le' hrr' hr pq hi₀' hi₀).trans
        (data.le₀₁' r hr pq hi₀ hi₁)) (data.le₁₂' pq hi₁ hi₂) (data.le₂₃' r hr pq hi₂ hi₃)
        (data.le₃₃' hrr' hr pq hi₃ hi₃') n₀ n₁ n₂ ≫
      (X.spectralSequencePageXIso data r' (hr.trans (by lia)) pq i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃'
        n₀ n₁ n₂ hn₁').inv := by
  rw [X.spectralSequence_iso data r r' hrr' hr _ pq pq'' rfl hpq i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀
    hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁', Iso.trans_hom, HomologicalComplex.π_homologyIsoSc'_hom_assoc]
  -- The left homology object of `spectralSequenceHomologyData` is only definitionally the object
  -- `E` that `spectralSequencePageXIso` starts from, so the composite of isomorphisms in
  -- `spectralSequence_iso` is not type correct at reducible transparency and `rw` cannot split it.
  erw [Iso.trans_hom, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  simp only [X.liftCycles_cyclesIsoSc'_hom_cyclesIso_hom_assoc data r r' hrr' hr pq pq'' hpq
    i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁',
    spectralSequenceHomologyData_left_π, Iso.symm_hom]

end General

section EInt

variable {C : Type*} [Category* C] [Abelian C] (X : SpectralObject C EInt)

/-- When `H^{n+1}(⊥ ≤ q - r + 2)` and `H^{n+1}(⊥ ≤ q - r' + 2)` vanish, `n = p + q` and
`r' = r + 1`, the canonical map `X.spectralSequencePageXToPageX r r'` from the object at
`pq = (p, q)` on page `r` to the object at `pq` on page `r'` is the map of the spectral sequence:
on cycles, it is the projection onto the homology of page `r` followed by the identification
`(X.spectralSequence coreE₂Cohomological).iso r r' pq` of that homology with page `r'`. -/
@[reassoc]
lemma iCycles_spectralSequencePageXToPageX (r r' : ℤ) (hrr' : r + 1 = r') (hr : 2 ≤ r)
    (pq : ℤ × ℤ) (n : ℤ) (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (h₀' : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r' + 2 : ℤ) : EInt)))))) :
    ((X.spectralSequence coreE₂Cohomological).page r).iCycles pq ≫
        X.spectralSequencePageXToPageX r r' hr (by lia) pq n hn h₀ h₀' =
      ((X.spectralSequence coreE₂Cohomological).page r).homologyπ pq ≫
        ((X.spectralSequence coreE₂Cohomological).iso r r' pq hrr' hr).hom := by
  have hab : ((pq.2 - r' + 2 : ℤ) : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt) := by simp; lia
  have hb : ((pq.2 - r + 2 : ℤ) : EInt) ≤ pq.2 := by simp; lia
  have h₂₃ : ((pq.2 + 1 : ℤ) : EInt) ≤ ((pq.2 + r - 1 : ℤ) : EInt) := by simp; lia
  -- `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1)` maps isomorphically onto `E^n(q - r' + 2 ≤ q ≤ …)`.
  have : IsIso (X.mapFourδ₁Toδ₀' ⊥ ((pq.2 - r' + 2 : ℤ) : EInt) pq.2 ((pq.2 + 1 : ℤ) : EInt)
      ((pq.2 + r - 1 : ℤ) : EInt) bot_le (hab.trans hb) (coe_le_coe_add_one pq.2) h₂₃
      (n - 1) n (n + 1)) :=
    X.isIso_mapFourδ₁Toδ₀' ⊥ _ _ _ _ bot_le (hab.trans hb) (coe_le_coe_add_one pq.2) h₂₃
      (n - 1) n (n + 1) h₀'
  -- The lift `L` of `E^n(q - r' + 2 ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E_r^{p,q}` to the cycles of page `r`
  -- is an isomorphism, so it suffices to compare both sides after composing with `L`.
  obtain ⟨L, hL, hLπ, _⟩ := (⟨_, HomologicalComplex.liftCycles_i ..,
    X.liftCycles_homologyπ_spectralSequence_iso_hom coreE₂Cohomological r r' hrr' hr pq _ rfl
      ((pq.2 - r' + 2 : ℤ) : EInt) ((pq.2 - r + 2 : ℤ) : EInt) pq.2 ((pq.2 + 1 : ℤ) : EInt)
      ((pq.2 + r - 1 : ℤ) : EInt) ((pq.2 + r' - 1 : ℤ) : EInt) rfl rfl rfl rfl rfl rfl
      (n - 1) n (n + 1) hn,
    X.isIso_liftCycles_mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv coreE₂Cohomological r r' hrr'
      hr pq _ rfl ((pq.2 - r' + 2 : ℤ) : EInt) ((pq.2 - r + 2 : ℤ) : EInt) pq.2
      ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt) rfl rfl rfl rfl rfl (n - 1) n (n + 1)
      hn⟩ : ∃ L,
      L ≫ ((X.spectralSequence coreE₂Cohomological).page r).iCycles pq = _ ∧ L ≫ _ = _ ∧ IsIso L)
  rw [← cancel_epi L, hLπ, ← Category.assoc, hL, ← cancel_epi (X.mapFourδ₁Toδ₀' ⊥
    ((pq.2 - r' + 2 : ℤ) : EInt) pq.2 ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt) bot_le
    (hab.trans hb) (coe_le_coe_add_one pq.2) h₂₃ (n - 1) n (n + 1))]
  have hE := (X.spectralSequencePageXIsoEBot r hr pq n hn h₀).inv_hom_id
  rw [spectralSequencePageXIsoEBot_inv, Category.assoc] at hE
  simp [spectralSequencePageXToPageX_def, spectralSequencePageXIsoEBot_inv,
    mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃'_assoc, mapFourδ₁Toδ₀'_comp_assoc, reassoc_of% hE]

end EInt

end CategoryTheory.Abelian.SpectralObject
