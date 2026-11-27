/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.EpiMono
public import TauCeti.Algebra.Homology.SpectralObject.Stabilization
public import TauCeti.Algebra.Homology.SpectralSequence.Degeneration
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
* `CategoryTheory.Abelian.SpectralObject.isIso_spectralSequencePageXToEInfty_of_d_eq_zero` and
  `CategoryTheory.Abelian.SpectralObject.isIso_spectralSequencePageXToEInfty_of_isZero`:
  stabilization by degeneration. The map from the page `r` onto `X.EInfty q n` is an isomorphism
  as soon as the differentials at `(p, q)` vanish on the pages `r ≤ r' < r₁`, where `r₁` is a page
  from which the object is known to be the limit object, for instance when their sources and
  targets vanish on the page `r`.
* `CategoryTheory.Abelian.SpectralObject.isIso_spectralSequencePageXToEInfty_of_mono`:
  stabilization at the top. The map from the page `r` onto `X.EInfty q n` is an isomorphism as
  soon as `H^n(⊥ ≤ q + r - 1) ⟶ H^n(⊥ ≤ ⊤)` is a monomorphism.
* `CategoryTheory.Abelian.SpectralObject.page_d_eq_zero_of_isIso_spectralSequencePageXToPageX`:
  conversely to stabilization by degeneration, when the map from the page `r` to the page `r + 1`
  at `(p, q)` is an isomorphism, both differentials at `(p, q)` vanish on the page `r`.

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

/-- **Stabilization by degeneration.** Let `pq = (p, q)` and `n = p + q`, and `r ≤ r₁` two pages.
Suppose that `H^{n+1}(⊥ ≤ q - r' + 2)` vanishes for `r ≤ r' ≤ r₁`, and that
`H^{n-1}(q + r₁ - 1 ≤ ⊤)` vanishes, so that the object at `pq` is the limit object
`X.EInfty q n` from the page `r₁` on. If on each page `r ≤ r' < r₁` the two differentials at `pq`
vanish, then the map `spectralSequencePageXToEInfty` from the page `r` onto `X.EInfty q n` is
already an isomorphism. -/
theorem isIso_spectralSequencePageXToEInfty_of_d_eq_zero (r₁ : ℤ) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2) (r : ℤ) (hr : 2 ≤ r) (hrr₁ : r ≤ r₁)
    (h₀ : ∀ r' : ℤ, r ≤ r' → r' ≤ r₁ → IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r' + 2 : ℤ) : EInt))))))
    (h₃ : IsZero ((X.H (n - 1)).obj
      (mk₁ (homOfLE (le_top : ((pq.2 + r₁ - 1 : ℤ) : EInt) ≤ ⊤)))))
    (hd : ∀ (r' : ℤ) (hr' : r ≤ r'), r' < r₁ →
      ((X.spectralSequence coreE₂Cohomological).page r' (hr.trans hr')).d
          (pq.1 - r', pq.2 + r' - 1) pq = 0 ∧
        ((X.spectralSequence coreE₂Cohomological).page r' (hr.trans hr')).d pq
          (pq.1 + r', pq.2 - r' + 1) = 0) :
    IsIso (X.spectralSequencePageXToEInfty r hr pq n hn (h₀ r le_rfl hrr₁)) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, r₁ = r + m := ⟨(r₁ - r).toNat, by omega⟩
  induction m generalizing r with
  | zero =>
    obtain rfl : r₁ = r := by omega
    rw [← X.spectralSequencePageXIsoEInfty_hom r₁ hr pq n hn (h₀ r₁ le_rfl le_rfl) h₃]
    infer_instance
  | succ m ih =>
    have := ih (r + 1) (by omega) (by omega) (fun r' h h' ↦ h₀ r' (by omega) h')
      (fun r' h₁ h₂ ↦ hd r' (by omega) h₂) (by omega)
    -- on the page `r`, both differentials at `pq` vanish, so the passage to the page `r + 1` is an
    -- isomorphism
    have : IsIso (((X.spectralSequence coreE₂Cohomological).page r).iCycles pq) :=
      HomologicalComplex.isIso_iCycles _ pq (pq.1 + r, pq.2 - r + 1)
        ((ComplexShape.up' _).next_eq' (Prod.ext (by dsimp) (by dsimp; omega)))
        (hd r le_rfl (by omega)).2
    have : IsIso (((X.spectralSequence coreE₂Cohomological).page r).homologyπ pq) :=
      HomologicalComplex.isIso_homologyπ _ (pq.1 - r, pq.2 + r - 1) pq
        ((ComplexShape.up' _).prev_eq' (Prod.ext (by dsimp; omega) (by dsimp; omega)))
        (hd r le_rfl (by omega)).1
    have hPP := X.iCycles_spectralSequencePageXToPageX r (r + 1) rfl hr pq n hn
      (h₀ r le_rfl hrr₁) (h₀ (r + 1) (by omega) (by omega))
    rw [← IsIso.eq_inv_comp] at hPP
    rw [← X.spectralSequencePageXToPageX_spectralSequencePageXToEInfty r (r + 1) hr (by omega) pq n
      hn (h₀ r le_rfl hrr₁) (h₀ (r + 1) (by omega) (by omega)), hPP]
    infer_instance

/-- **Stabilization by degeneration, from vanishing objects.** The special case of
`isIso_spectralSequencePageXToEInfty_of_d_eq_zero` where the sources and targets of the
differentials at `pq` of the pages `r ≤ r' < r₁` already vanish on the page `r`: the map
`spectralSequencePageXToEInfty` from the page `r` onto `X.EInfty q n` is an isomorphism. -/
theorem isIso_spectralSequencePageXToEInfty_of_isZero (r₁ : ℤ) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2) (r : ℤ) (hr : 2 ≤ r) (hrr₁ : r ≤ r₁)
    (h₀ : ∀ r' : ℤ, r ≤ r' → r' ≤ r₁ → IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r' + 2 : ℤ) : EInt))))))
    (h₃ : IsZero ((X.H (n - 1)).obj
      (mk₁ (homOfLE (le_top : ((pq.2 + r₁ - 1 : ℤ) : EInt) ≤ ⊤)))))
    (hd : ∀ r' : ℤ, r ≤ r' → r' < r₁ →
      IsZero (((X.spectralSequence coreE₂Cohomological).page r).X (pq.1 - r', pq.2 + r' - 1)) ∧
        IsZero (((X.spectralSequence coreE₂Cohomological).page r).X (pq.1 + r', pq.2 - r' + 1))) :
    IsIso (X.spectralSequencePageXToEInfty r hr pq n hn (h₀ r le_rfl hrr₁)) :=
  X.isIso_spectralSequencePageXToEInfty_of_d_eq_zero r₁ pq n hn r hr hrr₁ h₀ h₃
    fun r' hr' hr'₁ ↦
      ⟨(X.spectralSequence coreE₂Cohomological).page_d_eq_zero_of_le hr
          (Or.inl (hd r' hr' hr'₁).1) r' hr',
        (X.spectralSequence coreE₂Cohomological).page_d_eq_zero_of_le hr
          (Or.inr (hd r' hr' hr'₁).2) r' hr'⟩

/-- **Stabilization at the top.** Let `pq = (p, q)` and `n = p + q`. When `H^{n+1}(⊥ ≤ q - r + 2)`
vanishes and the map `H^n(⊥ ≤ q + r - 1) ⟶ H^n(⊥ ≤ ⊤)` is a monomorphism, the epimorphism
`spectralSequencePageXToEInfty` from the page `r` onto `X.EInfty q n` is an isomorphism. This
weakens the vanishing of `H^{n-1}(q + r - 1 ≤ ⊤)` assumed by `spectralSequencePageXIsoEInfty`. -/
theorem isIso_spectralSequencePageXToEInfty_of_mono (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (h₃ : Mono ((X.H n).map
      (twoδ₂Toδ₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 + r - 1 : ℤ) : EInt)))
        (homOfLE (le_top : ((pq.2 + r - 1 : ℤ) : EInt) ≤ ⊤)) (homOfLE bot_le)
        (Subsingleton.elim _ _)))) :
    IsIso (X.spectralSequencePageXToEInfty r hr pq n hn h₀) := by
  have := X.isIso_mapFourδ₄Toδ₃'_of_mono ⊥ pq.2 ((pq.2 + 1 : ℤ) : EInt)
    ((pq.2 + r - 1 : ℤ) : EInt) ⊤ bot_le (coe_le_coe_add_one pq.2) (by simp; lia) le_top
    (n - 1) n (n + 1) h₃
  rw [spectralSequencePageXToEInfty_def]
  infer_instance

/-- **Degeneration from stabilization.** Let `pq = (p, q)` and `n = p + q`. When
`H^{n+1}(⊥ ≤ q - r + 2)` and `H^{n+1}(⊥ ≤ q - r + 1)` vanish and the canonical map
`X.spectralSequencePageXToPageX r (r + 1)` at `pq` is an isomorphism, both differentials at `pq`
vanish on the page `r`. This is the converse of the inductive step of
`isIso_spectralSequencePageXToEInfty_of_d_eq_zero`. -/
theorem page_d_eq_zero_of_isIso_spectralSequencePageXToPageX (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (n : ℤ) (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (h₀' : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - (r + 1) + 2 : ℤ) : EInt))))))
    [IsIso (X.spectralSequencePageXToPageX r (r + 1) hr (by lia) pq n hn h₀ h₀')]
    {i j : ℤ × ℤ} (hij : i = pq ∨ j = pq) :
    ((X.spectralSequence coreE₂Cohomological).page r hr).d i j = 0 := by
  -- on cycles, the isomorphism from the page `r` to the page `r + 1` is the projection onto the
  -- homology of the page `r`
  have e := X.iCycles_spectralSequencePageXToPageX r (r + 1) rfl hr pq n hn h₀ h₀'
  rcases hij with rfl | rfl
  · -- every element of the page `r` at `pq` is a cycle
    have : Epi (((X.spectralSequence coreE₂Cohomological).page r hr).iCycles i) := by
      rw [(IsIso.eq_comp_inv _).2 e]
      infer_instance
    rw [← cancel_epi (((X.spectralSequence coreE₂Cohomological).page r hr).iCycles i),
      HomologicalComplex.iCycles_d, comp_zero]
  · -- no cycle of the page `r` at `pq` is a boundary
    have : Mono (((X.spectralSequence coreE₂Cohomological).page r hr).homologyπ j) := by
      rw [(IsIso.eq_comp_inv _).2 e.symm]
      infer_instance
    have h₀ : ((X.spectralSequence coreE₂Cohomological).page r hr).toCycles i j = 0 := by
      rw [← cancel_mono (((X.spectralSequence coreE₂Cohomological).page r hr).homologyπ j),
        HomologicalComplex.toCycles_comp_homologyπ, zero_comp]
    rw [← HomologicalComplex.toCycles_i, h₀, zero_comp]

end EInt

end CategoryTheory.Abelian.SpectralObject
