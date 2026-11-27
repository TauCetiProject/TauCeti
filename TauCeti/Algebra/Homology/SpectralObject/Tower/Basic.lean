/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.PageHomology
public import TauCeti.Algebra.Homology.SpectralSequence.Tower
public import TauCeti.CategoryTheory.Abelian.ImageSubobject

/-!
# The cycle and boundary towers of the spectral sequence of a spectral object

Let `X` be a spectral object in an abelian category, indexed by a preorder `ι`, and let `data` be a
recipe for spectral sequences starting on the page `r₀` with `X.HasSpectralSequence data`. The
object at `pq` on the page `r` of `X.spectralSequence data` is `E^n(i₀(r) ≤ i₁ ≤ i₂ ≤ i₃(r))`, where
`n = data.deg pq`, `i₀(r) = data.i₀ r pq` decreases and `i₃(r) = data.i₃ r pq` increases with `r`.
Every spectral sequence presents its page `r` at `pq` as a subquotient `Z_r(pq) / B_r(pq)` of its
first page `E_{r₀}(pq)` (`CategoryTheory.SpectralSequence.pagePresentation`). This file computes
these towers for the spectral sequence of `X`, for every recipe at once:

* the cycles `Z_r(pq)` are the image of the canonical monomorphism
  `E^n(i₀(r) ≤ i₁ ≤ i₂ ≤ i₃(r₀)) ⟶ E^n(i₀(r₀) ≤ i₁ ≤ i₂ ≤ i₃(r₀)) = E_{r₀}(pq)`
  (`CategoryTheory.Abelian.SpectralObject.cyclesSubobject_spectralSequence`);
* the boundaries `B_r(pq)` are the kernel of the canonical epimorphism
  `E_{r₀}(pq) ⟶ E^n(i₀(r₀) ≤ i₁ ≤ i₂ ≤ i₃(r))`
  (`CategoryTheory.Abelian.SpectralObject.boundariesSubobject_spectralSequence`);
* the projection of `Z_r(pq)` onto the page `r` is the canonical epimorphism
  `E^n(i₀(r) ≤ i₁ ≤ i₂ ≤ i₃(r₀)) ⟶ E^n(i₀(r) ≤ i₁ ≤ i₂ ≤ i₃(r))`
  (`CategoryTheory.Abelian.SpectralObject.exists_iso_pagePresentation`).

For the `E₂` cohomological recipe on a spectral object indexed by `EInt`, at `(p, q)` with
`n = p + q`, this says that `Z_r` is the image of `E^n(q - r + 2 ≤ q ≤ q + 1 ≤ q + 1)` and `B_r` the
kernel of the map to `E^n(q ≤ q ≤ q + 1 ≤ q + r - 1)`, inside `E^n(q ≤ q ≤ q + 1 ≤ q + 1)`, which is
`H^n(q ≤ q + 1)`.

The proof is by induction on `r`. The kernel of the differential leaving `pq` on the page `r` is the
image of `E^n(i₀(r + 1) ≤ i₁ ≤ i₂ ≤ i₃(r))` (Mathlib's homology data of the pages, through the
isomorphism `SpectralObject.towerLiftCycles` onto the cycles), and its preimage under the
projection is computed by the fact that boundaries are permanent cycles: the kernel of
`E^n(a ≤ i₁ ≤ i₂ ≤ b) ⟶ E^n(a ≤ i₁ ≤ i₂ ≤ b')` lies in the image of
`E^n(a' ≤ i₁ ≤ i₂ ≤ b) ⟶ E^n(a ≤ i₁ ≤ i₂ ≤ b)`
(`SpectralObject.kernelSubobject_mapFourδ₄Toδ₃'_le_imageSubobject_mapFourδ₁Toδ₀'`).

## Main results

* `CategoryTheory.Abelian.SpectralObject.exists_iso_pagePresentation`: the presentation of the page
  `r` inside the page `r₀`.
* `CategoryTheory.Abelian.SpectralObject.cyclesSubobject_spectralSequence`,
  `CategoryTheory.Abelian.SpectralObject.boundariesSubobject_spectralSequence`: the cycle and
  boundary towers.

## References

* [Stacks, Tag 012Q](https://stacks.math.columbia.edu/tag/012Q), Lemma 24.6, the filtered-complex
  form of these towers.
* G. O. Helle and J. Rognes, *Boardman's whole-plane obstruction group for Cartan–Eilenberg
  systems*, Documenta Math. 24 (2019), 1855–1878, Definition 4.5 and Remark 4.6.
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows Limits Subobject

variable {C ι : Type*} [Category* C] [Abelian C] [Preorder ι] (X : SpectralObject C ι)

/-- **Boundaries are permanent cycles.** For `a' ≤ a ≤ i₁ ≤ i₂ ≤ b ≤ b'`, the kernel of the
canonical epimorphism `E^n(a ≤ i₁ ≤ i₂ ≤ b) ⟶ E^n(a ≤ i₁ ≤ i₂ ≤ b')` lies in the image of the
canonical monomorphism `E^n(a' ≤ i₁ ≤ i₂ ≤ b) ⟶ E^n(a ≤ i₁ ≤ i₂ ≤ b)`: the first is the image of
a differential and the second the kernel of another, and their composite vanishes. -/
lemma kernelSubobject_mapFourδ₄Toδ₃'_le_imageSubobject_mapFourδ₁Toδ₀'
    (a' a i₁ i₂ b b' : ι) (h₀ : a' ≤ a) (h₁ : a ≤ i₁) (h₂ : i₁ ≤ i₂) (h₃ : i₂ ≤ b)
    (h₄ : b ≤ b') (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    kernelSubobject (X.mapFourδ₄Toδ₃' a i₁ i₂ b b' h₁ h₂ h₃ h₄ n₀ n₁ n₂) ≤
      imageSubobject (X.mapFourδ₁Toδ₀' a' a i₁ i₂ b h₀ h₁ h₂ h₃ n₀ n₁ n₂) := by
  have hc := (ShortComplex.exact_iff_image_eq_kernel _).1 (X.dCokernelSequence_exact
    (homOfLE h₁) (homOfLE h₂) (homOfLE h₃) (homOfLE h₄) (𝟙 b') (homOfLE (h₃.trans h₄)) rfl
    (n₀ - 1) n₀ n₁ n₂ (by lia) hn₁ hn₂)
  have hk := (ShortComplex.exact_iff_image_eq_kernel _).1 (X.dKernelSequence_exact
    (𝟙 a') (homOfLE h₀) (homOfLE h₁) (homOfLE h₂) (homOfLE h₃) (homOfLE (h₀.trans h₁)) rfl
    n₀ n₁ n₂ (n₂ + 1) hn₁ hn₂ rfl)
  dsimp at hc hk
  refine le_of_eq_of_le (Eq.trans ?_ hc.symm) (le_of_le_of_eq ?_ hk.symm)
  · -- `mapFourδ₄Toδ₃'` and `fourδ₄Toδ₃'` are abbreviations for this `X.map` of `fourδ₄Toδ₃`.
    with_reducible rfl
  · exact image_le_kernel _ _ (X.d_d (𝟙 a') (homOfLE h₀) (homOfLE h₁) (homOfLE h₂)
      (homOfLE h₃) (homOfLE h₄) (𝟙 b') (n₀ - 1) n₀ n₁ n₂ (n₂ + 1) (by lia) hn₁ hn₂ rfl)

section Tower

variable {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (data : SpectralSequenceDataCore ι c r₀) [X.HasSpectralSequence data] (pq : κ)

/-- The object `E^n(i₀(r) ≤ i₁ ≤ i₂ ≤ i₃(s))`, `n = deg pq`, with the lowest index of the page `r`
and the highest index of the page `s` at `pq`. -/
noncomputable abbrev towerE (r s : ℤ) (hr : r₀ ≤ r := by lia) (hs : r₀ ≤ s := by lia) : C :=
  X.E (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ s pq))
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)

/-- The canonical monomorphism `E^n(i₀(r') ≤ i₁ ≤ i₂ ≤ i₃(s)) ⟶ E^n(i₀(r) ≤ i₁ ≤ i₂ ≤ i₃(s))` for
`r ≤ r'`. -/
noncomputable abbrev towerι (r r' s : ℤ) (hr : r₀ ≤ r) (hrr' : r ≤ r') (hs : r₀ ≤ s) :
    X.towerE data pq r' s ⟶ X.towerE data pq r s :=
  X.mapFourδ₁Toδ₀' (data.i₀ r' pq) (data.i₀ r pq) (data.i₁ pq) (data.i₂ pq) (data.i₃ s pq)
    (data.antitone_i₀ r r' pq) (data.le₀₁ r pq) (data.le₁₂ pq) (data.le₂₃ s pq)
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)

/-- The canonical epimorphism `E^n(i₀(r) ≤ i₁ ≤ i₂ ≤ i₃(s)) ⟶ E^n(i₀(r) ≤ i₁ ≤ i₂ ≤ i₃(s'))` for
`s ≤ s'`. -/
noncomputable abbrev towerp (r s s' : ℤ) (hr : r₀ ≤ r) (hs : r₀ ≤ s) (hss' : s ≤ s') :
    X.towerE data pq r s ⟶ X.towerE data pq r s' :=
  X.mapFourδ₄Toδ₃' (data.i₀ r pq) (data.i₁ pq) (data.i₂ pq) (data.i₃ s pq) (data.i₃ s' pq)
    (data.le₀₁ r pq) (data.le₁₂ pq) (data.le₂₃ s pq) (data.monotone_i₃ s s' pq)
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)

omit [X.HasSpectralSequence data] in
@[simp]
lemma towerι_self (r s : ℤ) (hr : r₀ ≤ r) (hs : r₀ ≤ s) :
    X.towerι data pq r r s hr le_rfl hs = 𝟙 _ := by
  rw [← X.map_id (n₀ := data.deg pq - 1) (n₁ := data.deg pq) (n₂ := data.deg pq + 1)]
  congr 1

omit [X.HasSpectralSequence data] in
@[simp]
lemma towerp_self (r s : ℤ) (hr : r₀ ≤ r) (hs : r₀ ≤ s) :
    X.towerp data pq r s s hr hs le_rfl = 𝟙 _ := by
  rw [← X.map_id (n₀ := data.deg pq - 1) (n₁ := data.deg pq) (n₂ := data.deg pq + 1)]
  congr 1

/-- The object at `pq` on the page `r` is `E^n(i₀(r) ≤ i₁ ≤ i₂ ≤ i₃(r))`. -/
noncomputable abbrev towerPageXIso (r : ℤ) (hr : r₀ ≤ r) :
    ((X.spectralSequence data).page r).X pq ≅ X.towerE data pq r r :=
  X.spectralSequencePageXIso data r hr pq _ _ _ _ rfl rfl rfl rfl _ _ _ rfl

/-- The monomorphism `E^n(i₀(r) ≤ i₁ ≤ i₂ ≤ i₃(r₀)) ⟶ E_{r₀}(pq)`, whose image is the cycle tower
`Z_r(pq)`. -/
noncomputable def towerα (r : ℤ) (hr : r₀ ≤ r) :
    X.towerE data pq r r₀ ⟶ ((X.spectralSequence data).page r₀).X pq :=
  X.towerι data pq r₀ r r₀ le_rfl hr le_rfl ≫ (X.towerPageXIso data pq r₀ le_rfl).inv

@[reassoc]
lemma towerα_def (r : ℤ) (hr : r₀ ≤ r) :
    X.towerα data pq r hr =
      X.towerι data pq r₀ r r₀ le_rfl hr le_rfl ≫ (X.towerPageXIso data pq r₀ le_rfl).inv :=
  (rfl)

instance (r : ℤ) (hr : r₀ ≤ r) : Mono (X.towerα data pq r hr) := by
  rw [towerα_def]
  infer_instance

/-- The epimorphism `E^n(i₀(r) ≤ i₁ ≤ i₂ ≤ i₃(r₀)) ⟶ E_r(pq)`, which is the projection of the
cycle tower onto the page `r`. -/
noncomputable def towerπ (r : ℤ) (hr : r₀ ≤ r) :
    X.towerE data pq r r₀ ⟶ ((X.spectralSequence data).page r).X pq :=
  X.towerp data pq r r₀ r hr le_rfl hr ≫ (X.towerPageXIso data pq r hr).inv

@[reassoc]
lemma towerπ_def (r : ℤ) (hr : r₀ ≤ r) :
    X.towerπ data pq r hr =
      X.towerp data pq r r₀ r hr le_rfl hr ≫ (X.towerPageXIso data pq r hr).inv :=
  (rfl)

instance (r : ℤ) (hr : r₀ ≤ r) : Epi (X.towerπ data pq r hr) := by
  rw [towerπ_def]
  infer_instance

/-- The epimorphism `E_{r₀}(pq) ⟶ E^n(i₀(r₀) ≤ i₁ ≤ i₂ ≤ i₃(r))`, whose kernel is the boundary
tower `B_r(pq)`. -/
noncomputable def towerβ (r : ℤ) (hr : r₀ ≤ r) :
    ((X.spectralSequence data).page r₀).X pq ⟶ X.towerE data pq r₀ r :=
  (X.towerPageXIso data pq r₀ le_rfl).hom ≫ X.towerp data pq r₀ r₀ r le_rfl le_rfl hr

@[reassoc]
lemma towerβ_def (r : ℤ) (hr : r₀ ≤ r) :
    X.towerβ data pq r hr =
      (X.towerPageXIso data pq r₀ le_rfl).hom ≫ X.towerp data pq r₀ r₀ r le_rfl le_rfl hr :=
  (rfl)

instance (r : ℤ) (hr : r₀ ≤ r) : Epi (X.towerβ data pq r hr) := by
  rw [towerβ_def]
  infer_instance

/-- The lift to the cycles of the page `r` at `pq` of the cycle
`E^n(i₀(r + 1) ≤ i₁ ≤ i₂ ≤ i₃(r)) ⟶ E_r(pq)`; it is an isomorphism. -/
noncomputable def towerLiftCycles (r : ℤ) (hr : r₀ ≤ r) :
    X.towerE data pq (r + 1) r ⟶ (((X.spectralSequence data).page r).sc pq).cycles :=
  ((X.spectralSequence data).page r).liftCycles _ _ rfl
    (X.mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv_d data r (r + 1) rfl hr pq
      ((c r).next pq) _ _ _ _ _ rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq)
      (data.deg pq + 1) rfl)

@[reassoc (attr := simp)]
lemma towerLiftCycles_iCycles (r : ℤ) (hr : r₀ ≤ r) :
    X.towerLiftCycles data pq r hr ≫ (((X.spectralSequence data).page r).sc pq).iCycles =
      X.towerι data pq r (r + 1) r hr (by lia) hr ≫ (X.towerPageXIso data pq r hr).inv :=
  -- `HomologicalComplex.iCycles` is by definition the `iCycles` of `sc`.
  HomologicalComplex.liftCycles_i _ _ _ _ _

instance (r : ℤ) (hr : r₀ ≤ r) : IsIso (X.towerLiftCycles data pq r hr) :=
  X.isIso_liftCycles_mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv data r (r + 1) rfl hr pq _ rfl
    _ _ _ _ _ rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl

/-- The identification of the homology at `pq` of the page `r` with the page `r + 1` sends the
class of `towerLiftCycles` to the canonical epimorphism
`E^n(i₀(r + 1) ≤ i₁ ≤ i₂ ≤ i₃(r)) ⟶ E^n(i₀(r + 1) ≤ i₁ ≤ i₂ ≤ i₃(r + 1))`. -/
@[reassoc]
lemma towerLiftCycles_homologyπ_iso_hom (r : ℤ) (hr : r₀ ≤ r) :
    X.towerLiftCycles data pq r hr ≫ (((X.spectralSequence data).page r).sc pq).homologyπ ≫
        ((X.spectralSequence data).iso r (r + 1) pq rfl hr).hom =
      X.towerp data pq (r + 1) r (r + 1) (by lia) hr (by lia) ≫
        (X.towerPageXIso data pq (r + 1) (by lia)).inv :=
  -- `HomologicalComplex.homologyπ` is by definition the `homologyπ` of `sc`.
  X.liftCycles_homologyπ_spectralSequence_iso_hom data r (r + 1) rfl hr pq _ rfl
    _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl

/-- The kernel of the differential leaving `pq` on the page `r` is the image of the canonical map
`E^n(i₀(r + 1) ≤ i₁ ≤ i₂ ≤ i₃(r)) ⟶ E_r(pq)`. -/
lemma kernelSubobject_spectralSequence_page_sc_g (r : ℤ) (hr : r₀ ≤ r) :
    kernelSubobject (((X.spectralSequence data).page r).sc pq).g =
      imageSubobject (X.towerι data pq r (r + 1) r hr (by lia) hr ≫
        (X.towerPageXIso data pq r hr).inv) := by
  simp only [← X.towerLiftCycles_iCycles data pq r hr,
    ← ShortComplex.kernelSubobjectIsoCycles_inv_arrow, imageSubobject_mono]
  let S := ((X.spectralSequence data).page r).sc pq
  exact (Subobject.mk_eq_of_comm _
    (asIso (X.towerLiftCycles data pq r hr ≫ S.kernelSubobjectIsoCycles.inv)) (by simp [S])).symm

/-- The monomorphisms `towerι` compose: `Z_{r+1}` lies in `Z_r`. -/
@[reassoc]
lemma towerι_towerα (r : ℤ) (hr : r₀ ≤ r) :
    X.towerι data pq r (r + 1) r₀ hr (by lia) le_rfl ≫ X.towerα data pq r hr =
      X.towerα data pq (r + 1) (by lia) := by
  simp only [towerα_def, ← Category.assoc]
  congr 1
  exact X.mapFourδ₁Toδ₀'_comp ..

/-- The square relating the projections of the cycles onto the pages `r` and `r + 1`. -/
@[reassoc]
lemma towerι_towerπ (r : ℤ) (hr : r₀ ≤ r) :
    X.towerι data pq r (r + 1) r₀ hr (by lia) le_rfl ≫ X.towerπ data pq r hr =
      X.towerp data pq (r + 1) r₀ r (by lia) le_rfl hr ≫
        X.towerι data pq r (r + 1) r hr (by lia) hr ≫ (X.towerPageXIso data pq r hr).inv := by
  simp only [towerπ_def, ← Category.assoc]
  congr 1
  exact X.mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃' ..

/-- The inductive step for the cycles: if the presentation of the page `r` has cycles the image of
`towerα r` and projection `towerπ r`, then the preimage of the kernel of the differential leaving
`pq` is the image of `towerα (r + 1)`. -/
private lemma preimage_kernelSubobject_eq (r : ℤ) (hr : r₀ ≤ r)
    (P : TauCeti.SubquotientPresentation (((X.spectralSequence data).page r₀).X pq)
      (((X.spectralSequence data).page r).X pq)) (e : (P.Z : C) ≅ X.towerE data pq r r₀)
    (he : e.hom ≫ X.towerα data pq r hr = P.Z.arrow) (hπ : P.π = e.hom ≫ X.towerπ data pq r hr) :
    P.preimage (kernelSubobject (((X.spectralSequence data).page r).sc pq).g) =
      imageSubobject (X.towerα data pq (r + 1) (by lia)) := by
  have hker : kernelSubobject (X.towerπ data pq r hr) ≤
      imageSubobject (X.towerι data pq r (r + 1) r₀ hr (by lia) le_rfl) := by
    rw [towerπ_def, kernelSubobject_comp_mono]
    exact X.kernelSubobject_mapFourδ₄Toδ₃'_le_imageSubobject_mapFourδ₁Toδ₀' ..
  have hαe : X.towerα data pq r hr = e.inv ≫ P.Z.arrow := by rw [← he, Iso.inv_hom_id_assoc]
  rw [X.kernelSubobject_spectralSequence_page_sc_g data pq r hr]
  set ι := X.towerι data pq r (r + 1) r hr (by lia) hr ≫ (X.towerPageXIso data pq r hr).inv
  apply le_antisymm
  · apply Subobject.le_of_factors
    have hx : (P.preimage (imageSubobject ι)).Factors
        (ofLE _ _ (P.preimage_le_Z (imageSubobject ι)) ≫ P.Z.arrow) := by
      rw [ofLE_arrow]; exact Subobject.factors_self _
    rw [P.factors_preimage_iff, hπ, ← Category.assoc] at hx
    obtain ⟨A, π, _, z, hz⟩ := (imageSubobject_factors_iff_up_to_refinements _ _).1
      (imageSubobject_factors_of_comm _ _ _ _ (X.towerι_towerπ data pq r hr) hker _ hx)
    refine (imageSubobject_factors_iff_up_to_refinements _ _).2 ⟨A, π, inferInstance, z, ?_⟩
    rw [← X.towerι_towerα data pq r hr, ← reassoc_of% hz,
      ← ofLE_arrow (P.preimage_le_Z (imageSubobject ι)), hαe, Iso.hom_inv_id_assoc]
  · apply Subobject.le_of_factors
    rw [← Subobject.factors_epi_comp_iff _ (factorThruImageSubobject _),
      imageSubobject_arrow_comp, ← X.towerι_towerα data pq r hr, hαe, ← Category.assoc,
      P.factors_preimage_iff, Category.assoc, hπ, Iso.inv_hom_id_assoc,
      X.towerι_towerπ data pq r hr]
    exact imageSubobject_factors_comp_self _ _

/-- A morphism into the kernel of the differential leaving `pq` on the page `r` which lifts
`y ≫ towerι ≫ (towerPageXIso r).inv` is sent to `y ≫ towerLiftCycles` in the cycles. -/
private lemma comp_kernelSubobjectIsoCycles_hom_eq (r : ℤ) (hr : r₀ ≤ r) {W : C}
    (x : W ⟶ (kernelSubobject (((X.spectralSequence data).page r).sc pq).g : C))
    (y : W ⟶ X.towerE data pq (r + 1) r)
    (hx : x ≫ (kernelSubobject (((X.spectralSequence data).page r).sc pq).g).arrow =
      y ≫ X.towerι data pq r (r + 1) r hr (by lia) hr ≫ (X.towerPageXIso data pq r hr).inv) :
    x ≫ (((X.spectralSequence data).page r).sc pq).kernelSubobjectIsoCycles.hom =
      y ≫ X.towerLiftCycles data pq r hr := by
  rw [← cancel_mono (((X.spectralSequence data).page r).sc pq).iCycles, Category.assoc,
    ShortComplex.kernelSubobjectIsoCycles_hom_iCycles, hx, Category.assoc, towerLiftCycles_iCycles]

/-- If `K ≤ L` are subobjects identified with the images of `towerα (r + 1)` and `towerα r`, then
the inclusion `K ⟶ L` is `towerι`. -/
@[reassoc]
private lemma iso_inv_ofLE_iso_hom (r : ℤ) (hr : r₀ ≤ r)
    {K L : Subobject (((X.spectralSequence data).page r₀).X pq)} (h : K ≤ L)
    (e : (L : C) ≅ X.towerE data pq r r₀) (he : e.hom ≫ X.towerα data pq r hr = L.arrow)
    (e' : (K : C) ≅ X.towerE data pq (r + 1) r₀)
    (he' : e'.hom ≫ X.towerα data pq (r + 1) (by lia) = K.arrow) :
    e'.inv ≫ ofLE K L h ≫ e.hom = X.towerι data pq r (r + 1) r₀ hr (by lia) le_rfl := by
  rw [← cancel_mono (X.towerα data pq r hr), Category.assoc, Category.assoc, he, ofLE_arrow,
    towerι_towerα, ← he', Iso.inv_hom_id_assoc]

/-- The presentation of the page `r` at `pq` inside the page `r₀`: its larger subobject is the
image of `towerα` and its projection is `towerπ`. -/
theorem exists_iso_pagePresentation (r : ℤ) (hr : r₀ ≤ r) :
    ∃ e : (((X.spectralSequence data).pagePresentation pq r hr).Z : C) ≅
        X.towerE data pq r r₀,
      e.hom ≫ X.towerα data pq r hr =
          ((X.spectralSequence data).pagePresentation pq r hr).Z.arrow ∧
        ((X.spectralSequence data).pagePresentation pq r hr).π =
          e.hom ≫ X.towerπ data pq r hr := by
  induction r, hr using Int.leInduction with
  | base =>
    rw [SpectralSequence.pagePresentation_self]
    refine ⟨Subobject.isoOfEq _ _ TauCeti.SubquotientPresentation.refl_Z ≪≫
      asIso (⊤ : Subobject _).arrow ≪≫ X.towerPageXIso data pq r₀ le_rfl, ?_, ?_⟩
    · simp [towerα_def]
    · simp [towerπ_def, TauCeti.SubquotientPresentation.π_refl]
  | succ r hr ih =>
    rw [SpectralSequence.pagePresentation_add_one _ _ r hr]
    generalize (X.spectralSequence data).pagePresentation pq r hr = P at ih ⊢
    obtain ⟨e, he, hπ⟩ := ih
    let S := ((X.spectralSequence data).page r).sc pq
    let Q := (P.trans S.homologyPresentation).mapIso
      ((X.spectralSequence data).iso r (r + 1) pq rfl hr)
    have hZ : Q.Z = Subobject.mk (X.towerα data pq (r + 1) (by lia)) := by
      rw [TauCeti.SubquotientPresentation.mapIso_Z, TauCeti.SubquotientPresentation.trans_Z,
        ShortComplex.homologyPresentation_Z, X.preimage_kernelSubobject_eq data pq r hr P e he hπ,
        imageSubobject_mono]
    obtain ⟨e', he'⟩ : ∃ e' : (Q.Z : C) ≅ X.towerE data pq (r + 1) r₀,
        e'.hom ≫ X.towerα data pq (r + 1) (by lia) = Q.Z.arrow :=
      ⟨Subobject.isoOfEq _ _ hZ ≪≫ Subobject.underlyingIso _, by simp⟩
    refine ⟨e', he', ?_⟩
    rw [TauCeti.SubquotientPresentation.π_mapIso', TauCeti.SubquotientPresentation.π_trans',
      ShortComplex.π_homologyPresentation', ← cancel_epi e'.inv, Iso.inv_hom_id_assoc]
    simp only [← Category.assoc]
    rw [X.comp_kernelSubobjectIsoCycles_hom_eq data pq r hr _
      (X.towerp data pq (r + 1) r₀ r (by lia) le_rfl hr)]
    · simp only [Category.assoc, towerLiftCycles_homologyπ_iso_hom, towerπ_def]
      exact X.mapFourδ₄Toδ₃'_comp_assoc ..
    · simp only [Category.assoc, ofLE_arrow, TauCeti.SubquotientPresentation.preimageπ_arrow,
        ofLE_comp_ofLE_assoc, hπ, ← X.towerι_towerπ data pq r hr]
      exact X.iso_inv_ofLE_iso_hom_assoc data pq r hr _ e he e' he' _

/-- **The cycle tower of the spectral sequence of a spectral object.** The cycles `Z_r(pq)` are
the image of `E^n(i₀(r) ≤ i₁ ≤ i₂ ≤ i₃(r₀)) ⟶ E^n(i₀(r₀) ≤ i₁ ≤ i₂ ≤ i₃(r₀)) = E_{r₀}(pq)`. -/
theorem cyclesSubobject_spectralSequence (r : ℤ) (hr : r₀ ≤ r) :
    (X.spectralSequence data).cyclesSubobject pq r hr =
      imageSubobject (X.towerα data pq r hr) := by
  have h := X.exists_iso_pagePresentation data pq r hr
  rw [← SpectralSequence.pagePresentation_Z _ pq r hr]
  generalize (X.spectralSequence data).pagePresentation pq r hr = P at h ⊢
  obtain ⟨e, he, -⟩ := h
  rw [imageSubobject_mono]
  exact (Subobject.mk_eq_of_comm _ e.symm (by rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc])).symm

/-- The square relating `towerα`, `towerβ` and `towerπ`. -/
@[reassoc]
lemma towerα_towerβ (r : ℤ) (hr : r₀ ≤ r) :
    X.towerα data pq r hr ≫ X.towerβ data pq r hr = X.towerπ data pq r hr ≫
      (X.towerPageXIso data pq r hr).hom ≫ X.towerι data pq r₀ r r le_rfl hr hr := by
  simp only [towerα_def, towerβ_def, towerπ_def, Category.assoc, Iso.inv_hom_id_assoc]
  exact X.mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃' ..

/-- **The boundary tower of the spectral sequence of a spectral object.** The boundaries
`B_r(pq)` are the kernel of `E_{r₀}(pq) = E^n(i₀(r₀) ≤ i₁ ≤ i₂ ≤ i₃(r₀)) ⟶
E^n(i₀(r₀) ≤ i₁ ≤ i₂ ≤ i₃(r))`. -/
theorem boundariesSubobject_spectralSequence (r : ℤ) (hr : r₀ ≤ r) :
    (X.spectralSequence data).boundariesSubobject pq r hr =
      kernelSubobject (X.towerβ data pq r hr) := by
  have h := X.exists_iso_pagePresentation data pq r hr
  rw [← SpectralSequence.pagePresentation_B _ pq r hr]
  generalize (X.spectralSequence data).pagePresentation pq r hr = P at h ⊢
  obtain ⟨e, he, hπ⟩ := h
  have hsq := X.towerα_towerβ data pq r hr
  apply le_antisymm
  · refine le_kernelSubobject _ _ ?_
    rw [← ofLE_arrow P.le, Category.assoc, ← he, Category.assoc, hsq, ← Category.assoc e.hom,
      ← hπ, ← Category.assoc, (P.factors_B_iff _).1 (by rw [ofLE_arrow]; exact factors_self _),
      zero_comp]
  · apply Subobject.le_of_factors
    have h1 : (imageSubobject (X.towerι data pq r₀ r r₀ le_rfl hr le_rfl)).Factors
        ((kernelSubobject (X.towerβ data pq r hr)).arrow ≫
          (X.towerPageXIso data pq r₀ le_rfl).hom) :=
      Subobject.factors_of_le _
        (X.kernelSubobject_mapFourδ₄Toδ₃'_le_imageSubobject_mapFourδ₁Toδ₀' ..)
        (kernelSubobject_factors _ _ (by
          simpa [towerβ_def] using kernelSubobject_arrow_comp (X.towerβ data pq r hr)))
    -- `towerι` is a monomorphism, so the kernel of `towerβ` lifts along `towerα`.
    rw [imageSubobject_mono] at h1
    obtain ⟨t, ht⟩ : ∃ t, t ≫ X.towerι data pq r₀ r r₀ le_rfl hr le_rfl =
        (kernelSubobject (X.towerβ data pq r hr)).arrow ≫ (X.towerPageXIso data pq r₀ le_rfl).hom :=
      ⟨_ ≫ (underlyingIso _).hom, by rw [Category.assoc, underlyingIso_hom_comp_eq_mk,
        factorThru_arrow _ _ h1]⟩
    have ht' : t ≫ X.towerα data pq r hr = (kernelSubobject (X.towerβ data pq r hr)).arrow := by
      rw [towerα_def, reassoc_of% ht, Iso.hom_inv_id, Category.comp_id]
    rw [← ht', (Iso.eq_inv_comp e).2 he, ← Category.assoc, P.factors_B_iff,
      ← cancel_mono ((X.towerPageXIso data pq r hr).hom ≫ X.towerι data pq r₀ r r le_rfl hr hr),
      zero_comp, hπ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← hsq, reassoc_of% ht', kernelSubobject_arrow_comp]

end Tower

end CategoryTheory.Abelian.SpectralObject
