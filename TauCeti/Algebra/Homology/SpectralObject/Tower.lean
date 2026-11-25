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
image of `E^n(i₀(r + 1) ≤ i₁ ≤ i₂ ≤ i₃(r))` (Mathlib's homology data of the pages), and its preimage
under the projection is computed by the fact that boundaries are permanent cycles: the kernel of
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
  · rfl
  · exact image_le_kernel _ _ (X.d_d (𝟙 a') (homOfLE h₀) (homOfLE h₁) (homOfLE h₂)
      (homOfLE h₃) (homOfLE h₄) (𝟙 b') (n₀ - 1) n₀ n₁ n₂ (n₂ + 1) (by lia) hn₁ hn₂ rfl)

/-- **Lifting factorizations along a commutative square.** Let `α ≫ p = p' ≫ α'` with `p'` an
epimorphism, and suppose that the kernel of `p` lies in the image of `α`. If `y ≫ p` factors
through the image of `α'`, then `y` factors through the image of `α`. -/
lemma _root_.CategoryTheory.imageSubobject_factors_of_comm {E F E' F' W : C} (p : E ⟶ F)
    (α : E' ⟶ E) (α' : F' ⟶ F) (p' : E' ⟶ F') [Epi p'] (w : α ≫ p = p' ≫ α')
    (h : kernelSubobject p ≤ imageSubobject α) (y : W ⟶ E)
    (hy : (imageSubobject α').Factors (y ≫ p)) : (imageSubobject α).Factors y := by
  obtain ⟨A₁, π₁, _, x, hx⟩ := (imageSubobject_factors_iff_up_to_refinements α' _).1 hy
  obtain ⟨A₂, π₂, _, z, hz⟩ := surjective_up_to_refinements_of_epi p' x
  rw [← Subobject.factors_epi_comp_iff _ (π₂ ≫ π₁)]
  have hk : (kernelSubobject p).Factors ((π₂ ≫ π₁) ≫ y - z ≫ α) :=
    kernelSubobject_factors _ _ (by
      rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hx, Category.assoc, w,
        ← Category.assoc z, ← hz, Category.assoc, sub_self])
  have := Subobject.factors_add _ _ (Subobject.factors_of_le _ h hk)
    (imageSubobject_factors_comp_self α z)
  rwa [sub_add_cancel] at this

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

instance (r : ℤ) (hr : r₀ ≤ r) : Mono (X.towerα data pq r hr) := by
  dsimp [towerα]
  infer_instance

/-- The epimorphism `E^n(i₀(r) ≤ i₁ ≤ i₂ ≤ i₃(r₀)) ⟶ E_r(pq)`, which is the projection of the
cycle tower onto the page `r`. -/
noncomputable def towerπ (r : ℤ) (hr : r₀ ≤ r) :
    X.towerE data pq r r₀ ⟶ ((X.spectralSequence data).page r).X pq :=
  X.towerp data pq r r₀ r hr le_rfl hr ≫ (X.towerPageXIso data pq r hr).inv

/-- The epimorphism `E_{r₀}(pq) ⟶ E^n(i₀(r₀) ≤ i₁ ≤ i₂ ≤ i₃(r))`, whose kernel is the boundary
tower `B_r(pq)`. -/
noncomputable def towerβ (r : ℤ) (hr : r₀ ≤ r) :
    ((X.spectralSequence data).page r₀).X pq ⟶ X.towerE data pq r₀ r :=
  (X.towerPageXIso data pq r₀ le_rfl).hom ≫ X.towerp data pq r₀ r₀ r le_rfl le_rfl hr

/-- The kernel of the differential leaving `pq` on the page `r` is the image of the canonical map
`E^n(i₀(r + 1) ≤ i₁ ≤ i₂ ≤ i₃(r)) ⟶ E_r(pq)`. -/
lemma kernelSubobject_spectralSequence_page_sc_g (r : ℤ) (hr : r₀ ≤ r) :
    kernelSubobject (((X.spectralSequence data).page r).sc pq).g =
      imageSubobject (X.towerι data pq r (r + 1) r hr (by lia) hr ≫
        (X.towerPageXIso data pq r hr).inv) := by
  let S := ((X.spectralSequence data).page r).sc pq
  have hd := X.mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv_d data r (r + 1) rfl hr pq
    ((c r).next pq) _ _ _ _ _ rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq)
    (data.deg pq + 1) rfl
  let L := ((X.spectralSequence data).page r).liftCycles _ _ rfl hd
  have hL : L ≫ S.iCycles = X.towerι data pq r (r + 1) r hr (by lia) hr ≫
      (X.towerPageXIso data pq r hr).inv := HomologicalComplex.liftCycles_i _ _ _ _ _
  have : IsIso L := X.isIso_liftCycles_mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv data r
    (r + 1) rfl hr pq _ rfl _ _ _ _ _ rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq)
    (data.deg pq + 1) rfl
  simp only [← hL, ← S.kernelSubobjectIsoCycles_inv_arrow, imageSubobject_mono]
  exact (Subobject.mk_eq_of_comm _ (asIso (L ≫ S.kernelSubobjectIsoCycles.inv)) (by simp)).symm

/-- The monomorphisms `towerι` compose: `Z_{r+1}` lies in `Z_r`. -/
lemma towerι_towerα (r : ℤ) (hr : r₀ ≤ r) :
    X.towerι data pq r (r + 1) r₀ hr (by lia) le_rfl ≫ X.towerα data pq r hr =
      X.towerα data pq (r + 1) (by lia) := by
  simp only [towerα, ← Category.assoc]
  congr 1
  exact X.mapFourδ₁Toδ₀'_comp ..

/-- The square relating the projections of the cycles onto the pages `r` and `r + 1`. -/
lemma towerι_towerπ (r : ℤ) (hr : r₀ ≤ r) :
    X.towerι data pq r (r + 1) r₀ hr (by lia) le_rfl ≫ X.towerπ data pq r hr =
      X.towerp data pq (r + 1) r₀ r (by lia) le_rfl hr ≫
        X.towerι data pq r (r + 1) r hr (by lia) hr ≫ (X.towerPageXIso data pq r hr).inv := by
  simp only [towerπ, ← Category.assoc]
  congr 1
  exact X.mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃' ..

/-- The inductive step for the cycles: if the presentation of the page `r` has cycles the image of
`towerα r` and projection `towerπ r`, then the preimage of the kernel of the differential leaving
`pq` is the image of `towerα (r + 1)`. -/
lemma preimage_kernelSubobject_eq (r : ℤ) (hr : r₀ ≤ r)
    (P : TauCeti.SubquotientPresentation (((X.spectralSequence data).page r₀).X pq)
      (((X.spectralSequence data).page r).X pq)) (e : (P.Z : C) ≅ X.towerE data pq r r₀)
    (he : e.hom ≫ X.towerα data pq r hr = P.Z.arrow) (hπ : P.π = e.hom ≫ X.towerπ data pq r hr) :
    P.preimage (kernelSubobject (((X.spectralSequence data).page r).sc pq).g) =
      imageSubobject (X.towerα data pq (r + 1) (by lia)) := by
  have hker : kernelSubobject (X.towerπ data pq r hr) ≤
      imageSubobject (X.towerι data pq r (r + 1) r₀ hr (by lia) le_rfl) := by
    rw [towerπ, kernelSubobject_comp_mono]
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
    rw [← X.towerι_towerα data pq r hr, ← reassoc_of% hz, ← ofLE_arrow (P.preimage_le_Z _), hαe]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  · apply Subobject.le_of_factors
    rw [← Subobject.factors_epi_comp_iff _ (factorThruImageSubobject _),
      imageSubobject_arrow_comp, ← X.towerι_towerα data pq r hr, hαe, ← Category.assoc,
      P.factors_preimage_iff, Category.assoc, hπ, Iso.inv_hom_id_assoc,
      X.towerι_towerπ data pq r hr]
    exact imageSubobject_factors_comp_self _ _

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
    · simp [towerα]
    · simp [towerπ, TauCeti.SubquotientPresentation.π_refl]
  | succ r hr ih =>
    rw [SpectralSequence.pagePresentation_add_one _ _ r hr]
    generalize (X.spectralSequence data).pagePresentation pq r hr = P at ih ⊢
    obtain ⟨e, he, hπ⟩ := ih
    let S := ((X.spectralSequence data).page r).sc pq
    have hZ := X.preimage_kernelSubobject_eq data pq r hr P e he hπ
    refine ⟨Subobject.isoOfEq _ (Subobject.mk (X.towerα data pq (r + 1) (by lia))) ?_ ≪≫
      Subobject.underlyingIso _, ?_, ?_⟩
    · rw [← imageSubobject_mono, ← hZ]; rfl
    · simp
    · rw [TauCeti.SubquotientPresentation.π_mapIso, TauCeti.SubquotientPresentation.π_trans,
        ShortComplex.π_homologyPresentation]
      refine (Iso.inv_comp_eq _).1 ?_
      have hy : (Subobject.isoOfEq _ (Subobject.mk (X.towerα data pq (r + 1) (by lia)))
            (by rw [← imageSubobject_mono, ← hZ]) ≪≫ Subobject.underlyingIso _).inv ≫
          P.preimageπ (kernelSubobject S.g) ≫ S.kernelSubobjectIsoCycles.hom =
          X.towerp data pq (r + 1) r₀ r (by lia) le_rfl hr ≫
            ((X.spectralSequence data).page r).liftCycles _ _ rfl
              (X.mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv_d data r (r + 1) rfl hr pq
                ((c r).next pq) _ _ _ _ _ rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq)
                (data.deg pq + 1) rfl) := by
        rw [← cancel_mono S.iCycles]
        simp only [Category.assoc, ShortComplex.kernelSubobjectIsoCycles_hom_iCycles,
          TauCeti.SubquotientPresentation.preimageπ_arrow, hπ]
        erw [HomologicalComplex.liftCycles_i]
        rw [← X.towerι_towerπ data pq r hr]
        simp only [← Category.assoc]
        congr 1
        rw [← cancel_mono (X.towerα data pq r hr), Category.assoc, he, X.towerι_towerα,
          Category.assoc, ofLE_arrow]
        simp
      have h2 := hy =≫ (S.homologyπ ≫ ((X.spectralSequence data).iso r (r + 1) pq rfl hr).hom)
      simp only [Iso.trans_inv, Category.assoc] at h2
      erw [X.liftCycles_homologyπ_spectralSequence_iso_hom data r (r + 1) rfl hr pq _ rfl
        _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
        rfl] at h2
      refine Eq.trans ?_ (h2.trans ?_)
      · simp only [Iso.trans_inv]
        erw [Category.assoc, Category.assoc, Category.assoc]; rfl
      · simp only [towerπ, ← Category.assoc]
        congr 1
        exact X.mapFourδ₄Toδ₃'_comp ..

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
private lemma towerα_towerβ (r : ℤ) (hr : r₀ ≤ r) :
    X.towerα data pq r hr ≫ X.towerβ data pq r hr = X.towerπ data pq r hr ≫
      (X.towerPageXIso data pq r hr).hom ≫ X.towerι data pq r₀ r r le_rfl hr hr := by
  simp only [towerα, towerβ, towerπ, Category.assoc, Iso.inv_hom_id_assoc]
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
  obtain ⟨u, hu⟩ : ∃ u, u = (kernelSubobject P.π).arrow ≫ P.Z.arrow := ⟨_, rfl⟩
  have : Mono u := hu ▸ inferInstance
  have hB : P.B = Subobject.mk u := by
    calc P.B = (Subobject.map P.Z.arrow).obj (kernelSubobject P.π) := by
          rw [P.kernelSubobject_π, map_pullback_arrow_of_le P.le]
      _ = (Subobject.map P.Z.arrow).obj (Subobject.mk (kernelSubobject P.π).arrow) := by
          rw [mk_arrow]
      _ = Subobject.mk u := by rw [Subobject.map_mk]; subst hu; rfl
  have hsq := X.towerα_towerβ data pq r hr
  rw [hB]
  apply le_antisymm
  · apply Subobject.le_of_factors
    rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    refine Subobject.factors_of_factors_right _ (kernelSubobject_factors _ _ ?_)
    rw [hu, Category.assoc, ← he, Category.assoc, hsq, ← Category.assoc e.hom, ← hπ,
      ← Category.assoc, kernelSubobject_arrow_comp, zero_comp]
  · apply Subobject.le_of_factors
    have h1 : (imageSubobject (X.towerι data pq r₀ r r₀ le_rfl hr le_rfl)).Factors
        ((kernelSubobject (X.towerβ data pq r hr)).arrow ≫
          (X.towerPageXIso data pq r₀ le_rfl).hom) :=
      Subobject.factors_of_le _
        (X.kernelSubobject_mapFourδ₄Toδ₃'_le_imageSubobject_mapFourδ₁Toδ₀' ..)
        (kernelSubobject_factors _ _ (by
          simpa [towerβ] using kernelSubobject_arrow_comp (X.towerβ data pq r hr)))
    obtain ⟨A, π, _, z, hz⟩ := (imageSubobject_factors_iff_up_to_refinements _ _).1 h1
    have hz' : π ≫ (kernelSubobject (X.towerβ data pq r hr)).arrow =
        z ≫ X.towerα data pq r hr := by
      rw [towerα, ← reassoc_of% hz]
      simp
    have hz0 : (z ≫ e.inv) ≫ P.π = 0 := by
      rw [← cancel_mono ((X.towerPageXIso data pq r hr).hom ≫
        X.towerι data pq r₀ r r le_rfl hr hr), zero_comp, hπ]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← hsq, ← reassoc_of% hz', kernelSubobject_arrow_comp, comp_zero]
    rw [← Subobject.factors_epi_comp_iff _ π, hz', Subobject.mk_factors_iff]
    refine ⟨(kernelSubobject P.π).factorThru _ (kernelSubobject_factors _ _ hz0), ?_⟩
    change _ ≫ u = _
    rw [hu, ← Category.assoc, Subobject.factorThru_arrow, Category.assoc, ← he,
      Iso.inv_hom_id_assoc]

end Tower

end CategoryTheory.Abelian.SpectralObject
