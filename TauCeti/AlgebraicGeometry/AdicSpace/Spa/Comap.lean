/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic

/-!
# Pullbacks and quotient embeddings of sub-unit valuation loci

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Definition 7.23, Remark 7.30, and
Proposition 7.38.**

This file constructs the contravariant continuous map on sub-unit valuation loci induced by a
continuous ring homomorphism preserving the chosen subrings:

```text
spaComap φ : spa Bplus → spa Aplus
```

No Huber-ring hypotheses are needed. The bundled version for morphisms of Huber pairs is in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair`.

## Main definitions

* `TauCeti.ValuationSpectrum.spaComap`: the pullback map `spa Bplus → spa Aplus`.
* `TauCeti.ValuationSpectrum.spaComapTopHom`: the same map as a morphism of `TopCat`.
* `TauCeti.ValuationSpectrum.spaComapHomeomorph`: homeomorphism `spa Bplus ≃ₜ spa Aplus`
  induced by mutually inverse continuous ring homomorphisms.
* `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv`: homeomorphism `spa Aplus ≃ₜ spa Bplus`
  induced by a topological ring equivalence carrying `Aplus` onto `Bplus`.

## Main results

* `TauCeti.ValuationSpectrum.comap_mem_spa`: pullback preserves the sub-unit locus.
* `TauCeti.ValuationSpectrum.comap_preimage_spa_inter_inter_spa`: pulling back a subset
  `spa A⁺ ∩ S` cut out by a condition `S`.
* `TauCeti.ValuationSpectrum.mem_spa_map_iff`: a continuous point lies over the image plus ring
  exactly when its pullback lies over the original one.
* `TauCeti.ValuationSpectrum.continuous_spaComap`: `spaComap` is continuous.
* `TauCeti.ValuationSpectrum.spaComap_id`, `spaComap_comp`, `spaComapTopHom_id`,
  `spaComapTopHom_comp`: contravariant functoriality.
* `TauCeti.ValuationSpectrum.spaComap_spaComap`, `mem_of_spaComap_mem_map`: pulling back along a
  left inverse of `φ` and then along `φ` is the identity.
* `TauCeti.ValuationSpectrum.coe_spaComapHomeomorph`,
  `coe_spaComapHomeomorph_symm`, `spaComapHomeomorph_val`,
  `spaComapHomeomorph_symm_val`: coercion and valuation pullback formulas for
  `spaComapHomeomorph`.
* `TauCeti.ValuationSpectrum.coe_spaHomeomorphOfRingEquiv`,
  `coe_spaHomeomorphOfRingEquiv_symm`, `spaHomeomorphOfRingEquiv_val`,
  `spaHomeomorphOfRingEquiv_symm_val`: coercion and valuation pullback formulas for
  `spaHomeomorphOfRingEquiv`.
* `TauCeti.ValuationSpectrum.comap_preimage_rationalSubset_inter_spa`,
  `spaComap_preimage_rationalSubset`, `map_spaComapTopHom_obj_spaBasicOpen`: preimages of
  rational subsets.
* `TauCeti.ValuationSpectrum.comap_mem_rationalSubset`,
  `TauCeti.ValuationSpectrum.vle_one_of_comap_mem_rationalSubset`,
  `TauCeti.ValuationSpectrum.rationalSubset_image_eq_spa`: elementwise criteria for rational
  subsets under pullback.
* `TauCeti.ValuationSpectrum.isEmbedding_spaComap`: an embedding of valuation spectra restricts
  to an embedding of sub-unit loci.
* `TauCeti.ValuationSpectrum.isOpen_supp_comap_quotientMk_iff`,
  `isEmbedding_spaComap_quotientMk`,
  `range_spaComap_quotientMk`, `isClosedEmbedding_spaComap_quotientMk`: the quotient map for the
  image plus ring is a closed embedding with support locus as its range.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.23, Remark 7.30, Proposition 7.38.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), branch `dev/adic-spaces` at commit
`37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`, files `AffinoidRings.lean` and
`AdicSpectrum.lean`, was consulted rather than copied for the induced map and quotient embedding.
It bundles the plus ring into its affinoid ring and phrases those results at that level. Here the
plus subrings are explicit, the generic results require no Huber hypotheses, and the bundled
Huber-pair interface is provided separately. The rational-subset criteria are direct proofs;
AINTLIB was not consulted for them.
-/

public section

namespace TauCeti.ValuationSpectrum

open Valuation

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
  [CommRing C] [TopologicalSpace C]

/-- A continuous ring homomorphism mapping `A⁺` into `B⁺` pulls points of `spa (B, B⁺)` back
to points of `spa (A, A⁺)`. -/
theorem comap_mem_spa {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) {v : Spv B} (hv : v ∈ spa Bplus) :
    comap φ v ∈ spa Aplus := by
  rw [mem_spa_iff] at hv ⊢
  refine ⟨hv.1.comap hφ, fun a ha ↦ ?_⟩
  rw [comap_vle, map_one]
  exact hv.2 (φ a) (hplus a ha)

/-- Pulling back a subset of `spa (A, A⁺)` cut out by a condition `S`: the points of
`spa (B, B⁺)` whose pullback lies in `spa (A, A⁺) ∩ S` are those whose pullback lies in `S`. -/
theorem comap_preimage_spa_inter_inter_spa {φ : A →+* B} (hφ : Continuous φ)
    {Aplus : Subring A} {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (S : Set (Spv A)) :
    comap φ ⁻¹' (spa Aplus ∩ S) ∩ spa Bplus = spa Bplus ∩ comap φ ⁻¹' S := by
  ext v
  exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨comap_mem_spa hφ hplus h.1, h.2⟩, h.1⟩⟩

/-- A continuous point of `Spv B` lies in `spa (φ(A⁺))` exactly when its pullback along a
continuous ring homomorphism `φ : A →+* B` lies in `spa A⁺`. -/
theorem mem_spa_map_iff {φ : A →+* B} (hφ : Continuous φ) (Aplus : Subring A) {w : Spv B}
    (hw : w.IsContinuous) : w ∈ spa (Aplus.map φ) ↔ comap φ w ∈ spa Aplus := by
  simp [hw, hw.comap hφ, -isContinuous_def]

/-- The contravariant map on sub-unit valuation loci induced by a continuous ring homomorphism
`φ : A →+* B` carrying `Aplus` into `Bplus`. -/
def spaComap (φ : A →+* B) (hφ : Continuous φ) (Aplus : Subring A) (Bplus : Subring B)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (v : spa Bplus) : spa Aplus :=
  ⟨comap φ v.val, comap_mem_spa hφ hplus v.property⟩

@[simp]
theorem spaComap_val (φ : A →+* B) (hφ : Continuous φ) (Aplus : Subring A)
    (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (v : spa Bplus) :
    (spaComap φ hφ Aplus Bplus hplus v).val = comap φ v.val := (rfl)

/-- `spaComap` is continuous for the subspace topologies. -/
theorem continuous_spaComap (φ : A →+* B) (hφ : Continuous φ) (Aplus : Subring A)
    (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) :
    Continuous (spaComap φ hφ Aplus Bplus hplus) := by
  rw [continuous_induced_rng]
  exact (continuous_comap φ).comp continuous_subtypeVal

/-- `spaComap` of the identity homomorphism is the identity map on `spa Aplus`. -/
@[simp]
theorem spaComap_id {A : Type*} [CommRing A] [TopologicalSpace A] (Aplus : Subring A) :
    spaComap (RingHom.id A) continuous_id Aplus Aplus (fun _ ha ↦ ha) = _root_.id :=
  funext fun ⟨v, _⟩ ↦ Subtype.ext (congr_fun comap_id v)

/-- `spaComap` is contravariantly functorial: `spaComap (ψ ∘ φ) = spaComap φ ∘ spaComap ψ`. -/
@[simp]
theorem spaComap_comp {φ : A →+* B} (hφ : Continuous φ) {ψ : B →+* C} (hψ : Continuous ψ)
    (Aplus : Subring A) (Bplus : Subring B) (Cplus : Subring C)
    (hφ_plus : ∀ a ∈ Aplus, φ a ∈ Bplus) (hψ_plus : ∀ b ∈ Bplus, ψ b ∈ Cplus) :
    spaComap (ψ.comp φ) (hψ.comp hφ) Aplus Cplus
        (fun a ha ↦ hψ_plus (φ a) (hφ_plus a ha)) =
      spaComap φ hφ Aplus Bplus hφ_plus ∘ spaComap ψ hψ Bplus Cplus hψ_plus :=
  funext fun ⟨v, _⟩ ↦ Subtype.ext (congr_fun (comap_comp φ ψ) v)

/-- Pulling back along a left inverse `ψ` of `φ` and then along `φ` is the identity of
`Spa(A, A⁺)`. -/
theorem spaComap_spaComap (φ : A →+* B) (hφ : Continuous φ) {Aplus : Subring A}
    {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (ψ : B →+* A) (hψ : Continuous ψ)
    (hψφ : ∀ a, ψ (φ a) = a) (hplus' : ∀ b ∈ Bplus, ψ b ∈ Aplus) (w : ↥(spa Aplus)) :
    spaComap φ hφ Aplus Bplus hplus (spaComap ψ hψ Bplus Aplus hplus' w) = w := by
  have hcomp : ψ.comp φ = RingHom.id A := RingHom.ext hψφ
  refine Subtype.ext ?_
  rw [spaComap_val, spaComap_val, ← Function.comp_apply (f := comap φ), ← comap_comp, hcomp,
    comap_id, id]

/-- **Homeomorphism of adic spectra induced by mutually inverse continuous ring homomorphisms.**
Given continuous ring homomorphisms `φ : A →+* B` and `ψ : B →+* A` that are mutually inverse
and carry `A⁺` into `B⁺` and `B⁺` into `A⁺`, pulling valuations back along `φ` and `ψ` identifies
`Spa(B, B⁺)` homeomorphically with `Spa(A, A⁺)`. -/
@[expose] noncomputable def spaComapHomeomorph (φ : A →+* B) (hφ : Continuous φ)
    {Aplus : Subring A} {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (ψ : B →+* A) (hψ : Continuous ψ) (hψφ : ∀ a, ψ (φ a) = a) (hφψ : ∀ b, φ (ψ b) = b)
    (hplus' : ∀ b ∈ Bplus, ψ b ∈ Aplus) : spa Bplus ≃ₜ spa Aplus where
  toFun := spaComap φ hφ Aplus Bplus hplus
  invFun := spaComap ψ hψ Bplus Aplus hplus'
  left_inv := spaComap_spaComap ψ hψ hplus' φ hφ hφψ hplus
  right_inv := spaComap_spaComap φ hφ hplus ψ hψ hψφ hplus'
  continuous_toFun := continuous_spaComap _ hφ _ _ _
  continuous_invFun := continuous_spaComap _ hψ _ _ _

/-- `spaComapHomeomorph` coerces to `spaComap` along `φ`. -/
theorem coe_spaComapHomeomorph (φ : A →+* B) (hφ : Continuous φ)
    {Aplus : Subring A} {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (ψ : B →+* A) (hψ : Continuous ψ) (hψφ : ∀ a, ψ (φ a) = a) (hφψ : ∀ b, φ (ψ b) = b)
    (hplus' : ∀ b ∈ Bplus, ψ b ∈ Aplus) :
    (spaComapHomeomorph φ hφ hplus ψ hψ hψφ hφψ hplus' : spa Bplus → spa Aplus) =
      spaComap φ hφ Aplus Bplus hplus := (rfl)

/-- The inverse of `spaComapHomeomorph` coerces to `spaComap` along `ψ`. -/
theorem coe_spaComapHomeomorph_symm (φ : A →+* B) (hφ : Continuous φ)
    {Aplus : Subring A} {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (ψ : B →+* A) (hψ : Continuous ψ) (hψφ : ∀ a, ψ (φ a) = a) (hφψ : ∀ b, φ (ψ b) = b)
    (hplus' : ∀ b ∈ Bplus, ψ b ∈ Aplus) :
    ((spaComapHomeomorph φ hφ hplus ψ hψ hψφ hφψ hplus').symm : spa Aplus → spa Bplus) =
      spaComap ψ hψ Bplus Aplus hplus' := (rfl)

/-- `spaComapHomeomorph` pulls valuations back along `φ`. -/
@[simp] theorem spaComapHomeomorph_val (φ : A →+* B) (hφ : Continuous φ)
    {Aplus : Subring A} {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (ψ : B →+* A) (hψ : Continuous ψ) (hψφ : ∀ a, ψ (φ a) = a) (hφψ : ∀ b, φ (ψ b) = b)
    (hplus' : ∀ b ∈ Bplus, ψ b ∈ Aplus) (v : spa Bplus) :
    (spaComapHomeomorph φ hφ hplus ψ hψ hψφ hφψ hplus' v : Spv A) = comap φ v.val := (rfl)

/-- The inverse of `spaComapHomeomorph` pulls valuations back along `ψ`. -/
@[simp] theorem spaComapHomeomorph_symm_val (φ : A →+* B) (hφ : Continuous φ)
    {Aplus : Subring A} {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (ψ : B →+* A) (hψ : Continuous ψ) (hψφ : ∀ a, ψ (φ a) = a) (hφψ : ∀ b, φ (ψ b) = b)
    (hplus' : ∀ b ∈ Bplus, ψ b ∈ Aplus) (w : spa Aplus) :
    ((spaComapHomeomorph φ hφ hplus ψ hψ hψφ hφψ hplus').symm w : Spv B) =
      comap ψ w.val := (rfl)

section RingEquiv

variable {Aplus : Subring A} {Bplus : Subring B}
  (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
  (hplus : Aplus.map (e : A →+* B) = Bplus)

/-- **Homeomorphism of adic spectra induced by a topological ring equivalence.** Given a ring
isomorphism `e : A ≃+* B` continuous in both directions with `A⁺.map e = B⁺`, pulling valuations
back along `e.symm` identifies `Spa(A, A⁺)` homeomorphically with `Spa(B, B⁺)`. -/
noncomputable def spaHomeomorphOfRingEquiv : spa Aplus ≃ₜ spa Bplus :=
  spaComapHomeomorph (e.symm : B →+* A) he' (fun _ hb ↦ Subring.mem_map_equiv.mp (hplus ▸ hb))
    (e : A →+* B) he e.apply_symm_apply e.symm_apply_apply fun a ha ↦ hplus ▸ ⟨a, ha, rfl⟩

/-- `spaHomeomorphOfRingEquiv` coerces to `spaComap` along `e.symm`. -/
theorem coe_spaHomeomorphOfRingEquiv :
    (spaHomeomorphOfRingEquiv e he he' hplus : spa Aplus → spa Bplus) =
      spaComap (e.symm : B →+* A) he' Bplus Aplus
        fun _ hb ↦ Subring.mem_map_equiv.mp (hplus ▸ hb) := (rfl)

/-- The inverse of `spaHomeomorphOfRingEquiv` coerces to `spaComap` along `e`. -/
theorem coe_spaHomeomorphOfRingEquiv_symm :
    ((spaHomeomorphOfRingEquiv e he he' hplus).symm : spa Bplus → spa Aplus) =
      spaComap (e : A →+* B) he Aplus Bplus fun a ha ↦ hplus ▸ ⟨a, ha, rfl⟩ := (rfl)

/-- `spaHomeomorphOfRingEquiv` pulls valuations back along `e.symm`. -/
@[simp] theorem spaHomeomorphOfRingEquiv_val (v : spa Aplus) :
    (spaHomeomorphOfRingEquiv e he he' hplus v : Spv B) = comap (e.symm : B →+* A) v.val := (rfl)

/-- The inverse of `spaHomeomorphOfRingEquiv` pulls valuations back along `e`. -/
@[simp] theorem spaHomeomorphOfRingEquiv_symm_val (w : spa Bplus) :
    ((spaHomeomorphOfRingEquiv e he he' hplus).symm w : Spv A) = comap (e : A →+* B) w.val := (rfl)

end RingEquiv

open scoped Classical in
/-- Preimage of a rational subset under `comap φ`, after intersecting with `spa Bplus`:
`(comap φ) ⁻¹' R(T/s) ∩ spa Bplus = R(φ(T)/φ(s))`. -/
theorem comap_preimage_rationalSubset_inter_spa (φ : A →+* B) (hφ : Continuous φ)
    {Aplus : Subring A} {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (T : Finset A) (s : A) :
    comap φ ⁻¹' rationalSubset Aplus T s ∩ spa Bplus =
      rationalSubset Bplus (T.image φ) (φ s) := by
  ext v
  simp only [Set.mem_inter_iff, Set.mem_preimage, mem_rationalSubset_iff, mem_spa_iff,
    comap_vle, map_one, map_zero]
  constructor
  · rintro ⟨⟨⟨-, -⟩, hT, hs⟩, hv_cont, hv_plus⟩
    exact ⟨⟨hv_cont, hv_plus⟩, fun t ht ↦ by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
      exact hT a ha, hs⟩
  · rintro ⟨⟨hv_cont, hv_plus⟩, hT, hs⟩
    have hv_spa : v ∈ spa Bplus := (mem_spa_iff Bplus v).mpr ⟨hv_cont, hv_plus⟩
    have hcomap_spa := (mem_spa_iff Aplus (comap φ v)).mp (comap_mem_spa hφ hplus hv_spa)
    have hcomap_spa' : (comap φ v).IsContinuous ∧
        ∀ a ∈ Aplus, v.toValuativeRel.vle (φ a) 1 := by
      simpa only [comap_vle, map_one] using hcomap_spa
    exact ⟨⟨hcomap_spa', fun a ha ↦ hT (φ a) (Finset.mem_image_of_mem φ ha), hs⟩,
      hv_cont, hv_plus⟩

/-- A point of `Spa (B, B⁺)` pulls back into `R(T/s)` if `φ` inverts `s` and makes the
fractions `t/s` sub-unit. No Huber hypothesis is needed, and `T` is arbitrary. -/
theorem comap_mem_rationalSubset {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A}
    {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (T : Finset A) (s : A) {c : B}
    (hc : φ s * c = 1) (hT : ∀ t ∈ T, φ t * c ∈ Bplus) {v : Spv B} (hv : v ∈ spa Bplus) :
    comap φ v ∈ rationalSubset Aplus T s := by
  rw [mem_rationalSubset_iff]
  refine ⟨comap_mem_spa hφ hplus hv, fun t ht ↦ ?_, ?_⟩
  · have hsub : v.toValuativeRel.vle (φ t * c) 1 := ((mem_spa_iff Bplus v).mp hv).2 _ (hT t ht)
    have hclear : φ t * c * φ s = φ t := by
      rw [mul_assoc, mul_comm c, hc, mul_one]
    rw [comap_vle]
    simpa only [hclear, one_mul] using v.toValuativeRel.mul_vle_mul_left hsub (φ s)
  · have hunit : IsUnit (φ s) := ⟨⟨φ s, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩
    rw [comap_vle, map_zero]
    exact @TauCeti.ValuativeRel.not_vle_zero_of_isUnit B _ v.toValuativeRel _ hunit

/-- **The fractions are sub-unit.** At a point of `Spv B` whose pullback lies in `R(T/s)`, the
fraction `φ t / φ s` has value at most `1`.

For Huber pairs, the unit hypothesis on `φ s` is supplied by
`TauCeti.ValuationSpectrum.isUnit_of_forall_comap_mem_rationalSubset`. -/
theorem vle_one_of_comap_mem_rationalSubset {B : Type*} [CommRing B] {φ : A →+* B}
    {Aplus : Subring A} {T : Finset A} {s : A} (hs : IsUnit (φ s)) {w : Spv B}
    (hmem : comap φ w ∈ rationalSubset Aplus T s) {t : A} (ht : t ∈ T) :
    w.toValuativeRel.vle (φ t * ↑hs.unit⁻¹) 1 := by
  have hvle : w.toValuativeRel.vle (φ t) (φ s) := by
    have h := ((mem_rationalSubset_iff Aplus T s _).mp hmem).2.1 t ht
    rwa [comap_vle] at h
  have h := w.toValuativeRel.mul_vle_mul_left hvle (↑hs.unit⁻¹ : B)
  rwa [hs.mul_val_inv] at h

open scoped Classical in
omit [TopologicalSpace A] in
/-- If `φ` inverts `s` and makes every fraction `φ(t) / φ(s)` sub-unit, the rational subset
presented by the images of `T` and `s` is the whole target adic spectrum. -/
theorem rationalSubset_image_eq_spa (φ : A →+* B) (Bplus : Subring B) (T : Finset A) (s : A)
    {c : B} (hc : φ s * c = 1) (hT : ∀ t ∈ T, φ t * c ∈ Bplus) :
    rationalSubset Bplus (T.image φ) (φ s) = spa Bplus := by
  refine Set.Subset.antisymm (rationalSubset_subset_spa _ _ _) fun v hv ↦ ?_
  have hmem := comap_mem_rationalSubset (φ := RingHom.id B) continuous_id
    (Aplus := Bplus) (Bplus := Bplus) (fun _ ha ↦ ha) (T.image φ) (φ s) (by simpa using hc)
    (fun _ ht ↦ by
      obtain ⟨t, htT, rfl⟩ := Finset.mem_image.mp ht
      simpa using hT t htT) hv
  rwa [congr_fun comap_id v] at hmem

open scoped Classical in
/-- The preimage of `R(T/s)` under `spaComap φ` is `R(φ(T)/φ(s))`. -/
theorem spaComap_preimage_rationalSubset (φ : A →+* B) (hφ : Continuous φ)
    (Aplus : Subring A) (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (T : Finset A) (s : A) :
    spaComap φ hφ Aplus Bplus hplus ⁻¹' (Subtype.val ⁻¹' rationalSubset Aplus T s) =
      Subtype.val ⁻¹' rationalSubset Bplus (T.image φ) (φ s) := by
  ext ⟨v, hv⟩
  simp only [Set.mem_preimage, spaComap_val]
  simpa only [Set.mem_inter_iff, Set.mem_preimage, hv, and_true] using
    Set.ext_iff.mp (comap_preimage_rationalSubset_inter_spa φ hφ hplus T s) v

section TopCat

universe v

variable {A B : Type v} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
  {Aplus : Subring A} {Bplus : Subring B} (φ : A →+* B) (hφ : Continuous φ)
  (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)

/-- The map of adic spectra `Spa(B, B⁺) → Spa(A, A⁺)` induced by `φ`, as a morphism of `TopCat`. -/
noncomputable abbrev spaComapTopHom : TopCat.of ↥(spa Bplus) ⟶ TopCat.of ↥(spa Aplus) :=
  TopCat.ofHom ⟨spaComap φ hφ Aplus Bplus hplus, continuous_spaComap φ hφ Aplus Bplus hplus⟩

open scoped Classical in
/-- **The preimage of a basic open is a basic open**: the preimage of `R(T/s)` under the induced
map of adic spectra is `R(φ(T)/φ(s))`. This is `spaComap_preimage_rationalSubset` for `Opens`. -/
@[simp]
theorem map_spaComapTopHom_obj_spaBasicOpen (T : Finset A) (s : A) :
    (TopologicalSpace.Opens.map (spaComapTopHom φ hφ hplus)).obj (spaBasicOpen Aplus T s) =
      spaBasicOpen Bplus (T.image φ) (φ s) :=
  TopologicalSpace.Opens.ext <| Set.ext fun w ↦
    (TopologicalSpace.Opens.mem_map.trans mem_spaBasicOpen).trans <|
      (Set.ext_iff.mp (spaComap_preimage_rationalSubset φ hφ Aplus Bplus hplus T s) w).trans
        mem_spaBasicOpen.symm

/-- **A basic open lies in the preimage of a basic open** under the induced map of adic spectra
exactly when the rational subset it presents lies in the preimage of the other rational subset
under `comap φ`. -/
theorem spaBasicOpen_le_map_spaBasicOpen_iff {T : Finset A} {s : A} {T' : Finset B} {s' : B} :
    spaBasicOpen Bplus T' s' ≤
        (TopologicalSpace.Opens.map (spaComapTopHom φ hφ hplus)).obj (spaBasicOpen Aplus T s) ↔
      rationalSubset Bplus T' s' ⊆ comap φ ⁻¹' rationalSubset Aplus T s :=
  ⟨fun h v hv ↦ mem_spaBasicOpen.mp <| TopologicalSpace.Opens.mem_map.mp <|
      h ((mem_spaBasicOpen (v := ⟨v, rationalSubset_subset_spa Bplus T' s' hv⟩)).mpr hv),
    fun h _ hv ↦ TopologicalSpace.Opens.mem_map.mpr <|
      mem_spaBasicOpen.mpr (h (mem_spaBasicOpen.mp hv))⟩

open CategoryTheory in
/-- `spaComapTopHom` of the identity homomorphism is the identity morphism. -/
@[simp]
theorem spaComapTopHom_id :
    spaComapTopHom (RingHom.id A) continuous_id (Aplus := Aplus) (fun _ ha ↦ ha) =
      𝟙 (TopCat.of ↥(spa Aplus)) :=
  TopCat.ext fun x ↦ congrFun (spaComap_id Aplus) x

open CategoryTheory in
/-- `spaComapTopHom` is contravariantly functorial: the map induced by `ψ ∘ φ` is the map induced
by `ψ` followed by the map induced by `φ`. -/
@[simp]
theorem spaComapTopHom_comp {C : Type v} [CommRing C] [TopologicalSpace C] {Cplus : Subring C}
    {ψ : B →+* C} (hψ : Continuous ψ) (hplus' : ∀ b ∈ Bplus, ψ b ∈ Cplus) :
    spaComapTopHom (ψ.comp φ) (hψ.comp hφ) (fun a ha ↦ hplus' (φ a) (hplus a ha)) =
      spaComapTopHom ψ hψ hplus' ≫ spaComapTopHom φ hφ hplus :=
  TopCat.ext fun x ↦ congrFun (spaComap_comp hφ hψ Aplus Bplus Cplus hplus hplus') x

/-- The preimage of an open under the map induced by the identity is the open itself. -/
theorem map_spaComapTopHom_id_obj (U : TopologicalSpace.Opens ↥(spa Aplus)) :
    (TopologicalSpace.Opens.map
      (spaComapTopHom (RingHom.id A) continuous_id (Aplus := Aplus) fun _ ha ↦ ha)).obj U = U := by
  rw [spaComapTopHom_id, TopologicalSpace.Opens.map_id_obj]

/-- The preimage of an open under the map induced by `ψ ∘ φ` is its preimage under the map
induced by `φ` followed by the preimage under the map induced by `ψ`. -/
theorem map_spaComapTopHom_comp_obj {C : Type v} [CommRing C] [TopologicalSpace C]
    {Cplus : Subring C} {ψ : B →+* C} (hψ : Continuous ψ) (hplus' : ∀ b ∈ Bplus, ψ b ∈ Cplus)
    (U : TopologicalSpace.Opens ↥(spa Aplus)) :
    (TopologicalSpace.Opens.map
        (spaComapTopHom (ψ.comp φ) (hψ.comp hφ) fun a ha ↦ hplus' (φ a) (hplus a ha))).obj U =
      (TopologicalSpace.Opens.map (spaComapTopHom ψ hψ hplus')).obj
        ((TopologicalSpace.Opens.map (spaComapTopHom φ hφ hplus)).obj U) := by
  rw [spaComapTopHom_comp, TopologicalSpace.Opens.map_comp_obj]

/-- For `ψ` a left inverse of `φ`, a point `w` of `Spa(A, A⁺)` whose pullback along `ψ` lies in the
preimage of `W` under the map of adic spectra induced by `φ` lies in `W`. -/
theorem mem_of_spaComap_mem_map (ψ : B →+* A) (hψ : Continuous ψ) (hψφ : ∀ a, ψ (φ a) = a)
    (hplus' : ∀ b ∈ Bplus, ψ b ∈ Aplus) (W : TopologicalSpace.Opens ↥(spa Aplus))
    (w : ↥(spa Aplus))
    (hw : spaComap ψ hψ Bplus Aplus hplus' w ∈
      (TopologicalSpace.Opens.map (spaComapTopHom φ hφ hplus)).obj W) :
    w ∈ W := by
  rw [← spaComap_spaComap φ hφ hplus ψ hψ hψφ hplus' w]
  exact TopologicalSpace.Opens.mem_map.mp hw

end TopCat

/-- If pullback along `φ` embeds valuation spectra, then its restriction to compatible sub-unit
loci is also an embedding. -/
theorem isEmbedding_spaComap (φ : A →+* B) (hφ : Continuous φ) (Aplus : Subring A)
    (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hemb : Topology.IsEmbedding (comap φ)) :
    Topology.IsEmbedding (spaComap φ hφ Aplus Bplus hplus) := by
  have hcomp : Subtype.val ∘ spaComap φ hφ Aplus Bplus hplus =
      comap φ ∘ Subtype.val := by
    funext v
    exact spaComap_val φ hφ Aplus Bplus hplus v
  refine Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal |>.mp ?_
  rw [hcomp]
  exact hemb.comp Topology.IsEmbedding.subtypeVal

section Quotient

/-- Pullback along a quotient map preserves and reflects whether the support of a valuation is
open. -/
@[simp]
theorem isOpen_supp_comap_quotientMk_iff (J : Ideal A) (v : Spv (A ⧸ J)) :
    IsOpen ((comap (Ideal.Quotient.mk J) v).supp : Set A) ↔
      IsOpen (v.supp : Set (A ⧸ J)) := by
  have hsupp : Ideal.Quotient.mk J ⁻¹' (v.supp : Set (A ⧸ J)) =
      ((comap (Ideal.Quotient.mk J) v).supp : Set A) := by
    ext a
    simp only [Set.mem_preimage, SetLike.mem_coe, mem_supp_iff, comap_vle, map_zero]
  rw [← hsupp]
  exact isOpen_coinduced.symm

/-- The map on sub-unit valuation loci for a quotient homomorphism and the image plus ring is a
topological embedding. -/
theorem isEmbedding_spaComap_quotientMk (J : Ideal A) (Aplus : Subring A) :
    Topology.IsEmbedding (spaComap (Ideal.Quotient.mk J) continuous_quotient_mk' Aplus
      (Aplus.map (Ideal.Quotient.mk J))
      (fun a ha ↦ (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩)) :=
  isEmbedding_spaComap _ _ _ _ _ (isEmbedding_comap_quotientMk J)

/-- The range of the quotient map with the image plus ring is the points whose support contains
`J`. -/
theorem range_spaComap_quotientMk (J : Ideal A) (Aplus : Subring A) :
    Set.range (spaComap (Ideal.Quotient.mk J) continuous_quotient_mk' Aplus
      (Aplus.map (Ideal.Quotient.mk J))
      (fun a ha ↦ (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩)) =
      Subtype.val ⁻¹' {v : Spv A | J ≤ v.supp} := by
  ext ⟨v, hv⟩
  simp only [Set.mem_range, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨w, hw⟩, heq⟩
    have hval : comap (Ideal.Quotient.mk J) w = v := Subtype.ext_iff.mp heq
    rw [← hval]
    exact self_le_supp_comap J w
  · intro hJ
    have hlift_spa : quotientLift J hJ ∈ spa (Aplus.map (Ideal.Quotient.mk J)) :=
      (mem_spa_map_iff continuous_quotient_mk' Aplus
        (((mem_spa_iff Aplus v).mp hv).1.quotientLift J hJ)).mpr (by rwa [comap_quotientLift])
    refine ⟨⟨quotientLift J hJ, hlift_spa⟩, ?_⟩
    apply Subtype.ext
    exact (spaComap_val (Ideal.Quotient.mk J) continuous_quotient_mk' Aplus
      (Aplus.map (Ideal.Quotient.mk J)) _ ⟨quotientLift J hJ, hlift_spa⟩).trans
        (comap_quotientLift J hJ)

/-- The locus in a sub-unit valuation space where the support contains `J` is closed. -/
theorem isClosed_support_locus (Aplus : Subring A) (J : Ideal A) :
    IsClosed (Subtype.val ⁻¹' {v : Spv A | J ≤ v.supp} : Set (spa Aplus)) := by
  have hlocus : {v : Spv A | J ≤ v.supp} =
      suppFun ⁻¹' PrimeSpectrum.zeroLocus (J : Set A) := by
    ext v
    simp [PrimeSpectrum.mem_zeroLocus, suppFun_asIdeal]
  rw [hlocus, ← Set.preimage_comp]
  exact (PrimeSpectrum.isClosed_zeroLocus (J : Set A)).preimage
    (continuous_suppFun.comp continuous_subtypeVal)

/-- The quotient homomorphism with the image plus ring induces a closed embedding of sub-unit
valuation loci. -/
theorem isClosedEmbedding_spaComap_quotientMk (J : Ideal A) (Aplus : Subring A) :
    Topology.IsClosedEmbedding (spaComap (Ideal.Quotient.mk J) continuous_quotient_mk' Aplus
      (Aplus.map (Ideal.Quotient.mk J))
      (fun a ha ↦ (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩)) :=
  ⟨isEmbedding_spaComap_quotientMk J Aplus,
    range_spaComap_quotientMk J Aplus ▸ isClosed_support_locus Aplus J⟩

end Quotient

end TauCeti.ValuationSpectrum
