/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject
public import TauCeti.Algebra.Homology.HomotopyCategory.ShortExact
public import TauCeti.CategoryTheory.Subobject.Cokernel

/-!
# The first differential of the spectral sequence of a filtered complex

Let `F : EInt ⥤ CochainComplex C ℤ` be a functor, for instance the functor of a filtration
(`CochainComplex.filtrationFunctor`). Its spectral sequence `CochainComplex.spectralSequence F`
uses Mathlib's recipe `coreE₂Cohomological`, in which the first page is numbered `2`: the object at
`(p, q)` is the cohomology `H^{p+q}` of the graded piece `F_{q+1}/F_q` (when `F_q ⟶ F_{q+1}` is a
monomorphism, `CochainComplex.spectralSequenceFirstPageXIsoCokernel`), so `q` is the filtration
index and `p + q` the total degree, and the differential goes from `(p, q)` to `(p + 2, q - 1)`.

We show that this differential is the connecting map
`H^{p+q}(F_{q+1}/F_q) ⟶ H^{p+q+1}(F_q/F_{q-1})` of the short exact sequence
`F_q/F_{q-1} ⟶ F_{q+1}/F_{q-1} ⟶ F_{q+1}/F_q`
(`CochainComplex.spectralSequence_first_page_d_eq`). In McCleary's conventions, for the decreasing
filtration `F^s = F_{-s}`, the object at `(p, q)` is `E_1^{s,t} = H^{s+t}(F^s/F^{s+1})` with
`s = -q - 1` and `t = p + 2q + 1`, and this differential is `d_1 : E_1^{s,t} ⟶ E_1^{s+1,t}`.

The connecting maps of the spectral object of a functor with monomorphic transition maps are the
connecting maps of the short exact sequences of graded pieces
(`CochainComplex.spectralObject_δ_comp_spectralObjectHIsoCokernel_hom`), by
`CochainComplex.mappingCone.shiftMap_mappingConeCompTriangle_mor₃`.

## Main results

* `CochainComplex.spectralObject_δ_comp_spectralObjectHIsoCokernel_hom`,
  `CochainComplex.spectralObjectHIsoCokernel_inv_comp_spectralObject_δ`: the connecting maps of the
  spectral object, for monomorphic transition maps.
* `CochainComplex.spectralSequence_first_page_d_eq`: the first differential of the spectral
  sequence of a filtered complex, with `CochainComplex.spectralSequence_first_page_d_eq_of_eq` its
  form with the indices given by equations.
* `CochainComplex.spectralSequence_first_page_d_eq_cokernelMap`: the same, with the filtration
  indices given by equations and the target identified through an index equal to the middle one.
* `CochainComplex.δ_comp_homologyMap_cokernelFiltrationFunctorMapIso_trans_hom`: for a filtration,
  the connecting maps of the graded pieces of its functor are those of the quotients of the
  subobjects in the filtration.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, §2.2.
-/

public section

open CategoryTheory Limits ComposableArrows

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

section SpectralObject

variable {ι : Type*} [Category* ι] (F : ι ⥤ CochainComplex C ℤ)

/-- The connecting maps of the spectral object of `F`, for monomorphisms `F.map f` and `F.map g`,
are the connecting maps of the short exact sequences of cokernels
`cokernel (F.map f) ⟶ cokernel (F.map f ≫ F.map g) ⟶ cokernel (F.map g)`. -/
lemma spectralObject_δ_comp_spectralObjectHIsoCokernel_hom {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
    [Mono (F.map f)] [Mono (F.map g)] (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (spectralObject F).δ f g n₀ n₁ h ≫ (spectralObjectHIsoCokernel F f n₁).hom =
      (spectralObjectHIsoCokernel F g n₀).hom ≫
        (TauCeti.cokernelCompSequence_shortExact (F.map f) (F.map g)).δ
          n₀ n₁ (by simp [← h]) := by
  rw [spectralObject_δ, spectralObjectHIsoCokernel_hom, spectralObjectHIsoCokernel_hom]
  let A := (spectralObjectHIso F g n₀).hom
  let S := (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
    (mappingConeCompTriangle (F.map f) (F.map g)).mor₃ n₀ n₁ (by lia)
  exact (Category.assoc _ _ _).trans <|
    (congrArg (fun t => A ≫ t) ((Category.assoc _ _ _).trans
      (congrArg (fun t => S ≫ t) (Iso.inv_hom_id_assoc _ _)))).trans <|
    (congrArg (fun t => A ≫ t)
      (mappingCone.shiftMap_mappingConeCompTriangle_mor₃ (F.map f) (F.map g) n₀ n₁
        (by lia))).trans (Category.assoc _ _ _).symm

/-- The form of `spectralObject_δ_comp_spectralObjectHIsoCokernel_hom` with the identification of
`H^{n₀}(g)` with the cohomology of `cokernel (F.map g)` moved to the source: on the cohomology of
the cokernels, the connecting maps of the spectral object of `F` are the connecting maps of the
short exact sequences of cokernels. -/
@[reassoc]
lemma spectralObjectHIsoCokernel_inv_comp_spectralObject_δ {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
    [Mono (F.map f)] [Mono (F.map g)] (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (spectralObjectHIsoCokernel F g n₀).inv ≫ (spectralObject F).δ f g n₀ n₁ h =
      (TauCeti.cokernelCompSequence_shortExact (F.map f) (F.map g)).δ
          n₀ n₁ (by simp [← h]) ≫ (spectralObjectHIsoCokernel F f n₁).inv :=
  (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2
    (spectralObject_δ_comp_spectralObjectHIsoCokernel_hom F f g n₀ n₁ h)).trans
      (Category.assoc _ _ _))

end SpectralObject

section SpectralSequence

variable (F : EInt ⥤ CochainComplex C ℤ)

/-- **The first differential of the spectral sequence of a filtered complex.** When
`F_{q-1} ⟶ F_q` and `F_q ⟶ F_{q+1}` are monomorphisms, the differential of the first page (page
`2` in Mathlib's numbering) from `(p, q)` to `(p + 2, q - 1)` is, under the identifications of the
first page with the cohomology of the graded pieces, the connecting map
`H^{p+q}(F_{q+1}/F_q) ⟶ H^{p+q+1}(F_q/F_{q-1})` of the short exact sequence
`F_q/F_{q-1} ⟶ F_{q+1}/F_{q-1} ⟶ F_{q+1}/F_q`. -/
theorem spectralSequence_first_page_d_eq (p q : ℤ)
    [Mono (F.map (homOfLE (coe_le_coe_of_eq_add_one (show q - 1 = q - 1 from rfl)
      (show q = q - 1 + 1 by lia))))]
    [Mono (F.map (homOfLE (coe_le_coe_of_eq_add_one (show q = q from rfl) rfl)))] :
    ((spectralSequence F).page 2).d (p, q) (p + 2, q - 1) =
      (spectralSequenceFirstPageXIsoCokernel F (p, q) q (q + 1) rfl rfl (p + q) rfl).hom ≫
        (TauCeti.cokernelCompSequence_shortExact
          (F.map (homOfLE (coe_le_coe_of_eq_add_one (show q - 1 = q - 1 from rfl)
            (show q = q - 1 + 1 by lia))))
          (F.map (homOfLE (coe_le_coe_of_eq_add_one (show q = q from rfl) rfl)))).δ
            (p + q) (p + q + 1) rfl ≫
        (spectralSequenceFirstPageXIsoCokernel F (p + 2, q - 1) (q - 1) q rfl (by lia)
          (p + q + 1) (by lia)).inv := by
  have key := spectralObject_δ_comp_spectralObjectHIsoCokernel_hom F
    (homOfLE (coe_le_coe_of_eq_add_one (show q - 1 = q - 1 from rfl)
      (show q = q - 1 + 1 by lia)))
    (homOfLE (coe_le_coe_of_eq_add_one (show q = q from rfl) rfl)) (p + q) (p + q + 1) rfl
  replace key := (Iso.eq_comp_inv _).2 key
  rw [Abelian.SpectralObject.spectralSequence_first_page_d_eq (spectralObject F)
    Abelian.SpectralObject.coreE₂Cohomological (p, q) (p + 2, q - 1)
    (by simp [ComplexShape.up']; lia) ((q - 1 : ℤ) : EInt) q ((q + 1 : ℤ) : EInt) rfl rfl rfl
    (p + q) (p + q + 1) rfl, key]
  rw [spectralSequenceFirstPageXIsoCokernel_eq, spectralSequenceFirstPageXIsoCokernel_eq,
    Iso.trans_hom, Iso.trans_inv]
  simp only [Category.assoc]

/-- The form of `CochainComplex.spectralSequence_first_page_d_eq` in which the bidegrees, the
filtration indices `i ≤ j ≤ k` and the cohomological degrees are given together with equations, for
flexibility. -/
theorem spectralSequence_first_page_d_eq_of_eq (pq pq' : ℤ × ℤ)
    (hpq : pq' = (pq.1 + 2, pq.2 - 1)) (i j k : ℤ) (hi : i = pq'.2) (hj : j = pq.2)
    (hk : k = pq.2 + 1) (n n' : ℤ) (hn : n = pq.1 + pq.2) (hn' : n + 1 = n')
    [hij : Mono (F.map (TauCeti.eIntHomOfLE (show i ≤ j by lia)))]
    [hjk : Mono (F.map (TauCeti.eIntHomOfLE (show j ≤ k by lia)))] :
    ((spectralSequence F).page 2).d pq pq' =
      (spectralSequenceFirstPageXIsoCokernel F pq j k hj hk n hn).hom ≫
        (TauCeti.cokernelCompSequence_shortExact
          (F.map (TauCeti.eIntHomOfLE (show i ≤ j by lia)))
          (F.map (TauCeti.eIntHomOfLE (show j ≤ k by lia)))).δ n n' (by simp [← hn']) ≫
        (spectralSequenceFirstPageXIsoCokernel F pq' i j hi (by lia) n' (by lia)).inv := by
  -- The instances mention the equations through the proofs of `i ≤ j` and `j ≤ k`.
  revert hij hjk
  subst hpq hj hk hn hn' hi
  intro _ _
  exact spectralSequence_first_page_d_eq F pq.1 pq.2

/-- **The first differential of the spectral sequence of a filtered complex**, with the
filtration indices given by equations. When `F_{q₀} ⟶ F_{q₁}` and `F_{q₁} ⟶ F_{q₂}` are
monomorphisms, with `q₀ + 1 = q₁` and `q₁ + 1 = q₂`, the differential of the first page from
`(p, q₁)` to `(p + 2, q₀)` is the connecting map of `F_{q₁}/F_{q₀} ⟶ F_{q₂}/F_{q₀} ⟶ F_{q₂}/F_{q₁}`,
followed by the identification of `F_{q₁}/F_{q₀}` with `F_{q₁'}/F_{q₀}` for an index `q₁'` equal
to `q₁`. This is `CochainComplex.spectralSequence_first_page_d_eq`, in a form that applies when
the indices are not syntactically of the form `q - 1`, `q`, `q + 1`. -/
theorem spectralSequence_first_page_d_eq_cokernelMap (p p' q₀ q₁ q₁' q₂ n₀ n₁ : ℤ)
    (hp : p + 2 = p') (h₀ : q₀ + 1 = q₁) (h₁ : q₁ + 1 = q₂) (h' : q₁ = q₁')
    (hn₀ : n₀ = p + q₁) (hn₁ : n₀ + 1 = n₁)
    [Mono (F.map (homOfLE (coe_le_coe_of_eq_add_one (rfl : q₁ = q₁) h₁.symm)))]
    [Mono (F.map (homOfLE (coe_le_coe_of_eq_add_one (rfl : q₀ = q₀) (h₀ ▸ h').symm)))] :
    (spectralSequenceFirstPageXIsoCokernel F (p, q₁) q₁ q₂ rfl h₁.symm n₀ hn₀).inv ≫
      ((spectralSequence F).page 2).d (p, q₁) (p', q₀) ≫
      (spectralSequenceFirstPageXIsoCokernel F (p', q₀) q₀ q₁' rfl (h₀ ▸ h').symm n₁
        (by dsimp; lia)).hom =
    (TauCeti.cokernelCompSequence_shortExact
        (F.map (homOfLE (coe_le_coe_of_eq_add_one (rfl : q₀ = q₀) h₀.symm)))
        (F.map (homOfLE (coe_le_coe_of_eq_add_one (rfl : q₁ = q₁) h₁.symm)))).δ
        n₀ n₁ (by simp [← hn₁]) ≫
      HomologicalComplex.homologyMap (cokernel.map _ _ (𝟙 _)
        (F.map (homOfLE (by simp [h'] : (q₁ : EInt) ≤ q₁')))
        (by rw [Category.id_comp, ← F.map_comp]; exact congrArg F.map (Subsingleton.elim _ _)))
        n₁ := by
  subst hp h' h₁ hn₀ hn₁
  obtain rfl : q₀ = q₁ - 1 := by lia
  rw [spectralSequence_first_page_d_eq]
  simp only [homOfLE_leOfHom, Category.assoc, Iso.inv_hom_id_assoc, homOfLE_refl,
    CategoryTheory.Functor.map_id, cokernel.map_id, HomologicalComplex.homologyMap_id,
    Iso.inv_hom_id, Category.comp_id]

end SpectralSequence

section Filtration

variable {K : CochainComplex C ℤ} (F : ℤ → Subobject K) (hF : Monotone F)

/-- For a filtration `F` and subobjects `A ≤ B ≤ D` equal to `F i`, `F j` and `F k`, the connecting
map of the graded pieces `F_j/F_i ⟶ F_k/F_i ⟶ F_k/F_j` of the functor of the filtration is the
connecting map of the sequence `B/A ⟶ D/A ⟶ D/B`, under the identifications
`CochainComplex.cokernelFiltrationFunctorMapIso` and `CategoryTheory.Subobject.cokernelOfLEIsoOfEq`
of the graded pieces. -/
lemma δ_comp_homologyMap_cokernelFiltrationFunctorMapIso_trans_hom {i j k : ℤ} (hij : i ≤ j)
    (hjk : j ≤ k) {A B D : Subobject K} (hA : F i = A) (hB : F j = B) (hD : F k = D)
    (hAB : A ≤ B) (hBD : B ≤ D) (n₀ n₁ : ℤ) (h : (ComplexShape.up ℤ).Rel n₀ n₁) :
    (TauCeti.cokernelCompSequence_shortExact
        ((filtrationFunctor F hF).map (TauCeti.eIntHomOfLE hij))
        ((filtrationFunctor F hF).map (TauCeti.eIntHomOfLE hjk))).δ n₀ n₁ h ≫
      HomologicalComplex.homologyMap
        (cokernelFiltrationFunctorMapIso F hF (TauCeti.eIntHomOfLE hij) ≪≫
          Subobject.cokernelOfLEIsoOfEq ((filtrationEInt_coe F i).trans hA)
            ((filtrationEInt_coe F j).trans hB) _ hAB).hom n₁ =
    HomologicalComplex.homologyMap
        (cokernelFiltrationFunctorMapIso F hF (TauCeti.eIntHomOfLE hjk) ≪≫
          Subobject.cokernelOfLEIsoOfEq ((filtrationEInt_coe F j).trans hB)
            ((filtrationEInt_coe F k).trans hD) _ hBD).hom n₀ ≫
      (TauCeti.cokernelCompSequence_shortExact (Subobject.ofLE A B hAB)
        (Subobject.ofLE B D hBD)).δ n₀ n₁ h := by
  -- The comparison maps from the pieces of the functor of the filtration to `A`, `B` and `D`.
  let u : ∀ (a : ℤ) {S : Subobject K}, F a = S → ((filtrationFunctor F hF).obj a ⟶ S) :=
    fun a _ hS ↦ (filtrationFunctorObjIso F hF a).hom ≫
      Subobject.ofLE _ _ ((filtrationEInt_coe F a).trans hS).le
  have w : ∀ {a b : ℤ} (hab : a ≤ b) {S T : Subobject K} (hS : F a = S) (hT : F b = T)
      (hST : S ≤ T), u a hS ≫ Subobject.ofLE S T hST =
        (filtrationFunctor F hF).map (TauCeti.eIntHomOfLE hab) ≫ u b hT :=
    fun hab _ _ hS hT hST ↦ by
    simp [u, reassoc_of% filtrationFunctor_map_comp_objIso_hom, Subobject.ofLE_comp_ofLE]
  -- Under these comparisons, the induced maps of cokernels are the identifications of the
  -- graded pieces.
  have e : ∀ {a b : ℤ} (hab : a ≤ b) {S T : Subobject K} (hS : F a = S) (hT : F b = T)
      (hST : S ≤ T), cokernel.map _ _ (u a hS) (u b hT) (w hab hS hT hST) =
        (cokernelFiltrationFunctorMapIso F hF (TauCeti.eIntHomOfLE hab) ≪≫
          Subobject.cokernelOfLEIsoOfEq ((filtrationEInt_coe F a).trans hS)
            ((filtrationEInt_coe F b).trans hT) _ hST).hom := fun hab _ _ hS hT hST ↦ by
    apply coequalizer.hom_ext
    simp [u]
  have key := HomologicalComplex.HomologySequence.δ_naturality
    (TauCeti.cokernelCompSequenceMap (u i hA) (u j hB) (u k hD) (w hij hA hB hAB) (w hjk hB hD hBD))
    (TauCeti.cokernelCompSequence_shortExact _ _)
    (TauCeti.cokernelCompSequence_shortExact _ _) n₀ n₁ h
  rwa [TauCeti.cokernelCompSequenceMap_τ₁, TauCeti.cokernelCompSequenceMap_τ₃, e, e] at key

end Filtration

end CochainComplex
