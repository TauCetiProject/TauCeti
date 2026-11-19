/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject
public import TauCeti.Algebra.Homology.HomotopyCategory.ShortExact

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
  sequence of a filtered complex.
* `CochainComplex.spectralSequence_first_page_d_eq_cokernelMap`: the same, with the filtration
  indices given by equations.

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
        (TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact (F.map f) (F.map g)).δ
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
      (TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact (F.map f) (F.map g)).δ
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
        (TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact
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
    Iso.trans_hom, Iso.trans_inv, Category.assoc]
  congr 1
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

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
    (TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact
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
    CategoryTheory.Functor.map_id, cokernel.map_id, HomologicalComplex.homologyMap_id]
  -- What remains is `(δ ≫ e.inv) ≫ e.hom = δ ≫ 𝟙 _`, up to the types of the homology objects.
  exact (Category.assoc _ _ _).trans (congrArg _ (Iso.inv_hom_id _))

end SpectralSequence

end CochainComplex
