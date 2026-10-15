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

* `CochainComplex.spectralObject_δ_comp_spectralObjectHIsoCokernel_hom`: the connecting maps of the
  spectral object, for monomorphic transition maps.
* `CochainComplex.spectralSequence_first_page_d_eq`: the first differential of the spectral
  sequence of a filtered complex.

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

end SpectralSequence

end CochainComplex
