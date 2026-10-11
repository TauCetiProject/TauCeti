/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp

/-!
# The first differential of the spectral sequence of a filtered complex

For monomorphisms `a : X ⟶ Y` and `b : Y ⟶ Z` of cochain complexes, the sequence
`cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b` is short exact
(`CochainComplex.cokernelCompShortComplex_shortExact`). Under the identifications of the
cohomology of mapping cones of monomorphisms with the cohomology of their cokernels, the
connecting map of the distinguished triangle of mapping cones attached to `a` and `b` is the
connecting map of this short exact sequence
(`CochainComplex.homologySequenceδ_mappingConeCompTriangleh`), so the connecting maps of the
spectral object of a functor with monomorphic transition maps are those of the short exact
sequences of graded pieces (`CochainComplex.spectralObject_δ_comp_hIsoCokernel`).

For the spectral sequence of a functor `F : EInt ⥤ CochainComplex C ℤ` whose transition maps
are monomorphisms (for instance the functor of a filtration), the differential of the first page
from `(p, q)` to `(p + 2, q - 1)` is therefore the connecting map
`H^{p+q}(F_{q+1}/F_q) ⟶ H^{p+q+1}(F_q/F_{q-1})` of the short exact sequence
`F_q/F_{q-1} ⟶ F_{q+1}/F_{q-1} ⟶ F_{q+1}/F_q` (`CochainComplex.spectralSequence_page_two_d_eq`).

## Main results

* `CochainComplex.cokernelCompShortComplex_shortExact`: the short exact sequence of cokernels.
* `CochainComplex.homologySequenceδ_mappingConeCompTriangleh`: the connecting map of the triangle
  of mapping cones is the connecting map of the short exact sequence of cokernels.
* `CochainComplex.spectralObject_δ_comp_hIsoCokernel`: the same for the spectral object of a
  functor.
* `CochainComplex.spectralSequence_page_two_d_eq`: the first differential of the spectral
  sequence of a filtered complex.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, §2.2.
-/

public section

open CategoryTheory Limits ComposableArrows HomotopyCategory

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

section Cokernels

variable {X Y Z : CochainComplex C ℤ} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- The short complex `cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b` of two composable morphisms
of cochain complexes. -/
noncomputable abbrev cokernelCompShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (cokernel.map a (a ≫ b) (𝟙 _) b (by simp))
    (cokernel.map (a ≫ b) b a (𝟙 _) (by simp))
    ((cancel_epi (cokernel.π a)).1 (by simp))

/-- The sequence `cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b` is short exact when `b` is a
monomorphism. -/
lemma cokernelCompShortComplex_shortExact [Mono b] :
    (cokernelCompShortComplex a b).ShortExact := by
  have hE := kernelCokernelCompSequence_exact a b
  have h₂ : ((kernelCokernelCompSequence a b).sc hE.toIsComplex 2).Exact := hE.exact 2
  have h₃ : ((kernelCokernelCompSequence a b).sc hE.toIsComplex 3).Exact := hE.exact 3
  refine ShortComplex.ShortExact.mk' h₃ ?_ ?_
  · refine h₂.mono_g ?_
    dsimp
    rw [kernelCokernelCompSequence.δ_fac, kernel.ι_of_mono, zero_comp, neg_zero]
  · exact epi_of_epi_fac (cokernel.π_desc _ _ _)

/-- The morphism from the short exact sequence `Y ⟶ Z ⟶ cokernel b` to the short exact sequence
`cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b`. -/
noncomputable def cokernelShortComplexToCompShortComplex :
    ShortComplex.mk b (cokernel.π b) (cokernel.condition b) ⟶ cokernelCompShortComplex a b where
  τ₁ := cokernel.π a
  τ₂ := cokernel.π (a ≫ b)
  τ₃ := 𝟙 _
  comm₁₂ := by simp
  comm₂₃ := by simp

end Cokernels

section Connecting

variable {X Y Z : CochainComplex C ℤ} (a : X ⟶ Y) (b : Y ⟶ Z) [Mono a] [Mono b]

/-- The short exact sequence `X ⟶ Y ⟶ cokernel a` of a monomorphism `a`. -/
noncomputable abbrev cokernelSequence {X Y : CochainComplex C ℤ} (a : X ⟶ Y) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk a (cokernel.π a) (cokernel.condition a)

lemma cokernelSequence_shortExact {X Y : CochainComplex C ℤ} (a : X ⟶ Y) [Mono a] :
    (cokernelSequence a).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

omit [Mono a] in
/-- The connecting map in cohomology of the triangle of mapping cones
`cone a ⟶ cone (a ≫ b) ⟶ cone b ⟶ (cone a)⟦1⟧`, read through the quasi-isomorphisms
`cone a ⟶ cokernel a` and `cone b ⟶ cokernel b`, is the connecting map of the short exact
sequence `cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b`; version in the category of cochain
complexes. -/
lemma shiftMap_mappingConeCompTriangle_mor₃ (n₀ n₁ : ℤ) (h : 1 + n₀ = n₁) :
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (mappingConeCompTriangle a b).mor₃ n₀ n₁ h ≫
      HomologicalComplex.homologyMap (mappingCone.descShortComplex (cokernelSequence a)) n₁ =
    HomologicalComplex.homologyMap (mappingCone.descShortComplex (cokernelSequence b)) n₀ ≫
      (cokernelCompShortComplex_shortExact a b).δ n₀ n₁ (by simp [← h, add_comm]) := by
  -- The connecting map of the triangle of `b` alone, through `homologySequenceδ_triangleh`.
  have hb := mappingCone.homologySequenceδ_triangleh (cokernelSequence_shortExact b) n₀ n₁
    (by lia)
  rw [homologySequenceδ_quotient_mapTriangle_obj] at hb
  have hb' : (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (mappingCone.triangle b).mor₃ n₀ n₁ h =
      HomologicalComplex.homologyMap (mappingCone.descShortComplex (cokernelSequence b)) n₀ ≫
        (cokernelSequence_shortExact b).δ n₀ n₁ (by simp [← h, add_comm]) := by
    have h₁ := (Iso.cancel_iso_hom_left
      ((homologyFunctorFactors C (ComplexShape.up ℤ) n₀).app (mappingCone b)) _ _).1 hb
    exact (Iso.cancel_iso_inv_right _ _
      ((homologyFunctorFactors C (ComplexShape.up ℤ) n₁).app Y)).1
        (h₁.trans (Category.assoc _ _ _).symm)
  have hnat := HomologicalComplex.HomologySequence.δ_naturality
    (cokernelShortComplexToCompShortComplex a b) (cokernelSequence_shortExact b)
    (cokernelCompShortComplex_shortExact a b) n₀ n₁ (by simp [← h, add_comm])
  dsimp [cokernelShortComplexToCompShortComplex] at hnat
  rw [HomologicalComplex.homologyMap_id, Category.id_comp] at hnat
  dsimp only [mappingConeCompTriangle, Pretriangulated.Triangle.mk_mor₃]
  erw [Functor.shiftMap_comp]
  change ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (mappingCone.triangle b).mor₃ n₀ n₁ h ≫
        HomologicalComplex.homologyMap (mappingCone.inr a) n₁) ≫
      HomologicalComplex.homologyMap (mappingCone.descShortComplex (cokernelSequence a)) n₁ = _
  rw [hb']
  erw [Category.assoc, Category.assoc]
  erw [← HomologicalComplex.homologyMap_comp]
  erw [mappingCone.inr_descShortComplex (cokernelSequence a)]
  rw [← hnat]
  rfl

omit [Mono a] in
/-- The connecting map in cohomology of the distinguished triangle of mapping cones
`cone a ⟶ cone (a ≫ b) ⟶ cone b ⟶ (cone a)⟦1⟧` in the homotopy category, read through the
quasi-isomorphisms `cone a ⟶ cokernel a` and `cone b ⟶ cokernel b`, is the connecting map of the
short exact sequence `cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b`. -/
lemma homologySequenceδ_mappingConeCompTriangleh (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
        ((quotient C (ComplexShape.up ℤ)).mapTriangle.obj (mappingConeCompTriangle a b))
        n₀ n₁ h ≫
      (homologyFunctorFactors C (ComplexShape.up ℤ) n₁).hom.app (mappingCone a) ≫
        HomologicalComplex.homologyMap (mappingCone.descShortComplex (cokernelSequence a)) n₁ =
    (homologyFunctorFactors C (ComplexShape.up ℤ) n₀).hom.app (mappingCone b) ≫
      HomologicalComplex.homologyMap (mappingCone.descShortComplex (cokernelSequence b)) n₀ ≫
        (cokernelCompShortComplex_shortExact a b).δ n₀ n₁ (by simp [← h]) := by
  rw [homologySequenceδ_quotient_mapTriangle_obj]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc,
    shiftMap_mappingConeCompTriangle_mor₃ a b n₀ n₁ (by lia)]
  rfl

end Connecting

section SpectralObject

variable {ι : Type*} [Category* ι] (F : ι ⥤ CochainComplex C ℤ)

/-- The connecting maps of the spectral object of `F`, for monomorphisms `F.map f` and `F.map g`,
are the connecting maps of the short exact sequences of cokernels
`cokernel (F.map f) ⟶ cokernel (F.map f ≫ F.map g) ⟶ cokernel (F.map g)`. -/
lemma spectralObject_δ_comp_hIsoCokernel {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
    [Mono (F.map f)] [Mono (F.map g)] (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (spectralObject F).δ f g n₀ n₁ h ≫ (spectralObjectHIsoCokernel F f n₁).hom =
      (spectralObjectHIsoCokernel F g n₀).hom ≫
        (cokernelCompShortComplex_shortExact (F.map f) (F.map g)).δ n₀ n₁ (by simp [← h]) := by
  have e (a b : ι) (u : a ⟶ b) [Mono (F.map u)] (n : ℤ) : (spectralObjectHIsoCokernel F u n).hom =
      (homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.app (mappingCone (F.map u)) ≫
        HomologicalComplex.homologyMap (mappingCone.descShortComplex (cokernelSequence (F.map u)))
          n := rfl
  rw [spectralObject_δ, e, e]
  exact (homologySequenceδ_mappingConeCompTriangleh (F.map f) (F.map g) n₀ n₁ h).trans
    (Category.assoc _ _ _).symm

end SpectralObject

section SpectralSequence

variable (F : EInt ⥤ CochainComplex C ℤ) [∀ ⦃a b : EInt⦄ (u : a ⟶ b), Mono (F.map u)]

/-- **The first differential of the spectral sequence of a filtered complex.** When the
transition maps of `F : EInt ⥤ CochainComplex C ℤ` are monomorphisms, the differential of the
first page from `(p, q)` to `(p + 2, q - 1)` is, under the identifications of the first page with
the cohomology of the graded pieces, the connecting map
`H^{p+q}(F_{q+1}/F_q) ⟶ H^{p+q+1}(F_q/F_{q-1})` of the short exact sequence
`F_q/F_{q-1} ⟶ F_{q+1}/F_{q-1} ⟶ F_{q+1}/F_q`. -/
theorem spectralSequence_page_two_d_eq (p q : ℤ) :
    ((spectralSequence F).page 2).d (p, q) (p + 2, q - 1) =
      (spectralSequenceFirstPageXIsoCokernel F (p, q) q (q + 1) rfl rfl (p + q) rfl).hom ≫
        (cokernelCompShortComplex_shortExact
          (F.map (homOfLE (show ((q - 1 : ℤ) : EInt) ≤ q by simp)))
          (F.map (homOfLE (show (q : EInt) ≤ (q + 1 : ℤ) by simp)))).δ (p + q) (p + q + 1)
            rfl ≫
        (spectralSequenceFirstPageXIsoCokernel F (p + 2, q - 1) (q - 1) q rfl (by lia)
          (p + q + 1) (by lia)).inv := by
  have key := spectralObject_δ_comp_hIsoCokernel F
    (homOfLE (show ((q - 1 : ℤ) : EInt) ≤ q by simp))
    (homOfLE (show (q : EInt) ≤ (q + 1 : ℤ) by simp)) (p + q) (p + q + 1) rfl
  rw [← Iso.eq_comp_inv] at key
  rw [Abelian.SpectralObject.spectralSequence_first_page_d_eq (spectralObject F)
    Abelian.SpectralObject.coreE₂Cohomological (p, q) (p + 2, q - 1)
    (by simp [ComplexShape.up']; lia) ((q - 1 : ℤ) : EInt) q ((q + 1 : ℤ) : EInt) rfl rfl rfl
    (p + q) (p + q + 1) rfl, key]
  simp [spectralSequenceFirstPageXIsoCokernel]

end SpectralSequence

end CochainComplex
