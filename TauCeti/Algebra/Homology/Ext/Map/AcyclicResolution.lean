/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import TauCeti.Algebra.Homology.Ext.AcyclicResolution
public import TauCeti.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Exact functors and classes of cocycles of resolutions

Let `F ⟶ K` be a resolution in an abelian category `C` and `G : C ⥤ D` an exact functor. Then
`G` applied to `K` is a resolution of `G(F)`, and `G` sends the class
`CochainComplex.extMk` in `Extⁿ(P, F)` of a cocycle `f : P ⟶ Kⁿ` to the class in
`Extⁿ(G(P), G(F))` of the cocycle `G(f)` of `G(K)`
(`CochainComplex.mapExactFunctor_extMk`). The classes of the truncated resolutions
correspond through the identification `CategoryTheory.ShortComplex.mapCyclesIso` of the cycles
`G(Zⁿ) ≅ Zⁿ(G(K))` (`CochainComplex.mapExactFunctor_resolutionExtClass`).
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w w'

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {F : C} (K : CochainComplex C ℕ) (ι : F ⟶ K.X 0) [Mono ι] (hι : ι ≫ K.d 0 1 = 0)
  (hι' : (ShortComplex.mk ι (K.d 0 1) hι).Exact) (hK : ∀ j, K.ExactAt (j + 1))
  [Mono (G.map ι)] (hGι : G.map ι ≫ ((G.mapHomologicalComplex _).obj K).d 0 1 = 0)
  (hGι' : (ShortComplex.mk (G.map ι) (((G.mapHomologicalComplex _).obj K).d 0 1) hGι).Exact)
  (hGK : ∀ j, ((G.mapHomologicalComplex _).obj K).ExactAt (j + 1))

include hι' hK hGι' hGK in
/-- An exact functor sends the class of the truncated resolution `F ⟶ K⁰ ⟶ ⋯ ⟶ Kⁿ ⟶ Zⁿ⁺¹` to the
class of the truncated resolution of its image, through the identification of cycles. -/
lemma mapExactFunctor_resolutionExtClass (n : ℕ) :
    (K.resolutionExtClass ι hι hι' hK n).mapExactFunctor G =
      (Ext.mk₀ (((K.sc (n + 1)).mapCyclesIso G).inv)).comp
        (resolutionExtClass ((G.mapHomologicalComplex _).obj K) (G.map ι) hGι hGι' hGK n)
        (zero_add _) := by
  let L := (G.mapHomologicalComplex _).obj K
  have hc := fun k ↦ G.mapCyclesIso_inv_comp_iCycles _ k K
  induction n with
  | zero =>
    have hS := K.shortExact_resolution_zero ι hι hι' hK
    rw [resolutionExtClass_zero, Ext.mapExactFunctor_extClass, resolutionExtClass_zero]
    have h := (hS.map_of_exact G).extClass_naturality
      (shortExact_resolution_zero L (G.map ι) hGι hGι' hGK)
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := ((K.sc 1).mapCyclesIso G).inv
        comm₁₂ := by simp
        comm₂₃ := by
          simp [L, ← cancel_mono (((G.mapHomologicalComplex _).obj K).iCycles 1), hc,
            ← G.map_comp] }
    rw [Ext.comp_mk₀_id] at h
    exact h
  | succ n ih =>
    have hS := K.shortExact_resolution_succ hK n
    rw [resolutionExtClass_succ, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, ih,
      resolutionExtClass_succ, ← Ext.comp_assoc_of_second_deg_zero,
      (hS.map_of_exact G).extClass_naturality (shortExact_resolution_succ L hGK n)
        { τ₁ := ((K.sc (n + 1)).mapCyclesIso G).inv
          τ₂ := 𝟙 _
          τ₃ := ((K.sc (n + 2)).mapCyclesIso G).inv
          comm₁₂ := by simp [L, hc]
          comm₂₃ := by
            simp [L, ← cancel_mono (((G.mapHomologicalComplex _).obj K).iCycles (n + 2)), hc,
              ← G.map_comp] }]
    exact Ext.comp_assoc _ _ _ _ _ (by omega)

include hι' hK hGι' hGK in
/-- **Exact functors preserve classes of cocycles.** An exact functor `G` sends the class in
`Extⁿ(P, F)` of a cocycle `f : P ⟶ Kⁿ` of a resolution `F ⟶ K` to the class of the cocycle
`G(f)` of the resolution `G(F) ⟶ G(K)`. -/
theorem mapExactFunctor_extMk {P : C} {n : ℕ} (f : P ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    (K.extMk ι hι hι' hK f hf).mapExactFunctor G =
      extMk (K := (G.mapHomologicalComplex _).obj K) (G.map ι) hGι hGι' hGK (G.map f)
        (by rw [Functor.mapHomologicalComplex_obj_d, ← G.map_comp, hf, G.map_zero]) := by
  cases n with
  | zero =>
    rw [extMk_of_deg_zero, extMk_of_deg_zero, Ext.mapExactFunctor_mk₀]
    congr 1
    rw [← cancel_mono (G.map ι), hGι'.lift_f, ← G.map_comp, hι'.lift_f]
  | succ n =>
    rw [extMk_of_deg_succ, extMk_of_deg_succ, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      K.mapExactFunctor_resolutionExtClass G ι hι hι' hK hGι hGι' hGK n, Ext.mk₀_comp_mk₀_assoc]
    congr 2
    simp [← cancel_mono (((G.mapHomologicalComplex _).obj K).iCycles (n + 1)),
      Functor.mapCyclesIso_inv_comp_iCycles, ← G.map_comp]

end CochainComplex
