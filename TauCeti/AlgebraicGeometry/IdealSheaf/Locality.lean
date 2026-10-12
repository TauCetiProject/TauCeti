/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Locality of ideal sheaf data

An ideal sheaf is determined by its pullbacks to an open cover. This lets affine
computations of ideal sheaves, such as Fitting ideals, be glued on an arbitrary scheme.

-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti

universe u

variable {X : Scheme.{u}}

/-- An ideal sheaf is the intersection of the pushforwards of its restrictions to
an open cover. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.iInf_map_comap_openCover
    (I : X.IdealSheafData) (𝒰 : X.OpenCover) :
    (⨅ i, (I.comap (𝒰.f i)).map (𝒰.f i)) = I := by
  -- Mathlib's `Scheme.Hom.iInf_ker_openCover_map_comp` computes the kernel on an
  -- open cover of its source; apply it to the ideal sheaf's closed immersion.
  calc
    _ = ⨅ i, ((𝒰.pullback₁ I.subschemeι).f i ≫ I.subschemeι).ker := by
      congr 1
      funext i
      rw [← Scheme.Cover.pullbackHom_map, ← map_ker]
      congr 1
      -- The pullback cover uses the opposite order of the two projections from `comap`.
      rw [Scheme.Cover.pullbackHom, ← pullbackSymmetry_hom_comp_fst]
      exact (Scheme.Hom.ker_comp_of_isIso
        (pullbackSymmetry I.subschemeι (𝒰.f i)).hom
        (pullback.fst (𝒰.f i) I.subschemeι)).symm
    _ = I := (I.subschemeι.iInf_ker_openCover_map_comp _).trans I.ker_subschemeι

/-- Ideal sheaves with equal pullbacks to every member of an open cover are equal. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.ext_of_comap_openCover
    {I J : X.IdealSheafData} (𝒰 : X.OpenCover)
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J := by
  rw [← I.iInf_map_comap_openCover 𝒰, ← J.iInf_map_comap_openCover 𝒰]
  simp only [h]

end TauCeti
