/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# Topology of the adele ring of a number field

Mathlib's `NumberField.InfiniteAdeleRing K` is the finite product of the completions of `K` at its
infinite places, and `NumberField.AdeleRing R K` is the product of the infinite adele ring with the
finite adele ring of `R`.  Both are defined as type synonyms, so the Hausdorff property of the
underlying products is not found by instance search.  This file records it, so that closedness of
discrete subgroups and separation of quotients apply to the adele ring.

It also upgrades Mathlib's ring equivalence between the infinite adele ring and the Minkowski
mixed space to a homeomorphism.  Each local factor is isometric to `ℝ` or `ℂ`, so the product
equivalence and its inverse are continuous.
-/

public section

namespace NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The infinite adele ring is Hausdorff, as a finite product of the completions at the infinite
places. -/
instance InfiniteAdeleRing.instT2Space : T2Space (InfiniteAdeleRing K) :=
  inferInstanceAs <| T2Space ((v : InfinitePlace K) → v.Completion)

open scoped Classical in
/-- The infinite adele ring is homeomorphic to the Minkowski mixed space.  This is the topological
form of `InfiniteAdeleRing.ringEquiv_mixedSpace`. -/
noncomputable def InfiniteAdeleRing.homeomorph_mixedSpace :
    InfiniteAdeleRing K ≃ₜ mixedEmbedding.mixedSpace K :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace K ↦ v.IsReal)
      (fun v ↦ v.Completion)).trans
    ((Homeomorph.piCongrRight fun v ↦
        (InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph).prodCongr
      ((Homeomorph.piCongrRight fun v ↦
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp v.2)).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ : {w : InfinitePlace K // w.IsComplex} ↦ ℂ)
          (Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex))))

@[simp]
theorem InfiniteAdeleRing.homeomorph_mixedSpace_apply
    (x : InfiniteAdeleRing K) :
    InfiniteAdeleRing.homeomorph_mixedSpace K x =
      InfiniteAdeleRing.ringEquiv_mixedSpace K x :=
  by
    ext v <;> rfl

@[simp]
theorem InfiniteAdeleRing.homeomorph_mixedSpace_symm_apply
    (x : mixedEmbedding.mixedSpace K) :
    (InfiniteAdeleRing.homeomorph_mixedSpace K).symm x =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x := by
  apply (InfiniteAdeleRing.homeomorph_mixedSpace K).injective
  rw [Homeomorph.apply_symm_apply, InfiniteAdeleRing.homeomorph_mixedSpace_apply,
    RingEquiv.apply_symm_apply]

/-- The standard ring equivalence from the infinite adele ring to the Minkowski mixed space is
continuous. -/
theorem InfiniteAdeleRing.continuous_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  exact (InfiniteAdeleRing.homeomorph_mixedSpace K).continuous.congr fun x ↦
    InfiniteAdeleRing.homeomorph_mixedSpace_apply K x

/-- The inverse of the standard ring equivalence from the Minkowski mixed space to the infinite
adele ring is continuous. -/
theorem InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  exact (InfiniteAdeleRing.homeomorph_mixedSpace K).symm.continuous.congr fun x ↦
    InfiniteAdeleRing.homeomorph_mixedSpace_symm_apply K x

/-- The adele ring is Hausdorff, as the product of the infinite and the finite adele rings. -/
instance AdeleRing.instT2Space : T2Space (AdeleRing R K) :=
  inferInstanceAs <| T2Space (InfiniteAdeleRing K × IsDedekindDomain.FiniteAdeleRing R K)

end NumberField
