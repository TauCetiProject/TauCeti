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
underlying products is not found by instance search.  This file records Hausdorffness and local
compactness, so that closedness of discrete subgroups and the standard topological properties of
idele groups and their quotients apply to the adele ring.

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
form of `InfiniteAdeleRing.ringEquiv_mixedSpace`: the underlying equivalence is the one of that
ring isomorphism, and continuity in both directions comes from the isometry of each completion
with `ℝ` or `ℂ`. -/
noncomputable def InfiniteAdeleRing.homeomorphMixedSpace :
    InfiniteAdeleRing K ≃ₜ mixedEmbedding.mixedSpace K :=
  let isom : InfiniteAdeleRing K ≃ₜ mixedEmbedding.mixedSpace K :=
    (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace K ↦ v.IsReal)
        (fun v ↦ v.Completion)).trans
      ((Homeomorph.piCongrRight fun v ↦
          (InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph).prodCongr
        ((Homeomorph.piCongrRight fun v ↦
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
              (InfinitePlace.not_isReal_iff_isComplex.mp v.2)).toHomeomorph).trans
          (Homeomorph.piCongrLeft (Y := fun _ : {w : InfinitePlace K // w.IsComplex} ↦ ℂ)
            (Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex))))
  have h (x : InfiniteAdeleRing K) :
      isom x = InfiniteAdeleRing.ringEquiv_mixedSpace K x := by
    -- Both equivalences use the same real and complex completion maps; compare them through
    -- Mathlib's public evaluation theorem instead of asking the structure fields to be defeq.
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    rfl
  have hsymm (x : mixedEmbedding.mixedSpace K) :
      isom.symm x = (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x := by
    apply isom.injective
    rw [isom.apply_symm_apply, h, RingEquiv.apply_symm_apply]
  { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv
    continuous_toFun := isom.continuous.congr h
    continuous_invFun := isom.symm.continuous.congr hsymm }

@[simp]
theorem InfiniteAdeleRing.homeomorphMixedSpace_apply
    (x : InfiniteAdeleRing K) :
    InfiniteAdeleRing.homeomorphMixedSpace K x =
      InfiniteAdeleRing.ringEquiv_mixedSpace K x :=
  by
    rw [InfiniteAdeleRing.homeomorphMixedSpace]
    rfl

@[simp]
theorem InfiniteAdeleRing.coe_homeomorphMixedSpace :
    ⇑(InfiniteAdeleRing.homeomorphMixedSpace K) =
      ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace K) :=
  by
    rw [InfiniteAdeleRing.homeomorphMixedSpace]
    rfl

@[simp]
theorem InfiniteAdeleRing.homeomorphMixedSpace_symm_apply
    (x : mixedEmbedding.mixedSpace K) :
    (InfiniteAdeleRing.homeomorphMixedSpace K).symm x =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x :=
  by
    rw [InfiniteAdeleRing.homeomorphMixedSpace]
    rfl

@[simp]
theorem InfiniteAdeleRing.coe_homeomorphMixedSpace_symm :
    ⇑(InfiniteAdeleRing.homeomorphMixedSpace K).symm =
      ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace K).symm :=
  by
    rw [InfiniteAdeleRing.homeomorphMixedSpace]
    rfl

/-- The standard ring equivalence from the infinite adele ring to the Minkowski mixed space is
continuous. -/
@[continuity, fun_prop]
theorem InfiniteAdeleRing.continuous_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) :=
  (InfiniteAdeleRing.homeomorphMixedSpace K).continuous.congr fun x ↦
    InfiniteAdeleRing.homeomorphMixedSpace_apply K x

/-- The inverse of the standard ring equivalence from the Minkowski mixed space to the infinite
adele ring is continuous. -/
@[continuity, fun_prop]
theorem InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm :=
  (InfiniteAdeleRing.homeomorphMixedSpace K).symm.continuous.congr fun x ↦
    InfiniteAdeleRing.homeomorphMixedSpace_symm_apply K x

/-- The adele ring is Hausdorff, as the product of the infinite and the finite adele rings. -/
instance AdeleRing.instT2Space : T2Space (AdeleRing R K) :=
  inferInstanceAs <| T2Space (InfiniteAdeleRing K × IsDedekindDomain.FiniteAdeleRing R K)

/-- The adele ring of a number field is nontrivial. -/
noncomputable instance AdeleRing.instNontrivial [NumberField K] :
    Nontrivial (AdeleRing R K) :=
  inferInstanceAs <| Nontrivial
    (InfiniteAdeleRing K × IsDedekindDomain.FiniteAdeleRing R K)

/-- The adele ring of a number field is locally compact, as the product of its locally compact
infinite and finite adele rings. -/
noncomputable instance AdeleRing.instLocallyCompactSpace [NumberField K]
    [LocallyCompactSpace (IsDedekindDomain.FiniteAdeleRing R K)] :
    LocallyCompactSpace (AdeleRing R K) :=
  inferInstanceAs <| LocallyCompactSpace
    (InfiniteAdeleRing K × IsDedekindDomain.FiniteAdeleRing R K)

end NumberField
