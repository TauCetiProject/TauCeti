/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Extension
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic

/-!
# Extension of ideles concentrated at a single place

Let `L/K` be an extension of number fields. An idele of `K` concentrated at one place `v` extends in
`L` to the product over the places `w` of `L` above `v` of the ideles concentrated at `w` carrying
the images of the source component under the local completion maps. These decompositions are dual to
`ideleNormMap_ofAdicCompletion` and `ideleClassNormMap_ofAdicCompletion`, which evaluate the idele
norm on an idele of `L` concentrated at one place `w` as an idele of `K` concentrated at the place
below `w`.

## Main results

* `TauCeti.GlobalNumberFields.ideleExtension_ofAdicCompletion` and
  `TauCeti.GlobalNumberFields.ideleClassExtension_ofAdicCompletion`: place-above product
  decompositions of `ideleExtension` and `ideleClassExtension` at a finite place.
* `TauCeti.GlobalNumberFields.ideleExtension_ofCompletion` and
  `TauCeti.GlobalNumberFields.ideleClassExtension_ofCompletion`: place-above product decompositions
  of `ideleExtension` and `ideleClassExtension` at an infinite place.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped AdicCompletionExtension
attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Extension of an idele concentrated at a finite place.** Extending `ofAdicCompletion v u` from
`K` to `L` decomposes it as the product over the finite places `w` of `L` above `v` of
`ofAdicCompletion w` applied to the image of `u` in `L_wˣ`. -/
theorem ideleExtension_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ideleExtension K L (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) =
      ∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        IdeleGroup.ofAdicCompletion (𝓞 L) L w.1
          (Units.map (HeightOneSpectrum.adicCompletionExtension K L v w.1).toMonoidHom u) := by
  classical
  let _ : Fintype {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} :=
    Fintype.ofFinite _
  rw [finprod_eq_prod_of_fintype]
  refine IdeleGroup.ext (fun w ↦ ?_) (fun w ↦ ?_)
  · simp [ideleInfiniteCoord_ideleExtension, map_prod]
  · rw [ideleFiniteCoord_ideleExtension, map_prod]
    by_cases hw : w.asIdeal.LiesOver v.asIdeal
    · have hv : w.under (𝓞 K) = v := HeightOneSpectrum.asIdeal_injective hw.over.symm
      rw [Finset.prod_eq_single ⟨w, hw⟩
        (fun w' _ hw' ↦ w.ideleFiniteCoord_ofAdicCompletion_of_ne (fun h ↦ hw' (Subtype.ext h.symm))
          _)
        (fun h ↦ (h (Finset.mem_univ _)).elim),
        w.ideleFiniteCoord_ofAdicCompletion_self]
      subst hv
      simp only [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self]
    · have hne : w.under (𝓞 K) ≠ v := fun h ↦ hw (h ▸ inferInstance)
      rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne _ hne, map_one,
        Finset.prod_eq_one fun w' _ ↦
          w.ideleFiniteCoord_ofAdicCompletion_of_ne (fun h ↦ hw (h ▸ w'.2)) _]

/-- **Extension of an idele class concentrated at a finite place.** Extending
`IdeleClassGroup.ofAdicCompletion v u` from `K` to `L` decomposes it into the product over the
finite places `w` of `L` above `v`. -/
theorem ideleClassExtension_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ideleClassExtension K L (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u) =
      ∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        IdeleClassGroup.ofAdicCompletion (𝓞 L) L w.1
          (Units.map (HeightOneSpectrum.adicCompletionExtension K L v w.1).toMonoidHom u) := by
  classical
  let _ : Fintype {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} :=
    Fintype.ofFinite _
  rw [IdeleClassGroup.ofAdicCompletion_apply, ideleClassExtension_mk,
    ideleExtension_ofAdicCompletion, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype,
    ← QuotientGroup.mk'_apply, map_prod]
  rfl

/-- **Extension of an idele concentrated at an infinite place.** Extending `ofCompletion v u` from
`K` to `L` decomposes it as the product over the infinite places `w` of `L` above `v` of
`ofCompletion w` applied to the image of `u` in `L_wˣ`. -/
theorem ideleExtension_ofCompletion (v : InfinitePlace K) (u : v.Completionˣ) :
    ideleExtension K L (IdeleGroup.ofCompletion (𝓞 K) K v u) =
      ∏ᶠ w : {w : InfinitePlace L // w.LiesOver v},
        IdeleGroup.ofCompletion (𝓞 L) L w.1
          (Units.map (AbsoluteValue.Completion.map v.1 w.1.1).toMonoidHom u) := by
  classical
  let _ : Fintype {w : InfinitePlace L // w.LiesOver v} := Fintype.ofFinite _
  rw [finprod_eq_prod_of_fintype]
  refine IdeleGroup.ext (fun w ↦ ?_) (fun w ↦ ?_)
  · rw [ideleInfiniteCoord_ideleExtension, map_prod]
    by_cases hw : w.LiesOver v
    · have hv : w.comap (algebraMap K L) = v := InfinitePlace.LiesOver.comap_eq w v
      rw [Finset.prod_eq_single ⟨w, hw⟩
        (fun w' _ hw' ↦ w.ideleInfiniteCoord_ofCompletion_of_ne (fun h ↦ hw' (Subtype.ext h.symm))
          _)
        (fun h ↦ (h (Finset.mem_univ _)).elim),
        w.ideleInfiniteCoord_ofCompletion_self]
      subst hv
      simp only [InfinitePlace.ideleInfiniteCoord_ofCompletion_self]
    · have hne : w.comap (algebraMap K L) ≠ v := fun h ↦ hw (h ▸ inferInstance)
      rw [InfinitePlace.ideleInfiniteCoord_ofCompletion_of_ne _ hne, map_one,
        Finset.prod_eq_one fun w' _ ↦
          w.ideleInfiniteCoord_ofCompletion_of_ne (fun h ↦ hw (h ▸ w'.2)) _]
  · simp [ideleFiniteCoord_ideleExtension, map_prod]

/-- **Extension of an idele class concentrated at an infinite place.** Extending
`IdeleClassGroup.ofCompletion v u` from `K` to `L` decomposes it into the product over the infinite
places `w` of `L` above `v`. -/
theorem ideleClassExtension_ofCompletion (v : InfinitePlace K) (u : v.Completionˣ) :
    ideleClassExtension K L (IdeleClassGroup.ofCompletion (𝓞 K) K v u) =
      ∏ᶠ w : {w : InfinitePlace L // w.LiesOver v},
        IdeleClassGroup.ofCompletion (𝓞 L) L w.1
          (Units.map (AbsoluteValue.Completion.map v.1 w.1.1).toMonoidHom u) := by
  classical
  let _ : Fintype {w : InfinitePlace L // w.LiesOver v} := Fintype.ofFinite _
  rw [IdeleClassGroup.ofCompletion_apply, ideleClassExtension_mk,
    ideleExtension_ofCompletion, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype,
    ← QuotientGroup.mk'_apply, map_prod]
  rfl

end TauCeti.GlobalNumberFields
