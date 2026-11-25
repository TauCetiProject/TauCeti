/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.LocallyFinite
public import TauCeti.Topology.Homotopy.Extension.CWComplex
public import TauCeti.Topology.Homotopy.Extension.Proper.DeformationRetract
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import TauCeti.Topology.CWComplex.Classical.Finite
import TauCeti.Topology.Maps.Proper.Basic

/-!
# Proper homotopy extension for strongly locally finite CW complexes

For a subcomplex `E` of an infinite-dimensional CW complex `C`, the cell-by-cell skeletal cylinder
retraction `r : I × C → I × C` onto `{0} × C ∪ I × E` need not be proper under local finiteness
alone; Farrell, Taylor, and Wagoner show that **strong local finiteness**
(`Topology.CWComplex.StronglyLocallyFinite`) makes `r` proper.

Using `TauCeti.exists_retraction_cylinderExtensionDomain_base` from
`TauCeti.Topology.Homotopy.Extension.CWComplex`, the skeletal cylinder retraction `r` onto
`{0} × C ∪ I × E` preserves every closed-cell-saturated subset `S ⊆ X` — in particular every
subcomplex `F` of `C`. When `C` admits a locally finite cover by finite subcomplexes `(F k)`, any
compact `K ⊆ C` meets only finitely many `F k`, so `r⁻¹(I × K)` is closed inside a finite union of
compact cylinders `I × F k`, proving `IsProperMap r`
(`Topology.RelCWComplex.Subcomplex.hasProperHomotopyExtensionProperty`).

## Main results

* `Topology.RelCWComplex.Subcomplex.hasProperHomotopyExtensionProperty`,
  `Topology.RelCWComplex.Subcomplex.hasProperHomotopyExtensionProperty_of_finiteDimensional`,
  `Topology.RelCWComplex.Subcomplex.hasProperHomotopyExtensionProperty_univ`,
  `TauCeti.hasProperHomotopyExtensionProperty_skeletonLT`: **proper homotopy extension for
  subcomplexes and skeletons** of strongly locally finite (or finite-dimensional locally finite)
  Hausdorff CW complexes.
* `Topology.RelCWComplex.Subcomplex.hasProperHomotopyInverse_subtypeVal_iff`: in a strongly locally
  finite Hausdorff CW complex `C`, the inclusion of a subcomplex `E` is a proper homotopy
  equivalence if and only if `E` is a proper strong deformation retract of `C`.

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, Theorem 1.6.
* D. H. Baues, A. Quintero, *Infinite Homotopy Theory*, Kluwer Academic Publishers (2001),
  Chapter I, Proposition 3.8.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex unitInterval

universe u

namespace TauCeti

section StronglyLocallyFinite

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-- **Farrell–Taylor–Wagoner proper cofibration theorem.** Every subcomplex `E` of a strongly
locally finite Hausdorff CW complex `C` has the proper homotopy extension property inside `C`. -/
@[alias_in Topology.CWComplex.Subcomplex]
theorem _root_.Topology.RelCWComplex.Subcomplex.hasProperHomotopyExtensionProperty
    [CWComplex.StronglyLocallyFinite C] (E : CWComplex.Subcomplex C) :
    HasProperHomotopyExtensionProperty (Subtype.val ⁻¹' (E : Set X) : Set C) := by
  obtain ⟨r, hr_dom, hr_fix, hr_sat⟩ :=
    @exists_retraction_cylinderExtensionDomain_base X _ _ C E E.relCWComplex
  have hr_sub (F : CWComplex.Subcomplex C) (t : I) (x : C) (hx : (x : X) ∈ F) :
      ((r (t, x)).2 : X) ∈ F :=
    hr_sat (fun n i ⟨z, hzo, hzF⟩ ↦ by
      rw [E.openCell_relCWComplex] at hzo
      rw [E.closedCell_relCWComplex]
      exact F.closedCell_subset_of_mem ((F.mem_I_iff_of_mem_openCell hzo).2 hzF)) t x hx
  have hsnd : IsProperMap fun p : I × C ↦ (r p).2 := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨r.continuous.snd, fun K hK ↦ ?_⟩
    obtain ⟨ι, F, hF_fin, hF_cov, hF_lf⟩ :=
      CWComplex.StronglyLocallyFinite.exists_locallyFinite_finite_subcomplex (C := C)
    have hfin := hF_lf.finite_nonempty_inter_compact hK
    have hL_comp : IsCompact (⋃ k ∈ hfin.toFinset, (Subtype.val ⁻¹' (F k : Set X) : Set C)) :=
      hfin.toFinset.isCompact_biUnion fun k _ ↦ by
        have := hF_fin k
        exact RelCWComplex.isClosed.isProperMap_subtypeVal.isCompact_preimage
          CWComplex.isCompact_of_finite
    refine (isCompact_univ.prod hL_comp).of_isClosed_subset
      (hK.isClosed.preimage r.continuous.snd) fun ⟨t, x⟩ hxK ↦ ⟨trivial, ?_⟩
    obtain ⟨k, hxk⟩ := mem_iUnion.1 (hF_cov.symm.subset x.property)
    exact mem_biUnion (x := k) (hfin.mem_toFinset.2 ⟨(r (t, x)).2, hr_sub (F k) t x hxk, hxK⟩) hxk
  exact hasProperHomotopyExtensionProperty_of_retraction
    (hsnd.prodMk_of_t2_left r.continuous.fst) hr_dom hr_fix

/-- On a finite-dimensional locally finite Hausdorff CW complex, every subcomplex has the proper
homotopy extension property. -/
@[alias_in Topology.CWComplex.Subcomplex]
theorem
    _root_.Topology.RelCWComplex.Subcomplex.hasProperHomotopyExtensionProperty_of_finiteDimensional
    [CWComplex.LocallyFinite C] [CWComplex.FiniteDimensional C] (E : CWComplex.Subcomplex C) :
    HasProperHomotopyExtensionProperty (Subtype.val ⁻¹' (E : Set X) : Set C) := by
  have := CWComplex.LocallyFinite.stronglyLocallyFinite_of_finiteDimensional (C := C)
  exact E.hasProperHomotopyExtensionProperty

/-- Every skeleton of a strongly locally finite Hausdorff CW complex has the proper homotopy
extension property inside the complex. -/
theorem hasProperHomotopyExtensionProperty_skeletonLT [CWComplex.StronglyLocallyFinite C]
    (n : ℕ∞) :
    HasProperHomotopyExtensionProperty
      (Subtype.val ⁻¹' (CWComplex.skeletonLT C n : Set X) : Set C) :=
  (CWComplex.skeletonLT C n).hasProperHomotopyExtensionProperty

/-- When `W` carries a strongly locally finite CW structure on `univ`, every subcomplex `E` has the
proper homotopy extension property as a subset of `W`. -/
@[alias_in Topology.CWComplex.Subcomplex]
theorem _root_.Topology.RelCWComplex.Subcomplex.hasProperHomotopyExtensionProperty_univ
    {W : Type u} [TopologicalSpace W] [T2Space W] [CWComplex (univ : Set W)]
    [CWComplex.StronglyLocallyFinite (univ : Set W)]
    (E : CWComplex.Subcomplex (univ : Set W)) :
    HasProperHomotopyExtensionProperty (E : Set W) := by
  have h := E.hasProperHomotopyExtensionProperty.image (Homeomorph.Set.univ W)
  rwa [Homeomorph.Set.univ_apply, image_preimage_eq_range_inter, Subtype.range_coe, univ_inter] at h

/-- **Proper strong deformation retraction onto a subcomplex.** In a strongly locally finite
Hausdorff CW complex `C`, the inclusion of a subcomplex `E` is a proper homotopy equivalence if and
only if `E` is a proper strong deformation retract of `C`. -/
@[alias_in Topology.CWComplex.Subcomplex]
theorem _root_.Topology.RelCWComplex.Subcomplex.hasProperHomotopyInverse_subtypeVal_iff
    [CWComplex.StronglyLocallyFinite C] (E : CWComplex.Subcomplex C) :
    (ContinuousMap.subtypeVal
      (Subtype.val ⁻¹' (E : Set X) : Set C)).HasProperHomotopyInverse ↔
      ∃ r : C(C, Subtype.val ⁻¹' (E : Set X)), IsProperMap r ∧
        (∀ a : Subtype.val ⁻¹' (E : Set X), r a = a) ∧
        ∃ H : (ContinuousMap.id C).HomotopyRel
          ((ContinuousMap.subtypeVal (Subtype.val ⁻¹' (E : Set X) : Set C)).comp r)
          (Subtype.val ⁻¹' (E : Set X) : Set C), IsProperMap H := by
  rw [E.hasProperHomotopyExtensionProperty.hasProperHomotopyInverse_subtypeVal_iff,
    and_iff_right (E.closed.preimage continuous_subtypeVal)]

end StronglyLocallyFinite

end TauCeti
