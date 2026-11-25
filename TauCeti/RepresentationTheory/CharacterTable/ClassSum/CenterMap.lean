/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Center
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basis
public import TauCeti.RepresentationTheory.GroupAlgebra.OrbitSum

/-!
# Changing the coefficients of the centre of a group algebra

For a group `G`, a ring homomorphism `f : R →+* S` induces the ring homomorphism
`MonoidAlgebra.centerMapRingHom G f : Z(R[G]) →+* Z(S[G])` between the centres of the group
algebras. Since `Z(R[G]) = R[G]^G`, this is the case `H = G` of the map
`TauCeti.conjInvariantsMap f H : R[G]^H →+* S[G]^H`, and class sums are the orbit sums of
conjugation by `G` (`TauCeti.classSum_mk_eq_conjOrbitSum`). For finite `G`, read in the class-sum
bases of the two centres it is `f` applied to each coordinate: it sends each class sum to the class
sum of the same conjugacy class. It is surjective whenever `f` is, and for finite `G` its kernel is
the extension of `ker f` to `Z(R[G])`, consisting of the central elements all of whose coefficients
lie in `ker f`.

For the reduction `O → k` of a local ring onto its residue field this says that
`Z(O[G]) → Z(k[G])` is surjective, and for finite `G` its kernel is `𝔪 Z(O[G])`; it is the map
along which the blocks of `k[G]` are lifted to blocks of `O[G]`.

## Main results

* `TauCeti.classSum_mk_eq_conjOrbitSum`: class sums are the orbit sums of conjugation by `G`.
* `TauCeti.centerMapRingHom_classSumCenter`: the map on centres sends class sums to class sums.
* `TauCeti.centerMapRingHom_surjective`: the map on centres is surjective when `f` is.
* `TauCeti.ker_centerMapRingHom`: for finite `G`, its kernel is
  `(ker f).map (algebraMap R Z(R[G]))`.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {G R S : Type*} [Group G] [CommSemiring R] [CommSemiring S]

/-- The map on centres applies `f` to the coefficient of a central element on each conjugacy
class. -/
@[simp]
theorem centerToConjClasses_centerMapRingHom (f : R →+* S)
    (z : Subalgebra.center R (MonoidAlgebra R G)) (C : ConjClasses G) :
    centerToConjClasses (centerMapRingHom G f z) C = f (centerToConjClasses z C) := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  simp

section Fintype

variable [Fintype G] [DecidableEq G]

/-- The class sum of the conjugacy class of `g` is the orbit sum of `g` under conjugation by all
of `G`. -/
theorem classSum_mk_eq_conjOrbitSum (g : G) :
    classSum R (ConjClasses.mk g) = conjOrbitSum R (Quotient.mk (conjOrbitRel ⊤) g) := by
  classical
  ext h
  simp [ConjClasses.mk_eq_mk_iff_isConj, Quotient.eq, conjOrbitRel_top_iff]

/-- The map on centres sends the class sum of a conjugacy class to the class sum of the same
class. -/
@[simp]
theorem centerMapRingHom_classSumCenter (f : R →+* S) (C : ConjClasses G) :
    centerMapRingHom G f (classSumCenter C) = classSumCenter C := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  ext1
  simp [classSum_mk_eq_conjOrbitSum]

end Fintype

/-- **Surjectivity of the map on centres.** If `f : R →+* S` is surjective, so is the induced map
`Z(R[G]) → Z(S[G])`. -/
theorem centerMapRingHom_surjective {f : R →+* S} (hf : Function.Surjective f) :
    Function.Surjective (centerMapRingHom G f) := fun w ↦ by
  -- `Z(R[G]) = R[G]^G`, so this is `conjInvariantsMap_surjective` for `H = G`
  obtain ⟨x, hx⟩ := conjInvariantsMap_surjective f hf (⊤ : Subgroup G)
    ⟨w, by rw [conjInvariants_top]; exact w.property⟩
  refine ⟨⟨x, by rw [← conjInvariants_top]; exact x.property⟩, Subtype.ext ?_⟩
  simpa using congrArg Subtype.val hx

variable [Finite G]

/-- **The kernel of the map on centres.** The central elements of `R[G]` killed by `f` are those of
the extension of the ideal `ker f` to the centre `Z(R[G])`: they are the combinations of class sums
with coefficients in `ker f`. -/
theorem ker_centerMapRingHom (f : R →+* S) :
    RingHom.ker (centerMapRingHom G f) =
      (RingHom.ker f).map (algebraMap R (Subalgebra.center R (MonoidAlgebra R G))) := by
  let := Fintype.ofFinite G
  classical
  refine le_antisymm (fun z hz ↦ ?_) (Ideal.map_le_iff_le_comap.mpr fun r hr ↦ ?_)
  · have hcoeff (C : ConjClasses G) : centerToConjClasses z C ∈ RingHom.ker f := by
      rw [RingHom.mem_ker, ← centerToConjClasses_centerMapRingHom, (RingHom.mem_ker).mp hz]
      obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
      simp
    rw [← classSumBasis.sum_repr z]
    refine Ideal.sum_mem _ fun C _ ↦ ?_
    rw [Algebra.smul_def, classSumBasis_repr_apply]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hcoeff C))
  · rw [Ideal.mem_comap, RingHom.mem_ker, centerMapRingHom_algebraMap, (RingHom.mem_ker).mp hr,
      map_zero]

end TauCeti
