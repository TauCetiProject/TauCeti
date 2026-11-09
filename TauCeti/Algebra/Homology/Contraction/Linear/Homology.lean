/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.Algebra.Homology.Contraction.Linear.Basic
public import TauCeti.Algebra.Module.GradedModule.Homology
public import TauCeti.LinearAlgebra.Graded.Splitting

/-!
# Contracting a graded complex over a division ring onto its homology

Let `d` be a square-zero endomorphism of degree one of an internally `ℤ`-graded vector space `M`
over a division ring, for instance a field.  Then `(M, d)` contracts onto its homology
`H = ker d ⧸ im d` (`LinearMap.homology`), with zero differential and the induced grading
`TauCeti.InternalGrading.homology`: there is a special contraction whose inclusion and projection
have degree zero and whose homotopy has degree `-1`
(`TauCeti.InternalGrading.homologyContraction`).

The construction chooses two homogeneous splittings, which exist because every module over a
division ring is projective (`TauCeti.LinearMap.IsHomogeneous.exists_rightInverse`): a section `s`
of degree `-1` of the corestriction `M ⟶ im d` of `d`, and a section of degree zero of the
quotient map `ker d ⟶ H`, choosing cycle representatives.  The endomorphism `q = 1 - s d` projects
onto the cycles.  The inclusion `i` sends a class to its chosen representative, the projection `p`
sends `x` to the class of the cycle `q x`, and the homotopy is `h x = s (q x - i (p x))`, which
makes sense because the cycle `q x - i (p x)` has zero class and is therefore a boundary.

This is the input of homological transfer over a field: an `A∞` structure, or an `A∞` module
structure, whose unary operation is `d` transfers along this contraction to a minimal one on the
homology, which is Kadeishvili's theorem.

## Main definitions

* `TauCeti.InternalGrading.homologyContraction`: the special contraction of `(M, d)` onto its
  homology with zero differential.

## Main results

* `TauCeti.InternalGrading.homologyContraction_incl_mem_ker` and
  `TauCeti.InternalGrading.homologyπ_homologyContraction_incl`: the inclusion chooses a cycle
  representing the given homology class.
* `TauCeti.InternalGrading.homologyContraction_proj_of_mem_ker`: the projection sends a cycle to
  its homology class.
* `TauCeti.InternalGrading.isHomogeneous_homologyContraction_incl`,
  `TauCeti.InternalGrading.isHomogeneous_homologyContraction_proj` and
  `TauCeti.InternalGrading.isHomogeneous_homologyContraction_homotopy`: the inclusion and
  projection have degree zero and the homotopy has degree `-1`.

## References

* T. Kadeishvili, *The algebraic structure in the homology of an `A(∞)`-algebra*.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.3.
-/

public section

open DirectSum LinearMap

namespace TauCeti.InternalGrading

universe uK uM

variable {K : Type uK} {M : Type uM} [DivisionRing K] [AddCommGroup M] [Module K M]
  (G : InternalGrading K M) {d : Module.End K M}
  (hhom : TauCeti.LinearMap.IsHomogeneous d G.piece G.piece 1) (hd : d ∘ₗ d = 0)

/-! ### A homogeneous section of the differential onto its image -/

/-- The grading of the image of `d` by its homogeneous elements. -/
private noncomputable def rangeGrading : InternalGrading K (range d) :=
  G.submodule (range d) hhom.isHomogeneous_range

/-- A homogeneous section of degree `-1` of the corestriction of `d` to its image. -/
private noncomputable def rangeSection : range d →ₗ[K] M :=
  Classical.choose ((G.isHomogeneous_rangeRestrict hhom).exists_rightInverse
    d.surjective_rangeRestrict)

private theorem rangeRestrict_comp_rangeSection :
    d.rangeRestrict ∘ₗ G.rangeSection hhom = LinearMap.id :=
  (Classical.choose_spec ((G.isHomogeneous_rangeRestrict hhom).exists_rightInverse
    d.surjective_rangeRestrict)).1

private theorem isHomogeneous_rangeSection :
    TauCeti.LinearMap.IsHomogeneous (G.rangeSection hhom) (G.rangeGrading hhom).piece G.piece
      (-1) :=
  (Classical.choose_spec ((G.isHomogeneous_rangeRestrict hhom).exists_rightInverse
    d.surjective_rangeRestrict)).2

private theorem rangeRestrict_rangeSection (b : range d) :
    d.rangeRestrict (G.rangeSection hhom b) = b :=
  LinearMap.congr_fun (G.rangeRestrict_comp_rangeSection hhom) b

/-- The section is a preimage under `d`. -/
private theorem apply_rangeSection (b : range d) : d (G.rangeSection hhom b) = b :=
  congrArg Subtype.val (G.rangeRestrict_rangeSection hhom b)

private theorem coe_rangeRestrict (x : M) : (d.rangeRestrict x : M) = d x :=
  rfl

/-- A cycle has zero image in the image of `d`. -/
private theorem rangeRestrict_eq_zero_of_mem_ker {x : M} (hx : x ∈ LinearMap.ker d) :
    d.rangeRestrict x = 0 :=
  Subtype.ext hx

/-! ### Homogeneous cycle representatives -/

/-- A homogeneous choice of cycle representatives of homology classes. -/
private noncomputable def representative : d.homology hd →ₗ[K] LinearMap.ker d :=
  Classical.choose ((G.isHomogeneous_homologyπ hhom hd).exists_rightInverse
    (d.homologyπ_surjective hd))

private theorem homologyπ_representative (y : d.homology hd) :
    d.homologyπ hd (G.representative hhom hd y) = y :=
  LinearMap.congr_fun (Classical.choose_spec
    ((G.isHomogeneous_homologyπ hhom hd).exists_rightInverse (d.homologyπ_surjective hd))).1 y

private theorem isHomogeneous_representative :
    TauCeti.LinearMap.IsHomogeneous (G.representative hhom hd) (G.homology hhom hd).piece
      (G.ker hhom).piece 0 :=
  (Classical.choose_spec ((G.isHomogeneous_homologyπ hhom hd).exists_rightInverse
    (d.homologyπ_surjective hd))).2

/-! ### The contraction data -/

/-- The inclusion: a homology class goes to its chosen representative. -/
private noncomputable def incl : d.homology hd →ₗ[K] M :=
  (LinearMap.ker d).subtype ∘ₗ G.representative hhom hd

private theorem incl_apply (y : d.homology hd) :
    G.incl hhom hd y = G.representative hhom hd y :=
  rfl

private theorem cycleProjection_mem_ker (x : M) :
    x - G.rangeSection hhom (d.rangeRestrict x) ∈ LinearMap.ker d := by
  rw [LinearMap.mem_ker, map_sub, apply_rangeSection, coe_rangeRestrict, sub_self]

/-- The projection `q = 1 - s d` onto the cycles. -/
private noncomputable def cycleProjection : M →ₗ[K] LinearMap.ker d :=
  (LinearMap.id - G.rangeSection hhom ∘ₗ d.rangeRestrict).codRestrict (LinearMap.ker d)
    (G.cycleProjection_mem_ker hhom)

private theorem coe_cycleProjection (x : M) :
    (G.cycleProjection hhom x : M) = x - G.rangeSection hhom (d.rangeRestrict x) :=
  rfl

private theorem cycleProjection_of_mem_ker {x : M} (hx : x ∈ LinearMap.ker d) :
    G.cycleProjection hhom x = ⟨x, hx⟩ := by
  apply Subtype.ext
  rw [coe_cycleProjection, rangeRestrict_eq_zero_of_mem_ker hx, map_zero, sub_zero]

private theorem cycleProjection_rangeSection (b : range d) :
    G.cycleProjection hhom (G.rangeSection hhom b) = 0 := by
  apply Subtype.ext
  rw [coe_cycleProjection, rangeRestrict_rangeSection, sub_self, ZeroMemClass.coe_zero]

private theorem isHomogeneous_cycleProjection :
    TauCeti.LinearMap.IsHomogeneous (G.cycleProjection hhom) G.piece (G.ker hhom).piece 0 :=
  TauCeti.LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
    rw [add_zero, mem_ker_piece, coe_cycleProjection]
    exact Submodule.sub_mem _ hx <| by
      simpa only [add_neg_cancel_right] using (G.isHomogeneous_rangeSection hhom).map_mem
        ((G.isHomogeneous_rangeRestrict hhom).map_mem hx)

/-- The projection: the class of the cycle `q x`. -/
private noncomputable def proj : M →ₗ[K] d.homology hd :=
  d.homologyπ hd ∘ₗ G.cycleProjection hhom

private theorem proj_apply (x : M) :
    G.proj hhom hd x = d.homologyπ hd (G.cycleProjection hhom x) :=
  rfl

private theorem cycleProjection_incl (y : d.homology hd) :
    G.cycleProjection hhom (G.incl hhom hd y) = G.representative hhom hd y :=
  G.cycleProjection_of_mem_ker hhom (G.representative hhom hd y).2

private theorem proj_incl (y : d.homology hd) : G.proj hhom hd (G.incl hhom hd y) = y := by
  rw [proj_apply, cycleProjection_incl, homologyπ_representative]

include hd in
private theorem apply_mem_ker (x : M) : d x ∈ LinearMap.ker d := by
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hd, LinearMap.zero_apply]

private theorem proj_apply_apply (x : M) : G.proj hhom hd (d x) = 0 := by
  rw [proj_apply, G.cycleProjection_of_mem_ker hhom (apply_mem_ker hd x),
    homologyπ_eq_zero_iff]
  exact mem_range_self d x

private theorem proj_rangeSection (b : range d) : G.proj hhom hd (G.rangeSection hhom b) = 0 := by
  rw [proj_apply, cycleProjection_rangeSection, map_zero]

/-- The cycle `q x - i (p x)` is a boundary, since its class vanishes. -/
private theorem cycleProjection_sub_incl_proj_mem_range (x : M) :
    (G.cycleProjection hhom x : M) - G.incl hhom hd (G.proj hhom hd x) ∈ range d := by
  have h := (d.homologyπ_eq_zero_iff hd
    (G.cycleProjection hhom x - G.representative hhom hd (G.proj hhom hd x))).1 (by
      rw [map_sub, homologyπ_representative, proj_apply, sub_self])
  rw [incl_apply]
  simpa only [Submodule.coe_sub] using h

/-- The boundary `q x - i (p x)`. -/
private noncomputable def residual : M →ₗ[K] range d :=
  ((LinearMap.ker d).subtype ∘ₗ G.cycleProjection hhom -
      G.incl hhom hd ∘ₗ G.proj hhom hd).codRestrict (range d)
    (G.cycleProjection_sub_incl_proj_mem_range hhom hd)

private theorem coe_residual (x : M) :
    (G.residual hhom hd x : M) =
      G.cycleProjection hhom x - G.incl hhom hd (G.proj hhom hd x) :=
  rfl

private theorem residual_apply (x : M) : G.residual hhom hd (d x) = d.rangeRestrict x := by
  apply Subtype.ext
  rw [coe_residual, proj_apply_apply, map_zero, sub_zero,
    G.cycleProjection_of_mem_ker hhom (apply_mem_ker hd x), coe_rangeRestrict]

private theorem residual_incl (y : d.homology hd) : G.residual hhom hd (G.incl hhom hd y) = 0 := by
  apply Subtype.ext
  rw [coe_residual, proj_incl, cycleProjection_incl, incl_apply, sub_self,
    ZeroMemClass.coe_zero]

private theorem residual_rangeSection (b : range d) :
    G.residual hhom hd (G.rangeSection hhom b) = 0 := by
  apply Subtype.ext
  rw [coe_residual, cycleProjection_rangeSection, proj_rangeSection, map_zero, sub_zero,
    ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]

/-- The homotopy `h x = s (q x - i (p x))`. -/
private noncomputable def homotopy : Module.End K M :=
  G.rangeSection hhom ∘ₗ G.residual hhom hd

private theorem homotopy_apply (x : M) :
    G.homotopy hhom hd x = G.rangeSection hhom (G.residual hhom hd x) :=
  rfl

private theorem homotopy_rangeSection (b : range d) :
    G.homotopy hhom hd (G.rangeSection hhom b) = 0 := by
  rw [homotopy_apply, residual_rangeSection, map_zero]

/-! ### The contraction -/

/-- Over a division ring, a graded vector space with a square-zero differential `d` of degree one
**contracts onto its homology** `ker d ⧸ im d` with zero differential.  The inclusion chooses
homogeneous cycle representatives, the projection takes the class of the cycle `x - s (d x)` for
a homogeneous section `s` of `d` onto its image, and the homotopy is `s` applied to the boundary
`x - s (d x) - i (p x)`.  The inclusion and projection have degree zero and the homotopy has
degree `-1` (`isHomogeneous_homologyContraction_incl`, `isHomogeneous_homologyContraction_proj`,
`isHomogeneous_homologyContraction_homotopy`). -/
noncomputable def homologyContraction :
    LinearSpecialContraction d (0 : Module.End K (d.homology hd)) where
  incl := G.incl hhom hd
  proj := G.proj hhom hd
  homotopy := G.homotopy hhom hd
  dM_comp_incl := LinearMap.ext fun y ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.zero_apply, map_zero, incl_apply]
    exact (G.representative hhom hd y).2
  proj_comp_dM := LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, proj_apply_apply, LinearMap.zero_comp, LinearMap.zero_apply]
  proj_comp_incl := LinearMap.ext (G.proj_incl hhom hd)
  dM_comp_homotopy_add_homotopy_comp_dM := LinearMap.ext fun x ↦ by
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, homotopy_apply,
      apply_rangeSection, coe_residual, homotopy_apply, residual_apply, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.comp_apply, coe_cycleProjection]
    abel
  homotopy_comp_incl := LinearMap.ext fun y ↦ by
    rw [LinearMap.comp_apply, homotopy_apply, residual_incl, map_zero, LinearMap.zero_apply]
  proj_comp_homotopy := LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, homotopy_apply, proj_rangeSection, LinearMap.zero_apply]
  homotopy_comp_homotopy := LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, G.homotopy_apply hhom hd x, homotopy_rangeSection,
      LinearMap.zero_apply]

private theorem homologyContraction_incl : (G.homologyContraction hhom hd).incl = G.incl hhom hd :=
  rfl

private theorem homologyContraction_proj : (G.homologyContraction hhom hd).proj = G.proj hhom hd :=
  rfl

private theorem homologyContraction_homotopy :
    (G.homologyContraction hhom hd).homotopy = G.homotopy hhom hd :=
  rfl

private theorem isHomogeneous_incl :
    TauCeti.LinearMap.IsHomogeneous (G.incl hhom hd) (G.homology hhom hd).piece G.piece 0 :=
  TauCeti.LinearMap.isHomogeneous_def.2 fun _ y hy ↦ by
    rw [incl_apply]
    exact (G.mem_ker_piece hhom).1 ((G.isHomogeneous_representative hhom hd).map_mem hy)

private theorem isHomogeneous_proj :
    TauCeti.LinearMap.IsHomogeneous (G.proj hhom hd) G.piece (G.homology hhom hd).piece 0 :=
  TauCeti.LinearMap.isHomogeneous_def.2 fun _ x hx ↦ by
    rw [proj_apply]
    simpa only [add_zero] using (G.isHomogeneous_homologyπ hhom hd).map_mem
      ((G.isHomogeneous_cycleProjection hhom).map_mem hx)

/-- The inclusion of the homology contraction takes values in the cycles. -/
theorem homologyContraction_incl_mem_ker (y : d.homology hd) :
    (G.homologyContraction hhom hd).incl y ∈ LinearMap.ker d := by
  rw [homologyContraction_incl, incl_apply]
  exact (G.representative hhom hd y).2

/-- The inclusion of the homology contraction chooses a cycle representing the given class. -/
theorem homologyπ_homologyContraction_incl (y : d.homology hd) :
    d.homologyπ hd ⟨_, G.homologyContraction_incl_mem_ker hhom hd y⟩ = y := by
  simp only [homologyContraction_incl, incl_apply, Subtype.coe_eta]
  exact G.homologyπ_representative hhom hd y

/-- The projection of the homology contraction sends a cycle to its homology class. -/
@[simp]
theorem homologyContraction_proj_of_mem_ker {x : M} (hx : x ∈ LinearMap.ker d) :
    (G.homologyContraction hhom hd).proj x = d.homologyπ hd ⟨x, hx⟩ := by
  rw [homologyContraction_proj, proj_apply, G.cycleProjection_of_mem_ker hhom hx]

/-- The inclusion of the homology contraction has degree zero. -/
theorem isHomogeneous_homologyContraction_incl :
    TauCeti.LinearMap.IsHomogeneous (G.homologyContraction hhom hd).incl
      (G.homology hhom hd).piece G.piece 0 := by
  rw [homologyContraction_incl]
  exact G.isHomogeneous_incl hhom hd

/-- The projection of the homology contraction has degree zero. -/
theorem isHomogeneous_homologyContraction_proj :
    TauCeti.LinearMap.IsHomogeneous (G.homologyContraction hhom hd).proj G.piece
      (G.homology hhom hd).piece 0 := by
  rw [homologyContraction_proj]
  exact G.isHomogeneous_proj hhom hd

/-- The homotopy of the homology contraction has degree `-1`. -/
theorem isHomogeneous_homologyContraction_homotopy :
    TauCeti.LinearMap.IsHomogeneous (G.homologyContraction hhom hd).homotopy G.piece G.piece
      (-1) :=
  TauCeti.LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
    rw [homologyContraction_homotopy, homotopy_apply]
    refine (G.isHomogeneous_rangeSection hhom).map_mem ?_
    rw [rangeGrading, mem_submodule_piece, coe_residual]
    refine Submodule.sub_mem _ ?_ ?_
    · simpa only [add_zero, mem_ker_piece] using
        (G.isHomogeneous_cycleProjection hhom).map_mem hx
    · simpa only [add_zero] using
        (G.isHomogeneous_incl hhom hd).map_mem ((G.isHomogeneous_proj hhom hd).map_mem hx)

end TauCeti.InternalGrading
