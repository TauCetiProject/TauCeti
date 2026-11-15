/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.Algebra.Homology.Contraction.Linear.HomotopyEquiv
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
homology, which is Kadeishvili's theorem.  Combined on both sides of a chain map `f : M →ₗ[K] N`
inducing a bijection on homology, the two homology contractions also promote `f` directly to a
homogeneous `TauCeti.LinearHomotopyEquiv` with forward map `f`
(`TauCeti.LinearHomotopyEquiv.ofHomologyMapBijective`).

## Main definitions

* `TauCeti.InternalGrading.homologyContraction`: the special contraction of `(M, d)` onto its
  homology with zero differential.
* `TauCeti.LinearHomotopyEquiv.ofHomologyMapBijective`: promote a chain quasi-isomorphism between
  graded differential vector spaces over a division ring to a `LinearHomotopyEquiv` with forward
  map `f`, degree-zero inverse, and degree-`-1` homotopies.

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
* `TauCeti.InternalGrading.homologyContraction_proj_comp_comp_incl`: compressing a chain map
  between homology contractions recovers `LinearMap.homologyMap`.
* `TauCeti.LinearHomotopyEquiv.isHomogeneous_ofHomologyMapBijective_inv`,
  `TauCeti.LinearHomotopyEquiv.isHomogeneous_ofHomologyMapBijective_homotopyHom` and
  `TauCeti.LinearHomotopyEquiv.isHomogeneous_ofHomologyMapBijective_homotopyInv`: over a division
  ring, the inverse and homotopies produced from a degree-zero quasi-isomorphism have degrees `0`
  and `-1`.

## References

* T. Kadeishvili, *The algebraic structure in the homology of an `A(∞)`-algebra*.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.3.
-/

public section

open DirectSum LinearMap

namespace TauCeti.InternalGrading

universe uK uM

variable {K : Type uK} {M : Type uM} [DivisionRing K] [AddCommGroup M] [Module K M]
  (G : InternalGrading K M ℤ) {d : Module.End K M}
  (hhom : TauCeti.LinearMap.IsHomogeneous d G.piece G.piece 1) (hd : d ∘ₗ d = 0)

/-! ### A homogeneous section of the differential onto its image -/

/-- The grading of the image of `d` by its homogeneous elements. -/
private noncomputable def rangeGrading : InternalGrading K (range d) ℤ :=
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

/-- Compressing a chain map `f` between homology contractions yields `LinearMap.homologyMap f`. -/
theorem homologyContraction_proj_comp_comp_incl {N : Type*}
    [AddCommGroup N] [Module K N] (GN : InternalGrading K N ℤ) {dN : Module.End K N}
    (hdN_hom : TauCeti.LinearMap.IsHomogeneous dN GN.piece GN.piece 1) (hdN : dN ∘ₗ dN = 0)
    {f : M →ₗ[K] N} (hf : f ∘ₗ d = dN ∘ₗ f) :
    (GN.homologyContraction hdN_hom hdN).proj ∘ₗ f ∘ₗ
        (G.homologyContraction hhom hd).incl =
      _root_.LinearMap.homologyMap f hd hdN hf := by
  refine LinearMap.ext fun y ↦ ?_
  set z : _root_.LinearMap.ker d :=
    ⟨(G.homologyContraction hhom hd).incl y,
      G.homologyContraction_incl_mem_ker hhom hd y⟩
  have hfz : f z ∈ _root_.LinearMap.ker dN :=
    _root_.LinearMap.map_mem_ker_of_comp_eq f hf z.2
  have hz : Submodule.Quotient.mk z = y := by
    rw [← d.homologyπ_apply hd]
    exact G.homologyπ_homologyContraction_incl hhom hd y
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    GN.homologyContraction_proj_of_mem_ker hdN_hom hdN hfz, dN.homologyπ_apply, ← hz,
    _root_.LinearMap.homologyMap_mk]

end TauCeti.InternalGrading

/-! ### Promoting a quasi-isomorphism to a homogeneous homotopy equivalence -/

namespace TauCeti.LinearHomotopyEquiv

universe uK uM uN

section DivisionRing

variable {K : Type uK} {M : Type uM} {N : Type uN} [DivisionRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- Over a division ring, any chain map `f : M →ₗ[K] N` between graded differential modules of
degree `1` that induces a bijection on homology extends to a `LinearHomotopyEquiv` with forward map
`f`.  When `f` has degree `0`, the constructed inverse has degree `0` and both homotopies have
degree `-1` (`isHomogeneous_ofHomologyMapBijective_inv`,
`isHomogeneous_ofHomologyMapBijective_homotopyHom`,
`isHomogeneous_ofHomologyMapBijective_homotopyInv`). -/
noncomputable def ofHomologyMapBijective
    (GM : InternalGrading K M ℤ) {dM : Module.End K M}
    (hdM_hom : TauCeti.LinearMap.IsHomogeneous dM GM.piece GM.piece 1) (hdM : dM ∘ₗ dM = 0)
    (GN : InternalGrading K N ℤ) {dN : Module.End K N}
    (hdN_hom : TauCeti.LinearMap.IsHomogeneous dN GN.piece GN.piece 1) (hdN : dN ∘ₗ dN = 0)
    {f : M →ₗ[K] N} (hf : f ∘ₗ dM = dN ∘ₗ f)
    (hbij : Function.Bijective (_root_.LinearMap.homologyMap f hdM hdN hf)) :
    LinearHomotopyEquiv dM dN := by
  let cM := GM.homologyContraction hdM_hom hdM
  let cN := GN.homologyContraction hdN_hom hdN
  let eH := LinearEquiv.ofBijective (_root_.LinearMap.homologyMap f hdM hdN hf) hbij
  have heH_to : eH.toLinearMap = _root_.LinearMap.homologyMap f hdM hdN hf := rfl
  have heH_comp : cN.proj ∘ₗ f ∘ₗ cM.incl = eH.toLinearMap :=
    (GM.homologyContraction_proj_comp_comp_incl hdM_hom hdM GN hdN_hom hdN hf).trans heH_to.symm
  have hdM_incl : dM ∘ₗ cM.incl = 0 := by rw [cM.dM_comp_incl, LinearMap.comp_zero]
  have hdN_incl : dN ∘ₗ cN.incl = 0 := by rw [cN.dM_comp_incl, LinearMap.comp_zero]
  have hproj_dN : cN.proj ∘ₗ dN = 0 := by rw [cN.proj_comp_dM, LinearMap.zero_comp]
  let g : N →ₗ[K] M := cM.incl ∘ₗ eH.symm.toLinearMap ∘ₗ cN.proj
  have hdM_g : dM ∘ₗ g = 0 := by
    simp only [g, ← LinearMap.comp_assoc, hdM_incl, LinearMap.zero_comp]
  have hg_dN : g ∘ₗ dN = 0 := by
    simp only [g, LinearMap.comp_assoc, hproj_dN, LinearMap.comp_zero]
  let ψ : Module.End K M := LinearMap.id - g ∘ₗ f
  have hdM_ψ : dM ∘ₗ ψ = ψ ∘ₗ dM := by
    rw [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_id, LinearMap.id_comp,
      ← LinearMap.comp_assoc, hdM_g, LinearMap.zero_comp, LinearMap.comp_assoc, hf,
      ← LinearMap.comp_assoc, hg_dN, LinearMap.zero_comp]
  have hψ_incl : ψ ∘ₗ cM.incl = 0 := by
    calc
      (LinearMap.id - g ∘ₗ f) ∘ₗ cM.incl
        = cM.incl - cM.incl ∘ₗ eH.symm.toLinearMap ∘ₗ (cN.proj ∘ₗ f ∘ₗ cM.incl) := by
          simp only [g, LinearMap.sub_comp, LinearMap.id_comp, LinearMap.comp_assoc]
      _ = cM.incl - cM.incl ∘ₗ (eH.symm.toLinearMap ∘ₗ eH.toLinearMap) := by
          rw [heH_comp]
      _ = 0 := by rw [eH.symm_comp, LinearMap.comp_id, sub_self]
  let δ : dM.homology hdM →ₗ[K] N := f ∘ₗ cM.incl - cN.incl ∘ₗ eH.toLinearMap
  have hdN_δ : dN ∘ₗ δ = 0 := by
    rw [LinearMap.comp_sub, ← LinearMap.comp_assoc, ← hf, LinearMap.comp_assoc, hdM_incl,
      LinearMap.comp_zero, ← LinearMap.comp_assoc, hdN_incl, LinearMap.zero_comp, sub_self]
  have hproj_δ : cN.proj ∘ₗ δ = 0 := by
    rw [LinearMap.comp_sub, heH_comp, ← LinearMap.comp_assoc, cN.proj_comp_incl, LinearMap.id_comp,
      sub_self]
  have hdN_hN_δ : dN ∘ₗ cN.homotopy ∘ₗ δ = δ := by
    have h := congrArg (· ∘ₗ δ) cN.dM_comp_homotopy_add_homotopy_comp_dM
    simpa only [LinearMap.add_comp, LinearMap.sub_comp, LinearMap.id_comp, LinearMap.comp_assoc,
      hdN_δ, hproj_δ, LinearMap.comp_zero, add_zero, sub_zero] using h
  let k : Module.End K N := cN.homotopy ∘ₗ δ ∘ₗ eH.symm.toLinearMap ∘ₗ cN.proj
  have hdN_k : dN ∘ₗ k = f ∘ₗ g - cN.incl ∘ₗ cN.proj := by
    calc
      dN ∘ₗ k = (dN ∘ₗ cN.homotopy ∘ₗ δ) ∘ₗ eH.symm.toLinearMap ∘ₗ cN.proj := by
        simp only [k, LinearMap.comp_assoc]
      _ = (f ∘ₗ cM.incl - cN.incl ∘ₗ eH.toLinearMap) ∘ₗ eH.symm.toLinearMap ∘ₗ cN.proj := by
        rw [hdN_hN_δ]
      _ = f ∘ₗ g - cN.incl ∘ₗ (eH.toLinearMap ∘ₗ eH.symm.toLinearMap) ∘ₗ cN.proj := by
        simp only [g, LinearMap.sub_comp, LinearMap.comp_assoc]
      _ = f ∘ₗ g - cN.incl ∘ₗ cN.proj := by
        rw [eH.comp_symm, LinearMap.id_comp]
  have hk_dN : k ∘ₗ dN = 0 := by
    simp only [k, LinearMap.comp_assoc, hproj_dN, LinearMap.comp_zero]
  refine
    { hom := f
      inv := g
      homotopyHom := ψ ∘ₗ cM.homotopy
      homotopyInv := cN.homotopy - k
      dN_comp_hom := hf.symm
      dM_comp_inv := hdM_g.trans hg_dN.symm
      dM_comp_homotopyHom_add_homotopyHom_comp_dM := ?_
      dN_comp_homotopyInv_add_homotopyInv_comp_dN := ?_ }
  · calc
      dM ∘ₗ (ψ ∘ₗ cM.homotopy) + (ψ ∘ₗ cM.homotopy) ∘ₗ dM
        = ψ ∘ₗ (dM ∘ₗ cM.homotopy + cM.homotopy ∘ₗ dM) := by
          rw [← LinearMap.comp_assoc, hdM_ψ, LinearMap.comp_assoc, LinearMap.comp_assoc,
            ← LinearMap.comp_add]
      _ = ψ ∘ₗ (LinearMap.id - cM.incl ∘ₗ cM.proj) := by
          rw [cM.dM_comp_homotopy_add_homotopy_comp_dM]
      _ = LinearMap.id - g ∘ₗ f := by
          rw [LinearMap.comp_sub, LinearMap.comp_id, ← LinearMap.comp_assoc, hψ_incl,
            LinearMap.zero_comp, sub_zero]
  · calc
      dN ∘ₗ (cN.homotopy - k) + (cN.homotopy - k) ∘ₗ dN
        = (dN ∘ₗ cN.homotopy + cN.homotopy ∘ₗ dN) - dN ∘ₗ k - k ∘ₗ dN := by
          simp only [LinearMap.comp_sub, LinearMap.sub_comp]
          abel
      _ = (LinearMap.id - cN.incl ∘ₗ cN.proj) - (f ∘ₗ g - cN.incl ∘ₗ cN.proj) - 0 := by
          rw [cN.dM_comp_homotopy_add_homotopy_comp_dM, hdN_k, hk_dN]
      _ = LinearMap.id - f ∘ₗ g := by abel

/-- The forward map of `ofHomologyMapBijective` is the given chain map `f`. -/
@[simp]
theorem ofHomologyMapBijective_hom
    (GM : InternalGrading K M ℤ) {dM : Module.End K M}
    (hdM_hom : TauCeti.LinearMap.IsHomogeneous dM GM.piece GM.piece 1) (hdM : dM ∘ₗ dM = 0)
    (GN : InternalGrading K N ℤ) {dN : Module.End K N}
    (hdN_hom : TauCeti.LinearMap.IsHomogeneous dN GN.piece GN.piece 1) (hdN : dN ∘ₗ dN = 0)
    {f : M →ₗ[K] N} (hf : f ∘ₗ dM = dN ∘ₗ f)
    (hbij : Function.Bijective (_root_.LinearMap.homologyMap f hdM hdN hf)) :
    (ofHomologyMapBijective GM hdM_hom hdM GN hdN_hom hdN hf hbij).hom = f :=
  (rfl)

/-- When `f` is homogeneous of degree zero, the inverse constructed by `ofHomologyMapBijective` is
homogeneous of degree zero. -/
theorem isHomogeneous_ofHomologyMapBijective_inv
    (GM : InternalGrading K M ℤ) {dM : Module.End K M}
    (hdM_hom : TauCeti.LinearMap.IsHomogeneous dM GM.piece GM.piece 1) (hdM : dM ∘ₗ dM = 0)
    (GN : InternalGrading K N ℤ) {dN : Module.End K N}
    (hdN_hom : TauCeti.LinearMap.IsHomogeneous dN GN.piece GN.piece 1) (hdN : dN ∘ₗ dN = 0)
    {f : M →ₗ[K] N} (hf_hom : TauCeti.LinearMap.IsHomogeneous f GM.piece GN.piece 0)
    (hf : f ∘ₗ dM = dN ∘ₗ f)
    (hbij : Function.Bijective (_root_.LinearMap.homologyMap f hdM hdN hf)) :
    TauCeti.LinearMap.IsHomogeneous
      (ofHomologyMapBijective GM hdM_hom hdM GN hdN_hom hdN hf hbij).inv
      GN.piece GM.piece 0 := by
  have heH : TauCeti.LinearMap.IsHomogeneous
      (LinearEquiv.ofBijective (_root_.LinearMap.homologyMap f hdM hdN hf) hbij).toLinearMap
      (GM.homology hdM_hom hdM).piece (GN.homology hdN_hom hdN).piece 0 :=
    GM.isHomogeneous_homologyMap hdM_hom hdM GN hdN_hom hdN hf_hom hf
  simpa only [ofHomologyMapBijective, add_zero] using
    (GM.isHomogeneous_homologyContraction_incl hdM_hom hdM).comp
      (heH.linearEquiv_symm.comp (GN.isHomogeneous_homologyContraction_proj hdN_hom hdN))

/-- When `f` is homogeneous of degree zero, the source homotopy constructed by
`ofHomologyMapBijective` has degree `-1`. -/
theorem isHomogeneous_ofHomologyMapBijective_homotopyHom
    (GM : InternalGrading K M ℤ) {dM : Module.End K M}
    (hdM_hom : TauCeti.LinearMap.IsHomogeneous dM GM.piece GM.piece 1) (hdM : dM ∘ₗ dM = 0)
    (GN : InternalGrading K N ℤ) {dN : Module.End K N}
    (hdN_hom : TauCeti.LinearMap.IsHomogeneous dN GN.piece GN.piece 1) (hdN : dN ∘ₗ dN = 0)
    {f : M →ₗ[K] N} (hf_hom : TauCeti.LinearMap.IsHomogeneous f GM.piece GN.piece 0)
    (hf : f ∘ₗ dM = dN ∘ₗ f)
    (hbij : Function.Bijective (_root_.LinearMap.homologyMap f hdM hdN hf)) :
    TauCeti.LinearMap.IsHomogeneous
      (ofHomologyMapBijective GM hdM_hom hdM GN hdN_hom hdN hf hbij).homotopyHom
      GM.piece GM.piece (-1) := by
  have hg := isHomogeneous_ofHomologyMapBijective_inv GM hdM_hom hdM GN hdN_hom hdN hf_hom hf hbij
  have hψ : TauCeti.LinearMap.IsHomogeneous
      (LinearMap.id - (ofHomologyMapBijective GM hdM_hom hdM GN hdN_hom hdN hf hbij).inv ∘ₗ f)
      GM.piece GM.piece 0 :=
    (TauCeti.LinearMap.isHomogeneous_id GM.piece).sub
      (by simpa only [add_zero] using hg.comp hf_hom)
  -- Unfold `homotopyHom` to `(1 - inv ∘ f) ∘ cM.homotopy` without expanding `inv`.
  change TauCeti.LinearMap.IsHomogeneous
    ((LinearMap.id - (ofHomologyMapBijective GM hdM_hom hdM GN hdN_hom hdN hf hbij).inv ∘ₗ f) ∘ₗ
      (GM.homologyContraction hdM_hom hdM).homotopy) GM.piece GM.piece (-1)
  simpa only [add_zero] using
    hψ.comp (GM.isHomogeneous_homologyContraction_homotopy hdM_hom hdM)

/-- When `f` is homogeneous of degree zero, the target homotopy constructed by
`ofHomologyMapBijective` has degree `-1`. -/
theorem isHomogeneous_ofHomologyMapBijective_homotopyInv
    (GM : InternalGrading K M ℤ) {dM : Module.End K M}
    (hdM_hom : TauCeti.LinearMap.IsHomogeneous dM GM.piece GM.piece 1) (hdM : dM ∘ₗ dM = 0)
    (GN : InternalGrading K N ℤ) {dN : Module.End K N}
    (hdN_hom : TauCeti.LinearMap.IsHomogeneous dN GN.piece GN.piece 1) (hdN : dN ∘ₗ dN = 0)
    {f : M →ₗ[K] N} (hf_hom : TauCeti.LinearMap.IsHomogeneous f GM.piece GN.piece 0)
    (hf : f ∘ₗ dM = dN ∘ₗ f)
    (hbij : Function.Bijective (_root_.LinearMap.homologyMap f hdM hdN hf)) :
    TauCeti.LinearMap.IsHomogeneous
      (ofHomologyMapBijective GM hdM_hom hdM GN hdN_hom hdN hf hbij).homotopyInv
      GN.piece GN.piece (-1) := by
  let eH := LinearEquiv.ofBijective (_root_.LinearMap.homologyMap f hdM hdN hf) hbij
  have heH : TauCeti.LinearMap.IsHomogeneous eH.toLinearMap
      (GM.homology hdM_hom hdM).piece (GN.homology hdN_hom hdN).piece 0 :=
    GM.isHomogeneous_homologyMap hdM_hom hdM GN hdN_hom hdN hf_hom hf
  have hδ : TauCeti.LinearMap.IsHomogeneous
      (f ∘ₗ (GM.homologyContraction hdM_hom hdM).incl -
        (GN.homologyContraction hdN_hom hdN).incl ∘ₗ eH.toLinearMap)
      (GM.homology hdM_hom hdM).piece GN.piece 0 :=
    TauCeti.LinearMap.IsHomogeneous.sub
      (by simpa only [add_zero] using
        hf_hom.comp (GM.isHomogeneous_homologyContraction_incl hdM_hom hdM))
      (by simpa only [add_zero] using
        (GN.isHomogeneous_homologyContraction_incl hdN_hom hdN).comp heH)
  have hk : TauCeti.LinearMap.IsHomogeneous
      ((GN.homologyContraction hdN_hom hdN).homotopy ∘ₗ
        (f ∘ₗ (GM.homologyContraction hdM_hom hdM).incl -
          (GN.homologyContraction hdN_hom hdN).incl ∘ₗ eH.toLinearMap) ∘ₗ
        eH.symm.toLinearMap ∘ₗ (GN.homologyContraction hdN_hom hdN).proj)
      GN.piece GN.piece (-1) := by
    simpa only [zero_add, add_zero] using
      (GN.isHomogeneous_homologyContraction_homotopy hdN_hom hdN).comp
        (hδ.comp (heH.linearEquiv_symm.comp
          (GN.isHomogeneous_homologyContraction_proj hdN_hom hdN)))
  exact (GN.isHomogeneous_homologyContraction_homotopy hdN_hom hdN).sub hk

end DivisionRing

end TauCeti.LinearHomotopyEquiv
