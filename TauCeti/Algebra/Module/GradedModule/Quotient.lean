/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# Gradings of homogeneous submodules and of their quotients

Let `G` be an internal indexed grading of an `R`-module `M`, and let `U` be a submodule which is
homogeneous in Mathlib's sense `SetLike.IsHomogeneous`: it contains every homogeneous component
of each of its elements.  Then `U` and `M ⧸ U` inherit internal gradings.

* On `U`, the degree-`p` piece is the part of `U` lying in `G.piece p`.
* On `M ⧸ U`, the degree-`p` piece is the image of `G.piece p` under the quotient map.  The
  images span because the quotient map is surjective, and they are independent because an
  element of `U` is the sum of its homogeneous components, all of which lie in `U`.

In both cases the homogeneous projections are those of `M`, transported along the inclusion and
the quotient map respectively.  Combining the two gives the grading of a subquotient, such as the
cohomology `ker d ⧸ im d` of a differential of degree one.

The submodule may be over a larger semiring `S` than the semiring `R` of the grading; it and,
for rings, the quotient by it then inherit gradings by `R`-submodules through scalar restriction.

The kernel of a homogeneous linear map is homogeneous
(`TauCeti.LinearMap.IsHomogeneous.isHomogeneous_ker`), so it inherits a grading in the same way.
The map may be linear over a larger ring `S` than the ring `R` of the grading, as for a
differential over a polynomial ring whose variables move the degree; the kernel is then an
`S`-module graded by `R`-submodules.

## Main definitions

* `TauCeti.InternalGrading.submodule`: the grading of a homogeneous submodule.
* `TauCeti.InternalGrading.ker`: the grading of the kernel of a homogeneous linear map.
* `TauCeti.InternalGrading.quotient`: the grading of the quotient by a homogeneous submodule.

## Main results

* `TauCeti.InternalGrading.coe_decompose_submodule`: homogeneous projection in a homogeneous
  submodule is homogeneous projection in the ambient module.
* `TauCeti.InternalGrading.mem_ker_piece`: an element of the kernel of a homogeneous map is
  homogeneous exactly when it is homogeneous in the source.
* `TauCeti.InternalGrading.decompose_quotient_mk`: homogeneous projection commutes with the
  quotient map.
* `TauCeti.InternalGrading.isHomogeneous_rangeRestrict`: the corestriction of a homogeneous map
  to its image keeps its degree.
* `TauCeti.InternalGrading.isHomogeneous_mkQ`: the quotient map has degree zero.
-/

public section

open DirectSum

/-- The images of the homogeneous pieces under quotienting by a homogeneous submodule form an
internal direct sum. The submodule can be over a larger ring than the grading. -/
theorem DirectSum.IsInternal.map_mkQ {R S M ι : Type*} [Ring R] [Ring S] [SMul R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [DecidableEq ι]
    {ℳ : ι → Submodule R M} [DirectSum.Decomposition ℳ]
    (U : Submodule S M) (hU : SetLike.IsHomogeneous ℳ U) :
    DirectSum.IsInternal (fun i => (ℳ i).map (U.mkQ.restrictScalars R)) := by
  have hℳ := DirectSum.Decomposition.isInternal ℳ
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (hℳ.submodule_iSupIndep.map_of_ker_inf_iSup_le (U.mkQ.restrictScalars R) ?_) ?_
  · rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
    intro x hx
    classical
    rw [← DirectSum.sum_support_decompose ℳ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i
      ⟨hU i hx.1, (DirectSum.decompose ℳ x i).property⟩
  · rw [← Submodule.map_iSup, hℳ.submodule_iSup_eq_top, Submodule.map_top,
      LinearMap.range_restrictScalars, Submodule.range_mkQ, Submodule.restrictScalars_top]

namespace DirectSum.Decomposition

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
  {ℳ : ι → Submodule R M} (U : Submodule R M)

private def mkQComponents : (⨁ i, ℳ i) →ₗ[R] (⨁ i, (ℳ i).map U.mkQ) :=
  DirectSum.lmap fun i =>
    (U.mkQ.domRestrict (ℳ i)).codRestrict ((ℳ i).map U.mkQ) fun x => ⟨x, x.property, rfl⟩

variable [DecidableEq ι] [DirectSum.Decomposition ℳ]

private def decomposeAndMap : M →ₗ[R] (⨁ i, (ℳ i).map U.mkQ) :=
  (mkQComponents U).comp (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

private theorem le_ker_decomposeAndMap (hU : SetLike.IsHomogeneous ℳ U) :
    U ≤ LinearMap.ker (decomposeAndMap (ℳ := ℳ) U) := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply DFinsupp.ext
  intro i
  apply Subtype.ext
  change U.mkQ (DirectSum.decompose ℳ x i : M) = 0
  exact (Submodule.Quotient.mk_eq_zero U).mpr (hU i hx)

private def quotientDecompose (hU : SetLike.IsHomogeneous ℳ U) :
    M ⧸ U → (⨁ i, (ℳ i).map U.mkQ) :=
  QuotientAddGroup.lift U.toAddSubgroup (decomposeAndMap (ℳ := ℳ) U).toAddMonoidHom
    (fun _ hx => le_ker_decomposeAndMap U hU hx)

private theorem sum_quotientDecompose (hU : SetLike.IsHomogeneous ℳ U) :
    Function.LeftInverse (DirectSum.coeAddMonoidHom fun i => (ℳ i).map U.mkQ)
      (quotientDecompose U hU) := by
  have hsum : (DirectSum.coeLinearMap fun i => (ℳ i).map U.mkQ).comp (mkQComponents (ℳ := ℳ) U) =
      U.mkQ.comp (DirectSum.coeLinearMap ℳ) := by
    apply DirectSum.linearMap_ext R
    intro i
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, mkQComponents, DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
    rfl
  intro x
  obtain ⟨x, rfl⟩ := U.mkQ_surjective x
  change ((DirectSum.coeLinearMap _).comp (mkQComponents (ℳ := ℳ) U))
    (DirectSum.decomposeLinearEquiv ℳ x) = U.mkQ x
  rw [hsum]
  exact congrArg U.mkQ (DirectSum.Decomposition.left_inv x)

/-- Decompose a class modulo a homogeneous submodule by decomposing a representative and
mapping each component to its class. Homogeneity makes this independent of the representative. -/
@[instance_reducible]
def map_mkQ (hU : SetLike.IsHomogeneous ℳ U) :
    DirectSum.Decomposition (fun i => (ℳ i).map U.mkQ) where
  decompose' := quotientDecompose U hU
  left_inv := sum_quotientDecompose U hU
  right_inv := by
    have hinternal : DirectSum.IsInternal (fun i => (ℳ i).map U.mkQ) := by
      simpa only [LinearMap.restrictScalars_self] using DirectSum.IsInternal.map_mkQ U hU
    intro x
    exact hinternal.injective (sum_quotientDecompose U hU (DirectSum.coeAddMonoidHom _ x))

/-- On a representative, the quotient decomposition projects each homogeneous component. -/
theorem map_mkQ_decompose'_mk (hU : SetLike.IsHomogeneous ℳ U) (x : M) (i : ι) :
    ((map_mkQ U hU).decompose' (Submodule.Quotient.mk x) i : M ⧸ U) =
      Submodule.Quotient.mk (DirectSum.decompose ℳ x i : M) := (rfl)

end DirectSum.Decomposition

namespace TauCeti.InternalGrading

variable {R M : Type*} {ι : Type} [DecidableEq ι]

section Span

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- A submodule spanned by homogeneous elements is homogeneous. -/
theorem isHomogeneous_span (G : InternalGrading R M ι) (s : Set M)
    (hs : ∀ x ∈ s, ∃ p, x ∈ G.piece p) :
    SetLike.IsHomogeneous G.piece (Submodule.span R s) := by
  classical
  intro q x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp⟩ := hs x hx
    by_cases hpq : p = q
    · subst q
      rw [decompose_of_mem_same G.piece hp]
      exact Submodule.subset_span hx
    · rw [decompose_of_mem_ne G.piece hp hpq]
      exact Submodule.zero_mem _
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa using Submodule.add_mem _ ihx ihy
  | smul r x hx ih =>
    simpa only [decompose_smul, DirectSum.smul_apply, SetLike.val_smul] using
      Submodule.smul_mem _ r ih

end Span

section Submodule

variable {S : Type*} [Semiring R] [Semiring S] [SMul R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  (G : InternalGrading R M ι) (U : Submodule S M) (hU : SetLike.IsHomogeneous G.piece U)

include hU in
/-- The internal grading of a homogeneous `S`-submodule: its degree-`p` piece consists of the
elements lying in the degree-`p` piece of the ambient `R`-grading. -/
noncomputable def submodule : InternalGrading R U ι where
  piece p := (G.piece p).comap (U.subtype.restrictScalars R)
  isInternal := DirectSum.isInternal_comap G.piece _ (U.subtype.restrictScalars R)
    Subtype.val_injective
    (fun _ _ ↦ Iff.rfl) fun p x ↦ ⟨⟨_, hU p x.2⟩, rfl⟩

@[simp]
theorem submodule_piece (p : ι) :
    (G.submodule U hU).piece p = (G.piece p).comap (U.subtype.restrictScalars R) :=
  (rfl)

theorem mem_submodule_piece {p : ι} {x : U} :
    x ∈ (G.submodule U hU).piece p ↔ (x : M) ∈ G.piece p :=
  Iff.rfl

/-- Homogeneous projection in a homogeneous submodule is homogeneous projection in the ambient
module. -/
@[simp]
theorem coe_decompose_submodule (p : ι) (x : U) :
    ((decompose (G.submodule U hU).piece x p : U) : M) = decompose G.piece (x : M) p :=
  DirectSum.map_decompose_restrict G.piece (G.submodule U hU).piece (U.subtype.restrictScalars R)
    (fun _ _ ↦ Iff.rfl) p x

/-- The inclusion of a homogeneous submodule has degree zero. -/
theorem isHomogeneous_subtype [AddMonoid ι] :
    LinearMap.IsHomogeneous U.subtype (G.submodule U hU).piece G.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by simpa using hx

/-- The corestriction of a homogeneous linear map to its image has the same degree, for the
grading of the image by its homogeneous elements. -/
theorem isHomogeneous_rangeRestrict [AddMonoid ι] {N : Type*} [AddCommMonoid N] [Module R N]
    [Module S N] {H : InternalGrading R N ι} {f : N →ₗ[S] M} {r : ι}
    (hf : LinearMap.IsHomogeneous f H.piece G.piece r) :
    LinearMap.IsHomogeneous f.rangeRestrict H.piece
      (G.submodule (_root_.LinearMap.range f) hf.isHomogeneous_range).piece r :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ hf.map_mem hx

end Submodule

section Ker

variable [AddRightCancelMonoid ι]

variable {S N : Type*} [Semiring R] [Semiring S] [SMul R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommMonoid N] [Module R N] [Module S N]
  (G : InternalGrading R M ι) {H : InternalGrading R N ι} {f : M →ₗ[S] N} {r : ι}
  (hf : LinearMap.IsHomogeneous f G.piece H.piece r)

include hf in
/-- The internal grading of the kernel of a homogeneous linear map: its degree-`p` piece consists
of the elements of the kernel lying in the degree-`p` piece of `M`. -/
noncomputable def ker : InternalGrading R (_root_.LinearMap.ker f) ι :=
  G.submodule (_root_.LinearMap.ker f) hf.isHomogeneous_ker

/-- An element of the kernel of `f` is homogeneous of degree `p` exactly when it is homogeneous of
degree `p` in `M`. -/
@[simp]
theorem mem_ker_piece {p : ι} {z : _root_.LinearMap.ker f} :
    z ∈ (G.ker hf).piece p ↔ (z : M) ∈ G.piece p :=
  G.mem_submodule_piece (_root_.LinearMap.ker f) hf.isHomogeneous_ker

/-- Homogeneous projection in the kernel of `f` is homogeneous projection in `M`. -/
@[simp]
theorem coe_decompose_ker (p : ι) (z : _root_.LinearMap.ker f) :
    ((decompose (G.ker hf).piece z p : _root_.LinearMap.ker f) : M) =
      decompose G.piece (z : M) p :=
  G.coe_decompose_submodule (_root_.LinearMap.ker f) hf.isHomogeneous_ker p z

end Ker

section Quotient

variable {S : Type*} [Ring R] [Ring S] [SMul R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (G : InternalGrading R M ι) (U : Submodule S M) (hU : SetLike.IsHomogeneous G.piece U)

include hU in
/-- The internal grading of the quotient by a homogeneous `S`-submodule: its degree-`p` piece is
the image of the degree-`p` piece of `M`. -/
noncomputable def quotient : InternalGrading R (M ⧸ U) ι where
  piece p := (G.piece p).map (U.mkQ.restrictScalars R)
  isInternal := DirectSum.IsInternal.map_mkQ U hU

@[simp]
theorem quotient_piece (p : ι) :
    (G.quotient U hU).piece p = (G.piece p).map (U.mkQ.restrictScalars R) :=
  (rfl)

/-- An element of the quotient has degree `p` exactly when it is the class of an element of
degree `p`. -/
theorem mem_quotient_piece_iff {p : ι} {y : M ⧸ U} :
    y ∈ (G.quotient U hU).piece p ↔ ∃ x ∈ G.piece p, Submodule.Quotient.mk x = y := by
  simp only [quotient_piece, Submodule.mem_map, LinearMap.restrictScalars_apply,
    Submodule.mkQ_apply]

/-- The class of an element of degree `p` has degree `p`. -/
theorem mk_mem_quotient_piece {p : ι} {x : M} (hx : x ∈ G.piece p) :
    (Submodule.Quotient.mk x : M ⧸ U) ∈ (G.quotient U hU).piece p :=
  (G.mem_quotient_piece_iff U hU).2 ⟨x, hx, rfl⟩

/-- The quotient map by a homogeneous submodule has degree zero. -/
theorem isHomogeneous_mkQ [AddMonoid ι] :
    LinearMap.IsHomogeneous U.mkQ G.piece (G.quotient U hU).piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa using G.mk_mem_quotient_piece U hU hx

/-- Homogeneous projection commutes with the quotient map. -/
@[simp]
theorem decompose_quotient_mk (p : ι) (x : M) :
    (decompose (G.quotient U hU).piece (Submodule.Quotient.mk x : M ⧸ U) p : M ⧸ U) =
      Submodule.Quotient.mk (decompose G.piece x p : M) :=
  (DirectSum.map_decompose_shift G.piece (G.quotient U hU).piece U.mkQ.toAddMonoidHom
    id Function.injective_id (fun _ _ hx ↦ G.mk_mem_quotient_piece U hU hx) p x).symm

end Quotient

end TauCeti.InternalGrading
