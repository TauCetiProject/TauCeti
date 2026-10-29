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
* `TauCeti.InternalGrading.isHomogeneous_mkQ`: the quotient map has degree zero.
-/

public section

open DirectSum

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
  isInternal := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (G.isInternal.submodule_iSupIndep.map_of_ker_inf_iSup_le (U.mkQ.restrictScalars R) ?_) ?_
    · -- Map the internal decomposition of `U` into the ambient module.
      have hspan := congrArg (Submodule.map (U.subtype.restrictScalars R))
        (G.submodule U hU).isInternal.submodule_iSup_eq_top
      simp only [Submodule.map_iSup, submodule_piece, Submodule.map_comap_eq,
        Submodule.map_top, LinearMap.range_restrictScalars, Submodule.range_subtype] at hspan
      simpa only [LinearMap.ker_restrictScalars, Submodule.ker_mkQ, inf_comm] using
        inf_le_left.trans_eq hspan.symm
    · rw [← Submodule.map_iSup, G.isInternal.submodule_iSup_eq_top, Submodule.map_top,
        LinearMap.range_restrictScalars, Submodule.range_mkQ, Submodule.restrictScalars_top]

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
