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

Let `G` be an internal integer grading of an `R`-module `M`, and let `U` be a submodule which is
homogeneous in Mathlib's sense `SetLike.IsHomogeneous`: it contains every homogeneous component
of each of its elements.  Then `U` and `M ⧸ U` inherit internal gradings.

* On `U`, the degree-`p` piece is the part of `U` lying in `G.piece p`.
* On `M ⧸ U`, the degree-`p` piece is the image of `G.piece p` under the quotient map.  The
  images span because the quotient map is surjective, and they are independent because an
  element of `U` is the sum of its homogeneous components, all of which lie in `U`.

In both cases the homogeneous projections are those of `M`, transported along the inclusion and
the quotient map respectively.  Combining the two gives the grading of a subquotient, such as the
cohomology `ker d ⧸ im d` of a differential of degree one.

The kernel and the image of a homogeneous linear map are homogeneous, because such a map carries
the degree-`p` component of an element to the component of its image in the shifted degree. This
is how the cycles and boundaries of a homogeneous differential become homogeneous submodules. The
map may be linear over a larger ring `S` than the ring `R` of the grading, as for a differential
over a polynomial ring whose variables move the degree.

## Main definitions

* `TauCeti.InternalGrading.submodule`: the grading of a homogeneous submodule.
* `TauCeti.InternalGrading.quotient`: the grading of the quotient by a homogeneous submodule.

## Main results

* `TauCeti.InternalGrading.coe_decompose_submodule`: homogeneous projection in a homogeneous
  submodule is homogeneous projection in the ambient module.
* `TauCeti.InternalGrading.decompose_quotient_mk`: homogeneous projection commutes with the
  quotient map.
* `TauCeti.InternalGrading.isHomogeneous_mkQ`: the quotient map has degree zero.
* `TauCeti.LinearMap.IsHomogeneous.map_decompose`: a homogeneous map commutes with homogeneous
  projection, up to the shift of degree.
* `TauCeti.LinearMap.IsHomogeneous.isHomogeneous_ker` and
  `TauCeti.LinearMap.IsHomogeneous.isHomogeneous_range`: the kernel and the image of a homogeneous
  map are homogeneous submodules.
-/

public section

open DirectSum

namespace TauCeti.InternalGrading

variable {R M : Type*}

section Submodule

variable [Semiring R] [AddCommMonoid M] [Module R M] (G : InternalGrading R M)
  (U : Submodule R M) (hU : SetLike.IsHomogeneous G.piece U)

include hU in
/-- The internal grading of a homogeneous submodule: its degree-`p` piece consists of the
elements lying in the degree-`p` piece of the ambient grading. -/
noncomputable def submodule : InternalGrading R U where
  piece p := (G.piece p).comap U.subtype
  isInternal := DirectSum.isInternal_comap G.piece _ U.subtype Subtype.val_injective
    (fun _ _ ↦ Iff.rfl) fun p x ↦ ⟨⟨_, hU p x.2⟩, rfl⟩

@[simp]
theorem submodule_piece (p : ℤ) : (G.submodule U hU).piece p = (G.piece p).comap U.subtype :=
  (rfl)

theorem mem_submodule_piece {p : ℤ} {x : U} :
    x ∈ (G.submodule U hU).piece p ↔ (x : M) ∈ G.piece p :=
  Iff.rfl

/-- Homogeneous projection in a homogeneous submodule is homogeneous projection in the ambient
module. -/
@[simp]
theorem coe_decompose_submodule (p : ℤ) (x : U) :
    ((decompose (G.submodule U hU).piece x p : U) : M) = decompose G.piece (x : M) p :=
  DirectSum.map_decompose_restrict G.piece (G.submodule U hU).piece U.subtype
    (fun _ _ ↦ Iff.rfl) p x

/-- The inclusion of a homogeneous submodule has degree zero. -/
theorem isHomogeneous_subtype :
    LinearMap.IsHomogeneous U.subtype (G.submodule U hU).piece G.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by simpa using hx

end Submodule

section Quotient

variable [Ring R] [AddCommGroup M] [Module R M] (G : InternalGrading R M)
  (U : Submodule R M) (hU : SetLike.IsHomogeneous G.piece U)

include hU in
/-- A homogeneous submodule is the sum of its intersections with the homogeneous pieces. -/
private theorem le_iSup_inf_piece : U ≤ ⨆ p, U ⊓ G.piece p := by
  classical
  intro x hx
  rw [← DirectSum.sum_support_decompose G.piece x]
  exact Submodule.sum_mem _ fun p _ ↦
    Submodule.mem_iSup_of_mem p ⟨hU p hx, SetLike.coe_mem _⟩

include hU in
/-- The internal grading of the quotient by a homogeneous submodule: its degree-`p` piece is the
image of the degree-`p` piece of `M`. -/
noncomputable def quotient : InternalGrading R (M ⧸ U) where
  piece p := (G.piece p).map U.mkQ
  isInternal := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (iSupIndep_map_mkQ G.isInternal.submodule_iSupIndep ?_) ?_
    · exact inf_le_left.trans (le_iSup_inf_piece G U hU)
    · rw [← Submodule.map_iSup, G.isInternal.submodule_iSup_eq_top, Submodule.map_top,
        Submodule.range_mkQ]

@[simp]
theorem quotient_piece (p : ℤ) : (G.quotient U hU).piece p = (G.piece p).map U.mkQ :=
  (rfl)

/-- An element of the quotient has degree `p` exactly when it is the class of an element of
degree `p`. -/
theorem mem_quotient_piece_iff {p : ℤ} {y : M ⧸ U} :
    y ∈ (G.quotient U hU).piece p ↔ ∃ x ∈ G.piece p, Submodule.Quotient.mk x = y := by
  simp only [quotient_piece, Submodule.mem_map, Submodule.mkQ_apply]

/-- The class of an element of degree `p` has degree `p`. -/
theorem mk_mem_quotient_piece {p : ℤ} {x : M} (hx : x ∈ G.piece p) :
    (Submodule.Quotient.mk x : M ⧸ U) ∈ (G.quotient U hU).piece p :=
  (G.mem_quotient_piece_iff U hU).2 ⟨x, hx, rfl⟩

/-- The quotient map by a homogeneous submodule has degree zero. -/
theorem isHomogeneous_mkQ : LinearMap.IsHomogeneous U.mkQ G.piece (G.quotient U hU).piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa using G.mk_mem_quotient_piece U hU hx

/-- Homogeneous projection commutes with the quotient map. -/
@[simp]
theorem decompose_quotient_mk (p : ℤ) (x : M) :
    (decompose (G.quotient U hU).piece (Submodule.Quotient.mk x : M ⧸ U) p : M ⧸ U) =
      Submodule.Quotient.mk (decompose G.piece x p : M) :=
  (DirectSum.map_decompose_shift G.piece (G.quotient U hU).piece U.mkQ id Function.injective_id
    (fun _ _ hx ↦ G.mk_mem_quotient_piece U hU hx) p x).symm

end Quotient

end TauCeti.InternalGrading

namespace TauCeti.LinearMap.IsHomogeneous

variable {R S M N : Type*} [Semiring R] [Semiring S] [SMul R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
  {G : InternalGrading R M} {H : InternalGrading R N} {f : M →ₗ[S] N} {r : ℤ}

/-- A homogeneous linear map of degree `r` carries the degree-`p` component of an element to the
degree-`(p + r)` component of its image. -/
theorem map_decompose (hf : LinearMap.IsHomogeneous f G.piece H.piece r) (p : ℤ) (x : M) :
    f (decompose G.piece x p : M) = (decompose H.piece (f x) (p + r) : N) :=
  DirectSum.map_decompose_shift G.piece H.piece (f.restrictScalars R) (· + r)
    (add_left_injective r) (fun _ _ hx ↦ hf.map_mem hx) p x

/-- The kernel of a homogeneous linear map is a homogeneous submodule. -/
theorem isHomogeneous_ker (hf : LinearMap.IsHomogeneous f G.piece H.piece r) :
    SetLike.IsHomogeneous G.piece (_root_.LinearMap.ker f) := fun p x hx ↦ by
  rw [_root_.LinearMap.mem_ker] at hx ⊢
  rw [hf.map_decompose, hx, decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]

/-- The image of a homogeneous linear map is a homogeneous submodule. -/
theorem isHomogeneous_range (hf : LinearMap.IsHomogeneous f G.piece H.piece r) :
    SetLike.IsHomogeneous H.piece (_root_.LinearMap.range f) := by
  rintro q _ ⟨x, rfl⟩
  exact ⟨_, (hf.map_decompose (q - r) x).trans (by rw [sub_add_cancel])⟩

end TauCeti.LinearMap.IsHomogeneous
