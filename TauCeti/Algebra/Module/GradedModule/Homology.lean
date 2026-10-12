/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero
public import TauCeti.Algebra.Module.GradedModule.Quotient

/-!
# The grading of the homology of a homogeneous endomorphism

Let `G` be an internal integer grading of a module `M` over a ring `R`, and let `d` be a
square-zero endomorphism of `M`, linear over a ring `S` acting compatibly with `R`, which is
homogeneous of some degree `r` for `G`. Then its homology `ker d ⧸ im d` inherits an internal
grading over `R`: the kernel of `d` carries the grading `TauCeti.InternalGrading.ker`, and the
image of `d` is homogeneous (`TauCeti.LinearMap.IsHomogeneous.isHomogeneous_range`), so the
grading descends to the quotient of the kernel by the image.

The ring `S` of `d` may be larger than the ring `R` of the grading. This is the situation of a
complex over a polynomial ring whose variables move the degree: the homogeneous pieces are then
submodules over the coefficients only, while `d` and its homology are modules over the whole
polynomial ring. An element of `S` which moves every homogeneous piece of `M` by a fixed degree
moves every homogeneous piece of the homology by the same degree
(`TauCeti.InternalGrading.smul_mem_homology_piece`).

## Main definitions

* `TauCeti.InternalGrading.homology`: the grading of the homology of a homogeneous endomorphism.

## Main results

* `TauCeti.InternalGrading.mem_homology_piece_iff`: a homology class is homogeneous of degree `p`
  exactly when it is the class of a cycle of degree `p`, and
  `TauCeti.InternalGrading.homologyπ_mem_homology_piece`: the class of a homogeneous cycle is
  homogeneous of the same degree.
* `TauCeti.InternalGrading.smul_mem_homology_piece`: a scalar moving the degree of `M` by `q`
  moves the degree of the homology by `q`.
-/

public section

open DirectSum

namespace TauCeti.InternalGrading

variable {R S M : Type*} [Ring R] [Ring S] [SMul R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (G : InternalGrading R M) {r : ℤ}

variable {d : M →ₗ[S] M} (hhom : LinearMap.IsHomogeneous d G.piece G.piece r)
  (hd : d ∘ₗ d = 0)

include hhom in
/-- The image of `d` inside its kernel is homogeneous for the grading of the kernel. -/
theorem isHomogeneous_boundariesInKer :
    SetLike.IsHomogeneous (G.ker hhom).piece (d.boundariesInKer.restrictScalars R) := by
  intro p z hz
  rw [Submodule.restrictScalars_mem, LinearMap.mem_boundariesInKer, coe_decompose_ker]
  exact hhom.isHomogeneous_range p hz

/-- The internal grading of the homology `ker d ⧸ im d` of a homogeneous endomorphism: its
degree-`p` piece consists of the classes of the cycles of degree `p`. -/
noncomputable def homology : InternalGrading R (d.homology hd) :=
  ((G.ker hhom).quotient (d.boundariesInKer.restrictScalars R)
    (G.isHomogeneous_boundariesInKer hhom)).map
    (Submodule.Quotient.restrictScalarsEquiv R d.boundariesInKer)

/-- A homology class is homogeneous of degree `p` exactly when it is the class of a cycle of
degree `p`. -/
theorem mem_homology_piece_iff {p : ℤ} {y : d.homology hd} :
    y ∈ (G.homology hhom hd).piece p ↔
      ∃ z : _root_.LinearMap.ker d, (z : M) ∈ G.piece p ∧ d.homologyπ hd z = y := by
  simp only [homology, map_piece, quotient_piece, Submodule.mem_map, Submodule.mkQ_apply,
    mem_ker_piece, LinearEquiv.coe_coe, exists_exists_and_eq_and,
    Submodule.Quotient.restrictScalarsEquiv_mk, LinearMap.homologyπ_apply]

/-- The class of a cycle of degree `p` is a homology class of degree `p`. -/
theorem homologyπ_mem_homology_piece {p : ℤ} {z : _root_.LinearMap.ker d}
    (hz : (z : M) ∈ G.piece p) : d.homologyπ hd z ∈ (G.homology hhom hd).piece p :=
  (G.mem_homology_piece_iff hhom hd).mpr ⟨z, hz, rfl⟩

/-- An element of the ring of `d` which moves every homogeneous piece of `M` up by `q` moves every
homogeneous piece of the homology of `d` up by `q`. -/
theorem smul_mem_homology_piece {s : S} {q : ℤ}
    (hs : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → s • x ∈ G.piece (p + q)) {p : ℤ}
    {y : d.homology hd} (hy : y ∈ (G.homology hhom hd).piece p) :
    s • y ∈ (G.homology hhom hd).piece (p + q) := by
  obtain ⟨z, hz, rfl⟩ := (G.mem_homology_piece_iff hhom hd).mp hy
  rw [← map_smul]
  exact G.homologyπ_mem_homology_piece hhom hd (z := s • z) (hs hz)

end TauCeti.InternalGrading
