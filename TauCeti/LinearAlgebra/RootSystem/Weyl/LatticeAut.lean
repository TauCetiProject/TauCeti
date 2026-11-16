/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.CoweightLattice
public import TauCeti.LinearAlgebra.RootSystem.Weyl.BasedAut

/-!
# Automorphisms of a root pairing preserving a pair of lattices

Let `P` be a root pairing with weight space `M` and coweight space `N`, for instance a rational
root system. This file studies additive subgroups `X₀ ⊆ M` and `Y₀ ⊆ N` containing the roots
and the coroots and on which the pairing takes integer values. For an integral form of a finite
semisimple rational root system, these must additionally be full lattices in perfect ℤ-duality:
`Y₀ = P.dualLattice X₀`. In that setting the choices of `X₀` between the root lattice and the
weight lattice classify the isogeny forms of the root system.

An automorphism `g` of `P` acts on weights by `g.weightEquiv` and on coweights by the inverse
transpose `g.coweightEquiv.symm`, which is the weight action of `RootPairing.Equiv.autFlip P g`.
The automorphisms preserving both lattices for these forward actions form the subgroup
`P.latticeAut X₀ Y₀`. This file proves:

* when the lattices contain the roots and the coroots and pair integrally, the Weyl group lies in
  `P.latticeAut X₀ Y₀`. For a finite reduced crystallographic root pairing over a
  characteristic-zero domain, the decomposition of an automorphism as a Weyl-group element times a
  based automorphism (`RootPairing.Base.isComplement'_weylGroup_basedAut`) restricts to the
  lattice-preserving automorphisms: inside `P.latticeAut X₀ Y₀`, the Weyl group complements the
  lattice-preserving automorphisms fixing a base;
* for the dual lattice `Y₀ = P.dualLattice X₀`, the coweights pairing integrally with `X₀`, an
  automorphism preserves both lattices as soon as it preserves `X₀`;
* for the two extreme forms, the adjoint one (the root lattice and its dual, the coweight
  lattice) and the simply connected one (the weight lattice and the coroot lattice), every
  automorphism preserves the lattices.

For an intermediate isogeny form the subgroup can be proper: for type `D₄`, a diagram
automorphism permutes the three nonzero classes of the weight lattice modulo the root lattice,
so the lattice between them through one class is preserved only by the diagram automorphisms
fixing that class.

## Main definitions

* `RootPairing.latticeAut`: the automorphisms preserving a lattice of weights and a lattice of
  coweights.

## Main results

* `RootPairing.mem_latticeAut_iff`: an automorphism preserves the lattices exactly when its
  forward weight and coweight maps carry them onto themselves.
* `RootPairing.mem_latticeAut_dualLattice_iff` and
  `RootPairing.mem_latticeAut_flip_dualLattice_iff`: for a lattice and its dual, preserving one of
  the two lattices suffices.
* `RootPairing.autFlip_mem_latticeAut_iff`: `RootPairing.Equiv.autFlip` identifies the
  lattice-preserving automorphisms of `P` and of `P.flip`.
* `RootPairing.reflection_mem_latticeAut` and `RootPairing.weylGroup_le_latticeAut`: the
  reflections, hence the Weyl group, preserve lattices containing the roots and the coroots and
  pairing integrally.
* `RootPairing.latticeAut_rootSpan_coweightLattice` and
  `RootPairing.latticeAut_coweightLattice_flip_corootSpan`: every automorphism preserves the
  adjoint and the simply connected lattices.
* `RootPairing.Base.isComplement'_weylGroup_basedAut_latticeAut`: inside the lattice-preserving
  automorphisms, the Weyl group complements the based ones, for a finite reduced root pairing over
  a characteristic-zero domain. It specializes
  `RootPairing.Base.isComplement'_weylGroup_subgroupOf_basedAut_subgroupOf`.

## References

* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §6.7 and
  §7.4.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.5 and §1.9, and
  Plate IV.
-/

public section

open Pointwise Set

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N}

/-! ### Lattice-preserving automorphisms -/

variable (P) in
/-- The **lattice-preserving automorphisms** of a root pairing, for an additive subgroup `X₀` of
the weight space and an additive subgroup `Y₀` of the coweight space: the automorphisms `g` whose
weight map carries `X₀` onto itself and whose forward coweight map `g.coweightEquiv.symm` (the
weight map of `RootPairing.Equiv.autFlip P g`) carries `Y₀` onto itself. -/
noncomputable def latticeAut (X₀ : Submodule ℤ M) (Y₀ : Submodule ℤ N) : Subgroup P.Aut :=
  MulAction.stabilizer P.Aut X₀ ⊓
    (MulAction.stabilizer P.flip.Aut Y₀).comap (Equiv.autFlip P).toMonoidHom

variable (P) in
/-- `RootPairing.latticeAut` is the intersection of the stabilizer of `X₀` with the preimage
under `RootPairing.Equiv.autFlip` of the stabilizer of `Y₀`. -/
theorem latticeAut_def (X₀ : Submodule ℤ M) (Y₀ : Submodule ℤ N) :
    P.latticeAut X₀ Y₀ = MulAction.stabilizer P.Aut X₀ ⊓
      (MulAction.stabilizer P.flip.Aut Y₀).comap (Equiv.autFlip P).toMonoidHom :=
  (rfl)

variable {X₀ : Submodule ℤ M} {Y₀ : Submodule ℤ N} {g : P.Aut}

/-- Membership in `RootPairing.latticeAut` through the two pointwise actions on lattices. -/
theorem mem_latticeAut_iff_smul :
    g ∈ P.latticeAut X₀ Y₀ ↔ g • X₀ = X₀ ∧ Equiv.autFlip P g • Y₀ = Y₀ :=
  Iff.rfl

/-- **An automorphism preserves the lattices exactly when its forward weight and coweight maps
carry them onto themselves.** -/
theorem mem_latticeAut_iff :
    g ∈ P.latticeAut X₀ Y₀ ↔
      g.weightEquiv '' X₀ = X₀ ∧ g.coweightEquiv.symm '' Y₀ = Y₀ := by
  simp only [mem_latticeAut_iff_smul, ← SetLike.coe_set_eq, Submodule.coe_pointwise_smul,
    ← image_smul, Equiv.smul_eq_weightEquiv, Equiv.weightEquiv_autFlip]

/-- **For a lattice and its dual, an automorphism preserves both as soon as it preserves the
lattice of weights.** -/
@[simp]
theorem mem_latticeAut_dualLattice_iff :
    g ∈ P.latticeAut X₀ (P.dualLattice X₀) ↔ g • X₀ = X₀ :=
  mem_latticeAut_iff_smul.trans ⟨And.left, fun h ↦ ⟨h, by rw [autFlip_smul_dualLattice, h]⟩⟩

/-- `RootPairing.Equiv.autFlip` carries the automorphisms preserving `X₀` and `Y₀` onto the
automorphisms of the flipped pairing preserving `Y₀` and `X₀`. -/
@[simp]
theorem autFlip_mem_latticeAut_iff :
    Equiv.autFlip P g ∈ P.flip.latticeAut Y₀ X₀ ↔ g ∈ P.latticeAut X₀ Y₀ := by
  have key : Equiv.autFlip P.flip (Equiv.autFlip P g) = g :=
    (Equiv.autFlip_apply _).trans
      ((Equiv.autFlip_symm_apply _).symm.trans ((Equiv.autFlip P).symm_apply_apply g))
  -- `key` lives in the automorphisms of `P.flip.flip`, which is `P` by definition.
  rw [mem_latticeAut_iff_smul, mem_latticeAut_iff_smul, and_comm, key]
  exact Iff.rfl

/-- **For a lattice of coweights and its dual, an automorphism preserves both as soon as it
preserves the lattice of coweights.** -/
@[simp]
theorem mem_latticeAut_flip_dualLattice_iff :
    g ∈ P.latticeAut (P.flip.dualLattice Y₀) Y₀ ↔ Equiv.autFlip P g • Y₀ = Y₀ := by
  rw [← autFlip_mem_latticeAut_iff, mem_latticeAut_dualLattice_iff]

/-- A lattice-preserving automorphism preserves the lattice of weights. -/
theorem smul_eq_of_mem_latticeAut (hg : g ∈ P.latticeAut X₀ Y₀) : g • X₀ = X₀ :=
  hg.1

/-- A lattice-preserving automorphism preserves the lattice of coweights. -/
theorem autFlip_smul_eq_of_mem_latticeAut (hg : g ∈ P.latticeAut X₀ Y₀) :
    Equiv.autFlip P g • Y₀ = Y₀ :=
  hg.2

/-- A lattice-preserving automorphism moves a weight into the lattice of weights exactly when
the weight lies there. -/
theorem smul_mem_iff_of_mem_latticeAut (hg : g ∈ P.latticeAut X₀ Y₀) {x : M} :
    g • x ∈ X₀ ↔ x ∈ X₀ := by
  conv_lhs => rw [← hg.1]
  rw [← SetLike.mem_coe, Submodule.coe_pointwise_smul, smul_mem_smul_set_iff, SetLike.mem_coe]

/-- A lattice-preserving automorphism moves a coweight into the lattice of coweights exactly
when the coweight lies there. -/
theorem autFlip_smul_mem_iff_of_mem_latticeAut (hg : g ∈ P.latticeAut X₀ Y₀) {y : N} :
    Equiv.autFlip P g • y ∈ Y₀ ↔ y ∈ Y₀ :=
  smul_mem_iff_of_mem_latticeAut (P := P.flip) (autFlip_mem_latticeAut_iff.mpr hg)

/-- The coweight map of a lattice-preserving automorphism moves a coweight into the lattice of
coweights exactly when the coweight lies there. -/
theorem coweightEquiv_mem_iff_of_mem_latticeAut (hg : g ∈ P.latticeAut X₀ Y₀) {y : N} :
    g.coweightEquiv y ∈ Y₀ ↔ y ∈ Y₀ := by
  rw [← autFlip_smul_mem_iff_of_mem_latticeAut hg, Equiv.smul_eq_weightEquiv,
    Equiv.weightEquiv_autFlip, LinearEquiv.symm_apply_apply]

/-- The reflection in a root `αᵢ` preserves lattices containing `αᵢ` and `αᵢ^∨` and pairing
integrally. On coweights it is the reflection of the flipped pairing in `αᵢ^∨`
(`RootPairing.Equiv.autFlip_reflection`). -/
theorem reflection_mem_latticeAut {i : ι} (hroot : P.root i ∈ X₀) (hcoroot : P.coroot i ∈ Y₀)
    (hXY : Y₀ ≤ P.dualLattice X₀) : Equiv.reflection P i ∈ P.latticeAut X₀ Y₀ := by
  refine mem_latticeAut_iff_smul.mpr ⟨reflection_smul_eq_of_mem_dualLattice hroot (hXY hcoroot), ?_⟩
  rw [Equiv.autFlip_reflection]
  exact reflection_smul_eq_of_mem_dualLattice (P := P.flip) hcoroot
    (le_flip_dualLattice_iff.mpr hXY hroot)

/-- **The Weyl group preserves lattices containing the roots and the coroots and pairing
integrally.** -/
theorem weylGroup_le_latticeAut (hroot : ∀ i, P.root i ∈ X₀) (hcoroot : ∀ i, P.coroot i ∈ Y₀)
    (hXY : Y₀ ≤ P.dualLattice X₀) : P.weylGroup ≤ P.latticeAut X₀ Y₀ :=
  (Subgroup.closure_le _).mpr <| range_subset_iff.mpr fun i ↦
    reflection_mem_latticeAut (hroot i) (hcoroot i) hXY

/-- The Weyl group preserves a lattice containing the roots and lying in the weight lattice,
together with its dual. -/
theorem weylGroup_le_latticeAut_dualLattice (hroot : ∀ i, P.root i ∈ X₀)
    (hX : X₀ ≤ P.flip.coweightLattice) : P.weylGroup ≤ P.latticeAut X₀ (P.dualLattice X₀) :=
  weylGroup_le_latticeAut hroot
    (fun i ↦ mem_dualLattice.mpr fun _ hx ↦ P.flip.mem_coweightLattice.mp (hX hx) i) le_rfl

variable (P) in
/-- **Every automorphism preserves the adjoint lattices**: the root lattice and its dual, the
coweight lattice. -/
@[simp]
theorem latticeAut_rootSpan_coweightLattice :
    P.latticeAut (P.rootSpan ℤ) P.coweightLattice = ⊤ := by
  rw [← dualLattice_rootSpan, eq_top_iff]
  exact fun g _ ↦ mem_latticeAut_dualLattice_iff.mpr (Equiv.smul_rootSpan g)

variable (P) in
/-- **Every automorphism preserves the simply connected lattices**: the weight lattice and the
coroot lattice. -/
@[simp]
theorem latticeAut_coweightLattice_flip_corootSpan :
    P.latticeAut P.flip.coweightLattice (P.corootSpan ℤ) = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ ⟨g.smul_coweightLattice_flip, Equiv.smul_corootSpan _⟩

/-! ### The restricted decomposition -/

namespace Base

variable [Finite ι] [CharZero R] [IsDomain R] [P.IsReduced]

/-- **The Weyl group complements the based lattice-preserving automorphisms** among the
lattice-preserving automorphisms, for lattices containing the roots and the coroots and pairing
integrally. Such lattices force the pairing to be crystallographic
(`RootPairing.isCrystallographic_of_le_dualLattice`). -/
theorem isComplement'_weylGroup_basedAut_latticeAut (b : P.Base) (hroot : ∀ i, P.root i ∈ X₀)
    (hcoroot : ∀ i, P.coroot i ∈ Y₀) (hXY : Y₀ ≤ P.dualLattice X₀) :
    (P.weylGroup.subgroupOf (P.latticeAut X₀ Y₀)).IsComplement'
      (b.basedAut.subgroupOf (P.latticeAut X₀ Y₀)) :=
  have := isCrystallographic_of_le_dualLattice hroot hcoroot hXY
  b.isComplement'_weylGroup_subgroupOf_basedAut_subgroupOf
    (weylGroup_le_latticeAut hroot hcoroot hXY)

end Base

end RootPairing
