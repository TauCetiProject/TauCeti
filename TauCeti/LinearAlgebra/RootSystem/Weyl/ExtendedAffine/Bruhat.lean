/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.ExtendedAffine.Length
public import TauCeti.GroupTheory.Coxeter.Bruhat

/-!
# Bruhat order on extended affine Weyl groups

The Bruhat order compares `wω` and `vτ` precisely when `ω = τ` and `w ≤ v` in the affine Coxeter
system. Thus each component is a copy of the affine Bruhat order. Distinct elements of the
fundamental alcove stabilizer are incomparable. The order for every intermediate lattice is the
restriction of the extended affine order, compatibly with its own semidirect decomposition.

The partial orders are provided as data, as for `CoxeterSystem.bruhatPartialOrder`: the choice of
base determines the order.

## References

* G. Pappas and M. Rapoport, *Twisted loop groups and their affine flag varieties*, §8.
* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, §§2.1–2.2.
-/

public section

namespace RootPairing.Base

variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [Nonempty ι] [DecidableEq ι]
  [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] [Archimedean R] (b : P.Base)

/-- Bruhat order on the extended affine Weyl group: equal alcove-stabilizer factors and
Bruhat-comparable affine factors in the semidirect decomposition. -/
def ExtendedAffineBruhatLE (f g : P.extendedAffineWeylGroup) : Prop :=
  ((P.extendedAffineWeylGroupMulEquiv b).symm f).right =
      ((P.extendedAffineWeylGroupMulEquiv b).symm g).right ∧
    b.affineWeylCoxeterSystem.BruhatLE
      ((P.extendedAffineWeylGroupMulEquiv b).symm f).left
      ((P.extendedAffineWeylGroupMulEquiv b).symm g).left

/-- The affine and stabilizer components characterize extended affine Bruhat order. -/
theorem extendedAffineBruhatLE_def (f g : P.extendedAffineWeylGroup) :
    b.ExtendedAffineBruhatLE f g ↔
      ((P.extendedAffineWeylGroupMulEquiv b).symm f).right =
          ((P.extendedAffineWeylGroupMulEquiv b).symm g).right ∧
        b.affineWeylCoxeterSystem.BruhatLE
          ((P.extendedAffineWeylGroupMulEquiv b).symm f).left
          ((P.extendedAffineWeylGroupMulEquiv b).symm g).left :=
  Iff.rfl

/-- The defining comparison `wω ≤ vτ ↔ ω = τ ∧ w ≤ v`. -/
@[simp]
theorem extendedAffineBruhatLE_mulEquiv_iff
    (x y : P.affineWeylGroup ⋊[(P.affineWeylGroup.normalizerMonoidHom).comp
      (Subgroup.inclusion (fundamentalAlcoveStabilizer_le_normalizer_affineWeylGroup b))]
      P.fundamentalAlcoveStabilizer b) :
    b.ExtendedAffineBruhatLE (P.extendedAffineWeylGroupMulEquiv b x)
        (P.extendedAffineWeylGroupMulEquiv b y) ↔
      x.right = y.right ∧ b.affineWeylCoxeterSystem.BruhatLE x.left y.left := by
  simp [ExtendedAffineBruhatLE]

/-- Extended affine Bruhat order restricts to Coxeter Bruhat order on the affine subgroup. -/
@[simp]
theorem extendedAffineBruhatLE_inclusion_affineWeylGroup_iff (u w : P.affineWeylGroup) :
    b.ExtendedAffineBruhatLE
      (Subgroup.inclusion P.affineWeylGroup_le_extendedAffineWeylGroup u)
      (Subgroup.inclusion P.affineWeylGroup_le_extendedAffineWeylGroup w) ↔
      b.affineWeylCoxeterSystem.BruhatLE u w := by
  simp only [inclusion_affineWeylGroup_eq_mulEquiv b, extendedAffineBruhatLE_mulEquiv_iff,
    SemidirectProduct.right_inl, SemidirectProduct.left_inl, true_and]

/-- The extended affine Bruhat relation is a partial order. -/
@[instance_reducible]
def extendedAffineBruhatPartialOrder : PartialOrder P.extendedAffineWeylGroup where
  le := b.ExtendedAffineBruhatLE
  le_refl _ := ⟨rfl, b.affineWeylCoxeterSystem.bruhatLE_refl _⟩
  le_trans _ _ _ hfg hgh := ⟨hfg.1.trans hgh.1, hfg.2.trans hgh.2⟩
  le_antisymm f g hfg hgf := (P.extendedAffineWeylGroupMulEquiv b).symm.injective
    (SemidirectProduct.ext (hfg.2.antisymm hgf.2) hfg.1)

/-- The order relation of `extendedAffineBruhatPartialOrder` is `ExtendedAffineBruhatLE`. -/
@[simp]
theorem extendedAffineBruhatPartialOrder_le_iff (f g : P.extendedAffineWeylGroup) :
    @LE.le _ b.extendedAffineBruhatPartialOrder.toLE f g ↔ b.ExtendedAffineBruhatLE f g :=
  Iff.rfl

/-- Strict extended affine Bruhat order is Bruhat comparison between distinct elements. -/
@[simp]
theorem extendedAffineBruhatPartialOrder_lt_iff (f g : P.extendedAffineWeylGroup) :
    @LT.lt _ b.extendedAffineBruhatPartialOrder.toLT f g ↔
      b.ExtendedAffineBruhatLE f g ∧ f ≠ g :=
  @lt_iff_le_and_ne _ b.extendedAffineBruhatPartialOrder f g

/-- Extended affine length is monotone in Bruhat order. -/
theorem ExtendedAffineBruhatLE.length_le {f g : P.extendedAffineWeylGroup}
    (h : b.ExtendedAffineBruhatLE f g) : b.extendedAffineLength f ≤ b.extendedAffineLength g := by
  simpa only [extendedAffineLength_def] using h.2.length_le

/-- Every length-zero element is minimal in the extended affine Bruhat order. -/
theorem extendedAffineBruhatLE_iff_eq_of_length_eq_zero {f g : P.extendedAffineWeylGroup}
    (hg : b.extendedAffineLength g = 0) : b.ExtendedAffineBruhatLE f g ↔ f = g := by
  rw [extendedAffineLength_def] at hg
  have hg' := b.affineWeylCoxeterSystem.length_eq_zero_iff.mp hg
  constructor
  · intro h
    apply (P.extendedAffineWeylGroupMulEquiv b).symm.injective
    refine SemidirectProduct.ext ?_ h.1
    have hf := h.2
    rw [hg', b.affineWeylCoxeterSystem.bruhatLE_one_iff] at hf
    exact hf.trans hg'.symm
  · rintro rfl
    exact b.extendedAffineBruhatPartialOrder.le_refl _

/-- An element lies below an alcove stabilizer exactly when it equals that stabilizer.
In particular, distinct stabilizers are incomparable. -/
@[simp]
theorem extendedAffineBruhatLE_stabilizer_iff (f : P.extendedAffineWeylGroup)
    (ω : P.fundamentalAlcoveStabilizer b) :
    b.ExtendedAffineBruhatLE f (Subgroup.inclusion
      (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b) ω) ↔
      f = Subgroup.inclusion (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b) ω :=
  b.extendedAffineBruhatLE_iff_eq_of_length_eq_zero (b.extendedAffineLength_stabilizer ω)

section Lattice

variable (Y : Submodule ℤ N) (hQ : P.corootSpan ℤ ≤ Y) (hP : Y ≤ P.coweightLattice)

/-- Bruhat order for an intermediate lattice, restricted from the extended affine Weyl group. -/
def LatticeAffineBruhatLE (f g : P.latticeAffineWeylGroup Y hQ hP) : Prop :=
  b.ExtendedAffineBruhatLE
    (Subgroup.inclusion (P.latticeAffineWeylGroup_le_extendedAffineWeylGroup hQ hP) f)
    (Subgroup.inclusion (P.latticeAffineWeylGroup_le_extendedAffineWeylGroup hQ hP) g)

/-- Lattice and extended affine Bruhat orders agree under the canonical inclusion. -/
theorem latticeAffineBruhatLE_iff_extendedAffineBruhatLE
    (f g : P.latticeAffineWeylGroup Y hQ hP) :
    b.LatticeAffineBruhatLE Y hQ hP f g ↔ b.ExtendedAffineBruhatLE
      (Subgroup.inclusion (P.latticeAffineWeylGroup_le_extendedAffineWeylGroup hQ hP) f)
      (Subgroup.inclusion (P.latticeAffineWeylGroup_le_extendedAffineWeylGroup hQ hP) g) :=
  Iff.rfl

/-- Lattice affine Bruhat order restricts to Coxeter Bruhat order on the affine subgroup. -/
@[simp]
theorem latticeAffineBruhatLE_inclusion_affineWeylGroup_iff (u w : P.affineWeylGroup) :
    b.LatticeAffineBruhatLE Y hQ hP
      (Subgroup.inclusion (P.affineWeylGroup_le_latticeAffineWeylGroup hQ hP) u)
      (Subgroup.inclusion (P.affineWeylGroup_le_latticeAffineWeylGroup hQ hP) w) ↔
      b.affineWeylCoxeterSystem.BruhatLE u w := by
  rw [latticeAffineBruhatLE_iff_extendedAffineBruhatLE, inclusion_inclusion_affineWeylGroup,
    inclusion_inclusion_affineWeylGroup, extendedAffineBruhatLE_inclusion_affineWeylGroup_iff]

/-- For every intermediate lattice, `wω ≤ vτ` exactly when `ω = τ` and `w ≤ v`. -/
@[simp]
theorem latticeAffineBruhatLE_mulEquiv_iff
    (x y : P.affineWeylGroup ⋊[(P.affineWeylGroup.normalizerMonoidHom).comp
      (Subgroup.inclusion
        (latticeFundamentalAlcoveStabilizer_le_normalizer_affineWeylGroup b hQ hP))]
      P.latticeFundamentalAlcoveStabilizer b Y hQ hP) :
    b.LatticeAffineBruhatLE Y hQ hP (P.latticeAffineWeylGroupMulEquiv b Y hQ hP x)
        (P.latticeAffineWeylGroupMulEquiv b Y hQ hP y) ↔
      x.right = y.right ∧ b.affineWeylCoxeterSystem.BruhatLE x.left y.left := by
  rw [latticeAffineBruhatLE_iff_extendedAffineBruhatLE,
    inclusion_latticeAffineWeylGroupMulEquiv, inclusion_latticeAffineWeylGroupMulEquiv,
    extendedAffineBruhatLE_mulEquiv_iff]
  exact and_congr_left fun _ ↦ (Subgroup.inclusion_injective _).eq_iff

/-- The Bruhat partial order for an intermediate lattice. -/
@[instance_reducible]
def latticeAffineBruhatPartialOrder : PartialOrder (P.latticeAffineWeylGroup Y hQ hP) :=
  letI := b.extendedAffineBruhatPartialOrder
  PartialOrder.lift
    (Subgroup.inclusion (P.latticeAffineWeylGroup_le_extendedAffineWeylGroup hQ hP))
    (Subgroup.inclusion_injective _)

/-- The order relation of `latticeAffineBruhatPartialOrder` is `LatticeAffineBruhatLE`. -/
@[simp]
theorem latticeAffineBruhatPartialOrder_le_iff (f g : P.latticeAffineWeylGroup Y hQ hP) :
    @LE.le _ (b.latticeAffineBruhatPartialOrder Y hQ hP).toLE f g ↔
      b.LatticeAffineBruhatLE Y hQ hP f g :=
  Iff.rfl

/-- Strict lattice affine Bruhat order is Bruhat comparison between distinct elements. -/
@[simp]
theorem latticeAffineBruhatPartialOrder_lt_iff (f g : P.latticeAffineWeylGroup Y hQ hP) :
    @LT.lt _ (b.latticeAffineBruhatPartialOrder Y hQ hP).toLT f g ↔
      b.LatticeAffineBruhatLE Y hQ hP f g ∧ f ≠ g :=
  @lt_iff_le_and_ne _ (b.latticeAffineBruhatPartialOrder Y hQ hP) f g

/-- Lattice affine length is monotone in Bruhat order. -/
theorem LatticeAffineBruhatLE.length_le {f g : P.latticeAffineWeylGroup Y hQ hP}
    (h : b.LatticeAffineBruhatLE Y hQ hP f g) :
    b.latticeAffineLength Y hQ hP f ≤ b.latticeAffineLength Y hQ hP g := by
  simpa only [latticeAffineLength_eq_extendedAffineLength] using
    ((b.latticeAffineBruhatLE_iff_extendedAffineBruhatLE Y hQ hP f g).mp h).length_le

/-- Every length-zero element is minimal in the lattice affine Bruhat order. -/
theorem latticeAffineBruhatLE_iff_eq_of_length_eq_zero
    {f g : P.latticeAffineWeylGroup Y hQ hP} (hg : b.latticeAffineLength Y hQ hP g = 0) :
    b.LatticeAffineBruhatLE Y hQ hP f g ↔ f = g := by
  rw [latticeAffineLength_eq_extendedAffineLength] at hg
  rw [latticeAffineBruhatLE_iff_extendedAffineBruhatLE,
    b.extendedAffineBruhatLE_iff_eq_of_length_eq_zero hg]
  exact (Subgroup.inclusion_injective _).eq_iff

/-- An element lies below a lattice alcove stabilizer exactly when it equals that stabilizer. -/
@[simp]
theorem latticeAffineBruhatLE_stabilizer_iff (f : P.latticeAffineWeylGroup Y hQ hP)
    (ω : P.latticeFundamentalAlcoveStabilizer b Y hQ hP) :
    b.LatticeAffineBruhatLE Y hQ hP f (Subgroup.inclusion
      (latticeFundamentalAlcoveStabilizer_le_latticeAffineWeylGroup b hQ hP) ω) ↔
      f = Subgroup.inclusion
        (latticeFundamentalAlcoveStabilizer_le_latticeAffineWeylGroup b hQ hP) ω :=
  b.latticeAffineBruhatLE_iff_eq_of_length_eq_zero Y hQ hP
    (b.latticeAffineLength_stabilizer Y hQ hP ω)

end Lattice

end RootPairing.Base
