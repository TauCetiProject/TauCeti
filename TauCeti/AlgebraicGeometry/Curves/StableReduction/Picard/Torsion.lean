/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.Rank

/-!
# Prime torsion in the Picard group of a numerical type

For a numerical type `T`, this file equips the subgroup `Pic(T)[ℓ]` killed by a natural number
`ℓ` with its canonical `ZMod ℓ`-module structure.  When `ℓ` is prime this is a finite-dimensional
vector space.  Its cardinality is therefore `ℓ` raised to its dimension, which is the form of the
torsion invariant used when comparing a numerical type with torsion line bundles on a regular
model.

The total degree of every nonzero-order torsion class vanishes.  Equivalences of numerical types
carry torsion classes to torsion classes and induce linear equivalences on the corresponding
prime-torsion spaces, so both their dimension and cardinality are independent of the indexing of
the components.

The Picard group follows [Stacks, Tag 0C7H](https://stacks.math.columbia.edu/tag/0C7H), and its
finite generation and rank are [Stacks, Tag 0C7I](https://stacks.math.columbia.edu/tag/0C7I).
-/

public section

namespace TauCeti

namespace NumericalType

universe u v

variable (T : NumericalType.{u})

/-- The subgroup `Pic(T)[ℓ]` of Picard classes killed by `ℓ`.

Although the main application takes `ℓ` prime, the subgroup is useful for every natural number.
For prime `ℓ`, it carries the canonical vector-space structure over `ZMod ℓ`. -/
abbrev torsion (ℓ : ℕ) : AddSubgroup T.Pic :=
  AddSubgroup.torsionBy T.Pic (ℓ : ℤ)

/-- The canonical `ZMod ℓ`-module structure on the `ℓ`-torsion of `Pic(T)`. -/
noncomputable instance torsionModule (ℓ : ℕ) : Module (ZMod ℓ) (T.torsion ℓ) :=
  AddSubgroup.torsionBy.zmodModule

/-- If `ℓ` is nonzero, then the `ℓ`-torsion subgroup of `Pic(T)` is finite.

The ambient Picard group is finitely generated because it is a quotient of the finite free module
of multidegrees.  Its `ℓ`-torsion subgroup is therefore a finitely generated torsion abelian group.
-/
theorem finite_torsion {ℓ : ℕ} (hℓ : ℓ ≠ 0) : Finite (T.torsion ℓ) := by
  let _ : Module.Finite ℤ (T.torsion ℓ) := by
    exact (inferInstance : Module.Finite ℤ (T.torsion ℓ).toIntSubmodule)
  apply Module.finite_of_fg_torsion
  exact Submodule.torsionBy_isTorsion_nonZeroDivisor (ℓ : ℤ) (by simp [hℓ])

/-- For nonzero `ℓ`, the `ℓ`-torsion subgroup of `Pic(T)` is finitely generated over `ZMod ℓ`. -/
noncomputable instance torsionModuleFinite (ℓ : ℕ) [NeZero ℓ] :
    Module.Finite (ZMod ℓ) (T.torsion ℓ) := by
  let _ : Finite (T.torsion ℓ) := T.finite_torsion (NeZero.ne ℓ)
  have h := Module.Finite.span_of_finite (ZMod ℓ)
    (Set.toFinite (Set.univ : Set (T.torsion ℓ)))
  apply Module.Finite.of_surjective (Submodule.subtype
    (Submodule.span (ZMod ℓ) (Set.univ : Set (T.torsion ℓ))))
  intro x
  exact ⟨⟨x, by simp⟩, rfl⟩

/-- The cardinality of prime torsion is the prime raised to its vector-space dimension. -/
theorem natCard_torsion (ℓ : ℕ) [Fact ℓ.Prime] :
    Nat.card (T.torsion ℓ) = ℓ ^ Module.finrank (ZMod ℓ) (T.torsion ℓ) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod ℓ), Nat.card_zmod]

/-- Every Picard torsion class killed by a nonzero natural number has total degree zero. -/
@[simp]
theorem degree_coe_torsion {ℓ : ℕ} (hℓ : ℓ ≠ 0) (x : T.torsion ℓ) :
    T.degree (x : T.Pic) = 0 := by
  have h : ℓ • T.degree (x : T.Pic) = 0 := by
    have hx : ℓ • (x : T.Pic) = 0 := AddSubgroup.torsionBy.nsmul_iff.mp x.property
    simpa only [map_nsmul, map_zero] using congrArg T.degree hx
  exact (nsmul_eq_zero_iff_right hℓ).mp h

namespace Equiv

variable {T} {T' : NumericalType.{v}} {T'' : NumericalType}

private def torsionAddEquiv (f : T.Equiv T') (ℓ : ℕ) : T.torsion ℓ ≃+ T'.torsion ℓ where
  toFun x := ⟨f.picCongr x, by
    rw [AddSubgroup.torsionBy.nsmul_iff]
    have hx : ℓ • (x : T.Pic) = 0 := AddSubgroup.torsionBy.nsmul_iff.mp x.property
    simpa only [map_nsmul, map_zero] using congrArg f.picCongr hx⟩
  invFun x := ⟨f.picCongr.symm x, by
    rw [AddSubgroup.torsionBy.nsmul_iff]
    have hx : ℓ • (x : T'.Pic) = 0 := AddSubgroup.torsionBy.nsmul_iff.mp x.property
    simpa only [map_nsmul, map_zero] using congrArg f.picCongr.symm hx⟩
  left_inv x := by
    apply Subtype.ext
    exact f.picCongr.symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    exact f.picCongr.apply_symm_apply x
  map_add' x y := by
    apply Subtype.ext
    exact map_add f.picCongr (x : T.Pic) y

/-- An equivalence of numerical types induces a `ZMod ℓ`-linear equivalence on their
`ℓ`-torsion Picard subgroups. -/
noncomputable def torsionCongr (f : T.Equiv T') (ℓ : ℕ) :
    T.torsion ℓ ≃ₗ[ZMod ℓ] T'.torsion ℓ :=
  LinearEquiv.ofBijective ((f.torsionAddEquiv ℓ).toAddMonoidHom.toZModLinearMap ℓ)
    (f.torsionAddEquiv ℓ).bijective

/-- The underlying Picard class of a transported torsion class is transported by `picCongr`. -/
@[simp]
lemma coe_torsionCongr (f : T.Equiv T') (ℓ : ℕ) (x : T.torsion ℓ) :
    (f.torsionCongr ℓ x : T'.Pic) = f.picCongr x :=
  by simp [torsionCongr, torsionAddEquiv]

/-- The identity equivalence induces the identity on torsion Picard classes. -/
@[simp]
lemma torsionCongr_refl (ℓ : ℕ) :
    (Equiv.refl : T.Equiv T).torsionCongr ℓ = LinearEquiv.refl (ZMod ℓ) (T.torsion ℓ) := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  simp

/-- Torsion transport respects composition of equivalences of numerical types. -/
@[simp]
lemma torsionCongr_trans (f : T.Equiv T') (g : T'.Equiv T'') (ℓ : ℕ) :
    (f.trans g).torsionCongr ℓ = (f.torsionCongr ℓ).trans (g.torsionCongr ℓ) := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  simp

/-- Torsion transport along an inverse equivalence is the inverse linear equivalence. -/
@[simp]
lemma torsionCongr_symm (f : T.Equiv T') (ℓ : ℕ) :
    (f.torsionCongr ℓ).symm = f.symm.torsionCongr ℓ := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  apply f.picCongr.injective
  calc
    f.picCongr ((f.torsionCongr ℓ).symm x : T.Pic) =
        (f.torsionCongr ℓ ((f.torsionCongr ℓ).symm x) : T'.Pic) :=
      (f.coe_torsionCongr ℓ ((f.torsionCongr ℓ).symm x)).symm
    _ = x := congrArg Subtype.val ((f.torsionCongr ℓ).apply_symm_apply x)
    _ = f.picCongr (f.symm.picCongr (x : T'.Pic)) := by
      rw [← f.picCongr_symm]
      exact (f.picCongr.apply_symm_apply x).symm

/-- Prime-torsion dimension is invariant under equivalence of numerical types. -/
theorem finrank_torsion_eq (f : T.Equiv T') (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.finrank (ZMod ℓ) (T.torsion ℓ) =
      Module.finrank (ZMod ℓ) (T'.torsion ℓ) :=
  (f.torsionCongr ℓ).finrank_eq

/-- Torsion cardinality is invariant under equivalence of numerical types. -/
theorem natCard_torsion_eq (f : T.Equiv T') (ℓ : ℕ) :
    Nat.card (T.torsion ℓ) = Nat.card (T'.torsion ℓ) :=
  Nat.card_congr (f.torsionCongr ℓ).toEquiv

end Equiv

end NumericalType

end TauCeti
