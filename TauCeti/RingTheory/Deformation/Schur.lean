/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import TauCeti.RingTheory.Deformation.Lift

/-!
# Schur residual representations: strict and full conjugacy agree

A residual representation `ρbar : G →* GL n k` is *Schur* if its only endomorphisms are the
scalars: every matrix over `k` commuting with all `ρbar g` is a scalar matrix. Together with
Mazur's finiteness condition `Φ_p`, this is the hypothesis under which the deformation functor
`Def_ρbar` of strict classes of lifts is representable.

The main result is that for a Schur residual representation, two lifts that are conjugate by an
arbitrary invertible matrix over the coefficient ring are already conjugate by a matrix reducing to
the identity, so strict classes of lifts are just their `GL n`-conjugacy classes. On the
coefficient ring it only needs that units of `k` lift to units, which holds for every surjection
from a local ring, in particular for every object of the Artinian coefficient category `C_Λ`.
Neither hypothesis can be dropped: the statement fails for the non-Schur trivial representation of
rank two over the dual numbers, and for a Schur representation over the nonlocal ring `ℤ` mapping
onto `𝔽₅`.

## Main definitions

* `MonoidHom.IsSchur ρbar`: every matrix commuting with the image of `ρbar` is scalar.

## Main results

* `MonoidHom.IsSchur.mem_range_scalar_of_commute`: an invertible matrix centralising a Schur
  representation is a scalar unit.
* `MonoidHom.IsSchur.of_span_eq_top`: a representation whose image spans the full matrix algebra
  (for instance an absolutely irreducible one) is Schur.
* `MonoidHom.isSchur_one_iff`: the trivial representation is Schur exactly in rank at most one.
* `MonoidHom.IsSchur.exists_mem_ker_map_conj_eq`: over a coefficient ring whose units surject onto
  those of `k`, two lifts of a Schur representation that are conjugate are strictly conjugate.
* `TauCeti.Deformation.StrictClass.mk_eq_mk_iff_of_isSchur`: two lifts of a Schur residual
  representation to an object of `C_Λ` have the same strict class exactly when they are conjugate
  by some invertible matrix.

## References

* T. Gee, *Modularity lifting theorems*, Essent. Number Theory 1 (2022), §3.1, Definition 3.4 and
  the remark following it.
* B. Mazur, *Deforming Galois representations*, in *Galois groups over `ℚ`*, MSRI Publ. 16
  (1989), 385–437, §1.1.
-/

public section

open Matrix

universe u v w x

namespace MonoidHom

variable {G : Type w} [Monoid G] {k : Type v} [CommRing k] {n : Type x} [Fintype n] [DecidableEq n]

/-- A representation `ρbar : G →* GL n k` is *Schur* if its only endomorphisms are the scalars:
every matrix over `k` commuting with all `ρbar g` is a scalar matrix. -/
def IsSchur (ρbar : G →* GL n k) : Prop :=
  ∀ M : Matrix n n k, (∀ g, Commute M (ρbar g : Matrix n n k)) → M ∈ Set.range (scalar n)

/-- Unfolding `MonoidHom.IsSchur`. -/
theorem isSchur_iff {ρbar : G →* GL n k} :
    ρbar.IsSchur ↔
      ∀ M : Matrix n n k, (∀ g, Commute M (ρbar g : Matrix n n k)) → M ∈ Set.range (scalar n) :=
  Iff.rfl

namespace IsSchur

variable {ρbar : G →* GL n k}

/-- A matrix commuting with the image of a Schur representation is scalar. -/
theorem mem_range_scalar (hρbar : ρbar.IsSchur) {M : Matrix n n k}
    (hM : ∀ g, Commute M (ρbar g : Matrix n n k)) : M ∈ Set.range (scalar n) :=
  hρbar M hM

/-- An invertible matrix commuting with the image of a Schur representation is a scalar unit. -/
theorem mem_range_scalar_of_commute (hρbar : ρbar.IsSchur) {c : GL n k}
    (hc : ∀ g, Commute c (ρbar g)) : c ∈ (GeneralLinearGroup.scalar n).range := by
  rw [← GeneralLinearGroup.center_eq_range_scalar]
  exact GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    (hρbar.mem_range_scalar fun g ↦ (hc g).units_val)

/-- A representation whose image spans the full matrix algebra is Schur. Over a field this is the
case for an absolutely irreducible representation, by Burnside's theorem. -/
theorem of_span_eq_top
    (h : Submodule.span k (Set.range fun g ↦ (ρbar g : Matrix n n k)) = ⊤) : ρbar.IsSchur := by
  intro M hM
  rw [← center_eq_range, Semigroup.mem_center_iff]
  intro N
  have hN := Algebra.adjoin_le_centralizer_centralizer k _
    (Algebra.span_le_adjoin k _ (h ▸ Submodule.mem_top : N ∈ _))
  exact (hN M fun _ ⟨g, hg⟩ ↦ hg ▸ (hM g).symm.eq).symm

end IsSchur

/-- Every representation of rank at most one is Schur. -/
theorem isSchur_of_subsingleton [Subsingleton n] (ρbar : G →* GL n k) : ρbar.IsSchur := by
  intro M _
  rcases isEmpty_or_nonempty n with _ | ⟨⟨i⟩⟩
  · exact ⟨0, Subsingleton.elim _ _⟩
  · refine ⟨M i i, Matrix.ext fun a b ↦ ?_⟩
    rw [Subsingleton.elim a i, Subsingleton.elim b i, scalar_apply, diagonal_apply_eq]

variable (G) in
/-- The trivial representation is Schur exactly in rank at most one: in rank at least two every
matrix commutes with it, including non-scalar ones. -/
theorem isSchur_one_iff [Nontrivial k] : (1 : G →* GL n k).IsSchur ↔ Subsingleton n := by
  refine ⟨fun h ↦ ⟨fun i j ↦ by_contra fun hij ↦ ?_⟩, fun _ ↦ isSchur_of_subsingleton _⟩
  obtain ⟨c, hc⟩ := h (single i j 1) fun _ ↦ by simp
  have h := congr_fun₂ hc i j
  rw [single_apply_same, scalar_apply, diagonal_apply_ne _ hij] at h
  exact one_ne_zero h.symm

namespace IsSchur

variable {ρbar : G →* GL n k} {A : Type u} [CommRing A]

/-- Let `π : A →+* k` be a ring map whose induced map on units is surjective, for instance the
residue map of a local ring (`IsLocalRing.surjective_units_map_of_local_ringHom`). If two
homomorphisms `ρ ρ' : G →* GL n A` both reduce to a Schur representation `ρbar` along `π` and are
conjugate by some `a : GL n A`, then they are conjugate by an element of the kernel of the
reduction `GL n A →* GL n k`. -/
theorem exists_mem_ker_map_conj_eq (hρbar : ρbar.IsSchur) (π : A →+* k)
    (hπ : Function.Surjective (Units.map (π : A →* k))) {ρ ρ' : G →* GL n A}
    (hρ : ∀ g, GeneralLinearGroup.map π (ρ g) = ρbar g)
    (hρ' : ∀ g, GeneralLinearGroup.map π (ρ' g) = ρbar g) {a : GL n A}
    (ha : ∀ g, a * ρ g * a⁻¹ = ρ' g) :
    ∃ b ∈ (GeneralLinearGroup.map (n := n) π).ker, ∀ g, b * ρ g * b⁻¹ = ρ' g := by
  -- The reduction of `a` centralises `ρbar`, hence is a scalar unit `u`.
  have hc : ∀ g, Commute (GeneralLinearGroup.map π a) (ρbar g) := fun g ↦ by
    have := congrArg (GeneralLinearGroup.map π) (ha g)
    rw [map_mul, map_mul, map_inv, hρ, hρ', mul_inv_eq_iff_eq_mul] at this
    exact this
  obtain ⟨u, hu⟩ := hρbar.mem_range_scalar_of_commute hc
  -- Dividing `a` by a unit `v` lifting `u` gives a strict conjugator.
  obtain ⟨v, rfl⟩ := hπ u
  refine ⟨GeneralLinearGroup.scalar n v⁻¹ * a, ?_, fun g ↦ ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, ← hu, GeneralLinearGroup.map_scalar, ← map_mul, map_inv,
      inv_mul_cancel, map_one]
  · -- Conjugation by the scalar `v⁻¹` is trivial.
    calc _ = GeneralLinearGroup.scalar n v⁻¹ * (a * ρ g * a⁻¹) *
          GeneralLinearGroup.scalar n v := by rw [map_inv]; group
      _ = ρ' g := by
          rw [GeneralLinearGroup.scalar_commute, mul_assoc, ← map_mul, inv_mul_cancel, map_one,
            mul_one, ha]

end IsSchur

end MonoidHom

namespace TauCeti.Deformation

variable {Λ : Type u} [CommRing Λ] {k : Type v} [Field k] [Algebra Λ k]
  {n : Type x} [Fintype n] [DecidableEq n] {G : Type w} [Monoid G] [TopologicalSpace G]
  {ρbar : G →* GL n k} {A : ArtinLocalAlg Λ k}

namespace Lift

/-- Two lifts of a Schur residual representation to an object of `C_Λ` that are conjugate by an
invertible matrix are conjugate by an element of the strict kernel. -/
theorem exists_smul_eq_of_isSchur (hρbar : ρbar.IsSchur) {ρ ρ' : Lift ρbar A}
    {a : GL n A.obj.left} (ha : ∀ g, a * ρ g * a⁻¹ = ρ' g) :
    ∃ b : A.strictKernel n, b • ρ = ρ' := by
  obtain ⟨b, hb, hbρ⟩ := hρbar.exists_mem_ker_map_conj_eq (A.augmentation : A.obj.left →+* k)
    (IsLocalRing.surjective_units_map_of_local_ringHom _ A.augmentation_surjective
      (.of_surjective _ A.augmentation_surjective))
    (ρ := ρ.toMonoidHom) (ρ' := ρ'.toMonoidHom) ρ.map_augmentation_apply
    ρ'.map_augmentation_apply ha
  exact ⟨⟨b, ArtinLocalAlg.mem_strictKernel_iff.mpr (MonoidHom.mem_ker.mp hb)⟩, ext hbρ⟩

end Lift

namespace StrictClass

/-- Two lifts of a Schur residual representation to an object of `C_Λ` have the same strict class
exactly when they are conjugate by some invertible matrix, not necessarily one reducing to the
identity. -/
theorem mk_eq_mk_iff_of_isSchur (hρbar : ρbar.IsSchur) {ρ ρ' : Lift ρbar A} :
    mk ρ = mk ρ' ↔ ∃ a : GL n A.obj.left, ∀ g, a * ρ g * a⁻¹ = ρ' g := by
  rw [mk_eq_mk_iff]
  refine ⟨fun ⟨b, hb⟩ ↦ ⟨b, fun g ↦ by rw [← hb, Lift.smul_apply]⟩, fun ⟨a, ha⟩ ↦ ?_⟩
  exact Lift.exists_smul_eq_of_isSchur hρbar ha

end StrictClass

end TauCeti.Deformation
