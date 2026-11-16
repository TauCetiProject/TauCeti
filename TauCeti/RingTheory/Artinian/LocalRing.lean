/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.Algebra.Module.Submodule.Essential
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Nakayama
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Artinian modules over a local ring

Let `R` be a commutative ring and `M` an Artinian `R`-module. For any finitely generated ideal `I`
contained in the Jacobson radical of `R`, the descending chain `n ↦ I ^ n • R • x` stabilizes for
each `x ∈ M`, so Nakayama's lemma forces `I ^ n • x = 0`
(`Ideal.primaryComponent_eq_top_of_isArtinian`). No Noetherian hypothesis on `R` is needed.

When `R` is a commutative local ring with maximal ideal `𝔪` and residue field `κ`, the submodule
lattice of `M` is well-founded, hence atomic, and every simple submodule is killed by `𝔪` because
`1 - s r` is a unit whenever `r ∈ 𝔪`. Consequently the socle `M[𝔪] = Submodule.torsionBySet R M 𝔪`
is an essential submodule of `M` and finite-dimensional as a `κ`-vector space. If in addition `𝔪`
is finitely generated (in particular when `R` is Noetherian), then `M` equals its `𝔪`-primary
component. This is the input needed to equip an Artinian module over a Noetherian local ring with
its canonical module structure over the `𝔪`-adic completion and to embed it into a finite power of
the injective hull of `κ`.

## Main results

* `Ideal.primaryComponent_eq_top_of_isArtinian`: over any commutative ring, an Artinian module is
  `I`-power torsion for every finitely generated ideal `I ≤ Ring.jacobson R`.
* `TauCeti.isEssential_torsionBySet_maximalIdeal`: the socle `M[𝔪]` of an Artinian module over a
  commutative local ring is essential.
* `TauCeti.finite_quotient_torsionBySet_maximalIdeal`: the socle `M[𝔪]` of an Artinian module is a
  finite vector space over `R ⧸ 𝔪`.
* `TauCeti.exists_linearEquiv_fin_residueField_torsionBySet`: the socle `M[𝔪]` of an Artinian
  module is `R`-linearly isomorphic to `Fin n → κ` for some `n`.
* `TauCeti.primaryComponent_maximalIdeal_eq_top_of_isArtinian` and
  `TauCeti.mem_primaryComponent_maximalIdeal_of_isArtinian`: over a commutative local ring with
  finitely generated maximal ideal `𝔪`, every Artinian module is `𝔪`-power torsion.

## References

* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

namespace Ideal

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Over any commutative ring, an Artinian module is `I`-power torsion for every finitely generated
ideal `I` contained in the Jacobson radical. Neither a Noetherian nor a local hypothesis is
needed. -/
theorem primaryComponent_eq_top_of_isArtinian (I : Ideal R) [IsArtinian R M]
    (hI : I.FG) (hJ : I ≤ Ring.jacobson R) :
    I.primaryComponent M = ⊤ := by
  refine top_unique fun x _ ↦ ?_
  -- The descending chain `I ^ n • (R • x)` stabilizes because `M` is Artinian.
  let f : ℕ →o (Submodule R M)ᵒᵈ :=
    ⟨fun n ↦ OrderDual.toDual (I ^ n • Submodule.span R {x}), fun m n hmn ↦
      Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes f
  have hstab : I ^ n • Submodule.span R {x} = I • (I ^ n • Submodule.span R {x}) := by
    have h1 : I ^ n • Submodule.span R {x} = I ^ (n + 1) • Submodule.span R {x} :=
      OrderDual.toDual.injective (hn (n + 1) (Nat.le_succ n))
    rw [pow_succ', mul_smul] at h1
    exact h1
  have hfg : (I ^ n • Submodule.span R {x}).FG :=
    Submodule.FG.smul hI.pow (Submodule.fg_span_singleton x)
  have hbot : I ^ n • Submodule.span R {x} = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson I _ hfg hstab.le hJ
  refine (I.primaryComponent_mem M x).mpr ⟨n, (Submodule.mem_torsionBySet_iff _ _).mpr fun r ↦ ?_⟩
  have hmem : (r : R) • x ∈ I ^ n • Submodule.span R {x} :=
    Submodule.smul_mem_smul r.2 (Submodule.mem_span_singleton_self x)
  rwa [hbot, Submodule.mem_bot] at hmem

end Ideal

namespace TauCeti

open IsLocalRing Submodule

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]

/-- The socle `M[𝔪]` of an Artinian module over a commutative local ring is an essential
submodule. No Noetherian hypothesis is needed. -/
theorem isEssential_torsionBySet_maximalIdeal [IsArtinian R M] :
    IsEssential (Submodule.torsionBySet R M (maximalIdeal R : Set R)) := by
  refine isEssential_of_forall_atom_le fun a ha x hx ↦
    (Submodule.mem_torsionBySet_iff _ _).mpr fun ⟨r, hr⟩ ↦ ?_
  by_contra hrx
  -- Minimality of the atom `a` forces `R • (r • x) = a`, producing `1 - s r` killing `x`.
  have hspan : Submodule.span R {r • x} = a :=
    (ha.le_iff.mp (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (a.smul_mem r hx)))).resolve_left (mt Submodule.span_singleton_eq_bot.mp hrx)
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (hspan.symm ▸ hx)
  have hunit : IsUnit (1 - s * r) := notMem_maximalIdeal.mp fun h ↦
    (maximalIdeal R).ne_top_iff_one.mp (maximalIdeal.isMaximal R).ne_top <| by
      simpa using (maximalIdeal R).add_mem h ((maximalIdeal R).mul_mem_left s hr)
  have hx0 : (1 - s * r) • x = 0 := by
    rw [sub_smul, one_smul, mul_smul, hs, sub_self]
  obtain ⟨u, hu⟩ := hunit
  have : x = 0 := by
    calc x = u⁻¹ • u • x := (inv_smul_smul u x).symm
      _ = u⁻¹ • (1 - s * r) • x := by rw [Units.smul_def u x, hu]
      _ = 0 := by rw [hx0, smul_zero]
  exact hrx (by rw [this, smul_zero])

/-- The socle `M[𝔪]` of an Artinian module over a commutative local ring is finite-dimensional
over `R ⧸ 𝔪`. No Noetherian hypothesis is needed. -/
theorem finite_quotient_torsionBySet_maximalIdeal [IsArtinian R M] :
    Module.Finite (R ⧸ maximalIdeal R) (Submodule.torsionBySet R M (maximalIdeal R : Set R)) := by
  let := Ideal.Quotient.field (maximalIdeal R)
  have : IsArtinian (R ⧸ maximalIdeal R) (Submodule.torsionBySet R M (maximalIdeal R : Set R)) :=
    isArtinian_of_tower R (isArtinian_submodule' _)
  exact ((IsSemisimpleModule.finite_tfae (R := R ⧸ maximalIdeal R)
    (M := Submodule.torsionBySet R M (maximalIdeal R : Set R))).out 3 1).mp this

/-- The socle `M[𝔪]` of an Artinian module over a commutative local ring is `R`-linearly
isomorphic to a finite power of the residue field. -/
theorem exists_linearEquiv_fin_residueField_torsionBySet [IsArtinian R M] :
    ∃ n : ℕ, Nonempty
      (Submodule.torsionBySet R M (maximalIdeal R : Set R) ≃ₗ[R] (Fin n → ResidueField R)) := by
  let := Ideal.Quotient.field (maximalIdeal R)
  have : Module.Finite (R ⧸ maximalIdeal R)
      (Submodule.torsionBySet R M (maximalIdeal R : Set R)) :=
    finite_quotient_torsionBySet_maximalIdeal
  let b := Module.finBasis (R ⧸ maximalIdeal R)
    (Submodule.torsionBySet R M (maximalIdeal R : Set R))
  refine ⟨_, ⟨(b.equivFun.restrictScalars R).trans
    (LinearEquiv.piCongrRight fun _ ↦ quotientEquivResidueField (maximalIdeal.isMaximal R))⟩⟩

/-- Every Artinian module over a commutative local ring with finitely generated maximal ideal is
maximal-ideal-power torsion. -/
theorem primaryComponent_maximalIdeal_eq_top_of_isArtinian [IsArtinian R M]
    (h𝔪 : (maximalIdeal R).FG) :
    (maximalIdeal R).primaryComponent M = ⊤ :=
  (maximalIdeal R).primaryComponent_eq_top_of_isArtinian h𝔪
    (IsLocalRing.ringJacobson_eq_maximalIdeal (R := R)).ge

/-- Every element of an Artinian module over a commutative local ring with finitely generated
maximal ideal is killed by a power of the maximal ideal. -/
theorem mem_primaryComponent_maximalIdeal_of_isArtinian [IsArtinian R M]
    (h𝔪 : (maximalIdeal R).FG) (x : M) :
    x ∈ (maximalIdeal R).primaryComponent M := by
  rw [primaryComponent_maximalIdeal_eq_top_of_isArtinian h𝔪]
  exact mem_top

end TauCeti
