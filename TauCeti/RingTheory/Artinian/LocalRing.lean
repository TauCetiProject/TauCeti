/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.Algebra.Module.Submodule.Essential
import TauCeti.Algebra.Module.Torsion.Essential
import TauCeti.RingTheory.Artinian.Torsion
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Artinian modules over a local ring

Let `R` be a commutative local ring with maximal ideal `𝔪` and residue field `κ`, and let `M` be
an Artinian `R`-module. Specializing `TauCeti.isEssential_torsionBySet_of_subset_jacobson` and
`TauCeti.finite_quotient_torsionBySet` to `𝔪 = Ring.jacobson R` shows that the socle
`M[𝔪] = Submodule.torsionBySet R M 𝔪` is essential and finite-dimensional over `κ`, so `M` embeds
into a finite power `Fin n → E` of any injective `R`-module containing `κ`
(`TauCeti.exists_injective_linearMap_fin_of_isArtinian`). If in addition `𝔪` is finitely generated
(in particular when `R` is Noetherian), then `Ideal.primaryComponent_eq_top_of_isArtinian` shows
that `M` equals its `𝔪`-primary component.

## Main results

* `TauCeti.isEssential_torsionBySet_maximalIdeal`: in a module with atomic submodule lattice over
  a commutative local ring, the socle `M[𝔪]` is essential.
* `TauCeti.finite_quotient_torsionBySet_maximalIdeal`: the socle `M[𝔪]` of an Artinian module
  over a commutative local ring is finite-dimensional over `R ⧸ 𝔪`.
* `TauCeti.exists_linearEquiv_fin_residueField_torsionBySet`: the socle `M[𝔪]` of an Artinian
  module is `R`-linearly isomorphic to `Fin n → κ` for some `n`.
* `TauCeti.exists_injective_linearMap_fin_of_isArtinian`: over any commutative local ring, every
  Artinian module embeds into `Fin n → E` for any injective module `E` containing `κ`.
* `TauCeti.primaryComponent_maximalIdeal_eq_top_of_isArtinian` and
  `TauCeti.mem_primaryComponent_maximalIdeal_of_isArtinian`: over a commutative local ring with
  finitely generated maximal ideal `𝔪`, every Artinian module is `𝔪`-power torsion.

## References

* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

namespace TauCeti

open IsLocalRing Submodule

section LocalRing

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]

/-- The socle `M[𝔪]` of a module with atomic submodule lattice (in particular, any Artinian module)
over a commutative local ring is an essential submodule. No Noetherian hypothesis is needed. -/
theorem isEssential_torsionBySet_maximalIdeal [IsAtomic (Submodule R M)] :
    IsEssential (Submodule.torsionBySet R M (maximalIdeal R : Set R)) :=
  isEssential_torsionBySet_of_subset_jacobson
    (IsLocalRing.ringJacobson_eq_maximalIdeal (R := R)).ge

/-- The socle `M[𝔪]` of an Artinian module over a commutative local ring is finite-dimensional
over `R ⧸ 𝔪`. No Noetherian hypothesis is needed. -/
theorem finite_quotient_torsionBySet_maximalIdeal [IsArtinian R M] :
    Module.Finite (R ⧸ maximalIdeal R) (Submodule.torsionBySet R M (maximalIdeal R : Set R)) :=
  let := Ideal.Quotient.field (maximalIdeal R)
  finite_quotient_torsionBySet (maximalIdeal R)

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

universe u v w in
/-- Every Artinian module over a commutative local ring embeds into a finite power `Fin n → E` of
any injective module containing the residue field. Neither a Noetherian hypothesis nor essentiality
of `ι` is required. -/
theorem exists_injective_linearMap_fin_of_isArtinian {R : Type u} [CommRing R] [IsLocalRing R]
    {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R] [Module.Injective R E]
    {ι : ResidueField R →ₗ[R] E} (hι : Function.Injective ι)
    (M : Type w) [AddCommGroup M] [Module R M] [IsArtinian R M] :
    ∃ (n : ℕ) (f : M →ₗ[R] (Fin n → E)), Function.Injective f := by
  obtain ⟨n, ⟨e⟩⟩ := exists_linearEquiv_fin_residueField_torsionBySet (R := R) (M := M)
  let S := Submodule.torsionBySet R M (maximalIdeal R : Set R)
  -- Map the socle `M[𝔪] ≃ κⁿ` coordinatewise into `Eⁿ`.
  let g : S →ₗ[R] (Fin n → E) := (LinearMap.pi fun i ↦ ι.comp (LinearMap.proj i)).comp e.toLinearMap
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ e.injective <| funext fun i ↦ hι ?_
    simpa [g] using congrFun hx i
  -- Extend from the essential socle to all of `M` by injectivity of `Fin n → E`.
  obtain ⟨f, hf⟩ := Module.Injective.extension_property R (Fin n → E) S M S.subtype
    S.injective_subtype g
  refine ⟨n, f, ?_⟩
  have hrange : IsEssential (LinearMap.range S.subtype) := by
    rw [Submodule.range_subtype]
    exact isEssential_torsionBySet_maximalIdeal
  exact hrange.injective_of_injective_comp (hf.symm ▸ hg)

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

end LocalRing

end TauCeti
