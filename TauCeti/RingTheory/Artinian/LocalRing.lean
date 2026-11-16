/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.Algebra.Module.Submodule.Essential
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.Nakayama
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Artinian modules over a local ring

Let `R` be a commutative ring and `M` an Artinian `R`-module. For any finitely generated ideal `I`
contained in the Jacobson radical of `R`, the descending chain `n ↦ I ^ n • R • x` stabilizes for
each `x ∈ M`, so Nakayama's lemma forces `I ^ n • x = 0`
(`Ideal.primaryComponent_eq_top_of_isArtinian`). Moreover, any module whose submodule lattice is
atomic (in particular, any Artinian module) has an essential `s`-torsion submodule for every subset
`s ⊆ Ring.jacobson R`, since the Jacobson radical annihilates every simple submodule
(`TauCeti.isEssential_torsionBySet_of_subset_jacobson`), and for any ideal `I` with semisimple
quotient `R ⧸ I` the `I`-torsion submodule of an Artinian module is finitely generated over `R ⧸ I`
(`TauCeti.finite_quotient_torsionBySet`). No Noetherian hypothesis on `R` is needed.

When `R` is a commutative local ring with maximal ideal `𝔪` and residue field `κ`, specializing to
`𝔪 = Ring.jacobson R` shows that the socle `M[𝔪] = Submodule.torsionBySet R M 𝔪` of an Artinian
module is essential and finite-dimensional over `κ`, so `M` embeds into a finite power `Fin n → E`
of any injective `R`-module containing `κ` (`TauCeti.exists_injective_linearMap_fin_of_isArtinian`).
If in addition `𝔪` is finitely generated (in particular when `R` is Noetherian), then `M` equals its
`𝔪`-primary component.

## Main results

* `Ideal.primaryComponent_eq_top_of_isArtinian`: over any commutative ring, an Artinian module is
  `I`-power torsion for every finitely generated ideal `I ≤ Ring.jacobson R`.
* `TauCeti.isEssential_torsionBySet_of_subset_jacobson` and
  `TauCeti.isEssential_torsionBySet_maximalIdeal`: in a module with atomic submodule lattice, the
  submodule annihilated by any subset of `Ring.jacobson R` (in particular, the socle `M[𝔪]` over a
  local ring) is essential.
* `TauCeti.finite_quotient_torsionBySet` and `TauCeti.finite_quotient_torsionBySet_maximalIdeal`:
  for any ideal `I` with semisimple quotient `R ⧸ I` (in particular `𝔪` over a local ring), the
  `I`-torsion submodule of an Artinian module is finitely generated over `R ⧸ I`.
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

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- In a module with atomic submodule lattice (in particular, any Artinian module), the submodule
annihilated by any subset of the Jacobson radical is essential. -/
theorem isEssential_torsionBySet_of_subset_jacobson [IsAtomic (Submodule R M)] {s : Set R}
    (hs : s ⊆ Ring.jacobson R) : IsEssential (Submodule.torsionBySet R M s) := by
  refine isEssential_of_forall_atom_le fun a ha x hx ↦
    (Submodule.mem_torsionBySet_iff _ _).mpr fun ⟨r, hr⟩ ↦ ?_
  have : IsSimpleModule R a := isSimpleModule_iff_isAtom.mpr ha
  exact congrArg Subtype.val
    (Module.mem_annihilator.mp (IsSemisimpleModule.jacobson_le_annihilator R a (hs hr)) ⟨x, hx⟩)

/-- For any ideal `I` with semisimple quotient `R ⧸ I`, the `I`-torsion submodule of an Artinian
`R`-module is finitely generated over `R ⧸ I`. No Noetherian or local hypothesis is needed. -/
theorem finite_quotient_torsionBySet [IsArtinian R M] (I : Ideal R) [IsSemisimpleRing (R ⧸ I)] :
    Module.Finite (R ⧸ I) (Submodule.torsionBySet R M (I : Set R)) := by
  have : IsArtinian (R ⧸ I) (Submodule.torsionBySet R M (I : Set R)) :=
    isArtinian_of_tower R (isArtinian_submodule' _)
  exact ((IsSemisimpleModule.finite_tfae (R := R ⧸ I)
    (M := Submodule.torsionBySet R M (I : Set R))).out 3 1).mp this

end CommRing

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
