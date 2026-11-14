/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.HopkinsLevitzki
public import TauCeti.Algebra.Module.Torsion.ResidueField
public import TauCeti.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Artinian modules over commutative local rings

Let `R` be a commutative local ring with maximal ideal `𝔪` and residue field `κ`. Every simple
submodule of an `R`-module is annihilated by `𝔪`, so it lies in the socle `M[𝔪]`
(`Submodule.torsionBySet R M 𝔪`). When `M` is Artinian, its submodule lattice is atomic, hence
`M[𝔪]` is an essential submodule of `M` and is finite-dimensional over `κ`.

Two structural consequences follow:
* Without any Noetherian hypothesis on `R`, if `E` is an injective `R`-module containing a copy of
  `κ`, extending an embedding `M[𝔪] ↪ E^r` along `M[𝔪] ⊆ M` embeds `M` into a finite power `E^r`.
* If `R` is Noetherian, essentiality of `M[𝔪]` implies that every element of an Artinian `R`-module
  is killed by a power of `𝔪`, so `M` carries the canonical action of the `𝔪`-adic completion `R̂`.

## Main results

* `IsAtom.le_torsionBySet_maximalIdeal`: every simple submodule over a local ring lies in the
  `𝔪`-torsion submodule.
* `TauCeti.isEssential_torsionBySet_maximalIdeal`: the `𝔪`-torsion submodule of an Artinian module
  over a local ring is essential.
* `TauCeti.exists_torsionBySet_maximalIdeal_linearEquiv_pi`: the `𝔪`-torsion submodule of an
  Artinian module is `R`-linearly isomorphic to `Fin r → κ` for some `r : ℕ`.
* `TauCeti.exists_injective_linearMap_pi_of_isArtinian`: every Artinian module over a local ring
  embeds into a finite power of any injective module containing `κ`.
* `TauCeti.primaryComponent_maximalIdeal_eq_top_of_isArtinian`: over a Noetherian local ring,
  every Artinian module is maximal-ideal-power torsion.

## References

* [Stacks Project, Section 47.7](https://stacks.math.columbia.edu/tag/08Z1) and
  [Proposition 47.7.8](https://stacks.math.columbia.edu/tag/08Z9).
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

open IsLocalRing Submodule

/-- Every simple submodule of a module over a commutative local ring is annihilated by the
maximal ideal. -/
theorem IsAtom.le_torsionBySet_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {a : Submodule R M} (ha : IsAtom a) :
    a ≤ torsionBySet R M (maximalIdeal R) := by
  have : IsSimpleModule R a := isSimpleModule_iff_isAtom.mpr ha
  intro x hx
  rw [mem_torsionBySet_iff]
  intro m
  let x' : a := ⟨x, hx⟩
  -- If `m • x' ≠ 0`, simplicity spans `a` by `m • x'`, forcing `1 - r * m` to kill `x' ≠ 0`.
  suffices h : (m : R) • x' = 0 from congrArg Subtype.val h
  by_contra hmx
  have htop : Submodule.span R {(m : R) • x'} = ⊤ :=
    (eq_bot_or_eq_top _).resolve_left (span_singleton_eq_bot.not.mpr hmx)
  obtain ⟨r, hr⟩ := mem_span_singleton.mp (htop.symm ▸ mem_top : x' ∈ _)
  have hunit : IsUnit (1 - r * (m : R)) := by
    refine notMem_maximalIdeal.mp fun hmem ↦
      (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    have hrm : r * (m : R) ∈ maximalIdeal R := (maximalIdeal R).mul_mem_left r m.prop
    simpa using add_mem hmem hrm
  have hzero : (1 - r * (m : R)) • x' = 0 := by
    rw [sub_smul, one_smul, mul_smul, hr, sub_self]
  exact hmx (by simp [hunit.smul_eq_zero.mp hzero])

namespace TauCeti

universe u v w

section IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {M : Type w} [AddCommGroup M] [Module R M]

variable (R M) in
/-- Over a commutative local ring, the submodule of elements killed by the maximal ideal is
essential in every Artinian module. -/
theorem isEssential_torsionBySet_maximalIdeal [IsArtinian R M] :
    IsEssential (torsionBySet R M (maximalIdeal R)) :=
  isEssential_of_forall_atom_le fun _ ha ↦ ha.le_torsionBySet_maximalIdeal

variable (R M) in
/-- The `𝔪`-torsion submodule of an Artinian module over a local ring is finitely generated over
`R ⧸ 𝔪`. -/
theorem finite_quotient_maximalIdeal_torsionBySet [IsArtinian R M] :
    Module.Finite (R ⧸ maximalIdeal R) (torsionBySet R M (maximalIdeal R)) := by
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  have : IsArtinian (R ⧸ maximalIdeal R) (torsionBySet R M (maximalIdeal R)) :=
    isArtinian_of_tower R inferInstance
  exact IsSemiprimaryRing.finite_of_isArtinian (R ⧸ maximalIdeal R) (R ⧸ maximalIdeal R) _

variable (R M) in
/-- The `𝔪`-torsion submodule of an Artinian module over a local ring is `R`-linearly isomorphic to
a finite power of the residue field. -/
theorem exists_torsionBySet_maximalIdeal_linearEquiv_pi [IsArtinian R M] :
    ∃ r : ℕ, Nonempty (torsionBySet R M (maximalIdeal R) ≃ₗ[R] (Fin r → ResidueField R)) := by
  classical
  let K := R ⧸ maximalIdeal R
  let : Field K := Ideal.Quotient.field (maximalIdeal R)
  have : Module.Finite K (torsionBySet R M (maximalIdeal R)) :=
    finite_quotient_maximalIdeal_torsionBySet R M
  let b := Module.Free.chooseBasis K (torsionBySet R M (maximalIdeal R))
  let eK : torsionBySet R M (maximalIdeal R) ≃ₗ[K]
      (Fin (Fintype.card (Module.Free.ChooseBasisIndex K _)) → K) :=
    b.equivFun.trans (LinearEquiv.piCongrLeft K (fun _ ↦ K) (Fintype.equivFin _))
  refine ⟨_, ⟨eK.restrictScalars R ≪≫ₗ
    LinearEquiv.piCongrRight fun _ ↦ quotientEquivResidueField (maximalIdeal.isMaximal R)⟩⟩

/-- Every Artinian module over a commutative local ring embeds into a finite power of any injective
module containing a copy of the residue field. No Noetherian hypothesis on the ring is needed. -/
theorem exists_injective_linearMap_pi_of_isArtinian [IsArtinian R M]
    {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R] [Module.Injective R E]
    {ι : ResidueField R →ₗ[R] E} (hι : Function.Injective ι) :
    ∃ (r : ℕ) (j : M →ₗ[R] (Fin r → E)), Function.Injective j := by
  obtain ⟨r, ⟨e₀⟩⟩ := exists_torsionBySet_maximalIdeal_linearEquiv_pi R M
  let S₀ := torsionBySet R M (maximalIdeal R)
  let g₀ : S₀ →ₗ[R] (Fin r → E) := (LinearMap.pi fun i ↦ ι ∘ₗ LinearMap.proj i) ∘ₗ e₀.toLinearMap
  have hg₀ : Function.Injective g₀ := fun x y hxy ↦
    e₀.injective (funext fun i ↦ hι (congrFun hxy i))
  obtain ⟨j, hj⟩ := Module.Injective.extension_property R (Fin r → E) S₀ M
    S₀.subtype S₀.injective_subtype g₀
  have hrange : IsEssential (LinearMap.range S₀.subtype) := by
    simpa [Submodule.range_subtype] using isEssential_torsionBySet_maximalIdeal R M
  exact ⟨r, j, hrange.injective_of_injective_comp (hj.symm ▸ hg₀)⟩

end IsLocalRing

section Noetherian

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {M : Type w} [AddCommGroup M] [Module R M] [IsArtinian R M]

variable (R M) in
/-- Over a Noetherian local ring, every Artinian module equals its maximal-ideal primary component:
each element is annihilated by some power of the maximal ideal. -/
theorem primaryComponent_maximalIdeal_eq_top_of_isArtinian :
    (maximalIdeal R).primaryComponent M = ⊤ := by
  apply (isEssential_torsionBySet_maximalIdeal R M).primaryComponent_eq_top
  intro x hx
  exact ((maximalIdeal R).primaryComponent_mem M x).mpr ⟨1, by simpa using hx⟩

/-- Every element of an Artinian module over a Noetherian local ring is annihilated by a power of
the maximal ideal. -/
theorem mem_primaryComponent_maximalIdeal_of_isArtinian (x : M) :
    x ∈ (maximalIdeal R).primaryComponent M :=
  primaryComponent_maximalIdeal_eq_top_of_isArtinian R M ▸ mem_top

end Noetherian

end TauCeti
