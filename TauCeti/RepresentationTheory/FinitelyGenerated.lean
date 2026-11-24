/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Stabilizer
import TauCeti.RepresentationTheory.OfMulAction.CosetLift
import TauCeti.RepresentationTheory.Rep.DirectSum.AsModule

/-!
# Finitely generated representations

A representation `ρ` of a monoid `G` on an `A`-module `V` is *finitely generated* when `V` is a
finitely generated module over the group algebra `A[G]`, that is
`Module.Finite A[G] ρ.asModule`. This file proves that finite generation passes to quotients and
to finite direct sums, and that a permutation representation `A[X]` with finitely many orbits,
such as `A[G ⧸ U]` on the cosets of a subgroup, is finitely generated. Conversely, generators
`v_i` of a finitely generated representation give a surjection from `⊕_{i < n} A[G ⧸ U_i]`
through the coset lifts `g U_i ↦ ρ g v_i` (`Representation.cosetLift`), for any subgroups `U_i`
fixing `v_i`.

## Main results

* `Representation.finite_asModule_of_surjective`: finite generation passes to quotients.
* `Representation.finite_asModule_directSum`: a finite direct sum of finitely generated
  representations is finitely generated.
* `Representation.finite_asModule_ofMulAction`: a permutation representation `A[X]` with finitely
  many `G`-orbits on `X` is finitely generated; in particular so is `A[G ⧸ U]`.
* `Representation.exists_surjective_of_finite_asModule`: a finitely generated representation
  whose vectors are fixed by subgroups satisfying `P` is a quotient of `⊕_{i < n} A[G ⧸ U_i]`
  with each `U_i` satisfying `P`.
-/

public section

open scoped MonoidAlgebra

namespace Representation

variable {A G V W : Type*} [CommSemiring A] [Monoid G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

/-- **Finite generation passes to quotients.** -/
theorem finite_asModule_of_surjective [Module.Finite A[G] ρ.asModule] (f : IntertwiningMap ρ σ)
    (hf : Function.Surjective f) : Module.Finite A[G] σ.asModule :=
  Module.Finite.of_surjective (IntertwiningMap.equivLinearMapAsModule ρ σ f)
    ((IntertwiningMap.equivLinearMapAsModule_surjective_iff f).2 hf)

/-- A finite direct sum of finitely generated representations is finitely generated. -/
instance finite_asModule_directSum {ι : Type*} [Finite ι] {V' : ι → Type*}
    [∀ i, AddCommMonoid (V' i)] [∀ i, Module A (V' i)] (ρ' : ∀ i, Representation A G (V' i))
    [∀ i, Module.Finite A[G] (ρ' i).asModule] : Module.Finite A[G] (directSum ρ').asModule :=
  Module.Finite.equiv (directSumAsModuleEquiv ρ').symm

/-- **A permutation representation with finitely many orbits is finitely generated**: `A[X]` is
generated over `A[G]` by the basis vectors of one point in each `G`-orbit of `X`. -/
instance finite_asModule_ofMulAction {G X : Type*} [Group G] [MulAction G X]
    [Finite (MulAction.orbitRel.Quotient G X)] :
    Module.Finite A[G] (ofMulAction A G X).asModule := by
  set τ := ofMulAction A G X
  set S := Set.range fun q : MulAction.orbitRel.Quotient G X ↦
    τ.asModuleEquiv.symm (MonoidAlgebra.single q.out 1)
  refine ⟨Submodule.fg_def.2 ⟨S, Set.finite_range _, ?_⟩⟩
  suffices h : ∀ y, τ.asModuleEquiv.symm y ∈ Submodule.span A[G] S from
    eq_top_iff.2 fun x _ ↦ by
      have := h (τ.asModuleEquiv x)
      rwa [LinearEquiv.symm_apply_apply] at this
  intro y
  induction y using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add y z hy hz => rw [map_add]; exact add_mem hy hz
  | single x c =>
    obtain ⟨g, hg⟩ : ∃ g : G, g • (Quotient.mk (MulAction.orbitRel G X) x).out = x :=
      MulAction.mem_orbit_iff.1
        (MulAction.orbitRel_apply.1 ((MulAction.orbitRel G X).symm (Quotient.mk_out x)))
    have hx : MonoidAlgebra.single x c =
        c • τ g (MonoidAlgebra.single (Quotient.mk (MulAction.orbitRel G X) x).out 1) := by
      simp [τ, ofMulAction_single, MonoidAlgebra.smul_single, hg]
    rw [hx, asModuleEquiv_symm_map_smul, asModuleEquiv_symm_map_rho]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

/-- A permutation representation `A[G ⧸ U]` on cosets is finitely generated, `G` acting
transitively on `G ⧸ U`. -/
instance finite_asModule_ofMulAction_quotient {G : Type*} [Group G] (U : Subgroup G) :
    Module.Finite A[G] (ofMulAction A G (G ⧸ U)).asModule :=
  have := (MulAction.pretransitive_iff_subsingleton_quotient G (G ⧸ U)).1 inferInstance
  inferInstance

/-- **Generators give a surjection from permutation representations.** If `V` is finitely
generated and every vector is fixed by a subgroup satisfying `P`, then `V` is a quotient of
`⊕_{i < n} A[G ⧸ U_i]` for subgroups `U_i` satisfying `P`. -/
theorem exists_surjective_of_finite_asModule {G : Type*} [Group G] {ρ : Representation A G V}
    [Module.Finite A[G] ρ.asModule] {P : Subgroup G → Prop}
    (hP : ∀ v : V, ∃ U : Subgroup G, P U ∧ U ≤ ρ.stabilizer v) :
    ∃ (n : ℕ) (U : Fin n → Subgroup G), (∀ i, P (U i)) ∧
      ∃ f : IntertwiningMap (directSum fun i ↦ ofMulAction A G (G ⧸ U i)) ρ,
        Function.Surjective f := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A[G]) (M := ρ.asModule)
  choose U hPU hU using fun i : Fin n ↦ hP (ρ.asModuleEquiv (s i))
  let f := IntertwiningMap.directSumToModule fun i ↦ ρ.cosetLift _ _ (hU i)
  refine ⟨n, U, hPU, f, (IntertwiningMap.equivLinearMapAsModule_surjective_iff f).1 ?_⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine ⟨(directSum _).asModuleEquiv.symm
    (DirectSum.lof A _ _ i (MonoidAlgebra.single ((1 : G) : G ⧸ U i) 1)), ?_⟩
  apply ρ.asModuleEquiv.injective
  rw [asModuleEquiv_apply, asModuleEquiv_apply, IntertwiningMap.equivLinearMapAsModule_apply,
    asModuleEquiv_symm_apply]
  simp only [f, IntertwiningMap.directSumToModule_lof, cosetLift_single, map_one, one_smul,
    one_apply_eq_self]
  exact asModuleEquiv_apply (s i)

end Representation
