/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.Topology.Algebra.ContinuousZModDual
public import TauCeti.Topology.Algebra.Group.Profinite.MazurFiniteness
import TauCeti.Algebra.Module.ZMod.Dual
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Uniform vanishing of cocycles of bounded exponent

Let `G` be a topological group, `U` an open subgroup of finite index and `m ≠ 0`, and suppose that
`U` has only finitely many continuous homomorphisms to `ℤ/m`. Then there is **one** open normal
subgroup `N ≤ U` of `G` on which every continuous `1`-cocycle of `G` vanishes, for every discrete
`G`-module `B` killed by `m` on which `U` acts trivially. Such a cocycle is then constant on the
cosets `g N`, so it is determined by a function on the finite group `G ⧸ N`. The point is that
`N` depends on `U` and `m` only, not on `B` or on the cocycle.

For a profinite group every open subgroup has finite index, and the finiteness hypothesis holds
for every open `U` under Mazur's condition `Φ_m` (`TauCeti.MazurFiniteness`). For the Galois group
`G_{K,S}` of a number field `K` unramified outside a finite set `S` it is a consequence of
Hermite's theorem; see
`TauCeti.NumberTheory.NumberField.RestrictedRamification.UniformVanishing`.

The proof: a cocycle `f` restricts to a continuous homomorphism on `U`, since `U` acts trivially.
Let `W` be the common kernel of the finitely many continuous homomorphisms `U → ℤ/m`, an open
normal subgroup of `U`, and `N ≤ W` an open normal subgroup of `G`
(`OpenNormalSubgroup.exists_le_map_subtype`). For `g ∈ N` and any homomorphism `φ : B → ℤ/m`,
`φ ∘ f` is a continuous homomorphism `U → ℤ/m`, so it vanishes at `g`; as the homomorphisms to
`ℤ/m` separate the points of a group killed by `m`
(`TauCeti.exists_addMonoidHom_zmod_apply_ne_zero`), `f g = 0`.

## Main results

* `TauCeti.exists_openNormalSubgroup_forall_apply_eq_zero`: one open normal subgroup `N ≤ U` on
  which every continuous function `G → B`, additive on `U`, with values in a discrete group killed
  by `m`, vanishes.
* `TauCeti.ContCohomology.exists_openNormalSubgroup_forall_mem_Z1`: the same for continuous
  `1`-cocycles with values in discrete `G`-modules killed by `m` on which `U` acts trivially; each
  of them vanishes on `N` and is constant on the cosets of `N`.
* `TauCeti.MazurFiniteness.exists_openNormalSubgroup_forall_mem_Z1`: the same under Mazur's
  condition `Φ_m` on a profinite group, for every open subgroup `U`.

## Provenance

The uniformity argument is adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0,
Copyright 2026 Anthropic, PBC), file `src/New/Congruences/Selmer/OneSystem.lean`, declarations
`New.Selmer.exists_openNormalSubgroup_forall_eq_zero` and
`New.Selmer.eq_zero_of_forall_hom_zmod_eq_zero`. There it is stated for `Gal(Ω/E)` and cocycles
unramified outside `S`, with the finiteness of the cocycles as input; here the finiteness of the
continuous `ℤ/m`-dual of `U` is the only input.
-/

public section

namespace TauCeti

universe u v

namespace ContCohomology

section Cocycle

variable {G : Type u} [Monoid G] [TopologicalSpace G]

/-- A `1`-cocycle that vanishes at `n` satisfies `f (g * n) = f g` for every `g`. -/
theorem apply_mul_eq_of_mem_Z1 {B : Type v} [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [DistribMulAction G B] {f : G → B} (hf : f ∈ Z1 G B) (g : G) {n : G}
    (hn : f n = 0) : f (g * n) = f g := by
  have h : f (g * n) = g • f n + f g := (mem_Z1_iff.1 hf).2 g n
  rw [h, hn, smul_zero, zero_add]

end Cocycle

end ContCohomology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The common kernel in `U` of the continuous homomorphisms `U → ℤ/m`, when there are finitely
many of them: an open normal subgroup of `U`. -/
private def zmodDualKernel (U : Subgroup G) (m : ℕ) [Finite (continuousZModDual m U)] :
    OpenNormalSubgroup U where
  toSubgroup := ⨅ χ : continuousZModDual m U, (χ.toMul : U →* Multiplicative (ZMod m)).ker
  isOpen' := by
    change IsOpen ((⨅ χ : continuousZModDual m U,
      (χ.toMul : U →* Multiplicative (ZMod m)).ker : Subgroup U) : Set U)
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun χ ↦ (isOpen_discrete {1}).preimage χ.toMul.continuous
  isNormal' := Subgroup.normal_iInf_normal fun χ ↦ MonoidHom.normal_ker _

/-- A continuous function `G → B` into a discrete group, additive on `U`, followed by a
homomorphism `φ : B → ℤ/m`, as a continuous character of `U`. -/
private def toZModDual {U : Subgroup G} {m : ℕ} {B : Type v} [AddCommGroup B] [TopologicalSpace B]
    [DiscreteTopology B] (φ : B →+ ZMod m) (f : G → B) (hf : Continuous f)
    (hadd : ∀ g ∈ U, ∀ h ∈ U, f (g * h) = f g + f h) : continuousZModDual m U :=
  Additive.ofMul
    { toFun u := Multiplicative.ofAdd (φ (f u))
      map_one' := by
        have h := hadd 1 U.one_mem 1 U.one_mem
        rw [mul_one, left_eq_add] at h
        simp [h]
      map_mul' u w := by simp [hadd u u.property w w.property, ofAdd_add]
      continuous_toFun := continuous_ofAdd.comp
        ((continuous_of_discreteTopology (f := φ)).comp (hf.comp continuous_subtypeVal)) }

/-- **Uniform vanishing of homomorphisms of bounded exponent.** Let `U` be an open subgroup of
finite index of `G` with only finitely many continuous homomorphisms to `ℤ/m`, `m ≠ 0`. There is
an open normal subgroup `N ≤ U` of `G` such that every continuous function `f : G → B` that is
additive on `U`, with values in a discrete group `B` killed by `m`, vanishes on `N`. -/
theorem exists_openNormalSubgroup_forall_apply_eq_zero {U : Subgroup G} (hU : IsOpen (U : Set G))
    [U.FiniteIndex] (m : ℕ) [NeZero m] [Finite (continuousZModDual m U)] :
    ∃ N : OpenNormalSubgroup G, N.toSubgroup ≤ U ∧
      ∀ (B : Type v) [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B],
        (∀ b : B, m • b = 0) → ∀ f : G → B, Continuous f →
          (∀ g ∈ U, ∀ h ∈ U, f (g * h) = f g + f h) → ∀ g ∈ N, f g = 0 := by
  obtain ⟨N, hN⟩ := OpenNormalSubgroup.exists_le_map_subtype hU (zmodDualKernel U m)
  refine ⟨N, hN.trans (Subgroup.map_subtype_le _), fun B _ _ _ hB f hf hadd g hg ↦ ?_⟩
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 (hN hg)
  by_contra h
  obtain ⟨φ, hφ⟩ := exists_addMonoidHom_zmod_apply_ne_zero hB h
  -- `φ ∘ f` is a continuous character of `U`, so it vanishes on the common kernel
  have := Subgroup.mem_iInf.1 hu (toZModDual φ f hf hadd)
  exact hφ (by simpa [toZModDual] using this)

namespace ContCohomology

/-- **Uniform vanishing of cocycles of bounded exponent.** Let `U` be an open subgroup of finite
index of `G` with only finitely many continuous homomorphisms to `ℤ/m`, `m ≠ 0`. There is one open
normal subgroup `N ≤ U` of `G` such that, for every discrete `G`-module `B` killed by `m` on which
`U` acts trivially, every continuous `1`-cocycle `f : G → B` vanishes on `N`, and so satisfies
`f (g * n) = f g` for all `g : G` and `n ∈ N`. -/
theorem exists_openNormalSubgroup_forall_mem_Z1 {U : Subgroup G} (hU : IsOpen (U : Set G))
    [U.FiniteIndex] (m : ℕ) [NeZero m] [Finite (continuousZModDual m U)] :
    ∃ N : OpenNormalSubgroup G, N.toSubgroup ≤ U ∧
      ∀ (B : Type v) [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
        [DistribMulAction G B], (∀ b : B, m • b = 0) → (∀ u ∈ U, ∀ b : B, u • b = b) →
          ∀ f ∈ Z1 G B, ∀ n ∈ N, f n = 0 ∧ ∀ g, f (g * n) = f g := by
  obtain ⟨N, hNU, hN⟩ := exists_openNormalSubgroup_forall_apply_eq_zero.{u, v} hU m
  refine ⟨N, hNU, fun B _ _ _ _ hB hU f hf n hn ↦ ?_⟩
  have hfn : f n = 0 := hN B hB f (mem_Z1_iff.1 hf).1
    (fun g hg h _ ↦ map_mul_of_smul_eq_self_of_mem_Z1 hf (hU g hg) h) n hn
  exact ⟨hfn, fun g ↦ apply_mul_eq_of_mem_Z1 hf g hfn⟩

end ContCohomology

/-- **Uniform vanishing of cocycles under Mazur's condition.** Let `G` be a compact group
satisfying `Φ_m` for some `m ≠ 0`: every open subgroup has finitely many continuous homomorphisms
to `ℤ/m`. For every open subgroup `U` there is one open normal subgroup `N ≤ U` on which every
continuous `1`-cocycle with values in a discrete `G`-module killed by `m` and fixed by `U`
vanishes; such a cocycle is constant on the cosets of `N`. -/
theorem MazurFiniteness.exists_openNormalSubgroup_forall_mem_Z1 [CompactSpace G] {m : ℕ}
    [NeZero m] (hG : MazurFiniteness m G) (U : OpenSubgroup G) :
    ∃ N : OpenNormalSubgroup G, N.toSubgroup ≤ U ∧
      ∀ (B : Type v) [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
        [DistribMulAction G B], (∀ b : B, m • b = 0) → (∀ u ∈ U, ∀ b : B, u • b = b) →
          ∀ f ∈ ContCohomology.Z1 G B, ∀ n ∈ N, f n = 0 ∧ ∀ g, f (g * n) = f g :=
  have := mazurFiniteness_iff_forall_finite.1 hG U
  ContCohomology.exists_openNormalSubgroup_forall_mem_Z1 (U := U.toSubgroup) U.isOpen m

end TauCeti
