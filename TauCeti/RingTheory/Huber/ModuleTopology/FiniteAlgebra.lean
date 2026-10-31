/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.Basic
public import TauCeti.RingTheory.Huber.PowerBounded
public import TauCeti.Topology.Algebra.Ring.Subring
import Mathlib.Topology.Algebra.Algebra
import TauCeti.Algebra.Module.Submodule.MultiplierRing
import TauCeti.RingTheory.Huber.RingOfDefinition

/-!
# Finite algebras over a Huber ring

Let `A` be a Huber ring and `B` a commutative `A`-algebra that is finite as an `A`-module, with
its natural topology (`IsModuleTopology A B`). Then `B` is a topological ring
(`IsModuleTopology.isTopologicalRing`), and this file shows that it is again a Huber ring, and a
Tate ring when `A` is. No completeness, noetherian, flatness or separatedness hypothesis is
needed. This is how a finite étale algebra over a complete Tate ring becomes a Tate ring, the first
step in making it a Huber pair over `(A, A⁺)`.

Fix a pair of definition `(A₀, I)` of `A` and a finitely generated `A₀`-submodule `M₀ ⊆ B`
containing `1` and spanning `B` over `A`. The submodules `Iⁿ • M₀` are a neighbourhood basis of
`0` (`TauCeti.Huber.PairOfDefinition.hasBasis_nhds_zero_idealOfDefinition_pow_smul`). The
*multiplier ring* `B₀ = {b ∈ B | b M₀ ⊆ M₀}` is a subring of `B` (`AddSubgroup.multiplierRing`).
Since `M₀ * M₀` is finitely generated, a power `Iʲ` carries it into `M₀`
(`TauCeti.Huber.PairOfDefinition.exists_pow_smul_le`), so `Iʲ • M₀ ⊆ B₀`
(`Submodule.smul_subset_multiplierRing`) and `B₀` is open. With the extension `J` of `I` to
`B₀`, one gets `I^(n + j) • M₀ ⊆ Jⁿ ⊆ Iⁿ • M₀` (`Submodule.smul_subset_coe_map_pow`,
`Submodule.coe_map_pow_subset`), the second inclusion because `1 ∈ M₀` and `B₀ M₀ ⊆ M₀`. So the
topology of `B₀` is the `J`-adic one and `(B₀, J)` is a pair of definition of `B`. When `A` is
Tate, the image of a pseudouniformiser of `A` is one of `B`.

## Main results

* `TauCeti.Huber.PairOfDefinition.exists_pairOfDefinition_isIntegral`: every pair of definition
  `(A₀, I)` of `A` gives a pair of definition of `B` whose ring of definition contains the image
  of `A₀` and is integral over `A₀`.
* `TauCeti.Huber.IsHuberRing.of_isModuleTopology`: a finite algebra over a Huber ring, with its
  natural topology, is a Huber ring.
* `TauCeti.Huber.IsTateRing.of_isModuleTopology`: a finite algebra over a Tate ring, with its
  natural topology, is a Tate ring.
* `TauCeti.Huber.IsPowerBounded.algebraMap_of_isModuleTopology`: the structure map `A → B`
  preserves power-boundedness.
* `TauCeti.Huber.isOpen_integralClosure_map_algebraMap`: the integral closure in `B` of the image
  of an open subring of `A` is open.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, before Lemma 2.3.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.2, Lemma 2.2.12, and §2.4, Remark 2.4.2.
-/

public section

open Filter Topology Pointwise

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] {B : Type*} [CommRing B] [Algebra A B]

namespace PairOfDefinition

/-! ### The pair of definition -/

variable [IsTopologicalRing A] [TopologicalSpace B] [IsModuleTopology A B] [Module.Finite A B]

/-- **Pairs of definition of a finite algebra.** For every pair of definition `(A₀, I)` of `A`, a
finite `A`-algebra `B` with its natural topology has a pair of definition `(B₀, J)` whose ring of
definition contains the image of `A₀` and is integral over `A₀`. It is the multiplier ring of a
finitely generated spanning lattice containing `1`, with the extension of `I` to it. -/
theorem exists_pairOfDefinition_isIntegral (P : PairOfDefinition A) :
    ∃ Q : PairOfDefinition B,
      (∀ a ∈ P.ringOfDefinition, algebraMap A B a ∈ Q.ringOfDefinition) ∧
        ∀ b ∈ Q.ringOfDefinition, IsIntegral P.ringOfDefinition b := by
  have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
  -- the lattice `M₀`: the `A₀`-span of `1` and a finite set spanning `B` over `A`
  set T : Set B := insert 1 (s : Set B)
  have hT : T.Finite := (s.finite_toSet.insert 1)
  set M₀ : Submodule P.ringOfDefinition B := Submodule.span P.ringOfDefinition T
  have h1 : (1 : B) ∈ M₀ := Submodule.subset_span (Set.mem_insert 1 _)
  have hspan : Submodule.span A (M₀ : Set B) = ⊤ := by
    rw [Submodule.span_span_of_tower, eq_top_iff, ← hs]
    exact Submodule.span_mono (Set.subset_insert 1 _)
  have hbasis := P.hasBasis_nhds_zero_idealOfDefinition_pow_smul (Submodule.fg_span hT) hspan
  -- a power of `I` carries `M₀ * M₀` into `M₀`, so `Iʲ • M₀ ⊆ B₀`
  have hfg : (M₀ * M₀).FG := by
    rw [Submodule.span_mul_span]
    exact Submodule.fg_span (hT.mul hT)
  obtain ⟨j, hj⟩ := P.exists_pow_smul_le M₀ hfg (by simp [hspan])
  have hjB₀ := Submodule.smul_subset_multiplierRing hj
  set B₀ := M₀.toAddSubgroup.multiplierRing
  set J := P.idealOfDefinition.map M₀.toMultiplierRing
  refine ⟨{ ringOfDefinition := B₀
            isOpen_ringOfDefinition := B₀.toAddSubgroup.isOpen_of_mem_nhds
              (mem_of_superset (hbasis.mem_of_mem (i := j) trivial) hjB₀)
            idealOfDefinition := J
            fg_idealOfDefinition := P.fg_idealOfDefinition.map _
            isAdic_idealOfDefinition := isAdic_iff.mpr ⟨fun n ↦ ?_, fun U hU ↦ ?_⟩ },
    fun a ha ↦ M₀.algebraMap_mem_multiplierRing ⟨a, ha⟩,
    fun b hb ↦ Submodule.isIntegral_of_mem_multiplierRing (Submodule.fg_span hT) h1 hb⟩
  · -- `Jⁿ` contains the neighbourhood `I^(n + j) • M₀` of `0`
    refine (J ^ n).toAddSubgroup.isOpen_of_mem_nhds (g := 0) ?_
    have hmem := continuous_subtype_val.continuousAt.preimage_mem_nhds
      (hbasis.mem_of_mem (i := n + j) trivial) (x := (0 : B₀))
    refine mem_of_superset hmem fun x hx ↦ ?_
    obtain ⟨y, hy, hxy⟩ := Submodule.smul_subset_coe_map_pow hjB₀ n hx
    rwa [← Subtype.ext hxy]
  · -- `Jⁿ` lies in `Iⁿ • M₀`, which lies in any given neighbourhood of `0` for large `n`
    rw [nhds_induced, mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨n, -, hn⟩ := hbasis.mem_iff.mp hV
    exact ⟨n, fun x hx ↦ hVU (hn (Submodule.coe_map_pow_subset h1 _ n ⟨x, hx, rfl⟩))⟩

end PairOfDefinition

variable [IsTopologicalRing A] [TopologicalSpace B] [IsModuleTopology A B] [Module.Finite A B]

/-- **A finite algebra over a Huber ring is a Huber ring.** If `B` is a commutative `A`-algebra,
finite as an `A`-module and carrying its natural topology, then `B` is a Huber ring. -/
theorem IsHuberRing.of_isModuleTopology [IsHuberRing A] :
    haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
    IsHuberRing B :=
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
  ⟨IsHuberRing.nonempty_pairOfDefinition.elim fun P : PairOfDefinition A ↦
    let ⟨Q, _⟩ := P.exists_pairOfDefinition_isIntegral (B := B); ⟨Q⟩⟩

/-- **A finite algebra over a Tate ring is a Tate ring.** If `B` is a commutative `A`-algebra,
finite as an `A`-module and carrying its natural topology, then `B` is a Tate ring; the image of a
pseudouniformiser of `A` is a pseudouniformiser of `B`. -/
theorem IsTateRing.of_isModuleTopology [IsTateRing A] :
    haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
    IsTateRing B :=
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
  haveI : IsHuberRing B := IsHuberRing.of_isModuleTopology (A := A)
  IsTateRing.of_continuous (A := A) (φ := algebraMap A B) (continuous_algebraMap A B)

/-! ### Power-bounded and integral elements -/

/-- **The structure map of a finite algebra preserves power-boundedness.** A power-bounded `a`
lies in a ring of definition `A₀` of `A`, and `algebraMap A B` carries `A₀` into a ring of
definition of `B`. -/
theorem IsPowerBounded.algebraMap_of_isModuleTopology [IsHuberRing A] {a : A}
    (ha : IsPowerBounded a) : IsPowerBounded (algebraMap A B a) := by
  have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
  have : IsHuberRing B := IsHuberRing.of_isModuleTopology (A := A)
  obtain ⟨P, haP⟩ := isPowerBounded_iff_exists_mem_ringOfDefinition.mp ha
  obtain ⟨Q, hQ, -⟩ := P.exists_pairOfDefinition_isIntegral (B := B)
  exact isPowerBounded_iff_exists_mem_ringOfDefinition.mpr ⟨Q, hQ a haP⟩

/-- **The integral closure of the image of an open subring is open.** If `C` is an open subring
of a Huber ring `A`, the integral closure of its image in a finite `A`-algebra `B` with its natural
topology is open: it contains a ring of definition of `B` that is integral over a ring of
definition `A₀ ⊆ C` of `A`. -/
theorem isOpen_integralClosure_map_algebraMap [IsHuberRing A] {C : Subring A}
    (hC : IsOpen (C : Set A)) :
    IsOpen ((integralClosure (C.map (algebraMap A B)) B).toSubring : Set B) := by
  have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
  obtain ⟨P, hP⟩ := exists_pairOfDefinition_ringOfDefinition_le hC
  obtain ⟨Q, -, hQ⟩ := P.exists_pairOfDefinition_isIntegral (B := B)
  refine AddSubgroup.isOpen_mono (H₁ := Q.ringOfDefinition.toAddSubgroup)
    (H₂ := (integralClosure (C.map (algebraMap A B)) B).toSubring.toAddSubgroup)
    (fun b hb ↦ ?_) Q.isOpen_ringOfDefinition
  -- `b` is integral over `A₀`, hence over the image of `C ⊇ A₀`
  let φ : P.ringOfDefinition →+* C.map (algebraMap A B) :=
    ((algebraMap A B).comp P.ringOfDefinition.subtype).codRestrict _
      fun a ↦ Subring.mem_map.mpr ⟨a, hP a.2, rfl⟩
  exact (hQ b hb).map_of_comp_eq φ (RingHom.id B) (RingHom.ext fun _ ↦ rfl)

end TauCeti.Huber

end
