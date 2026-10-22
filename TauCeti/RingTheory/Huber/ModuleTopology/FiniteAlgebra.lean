/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.Basic
import Mathlib.Topology.Algebra.Algebra
import TauCeti.Algebra.Ring.Subgroup

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
(`TauCeti.Huber.PairOfDefinition.exists_pow_smul_le`), so `Iʲ • M₀ ⊆ B₀` and `B₀` is open.
With the extension `J` of `I` to `B₀`, one gets `I^(n + j) • M₀ ⊆ Jⁿ ⊆ Iⁿ • M₀`, the second
inclusion because `1 ∈ M₀` and `B₀ M₀ ⊆ M₀`. So the topology of `B₀` is the `J`-adic one and
`(B₀, J)` is a pair of definition of `B`. When `A` is Tate, the image of a pseudouniformiser of
`A` is one of `B`.

## Main results

* `TauCeti.Huber.IsHuberRing.of_isModuleTopology`: a finite algebra over a Huber ring, with its
  natural topology, is a Huber ring.
* `TauCeti.Huber.IsTateRing.of_isModuleTopology`: a finite algebra over a Tate ring, with its
  natural topology, is a Tate ring.

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

/-! ### The multiplier ring of a lattice -/

/-- The image of `A₀` lies in the multiplier ring. -/
private theorem algebraMap_mem_multiplierRing (P : PairOfDefinition A)
    (M₀ : Submodule P.ringOfDefinition B) (a : P.ringOfDefinition) :
    algebraMap P.ringOfDefinition B a ∈ M₀.toAddSubgroup.multiplierRing := by
  refine AddSubgroup.mem_multiplierRing.mpr fun m hm ↦ ?_
  rw [← Algebra.smul_def]
  exact M₀.smul_mem a hm

/-- If `Iʲ` carries `M₀ * M₀` into `M₀`, then `Iʲ • M₀` lies in the multiplier ring. -/
private theorem smul_subset_multiplierRing (P : PairOfDefinition A)
    {M₀ : Submodule P.ringOfDefinition B} {j : ℕ} (hj : P.idealOfDefinition ^ j • (M₀ * M₀) ≤ M₀) :
    ((P.idealOfDefinition ^ j • M₀ : Submodule P.ringOfDefinition B) : Set B) ⊆
      M₀.toAddSubgroup.multiplierRing := fun x hx ↦ by
  refine Submodule.smul_induction_on hx (fun t ht n hn ↦ ?_) fun x y hx hy ↦ ?_
  · refine AddSubgroup.mem_multiplierRing.mpr fun m hm ↦ ?_
    rw [smul_mul_assoc]
    exact hj (Submodule.smul_mem_smul ht (Submodule.mul_mem_mul hn hm))
  · exact M₀.toAddSubgroup.multiplierRing.add_mem hx hy

/-! ### The ideal of definition of the multiplier ring -/

/-- The structure map `A₀ → B₀` into the multiplier ring. -/
private noncomputable def toMultiplierRing (P : PairOfDefinition A)
    (M₀ : Submodule P.ringOfDefinition B) :
    P.ringOfDefinition →+* M₀.toAddSubgroup.multiplierRing :=
  (algebraMap P.ringOfDefinition B).codRestrict _ (algebraMap_mem_multiplierRing P M₀)

/-- The structure map `A₀ → B₀` sends `a` to `a • 1`. -/
private theorem coe_toMultiplierRing (P : PairOfDefinition A) (M₀ : Submodule P.ringOfDefinition B)
    (a : P.ringOfDefinition) : (toMultiplierRing P M₀ a : B) = a • (1 : B) := by
  rw [toMultiplierRing, RingHom.codRestrict_apply, Algebra.smul_def, mul_one]

/-- The powers of the extended ideal `J = I B₀` lie in `Iⁿ • M₀` when `1 ∈ M₀`. -/
private theorem coe_map_pow_subset (P : PairOfDefinition A) {M₀ : Submodule P.ringOfDefinition B}
    (h1 : (1 : B) ∈ M₀) (n : ℕ) :
    Subtype.val '' ((P.idealOfDefinition.map (toMultiplierRing P M₀) ^ n :
      Ideal M₀.toAddSubgroup.multiplierRing) : Set M₀.toAddSubgroup.multiplierRing) ⊆
        ((P.idealOfDefinition ^ n • M₀ : Submodule P.ringOfDefinition B) : Set B) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, ← Ideal.map_pow] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    rw [SetLike.mem_coe, coe_toMultiplierRing]
    exact Submodule.smul_mem_smul ha h1
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [smul_eq_mul, Subring.coe_mul]
    refine Submodule.smul_induction_on' hy (fun t ht m hm ↦ ?_) fun _ _ _ _ h₁ h₂ ↦ ?_
    · rw [mul_smul_comm]
      exact Submodule.smul_mem_smul ht (AddSubgroup.mem_multiplierRing.mp r.2 m hm)
    · rw [mul_add]
      exact Submodule.add_mem _ h₁ h₂

/-- If `Iʲ • M₀` lies in the multiplier ring, then `I^(n + j) • M₀` lies in the `n`-th power of the
extended ideal `J = I B₀`. -/
private theorem smul_subset_coe_map_pow (P : PairOfDefinition A)
    {M₀ : Submodule P.ringOfDefinition B} {j : ℕ}
    (hj : ((P.idealOfDefinition ^ j • M₀ : Submodule P.ringOfDefinition B) : Set B) ⊆
      M₀.toAddSubgroup.multiplierRing) (n : ℕ) :
    ((P.idealOfDefinition ^ (n + j) • M₀ : Submodule P.ringOfDefinition B) : Set B) ⊆
      Subtype.val '' ((P.idealOfDefinition.map (toMultiplierRing P M₀) ^ n :
        Ideal M₀.toAddSubgroup.multiplierRing) : Set M₀.toAddSubgroup.multiplierRing) := by
  intro x hx
  rw [pow_add, Submodule.mul_smul] at hx
  refine Submodule.smul_induction_on hx (fun a ha y hy ↦ ?_) ?_
  · refine ⟨toMultiplierRing P M₀ a * ⟨y, hj hy⟩, ?_, ?_⟩
    · rw [← Ideal.map_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    · rw [Subring.coe_mul, coe_toMultiplierRing, smul_one_mul]
  · rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, Ideal.add_mem _ hx hy, rfl⟩

/-! ### The pair of definition -/

variable [IsTopologicalRing A] [TopologicalSpace B] [IsModuleTopology A B] [Module.Finite A B]

/-- **A finite algebra over a Huber ring has a pair of definition**, given by the multiplier ring of
a finitely generated spanning lattice containing `1` and the extension of `I` to it. -/
private theorem nonempty_pairOfDefinition (P : PairOfDefinition A) :
    haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
    Nonempty (PairOfDefinition B) := by
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
  have hjB₀ := smul_subset_multiplierRing P hj
  set B₀ := M₀.toAddSubgroup.multiplierRing
  set J := P.idealOfDefinition.map (toMultiplierRing P M₀)
  refine ⟨{ ringOfDefinition := B₀
            isOpen_ringOfDefinition := B₀.toAddSubgroup.isOpen_of_mem_nhds
              (mem_of_superset (hbasis.mem_of_mem (i := j) trivial) hjB₀)
            idealOfDefinition := J
            fg_idealOfDefinition := P.fg_idealOfDefinition.map _
            isAdic_idealOfDefinition := isAdic_iff.mpr ⟨fun n ↦ ?_, fun U hU ↦ ?_⟩ }⟩
  · -- `Jⁿ` contains the neighbourhood `I^(n + j) • M₀` of `0`
    refine (J ^ n).toAddSubgroup.isOpen_of_mem_nhds (g := 0) ?_
    have hmem := continuous_subtype_val.continuousAt.preimage_mem_nhds
      (hbasis.mem_of_mem (i := n + j) trivial) (x := (0 : B₀))
    refine mem_of_superset hmem fun x hx ↦ ?_
    obtain ⟨y, hy, hxy⟩ := smul_subset_coe_map_pow P hjB₀ n hx
    rwa [← Subtype.ext hxy]
  · -- `Jⁿ` lies in `Iⁿ • M₀`, which lies in any given neighbourhood of `0` for large `n`
    rw [nhds_induced, mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨n, -, hn⟩ := hbasis.mem_iff.mp hV
    exact ⟨n, fun x hx ↦ hVU (hn (coe_map_pow_subset P h1 n ⟨x, hx, rfl⟩))⟩

end PairOfDefinition

variable [IsTopologicalRing A] [TopologicalSpace B] [IsModuleTopology A B] [Module.Finite A B]

/-- **A finite algebra over a Huber ring is a Huber ring.** If `B` is a commutative `A`-algebra,
finite as an `A`-module and carrying its natural topology, then `B` is a Huber ring. -/
theorem IsHuberRing.of_isModuleTopology [IsHuberRing A] :
    haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
    IsHuberRing B :=
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
  ⟨IsHuberRing.nonempty_pairOfDefinition.elim fun P : PairOfDefinition A ↦
    P.nonempty_pairOfDefinition (B := B)⟩

/-- **A finite algebra over a Tate ring is a Tate ring.** If `B` is a commutative `A`-algebra,
finite as an `A`-module and carrying its natural topology, then `B` is a Tate ring; the image of a
pseudouniformiser of `A` is a pseudouniformiser of `B`. -/
theorem IsTateRing.of_isModuleTopology [IsTateRing A] :
    haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
    IsTateRing B :=
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
  haveI : IsHuberRing B := IsHuberRing.of_isModuleTopology (A := A)
  IsTateRing.of_continuous (A := A) (φ := algebraMap A B) (continuous_algebraMap A B)

end TauCeti.Huber

end
