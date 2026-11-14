/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Ring.Compact
public import TauCeti.Topology.Algebra.Module.Compact
import Mathlib.RingTheory.Filtration
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.UniformSpace.Cauchy
import TauCeti.Topology.Algebra.Module.Nakayama

/-!
# The topology of a compact Hausdorff noetherian local ring is adic

Let `R` be a compact Hausdorff noetherian local ring with maximal ideal `m`, for instance the
valuation ring of a nonarchimedean local field or a complete noetherian local ring with finite
residue field and its `m`-adic topology. Mathlib shows that every power `m ^ n` is open
(`IsLocalRing.isOpen_maximalIdeal_pow`). Conversely, the powers `m ^ n` are compact, they decrease,
and they meet only in `0` by the Krull intersection theorem, so every neighbourhood of `0`
contains one of them. Hence the topology of `R` is its `m`-adic topology, with no completeness
or discreteness hypothesis. This identifies the neighbourhoods of the identity in the groups of
points over `R` of an affine group of finite type with its congruence subgroups.

Several structural properties of `R` and of compact `R`-modules follow immediately from this adic
characterization:

* `R` is nonarchimedean and totally disconnected, and is `m`-adically complete and separated
  (`IsAdicComplete (maximalIdeal R) R`); in particular `R` is a `TauCeti.IsCompactModule` over
  itself without a separate total-disconnectedness hypothesis.
* For any compact `R`-module `M`, each submodule `m ^ n • ⊤` is compact hence closed, every open
  submodule of `M` contains some `m ^ n • ⊤` because the finite discrete quotient `M ⧸ N` is
  annihilated by a power of `m`, and consequently `M` is `m`-adically complete and separated
  (`IsAdicComplete (maximalIdeal R) M`).

## Main results

* `IsLocalRing.isAdic_maximalIdeal`: the topology of a compact Hausdorff noetherian local ring is
  its `m`-adic topology.
* `IsLocalRing.nonarchimedeanRing_of_compactSpace`,
  `IsLocalRing.totallyDisconnectedSpace_of_compactSpace`,
  `IsLocalRing.isAdicComplete_maximalIdeal_of_compactSpace`: `R` is nonarchimedean, totally
  disconnected, and `m`-adically complete.
* `TauCeti.IsCompactModule.self_of_isLocalRing`: `R` is a compact module over itself.
* `TauCeti.IsCompactModule.isClosed_maximalIdeal_pow_smul_top`,
  `TauCeti.IsCompactModule.exists_maximalIdeal_pow_smul_top_le`,
  `TauCeti.IsCompactModule.isAdicComplete_maximalIdeal`: every compact `R`-module has closed adic
  filtration steps, open submodules containing a power of `m`, and `m`-adic completeness.
-/

public section

open Topology

namespace IsLocalRing

variable (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R] [IsLocalRing R] [IsNoetherianRing R]

/-- **The topology of a compact Hausdorff noetherian local ring is its `m`-adic topology**: the
powers of the maximal ideal are open, and every neighbourhood of `0` contains one of them. -/
theorem isAdic_maximalIdeal : IsAdic (maximalIdeal R) := by
  refine isAdic_iff.mpr ⟨isOpen_maximalIdeal_pow R, fun s hs ↦ ?_⟩
  -- The powers `m ^ n` are compact, decreasing, and meet in `{0}` by Krull's intersection theorem.
  have hinter : (⋂ n : ℕ, ((maximalIdeal R ^ n : Ideal R) : Set R)) = {0} := by
    rw [← Submodule.coe_iInf,
      Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top, Submodule.bot_coe]
  refine exists_subset_nhds_of_isCompact (fun i j ↦ ⟨max i j, ?_, ?_⟩)
    (fun n ↦ Ideal.isCompact_of_fg (IsNoetherian.noetherian _)) (by rwa [hinter, nhdsSet_singleton])
  · exact Ideal.pow_le_pow_right (le_max_left i j)
  · exact Ideal.pow_le_pow_right (le_max_right i j)

/-- A compact Hausdorff noetherian local ring is nonarchimedean: its topology is `m`-adic. -/
theorem nonarchimedeanRing_of_compactSpace : NonarchimedeanRing R :=
  isAdic_maximalIdeal R ▸ (maximalIdeal R).nonarchimedean

/-- A compact Hausdorff noetherian local ring is totally disconnected. -/
theorem totallyDisconnectedSpace_of_compactSpace : TotallyDisconnectedSpace R :=
  have := nonarchimedeanRing_of_compactSpace R
  inferInstance

/-- **A compact Hausdorff noetherian local ring is `m`-adically complete and separated.** -/
theorem isAdicComplete_maximalIdeal_of_compactSpace : IsAdicComplete (maximalIdeal R) R := by
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  have : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  exact (isAdic_maximalIdeal R).isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

end IsLocalRing

namespace TauCeti.IsCompactModule

open IsLocalRing

variable {R M : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M]

variable (R) in
/-- A compact Hausdorff noetherian local ring is a compact module over itself. -/
theorem self_of_isLocalRing : IsCompactModule R R :=
  have := totallyDisconnectedSpace_of_compactSpace R
  .self

variable (hM : IsCompactModule R M)
include hM

omit [IsTopologicalRing R] [CompactSpace R] [T2Space R] in
/-- In a compact module over a noetherian local ring, every step `m ^ n • ⊤` of the adic
filtration is closed. -/
theorem isClosed_maximalIdeal_pow_smul_top (n : ℕ) :
    IsClosed (((maximalIdeal R ^ n) • (⊤ : Submodule R M) : Submodule R M) : Set M) := by
  have := hM.isTopologicalAddGroup
  have := hM.continuousSMul
  have := hM.compactSpace
  have := hM.t2Space
  exact (Ideal.FG.isCompact_smul (IsNoetherian.noetherian (maximalIdeal R ^ n))
    (by simpa using isCompact_univ)).isClosed

/-- **Every open submodule of a compact module over a compact Hausdorff noetherian local ring
contains `m ^ n • ⊤` for some `n`.** -/
theorem exists_maximalIdeal_pow_smul_top_le (N : Submodule R M) (hN : IsOpen (N : Set M)) :
    ∃ n : ℕ, (maximalIdeal R ^ n) • (⊤ : Submodule R M) ≤ N := by
  have := hM.isTopologicalAddGroup
  have := hM.continuousSMul
  have := Submodule.Quotient.discreteTopology_of_isOpen N hN
  have hfin := hM.finite_quotient_of_isOpen N hN
  have := Fintype.ofFinite (M ⧸ N)
  -- Each element of the finite discrete quotient `M ⧸ N` has an open annihilator ideal in `R`,
  -- which contains a power of `m` by `isAdic_maximalIdeal`.
  have hann : ∀ q : M ⧸ N, ∃ k : ℕ, ∀ r ∈ maximalIdeal R ^ k, r • q = 0 := fun q ↦ by
    have hopen : IsOpen {r : R | r • q = 0} :=
      (isOpen_discrete ({0} : Set (M ⧸ N))).preimage (continuous_id.smul continuous_const)
    obtain ⟨k, -, hk⟩ := (isAdic_maximalIdeal R).hasBasis_nhds_zero.mem_iff.mp
      (hopen.mem_nhds (zero_smul R q))
    exact ⟨k, fun r hr ↦ hk hr⟩
  choose k hk using hann
  refine ⟨Finset.univ.sup k, ?_⟩
  rw [Submodule.smul_le]
  intro r hr m _
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_smul]
  exact hk (N.mkQ m) r (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ _)) hr)

/-- **Every compact module over a compact Hausdorff noetherian local ring is `m`-adically complete
and separated.** -/
theorem isAdicComplete_maximalIdeal : IsAdicComplete (maximalIdeal R) M := by
  have := hM.isTopologicalAddGroup
  have := hM.compactSpace
  refine { haus' := fun x hx ↦ ?_, prec' := fun f hf ↦ ?_ }
  · -- Separatedness: every open submodule contains some `m ^ n • ⊤`.
    refine hM.eq_zero_of_forall_mem_of_isOpen fun N hN ↦ ?_
    obtain ⟨n, hn⟩ := hM.exists_maximalIdeal_pow_smul_top_le N hN
    exact hn (by simpa [SModEq.zero] using hx n)
  · -- Precompleteness: Cantor's intersection theorem on the closed cosets of `m ^ n • ⊤`.
    set C : ℕ → Set M := fun n ↦
      (fun y ↦ f n - y) ⁻¹' (((maximalIdeal R ^ n) • (⊤ : Submodule R M) : Submodule R M) : Set M)
    have hclosed : ∀ n, IsClosed (C n) := fun n ↦
      (hM.isClosed_maximalIdeal_pow_smul_top n).preimage (continuous_const.sub continuous_id)
    have hne : ∀ n, (C n).Nonempty := fun n ↦ ⟨f n, by simp [C]⟩
    have hmono : Antitone C := fun m n hmn y hy ↦ by
      have hfm : f m - f n ∈ (maximalIdeal R ^ m) • (⊤ : Submodule R M) :=
        SModEq.sub_mem.mp (hf hmn)
      have hfn : f n - y ∈ (maximalIdeal R ^ m) • (⊤ : Submodule R M) :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn) hy
      simpa [C, sub_add_sub_cancel] using add_mem hfm hfn
    obtain ⟨L, hL⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      (fun n ↦ hmono (Nat.le_succ n)) hne (hclosed 0).isCompact hclosed
    exact ⟨L, fun n ↦ SModEq.sub_mem.mpr (Set.mem_iInter.mp hL n)⟩

end TauCeti.IsCompactModule
