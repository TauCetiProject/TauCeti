/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Ring.Compact
public import TauCeti.Topology.Algebra.Module.Compact
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.UniformSpace.Cauchy

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

More generally, whenever a commutative topological ring `R` has `I`-adic topology (`IsAdic I`),
compactness and Hausdorffness of `R` (or compactness of an `R`-module `M`) yield:

* If `R` is compact and Hausdorff, `R` is `I`-adically complete and separated
  (`IsAdic.isAdicComplete_of_compactSpace`), is a `TauCeti.IsCompactModule` over itself
  (`TauCeti.IsCompactModule.self_of_isAdic`), and has compact quotients `R ⧸ I`
  (`TauCeti.IsCompactModule.quotient_of_isAdic`).
* For any compact `R`-module `M`, every open submodule contains `(I ^ n) • ⊤` for some `n`
  (`TauCeti.IsCompactModule.exists_pow_smul_top_le`); when `I` is finitely generated, `M ⧸ (I • ⊤)`
  is a compact `R ⧸ I`-module (`TauCeti.IsCompactModule.quotient_smul_top_of_isAdic`) and (for `R`
  compact) `M` is `I`-adically complete and separated
  (`TauCeti.IsCompactModule.isAdicComplete_of_isAdic`).
* Specializing to `I = maximalIdeal R` on a compact Hausdorff noetherian local ring gives the
  corresponding `maximalIdeal` results directly from `IsLocalRing.isAdic_maximalIdeal`.

## Main results

* `IsAdic.isAdicComplete_of_compactSpace`: a compact Hausdorff `I`-adic ring is `I`-adically
  complete and separated.
* `IsLocalRing.isAdic_maximalIdeal`: the topology of a compact Hausdorff noetherian local ring is
  its `m`-adic topology.
* `IsLocalRing.nonarchimedeanRing_of_compactSpace`,
  `IsLocalRing.totallyDisconnectedSpace_of_compactSpace`,
  `IsLocalRing.isAdicComplete_maximalIdeal_of_compactSpace`: `R` is nonarchimedean, totally
  disconnected, and `m`-adically complete.
* `TauCeti.IsCompactModule.self_of_isAdic`, `TauCeti.IsCompactModule.quotient_of_isAdic`,
  `TauCeti.IsCompactModule.exists_pow_smul_top_le`,
  `TauCeti.IsCompactModule.isAdicComplete_of_isAdic`,
  `TauCeti.IsCompactModule.quotient_smul_top_of_isAdic`: adic properties of compact modules over
  `I`-adic rings.
* `TauCeti.IsCompactModule.self_of_isLocalRing`,
  `TauCeti.IsCompactModule.quotient_maximalIdeal`,
  `TauCeti.IsCompactModule.isClosed_maximalIdeal_pow_smul_top`,
  `TauCeti.IsCompactModule.exists_maximalIdeal_pow_smul_top_le`,
  `TauCeti.IsCompactModule.isAdicComplete_maximalIdeal`,
  `TauCeti.IsCompactModule.quotient_maximalIdeal_smul_top`: specializations to `maximalIdeal R`.
-/

public section

open Topology

namespace IsAdic

/-- **A compact Hausdorff commutative ring whose topology is `I`-adic is `I`-adically complete and
separated.** -/
theorem isAdicComplete_of_compactSpace {R : Type*} [CommRing R] [TopologicalSpace R]
    [CompactSpace R] [T2Space R] {I : Ideal R} (hI : IsAdic I) : IsAdicComplete I R := by
  have := hI.nonarchimedeanRing
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  have : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  exact hI.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

end IsAdic

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
  (isAdic_maximalIdeal R).nonarchimedeanRing

/-- A compact Hausdorff noetherian local ring is totally disconnected. -/
theorem totallyDisconnectedSpace_of_compactSpace : TotallyDisconnectedSpace R :=
  (isAdic_maximalIdeal R).totallyDisconnectedSpace

/-- **A compact Hausdorff noetherian local ring is `m`-adically complete and separated.** -/
theorem isAdicComplete_maximalIdeal_of_compactSpace : IsAdicComplete (maximalIdeal R) R :=
  (isAdic_maximalIdeal R).isAdicComplete_of_compactSpace

end IsLocalRing

namespace TauCeti.IsCompactModule

open IsLocalRing

section IsAdic

variable {R M : Type*} [CommRing R] [TopologicalSpace R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M]

/-- A compact Hausdorff commutative ring whose topology is `I`-adic is a compact module over
itself. -/
theorem self_of_isAdic [CompactSpace R] [T2Space R] {I : Ideal R} (hI : IsAdic I) :
    IsCompactModule R R :=
  have := hI.nonarchimedeanRing
  have := hI.totallyDisconnectedSpace
  .self

/-- Over a compact Hausdorff `I`-adic commutative ring `R`, the quotient `R ⧸ I` with its quotient
topology is a compact `R`-module. -/
theorem quotient_of_isAdic [CompactSpace R] [T2Space R] {I : Ideal R} (hI : IsAdic I) :
    IsCompactModule R (R ⧸ I) :=
  (self_of_isAdic hI).quotient I (by simpa [pow_one] using hI.isClosed_pow 1)

/-- **Every open submodule of a compact module over an `I`-adic ring contains `(I ^ n) • ⊤` for
some `n`.** -/
theorem exists_pow_smul_top_le (hM : IsCompactModule R M) {I : Ideal R} (hI : IsAdic I)
    (N : Submodule R M) (hN : IsOpen (N : Set M)) :
    ∃ n : ℕ, (I ^ n) • (⊤ : Submodule R M) ≤ N := by
  have := hM.isTopologicalAddGroup
  have := hM.continuousSMul
  have := Submodule.Quotient.discreteTopology_of_isOpen N hN
  have hfin := hM.finite_quotient_of_isOpen N hN
  have := Fintype.ofFinite (M ⧸ N)
  -- Each element of the finite discrete quotient `M ⧸ N` has an open annihilator ideal in `R`,
  -- which contains a power of `I` by `hI`.
  have hann : ∀ q : M ⧸ N, ∃ k : ℕ, ∀ r ∈ I ^ k, r • q = 0 := fun q ↦ by
    have hopen : IsOpen {r : R | r • q = 0} :=
      (isOpen_discrete ({0} : Set (M ⧸ N))).preimage (continuous_id.smul continuous_const)
    obtain ⟨k, -, hk⟩ := hI.hasBasis_nhds_zero.mem_iff.mp (hopen.mem_nhds (zero_smul R q))
    exact ⟨k, fun r hr ↦ hk hr⟩
  choose k hk using hann
  refine ⟨Finset.univ.sup k, ?_⟩
  rw [Submodule.smul_le]
  intro r hr m _
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_smul]
  exact hk (N.mkQ m) r (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ _)) hr)

/-- **Every compact module over a compact `I`-adic commutative ring with `I` finitely generated is
`I`-adically complete and separated.** -/
theorem isAdicComplete_of_isAdic [CompactSpace R] (hM : IsCompactModule R M) {I : Ideal R}
    (hI : IsAdic I) (hIfg : I.FG) : IsAdicComplete I M := by
  have := hM.isTopologicalAddGroup
  have := hM.compactSpace
  refine { haus' := fun x hx ↦ ?_, prec' := fun f hf ↦ ?_ }
  · -- Separatedness: every open submodule contains some `(I ^ n) • ⊤`.
    refine hM.eq_zero_of_forall_mem_of_isOpen fun N hN ↦ ?_
    obtain ⟨n, hn⟩ := hM.exists_pow_smul_top_le hI N hN
    exact hn (by simpa [SModEq.zero] using hx n)
  · -- Precompleteness: Cantor's intersection theorem on the closed cosets of `(I ^ n) • ⊤`.
    set C : ℕ → Set M := fun n ↦
      (fun y ↦ f n - y) ⁻¹' (((I ^ n) • (⊤ : Submodule R M) : Submodule R M) : Set M)
    have hclosed : ∀ n, IsClosed (C n) := fun n ↦
      (hM.isClosed_smul_top hIfg.pow).preimage (continuous_const.sub continuous_id)
    have hne : ∀ n, (C n).Nonempty := fun n ↦ ⟨f n, by simp [C]⟩
    have hmono : Antitone C := fun m n hmn y hy ↦ by
      have hfm : f m - f n ∈ (I ^ m) • (⊤ : Submodule R M) :=
        SModEq.sub_mem.mp (hf hmn)
      have hfn : f n - y ∈ (I ^ m) • (⊤ : Submodule R M) :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn) hy
      simpa [C, sub_add_sub_cancel] using add_mem hfm hfn
    obtain ⟨L, hL⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      (fun n ↦ hmono (Nat.le_succ n)) hne (hclosed 0).isCompact hclosed
    exact ⟨L, fun n ↦ SModEq.sub_mem.mpr (Set.mem_iInter.mp hL n)⟩

/-- For a finitely generated ideal of definition `I` of `R`, the reduction `M ⧸ (I • ⊤)` of a
compact `R`-module `M` is a compact module over the discrete quotient ring `R ⧸ I`. -/
theorem quotient_smul_top_of_isAdic (hM : IsCompactModule R M) {I : Ideal R} (hI : IsAdic I)
    (hIfg : I.FG) : IsCompactModule (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) := by
  have := hI.discreteTopology_quotient
  have : IsScalarTower R (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
    (Module.isTorsionBySet_quotient_ideal_smul M I).isScalarTower
  have hM₀ := hM.quotient _ (hM.isClosed_smul_top hIfg)
  have := hM₀.isTopologicalAddGroup
  have := hM₀.continuousSMul
  have := hM₀.compactSpace
  have := hM₀.totallyDisconnectedSpace
  refine ⟨inferInstance, ⟨continuous_prod_of_discrete_left.mpr fun r ↦ ?_⟩,
    inferInstance, inferInstance⟩
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact (continuous_const_smul c).congr fun x ↦ by
    rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

end IsAdic

section IsLocalRing

variable {R M : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M]

variable (R) in
/-- A compact Hausdorff noetherian local ring is a compact module over itself. -/
theorem self_of_isLocalRing : IsCompactModule R R :=
  self_of_isAdic (isAdic_maximalIdeal R)

variable (R) in
/-- Over a compact Hausdorff noetherian local ring `R`, the residue field `R ⧸ maximalIdeal R` with
its quotient topology is a compact `R`-module. -/
theorem quotient_maximalIdeal : IsCompactModule R (R ⧸ maximalIdeal R) :=
  quotient_of_isAdic (isAdic_maximalIdeal R)

variable (hM : IsCompactModule R M)
include hM

omit [IsTopologicalRing R] [CompactSpace R] [T2Space R] in
/-- In a compact module over a noetherian local ring, every step `m ^ n • ⊤` of the maximal ideal
filtration is closed. -/
theorem isClosed_maximalIdeal_pow_smul_top (n : ℕ) :
    IsClosed (((maximalIdeal R ^ n) • (⊤ : Submodule R M) : Submodule R M) : Set M) :=
  hM.isClosed_smul_top (IsNoetherian.noetherian (maximalIdeal R ^ n))

/-- **Every open submodule of a compact module over a compact Hausdorff noetherian local ring
contains `m ^ n • ⊤` for some `n`.** -/
theorem exists_maximalIdeal_pow_smul_top_le (N : Submodule R M) (hN : IsOpen (N : Set M)) :
    ∃ n : ℕ, (maximalIdeal R ^ n) • (⊤ : Submodule R M) ≤ N :=
  hM.exists_pow_smul_top_le (isAdic_maximalIdeal R) N hN

/-- **Every compact module over a compact Hausdorff noetherian local ring is `m`-adically complete
and separated.** -/
theorem isAdicComplete_maximalIdeal : IsAdicComplete (maximalIdeal R) M :=
  hM.isAdicComplete_of_isAdic (isAdic_maximalIdeal R) (IsNoetherian.noetherian (maximalIdeal R))

/-- Over a compact Hausdorff noetherian local ring `R`, the reduction
`M ⧸ (maximalIdeal R • ⊤)` of a compact `R`-module `M` is a compact module over the discrete
residue field `R ⧸ maximalIdeal R`. -/
theorem quotient_maximalIdeal_smul_top :
    IsCompactModule (R ⧸ maximalIdeal R) (M ⧸ ((maximalIdeal R) • (⊤ : Submodule R M))) :=
  hM.quotient_smul_top_of_isAdic (isAdic_maximalIdeal R) (IsNoetherian.noetherian (maximalIdeal R))

end IsLocalRing

end TauCeti.IsCompactModule
