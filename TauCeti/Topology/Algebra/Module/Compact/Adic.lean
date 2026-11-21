/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.Topology.Algebra.Module.Compact.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic
import Mathlib.RingTheory.Filtration

/-!
# Adic properties of compact modules

For an `I`-adic commutative topological ring `R`: when compact and Hausdorff, `R` and `R ⧸ I` are
compact `R`-modules (`self_of_isAdic`, `quotient_of_isAdic`); every open submodule of a compact
`R`-module contains `(I ^ n) • ⊤` (`exists_pow_smul_top_le`); and when `I` is finitely generated,
`M ⧸ (I • ⊤)` is a compact `R ⧸ I`-module (`quotient_smul_top_of_isAdic`) and compact `R`-modules
over compact `R` are `I`-adically complete (`isAdicComplete_of_isAdic`).
-/

public section

open Topology

namespace TauCeti.IsCompactModule

variable {R M : Type*} [CommRing R] [TopologicalSpace R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M]

/-- A compact Hausdorff commutative ring whose topology is `I`-adic is a compact module over
itself. -/
theorem self_of_isAdic [CompactSpace R] [T2Space R] {I : Ideal R} (hI : IsAdic I) :
    IsCompactModule R R :=
  have := hI.nonarchimedeanRing; have := hI.totallyDisconnectedSpace; .self

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
  have := hM.isTopologicalAddGroup; have := hM.continuousSMul
  have := Submodule.Quotient.discreteTopology_of_isOpen N hN
  have := hM.finite_quotient_of_isOpen N hN; have := Fintype.ofFinite (M ⧸ N)
  choose k hk using fun q : M ⧸ N ↦
    (hI.hasBasis_nhds_zero.mem_iff.mp (((isOpen_discrete ({0} : Set (M ⧸ N))).preimage
      (continuous_id.smul continuous_const)).mem_nhds (zero_smul R q))).imp fun _ h ↦ h.2
  refine ⟨Finset.univ.sup k, Submodule.smul_le.mpr fun r hr m _ ↦ ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_smul]
  exact hk (N.mkQ m) (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ _)) hr)

/-- **Every compact module over a compact `I`-adic commutative ring with `I` finitely generated is
`I`-adically complete and separated.** -/
theorem isAdicComplete_of_isAdic [CompactSpace R] (hM : IsCompactModule R M) {I : Ideal R}
    (hI : IsAdic I) (hIfg : I.FG) : IsAdicComplete I M := by
  have := hM.isTopologicalAddGroup; have := hM.compactSpace
  refine { haus' := fun x hx ↦ hM.eq_zero_of_forall_mem_of_isOpen fun N hN ↦ ?_, prec' := ?_ }
  · obtain ⟨n, hn⟩ := hM.exists_pow_smul_top_le hI N hN
    exact hn (by simpa [SModEq.zero] using hx n)
  · intro f hf
    set C : ℕ → Set M := fun n ↦
      (fun y ↦ f n - y) ⁻¹' (((I ^ n) • (⊤ : Submodule R M) : Submodule R M) : Set M)
    have hclosed : ∀ n, IsClosed (C n) := fun n ↦
      (hM.isClosed_smul_top hIfg.pow).preimage (continuous_const.sub continuous_id)
    have hmono : Antitone C := fun _ _ hmn _ hy ↦ by
      simpa [C, sub_add_sub_cancel] using add_mem (SModEq.sub_mem.mp (hf hmn))
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn) hy)
    obtain ⟨L, hL⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      (fun n ↦ hmono (Nat.le_succ n)) (fun n ↦ ⟨f n, by simp [C]⟩) (hclosed 0).isCompact hclosed
    exact ⟨L, fun n ↦ SModEq.sub_mem.mpr (Set.mem_iInter.mp hL n)⟩

/-- For a finitely generated ideal of definition `I` of `R`, the reduction `M ⧸ (I • ⊤)` of a
compact `R`-module `M` is a compact module over the discrete quotient ring `R ⧸ I`. -/
theorem quotient_smul_top_of_isAdic (hM : IsCompactModule R M) {I : Ideal R} (hI : IsAdic I)
    (hIfg : I.FG) : IsCompactModule (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) := by
  have := hI.discreteTopology_quotient
  have : IsScalarTower R (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
    (Module.isTorsionBySet_quotient_ideal_smul M I).isScalarTower
  have ⟨_, _, _, _⟩ := hM.quotient _ (hM.isClosed_smul_top hIfg)
  refine ⟨inferInstance, ⟨continuous_prod_of_discrete_left.mpr fun r ↦ ?_⟩,
    inferInstance, inferInstance⟩
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact (continuous_const_smul c).congr fun x ↦ by
    rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

end TauCeti.IsCompactModule
