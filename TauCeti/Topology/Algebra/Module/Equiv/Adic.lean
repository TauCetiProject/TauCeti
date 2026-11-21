/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# Adic congruence neighbourhoods from product coordinate equivalences

Given a topological coordinate isomorphism `e : M ≃L[R] (I → R)` and an ideal `J` of `R`,
`ContinuousLinearEquiv.submodulePiPow e J s n` is the `R`-submodule
`{m : M | ∀ i ∈ s, e m i ∈ J ^ n}` cut out on a finite set `s : Finset I`. When the topology of
`R` is `J`-adic, these submodules are open (`ContinuousLinearEquiv.isOpen_submodulePiPow`) and form
a basis of neighbourhoods of `0` in `M` (`ContinuousLinearEquiv.hasBasis_nhds_zero_submodulePiPow`).
-/

public section

open Filter Topology

namespace ContinuousLinearEquiv

section Adic

variable {R M I : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]

section Submodule

variable (e : M ≃L[R] (I → R)) (J : Ideal R)

/-- Given a topological coordinate isomorphism `e : M ≃L[R] (I → R)` and an ideal `J` of `R`, the
`R`-submodule `{m : M | ∀ i ∈ s, e m i ∈ J ^ n}` cut out on a finite set of coordinates `s`. -/
def submodulePiPow (s : Finset I) (n : ℕ) : Submodule R M :=
  (Submodule.pi (s : Set I) fun _ ↦ J ^ n).comap e.toLinearMap

theorem submodulePiPow_def (s : Finset I) (n : ℕ) :
    e.submodulePiPow J s n = (Submodule.pi (s : Set I) fun _ ↦ J ^ n).comap e.toLinearMap := by
  rfl

@[simp, grind =]
theorem mem_submodulePiPow_iff (s : Finset I) (n : ℕ) (m : M) :
    m ∈ e.submodulePiPow J s n ↔ ∀ i ∈ s, e m i ∈ J ^ n := by
  simp [submodulePiPow_def]

@[simp, grind =]
theorem submodulePiPow_empty (n : ℕ) : e.submodulePiPow J ∅ n = ⊤ := by
  simp [submodulePiPow_def]

@[simp, grind =]
theorem submodulePiPow_zero (s : Finset I) : e.submodulePiPow J s 0 = ⊤ := by
  simp [submodulePiPow_def]

@[simp, grind =]
theorem submodulePiPow_union [DecidableEq I] (s₁ s₂ : Finset I) (n : ℕ) :
    e.submodulePiPow J (s₁ ∪ s₂) n = e.submodulePiPow J s₁ n ⊓ e.submodulePiPow J s₂ n := by
  ext m
  simp [or_imp, forall_and]

@[simp, grind =]
theorem map_submodulePiPow (s : Finset I) (n : ℕ) :
    (e.submodulePiPow J s n).map e.toLinearMap = Submodule.pi (s : Set I) fun _ ↦ J ^ n := by
  rw [submodulePiPow_def]
  exact Submodule.map_comap_eq_of_surjective e.surjective _

/-- `e.submodulePiPow J s n` is antitone in both the finite coordinate set `s` and the exponent
`n`. -/
theorem submodulePiPow_anti {s₁ s₂ : Finset I} {n₁ n₂ : ℕ} (hs : s₁ ⊆ s₂) (hn : n₁ ≤ n₂) :
    e.submodulePiPow J s₂ n₂ ≤ e.submodulePiPow J s₁ n₁ := fun _ hm i hi ↦
  Ideal.pow_le_pow_right hn ((mem_submodulePiPow_iff e J s₂ n₂ _).mp hm i (hs hi))

/-- `e.submodulePiPow J s n` is antitone in the finite coordinate set `s`. -/
theorem submodulePiPow_left_antitone (n : ℕ) :
    Antitone (fun s : Finset I ↦ e.submodulePiPow J s n) :=
  fun _ _ hs ↦ e.submodulePiPow_anti J hs le_rfl

/-- `e.submodulePiPow J s n` is antitone in the exponent `n`. -/
theorem submodulePiPow_right_antitone (s : Finset I) :
    Antitone (e.submodulePiPow J s) :=
  fun _ _ hn ↦ e.submodulePiPow_anti J Finset.Subset.rfl hn

end Submodule

/-- When the topology of `R` is `J`-adic, each `e.submodulePiPow J s n` is open in `M`. -/
theorem isOpen_submodulePiPow (e : M ≃L[R] (I → R)) {J : Ideal R} (hJ : IsAdic J)
    (s : Finset I) (n : ℕ) : IsOpen (e.submodulePiPow J s n : Set M) := by
  rw [submodulePiPow_def, Submodule.comap_coe, Submodule.coe_pi,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
  exact (isOpen_set_pi s.finite_toSet fun _ _ ↦ hJ.isOpen_pow n).preimage e.continuous

/-- **Neighbourhood basis from a product coordinate equivalence.** If `e : M ≃L[R] (I → R)` and
the topology of `R` is `J`-adic, then `e.submodulePiPow J s n` form a basis of neighbourhoods of
`0` in `M`. -/
theorem hasBasis_nhds_zero_submodulePiPow (e : M ≃L[R] (I → R)) {J : Ideal R} (hJ : IsAdic J) :
    (𝓝 (0 : M)).HasBasis (fun _ : Finset I × ℕ ↦ True)
      (fun p ↦ (e.submodulePiPow J p.1 p.2 : Set M)) := by
  refine hasBasis_iff.mpr fun W ↦ ⟨fun hW ↦ ?_, fun ⟨⟨s, n⟩, _, hsub⟩ ↦
    mem_of_superset ((e.isOpen_submodulePiPow hJ s n).mem_nhds (zero_mem _)) hsub⟩
  have hW' : e.symm ⁻¹' W ∈ 𝓝 (0 : I → R) :=
    e.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hW)
  rw [nhds_pi, Filter.mem_pi'] at hW'
  obtain ⟨s, t, ht, hst⟩ := hW'
  choose k hk using fun i ↦ hJ.hasBasis_nhds_zero.mem_iff.mp (ht i)
  refine ⟨(s, s.sup fun i ↦ k i), trivial, fun m hm ↦ ?_⟩
  rw [SetLike.mem_coe, mem_submodulePiPow_iff] at hm
  have hem : e m ∈ (s : Set I).pi t := fun i hi ↦ (hk i).2 (Ideal.pow_le_pow_right
    (Finset.le_sup (Finset.mem_coe.mp hi)) (hm i (Finset.mem_coe.mp hi)))
  simpa using hst hem

end Adic

end ContinuousLinearEquiv
