/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
theorem submodulePiPow_empty (n : ℕ) : e.submodulePiPow J ∅ n = ⊤ := by simp [submodulePiPow_def]

@[simp, grind =]
theorem submodulePiPow_zero (s : Finset I) : e.submodulePiPow J s 0 = ⊤ := by
  simp [submodulePiPow_def]

@[simp, grind =]
theorem submodulePiPow_union [DecidableEq I] (s₁ s₂ : Finset I) (n : ℕ) :
    e.submodulePiPow J (s₁ ∪ s₂) n = e.submodulePiPow J s₁ n ⊓ e.submodulePiPow J s₂ n := by
  ext m; simp [or_imp, forall_and]

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
theorem submodulePiPow_right_antitone (s : Finset I) : Antitone (e.submodulePiPow J s) :=
  fun _ _ hn ↦ e.submodulePiPow_anti J Finset.Subset.rfl hn

end Submodule

/-- When the topology of `R` is `J`-adic, each `e.submodulePiPow J s n` is open in `M`. -/
theorem isOpen_submodulePiPow (e : M ≃L[R] (I → R)) {J : Ideal R} (hJ : IsAdic J)
    (s : Finset I) (n : ℕ) : IsOpen (e.submodulePiPow J s n : Set M) := by
  simpa [submodulePiPow_def] using
    (isOpen_set_pi s.finite_toSet fun _ _ ↦ hJ.isOpen_pow n).preimage e.continuous

/-- **Neighbourhood basis from a product coordinate equivalence.** If `e : M ≃L[R] (I → R)` and
the topology of `R` is `J`-adic, then `e.submodulePiPow J s n` form a basis of neighbourhoods of
`0` in `M`. -/
theorem hasBasis_nhds_zero_submodulePiPow (e : M ≃L[R] (I → R)) {J : Ideal R} (hJ : IsAdic J) :
    (𝓝 (0 : M)).HasBasis (fun _ : Finset I × ℕ ↦ True)
      (fun p ↦ (e.submodulePiPow J p.1 p.2 : Set M)) := by
  have h0 : (𝓝 (0 : I → R)).HasBasis (fun Ik : Set I × ℕ ↦ Ik.1.Finite ∧ True)
      (fun Ik ↦ Ik.1.pi fun _ ↦ ((J ^ Ik.2 : Ideal R) : Set R)) := by
    rw [nhds_pi]
    exact hJ.hasBasis_nhds_zero.pi_self
  refine (e.toHomeomorph.isInducing.basis_nhds (map_zero e ▸ h0)).to_hasBasis ?_ ?_
  · rintro ⟨s, n⟩ ⟨hs, _⟩
    exact ⟨(hs.toFinset, n), trivial, fun m hm ↦ by simpa [hs.mem_toFinset] using hm⟩
  · rintro ⟨s, n⟩ _
    exact ⟨(s, n), ⟨s.finite_toSet, trivial⟩, fun m hm ↦ by simpa using hm⟩

end Adic

end ContinuousLinearEquiv
