/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic

/-!
# Topologically characteristic subgroups

A subgroup of a topological group is **topologically characteristic** if every continuous
automorphism preserves it. This is weaker than Mathlib's `Subgroup.Characteristic`, which tests
all abstract automorphisms. The distinction matters for profinite groups, whose abstract
automorphisms need not be continuous.

The predicate `TauCeti.IsTopCharacteristic G N` is expressed by the image equation
`N.map φ = N`. Its equivalent image and preimage inclusion criteria make it convenient to prove,
and it is stable under arbitrary suprema and infima. A topologically characteristic subgroup is
normal as soon as inner automorphisms are continuous.

The characterizations and lattice API parallel Mathlib's API for
`Subgroup.Characteristic` in `Mathlib.Algebra.Group.Subgroup.Basic`.

## Main definitions

* `TauCeti.IsTopCharacteristic`: invariance of a subgroup under every continuous automorphism.

## Main results

* `Subgroup.Characteristic.isTopCharacteristic`: every abstractly characteristic subgroup is
  topologically characteristic.
* `TauCeti.IsTopCharacteristic.normal`: a topologically characteristic subgroup is normal when
  inner automorphisms are continuous.
-/

public section

namespace TauCeti

universe u

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- A subgroup is **topologically characteristic** if every continuous automorphism maps it onto
itself. This is weaker than `Subgroup.Characteristic`, which quantifies over all abstract
automorphisms. -/
def IsTopCharacteristic (N : Subgroup G) : Prop :=
  ∀ φ : ContinuousAut G, N.map φ.toMulEquiv.toMonoidHom = N

variable {G} {N K : Subgroup G}

/-- A subgroup is topologically characteristic exactly when every continuous automorphism maps
it onto itself. -/
theorem isTopCharacteristic_iff_map_eq :
    IsTopCharacteristic G N ↔
      ∀ φ : ContinuousAut G, N.map φ.toMulEquiv.toMonoidHom = N :=
  Iff.rfl

/-- A subgroup is topologically characteristic exactly when it is the preimage of itself under
every continuous automorphism. -/
theorem isTopCharacteristic_iff_comap_eq :
    IsTopCharacteristic G N ↔
      ∀ φ : ContinuousAut G, N.comap φ.toMulEquiv.toMonoidHom = N := by
  simp_rw [IsTopCharacteristic, Subgroup.map_equiv_eq_comap_symm']
  exact ⟨fun h φ ↦ h φ.symm, fun h φ ↦ h φ.symm⟩

/-- To prove that a subgroup is topologically characteristic, it suffices to prove that its
preimage under every continuous automorphism is contained in it. -/
theorem isTopCharacteristic_iff_comap_le :
    IsTopCharacteristic G N ↔
      ∀ φ : ContinuousAut G, N.comap φ.toMulEquiv.toMonoidHom ≤ N :=
  isTopCharacteristic_iff_comap_eq.trans
    ⟨fun h φ ↦ le_of_eq (h φ), fun h φ ↦
      le_antisymm (h φ) fun g hg ↦
        h φ.symm ((congr_arg (· ∈ N) (φ.symm_apply_apply g)).mpr hg)⟩

/-- To prove that a subgroup is topologically characteristic, it suffices to prove that it is
contained in its preimage under every continuous automorphism. -/
theorem isTopCharacteristic_iff_le_comap :
    IsTopCharacteristic G N ↔
      ∀ φ : ContinuousAut G, N ≤ N.comap φ.toMulEquiv.toMonoidHom :=
  isTopCharacteristic_iff_comap_eq.trans
    ⟨fun h φ ↦ ge_of_eq (h φ), fun h φ ↦
      le_antisymm
        (fun g hg ↦ (congr_arg (· ∈ N) (φ.symm_apply_apply g)).mp (h φ.symm hg)) (h φ)⟩

/-- To prove that a subgroup is topologically characteristic, it suffices to prove that every
continuous automorphism maps it into itself. -/
theorem isTopCharacteristic_iff_map_le :
    IsTopCharacteristic G N ↔
      ∀ φ : ContinuousAut G, N.map φ.toMulEquiv.toMonoidHom ≤ N := by
  simp_rw [Subgroup.map_equiv_eq_comap_symm']
  exact isTopCharacteristic_iff_comap_le.trans
    ⟨fun h φ ↦ h φ.symm, fun h φ ↦ h φ.symm⟩

/-- To prove that a subgroup is topologically characteristic, it suffices to prove that the image
under every continuous automorphism contains it. -/
theorem isTopCharacteristic_iff_le_map :
    IsTopCharacteristic G N ↔
      ∀ φ : ContinuousAut G, N ≤ N.map φ.toMulEquiv.toMonoidHom := by
  simp_rw [Subgroup.map_equiv_eq_comap_symm']
  exact isTopCharacteristic_iff_le_comap.trans
    ⟨fun h φ ↦ h φ.symm, fun h φ ↦ h φ.symm⟩

/-- Every abstractly characteristic subgroup is topologically characteristic. -/
theorem _root_.Subgroup.Characteristic.isTopCharacteristic (hN : N.Characteristic) :
    IsTopCharacteristic G N :=
  fun φ ↦ Subgroup.characteristic_iff_map_eq.mp hN φ.toMulEquiv

namespace IsTopCharacteristic

/-- The trivial subgroup is topologically characteristic. -/
theorem bot : IsTopCharacteristic G (⊥ : Subgroup G) :=
  isTopCharacteristic_iff_le_map.mpr fun _φ ↦ bot_le

/-- The whole group is topologically characteristic. -/
theorem top : IsTopCharacteristic G (⊤ : Subgroup G) :=
  isTopCharacteristic_iff_map_le.mpr fun _φ ↦ le_top

/-- The supremum of two topologically characteristic subgroups is topologically characteristic. -/
theorem sup (hN : IsTopCharacteristic G N) (hK : IsTopCharacteristic G K) :
    IsTopCharacteristic G (N ⊔ K) := by
  intro φ
  rw [Subgroup.map_sup, hN φ, hK φ]

/-- An arbitrary supremum of topologically characteristic subgroups is topologically
characteristic. -/
theorem iSup {ι : Sort*} {N : ι → Subgroup G} (hN : ∀ i, IsTopCharacteristic G (N i)) :
    IsTopCharacteristic G (⨆ i, N i) := by
  intro φ
  rw [Subgroup.map_iSup]
  exact iSup_congr fun i ↦ hN i φ

/-- The infimum of two topologically characteristic subgroups is topologically characteristic. -/
theorem inf (hN : IsTopCharacteristic G N) (hK : IsTopCharacteristic G K) :
    IsTopCharacteristic G (N ⊓ K) := by
  rw [isTopCharacteristic_iff_comap_eq]
  intro φ
  rw [Subgroup.comap_inf, isTopCharacteristic_iff_comap_eq.mp hN φ,
    isTopCharacteristic_iff_comap_eq.mp hK φ]

/-- An arbitrary infimum of topologically characteristic subgroups is topologically
characteristic. -/
theorem iInf {ι : Sort*} {N : ι → Subgroup G} (hN : ∀ i, IsTopCharacteristic G (N i)) :
    IsTopCharacteristic G (⨅ i, N i) := by
  rw [isTopCharacteristic_iff_comap_eq]
  intro φ
  rw [Subgroup.comap_iInf]
  exact iInf_congr fun i ↦ isTopCharacteristic_iff_comap_eq.mp (hN i) φ

/-- A topologically characteristic subgroup is normal when inner automorphisms are continuous. -/
theorem normal [SeparatelyContinuousMul G] (hN : IsTopCharacteristic G N) : N.Normal where
  conj_mem := by
    intro n hn g
    rw [← hN (ContinuousAut.conj g)]
    rw [← ContinuousAut.conj_apply]
    exact Subgroup.mem_map_of_mem (ContinuousAut.conj g).toMulEquiv.toMonoidHom hn

end IsTopCharacteristic

end TauCeti
