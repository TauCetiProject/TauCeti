/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic
import TauCeti.Topology.Algebra.ProperAction.Orbit

/-!
# Injectivity near an orbit of a proper action

`ProperSMul.exists_isOpen_injOn_smul_of_le_stabilizer` promotes local injectivity of an
equivariant map to injectivity on an invariant open neighbourhood of an orbit, provided the
map preserves the stabilizer at the chosen point. The transporter control
`ProperSMul.mem_nhdsSet_stabilizer_iff` lets one apply local injectivity to points in the tube.

## References

* E. Meinrenken, *Group actions on manifolds*, lecture notes, 2003, proof of Theorem 1.25.
-/

public section

open Set Filter Topology
open scoped Pointwise

namespace ProperSMul

/-- If an equivariant map into a proper action is continuous and injective near `y` and preserves
the stabilizer there, a smaller open neighbourhood of `y` has an injective saturation. -/
theorem exists_isOpen_injOn_smul_of_le_stabilizer {G Y X : Type*} [Group G]
    [TopologicalSpace G] [TopologicalSpace Y] [TopologicalSpace X]
    [MulAction G Y] [MulAction G X] [ContinuousSMul G Y] [ProperSMul G X]
    {f : Y → X} {y : Y} (hf : ContinuousAt f y) (hequiv : ∀ (g : G) z, f (g • z) = g • f z)
    (hstab : MulAction.stabilizer G (f y) ≤ MulAction.stabilizer G y)
    {N : Set Y} (hN : N ∈ 𝓝 y) (hinj : InjOn f N) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ U ⊆ N ∧ InjOn f ((univ : Set G) • U) := by
  -- Compactness makes the local injectivity neighbourhood uniform over the stabilizer.
  have hprod : (MulAction.stabilizer G (f y) : Set G) ×ˢ {y} ⊆
      (fun p : G × Y ↦ p.1 • p.2) ⁻¹' interior N := by
    rintro ⟨g, z⟩ ⟨hg, hz⟩
    have hzy : z = y := mem_singleton_iff.mp hz
    have hgz : g • z ∈ interior N := by
      rw [hzy, MulAction.mem_stabilizer_iff.mp (hstab hg), mem_interior_iff_mem_nhds]
      exact hN
    exact hgz
  obtain ⟨V, W, hV, hW, hKV, hyW, hVW⟩ := generalized_tube_lemma
    (isCompact_stabilizer (f y)) isCompact_singleton
    (isOpen_interior.preimage continuous_smul) hprod
  obtain ⟨B, hB, hmove⟩ := mem_nhdsSet_stabilizer_iff.mp (hV.mem_nhdsSet.mpr hKV)
  obtain ⟨U, hU, hopen, hy⟩ := mem_nhds_iff.mp
    (inter_mem (inter_mem hN (hW.mem_nhds (hyW (mem_singleton y)))) (hf hB))
  refine ⟨U, hopen, hy, fun _ hz ↦ (hU hz).1.1, ?_⟩
  have hnormalize (g : G) {z z' : Y} (hz : z ∈ U) (hz' : z' ∈ U)
      (heq : g • f z = f z') : g • z = z' := by
    have hgV : g ∈ V := hmove ⟨f z', heq ▸ smul_mem_smul_set (hU hz).2, (hU hz').2⟩
    have hgz : g • z ∈ N := interior_subset (hVW (mk_mem_prod hgV (hU hz).1.2))
    exact hinj hgz (hU hz').1.1 ((hequiv g z).trans heq)
  rintro _ ⟨g, -, z, hz, rfl⟩ _ ⟨g', -, z', hz', rfl⟩ heq
  rw [hequiv, hequiv] at heq
  have h : (g'⁻¹ * g) • f z = f z' := by
    rw [mul_smul, heq, inv_smul_smul]
  have hz_eq := congrArg (g' • ·) (hnormalize (g'⁻¹ * g) hz hz' h)
  simpa only [← mul_smul, mul_inv_cancel_left] using hz_eq

end ProperSMul
