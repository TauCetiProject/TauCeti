/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.Geometry.Lie.Subgroup.Torus
import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic

/-!
# Conjugacy of maximal tori in the unitary group

Every commutative subgroup of `U(n)` is conjugate into the diagonal torus: a commuting family
of unitary matrices admits one common unitary diagonalizer. Compactness, connectedness, and
closedness of the subgroup are not needed for this containment.

The diagonal torus is compact and connected, being the continuous image of a product of
circles. Its self-centralizing property makes it a maximal torus in the sense of
`TauCeti.Lie.IsMaximalTorus`. Consequently every maximal torus of `U(n)` is conjugate to it,
and any two maximal tori of `U(n)` are conjugate.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98
  (1985), Chapter IV, §1.
-/

public section

namespace TauCeti

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every commutative subgroup of `U(n)` is simultaneously conjugate into its diagonal torus.
No topological assumptions on the subgroup are needed. -/
theorem exists_map_conj_le_unitaryTorus {H : Subgroup (unitaryGroup n ℂ)}
    [IsMulCommutative H] :
    ∃ u : unitaryGroup n ℂ, H.map (MulAut.conj u).toMonoidHom ≤ unitaryTorus n := by
  have hC : Pairwise (fun g h : H => Commute (g.val : Matrix n n ℂ) (h.val : Matrix n n ℂ)) := by
    intro g h _
    exact congrArg (fun a : H => (a.val : Matrix n n ℂ)) (mul_comm' g h)
  obtain ⟨U, hU, d, hd⟩ := exists_mem_unitaryGroup_forall_star_mul_mul_eq_diagonal
    (fun g : H => (g.val : Matrix n n ℂ)) (fun _ => inferInstance) hC
  let u : unitaryGroup n ℂ := ⟨U, hU⟩
  refine ⟨u⁻¹, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  apply mem_unitaryTorus_iff.mpr
  have hcoe : (((MulAut.conj u⁻¹).toMonoidHom g : unitaryGroup n ℂ) : Matrix n n ℂ) =
      star U * (g : Matrix n n ℂ) * U := by
    simp [MulAut.conj_apply, ← Unitary.star_eq_inv, u]
  rw [hcoe, hd ⟨g, hg⟩]
  exact isDiag_diagonal _

/-- The diagonal unitary subgroup is a torus: it is compact, connected, and commutative. -/
theorem isTorus_unitaryTorus : Lie.IsTorus (unitaryTorus n) := by
  have hset : (unitaryTorus n : Set (unitaryGroup n ℂ)) = Set.range (unitaryTorusHom n) :=
    Set.ext fun _ => mem_unitaryTorus_iff_exists_unitaryTorusHom
  exact ⟨hset ▸ isCompact_range continuous_unitaryTorusHom,
    hset ▸ isConnected_range continuous_unitaryTorusHom, inferInstance⟩

/-- The diagonal torus is a maximal torus of `U(n)`. -/
theorem isMaximalTorus_unitaryTorus : Lie.IsMaximalTorus (unitaryTorus n) := by
  rw [Lie.isMaximalTorus_iff]
  refine ⟨isTorus_unitaryTorus, fun H hH hle => ?_⟩
  have := hH.isMulCommutative
  exact (eq_unitaryTorus_of_isMulCommutative hle).le

/-- Every maximal torus of `U(n)` is conjugate to the diagonal torus. -/
theorem exists_map_conj_eq_unitaryTorus {T : Subgroup (unitaryGroup n ℂ)}
    (hT : Lie.IsMaximalTorus T) :
    ∃ u : unitaryGroup n ℂ, T.map (MulAut.conj u).toMonoidHom = unitaryTorus n := by
  have := hT.isTorus.isMulCommutative
  obtain ⟨u, hu⟩ := exists_map_conj_le_unitaryTorus (H := T)
  let e := ContinuousAut.conj u
  have he : e.toMulEquiv = MulAut.conj u := ContinuousAut.toMulEquiv_conj u
  refine ⟨u, ?_⟩
  rw [← he] at hu ⊢
  exact (hT.map_mulEquiv e.toMulEquiv e.continuous e.symm.continuous).eq_of_le
    isTorus_unitaryTorus hu

/-- The maximal tori of `U(n)` are exactly the conjugates of its diagonal torus. -/
theorem isMaximalTorus_iff_exists_map_conj_eq_unitaryTorus
    {T : Subgroup (unitaryGroup n ℂ)} :
    Lie.IsMaximalTorus T ↔
      ∃ u : unitaryGroup n ℂ, T.map (MulAut.conj u).toMonoidHom = unitaryTorus n := by
  refine ⟨exists_map_conj_eq_unitaryTorus, ?_⟩
  rintro ⟨u, hu⟩
  let e := ContinuousAut.conj u
  have he : e.toMulEquiv = MulAut.conj u := ContinuousAut.toMulEquiv_conj u
  rw [← he] at hu
  have h := isMaximalTorus_unitaryTorus.map_mulEquiv e.toMulEquiv.symm
    e.symm.continuous e.continuous
  rw [← hu] at h
  simpa [Subgroup.map_map] using h

/-- Any two maximal tori of `U(n)` are conjugate. -/
theorem exists_map_conj_eq_of_isMaximalTorus {T S : Subgroup (unitaryGroup n ℂ)}
    (hT : Lie.IsMaximalTorus T) (hS : Lie.IsMaximalTorus S) :
    ∃ u : unitaryGroup n ℂ, T.map (MulAut.conj u).toMonoidHom = S := by
  obtain ⟨u, hu⟩ := exists_map_conj_eq_unitaryTorus hT
  obtain ⟨v, hv⟩ := exists_map_conj_eq_unitaryTorus hS
  refine ⟨v⁻¹ * u, ?_⟩
  apply (Subgroup.map_injective (f := (MulAut.conj v).toMonoidHom)
    (MulAut.conj v).injective)
  rw [hv, Subgroup.map_map]
  have hcomp : (MulAut.conj v).toMonoidHom.comp (MulAut.conj (v⁻¹ * u)).toMonoidHom =
      (MulAut.conj u).toMonoidHom := by
    ext g
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, hu]

end TauCeti
