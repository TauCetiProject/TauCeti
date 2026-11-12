/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Horodisc
import TauCeti.Analysis.Complex.Fuchsian.Polygon.CuspDatum
import TauCeti.Analysis.Complex.Fuchsian.ProperAction
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Truncation
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Local finiteness of cuspidal polygon translates

The translates of a convex hyperbolic polygon by a discrete subgroup of `PSL(2, ℝ)` are locally
finite whenever every ideal vertex is a cusp of the group. No side pairing or coverage of the
upper half-plane is required.

Normalized cusp data supply a uniform bound on the heights of all translates of a neighbourhood
of any point, by `CuspDatum.exists_isOpen_mem_forall_im_scaling_smul_smul_le`. Truncating the
polygon at these heights leaves a compact core, by `ConvexPolygon.isCompact_carrier_diff_iUnion`.
Every tile meeting the chosen neighbourhood meets a translate of that core; proper discontinuity
then gives local finiteness. This accounts for the noncompact cusp tails when constructing
fundamental polygons.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 9.
* Svetlana Katok, *Fuchsian Groups*, Chapters 3–4.
-/

public section

open Set Topology UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint

namespace TauCeti.UpperHalfPlane.ConvexPolygon

variable {n : ℕ} [NeZero n] (P : ConvexPolygon n) {Γ : Subgroup PSL(2, ℝ)}

/-- A discrete group's translates of a convex hyperbolic polygon are locally finite if every
ideal vertex is a cusp of the group. The polygon need not meet every orbit or admit side pairings.
-/
theorem locallyFinite_smul_carrier_of_isCuspPoint [DiscreteTopology Γ]
    (hcusp : ∀ i c, P.vertex i = .inr c → Γ.IsCuspPoint c) :
    LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier := by
  classical
  -- Only ideal vertices require cusp data; this also handles polygons with no ideal vertices.
  let I := {i : Fin n // (P.vertex i).isRight}
  obtain ⟨D, -, g, hgD, hg⟩ := P.exists_cuspDatum_scaling hcusp
  intro z
  -- All translates of this neighbourhood have bounded height in each cusp coordinate.
  choose S hS hz A hA using fun i : I ↦
    TauCeti.Subgroup.CuspDatum.exists_isOpen_mem_forall_im_scaling_smul_smul_le (D i) z
  let U : Set ℍ := ⋂ i : I, S i
  have hUz : U ∈ 𝓝 z := (isOpen_iInter_of_finite hS).mem_nhds (mem_iInter.mpr hz)
  let B (i : Fin n) : ℝ := if hi : (P.vertex i).isRight then A ⟨i, hi⟩ else 0
  let K : Set ℍ :=
    P.carrier \ ⋃ i, ⋃ (_ : (P.vertex i).isRight), {w : ℍ | B i < (g i • w).im}
  have hK : IsCompact K := P.isCompact_carrier_diff_iUnion g hg B
  obtain ⟨V, hVz, hfinite⟩ := (TauCeti.locallyFinite_smul_of_isCompact (Γ := Γ) hK) z
  refine ⟨U ∩ V, Filter.inter_mem hUz hVz, hfinite.subset ?_⟩
  rintro γ ⟨w, hwP, hwU, hwV⟩
  obtain ⟨x, hx, rfl⟩ := mem_smul_set.mp hwP
  refine ⟨(γ : PSL(2, ℝ)) • x, smul_mem_smul_set ⟨hx, ?_⟩, hwV⟩
  intro hxUnion
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxUnion
  have hbound := hA ⟨i, hi⟩ γ⁻¹ ((γ : PSL(2, ℝ)) • x)
    (mem_iInter.mp hwU ⟨i, hi⟩)
  have hle : (g i • x).im ≤ B i := by
    simpa only [hgD i hi, B, dite_eq_left hi, Subgroup.smul_def, Subgroup.coe_inv,
      inv_smul_smul] using hbound
  exact hxi.not_ge hle

end TauCeti.UpperHalfPlane.ConvexPolygon
