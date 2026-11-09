/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Deformation
public import TauCeti.Topology.Homotopy.Extension.NDRPair
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# Regular sublevels are closed cofibrations

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let `a`
be a regular value of `f` such that the band `f⁻¹[a, b]` is compact for some `b > a`. Then the
sublevel `M_a = {f ≤ a}` has the homotopy extension property in `M`
(`TauCeti.hasHomotopyExtensionProperty_sublevel`) and in every sublevel `M_b` with `a ≤ b` whose
band `f⁻¹[a, b]` is compact (`TauCeti.hasHomotopyExtensionProperty_sublevel_sublevel`). Since
`M_a` is closed, these inclusions are closed cofibrations.

The proof uses a collar above the regular level. A regular level has a neighbourhood free of
critical points, so for some `a' ∈ (a, b]` the band `f⁻¹[a, a']` is a compact band without
critical points, and the flow lowering `f` through it deformation retracts `M_{a'}` onto `M_a`
relative to `M_a` (`TauCeti.exists_sublevelDeformation`). The function `(f - a) / (a' - a)`,
truncated to `[0, 1]`, vanishes exactly on `M_a` and is less than one only on `M_{a'}`, so the
deformation cut off by it is NDR data for `M_a` (`TauCeti.NDRPair.ofHomotopyRel`). That
deformation moves points only inside `M_{a'}`, so it restricts to every sublevel `M_b` with
`a' ≤ b` (`TauCeti.NDRPair.restrict`).

For a proper Morse function bounded below, the sublevels at an increasing sequence of regular
values therefore form a tower of closed cofibrations exhausting `M`. This is what is needed to
compare `M` with a CW complex built stage by stage, one cell for each critical point: a map of such
towers which is a homotopy equivalence at every stage is a homotopy equivalence of the unions.

## Main results

* `TauCeti.hasHomotopyExtensionProperty_sublevel`: a regular sublevel with a compact band above it
  has the homotopy extension property in `M`.
* `TauCeti.hasHomotopyExtensionProperty_sublevel_sublevel`: a regular sublevel `M_a` has the
  homotopy extension property in `M_b` whenever the band `f⁻¹[a, b]` is compact.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1, for the deformation across a band without critical points, and §3, for the
  sublevels of a proper Morse function.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, the section
  The Homotopy Extension Property, for subspaces with a mapping cylinder neighbourhood.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ} {a b : ℝ}

/-- NDR data for a regular sublevel `{f ≤ a}` of `M` whose deformation keeps every point of the
sublevel `{f ≤ b}` in that sublevel. It is obtained by cutting off the deformation retraction of a
collar `{f ≤ a'}`, `a < a' ≤ b`, onto `{f ≤ a}`. -/
private theorem exists_ndrPair_sublevel (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a) :
    ∃ N : NDRPair {x : M | f x ≤ a},
      ∀ (t : unitInterval) {x : M}, f x ≤ b → f (N.deformation (t, x)) ≤ b := by
  -- A collar `f⁻¹[a, a']` without critical points above the regular level.
  obtain ⟨a', ⟨haa', ha'b⟩, hcrit⟩ :=
    exists_mem_Ioc_forall_notMem_criticalPoints (hf.of_le (by simp)) hab hcompact ha
  have hcollar : IsCompact (f ⁻¹' Icc a a') :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (preimage_mono (Icc_subset_Icc_right ha'b))
  obtain ⟨r, -, ⟨D⟩⟩ := exists_sublevelDeformation hf haa'.le hcollar
    fun x h₁ h₂ hx ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨h₁, h₂⟩
  rw [sublevelInclusion_eq_inclusion] at D
  have hpos : 0 < a' - a := sub_pos.2 haa'
  -- The control function `(f - a) / (a' - a)`, truncated to `[0, 1]`.
  let u : C(M, unitInterval) := ⟨fun x ↦ projIcc 0 1 zero_le_one ((f x - a) / (a' - a)),
    continuous_projIcc.comp ((hf.continuous.sub continuous_const).div_const _)⟩
  have hu (x : M) : u x = 0 ↔ x ∈ {x | f x ≤ a} := by
    simp only [u, ContinuousMap.coe_mk, projIcc_eq_zero, div_le_iff₀ hpos, zero_mul,
      sub_nonpos, mem_ofPred_eq]
  have huU (x : M) (hx : u x < 1) : x ∈ {x | f x ≤ a'} := by
    by_contra hx'
    refine hx.ne (projIcc_eq_one.2 ((one_le_div hpos).2 ?_))
    simp only [mem_ofPred_eq, not_le] at hx'
    linarith
  refine ⟨NDRPair.ofHomotopyRel (sublevel_mono f haa'.le) D.symm u hu huU, fun t x hx ↦ ?_⟩
  by_cases hxU : x ∈ {x | f x ≤ a'}
  · rw [NDRPair.ofHomotopyRel_deformation_of_mem D.symm u hu huU t hxU]
    exact (D.symm _).2.trans ha'b
  · rwa [NDRPair.ofHomotopyRel_deformation_of_notMem D.symm u hu huU t hxU]

/-- **A regular sublevel is a closed cofibration.** If `f` is smooth, `a` is a regular value of
`f`, and the band `f⁻¹[a, b]` is compact for some `b > a`, then the sublevel `{f ≤ a}` has the
homotopy extension property in `M`. -/
theorem hasHomotopyExtensionProperty_sublevel (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a) :
    HasHomotopyExtensionProperty {x : M | f x ≤ a} :=
  (exists_ndrPair_sublevel hf hab hcompact ha).choose.hasHomotopyExtensionProperty

/-- **The inclusion of regular sublevels is a closed cofibration.** If `f` is smooth, `a ≤ b`,
the band `f⁻¹[a, b]` is compact and `a` is a regular value of `f`, then the sublevel `{f ≤ a}` has
the homotopy extension property in the sublevel `{f ≤ b}`. The value `b` need not be regular, and
the band may contain critical points. -/
theorem hasHomotopyExtensionProperty_sublevel_sublevel (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a) :
    HasHomotopyExtensionProperty {x : {x : M | f x ≤ b} | f x ≤ a} := by
  rcases hab.eq_or_lt with rfl | hab
  · -- For `a = b` the subset is the whole sublevel.
    have huniv : {x : {x : M | f x ≤ a} | f x ≤ a} = univ := eq_univ_of_forall fun x ↦ x.2
    rw [huniv]
    exact isClopen_univ.hasHomotopyExtensionProperty
  obtain ⟨N, hN⟩ := exists_ndrPair_sublevel hf hab hcompact ha
  exact (N.restrict {x | f x ≤ b} fun t _ hx ↦ hN t hx).hasHomotopyExtensionProperty

end TauCeti
