/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Convolution
public import TauCeti.Topology.Algebra.Group.LocallyConstant.CompactSupport
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact

/-!
# The Hecke algebra has a unit exactly when the group is discrete

Let `G` be a locally profinite group (a Hausdorff, weakly locally compact, nonarchimedean
topological group), `A` a nonzero commutative semiring and `μ` an `A`-valued Haar measure on `G`.

* If some `e ∈ C_c^∞(G, A)` is a left unit for convolution, `e ⋆ f = f` for every `f`, then `G`
  is discrete (`TauCeti.HaarMeasureWithValues.discreteTopology_of_forall_convolution_eq`), and
  likewise for a right unit
  (`TauCeti.HaarMeasureWithValues.discreteTopology_of_forall_convolution_eq'`). Indeed `e` is
  left invariant under some compact open subgroup `U`, so `e ⋆ f` and hence every `f` is; testing
  on the indicators of compact open subgroups puts `U` inside all of them, so `U = {1}`.
* On a discrete group, a multiple `c • 1_{{1}}` of the point mass at `1` convolves as
  `(c μ({1})) •` on both sides
  (`TauCeti.HaarMeasureWithValues.convolution_pointIndicator_left`,
  `TauCeti.HaarMeasureWithValues.convolution_pointIndicator_right`), so `μ({1})⁻¹ • 1_{{1}}` is a
  unit when `μ({1})` is invertible. This holds when `μ` gives unit volume to some compact open
  subgroup `U₀`, which is finite with `μ(U₀) = |U₀| μ({1})`.

Together: when `μ` gives a compact open subgroup a unit volume (for instance when `μ` is
normalised on a compact open subgroup of invertible pro-order), the Hecke algebra `H(G, A)` has a
two-sided identity element if and only if `G` is discrete
(`TauCeti.HeckeAlgebra.exists_forall_mul_eq_iff_discreteTopology`).

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §2.1, pp. 11–12.
* C. J. Bushnell and G. Henniart, *The Local Langlands Conjecture for GL(2)*, Grundlehren der
  mathematischen Wissenschaften 335, Springer, 2006, §4.1, pp. 33–34.
-/

public section

open Set Function TopologicalSpace LocallyConstant
open scoped Pointwise

namespace TauCeti

variable {A G : Type*} [CommSemiring A] [Group G] [TopologicalSpace G]

namespace HaarMeasureWithValues

section Discrete

variable [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G] [T2Space G]

/-- An element lying in every compact open subgroup of a Hausdorff locally profinite group is the
identity: a compact open subgroup inside the neighbourhood `{u}ᶜ` of `1` avoids `u ≠ 1`. -/
private theorem eq_one_of_forall_mem {u : G}
    (h : ∀ V : OpenSubgroup G, IsCompact (V : Set G) → u ∈ V) : u = 1 := by
  by_contra hne
  obtain ⟨V, hVc, hVu⟩ := (NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup
    (G := G)).mem_iff.1 (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
  exact hVu (h V hVc) rfl

variable [Nontrivial A] (μ : HaarMeasureWithValues A G)

/-- **A left unit forces discreteness.** If `e ⋆ f = f` for every test function `f` on a locally
profinite group and `A` is nonzero, the group is discrete. -/
theorem discreteTopology_of_forall_convolution_eq {e : compactlySupported A G A}
    (he : ∀ f, μ.convolution e f = f) : DiscreteTopology G := by
  classical
  obtain ⟨U, -, hU⟩ :=
    LocallyConstant.exists_isCompact_openSubgroup_forall_mul_eq
      (mem_compactlySupported.1 e.property)
  -- Every `u ∈ U` fixes `e`, hence `e ⋆ f = f` for every `f`.
  have hfix (u : G) (hu : u ∈ U) (f : compactlySupported A G A) :
      compactlySupportedRep A G G A u f = f := by
    have heu : compactlySupportedRep A G G A u e = e := by
      ext x
      simp [compactlySupportedRep_apply_coe, (hU u⁻¹ (inv_mem hu) x).1]
    rw [← he f, ← convolution_compactlySupportedRep_left, heu]
  refine discreteTopology_of_isOpen_singleton_one ?_
  convert U.isOpen using 1
  refine (Set.ext fun u ↦ ⟨fun h ↦ h ▸ U.one_mem, fun hu ↦ ?_⟩)
  refine eq_one_of_forall_mem fun V hV ↦ by_contra fun huV ↦ ?_
  have := congrArg (fun f : compactlySupported A G A ↦ (f : LocallyConstant G A) u)
    (hfix u hu ⟨compactOpenIndicator (V.toCompactOpens hV) 1,
      compactOpenIndicator_mem_compactlySupported _ 1⟩)
  dsimp only at this
  rw [compactlySupportedRep_apply_coe, smul_eq_mul, inv_mul_cancel,
    compactOpenIndicator_of_mem (OpenSubgroup.mem_toCompactOpens.2 V.one_mem),
    compactOpenIndicator_of_notMem (mt OpenSubgroup.mem_toCompactOpens.1 huV)] at this
  exact one_ne_zero this

/-- **A right unit forces discreteness.** If `f ⋆ e = f` for every test function `f` on a locally
profinite group and `A` is nonzero, the group is discrete. -/
theorem discreteTopology_of_forall_convolution_eq' {e : compactlySupported A G A}
    (he : ∀ f, μ.convolution f e = f) : DiscreteTopology G := by
  classical
  obtain ⟨U, -, hU⟩ :=
    LocallyConstant.exists_isCompact_openSubgroup_forall_mul_eq
      (mem_compactlySupported.1 e.property)
  -- Every `u ∈ U`, acting by right translation, fixes `e`, hence every `f = f ⋆ e`.
  have hfix (u : G) (hu : u ∈ U) (f : compactlySupported A G A) :
      compactlySupportedRep A Gᵐᵒᵖ G A (MulOpposite.op u) f = f := by
    have heu : compactlySupportedRep A Gᵐᵒᵖ G A (MulOpposite.op u) e = e := by
      ext x
      simp [compactlySupportedRep_apply_coe, (hU u⁻¹ (inv_mem hu) x).2]
    rw [← he f, ← convolution_compactlySupportedRep_right, heu]
  refine discreteTopology_of_isOpen_singleton_one ?_
  convert U.isOpen using 1
  refine (Set.ext fun u ↦ ⟨fun h ↦ h ▸ U.one_mem, fun hu ↦ ?_⟩)
  refine eq_one_of_forall_mem fun V hV ↦ by_contra fun huV ↦ ?_
  have := congrArg (fun f : compactlySupported A G A ↦ (f : LocallyConstant G A) u)
    (hfix u hu ⟨compactOpenIndicator (V.toCompactOpens hV) 1,
      compactOpenIndicator_mem_compactlySupported _ 1⟩)
  dsimp only at this
  rw [compactlySupportedRep_apply_coe, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_inv,
    MulOpposite.unop_op, mul_inv_cancel,
    compactOpenIndicator_of_mem (OpenSubgroup.mem_toCompactOpens.2 V.one_mem),
    compactOpenIndicator_of_notMem (mt OpenSubgroup.mem_toCompactOpens.1 huV)] at this
  exact one_ne_zero this

end Discrete

section PointMass

variable [IsTopologicalGroup G] [T2Space G] [DiscreteTopology G] (μ : HaarMeasureWithValues A G)

/-- On a discrete group, convolving on the left with the multiple `c • 1_{{1}}` of the point mass
at `1` multiplies by `c μ({1})`. -/
theorem convolution_pointIndicator_left (c : A) (f : compactlySupported A G A) :
    μ.convolution ⟨compactOpenIndicator ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ c,
        compactOpenIndicator_mem_compactlySupported _ c⟩ f =
      (c * μ ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩) • f := by
  classical
  ext x
  rw [convolution_apply]
  -- The integrand `y ↦ c 1_{{1}}(y) f(y⁻¹x)` is `(c f(x)) • 1_{{1}}`.
  have h : compactlySupported.sliceRight A A x (convolutionKernel
      ⟨compactOpenIndicator ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ c,
        compactOpenIndicator_mem_compactlySupported _ c⟩ f) =
      ⟨compactOpenIndicator ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩
        (c * (f : LocallyConstant G A) x), compactOpenIndicator_mem_compactlySupported _ _⟩ := by
    ext y
    by_cases hy : y = 1
    · subst hy
      simp
    · simp [hy]
  rw [h, integral_compactOpenIndicator]
  simp only [smul_eq_mul, Submodule.coe_smul, LocallyConstant.coe_smul, Pi.smul_apply]
  ring

/-- On a discrete group, convolving on the right with the multiple `c • 1_{{1}}` of the point mass
at `1` multiplies by `c μ({1})`. -/
theorem convolution_pointIndicator_right (c : A) (f : compactlySupported A G A) :
    μ.convolution f ⟨compactOpenIndicator ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ c,
        compactOpenIndicator_mem_compactlySupported _ c⟩ =
      (c * μ ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩) • f := by
  classical
  ext x
  rw [convolution_apply]
  -- The integrand `y ↦ f(y) c 1_{{1}}(y⁻¹x)` is `(f(x) c) • 1_{{x}}`, and `{x} = x • {1}`.
  have h : compactlySupported.sliceRight A A x (convolutionKernel f
      ⟨compactOpenIndicator ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ c,
        compactOpenIndicator_mem_compactlySupported _ c⟩) =
      ⟨compactOpenIndicator (x • ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ :
        CompactOpens G) ((f : LocallyConstant G A) x * c),
        compactOpenIndicator_mem_compactlySupported _ _⟩ := by
    ext y
    by_cases hy : y = x
    · subst hy
      simp
    · have hy' : y⁻¹ * x ≠ 1 := fun h ↦ hy (inv_mul_eq_one.1 h)
      simp [hy', hy]
  rw [h, integral_compactOpenIndicator, apply_smul]
  simp only [smul_eq_mul, Submodule.coe_smul, LocallyConstant.coe_smul, Pi.smul_apply]
  ring

end PointMass

end HaarMeasureWithValues

namespace HeckeAlgebra

variable [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G] [T2Space G] [Nontrivial A]
  (μ : HaarMeasureWithValues A G)

/-- **The Hecke algebra is unital exactly when the group is discrete.** For a locally profinite
group `G`, a nonzero coefficient semiring `A` and an `A`-valued Haar measure `μ` giving some
compact open subgroup `U₀` a unit volume, `H(G, A)` has a two-sided identity element if and only
if `G` is discrete. On a discrete group the identity is `μ({1})⁻¹ • 1_{{1}}`. -/
theorem exists_forall_mul_eq_iff_discreteTopology {U₀ : OpenSubgroup G}
    (hU₀ : IsCompact (U₀ : Set G)) (hμ : IsUnit (μ (U₀.toCompactOpens hU₀))) :
    (∃ e : HeckeAlgebra μ, ∀ f, e * f = f ∧ f * e = f) ↔ DiscreteTopology G := by
  refine ⟨fun ⟨e, he⟩ ↦ μ.discreteTopology_of_forall_convolution_eq (e := e.toCompactlySupported)
    fun f ↦ congrArg toCompactlySupported (he ⟨f⟩).1, fun _ ↦ ?_⟩
  -- `{1}` is a compact open subgroup, and `μ(U₀) = [U₀ : 1] μ({1})`, so `μ({1})` is a unit.
  let W : OpenSubgroup G := ⟨⊥, isOpen_discrete _⟩
  have hWmem (g : G) : g ∈ W ↔ g = 1 := Subgroup.mem_bot
  have hW : IsCompact (W : Set G) := by
    convert (isCompact_singleton : IsCompact ({1} : Set G))
  have hWP : W.toCompactOpens hW = ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ := by
    ext g
    exact (OpenSubgroup.mem_toCompactOpens).trans (hWmem g)
  have hWU : W ≤ U₀ := fun g hg ↦ by
    rw [(hWmem g).1 hg]
    exact U₀.one_mem
  have hP : IsUnit (μ ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩) := by
    rw [μ.apply_toCompactOpens_eq_relIndex_smul hU₀ hW hWU, hWP, nsmul_eq_mul] at hμ
    exact isUnit_of_mul_isUnit_right hμ
  refine ⟨⟨⟨compactOpenIndicator ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩
    (↑hP.unit⁻¹ : A), compactOpenIndicator_mem_compactlySupported _ _⟩⟩, fun f ↦ ⟨?_, ?_⟩⟩
  · ext1
    rw [toCompactlySupported_mul, HaarMeasureWithValues.convolution_pointIndicator_left,
      IsUnit.val_inv_mul, one_smul]
  · ext1
    rw [toCompactlySupported_mul, HaarMeasureWithValues.convolution_pointIndicator_right,
      IsUnit.val_inv_mul, one_smul]

end HeckeAlgebra

end TauCeti
