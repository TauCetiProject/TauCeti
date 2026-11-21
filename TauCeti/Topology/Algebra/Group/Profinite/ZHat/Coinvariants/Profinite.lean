/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Coinvariants.Basic
public import TauCeti.Topology.Algebra.Module.Compact
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Extension
import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup
import TauCeti.Topology.Algebra.GroupAction.TypeTags
import TauCeti.Topology.Algebra.GroupExtension.FactorSet

/-!
# First cohomology of the profinite integers with profinite and rational coefficients

Let `M` be a topological abelian group with a continuous action of the profinite integers `zHat`.
Evaluation of continuous `1`-cocycles at the topological generator `zHat.gen` is the homomorphism
`TauCeti.zHat.evalGen M : H¹(zHat, M) →+ M ⧸ (zHat.gen - 1) M`. It is injective whenever `M` is
`T₁` (`TauCeti.zHat.evalGen_injective`), and it is surjective for discrete torsion `M`
(`TauCeti.zHat.evalGen_surjective`). This file proves surjectivity, and hence

`H¹(zHat, M) ≃+ M ⧸ (zHat.gen - 1) M`,

for three further classes of coefficients:

* **profinite coefficients**: `M` compact and totally disconnected;
* **integral coefficients**: `M` a finitely generated Hausdorff topological module over a compact
  totally disconnected ring, for instance a finitely generated `ℤ_p`-module with a continuous
  action, which is a compact module by `TauCeti.IsCompactModule.of_finite`;
* **rational coefficients**: `M` a finite-dimensional Hausdorff topological vector space over a
  locally compact field with an ultrametric norm, for instance a finite-dimensional
  `ℚ_p`-representation of `zHat`.

The action is only assumed to be by continuous additive maps; it need not commute with the scalars.

For profinite `M`, a continuous `1`-cocycle `f` is the same as a continuous homomorphic section
`g ↦ (f g, g)` of the semidirect product `M ⋊ zHat`, which is a profinite group. Such a section
may be prescribed at `zHat.gen` (`GroupExtension.exists_splitting_continuous_zHat_apply_gen_eq`),
so every `m ∈ M` is the value at `zHat.gen` of a continuous cocycle
(`TauCeti.FactorSet.mem_Z1_of_splitting`). This is the argument of
`TauCeti.freeProP.exists_mem_Z1_forall_apply_of_eq` for free pro-`p` groups.

For rational coefficients the orbit of `c ∈ V` under `zHat` is compact, hence bounded in
coordinates. The elements all of whose translates have coordinates bounded by the same constant
form a compact `zHat`-stable subgroup of `V` containing `c`, because the norm of the field is
ultrametric. It is totally disconnected, as `V` is, so the profinite case applies to it.

Some hypothesis of this kind is needed. For the trivial action on the circle `ℝ ⧸ ℤ` or on the
real line, `H¹(zHat, M)` is the group of continuous homomorphisms `zHat → M`. Their images are
profinite subgroups of `M`, hence finite, so evaluation at `zHat.gen` only reaches the torsion
elements of `M ⧸ (zHat.gen - 1) M = M`.

## Main results

* `TauCeti.zHat.exists_apply_gen_eq_of_profinite`,
  `TauCeti.zHat.evalGen_surjective_of_profinite`,
  `TauCeti.zHat.h1AddEquivCoinvariantsOfProfinite`: profinite coefficients.
* `TauCeti.zHat.evalGen_surjective_of_moduleFinite`,
  `TauCeti.zHat.h1AddEquivCoinvariantsOfModuleFinite`: finitely generated modules over a compact
  totally disconnected ring.
* `TauCeti.zHat.exists_apply_gen_eq_of_finiteDimensional`,
  `TauCeti.zHat.evalGen_surjective_of_finiteDimensional`,
  `TauCeti.zHat.h1AddEquivCoinvariantsOfFiniteDimensional`: finite-dimensional vector spaces over a
  locally compact ultrametric field.

## References

* K. Rubin, *Euler Systems*, 1999 draft, Appendix B, Lemma 2.8.
* J.-P. Serre, *Local Fields*, Chapter XIII, §1, Proposition 1, for finite coefficients.
-/

public noncomputable section

namespace TauCeti.zHat

open ContCohomology Topology

universe u v

section Profinite

variable (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [CompactSpace M] [TotallyDisconnectedSpace M] [DistribMulAction zHat.{u} M]
  [ContinuousSMul zHat.{u} M]

variable {M} in
/-- **Every element of a profinite continuous `zHat`-module is the value at `zHat.gen` of a
continuous `1`-cocycle.** -/
theorem exists_apply_gen_eq_of_profinite (m : M) : ∃ f : Z1 zHat.{u} M, f.val gen = m := by
  -- The cocycle is the `M`-component of a continuous homomorphic section of the semidirect
  -- product `M ⋊ zHat` sending `zHat.gen` to `(m, zHat.gen)`. The argument is that of
  -- `TauCeti.freeProP.exists_mem_Z1_forall_apply_of_eq`, with the splitting of extensions of
  -- `zHat` in place of that of extensions of a free pro-`p` group.
  -- The semidirect product is the extension attached to the trivial factor set; it is profinite.
  have _ : IsTopologicalGroup (FactorSet.trivial zHat.{u} (Multiplicative M)).Extension :=
    FactorSet.Extension.isTopologicalGroup FactorSet.continuous_trivial
  obtain ⟨s, hs, hsg⟩ := GroupExtension.exists_splitting_continuous_zHat_apply_gen_eq
    (FactorSet.trivial zHat.{u} (Multiplicative M)).groupExtension
    (by rw [FactorSet.groupExtension_rightHom]; exact FactorSet.continuous_rightHom _)
    ⟨Multiplicative.ofAdd m, gen⟩
    (by rw [FactorSet.groupExtension_rightHom, FactorSet.rightHom_apply])
  exact ⟨⟨_, FactorSet.mem_Z1_of_splitting s hs⟩,
    congrArg (fun z ↦ Multiplicative.toAdd z.left) hsg⟩

/-- **Evaluation at `zHat.gen` is surjective on `H¹(zHat, M)`** for every profinite continuous
`zHat`-module `M`. -/
theorem evalGen_surjective_of_profinite : Function.Surjective (evalGen.{u} M) :=
  evalGen_surjective_of_forall_exists exists_apply_gen_eq_of_profinite.{u}

/-- **First continuous cohomology of `zHat` with profinite coefficients**:
`H¹(zHat, M) ≃+ M ⧸ (zHat.gen - 1) M` via evaluation at `zHat.gen`, for every compact totally
disconnected continuous `zHat`-module `M`. -/
def h1AddEquivCoinvariantsOfProfinite : H1 zHat.{u} M ≃+ M ⧸ (genSubId.{u} M).range :=
  AddEquiv.ofBijective (evalGen.{u} M) ⟨evalGen_injective M, evalGen_surjective_of_profinite M⟩

/-- `h1AddEquivCoinvariantsOfProfinite` acts as `evalGen`. -/
@[simp]
theorem h1AddEquivCoinvariantsOfProfinite_apply (x : H1 zHat.{u} M) :
    h1AddEquivCoinvariantsOfProfinite.{u} M x = evalGen.{u} M x :=
  (rfl)

/-- The underlying additive homomorphism of `h1AddEquivCoinvariantsOfProfinite` is `evalGen`. -/
@[simp]
theorem h1AddEquivCoinvariantsOfProfinite_toAddMonoidHom :
    (h1AddEquivCoinvariantsOfProfinite.{u} M : H1 zHat.{u} M →+ M ⧸ (genSubId.{u} M).range) =
      evalGen.{u} M :=
  (rfl)

/-- Evaluating at `zHat.gen` cancels the inverse of `h1AddEquivCoinvariantsOfProfinite`. -/
@[simp]
theorem evalGen_h1AddEquivCoinvariantsOfProfinite_symm (q : M ⧸ (genSubId.{u} M).range) :
    evalGen.{u} M ((h1AddEquivCoinvariantsOfProfinite.{u} M).symm q) = q :=
  (h1AddEquivCoinvariantsOfProfinite.{u} M).apply_symm_apply q

/-- Applying the inverse of `h1AddEquivCoinvariantsOfProfinite` to `evalGen M x` recovers `x`. -/
@[simp]
theorem h1AddEquivCoinvariantsOfProfinite_symm_evalGen (x : H1 zHat.{u} M) :
    (h1AddEquivCoinvariantsOfProfinite.{u} M).symm (evalGen.{u} M x) = x :=
  (h1AddEquivCoinvariantsOfProfinite.{u} M).symm_apply_apply x

end Profinite

section ModuleFinite

variable (R : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [TotallyDisconnectedSpace R]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T2Space M]
  [Module R M] [Module.Finite R M] [ContinuousSMul R M]
  [DistribMulAction zHat.{u} M] [ContinuousSMul zHat.{u} M]

include R in
/-- **Evaluation at `zHat.gen` is surjective on `H¹(zHat, M)`** for every finitely generated
Hausdorff topological module `M` over a compact totally disconnected ring, for instance a finitely
generated `ℤ_p`-module, with a continuous action of `zHat`. -/
theorem evalGen_surjective_of_moduleFinite : Function.Surjective (evalGen.{u} M) :=
  have hM := IsCompactModule.of_finite (R := R) (M := M)
  have := hM.compactSpace
  have := hM.totallyDisconnectedSpace
  evalGen_surjective_of_profinite M

/-- **First continuous cohomology of `zHat` with integral coefficients**:
`H¹(zHat, M) ≃+ M ⧸ (zHat.gen - 1) M` via evaluation at `zHat.gen`, for every finitely generated
Hausdorff topological module `M` over a compact totally disconnected ring, for instance a finitely
generated `ℤ_p`-module, with a continuous action of `zHat`. -/
def h1AddEquivCoinvariantsOfModuleFinite : H1 zHat.{u} M ≃+ M ⧸ (genSubId.{u} M).range :=
  AddEquiv.ofBijective (evalGen.{u} M)
    ⟨evalGen_injective M, evalGen_surjective_of_moduleFinite R M⟩

/-- `h1AddEquivCoinvariantsOfModuleFinite` acts as `evalGen`. -/
@[simp]
theorem h1AddEquivCoinvariantsOfModuleFinite_apply (x : H1 zHat.{u} M) :
    h1AddEquivCoinvariantsOfModuleFinite.{u} R M x = evalGen.{u} M x :=
  (rfl)

/-- The underlying additive homomorphism of `h1AddEquivCoinvariantsOfModuleFinite` is `evalGen`. -/
@[simp]
theorem h1AddEquivCoinvariantsOfModuleFinite_toAddMonoidHom :
    (h1AddEquivCoinvariantsOfModuleFinite.{u} R M : H1 zHat.{u} M →+ M ⧸ (genSubId.{u} M).range) =
      evalGen.{u} M :=
  (rfl)

/-- Evaluating at `zHat.gen` cancels the inverse of `h1AddEquivCoinvariantsOfModuleFinite`. -/
@[simp]
theorem evalGen_h1AddEquivCoinvariantsOfModuleFinite_symm (q : M ⧸ (genSubId.{u} M).range) :
    evalGen.{u} M ((h1AddEquivCoinvariantsOfModuleFinite.{u} R M).symm q) = q :=
  (h1AddEquivCoinvariantsOfModuleFinite.{u} R M).apply_symm_apply q

/-- Applying the inverse of `h1AddEquivCoinvariantsOfModuleFinite` to `evalGen M x` recovers
`x`. -/
@[simp]
theorem h1AddEquivCoinvariantsOfModuleFinite_symm_evalGen (x : H1 zHat.{u} M) :
    (h1AddEquivCoinvariantsOfModuleFinite.{u} R M).symm (evalGen.{u} M x) = x :=
  (h1AddEquivCoinvariantsOfModuleFinite.{u} R M).symm_apply_apply x

end ModuleFinite

section FiniteDimensional

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  (V : Type v) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [Module K V] [ContinuousSMul K V] [FiniteDimensional K V]
  [DistribMulAction zHat.{u} V] [ContinuousSMul zHat.{u} V]

include K in
/-- Every element `c` of a finite-dimensional Hausdorff vector space over a locally compact
ultrametric field with a continuous `zHat`-action lies in a compact totally disconnected
`zHat`-stable additive subgroup. -/
private theorem exists_isCompact_addSubgroup (c : V) :
    ∃ N : AddSubgroup V, c ∈ N ∧ (∀ g : zHat.{u}, ∀ x ∈ N, g • x ∈ N) ∧ IsCompact (N : Set V) ∧
      TotallyDisconnectedSpace N := by
  let e : V ≃L[K] (Fin (Module.finrank K V) → K) :=
    (Module.finBasis K V).equivFun.toContinuousLinearEquiv
  have : TotallyDisconnectedSpace V := e.symm.toHomeomorph.totallyDisconnectedSpace
  -- The orbit of `c` is compact, so its coordinates are bounded by some `r > 0`.
  obtain ⟨r₀, hr₀⟩ := isCompact_univ.exists_bound_of_continuousOn
    (e.continuous.comp (continuous_id.smul continuous_const) : Continuous fun g : zHat.{u} ↦
      e (g • c)).continuousOn
  have hr : 0 < max r₀ 1 := lt_max_of_lt_right one_pos
  -- `T` is the closed ball of radius `r` in coordinates, an additive subgroup since the norm is
  -- ultrametric, and `N` the elements all of whose translates lie in `T`.
  let T : AddSubgroup V := (IsUltrametricDist.closedBall_openAddSubgroup _ hr).toAddSubgroup.comap
    (e : V →+ (Fin (Module.finrank K V) → K))
  have hT (x : V) : x ∈ T ↔ ‖e x‖ ≤ max r₀ 1 := by
    simp [T, IsUltrametricDist.closedBall_openAddSubgroup]
  let N : AddSubgroup V := ⨅ g : zHat.{u}, T.comap (DistribSMul.toAddMonoidHom V g)
  have hN (x : V) : x ∈ N ↔ ∀ g : zHat.{u}, g • x ∈ T := by
    simp [N, AddSubgroup.mem_iInf]
  refine ⟨N, (hN c).mpr fun g ↦ (hT _).mpr ((hr₀ g trivial).trans (le_max_left _ _)),
    fun g x hx ↦ (hN _).mpr fun g' ↦ by rw [smul_smul]; exact (hN x).mp hx _, ?_, inferInstance⟩
  have hTc : IsCompact (T : Set V) := by
    have : (T : Set V) = e ⁻¹' Metric.closedBall 0 (max r₀ 1) := by
      ext x
      simp [hT]
    rw [this]
    exact e.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  have hTcl : IsClosed (T : Set V) := hTc.isClosed
  refine hTc.of_isClosed_subset ?_ fun x hx ↦ by simpa using (hN x).mp hx 1
  have : (N : Set V) = ⋂ g : zHat.{u}, (fun x ↦ g • x) ⁻¹' (T : Set V) := by
    ext x
    simp [hN]
  rw [this]
  exact isClosed_iInter fun g ↦ hTcl.preimage (continuous_const_smul g)

include K in
variable {V} in
/-- **Every element of a finite-dimensional Hausdorff vector space over a locally compact
ultrametric field with a continuous `zHat`-action is the value at `zHat.gen` of a continuous
`1`-cocycle.** The action need not be linear. -/
theorem exists_apply_gen_eq_of_finiteDimensional (c : V) : ∃ f : Z1 zHat.{u} V, f.val gen = c := by
  obtain ⟨N, hcN, hN, hNc, _⟩ := exists_isCompact_addSubgroup.{u} K V c
  let := N.restrictDistribMulAction hN
  have : ContinuousSMul zHat.{u} N := N.restrictDistribMulAction_continuousSMul hN
  have : CompactSpace N := isCompact_iff_compactSpace.mp hNc
  obtain ⟨f, hf⟩ := exists_apply_gen_eq_of_profinite.{u} (⟨c, hcN⟩ : N)
  obtain ⟨hcont, hcoc⟩ := mem_Z1_iff.mp f.2
  -- Composing with the inclusion `N → V` keeps continuity and the cocycle identity.
  refine ⟨⟨fun x ↦ (f.val x : V), mem_Z1_iff.mpr ⟨continuous_subtype_val.comp hcont,
    fun g h ↦ ?_⟩⟩, congrArg Subtype.val hf⟩
  have := congrArg Subtype.val (hcoc g h)
  rwa [AddSubgroup.coe_add, AddSubgroup.restrictDistribMulAction_coe_smul] at this

include K in
/-- **Evaluation at `zHat.gen` is surjective on `H¹(zHat, V)`** for every finite-dimensional
Hausdorff vector space `V` over a locally compact ultrametric field, for instance a
finite-dimensional `ℚ_p`-vector space, with a continuous action of `zHat`. -/
theorem evalGen_surjective_of_finiteDimensional : Function.Surjective (evalGen.{u} V) :=
  evalGen_surjective_of_forall_exists (exists_apply_gen_eq_of_finiteDimensional.{u} K)

/-- **First continuous cohomology of `zHat` with rational coefficients**:
`H¹(zHat, V) ≃+ V ⧸ (zHat.gen - 1) V` via evaluation at `zHat.gen`, for every finite-dimensional
Hausdorff vector space `V` over a locally compact ultrametric field, for instance a
finite-dimensional `ℚ_p`-vector space, with a continuous action of `zHat`. -/
def h1AddEquivCoinvariantsOfFiniteDimensional : H1 zHat.{u} V ≃+ V ⧸ (genSubId.{u} V).range :=
  AddEquiv.ofBijective (evalGen.{u} V)
    ⟨evalGen_injective V, evalGen_surjective_of_finiteDimensional K V⟩

/-- `h1AddEquivCoinvariantsOfFiniteDimensional` acts as `evalGen`. -/
@[simp]
theorem h1AddEquivCoinvariantsOfFiniteDimensional_apply (x : H1 zHat.{u} V) :
    h1AddEquivCoinvariantsOfFiniteDimensional.{u} K V x = evalGen.{u} V x :=
  (rfl)

/-- The underlying additive homomorphism of `h1AddEquivCoinvariantsOfFiniteDimensional` is
`evalGen`. -/
@[simp]
theorem h1AddEquivCoinvariantsOfFiniteDimensional_toAddMonoidHom :
    (h1AddEquivCoinvariantsOfFiniteDimensional.{u} K V :
      H1 zHat.{u} V →+ V ⧸ (genSubId.{u} V).range) = evalGen.{u} V :=
  (rfl)

/-- Evaluating at `zHat.gen` cancels the inverse of `h1AddEquivCoinvariantsOfFiniteDimensional`. -/
@[simp]
theorem evalGen_h1AddEquivCoinvariantsOfFiniteDimensional_symm (q : V ⧸ (genSubId.{u} V).range) :
    evalGen.{u} V ((h1AddEquivCoinvariantsOfFiniteDimensional.{u} K V).symm q) = q :=
  (h1AddEquivCoinvariantsOfFiniteDimensional.{u} K V).apply_symm_apply q

/-- Applying the inverse of `h1AddEquivCoinvariantsOfFiniteDimensional` to `evalGen V x` recovers
`x`. -/
@[simp]
theorem h1AddEquivCoinvariantsOfFiniteDimensional_symm_evalGen (x : H1 zHat.{u} V) :
    (h1AddEquivCoinvariantsOfFiniteDimensional.{u} K V).symm (evalGen.{u} V x) = x :=
  (h1AddEquivCoinvariantsOfFiniteDimensional.{u} K V).symm_apply_apply x

end FiniteDimensional

end TauCeti.zHat
