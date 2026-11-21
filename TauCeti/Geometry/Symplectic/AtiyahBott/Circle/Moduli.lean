/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.LogDeriv
public import TauCeti.Geometry.Symplectic.AtiyahBott.Circle.Basic

/-!
# The moduli torus of flat connections on the trivial circle bundle

The flat connections `d + i a` on the trivial circle bundle over a manifold `M` are the closed
real `1`-forms `a`, and the gauge group `C^∞(M, U(1))` acts on them by the translations
`a ↦ a - circleLogDeriv u` (`TauCeti.circleGaugeAction`). On a closed oriented surface they form
the zero level of the Atiyah–Bott moment map (`TauCeti.atiyahBottMoment_eq_zero_iff`). This file
computes the quotient, with no compactness or connectedness assumption:

`{flat connections} / C^∞(M, U(1)) ≃ H¹_dR(M) / 2π H¹(M; ℤ)`

(`TauCeti.flatCircleModuliEquiv`). Here `2π H¹(M; ℤ)` denotes the subgroup
`TauCeti.deRhamCohomology.circlePeriodLattice` of de Rham classes whose periods on the first
singular homology group `H₁(M; ℤ)` lie in `2πℤ`. The real logarithmic derivative of a smooth map
`u : M → U(1)` has periods `2π` times the winding numbers of `u`, and conversely every closed form
with periods in `2πℤ` is the real logarithmic derivative of a circle-valued map. So two flat
connections are gauge equivalent exactly when their classes differ by an element of the lattice
(`TauCeti.exists_circleGaugeAction_eq_iff`). Exact forms `df` are the infinitesimal part of this
identification: they are the real logarithmic derivatives of the maps `exp (i f)`.

On a closed oriented surface this quotient is the moduli space of flat `U(1)`-connections on the
trivial bundle. On a connected manifold every connection has the constant maps `U(1)` as its
stabilizer (`TauCeti.circleGaugeAction_apply_eq_self_iff`), so the gauge action is not effective.

## References

* M. F. Atiyah and R. Bott, *The Yang–Mills equations over Riemann surfaces*, Philos. Trans.
  Roy. Soc. London Ser. A 308 (1983), 523–615 (flat connections modulo gauge, and the torus of
  flat `U(1)`-connections).
-/

public section

noncomputable section

open CategoryTheory
open scoped Manifold ContDiff Real

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

variable (I M) in
/-- The real logarithmic derivatives of the smooth circle-valued maps, as a subgroup of the
closed `1`-forms: the gauge orbit of the trivial connection. -/
def circleLogDerivSubgroup : AddSubgroup (closedForms I M 1) where
  carrier := {a | ∃ u : C^∞⟮I, M; 𝓡 1, Circle⟯, u.circleLogDeriv = a.val}
  add_mem' {a b} := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u * v, by rw [ContMDiffMap.circleLogDeriv_mul, hu, hv, Submodule.coe_add]⟩
  zero_mem' := ⟨1, by rw [ContMDiffMap.circleLogDeriv_one, Submodule.coe_zero]⟩
  neg_mem' {a} := by
    rintro ⟨u, hu⟩
    exact ⟨u⁻¹, by rw [ContMDiffMap.circleLogDeriv_inv, hu, Submodule.coe_neg]⟩

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem mem_circleLogDerivSubgroup_iff {a : closedForms I M 1} :
    a ∈ circleLogDerivSubgroup I M ↔ ∃ u : C^∞⟮I, M; 𝓡 1, Circle⟯, u.circleLogDeriv = a.val :=
  Iff.rfl

/-- **The real logarithmic derivatives are the closed forms with periods in `2πℤ`.** A closed
`1`-form is the real logarithmic derivative of a smooth circle-valued map exactly when its de Rham
class lies in `2π H¹(M; ℤ)`. -/
theorem mem_circleLogDerivSubgroup_iff_mk_mem_circlePeriodLattice {a : closedForms I M 1} :
    a ∈ circleLogDerivSubgroup I M ↔
      deRhamCohomology.mk I 1 a ∈ deRhamCohomology.circlePeriodLattice I M := by
  rw [mem_circleLogDerivSubgroup_iff, deRhamCohomology.mk_mem_circlePeriodLattice_iff]

/-- **Gauge equivalence of flat connections.** Two flat connections `a` and `b` on the trivial
circle bundle are related by a gauge transformation exactly when their de Rham classes differ by
an element of `2π H¹(M; ℤ)`. -/
theorem exists_circleGaugeAction_eq_iff {a b : closedForms I M 1} :
    (∃ u : C^∞⟮I, M; 𝓡 1, Circle⟯, circleGaugeAction u a.val = b.val) ↔
      deRhamCohomology.mk I 1 a - deRhamCohomology.mk I 1 b ∈
        deRhamCohomology.circlePeriodLattice I M := by
  rw [← map_sub, ← mem_circleLogDerivSubgroup_iff_mk_mem_circlePeriodLattice,
    mem_circleLogDerivSubgroup_iff]
  refine exists_congr fun u ↦ ?_
  rw [circleGaugeAction_apply, Submodule.coe_sub, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add',
    eq_comm]

/-- Two flat connections define the same gauge orbit exactly when a gauge transformation relates
them. -/
theorem circleLogDerivSubgroup_mk_eq_mk_iff {a b : closedForms I M 1} :
    (QuotientAddGroup.mk a : closedForms I M 1 ⧸ circleLogDerivSubgroup I M) =
        QuotientAddGroup.mk b ↔
      ∃ u : C^∞⟮I, M; 𝓡 1, Circle⟯, circleGaugeAction u a.val = b.val := by
  have hab : -a + b = -(a - b) := by abel
  rw [QuotientAddGroup.eq, hab, AddSubgroup.neg_mem_iff,
    mem_circleLogDerivSubgroup_iff_mk_mem_circlePeriodLattice, exists_circleGaugeAction_eq_iff,
    ← map_sub]

/-- The map from flat connections to `H¹_dR(M) / 2π H¹(M; ℤ)` taking `a` to its de Rham class. -/
private def flatCircleModuliMap :
    closedForms I M 1 →+ deRhamCohomology I M 1 ⧸ deRhamCohomology.circlePeriodLattice I M :=
  (QuotientAddGroup.mk' _).comp (deRhamCohomology.mk I 1).toAddMonoidHom

private theorem flatCircleModuliMap_surjective :
    Function.Surjective (flatCircleModuliMap (I := I) (M := M)) :=
  (QuotientAddGroup.mk'_surjective _).comp (deRhamCohomology.mk_surjective I 1)

private theorem circleLogDerivSubgroup_eq_ker_flatCircleModuliMap :
    circleLogDerivSubgroup I M = (flatCircleModuliMap (I := I) (M := M)).ker := by
  ext a
  rw [AddMonoidHom.mem_ker, flatCircleModuliMap, AddMonoidHom.comp_apply,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    mem_circleLogDerivSubgroup_iff_mk_mem_circlePeriodLattice, LinearMap.toAddMonoidHom_coe]

variable (I M) in
/-- **Flat circle connections modulo gauge.** Taking de Rham classes identifies, as additive
groups, the gauge orbits of flat connections on the trivial circle bundle over `M` with
`H¹_dR(M) / 2π H¹(M; ℤ)`. For a closed surface `M` this quotient is the moduli torus of flat
`U(1)`-connections; no topology on it is constructed here. -/
def flatCircleModuliEquiv :
    closedForms I M 1 ⧸ circleLogDerivSubgroup I M ≃+
      deRhamCohomology I M 1 ⧸ deRhamCohomology.circlePeriodLattice I M :=
  QuotientAddGroup.liftEquiv (circleLogDerivSubgroup I M) flatCircleModuliMap_surjective
    circleLogDerivSubgroup_eq_ker_flatCircleModuliMap

@[simp]
theorem flatCircleModuliEquiv_mk (a : closedForms I M 1) :
    flatCircleModuliEquiv I M (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (deRhamCohomology.mk I 1 a) := by
  simp [flatCircleModuliEquiv, flatCircleModuliMap]

end TauCeti
