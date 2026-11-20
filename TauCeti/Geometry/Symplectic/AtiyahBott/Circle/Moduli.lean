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

namespace deRhamCohomology

variable (I M) in
/-- The lattice `2π H¹(M; ℤ)` in the first de Rham cohomology: the classes whose periods on every
singular `1`-cycle lie in `2πℤ`. -/
def circlePeriodLattice : AddSubgroup (deRhamCohomology I M 1) where
  carrier := {c | ∀ z, ∃ n : ℤ, homologyPeriod c z = n * (2 * π)}
  add_mem' {c d} hc hd z := by
    obtain ⟨m, hm⟩ := hc z
    obtain ⟨n, hn⟩ := hd z
    exact ⟨m + n, by rw [map_add, AddMonoidHom.add_apply, hm, hn]; push_cast; ring⟩
  zero_mem' z := ⟨0, by simp⟩
  neg_mem' {c} hc z := by
    obtain ⟨n, hn⟩ := hc z
    exact ⟨-n, by rw [map_neg, AddMonoidHom.neg_apply, hn]; push_cast; ring⟩

theorem mem_circlePeriodLattice_iff {c : deRhamCohomology I M 1} :
    c ∈ circlePeriodLattice I M ↔ ∀ z, ∃ n : ℤ, homologyPeriod c z = n * (2 * π) :=
  Iff.rfl

end deRhamCohomology

variable (I M) in
/-- The real logarithmic derivatives of the smooth circle-valued maps, as a subgroup of the
closed `1`-forms: the gauge orbit of the trivial connection. -/
def circleGaugeSubgroup : AddSubgroup (closedForms I M 1) where
  carrier := {a | ∃ u : C^∞⟮I, M; 𝓡 1, Circle⟯, circleLogDeriv u = a.1}
  add_mem' {a b} := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u * v, by rw [circleLogDeriv_mul, hu, hv, Submodule.coe_add]⟩
  zero_mem' := ⟨1, by rw [circleLogDeriv_one, Submodule.coe_zero]⟩
  neg_mem' {a} := by
    rintro ⟨u, hu⟩
    exact ⟨u⁻¹, by rw [circleLogDeriv_inv, hu, Submodule.coe_neg]⟩

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem mem_circleGaugeSubgroup_iff {a : closedForms I M 1} :
    a ∈ circleGaugeSubgroup I M ↔ ∃ u : C^∞⟮I, M; 𝓡 1, Circle⟯, circleLogDeriv u = a.1 :=
  Iff.rfl

/-- **The real logarithmic derivatives are the closed forms with periods in `2πℤ`.** A closed
`1`-form is the real logarithmic derivative of a smooth circle-valued map exactly when its de Rham
class lies in `2π H¹(M; ℤ)`. -/
theorem mem_circleGaugeSubgroup_iff_mk_mem_circlePeriodLattice {a : closedForms I M 1} :
    a ∈ circleGaugeSubgroup I M ↔
      deRhamCohomology.mk I 1 a ∈ deRhamCohomology.circlePeriodLattice I M := by
  rw [mem_circleGaugeSubgroup_iff, deRhamCohomology.mem_circlePeriodLattice_iff,
    deRhamCohomology.homologyPeriod_mk]
  refine ⟨fun ⟨u, hu⟩ z ↦ ⟨_, hu ▸ homologyPeriodHom_circleLogDeriv u z⟩, fun h ↦ ?_⟩
  exact exists_circleLogDeriv_eq ((mem_closedForms I a.1).mp a.2) h

/-- **Gauge equivalence of flat connections.** Two flat connections `a` and `b` on the trivial
circle bundle are related by a gauge transformation exactly when their de Rham classes differ by
an element of `2π H¹(M; ℤ)`. -/
theorem exists_circleGaugeAction_eq_iff {a b : closedForms I M 1} :
    (∃ u : C^∞⟮I, M; 𝓡 1, Circle⟯, circleGaugeAction u a.1 = b.1) ↔
      deRhamCohomology.mk I 1 a - deRhamCohomology.mk I 1 b ∈
        deRhamCohomology.circlePeriodLattice I M := by
  rw [← map_sub, ← mem_circleGaugeSubgroup_iff_mk_mem_circlePeriodLattice,
    mem_circleGaugeSubgroup_iff]
  refine exists_congr fun u ↦ ?_
  rw [circleGaugeAction_apply, Submodule.coe_sub, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add',
    eq_comm]

/-- Two flat connections define the same gauge orbit exactly when a gauge transformation relates
them. -/
theorem circleGaugeSubgroup_mk_eq_mk_iff {a b : closedForms I M 1} :
    (QuotientAddGroup.mk a : closedForms I M 1 ⧸ circleGaugeSubgroup I M) = QuotientAddGroup.mk b ↔
      ∃ u : C^∞⟮I, M; 𝓡 1, Circle⟯, circleGaugeAction u a.1 = b.1 := by
  have hab : -a + b = -(a - b) := by abel
  rw [QuotientAddGroup.eq, hab, AddSubgroup.neg_mem_iff,
    mem_circleGaugeSubgroup_iff_mk_mem_circlePeriodLattice, exists_circleGaugeAction_eq_iff,
    ← map_sub]

/-- The map from flat connections to `H¹_dR(M) / 2π H¹(M; ℤ)` taking `a` to its de Rham class. -/
private def flatCircleModuliMap :
    closedForms I M 1 →+ deRhamCohomology I M 1 ⧸ deRhamCohomology.circlePeriodLattice I M :=
  (QuotientAddGroup.mk' _).comp (deRhamCohomology.mk I 1).toAddMonoidHom

private theorem flatCircleModuliMap_surjective :
    Function.Surjective (flatCircleModuliMap (I := I) (M := M)) :=
  (QuotientAddGroup.mk'_surjective _).comp (deRhamCohomology.mk_surjective I 1)

private theorem circleGaugeSubgroup_eq_ker_flatCircleModuliMap :
    circleGaugeSubgroup I M = (flatCircleModuliMap (I := I) (M := M)).ker := by
  ext a
  rw [AddMonoidHom.mem_ker, flatCircleModuliMap, AddMonoidHom.comp_apply,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    mem_circleGaugeSubgroup_iff_mk_mem_circlePeriodLattice]
  rfl

variable (I M) in
/-- **The moduli torus of flat circle connections.** The gauge orbits of flat connections on the
trivial circle bundle over `M` are identified with `H¹_dR(M) / 2π H¹(M; ℤ)` by taking de Rham
classes. -/
def flatCircleModuliEquiv :
    closedForms I M 1 ⧸ circleGaugeSubgroup I M ≃+
      deRhamCohomology I M 1 ⧸ deRhamCohomology.circlePeriodLattice I M :=
  QuotientAddGroup.liftEquiv (circleGaugeSubgroup I M) flatCircleModuliMap_surjective
    circleGaugeSubgroup_eq_ker_flatCircleModuliMap

@[simp]
theorem flatCircleModuliEquiv_mk (a : closedForms I M 1) :
    flatCircleModuliEquiv I M (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (deRhamCohomology.mk I 1 a) :=
  (rfl)

end TauCeti
