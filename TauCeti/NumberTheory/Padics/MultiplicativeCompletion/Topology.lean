/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Open
public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Finite
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Product
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup

/-!
# Topology of the p-adic completion of a local multiplicative group

For a mixed-characteristic nonarchimedean local field `L`, this file proves that
`padicCompletionUnits p L` is a profinite pro-`p` group.  Its topology is the subspace topology
from the product of the finite discrete power-class groups.  The canonical map from `Lˣ` has
dense range: a compatible family can be matched on any finite collection of coordinates by a
representative of its largest coordinate.

## Main results

* `TauCeti.padicCompletionUnitsCompactSpace`: `A(L)` is compact.
* `TauCeti.isProP_padicCompletionUnits`: `A(L)` is pro-`p`.
* `TauCeti.continuous_padicCompletionUnitsAut`: field automorphisms act continuously on `A(L)`.
* `TauCeti.denseRange_padicCompletionUnitsOf`: `Lˣ` is dense in `A(L)`.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [CharZero L]

/-- The coordinatewise action of a field automorphism on the multiplicative `p`-adic completion
is continuous. -/
theorem continuous_padicCompletionUnitsAut (K : Type*) [Field K] [Algebra K L]
    (σ : L ≃ₐ[K] L) : Continuous (padicCompletionUnitsAut p L K σ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro m
  have hσ : Continuous (padicCompletionPowerClassMap p L K σ m) :=
    continuous_of_discreteTopology
  have hm : Continuous (fun x : ↑(padicCompletionUnits p L) ↦ x.1 m) :=
    (continuous_apply m).comp continuous_subtype_val
  exact (hσ.comp hm).congr fun x ↦ (padicCompletionUnitsAut_apply p L K σ x m).symm

private theorem isClosed_padicCompletionUnits :
    IsClosed (padicCompletionUnits p L : Set
      (∀ m : ℕ, Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range)) := by
  have hset : (padicCompletionUnits p L : Set
      (∀ m : ℕ, Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range)) =
      ⋂ m, {x | padicCompletionTransition p L m (x (m + 1)) = x m} := by
    ext x
    rw [Set.mem_iInter]
    exact mem_padicCompletionUnits_iff p L x
  rw [hset]
  exact isClosed_iInter fun m ↦ isClosed_eq
    (continuous_of_discreteTopology.comp (continuous_apply (m + 1))) (continuous_apply m)

/-- The completed multiplicative group of a mixed-characteristic local field is compact, as a
closed subset of a product of finite discrete groups. -/
instance padicCompletionUnitsCompactSpace : CompactSpace ↑(padicCompletionUnits p L) :=
  isCompact_iff_compactSpace.mp (isClosed_padicCompletionUnits p L).isCompact

/-- The completed multiplicative group of a mixed-characteristic local field is pro-`p`: each
power-class group `Lˣ/(Lˣ)^(p^m)` is a `p`-group. -/
theorem isProP_padicCompletionUnits : IsProP p ↑(padicCompletionUnits p L) :=
  (IsProP.pi fun m ↦ IsPGroup.isProP (isPGroup_iff_pow_pow_eq_one.2 fun x ↦
    ⟨m, QuotientGroup.pow_eq_one_quotient_range_powMonoidHom _ x⟩)).subgroup
    (padicCompletionUnits p L)

omit [Fact p.Prime] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [CharZero L] in
private theorem padicCompletionUnits_apply_eq_mk_of_le
    (x : ↑(padicCompletionUnits p L)) {n m : ℕ} (hnm : n ≤ m) (u : Lˣ)
    (hu : x.1 m = QuotientGroup.mk' _ u) : x.1 n = QuotientGroup.mk' _ u := by
  induction m, hnm using Nat.le_induction with
  | base => exact hu
  | succ m _ ih =>
      apply ih
      rw [← (mem_padicCompletionUnits_iff p L x.1).mp x.2 m, hu]
      exact padicCompletionTransition_mk p L m u

omit [Fact p.Prime] [ValuativeRel L] [IsNonarchimedeanLocalField L] [CharZero L] in
/-- The canonical map `Lˣ → A(L)` has dense range. -/
theorem denseRange_padicCompletionUnitsOf : DenseRange (padicCompletionUnitsOf p L) := by
  rw [DenseRange, dense_iff_inter_open]
  rintro U ⟨s, hs, hsU⟩ ⟨x, hx⟩
  rw [← hsU, Set.mem_preimage] at hx
  obtain ⟨I, t, ht, htU⟩ := isOpen_pi_iff.mp hs x.1 hx
  let m := I.sup id
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (x.1 m)
  refine ⟨padicCompletionUnitsOf p L u, ?_, u, rfl⟩
  rw [← hsU]
  apply htU
  intro n hn
  rw [padicCompletionUnitsOf_apply]
  have hcoord := padicCompletionUnits_apply_eq_mk_of_le p L x
    (Finset.le_sup hn) u hu.symm
  have hcoord' : x.1 n = QuotientGroup.mk' _ u := by simpa [m] using hcoord
  rw [← hcoord']
  exact (ht n hn).2

end TauCeti
