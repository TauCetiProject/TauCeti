/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.NumberTheory.LocalField.AddChar.DualLattice
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.LinearAlgebra.BilinearForm.Dual.Index
import TauCeti.MeasureTheory.Group.Measure
import TauCeti.NumberTheory.LocalField.Lattice
import TauCeti.NumberTheory.LocalField.Topology
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Volumes of a lattice and of its dual over a nonarchimedean local field

Let `K` be a nonarchimedean local field with valuation ring `O = 𝒪[K]`, let `ψ` be a nontrivial
additive character of `K` which is trivial on a neighbourhood of `0`, and let `B` be a
nondegenerate bilinear form on a `K`-vector space `V` with its module topology. The dual of an
`O`-lattice `L` in `V` is its annihilator `L^∨ = L.characterAnnihilator ψ B` under the pairing
`(x, y) ↦ ψ (B x y)`, again a lattice (`Submodule.isFullLattice_characterAnnihilator`).

Duality preserves indices: `[L^∨ : L^∨ ∩ L'^∨] = [L' : L ∩ L']` for any two lattices, so
`[L^∨ : L'^∨] = [L' : L]` when `L ≤ L'` (`Submodule.relIndex_characterAnnihilator`), because `L^∨`
is the dual submodule of `L` for a rescaling of the transposed form
(`Submodule.characterAnnihilator_eq_dualSubmodule`, `LinearMap.BilinForm.relIndex_dualSubmodule`).
Lattices are compact open subgroups of `V`, so for `L ≤ L'` and every invariant measure `μ` on `V`,
`μ L' = [L' : L] μ L` and `μ L^∨ = [L^∨ : L'^∨] μ L'^∨` (`AddSubgroup.relIndex_mul_measure_inf`).
Hence `μ L * μ L^∨ = μ L' * μ L'^∨`, and comparing two lattices with their intersection shows that
the product `μ L * μ L^∨` does not depend on the lattice at all
(`Submodule.measure_mul_measure_characterAnnihilator`). Replacing `μ` by `c • μ` multiplies it by
`c ^ 2`, and any two Haar measures on `V` differ by such a scalar, so exactly one Haar measure gives
every lattice and its dual reciprocal volumes
(`Submodule.existsUnique_isAddHaarMeasure_measure_mul_measure_characterAnnihilator_eq_one`): the
self-dual measure of `ψ` and `B` in Tate's local theory.

Nothing here depends on the characteristic of `K`.

## Main results

* `Submodule.relIndex_characterAnnihilator`: `[L^∨ : L^∨ ∩ L'^∨] = [L' : L ∩ L']`.
* `Submodule.measure_mul_measure_characterAnnihilator`: `μ L * μ L^∨ = μ L' * μ L'^∨` for every
  invariant measure `μ` and any two lattices `L`, `L'`.
* `Submodule.existsUnique_isAddHaarMeasure_measure_mul_measure_characterAnnihilator_eq_one`:
  exactly one Haar measure `μ` on `V` satisfies `μ L * μ L^∨ = 1`, for any given lattice `L`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, Thesis (1950), in
  Cassels–Fröhlich, *Algebraic Number Theory*, §2.2.
* A. Weil, *Basic Number Theory*, Chapter VII, §2.
-/

public section

open Filter Topology ValuativeRel MeasureTheory

namespace Submodule

variable {K V M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [AddCommGroup V] [Module K V] [Module 𝒪[K] V]
  [IsScalarTower 𝒪[K] K V] [CommMonoid M] {ψ : AddChar K M} {B : LinearMap.BilinForm K V}

/-- **Duality preserves the index of lattices.** For a nondegenerate `B` and a nontrivial `ψ`
trivial on a neighbourhood of `0`, the dual lattices `L^∨ = L.characterAnnihilator ψ B` satisfy
`[L^∨ : L^∨ ∩ L'^∨] = [L' : L ∩ L']`; in particular `[L^∨ : L'^∨] = [L' : L]` when `L ≤ L'`. -/
theorem relIndex_characterAnnihilator (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K)) (h1 : ψ ≠ 1)
    (hB : B.Nondegenerate) (L L' : Submodule 𝒪[K] V) [L.IsFullLattice K] [L'.IsFullLattice K] :
    (L'.characterAnnihilator ψ B).toAddSubgroup.relIndex
        (L.characterAnnihilator ψ B).toAddSubgroup =
      L.toAddSubgroup.relIndex L'.toAddSubgroup := by
  obtain ⟨c, hc⟩ := valuation_surjective (uniformizer K ^ (-ψ.conductorExponent))
  have hc0 : c ≠ 0 := (valuation K).ne_zero_iff.1 (hc ▸ zpow_ne_zero _ uniformizer_ne_zero)
  rw [characterAnnihilator_eq_dualSubmodule h0 h1 hc,
    characterAnnihilator_eq_dualSubmodule h0 h1 hc]
  exact (c⁻¹ • B.flip).relIndex_dualSubmodule ((TauCeti.BilinForm.nondegenerate_smul_iff
    (IsRegular.of_ne_zero (inv_ne_zero hc0))).2 hB.flip) L L'

variable [TopologicalSpace V] [IsModuleTopology K V] [MeasurableSpace V] [BorelSpace V]

/-- The case `L ≤ L'` of `Submodule.measure_mul_measure_characterAnnihilator`: the volumes of
`L ≤ L'` and of `L'^∨ ≤ L^∨` differ by the same index. -/
private theorem measure_mul_measure_characterAnnihilator_of_le (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K))
    (h1 : ψ ≠ 1) (hB : B.Nondegenerate) (μ : Measure V) [μ.IsAddLeftInvariant]
    {L L' : Submodule 𝒪[K] V} [L.IsFullLattice K] [L'.IsFullLattice K] (h : L ≤ L') :
    μ L * μ (L.characterAnnihilator ψ B) = μ L' * μ (L'.characterAnnihilator ψ B) := by
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup K V
  have := Module.Finite.of_isFullLattice (A := K) L
  have : T2Space V := TauCeti.ModuleTopology.t2Space (Module.Free.chooseBasis K V)
  have := isFullLattice_characterAnnihilator h0 h1 hB L
  have := isFullLattice_characterAnnihilator h0 h1 hB L'
  -- `μ L' = [L' : L] μ L` and `μ L^∨ = [L^∨ : L'^∨] μ L'^∨`, with equal indices.
  have hL := AddSubgroup.relIndex_mul_measure_inf (H := L.toAddSubgroup)
    (K := L'.toAddSubgroup) (IsFullLattice.isCompact L') (IsFullLattice.isOpen L) μ
  have hL' := AddSubgroup.relIndex_mul_measure_inf
    (H := (L'.characterAnnihilator ψ B).toAddSubgroup)
    (K := (L.characterAnnihilator ψ B).toAddSubgroup)
    (IsFullLattice.isCompact _) (IsFullLattice.isOpen _) μ
  rw [inf_of_le_left ((toAddSubgroup_le _ _).2 h)] at hL
  rw [inf_of_le_left ((toAddSubgroup_le _ _).2 (characterAnnihilator_anti h)),
    relIndex_characterAnnihilator h0 h1 hB L L'] at hL'
  simp only [coe_toAddSubgroup] at hL hL'
  rw [← hL, ← hL', mul_left_comm, mul_assoc]

/-- **The volume product of a lattice and its dual does not depend on the lattice.** For a
nondegenerate `B`, a nontrivial `ψ` trivial on a neighbourhood of `0` and every invariant measure
`μ` on `V`, `μ L * μ L^∨ = μ L' * μ L'^∨` for any two lattices `L` and `L'`, where
`L^∨ = L.characterAnnihilator ψ B`. -/
theorem measure_mul_measure_characterAnnihilator (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K))
    (h1 : ψ ≠ 1) (hB : B.Nondegenerate) (μ : Measure V) [μ.IsAddLeftInvariant]
    (L L' : Submodule 𝒪[K] V) [L.IsFullLattice K] [L'.IsFullLattice K] :
    μ L * μ (L.characterAnnihilator ψ B) = μ L' * μ (L'.characterAnnihilator ψ B) := by
  have := IsFullLattice.inf K L L'
  rw [← measure_mul_measure_characterAnnihilator_of_le h0 h1 hB μ (inf_le_left : L ⊓ L' ≤ L),
    measure_mul_measure_characterAnnihilator_of_le h0 h1 hB μ (inf_le_right : L ⊓ L' ≤ L')]

/-- **The self-dual Haar measure.** For a nondegenerate `B` and a nontrivial `ψ` trivial on a
neighbourhood of `0`, exactly one Haar measure `μ` on `V` gives a lattice `L` and its dual
`L^∨ = L.characterAnnihilator ψ B` reciprocal volumes, `μ L * μ L^∨ = 1`. By
`Submodule.measure_mul_measure_characterAnnihilator` it does so for every lattice. -/
theorem existsUnique_isAddHaarMeasure_measure_mul_measure_characterAnnihilator_eq_one
    (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K)) (h1 : ψ ≠ 1) (hB : B.Nondegenerate)
    (L : Submodule 𝒪[K] V) [L.IsFullLattice K] :
    ∃! μ : Measure V, μ.IsAddHaarMeasure ∧ μ L * μ (L.characterAnnihilator ψ B) = 1 := by
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup K V
  have := Module.Finite.of_isFullLattice (A := K) L
  let b := Module.Free.chooseBasis K V
  have : T2Space V := TauCeti.ModuleTopology.t2Space b
  have : LocallyCompactSpace V := TauCeti.ModuleTopology.locallyCompactSpace b
  have : SecondCountableTopology V :=
    (TauCeti.ModuleTopology.equivFunHomeomorph b).isEmbedding.secondCountableTopology
  have := isFullLattice_characterAnnihilator h0 h1 hB L
  set A := L.characterAnnihilator ψ B
  -- Two Haar measures with this property are equal: they differ by a scalar `c` with `c ^ 2 = 1`.
  have huniq (μ μ' : Measure V) [μ.IsAddHaarMeasure] [μ'.IsAddHaarMeasure]
      (hμ : μ L * μ A = 1) (hμ' : μ' L * μ' A = 1) : μ' = μ := by
    have h := Measure.isAddLeftInvariant_eq_smul μ' μ
    rw [h, Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply, mul_mul_mul_comm, hμ,
      mul_one, ← ENNReal.coe_mul, ENNReal.coe_eq_one, ← sq,
      pow_eq_one_iff_of_nonneg (a := μ'.addHaarScalarFactor μ) bot_le two_ne_zero] at hμ'
    rw [h, hμ', one_smul]
  -- The Haar measure `μ₀` giving `L` mass one, rescaled by `μ₀ A ^ (-1 / 2)`.
  let L₀ : TopologicalSpace.PositiveCompacts V := ⟨⟨L, IsFullLattice.isCompact L⟩, by
    change (interior (L : Set V)).Nonempty
    rw [(IsFullLattice.isOpen L).interior_eq]
    exact ⟨0, L.zero_mem⟩⟩
  let μ₀ := Measure.addHaarMeasure L₀
  have hμ₀L : μ₀ L = 1 := Measure.addHaarMeasure_self (K₀ := L₀)
  have ha0 : μ₀ A ≠ 0 := (IsFullLattice.isOpen A).measure_ne_zero μ₀ A.nonempty
  have hatop : μ₀ A ≠ ⊤ := (IsFullLattice.isCompact A).measure_lt_top.ne
  have hc : μ₀ A ^ (-(1 / 2) : ℝ) * μ₀ A ^ (-(1 / 2) : ℝ) = (μ₀ A)⁻¹ := by
    rw [← ENNReal.rpow_add _ _ ha0 hatop]
    norm_num [ENNReal.rpow_neg_one]
  have : (μ₀ A ^ (-(1 / 2) : ℝ) • μ₀).IsAddHaarMeasure :=
    .smul _ (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hatop).ne'
      (ENNReal.rpow_ne_top_of_ne_zero ha0 hatop)
  have hprod : (μ₀ A ^ (-(1 / 2) : ℝ) • μ₀) L * (μ₀ A ^ (-(1 / 2) : ℝ) • μ₀) A = 1 := by
    rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, hμ₀L, mul_one, ← mul_assoc, hc,
      ENNReal.inv_mul_cancel ha0 hatop]
  exact ⟨_, ⟨this, hprod⟩, fun μ ⟨hμ, hμL⟩ ↦ huniq _ μ hprod hμL⟩

end Submodule
