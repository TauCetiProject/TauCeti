/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import TauCeti.MeasureTheory.Group.FundamentalDomain.Discrete
public import TauCeti.MeasureTheory.Group.Lattice
public import TauCeti.MeasureTheory.Group.ModularCharacter.FiniteCovolume
public import TauCeti.MeasureTheory.Measure.Haar.Matrix.SpecialLinearTwo
public import TauCeti.MeasureTheory.Measure.Haar.Unimodular
public import TauCeti.NumberTheory.Modular
public import TauCeti.NumberTheory.Modular.Orbits

/-!
# `SL(2, ℤ)` is a nonuniform lattice in `SL(2, ℝ)`

Let `Γ` be a discrete subgroup of `SL(2, ℝ)` and `F ⊆ ℍ` a set of finite hyperbolic area meeting
every `Γ`-orbit of the upper half-plane. The preimage of `F` under the orbit map `g ↦ g • i` has
Haar measure the area of `F` (`Matrix.SpecialLinearGroup.volume_preimage_smul_I`), and its
translates by `Γ` cover `SL(2, ℝ)`, so every fundamental domain of `Γ` acting by left
multiplication has measure at most the area of `F`. For `Γ = SL(2, ℤ)` the standard modular
fundamental domain is such a set, of area `π / 3`.

A countable subgroup acting on the left with a fundamental domain of finite Haar measure forces
the modular character to be trivial
(`MeasureTheory.IsFundamentalDomain.isMulRightInvariant_of_measure_ne_top`). So `SL(2, ℤ)` shows
that `SL(2, ℝ)` is unimodular: its Haar measure is right invariant and invariant under inversion.
Inversion then turns fundamental domains of the left action into fundamental domains of the right
action `g ↦ g γ` with the same measure, which is the lattice condition `Subgroup.IsLattice`
(`Subgroup.isLattice_of_isFundamentalDomain_measure_lt_top`).

The lattice `SL(2, ℤ)` is not uniform: if `K * SL(2, ℤ) = SL(2, ℝ)` for a compact `K`, every
point of `ℍ` would be an `SL(2, ℤ)`-translate of a point of the compact set `K⁻¹ • i`, whose
imaginary parts lie in some `[m, M]` with `m > 0`. But the translates of `i y` by `SL(2, ℤ)` have
imaginary part `y` or at most `1 / y`, because `Im (γ • z) = Im z / |c z + d|²`.

## Main results

* `Matrix.SpecialLinearGroup.instCountableRangeMapIntCast`: the image of `SL(2, ℤ)` in
  `SL(2, ℝ)` is countable.
* `Matrix.SpecialLinearGroup.instIsMulRightInvariantSL2R`: `SL(2, ℝ)` is unimodular.
* `Subgroup.isLattice_of_forall_exists_smul_mem`: a discrete subgroup of `SL(2, ℝ)` whose orbits
  on `ℍ` all meet a set of finite area is a lattice.
* `Matrix.SpecialLinearGroup.isLattice_range_map_intCast`: `SL(2, ℤ)` is a lattice in `SL(2, ℝ)`.
* `Matrix.SpecialLinearGroup.not_isUniformLattice_range_map_intCast`: it is not a uniform lattice.

## References

* Frederick M. Goodman, Pierre de la Harpe, Vaughan F. R. Jones, *Coxeter Graphs and Towers of
  Algebras*, Springer, 1989, §3.3.
* Dave Witte Morris, *Introduction to Arithmetic Groups*, Deductive Press, 2015, §4.1.
-/

public section

open MeasureTheory Measure Set UpperHalfPlane
open scoped MatrixGroups ENNReal Pointwise

namespace Subgroup

variable {Γ : Subgroup SL(2, ℝ)} [DiscreteTopology Γ]

/-- If every `Γ`-orbit of `ℍ` meets `F`, a discrete subgroup `Γ` of `SL(2, ℝ)` acting by left
multiplication has a measurable fundamental domain of Haar measure at most the area of `F`. -/
theorem exists_isFundamentalDomain_volume_le_of_forall_exists_smul_mem {F : Set ℍ}
    (hF : ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F) :
    ∃ D : Set SL(2, ℝ), MeasurableSet D ∧ IsFundamentalDomain Γ D volume ∧ volume D ≤ volume F := by
  have : Countable Γ := countable_of_Lindelof_of_discrete
  obtain ⟨D, hDm, hD⟩ := Γ.exists_isFundamentalDomain_mul_left (volume : Measure SL(2, ℝ))
  refine ⟨D, hDm, hD, ?_⟩
  -- the `Γ`-translates of the preimage of `F` under the orbit map cover `SL(2, ℝ)`
  have hcov : D ⊆ ⋃ γ : Γ, γ • ((· • I) ⁻¹' F : Set SL(2, ℝ)) := fun x _ ↦ by
    obtain ⟨γ, hγ, hγx⟩ := hF (x • I)
    refine mem_iUnion.mpr ⟨⟨γ, hγ⟩⁻¹, ?_⟩
    simpa [mem_smul_set_iff_inv_smul_mem, mul_smul] using hγx
  exact (hD.measure_le_of_subset_iUnion_smul hcov).trans
    (Matrix.SpecialLinearGroup.volume_preimage_smul_I F).le

end Subgroup

namespace Matrix.SpecialLinearGroup

/-- Every orbit of `SL(2, ℤ)` on `ℍ` meets the standard fundamental domain. -/
private theorem forall_exists_smul_mem_fd :
    ∀ z : ℍ, ∃ γ ∈ (map (Int.castRingHom ℝ) : SL(2, ℤ) →* SL(2, ℝ)).range,
      γ • z ∈ ModularGroup.fd := fun z ↦ by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  exact ⟨map (Int.castRingHom ℝ) g, ⟨g, rfl⟩, by simpa using hg⟩

/-- The image of `SL(2, ℤ)` in `SL(2, ℝ)` is countable, as a discrete subgroup of a second
countable group. -/
instance instCountableRangeMapIntCast :
    Countable (map (Int.castRingHom ℝ) : SL(2, ℤ) →* SL(2, ℝ)).range :=
  countable_of_Lindelof_of_discrete

/-- **`SL(2, ℝ)` is unimodular.** Its Haar measure is right invariant: `SL(2, ℤ)` acting by left
multiplication has a fundamental domain of finite measure, which forces the modular character to
be trivial. -/
instance instIsMulRightInvariantSL2R : (volume : Measure SL(2, ℝ)).IsMulRightInvariant := by
  obtain ⟨D, -, hD, hDF⟩ :=
    Subgroup.exists_isFundamentalDomain_volume_le_of_forall_exists_smul_mem
      forall_exists_smul_mem_fd
  exact hD.isMulRightInvariant_of_measure_ne_top
    (hDF.trans_lt ModularGroup.volume_fd_lt_top).ne

/-- The Haar measure of `SL(2, ℝ)` is invariant under inversion. -/
instance instIsInvInvariantSL2R : (volume : Measure SL(2, ℝ)).IsInvInvariant :=
  isInvInvariant_of_isMulRightInvariant _

end Matrix.SpecialLinearGroup

namespace Subgroup

variable {Γ : Subgroup SL(2, ℝ)} [DiscreteTopology Γ]

/-- **A criterion for lattices in `SL(2, ℝ)`.** A discrete subgroup of `SL(2, ℝ)` whose orbits on
`ℍ` all meet a set of finite hyperbolic area is a lattice. -/
theorem isLattice_of_forall_exists_smul_mem {F : Set ℍ} (hFv : volume F ≠ ∞)
    (hF : ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F) : Γ.IsLattice volume := by
  have : Countable Γ := countable_of_Lindelof_of_discrete
  obtain ⟨D, -, hD, hDF⟩ := exists_isFundamentalDomain_volume_le_of_forall_exists_smul_mem hF
  exact isLattice_of_isFundamentalDomain_measure_lt_top hD (hDF.trans_lt hFv.lt_top)

end Subgroup

namespace Matrix.SpecialLinearGroup

/-- **`SL(2, ℤ)` is a lattice in `SL(2, ℝ)`.** -/
theorem isLattice_range_map_intCast :
    (map (Int.castRingHom ℝ) : SL(2, ℤ) →* SL(2, ℝ)).range.IsLattice volume :=
  Subgroup.isLattice_of_forall_exists_smul_mem ModularGroup.volume_fd_lt_top.ne
    forall_exists_smul_mem_fd

/-- **`SL(2, ℤ)` is not a uniform lattice in `SL(2, ℝ)`.** If `K * SL(2, ℤ) = SL(2, ℝ)` for a
compact `K`, every point of `ℍ` would be a translate of a point of `K⁻¹ • i`, whose imaginary parts
lie in some `[m, M]` with `m > 0`; but the translates of `i y` have imaginary part `y` or at most
`1 / y` (`ModularGroup.im_smul_eq_or_le_inv`). -/
theorem not_isUniformLattice_range_map_intCast :
    ¬ (map (Int.castRingHom ℝ) : SL(2, ℤ) →* SL(2, ℝ)).range.IsUniformLattice volume := by
  intro h
  obtain ⟨K, hK, hKΓ⟩ := h.exists_isCompact_mul_eq_univ
  have hKne : K.Nonempty := by
    by_contra hK0
    rw [not_nonempty_iff_eq_empty.mp hK0, Set.empty_mul] at hKΓ
    exact empty_ne_univ hKΓ
  -- the imaginary parts of `K⁻¹ • i` lie in `[m, M]`, `m > 0`
  have hcont : Continuous fun k : SL(2, ℝ) ↦ (k⁻¹ • I).im :=
    UpperHalfPlane.continuous_im.comp (continuous_inv.smul continuous_const)
  obtain ⟨k₀, -, hmin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
  obtain ⟨k₁, -, hmax⟩ := hK.exists_isMaxOn hKne hcont.continuousOn
  set m := (k₀⁻¹ • I).im
  set M := (k₁⁻¹ • I).im
  have hm : 0 < m := UpperHalfPlane.im_pos _
  set y := max M m⁻¹ + 1
  have hy : 0 < y := by positivity
  let w : ℍ := ⟨y * Complex.I, by simpa using hy⟩
  have hw : w.im = y := by simp [w, UpperHalfPlane.im]
  obtain ⟨k, hk, γ, ⟨g, rfl⟩, hkγ⟩ : (toSL2R w)⁻¹ ∈ K * (_ : Set SL(2, ℝ)) :=
    hKΓ ▸ mem_univ _
  -- `k⁻¹ • i = g • w`
  have hkw : k⁻¹ • I = g • w := by
    rw [inv_smul_I_eq_smul_of_mul_eq_toSL2R_inv (b := map (Int.castRingHom ℝ) g) hkγ]
    simp only [ModularGroup.sl_moeb, toGL_smul]
  have hlo : m ≤ (g • w).im := hkw ▸ hmin hk
  have hhi : (g • w).im ≤ M := hkw ▸ hmax hk
  rcases ModularGroup.im_smul_eq_or_le_inv g w with h | h
  · rw [h, hw] at hhi
    linarith [le_max_left M m⁻¹]
  · rw [hw] at h
    have : y⁻¹ < m := by
      rw [inv_lt_comm₀ hy hm]
      linarith [le_max_right M m⁻¹]
    linarith

end Matrix.SpecialLinearGroup
