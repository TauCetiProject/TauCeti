/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
public import TauCeti.GroupTheory.FreeGroup.Linear
public import TauCeti.GroupTheory.HaagerupProperty.Basic
public import TauCeti.GroupTheory.PropertyT.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Action

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Metrizable.Urysohn
import TauCeti.Geometry.Manifold.Instances.OnePoint.InvariantMeasure
import TauCeti.GroupTheory.Amenable.Abelian
import TauCeti.GroupTheory.Amenable.Extension
import TauCeti.GroupTheory.Amenable.FreeGroup
import TauCeti.GroupTheory.HaagerupProperty.Amenable
import TauCeti.GroupTheory.HaagerupProperty.PropertyT
import TauCeti.RepresentationTheory.Continuous.Unitary.SpectralMeasure

/-!
# Relative property (T) for `(ℤ² ⋊ G, ℤ²)` and Burger's criterion

Let `G` be a group acting on `ℤ²` through an injective homomorphism `ι : G →* SL(2, ℤ)` and column
multiplication `TauCeti.slTwoAction`. We prove **Burger's theorem**: the normal subgroup `ℤ²` inside
`ℤ² ⋊ G` has relative property (T) whenever `G` is nonamenable (equivalently, lacks Følner sets).
Together with the Haagerup obstruction for amenable semidirect products, this yields the exact
characterization for subgroups `G ≤ SL(2, ℤ)`:

`(ℤ² ⋊ G, ℤ²)` has relative property (T) in universe `u` if and only if `G` is not amenable.

Specializing to `G = SL(2, ℤ)` (which contains a rank-two free subgroup by Sanov's theorem and is
therefore nonamenable) gives the **Kazhdan–Margulis theorem** that `(ℤ² ⋊ SL(2, ℤ), ℤ²)` has
relative property (T), hence `ℤ² ⋊ SL(2, ℤ)` fails the Haagerup property. Specializing to Sanov's
free subgroup gives relative property (T) for `(ℤ² ⋊ F₂, ℤ²)`; specializing to a unipotent shear
subgroup shows that `(ℤ² ⋊ ℤ, ℤ²)` does not have relative property (T).

## Proof outline

Suppose `ρ` is a unitary representation of `ℤ² ⋊ G` on a complex Hilbert space `H` with almost
invariant unit vectors, and assume for contradiction that `ρ` has no nonzero `ℤ²`-invariant vector.
Let `P` be the spectral projection-valued measure of `ρ|_{ℤ²}` on the compact Pontryagin dual
`𝕋² = PontryaginDual (Multiplicative (Fin 2 → ℤ))` (`ContRepresentation.spectralPVM`).

1. Since `P({1})` projects onto the `ℤ²`-invariant vectors, `P.diag ξ {1} = 0` for every `ξ : H`,
   and `P.diag ξ` is a probability measure on `𝕋²` whenever `‖ξ‖ = 1`.
2. Identifying each circle factor with `[-1/2, 1/2)` via `AddCircle.measurableEquivIco`, every
   character `χ ∈ 𝕋²` has Borel coordinates `σ(χ) ∈ [-1/2, 1/2)²` with `σ(χ) = 0 ↔ χ = 1`.
   Map `v ∈ ℝ² \ {0}` to `OnePoint ℝ` by the symplectic projection `v ↦ [-v 1 : v 0]` (sending
   `v 0 = 0` to `∞` and `v 0 ≠ 0` to `-v 1 / v 0`). Because `J (g⁻¹)ᵀ = g J` for
   `J = !![0, -1; 1, 0]` and every `g ∈ SL(2, ℝ)`, whenever `σ(χ) ≠ 0` is small enough that
   `(ι g⁻¹)ᵀ σ(χ)` stays in `(-1/2, 1/2)²`, the dual torus action of `ι g⁻¹` intertwines the
   symplectic projection with the Möbius action of `sl2zToPSL2R (ι g)` on `OnePoint ℝ`.
3. Along the net of `(K, n)`-almost invariant unit vectors `ξ_(K, n)`, the spectral displacement
   identity concentrates `P.diag (ξ_(K, n))` arbitrarily close to `{1}` while assigning zero mass
   to `{1}`, and equivariance of `P.diag` under `ρ (inr g⁻¹)` shows that the pushed-forward
   probability measures on `OnePoint ℝ` are asymptotically `G`-invariant.
4. By Prokhorov compactness of `ProbabilityMeasure (OnePoint ℝ)`, a weak-* cluster point of these
   pushforwards is a `G`-invariant Borel probability measure on `OnePoint ℝ`. Furstenberg's
   projective-line concentration lemma (`TauCeti.hasFoelnerSets_of_injective_sl2z_of_map_smul_eq`)
   then forces `G` to have Følner sets, a contradiction.

## Main results

* `TauCeti.relativePropertyT_inl_of_injective_of_not_hasFoelnerSets` and
  `TauCeti.relativePropertyT_inl_of_injective_of_not_amenable`: Burger's theorem for any group
  admitting an injective homomorphism into `SL(2, ℤ)`.
* `TauCeti.relativePropertyT_inl_of_not_amenable` and
  `TauCeti.relativePropertyT_inl_iff_not_amenable`: Burger's theorem and the exact amenability
  characterization for subgroups `G ≤ SL(2, ℤ)`.
* `TauCeti.not_amenable_slTwoZ` and `TauCeti.relativePropertyT_inl_slTwo`: nonamenability of
  `SL(2, ℤ)` and the Kazhdan–Margulis theorem for `(ℤ² ⋊ SL(2, ℤ), ℤ²)`.
* `TauCeti.not_hasHaagerupProperty_semidirectProduct_of_not_amenable` and
  `TauCeti.not_hasHaagerupProperty_semidirectProduct_slTwo`: failure of the Haagerup property for
  `ℤ² ⋊ G` (for nonamenable `G ≤ SL(2, ℤ)`) and `ℤ² ⋊ SL(2, ℤ)`.
* `TauCeti.relativePropertyT_inl_freeGroup` and
  `TauCeti.not_relativePropertyT_inl_range_transvectionHom`: relative property (T) for
  `(ℤ² ⋊ F₂, ℤ²)` via Sanov's embedding, and failure of relative property (T) for unipotent shear
  subgroups.

## References

* D. A. Kazhdan, *On the connection of the dual space of a group with the structure of its closed
  subgroups*, Funct. Anal. Appl. 1 (1967), 63–65.
* G. A. Margulis, *Explicit constructions of expanders*, Problemy Peredači Informacii 9 (1973),
  71–80.
* M. Burger, *Kazhdan constants for `SL(3, ℤ)`*, J. Reine Angew. Math. 413 (1991), 36–67,
  Proposition 3.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Cambridge University Press,
  2008, §4.2.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Example 14.2.8.
-/

noncomputable section

open Filter Topology MeasureTheory Set Matrix BoundedContinuousFunction OnePoint
open scoped MatrixGroups InnerProductSpace

namespace TauCeti

namespace BurgerProof

/-- Fundamental-domain coordinate in `[-1/2, 1/2)` of a point on the unit-period circle
`AddCircle (1 : ℝ)`. -/
def torusAngle (x : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.measurableEquivIco (1 : ℝ) (-1 / 2) x : ℝ)

theorem measurable_torusAngle : Measurable torusAngle :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) (-1 / 2)).measurable

theorem torusAngle_mem_Ico (x : AddCircle (1 : ℝ)) :
    torusAngle x ∈ Ico (-1 / 2 : ℝ) (1 / 2) := by
  unfold torusAngle
  have hx := (AddCircle.measurableEquivIco (1 : ℝ) (-1 / 2) x).2
  exact ⟨hx.1, by linarith [hx.2]⟩

theorem abs_torusAngle_le (x : AddCircle (1 : ℝ)) : |torusAngle x| ≤ 1 / 2 := by
  have hx := torusAngle_mem_Ico x
  exact abs_le.mpr ⟨by linarith [hx.1], hx.2.le⟩

@[simp]
theorem coe_torusAngle (x : AddCircle (1 : ℝ)) :
    (torusAngle x : AddCircle (1 : ℝ)) = x :=
  AddCircle.coe_equivIco

theorem torusAngle_coe_of_mem {t : ℝ} (ht : t ∈ Ico (-1 / 2 : ℝ) (1 / 2)) :
    torusAngle (t : AddCircle (1 : ℝ)) = t := by
  have ht' : t ∈ Ico (-1 / 2 : ℝ) (-1 / 2 + 1) := ⟨ht.1, by linarith [ht.2]⟩
  exact AddCircle.equivIco_coe_of_mem ht'

@[simp]
theorem torusAngle_eq_zero_iff (x : AddCircle (1 : ℝ)) :
    torusAngle x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [← coe_torusAngle x, h]
    exact QuotientAddGroup.mk_zero _
  · rintro rfl
    simpa using torusAngle_coe_of_mem (t := 0) (by constructor <;> norm_num)

/-- Coordinates in `[-1/2, 1/2)²` of a character on `ℤ²`. -/
def torusCoords (χ : PontryaginDual (Multiplicative (Fin 2 → ℤ))) (j : Fin 2) : ℝ :=
  torusAngle ((AddCircle.homeomorphCircle one_ne_zero).symm
    (χ (Multiplicative.ofAdd (Pi.single j 1))))

theorem torusCoords_apply (χ : PontryaginDual (Multiplicative (Fin 2 → ℤ))) (j : Fin 2) :
    torusCoords χ j =
      torusAngle ((AddCircle.homeomorphCircle one_ne_zero).symm
        (χ (Multiplicative.ofAdd (Pi.single j 1)))) :=
  rfl

theorem measurable_torusCoords {_ : MeasurableSpace (PontryaginDual (Multiplicative (Fin 2 → ℤ)))}
    [OpensMeasurableSpace (PontryaginDual (Multiplicative (Fin 2 → ℤ)))] :
    Measurable torusCoords := by
  refine Measurable.of_eval fun j ↦ measurable_torusAngle.comp ?_
  have heval : Continuous fun χ : PontryaginDual (Multiplicative (Fin 2 → ℤ)) ↦
      χ (Multiplicative.ofAdd (Pi.single j 1)) :=
    continuous_eval_const (F := Multiplicative (Fin 2 → ℤ) →ₜ* Circle)
      (Multiplicative.ofAdd (Pi.single j 1))
  exact ((AddCircle.homeomorphCircle one_ne_zero).symm.continuous.comp heval).measurable

theorem toCircle_torusCoords (χ : PontryaginDual (Multiplicative (Fin 2 → ℤ))) (j : Fin 2) :
    AddCircle.toCircle (torusCoords χ j : AddCircle (1 : ℝ)) =
      χ (Multiplicative.ofAdd (Pi.single j 1)) := by
  rw [torusCoords_apply, coe_torusAngle, ← AddCircle.homeomorphCircle_apply one_ne_zero,
    Homeomorph.apply_symm_apply]

theorem torusCoords_eq_zero_iff (χ : PontryaginDual (Multiplicative (Fin 2 → ℤ))) :
    torusCoords χ = 0 ↔ χ = 1 := by
  refine ⟨fun h ↦ PontryaginDual.ext fun v ↦ ?_, fun h ↦ ?_⟩
  · have hj (j : Fin 2) : χ (Multiplicative.ofAdd (Pi.single j 1)) = 1 := by
      have h0 : torusCoords χ j = 0 := congrFun h j
      rw [← toCircle_torusCoords, h0]
      exact AddCircle.toCircle_zero
    have hv : v = Multiplicative.ofAdd (Pi.single 0 1) ^ (Multiplicative.toAdd v 0) *
        Multiplicative.ofAdd (Pi.single 1 1) ^ (Multiplicative.toAdd v 1) := by
      apply Multiplicative.toAdd.injective
      ext i
      fin_cases i <;> simp
    rw [hv, map_mul, map_zpow, map_zpow, hj 0, hj 1]
    simp
  · subst h
    ext j
    simp only [Pi.zero_apply, torusCoords, torusAngle_eq_zero_iff]
    rw [Homeomorph.symm_apply_eq, AddCircle.homeomorphCircle_apply]
    exact AddCircle.toCircle_zero.symm

/-- The dual torus endomorphism induced by `slTwoAction A` for `A ∈ SL(2, ℤ)`. -/
def dualTorusMap (A : SL(2, ℤ)) :
    PontryaginDual (Multiplicative (Fin 2 → ℤ)) →ₜ*
      PontryaginDual (Multiplicative (Fin 2 → ℤ)) :=
  PontryaginDual.map ⟨(slTwoAction A).toMonoidHom, continuous_of_discreteTopology⟩

@[simp]
theorem dualTorusMap_apply (A : SL(2, ℤ))
    (χ : PontryaginDual (Multiplicative (Fin 2 → ℤ))) (v : Multiplicative (Fin 2 → ℤ)) :
    dualTorusMap A χ v = χ (slTwoAction A v) :=
  rfl

theorem torusCoords_dualTorusMap_eq_mulVec (A : SL(2, ℤ))
    (χ : PontryaginDual (Multiplicative (Fin 2 → ℤ)))
    (hsmall : ∀ j : Fin 2,
      (((A : Matrix (Fin 2) (Fin 2) ℤ)ᵀ.map (Int.cast : ℤ → ℝ)).mulVec (torusCoords χ)) j ∈
        Ico (-1 / 2 : ℝ) (1 / 2)) :
    torusCoords (dualTorusMap A χ) =
      ((A : Matrix (Fin 2) (Fin 2) ℤ)ᵀ.map (Int.cast : ℤ → ℝ)).mulVec (torusCoords χ) := by
  ext j
  have hact : slTwoAction A (Multiplicative.ofAdd (Pi.single j 1)) =
      Multiplicative.ofAdd (Pi.single 0 1) ^ ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 j) *
        Multiplicative.ofAdd (Pi.single 1 1) ^ ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 j) := by
    apply Multiplicative.toAdd.injective
    rw [slTwoAction_apply_eq_mulVec]
    ext i
    fin_cases j <;> fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have heval : dualTorusMap A χ (Multiplicative.ofAdd (Pi.single j 1)) =
      AddCircle.toCircle
        ((((A : Matrix (Fin 2) (Fin 2) ℤ)ᵀ.map (Int.cast : ℤ → ℝ)).mulVec (torusCoords χ) j : ℝ) :
          AddCircle (1 : ℝ)) := by
    rw [dualTorusMap_apply, hact, map_mul, map_zpow, map_zpow,
      ← toCircle_torusCoords χ 0, ← toCircle_torusCoords χ 1,
      ← AddCircle.toCircle_zsmul, ← AddCircle.toCircle_zsmul, ← AddCircle.toCircle_add]
    congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [torusCoords_apply, heval, ← AddCircle.homeomorphCircle_apply one_ne_zero,
    Homeomorph.symm_apply_apply]
  exact torusAngle_coe_of_mem (hsmall j)

/-- On `{t : ℝ | δ ≤ |t| ∧ |t| ≤ 1/2}` (`0 < δ ≤ 1/2`), the squared chord distance
`‖toCircle t - 1‖²` is bounded below by a strictly positive constant. -/
theorem exists_pos_le_norm_toCircle_sub_one_sq {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, δ ≤ |t| → |t| ≤ 1 / 2 →
      c ≤ ‖(AddCircle.toCircle (t : AddCircle (1 : ℝ)) : ℂ) - 1‖ ^ 2 := by
  let K : Set ℝ := Icc (-1 / 2) (-δ) ∪ Icc δ (1 / 2)
  have hK_compact : IsCompact K := isCompact_Icc.union isCompact_Icc
  have hK_nonempty : K.Nonempty := ⟨δ, Or.inr ⟨le_rfl, hδ2⟩⟩
  let φ : ℝ → ℝ := fun t ↦ ‖(AddCircle.toCircle (t : AddCircle (1 : ℝ)) : ℂ) - 1‖ ^ 2
  have hcont : Continuous φ :=
    (((continuous_subtype_val.comp
      (AddCircle.continuous_toCircle.comp (AddCircle.continuous_mk' (1 : ℝ)))).sub
        continuous_const).norm).pow 2
  obtain ⟨t₀, ht₀K, ht₀min⟩ := hK_compact.exists_isMinOn hK_nonempty hcont.continuousOn
  have ht₀_abs : δ ≤ |t₀| ∧ |t₀| ≤ 1 / 2 := by
    rcases ht₀K with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [abs_of_neg (h2.trans_lt (neg_lt_zero.mpr hδ))],
        abs_le.mpr ⟨by linarith, by linarith⟩⟩
    · exact ⟨(le_abs_self t₀).trans' h1, abs_le.mpr ⟨by linarith, h2⟩⟩
  have hpos : 0 < φ t₀ := by
    refine lt_of_le_of_ne (sq_nonneg _) fun hzero ↦ ?_
    have h1 : AddCircle.toCircle (t₀ : AddCircle (1 : ℝ)) = 1 := by
      apply Subtype.ext
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero.symm))
    have hcoe0 : (t₀ : AddCircle (1 : ℝ)) = 0 := by
      apply (AddCircle.homeomorphCircle one_ne_zero).injective
      rw [AddCircle.homeomorphCircle_apply, h1, ← AddCircle.toCircle_zero,
        ← AddCircle.homeomorphCircle_apply one_ne_zero]
    rcases lt_or_eq_of_le (abs_le.mp ht₀_abs.2).2 with hlt | rfl
    · have ht₀_Ico : t₀ ∈ Ico (-1 / 2 : ℝ) (1 / 2) :=
        ⟨by linarith [(abs_le.mp ht₀_abs.2).1], hlt⟩
      have ht₀0 : t₀ = 0 := by
        rw [← torusAngle_coe_of_mem ht₀_Ico, hcoe0, torusAngle_eq_zero_iff]
      have hle := ht₀_abs.1
      rw [ht₀0, abs_zero] at hle
      linarith
    · have hhalf : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = ((-1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
        simpa [(by norm_num : (-1 / 2 : ℝ) + 1 = 1 / 2)] using
          AddCircle.coe_add_period (1 : ℝ) (-1 / 2)
      rw [hhalf] at hcoe0
      have hneg := (torusAngle_eq_zero_iff _).mpr hcoe0
      rw [torusAngle_coe_of_mem (by constructor <;> norm_num)] at hneg
      norm_num at hneg
  refine ⟨φ t₀, hpos, fun t ht1 ht2 ↦ ht₀min ?_⟩
  rcases le_or_gt 0 t with hnonneg | hneg
  · exact Or.inr ⟨by rwa [abs_of_nonneg hnonneg] at ht1, (abs_le.mp ht2).2⟩
  · exact Or.inl ⟨by linarith [(abs_le.mp ht2).1], by linarith [abs_of_neg hneg]⟩

/-- Symplectic projection `v ↦ [-v 1 : v 0]` from `ℝ²` to `OnePoint ℝ`, sending lines with
`v 0 = 0` to `∞` and `v 0 ≠ 0` to `-v 1 / v 0`. -/
def symplecticProj (v : Fin 2 → ℝ) : OnePoint ℝ :=
  if v 0 = 0 then (∞ : OnePoint ℝ) else ((-v 1 / v 0 : ℝ) : OnePoint ℝ)

@[simp]
theorem symplecticProj_of_eq_zero {v : Fin 2 → ℝ} (hv : v 0 = 0) :
    symplecticProj v = ∞ := by
  simp [symplecticProj, hv]

@[simp]
theorem symplecticProj_of_ne_zero {v : Fin 2 → ℝ} (hv : v 0 ≠ 0) :
    symplecticProj v = ((-v 1 / v 0 : ℝ) : OnePoint ℝ) := by
  simp [symplecticProj, hv]

theorem measurable_symplecticProj {_ : MeasurableSpace (OnePoint ℝ)} [BorelSpace (OnePoint ℝ)] :
    Measurable symplecticProj := by
  refine Measurable.ite ?_ measurable_const ?_
  · exact (isClosed_eq (continuous_apply 0) continuous_const).measurableSet
  · exact OnePoint.continuous_coe.measurable.comp
      (((continuous_apply 1).neg.measurable).div (continuous_apply 0).measurable)

/-- Because `J (g⁻¹)ᵀ = g J` for `J = !![0, -1; 1, 0]`, `symplecticProj` intertwines `(g⁻¹)ᵀ` on
nonzero vectors in `ℝ²` with the Möbius action of `(g : PSL(2, ℝ))` on `OnePoint ℝ`. -/
theorem symplecticProj_mulVec_transpose_inv (g : SL(2, ℝ)) {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    symplecticProj (((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)ᵀ.mulVec v) =
      (g : PSL(2, ℝ)) • symplecticProj v := by
  set w : Fin 2 → ℝ := ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)ᵀ.mulVec v
  have hw0 : w 0 = (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 * v 0 -
      (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * v 1 := by
    simp [w, Matrix.adjugate_fin_two]
    ring
  have hw1 : w 1 = -(g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * v 0 +
      (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * v 1 := by
    simp [w, Matrix.adjugate_fin_two]
  rw [pslMk_smul]
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := fun hv1 ↦ hv (by ext i; fin_cases i <;> assumption)
    rw [symplecticProj_of_eq_zero hv0, smul_infty_eq_ite]
    by_cases hg10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0
    · have hw0_zero : w 0 = 0 := by simp [hw0, hv0, hg10]
      simp [symplecticProj_of_eq_zero hw0_zero, hg10]
    · have hw0_ne : w 0 ≠ 0 := by simp [hw0, hv0, hg10, hv1]
      simp only [symplecticProj_of_ne_zero hw0_ne, SpecialLinearGroup.coe_GL_coe_matrix, hg10,
        ↓reduceIte, hw0, hw1, hv0, mul_zero, zero_sub, zero_add]
      congr 1
      field_simp
  · rw [symplecticProj_of_ne_zero hv0, smul_some_eq_ite]
    by_cases hden : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (-v 1 / v 0) +
        (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 0
    · have hw0_zero : w 0 = 0 := by
        rw [hw0]
        field_simp at hden
        linarith
      simp [symplecticProj_of_eq_zero hw0_zero, hden]
    · have hw0_ne : w 0 ≠ 0 := by
        rw [hw0]
        intro h0
        apply hden
        field_simp
        linarith
      simp only [symplecticProj_of_ne_zero hw0_ne, SpecialLinearGroup.coe_GL_coe_matrix, hden,
        ↓reduceIte, hw0, hw1]
      congr 1
      field_simp [hw0_ne]
      ring

/-- For every `g ∈ SL(2, ℤ)` there is a small punctured box `(-δ, δ)² \ {0}` in torus coordinates
on which `dualTorusMap g⁻¹` intertwines `symplecticProj ∘ torusCoords` with the Möbius action of
`sl2zToPSL2R g`, together with a positive lower bound `c` on the squared chord distance outside
`(-δ, δ)`. -/
theorem exists_small_box_symplecticProj_equiv (g : SL(2, ℤ)) :
    ∃ δ c : ℝ, 0 < c ∧
      (∀ t : ℝ, δ ≤ |t| → |t| ≤ 1 / 2 →
        c ≤ ‖(AddCircle.toCircle (t : AddCircle (1 : ℝ)) : ℂ) - 1‖ ^ 2) ∧
      ∀ χ : PontryaginDual (Multiplicative (Fin 2 → ℤ)),
        χ ≠ 1 → (∀ j : Fin 2, |torusCoords χ j| < δ) →
        symplecticProj (torusCoords (dualTorusMap g⁻¹ χ)) =
          sl2zToPSL2R g • symplecticProj (torusCoords χ) := by
  let A : SL(2, ℤ) := g⁻¹
  let M : ℝ := 1 + max
    (max |((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ)| |((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ)|)
    (max |((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ)| |((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ)|)
  have hM_ge : 1 ≤ M := by
    dsimp [M]
    have h0 : 0 ≤ max
        (max |((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ)|
          |((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ)|)
        (max |((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ)|
          |((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ)|) := by positivity
    linarith
  have hM_entry (i j : Fin 2) : |((A : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ)| ≤ M - 1 := by
    dsimp [M]
    ring_nf
    fin_cases i <;> fin_cases j <;> simp [le_max_iff]
  let δ : ℝ := 1 / (4 * M)
  have hδ_pos : 0 < δ := by positivity
  have hδ_le : δ ≤ 1 / 2 := by
    dsimp [δ]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  obtain ⟨c, hc_pos, hc_le⟩ := exists_pos_le_norm_toCircle_sub_one_sq hδ_pos hδ_le
  refine ⟨δ, c, hc_pos, hc_le, fun χ hχ1 hχδ ↦ ?_⟩
  have hsmall (j : Fin 2) :
      (((A : Matrix (Fin 2) (Fin 2) ℤ)ᵀ.map (Int.cast : ℤ → ℝ)).mulVec (torusCoords χ)) j ∈
        Ico (-1 / 2 : ℝ) (1 / 2) := by
    have habs :
        |(((A : Matrix (Fin 2) (Fin 2) ℤ)ᵀ.map (Int.cast : ℤ → ℝ)).mulVec
            (torusCoords χ)) j| < 1 / 2 := by
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
        Matrix.transpose_apply]
      calc |((A : Matrix (Fin 2) (Fin 2) ℤ) 0 j : ℝ) * torusCoords χ 0 +
            ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 j : ℝ) * torusCoords χ 1|
        _ ≤ |((A : Matrix (Fin 2) (Fin 2) ℤ) 0 j : ℝ) * torusCoords χ 0| +
              |((A : Matrix (Fin 2) (Fin 2) ℤ) 1 j : ℝ) * torusCoords χ 1| :=
            abs_add_le _ _
        _ = |((A : Matrix (Fin 2) (Fin 2) ℤ) 0 j : ℝ)| * |torusCoords χ 0| +
              |((A : Matrix (Fin 2) (Fin 2) ℤ) 1 j : ℝ)| * |torusCoords χ 1| := by
            rw [abs_mul, abs_mul]
        _ ≤ (M - 1) * δ + (M - 1) * δ := by
            gcongr
            · exact hM_entry 0 j
            · exact (hχδ 0).le
            · exact hM_entry 1 j
            · exact (hχδ 1).le
        _ < 2 * M * δ := by nlinarith
        _ = 1 / 2 := by dsimp [δ]; field_simp; ring
    exact ⟨by linarith [(abs_lt.mp habs).1], (abs_lt.mp habs).2⟩
  rw [torusCoords_dualTorusMap_eq_mulVec A χ hsmall, sl2zToPSL2R_apply]
  have hcast : ((A : Matrix (Fin 2) (Fin 2) ℤ)ᵀ.map (Int.cast : ℤ → ℝ)) =
      (((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g)⁻¹ : SL(2, ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ)ᵀ := by
    have hinv : Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A =
        (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g)⁻¹ := by
      simp [A]
    rw [← hinv]
    ext i j
    rfl
  rw [hcast]
  exact symplecticProj_mulVec_transpose_inv
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g)
    (mt (torusCoords_eq_zero_iff χ).mp hχ1)

section SpectralEstimates

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Perturbation bound for integrals of bounded measurable real functions against diagonal
measures of unit vectors. -/
theorem abs_integral_diag_sub_le (P : ProjValMeasure X H) {f : X → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfC : ∀ x, |f x| ≤ C) {ξ η : H} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) :
    |(∫ x, f x ∂(P.diag η)) - ∫ x, f x ∂(P.diag ξ)| ≤ 2 * C * ‖η - ξ‖ := by
  let fB : BoundedBorelFunction X :=
    BoundedBorelFunction.ofFunction (fun x ↦ (f x : ℂ))
      (Complex.continuous_ofReal.measurable.comp hf)
      ⟨C, hC, fun x ↦ by simpa [Complex.norm_real] using hfC x⟩
  have hfB_norm : ‖fB‖ ≤ C :=
    (BoundedBorelFunction.norm_le hC).mpr fun x ↦ by simpa [fB, Complex.norm_real] using hfC x
  have heq : ‖(((∫ x, f x ∂(P.diag η)) - ∫ x, f x ∂(P.diag ξ) : ℝ) : ℂ)‖ =
      ‖(∫ x, fB x ∂(P.diag η)) - ∫ x, fB x ∂(P.diag ξ)‖ := by
    push_cast
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    simp only [fB, BoundedBorelFunction.ofFunction_apply]
  rw [← Real.norm_eq_abs, ← Complex.norm_real, heq]
  refine (P.norm_integral_diag_sub_le fB ξ η).trans ?_
  rw [hξ, hη]
  nlinarith [norm_nonneg (η - ξ)]

end SpectralEstimates

/-- Concentration bound near the trivial character for the spectral measure of a unitary `ℤ²`
representation: the `P.diag ξ`-mass outside `(-δ, δ)²` is controlled by the displacements of the
two standard generators of `ℤ²`. -/
theorem diag_outside_box_toReal_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {_ : MeasurableSpace (PontryaginDual (Multiplicative (Fin 2 → ℤ)))}
    [BorelSpace (PontryaginDual (Multiplicative (Fin 2 → ℤ)))]
    {π : ContRepresentation ℂ (Multiplicative (Fin 2 → ℤ)) H} (hπ : π.IsUnitary)
    {δ c : ℝ} (hc : 0 < c)
    (hc_le : ∀ t : ℝ, δ ≤ |t| → |t| ≤ 1 / 2 →
      c ≤ ‖(AddCircle.toCircle (t : AddCircle (1 : ℝ)) : ℂ) - 1‖ ^ 2)
    (ξ : H) :
    ((π.spectralPVM hπ).diag ξ
        {χ | ¬ ∀ j : Fin 2, |torusCoords χ j| < δ}).toReal ≤
      (‖π (Multiplicative.ofAdd (Pi.single 0 1)) ξ - ξ‖ ^ 2 +
        ‖π (Multiplicative.ofAdd (Pi.single 1 1)) ξ - ξ‖ ^ 2) / c := by
  let P := π.spectralPVM hπ
  have hcoord (j : Fin 2) :
      c * (P.diag ξ {χ | δ ≤ |torusCoords χ j|}).toReal ≤
        ‖π (Multiplicative.ofAdd (Pi.single j 1)) ξ - ξ‖ ^ 2 := by
    let B : Set (PontryaginDual (Multiplicative (Fin 2 → ℤ))) := {χ | δ ≤ |torusCoords χ j|}
    have hBm : MeasurableSet B :=
      measurableSet_Ici.preimage ((measurable_pi_apply j).comp measurable_torusCoords).norm
    let E : BoundedBorelFunction (PontryaginDual (Multiplicative (Fin 2 → ℤ))) :=
      BoundedBorelFunction.ofContinuousMap
        (PontryaginDual.evalBoundedContinuous (Pi.single j (1 : ℤ))).toContinuousMap - 1
    have hE_int : P.integral E ξ = π (Multiplicative.ofAdd (Pi.single j 1)) ξ - ξ := by
      simp [P, E, map_sub, map_one]
    have hE_norm : ‖π (Multiplicative.ofAdd (Pi.single j 1)) ξ - ξ‖ ^ 2 =
        ∫ χ, ‖E χ‖ ^ 2 ∂(P.diag ξ) := by
      rw [← hE_int, P.norm_sq_integral_apply]
    have hint : Integrable (fun χ ↦ ‖E χ‖ ^ 2) (P.diag ξ) :=
      .of_bound (E.measurable.norm.pow_const 2).aestronglyMeasurable (‖E‖ ^ 2)
        (.of_forall fun χ ↦ by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (E.norm_coe_le_norm χ) 2)
    have hle : ∀ χ, B.indicator (fun _ ↦ c) χ ≤ ‖E χ‖ ^ 2 := fun χ ↦ by
      by_cases hχ : χ ∈ B
      · rw [indicator_of_mem hχ]
        have h1 : c ≤ ‖(AddCircle.toCircle (torusCoords χ j : AddCircle (1 : ℝ)) : ℂ) - 1‖ ^ 2 :=
          hc_le (torusCoords χ j) hχ (abs_torusAngle_le _)
        rw [toCircle_torusCoords] at h1
        simpa [E] using h1
      · rw [indicator_of_notMem hχ]
        exact sq_nonneg _
    rw [hE_norm]
    calc c * (P.diag ξ B).toReal
      _ = ∫ χ, B.indicator (fun _ ↦ c) χ ∂(P.diag ξ) := by
          rw [integral_indicator_const _ hBm, smul_eq_mul, mul_comm, measureReal_def]
      _ ≤ ∫ χ, ‖E χ‖ ^ 2 ∂(P.diag ξ) :=
          integral_mono (integrable_const c |>.indicator hBm) hint hle
  have hsub : {χ | ¬ ∀ j : Fin 2, |torusCoords χ j| < δ} ⊆
      {χ | δ ≤ |torusCoords χ 0|} ∪ {χ | δ ≤ |torusCoords χ 1|} := by
    intro χ hχ
    rw [Set.mem_ofPred_eq, not_forall] at hχ
    obtain ⟨j, hj⟩ := hχ
    fin_cases j
    · exact Or.inl (not_lt.mp hj)
    · exact Or.inr (not_lt.mp hj)
  have hmeas_le : (P.diag ξ {χ | ¬ ∀ j : Fin 2, |torusCoords χ j| < δ}).toReal ≤
      (P.diag ξ {χ | δ ≤ |torusCoords χ 0|}).toReal +
        (P.diag ξ {χ | δ ≤ |torusCoords χ 1|}).toReal := by
    have h1 : P.diag ξ {χ | ¬ ∀ j : Fin 2, |torusCoords χ j| < δ} ≤
        P.diag ξ {χ | δ ≤ |torusCoords χ 0|} + P.diag ξ {χ | δ ≤ |torusCoords χ 1|} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h1
  rw [le_div_iff₀ hc]
  linarith [hcoord 0, hcoord 1, mul_le_mul_of_nonneg_left hmeas_le hc.le]

/-- Quantitative almost-invariance estimate for the pushed-forward spectral measure on
`OnePoint ℝ` under the Möbius action of `sl2zToPSL2R (ι g)`. -/
theorem abs_integral_map_symplecticProj_sub_le
    {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {_ : MeasurableSpace (PontryaginDual (Multiplicative (Fin 2 → ℤ)))}
    [BorelSpace (PontryaginDual (Multiplicative (Fin 2 → ℤ)))]
    {_ : MeasurableSpace (OnePoint ℝ)} [BorelSpace (OnePoint ℝ)]
    {ι : G →* SL(2, ℤ)}
    {ρ : ContRepresentation ℂ (Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction.comp ι] G) H}
    (hρ : ρ.IsUnitary) (g : G) (F : OnePoint ℝ →ᵇ ℝ)
    {δ c : ℝ} (hc_pos : 0 < c)
    (hc_le : ∀ t : ℝ, δ ≤ |t| → |t| ≤ 1 / 2 →
      c ≤ ‖(AddCircle.toCircle (t : AddCircle (1 : ℝ)) : ℂ) - 1‖ ^ 2)
    (hS_equiv : ∀ χ : PontryaginDual (Multiplicative (Fin 2 → ℤ)),
      χ ≠ 1 → (∀ j : Fin 2, |torusCoords χ j| < δ) →
      symplecticProj (torusCoords (dualTorusMap (ι g)⁻¹ χ)) =
        sl2zToPSL2R (ι g) • symplecticProj (torusCoords χ))
    {ξ : H} (hξ_norm : ‖ξ‖ = 1)
    (hdiag_one : ((ρ.restrict (SemidirectProduct.inl (G := G)
      (φ := slTwoAction.comp ι))).spectralPVM (hρ.restrict _)).diag ξ {1} = 0) :
    let π := ρ.restrict (SemidirectProduct.inl (G := G) (φ := slTwoAction.comp ι))
    let μ := Measure.map (symplecticProj ∘ torusCoords) ((π.spectralPVM (hρ.restrict _)).diag ξ)
    |(∫ y, F (sl2zToPSL2R (ι g) • y) ∂μ) - ∫ y, F y ∂μ| ≤
      2 * ‖F‖ * ((‖π (Multiplicative.ofAdd (Pi.single 0 1)) ξ - ξ‖ ^ 2 +
        ‖π (Multiplicative.ofAdd (Pi.single 1 1)) ξ - ξ‖ ^ 2) / c) +
      2 * ‖F‖ * ‖ρ (SemidirectProduct.inr g⁻¹) ξ - ξ‖ := by
  let inlHom := SemidirectProduct.inl (G := G) (φ := slTwoAction.comp ι)
  let inrHom := SemidirectProduct.inr (N := Multiplicative (Fin 2 → ℤ)) (φ := slTwoAction.comp ι)
  let π := ρ.restrict inlHom
  have hπ : π.IsUnitary := hρ.restrict inlHom
  let P := π.spectralPVM hπ
  let Φ := symplecticProj ∘ torusCoords
  have hΦ_meas : Measurable Φ := measurable_symplecticProj.comp measurable_torusCoords
  let A : SL(2, ℤ) := ι g⁻¹
  let η : H := ρ (inrHom g⁻¹) ξ
  have hη_norm : ‖η‖ = 1 := by simpa [η, hξ_norm] using hρ.norm_map (inrHom g⁻¹) ξ
  have hFg_cont : Continuous (fun y : OnePoint ℝ ↦ F (sl2zToPSL2R (ι g) • y)) :=
    F.continuous.comp (continuous_const_smul _)
  have hI1 : ∫ y, F (sl2zToPSL2R (ι g) • y) ∂(Measure.map Φ (P.diag ξ)) =
      ∫ χ, F (sl2zToPSL2R (ι g) • Φ χ) ∂(P.diag ξ) :=
    integral_map hΦ_meas.aemeasurable hFg_cont.aestronglyMeasurable
  have hmap_diag : Measure.map (dualTorusMap A) (P.diag η) = P.diag ξ :=
    ContRepresentation.map_diag_spectralPVM_restrict_inl_apply_inr hρ g⁻¹ ξ
  have hI2 : ∫ y, F y ∂(Measure.map Φ (P.diag ξ)) =
      ∫ χ, F (Φ (dualTorusMap A χ)) ∂(P.diag η) := by
    rw [integral_map hΦ_meas.aemeasurable F.continuous.aestronglyMeasurable, ← hmap_diag,
      integral_map (f := fun x ↦ F (Φ x))
        (map_continuous (dualTorusMap A)).measurable.aemeasurable
        (F.continuous.measurable.comp hΦ_meas).aestronglyMeasurable]
  let Imid : ℝ := ∫ χ, F (Φ (dualTorusMap A χ)) ∂(P.diag ξ)
  have hdiff2 : |Imid - ∫ χ, F (Φ (dualTorusMap A χ)) ∂(P.diag η)| ≤ 2 * ‖F‖ * ‖η - ξ‖ := by
    rw [abs_sub_comm]
    exact abs_integral_diag_sub_le P
      (F.continuous.measurable.comp (hΦ_meas.comp (map_continuous (dualTorusMap A)).measurable))
      (norm_nonneg F) (fun _ ↦ F.norm_coe_le_norm _) hξ_norm hη_norm
  have hdiff1 : |(∫ χ, F (sl2zToPSL2R (ι g) • Φ χ) ∂(P.diag ξ)) - Imid| ≤
      2 * ‖F‖ * ((‖π (Multiplicative.ofAdd (Pi.single 0 1)) ξ - ξ‖ ^ 2 +
        ‖π (Multiplicative.ofAdd (Pi.single 1 1)) ξ - ξ‖ ^ 2) / c) := by
    let f1 := fun χ ↦ F (sl2zToPSL2R (ι g) • Φ χ)
    let f2 := fun χ ↦ F (Φ (dualTorusMap A χ))
    have hf1 : Integrable f1 (P.diag ξ) :=
      .of_bound (hFg_cont.measurable.comp hΦ_meas).aestronglyMeasurable ‖F‖
        (.of_forall fun _ ↦ F.norm_coe_le_norm _)
    have hf2 : Integrable f2 (P.diag ξ) :=
      .of_bound (F.continuous.measurable.comp
        (hΦ_meas.comp (map_continuous (dualTorusMap A)).measurable)).aestronglyMeasurable
        ‖F‖ (.of_forall fun _ ↦ F.norm_coe_le_norm _)
    let B : Set (PontryaginDual (Multiplicative (Fin 2 → ℤ))) :=
      {χ | ¬ ∀ j : Fin 2, |torusCoords χ j| < δ}
    have hBm : MeasurableSet B := by
      have hBeq : B = (⋂ j : Fin 2, {χ | |torusCoords χ j| < δ})ᶜ := by
        ext
        simp only [B, mem_compl_iff, mem_iInter, Set.mem_ofPred_eq]
      rw [hBeq]
      refine (MeasurableSet.iInter fun j ↦ ?_).compl
      exact (continuous_abs.measurable.comp
        ((measurable_pi_apply j).comp measurable_torusCoords)) measurableSet_Iio
    have hae_le : (fun χ ↦ ‖f1 χ - f2 χ‖) ≤ᵐ[P.diag ξ] B.indicator (fun _ ↦ 2 * ‖F‖) := by
      have hnot1 : ∀ᵐ χ ∂(P.diag ξ), χ ≠ 1 := by rw [ae_iff]; simpa using hdiag_one
      filter_upwards [hnot1] with χ hχ1
      by_cases hχB : χ ∈ B
      · rw [indicator_of_mem hχB, Real.norm_eq_abs]
        calc |f1 χ - f2 χ|
          _ ≤ |f1 χ| + |f2 χ| := abs_sub _ _
          _ ≤ ‖F‖ + ‖F‖ := add_le_add (F.norm_coe_le_norm _) (F.norm_coe_le_norm _)
          _ = 2 * ‖F‖ := by ring
      · rw [indicator_of_notMem hχB]
        have hA : A = (ι g)⁻¹ := map_inv ι g
        simp [f1, f2, Φ, hA, hS_equiv χ hχ1 (not_not.mp hχB)]
    calc |(∫ χ, f1 χ ∂(P.diag ξ)) - ∫ χ, f2 χ ∂(P.diag ξ)|
      _ = ‖∫ χ, (f1 χ - f2 χ) ∂(P.diag ξ)‖ := by rw [← integral_sub hf1 hf2, Real.norm_eq_abs]
      _ ≤ ∫ χ, ‖f1 χ - f2 χ‖ ∂(P.diag ξ) := norm_integral_le_integral_norm _
      _ ≤ ∫ χ, B.indicator (fun _ ↦ 2 * ‖F‖) χ ∂(P.diag ξ) :=
          integral_mono_ae (hf1.sub hf2).norm ((integrable_const _).indicator hBm) hae_le
      _ = 2 * ‖F‖ * (P.diag ξ B).toReal := by
          rw [integral_indicator_const _ hBm, smul_eq_mul, mul_comm, measureReal_def]
      _ ≤ 2 * ‖F‖ * ((‖π (Multiplicative.ofAdd (Pi.single 0 1)) ξ - ξ‖ ^ 2 +
            ‖π (Multiplicative.ofAdd (Pi.single 1 1)) ξ - ξ‖ ^ 2) / c) :=
          mul_le_mul_of_nonneg_left (diag_outside_box_toReal_le hπ hc_pos hc_le ξ) (by positivity)
  dsimp only
  rw [hI1, hI2]
  exact (abs_sub_le _ Imid _).trans (add_le_add hdiff1 hdiff2)

/-- Extract a directed net of unit vectors whose displacements tend to `0` at every group element
from `ContRepresentation.HasAlmostInvariantVectors`. -/
theorem exists_unit_net_tendsto_sub_zero {Γ H : Type*} [Group Γ]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ρ : ContRepresentation ℂ Γ H} (halm : ρ.HasAlmostInvariantVectors) :
    ∃ ξ : Finset Γ × ℕ → H, (∀ p, ‖ξ p‖ = 1) ∧
      ∀ γ : Γ, Tendsto (fun p ↦ ‖ρ γ (ξ p) - ξ p‖) atTop (𝓝 0) := by
  classical
  have hex (p : Finset Γ × ℕ) :
      ∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ γ ∈ p.1, ‖ρ γ ξ - ξ‖ < 1 / (p.2 + 1 : ℝ) :=
    (ContRepresentation.hasAlmostInvariantVectors_def ρ).mp halm p.1 (1 / (p.2 + 1 : ℝ))
      (by positivity)
  choose ξ hξ_norm hξ_alm using hex
  refine ⟨ξ, hξ_norm, fun γ ↦ Metric.tendsto_nhds.mpr fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hεN : 1 / (N + 1 : ℝ) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    have : 1 / ε < (N + 1 : ℝ) := hN.trans (by linarith)
    rwa [div_lt_iff₀ hε, mul_comm] at this
  refine eventually_atTop.mpr ⟨({γ}, N), fun p hp ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have h1 : ‖ρ γ (ξ p) - ξ p‖ < 1 / (p.2 + 1 : ℝ) :=
    hξ_alm p γ (hp.1 (Finset.mem_singleton_self γ))
  have h2 : 1 / (p.2 + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hp.2 1)
  linarith

theorem infinite_multiplicative_fin_two_int : Infinite (Multiplicative (Fin 2 → ℤ)) :=
  Infinite.of_injective (fun n : ℤ ↦ Multiplicative.ofAdd ![n, 0]) fun a b h ↦ by
    simpa using congrFun (Multiplicative.toAdd.injective h) 0

theorem infinite_range_inl {N G : Type*} [Group N] [Infinite N] [Group G] (φ : G →* MulAut N) :
    Infinite (SemidirectProduct.inl (G := G) (φ := φ)).range :=
  Infinite.of_injective (SemidirectProduct.inl (G := G) (φ := φ)).rangeRestrict fun _ _ h ↦
    SemidirectProduct.inl_injective (congrArg Subtype.val h)

end BurgerProof

end TauCeti

public section

namespace TauCeti

open BurgerProof

/-- **Burger's theorem** (Følner form): if `G` embeds injectively into `SL(2, ℤ)` and does not have
Følner sets, then the normal subgroup `ℤ²` inside `ℤ² ⋊ G` has relative property (T) in every
Hilbert-space universe `u`. -/
theorem relativePropertyT_inl_of_injective_of_not_hasFoelnerSets.{u, v}
    {G : Type v} [Group G] {ι : G →* SL(2, ℤ)} (hι : Function.Injective ι)
    (hG : ¬ HasFoelnerSets G) :
    (SemidirectProduct.inl (G := G) (φ := slTwoAction.comp ι)).range.RelativePropertyT.{u} := by
  classical
  rw [Subgroup.relativePropertyT_def]
  intro H _ _ _ ρ hρ halm
  by_contra! hno_inv
  let T := PontryaginDual (Multiplicative (Fin 2 → ℤ))
  let : MeasurableSpace T := borel T
  have : BorelSpace T := ⟨rfl⟩
  let : MeasurableSpace (OnePoint ℝ) := borel (OnePoint ℝ)
  have : BorelSpace (OnePoint ℝ) := ⟨rfl⟩
  have : SecondCountableTopology (OnePoint ℝ) :=
    (OnePoint.diffeomorphProjectivization ℝ 0).toHomeomorph.secondCountableTopology
  have : TopologicalSpace.MetrizableSpace (OnePoint ℝ) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable (OnePoint ℝ)
  let inlHom := SemidirectProduct.inl (G := G) (φ := slTwoAction.comp ι)
  let inrHom := SemidirectProduct.inr (N := Multiplicative (Fin 2 → ℤ)) (φ := slTwoAction.comp ι)
  let π := ρ.restrict inlHom
  have hπ : π.IsUnitary := hρ.restrict inlHom
  let P := π.spectralPVM hπ
  have hdiag_one (ξ : H) : P.diag ξ {1} = 0 := by
    have hfix : P.proj {1} (measurableSet_singleton 1) ξ ∈ π.invariants := fun n ↦
      ContRepresentation.apply_spectralPVM_proj_singleton_one hπ n ξ
    have hzero : P.proj {1} (measurableSet_singleton 1) ξ = 0 := by
      by_contra hv0
      exact hno_inv _ hv0 fun ⟨_, ⟨n, rfl⟩⟩ ↦ hfix n
    have htoReal : (P.diag ξ {1}).toReal = 0 := by
      rw [← P.norm_sq_proj_apply {1} (measurableSet_singleton 1) ξ, hzero, norm_zero, sq, mul_zero]
    exact (ENNReal.toReal_eq_zero_iff _).mp htoReal |>.resolve_right (measure_ne_top _ _)
  -- Push forward the spectral diagonal measures along `symplecticProj ∘ torusCoords` and pass to a
  -- weak-* cluster point in the compact space `ProbabilityMeasure (OnePoint ℝ)`.
  obtain ⟨ξ, hξ_norm, hξ_tendsto⟩ := exists_unit_net_tendsto_sub_zero halm
  have hΦ_meas : Measurable (symplecticProj ∘ torusCoords) :=
    measurable_symplecticProj.comp measurable_torusCoords
  let μNet (p : Finset (Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction.comp ι] G) × ℕ) :
      ProbabilityMeasure (OnePoint ℝ) :=
    ⟨Measure.map (symplecticProj ∘ torusCoords) (P.diag (ξ p)), by
      have hprob : IsProbabilityMeasure (P.diag (ξ p)) := ⟨by
        rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), P.diag_univ_toReal, hξ_norm p,
          one_pow, ENNReal.ofReal_one]⟩
      exact (Measure.isProbabilityMeasure_map_iff hΦ_meas.aemeasurable).mpr hprob⟩
  obtain ⟨ν₀, -, hν₀_cluster⟩ := isCompact_univ.exists_clusterPt
    (f := Filter.map μNet atTop) (le_principal_iff.mpr univ_mem)
  -- Every `g ∈ G` fixes `ν₀`: tested against any bounded continuous `F`, the integral discrepancy
  -- along `μNet` tends to `0`, while `D (ν₀)` is a cluster point of `D ∘ μNet`.
  have hν₀_inv (g : G) :
      Measure.map (sl2zToPSL2R (ι g) • ·) (ν₀ : Measure (OnePoint ℝ)) = ν₀ := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro F
    let Fg : OnePoint ℝ →ᵇ ℝ :=
      F.compContinuous ⟨(sl2zToPSL2R (ι g) • ·), continuous_const_smul _⟩
    rw [integral_map (continuous_const_smul _).measurable.aemeasurable
      F.continuous.aestronglyMeasurable]
    let D : ProbabilityMeasure (OnePoint ℝ) → ℝ := fun ν ↦
      (∫ y, Fg y ∂(ν : Measure (OnePoint ℝ))) - ∫ y, F y ∂(ν : Measure (OnePoint ℝ))
    have hD_cont : Continuous D :=
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction Fg).sub
        (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F)
    obtain ⟨δ, c, hc_pos, hc_le, hS_equiv⟩ := exists_small_box_symplecticProj_equiv (ι g)
    have hbound_tendsto : Tendsto
        (fun p ↦ 2 * ‖F‖ *
            ((‖π (Multiplicative.ofAdd (Pi.single 0 1)) (ξ p) - ξ p‖ ^ 2 +
              ‖π (Multiplicative.ofAdd (Pi.single 1 1)) (ξ p) - ξ p‖ ^ 2) / c) +
          2 * ‖F‖ * ‖ρ (inrHom g⁻¹) (ξ p) - ξ p‖) atTop (𝓝 0) := by
      have h0 := hξ_tendsto (inlHom (Multiplicative.ofAdd (Pi.single 0 1)))
      have h1 := hξ_tendsto (inlHom (Multiplicative.ofAdd (Pi.single 1 1)))
      have hg := hξ_tendsto (inrHom g⁻¹)
      simpa [π] using
        (((((h0.pow 2).add (h1.pow 2)).div_const c).const_mul (2 * ‖F‖)).add
          (hg.const_mul (2 * ‖F‖)))
    have hD_tendsto : Tendsto (D ∘ μNet) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (Eventually.of_forall fun p ↦ ?_) hbound_tendsto
      dsimp only [Function.comp_apply, D, Fg, μNet, P, π, inlHom, inrHom]
      rw [Real.norm_eq_abs]
      exact abs_integral_map_symplecticProj_sub_le hρ g F hc_pos hc_le hS_equiv
        (hξ_norm p) (hdiag_one (ξ p))
    have hD_zero : D ν₀ = 0 :=
      eq_of_nhds_neBot
        (hν₀_cluster.map hD_cont.continuousAt (tendsto_map'_iff.mpr hD_tendsto)).neBot
    simpa [Fg] using sub_eq_zero.mp hD_zero
  exact hG (hasFoelnerSets_of_injective_sl2z_of_map_smul_eq hι
    (IsProbabilityMeasure.ne_zero (ν₀ : Measure (OnePoint ℝ))) hν₀_inv)

/-- **Burger's theorem**: if a topological group `G` embeds injectively into `SL(2, ℤ)` and is not
amenable, then the normal subgroup `ℤ²` inside `ℤ² ⋊ G` has relative property (T) in every
Hilbert-space universe `u`. -/
theorem relativePropertyT_inl_of_injective_of_not_amenable.{u, v}
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ι : G →* SL(2, ℤ)} (hι : Function.Injective ι) (hG : ¬ Amenable G) :
    (SemidirectProduct.inl (G := G) (φ := slTwoAction.comp ι)).range.RelativePropertyT.{u} :=
  relativePropertyT_inl_of_injective_of_not_hasFoelnerSets hι
    (mt Amenable.of_hasFoelnerSets hG)

/-- **Burger's theorem** for subgroups `G ≤ SL(2, ℤ)`: if `G` is not amenable, then the pair
`(ℤ² ⋊ G, ℤ²)` has relative property (T) in every Hilbert-space universe `u`. -/
theorem relativePropertyT_inl_of_not_amenable.{u}
    (G : Subgroup SL(2, ℤ)) (hG : ¬ Amenable G) :
    (SemidirectProduct.inl (G := G)
      (φ := slTwoAction.comp G.subtype)).range.RelativePropertyT.{u} :=
  relativePropertyT_inl_of_injective_of_not_amenable G.subtype_injective hG

/-- **Amenability characterization of relative property (T) for `(ℤ² ⋊ G, ℤ²)`**: for any subgroup
`G ≤ SL(2, ℤ)`, the pair `(ℤ² ⋊ G, ℤ²)` has relative property (T) in universe `u` if and only if
`G` is not amenable. -/
theorem relativePropertyT_inl_iff_not_amenable.{u} (G : Subgroup SL(2, ℤ)) :
    (SemidirectProduct.inl (G := G)
        (φ := slTwoAction.comp G.subtype)).range.RelativePropertyT.{u} ↔
      ¬ Amenable G := by
  refine ⟨fun hT hAmen ↦ ?_, relativePropertyT_inl_of_not_amenable G⟩
  let : TopologicalSpace (Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction.comp G.subtype] G) := ⊥
  have : DiscreteTopology (Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction.comp G.subtype] G) := ⟨rfl⟩
  have : Infinite (Multiplicative (Fin 2 → ℤ)) := infinite_multiplicative_fin_two_int
  have : Infinite (SemidirectProduct.inl (G := G) (φ := slTwoAction.comp G.subtype)).range :=
    infinite_range_inl _
  exact not_hasHaagerupProperty_of_relativePropertyT.{u, 0} hT hasHaagerupProperty_of_amenable

/-- The modular group `SL(2, ℤ)` is not amenable. -/
theorem not_amenable_slTwoZ : ¬ Amenable SL(2, ℤ) :=
  not_amenable_of_injective_freeGroup _ injective_freeGroup_lift_transvection_two

/-- **Kazhdan–Margulis theorem**: the pair `(ℤ² ⋊ SL(2, ℤ), ℤ²)` has relative property (T) in
every Hilbert-space universe `u`. -/
theorem relativePropertyT_inl_slTwo.{u} :
    (SemidirectProduct.inl (G := SL(2, ℤ)) (φ := slTwoAction)).range.RelativePropertyT.{u} :=
  relativePropertyT_inl_of_injective_of_not_amenable (ι := MonoidHom.id SL(2, ℤ))
    Function.injective_id not_amenable_slTwoZ

/-- For every nonamenable subgroup `G ≤ SL(2, ℤ)`, the semidirect product `ℤ² ⋊ G` does not have
the Haagerup property. -/
theorem not_hasHaagerupProperty_semidirectProduct_of_not_amenable
    (G : Subgroup SL(2, ℤ)) (hG : ¬ Amenable G) :
    ¬ HasHaagerupProperty (Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction.comp G.subtype] G) := by
  have : Infinite (Multiplicative (Fin 2 → ℤ)) := infinite_multiplicative_fin_two_int
  have : Infinite (SemidirectProduct.inl (G := G) (φ := slTwoAction.comp G.subtype)).range :=
    infinite_range_inl _
  exact not_hasHaagerupProperty_of_relativePropertyT.{0, 0}
    (relativePropertyT_inl_of_not_amenable.{0} G hG)

/-- The semidirect product `ℤ² ⋊ SL(2, ℤ)` does not have the Haagerup property. -/
theorem not_hasHaagerupProperty_semidirectProduct_slTwo :
    ¬ HasHaagerupProperty (Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction] SL(2, ℤ)) := by
  have : Infinite (Multiplicative (Fin 2 → ℤ)) := infinite_multiplicative_fin_two_int
  have : Infinite (SemidirectProduct.inl (G := SL(2, ℤ)) (φ := slTwoAction)).range :=
    infinite_range_inl _
  exact not_hasHaagerupProperty_of_relativePropertyT.{0, 0} relativePropertyT_inl_slTwo.{0}

/-- For any injective linear action `ι : FreeGroup α →* SL(2, ℤ)` of a free group on at least two
generators (for instance Sanov's embedding for `α = Fin 2`), the pair `(ℤ² ⋊ FreeGroup α, ℤ²)` has
relative property (T) in every Hilbert-space universe `u`. -/
theorem relativePropertyT_inl_freeGroup.{u} {α : Type*} [Nontrivial α]
    {ι : FreeGroup α →* SL(2, ℤ)} (hι : Function.Injective ι) :
    (SemidirectProduct.inl (G := FreeGroup α)
      (φ := slTwoAction.comp ι)).range.RelativePropertyT.{u} := by
  let : TopologicalSpace (FreeGroup α) := ⊥
  have : DiscreteTopology (FreeGroup α) := ⟨rfl⟩
  exact relativePropertyT_inl_of_injective_of_not_amenable hι not_amenable_freeGroup

/-- For a unipotent transvection subgroup `(Matrix.SpecialLinearGroup.transvectionHom hij).range`
of `SL(2, ℤ)`, the pair `(ℤ² ⋊ G, ℤ²)` does not have relative property (T) in any universe `u`. -/
theorem not_relativePropertyT_inl_range_transvectionHom.{u} {i j : Fin 2} (hij : i ≠ j) :
    ¬ (SemidirectProduct.inl
        (G := (Matrix.SpecialLinearGroup.transvectionHom (A := ℤ) hij).range)
        (φ := slTwoAction.comp
          (Matrix.SpecialLinearGroup.transvectionHom
            (A := ℤ) hij).range.subtype)).range.RelativePropertyT.{u} := by
  rw [relativePropertyT_inl_iff_not_amenable, not_not]
  exact .of_denseRange
    ⟨(Matrix.SpecialLinearGroup.transvectionHom (A := ℤ) hij).rangeRestrict,
      continuous_of_discreteTopology⟩
    (MonoidHom.rangeRestrict_surjective _).denseRange

end TauCeti

end
