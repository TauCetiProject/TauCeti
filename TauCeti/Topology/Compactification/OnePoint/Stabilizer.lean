/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.AffineSpace.AffineEquiv
public import TauCeti.Topology.Compactification.OnePoint.MultipleTransitivity

/-!
# Stabilizers of one, two and three points of the projective line

Let `K` be a field. The Möbius transformations of the projective line `OnePoint K` act sharply
triply transitively (`OnePoint.existsUnique_pgl_smul_zero_one_infty_eq`). This file identifies the
subgroups of `PGL(2, K)` fixing one, two and three points.

* The stabilizer of `∞` is the **affine group** `K ≃ᵃ[K] K` of the line, the maps `z ↦ a * z + b`
  with `a ≠ 0` (`OnePoint.pglStabilizerInftyEquiv`). An element fixing `∞` preserves the affine
  part `K` of the projective line, and the equivalence sends it to its restriction there. Through
  `AffineEquiv.linearHom` and `AffineEquiv.constVAddHom` the affine group is the semidirect product
  `K ⋊ Kˣ` of the translations by the dilations; the translations alone are only its unipotent
  radical.
* The subgroup fixing both `0` and `∞` is the group `Kˣ` of dilations `z ↦ a * z`
  (`OnePoint.pglFixingZeroInftyEquiv`).
* The subgroup fixing three distinct points is trivial (`OnePoint.fixingSubgroup_pgl_eq_bot`).

Since the action is transitive, the stabilizer of any other point is conjugate to that of `∞`
(`MulAction.stabilizerEquivStabilizer`), and similarly for pairs of distinct points.

The same holds for `PSL(2, K)` when every unit of `K` is a square, in particular for the
automorphisms `PSL(2, ℂ)` of the Riemann sphere: there the inclusion `PSL(2, K) → PGL(2, K)` is
bijective and compatible with the actions, so it identifies the corresponding stabilizers
(`OnePoint.comap_toPGL_stabilizer`, `OnePoint.comap_toPGL_fixingSubgroup`). The subgroup of
`PSL(2, K)` fixing three distinct points is trivial over every field
(`OnePoint.fixingSubgroup_psl_eq_bot`). Without square roots the inclusion carries the one- and
two-point stabilizers of `PSL(2, K)` onto proper subgroups of those of `PGL(2, K)`: the class of
`!![a, 0; 0, a⁻¹]` acts by `z ↦ a ^ 2 * z`, so over `ℝ` no element of `PSL(2, ℝ)` fixing `0` and
`∞` acts by `z ↦ -z`.

For the Riemann sphere these are the reparametrization groups of a genus-zero domain with one,
two and three marked points: `ℂ ⋊ ℂˣ`, `ℂˣ` and the trivial group.

## Main declarations

* `OnePoint.pglStabilizerInftyEquiv`, `OnePoint.pslStabilizerInftyEquiv`: the stabilizer of `∞`
  is the affine group of the line.
* `OnePoint.pglFixingZeroInftyEquiv`, `OnePoint.pslFixingZeroInftyEquiv`: the subgroup fixing `0`
  and `∞` is the multiplicative group of dilations.
* `OnePoint.fixingSubgroup_pgl_eq_bot`, `OnePoint.fixingSubgroup_psl_eq_bot`: the subgroup fixing
  three distinct points is trivial.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §§3.2 and 4.3.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §2.
-/

public section

open Function Matrix MulAction
open scoped MatrixGroups

namespace OnePoint

variable {K : Type*} [Field K]

/-! ### Affine maps of the line as Möbius transformations -/

variable [DecidableEq K]

/-- The Möbius transformation of an affine map of the line. -/
private noncomputable def affineToPGL : (K ≃ᵃ[K] K) →* PGL(2, K) :=
  ProjGenLinGroup.mk.comp AffineEquiv.toGL

/-- The Möbius transformation of an affine map acts on the affine part as the map does. -/
private theorem affineToPGL_smul_coe (φ : K ≃ᵃ[K] K) (z : K) :
    affineToPGL φ • (z : OnePoint K) = (φ z : OnePoint K) := by
  rw [affineToPGL, MonoidHom.comp_apply, pglMk_smul, smul_some_eq_ite]
  simp [AffineEquiv.apply_eq_linear_one_mul_add φ z]

/-- The Möbius transformation of an affine map fixes `∞`. -/
private theorem affineToPGL_smul_infty (φ : K ≃ᵃ[K] K) :
    affineToPGL φ • (∞ : OnePoint K) = ∞ := by
  rw [affineToPGL, MonoidHom.comp_apply, pglMk_smul, smul_infty_eq_self_iff]
  simp

omit [DecidableEq K] in
private theorem affineToPGL_injective : Injective (affineToPGL (K := K)) := by
  classical
  intro φ ψ h
  refine AffineEquiv.ext fun z ↦ coe_injective ?_
  rw [← affineToPGL_smul_coe, ← affineToPGL_smul_coe, h]

/-- A Möbius transformation fixing `∞` is the transformation of an affine map. -/
private theorem exists_affineToPGL_eq {g : PGL(2, K)} (hg : g • (∞ : OnePoint K) = ∞) :
    ∃ φ : K ≃ᵃ[K] K, affineToPGL φ = g := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g =>
  rw [pglMk_smul, smul_infty_eq_self_iff] at hg
  have hdet : g 0 0 * g 1 1 ≠ 0 := by
    simpa [det_fin_two, hg] using g.det_ne_zero
  have ha : g 0 0 / g 1 1 ≠ 0 := div_ne_zero (left_ne_zero_of_mul hdet) (right_ne_zero_of_mul hdet)
  let φ : K ≃ᵃ[K] K :=
    AffineEquiv.constVAdd K K (g 0 1 / g 1 1) * AffineEquiv.homothetyUnitsMulHom 0 (Units.mk0 _ ha)
  have hφ (z : K) : φ z = g 0 0 / g 1 1 * z + g 0 1 / g 1 1 := by
    simp [φ, AffineEquiv.coe_mul, AffineMap.homothety_apply, add_comm]
  refine ⟨φ, eq_of_smul_eq_smul (α := OnePoint K) fun x ↦ ?_⟩
  induction x using OnePoint.rec with
  | infty =>
    rw [affineToPGL_smul_infty, pglMk_smul, smul_infty_eq_self_iff.mpr hg]
  | coe z =>
    rw [affineToPGL_smul_coe, hφ, pglMk_smul, smul_some_eq_ite, hg, zero_mul, zero_add]
    simp only [right_ne_zero_of_mul hdet, ↓reduceIte, coe_eq_coe]
    field_simp

private theorem range_affineToPGL :
    (affineToPGL (K := K)).range = stabilizer PGL(2, K) (∞ : OnePoint K) := by
  ext g
  refine ⟨?_, fun hg ↦ exists_affineToPGL_eq hg⟩
  rintro ⟨φ, rfl⟩
  exact affineToPGL_smul_infty φ

/-! ### The stabilizer of `∞` in `PGL(2, K)` -/

/-- **The stabilizer of `∞` in `PGL(2, K)` is the affine group of the line.** An element fixing `∞`
preserves the affine part `K` of the projective line, and is sent to the affine map
`z ↦ a * z + b` by which it acts there (`OnePoint.coe_pglStabilizerInftyEquiv_apply`). -/
noncomputable def pglStabilizerInftyEquiv :
    stabilizer PGL(2, K) (∞ : OnePoint K) ≃* (K ≃ᵃ[K] K) :=
  ((MonoidHom.ofInjective affineToPGL_injective).trans
    (MulEquiv.subgroupCongr range_affineToPGL)).symm

/-- The element of the stabilizer of `∞` attached to an affine map acts on the affine part of the
projective line as the map does. -/
@[simp]
theorem pglStabilizerInftyEquiv_symm_smul_coe (φ : K ≃ᵃ[K] K) (z : K) :
    (pglStabilizerInftyEquiv.symm φ : PGL(2, K)) • (z : OnePoint K) = (φ z : OnePoint K) :=
  affineToPGL_smul_coe φ z

/-- The affine map attached to an element of the stabilizer of `∞` is its action on the affine
part of the projective line. -/
@[simp]
theorem coe_pglStabilizerInftyEquiv_apply (g : stabilizer PGL(2, K) (∞ : OnePoint K)) (z : K) :
    (pglStabilizerInftyEquiv g z : OnePoint K) = (g : PGL(2, K)) • (z : OnePoint K) := by
  conv_rhs => rw [← pglStabilizerInftyEquiv.symm_apply_apply g]
  rw [pglStabilizerInftyEquiv_symm_smul_coe]

/-! ### The subgroup of `PGL(2, K)` fixing `0` and `∞` -/

/-- The Möbius transformation of the dilation `z ↦ a * z`. -/
private noncomputable def unitsToPGL : Kˣ →* PGL(2, K) :=
  affineToPGL.comp (AffineEquiv.homothetyUnitsMulHom 0)

private theorem unitsToPGL_smul_coe (a : Kˣ) (z : K) :
    unitsToPGL a • (z : OnePoint K) = ((a * z : K) : OnePoint K) := by
  simp [unitsToPGL, affineToPGL_smul_coe, AffineMap.homothety_apply]

omit [DecidableEq K] in
private theorem unitsToPGL_injective : Injective (unitsToPGL (K := K)) := by
  classical
  intro a b h
  have h1 := congrArg (· • ((1 : K) : OnePoint K)) h
  simpa [unitsToPGL_smul_coe, Units.ext_iff] using h1

private theorem range_unitsToPGL :
    (unitsToPGL (K := K)).range = fixingSubgroup PGL(2, K) {((0 : K) : OnePoint K), ∞} := by
  ext g
  simp only [MonoidHom.mem_range, mem_fixingSubgroup_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨by simp [unitsToPGL_smul_coe], ?_⟩
    exact affineToPGL_smul_infty _
  · rintro ⟨h0, hinf⟩
    obtain ⟨φ, rfl⟩ := exists_affineToPGL_eq hinf
    have hφ0 : φ 0 = 0 := coe_injective (by rw [← affineToPGL_smul_coe, h0])
    refine ⟨Units.mk0 _ φ.linear_one_ne_zero, congrArg affineToPGL ?_⟩
    refine AffineEquiv.ext fun z ↦ ?_
    simp [AffineMap.homothety_apply, AffineEquiv.apply_eq_linear_one_mul_add φ z, hφ0, mul_comm]

/-- **The subgroup of `PGL(2, K)` fixing `0` and `∞` is the group of dilations.** An element
fixing `0` and `∞` acts on the affine part of the projective line as `z ↦ a * z` for a unique
unit `a` (`OnePoint.coe_pglFixingZeroInftyEquiv_mul`). -/
noncomputable def pglFixingZeroInftyEquiv :
    fixingSubgroup PGL(2, K) {((0 : K) : OnePoint K), ∞} ≃* Kˣ :=
  ((MonoidHom.ofInjective unitsToPGL_injective).trans
    (MulEquiv.subgroupCongr range_unitsToPGL)).symm

/-- The element fixing `0` and `∞` attached to a unit `a` acts as the dilation `z ↦ a * z`. -/
@[simp]
theorem pglFixingZeroInftyEquiv_symm_smul_coe (a : Kˣ) (z : K) :
    (pglFixingZeroInftyEquiv.symm a : PGL(2, K)) • (z : OnePoint K) =
      ((a * z : K) : OnePoint K) :=
  unitsToPGL_smul_coe a z

/-- An element fixing `0` and `∞` acts as the dilation by the attached unit. -/
@[simp]
theorem coe_pglFixingZeroInftyEquiv_mul
    (g : fixingSubgroup PGL(2, K) {((0 : K) : OnePoint K), ∞}) (z : K) :
    (((pglFixingZeroInftyEquiv g : K) * z : K) : OnePoint K) =
      (g : PGL(2, K)) • (z : OnePoint K) := by
  conv_rhs => rw [← pglFixingZeroInftyEquiv.symm_apply_apply g]
  rw [pglFixingZeroInftyEquiv_symm_smul_coe]

/-! ### Three points -/

/-- **The subgroup of `PGL(2, K)` fixing three distinct points of the projective line is
trivial.** -/
theorem fixingSubgroup_pgl_eq_bot {x y z : OnePoint K} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : fixingSubgroup PGL(2, K) {x, y, z} = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg ↦ ?_
  simp only [mem_fixingSubgroup_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq] at hg
  obtain ⟨h, hh, huniq⟩ := existsUnique_pgl_smul_zero_one_infty_eq hxy hxz hyz
  have hgh : g * h = h := huniq _ <| by simp only [mul_smul, hh.1, hh.2.1, hh.2.2, hg, and_self]
  simpa using hgh

/-! ### Transfer to `PSL(2, K)` -/

/-- The inclusion `PSL(2, K) → PGL(2, K)` pulls the stabilizer of a point back to its stabilizer
in `PSL(2, K)`. -/
@[simp]
theorem comap_toPGL_stabilizer (x : OnePoint K) :
    (stabilizer PGL(2, K) x).comap ProjectiveSpecialLinearGroup.toPGL = stabilizer PSL(2, K) x := by
  ext g
  simp [ProjectiveSpecialLinearGroup.toPGL_smul]

/-- The inclusion `PSL(2, K) → PGL(2, K)` pulls the subgroup fixing a set back to the subgroup of
`PSL(2, K)` fixing it. -/
@[simp]
theorem comap_toPGL_fixingSubgroup (s : Set (OnePoint K)) :
    (fixingSubgroup PGL(2, K) s).comap ProjectiveSpecialLinearGroup.toPGL =
      fixingSubgroup PSL(2, K) s := by
  ext g
  simp [mem_fixingSubgroup_iff, ProjectiveSpecialLinearGroup.toPGL_smul]

/-- **The subgroup of `PSL(2, K)` fixing three distinct points of the projective line is
trivial**, over every field. -/
theorem fixingSubgroup_psl_eq_bot {x y z : OnePoint K} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : fixingSubgroup PSL(2, K) {x, y, z} = ⊥ := by
  rw [← comap_toPGL_fixingSubgroup, fixingSubgroup_pgl_eq_bot hxy hxz hyz,
    MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff _).2
      ProjectiveSpecialLinearGroup.toPGL_injective]

section Roots

variable (hK : ∀ r : Kˣ, ∃ k : Kˣ, k ^ 2 = r)
include hK

/-- **The stabilizer of `∞` in `PSL(2, K)` is the affine group of the line** when every unit of
`K` is a square, as for the automorphisms `PSL(2, ℂ)` of the Riemann sphere. An element fixing `∞`
is sent to the affine map by which it acts on the affine part `K`
(`OnePoint.coe_pslStabilizerInftyEquiv_apply`). -/
noncomputable def pslStabilizerInftyEquiv :
    stabilizer PSL(2, K) (∞ : OnePoint K) ≃* (K ≃ᵃ[K] K) :=
  (MulEquiv.subgroupCongr (comap_toPGL_stabilizer ∞).symm).trans
    ((MulEquiv.ofBijective _ (ProjectiveSpecialLinearGroup.bijective_toPGL_subgroupComap_of_roots
        (by simpa using hK) _)).trans
      pglStabilizerInftyEquiv)

/-- The affine map attached to an element of the stabilizer of `∞` in `PSL(2, K)` is its action on
the affine part of the projective line. -/
@[simp]
theorem coe_pslStabilizerInftyEquiv_apply (g : stabilizer PSL(2, K) (∞ : OnePoint K)) (z : K) :
    (pslStabilizerInftyEquiv hK g z : OnePoint K) = (g : PSL(2, K)) • (z : OnePoint K) := by
  simp only [pslStabilizerInftyEquiv, MulEquiv.trans_apply, MulEquiv.ofBijective_apply,
    coe_pglStabilizerInftyEquiv_apply]
  exact ProjectiveSpecialLinearGroup.toPGL_smul (g : PSL(2, K)) (z : OnePoint K)

/-- The element of the stabilizer of `∞` in `PSL(2, K)` attached to an affine map acts on the
affine part of the projective line as the map does. -/
@[simp]
theorem pslStabilizerInftyEquiv_symm_smul_coe (φ : K ≃ᵃ[K] K) (z : K) :
    ((pslStabilizerInftyEquiv hK).symm φ : PSL(2, K)) • (z : OnePoint K) = (φ z : OnePoint K) := by
  rw [← coe_pslStabilizerInftyEquiv_apply hK, MulEquiv.apply_symm_apply]

/-- **The subgroup of `PSL(2, K)` fixing `0` and `∞` is the group of dilations** when every unit
of `K` is a square. An element fixing `0` and `∞` acts on the affine part of the projective line
as `z ↦ a * z` for a unique unit `a` (`OnePoint.coe_pslFixingZeroInftyEquiv_mul`). -/
noncomputable def pslFixingZeroInftyEquiv :
    fixingSubgroup PSL(2, K) {((0 : K) : OnePoint K), ∞} ≃* Kˣ :=
  (MulEquiv.subgroupCongr (comap_toPGL_fixingSubgroup _).symm).trans
    ((MulEquiv.ofBijective _ (ProjectiveSpecialLinearGroup.bijective_toPGL_subgroupComap_of_roots
        (by simpa using hK) _)).trans
      pglFixingZeroInftyEquiv)

/-- An element of `PSL(2, K)` fixing `0` and `∞` acts as the dilation by the attached unit. -/
@[simp]
theorem coe_pslFixingZeroInftyEquiv_mul
    (g : fixingSubgroup PSL(2, K) {((0 : K) : OnePoint K), ∞}) (z : K) :
    (((pslFixingZeroInftyEquiv hK g : K) * z : K) : OnePoint K) =
      (g : PSL(2, K)) • (z : OnePoint K) := by
  simp only [pslFixingZeroInftyEquiv, MulEquiv.trans_apply, MulEquiv.ofBijective_apply,
    coe_pglFixingZeroInftyEquiv_mul]
  exact ProjectiveSpecialLinearGroup.toPGL_smul (g : PSL(2, K)) (z : OnePoint K)

/-- The element of `PSL(2, K)` fixing `0` and `∞` attached to a unit `a` acts as the dilation
`z ↦ a * z`. -/
@[simp]
theorem pslFixingZeroInftyEquiv_symm_smul_coe (a : Kˣ) (z : K) :
    ((pslFixingZeroInftyEquiv hK).symm a : PSL(2, K)) • (z : OnePoint K) =
      ((a * z : K) : OnePoint K) := by
  rw [← coe_pslFixingZeroInftyEquiv_mul hK, MulEquiv.apply_symm_apply]

end Roots

end OnePoint
