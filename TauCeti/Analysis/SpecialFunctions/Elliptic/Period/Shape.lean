/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Modular
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair

/-!
# Shapes and conformal classes of marked lattices in `ℂ`

A **marked lattice** in `ℂ` is a period pair `L = (ω₁, ω₂)` (`PeriodPair`): two `ℝ`-linearly
independent complex numbers, which form a `ℤ`-basis of their lattice `ℤ ω₁ + ℤ ω₂`. Its
**shape** is the raw ratio `L.shape = ω₁ / ω₂`, first period over second, a complex number off the
real line.
For the peripheral lattice of a cusp of a hyperbolic `3`-manifold marked by a meridian and a
longitude, this is the homological shape `meridian / longitude` of Adams, Hildebrand and Weeks;
for a basis of shortest translations it is their geometrical shape.

The shape is invariant under complex rescaling, `(c • L).shape = L.shape`, and two marked
lattices have the same shape exactly when one is a rescaling of the other
(`PeriodPair.shape_eq_shape_iff`). A change of marking is the action of `GL(2, ℤ)` on period
pairs, `g • (ω₁, ω₂) = (g₀₀ ω₁ + g₀₁ ω₂, g₁₀ ω₁ + g₁₁ ω₂)`, which keeps the lattice
(`PeriodPair.lattice_glSMul`), and any two markings of the same lattice differ by it
(`PeriodPair.lattice_eq_lattice_iff`). On shapes it acts by Möbius transformations,
`(g • L).shape = (g₀₀ τ + g₀₁) / (g₁₀ τ + g₁₁)` with nonvanishing denominator, which is the action
of the image of `g` in `GL(2, ℂ)` on the projective line `OnePoint ℂ`
(`PeriodPair.coe_shape_glSMul`). Since `-1` acts trivially there, this is an action of
`PGL(2, ℤ)`.

The **conformal class** `L.conformalClass` is the set of shapes of all markings of the lattice of
`L`, the `PGL(2, ℤ)`-orbit of `L.shape` in `ℂ ∖ ℝ`. It depends only on the lattice
(`PeriodPair.conformalClass_glSMul`) and only on its class under complex rescaling
(`PeriodPair.conformalClass_smul`), and it is a complete invariant: two lattices have the same
conformal class exactly when one is a complex multiple of the other
(`PeriodPair.conformalClass_eq_conformalClass_iff`). The class contains with every shape its
negative and its reciprocal, the shapes of `(-ω₁, ω₂)` and of the swapped pair `(ω₂, ω₁)`.

Complex conjugation of the periods (`PeriodPair.conjugate`) conjugates shapes and conformal classes.
The **unoriented** class of `L` is the union of the conformal classes of `L` and of its conjugate.
For a point `z` of the upper half-plane and its marked lattice `(z, 1)`
(`UpperHalfPlane.periodPair`), the points of `ℍ` in the conformal class of `(z, 1)` form the
`SL(2, ℤ)`-orbit of `z` (`UpperHalfPlane.exists_smul_eq_iff_mem_conformalClass`), and those in the
unoriented class form the `GL(2, ℤ)`-orbit of `z` for Mathlib's action on `ℍ`, in which matrices of
determinant `-1` act by a Möbius transformation followed by conjugation
(`UpperHalfPlane.exists_map_smul_eq_iff_mem_union_conformalClass`). The two classes differ in
general: for a point `z` of the open standard fundamental domain off the imaginary axis, such as
`1/3 + 2i`, the conjugate `conj z` is not in the conformal class of `(z, 1)`, so the lattice
`ℤ z + ℤ` is not a complex multiple of its mirror image `ℤ (conj z) + ℤ`
(`UpperHalfPlane.conj_notMem_conformalClass_of_mem_fdo`).

## Main definitions

* `PeriodPair.shape`: the ratio `ω₁ / ω₂` of a marked lattice.
* `PeriodPair.instMulActionGL`: the change-of-marking action of `GL(2, ℤ)` on period pairs.
* `PeriodPair.conformalClass`: the set of shapes of all markings of the lattice.
* `PeriodPair.conjugate`: the complex conjugate of a period pair.

## Main results

* `PeriodPair.shape_eq_shape_iff`: equal shapes means equal up to complex rescaling.
* `PeriodPair.shape_glSMul`, `PeriodPair.coe_shape_glSMul`: change of marking acts on shapes by
  Möbius transformations.
* `PeriodPair.lattice_eq_lattice_iff`: two markings of the same lattice differ by `GL(2, ℤ)`.
* `PeriodPair.mem_conformalClass_iff_exists_map_smul`: the conformal class is the
  `GL(2, ℤ)`-orbit of the shape on the projective line.
* `PeriodPair.conformalClass_eq_conformalClass_iff`: the conformal class classifies lattices up
  to complex-linear similarity.
* `UpperHalfPlane.exists_smul_eq_iff_mem_conformalClass`,
  `UpperHalfPlane.exists_map_smul_eq_iff_mem_union_conformalClass`: comparison of the conformal
  and unoriented classes with the `SL(2, ℤ)`- and `GL(2, ℤ)`-orbits in the upper half-plane.
* `UpperHalfPlane.conj_notMem_conformalClass_of_mem_fdo`: conjugation changes the conformal class
  of `ℤ z + ℤ` for `z` in the open fundamental domain off the imaginary axis.

## References

* C. C. Adams, M. Hildebrand, J. R. Weeks, *Hyperbolic invariants of knots and links*,
  Trans. Amer. Math. Soc. 326 (1991), §2, for cusp shapes.
* J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
  §VII.2.2, for lattices up to homothety and the action of the modular group.
-/

public section

noncomputable section

open Complex Matrix UpperHalfPlane
open scoped MatrixGroups ComplexConjugate Modular

namespace PeriodPair

variable (L : PeriodPair)

/-! ### The shape of a marked lattice -/

/-- The **shape** of a marked lattice `(ω₁, ω₂)`: the ratio `ω₁ / ω₂` of its periods, first over
second. For a cusp marked by meridian and longitude it is the shape `meridian / longitude`. -/
def shape : ℂ := L.ω₁ / L.ω₂

lemma shape_def : L.shape = L.ω₁ / L.ω₂ := (rfl)

/-- The shape of a marked lattice is not real. -/
lemma im_shape_ne_zero : L.shape.im ≠ 0 := L.im_ω₁_div_ω₂_ne_zero

lemma shape_mul_ω₂ : L.shape * L.ω₂ = L.ω₁ := div_mul_cancel₀ _ L.ω₂_ne_zero

/-- The shape is invariant under complex rescaling. -/
@[simp]
lemma shape_smul (c : ℂˣ) : (c • L).shape = L.shape := by
  simp [shape_def, mul_div_mul_left _ _ c.ne_zero]

/-- Two marked lattices have the same shape exactly when one is a complex multiple of the other. -/
theorem shape_eq_shape_iff {L L' : PeriodPair} : L'.shape = L.shape ↔ ∃ c : ℂˣ, L' = c • L := by
  refine ⟨fun h ↦ ⟨Units.mk0 (L'.ω₂ / L.ω₂) (div_ne_zero L'.ω₂_ne_zero L.ω₂_ne_zero), ?_⟩,
    fun ⟨c, hc⟩ ↦ hc ▸ L.shape_smul c⟩
  ext
  · rw [smul_ω₁, Units.val_mk0, div_mul_comm, ← shape_def, ← h, shape_mul_ω₂]
  · rw [smul_ω₂, Units.val_mk0, div_mul_cancel₀ _ L.ω₂_ne_zero]

/-! ### Change of marking -/

/-- A change of marking: `g • (ω₁, ω₂) = (g₀₀ ω₁ + g₀₁ ω₂, g₁₀ ω₁ + g₁₁ ω₂)` for `g ∈ GL(2, ℤ)`. It
keeps the lattice (`PeriodPair.lattice_glSMul`). -/
instance instSMulGL : SMul (GL (Fin 2) ℤ) PeriodPair where
  smul g L :=
    { ω₁ := g 0 0 * L.ω₁ + g 0 1 * L.ω₂
      ω₂ := g 1 0 * L.ω₁ + g 1 1 * L.ω₂
      indep := by
        refine LinearIndependent.pair_iff.mpr fun s t hst ↦ ?_
        simp only [Complex.real_smul] at hst
        obtain ⟨h₁, h₂⟩ := LinearIndependent.pair_iff.mp L.indep
          (s * g 0 0 + t * g 1 0) (s * g 0 1 + t * g 1 1) (by
            simp only [Complex.real_smul]
            push_cast
            linear_combination hst)
        -- The determinant of `g` is a unit of `ℤ`, so it is nonzero in `ℝ`.
        have hdet : (g 0 0 * g 1 1 - g 0 1 * g 1 0 : ℝ) ≠ 0 := by
          have h : (g : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
            rw [← GeneralLinearGroup.val_det_apply]
            exact g.det.ne_zero
          rw [det_fin_two] at h
          exact_mod_cast h
        constructor
        · refine (mul_eq_zero.mp ?_).resolve_right hdet
          linear_combination (g 1 1 : ℝ) * h₁ - (g 1 0 : ℝ) * h₂
        · refine (mul_eq_zero.mp ?_).resolve_right hdet
          linear_combination (g 0 0 : ℝ) * h₂ - (g 0 1 : ℝ) * h₁ }

variable (g : GL (Fin 2) ℤ)

@[simp]
lemma glSMul_ω₁ : (g • L).ω₁ = g 0 0 * L.ω₁ + g 0 1 * L.ω₂ := rfl

@[simp]
lemma glSMul_ω₂ : (g • L).ω₂ = g 1 0 * L.ω₁ + g 1 1 * L.ω₂ := rfl

/-- The change-of-marking action of `GL(2, ℤ)` on period pairs. -/
instance instMulActionGL : MulAction (GL (Fin 2) ℤ) PeriodPair where
  one_smul L := by ext <;> simp
  mul_smul g h L := by
    ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Changing the marking commutes with complex rescaling. -/
instance : SMulCommClass ℂˣ (GL (Fin 2) ℤ) PeriodPair where
  smul_comm c g L := by ext <;> simp <;> ring

/-- Changing the marking keeps the lattice. -/
@[simp]
theorem lattice_glSMul : (g • L).lattice = L.lattice := by
  have key (g : GL (Fin 2) ℤ) (L : PeriodPair) : (g • L).lattice ≤ L.lattice := by
    refine Submodule.span_le.mpr ?_
    rintro x (rfl | rfl) <;> exact mem_lattice.mpr ⟨_, _, rfl⟩
  refine le_antisymm (key g L) ?_
  calc L.lattice = (g⁻¹ • g • L).lattice := by rw [inv_smul_smul]
    _ ≤ (g • L).lattice := key _ _

/-- The denominator `g₁₀ τ + g₁₁` of the Möbius transformation of the shape `τ` does not vanish. -/
lemma intCast_mul_shape_add_intCast_ne_zero :
    (g 1 0 : ℂ) * L.shape + g 1 1 ≠ 0 := by
  have h : ((g 1 0 : ℂ) * L.shape + g 1 1) * L.ω₂ = (g • L).ω₂ := by
    rw [glSMul_ω₂, ← L.shape_mul_ω₂]
    ring
  exact fun h0 ↦ (g • L).ω₂_ne_zero (by rw [← h, h0, zero_mul])

/-- A change of marking acts on shapes by the Möbius transformation of its matrix. -/
theorem shape_glSMul :
    (g • L).shape = (g 0 0 * L.shape + g 0 1) / (g 1 0 * L.shape + g 1 1) := by
  have h₁ : (g 0 0 : ℂ) * (L.shape * L.ω₂) + g 0 1 * L.ω₂ = (g 0 0 * L.shape + g 0 1) * L.ω₂ := by
    ring
  have h₂ : (g 1 0 : ℂ) * (L.shape * L.ω₂) + g 1 1 * L.ω₂ = (g 1 0 * L.shape + g 1 1) * L.ω₂ := by
    ring
  rw [shape_def, glSMul_ω₁, glSMul_ω₂, ← L.shape_mul_ω₂, h₁, h₂,
    mul_div_mul_right _ _ L.ω₂_ne_zero]

/-- A change of marking acts on shapes as its image in `GL(2, ℂ)` acts on the projective line
`OnePoint ℂ`. Since `-1` acts trivially there, this is an action of `PGL(2, ℤ)`. -/
theorem coe_shape_glSMul :
    ((g • L).shape : OnePoint ℂ) = g.map (Int.castRingHom ℂ) • (L.shape : OnePoint ℂ) := by
  rw [OnePoint.smul_some_eq_ite]
  simp only [GeneralLinearGroup.map_apply, eq_intCast]
  rw [ite_eq_right (L.intCast_mul_shape_add_intCast_ne_zero g), shape_glSMul]

/-- **Two markings of the same lattice differ by a change of marking.** -/
theorem lattice_eq_lattice_iff {L L' : PeriodPair} :
    L'.lattice = L.lattice ↔ ∃ g : GL (Fin 2) ℤ, L' = g • L := by
  refine ⟨fun h ↦ ?_, fun ⟨g, hg⟩ ↦ hg ▸ L.lattice_glSMul g⟩
  -- Write the periods of each pair in terms of the other pair.
  obtain ⟨a, b, hab⟩ := mem_lattice.mp (h ▸ L'.ω₁_mem_lattice)
  obtain ⟨c, d, hcd⟩ := mem_lattice.mp (h ▸ L'.ω₂_mem_lattice)
  obtain ⟨e, f, hef⟩ := mem_lattice.mp (h.symm ▸ L.ω₁_mem_lattice)
  obtain ⟨p, q, hpq⟩ := mem_lattice.mp (h.symm ▸ L.ω₂_mem_lattice)
  -- The two integer matrices are mutually inverse, by independence of `ω₁` and `ω₂`.
  obtain ⟨h₁, h₂⟩ := (L.intCast_mul_add_intCast_mul_eq_zero_iff
    (m := e * a + f * c - 1) (n := e * b + f * d)).mp (by
      push_cast; linear_combination e * hab + f * hcd + hef)
  obtain ⟨h₃, h₄⟩ := (L.intCast_mul_add_intCast_mul_eq_zero_iff
    (m := p * a + q * c) (n := p * b + q * d - 1)).mp (by
      push_cast; linear_combination p * hab + q * hcd + hpq)
  have hinv : !![e, f; p, q] * !![a, b; c, d] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  let g : GL (Fin 2) ℤ := ⟨!![a, b; c, d], !![e, f; p, q], mul_eq_one_comm.mp hinv, hinv⟩
  exact ⟨g, PeriodPair.ext (by simpa [g] using hab.symm) (by simpa [g] using hcd.symm)⟩

/-! ### The conformal class -/

/-- The **conformal class** of a marked lattice: the set of shapes of all its changes of marking,
equivalently of all markings of its lattice
(`PeriodPair.mem_conformalClass_iff_exists_lattice_eq`). It is the `PGL(2, ℤ)`-orbit of the shape
in `ℂ ∖ ℝ` (`PeriodPair.mem_conformalClass_iff_exists_map_smul`), and classifies lattices up to
complex-linear similarity (`PeriodPair.conformalClass_eq_conformalClass_iff`). -/
def conformalClass : Set ℂ := Set.range fun g : GL (Fin 2) ℤ ↦ (g • L).shape

lemma conformalClass_def : L.conformalClass = Set.range fun g : GL (Fin 2) ℤ ↦ (g • L).shape :=
  (rfl)

lemma mem_conformalClass {τ : ℂ} : τ ∈ L.conformalClass ↔ ∃ g : GL (Fin 2) ℤ, (g • L).shape = τ :=
  Iff.rfl

@[simp]
lemma glSMul_shape_mem_conformalClass : (g • L).shape ∈ L.conformalClass := ⟨g, rfl⟩

@[simp]
lemma shape_mem_conformalClass : L.shape ∈ L.conformalClass :=
  ⟨1, congrArg shape (one_smul _ L)⟩

/-- The conformal class consists of the shapes of the markings of the lattice. -/
theorem mem_conformalClass_iff_exists_lattice_eq {τ : ℂ} :
    τ ∈ L.conformalClass ↔ ∃ L' : PeriodPair, L'.lattice = L.lattice ∧ L'.shape = τ := by
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨g • L, L.lattice_glSMul g, hg⟩, fun ⟨L', hL', hτ⟩ ↦ ?_⟩
  obtain ⟨g, rfl⟩ := lattice_eq_lattice_iff.mp hL'
  exact ⟨g, hτ⟩

/-- The conformal class is the orbit of the shape under `GL(2, ℤ)` acting on the projective line
by Möbius transformations. -/
theorem mem_conformalClass_iff_exists_map_smul {τ : ℂ} :
    τ ∈ L.conformalClass ↔ ∃ g : GL (Fin 2) ℤ,
      (τ : OnePoint ℂ) = g.map (Int.castRingHom ℂ) • (L.shape : OnePoint ℂ) := by
  simp only [conformalClass_def, Set.mem_range, ← coe_shape_glSMul, OnePoint.coe_eq_coe, eq_comm]

/-- The conformal class lies off the real line. -/
lemma im_ne_zero_of_mem_conformalClass {τ : ℂ} (hτ : τ ∈ L.conformalClass) : τ.im ≠ 0 := by
  obtain ⟨g, rfl⟩ := hτ
  exact (g • L).im_shape_ne_zero

/-- The conformal class does not depend on the marking. -/
@[simp]
theorem conformalClass_glSMul : (g • L).conformalClass = L.conformalClass := by
  ext τ
  simp only [mem_conformalClass_iff_exists_lattice_eq, lattice_glSMul]

/-- The conformal class is invariant under complex rescaling. -/
@[simp]
theorem conformalClass_smul (c : ℂˣ) : (c • L).conformalClass = L.conformalClass := by
  ext τ
  simp only [mem_conformalClass]
  exact exists_congr fun g ↦ by rw [← smul_comm c g L, shape_smul]

/-- The shape of `L'` lies in the conformal class of `L` exactly when the two conformal classes
agree. -/
theorem shape_mem_conformalClass_iff {L L' : PeriodPair} :
    L'.shape ∈ L.conformalClass ↔ L'.conformalClass = L.conformalClass := by
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun h ↦ h ▸ L'.shape_mem_conformalClass⟩
  obtain ⟨c, rfl⟩ := shape_eq_shape_iff.mp hg.symm
  rw [conformalClass_smul, conformalClass_glSMul]

/-- **The conformal class classifies lattices up to similarity**: two marked lattices have the
same conformal class exactly when the lattice of one is a complex multiple of that of the other. -/
theorem conformalClass_eq_conformalClass_iff {L L' : PeriodPair} :
    L'.conformalClass = L.conformalClass ↔ ∃ c : ℂˣ, L'.lattice = (c • L).lattice := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc⟩ ↦ ?_⟩
  · obtain ⟨g, hg⟩ := shape_mem_conformalClass_iff.mpr h
    obtain ⟨c, rfl⟩ := shape_eq_shape_iff.mp hg.symm
    exact ⟨c, by rw [smul_comm, lattice_glSMul]⟩
  · obtain ⟨g, rfl⟩ := lattice_eq_lattice_iff.mp hc
    rw [conformalClass_glSMul, conformalClass_smul]

/-- The conformal class is closed under negation: `-τ` is the shape of `(-ω₁, ω₂)`. -/
lemma neg_mem_conformalClass {τ : ℂ} (hτ : τ ∈ L.conformalClass) : -τ ∈ L.conformalClass := by
  obtain ⟨g, rfl⟩ := hτ
  let r : GL (Fin 2) ℤ := ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by simp [one_fin_two],
    by simp [one_fin_two]⟩
  refine ⟨r * g, ?_⟩
  simp only [mul_smul, shape_def, glSMul_ω₁, glSMul_ω₂, r]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  push_cast
  ring

/-- The conformal class is closed under inversion: `τ⁻¹` is the shape of the swapped pair
`(ω₂, ω₁)`. -/
lemma inv_mem_conformalClass {τ : ℂ} (hτ : τ ∈ L.conformalClass) : τ⁻¹ ∈ L.conformalClass := by
  obtain ⟨g, rfl⟩ := hτ
  let s : GL (Fin 2) ℤ := ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [one_fin_two],
    by simp [one_fin_two]⟩
  refine ⟨s * g, ?_⟩
  simp only [mul_smul, shape_def, glSMul_ω₁, glSMul_ω₂, s]
  simp

/-! ### Complex conjugation -/

/-- The **complex conjugate** `(conj ω₁, conj ω₂)` of a period pair, a marking of the mirror image
of the lattice (`PeriodPair.mem_lattice_conjugate_iff`). -/
def conjugate : PeriodPair where
  ω₁ := conj L.ω₁
  ω₂ := conj L.ω₂
  indep := by
    convert L.indep.map' Complex.conjLIE.toLinearEquiv.toLinearMap
      (LinearEquiv.ker Complex.conjLIE.toLinearEquiv) using 1
    ext i
    fin_cases i <;> rfl

@[simp]
lemma conjugate_ω₁ : L.conjugate.ω₁ = conj L.ω₁ := (rfl)

@[simp]
lemma conjugate_ω₂ : L.conjugate.ω₂ = conj L.ω₂ := (rfl)

@[simp]
lemma conjugate_conjugate : L.conjugate.conjugate = L := by
  ext <;> simp

@[simp]
lemma shape_conjugate : L.conjugate.shape = conj L.shape := by
  simp [shape_def]

/-- The lattice of the conjugate pair is the mirror image of the lattice. -/
lemma mem_lattice_conjugate_iff {x : ℂ} : x ∈ L.conjugate.lattice ↔ conj x ∈ L.lattice := by
  simp only [mem_lattice, conjugate_ω₁, conjugate_ω₂]
  refine exists₂_congr fun m n ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]
    simp
  · rw [← conj_conj x, ← h]
    simp

@[simp]
lemma conjugate_glSMul : (g • L).conjugate = g • L.conjugate := by
  ext <;> simp

/-- The conformal class of the conjugate pair is the conjugate of the conformal class. -/
theorem mem_conformalClass_conjugate_iff {τ : ℂ} :
    τ ∈ L.conjugate.conformalClass ↔ conj τ ∈ L.conformalClass := by
  simp only [mem_conformalClass, ← conjugate_glSMul, shape_conjugate]
  exact exists_congr fun g ↦ ⟨fun h ↦ by rw [← h, conj_conj], fun h ↦ by rw [h, conj_conj]⟩

end PeriodPair

/-! ### Comparison with the upper half-plane -/

namespace UpperHalfPlane

open PeriodPair

variable (g : GL (Fin 2) ℤ) (z : ℍ)

@[simp]
lemma shape_periodPair : z.periodPair.shape = z := by
  simp [shape_def]

/-- The shape of the marking `g • (z, 1)` is the Möbius transformation `num g z / denom g z` of
`z` by the image of `g` in `GL(2, ℝ)`. -/
lemma shape_glSMul_periodPair :
    (g • z.periodPair).shape =
      num (g.map (Int.castRingHom ℝ)) z / denom (g.map (Int.castRingHom ℝ)) z := by
  simp [shape_glSMul, num, denom, GeneralLinearGroup.map_apply]

/-- The determinant of the image of `g ∈ GL(2, ℤ)` in `GL(2, ℝ)`. -/
private lemma val_det_map (g : GL (Fin 2) ℤ) :
    (g.map (Int.castRingHom ℝ)).det.val = ((g 0 0 * g 1 1 - g 0 1 * g 1 0 : ℤ) : ℝ) := by
  rw [GeneralLinearGroup.val_det_apply, det_fin_two]
  simp [GeneralLinearGroup.map_apply]

/-- The shape of `g • (z, 1)` lies in the upper half-plane exactly when `g` has determinant `1`. -/
private lemma im_shape_glSMul_periodPair_pos_iff :
    0 < (g • z.periodPair).shape.im ↔ 0 < g 0 0 * g 1 1 - g 0 1 * g 1 0 := by
  rw [shape_glSMul_periodPair, moebius_im, val_det_map]
  have hn := normSq_denom_pos (g.map (Int.castRingHom ℝ)) z.im_ne_zero
  have hz : 0 < (z : ℂ).im := z.im_pos
  rw [div_pos_iff_of_pos_right hn, mul_pos_iff_of_pos_right hz]
  exact_mod_cast Iff.rfl

/-- Mathlib's action of the image of `g ∈ GL(2, ℤ)` on the upper half-plane sends `z` to the shape
of `g • (z, 1)` if `g` has determinant `1`, and to its conjugate otherwise. -/
private lemma coe_map_smul :
    ((g.map (Int.castRingHom ℝ) • z : ℍ) : ℂ) =
      if 0 < g 0 0 * g 1 1 - g 0 1 * g 1 0 then (g • z.periodPair).shape
      else conj (g • z.periodPair).shape := by
  rw [coe_smul, shape_glSMul_periodPair, σ, val_det_map]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (by exact_mod_cast h₁) h₂
  · exact absurd (by exact_mod_cast h₂) h₁
  · rfl

/-- **The conformal class in the upper half-plane is the `SL(2, ℤ)`-orbit**: a point `w` of `ℍ` is
in the conformal class of `(z, 1)` exactly when `w = γ • z` for some `γ ∈ SL(2, ℤ)`. -/
theorem exists_smul_eq_iff_mem_conformalClass {w : ℍ} :
    (∃ γ : SL(2, ℤ), γ • z = w) ↔ (w : ℂ) ∈ z.periodPair.conformalClass := by
  rw [← shape_periodPair w, shape_mem_conformalClass_iff, conformalClass_eq_conformalClass_iff]
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨_, lattice_periodPair_smul γ z⟩
  · rintro ⟨c, hc⟩
    obtain ⟨γ, hγ, -⟩ := exists_smul_eq_and_denom_eq_of_lattice_periodPair_eq hc
    exact ⟨γ⁻¹, by rw [← hγ, inv_smul_smul]⟩

/-- **The unoriented class in the upper half-plane is the `GL(2, ℤ)`-orbit**: a point `w` of `ℍ`
is in the conformal class of `(z, 1)` or of its conjugate `(conj z, 1)` exactly when `w = g • z` for
some `g ∈ GL(2, ℤ)` acting through `GL(2, ℝ)`, matrices of determinant `-1` acting by a Möbius
transformation followed by conjugation. -/
theorem exists_map_smul_eq_iff_mem_union_conformalClass {w : ℍ} :
    (∃ g : GL (Fin 2) ℤ, g.map (Int.castRingHom ℝ) • z = w) ↔
      (w : ℂ) ∈ z.periodPair.conformalClass ∪ z.periodPair.conjugate.conformalClass := by
  rw [Set.mem_union, mem_conformalClass_conjugate_iff, mem_conformalClass, mem_conformalClass]
  constructor
  · rintro ⟨g, rfl⟩
    rw [coe_map_smul]
    split_ifs
    · exact Or.inl ⟨g, rfl⟩
    · exact Or.inr ⟨g, by rw [conj_conj]⟩
  · rintro (⟨g, hg⟩ | ⟨g, hg⟩)
    · refine ⟨g, UpperHalfPlane.ext ?_⟩
      rw [coe_map_smul,
        ite_eq_left ((im_shape_glSMul_periodPair_pos_iff g z).mp (hg ▸ w.im_pos)), hg]
    · have hneg : ¬ 0 < (g • z.periodPair).shape.im := by
        rw [hg, conj_im]
        exact not_lt.mpr (neg_nonpos.mpr w.im_pos.le)
      refine ⟨g, UpperHalfPlane.ext ?_⟩
      rw [coe_map_smul, ite_eq_right ((im_shape_glSMul_periodPair_pos_iff g z).not.mp hneg), hg,
        conj_conj]

/-- **Conjugation changes the conformal class.** For `z` in the open standard fundamental domain
`𝒟ᵒ` off the imaginary axis, such as `1/3 + 2i`, the conjugate `conj z` is not in the conformal
class of `(z, 1)`: the lattice `ℤ z + ℤ` is not a complex multiple of its mirror image
`ℤ (conj z) + ℤ`, so the oriented and unoriented classes differ. -/
theorem conj_notMem_conformalClass_of_mem_fdo (hz : z ∈ 𝒟ᵒ) (hre : z.re ≠ 0) :
    conj (z : ℂ) ∉ z.periodPair.conformalClass := by
  intro h
  -- The reflection `w = -conj z` of `z` in the imaginary axis is in the class and in `ℍ`.
  let w : ℍ := mk (-conj (z : ℂ)) (by simpa using z.im_pos)
  have hwc : (w : ℂ) = -conj (z : ℂ) := coe_mk _ _
  obtain ⟨γ, hγ⟩ := (exists_smul_eq_iff_mem_conformalClass z (w := w)).mpr
    (hwc ▸ z.periodPair.neg_mem_conformalClass h)
  -- `w` is in `𝒟ᵒ` as well, so `γ • z = z`, forcing `Re z = -Re z`.
  have hw : w ∈ 𝒟ᵒ := by
    obtain ⟨h₁, h₂⟩ := hz
    refine ⟨?_, ?_⟩
    · rwa [hwc, normSq_neg, normSq_conj]
    · rwa [← coe_re, hwc, neg_re, conj_re, abs_neg, coe_re]
  have hzw : z = w := (ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo hz (hγ ▸ hw)).trans hγ
  have hre' : (z : ℂ).re = -(z : ℂ).re := by
    conv_lhs => rw [hzw]
    rw [hwc, neg_re, conj_re]
  exact hre (by rw [← coe_re]; linarith)

end UpperHalfPlane
