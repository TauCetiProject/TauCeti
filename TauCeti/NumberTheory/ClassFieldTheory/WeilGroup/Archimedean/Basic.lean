/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Units
public import Mathlib.Analysis.Quaternion
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.GroupWithZero
import TauCeti.Algebra.Quaternion.ComplexSubfield
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.GroupTheory.QuotientGroup.KerEquiv
import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv
import TauCeti.Topology.Algebra.Group.Quotient.Basic
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# The archimedean Weil groups

The Weil group of `ℂ` is `W_ℂ = ℂˣ`. The Weil group of `ℝ` is the nonsplit extension
`1 → ℂˣ → W_ℝ → Gal(ℂ/ℝ) → 1` realised inside the unit group of Hamilton's quaternions `ℍ` as
`W_ℝ = ℂˣ ∪ jℂˣ`, where `ℂ ⊆ ℍ` is spanned by `1` and `i`. In `W_ℝ` we have `j² = -1` and
`j z j⁻¹ = conj z` for `z ∈ ℂˣ`. It is a topological group with the subspace topology of `ℍˣ`,
and `ℂˣ` is an open subgroup whose complement is `jℂˣ`.

The norm `W_ℝ → ℝˣ` sends `z ↦ |z|²` and `j ↦ -1`; on a quaternion `q ∈ W_ℝ` it is
`q.re² + q.imI² - q.imJ² - q.imK²`. It is a surjective continuous homomorphism whose kernel is the
commutator subgroup, so it identifies the abelianization of `W_ℝ` with `ℝˣ`, both algebraically
(`Group.Abelianization`) and as topological groups (`TopologicalAbelianization`). The extension
does not split: every element outside `ℂˣ` squares to its norm, a negative real number, so no
element outside `ℂˣ` has order two and `W_ℝ → Gal(ℂ/ℝ)` has no homomorphic section.

The archimedean Weil groups play the role for `ℝ` and `ℂ` that the Weil group `W_K` plays for a
nonarchimedean local field: the norm realizes archimedean local reciprocity `W_ℝ^{ab} ≃ₜ* ℝˣ`,
and continuous representations of `W_ℝ` and `W_ℂ` are the archimedean Langlands parameters.
Homomorphisms out of `W_ℝ` are built from a homomorphism out of `ℂˣ` and an image of `j` by
`WeilGroupReal.lift`, are determined by these data (`WeilGroupReal.hom_ext`), and are continuous
when they are continuous on `ℂˣ` (`WeilGroupReal.continuous_iff_continuous_comp_includeComplex`).

## Main definitions

* `TauCeti.ClassFieldTheory.WeilGroupComplex`: the Weil group `ℂˣ` of `ℂ`.
* `TauCeti.ClassFieldTheory.realWeilSubgroup`: the subgroup `ℂˣ ∪ jℂˣ` of `ℍˣ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal`: the Weil group of `ℝ`, the subgroup above as a type.
* `TauCeti.ClassFieldTheory.WeilGroupReal.includeComplex`: the inclusion `W_ℂ → W_ℝ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.j`: the element `j`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.lift`: the homomorphism out of `W_ℝ` given by a
  homomorphism out of `W_ℂ` and an image of `j` satisfying the relations.
* `TauCeti.ClassFieldTheory.WeilGroupReal.norm`: the norm `W_ℝ → ℝˣ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.abelianizationEquiv`: `W_ℝ^{ab} ≃* ℝˣ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.topologicalAbelianizationEquiv`: the topological
  abelianization of `W_ℝ` is `ℝˣ` as a topological group.

## Main results

* `TauCeti.ClassFieldTheory.WeilGroupReal.j_sq`,
  `TauCeti.ClassFieldTheory.WeilGroupReal.j_mul_includeComplex_mul_inv_j`: `j² = -1` and
  `j z j⁻¹ = conj z`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.exists_includeComplex_or_j_mul`,
  `TauCeti.ClassFieldTheory.WeilGroupReal.j_mul_includeComplex_notMem_range_includeComplex`:
  `W_ℝ` is the disjoint union of `ℂˣ` and `jℂˣ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.hom_ext`: homomorphisms out of `W_ℝ` are determined on
  `ℂˣ` and `j`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.isOpenEmbedding_includeComplex`,
  `TauCeti.ClassFieldTheory.WeilGroupReal.index_range_includeComplex`: `ℂˣ` is an open subgroup
  of `W_ℝ` of index two, with its own topology.
* `TauCeti.ClassFieldTheory.WeilGroupReal.continuous_iff_continuous_comp_includeComplex`: a
  homomorphism out of `W_ℝ` is continuous when it is continuous on `ℂˣ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.coe_norm_pos_iff`: the norm is positive exactly on `ℂˣ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.ker_norm`,
  `TauCeti.ClassFieldTheory.WeilGroupReal.isQuotientMap_norm`: the norm is a quotient map with
  kernel the commutator subgroup.
* `TauCeti.ClassFieldTheory.WeilGroupReal.sq_eq_norm_of_notMem_range_includeComplex`,
  `TauCeti.ClassFieldTheory.WeilGroupReal.sq_ne_one_of_notMem_range_includeComplex`: an element
  outside `ℂˣ` squares to its norm, which is negative, so it does not have order two.
* `TauCeti.ClassFieldTheory.WeilGroupReal.not_rightInverse_mk'_range_includeComplex`: the quotient
  map `W_ℝ → W_ℝ ⧸ ℂˣ` has no homomorphic section.

## References

* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1.4.3.
* A. W. Knapp, *Local Langlands correspondence: the archimedean case*, in *Motives*,
  Proc. Sympos. Pure Math. 55, Part 2 (1994), §3.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.Quaternion Topology
open scoped commutatorElement

/-- **The Weil group of `ℂ`**: the multiplicative group `ℂˣ`. -/
abbrev WeilGroupComplex : Type := ℂˣ

example : IsTopologicalGroup WeilGroupComplex := inferInstance

example : LocallyCompactSpace WeilGroupComplex := inferInstance

/-- The quaternions in `ℂˣ ∪ jℂˣ`, the subgroup of `ℍˣ` underlying the Weil group of `ℝ`. Here
`ℂ ⊆ ℍ` is spanned by `1` and `i`, and `jℂ` by `j` and `k`. -/
def realWeilSubgroup : Subgroup ℍˣ where
  carrier := {q | ((q : ℍ).imJ = 0 ∧ (q : ℍ).imK = 0) ∨ ((q : ℍ).re = 0 ∧ (q : ℍ).imI = 0)}
  mul_mem' := by
    rintro a b (⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩) (⟨hb₁, hb₂⟩ | ⟨hb₁, hb₂⟩) <;> simp [*]
  one_mem' := by simp
  inv_mem' := by
    rintro a (⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩) <;> simp [Quaternion.inv_def, *]

/-- An invertible quaternion lies in `realWeilSubgroup` exactly when it lies in `ℂ` or in `jℂ`. -/
theorem mem_realWeilSubgroup_iff {q : ℍˣ} :
    q ∈ realWeilSubgroup ↔
      ((q : ℍ).imJ = 0 ∧ (q : ℍ).imK = 0) ∨ ((q : ℍ).re = 0 ∧ (q : ℍ).imI = 0) :=
  Iff.rfl

/-- `ℂˣ ∪ jℂˣ` is closed in `ℍˣ`. -/
theorem isClosed_realWeilSubgroup : IsClosed (realWeilSubgroup : Set ℍˣ) := by
  have hc (f : ℍ → ℝ) (hf : Continuous f) : IsClosed {q : ℍˣ | f q = 0} :=
    isClosed_eq (hf.comp Units.continuous_val) continuous_const
  exact ((hc _ continuous_imJ).inter (hc _ continuous_imK)).union
    ((hc _ continuous_re).inter (hc _ continuous_imI))

/-- **The Weil group of `ℝ`**: the group `ℂˣ ∪ jℂˣ ⊆ ℍˣ`, with the subspace topology. -/
abbrev WeilGroupReal : Type := realWeilSubgroup

example : IsTopologicalGroup WeilGroupReal := inferInstance

/-- `W_ℝ` is locally compact. -/
instance instLocallyCompactSpaceWeilGroupReal : LocallyCompactSpace WeilGroupReal :=
  -- a closed subgroup of the locally compact group `ℍˣ`
  isClosed_realWeilSubgroup.locallyCompactSpace

namespace WeilGroupReal

/-- Elements of `W_ℝ` are equal when the underlying quaternions are. -/
theorem ext_iff {v w : WeilGroupReal} : v = w ↔ ((v : ℍˣ) : ℍ) = ((w : ℍˣ) : ℍ) :=
  ⟨fun h ↦ h ▸ rfl, fun h ↦ Subtype.ext (Units.ext h)⟩

/-- `W_ℝ` carries the subspace topology of `ℍ`. -/
theorem isEmbedding_coe_quaternion : IsEmbedding fun w : WeilGroupReal ↦ ((w : ℍˣ) : ℍ) :=
  Units.isEmbedding_val₀.comp IsEmbedding.subtypeVal

/-- The underlying quaternion of an element of `W_ℝ` depends continuously on it. -/
@[fun_prop]
theorem continuous_coe_quaternion : Continuous fun w : WeilGroupReal ↦ ((w : ℍˣ) : ℍ) :=
  isEmbedding_coe_quaternion.continuous

/-- **The inclusion `W_ℂ → W_ℝ`**, through `ℂ ⊆ ℍ`. -/
def includeComplex : WeilGroupComplex →* WeilGroupReal :=
  (Units.map (Quaternion.ofComplex : ℂ →* ℍ)).codRestrict realWeilSubgroup fun _ ↦ by
    simp [mem_realWeilSubgroup_iff]

/-- The inclusion `W_ℂ → W_ℝ` is `ℂ ⊆ ℍ` on underlying quaternions. -/
@[simp]
theorem coe_includeComplex (z : WeilGroupComplex) :
    ((includeComplex z : ℍˣ) : ℍ) = ((z : ℂ) : ℍ) := by
  simp [includeComplex]

/-- The element `j` of `W_ℝ`: the quaternion unit `TauCeti.Quaternion.jUnit`. -/
def j : WeilGroupReal :=
  ⟨TauCeti.Quaternion.jUnit, Or.inr (by rw [TauCeti.Quaternion.coe_jUnit]; exact ⟨rfl, rfl⟩)⟩

/-- The underlying quaternion of `j` is the quaternion unit `j`. -/
@[simp]
theorem coe_j : ((j : ℍˣ) : ℍ) = ⟨0, 0, 1, 0⟩ :=
  TauCeti.Quaternion.coe_jUnit

/-- The underlying unit of `j` is `TauCeti.Quaternion.jUnit`. -/
private theorem val_j : (j : ℍˣ) = TauCeti.Quaternion.jUnit :=
  rfl

/-- The underlying quaternion of `j⁻¹` is `-j`. -/
theorem coe_inv_j : ((j⁻¹ : WeilGroupReal) : ℍˣ) = (⟨0, 0, -1, 0⟩ : ℍ) := by
  rw [Subgroup.coe_inv, val_j]
  exact TauCeti.Quaternion.coe_inv_jUnit

/-- The inclusion `W_ℂ → W_ℝ` is injective. -/
theorem includeComplex_injective : Function.Injective includeComplex := fun z w h ↦ by
  rw [ext_iff, coe_includeComplex, coe_includeComplex] at h
  exact Units.ext (Quaternion.ofComplex.toRingHom.injective h)

/-- The inclusion `W_ℂ → W_ℝ` is injective, as an `iff`. -/
@[simp]
theorem includeComplex_inj {z w : WeilGroupComplex} : includeComplex z = includeComplex w ↔ z = w :=
  includeComplex_injective.eq_iff

/-- **`j² = -1`** in `W_ℝ`. -/
@[simp]
theorem j_sq : j ^ 2 = includeComplex (-1) := by
  rw [ext_iff, pow_two]
  ext <;> simp

/-- `j * j = -1` in `W_ℝ`. -/
@[simp]
theorem j_mul_j : j * j = includeComplex (-1) := by
  rw [← pow_two, j_sq]

/-- `j⁻¹ = -j` in `W_ℝ`. -/
theorem inv_j : j⁻¹ = j * includeComplex (-1) := by
  rw [ext_iff, coe_inv_j]
  ext <;> simp

/-- **Conjugation by `j` is complex conjugation**: `j z j⁻¹ = conj z`. -/
@[simp]
theorem j_mul_includeComplex_mul_inv_j (z : WeilGroupComplex) :
    j * includeComplex z * j⁻¹ = includeComplex (star z) := by
  rw [ext_iff]
  simpa [val_j, Complex.star_def, ← Complex.conjAe_coe] using
    (TauCeti.Quaternion.ofComplex_conjAe (z : ℂ)).symm

/-- Moving `j` past `z ∈ ℂˣ` conjugates `z`. -/
@[simp]
theorem includeComplex_mul_j (z : WeilGroupComplex) :
    includeComplex z * j = j * includeComplex (star z) := by
  conv_lhs => rw [← star_star z, ← j_mul_includeComplex_mul_inv_j]
  rw [inv_mul_cancel_right]

/-- Conjugation by `j⁻¹` is complex conjugation: `j⁻¹ z j = conj z`. -/
@[simp]
theorem inv_j_mul_includeComplex_mul_j (z : WeilGroupComplex) :
    j⁻¹ * includeComplex z * j = includeComplex (star z) := by
  rw [mul_assoc, includeComplex_mul_j, inv_mul_cancel_left]

/-- **Multiplication on `jℂˣ`**: `(j a)(j b) = -conj(a) b`. -/
@[simp]
theorem j_mul_includeComplex_mul_j_mul_includeComplex (a b : WeilGroupComplex) :
    j * includeComplex a * (j * includeComplex b) = includeComplex (-1 * star a * b) := by
  rw [map_mul, map_mul, ← j_mul_j, mul_assoc j, ← mul_assoc (includeComplex a),
    includeComplex_mul_j]
  group

/-- An element of `W_ℝ` lies in `ℂˣ` exactly when its `j`- and `k`-coordinates vanish. -/
theorem mem_range_includeComplex_iff {w : WeilGroupReal} :
    w ∈ includeComplex.range ↔ ((w : ℍˣ) : ℍ).imJ = 0 ∧ ((w : ℍˣ) : ℍ).imK = 0 := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨z, rfl⟩
    simp
  · obtain ⟨h₁, h₂⟩ := h
    refine ⟨Units.mk0 ⟨((w : ℍˣ) : ℍ).re, ((w : ℍˣ) : ℍ).imI⟩ fun h ↦ (w : ℍˣ).ne_zero ?_, ?_⟩
    · ext <;> simp_all [Complex.ext_iff]
    · rw [ext_iff]
      ext <;> simp [h₁, h₂]

/-- **`W_ℝ = ℂˣ ∪ jℂˣ`**: every element of `W_ℝ` lies in `ℂˣ` or in `jℂˣ`. -/
theorem exists_includeComplex_or_j_mul (w : WeilGroupReal) :
    (∃ z, includeComplex z = w) ∨ ∃ z, j * includeComplex z = w := by
  obtain ⟨q, (h | ⟨h₁, h₂⟩)⟩ := w
  · exact Or.inl (MonoidHom.mem_range.1 (mem_range_includeComplex_iff.2 h))
  · refine Or.inr ⟨Units.mk0 ⟨(q : ℍ).imJ, -(q : ℍ).imK⟩ fun h ↦ q.ne_zero ?_, ?_⟩
    · ext <;> simp_all [Complex.ext_iff]
    · rw [ext_iff]
      ext <;> simp [h₁, h₂]

/-- **`ℂˣ` and `jℂˣ` are disjoint**: no element of `jℂˣ` lies in `ℂˣ`. -/
theorem j_mul_includeComplex_notMem_range_includeComplex (z : WeilGroupComplex) :
    j * includeComplex z ∉ includeComplex.range := by
  rw [mem_range_includeComplex_iff]
  rintro ⟨h₁, h₂⟩
  exact z.ne_zero (Complex.ext (by simpa using h₁) (by simpa using h₂))

/-- `j` does not lie in `ℂˣ`. -/
theorem j_notMem_range_includeComplex : j ∉ includeComplex.range := by
  simpa using j_mul_includeComplex_notMem_range_includeComplex 1

/-- **Homomorphisms out of `W_ℝ` are determined on `ℂˣ` and `j`.** -/
theorem hom_ext {G : Type*} [MulOneClass G] {f g : WeilGroupReal →* G}
    (h : f.comp includeComplex = g.comp includeComplex) (hj : f j = g j) : f = g := by
  ext w
  obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := exists_includeComplex_or_j_mul w
  · exact DFunLike.congr_fun h z
  · rw [map_mul, map_mul, hj]
    exact congrArg _ (DFunLike.congr_fun h z)

section lift

variable {G : Type*} [Monoid G] (f : WeilGroupComplex →* G) (g : G)

open scoped Classical in
/-- The function underlying `WeilGroupReal.lift`: `z ↦ f z` on `ℂˣ` and `jz ↦ g * f z` on
`jℂˣ`. -/
private def liftFun (w : WeilGroupReal) : G :=
  if h : ∃ z, includeComplex z = w then f h.choose
  else g * f ((exists_includeComplex_or_j_mul w).resolve_left h).choose

private theorem liftFun_includeComplex (z : WeilGroupComplex) :
    liftFun f g (includeComplex z) = f z := by
  have h : ∃ x, includeComplex x = includeComplex z := ⟨z, rfl⟩
  rw [liftFun, dite_eq_left h, includeComplex_injective h.choose_spec]

private theorem liftFun_j_mul (z : WeilGroupComplex) :
    liftFun f g (j * includeComplex z) = g * f z := by
  have h : ¬∃ x, includeComplex x = j * includeComplex z := fun ⟨x, hx⟩ ↦
    j_mul_includeComplex_notMem_range_includeComplex z ⟨x, hx⟩
  rw [liftFun, dite_eq_right h]
  congr 2
  exact includeComplex_injective
    (mul_left_cancel ((exists_includeComplex_or_j_mul _).resolve_left h).choose_spec)

/-- **The universal property of `W_ℝ`**: a homomorphism `f : W_ℂ →* G` together with `g : G`
satisfying `g² = f (-1)` and `g (f z) = f (conj z) g` extends uniquely (`hom_ext`) to `W_ℝ`,
sending `j` to `g`. The target need only be a monoid, such as `Module.End ℂ V`. -/
def lift (hg : g ^ 2 = f (-1)) (hgf : ∀ z, g * f z = f (star z) * g) :
    WeilGroupReal →* G where
  toFun := liftFun f g
  map_one' := by rw [← map_one includeComplex, liftFun_includeComplex, map_one]
  map_mul' v w := by
    -- The commutation and square relations, associated to the right.
    have hc (z : WeilGroupComplex) (x : G) : f z * (g * x) = g * (f (star z) * x) := by
      rw [← mul_assoc, ← mul_assoc, hgf, star_star]
    have hgg (x : G) : g * (g * x) = f (-1) * x := by
      rw [← mul_assoc, ← sq, hg]
    obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ := exists_includeComplex_or_j_mul v <;>
    obtain ⟨b, rfl⟩ | ⟨b, rfl⟩ := exists_includeComplex_or_j_mul w
    -- Write each product as `z` or `j * z` with `z ∈ ℂˣ`, then evaluate both sides.
    on_goal 1 => rw [← map_mul]
    on_goal 2 => rw [← mul_assoc, includeComplex_mul_j, mul_assoc, ← map_mul]
    on_goal 3 => rw [mul_assoc, ← map_mul]
    on_goal 4 => rw [j_mul_includeComplex_mul_j_mul_includeComplex]
    all_goals simp only [liftFun_includeComplex, liftFun_j_mul, map_mul f, mul_assoc, hc, hgg]

variable {f g} {hg : g ^ 2 = f (-1)} {hgf : ∀ z, g * f z = f (star z) * g}

/-- `WeilGroupReal.lift f g` restricts to `f` on `ℂˣ`. -/
@[simp]
theorem lift_includeComplex (z : WeilGroupComplex) :
    lift f g hg hgf (includeComplex z) = f z :=
  liftFun_includeComplex f g z

/-- `WeilGroupReal.lift f g` sends `j` to `g`. -/
@[simp]
theorem lift_j : lift f g hg hgf j = g := by
  have h := liftFun_j_mul f g 1
  simp only [map_one, mul_one] at h
  exact h

/-- `WeilGroupReal.lift f g` restricts to `f` on `ℂˣ`, as homomorphisms. -/
@[simp]
theorem lift_comp_includeComplex : (lift f g hg hgf).comp includeComplex = f :=
  MonoidHom.ext fun z ↦ lift_includeComplex (hg := hg) (hgf := hgf) z

end lift

/-! ### The norm -/

/-- The quadratic form `q.re² + q.imI² - q.imJ² - q.imK²` on `W_ℝ` is nowhere zero. -/
private theorem normForm_ne_zero (w : WeilGroupReal) :
    ((w : ℍˣ) : ℍ).re ^ 2 + ((w : ℍˣ) : ℍ).imI ^ 2 - ((w : ℍˣ) : ℍ).imJ ^ 2 -
      ((w : ℍˣ) : ℍ).imK ^ 2 ≠ 0 := by
  -- On `ℂˣ ∪ jℂˣ` the form is `±|q|²`.
  obtain ⟨q, (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)⟩ := w <;>
  · have h := Quaternion.normSq_ne_zero.2 q.ne_zero
    rw [Quaternion.normSq_def'] at h
    simp only [h₁, h₂] at h ⊢
    contrapose h
    linarith

/-- **The norm `W_ℝ → ℝˣ`**, sending `z ∈ ℂˣ` to `|z|²` and `j` to `-1`. On a quaternion `q` it is
`q.re² + q.imI² - q.imJ² - q.imK²`. -/
def norm : WeilGroupReal →* ℝˣ where
  toFun w := Units.mk0 _ (normForm_ne_zero w)
  map_one' := by ext; simp
  map_mul' := by
    rintro ⟨a, (⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩)⟩ ⟨b, (⟨hb₁, hb₂⟩ | ⟨hb₁, hb₂⟩)⟩ <;>
    · ext
      simp [ha₁, ha₂, hb₁, hb₂]
      ring

/-- The norm of `q ∈ W_ℝ` is `q.re² + q.imI² - q.imJ² - q.imK²`. -/
theorem coe_norm (w : WeilGroupReal) :
    (norm w : ℝ) = ((w : ℍˣ) : ℍ).re ^ 2 + ((w : ℍˣ) : ℍ).imI ^ 2 - ((w : ℍˣ) : ℍ).imJ ^ 2 -
      ((w : ℍˣ) : ℍ).imK ^ 2 :=
  (rfl)

/-- The norm of `z ∈ ℂˣ` is `|z|²`. -/
@[simp]
theorem coe_norm_includeComplex (z : WeilGroupComplex) :
    (norm (includeComplex z) : ℝ) = Complex.normSq z := by
  simp [coe_norm, Complex.normSq_apply, sq]

/-- The norm of `j` is `-1`. -/
@[simp]
theorem norm_j : norm j = -1 := by
  ext
  simp [coe_norm]

/-- The norm is continuous. -/
@[fun_prop]
theorem continuous_norm : Continuous norm := by
  rw [Units.isEmbedding_val₀.continuous_iff]
  simp only [Function.comp_def, coe_norm]
  have h := continuous_coe_quaternion
  exact ((((continuous_re.comp h).pow 2).add ((continuous_imI.comp h).pow 2)).sub
    ((continuous_imJ.comp h).pow 2)).sub ((continuous_imK.comp h).pow 2)

/-- **The norm is negative exactly on `jℂˣ`.** -/
theorem coe_norm_neg_iff {w : WeilGroupReal} : (norm w : ℝ) < 0 ↔ w ∉ includeComplex.range := by
  obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := exists_includeComplex_or_j_mul w
  · simpa using Complex.normSq_nonneg _
  · simp only [j_mul_includeComplex_notMem_range_includeComplex, not_false_eq_true, iff_true]
    simp

/-- **The norm is positive exactly on `ℂˣ`.** -/
theorem coe_norm_pos_iff {w : WeilGroupReal} : 0 < (norm w : ℝ) ↔ w ∈ includeComplex.range := by
  rw [← not_iff_not, not_lt, ← coe_norm_neg_iff, le_iff_lt_or_eq, or_iff_left (norm w).ne_zero]

/-- `ℂˣ` is the preimage under the norm of the positive reals. -/
theorem range_includeComplex_eq_comap_norm :
    includeComplex.range = (Units.posSubgroup ℝ).comap norm := by
  ext w
  rw [Subgroup.mem_comap, Units.mem_posSubgroup, coe_norm_pos_iff]

/-- `ℂˣ` is a normal subgroup of `W_ℝ`. -/
instance instNormalRangeIncludeComplex : includeComplex.range.Normal := by
  rw [range_includeComplex_eq_comap_norm]
  infer_instance

/-- A continuous section of the norm, `r ↦ √r` for `r > 0` and `r ↦ j√(-r)` for `r < 0`, written
in coordinates as `⟨√(max r 0), 0, √(max (-r) 0), 0⟩`. -/
private def normSection (r : ℝˣ) : WeilGroupReal :=
  ⟨Units.mk0 ⟨√(max (r : ℝ) 0), 0, √(max (-r : ℝ) 0), 0⟩ fun h ↦ r.ne_zero (by
      have h₁ := congrArg QuaternionAlgebra.re h
      have h₂ := congrArg QuaternionAlgebra.imJ h
      simp only [QuaternionAlgebra.re_zero, QuaternionAlgebra.imJ_zero, Real.sqrt_eq_zero',
        max_le_iff] at h₁ h₂
      exact le_antisymm h₁.1 (by linarith [h₂.1])),
    by
      rcases lt_or_gt_of_ne r.ne_zero with h | h
      · exact Or.inr ⟨by simp [max_eq_right h.le], rfl⟩
      · exact Or.inl ⟨by simp [max_eq_right (neg_nonpos.2 h.le)], rfl⟩⟩

/-- `normSection` is a section of the norm. -/
private theorem norm_normSection (r : ℝˣ) : norm (normSection r) = r := by
  ext
  simp only [coe_norm, normSection, Units.val_mk0]
  rw [Real.sq_sqrt (le_max_right _ 0), Real.sq_sqrt (le_max_right _ 0)]
  rcases le_total (r : ℝ) 0 with h | h
  · simp [max_eq_right h, max_eq_left (neg_nonneg.2 h)]
  · simp [max_eq_left h, max_eq_right (neg_nonpos.2 h)]

/-- `normSection` is continuous. -/
private theorem continuous_normSection : Continuous normSection := by
  refine Continuous.subtype_mk ?_ _
  rw [Units.isEmbedding_val₀.continuous_iff]
  have h : (fun r : ℝˣ ↦ (⟨√(max (r : ℝ) 0), 0, √(max (-r : ℝ) 0), 0⟩ : ℍ)) = fun r : ℝˣ ↦
      ((√(max (r : ℝ) 0) : ℝ) : ℍ) + √(max (-r : ℝ) 0) • (⟨0, 0, 1, 0⟩ : ℍ) := by
    ext r <;> simp
  simp only [Function.comp_def, Units.val_mk0]
  rw [h]
  have hv : Continuous fun r : ℝˣ ↦ (r : ℝ) := Units.continuous_val
  exact (Quaternion.continuous_coe.comp (hv.max continuous_const).sqrt).add
    (((hv.neg.max continuous_const).sqrt).smul continuous_const)

/-- **The norm is a quotient map.** -/
theorem isQuotientMap_norm : IsQuotientMap norm :=
  .of_inverse continuous_normSection continuous_norm norm_normSection

/-- **The norm is surjective.** -/
theorem norm_surjective : Function.Surjective norm :=
  isQuotientMap_norm.surjective

/-- The norm is an open quotient map. -/
theorem isOpenQuotientMap_norm : IsOpenQuotientMap norm :=
  MonoidHom.isOpenQuotientMap_of_isQuotientMap isQuotientMap_norm

/-- `ℂˣ` has index two in `W_ℝ`. -/
theorem index_range_includeComplex : includeComplex.range.index = 2 := by
  rw [range_includeComplex_eq_comap_norm, Subgroup.index_comap_of_surjective _ norm_surjective,
    Units.index_posSubgroup]

/-- An element `w` of `W_ℝ` outside `ℂˣ` squares to its norm in `ℂˣ`, which is negative by
`coe_norm_neg_iff`. -/
theorem sq_eq_norm_of_notMem_range_includeComplex {w : WeilGroupReal}
    (hw : w ∉ includeComplex.range) :
    w ^ 2 = includeComplex (Units.map (algebraMap ℝ ℂ : ℝ →* ℂ) (norm w)) := by
  obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := exists_includeComplex_or_j_mul w
  · exact absurd ⟨z, rfl⟩ hw
  · rw [sq, j_mul_includeComplex_mul_j_mul_includeComplex, includeComplex_inj, map_mul, norm_j]
    ext
    simp [Complex.normSq_eq_conj_mul_self]

/-- **No element outside `ℂˣ` squares to `1`.** -/
theorem sq_ne_one_of_notMem_range_includeComplex {w : WeilGroupReal}
    (hw : w ∉ includeComplex.range) : w ^ 2 ≠ 1 := by
  rw [sq_eq_norm_of_notMem_range_includeComplex hw, ← map_one includeComplex,
    includeComplex_injective.ne_iff]
  intro h
  have : (norm w : ℝ) = 1 := by simpa using congrArg (fun u : ℂˣ ↦ (u : ℂ).re) h
  linarith [coe_norm_neg_iff.2 hw]

/-- **The extension `1 → ℂˣ → W_ℝ → W_ℝ ⧸ ℂˣ → 1` does not split**: the quotient map by `ℂˣ`
has no homomorphic section. -/
theorem not_rightInverse_mk'_range_includeComplex
    (s : WeilGroupReal ⧸ includeComplex.range →* WeilGroupReal) :
    ¬Function.RightInverse s (QuotientGroup.mk' includeComplex.range) := by
  intro hs
  -- `s` sends the class of `j`, which has order two, to an element of order two outside `ℂˣ`.
  have hj : (j : WeilGroupReal ⧸ includeComplex.range) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact j_notMem_range_includeComplex
  have hmem : s j ∉ includeComplex.range := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, hs]
    exact hj
  refine sq_ne_one_of_notMem_range_includeComplex hmem ?_
  rw [← map_pow, ← QuotientGroup.mk_pow, j_sq,
    (QuotientGroup.eq_one_iff _).2 (MonoidHom.mem_range.2 ⟨_, rfl⟩), map_one]

/-- The commutator of `j` and `z ∈ ℂˣ` is `conj z / z`. -/
theorem commutatorElement_j_includeComplex (z : WeilGroupComplex) :
    (⁅j, includeComplex z⁆ : WeilGroupReal) = includeComplex (star z * z⁻¹) := by
  rw [commutatorElement_def, j_mul_includeComplex_mul_inv_j, map_mul, map_inv]

/-- **The norm induces the abelianization**: its kernel is the commutator subgroup of `W_ℝ`. -/
theorem ker_norm : norm.ker = commutator WeilGroupReal := by
  refine le_antisymm (fun w hw ↦ ?_) (Group.Abelianization.commutator_le_ker norm)
  rw [MonoidHom.mem_ker] at hw
  -- The kernel is the unit circle in `ℂˣ`.
  obtain ⟨z, rfl⟩ := coe_norm_pos_iff.1 (by rw [hw, Units.val_one]; exact one_pos)
  obtain ⟨s, rfl, hs⟩ := Complex.exists_sq_eq_and_star_mul_self_eq_one (z := z)
    (by rw [← coe_norm_includeComplex, hw, Units.val_one])
  -- `s ^ 2 = s / conj s = ⁅j, conj s⁆`, since `conj s = s⁻¹`.
  have h : ⁅j, includeComplex (star s)⁆ = includeComplex (s ^ 2) := by
    rw [commutatorElement_j_includeComplex, star_star, eq_inv_of_mul_eq_one_left hs, inv_inv, sq]
  rw [← h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- **The abelianization of `W_ℝ` is `ℝˣ`**, through the norm. -/
def abelianizationEquiv : Group.Abelianization WeilGroupReal ≃* ℝˣ :=
  -- `W_ℝ^{ab} ≃* W_ℝ ⧸ ker of = W_ℝ ⧸ ker norm ≃* ℝˣ`
  let e := QuotientGroup.quotientKerEquivOfSurjective _ (Group.Abelianization.surjective_of _)
  e.symm.trans <|
    (QuotientGroup.quotientMulEquivOfEq ((Group.Abelianization.ker_of _).trans ker_norm.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective norm norm_surjective)

/-- `abelianizationEquiv` sends the class of `w` to its norm. -/
@[simp]
theorem abelianizationEquiv_of (w : WeilGroupReal) :
    abelianizationEquiv (Group.Abelianization.of w) = norm w := by
  simp [abelianizationEquiv]

/-- The inverse of `abelianizationEquiv` sends the norm of `w` to the class of `w`. -/
@[simp]
theorem abelianizationEquiv_symm_norm (w : WeilGroupReal) :
    abelianizationEquiv.symm (norm w) = Group.Abelianization.of w := by
  rw [MulEquiv.symm_apply_eq, abelianizationEquiv_of]

/-- The commutator subgroup of `W_ℝ` is closed. -/
theorem isClosed_commutator : IsClosed (commutator WeilGroupReal : Set WeilGroupReal) := by
  rw [← ker_norm, MonoidHom.coe_ker]
  exact isClosed_singleton.preimage continuous_norm

/-- **The topological abelianization of `W_ℝ` is `ℝˣ`**, through the norm. -/
def topologicalAbelianizationEquiv : TopologicalAbelianization WeilGroupReal ≃ₜ* ℝˣ :=
  (Subgroup.quotientContinuousMulEquivOfEq
      (isClosed_commutator.subgroup_topologicalClosure_eq.trans ker_norm.symm)).trans
    (ContinuousMulEquiv.quotientKerEquivOfSurjective norm isQuotientMap_norm.isStrictMap
      norm_surjective)

/-- `topologicalAbelianizationEquiv` sends the class of `w` to its norm. -/
@[simp]
theorem topologicalAbelianizationEquiv_mk (w : WeilGroupReal) :
    topologicalAbelianizationEquiv (w : TopologicalAbelianization WeilGroupReal) = norm w := by
  simp [topologicalAbelianizationEquiv]

/-- The inverse of `topologicalAbelianizationEquiv` sends the norm of `w` to the class of
`w`. -/
@[simp]
theorem topologicalAbelianizationEquiv_symm_norm (w : WeilGroupReal) :
    topologicalAbelianizationEquiv.symm (norm w) =
      (w : TopologicalAbelianization WeilGroupReal) := by
  rw [ContinuousMulEquiv.symm_apply_eq, topologicalAbelianizationEquiv_mk]

/-! ### Topology -/

/-- **`ℂˣ` is an open subgroup of `W_ℝ`.** -/
theorem isOpen_range_includeComplex : IsOpen (includeComplex.range : Set WeilGroupReal) := by
  -- `ℂˣ` is where the norm is positive.
  have h : (includeComplex.range : Set WeilGroupReal) =
      (fun w ↦ (norm w : ℝ)) ⁻¹' Set.Ioi 0 := by
    ext w
    exact coe_norm_pos_iff.symm
  rw [h]
  exact isOpen_Ioi.preimage (Units.continuous_val.comp continuous_norm)

/-- **`ℂˣ` is an open subgroup of `W_ℝ`, with its own topology**: the inclusion is an open
embedding. -/
theorem isOpenEmbedding_includeComplex : IsOpenEmbedding includeComplex := by
  refine ⟨⟨?_, includeComplex_injective⟩, isOpen_range_includeComplex⟩
  rw [← isEmbedding_coe_quaternion.isInducing.of_comp_iff]
  have hcomp : (fun w : WeilGroupReal ↦ ((w : ℍˣ) : ℍ)) ∘ includeComplex =
      Quaternion.ofComplex.toLinearMap ∘ ((↑) : ℂˣ → ℂ) := by
    ext z <;> simp
  rw [hcomp]
  exact ((LinearMap.isClosedEmbedding_of_injective (f := Quaternion.ofComplex.toLinearMap)
    (LinearMap.ker_eq_bot_of_injective Quaternion.ofComplex.toRingHom.injective)).isEmbedding.comp
    Units.isEmbedding_val₀).isInducing

/-- The inclusion `W_ℂ → W_ℝ` is continuous. -/
@[fun_prop]
theorem continuous_includeComplex : Continuous includeComplex :=
  isOpenEmbedding_includeComplex.continuous

/-- **A homomorphism out of `W_ℝ` is continuous exactly when it is continuous on `ℂˣ`.** -/
theorem continuous_iff_continuous_comp_includeComplex {G : Type*} [MulOneClass G]
    [TopologicalSpace G] [ContinuousMul G] (φ : WeilGroupReal →* G) :
    Continuous φ ↔ Continuous (φ.comp includeComplex) := by
  refine ⟨fun h ↦ h.comp continuous_includeComplex, fun h ↦ continuous_of_continuousAt_one φ ?_⟩
  rw [← map_one includeComplex, ← isOpenEmbedding_includeComplex.continuousAt_iff]
  exact h.continuousAt

end WeilGroupReal

end TauCeti.ClassFieldTheory
