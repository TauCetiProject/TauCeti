/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.Basic

/-!
# Bounded archimedean parameters

An `n`-dimensional parameter of a group `G`, such as the Weil groups `W_ℂ = ℂˣ` and
`W_ℝ = ℂˣ ⊔ jℂˣ`, is a homomorphism `r : G → GL_n(ℂ)`. It is **bounded**
(`TauCeti.ClassFieldTheory.IsBoundedParameter`) when its image is relatively compact in
`GL_n(ℂ)`. For a parameter of `GL_n(ℝ)` or `GL_n(ℂ)`, boundedness is the Weil-group counterpart of
temperedness. Boundedness asks for a relatively compact image, not merely for bounded eigenvalues
of the individual matrices: the parameter `w ↦ [[1, log |norm w|], [0, 1]]` of `W_ℝ` has every
eigenvalue equal to `1` and is not bounded
(`TauCeti.ClassFieldTheory.WeilGroupReal.not_isBoundedParameter_logNormUnipotent`).

Since `ℂˣ` has index two in `W_ℝ`, a parameter of `W_ℝ` is bounded exactly when its restriction
to `W_ℂ` is (`TauCeti.ClassFieldTheory.WeilGroupReal.isBoundedParameter_restrictComplex_iff`).

## Main definitions

* `TauCeti.ClassFieldTheory.IsBoundedParameter r`: the image of `r : G →* GL_n(ℂ)` is relatively
  compact.
* `TauCeti.ClassFieldTheory.WeilGroupReal.restrictComplex r`: the restriction of a parameter of
  `W_ℝ` to `W_ℂ = ℂˣ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.logNormUnipotent`: the continuous parameter
  `w ↦ [[1, log |norm w|], [0, 1]]` of `W_ℝ`.

## Main results

* `TauCeti.ClassFieldTheory.IsBoundedParameter.comp`: boundedness passes to the composite with a
  homomorphism into `G`.
* `TauCeti.ClassFieldTheory.isBoundedParameter_of_compactSpace`: continuous parameters of compact
  groups are bounded.
* `TauCeti.ClassFieldTheory.WeilGroupReal.isBoundedParameter_restrictComplex_iff`: a parameter of
  `W_ℝ` is bounded exactly when its restriction to `W_ℂ` is.
* `TauCeti.ClassFieldTheory.WeilGroupReal.not_isBoundedParameter_logNormUnipotent`: the unipotent
  parameter `w ↦ [[1, log |norm w|], [0, 1]]` is not bounded.

## References

* A. W. Knapp, *Local Langlands correspondence: the archimedean case*, §3, pp.401–403.
-/

public section

open Matrix

namespace TauCeti.ClassFieldTheory

/-- An `n`-dimensional parameter `r : G →* GL_n(ℂ)` is **bounded** when its image is relatively
compact in `GL_n(ℂ)`. This is stronger than asking each `r g` to have eigenvalues of absolute
value one. -/
def IsBoundedParameter {G : Type*} [Group G] {n : ℕ} (r : G →* GL (Fin n) ℂ) : Prop :=
  IsCompact (closure (Set.range r))

theorem isBoundedParameter_iff {G : Type*} [Group G] {n : ℕ} (r : G →* GL (Fin n) ℂ) :
    IsBoundedParameter r ↔ IsCompact (closure (Set.range r)) :=
  Iff.rfl

/-- A bounded parameter stays bounded after composing with a homomorphism into the group. -/
theorem IsBoundedParameter.comp {G H : Type*} [Group G] [Group H] {n : ℕ}
    {r : G →* GL (Fin n) ℂ} (hr : IsBoundedParameter r) (f : H →* G) :
    IsBoundedParameter (r.comp f) :=
  hr.closure_of_subset ((Set.range_comp_subset_range f r).trans subset_closure)

/-- A continuous parameter of a compact group is bounded. -/
theorem isBoundedParameter_of_compactSpace {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] {n : ℕ} {r : G →* GL (Fin n) ℂ} (hr : Continuous r) :
    IsBoundedParameter r :=
  (isCompact_range hr).closure

namespace WeilGroupReal

variable {n : ℕ}

/-- The restriction of a parameter of `W_ℝ` to `W_ℂ = ℂˣ`. -/
def restrictComplex (r : WeilGroupReal →* GL (Fin n) ℂ) : WeilGroupComplex →* GL (Fin n) ℂ :=
  r.comp includeComplex

@[simp]
theorem restrictComplex_apply (r : WeilGroupReal →* GL (Fin n) ℂ) (z : WeilGroupComplex) :
    restrictComplex r z = r (includeComplex z) :=
  (rfl)

/-- The restriction of a continuous parameter is continuous. -/
@[fun_prop]
theorem continuous_restrictComplex {r : WeilGroupReal →* GL (Fin n) ℂ} (hr : Continuous r) :
    Continuous (restrictComplex r) :=
  hr.comp continuous_includeComplex

/-- **Boundedness is detected on `ℂˣ`.** A parameter of `W_ℝ` is bounded exactly when its
restriction to `W_ℂ = ℂˣ` is: the image of `W_ℝ = ℂˣ ⊔ jℂˣ` is the union of the image of `ℂˣ` and
its translate by `r j`. -/
@[simp]
theorem isBoundedParameter_restrictComplex_iff (r : WeilGroupReal →* GL (Fin n) ℂ) :
    IsBoundedParameter (restrictComplex r) ↔ IsBoundedParameter r := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp includeComplex⟩
  set R := closure (Set.range (restrictComplex r))
  have hsub : Set.range r ⊆ R ∪ (fun x ↦ r j * x) '' R := by
    rintro _ ⟨w, rfl⟩
    rcases exists_includeComplex_or_j_mul w with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact Or.inl (subset_closure ⟨z, rfl⟩)
    · exact Or.inr ⟨r (includeComplex z), subset_closure ⟨z, rfl⟩, (map_mul r _ _).symm⟩
  have hK : IsCompact (R ∪ (fun x ↦ r j * x) '' R) :=
    h.union (h.image (continuous_const.mul continuous_id))
  exact hK.closure_of_subset hsub

/-! ### A unipotent parameter with unbounded image -/

/-- The homomorphism `ℝˣ →* Multiplicative ℂ`, `t ↦ log |t|`, written `Real.log t` because
`Real.log` already ignores the sign. -/
private noncomputable def logAbs : ℝˣ →* Multiplicative ℂ where
  toFun t := .ofAdd (Real.log (t : ℝ) : ℂ)
  map_one' := by simp
  map_mul' s t := by
    rw [Units.val_mul, Real.log_mul s.ne_zero t.ne_zero, Complex.ofReal_add, ofAdd_add]

private theorem logAbs_apply (t : ℝˣ) : logAbs t = .ofAdd (Real.log (t : ℝ) : ℂ) :=
  (rfl)

/-- **The parameter `w ↦ [[1, log |norm w|], [0, 1]]` of `W_ℝ`**: every `w` acts by a unipotent
matrix, with both eigenvalues `1`, and the parameter is continuous
(`TauCeti.ClassFieldTheory.WeilGroupReal.continuous_logNormUnipotent`) but not bounded
(`TauCeti.ClassFieldTheory.WeilGroupReal.not_isBoundedParameter_logNormUnipotent`). -/
noncomputable def logNormUnipotent : WeilGroupReal →* GL (Fin 2) ℂ :=
  GeneralLinearGroup.upperRightHom.toMonoidHom.comp (logAbs.comp norm)

/-- `logNormUnipotent w` is Mathlib's unipotent matrix `upperRightHom (log |norm w|)`. -/
theorem logNormUnipotent_apply (w : WeilGroupReal) :
    logNormUnipotent w = GeneralLinearGroup.upperRightHom (Real.log (norm w : ℝ) : ℂ) := by
  simp [logNormUnipotent, logAbs_apply]

@[simp]
theorem coe_logNormUnipotent (w : WeilGroupReal) :
    (logNormUnipotent w : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1, (Real.log (norm w : ℝ) : ℂ); 0, 1] := by
  simp [logNormUnipotent_apply, GeneralLinearGroup.upperRightHom_apply]

/-- The `(0, 1)` entry of `logNormUnipotent w` is `log |norm w|`. -/
theorem logNormUnipotent_apply_zero_one (w : WeilGroupReal) :
    (logNormUnipotent w : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = (Real.log (norm w : ℝ) : ℂ) := by
  simp

/-- The parameter `w ↦ [[1, log |norm w|], [0, 1]]` is continuous. -/
@[fun_prop]
theorem continuous_logNormUnipotent : Continuous logNormUnipotent := by
  rw [show ⇑logNormUnipotent = _ from funext logNormUnipotent_apply]
  exact GeneralLinearGroup.continuous_upperRightHom.comp <| Complex.continuous_ofReal.comp <|
    (Units.continuous_val.comp continuous_norm).log fun w ↦ (norm w).ne_zero

/-- **A unipotent parameter need not be bounded.** The parameter
`w ↦ [[1, log |norm w|], [0, 1]]` has both eigenvalues `1` at every `w` but unbounded image, since
`log |norm w|` takes every real value. -/
theorem not_isBoundedParameter_logNormUnipotent : ¬ IsBoundedParameter logNormUnipotent := by
  intro h
  -- the `(0, 1)` entry is bounded on the compact closure of the image
  obtain ⟨B, hB⟩ := (h.image (Units.continuous_val.matrix_elem 0 1)).isBounded.exists_norm_le
  obtain ⟨w, hw⟩ := norm_surjective (Units.mk0 (Real.exp (B + 1)) (Real.exp_pos _).ne')
  have := hB _ ⟨logNormUnipotent w, subset_closure ⟨w, rfl⟩, rfl⟩
  simp only [logNormUnipotent_apply_zero_one, hw, Units.val_mk0, Real.log_exp, Complex.norm_real,
    Real.norm_eq_abs] at this
  linarith [le_abs_self (B + 1)]

end WeilGroupReal

end TauCeti.ClassFieldTheory
