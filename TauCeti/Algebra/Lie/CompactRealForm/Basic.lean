/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.Algebra.Lie.BaseChange.Hom
import TauCeti.LinearAlgebra.Trace.Basic

/-!
# Real forms of a complex Lie algebra fixed by a conjugation, and compact real forms

A *conjugation* of a complex Lie algebra `L` is a bracket-preserving conjugate-linear involution
`τ`. Its fixed points form a real Lie subalgebra `𝔲 = Fix τ`, and `L = 𝔲 ⊕ i 𝔲`: every real basis
of `𝔲` is a complex basis of `L` (`TauCeti.IsLieConjugation.complexBasis`), and the inclusion
induces an isomorphism of complex Lie algebras `ℂ ⊗[ℝ] 𝔲 ≃ L`
(`TauCeti.IsLieConjugation.complexificationEquiv`). This is real-form descent. In a basis of `𝔲`
the matrix of `ad X` for `X ∈ 𝔲` is the same over `ℝ` and over `ℂ`, so the real Killing form of `𝔲`
is the restriction of the complex Killing form of `L`
(`TauCeti.IsLieConjugation.killingForm_realForm`).

The *Hermitian Killing form* `H_τ(x, y) = -B(x, τ y)` of `τ` is linear in `x` and conjugate-linear
in `y`. Since `τ` conjugates the Killing form, `B(τ x, τ y) = conj B(x, y)`, it is Hermitian
symmetric (`TauCeti.killingHermitianForm_conj_symm`). The conjugation is *compact*
(`TauCeti.IsCompactConjugation`) when `H_τ` is positive definite; its fixed points are then a
*compact real form* of `L`, on which the real Killing form is negative definite, because
`B(X, X) = -H_τ(X, X)` for `τ X = X` (`TauCeti.IsCompactConjugation.killingForm_realForm_neg`).

For `𝔰𝔩₂(ℂ)` with `τ h = -h`, `τ e = -f`, `τ f = -e`, the compact real form is
`span_ℝ(i h, e - f, i (e + f)) = 𝔰𝔲(2)`, and `H_τ(e, e) = B(e, f) = 4`, `H_τ(h, h) = B(h, h) = 8`.
The complex-linear Chevalley involution is not a conjugation in this sense: its fixed points form a
complex subalgebra, and `-B(x, ω y)` is bilinear rather than Hermitian.

## Main definitions

* `TauCeti.IsLieConjugation`: a bracket-preserving conjugate-linear involution.
* `TauCeti.IsLieConjugation.realForm`: its fixed points, a real Lie subalgebra.
* `TauCeti.IsLieConjugation.complexBasis`: a real basis of the real form, as a complex basis.
* `TauCeti.IsLieConjugation.complexificationEquiv`: real-form descent `ℂ ⊗[ℝ] 𝔲 ≃ₗ⁅ℂ⁆ L`.
* `TauCeti.killingHermitianForm`: the Hermitian form `H_τ(x, y) = -B(x, τ y)`.
* `TauCeti.IsCompactConjugation`: a conjugation with positive definite `H_τ`.

## Main results

* `TauCeti.IsLieConjugation.killingForm_map`: `B(τ x, τ y) = conj B(x, y)`.
* `TauCeti.killingHermitianForm_conj_symm`: `H_τ(y, x) = conj H_τ(x, y)`.
* `TauCeti.IsLieConjugation.killingForm_realForm`: the Killing form of the real form is the
  restriction of the Killing form of `L`.
* `TauCeti.IsCompactConjugation.killingForm_realForm_neg`: the Killing form of a compact real form
  is negative definite.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, Sections I.8
  and VI.1.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Academic Press, 1978,
  Chapter III, Section 6.
-/

@[expose] public section

open scoped ComplexOrder TensorProduct

namespace TauCeti

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- A *conjugation* of a complex Lie algebra: a conjugate-linear map `τ` preserving brackets with
`τ ∘ τ = id`. -/
structure IsLieConjugation (τ : L →ₛₗ[starRingEnd ℂ] L) : Prop where
  /-- `τ` preserves brackets. -/
  map_lie (x y : L) : τ ⁅x, y⁆ = ⁅τ x, τ y⁆
  /-- `τ` is an involution. -/
  involutive : Function.Involutive τ

/-- The **Hermitian Killing form** `H_τ(x, y) = -B(x, τ y)` of a conjugate-linear map `τ`, with
`B` the Killing form. It is linear in `x` and conjugate-linear in `y`. -/
noncomputable def killingHermitianForm (τ : L →ₛₗ[starRingEnd ℂ] L) (x y : L) : ℂ :=
  -killingForm ℂ L x (τ y)

/-- A *compact conjugation*: a conjugation whose Hermitian Killing form `-B(x, τ y)` is positive
definite. Its fixed points form a compact real form. -/
structure IsCompactConjugation (τ : L →ₛₗ[starRingEnd ℂ] L) : Prop extends IsLieConjugation τ where
  /-- The Hermitian Killing form is positive definite. -/
  pos (x : L) (hx : x ≠ 0) : 0 < killingHermitianForm τ x x

namespace IsLieConjugation

variable [LieAlgebra ℝ L] [IsScalarTower ℝ ℂ L] {τ : L →ₛₗ[starRingEnd ℂ] L}

omit [LieAlgebra ℝ L] [IsScalarTower ℝ ℂ L] in
/-- A conjugation applied twice is the identity. -/
@[simp]
theorem apply_apply (hτ : IsLieConjugation τ) (x : L) : τ (τ x) = x :=
  hτ.involutive x

omit [LieAlgebra ℝ L] [IsScalarTower ℝ ℂ L] in
/-- `ad (τ x) = τ ∘ ad x ∘ τ`. -/
theorem ad_apply_eq (hτ : IsLieConjugation τ) (x : L) :
    LieAlgebra.ad ℂ L (τ x) = (τ.comp (LieAlgebra.ad ℂ L x)).comp τ := by
  ext y
  simp [hτ.map_lie, hτ.apply_apply]

/-- A conjugate-linear map is real-linear. -/
theorem map_real_smul (τ : L →ₛₗ[starRingEnd ℂ] L) (r : ℝ) (x : L) : τ (r • x) = r • τ x := by
  rw [← algebraMap_smul ℂ r x, τ.map_smulₛₗ, ← algebraMap_smul ℂ r (τ x)]
  simp

/-- The **real form** of a conjugation `τ`: the real Lie subalgebra of its fixed points. -/
def realForm (hτ : IsLieConjugation τ) : LieSubalgebra ℝ L where
  carrier := {x | τ x = x}
  add_mem' {x y} (hx : τ x = x) (hy : τ y = y) := show τ (x + y) = x + y by
    rw [map_add, hx, hy]
  zero_mem' := map_zero τ
  smul_mem' r x (hx : τ x = x) := show τ (r • x) = r • x by
    rw [map_real_smul, hx]
  lie_mem' {x y} (hx : τ x = x) (hy : τ y = y) := show τ ⁅x, y⁆ = ⁅x, y⁆ by
    rw [hτ.map_lie, hx, hy]

variable (hτ : IsLieConjugation τ)

/-- Membership in the real form is being fixed by `τ`. -/
@[simp]
theorem mem_realForm {x : L} : x ∈ hτ.realForm ↔ τ x = x :=
  Iff.rfl

/-- `τ` fixes the elements of its real form. -/
@[simp]
theorem apply_coe_realForm (x : hτ.realForm) : τ x = x :=
  x.2

/-- The **real part** `(x + τ x) / 2` of an element, in the real form. -/
noncomputable def re : L →ₗ[ℝ] hτ.realForm where
  toFun x := ⟨(1 / 2 : ℝ) • (x + τ x), by
    rw [mem_realForm, map_real_smul, map_add, hτ.apply_apply, add_comm]⟩
  map_add' x y := Subtype.ext <| show (1 / 2 : ℝ) • (x + y + τ (x + y)) =
      (1 / 2 : ℝ) • (x + τ x) + (1 / 2 : ℝ) • (y + τ y) by
    rw [map_add]; module
  map_smul' r x := Subtype.ext <| show (1 / 2 : ℝ) • (r • x + τ (r • x)) =
      r • ((1 / 2 : ℝ) • (x + τ x)) by
    rw [map_real_smul]; module

/-- The **imaginary part** `-i (x - τ x) / 2` of an element, in the real form. -/
noncomputable def im : L →ₗ[ℝ] hτ.realForm where
  toFun x := ⟨(-(Complex.I / 2)) • (x - τ x), by
    rw [mem_realForm, τ.map_smulₛₗ, map_sub, hτ.apply_apply]
    simp only [map_neg, map_div₀, Complex.conj_I, map_ofNat]
    module⟩
  map_add' x y := Subtype.ext <| show (-(Complex.I / 2)) • (x + y - τ (x + y)) =
      (-(Complex.I / 2)) • (x - τ x) + (-(Complex.I / 2)) • (y - τ y) by
    rw [map_add]; module
  map_smul' r x := Subtype.ext <| show (-(Complex.I / 2)) • (r • x - τ (r • x)) =
      r • ((-(Complex.I / 2)) • (x - τ x)) by
    rw [map_real_smul, ← algebraMap_smul ℂ r x, ← algebraMap_smul ℂ r (τ x),
      ← algebraMap_smul ℂ r]
    module

/-- The real part is `(x + τ x) / 2`. -/
theorem coe_re (x : L) : (hτ.re x : L) = (1 / 2 : ℝ) • (x + τ x) :=
  rfl

/-- The imaginary part is `-i (x - τ x) / 2`. -/
theorem coe_im (x : L) : (hτ.im x : L) = (-(Complex.I / 2)) • (x - τ x) :=
  rfl

/-- Every element is `re x + i im x`: `L = 𝔲 + i 𝔲`. -/
theorem re_add_I_smul_im (x : L) : (hτ.re x : L) + Complex.I • (hτ.im x : L) = x := by
  rw [coe_re, coe_im, ← algebraMap_smul ℂ]
  match_scalars <;> simp only [Complex.coe_algebraMap] <;> ring_nf <;> norm_num [Complex.I_sq]

/-- The real part of a complex multiple of an element of the real form. -/
theorem re_smul_coe (c : ℂ) (y : hτ.realForm) : hτ.re (c • (y : L)) = c.re • y := by
  apply Subtype.ext
  rw [coe_re, τ.map_smulₛₗ, apply_coe_realForm, SetLike.val_smul, ← algebraMap_smul ℂ,
    ← algebraMap_smul ℂ c.re, ← add_smul, smul_smul, Complex.add_conj]
  congr 1
  simp only [Complex.coe_algebraMap]
  push_cast
  ring

/-- The imaginary part of a complex multiple of an element of the real form. -/
theorem im_smul_coe (c : ℂ) (y : hτ.realForm) : hτ.im (c • (y : L)) = c.im • y := by
  apply Subtype.ext
  rw [coe_im, τ.map_smulₛₗ, apply_coe_realForm, SetLike.val_smul, ← algebraMap_smul ℂ c.im,
    ← sub_smul, smul_smul, Complex.sub_conj]
  congr 1
  simp only [Complex.coe_algebraMap]
  push_cast
  linear_combination (-(c.im : ℂ)) * Complex.I_sq

/-- A real-linearly independent family in the real form is complex-linearly independent in `L`. -/
theorem linearIndependent_coe {ι : Type*} {v : ι → hτ.realForm} (hv : LinearIndependent ℝ v) :
    LinearIndependent ℂ (fun i ↦ (v i : L)) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  have hre := congrArg hτ.re hg
  have him := congrArg hτ.im hg
  simp only [map_sum, re_smul_coe, im_smul_coe, map_zero] at hre him
  exact Complex.ext (hv s (fun j ↦ (g j).re) hre i hi) (hv s (fun j ↦ (g j).im) him i hi)

/-- A real spanning family of the real form spans `L` over `ℂ`. -/
theorem span_coe_eq_top {ι : Type*} {v : ι → hτ.realForm}
    (hv : Submodule.span ℝ (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range fun i ↦ (v i : L)) = ⊤ := by
  have hsub : ∀ y : hτ.realForm, (y : L) ∈ Submodule.span ℂ (Set.range fun i ↦ (v i : L)) := by
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range v) := hv ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      rw [SetLike.val_smul, ← algebraMap_smul ℂ r]
      exact Submodule.smul_mem _ _ ha
  refine eq_top_iff.2 fun x _ ↦ ?_
  rw [← hτ.re_add_I_smul_im x]
  exact Submodule.add_mem _ (hsub _) (Submodule.smul_mem _ _ (hsub _))

/-- **A real basis of the real form is a complex basis of `L`.** -/
noncomputable def complexBasis {ι : Type*} (b : Module.Basis ι ℝ hτ.realForm) :
    Module.Basis ι ℂ L :=
  Module.Basis.mk (hτ.linearIndependent_coe b.linearIndependent)
    (hτ.span_coe_eq_top b.span_eq).ge

variable {ι : Type*} (b : Module.Basis ι ℝ hτ.realForm)

/-- The complex basis consists of the vectors of the real basis. -/
@[simp]
theorem complexBasis_apply (i : ι) : hτ.complexBasis b i = b i :=
  Module.Basis.mk_apply _ _ i

/-- `τ` fixes the complex basis built from a basis of the real form. -/
theorem apply_complexBasis (i : ι) : τ (hτ.complexBasis b i) = hτ.complexBasis b i := by
  rw [complexBasis_apply, apply_coe_realForm]

/-- The complex coordinates of an element of the real form are its real coordinates. -/
theorem complexBasis_repr_coe [Finite ι] (y : hτ.realForm) (i : ι) :
    (hτ.complexBasis b).repr y i = (b.repr y i : ℂ) := by
  have := Fintype.ofFinite ι
  have h : (y : L) = (hτ.complexBasis b).equivFun.symm fun j ↦ (b.repr y j : ℂ) := by
    rw [Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [← b.sum_repr y]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [complexBasis_apply, SetLike.val_smul, ← algebraMap_smul ℂ, Complex.coe_algebraMap]
  rw [h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

/-- `τ` conjugates the coordinates in the complex basis built from a basis of the real form. -/
theorem complexBasis_repr_apply [Finite ι] (x : L) (i : ι) :
    (hτ.complexBasis b).repr (τ x) i = star ((hτ.complexBasis b).repr x i) := by
  rw [← hτ.re_add_I_smul_im x, map_add, τ.map_smulₛₗ, apply_coe_realForm, apply_coe_realForm,
    map_add, map_smul, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.add_apply, Finsupp.smul_apply, complexBasis_repr_coe, complexBasis_repr_coe,
    smul_eq_mul, smul_eq_mul, star_add, star_mul', starRingEnd_apply, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]

include hτ in
/-- Conjugating a complex-linear map by `τ` conjugates its trace. -/
theorem trace_comp_comp (f : Module.End ℂ L) :
    LinearMap.trace ℂ L ((τ.comp f).comp τ) = star (LinearMap.trace ℂ L f) := by
  by_cases hfin : ¬FiniteDimensional ℂ L
  · simp [TauCeti.LinearMap.trace_eq_zero_of_not_finite hfin]
  rw [not_not] at hfin
  have : FiniteDimensional ℝ L := Module.Finite.trans ℂ L
  let c := hτ.complexBasis (Module.finBasis ℝ hτ.realForm)
  rw [LinearMap.trace_eq_matrix_trace ℂ c, LinearMap.trace_eq_matrix_trace ℂ c, Matrix.trace,
    Matrix.trace, star_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.coe_comp,
    Function.comp_apply, c, apply_complexBasis, complexBasis_repr_apply]

/-- **Real-form descent**: the inclusion of the real form induces an isomorphism
`ℂ ⊗[ℝ] 𝔲 ≃ₗ⁅ℂ⁆ L` of complex Lie algebras. -/
noncomputable def complexificationEquiv : ℂ ⊗[ℝ] hτ.realForm ≃ₗ⁅ℂ⁆ L :=
  let b := Module.Free.chooseBasis ℝ hτ.realForm
  LieEquiv.ofBijective (LieHom.liftBaseChange ℂ hτ.realForm.incl) <| by
    have h : (LieHom.liftBaseChange ℂ hτ.realForm.incl).toLinearMap =
        ((Algebra.TensorProduct.basis ℂ b).equiv (hτ.complexBasis b) (Equiv.refl _)).toLinearMap :=
      (Algebra.TensorProduct.basis ℂ b).ext fun i ↦ by
        rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, complexBasis_apply,
          Algebra.TensorProduct.basis_apply, LieHom.coe_toLinearMap, LieHom.liftBaseChange_tmul,
          one_smul, LieSubalgebra.coe_incl]
    change Function.Bijective (LieHom.liftBaseChange ℂ hτ.realForm.incl).toLinearMap
    rw [h]
    exact LinearEquiv.bijective _

/-- Real-form descent sends `c ⊗ y` to `c • y`. -/
@[simp]
theorem complexificationEquiv_tmul (c : ℂ) (y : hτ.realForm) :
    hτ.complexificationEquiv (c ⊗ₜ y) = c • (y : L) :=
  LieHom.liftBaseChange_tmul ℂ _ c y

/-- **The Killing form of the real form is the restriction of the Killing form of `L`.** In a
real basis of `𝔲` the matrix of `ad X ∘ ad Y` for `X, Y ∈ 𝔲` is the same over `ℝ` and over `ℂ`. -/
theorem killingForm_realForm (x y : hτ.realForm) :
    (killingForm ℝ hτ.realForm x y : ℂ) = killingForm ℂ L x y := by
  by_cases hfin : ¬FiniteDimensional ℝ hτ.realForm
  · have hL : ¬FiniteDimensional ℂ L := fun _ ↦ hfin <| by
      have : FiniteDimensional ℝ L := Module.Finite.trans ℂ L
      infer_instance
    rw [killingForm_apply_apply, killingForm_apply_apply,
      TauCeti.LinearMap.trace_eq_zero_of_not_finite hfin,
      TauCeti.LinearMap.trace_eq_zero_of_not_finite hL, LinearMap.zero_apply, LinearMap.zero_apply,
      Complex.ofReal_zero]
  rw [not_not] at hfin
  let b := Module.finBasis ℝ hτ.realForm
  rw [killingForm_apply_apply, killingForm_apply_apply, LinearMap.trace_eq_matrix_trace ℝ b,
    LinearMap.trace_eq_matrix_trace ℂ (hτ.complexBasis b), Matrix.trace, Matrix.trace,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.coe_comp, Function.comp_apply,
    LieAlgebra.ad_apply, complexBasis_apply]
  rw [← complexBasis_repr_coe, LieSubalgebra.coe_bracket, LieSubalgebra.coe_bracket]

end IsLieConjugation

namespace IsLieConjugation

variable {τ : L →ₛₗ[starRingEnd ℂ] L}

/-- **A conjugation conjugates the Killing form**: `B(τ x, τ y) = conj B(x, y)`. -/
theorem killingForm_map (hτ : IsLieConjugation τ) (x y : L) :
    killingForm ℂ L (τ x) (τ y) = star (killingForm ℂ L x y) := by
  let : LieAlgebra ℝ L := { lie_smul r x y := lie_smul (r : ℂ) x y }
  rw [killingForm_apply_apply, killingForm_apply_apply, hτ.ad_apply_eq, hτ.ad_apply_eq,
    ← hτ.trace_comp_comp]
  congr 1
  ext z
  simp [hτ.apply_apply]

end IsLieConjugation

variable {τ : L →ₛₗ[starRingEnd ℂ] L}

/-- The Hermitian Killing form is linear in the first argument. -/
theorem killingHermitianForm_smul_left (c : ℂ) (x y : L) :
    killingHermitianForm τ (c • x) y = c * killingHermitianForm τ x y := by
  simp [killingHermitianForm]

/-- The Hermitian Killing form is conjugate-linear in the second argument. -/
theorem killingHermitianForm_smul_right (c : ℂ) (x y : L) :
    killingHermitianForm τ x (c • y) = star c * killingHermitianForm τ x y := by
  simp [killingHermitianForm]

/-- **The Hermitian Killing form of a conjugation is Hermitian**: `H_τ(y, x) = conj H_τ(x, y)`. -/
theorem killingHermitianForm_conj_symm (hτ : IsLieConjugation τ)
    (x y : L) : killingHermitianForm τ y x = star (killingHermitianForm τ x y) := by
  rw [killingHermitianForm, killingHermitianForm, star_neg, ← hτ.killingForm_map,
    hτ.apply_apply, LieModule.traceForm_comm]

namespace IsCompactConjugation

variable [LieAlgebra ℝ L] [IsScalarTower ℝ ℂ L] (hτ : IsCompactConjugation τ)

/-- **The Killing form of a compact real form is negative definite.** For `X` in the real form,
`B(X, X) = -H_τ(X, X)`, and `H_τ` is positive definite. -/
theorem killingForm_realForm_neg (x : hτ.realForm) (hx : x ≠ 0) :
    killingForm ℝ hτ.realForm x x < 0 := by
  have hpos := hτ.pos x (by simpa using hx)
  rw [killingHermitianForm, IsLieConjugation.apply_coe_realForm,
    ← hτ.toIsLieConjugation.killingForm_realForm, ← Complex.ofReal_neg, Complex.zero_lt_real]
    at hpos
  linarith

end IsCompactConjugation

end TauCeti
