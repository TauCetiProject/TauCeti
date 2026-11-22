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
public import TauCeti.LinearAlgebra.Complex.RealForm
import TauCeti.LinearAlgebra.Trace.Basic
import TauCeti.LinearAlgebra.Trace.Semilinear

/-!
# Real forms of a complex Lie algebra fixed by a conjugation, and compact real forms

A *conjugation* of a complex Lie algebra `L` is a bracket-preserving conjugate-linear involution
`τ`. Its fixed points form a real Lie subalgebra `𝔲 = Fix τ`, and `L = 𝔲 ⊕ i 𝔲`: by real-form
descent for vector spaces (`LinearMap.isBaseChange_complex_of_conj`) the inclusion induces an
isomorphism of complex Lie algebras `ℂ ⊗[ℝ] 𝔲 ≃ L`
(`TauCeti.IsLieConjugation.complexificationEquiv`), so every real basis of `𝔲` is a complex basis
of `L` (`TauCeti.IsLieConjugation.complexBasis`), in which `τ` conjugates the coordinates. In a
basis of `𝔲` the matrix of `ad X` for `X ∈ 𝔲` is the same over `ℝ` and over `ℂ`, so the real
Killing form of `𝔲` is the restriction of the complex Killing form of `L`
(`TauCeti.IsLieConjugation.killingForm_realForm`).

The *Hermitian Killing form* `H_τ(x, y) = -B(x, τ y)` of `τ` is linear in `x` and conjugate-linear
in `y`. Since `τ` conjugates traces (`LinearMap.trace_comp_comp_of_involutive`), it conjugates the
Killing form, `B(τ x, τ y) = conj B(x, y)`, so `H_τ` is Hermitian
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
* `Module.Basis.isLieConjugation_conj`: the conjugation fixing a basis with real structure
  constants is a conjugation of Lie algebras.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, Sections I.8
  and VI.1.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Academic Press, 1978,
  Chapter III, Section 6.
-/

public section

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

/-- The defining formula `H_τ(x, y) = -B(x, τ y)` of the Hermitian Killing form. -/
theorem killingHermitianForm_def (τ : L →ₛₗ[starRingEnd ℂ] L) (x y : L) :
    killingHermitianForm τ x y = -killingForm ℂ L x (τ y) :=
  (rfl)

/-- A *compact conjugation*: a conjugation whose Hermitian Killing form `-B(x, τ y)` is positive
definite. Its fixed points form a compact real form. -/
structure IsCompactConjugation (τ : L →ₛₗ[starRingEnd ℂ] L) : Prop extends IsLieConjugation τ where
  /-- The Hermitian Killing form is positive definite. -/
  pos (x : L) (hx : x ≠ 0) : 0 < killingHermitianForm τ x x

namespace IsLieConjugation

variable {τ : L →ₛₗ[starRingEnd ℂ] L}

/-- A conjugation applied twice is the identity. -/
@[simp]
theorem apply_apply (hτ : IsLieConjugation τ) (x : L) : τ (τ x) = x :=
  hτ.involutive x

/-- `ad (τ x) = τ ∘ ad x ∘ τ`. -/
theorem ad_apply_eq (hτ : IsLieConjugation τ) (x : L) :
    LieAlgebra.ad ℂ L (τ x) = (τ.comp (LieAlgebra.ad ℂ L x)).comp τ := by
  ext y
  simp [hτ.map_lie, hτ.apply_apply]

/-- **A conjugation conjugates the Killing form**: `B(τ x, τ y) = conj B(x, y)`. -/
theorem killingForm_map (hτ : IsLieConjugation τ) (x y : L) :
    killingForm ℂ L (τ x) (τ y) = star (killingForm ℂ L x y) := by
  rw [killingForm_apply_apply, killingForm_apply_apply, hτ.ad_apply_eq, hτ.ad_apply_eq,
    ← starRingEnd_apply, ← LinearMap.trace_comp_comp_of_involutive hτ.involutive]
  congr 1
  ext z
  simp [hτ.apply_apply]

variable [LieAlgebra ℝ L] [IsScalarTower ℝ ℂ L]

/-- The **real form** of a conjugation `τ`: the real Lie subalgebra of its fixed points. -/
def realForm (hτ : IsLieConjugation τ) : LieSubalgebra ℝ L where
  carrier := {x | τ x = x}
  add_mem' {x y} hx hy := by
    rw [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_add, hx, hy]
  zero_mem' := map_zero τ
  smul_mem' r x hx := by
    rw [Set.mem_ofPred_eq] at hx ⊢
    rw [τ.map_real_smul, hx]
  lie_mem' {x y} hx hy := by
    rw [Set.mem_ofPred_eq] at hx hy ⊢
    rw [hτ.map_lie, hx, hy]

variable (hτ : IsLieConjugation τ)

/-- Membership in the real form is being fixed by `τ`. -/
@[simp]
theorem mem_realForm {x : L} : x ∈ hτ.realForm ↔ τ x = x :=
  Iff.rfl

/-- `τ` fixes the elements of its real form. -/
@[simp]
theorem apply_coe_realForm (x : hτ.realForm) : τ x = x :=
  x.property

/-- The inclusion of the real form exhibits `L` as its complexification: an instance of real-form
descent for the conjugation `τ` (`LinearMap.isBaseChange_complex_of_conj`). -/
theorem isBaseChange_incl : IsBaseChange ℂ (hτ.realForm.incl : hτ.realForm →ₗ[ℝ] L) :=
  (hτ.realForm.incl : hτ.realForm →ₗ[ℝ] L).isBaseChange_complex_of_conj hτ.involutive
    Subtype.val_injective (fun x ↦ hτ.apply_coe_realForm x) fun v hv ↦ ⟨⟨v, hv⟩, rfl⟩

/-- **Real-form descent**: the inclusion of the real form induces an isomorphism
`ℂ ⊗[ℝ] 𝔲 ≃ₗ⁅ℂ⁆ L` of complex Lie algebras. -/
noncomputable def complexificationEquiv : ℂ ⊗[ℝ] hτ.realForm ≃ₗ⁅ℂ⁆ L :=
  hτ.isBaseChange_incl.lieEquiv

/-- Real-form descent sends `c ⊗ y` to `c • y`. -/
@[simp]
theorem complexificationEquiv_tmul (c : ℂ) (y : hτ.realForm) :
    hτ.complexificationEquiv (c ⊗ₜ y) = c • (y : L) := by
  rw [complexificationEquiv, IsBaseChange.lieEquiv_tmul, LieSubalgebra.coe_incl]

/-- The inverse of real-form descent sends an element `y` of the real form to `1 ⊗ y`. -/
@[simp]
theorem complexificationEquiv_symm_coe (y : hτ.realForm) :
    hτ.complexificationEquiv.symm y = 1 ⊗ₜ y := by
  rw [LieEquiv.symm_apply_eq, complexificationEquiv_tmul, one_smul]

/-- **A real basis of the real form is a complex basis of `L`**, through real-form descent. -/
noncomputable def complexBasis {ι : Type*} (b : Module.Basis ι ℝ hτ.realForm) :
    Module.Basis ι ℂ L :=
  (Algebra.TensorProduct.basis ℂ b).map hτ.complexificationEquiv.toLinearEquiv

variable {ι : Type*} (b : Module.Basis ι ℝ hτ.realForm)

/-- The complex basis consists of the vectors of the real basis. -/
@[simp]
theorem complexBasis_apply (i : ι) : hτ.complexBasis b i = b i := by
  rw [complexBasis, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    LieEquiv.coe_toLinearEquiv, complexificationEquiv_tmul, one_smul]

/-- `τ` fixes the complex basis built from a basis of the real form. -/
theorem apply_complexBasis (i : ι) : τ (hτ.complexBasis b i) = hτ.complexBasis b i := by
  rw [complexBasis_apply, apply_coe_realForm]

/-- The complex coordinates of an element of the real form are its real coordinates. -/
theorem complexBasis_repr_coe (y : hτ.realForm) (i : ι) :
    (hτ.complexBasis b).repr y i = (b.repr y i : ℂ) := by
  have h : hτ.complexificationEquiv.toLinearEquiv.symm y = 1 ⊗ₜ y := by
    rw [LinearEquiv.symm_apply_eq, LieEquiv.coe_toLinearEquiv, complexificationEquiv_tmul,
      one_smul]
  rw [complexBasis, Module.Basis.map_repr, LinearEquiv.trans_apply, h,
    Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply,
    Complex.coe_algebraMap]

/-- `τ` conjugates the coordinates in the complex basis built from a basis of the real form. -/
theorem complexBasis_repr_apply (x : L) (i : ι) :
    (hτ.complexBasis b).repr (τ x) i = star ((hτ.complexBasis b).repr x i) := by
  have hx : x ∈ Submodule.span ℂ (Set.range (hτ.complexBasis b)) := (hτ.complexBasis b).mem_span x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    classical
    rw [apply_complexBasis, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, star_add]
  | smul c x _ hx => rw [τ.map_smulₛₗ, map_smul, map_smul, Finsupp.smul_apply,
      Finsupp.smul_apply, hx, smul_eq_mul, smul_eq_mul, star_mul', starRingEnd_apply]

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

variable {τ : L →ₛₗ[starRingEnd ℂ] L}

/-- The Hermitian Killing form vanishes when its first argument does. -/
@[simp]
theorem killingHermitianForm_zero_left (y : L) : killingHermitianForm τ 0 y = 0 := by
  simp [killingHermitianForm_def]

/-- The Hermitian Killing form vanishes when its second argument does. -/
@[simp]
theorem killingHermitianForm_zero_right (x : L) : killingHermitianForm τ x 0 = 0 := by
  simp [killingHermitianForm_def]

/-- The Hermitian Killing form is additive in the first argument. -/
@[simp]
theorem killingHermitianForm_add_left (x x' y : L) :
    killingHermitianForm τ (x + x') y =
      killingHermitianForm τ x y + killingHermitianForm τ x' y := by
  simp only [killingHermitianForm_def, map_add, LinearMap.add_apply, neg_add]

/-- The Hermitian Killing form is additive in the second argument. -/
@[simp]
theorem killingHermitianForm_add_right (x y y' : L) :
    killingHermitianForm τ x (y + y') =
      killingHermitianForm τ x y + killingHermitianForm τ x y' := by
  simp only [killingHermitianForm_def, map_add, neg_add]

/-- The Hermitian Killing form is linear in the first argument. -/
@[simp]
theorem killingHermitianForm_smul_left (c : ℂ) (x y : L) :
    killingHermitianForm τ (c • x) y = c * killingHermitianForm τ x y := by
  simp [killingHermitianForm_def]

/-- The Hermitian Killing form is conjugate-linear in the second argument. -/
@[simp]
theorem killingHermitianForm_smul_right (c : ℂ) (x y : L) :
    killingHermitianForm τ x (c • y) = star c * killingHermitianForm τ x y := by
  simp [killingHermitianForm_def]

/-- **The Hermitian Killing form of a conjugation is Hermitian**: `H_τ(y, x) = conj H_τ(x, y)`. -/
theorem killingHermitianForm_conj_symm (hτ : IsLieConjugation τ)
    (x y : L) : killingHermitianForm τ y x = star (killingHermitianForm τ x y) := by
  rw [killingHermitianForm_def, killingHermitianForm_def, star_neg, ← hτ.killingForm_map,
    hτ.apply_apply, LieModule.traceForm_comm]

namespace IsCompactConjugation

variable [LieAlgebra ℝ L] [IsScalarTower ℝ ℂ L] (hτ : IsCompactConjugation τ)

/-- **The Killing form of a compact real form is negative definite.** For `X` in the real form,
`B(X, X) = -H_τ(X, X)`, and `H_τ` is positive definite. -/
theorem killingForm_realForm_neg (x : hτ.realForm) (hx : x ≠ 0) :
    killingForm ℝ hτ.realForm x x < 0 := by
  have hpos := hτ.pos x (by simpa using hx)
  rw [killingHermitianForm_def, IsLieConjugation.apply_coe_realForm,
    ← hτ.toIsLieConjugation.killingForm_realForm, ← Complex.ofReal_neg, Complex.zero_lt_real]
    at hpos
  linarith

end IsCompactConjugation

end TauCeti

namespace Module.Basis

variable {L ι : Type*} [LieRing L] [LieAlgebra ℂ L] (c : Module.Basis ι ℂ L)

/-- **The conjugation fixing a basis with real structure constants preserves brackets.** -/
theorem isLieConjugation_conj (h : ∀ i j, c.conj ⁅c i, c j⁆ = ⁅c i, c j⁆) :
    TauCeti.IsLieConjugation c.conj where
  map_lie x y := by
    have hx : x ∈ Submodule.span ℂ (Set.range c) := c.mem_span x
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hy : y ∈ Submodule.span ℂ (Set.range c) := c.mem_span y
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        rw [h, conj_self, conj_self]
      | zero => simp
      | add y y' _ _ hy hy' => rw [lie_add, map_add, hy, hy', map_add, lie_add]
      | smul a y _ hy => rw [lie_smul, LinearMap.map_smulₛₗ, hy, LinearMap.map_smulₛₗ, lie_smul]
    | zero => simp
    | add x x' _ _ hx hx' => rw [add_lie, map_add, hx, hx', map_add, add_lie]
    | smul a x _ hx => rw [smul_lie, LinearMap.map_smulₛₗ, hx, LinearMap.map_smulₛₗ, smul_lie]
  involutive := c.conj_involutive

end Module.Basis
