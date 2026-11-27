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
public import TauCeti.LinearAlgebra.Basis.Semilinear
public import TauCeti.LinearAlgebra.Complex.RealForm
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import TauCeti.Algebra.Lie.Killing.Basic
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
Killing form, `B(τ x, τ y) = conj B(x, y)`, so `H_τ` is Hermitian symmetric
(`TauCeti.IsLieConjugation.killingHermitianForm_conj_symm`). The conjugation is *compact*
(`TauCeti.IsCompactConjugation`) when `H_τ` is positive definite; its fixed points are then a
*compact real form* of `L`, on which the real Killing form is negative definite, because
`B(X, X) = -H_τ(X, X)` for `τ X = X` (`TauCeti.IsCompactConjugation.killingForm_realForm_self_neg`).

For `𝔰𝔩₂(ℂ)` with `τ h = -h`, `τ e = -f`, `τ f = -e`, the compact real form is
`span_ℝ(i h, e - f, i (e + f)) = 𝔰𝔲(2)`, and `H_τ(e, e) = B(e, f) = 4`, `H_τ(h, h) = B(h, h) = 8`.
The complex-linear Chevalley involution is not a conjugation in this sense: its fixed points form a
complex subalgebra, and `-B(x, ω y)` is bilinear rather than Hermitian.

## Main definitions

* `TauCeti.IsLieConjugation`: a bracket-preserving conjugate-linear involution.
* `TauCeti.IsLieConjugation.realForm`: its fixed points, a real Lie subalgebra.
* `TauCeti.IsLieConjugation.complexBasis`: a real basis of the real form, as a complex basis.
* `TauCeti.IsLieConjugation.complexificationEquiv`: real-form descent `ℂ ⊗[ℝ] 𝔲 ≃ₗ⁅ℂ⁆ L`.
* `LinearMap.killingHermitianForm`: the Hermitian form `H_τ(x, y) = -B(x, τ y)`.
* `TauCeti.IsCompactConjugation`: a conjugation with positive definite `H_τ`.

## Main results

* `TauCeti.IsLieConjugation.killingForm_map`: `B(τ x, τ y) = conj B(x, y)`.
* `TauCeti.IsLieConjugation.killingHermitianForm_conj_symm`: `H_τ(y, x) = conj H_τ(x, y)`, and
  `TauCeti.IsLieConjugation.killingHermitianForm_lie_left`: `H_τ(⁅z, x⁆, y) = -H_τ(x, ⁅τ z, y⁆)`.
* `TauCeti.IsLieConjugation.killingForm_realForm`: the Killing form of the real form is the
  restriction of the Killing form of `L`.
* `TauCeti.IsCompactConjugation.killingForm_realForm_neg`: `B(X, τ X) < 0` for `X ≠ 0` with `X`
  and `τ X` in a real form `Fix σ`, and its case `σ = τ`,
  `TauCeti.IsCompactConjugation.killingForm_realForm_self_neg`: the Killing form of a compact real
  form is negative definite.
* `Module.Basis.isLieConjugation_coordConj`: the conjugation of the coordinates in a basis with
  real structure constants is a conjugation of Lie algebras.
* `TauCeti.IsCompactConjugation.isKilling` and `TauCeti.IsCompactConjugation.finiteDimensional`:
  a complex Lie algebra with a compact conjugation is finite-dimensional with nondegenerate Killing
  form.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, Sections I.8
  and VI.1.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Academic Press, 1978,
  Chapter III, Section 6.
-/

public section

open scoped ComplexOrder TensorProduct

namespace LinearMap

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- The **Hermitian Killing form** `H_τ(x, y) = -B(x, τ y)` of a conjugate-linear map `τ`, with
`B` the Killing form: a sesquilinear form, linear in `x` and conjugate-linear in `y`. -/
noncomputable def killingHermitianForm (τ : L →ₛₗ[starRingEnd ℂ] L) :
    L →ₗ[ℂ] L →ₛₗ[starRingEnd ℂ] ℂ :=
  -(killingForm ℂ L).compl₂ τ

/-- The defining formula `H_τ(x, y) = -B(x, τ y)` of the Hermitian Killing form. -/
theorem killingHermitianForm_def (τ : L →ₛₗ[starRingEnd ℂ] L) (x y : L) :
    τ.killingHermitianForm x y = -killingForm ℂ L x (τ y) :=
  (rfl)

end LinearMap

namespace TauCeti

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- A *conjugation* of a complex Lie algebra: a conjugate-linear map `τ` preserving brackets with
`τ ∘ τ = id`. -/
structure IsLieConjugation (τ : L →ₛₗ[starRingEnd ℂ] L) : Prop where
  /-- `τ` preserves brackets. -/
  map_lie (x y : L) : τ ⁅x, y⁆ = ⁅τ x, τ y⁆
  /-- `τ` is an involution. -/
  involutive : Function.Involutive τ

/-- A *compact conjugation*: a conjugation whose Hermitian Killing form `-B(x, τ y)` is positive
definite. Its fixed points form a compact real form. -/
structure IsCompactConjugation (τ : L →ₛₗ[starRingEnd ℂ] L) : Prop extends IsLieConjugation τ where
  /-- The Hermitian Killing form is positive definite. -/
  pos (x : L) (hx : x ≠ 0) : 0 < τ.killingHermitianForm x x

namespace IsLieConjugation

variable {τ : L →ₛₗ[starRingEnd ℂ] L}

/-- A conjugation applied twice is the identity. -/
@[simp]
theorem apply_apply (hτ : IsLieConjugation τ) (x : L) : τ (τ x) = x :=
  hτ.involutive x

/-- `ad (τ x) = τ ∘ ad x ∘ τ`. -/
theorem ad_map (hτ : IsLieConjugation τ) (x : L) :
    LieAlgebra.ad ℂ L (τ x) = (τ.comp (LieAlgebra.ad ℂ L x)).comp τ := by
  ext y
  simp [hτ.map_lie, hτ.apply_apply]

/-- **A conjugation conjugates the Killing form**: `B(τ x, τ y) = conj B(x, y)`. -/
theorem killingForm_map (hτ : IsLieConjugation τ) (x y : L) :
    killingForm ℂ L (τ x) (τ y) = star (killingForm ℂ L x y) := by
  rw [killingForm_apply_apply, killingForm_apply_apply, hτ.ad_map, hτ.ad_map,
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

/-- Real-form descent intertwines the conjugation of `ℂ ⊗[ℝ] 𝔲` with `τ`. -/
@[simp]
theorem complexificationEquiv_tmulConj (u : ℂ ⊗[ℝ] hτ.realForm) :
    hτ.complexificationEquiv (tmulConj hτ.realForm u) = τ (hτ.complexificationEquiv u) := by
  induction u with
  | tmul c y => simp [tmulConj_tmul]
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, map_add]

/-- **A real basis of the real form is a complex basis of `L`**, through real-form descent. -/
noncomputable def complexBasis {ι : Type*} (b : Module.Basis ι ℝ hτ.realForm) :
    Module.Basis ι ℂ L :=
  hτ.isBaseChange_incl.basis b

variable {ι : Type*} (b : Module.Basis ι ℝ hτ.realForm)

/-- The complex basis consists of the vectors of the real basis. -/
@[simp]
theorem complexBasis_apply (i : ι) : hτ.complexBasis b i = b i :=
  hτ.isBaseChange_incl.basis_apply b i

/-- `τ` fixes the complex basis built from a basis of the real form. -/
theorem apply_complexBasis (i : ι) : τ (hτ.complexBasis b i) = hτ.complexBasis b i := by
  rw [complexBasis_apply, apply_coe_realForm]

/-- The complex coordinates of an element of the real form are its real coordinates. -/
@[simp]
theorem complexBasis_repr_coe (y : hτ.realForm) (i : ι) :
    (hτ.complexBasis b).repr y i = (b.repr y i : ℂ) :=
  hτ.isBaseChange_incl.basis_repr_comp_apply b y i

/-- `τ` is the conjugation of the coordinates in the complex basis built from a basis of the real
form. -/
theorem eq_coordConj_complexBasis : τ = (hτ.complexBasis b).coordConj.toLinearMap :=
  (hτ.complexBasis b).ext fun i ↦ by
    rw [apply_complexBasis, LinearEquiv.coe_coe, Module.Basis.coordConj_self]

/-- `τ` conjugates the coordinates in the complex basis built from a basis of the real form. -/
@[simp]
theorem complexBasis_repr_map (x : L) (i : ι) :
    (hτ.complexBasis b).repr (τ x) i = star ((hτ.complexBasis b).repr x i) := by
  rw [LinearMap.congr_fun (hτ.eq_coordConj_complexBasis b) x, LinearEquiv.coe_coe,
    Module.Basis.repr_coordConj]

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
  -- Transport along real-form descent, then use the base-change formula for the Killing form.
  rw [← one_smul ℂ (x : L), ← one_smul ℂ (y : L), ← complexificationEquiv_tmul,
    ← complexificationEquiv_tmul, LieAlgebra.killingForm_of_equiv_apply]
  -- The Killing form is the trace form of the adjoint representation.
  change ((LieModule.traceForm ℝ hτ.realForm hτ.realForm x y : ℝ) : ℂ) =
    LieModule.traceForm ℂ (ℂ ⊗[ℝ] hτ.realForm) (ℂ ⊗[ℝ] hτ.realForm) (1 ⊗ₜ x) (1 ⊗ₜ y)
  rw [LieModule.traceForm_baseChange, LinearMap.BilinForm.baseChange_tmul, one_mul,
    Algebra.smul_def, mul_one, Complex.coe_algebraMap]

end IsLieConjugation

variable {τ : L →ₛₗ[starRingEnd ℂ] L}

/-- **The Hermitian Killing form of a conjugation is Hermitian**: `H_τ(y, x) = conj H_τ(x, y)`. -/
theorem IsLieConjugation.killingHermitianForm_conj_symm (hτ : IsLieConjugation τ) (x y : L) :
    τ.killingHermitianForm y x = star (τ.killingHermitianForm x y) := by
  rw [LinearMap.killingHermitianForm_def, LinearMap.killingHermitianForm_def, star_neg,
    ← hτ.killingForm_map, hτ.apply_apply, LieModule.traceForm_comm]

/-- A conjugation conjugates its Hermitian Killing form: `H_τ(τ x, τ y) = conj H_τ(x, y)`. -/
theorem IsLieConjugation.killingHermitianForm_map (hτ : IsLieConjugation τ) (x y : L) :
    τ.killingHermitianForm (τ x) (τ y) = star (τ.killingHermitianForm x y) := by
  rw [LinearMap.killingHermitianForm_def, LinearMap.killingHermitianForm_def, hτ.killingForm_map,
    star_neg]

/-- **Invariance of the Hermitian Killing form**: `ad z` is adjoint to `-ad (τ z)`, that is
`H_τ(⁅z, x⁆, y) = -H_τ(x, ⁅τ z, y⁆)`. -/
theorem IsLieConjugation.killingHermitianForm_lie_left (hτ : IsLieConjugation τ) (z x y : L) :
    τ.killingHermitianForm ⁅z, x⁆ y = -τ.killingHermitianForm x ⁅τ z, y⁆ := by
  rw [LinearMap.killingHermitianForm_def, LinearMap.killingHermitianForm_def, hτ.map_lie,
    hτ.apply_apply, neg_neg, ← lie_skew, map_neg, LinearMap.neg_apply, neg_neg,
    LieModule.traceForm_apply_lie_apply]

/-- A conjugation is compact exactly when its Hermitian Killing form is positive definite. -/
theorem isCompactConjugation_iff :
    IsCompactConjugation τ ↔
      IsLieConjugation τ ∧ ∀ x : L, x ≠ 0 → 0 < τ.killingHermitianForm x x :=
  ⟨fun h ↦ ⟨h.toIsLieConjugation, h.pos⟩, fun h ↦ ⟨h.1, h.2⟩⟩

namespace IsCompactConjugation

section Complex

variable (hτ : IsCompactConjugation τ)
include hτ

/-- The Hermitian Killing form of a compact conjugation is nonnegative on the diagonal. -/
theorem killingHermitianForm_self_nonneg (x : L) : 0 ≤ τ.killingHermitianForm x x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (hτ.pos x hx).le

/-- The Hermitian Killing form of a compact conjugation vanishes at `(x, x)` only for `x = 0`. -/
@[simp]
theorem killingHermitianForm_self_eq_zero {x : L} : τ.killingHermitianForm x x = 0 ↔ x = 0 :=
  ⟨fun h ↦ by_contra fun hx ↦ (hτ.pos x hx).ne' h, fun h ↦ by simp [h]⟩

/-- **The Killing form of a complex Lie algebra with a compact conjugation is nondegenerate**: if
`B(y, x) = 0` for all `y`, then `H_τ(x, x) = -B(τ x, x) = 0`, so `x = 0`. -/
theorem isKilling : LieAlgebra.IsKilling ℂ L where
  killingCompl_top_eq_bot := by
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    rw [LieIdeal.mem_killingCompl] at hx
    rw [LieSubmodule.mem_bot, ← hτ.killingHermitianForm_self_eq_zero,
      LinearMap.killingHermitianForm_def, LieModule.traceForm_comm,
      hx (τ x) (LieSubmodule.mem_top _), neg_zero]

/-- **A complex Lie algebra with a compact conjugation is finite-dimensional**, since its Killing
form is nondegenerate (`isKilling`) and a Lie algebra with nondegenerate Killing form is finite
(`TauCeti.finite_of_isKilling`). -/
theorem finiteDimensional : FiniteDimensional ℂ L :=
  have := hτ.isKilling
  finite_of_isKilling (R := ℂ) (L := L)

end Complex

variable [LieAlgebra ℝ L] [IsScalarTower ℝ ℂ L] (hτ : IsCompactConjugation τ)

include hτ in
/-- **The Killing form of a real form against a compact conjugation is negative.** For a
conjugation `σ` and `X ≠ 0`, `Y` in the real form `Fix σ` with `Y = τ X`,
`B(X, Y) = B(X, τ X) = -H_τ(X, X) < 0`. -/
theorem killingForm_realForm_neg {σ : L →ₛₗ[starRingEnd ℂ] L} (hσ : IsLieConjugation σ)
    {x y : hσ.realForm} (hy : (y : L) = τ x) (hx : x ≠ 0) :
    killingForm ℝ hσ.realForm x y < 0 := by
  have hpos := hτ.pos x (by simpa using hx)
  rw [LinearMap.killingHermitianForm_def, ← hy, ← hσ.killingForm_realForm, ← Complex.ofReal_neg,
    Complex.zero_lt_real] at hpos
  linarith

/-- **The Killing form of a compact real form is negative definite.** For `X` in the real form,
`B(X, X) = -H_τ(X, X)`, and `H_τ` is positive definite. -/
theorem killingForm_realForm_self_neg (x : hτ.realForm) (hx : x ≠ 0) :
    killingForm ℝ hτ.realForm x x < 0 :=
  hτ.killingForm_realForm_neg hτ.toIsLieConjugation (hτ.apply_coe_realForm x).symm hx

end IsCompactConjugation

end TauCeti

namespace Module.Basis

variable {L ι : Type*} [LieRing L] [LieAlgebra ℂ L] (c : Module.Basis ι ℂ L)

/-- **The conjugation of the coordinates in a basis with real structure constants preserves
brackets.** -/
theorem isLieConjugation_coordConj (h : ∀ i j, c.coordConj ⁅c i, c j⁆ = ⁅c i, c j⁆) :
    TauCeti.IsLieConjugation c.coordConj.toLinearMap where
  map_lie x y := by
    have hx : x ∈ Submodule.span ℂ (Set.range c) := c.mem_span x
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hy : y ∈ Submodule.span ℂ (Set.range c) := c.mem_span y
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        rw [LinearEquiv.coe_coe, h, coordConj_self, coordConj_self]
      | zero => simp
      | add y y' _ _ hy hy' => rw [lie_add, map_add, hy, hy', map_add, lie_add]
      | smul a y _ hy => rw [lie_smul, LinearMap.map_smulₛₗ, hy, LinearMap.map_smulₛₗ, lie_smul]
    | zero => simp
    | add x x' _ _ hx hx' => rw [add_lie, map_add, hx, hx', map_add, add_lie]
    | smul a x _ hx => rw [smul_lie, LinearMap.map_smulₛₗ, hx, LinearMap.map_smulₛₗ, smul_lie]
  involutive := c.coordConj_coordConj

end Module.Basis
