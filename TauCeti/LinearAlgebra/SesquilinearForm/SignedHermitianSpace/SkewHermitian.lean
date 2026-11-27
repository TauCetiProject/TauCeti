/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Isometry
import TauCeti.FieldTheory.Galois.Trace

/-!
# Skew-hermitian forms: rescaling to hermitian forms and trace forms

Let `K` be a commutative ring with an involution `σ`. This file relates signed hermitian spaces of
the two signs, and attaches an alternating form to a skew-hermitian one.

**Rescaling.** For a unit `c` of `K` with `σ c = ε' ε c`, multiplying an `ε`-hermitian form by
`c` gives an `ε'`-hermitian form (`TauCeti.SignedHermitianSpace.unitsSMul`). For a trace-zero unit
`δ` of a quadratic algebra (`σ δ = -δ`) this is the passage `w ↦ δ⁻¹ w` from skew-hermitian to
hermitian forms, and `h ↦ δ h` back. Rescaling is a bijection
(`TauCeti.SignedHermitianSpace.unitsSMulEquiv`), compatible with isometries, orthogonal sums and
unitary groups, so classifications of hermitian spaces transfer to skew-hermitian ones.

**Trace forms.** Let `K` be an algebra over a commutative ring `F` whose image `σ` fixes, let `V`
be a `K`-module with compatible `F`-module structure, and let `t : K → F` be `F`-linear (for
example the trace of a quadratic étale algebra). For a signed hermitian form `h` on `V`, `t ∘ h` is
an `F`-bilinear form on `V` (`TauCeti.SignedHermitianSpace.traceForm`), preserved by the unitary
group of `h`. If `t` vanishes on the elements negated by `σ` and `h` is skew-hermitian, `t ∘ h` is
alternating, not merely skew-symmetric. If `t` is invariant under `σ` and the pairing
`(a, b) ↦ t (a b)` on `K` is nondegenerate, `t ∘ h` is nondegenerate, for either sign. Under all
three conditions, the unitary group of a skew-hermitian space lies in the symplectic group of its
trace form. For a Galois extension of
fields `K/F` and `τ ≠ 1`, the trace form of a skew-hermitian form for `τ` is alternating, because
a nonzero such space forces `τ` to have order two
(`TauCeti.SignedHermitianSpace.isAlt_traceForm_trace`). For a finite separable `K/F` it is
nondegenerate for any `τ` and either sign
(`TauCeti.SignedHermitianSpace.nondegenerate_traceForm_trace`).

## Main definitions

* `TauCeti.SignedHermitianSpace.unitsSMul H c hc`: the form `c h`, of sign `ε'`, for a unit `c` with
  `σ c = ε' ε c`.
* `TauCeti.SignedHermitianSpace.unitsSMulEquiv c hc`: rescaling by `c` as a bijection from
  `ε`-hermitian to `ε'`-hermitian forms, with inverse rescaling by `c⁻¹`.
* `TauCeti.SignedHermitianSpace.traceForm H t hσ`: the `F`-bilinear form `t ∘ h`.

## Main statements

* `TauCeti.SignedHermitianSpace.unitsSMul_unitsSMul`: rescaling by `c` and then by `d` is
  rescaling by `d c`.
* `TauCeti.SignedHermitianSpace.equivalent_unitsSMul_iff`,
  `TauCeti.SignedHermitianSpace.unitsSMul_prod`,
  `TauCeti.SignedHermitianSpace.isometryGroup_unitsSMul`: rescaling preserves isometry classes,
  orthogonal sums and the unitary group.
* `TauCeti.SignedHermitianSpace.isAlt_traceForm`: the trace form of a skew-hermitian form is
  alternating when `t` vanishes on the elements negated by `σ`, in every characteristic.
* `TauCeti.SignedHermitianSpace.nondegenerate_traceForm`: the trace form of a signed hermitian
  form is nondegenerate when `t` is `σ`-invariant and the trace pairing of `K` is nondegenerate.
* `TauCeti.SignedHermitianSpace.restrictScalars_mem_isometryGroup_traceForm`: the unitary group
  preserves the trace form.
* `TauCeti.SignedHermitianSpace.isAlt_traceForm_trace`,
  `TauCeti.SignedHermitianSpace.nondegenerate_traceForm_trace`: for a Galois extension of fields
  and `τ ≠ 1`, the trace form of a skew-hermitian form is alternating; for a finite separable
  extension it is nondegenerate, for any automorphism and sign.

## References

* W. Scharlau, *Quadratic and Hermitian Forms*, Grundlehren 270, Springer (1985), Chapter 7, §1.
-/

public section

open Module

namespace TauCeti

namespace SignedHermitianSpace

variable {K V V₁ V₂ : Type*} [CommRing K] {σ : K →+* K} {ε ε' : ℤˣ}
  [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

/-! ### Rescaling by a unit -/

/-- If `σ c = ε' ε c` for a unit `c`, then `σ c⁻¹ = ε ε' c⁻¹`. -/
theorem map_units_inv_eq_smul {c : Kˣ} (hc : σ c = (ε' * ε) • (c : K)) :
    σ ↑c⁻¹ = (ε * ε') • (↑c⁻¹ : K) := by
  rw [mul_comm ε]
  refine left_inv_eq_right_inv (a := σ c) ?_ ?_
  · simp [← map_mul]
  · simp [hc, smul_mul_smul_comm]

/-- If `σ c = ε' ε c` and `σ d = ε'' ε' d` for units `c` and `d`, then `σ (d c) = ε'' ε (d c)`. -/
theorem map_units_mul_eq_smul {ε'' : ℤˣ} {c d : Kˣ} (hc : σ c = (ε' * ε) • (c : K))
    (hd : σ d = (ε'' * ε') • (d : K)) : σ ↑(d * c) = (ε'' * ε) • (↑(d * c) : K) := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl <;>
    rcases Int.units_eq_one_or ε'' with rfl | rfl <;> simp_all

/-- **Rescaling** an `ε`-hermitian form `h` by a unit `c` with `σ c = ε' ε c`: the form `c h` is
`ε'`-hermitian. For `σ δ = -δ`, rescaling by `δ⁻¹` turns skew-hermitian forms into hermitian
ones, and rescaling by `δ` turns them back. -/
def unitsSMul (H : SignedHermitianSpace K V σ ε) (c : Kˣ) (hc : σ c = (ε' * ε) • (c : K)) :
    SignedHermitianSpace K V σ ε' where
  form := (c : K) • H.form
  form_swap v w := by
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, hc, H.form_swap v w]
    rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl <;>
      simp
  separatingLeft v hv := H.separatingLeft v fun w ↦ (Units.mul_right_eq_zero c).1 (hv w)

@[simp]
theorem unitsSMul_form_apply (H : SignedHermitianSpace K V σ ε) (c : Kˣ)
    (hc : σ c = (ε' * ε) • (c : K)) (x y : V) :
    (H.unitsSMul c hc).form x y = c * H.form x y :=
  (rfl)

/-- Rescaling by `1` does nothing. -/
@[simp]
theorem unitsSMul_one (H : SignedHermitianSpace K V σ ε)
    (h : σ ((1 : Kˣ) : K) = (ε * ε) • ((1 : Kˣ) : K)) : H.unitsSMul 1 h = H := by
  ext x y
  simp

/-- Rescaling by `c` and then by `d` is rescaling by `d c`. In particular, replacing the
trace-zero unit `δ` by `a δ` multiplies the rescaled form `δ⁻¹ w` by `a⁻¹`. -/
@[simp]
theorem unitsSMul_unitsSMul {ε'' : ℤˣ} (H : SignedHermitianSpace K V σ ε) (c d : Kˣ)
    (hc : σ c = (ε' * ε) • (c : K)) (hd : σ d = (ε'' * ε') • (d : K)) :
    (H.unitsSMul c hc).unitsSMul d hd = H.unitsSMul (d * c) (map_units_mul_eq_smul hc hd) := by
  ext x y
  simp [mul_assoc]

/-- Rescaling by `c` and then by `c⁻¹` returns the original form. -/
theorem unitsSMul_unitsSMul_inv (H : SignedHermitianSpace K V σ ε) (c : Kˣ)
    (hc : σ c = (ε' * ε) • (c : K)) :
    (H.unitsSMul c hc).unitsSMul c⁻¹ (map_units_inv_eq_smul hc) = H := by
  ext x y
  simp

/-- Rescaling by `c⁻¹` and then by `c` returns the original form. -/
theorem unitsSMul_inv_unitsSMul (H : SignedHermitianSpace K V σ ε') (c : Kˣ)
    (hc : σ c = (ε' * ε) • (c : K)) :
    (H.unitsSMul c⁻¹ (map_units_inv_eq_smul hc)).unitsSMul c hc = H := by
  ext x y
  simp

variable (V) in
/-- Rescaling by a unit `c` with `σ c = ε' ε c`, as a bijection from `ε`-hermitian to
`ε'`-hermitian forms on `V`; its inverse is rescaling by `c⁻¹`. -/
def unitsSMulEquiv (c : Kˣ) (hc : σ c = (ε' * ε) • (c : K)) :
    SignedHermitianSpace K V σ ε ≃ SignedHermitianSpace K V σ ε' where
  toFun H := H.unitsSMul c hc
  invFun H := H.unitsSMul c⁻¹ (map_units_inv_eq_smul hc)
  left_inv H := unitsSMul_unitsSMul_inv H c hc
  right_inv H := unitsSMul_inv_unitsSMul H c hc

@[simp]
theorem unitsSMulEquiv_apply (c : Kˣ) (hc : σ c = (ε' * ε) • (c : K))
    (H : SignedHermitianSpace K V σ ε) : unitsSMulEquiv V c hc H = H.unitsSMul c hc :=
  (rfl)

@[simp]
theorem unitsSMulEquiv_symm_apply (c : Kˣ) (hc : σ c = (ε' * ε) • (c : K))
    (H : SignedHermitianSpace K V σ ε') :
    (unitsSMulEquiv V c hc).symm H = H.unitsSMul c⁻¹ (map_units_inv_eq_smul hc) :=
  (rfl)

/-- An isometric equivalence stays one after both forms are rescaled by the same unit. -/
def IsometryEquiv.unitsSMul {H₁ : SignedHermitianSpace K V₁ σ ε}
    {H₂ : SignedHermitianSpace K V₂ σ ε} (f : IsometryEquiv H₁ H₂) (c : Kˣ)
    (hc : σ c = (ε' * ε) • (c : K)) : IsometryEquiv (H₁.unitsSMul c hc) (H₂.unitsSMul c hc) where
  toLinearEquiv := f.toLinearEquiv
  map_app' x y := congrArg ((c : K) * ·) (f.map_app x y)

@[simp]
theorem IsometryEquiv.unitsSMul_apply {H₁ : SignedHermitianSpace K V₁ σ ε}
    {H₂ : SignedHermitianSpace K V₂ σ ε} (f : IsometryEquiv H₁ H₂) (c : Kˣ)
    (hc : σ c = (ε' * ε) • (c : K)) (x : V₁) : f.unitsSMul c hc x = f x :=
  (rfl)

/-- Rescaling by a unit preserves and reflects isometry classes. -/
theorem equivalent_unitsSMul_iff {H₁ : SignedHermitianSpace K V₁ σ ε}
    {H₂ : SignedHermitianSpace K V₂ σ ε} (c : Kˣ) (hc : σ c = (ε' * ε) • (c : K)) :
    Equivalent (H₁.unitsSMul c hc) (H₂.unitsSMul c hc) ↔ Equivalent H₁ H₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ (h.nonempty.some.unitsSMul c hc).equivalent⟩
  have g := h.nonempty.some.unitsSMul c⁻¹ (map_units_inv_eq_smul hc)
  rw [unitsSMul_unitsSMul_inv, unitsSMul_unitsSMul_inv] at g
  exact g.equivalent

/-- Rescaling commutes with orthogonal sums. -/
theorem unitsSMul_prod (H₁ : SignedHermitianSpace K V₁ σ ε) (H₂ : SignedHermitianSpace K V₂ σ ε)
    (c : Kˣ) (hc : σ c = (ε' * ε) • (c : K)) :
    (H₁.prod H₂).unitsSMul c hc = (H₁.unitsSMul c hc).prod (H₂.unitsSMul c hc) :=
  SignedHermitianSpace.ext <| LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ by simp [mul_add]

/-- Rescaling by a unit does not change the unitary group. -/
@[simp]
theorem isometryGroup_unitsSMul (H : SignedHermitianSpace K V σ ε) (c : Kˣ)
    (hc : σ c = (ε' * ε) • (c : K)) :
    (H.unitsSMul c hc).form.isometryGroup = H.form.isometryGroup := by
  ext e
  simp

/-! ### Trace forms -/

section Trace

variable {F : Type*} [CommRing F] [Algebra F K] [Module F V] [IsScalarTower F K V]

/-- The **trace form** `t ∘ h` of a signed hermitian form `h`, for an `F`-linear `t : K → F` and an
involution `σ` fixing the image of `F`: the `F`-bilinear form `(x, y) ↦ t (h x y)` on the
underlying `F`-module of `V`. For a skew-hermitian `h` it is alternating when `t` vanishes on the
elements negated by `σ` (`TauCeti.SignedHermitianSpace.isAlt_traceForm`). For either sign it is
nondegenerate when `t` is invariant under `σ` and the pairing `(a, b) ↦ t (a b)` on `K` is
nondegenerate (`TauCeti.SignedHermitianSpace.nondegenerate_traceForm`). -/
def traceForm (H : SignedHermitianSpace K V σ ε) (t : K →ₗ[F] F)
    (hσ : ∀ a : F, σ (algebraMap F K a) = algebraMap F K a) : LinearMap.BilinForm F V :=
  LinearMap.mk₂ F (fun x y ↦ t (H.form x y))
    (fun x x' y ↦ by simp)
    (fun a x y ↦ by
      simpa [hσ, -smul_eq_mul] using
        congrArg t (LinearMap.congr_fun (H.form.map_smulₛₗ (algebraMap F K a) x) y))
    (fun x y y' ↦ by simp)
    (fun a x y ↦ by simp)

variable (H : SignedHermitianSpace K V σ ε) (t : K →ₗ[F] F)
  (hσ : ∀ a : F, σ (algebraMap F K a) = algebraMap F K a)

@[simp]
theorem traceForm_apply (x y : V) : H.traceForm t hσ x y = t (H.form x y) :=
  (rfl)

/-- The trace form of a skew-hermitian form is **alternating** as soon as `t` vanishes on the
elements negated by `σ`. In characteristic two this is stronger than skew-symmetry. -/
theorem isAlt_traceForm (H : SignedHermitianSpace K V σ (-1)) (ht : ∀ b, σ b = -b → t b = 0) :
    (H.traceForm t hσ).IsAlt := fun x ↦ ht _ <| by
  rw [H.apply_form_self, Units.neg_smul, one_smul]

/-- The trace form of a signed hermitian form is reflexive when `t` is invariant under `σ`. -/
theorem isRefl_traceForm (ht : ∀ b, t (σ b) = t b) : (H.traceForm t hσ).IsRefl := fun x y hxy ↦ by
  simpa [H.form_swap x y, ht] using congrArg (ε • ·) hxy

/-- The trace form separates on the left when the pairing `(a, b) ↦ t (a b)` on `K` does. -/
theorem separatingLeft_traceForm (hnd : ∀ b, (∀ a, t (a * b) = 0) → b = 0) :
    (H.traceForm t hσ).SeparatingLeft := fun x hx ↦
  H.separatingLeft x fun y ↦ hnd _ fun a ↦ by simpa using hx (a • y)

/-- The trace form of a signed hermitian form, of either sign, is **nondegenerate** when `t` is
invariant under `σ` and the pairing `(a, b) ↦ t (a b)` on `K` is nondegenerate. -/
theorem nondegenerate_traceForm (ht : ∀ b, t (σ b) = t b)
    (hnd : ∀ b, (∀ a, t (a * b) = 0) → b = 0) : (H.traceForm t hσ).Nondegenerate :=
  (H.isRefl_traceForm t hσ ht).nondegenerate_iff_separatingLeft.2
    (H.separatingLeft_traceForm t hσ hnd)

/-- The unitary group of `h` preserves its trace form `t ∘ h`. For a skew-hermitian `h`, this places
it in the symplectic group of `t ∘ h` when `t` satisfies the hypotheses of
`TauCeti.SignedHermitianSpace.isAlt_traceForm` and
`TauCeti.SignedHermitianSpace.nondegenerate_traceForm`. -/
theorem restrictScalars_mem_isometryGroup_traceForm {e : V ≃ₗ[K] V}
    (he : e ∈ H.form.isometryGroup) :
    e.restrictScalars F ∈ (H.traceForm t hσ).isometryGroup :=
  LinearMap.mem_isometryGroup_iff.2 fun x y ↦
    congrArg t (LinearMap.mem_isometryGroup_iff.1 he x y)

end Trace

section GaloisTrace

variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]

/-- For a Galois extension of fields `K/F` and an automorphism `τ ≠ 1`, the trace form
`Tr_{K/F} ∘ w` of a skew-hermitian form `w` for `τ` is alternating. On a nonzero space `τ` has
order two (`TauCeti.SignedHermitianSpace.map_map_eq_of_nontrivial`), so the trace vanishes on the
elements negated by `τ`. -/
theorem isAlt_traceForm_trace [IsGalois F K] {τ : Gal(K/F)} (hτ : τ ≠ 1)
    (H : SignedHermitianSpace K V (τ : K →+* K) (-1)) :
    (H.traceForm (Algebra.trace F K) fun a ↦ τ.commutes a).IsAlt := by
  cases subsingleton_or_nontrivial V with
  | inl _ => exact fun x ↦ by simp [Subsingleton.elim x 0]
  | inr _ =>
    exact H.isAlt_traceForm _ _ fun _ ↦ Algebra.trace_eq_zero_of_apply_eq_neg hτ
      (AlgEquiv.ext H.map_map_eq_of_nontrivial)

/-- For a finite separable extension of fields `K/F` and any automorphism `τ`, the trace form
`Tr_{K/F} ∘ h` of a signed hermitian form `h` for `τ` is nondegenerate: it is reflexive since the
trace is invariant under `τ`, and separating since the trace pairing of `K/F` is. -/
theorem nondegenerate_traceForm_trace [FiniteDimensional F K] [Algebra.IsSeparable F K]
    {τ : Gal(K/F)} (H : SignedHermitianSpace K V (τ : K →+* K) ε) :
    (H.traceForm (Algebra.trace F K) fun a ↦ τ.commutes a).Nondegenerate :=
  H.nondegenerate_traceForm _ _ (Algebra.trace_eq_of_algEquiv τ) fun b hb ↦
    (traceForm_nondegenerate F K).2 b fun a ↦ by simpa using hb a

end GaloisTrace

end SignedHermitianSpace

end TauCeti
