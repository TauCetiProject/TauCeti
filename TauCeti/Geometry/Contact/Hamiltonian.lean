/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Contact Hamiltonian vector fields

Let `α` be a one-form on a manifold `M`, with Reeb vector field `R_α`. A vector field `X` is a
**contact Hamiltonian vector field** of a function `f : M → ℝ` when

`α(X) = f`, `ι_X dα = (R_α f) α - df`

(`TauCeti.SmoothForm.IsContactHamiltonianVectorField`). With these sign conventions, Cartan's
formula `L_X α = ι_X dα + d(ι_X α)` turns the two equations into

`L_X α = (R_α f) α`

(`TauCeti.SmoothForm.IsContactHamiltonianVectorField.mlieDerivForm_eq`), with no hypothesis on
`α` beyond smoothness. This is the infinitesimal form of the statement that the flow of `X`
rescales `α` by positive functions, so that it preserves the contact distribution `ξ = ker α`
together with its coorientation. Accordingly, the bracket of `X` with any vector field tangent to
`ξ` is again tangent to `ξ`
(`TauCeti.SmoothForm.IsContactHamiltonianVectorField.mlieBracket_mem_kerDistribution`).
Conversely, for a contact form, a differentiable vector field `X` with `L_X α = g α` for some
function `g` is the contact Hamiltonian vector field of `α(X)`
(`TauCeti.SmoothForm.IsContactForm.isContactHamiltonianVectorField_iff_mlieDerivForm`,
`TauCeti.SmoothForm.IsContactForm.eq_contactHamiltonianVectorField_of_mlieDerivForm_eq_smul`); then
necessarily `g = R_α(α(X))`
(`TauCeti.SmoothForm.IsContactForm.eq_mvfderiv_reebVectorField_of_mlieDerivForm_apply_eq_smul`).
So contact vector fields are determined by their Hamiltonians.

The two defining equations together say that the contact flat map `v ↦ ι_v dα + α(v) α` of
`TauCeti.SmoothForm.contactFlat` sends `X` to the covector `(f + R_α f) α - df`. For a contact
form on a finite-dimensional manifold the contact flat maps are invertible, so the **contact
Hamiltonian vector field** `X_f` (`TauCeti.SmoothForm.contactHamiltonianVectorField`), defined as
the inverse contact flat map applied to this covector, is the unique contact Hamiltonian vector
field of `f` (`TauCeti.SmoothForm.IsContactForm.isContactHamiltonianVectorField_iff_eq`). The
Hamiltonian of the Reeb vector field is the constant `1`: more generally `X_c = c R_α` for a
constant `c` (`TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_const`). The
contact Hamiltonian vector field of a `C^(n+1)` function is a `C^n` vector field
(`TauCeti.SmoothForm.IsContactForm.contMDiff_contactHamiltonianVectorField`), as is its Reeb
derivative `R_α f` (`TauCeti.SmoothForm.IsContactForm.contMDiff_mvfderiv_reebVectorField`).

Unlike a symplectic Hamiltonian, a contact Hamiltonian need not be conserved: along `X_f` it
changes by `df(X_f) = (R_α f) f`, so it is conserved exactly where `(R_α f) f = 0`
(`TauCeti.SmoothForm.IsContactHamiltonianVectorField.mvfderiv_apply_self`).
Since `α(X) = f`, a contact Hamiltonian vector field `X` of `f` is tangent to `ξ` exactly where `f`
vanishes (`TauCeti.SmoothForm.IsContactHamiltonianVectorField.mem_kerDistribution_iff`). For a
contact form, `X_f` vanishes exactly where `f` vanishes and `df` vanishes on `ξ`
(`TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_eq_zero_iff`).

## Main declarations

* `TauCeti.SmoothForm.IsContactHamiltonianVectorField`: the defining equations.
* `TauCeti.SmoothForm.contactHamiltonianVectorField`: the contact Hamiltonian vector field `X_f`.
* `TauCeti.SmoothForm.IsContactForm.isContactHamiltonianVectorField_iff_eq`: existence and
  uniqueness.
* `TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_eq_zero_iff`: the zeros of `X_f`.
* `TauCeti.SmoothForm.IsContactHamiltonianVectorField.contMDiff`: a contact Hamiltonian vector
  field of a `C^(n+1)` function is `C^n`.
* `TauCeti.SmoothForm.IsContactHamiltonianVectorField.mlieDerivForm_eq`: `L_X α = (R_α f) α`.
* `TauCeti.SmoothForm.IsContactHamiltonianVectorField.mlieBracket_mem_kerDistribution`:
  infinitesimal preservation of the contact distribution.
* `TauCeti.SmoothForm.mlieDerivForm_apply_eq_neg_apply_mlieBracket`: `L_X α (W) = -α([X, W])` at a
  point, for `W` tangent to `ker α` near that point.
* `TauCeti.SmoothForm.mlieDerivForm_apply_eq_of_eventuallyEq`,
  `TauCeti.SmoothForm.mlieBracket_mem_kerDistribution_of_eventuallyEq`: the same two statements at
  a point, for a vector field satisfying the defining equations only near that point.
* `TauCeti.SmoothForm.IsContactForm.isContactHamiltonianVectorField_iff_mlieDerivForm`,
  `TauCeti.SmoothForm.IsContactForm.eq_contactHamiltonianVectorField_of_mlieDerivForm_eq_smul`:
  contact vector fields are the contact Hamiltonian vector fields of their Hamiltonians.
* `TauCeti.SmoothForm.IsContactForm.eq_mvfderiv_reebVectorField_of_mlieDerivForm_apply_eq_smul`:
  the multiplier `g` in `L_X α = g α` is `R_α(α(X))`.
* `TauCeti.SmoothForm.contactFlat_apply_eq_smul_sub_mvfderiv_iff_of_isContactFormAt`,
  `TauCeti.SmoothForm.apply_contactHamiltonianVectorField_of_isContactFormAt`,
  `TauCeti.SmoothForm.mextDeriv_contactHamiltonianVectorField_left_of_isContactFormAt`,
  `TauCeti.SmoothForm.contMDiffAt_contactHamiltonianVectorField`,
  `TauCeti.SmoothForm.mlieBracket_contactHamiltonianVectorField_mem_kerDistribution`: the defining
  equations, regularity and preservation of `ker α` near points where `α` is contact, for a
  one-form which is a contact form only on an open set, such as a cut-off local contact form.

The construction of `X_f`, its linearity lemmas and its regularity proof are adapted from
`TauCeti.SmoothTwoForm.hamiltonianVectorField` in
`TauCeti.Geometry.Symplectic.Hamiltonian.Manifold`.

## References

* Hansjörg Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced
  Mathematics 109 (2008), Section 2.3.
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1} {f g : M → ℝ} {X : (x : M) → TangentSpace I x}

/-! ### The defining equations -/

/-- A vector field `X` is a **contact Hamiltonian vector field** of `f` for the one-form `α` when
`α(X) = f` and `ι_X dα = (R_α f) α - df`, where `R_α` is the Reeb vector field of `α`. -/
def IsContactHamiltonianVectorField (α : SmoothForm I M ℝ 1) (f : M → ℝ)
    (X : (x : M) → TangentSpace I x) : Prop :=
  ∀ x, α.val x ![X x] = f x ∧ ∀ v, mextDeriv α.val x ![X x, v] =
    mvfderiv I f x (α.reebVectorField x) * α.val x ![v] - mvfderiv I f x v

/-- The defining characterization of a contact Hamiltonian vector field. -/
theorem isContactHamiltonianVectorField_iff :
    α.IsContactHamiltonianVectorField f X ↔ ∀ x, α.val x ![X x] = f x ∧ ∀ v,
      mextDeriv α.val x ![X x, v] =
        mvfderiv I f x (α.reebVectorField x) * α.val x ![v] - mvfderiv I f x v :=
  Iff.rfl

/-! ### The defining equations near a point -/

section Pointwise

variable {x : M}

/-- **The Lie derivative of a one-form on a vector field tangent to its kernel.** If `W` is
differentiable at `x` and tangent to `ker α` near `x`, then `L_X α (W) = -α([X, W])` at `x`: the
derivative of `α(W)` vanishes there. -/
theorem mlieDerivForm_apply_eq_neg_apply_mlieBracket {W : (y : M) → TangentSpace I y}
    (hWd : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x)
    (hW : ∀ᶠ y in 𝓝 x, W y ∈ α.kerDistribution y) :
    mlieDerivForm X α.val x ![W x] = -α.val x ![mlieBracket I X W x] := by
  rw [mlieDerivForm_apply_one (α.mdifferentiableAt x) hWd,
    Filter.EventuallyEq.mvfderiv_eq (f := fun _ ↦ (0 : ℝ))
      (hW.mono fun y hy ↦ mem_kerDistribution.1 hy), mvfderiv_const, zero_apply, zero_sub]

/-- **Cartan's formula for a vector field satisfying the contact Hamiltonian equations at a
point.** If `α(X) = f` near `x`, `ι_X dα = (R_α f) α - df` at `x` and `X` is differentiable at `x`,
then `L_X α = (R_α f) α` at `x`. -/
theorem mlieDerivForm_apply_eq_of_eventuallyEq
    (hf : (fun y ↦ α.val y ![X y]) =ᶠ[𝓝 x] f) (hd : ∀ v, mextDeriv α.val x ![X x, v] =
      mvfderiv I f x (α.reebVectorField x) * α.val x ![v] - mvfderiv I f x v)
    (hXd : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x) :
    mlieDerivForm X α.val x = mvfderiv I f x (α.reebVectorField x) • α.val x := by
  ext v
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, by ext i; fin_cases i; rfl⟩
  rw [mlieDerivForm_apply_eq_mextDeriv_add (fun _ ↦ rfl) (α.mdifferentiableAt x) hXd,
    hf.mvfderiv_eq, hd, ContinuousAlternatingMap.smul_apply, smul_eq_mul, sub_add_cancel]

/-- **A vector field satisfying the contact Hamiltonian equations near a point preserves the
kernel there.** If `α(X) = f` near `x`, `ι_X dα = (R_α f) α - df` at `x` and `X` is differentiable
at `x`, then the bracket of `X` at `x` with a vector field differentiable at `x` and tangent to
`ker α` near `x` is tangent to `ker α` at `x`. -/
theorem mlieBracket_mem_kerDistribution_of_eventuallyEq
    (hf : (fun y ↦ α.val y ![X y]) =ᶠ[𝓝 x] f) (hd : ∀ v, mextDeriv α.val x ![X x, v] =
      mvfderiv I f x (α.reebVectorField x) * α.val x ![v] - mvfderiv I f x v)
    (hXd : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    {W : (y : M) → TangentSpace I y}
    (hWd : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x)
    (hW : ∀ᶠ y in 𝓝 x, W y ∈ α.kerDistribution y) :
    mlieBracket I X W x ∈ α.kerDistribution x := by
  -- `-α([X, W]) = L_X α (W) = (R_α f) α(W)`, where `α(W) = 0` at `x`.
  have h := mlieDerivForm_apply_eq_neg_apply_mlieBracket (X := X) hWd hW
  rw [mlieDerivForm_apply_eq_of_eventuallyEq hf hd hXd, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, mem_kerDistribution.1 hW.self_of_nhds, mul_zero, eq_comm, neg_eq_zero] at h
  exact mem_kerDistribution.2 h

end Pointwise

namespace IsContactHamiltonianVectorField

/-- A contact Hamiltonian vector field of `f` takes the value `f` under `α`. -/
theorem apply_eq (hX : α.IsContactHamiltonianVectorField f X) (x : M) : α.val x ![X x] = f x :=
  (hX x).1

/-- The contraction of `dα` with a contact Hamiltonian vector field of `f` is `(R_α f) α - df`. -/
theorem mextDeriv_apply_eq (hX : α.IsContactHamiltonianVectorField f X) (x : M)
    (v : TangentSpace I x) : mextDeriv α.val x ![X x, v] =
      mvfderiv I f x (α.reebVectorField x) * α.val x ![v] - mvfderiv I f x v :=
  (hX x).2 v

/-- A contact Hamiltonian vector field of `f` lies in the contact distribution exactly where `f`
vanishes. -/
theorem mem_kerDistribution_iff (hX : α.IsContactHamiltonianVectorField f X) (x : M) :
    X x ∈ α.kerDistribution x ↔ f x = 0 := by
  rw [mem_kerDistribution, hX.apply_eq]

/-- **A contact Hamiltonian need not be conserved**: along its contact Hamiltonian vector field it
changes by `df(X) = (R_α f) f`. -/
theorem mvfderiv_apply_self (hX : α.IsContactHamiltonianVectorField f X) (x : M) :
    mvfderiv I f x (X x) = mvfderiv I f x (α.reebVectorField x) * f x := by
  have h := hX.mextDeriv_apply_eq x (X x)
  rw [(mextDeriv α.val x).map_eq_zero_of_eq ![X x, X x] (i := 0) (j := 1) rfl (by decide),
    hX.apply_eq] at h
  linarith

/-- **Cartan's formula for a contact Hamiltonian vector field** at a point where it is
differentiable: `L_X α = (R_α f) α`. -/
theorem mlieDerivForm_apply_eq (hX : α.IsContactHamiltonianVectorField f X) {x : M}
    (hXd : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x) :
    mlieDerivForm X α.val x = mvfderiv I f x (α.reebVectorField x) • α.val x :=
  mlieDerivForm_apply_eq_of_eventuallyEq (Filter.Eventually.of_forall hX.apply_eq)
    (hX.mextDeriv_apply_eq x) hXd

/-- The derivative of `α(W)` along a contact Hamiltonian vector field `X` of `f`, from
`L_X α = (R_α f) α`: `X(α(W)) - α([X, W]) = (R_α f) α(W)`. -/
theorem mvfderiv_apply_sub_apply_mlieBracket {x : M}
    {W : (y : M) → TangentSpace I y} (hX : α.IsContactHamiltonianVectorField f X)
    (hXd : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x) :
    mvfderiv I (fun y ↦ α.val y ![W y]) x (X x) - α.val x ![mlieBracket I X W x] =
      mvfderiv I f x (α.reebVectorField x) * α.val x ![W x] := by
  have h := mlieDerivForm_apply_one (V := X) (α.mdifferentiableAt x) hW
  rw [hX.mlieDerivForm_apply_eq hXd, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h
  exact h.symm

/-- **Cartan's formula for a contact Hamiltonian vector field**: a differentiable contact
Hamiltonian vector field `X` of `f` satisfies `L_X α = (R_α f) α`. -/
theorem mlieDerivForm_eq (hX : α.IsContactHamiltonianVectorField f X)
    (hXd : MDifferentiable I I.tangent (fun y ↦ (X y : TangentBundle I M))) :
    mlieDerivForm X α.val = fun x ↦ mvfderiv I f x (α.reebVectorField x) • α.val x :=
  funext fun x ↦ hX.mlieDerivForm_apply_eq (hXd x)

/-- **A contact Hamiltonian vector field preserves the contact distribution** infinitesimally: its
bracket at `x` with a vector field tangent to `ξ = ker α` near `x` is again tangent to `ξ`. -/
theorem mlieBracket_mem_kerDistribution (hX : α.IsContactHamiltonianVectorField f X) {x : M}
    (hXd : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    {Y : (x : M) → TangentSpace I x}
    (hYd : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x)
    (hY : ∀ᶠ y in 𝓝 x, Y y ∈ α.kerDistribution y) :
    mlieBracket I X Y x ∈ α.kerDistribution x :=
  mlieBracket_mem_kerDistribution_of_eventuallyEq (Filter.Eventually.of_forall hX.apply_eq)
    (hX.mextDeriv_apply_eq x) hXd hYd hY

end IsContactHamiltonianVectorField

/-! ### The contact Hamiltonian vector field -/

/-- The **contact Hamiltonian vector field** `X_f` of a function `f`: the inverse contact flat map
applied to the covector `(f + R_α f) α - df`. For a contact form on a finite-dimensional manifold
it is the unique contact Hamiltonian vector field of `f`
(`TauCeti.SmoothForm.IsContactForm.isContactHamiltonianVectorField_iff_eq`); the inverse is
`ContinuousLinearMap.inverse`, so the field vanishes at points where the contact flat map is not
invertible. -/
def contactHamiltonianVectorField (α : SmoothForm I M ℝ 1) (f : M → ℝ) (x : M) :
    TangentSpace I x :=
  (α.contactFlat x).inverse
    ((f x + mvfderiv I f x (α.reebVectorField x)) • degreeOneEquiv α x - mvfderiv I f x)

/-- The contact Hamiltonian vector field unfolds as the inverse contact flat map applied to
`(f + R_α f) α - df`. -/
theorem contactHamiltonianVectorField_def (α : SmoothForm I M ℝ 1) (f : M → ℝ) (x : M) :
    α.contactHamiltonianVectorField f x = (α.contactFlat x).inverse
      ((f x + mvfderiv I f x (α.reebVectorField x)) • degreeOneEquiv α x - mvfderiv I f x) :=
  (rfl)

/-- The value at `x` of the contact Hamiltonian vector field of `f` only depends on the germ of `f`
at `x`. -/
theorem _root_.Filter.EventuallyEq.contactHamiltonianVectorField_eq (α : SmoothForm I M ℝ 1)
    {x : M} (h : f =ᶠ[𝓝 x] g) :
    α.contactHamiltonianVectorField f x = α.contactHamiltonianVectorField g x := by
  rw [contactHamiltonianVectorField_def, contactHamiltonianVectorField_def, h.eq_of_nhds,
    h.mvfderiv_eq]

/-- The contact Hamiltonian vector field of the zero function vanishes. -/
@[simp]
theorem contactHamiltonianVectorField_zero (α : SmoothForm I M ℝ 1) :
    α.contactHamiltonianVectorField 0 = 0 := by
  funext x
  simp [contactHamiltonianVectorField_def, mvfderiv_zero]

/-- A contact Hamiltonian with vanishing value and differential has a stationary vector field.
This follows from the inverse-flat construction even without contactness. -/
theorem contactHamiltonianVectorField_eq_zero_of_jet_eq_zero (α : SmoothForm I M ℝ 1)
    {x : M} (hf : f x = 0) (hdf : mvfderiv I f x = 0) :
    α.contactHamiltonianVectorField f x = 0 := by
  simp [contactHamiltonianVectorField_def, hf, hdf]

/-- The contact Hamiltonian vector field is additive on differentiable functions. -/
theorem contactHamiltonianVectorField_add {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    α.contactHamiltonianVectorField (f + g) x =
      α.contactHamiltonianVectorField f x + α.contactHamiltonianVectorField g x := by
  simp only [contactHamiltonianVectorField_def, mvfderiv_add hf hg, ← map_add]
  congr 1
  simp only [Pi.add_apply, add_apply]
  module

/-- The contact Hamiltonian vector field of `-f` is the opposite of that of `f`. -/
@[simp]
theorem contactHamiltonianVectorField_neg (x : M) :
    α.contactHamiltonianVectorField (-f) x = -α.contactHamiltonianVectorField f x := by
  simp only [contactHamiltonianVectorField_def, mvfderiv_neg, ← map_neg]
  congr 1
  simp only [Pi.neg_apply, neg_apply]
  module

/-- The contact Hamiltonian vector field commutes with multiplication by a real constant. -/
@[simp]
theorem contactHamiltonianVectorField_const_smul (c : ℝ) (x : M) :
    α.contactHamiltonianVectorField (c • f) x = c • α.contactHamiltonianVectorField f x := by
  simp only [contactHamiltonianVectorField_def, mvfderiv_const_smul_field, ← map_smul]
  congr 1
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
  module

/-! ### Points where the form is contact -/

section ContactPoint

variable [FiniteDimensional ℝ E] {x : M}

/-- At a point where `α` is a contact form, the contact flat map sends `v` to
`(f + R_α f) α - df` exactly when `v` satisfies the defining equations `α(v) = f` and
`ι_v dα = (R_α f) α - df` of a contact Hamiltonian vector field of `f` at that point. -/
theorem contactFlat_apply_eq_smul_sub_mvfderiv_iff_of_isContactFormAt
    (h : IsContactFormAt α.val x) (f : M → ℝ) (v : TangentSpace I x) :
    α.contactFlat x v =
        (f x + mvfderiv I f x (α.reebVectorField x)) • degreeOneEquiv α x - mvfderiv I f x ↔
      α.val x ![v] = f x ∧ ∀ w, mextDeriv α.val x ![v, w] =
        mvfderiv I f x (α.reebVectorField x) * α.val x ![w] - mvfderiv I f x w := by
  refine ⟨fun hv ↦ ?_, fun ⟨hf, hd⟩ ↦ ?_⟩
  · -- Evaluating at the Reeb vector recovers `α(v) = f`.
    have hR := DFunLike.congr_fun hv (α.reebVectorField x)
    simp only [contactFlat_apply, apply_reebVectorField_of_isContactFormAt h,
      mextDeriv_reebVectorField_right_of_isContactFormAt h, sub_apply, smul_apply,
      degreeOneEquiv_apply_apply_vec, smul_eq_mul] at hR
    have hf : α.val x ![v] = f x := by linarith
    refine ⟨hf, fun w ↦ ?_⟩
    have hw := DFunLike.congr_fun hv w
    simp only [contactFlat_apply, hf, sub_apply, smul_apply, degreeOneEquiv_apply_apply_vec,
      smul_eq_mul] at hw
    linarith
  · ext w
    simp only [contactFlat_apply, hf, hd, sub_apply, smul_apply, degreeOneEquiv_apply_apply_vec,
      smul_eq_mul]
    ring

/-- At a point where `α` is a contact form, the contact flat map sends the contact Hamiltonian
vector field of `f` to `(f + R_α f) α - df`. -/
theorem contactFlat_contactHamiltonianVectorField_of_isContactFormAt
    (h : IsContactFormAt α.val x) (f : M → ℝ) :
    α.contactFlat x (α.contactHamiltonianVectorField f x) =
      (f x + mvfderiv I f x (α.reebVectorField x)) • degreeOneEquiv α x - mvfderiv I f x :=
  (isInvertible_contactFlat_of_isContactFormAt h).self_apply_inverse _

/-- At a point where `α` is a contact form, `α` takes the value `f` on the contact Hamiltonian
vector field of `f`. -/
theorem apply_contactHamiltonianVectorField_of_isContactFormAt (h : IsContactFormAt α.val x)
    (f : M → ℝ) : α.val x ![α.contactHamiltonianVectorField f x] = f x :=
  ((contactFlat_apply_eq_smul_sub_mvfderiv_iff_of_isContactFormAt h f _).1
    (contactFlat_contactHamiltonianVectorField_of_isContactFormAt h f)).1

/-- At a point where `α` is a contact form, the contraction of `dα` with the contact Hamiltonian
vector field of `f` is `(R_α f) α - df`. -/
theorem mextDeriv_contactHamiltonianVectorField_left_of_isContactFormAt
    (h : IsContactFormAt α.val x) (f : M → ℝ) (v : TangentSpace I x) :
    mextDeriv α.val x ![α.contactHamiltonianVectorField f x, v] =
      mvfderiv I f x (α.reebVectorField x) * α.val x ![v] - mvfderiv I f x v :=
  ((contactFlat_apply_eq_smul_sub_mvfderiv_iff_of_isContactFormAt h f _).1
    (contactFlat_contactHamiltonianVectorField_of_isContactFormAt h f)).2 v

/-- **Local regularity of contact Hamiltonian vector fields.** If `α` is a contact form at every
point near `x`, the contact Hamiltonian vector field of a function which is `C^(n+1)` at `x` is
`C^n` at `x`, for `n ≤ ∞`. -/
theorem contMDiffAt_contactHamiltonianVectorField {n : WithTop ℕ∞} (hn : n ≤ ∞)
    (h : ∀ᶠ y in 𝓝 x, IsContactFormAt α.val y) (hf : ContMDiffAt I 𝓘(ℝ) (n + 1) f x) :
    ContMDiffAt I I.tangent n (T% (α.contactHamiltonianVectorField f)) x := by
  have hRf := (hf.contMDiffAt_mvfderiv_apply le_rfl).comp x
    ((contMDiffAt_reebVectorField h).of_le hn)
  have hcov : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n (fun y ↦
      TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun z : M ↦ TangentSpace I z →L[ℝ] ℝ) y
        ((f y + mvfderiv I f y (α.reebVectorField y)) • degreeOneEquiv α y - mvfderiv I f y)) x :=
    (((hf.of_le le_self_add).add hRf).smul_section
      (((degreeOneEquiv α).contMDiff x).of_le hn)).sub_section
        hf.contMDiffAt_totalSpaceMk_mvfderiv
  exact ((((contMDiff_contactFlat α) x).clm_bundle_inverse
    (isInvertible_contactFlat_of_isContactFormAt h.self_of_nhds)).of_le hn).clm_bundle_apply hcov

/-- **A contact Hamiltonian vector field preserves the kernel where the form is contact.** If `α`
is a contact form at every point near `x` and the contact Hamiltonian vector field `X_f` is
differentiable at `x`, then its bracket at `x` with a vector field differentiable at `x` and
tangent to `ker α` near `x` is tangent to `ker α` at `x`. -/
theorem mlieBracket_contactHamiltonianVectorField_mem_kerDistribution
    (h : ∀ᶠ y in 𝓝 x, IsContactFormAt α.val y)
    (hXd : MDifferentiableAt I I.tangent
      (fun y ↦ (α.contactHamiltonianVectorField f y : TangentBundle I M)) x)
    {W : (y : M) → TangentSpace I y}
    (hWd : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x)
    (hW : ∀ᶠ y in 𝓝 x, W y ∈ α.kerDistribution y) :
    mlieBracket I (α.contactHamiltonianVectorField f) W x ∈ α.kerDistribution x :=
  mlieBracket_mem_kerDistribution_of_eventuallyEq
    (h.mono fun _ hy ↦ apply_contactHamiltonianVectorField_of_isContactFormAt hy f)
    (mextDeriv_contactHamiltonianVectorField_left_of_isContactFormAt h.self_of_nhds f) hXd hWd hW

end ContactPoint

/-! ### Contact forms -/

namespace IsContactForm

variable [FiniteDimensional ℝ E] (hα : α.IsContactForm)
include hα

/-- A vector field is a contact Hamiltonian vector field of `f` exactly when the contact flat map
sends it to the covector `(f + R_α f) α - df`. -/
theorem isContactHamiltonianVectorField_iff_contactFlat :
    α.IsContactHamiltonianVectorField f X ↔ ∀ x, α.contactFlat x (X x) =
      (f x + mvfderiv I f x (α.reebVectorField x)) • degreeOneEquiv α x - mvfderiv I f x :=
  forall_congr' fun x ↦ (contactFlat_apply_eq_smul_sub_mvfderiv_iff_of_isContactFormAt
    (isContactForm_iff_forall_isContactFormAt.1 hα x) f (X x)).symm

/-- The contact flat map sends the contact Hamiltonian vector field of `f` to
`(f + R_α f) α - df`. -/
@[simp]
theorem contactFlat_contactHamiltonianVectorField (f : M → ℝ) (x : M) :
    α.contactFlat x (α.contactHamiltonianVectorField f x) =
      (f x + mvfderiv I f x (α.reebVectorField x)) • degreeOneEquiv α x - mvfderiv I f x :=
  contactFlat_contactHamiltonianVectorField_of_isContactFormAt
    (isContactForm_iff_forall_isContactFormAt.1 hα x) f

/-- The contact Hamiltonian vector field of `f` is a contact Hamiltonian vector field of `f`. -/
theorem isContactHamiltonianVectorField_contactHamiltonianVectorField (f : M → ℝ) :
    α.IsContactHamiltonianVectorField f (α.contactHamiltonianVectorField f) := fun x ↦
  have h := isContactForm_iff_forall_isContactFormAt.1 hα x
  ⟨apply_contactHamiltonianVectorField_of_isContactFormAt h f,
    mextDeriv_contactHamiltonianVectorField_left_of_isContactFormAt h f⟩

/-- A contact form takes the value `f` on the contact Hamiltonian vector field of `f`. -/
@[simp]
theorem apply_contactHamiltonianVectorField (f : M → ℝ) (x : M) :
    α.val x ![α.contactHamiltonianVectorField f x] = f x :=
  (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f).apply_eq x

/-- **Contraction of `dα` with the contact Hamiltonian vector field** of `f` is
`(R_α f) α - df`. -/
@[simp]
theorem mextDeriv_contactHamiltonianVectorField_left (f : M → ℝ) (x : M)
    (v : TangentSpace I x) : mextDeriv α.val x ![α.contactHamiltonianVectorField f x, v] =
      mvfderiv I f x (α.reebVectorField x) * α.val x ![v] - mvfderiv I f x v :=
  (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f).mextDeriv_apply_eq x v

/-- **Existence and uniqueness of contact Hamiltonian vector fields.** For a contact form on a
finite-dimensional manifold, `X_f` is the only contact Hamiltonian vector field of `f`. -/
theorem isContactHamiltonianVectorField_iff_eq :
    α.IsContactHamiltonianVectorField f X ↔ X = α.contactHamiltonianVectorField f := by
  refine ⟨fun hX ↦ funext fun x ↦ (hα.isInvertible_contactFlat x).injective ?_, fun hX ↦ hX ▸
    hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f⟩
  rw [hα.contactFlat_contactHamiltonianVectorField,
    hα.isContactHamiltonianVectorField_iff_contactFlat.1 hX x]

/-- A contact Hamiltonian vector field is characterized by its value under `α` and its
contraction equation tested only on the contact hyperplanes. -/
theorem isContactHamiltonianVectorField_iff_kerDistribution :
    α.IsContactHamiltonianVectorField f X ↔ ∀ x, α.val x ![X x] = f x ∧
      ∀ v ∈ α.kerDistribution x, mextDeriv α.val x ![X x, v] = -mvfderiv I f x v := by
  constructor
  · intro hX x
    refine ⟨hX.apply_eq x, fun v hv ↦ ?_⟩
    rw [hX.mextDeriv_apply_eq, mem_kerDistribution.1 hv, mul_zero, zero_sub]
  · intro hX x
    refine ⟨(hX x).1, fun v ↦ ?_⟩
    -- Subtract the Reeb component to test the equation on a vector in the contact plane.
    have h := (hX x).2 _ (hα.sub_smul_reebVectorField_mem_kerDistribution v)
    have hR := hα.mextDeriv_reebVectorField_right x (X x)
    rw [mextDeriv_eq_bilinFormAt] at hR
    simp only [mextDeriv_eq_bilinFormAt, map_sub, map_smul, hR,
      smul_eq_mul] at h ⊢
    linarith

/-- **Zeros of a contact Hamiltonian vector field.** For a contact form `α`, the contact
Hamiltonian vector field of `f` vanishes at `x` exactly when `f` vanishes at `x` and `df_x`
vanishes on the contact hyperplane `ξ_x = ker α_x`. -/
theorem contactHamiltonianVectorField_eq_zero_iff {x : M} :
    α.contactHamiltonianVectorField f x = 0 ↔
      f x = 0 ∧ ∀ v ∈ α.kerDistribution x, mvfderiv I f x v = 0 := by
  constructor
  · intro h
    have h1 := hα.apply_contactHamiltonianVectorField f x
    rw [h, (α.val x).map_coord_zero (m := ![0]) 0 rfl] at h1
    refine ⟨h1.symm, fun v hv ↦ ?_⟩
    have h2 := hα.mextDeriv_contactHamiltonianVectorField_left f x v
    rw [h, (mextDeriv α.val x).map_coord_zero (m := ![0, v]) 0 rfl, mem_kerDistribution.1 hv,
      mul_zero, zero_sub] at h2
    linarith
  · rintro ⟨h0, hξ⟩
    -- The covector `(f + R_α f) α - df` vanishes at `x`: on `v`, its value is the value of `df`
    -- on `v - α(v) R_α ∈ ξ_x`, up to sign.
    have hcov : (f x + mvfderiv I f x (α.reebVectorField x)) • degreeOneEquiv α x -
        mvfderiv I f x = 0 := by
      ext v
      have hv := hξ _ (hα.sub_smul_reebVectorField_mem_kerDistribution v)
      rw [map_sub, map_smul, smul_eq_mul] at hv
      simp only [_root_.sub_apply, _root_.smul_apply, degreeOneEquiv_apply_apply_vec, h0,
        smul_eq_mul, _root_.zero_apply]
      linear_combination -hv
    rw [contactHamiltonianVectorField_def, hcov, map_zero]

/-- The contact Hamiltonian vector field of a constant `c` is `c R_α`. -/
@[simp]
theorem contactHamiltonianVectorField_const (c : ℝ) :
    α.contactHamiltonianVectorField (fun _ ↦ c) = c • α.reebVectorField := by
  funext x
  refine (hα.isInvertible_contactFlat x).injective ?_
  rw [hα.contactFlat_contactHamiltonianVectorField, Pi.smul_apply, map_smul,
    hα.contactFlat_apply_eq_iff.2
      ⟨hα.apply_reebVectorField x, hα.mextDeriv_reebVectorField_left x⟩]
  simp [mvfderiv_const]

/-- **The Reeb vector field is the contact Hamiltonian vector field of the constant `1`.** -/
@[simp]
theorem contactHamiltonianVectorField_one :
    α.contactHamiltonianVectorField 1 = α.reebVectorField := by
  rw [Pi.one_def, hα.contactHamiltonianVectorField_const, one_smul]

/-- For a contact form on a finite-dimensional manifold, the derivative `R_α f` of a `C^(n+1)`
function along the Reeb vector field is `C^n`, for `n ≤ ∞`. -/
theorem contMDiff_mvfderiv_reebVectorField {n : WithTop ℕ∞} (hn : n ≤ ∞)
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f) :
    ContMDiff I 𝓘(ℝ) n fun x ↦ mvfderiv I f x (α.reebVectorField x) :=
  (hf.contMDiff_mvfderiv_apply le_rfl).comp (hα.contMDiff_reebVectorField.of_le hn)

/-- For a contact form on a finite-dimensional manifold, the derivative `R_α f` of a `C²` function
along the Reeb vector field is differentiable. -/
theorem mdifferentiable_mvfderiv_reebVectorField (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    MDifferentiable I 𝓘(ℝ) fun x ↦ mvfderiv I f x (α.reebVectorField x) :=
  (hα.contMDiff_mvfderiv_reebVectorField (n := 1) (by simp)
    (by norm_num [hf])).mdifferentiable one_ne_zero

/-- **Local regularity of contact Hamiltonian vector fields.** A Hamiltonian which is
`C^(n+1)` at a point has contact Hamiltonian field `C^n` there, for `n ≤ ∞`. -/
theorem contMDiffAt_contactHamiltonianVectorField {n : WithTop ℕ∞} (hn : n ≤ ∞)
    {x : M} (hf : ContMDiffAt I 𝓘(ℝ) (n + 1) f x) :
    ContMDiffAt I I.tangent n (T% (α.contactHamiltonianVectorField f)) x :=
  SmoothForm.contMDiffAt_contactHamiltonianVectorField hn
    (Filter.Eventually.of_forall (isContactForm_iff_forall_isContactFormAt.1 hα)) hf

/-- **Regularity of contact Hamiltonian vector fields.** For a contact form on a
finite-dimensional manifold, the contact Hamiltonian vector field of a `C^(n+1)` function is a
`C^n` vector field, for `n ≤ ∞`. -/
theorem contMDiff_contactHamiltonianVectorField {n : WithTop ℕ∞} (hn : n ≤ ∞)
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f) :
    ContMDiff I I.tangent n (T% (α.contactHamiltonianVectorField f)) :=
  fun x ↦ hα.contMDiffAt_contactHamiltonianVectorField hn (hf x)

/-- **Regularity of contact Hamiltonian vector fields.** For a contact form on a
finite-dimensional manifold, every contact Hamiltonian vector field of a `C^(n+1)` function is a
`C^n` vector field, for `n ≤ ∞`. -/
theorem _root_.TauCeti.SmoothForm.IsContactHamiltonianVectorField.contMDiff
    (hX : α.IsContactHamiltonianVectorField f X) {n : WithTop ℕ∞} (hn : n ≤ ∞)
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f) :
    ContMDiff I I.tangent n (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) := by
  rw [hα.isContactHamiltonianVectorField_iff_eq.1 hX]
  exact hα.contMDiff_contactHamiltonianVectorField hn hf

/-- The contact Hamiltonian vector field of a `C²` function is differentiable. -/
theorem mdifferentiable_contactHamiltonianVectorField (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    MDifferentiable I I.tangent
      (fun y ↦ (α.contactHamiltonianVectorField f y : TangentBundle I M)) :=
  (hα.contMDiff_contactHamiltonianVectorField (n := 1) (by simp)
    (by norm_num [hf])).mdifferentiable one_ne_zero

/-- **The multiplier of a contact vector field.** For a contact form `α` and a vector field `X`
differentiable at `x` with `α(X) = f`, if `L_X α = c α` at `x`, then `c = R_α f` at `x`. -/
theorem eq_mvfderiv_reebVectorField_of_mlieDerivForm_apply_eq_smul
    (hf : ∀ y, α.val y ![X y] = f y) {x : M}
    (hXd : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x) {c : ℝ}
    (hc : mlieDerivForm X α.val x = c • α.val x) :
    c = mvfderiv I f x (α.reebVectorField x) := by
  -- Evaluate Cartan's formula `L_X α = ι_X dα + df` at the Reeb vector field.
  have h := mlieDerivForm_apply_eq_mextDeriv_add hf (α.mdifferentiableAt x) hXd
    (α.reebVectorField x)
  rwa [hc, ContinuousAlternatingMap.smul_apply, smul_eq_mul, hα.apply_reebVectorField,
    hα.mextDeriv_reebVectorField_right, mul_one, zero_add] at h

/-- **Contact vector fields are contact Hamiltonian vector fields.** For a contact form `α` and a
differentiable vector field `X`, `X` is a contact Hamiltonian vector field of `f` exactly when
`α(X) = f` and the Lie derivative `L_X α` is a multiple `g α` of `α` by some function `g`. The
multiplier is then `g = R_α f`
(`TauCeti.SmoothForm.IsContactForm.eq_mvfderiv_reebVectorField_of_mlieDerivForm_apply_eq_smul`). -/
theorem isContactHamiltonianVectorField_iff_mlieDerivForm
    (hXd : MDifferentiable I I.tangent (fun y ↦ (X y : TangentBundle I M))) :
    α.IsContactHamiltonianVectorField f X ↔ (∀ x, α.val x ![X x] = f x) ∧
      ∃ g : M → ℝ, mlieDerivForm X α.val = fun x ↦ g x • α.val x := by
  refine ⟨fun hX ↦ ⟨hX.apply_eq, _, hX.mlieDerivForm_eq hXd⟩,
    fun ⟨hf, g, hg⟩ x ↦ ⟨hf x, fun v ↦ ?_⟩⟩
  -- Cartan's formula: `g α = ι_X dα + df`.
  have key : ∀ v, g x * α.val x ![v] = mextDeriv α.val x ![X x, v] + mvfderiv I f x v := fun v ↦ by
    rw [← mlieDerivForm_apply_eq_mextDeriv_add hf (α.mdifferentiableAt x) (hXd x), hg,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [← hα.eq_mvfderiv_reebVectorField_of_mlieDerivForm_apply_eq_smul hf (hXd x) (congrFun hg x)]
  linarith [key v]

/-- **A contact vector field is the contact Hamiltonian vector field of its Hamiltonian.** For a
contact form `α`, a differentiable vector field `X` whose Lie derivative `L_X α` is a multiple of
`α` is the contact Hamiltonian vector field of `α(X)`. -/
theorem eq_contactHamiltonianVectorField_of_mlieDerivForm_eq_smul
    (hXd : MDifferentiable I I.tangent (fun y ↦ (X y : TangentBundle I M))) {g : M → ℝ}
    (hg : mlieDerivForm X α.val = fun x ↦ g x • α.val x) :
    X = α.contactHamiltonianVectorField fun x ↦ α.val x ![X x] :=
  hα.isContactHamiltonianVectorField_iff_eq.1
    ((hα.isContactHamiltonianVectorField_iff_mlieDerivForm hXd).2 ⟨fun _ ↦ rfl, g, hg⟩)

end IsContactForm

end SmoothForm

end TauCeti
