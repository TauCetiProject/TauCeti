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
(`TauCeti.SmoothForm.IsContactForm.contMDiff_contactHamiltonianVectorField`).

Unlike a symplectic Hamiltonian, a contact Hamiltonian is not conserved: along `X_f` it changes by
`df(X_f) = (R_α f) f` (`TauCeti.SmoothForm.IsContactHamiltonianVectorField.mvfderiv_apply_self`).
In particular `X_f` is tangent to `ξ` exactly where `f` vanishes.

## Main declarations

* `TauCeti.SmoothForm.IsContactHamiltonianVectorField`: the defining equations.
* `TauCeti.SmoothForm.contactHamiltonianVectorField`: the contact Hamiltonian vector field `X_f`.
* `TauCeti.SmoothForm.IsContactForm.isContactHamiltonianVectorField_iff_eq`: existence and
  uniqueness.
* `TauCeti.SmoothForm.IsContactHamiltonianVectorField.mlieDerivForm_eq`: `L_X α = (R_α f) α`.
* `TauCeti.SmoothForm.IsContactHamiltonianVectorField.mlieBracket_mem_kerDistribution`:
  infinitesimal preservation of the contact distribution.
* `TauCeti.SmoothForm.IsContactForm.isContactHamiltonianVectorField_iff_mlieDerivForm`,
  `TauCeti.SmoothForm.IsContactForm.eq_contactHamiltonianVectorField_of_mlieDerivForm_eq_smul`:
  contact vector fields are the contact Hamiltonian vector fields of their Hamiltonians.
* `TauCeti.SmoothForm.IsContactForm.eq_mvfderiv_reebVectorField_of_mlieDerivForm_apply_eq_smul`:
  the multiplier `g` in `L_X α = g α` is `R_α(α(X))`.

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
open scoped ContDiff Manifold

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
  ∀ x, α.1 x ![X x] = f x ∧ ∀ v, mextDeriv α.1 x ![X x, v] =
    mvfderiv I f x (α.reebVectorField x) * α.1 x ![v] - mvfderiv I f x v

/-- The defining characterization of a contact Hamiltonian vector field. -/
theorem isContactHamiltonianVectorField_iff :
    α.IsContactHamiltonianVectorField f X ↔ ∀ x, α.1 x ![X x] = f x ∧ ∀ v,
      mextDeriv α.1 x ![X x, v] =
        mvfderiv I f x (α.reebVectorField x) * α.1 x ![v] - mvfderiv I f x v :=
  Iff.rfl

namespace IsContactHamiltonianVectorField

/-- A contact Hamiltonian vector field of `f` takes the value `f` under `α`. -/
theorem apply_eq (hX : α.IsContactHamiltonianVectorField f X) (x : M) : α.1 x ![X x] = f x :=
  (hX x).1

/-- The contraction of `dα` with a contact Hamiltonian vector field of `f` is `(R_α f) α - df`. -/
theorem mextDeriv_apply_eq (hX : α.IsContactHamiltonianVectorField f X) (x : M)
    (v : TangentSpace I x) : mextDeriv α.1 x ![X x, v] =
      mvfderiv I f x (α.reebVectorField x) * α.1 x ![v] - mvfderiv I f x v :=
  (hX x).2 v

/-- A contact Hamiltonian vector field of `f` lies in the contact distribution exactly where `f`
vanishes. -/
theorem mem_kerDistribution_iff (hX : α.IsContactHamiltonianVectorField f X) (x : M) :
    X x ∈ α.kerDistribution x ↔ f x = 0 := by
  rw [mem_kerDistribution, hX.apply_eq]

/-- **A contact Hamiltonian is not conserved**: along its contact Hamiltonian vector field it
changes by `df(X) = (R_α f) f`. -/
theorem mvfderiv_apply_self (hX : α.IsContactHamiltonianVectorField f X) (x : M) :
    mvfderiv I f x (X x) = mvfderiv I f x (α.reebVectorField x) * f x := by
  have h := hX.mextDeriv_apply_eq x (X x)
  rw [(mextDeriv α.1 x).map_eq_zero_of_eq ![X x, X x] (i := 0) (j := 1) rfl (by decide),
    hX.apply_eq] at h
  linarith

/-- **Cartan's formula for a contact Hamiltonian vector field** at a point where it is
differentiable: `L_X α = (R_α f) α`. -/
theorem mlieDerivForm_apply_eq (hX : α.IsContactHamiltonianVectorField f X) {x : M}
    (hXd : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x) :
    mlieDerivForm X α.1 x = mvfderiv I f x (α.reebVectorField x) • α.1 x := by
  ext v
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, by ext i; fin_cases i; rfl⟩
  rw [mlieDerivForm_apply_eq_mextDeriv_add hX.apply_eq (α.mdifferentiableAt x) hXd,
    hX.mextDeriv_apply_eq, ContinuousAlternatingMap.smul_apply, smul_eq_mul, sub_add_cancel]

/-- **Cartan's formula for a contact Hamiltonian vector field**: a differentiable contact
Hamiltonian vector field `X` of `f` satisfies `L_X α = (R_α f) α`. -/
theorem mlieDerivForm_eq (hX : α.IsContactHamiltonianVectorField f X)
    (hXd : MDifferentiable I I.tangent (fun y ↦ (X y : TangentBundle I M))) :
    mlieDerivForm X α.1 = fun x ↦ mvfderiv I f x (α.reebVectorField x) • α.1 x :=
  funext fun x ↦ hX.mlieDerivForm_apply_eq (hXd x)

/-- **A contact Hamiltonian vector field preserves the contact distribution** infinitesimally: its
bracket with a vector field tangent to `ξ = ker α` is again tangent to `ξ`. -/
theorem mlieBracket_mem_kerDistribution (hX : α.IsContactHamiltonianVectorField f X) {x : M}
    (hXd : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    {Y : (x : M) → TangentSpace I x}
    (hYd : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x)
    (hY : ∀ y, Y y ∈ α.kerDistribution y) : mlieBracket I X Y x ∈ α.kerDistribution x := by
  -- The bracket formula `(L_X α)(Y) = X(α(Y)) - α([X, Y])`, where `α(Y) = 0` identically and
  -- `(L_X α)(Y) = (R_α f) α(Y) = 0`.
  have h := mlieDerivForm_apply_vectorField (V := X) (X := fun _ ↦ Y) (α.mdifferentiableAt x)
    (fun _ ↦ hYd)
  have hY' : ∀ y, α.1 y (fun _ ↦ Y y) = 0 := fun y ↦ by
    rw [← Matrix.vec_single_eq_const, ← mem_kerDistribution]
    exact hY y
  have hupd : Function.update (fun _ : Fin 1 ↦ Y x) 0 (mlieBracket I X Y x) =
      ![mlieBracket I X Y x] := by
    rw [Function.update_eq_const_of_subsingleton, Matrix.vec_single_eq_const]
    rfl
  have hd : mvfderiv I (fun y ↦ α.1 y (fun _ ↦ Y y)) x = 0 := by
    rw [funext hY']
    exact mvfderiv_const (0 : ℝ)
  rw [hX.mlieDerivForm_apply_eq hXd, ContinuousAlternatingMap.smul_apply, hY', smul_zero, hd,
    zero_apply, zero_sub, Fin.sum_univ_one, hupd, zero_eq_neg] at h
  exact mem_kerDistribution.2 h

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

/-- The contact Hamiltonian vector field of the zero function vanishes. -/
@[simp]
theorem contactHamiltonianVectorField_zero (α : SmoothForm I M ℝ 1) :
    α.contactHamiltonianVectorField 0 = 0 := by
  funext x
  simp [contactHamiltonianVectorField_def, mvfderiv_zero]

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
theorem contactHamiltonianVectorField_const_smul (c : ℝ) (x : M) :
    α.contactHamiltonianVectorField (c • f) x = c • α.contactHamiltonianVectorField f x := by
  simp only [contactHamiltonianVectorField_def, mvfderiv_const_smul_field, ← map_smul]
  congr 1
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
  module

/-! ### Contact forms -/

namespace IsContactForm

variable [FiniteDimensional ℝ E] (hα : α.IsContactForm)
include hα

/-- A vector field is a contact Hamiltonian vector field of `f` exactly when the contact flat map
sends it to the covector `(f + R_α f) α - df`. -/
theorem isContactHamiltonianVectorField_iff_contactFlat :
    α.IsContactHamiltonianVectorField f X ↔ ∀ x, α.contactFlat x (X x) =
      (f x + mvfderiv I f x (α.reebVectorField x)) • degreeOneEquiv α x - mvfderiv I f x := by
  have h1 : ∀ x (v : TangentSpace I x), degreeOneEquiv α x v = α.1 x ![v] := fun x v ↦ by
    rw [degreeOneEquiv_apply_apply, ← Matrix.vec_single_eq_const]
  refine forall_congr' fun x ↦ ⟨fun ⟨hf, hd⟩ ↦ ?_, fun h ↦ ?_⟩
  · ext v
    simp only [contactFlat_apply, hf, hd, sub_apply,
      smul_apply, h1, smul_eq_mul]
    ring
  · -- Evaluating at the Reeb vector field recovers `α(X) = f`.
    have hR := DFunLike.congr_fun h (α.reebVectorField x)
    simp only [contactFlat_apply, hα.mextDeriv_reebVectorField_right, hα.apply_reebVectorField,
      sub_apply, smul_apply, h1, smul_eq_mul] at hR
    have hf : α.1 x ![X x] = f x := by linarith
    refine ⟨hf, fun v ↦ ?_⟩
    have hv := DFunLike.congr_fun h v
    simp only [contactFlat_apply, hf, sub_apply,
      smul_apply, h1, smul_eq_mul] at hv
    linarith

/-- The contact flat map sends the contact Hamiltonian vector field of `f` to
`(f + R_α f) α - df`. -/
@[simp]
theorem contactFlat_contactHamiltonianVectorField (f : M → ℝ) (x : M) :
    α.contactFlat x (α.contactHamiltonianVectorField f x) =
      (f x + mvfderiv I f x (α.reebVectorField x)) • degreeOneEquiv α x - mvfderiv I f x :=
  (hα.isInvertible_contactFlat x).self_apply_inverse _

/-- The contact Hamiltonian vector field of `f` is a contact Hamiltonian vector field of `f`. -/
theorem isContactHamiltonianVectorField_contactHamiltonianVectorField (f : M → ℝ) :
    α.IsContactHamiltonianVectorField f (α.contactHamiltonianVectorField f) :=
  hα.isContactHamiltonianVectorField_iff_contactFlat.2
    (hα.contactFlat_contactHamiltonianVectorField f)

/-- A contact form takes the value `f` on the contact Hamiltonian vector field of `f`. -/
@[simp]
theorem apply_contactHamiltonianVectorField (f : M → ℝ) (x : M) :
    α.1 x ![α.contactHamiltonianVectorField f x] = f x :=
  (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f).apply_eq x

/-- **Contraction of `dα` with the contact Hamiltonian vector field** of `f` is
`(R_α f) α - df`. -/
@[simp]
theorem mextDeriv_contactHamiltonianVectorField_left (f : M → ℝ) (x : M)
    (v : TangentSpace I x) : mextDeriv α.1 x ![α.contactHamiltonianVectorField f x, v] =
      mvfderiv I f x (α.reebVectorField x) * α.1 x ![v] - mvfderiv I f x v :=
  (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f).mextDeriv_apply_eq x v

/-- **Existence and uniqueness of contact Hamiltonian vector fields.** For a contact form on a
finite-dimensional manifold, `X_f` is the only contact Hamiltonian vector field of `f`. -/
theorem isContactHamiltonianVectorField_iff_eq :
    α.IsContactHamiltonianVectorField f X ↔ X = α.contactHamiltonianVectorField f := by
  refine ⟨fun hX ↦ funext fun x ↦ (hα.isInvertible_contactFlat x).injective ?_, fun hX ↦ hX ▸
    hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f⟩
  rw [hα.contactFlat_contactHamiltonianVectorField,
    hα.isContactHamiltonianVectorField_iff_contactFlat.1 hX x]

/-- The contact Hamiltonian vector field of a constant `c` is `c R_α`. -/
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

/-- **Regularity of contact Hamiltonian vector fields.** For a contact form on a
finite-dimensional manifold, the contact Hamiltonian vector field of a `C^(n+1)` function is a
`C^n` vector field, for `n ≤ ∞`. -/
theorem contMDiff_contactHamiltonianVectorField {n : WithTop ℕ∞} (hn : n ≤ ∞)
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f) :
    ContMDiff I I.tangent n (T% (α.contactHamiltonianVectorField f)) := by
  have hRf : ContMDiff I 𝓘(ℝ) n fun x ↦ mvfderiv I f x (α.reebVectorField x) :=
    (hf.contMDiff_mvfderiv_apply le_rfl).comp (hα.contMDiff_reebVectorField.of_le hn)
  have hcov : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x
      ((f x + mvfderiv I f x (α.reebVectorField x)) • degreeOneEquiv α x - mvfderiv I f x) :=
    (((hf.of_le le_self_add).add hRf).smul_section
      ((degreeOneEquiv α).contMDiff.of_le hn)).sub_section hf.contMDiff_totalSpaceMk_mvfderiv
  exact (((contMDiff_contactFlat α).clm_bundle_inverse hα.isInvertible_contactFlat).of_le
    hn).clm_bundle_apply hcov

/-- The contact Hamiltonian vector field of a `C²` function is differentiable. -/
theorem mdifferentiable_contactHamiltonianVectorField (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    MDifferentiable I I.tangent
      (fun y ↦ (α.contactHamiltonianVectorField f y : TangentBundle I M)) :=
  (hα.contMDiff_contactHamiltonianVectorField (n := 1) (by simp)
    (by norm_num [hf])).mdifferentiable one_ne_zero

/-- **The multiplier of a contact vector field.** For a contact form `α` and a vector field `X`
differentiable at `x` with `α(X) = f`, if `L_X α = c α` at `x`, then `c = R_α f` at `x`. -/
theorem eq_mvfderiv_reebVectorField_of_mlieDerivForm_apply_eq_smul
    (hf : ∀ y, α.1 y ![X y] = f y) {x : M}
    (hXd : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x) {c : ℝ}
    (hc : mlieDerivForm X α.1 x = c • α.1 x) :
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
    α.IsContactHamiltonianVectorField f X ↔ (∀ x, α.1 x ![X x] = f x) ∧
      ∃ g : M → ℝ, mlieDerivForm X α.1 = fun x ↦ g x • α.1 x := by
  refine ⟨fun hX ↦ ⟨hX.apply_eq, _, hX.mlieDerivForm_eq hXd⟩,
    fun ⟨hf, g, hg⟩ x ↦ ⟨hf x, fun v ↦ ?_⟩⟩
  -- Cartan's formula: `g α = ι_X dα + df`.
  have key : ∀ v, g x * α.1 x ![v] = mextDeriv α.1 x ![X x, v] + mvfderiv I f x v := fun v ↦ by
    rw [← mlieDerivForm_apply_eq_mextDeriv_add hf (α.mdifferentiableAt x) (hXd x), hg,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [← hα.eq_mvfderiv_reebVectorField_of_mlieDerivForm_apply_eq_smul hf (hXd x) (congrFun hg x)]
  linarith [key v]

/-- **A contact vector field is the contact Hamiltonian vector field of its Hamiltonian.** For a
contact form `α`, a differentiable vector field `X` whose Lie derivative `L_X α` is a multiple of
`α` is the contact Hamiltonian vector field of `α(X)`. -/
theorem eq_contactHamiltonianVectorField_of_mlieDerivForm_eq_smul
    (hXd : MDifferentiable I I.tangent (fun y ↦ (X y : TangentBundle I M))) {g : M → ℝ}
    (hg : mlieDerivForm X α.1 = fun x ↦ g x • α.1 x) :
    X = α.contactHamiltonianVectorField fun x ↦ α.1 x ![X x] :=
  hα.isContactHamiltonianVectorField_iff_eq.1
    ((hα.isContactHamiltonianVectorField_iff_mlieDerivForm hXd).2 ⟨fun _ ↦ rfl, g, hg⟩)

end IsContactForm

end SmoothForm

end TauCeti
