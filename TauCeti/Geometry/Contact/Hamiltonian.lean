/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Contact Hamiltonian vector fields

Let `α` be a contact form on a finite-dimensional manifold `M`, with Reeb vector field `R_α`. The
**contact Hamiltonian vector field** of a function `f : M → ℝ`
(`TauCeti.SmoothForm.contactHamiltonianVectorField`) is the vector field `X_f` determined by

`α(X_f) = f`, `ι_(X_f) dα = (R_α f) α - df`.

It is obtained by inverting the contact flat map `v ↦ ι_v dα + α(v) α`
(`TauCeti.SmoothForm.contactFlat`) on the covector `(R_α f + f) α - df`. These two equations
determine `X_f` uniquely
(`TauCeti.SmoothForm.IsContactForm.eq_contactHamiltonianVectorField_iff`), and it is enough to test
the second one on the contact distribution `ξ = ker α`, where it reads `ι_(X_f) dα = -df`
(`TauCeti.SmoothForm.IsContactForm.eq_contactHamiltonianVectorField_iff_kerDistribution`).

By Cartan's formula `L_X α = ι_X dα + d(α(X))`, the defining equations give

`L_(X_f) α = (R_α f) α`

(`TauCeti.SmoothForm.IsContactForm.mlieDerivForm_contactHamiltonianVectorField`), so the local flow
of `X_f` preserves `ξ` together with its coorientation. Infinitesimally, the bracket of `X_f` with
any vector field tangent to `ξ` is again tangent to `ξ`
(`TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_mlieBracket_mem_kerDistribution`).
Conversely, a vector field `X` with `L_X α = g α` for some function `g` is the contact Hamiltonian
vector field of `α(X)`, and then `g = R_α(α(X))`
(`TauCeti.SmoothForm.IsContactForm.exists_mlieDerivForm_eq_smul_iff`).

The Hamiltonian `f = 1` gives the Reeb vector field, and more generally a constant `c` gives
`c R_α` (`TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_const`). The field `X_f`
is tangent to `ξ` exactly where `f` vanishes. Unlike a symplectic Hamiltonian vector field,
`X_f` need not preserve `f`: one has `df(X_f) = (R_α f) f`
(`TauCeti.SmoothForm.IsContactForm.mvfderiv_contactHamiltonianVectorField`). Since the Reeb
vector field is smooth (`TauCeti.SmoothForm.IsContactForm.contMDiff_reebVectorField`), the contact
Hamiltonian vector field of a `C^(n+1)` function is a `C^n` vector field
(`TauCeti.SmoothForm.IsContactForm.contMDiff_contactHamiltonianVectorField`).

## Conventions

This file follows the convention `α(X_f) = f`, `ι_(X_f) dα = (R_α f) α - df` of the roadmap and of
Geiges' book. Some authors (for example in contact Hamiltonian mechanics) use the opposite sign
`α(X_f) = -f`, `ι_(X_f) dα = df - (R_α f) α`; their field for `f` is the field here for `-f`
(`TauCeti.SmoothForm.contactHamiltonianVectorField_neg`). Both conventions give the same
correspondence between the vector fields that preserve `ξ` and their Hamiltonians, up to this
sign.

## Main declarations

* `TauCeti.SmoothForm.contactHamiltonianVectorField`: the contact Hamiltonian vector field.
* `TauCeti.SmoothForm.IsContactForm.apply_contactHamiltonianVectorField`,
  `TauCeti.SmoothForm.IsContactForm.mextDeriv_contactHamiltonianVectorField_left`: the defining
  equations.
* `TauCeti.SmoothForm.IsContactForm.eq_contactHamiltonianVectorField_iff`: uniqueness.
* `TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_const`: constant Hamiltonians
  give multiples of the Reeb vector field.
* `TauCeti.SmoothForm.IsContactForm.mlieDerivForm_contactHamiltonianVectorField`: the Lie
  derivative `L_(X_f) α = (R_α f) α`.
* `TauCeti.SmoothForm.IsContactForm.exists_mlieDerivForm_eq_smul_iff`: the vector fields
  preserving `ξ` are the contact Hamiltonian vector fields.
* `TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_mlieBracket_mem_kerDistribution`:
  contact Hamiltonian vector fields preserve `ξ` infinitesimally.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.3.
-/

public section

noncomputable section

open Bundle Module
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1} {f g : M → ℝ}

/-- The **contact Hamiltonian vector field** `X_f` of a function `f` for a one-form `α`: the
preimage of the covector `(R_α f + f) α - df` under the contact flat map `v ↦ ι_v dα + α(v) α`.
For a contact form on a finite-dimensional manifold it is the unique vector field with
`α(X_f) = f` and `ι_(X_f) dα = (R_α f) α - df`
(`TauCeti.SmoothForm.IsContactForm.eq_contactHamiltonianVectorField_iff`); the inverse is
`ContinuousLinearMap.inverse`, so the field vanishes at points where the contact flat map is not
invertible. -/
def contactHamiltonianVectorField (α : SmoothForm I M ℝ 1) (f : M → ℝ) (x : M) :
    TangentSpace I x :=
  (α.contactFlat x).inverse
    ((mvfderiv I f x (α.reebVectorField x) + f x) • degreeOneEquiv α x - mvfderiv I f x)

/-- The contact Hamiltonian vector field unfolds as the inverse contact flat map applied to
`(R_α f + f) α - df`. -/
theorem contactHamiltonianVectorField_def (α : SmoothForm I M ℝ 1) (f : M → ℝ) (x : M) :
    α.contactHamiltonianVectorField f x = (α.contactFlat x).inverse
      ((mvfderiv I f x (α.reebVectorField x) + f x) • degreeOneEquiv α x - mvfderiv I f x) :=
  (rfl)

/-- The contact Hamiltonian vector field is additive on differentiable functions. -/
theorem contactHamiltonianVectorField_add {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    α.contactHamiltonianVectorField (f + g) x =
      α.contactHamiltonianVectorField f x + α.contactHamiltonianVectorField g x := by
  rw [contactHamiltonianVectorField_def, contactHamiltonianVectorField_def,
    contactHamiltonianVectorField_def, ← map_add, mvfderiv_add hf hg]
  congr 1
  simp only [add_apply, Pi.add_apply]
  module

/-- The contact Hamiltonian vector field of `-f` is the opposite of that of `f`. -/
@[simp]
theorem contactHamiltonianVectorField_neg (x : M) :
    α.contactHamiltonianVectorField (-f) x = -α.contactHamiltonianVectorField f x := by
  rw [contactHamiltonianVectorField_def, contactHamiltonianVectorField_def, ← map_neg,
    mvfderiv_neg]
  congr 1
  simp only [neg_apply, Pi.neg_apply]
  module

/-! ### Cartan's formula for the contact form -/

/-- The interior product of a vector field `X` with `α` is the `0`-form of the function
`y ↦ α(X y)`. -/
private theorem interior_eq_ofFunction (X : (x : M) → TangentSpace I x) :
    RoughForm.interior X α.1 = RoughForm.ofFunction I (fun y ↦ α.1 y ![X y]) := by
  funext y
  ext v
  simp only [RoughForm.interior_apply, RoughForm.ofFunction_apply]
  congr 1
  funext i
  fin_cases i
  rfl

/-- `L_X α`, evaluated on a tangent vector, is `dα(X, v) + d(α(X))(v)`, by Cartan's formula. -/
private theorem mlieDerivForm_apply_eq {X : (x : M) → TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (v : TangentSpace I x) :
    mlieDerivForm X α.1 x ![v] =
      mextDeriv α.1 x ![X x, v] + mvfderiv I (fun y ↦ α.1 y ![X y]) x v := by
  rw [mlieDerivForm_eq_interior_mextDeriv_add_apply (α.mdifferentiableAt x) hX,
    ContinuousAlternatingMap.add_apply, RoughForm.interior_apply, interior_eq_ofFunction,
    mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply]
  congr 2

/-- The contact Hamiltonian vector field commutes with multiplication by a real constant. -/
theorem contactHamiltonianVectorField_const_smul (c : ℝ) (x : M) :
    α.contactHamiltonianVectorField (c • f) x = c • α.contactHamiltonianVectorField f x := by
  rw [contactHamiltonianVectorField_def, contactHamiltonianVectorField_def, ← map_smul]
  congr 1
  by_cases hf : MDifferentiableAt I 𝓘(ℝ) f x
  · have hcf : c • f = fun y ↦ c • f y := rfl
    rw [hcf, mvfderiv_const_smul hf c]
    simp only [smul_apply, smul_eq_mul]
    module
  · rcases eq_or_ne c 0 with rfl | hc
    · simp
    -- Neither `f` nor `c • f` is differentiable at `x`, so both derivatives vanish.
    have hcf : ¬MDifferentiableAt I 𝓘(ℝ) (c • f) x := fun hcf ↦
      hf (by simpa [smul_smul, inv_mul_cancel₀ hc] using hcf.const_smul c⁻¹)
    simp only [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt hcf, ContinuousLinearMap.comp_zero, zero_apply,
      Pi.smul_apply, smul_eq_mul, zero_add, sub_zero, smul_smul]

namespace IsContactForm

variable [FiniteDimensional ℝ E] (hα : α.IsContactForm)
include hα

/-- The contact flat map sends the contact Hamiltonian vector field of `f` to
`(R_α f + f) α - df`. -/
theorem contactFlat_contactHamiltonianVectorField (f : M → ℝ) (x : M) :
    α.contactFlat x (α.contactHamiltonianVectorField f x) =
      (mvfderiv I f x (α.reebVectorField x) + f x) • degreeOneEquiv α x - mvfderiv I f x :=
  (hα.isInvertible_contactFlat x).self_apply_inverse _

/-- **The first contact Hamiltonian equation**: `α(X_f) = f`. -/
@[simp]
theorem apply_contactHamiltonianVectorField (f : M → ℝ) (x : M) :
    α.1 x ![α.contactHamiltonianVectorField f x] = f x := by
  have h := congrArg (fun L ↦ L (α.reebVectorField x))
    (hα.contactFlat_contactHamiltonianVectorField f x)
  simp only [contactFlat_apply, hα.mextDeriv_reebVectorField_right, hα.apply_reebVectorField,
    zero_add, mul_one, sub_apply, smul_apply,
    degreeOneEquiv_apply_apply, smul_eq_mul] at h
  rw [← Matrix.vec_single_eq_const, hα.apply_reebVectorField] at h
  linarith

/-- **The second contact Hamiltonian equation**: `ι_(X_f) dα = (R_α f) α - df`. -/
theorem mextDeriv_contactHamiltonianVectorField_left (f : M → ℝ) (x : M)
    (w : TangentSpace I x) :
    mextDeriv α.1 x ![α.contactHamiltonianVectorField f x, w] =
      mvfderiv I f x (α.reebVectorField x) * α.1 x ![w] - mvfderiv I f x w := by
  have h := congrArg (fun L ↦ L w) (hα.contactFlat_contactHamiltonianVectorField f x)
  simp only [contactFlat_apply, hα.apply_contactHamiltonianVectorField,
    sub_apply, smul_apply, degreeOneEquiv_apply_apply,
    smul_eq_mul] at h
  rw [← Matrix.vec_single_eq_const] at h
  linarith

/-- **Characterization of the contact Hamiltonian vector field**: `X_f(x)` is the unique tangent
vector `v` with `α(v) = f(x)` and `ι_v dα = (R_α f) α - df` at `x`. -/
theorem eq_contactHamiltonianVectorField_iff {x : M} {v : TangentSpace I x} :
    v = α.contactHamiltonianVectorField f x ↔
      α.1 x ![v] = f x ∧ ∀ w : TangentSpace I x, mextDeriv α.1 x ![v, w] =
        mvfderiv I f x (α.reebVectorField x) * α.1 x ![w] - mvfderiv I f x w := by
  refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ (hα.isInvertible_contactFlat x).injective ?_⟩
  · rintro rfl
    exact ⟨hα.apply_contactHamiltonianVectorField f x,
      hα.mextDeriv_contactHamiltonianVectorField_left f x⟩
  rw [hα.contactFlat_contactHamiltonianVectorField]
  ext w
  simp only [contactFlat_apply, h₁, h₂, sub_apply,
    smul_apply, degreeOneEquiv_apply_apply, smul_eq_mul,
    ← Matrix.vec_single_eq_const]
  ring

/-- **Characterization of the contact Hamiltonian vector field**, tested on the contact
distribution: `X_f(x)` is the unique tangent vector `v` with `α(v) = f(x)` and
`dα(v, w) = -df(w)` for all `w ∈ ker α_x`. -/
theorem eq_contactHamiltonianVectorField_iff_kerDistribution {x : M} {v : TangentSpace I x} :
    v = α.contactHamiltonianVectorField f x ↔
      α.1 x ![v] = f x ∧ ∀ w : TangentSpace I x, α.1 x ![w] = 0 →
        mextDeriv α.1 x ![v, w] = -mvfderiv I f x w := by
  rw [hα.eq_contactHamiltonianVectorField_iff]
  refine and_congr_right fun _ ↦ ⟨fun h w hw ↦ by rw [h w, hw]; ring, fun h w ↦ ?_⟩
  -- Split `w` along `ξ ⊕ ℝ R_α` and use `dα(v, R_α) = 0`.
  set R := α.reebVectorField x
  set a := (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
  set B := (mextDerivₗ I 1 α).bilinFormAt x
  have ha (u : TangentSpace I x) : α.1 x ![u] = a u := (degreeOneEquiv_coe_apply α x u).symm
  have hB (u u' : TangentSpace I x) : mextDeriv α.1 x ![u, u'] = B u u' := by
    simp [B, bilinFormAt_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply]
  have hR : a R = 1 := by rw [← ha]; exact hα.apply_reebVectorField x
  have hw₀ : α.1 x ![w - a w • R] = 0 := by
    rw [ha, map_sub, map_smul, hR, smul_eq_mul, mul_one, sub_self]
  have hvR : B v R = 0 := by
    rw [← hB]; exact hα.mextDeriv_reebVectorField_right x _
  have := h _ hw₀
  rw [hB, map_sub, map_smul, smul_eq_mul, hvR, mul_zero, sub_zero, map_sub, map_smul,
    smul_eq_mul] at this
  rw [hB, this, ha]
  ring

/-- The contact Hamiltonian vector field of a constant function `c` is `c R_α`. -/
theorem contactHamiltonianVectorField_const (c : ℝ) (x : M) :
    α.contactHamiltonianVectorField (fun _ ↦ c) x = c • α.reebVectorField x := by
  refine ((hα.eq_contactHamiltonianVectorField_iff).2 ⟨?_, fun w ↦ ?_⟩).symm
  · rw [← degreeOneEquiv_coe_apply, map_smul, degreeOneEquiv_coe_apply,
      hα.apply_reebVectorField, smul_eq_mul, mul_one]
  · have hB (u u' : TangentSpace I x) :
        mextDeriv α.1 x ![u, u'] = (mextDerivₗ I 1 α).bilinFormAt x u u' := by
      simp [bilinFormAt_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply]
    rw [hB, map_smul, LinearMap.smul_apply, ← hB, hα.mextDeriv_reebVectorField_left,
      mvfderiv_const]
    simp

/-- The contact Hamiltonian vector field of the constant function `1` is the Reeb vector field. -/
@[simp]
theorem contactHamiltonianVectorField_one (x : M) :
    α.contactHamiltonianVectorField (fun _ ↦ 1) x = α.reebVectorField x := by
  rw [hα.contactHamiltonianVectorField_const, one_smul]

/-- The contact Hamiltonian vector field of `f` is tangent to the contact distribution exactly
where `f` vanishes. -/
theorem contactHamiltonianVectorField_mem_kerDistribution_iff (x : M) :
    α.contactHamiltonianVectorField f x ∈ α.kerDistribution x ↔ f x = 0 := by
  rw [mem_kerDistribution, hα.apply_contactHamiltonianVectorField]

/-- The derivative of `f` along its contact Hamiltonian vector field is `df(X_f) = (R_α f) f`. -/
theorem mvfderiv_contactHamiltonianVectorField (f : M → ℝ) (x : M) :
    mvfderiv I f x (α.contactHamiltonianVectorField f x) =
      mvfderiv I f x (α.reebVectorField x) * f x := by
  have h := hα.mextDeriv_contactHamiltonianVectorField_left f x
    (α.contactHamiltonianVectorField f x)
  rw [hα.apply_contactHamiltonianVectorField] at h
  have h₀ : mextDeriv α.1 x ![α.contactHamiltonianVectorField f x,
      α.contactHamiltonianVectorField f x] = 0 :=
    (mextDeriv α.1 x).map_eq_zero_of_eq ![_, _] (i := 0) (j := 1) rfl (by decide)
  linarith

/-! ### Regularity -/

/-- **Regularity of contact Hamiltonian vector fields.** For a contact form on a
finite-dimensional manifold, the contact Hamiltonian vector field of a `C^(n+1)` function is a
`C^n` vector field, for `n ≤ ∞`. -/
theorem contMDiff_contactHamiltonianVectorField {n : WithTop ℕ∞} (hn : n ≤ ∞)
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f) :
    ContMDiff I I.tangent n (T% (α.contactHamiltonianVectorField f)) := by
  have hdf := hf.contMDiff_totalSpaceMk_mvfderiv
  -- The function `x ↦ df_x (R_α x) + f x`.
  have hRf : ContMDiff I 𝓘(ℝ) n (fun x ↦ mvfderiv I f x (α.reebVectorField x) + f x) := by
    refine ContMDiff.add (fun x₀ ↦ ?_) (hf.of_le le_self_add)
    have h := (hdf.clm_bundle_apply (hα.contMDiff_reebVectorField.of_le hn)) x₀
    rw [contMDiffAt_section] at h
    simpa [Trivial.eq_trivialization M ℝ] using h
  have hθ := (hRf.smul_section ((degreeOneEquiv α).contMDiff.of_le hn)).sub_section hdf
  exact ((contMDiff_contactFlat α).clm_bundle_inverse hα.isInvertible_contactFlat).of_le
    hn |>.clm_bundle_apply hθ

/-! ### The Lie derivative of the contact form -/

/-- **The Lie derivative of `α` along a contact Hamiltonian vector field**:
`L_(X_f) α = (R_α f) α`. Hence the local flow of `X_f` preserves the contact distribution and its
coorientation. -/
theorem mlieDerivForm_contactHamiltonianVectorField {x : M}
    (hX : MDifferentiableAt I I.tangent
      (fun y ↦ (α.contactHamiltonianVectorField f y : TangentBundle I M)) x) :
    mlieDerivForm (α.contactHamiltonianVectorField f) α.1 x =
      mvfderiv I f x (α.reebVectorField x) • α.1 x := by
  ext v
  have hv : v = ![v 0] := by funext i; fin_cases i; rfl
  have hfun : (fun y ↦ α.1 y ![α.contactHamiltonianVectorField f y]) = f :=
    funext (hα.apply_contactHamiltonianVectorField f)
  rw [hv, mlieDerivForm_apply_eq hX, hfun, hα.mextDeriv_contactHamiltonianVectorField_left,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

/-- **Smooth contact Hamiltonian vector fields preserve the contact form up to a factor**: for a
`C²` function `f`, `L_(X_f) α = (R_α f) α`. -/
theorem mlieDerivForm_contactHamiltonianVectorField_eq (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    mlieDerivForm (α.contactHamiltonianVectorField f) α.1 =
      fun x ↦ mvfderiv I f x (α.reebVectorField x) • α.1 x :=
  funext fun x ↦ hα.mlieDerivForm_contactHamiltonianVectorField <|
    ((hα.contMDiff_contactHamiltonianVectorField (n := 1) (by simp) hf) x).mdifferentiableAt
      one_ne_zero

/-- **Contact vector fields are contact Hamiltonian.** For a vector field `X` differentiable at
`x`, the Lie derivative `L_X α` is a multiple of `α` at `x` exactly when `X(x)` is the contact
Hamiltonian vector field of the function `α(X)` at `x`. The factor is then `R_α(α(X))`. -/
theorem exists_mlieDerivForm_eq_smul_iff {X : (x : M) → TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x) :
    (∃ c : ℝ, mlieDerivForm X α.1 x = c • α.1 x) ↔
      X x = α.contactHamiltonianVectorField (fun y ↦ α.1 y ![X y]) x := by
  set h : M → ℝ := fun y ↦ α.1 y ![X y]
  refine ⟨fun ⟨c, hL⟩ ↦ ?_, fun hXh ↦ ⟨mvfderiv I h x (α.reebVectorField x), ?_⟩⟩
  · have hL' (w : TangentSpace I x) :
        mextDeriv α.1 x ![X x, w] + mvfderiv I h x w = c * α.1 x ![w] := by
      rw [← mlieDerivForm_apply_eq hX, hL, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    -- Testing on the Reeb vector field identifies `c = R_α (α(X))`.
    have hc : c = mvfderiv I h x (α.reebVectorField x) := by
      have := hL' (α.reebVectorField x)
      rwa [hα.mextDeriv_reebVectorField_right, zero_add, hα.apply_reebVectorField, mul_one,
        eq_comm] at this
    refine hα.eq_contactHamiltonianVectorField_iff.2 ⟨rfl, fun w ↦ ?_⟩
    rw [← hc]
    linarith [hL' w]
  · ext v
    have hv : v = ![v 0] := by funext i; fin_cases i; rfl
    rw [hv, mlieDerivForm_apply_eq hX, hXh, hα.mextDeriv_contactHamiltonianVectorField_left,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring

/-- **Contact Hamiltonian vector fields preserve the contact distribution.** If `X_f` and a
vector field `Y` are differentiable at `x`, and `Y` is tangent to `ξ = ker α` near `x`, then the
bracket `[X_f, Y]` is tangent to `ξ` at `x`. This holds for instance when `f` is `C²`
(`TauCeti.SmoothForm.IsContactForm.contMDiff_contactHamiltonianVectorField`). -/
theorem contactHamiltonianVectorField_mlieBracket_mem_kerDistribution
    {Y : (x : M) → TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I I.tangent
      (fun y ↦ (α.contactHamiltonianVectorField f y : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x)
    (hYξ : ∀ᶠ y in 𝓝 x, Y y ∈ α.kerDistribution y) :
    VectorField.mlieBracket I (α.contactHamiltonianVectorField f) Y x ∈ α.kerDistribution x := by
  have hbr := mlieDerivForm_apply_vectorField (V := α.contactHamiltonianVectorField f)
    (X := ![Y]) (α.mdifferentiableAt x) (fun i ↦ by fin_cases i; exact hY)
  rw [hα.mlieDerivForm_contactHamiltonianVectorField hX] at hbr
  -- `α(Y)` vanishes near `x`, so its derivative vanishes at `x`.
  have hzero : mvfderiv I (fun y ↦ α.1 y (![Y] · y)) x = 0 := by
    have : (fun y ↦ α.1 y (![Y] · y)) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hYξ] with y hy
      rw [mem_kerDistribution] at hy
      convert hy using 2
      funext i; fin_cases i; rfl
    ext v
    simp [mvfderiv, this.mfderiv_eq]
  have hYx : α.1 x ![Y x] = 0 := mem_kerDistribution.1 hYξ.self_of_nhds
  have hYx' : α.1 x (![Y] · x) = 0 := by
    convert hYx using 2
    funext i; fin_cases i; rfl
  rw [mem_kerDistribution]
  simp only [ContinuousAlternatingMap.smul_apply, hYx', smul_zero, hzero,
    zero_apply, zero_sub, Fin.sum_univ_one] at hbr
  rw [eq_comm, neg_eq_zero] at hbr
  convert hbr using 2
  funext i; fin_cases i; rfl

end IsContactForm

end SmoothForm

end TauCeti
