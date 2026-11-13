/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactomorphism
public import TauCeti.Geometry.Contact.Family
public import TauCeti.Geometry.Contact.Hamiltonian
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The strict contact-Moser equation

Let `α` be a contact form on a finite-dimensional manifold `M`, with Reeb vector field `R_α`, and
let `β` be a one-form. The **strict contact-Moser equation** asks for a vector field `X` with

`L_X α = β`.

By Cartan's formula `L_X α = ι_X dα + d(α(X))`, it splits into the equations
`α(X) = h` and `ι_X dα + dh = β` for the function `h = α(X)`. Evaluating the second equation on
`R_α`, which spans the kernel of `dα`, gives the scalar **Reeb-direction equation**

`R_α h = β(R_α)`.

Conversely, every solution `h` of the Reeb-direction equation determines exactly one solution `X`.
The contact flat map `v ↦ ι_v dα + α(v) α` (`TauCeti.SmoothForm.contactFlat`) is invertible, and
`X` is its inverse applied to `β - dh + h α`. This is the **strict contact-Moser vector field**
`TauCeti.SmoothForm.strictContactMoserVectorField α β h`. The file proves:

* the pointwise equations are solvable exactly when the Reeb-direction equation holds
  (`TauCeti.SmoothForm.IsContactForm.exists_apply_eq_and_mextDeriv_add_eq_iff`), and then the
  solution is the strict contact-Moser vector
  (`TauCeti.SmoothForm.IsContactForm.eq_strictContactMoserVectorField_iff`);
* if `h` is `C²` and solves the Reeb-direction equation everywhere, then `L_X α = β`
  (`TauCeti.SmoothForm.IsContactForm.mlieDerivForm_strictContactMoserVectorField`); at a single
  point `x` it suffices that `X` is differentiable at `x` and `h` solves the Reeb-direction
  equation near `x`
  (`TauCeti.SmoothForm.IsContactForm.mlieDerivForm_strictContactMoserVectorField_apply`); every
  differentiable `X` with `L_X α = β` arises in this way from `h = α(X)`
  (`TauCeti.SmoothForm.IsContactForm.mlieDerivForm_eq_iff_eq_strictContactMoserVectorField`);
* where `h` solves the Reeb-direction equation, the strict field is the horizontal
  contact-Moser vector field of `-β` plus the contact Hamiltonian vector field of `h`
  (`TauCeti.SmoothForm.IsContactForm.strictContactMoserVectorField_eq_add`);
* where `h` solves the Reeb-direction equation, it vanishes at a point exactly when `h` and
  `β - dh` vanish there
  (`TauCeti.SmoothForm.IsContactForm.strictContactMoserVectorField_eq_zero_iff`);
* it is `C^n` for a `C^(n+1)` function `h`, and depends smoothly on parameters
  (`TauCeti.SmoothForm.contMDiffAt_sectionAlong_strictContactMoserVectorField`).

Compared with Gray's horizontal contact-Moser equation (`TauCeti.Geometry.Contact.Moser`), whose
solution `Y` only satisfies `L_Y α + β = β(R_α) α`, the strict equation prescribes `L_X α`
exactly. For a family of contact forms `α_t`, Gray's equation with `β = ∂_t α_t` integrates to a
flow that pulls `α_t` back to a positive multiple of `α_s`, whereas the strict equation with
`β = -∂_t α_t` integrates to a flow that pulls `α_t` back to `α_s` itself (see below). The price is
the Reeb-direction equation, an ordinary differential equation along the Reeb flow, which this
file takes as a hypothesis.

For a smooth family of contact forms `α_t`, represented by a one-form on `ℝ × M`, and a smooth
time-dependent function `h_t`, the **strict Moser vector field**
`TauCeti.SmoothForm.strictMoserVectorField` is at time `t` the strict contact-Moser vector field of
`(α_t, -∂_t α_t, h_t)`. It is jointly smooth, and when `h_t` solves
`R_(α_t) h_t = -(∂_t α_t)(R_(α_t))` it satisfies `L_(X_t) α_t + ∂_t α_t = 0`. On a compact
manifold without boundary its time-dependent flow `φ_(s,t)`
(`TauCeti.SmoothForm.strictMoserDiffeomorph`) therefore pulls `α_t` back to `α_s` exactly: it is a
strict contactomorphism (`TauCeti.SmoothForm.isStrictContactomorphism_strictMoserDiffeomorph`),
not merely a contactomorphism as Gray's isotopy is. It fixes the points where the field vanishes
at all times. This Moser step, with `α_t` the linear interpolation of two contact forms and `h_t`
supplied by the Reeb-direction equation, is how strict normal forms such as the neighbourhood
theorem for Legendrian submanifolds are proved.

## Main declarations

* `TauCeti.SmoothForm.strictContactMoserVectorField`: the strict contact-Moser vector field.
* `TauCeti.SmoothForm.IsContactForm.eq_strictContactMoserVectorField_iff`: its characterization.
* `TauCeti.SmoothForm.IsContactForm.mlieDerivForm_strictContactMoserVectorField`: `L_X α = β`.
* `TauCeti.SmoothForm.IsContactForm.mlieDerivForm_eq_iff_eq_strictContactMoserVectorField`: the
  solutions of `L_X α = β`.
* `TauCeti.SmoothForm.strictMoserVectorField`: the strict Moser vector field of a family.
* `TauCeti.SmoothForm.mlieDerivForm_strictMoserVectorField_add`: `L_(X_t) α_t + ∂_t α_t = 0`.
* `TauCeti.SmoothForm.strictMoserDiffeomorph`: on a compact manifold, its flow as a diffeomorphism.
* `TauCeti.SmoothForm.isStrictContactomorphism_strictMoserDiffeomorph`: the flow pulls `α_t` back
  to `α_s`.

## References

* A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*, AMS, 1997,
  Proposition 43.18.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Sections 2.2 and 2.5.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α β : SmoothForm I M ℝ 1} {h : M → ℝ} {X : (x : M) → TangentSpace I x}

/-- The **strict contact-Moser vector field** of a one-form `α`, a one-form `β` and a function
`h`: the inverse contact flat map applied to `β - dh + h α`. For a contact form in finite
dimensions, at a point `x` where `h` solves the Reeb-direction equation `R_α h = β(R_α)`, it is
the unique vector `X` with `α(X) = h` and `ι_X dα + dh = β`
(`TauCeti.SmoothForm.IsContactForm.eq_strictContactMoserVectorField_iff`). If moreover `h` solves
the Reeb-direction equation near `x` and the field is differentiable at `x`, then `L_X α = β` at
`x` (`TauCeti.SmoothForm.IsContactForm.mlieDerivForm_strictContactMoserVectorField_apply`).
The inverse is `ContinuousLinearMap.inverse`, so the definition is zero wherever the contact flat
map is not invertible. -/
def strictContactMoserVectorField (α β : SmoothForm I M ℝ 1) (h : M → ℝ) (x : M) :
    TangentSpace I x :=
  (α.contactFlat x).inverse (degreeOneEquiv β x - mvfderiv I h x + h x • degreeOneEquiv α x)

/-- The formula for the strict contact-Moser vector field. -/
theorem strictContactMoserVectorField_def (α β : SmoothForm I M ℝ 1) (h : M → ℝ) (x : M) :
    α.strictContactMoserVectorField β h x = (α.contactFlat x).inverse
      (degreeOneEquiv β x - mvfderiv I h x + h x • degreeOneEquiv α x) :=
  (rfl)

/-- **Strict contact-Moser vector fields of smooth families.** Let `α m`, `β m` be one-forms and
`h m` functions on `M`, depending on a parameter `m ∈ N`, such that `α m` is a contact form for
`m` near `m₀`, and let `b : N → M`. If the values `(α m)_(b m)`, `(β m)_(b m)`, `h m (b m)`, the
exterior derivatives `(dα m)_(b m)` and the differentials `d(h m)_(b m)` depend `C^n` on `m`, as
sections along `b`, then so do the strict contact-Moser vectors of `(α m, β m, h m)` at `b m`, as
a map to the tangent bundle. -/
theorem contMDiffAt_sectionAlong_strictContactMoserVectorField [FiniteDimensional ℝ E]
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] {n : WithTop ℕ∞}
    {b : N → M} {α β : N → SmoothForm I M ℝ 1} {h : N → M → ℝ} {m₀ : N}
    (hc : ∀ᶠ m in 𝓝 m₀, (α m).IsContactForm)
    (hα : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x) (b m) ((α m).1 (b m))) m₀)
    (hdα : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) (b m)
        (mextDeriv (α m).1 (b m))) m₀)
    (hβ : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x) (b m)
        ((β m).1 (b m))) m₀)
    (hh : ContMDiffAt J 𝓘(ℝ) n (fun m ↦ h m (b m)) m₀)
    (hdh : ContMDiffAt J (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (b m)
        (mvfderiv I (h m) (b m))) m₀) :
    ContMDiffAt J I.tangent n
      (fun m ↦ (⟨b m, (α m).strictContactMoserVectorField (β m) (h m) (b m)⟩ :
        TangentBundle I M)) m₀ := by
  have hβ₁ := (contMDiffAt_sectionAlong_degreeOneEquiv_iff (b := b) (α := β)).2 hβ
  have hX := (ContMDiffAt.clm_bundle_inverse (x := m₀) (ϕ := fun m ↦ (α m).contactFlat (b m))
    (contMDiffAt_sectionAlong_contactFlat hα hdα)
    (hc.self_of_nhds.isInvertible_contactFlat (b m₀))).clm_bundle_apply
      ((hβ₁.sub_sectionAlong hdh).add_sectionAlong
        (hh.smul_totalSpace (contMDiffAt_sectionAlong_degreeOneEquiv_iff.2 hα)))
  simpa only [strictContactMoserVectorField_def] using hX

namespace IsContactForm

variable [FiniteDimensional ℝ E] (hα : α.IsContactForm)
include hα

/-- The contact flat map sends the strict contact-Moser vector to `β - dh + h α`. -/
@[simp]
theorem contactFlat_strictContactMoserVectorField (β : SmoothForm I M ℝ 1) (h : M → ℝ) (x : M) :
    α.contactFlat x (α.strictContactMoserVectorField β h x) =
      degreeOneEquiv β x - mvfderiv I h x + h x • degreeOneEquiv α x :=
  (hα.isInvertible_contactFlat x).self_apply_inverse _

/-- The value of `α` on the strict contact-Moser vector is `h` corrected by the defect
`β(R_α) - R_α h` of the Reeb-direction equation. -/
theorem apply_strictContactMoserVectorField (β : SmoothForm I M ℝ 1) (h : M → ℝ) (x : M) :
    α.1 x ![α.strictContactMoserVectorField β h x] =
      h x + (β.1 x ![α.reebVectorField x] - mvfderiv I h x (α.reebVectorField x)) := by
  have hR := DFunLike.congr_fun (hα.contactFlat_strictContactMoserVectorField β h x)
    (α.reebVectorField x)
  simp only [contactFlat_apply, hα.mextDeriv_reebVectorField_right, hα.apply_reebVectorField,
    add_apply, sub_apply,
    smul_apply, degreeOneEquiv_apply_apply_vec, smul_eq_mul] at hR
  linarith

/-- The contraction of `dα` with the strict contact-Moser vector is `β - dh`, corrected along
`α` by the defect of the Reeb-direction equation. -/
theorem mextDeriv_strictContactMoserVectorField_left (β : SmoothForm I M ℝ 1) (h : M → ℝ)
    (x : M) (v : TangentSpace I x) :
    mextDeriv α.1 x ![α.strictContactMoserVectorField β h x, v] =
      β.1 x ![v] - mvfderiv I h x v -
        (β.1 x ![α.reebVectorField x] - mvfderiv I h x (α.reebVectorField x)) * α.1 x ![v] := by
  have hv := DFunLike.congr_fun (hα.contactFlat_strictContactMoserVectorField β h x) v
  simp only [contactFlat_apply, hα.apply_strictContactMoserVectorField,
    add_apply, sub_apply,
    smul_apply, degreeOneEquiv_apply_apply_vec, smul_eq_mul] at hv
  linarith

section ReebDirection

variable {x : M}
  (hR : mvfderiv I h x (α.reebVectorField x) = β.1 x ![α.reebVectorField x])
include hR

/-- Where `h` solves the Reeb-direction equation, `α` takes the value `h` on the strict
contact-Moser vector. -/
theorem apply_strictContactMoserVectorField_of_mvfderiv_eq :
    α.1 x ![α.strictContactMoserVectorField β h x] = h x := by
  rw [hα.apply_strictContactMoserVectorField, hR, sub_self, add_zero]

/-- Where `h` solves the Reeb-direction equation, the contraction of `dα` with the strict
contact-Moser vector is `β - dh`. -/
theorem mextDeriv_strictContactMoserVectorField_left_of_mvfderiv_eq (v : TangentSpace I x) :
    mextDeriv α.1 x ![α.strictContactMoserVectorField β h x, v] =
      β.1 x ![v] - mvfderiv I h x v := by
  rw [hα.mextDeriv_strictContactMoserVectorField_left, hR, sub_self, zero_mul, sub_zero]

/-- **Characterization of the strict contact-Moser vector.** Where `h` solves the Reeb-direction
equation `R_α h = β(R_α)`, a tangent vector `v` is the strict contact-Moser vector exactly when
`α(v) = h` and `ι_v dα + dh = β`. -/
theorem eq_strictContactMoserVectorField_iff {v : TangentSpace I x} :
    v = α.strictContactMoserVectorField β h x ↔ α.1 x ![v] = h x ∧
      ∀ w, mextDeriv α.1 x ![v, w] + mvfderiv I h x w = β.1 x ![w] := by
  constructor
  · rintro rfl
    refine ⟨hα.apply_strictContactMoserVectorField_of_mvfderiv_eq hR, fun w ↦ ?_⟩
    rw [hα.mextDeriv_strictContactMoserVectorField_left_of_mvfderiv_eq hR, sub_add_cancel]
  · rintro ⟨hv, hd⟩
    refine (hα.isInvertible_contactFlat x).injective (ContinuousLinearMap.ext fun w ↦ ?_)
    have hw := hd w
    rw [hα.contactFlat_strictContactMoserVectorField]
    simp only [contactFlat_apply, hv, add_apply,
      sub_apply, smul_apply,
      degreeOneEquiv_apply_apply_vec, smul_eq_mul]
    linarith

/-- **Vanishing of the strict contact-Moser vector.** Where `h` solves the Reeb-direction
equation, the strict contact-Moser vector vanishes exactly when `h` vanishes and `dh = β`. -/
theorem strictContactMoserVectorField_eq_zero_iff :
    α.strictContactMoserVectorField β h x = 0 ↔
      h x = 0 ∧ ∀ w, mvfderiv I h x w = β.1 x ![w] := by
  rw [eq_comm, hα.eq_strictContactMoserVectorField_iff hR]
  have h0 : α.1 x ![0] = 0 := (α.1 x).map_coord_zero 0 rfl
  have h1 (w : TangentSpace I x) : mextDeriv α.1 x ![0, w] = 0 :=
    (mextDeriv α.1 x).map_coord_zero 0 rfl
  simp only [h0, h1, zero_add, eq_comm]

/-- **The strict contact-Moser vector as a sum.** Where `h` solves the Reeb-direction equation,
the strict contact-Moser vector of `(β, h)` is the horizontal contact-Moser vector of `-β` plus
the contact Hamiltonian vector of `h`. -/
theorem strictContactMoserVectorField_eq_add :
    α.strictContactMoserVectorField β h x =
      α.contactMoserVectorField (-β) x + α.contactHamiltonianVectorField h x := by
  symm
  refine (hα.eq_strictContactMoserVectorField_iff hR).2 ⟨?_, fun w ↦ ?_⟩
  · rw [← degreeOneEquiv_apply_apply_vec, map_add, degreeOneEquiv_apply_apply_vec,
      degreeOneEquiv_apply_apply_vec, hα.apply_contactMoserVectorField,
      hα.apply_contactHamiltonianVectorField, zero_add]
  · have hadd : mextDeriv α.1 x
        ![α.contactMoserVectorField (-β) x + α.contactHamiltonianVectorField h x, w] =
          mextDeriv α.1 x ![α.contactMoserVectorField (-β) x, w] +
            mextDeriv α.1 x ![α.contactHamiltonianVectorField h x, w] := by
      simp only [mextDeriv_eq_bilinFormAt, map_add, LinearMap.add_apply]
    rw [hadd, hα.mextDeriv_contactMoserVectorField_left,
      hα.mextDeriv_contactHamiltonianVectorField_left, hR]
    simp only [neg_toRoughForm, Pi.neg_apply, ContinuousAlternatingMap.neg_apply]
    ring

end ReebDirection

/-- **Solvability of the strict contact-Moser equations.** There is a tangent vector `v` with
`α(v) = h` and `ι_v dα + dh = β` exactly when `h` solves the Reeb-direction equation
`R_α h = β(R_α)` at that point. -/
theorem exists_apply_eq_and_mextDeriv_add_eq_iff {x : M} :
    (∃ v : TangentSpace I x, α.1 x ![v] = h x ∧
      ∀ w, mextDeriv α.1 x ![v, w] + mvfderiv I h x w = β.1 x ![w]) ↔
      mvfderiv I h x (α.reebVectorField x) = β.1 x ![α.reebVectorField x] := by
  constructor
  · rintro ⟨v, -, hd⟩
    rw [← hd, hα.mextDeriv_reebVectorField_right, zero_add]
  · intro hR
    exact ⟨_, ((hα.eq_strictContactMoserVectorField_iff hR).1 rfl)⟩

/-- **Contact Hamiltonian vector fields are strict contact-Moser vector fields.** If `β` is the
multiple `(R_α h) α` of `α` at `x`, then the strict contact-Moser vector of `(β, h)` at `x` is the
contact Hamiltonian vector of `h`. -/
theorem strictContactMoserVectorField_eq_contactHamiltonianVectorField {x : M}
    (hβ : β.1 x = mvfderiv I h x (α.reebVectorField x) • α.1 x) :
    α.strictContactMoserVectorField β h x = α.contactHamiltonianVectorField h x := by
  have hR : mvfderiv I h x (α.reebVectorField x) = β.1 x ![α.reebVectorField x] := by
    rw [hβ, ContinuousAlternatingMap.smul_apply, hα.apply_reebVectorField, smul_eq_mul, mul_one]
  rw [hα.strictContactMoserVectorField_eq_add hR, add_eq_right,
    hα.contactMoserVectorField_eq_zero_iff]
  intro w hw
  rw [neg_toRoughForm, Pi.neg_apply, ContinuousAlternatingMap.neg_apply, hβ,
    ContinuousAlternatingMap.smul_apply, mem_kerDistribution.1 hw, smul_zero, neg_zero]

/-- **Regularity of strict contact-Moser vector fields.** For a contact form on a
finite-dimensional manifold, a smooth one-form `β` and a `C^(n+1)` function `h`, the strict
contact-Moser vector field is a `C^n` vector field, for `n ≤ ∞`. -/
theorem contMDiff_strictContactMoserVectorField {n : WithTop ℕ∞} (hn : n ≤ ∞)
    (β : SmoothForm I M ℝ 1) (hh : ContMDiff I 𝓘(ℝ) (n + 1) h) :
    ContMDiff I I.tangent n (T% (α.strictContactMoserVectorField β h)) := fun x ↦
  contMDiffAt_sectionAlong_strictContactMoserVectorField (b := id) (α := fun _ ↦ α)
    (β := fun _ ↦ β) (h := fun _ ↦ h) (.of_forall fun _ ↦ hα) ((α.contMDiff x).of_le hn)
    ((contMDiff_mextDeriv α x).of_le hn) ((β.contMDiff x).of_le hn) ((hh x).of_le le_self_add)
    (hh.contMDiff_totalSpaceMk_mvfderiv x)

/-- The strict contact-Moser vector field of a `C²` function is differentiable. -/
theorem mdifferentiable_strictContactMoserVectorField (β : SmoothForm I M ℝ 1)
    (hh : ContMDiff I 𝓘(ℝ) 2 h) :
    MDifferentiable I I.tangent (T% (α.strictContactMoserVectorField β h)) :=
  (hα.contMDiff_strictContactMoserVectorField (n := 1) (by simp) β
    (by norm_num [hh])).mdifferentiable one_ne_zero

/-- **The strict contact-Moser equation at a point.** If the strict contact-Moser vector field of
`(β, h)` is differentiable at `x` and `h` solves the Reeb-direction equation `R_α h = β(R_α)` near
`x`, then `L_X α = β` at `x`. -/
theorem mlieDerivForm_strictContactMoserVectorField_apply {x : M}
    (hXd : MDifferentiableAt I I.tangent (T% (α.strictContactMoserVectorField β h)) x)
    (hR : ∀ᶠ y in 𝓝 x, mvfderiv I h y (α.reebVectorField y) = β.1 y ![α.reebVectorField y]) :
    mlieDerivForm (α.strictContactMoserVectorField β h) α.1 x = β.1 x := by
  ext v
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, by ext i; fin_cases i; rfl⟩
  -- Near `x` the field takes the value `h` under `α`, so `d(α(X)) = dh` at `x`.
  have hd : mvfderiv I (fun y ↦ α.1 y ![α.strictContactMoserVectorField β h y]) x =
      mvfderiv I h x :=
    Filter.EventuallyEq.mvfderiv_eq
      (hR.mono fun y hy ↦ hα.apply_strictContactMoserVectorField_of_mvfderiv_eq hy)
  rw [mlieDerivForm_apply_eq_mextDeriv_add (fun _ ↦ rfl) (α.mdifferentiableAt x) hXd, hd,
    hα.mextDeriv_strictContactMoserVectorField_left_of_mvfderiv_eq hR.self_of_nhds,
    sub_add_cancel]

/-- **The strict contact-Moser equation.** For a contact form on a finite-dimensional manifold,
if `h` is `C²` and solves the Reeb-direction equation `R_α h = β(R_α)` everywhere, then the
strict contact-Moser vector field `X` of `(β, h)` satisfies `L_X α = β`. -/
theorem mlieDerivForm_strictContactMoserVectorField (hh : ContMDiff I 𝓘(ℝ) 2 h)
    (hR : ∀ y, mvfderiv I h y (α.reebVectorField y) = β.1 y ![α.reebVectorField y]) :
    mlieDerivForm (α.strictContactMoserVectorField β h) α.1 = β.1 :=
  funext fun x ↦ hα.mlieDerivForm_strictContactMoserVectorField_apply
    (hα.mdifferentiable_strictContactMoserVectorField β hh x) (.of_forall hR)

/-- **Solutions of the strict contact-Moser equation solve the Reeb-direction equation.** If a
vector field `X` is differentiable at `x` and `L_X α = β` at `x`, then `h = α(X)` satisfies
`R_α h = β(R_α)` at `x`. -/
theorem mvfderiv_apply_reebVectorField_of_mlieDerivForm_apply_eq {x : M}
    (hXd : MDifferentiableAt I I.tangent (T% X) x) (hL : mlieDerivForm X α.1 x = β.1 x) :
    mvfderiv I (fun y ↦ α.1 y ![X y]) x (α.reebVectorField x) =
      β.1 x ![α.reebVectorField x] := by
  -- Evaluate Cartan's formula `L_X α = ι_X dα + d(α(X))` at the Reeb vector field.
  have h := mlieDerivForm_apply_eq_mextDeriv_add (fun _ ↦ rfl) (α.mdifferentiableAt x) hXd
    (α.reebVectorField x)
  rwa [hL, hα.mextDeriv_reebVectorField_right, zero_add, eq_comm] at h

/-- **Solutions of the strict contact-Moser equation are strict contact-Moser vectors.** If a
vector field `X` is differentiable at `x` and `L_X α = β` at `x`, then `X` at `x` is the strict
contact-Moser vector of `(β, α(X))`. -/
theorem eq_strictContactMoserVectorField_of_mlieDerivForm_apply_eq {x : M}
    (hXd : MDifferentiableAt I I.tangent (T% X) x) (hL : mlieDerivForm X α.1 x = β.1 x) :
    X x = α.strictContactMoserVectorField β (fun y ↦ α.1 y ![X y]) x := by
  refine (hα.eq_strictContactMoserVectorField_iff
    (hα.mvfderiv_apply_reebVectorField_of_mlieDerivForm_apply_eq hXd hL)).2 ⟨rfl, fun w ↦ ?_⟩
  rw [← mlieDerivForm_apply_eq_mextDeriv_add (fun _ ↦ rfl) (α.mdifferentiableAt x) hXd, hL]

/-- **The solutions of the strict contact-Moser equation.** For a contact form on a
finite-dimensional manifold, a differentiable vector field `X` satisfies `L_X α = β` exactly when
`h = α(X)` solves the Reeb-direction equation `R_α h = β(R_α)` and `X` is the strict
contact-Moser vector field of `(β, h)`. -/
theorem mlieDerivForm_eq_iff_eq_strictContactMoserVectorField
    (hXd : MDifferentiable I I.tangent (T% X)) :
    mlieDerivForm X α.1 = β.1 ↔
      (∀ x, mvfderiv I (fun y ↦ α.1 y ![X y]) x (α.reebVectorField x) =
        β.1 x ![α.reebVectorField x]) ∧
      X = α.strictContactMoserVectorField β (fun y ↦ α.1 y ![X y]) := by
  refine ⟨fun hL ↦ ⟨fun x ↦ hα.mvfderiv_apply_reebVectorField_of_mlieDerivForm_apply_eq (hXd x)
    (congrFun hL x), funext fun x ↦
      hα.eq_strictContactMoserVectorField_of_mlieDerivForm_apply_eq (hXd x) (congrFun hL x)⟩,
    fun ⟨hR, hX⟩ ↦ funext fun x ↦ ?_⟩
  have hXd' : MDifferentiableAt I I.tangent
      (T% (α.strictContactMoserVectorField β (fun y ↦ α.1 y ![X y]))) x := by
    rw [← hX]
    exact hXd x
  have h := hα.mlieDerivForm_strictContactMoserVectorField_apply hXd' (.of_forall hR)
  rwa [← hX] at h

end IsContactForm

/-! ### The strict Moser isotopy of a family of contact forms -/

section Family

variable (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1) (h : ℝ × M → ℝ)

/-- The **strict Moser vector field** of a smooth family of one-forms `α_t = ι_t^* α` on `M`,
represented by a one-form `α` on `ℝ × M`, and of a time-dependent function `h_t = h (t, ·)`. At
time `t` it is the strict contact-Moser vector field of `α_t`, of `-∂_t α_t` and of `h_t`. When
the `α_t` are contact forms on a finite-dimensional manifold, `h` is smooth and every `h_t` solves
`R_(α_t) h_t = -(∂_t α_t)(R_(α_t))`, it satisfies `L_(X_t) α_t + ∂_t α_t = 0`
(`TauCeti.SmoothForm.mlieDerivForm_strictMoserVectorField_add`). -/
def strictMoserVectorField (t : ℝ) (x : M) : TangentSpace I x :=
  (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).strictContactMoserVectorField
    (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (-α.timeDeriv))
    (fun y ↦ h (t, y)) x

/-- The strict Moser vector field at time `t` is the strict contact-Moser vector field of the slice
`α_t`, of minus its velocity and of the slice `h_t`. -/
theorem strictMoserVectorField_def (t : ℝ) :
    α.strictMoserVectorField h t =
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).strictContactMoserVectorField
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (-α.timeDeriv))
        (fun y ↦ h (t, y)) :=
  (rfl)

variable {α h} [FiniteDimensional ℝ E]
  (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
  (hh : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ h)
include hc hh

/-- The strict Moser vector field of a smooth family of contact forms and a smooth time-dependent
function depends smoothly on time and point: `(t, x) ↦ (x, X_t(x))` is smooth into the tangent
bundle. -/
theorem contMDiff_strictMoserVectorField :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, α.strictMoserVectorField h p.1 p.2⟩ : TangentBundle I M)) :=
  fun p ↦ contMDiffAt_sectionAlong_strictContactMoserVectorField (b := Prod.snd)
    (α := fun q : ℝ × M ↦ mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α)
    (β := fun q : ℝ × M ↦
      mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) (-α.timeDeriv))
    (h := fun q y ↦ h (q.1, y)) (.of_forall fun q ↦ hc q.1) (contMDiff_mpullback_prodMk α p)
    (contMDiff_mextDeriv_mpullback_prodMk α p) (contMDiff_mpullback_prodMk (-α.timeDeriv) p)
    (hh p) (ContMDiff.contMDiff_totalSpaceMk_mvfderiv_uncurry (f := fun t y ↦ h (t, y))
      (hh.of_le (by simp)) p)

variable (hR : ∀ t x, mvfderiv I (fun y ↦ h (t, y)) x
    ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField x) =
      -(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).1 x
        ![(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField x])
include hR

/-- **The strict Moser equation for a family.** If `h_t` solves the Reeb-direction equation
`R_(α_t) h_t = -(∂_t α_t)(R_(α_t))` for every `t`, then `L_(X_t) α_t + ∂_t α_t = 0`, evaluated on
a tangent vector. -/
theorem mlieDerivForm_strictMoserVectorField_add (t : ℝ) (x : M) (v : TangentSpace I x) :
    mlieDerivForm (α.strictMoserVectorField h t)
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![v] +
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).1 x ![v] = 0 := by
  have hht : ContMDiff I 𝓘(ℝ) 2 fun y ↦ h (t, y) :=
    (hh.comp ((contMDiff_const (c := t)).prodMk contMDiff_id)).of_le (by simp)
  have hL := congrFun ((hc t).mlieDerivForm_strictContactMoserVectorField hht
    (β := mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (-α.timeDeriv))
    fun y ↦ by rw [map_neg, neg_toRoughForm, Pi.neg_apply,
      ContinuousAlternatingMap.neg_apply, hR]) x
  rw [strictMoserVectorField_def, hL, map_neg, neg_toRoughForm, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, neg_add_cancel]

/-! ### The strict Moser isotopy on compact manifolds -/

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit hR in
/-- On a compact manifold, the strict Moser vector field has a complete suspension: its
time-dependent flow is defined for all times. -/
theorem isCompleteVectorField_timeDependentSuspensionField_strictMoserVectorField :
    IsCompleteVectorField (timeDependentSuspensionField (α.strictMoserVectorField h)) :=
  isCompleteVectorField_timeDependentSuspensionField
    ((contMDiff_strictMoserVectorField hc hh).of_le (by simp)) isCompact_univ (by simp)

omit hR in
/-- **The strict Moser isotopy.** On a compact manifold without boundary, the time-dependent flow
of the strict Moser vector field of a smooth family of contact forms `α_t` and a smooth function
`h`, from time `s` to time `t`, as a diffeomorphism. When `h_t` solves the Reeb-direction equation
`R_(α_t) h_t = -(∂_t α_t)(R_(α_t))`, it pulls `α_t` back to `α_s`
(`TauCeti.SmoothForm.isStrictContactomorphism_strictMoserDiffeomorph`). -/
def strictMoserDiffeomorph (s t : ℝ) : M ≃ₘ⟮I, I⟯ M :=
  timeDependentFlowDiffeomorph
    (isCompleteVectorField_timeDependentSuspensionField_strictMoserVectorField hc hh) le_top
    (contMDiff_strictMoserVectorField hc hh) s t

omit hR in
/-- The strict Moser isotopy is the time-dependent flow of the strict Moser vector field. -/
theorem strictMoserDiffeomorph_apply (s t : ℝ) (x : M) :
    strictMoserDiffeomorph hc hh s t x = timeDependentFlowOf (α.strictMoserVectorField h) s t x :=
  timeDependentFlowDiffeomorph_apply _ _ _ s t x

omit hR in
/-- The inverse of the strict Moser isotopy from `s` to `t` is the strict Moser isotopy from `t` to
`s`. -/
@[simp]
theorem strictMoserDiffeomorph_symm_apply (s t : ℝ) (x : M) :
    (strictMoserDiffeomorph hc hh s t).symm x = strictMoserDiffeomorph hc hh t s x :=
  (timeDependentFlowDiffeomorph_symm_apply _ _ _ s t x).trans
    (strictMoserDiffeomorph_apply hc hh t s x).symm

omit hR in
/-- The strict Moser isotopy from a time to itself is the identity. -/
@[simp]
theorem strictMoserDiffeomorph_self (s : ℝ) (x : M) : strictMoserDiffeomorph hc hh s s x = x := by
  rw [strictMoserDiffeomorph_apply, timeDependentFlowOf_self]

omit hR in
/-- The strict Moser isotopy composes: flowing from `r` to `s` and then from `s` to `t` is flowing
from `r` to `t`. -/
@[simp]
theorem strictMoserDiffeomorph_strictMoserDiffeomorph (r s t : ℝ) (x : M) :
    strictMoserDiffeomorph hc hh s t (strictMoserDiffeomorph hc hh r s x) =
      strictMoserDiffeomorph hc hh r t x := by
  simp only [strictMoserDiffeomorph_apply]
  exact timeDependentFlowOf_trans
    (isCompleteVectorField_timeDependentSuspensionField_strictMoserVectorField hc hh)
    ((contMDiff_strictMoserVectorField hc hh).of_le (by simp)) r s t x

omit hR in
/-- The strict Moser isotopy depends smoothly on the initial time, the final time and the point. -/
theorem contMDiff_strictMoserDiffeomorph :
    ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
      (fun p : (ℝ × ℝ) × M ↦ strictMoserDiffeomorph hc hh p.1.1 p.1.2 p.2) := by
  simp only [strictMoserDiffeomorph_apply]
  exact contMDiff_timeDependentFlowOf
    (isCompleteVectorField_timeDependentSuspensionField_strictMoserVectorField hc hh) le_top
    (contMDiff_strictMoserVectorField hc hh)

omit hR in
/-- The strict Moser isotopy fixes every point at which the strict Moser vector field vanishes at
all times. -/
theorem strictMoserDiffeomorph_apply_eq_self {x : M} (hx : ∀ u, α.strictMoserVectorField h u x = 0)
    (s t : ℝ) : strictMoserDiffeomorph hc hh s t x = x := by
  rw [strictMoserDiffeomorph_apply]
  exact timeDependentFlowOf_eq_self_of_forall_eq_zero
    ((contMDiff_strictMoserVectorField hc hh).of_le (by simp)) hx s t

/-- **The strict Moser theorem for a family of contact forms.** On a compact manifold without
boundary, let `α_t` be a smooth family of contact forms and let `h_t` be a smooth time-dependent
function solving the Reeb-direction equation `R_(α_t) h_t = -(∂_t α_t)(R_(α_t))`. Then the strict
Moser isotopy from `s` to `t` pulls `α_t` back to `α_s`: it is a strict contactomorphism. -/
theorem isStrictContactomorphism_strictMoserDiffeomorph (s t : ℝ) :
    (strictMoserDiffeomorph hc hh s t).IsStrictContactomorphism
      (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α)
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) := by
  have hX := contMDiff_strictMoserVectorField hc hh
  -- The rate `∂_t α_t + L_{X_t} α_t` of the family vanishes.
  have hL (t : ℝ) :
      TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α.1) +
        mlieDerivForm (α.strictMoserVectorField h t)
          (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α.1) = 0 := by
    funext y
    ext v
    have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
    have hv0 := mlieDerivForm_strictMoserVectorField_add hc hh hR t y (v 0)
    rw [hv]
    simp only [coe_mpullback, coe_timeDeriv] at hv0
    simp only [Pi.add_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    rw [add_comm, hv0]
  rw [Diffeomorph.isStrictContactomorphism_def]
  have hφ : ⇑(strictMoserDiffeomorph hc hh s t) =
      timeDependentFlowOf (α.strictMoserVectorField h) s t :=
    funext (strictMoserDiffeomorph_apply hc hh s t)
  refine Subtype.ext ?_
  simpa only [coe_mpullback, hφ] using mpullback_timeDependentFlowOf_mpullback_prodMk_eq
    (hX.of_le (by simp))
    (isCompleteVectorField_timeDependentSuspensionField_strictMoserVectorField hc hh)
    (α.contMDiff.of_le (by simp)) hL s t

end Family

end TauCeti.SmoothForm
