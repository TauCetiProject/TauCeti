/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactomorphism
public import TauCeti.Geometry.Contact.Hamiltonian
public import TauCeti.Geometry.Contact.Moser
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
public import TauCeti.Geometry.Manifold.Flow.Transport
import TauCeti.Geometry.Contact.Family
import TauCeti.Geometry.Manifold.Flow.Parametric
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

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
the Reeb-direction equation, an ordinary differential equation along the Reeb flow, which the
Moser theorems below take as a hypothesis, and which is solved below near a transverse slice.

For a smooth family of contact forms `α_t`, represented by a one-form on `ℝ × M`, and a smooth
time-dependent function `h_t`, the **strict Moser vector field**
`TauCeti.SmoothForm.strictMoserVectorField` is at time `t` the strict contact-Moser vector field of
`(α_t, -∂_t α_t, h_t)`. It is jointly `C^n` when `h` is `C^(n+1)`, and when the slice `α_t` is a
contact form and `h_t` is `C²` and solves `R_(α_t) h_t = -(∂_t α_t)(R_(α_t))` it satisfies
`L_(X_t) α_t + ∂_t α_t = 0`. On a manifold without boundary, whenever its suspension is complete,
its time-dependent flow therefore pulls `α_t` back to `α_s` exactly
(`TauCeti.SmoothForm.mpullback_timeDependentFlowOf_strictMoserVectorField`). On a compact manifold
the suspension is complete, and the flow `φ_(s,t)` (`TauCeti.SmoothForm.strictMoserDiffeomorph`)
is a strict contactomorphism
(`TauCeti.SmoothForm.isStrictContactomorphism_strictMoserDiffeomorph`), not merely a
contactomorphism as Gray's isotopy is. It fixes the points where the field vanishes at all times.
This Moser step, with `α_t` the linear interpolation of two contact forms and `h_t` supplied by the
Reeb-direction equation, is how strict normal forms such as the neighbourhood theorem for
Legendrian submanifolds are proved.

Without compactness the flow need not be defined for all times, but its domain is open. The time
map from `s` to `t` is then a smooth partial diffeomorphism
`TauCeti.SmoothForm.strictMoserPartialDiffeomorph`, defined on the open set of points whose
trajectory exists from time `s` up to time `t`. The Moser computation only reads the
Reeb-direction equation along trajectories: if `h_u` solves it near the point `φ_(s,u) x` at every
time `u` between `s` and `t`, then `φ_(s,t)` pulls `α_t` back to `α_s` at `x`
(`TauCeti.SmoothForm.mpullback_strictMoserPartialDiffeomorph_apply_of_forall_mem_uIcc`). A point
at which the field vanishes at all times has a constant trajectory, so it lies in the source and
the target and is fixed. This gives the **relative strict Moser theorem**
(`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq`): if the field vanishes at all times
on a set `K`, and `h_t` solves the Reeb-direction equation on an open set `U ⊆ ℝ × M` containing
`(u, x)` for every `x ∈ K` and every time `u` between `s` and `t`, the partial isotopy restricted
to the points whose trajectories stay in `U` is a partial diffeomorphism fixing `K`, defined on
open neighbourhoods of `K`, which pulls `α_t` back to `α_s` exactly. Neither `K` nor `M` need be
compact, and the Reeb-direction equation need only hold near `K`.

Such a function `h` exists near a closed embedded hypersurface `ι : S → M` transverse to every Reeb
field `R_(α_t)`: there is a smooth `h`, vanishing on `ℝ × ι(S)`, which solves the Reeb-direction
equation on an open neighbourhood of `ℝ × ι(S)` in `ℝ × M`
(`TauCeti.SmoothForm.exists_contMDiff_mvfderiv_reebVectorField_eq_of_isTransverseAlong`). It is
the solution of a transport equation along the trajectories of the Reeb fields, with zero initial
values on the slice (`TauCeti.exists_contMDiff_mvfderiv_eq_of_isTransverseAlong`).

## Main declarations

* `TauCeti.SmoothForm.strictContactMoserVectorField`: the strict contact-Moser vector field.
* `TauCeti.SmoothForm.IsContactForm.eq_strictContactMoserVectorField_iff`: its characterization.
* `TauCeti.SmoothForm.IsContactForm.mlieDerivForm_strictContactMoserVectorField`: `L_X α = β`.
* `TauCeti.SmoothForm.IsContactForm.mlieDerivForm_eq_iff_eq_strictContactMoserVectorField`: the
  solutions of `L_X α = β`.
* `TauCeti.SmoothForm.strictMoserVectorField`: the strict Moser vector field of a family.
* `TauCeti.SmoothForm.mlieDerivForm_strictMoserVectorField_add`: `L_(X_t) α_t + ∂_t α_t = 0`.
* `TauCeti.SmoothForm.mpullback_timeDependentFlowOf_strictMoserVectorField`: a complete flow of
  the strict Moser vector field pulls `α_t` back to `α_s`.
* `TauCeti.SmoothForm.strictMoserPartialDiffeomorph`: its flow from time `s` to time `t` as a
  partial diffeomorphism, with no compactness.
* `TauCeti.SmoothForm.mpullback_strictMoserPartialDiffeomorph_apply_of_forall_mem_uIcc`: the
  partial flow pulls `α_t` back to `α_s` at every point along whose trajectory `h` solves the
  Reeb-direction equation.
* `TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq`: the relative strict Moser theorem.
* `TauCeti.SmoothForm.exists_contMDiff_mvfderiv_reebVectorField_eq_of_isTransverseAlong`: a
  solution of the Reeb-direction equation near a transverse slice, vanishing on the slice.
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

/-- The strict contact-Moser vector field of the zero one-form and the zero function vanishes. -/
@[simp]
theorem strictContactMoserVectorField_zero (α : SmoothForm I M ℝ 1) :
    α.strictContactMoserVectorField 0 (0 : M → ℝ) = 0 := by
  funext x
  simp [strictContactMoserVectorField_def, mvfderiv_zero]

/-- The strict contact-Moser vector field of `(-β, -h)` is the opposite of that of `(β, h)`. -/
@[simp]
theorem strictContactMoserVectorField_neg (x : M) :
    α.strictContactMoserVectorField (-β) (-h) x = -α.strictContactMoserVectorField β h x := by
  simp only [strictContactMoserVectorField_def, mvfderiv_neg, ← map_neg]
  congr 1
  simp only [map_neg, ContMDiffSection.coe_neg, Pi.neg_apply]
  module

/-- The strict contact-Moser vector field commutes with multiplying `β` and `h` by the same real
constant. -/
@[simp]
theorem strictContactMoserVectorField_const_smul (c : ℝ) (x : M) :
    α.strictContactMoserVectorField (c • β) (c • h) x =
      c • α.strictContactMoserVectorField β h x := by
  simp only [strictContactMoserVectorField_def, mvfderiv_const_smul_field, ← map_smul]
  congr 1
  simp only [map_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
  module

/-- **Strict contact-Moser vector fields of smooth families.** Let `α m`, `β m` be one-forms and
`h m` functions on `M`, depending on a parameter `m ∈ N`, and let `b : N → M`. Suppose that the
contact flat map of `α m₀` is invertible at `b m₀`, as it is when `α m₀` is a contact form there
(`TauCeti.SmoothForm.IsContactForm.isInvertible_contactFlat`). If the values `(α m)_(b m)`,
`(β m)_(b m)`, `h m (b m)`, the exterior derivatives `(dα m)_(b m)` and the differentials
`d(h m)_(b m)` depend `C^n` on `m` at `m₀`, as sections along `b`, then so do the strict
contact-Moser vectors of `(α m, β m, h m)` at `b m`, as a map to the tangent bundle. -/
theorem contMDiffAt_sectionAlong_strictContactMoserVectorField [CompleteSpace E]
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] {n : WithTop ℕ∞}
    {b : N → M} {α β : N → SmoothForm I M ℝ 1} {h : N → M → ℝ} {m₀ : N}
    (hc : ((α m₀).contactFlat (b m₀)).IsInvertible)
    (hα : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x) (b m) ((α m).val
            (b m))) m₀)
    (hdα : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) (b m)
        (mextDeriv (α m).val (b m))) m₀)
    (hβ : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x) (b m)
        ((β m).val (b m))) m₀)
    (hh : ContMDiffAt J 𝓘(ℝ) n (fun m ↦ h m (b m)) m₀)
    (hdh : ContMDiffAt J (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (b m)
        (mvfderiv I (h m) (b m))) m₀) :
    ContMDiffAt J I.tangent n
      (fun m ↦ (⟨b m, (α m).strictContactMoserVectorField (β m) (h m) (b m)⟩ :
        TangentBundle I M)) m₀ := by
  have hβ₁ := (contMDiffAt_sectionAlong_degreeOneEquiv_iff (b := b) (α := β)).2 hβ
  have hX := (ContMDiffAt.clm_bundle_inverse (x := m₀) (ϕ := fun m ↦ (α m).contactFlat (b m))
    (contMDiffAt_sectionAlong_contactFlat hα hdα) hc).clm_bundle_apply
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
    α.val x ![α.strictContactMoserVectorField β h x] =
      h x + (β.val x ![α.reebVectorField x] - mvfderiv I h x (α.reebVectorField x)) := by
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
    mextDeriv α.val x ![α.strictContactMoserVectorField β h x, v] =
      β.val x ![v] - mvfderiv I h x v -
        (β.val x ![α.reebVectorField x] - mvfderiv I h x (α.reebVectorField x)) * α.val x ![v] := by
  have hv := DFunLike.congr_fun (hα.contactFlat_strictContactMoserVectorField β h x) v
  simp only [contactFlat_apply, hα.apply_strictContactMoserVectorField,
    add_apply, sub_apply,
    smul_apply, degreeOneEquiv_apply_apply_vec, smul_eq_mul] at hv
  linarith

section ReebDirection

variable {x : M}
  (hR : mvfderiv I h x (α.reebVectorField x) = β.val x ![α.reebVectorField x])
include hR

/-- Where `h` solves the Reeb-direction equation, `α` takes the value `h` on the strict
contact-Moser vector. -/
theorem apply_strictContactMoserVectorField_of_mvfderiv_eq :
    α.val x ![α.strictContactMoserVectorField β h x] = h x := by
  rw [hα.apply_strictContactMoserVectorField, hR, sub_self, add_zero]

/-- Where `h` solves the Reeb-direction equation, the contraction of `dα` with the strict
contact-Moser vector is `β - dh`. -/
theorem mextDeriv_strictContactMoserVectorField_left_of_mvfderiv_eq (v : TangentSpace I x) :
    mextDeriv α.val x ![α.strictContactMoserVectorField β h x, v] =
      β.val x ![v] - mvfderiv I h x v := by
  rw [hα.mextDeriv_strictContactMoserVectorField_left, hR, sub_self, zero_mul, sub_zero]

/-- **Characterization of the strict contact-Moser vector.** Where `h` solves the Reeb-direction
equation `R_α h = β(R_α)`, a tangent vector `v` is the strict contact-Moser vector exactly when
`α(v) = h` and `ι_v dα + dh = β`. -/
theorem eq_strictContactMoserVectorField_iff {v : TangentSpace I x} :
    v = α.strictContactMoserVectorField β h x ↔ α.val x ![v] = h x ∧
      ∀ w, mextDeriv α.val x ![v, w] + mvfderiv I h x w = β.val x ![w] := by
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
      h x = 0 ∧ ∀ w, mvfderiv I h x w = β.val x ![w] := by
  rw [eq_comm, hα.eq_strictContactMoserVectorField_iff hR]
  have h0 : α.val x ![0] = 0 := (α.val x).map_coord_zero 0 rfl
  have h1 (w : TangentSpace I x) : mextDeriv α.val x ![0, w] = 0 :=
    (mextDeriv α.val x).map_coord_zero 0 rfl
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
  · have hadd : mextDeriv α.val x
        ![α.contactMoserVectorField (-β) x + α.contactHamiltonianVectorField h x, w] =
          mextDeriv α.val x ![α.contactMoserVectorField (-β) x, w] +
            mextDeriv α.val x ![α.contactHamiltonianVectorField h x, w] := by
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
    (∃ v : TangentSpace I x, α.val x ![v] = h x ∧
      ∀ w, mextDeriv α.val x ![v, w] + mvfderiv I h x w = β.val x ![w]) ↔
      mvfderiv I h x (α.reebVectorField x) = β.val x ![α.reebVectorField x] := by
  constructor
  · rintro ⟨v, -, hd⟩
    rw [← hd, hα.mextDeriv_reebVectorField_right, zero_add]
  · intro hR
    exact ⟨_, ((hα.eq_strictContactMoserVectorField_iff hR).1 rfl)⟩

/-- **Contact Hamiltonian vector fields are strict contact-Moser vector fields.** If `β` is the
multiple `(R_α h) α` of `α` at `x`, then the strict contact-Moser vector of `(β, h)` at `x` is the
contact Hamiltonian vector of `h`. -/
theorem strictContactMoserVectorField_eq_contactHamiltonianVectorField {x : M}
    (hβ : β.val x = mvfderiv I h x (α.reebVectorField x) • α.val x) :
    α.strictContactMoserVectorField β h x = α.contactHamiltonianVectorField h x := by
  have hR : mvfderiv I h x (α.reebVectorField x) = β.val x ![α.reebVectorField x] := by
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
    (β := fun _ ↦ β) (h := fun _ ↦ h) (hα.isInvertible_contactFlat x) ((α.contMDiff x).of_le hn)
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
    (hR : ∀ᶠ y in 𝓝 x, mvfderiv I h y (α.reebVectorField y) = β.val y ![α.reebVectorField y]) :
    mlieDerivForm (α.strictContactMoserVectorField β h) α.val x = β.val x := by
  ext v
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, by ext i; fin_cases i; rfl⟩
  -- Near `x` the field takes the value `h` under `α`, so `d(α(X)) = dh` at `x`.
  have hd : mvfderiv I (fun y ↦ α.val y ![α.strictContactMoserVectorField β h y]) x =
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
    (hR : ∀ y, mvfderiv I h y (α.reebVectorField y) = β.val y ![α.reebVectorField y]) :
    mlieDerivForm (α.strictContactMoserVectorField β h) α.val = β.val :=
  funext fun x ↦ hα.mlieDerivForm_strictContactMoserVectorField_apply
    (hα.mdifferentiable_strictContactMoserVectorField β hh x) (.of_forall hR)

/-- **Solutions of the strict contact-Moser equation solve the Reeb-direction equation.** If a
vector field `X` is differentiable at `x` and `L_X α = β` at `x`, then `h = α(X)` satisfies
`R_α h = β(R_α)` at `x`. -/
theorem mvfderiv_apply_reebVectorField_of_mlieDerivForm_apply_eq {x : M}
    (hXd : MDifferentiableAt I I.tangent (T% X) x) (hL : mlieDerivForm X α.val x = β.val x) :
    mvfderiv I (fun y ↦ α.val y ![X y]) x (α.reebVectorField x) =
      β.val x ![α.reebVectorField x] := by
  -- Evaluate Cartan's formula `L_X α = ι_X dα + d(α(X))` at the Reeb vector field.
  have h := mlieDerivForm_apply_eq_mextDeriv_add (fun _ ↦ rfl) (α.mdifferentiableAt x) hXd
    (α.reebVectorField x)
  rwa [hL, hα.mextDeriv_reebVectorField_right, zero_add, eq_comm] at h

/-- **Solutions of the strict contact-Moser equation are strict contact-Moser vectors.** If a
vector field `X` is differentiable at `x` and `L_X α = β` at `x`, then `X` at `x` is the strict
contact-Moser vector of `(β, α(X))`. -/
theorem eq_strictContactMoserVectorField_of_mlieDerivForm_apply_eq {x : M}
    (hXd : MDifferentiableAt I I.tangent (T% X) x) (hL : mlieDerivForm X α.val x = β.val x) :
    X x = α.strictContactMoserVectorField β (fun y ↦ α.val y ![X y]) x := by
  refine (hα.eq_strictContactMoserVectorField_iff
    (hα.mvfderiv_apply_reebVectorField_of_mlieDerivForm_apply_eq hXd hL)).2 ⟨rfl, fun w ↦ ?_⟩
  rw [← mlieDerivForm_apply_eq_mextDeriv_add (fun _ ↦ rfl) (α.mdifferentiableAt x) hXd, hL]

/-- **The solutions of the strict contact-Moser equation.** For a contact form on a
finite-dimensional manifold, a differentiable vector field `X` satisfies `L_X α = β` exactly when
`h = α(X)` solves the Reeb-direction equation `R_α h = β(R_α)` and `X` is the strict
contact-Moser vector field of `(β, h)`. -/
theorem mlieDerivForm_eq_iff_eq_strictContactMoserVectorField
    (hXd : MDifferentiable I I.tangent (T% X)) :
    mlieDerivForm X α.val = β.val ↔
      (∀ x, mvfderiv I (fun y ↦ α.val y ![X y]) x (α.reebVectorField x) =
        β.val x ![α.reebVectorField x]) ∧
      X = α.strictContactMoserVectorField β (fun y ↦ α.val y ![X y]) := by
  refine ⟨fun hL ↦ ⟨fun x ↦ hα.mvfderiv_apply_reebVectorField_of_mlieDerivForm_apply_eq (hXd x)
    (congrFun hL x), funext fun x ↦
      hα.eq_strictContactMoserVectorField_of_mlieDerivForm_apply_eq (hXd x) (congrFun hL x)⟩,
    fun ⟨hR, hX⟩ ↦ funext fun x ↦ ?_⟩
  have hXd' : MDifferentiableAt I I.tangent
      (T% (α.strictContactMoserVectorField β (fun y ↦ α.val y ![X y]))) x := by
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
`α_t` is a contact form on a finite-dimensional manifold and `h_t` is `C²` and solves
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

omit [FiniteDimensional ℝ E] in
/-- The Reeb-direction equation for the strict Moser vector field at time `t`, restated with the
velocity `-∂_t α_t` that enters the strict contact-Moser vector field. -/
private theorem mvfderiv_eq_mpullback_neg_timeDeriv {t : ℝ} {x : M}
    (hR : mvfderiv I (fun y ↦ h (t, y)) x
      ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField x) =
        -(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val x
          ![(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField x]) :
    mvfderiv I (fun y ↦ h (t, y)) x
      ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField x) =
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (-α.timeDeriv)).val x
          ![(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField x] := by
  rw [map_neg, neg_toRoughForm, Pi.neg_apply, ContinuousAlternatingMap.neg_apply, hR]

section Slice

variable {t : ℝ}
  (hc : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
include hc

section ReebDirection

variable {x : M}
  (hR : mvfderiv I (fun y ↦ h (t, y)) x
    ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField x) =
      -(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val x
        ![(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField x])
include hR

/-- If the slice `α_t` is a contact form and `h_t` solves the Reeb-direction equation
`R_(α_t) h_t = -(∂_t α_t)(R_(α_t))` at `x`, then `α_t` takes the value `h_t` on the strict Moser
vector field at time `t` and at `x`. -/
theorem apply_strictMoserVectorField :
    (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).val x
      ![α.strictMoserVectorField h t x] = h (t, x) :=
  hc.apply_strictContactMoserVectorField_of_mvfderiv_eq (mvfderiv_eq_mpullback_neg_timeDeriv hR)

/-- **Characterization of the strict Moser vector field.** If the slice `α_t` is a contact form
and `h_t` solves the Reeb-direction equation `R_(α_t) h_t = -(∂_t α_t)(R_(α_t))` at `x`, a tangent
vector `v` at `x` is the value of the strict Moser vector field at time `t` exactly when
`α_t(v) = h_t` and `ι_v dα_t + dh_t + ∂_t α_t = 0`. -/
theorem eq_strictMoserVectorField_iff {v : TangentSpace I x} :
    v = α.strictMoserVectorField h t x ↔
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).val x ![v] = h (t, x) ∧
        ∀ w,
          mextDeriv (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).val x ![v, w] +
            mvfderiv I (fun y ↦ h (t, y)) x w =
              -(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val x
                ![w] := by
  rw [strictMoserVectorField_def,
    hc.eq_strictContactMoserVectorField_iff (mvfderiv_eq_mpullback_neg_timeDeriv hR)]
  simp only [map_neg, neg_toRoughForm, Pi.neg_apply, ContinuousAlternatingMap.neg_apply]

/-- **Vanishing of the strict Moser vector field.** If the slice `α_t` is a contact form and `h_t`
solves the Reeb-direction equation `R_(α_t) h_t = -(∂_t α_t)(R_(α_t))` at `x`, the strict Moser
vector field vanishes at time `t` and at `x` exactly when `h_t` vanishes there and
`dh_t = -∂_t α_t` there. -/
theorem strictMoserVectorField_eq_zero_iff :
    α.strictMoserVectorField h t x = 0 ↔
      h (t, x) = 0 ∧ ∀ w, mvfderiv I (fun y ↦ h (t, y)) x w =
        -(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val x ![w] := by
  rw [strictMoserVectorField_def,
    hc.strictContactMoserVectorField_eq_zero_iff (mvfderiv_eq_mpullback_neg_timeDeriv hR)]
  simp only [map_neg, neg_toRoughForm, Pi.neg_apply, ContinuousAlternatingMap.neg_apply]

end ReebDirection

/-- **The strict Moser equation for a family, at a point.** If the slice `α_t` is a contact form,
`h_t` is `C²` and `h_t` solves the Reeb-direction equation `R_(α_t) h_t = -(∂_t α_t)(R_(α_t))` on a
neighbourhood of `x`, then `L_(X_t) α_t + ∂_t α_t = 0` at `x`, evaluated on a tangent vector. -/
theorem mlieDerivForm_strictMoserVectorField_add_apply
    (hh : ContMDiff I 𝓘(ℝ) 2 fun y ↦ h (t, y)) {x : M}
    (hR : ∀ᶠ y in 𝓝 x, mvfderiv I (fun z ↦ h (t, z)) y
      ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField y) =
        -(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val y
          ![(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField y])
    (v : TangentSpace I x) :
    mlieDerivForm (α.strictMoserVectorField h t)
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).val x ![v] +
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val x ![v] = 0 := by
  have hL := hc.mlieDerivForm_strictContactMoserVectorField_apply
    (hc.mdifferentiable_strictContactMoserVectorField _ hh x)
    (hR.mono fun _ hy ↦ mvfderiv_eq_mpullback_neg_timeDeriv hy)
  rw [strictMoserVectorField_def, hL, map_neg, neg_toRoughForm, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, neg_add_cancel]

/-- **The strict Moser equation for a family.** If the slice `α_t` is a contact form and `h_t` is
`C²` and solves the Reeb-direction equation `R_(α_t) h_t = -(∂_t α_t)(R_(α_t))` everywhere, then
`L_(X_t) α_t + ∂_t α_t = 0`, evaluated on a tangent vector. -/
theorem mlieDerivForm_strictMoserVectorField_add (hh : ContMDiff I 𝓘(ℝ) 2 fun y ↦ h (t, y))
    (hR : ∀ y, mvfderiv I (fun z ↦ h (t, z)) y
      ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField y) =
        -(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val y
          ![(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField y])
    (x : M) (v : TangentSpace I x) :
    mlieDerivForm (α.strictMoserVectorField h t)
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).val x ![v] +
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val x ![v] = 0 :=
  mlieDerivForm_strictMoserVectorField_add_apply hc hh (.of_forall hR) v

end Slice

omit [FiniteDimensional ℝ E] in
/-- **Regularity of the strict Moser vector field at a point.** If the contact flat map of the
slice `α_t` is invertible at `x`, as it is when `α_t` is a contact form, and `h` is `C^(n+1)`, then
`(t, x) ↦ (x, X_t(x))` is `C^n` into the tangent bundle at `(t, x)`, for `n ≤ ∞`. -/
theorem contMDiffAt_strictMoserVectorField [CompleteSpace E] {n : WithTop ℕ∞} (hn : n ≤ ∞)
    (hh : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) (n + 1) h) {p : ℝ × M}
    (hc : ((mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).contactFlat
      p.2).IsInvertible) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun q : ℝ × M ↦ (⟨q.2, α.strictMoserVectorField h q.1 q.2⟩ : TangentBundle I M)) p :=
  contMDiffAt_sectionAlong_strictContactMoserVectorField (b := Prod.snd)
    (α := fun q : ℝ × M ↦ mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α)
    (β := fun q : ℝ × M ↦
      mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) (-α.timeDeriv))
    (h := fun q y ↦ h (q.1, y)) hc ((contMDiff_mpullback_prodMk α p).of_le hn)
    ((contMDiff_mextDeriv_mpullback_prodMk α p).of_le hn)
    ((contMDiff_mpullback_prodMk (-α.timeDeriv) p).of_le hn) ((hh p).of_le le_self_add)
    (ContMDiff.contMDiff_totalSpaceMk_mvfderiv_uncurry (f := fun t y ↦ h (t, y)) hh p)

variable (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
include hc

/-- The strict Moser vector field of a smooth family of contact forms and a `C^(n+1)`
time-dependent function depends `C^n` on time and point, for `n ≤ ∞`: `(t, x) ↦ (x, X_t(x))` is
`C^n` into the tangent bundle. -/
theorem contMDiff_strictMoserVectorField {n : WithTop ℕ∞} (hn : n ≤ ∞)
    (hh : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) (n + 1) h) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, α.strictMoserVectorField h p.1 p.2⟩ : TangentBundle I M)) :=
  fun p ↦ contMDiffAt_strictMoserVectorField hn hh ((hc p.1).isInvertible_contactFlat p.2)

/-- **The strict Moser equation for a family**, as an identity of forms at a point. If `h` is `C²`
and `h_t` solves the Reeb-direction equation `R_(α_t) h_t = -(∂_t α_t)(R_(α_t))` on a
neighbourhood of `x`, then the rate `ι_t^* L_{∂_t} α + L_{X_t} α_t` of the family along the strict
Moser vector field vanishes at `x`. This is the hypothesis of Moser's principle for families of
forms. -/
private theorem mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_strictMoserVectorField_apply
    (hh : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 2 h) {t : ℝ} {x : M}
    (hR : ∀ᶠ y in 𝓝 x, mvfderiv I (fun z ↦ h (t, z)) y
      ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField y) =
        -(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val y
          ![(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField y]) :
    (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α.val) +
        mlieDerivForm (α.strictMoserVectorField h t)
          (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α.val)) x = 0 := by
  ext v
  have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
  have hv0 := mlieDerivForm_strictMoserVectorField_add_apply (hc t)
    (hh.comp ((contMDiff_const (c := t)).prodMk contMDiff_id)) hR (v 0)
  rw [hv]
  simp only [coe_mpullback, coe_timeDeriv] at hv0
  simp only [Pi.add_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  rw [add_comm, hv0]

variable (hR : ∀ t x, mvfderiv I (fun y ↦ h (t, y)) x
    ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField x) =
      -(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val x
        ![(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField x])

variable [I.Boundaryless] [T2Space M]

include hR in
/-- **The strict Moser theorem along a complete flow.** On a manifold without boundary, let `α_t`
be a smooth family of contact forms and let `h_t` be a `C³` time-dependent function solving the
Reeb-direction equation `R_(α_t) h_t = -(∂_t α_t)(R_(α_t))`. If the suspension of the strict Moser
vector field is complete, for instance because the field has compact support, then its
time-dependent flow from `s` to `t` pulls `α_t` back to `α_s`. -/
theorem mpullback_timeDependentFlowOf_strictMoserVectorField
    (hh : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 3 h)
    (hcomplete : IsCompleteVectorField (timeDependentSuspensionField (α.strictMoserVectorField h)))
    (s t : ℝ) :
    TauCeti.mpullback I I (timeDependentFlowOf (α.strictMoserVectorField h) s t)
        (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α.val) =
      TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α.val :=
  mpullback_timeDependentFlowOf_mpullback_prodMk_eq
    (contMDiff_strictMoserVectorField hc (n := 2) (by norm_num) hh) hcomplete
    (α.contMDiff.of_le (by simp))
    (fun t ↦ funext fun _ ↦
      mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_strictMoserVectorField_apply hc
        (hh.of_le (by norm_num)) (.of_forall (hR t)))
    s t

/-! ### The relative strict Moser isotopy -/

section Relative

variable (hh : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ h)
include hh

/-- **The strict Moser partial isotopy.** The time-dependent flow of the strict Moser vector field
of a smooth family of contact forms `α_t` and a smooth function `h`, from time `s` to time `t`, as
a smooth partial diffeomorphism of `M`. Its source is the open set of points from which the flow
is defined from time `s` up to time `t`, and its inverse is the flow from `t` back to `s`. Where
`h_t` solves the Reeb-direction equation `R_(α_t) h_t = -(∂_t α_t)(R_(α_t))` along a trajectory,
it pulls `α_t` back to `α_s` at its starting point
(`TauCeti.SmoothForm.mpullback_strictMoserPartialDiffeomorph_apply_of_forall_mem_uIcc`). No
compactness is needed. -/
def strictMoserPartialDiffeomorph (s t : ℝ) : PartialDiffeomorph I I M M ∞ :=
  timeDependentFlowPartialDiffeomorph le_top
    (contMDiff_strictMoserVectorField hc le_rfl (hh.of_le (by simp))) s t

/-- The strict Moser partial isotopy is the time-dependent flow of the strict Moser vector
field. -/
@[simp]
theorem strictMoserPartialDiffeomorph_apply (s t : ℝ) (x : M) :
    strictMoserPartialDiffeomorph hc hh s t x =
      timeDependentFlowOf (α.strictMoserVectorField h) s t x :=
  timeDependentFlowPartialDiffeomorph_apply _ _ s t x

/-- The inverse of the strict Moser partial isotopy from `s` to `t` is the time-dependent flow of
the strict Moser vector field from `t` to `s`. -/
@[simp]
theorem strictMoserPartialDiffeomorph_symm_apply (s t : ℝ) (x : M) :
    (strictMoserPartialDiffeomorph hc hh s t).toPartialEquiv.symm x =
      timeDependentFlowOf (α.strictMoserVectorField h) t s x :=
  timeDependentFlowPartialDiffeomorph_symm_apply _ _ s t x

/-- A point lies in the source of the strict Moser partial isotopy from `s` to `t` exactly when
the flow of the strict Moser vector field from `(s, x)` is defined up to time `t`. -/
@[simp]
theorem mem_strictMoserPartialDiffeomorph_source_iff {s t : ℝ} {x : M} :
    x ∈ (strictMoserPartialDiffeomorph hc hh s t).source ↔
      ((s, t), x) ∈ timeDependentFlowDomain (α.strictMoserVectorField h) :=
  mem_timeDependentFlowPartialDiffeomorph_source_iff _ _

/-- A point lies in the target of the strict Moser partial isotopy from `s` to `t` exactly when
the flow of the strict Moser vector field from `(t, x)` is defined back to time `s`. -/
@[simp]
theorem mem_strictMoserPartialDiffeomorph_target_iff {s t : ℝ} {x : M} :
    x ∈ (strictMoserPartialDiffeomorph hc hh s t).target ↔
      ((t, s), x) ∈ timeDependentFlowDomain (α.strictMoserVectorField h) :=
  mem_timeDependentFlowPartialDiffeomorph_target_iff _ _

/-- The strict Moser partial isotopy depends smoothly on the final time and the point, on the open
set of pairs `(t, x)` for which the flow from `(s, x)` is defined up to time `t`. -/
theorem contMDiffOn_strictMoserPartialDiffeomorph (s : ℝ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M ↦ strictMoserPartialDiffeomorph hc hh s p.1 p.2)
      {p | ((s, p.1), p.2) ∈ timeDependentFlowDomain (α.strictMoserVectorField h)} := by
  simp only [strictMoserPartialDiffeomorph_apply]
  exact (contMDiffOn_timeDependentFlowOf le_top
    (contMDiff_strictMoserVectorField hc le_rfl (hh.of_le (by simp)))).comp
    (((contMDiff_const (c := s)).prodMk contMDiff_fst).prodMk contMDiff_snd).contMDiffOn
    fun _ hp ↦ hp

/-- **The strict Moser theorem along a trajectory.** Let `α_t` be a smooth family of contact forms
on a boundaryless manifold, `h` a smooth time-dependent function and `x` a point of the source of
the strict Moser partial isotopy `φ_(s,t)`. If at every time `u` between `s` and `t` the slice
`h_u` solves the Reeb-direction equation `R_(α_u) h_u = -(∂_t α_u)(R_(α_u))` on a neighbourhood of
the point `φ_(s,u) x` of the trajectory of `x`, then `φ_(s,t)` pulls `α_t` back to `α_s` at `x`.
The Reeb-direction equation is assumed only near the trajectory of `x`; `h` must still be smooth
everywhere. -/
theorem mpullback_strictMoserPartialDiffeomorph_apply_of_forall_mem_uIcc {s t : ℝ} {x : M}
    (hx : x ∈ (strictMoserPartialDiffeomorph hc hh s t).source)
    (hR : ∀ u ∈ Set.uIcc s t, ∀ᶠ y in 𝓝 (strictMoserPartialDiffeomorph hc hh s u x),
      mvfderiv I (fun z ↦ h (u, z)) y
        ((mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField y) =
          -(mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val y
            ![(mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField
              y]) :
    TauCeti.mpullback I I (strictMoserPartialDiffeomorph hc hh s t)
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).val x =
      (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).val x := by
  have hφ (u : ℝ) : ⇑(strictMoserPartialDiffeomorph hc hh s u) =
      timeDependentFlowOf (α.strictMoserVectorField h) s u :=
    funext (strictMoserPartialDiffeomorph_apply hc hh s u)
  have hpull := mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc_of_mem
    (contMDiff_strictMoserVectorField hc (n := 2) (by norm_num) (hh.of_le (by simp)))
    ((mem_strictMoserPartialDiffeomorph_source_iff hc hh).1 hx)
    (fun _ _ ↦ (α.contMDiff.of_le (by simp)).contMDiffAt)
    (fun u hu ↦ mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_strictMoserVectorField_apply hc
      (hh.of_le (by simp)) (by simpa only [hφ] using hR u hu))
  simpa only [coe_mpullback, hφ] using hpull

include hR in
/-- **The strict Moser theorem along the domain of the flow.** On a manifold without boundary, let
`α_t` be a smooth family of contact forms and let `h_t` be a smooth time-dependent function solving
the Reeb-direction equation `R_(α_t) h_t = -(∂_t α_t)(R_(α_t))`. On the source of the strict Moser
partial isotopy `φ_(s,t)`, it pulls `α_t` back to `α_s`. -/
theorem mpullback_strictMoserPartialDiffeomorph_apply {s t : ℝ} {x : M}
    (hx : x ∈ (strictMoserPartialDiffeomorph hc hh s t).source) :
    TauCeti.mpullback I I (strictMoserPartialDiffeomorph hc hh s t)
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).val x =
      (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).val x :=
  mpullback_strictMoserPartialDiffeomorph_apply_of_forall_mem_uIcc hc hh hx
    fun u _ ↦ .of_forall (hR u)

/-- A point at which the strict Moser vector field vanishes at all times lies in the source of the
strict Moser partial isotopy between any two times. -/
theorem mem_strictMoserPartialDiffeomorph_source {x : M}
    (hx : ∀ u, α.strictMoserVectorField h u x = 0) (s t : ℝ) :
    x ∈ (strictMoserPartialDiffeomorph hc hh s t).source :=
  (mem_strictMoserPartialDiffeomorph_source_iff hc hh).2
    (mem_timeDependentFlowDomain_of_forall_eq_zero hx s t)

/-- A point at which the strict Moser vector field vanishes at all times lies in the target of the
strict Moser partial isotopy between any two times. -/
theorem mem_strictMoserPartialDiffeomorph_target {x : M}
    (hx : ∀ u, α.strictMoserVectorField h u x = 0) (s t : ℝ) :
    x ∈ (strictMoserPartialDiffeomorph hc hh s t).target :=
  (mem_strictMoserPartialDiffeomorph_target_iff hc hh).2
    (mem_timeDependentFlowDomain_of_forall_eq_zero hx t s)

/-- The strict Moser partial isotopy fixes every point at which the strict Moser vector field
vanishes at all times. -/
theorem strictMoserPartialDiffeomorph_apply_eq_self {x : M}
    (hx : ∀ u, α.strictMoserVectorField h u x = 0) (s t : ℝ) :
    strictMoserPartialDiffeomorph hc hh s t x = x := by
  rw [strictMoserPartialDiffeomorph_apply]
  exact timeDependentFlowOf_eq_self_of_forall_eq_zero
    (contMDiff_strictMoserVectorField hc (n := 1) (by simp) (hh.of_le (by simp))) hx s t

/-- **The relative strict Moser theorem.** Let `α_t` be a smooth family of contact forms on a
boundaryless manifold and `h` a smooth time-dependent function. Let `K` be a set of points at each
of which the strict Moser vector field vanishes at all times, and let `U ⊆ ℝ × M` be an open set
on which `h_t` solves the Reeb-direction equation `R_(α_t) h_t = -(∂_t α_t)(R_(α_t))` and which
contains `(u, x)` for every `x ∈ K` and every time `u` between `s` and `t`. Then there is a smooth
partial diffeomorphism `φ` of `M`, whose source and target are open neighbourhoods of `K`, which
fixes every point of `K` and pulls `α_t` back to `α_s` on its source. Neither `K` nor `M` need be
compact, and `K` need not be closed. -/
theorem exists_partialDiffeomorph_mpullback_eq {K : Set M}
    (hK : ∀ x ∈ K, ∀ u, α.strictMoserVectorField h u x = 0) {U : Set (ℝ × M)} (hU : IsOpen U)
    {s t : ℝ} (hKU : ∀ x ∈ K, ∀ u ∈ Set.uIcc s t, (u, x) ∈ U)
    (hR : ∀ p ∈ U, mvfderiv I (fun y ↦ h (p.1, y)) p.2
      ((mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField p.2) =
        -(mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val p.2
          ![(mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField
            p.2]) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, TauCeti.mpullback I I φ
          (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).val x =
        (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).val x := by
  have hX := contMDiff_strictMoserVectorField hc (n := 1) (by simp) (hh.of_le (by simp))
  set W := {x | ∀ u ∈ Set.uIcc s t,
    ((s, u), x) ∈ timeDependentFlowDomain (α.strictMoserVectorField h) ∧
      (u, timeDependentFlowOf (α.strictMoserVectorField h) s u x) ∈ U}
  have hW : IsOpen W := isOpen_setOf_forall_timeDependentFlowOf_mem hX isCompact_uIcc hU s
  -- The points of `K` stay put, so their trajectories stay in `U`.
  have hKW (x : M) (hx : x ∈ K) : x ∈ W := fun u hu ↦
    ⟨mem_timeDependentFlowDomain_of_forall_eq_zero (hK x hx) s u, by
      rw [← strictMoserPartialDiffeomorph_apply hc hh,
        strictMoserPartialDiffeomorph_apply_eq_self hc hh (hK x hx)]
      exact hKU x hx u hu⟩
  refine ⟨(strictMoserPartialDiffeomorph hc hh s t).restrOpen W hW, fun x hx ↦ ?_,
    fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [PartialDiffeomorph.restrOpen_source]
    exact ⟨mem_strictMoserPartialDiffeomorph_source hc hh (hK x hx) s t, hKW x hx⟩
  · rw [PartialDiffeomorph.restrOpen_target, Set.mem_inter_iff, Set.mem_preimage,
      strictMoserPartialDiffeomorph_symm_apply,
      timeDependentFlowOf_eq_self_of_forall_eq_zero hX (hK x hx)]
    exact ⟨mem_strictMoserPartialDiffeomorph_target hc hh (hK x hx) s t, hKW x hx⟩
  · rw [PartialDiffeomorph.coe_restrOpen]
    exact strictMoserPartialDiffeomorph_apply_eq_self hc hh (hK x hx) s t
  · -- Along the trajectory of a point of the source, `h` solves the Reeb-direction equation.
    rw [PartialDiffeomorph.restrOpen_source] at hx
    rw [PartialDiffeomorph.coe_restrOpen]
    refine mpullback_strictMoserPartialDiffeomorph_apply_of_forall_mem_uIcc hc hh hx.1
      fun u hu ↦ ?_
    rw [strictMoserPartialDiffeomorph_apply]
    exact Filter.mem_of_superset
      ((hU.preimage (Continuous.prodMk_right u)).mem_nhds (hx.2 u hu).2) fun y hy ↦ hR (u, y) hy

end Relative

/-! ### Solving the Reeb-direction equation from a transverse slice -/

section Transport

variable [TopologicalSpace.PseudoMetrizableSpace M] [SigmaCompactSpace M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]
  [BoundarylessManifold J S] [TopologicalSpace.PseudoMetrizableSpace S] {ι : S → M}

/-- **Solving the Reeb-direction equation from a transverse slice.** Let `α_t` be a smooth family
of contact forms on a boundaryless σ-compact manifold `M`, and let `ι : S → M` be a smooth
embedding with closed image of a boundaryless manifold of one dimension less, to which every Reeb
vector field `R_(α_t)` is transverse. Then there is a smooth time-dependent function `h_t`,
vanishing on the image of `ι` at all times, which solves the Reeb-direction equation
`R_(α_t) h_t = -(∂_t α_t)(R_(α_t))` on an open neighbourhood of `ℝ × ι(S)` in `ℝ × M`.

This supplies the function `h` and the open set of
`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq`. It is the transport equation for the
vertical field `(t, x) ↦ (0, R_(α_t)(x))` on `ℝ × M`, solved near the transverse hypersurface
`ℝ × ι(S)` (`TauCeti.exists_contMDiff_mvfderiv_eq_of_isTransverseAlong`). -/
theorem exists_contMDiff_mvfderiv_reebVectorField_eq_of_isTransverseAlong
    (hι : ContMDiff J I ∞ ι) (himm : ∀ s, Function.Injective (mfderiv J I ι s))
    (hind : Topology.IsInducing ι) (hclosed : _root_.IsClosed (Set.range ι))
    (htr : ∀ t, IsTransverseAlong J
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField ι)
    (hdim : Module.finrank ℝ E' + 1 = Module.finrank ℝ E) :
    ∃ U : Set (ℝ × M), IsOpen U ∧ (∀ t s, (t, ι s) ∈ U) ∧
      ∃ h : ℝ × M → ℝ, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ h ∧ (∀ t s, h (t, ι s) = 0) ∧ ∀ p ∈ U,
        mvfderiv I (fun y ↦ h (p.1, y)) p.2
            ((mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField
              p.2) =
          -(mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val p.2
            ![(mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField
              p.2] := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · exact ⟨∅, isOpen_empty, fun _ s ↦ isEmptyElim s, 0, contMDiff_const, fun _ s ↦ isEmptyElim s,
      fun _ hp ↦ hp.elim⟩
  have : FiniteDimensional ℝ E' := by
    have : FiniteDimensional ℝ (TangentSpace I (ι s₀)) := inferInstanceAs (FiniteDimensional ℝ E)
    exact FiniteDimensional.of_injective (mfderiv J I ι s₀).toLinearMap (himm s₀)
  -- The slice `ℝ × ι(S)` is a closed embedded hypersurface of `ℝ × M`.
  have himm' (q : ℝ × S) : Function.Injective
      (mfderiv (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod I) (Prod.map id ι) q) := by
    rw [mfderiv_prodMap mdifferentiableAt_id (hι.mdifferentiableAt (by simp)), mfderiv_id]
    exact Function.Injective.prodMap (fun _ _ h ↦ h) (himm q.2)
  have htr' : IsTransverseAlong (𝓘(ℝ, ℝ).prod J)
      (verticalField 𝓘(ℝ, ℝ) fun t ↦
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField)
      (Prod.map id ι) := by
    refine isTransverseAlong_iff.2 fun q ⟨w, hw⟩ ↦ isTransverseAlong_iff.1 (htr q.1) q.2
      ⟨w.2, ?_⟩
    rw [mfderiv_prodMap mdifferentiableAt_id (hι.mdifferentiableAt (by simp))] at hw
    exact (congrArg Prod.snd hw).trans (verticalField_snd _ _)
  obtain ⟨U, hU, hιU, h, hh, h0, hZh⟩ := exists_contMDiff_mvfderiv_eq_of_isTransverseAlong
    (contMDiff_verticalField (contMDiff_reebVectorField_mpullback_prodMk α hc))
    (contMDiff_apply_reebVectorField_mpullback_prodMk α α.timeDeriv hc).neg
    (contMDiff_id.prodMap hι) himm' (Topology.IsInducing.id.prodMap hind)
    (by rw [Set.range_prodMap, Set.range_id]; exact isClosed_univ.prod hclosed) htr'
    (by rw [Module.finrank_prod, Module.finrank_prod, ← hdim]; ring)
  refine ⟨U, hU, fun t s ↦ hιU ⟨(t, s), rfl⟩, h, hh, fun t s ↦ h0 (t, s), fun p hp ↦ ?_⟩
  -- The derivative of the slice `h_t` along `R_(α_t)` is that of `h` along `(0, R_(α_t))`.
  rw [← hZh p hp, show (fun y ↦ h (p.1, y)) = Function.curry h p.1 from rfl,
    mvfderiv_curry_right p.1 p.2 (hh.mdifferentiableAt (by simp)), verticalField_apply]
  -- `inr` sends `v` to `(0, v)`; the product tangent space at `(p.1, p.2)` is that at `p`.
  rfl

end Transport

/-! ### The strict Moser isotopy on compact manifolds -/

variable [CompactSpace M]

/-- On a compact manifold, the strict Moser vector field of a smooth family of contact forms and a
`C²` time-dependent function has a complete suspension: its time-dependent flow is defined for all
times. -/
theorem isCompleteVectorField_timeDependentSuspensionField_strictMoserVectorField
    (hh : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 2 h) :
    IsCompleteVectorField (timeDependentSuspensionField (α.strictMoserVectorField h)) :=
  isCompleteVectorField_timeDependentSuspensionField
    (contMDiff_strictMoserVectorField hc (n := 1) (by simp) (by norm_num [hh])) isCompact_univ
    (by simp)

variable (hh : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ h)
include hh

/-- **The strict Moser isotopy.** On a compact manifold without boundary, the time-dependent flow
of the strict Moser vector field of a smooth family of contact forms `α_t` and a smooth function
`h`, from time `s` to time `t`, as a diffeomorphism. When `h_t` solves the Reeb-direction equation
`R_(α_t) h_t = -(∂_t α_t)(R_(α_t))`, it pulls `α_t` back to `α_s`
(`TauCeti.SmoothForm.isStrictContactomorphism_strictMoserDiffeomorph`). -/
def strictMoserDiffeomorph (s t : ℝ) : M ≃ₘ⟮I, I⟯ M :=
  timeDependentFlowDiffeomorph
    (isCompleteVectorField_timeDependentSuspensionField_strictMoserVectorField hc
      (hh.of_le (by simp))) le_top
    (contMDiff_strictMoserVectorField hc le_rfl (hh.of_le (by simp))) s t

/-- The strict Moser isotopy is the time-dependent flow of the strict Moser vector field. -/
theorem strictMoserDiffeomorph_apply (s t : ℝ) (x : M) :
    strictMoserDiffeomorph hc hh s t x = timeDependentFlowOf (α.strictMoserVectorField h) s t x :=
  timeDependentFlowDiffeomorph_apply _ _ _ s t x

/-- The inverse of the strict Moser isotopy from `s` to `t`, applied to a point, is the strict
Moser isotopy from `t` to `s`. -/
theorem strictMoserDiffeomorph_symm_apply (s t : ℝ) (x : M) :
    (strictMoserDiffeomorph hc hh s t).symm x = strictMoserDiffeomorph hc hh t s x :=
  (timeDependentFlowDiffeomorph_symm_apply _ _ _ s t x).trans
    (strictMoserDiffeomorph_apply hc hh t s x).symm

/-- The inverse of the strict Moser isotopy from `s` to `t` is the strict Moser isotopy from `t` to
`s`. -/
@[simp]
theorem strictMoserDiffeomorph_symm (s t : ℝ) :
    (strictMoserDiffeomorph hc hh s t).symm = strictMoserDiffeomorph hc hh t s :=
  Diffeomorph.ext (strictMoserDiffeomorph_symm_apply hc hh s t)

/-- The strict Moser isotopy from a time to itself fixes every point. -/
theorem strictMoserDiffeomorph_self_apply (s : ℝ) (x : M) :
    strictMoserDiffeomorph hc hh s s x = x := by
  rw [strictMoserDiffeomorph_apply, timeDependentFlowOf_self]

/-- The strict Moser isotopy from a time to itself is the identity. -/
@[simp]
theorem strictMoserDiffeomorph_self (s : ℝ) :
    strictMoserDiffeomorph hc hh s s = Diffeomorph.refl I M ∞ :=
  Diffeomorph.ext (strictMoserDiffeomorph_self_apply hc hh s)

/-- The strict Moser isotopy composes: flowing from `r` to `s` and then from `s` to `t` is flowing
from `r` to `t`. -/
@[simp]
theorem strictMoserDiffeomorph_strictMoserDiffeomorph (r s t : ℝ) (x : M) :
    strictMoserDiffeomorph hc hh s t (strictMoserDiffeomorph hc hh r s x) =
      strictMoserDiffeomorph hc hh r t x := by
  simp only [strictMoserDiffeomorph_apply]
  exact timeDependentFlowOf_trans
    (isCompleteVectorField_timeDependentSuspensionField_strictMoserVectorField hc
      (hh.of_le (by simp)))
    (contMDiff_strictMoserVectorField hc (n := 1) (by simp) (hh.of_le (by simp))) r s t x

/-- The strict Moser isotopy from `r` to `s` followed by the strict Moser isotopy from `s` to `t`
is the strict Moser isotopy from `r` to `t`. -/
@[simp]
theorem strictMoserDiffeomorph_trans_strictMoserDiffeomorph (r s t : ℝ) :
    (strictMoserDiffeomorph hc hh r s).trans (strictMoserDiffeomorph hc hh s t) =
      strictMoserDiffeomorph hc hh r t :=
  Diffeomorph.ext (strictMoserDiffeomorph_strictMoserDiffeomorph hc hh r s t)

/-- The strict Moser isotopy depends smoothly on the initial time, the final time and the point. -/
theorem contMDiff_strictMoserDiffeomorph :
    ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
      (fun p : (ℝ × ℝ) × M ↦ strictMoserDiffeomorph hc hh p.1.1 p.1.2 p.2) := by
  simp only [strictMoserDiffeomorph_apply]
  exact contMDiff_timeDependentFlowOf
    (isCompleteVectorField_timeDependentSuspensionField_strictMoserVectorField hc
      (hh.of_le (by simp))) le_top
    (contMDiff_strictMoserVectorField hc le_rfl (hh.of_le (by simp)))

/-- The strict Moser isotopy fixes every point at which the strict Moser vector field vanishes at
all times. -/
theorem strictMoserDiffeomorph_apply_eq_self {x : M} (hx : ∀ u, α.strictMoserVectorField h u x = 0)
    (s t : ℝ) : strictMoserDiffeomorph hc hh s t x = x := by
  rw [strictMoserDiffeomorph_apply]
  exact timeDependentFlowOf_eq_self_of_forall_eq_zero
    (contMDiff_strictMoserVectorField hc (n := 1) (by simp) (hh.of_le (by simp))) hx s t

include hR

/-- **The strict Moser theorem for a family of contact forms**, as an identity of forms. On a
compact manifold without boundary, let `α_t` be a smooth family of contact forms and let `h_t` be a
smooth time-dependent function solving the Reeb-direction equation
`R_(α_t) h_t = -(∂_t α_t)(R_(α_t))`. Then the strict Moser isotopy from `s` to `t` pulls `α_t`
back to `α_s`. -/
@[simp]
theorem mpullback_strictMoserDiffeomorph (s t : ℝ) :
    mpullback (strictMoserDiffeomorph hc hh s t) (strictMoserDiffeomorph hc hh s t).contMDiff
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) =
      mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α := by
  have hφ : ⇑(strictMoserDiffeomorph hc hh s t) =
      timeDependentFlowOf (α.strictMoserVectorField h) s t :=
    funext (strictMoserDiffeomorph_apply hc hh s t)
  refine Subtype.ext ?_
  simpa only [coe_mpullback, hφ] using mpullback_timeDependentFlowOf_strictMoserVectorField hc hR
    (hh.of_le (by simp))
    (isCompleteVectorField_timeDependentSuspensionField_strictMoserVectorField hc
      (hh.of_le (by simp))) s t

/-- **The strict Moser theorem for a family of contact forms.** On a compact manifold without
boundary, let `α_t` be a smooth family of contact forms and let `h_t` be a smooth time-dependent
function solving the Reeb-direction equation `R_(α_t) h_t = -(∂_t α_t)(R_(α_t))`. Then the strict
Moser isotopy from `s` to `t` pulls `α_t` back to `α_s`: it is a strict contactomorphism. -/
theorem isStrictContactomorphism_strictMoserDiffeomorph (s t : ℝ) :
    (strictMoserDiffeomorph hc hh s t).IsStrictContactomorphism
      (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α)
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) :=
  Diffeomorph.isStrictContactomorphism_def.2 (mpullback_strictMoserDiffeomorph hc hR hh s t)

end Family

end TauCeti.SmoothForm
