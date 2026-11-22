/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Contact.Jacobi
public import TauCeti.Geometry.Manifold.Distribution.Preserving

/-!
# Contact vector fields of a contact structure

A **contact vector field** of a contact structure `ξ` is a vector field preserving `ξ`
(`TauCeti.PreservesDistribution I ξ X`): its Lie bracket with every smooth vector field tangent to
`ξ` is tangent to `ξ`. This notion involves only the hyperplane field, so it applies to contact
structures that are not cooriented, and are therefore not the kernel of any global contact form.
The contact Hamiltonian vector fields `X_f` of a chosen contact form are recovered as the contact
vector fields of its kernel, and the Jacobi bracket of functions as the Lie bracket of contact
vector fields, read in the trivialization of the contact line `TM ⧸ ξ` given by that form.

**A contact vector field is determined by its section of the contact line.** A contact vector
field that is differentiable at `x` and tangent to `ξ` near `x` vanishes at `x`
(`TauCeti.PreservesDistribution.apply_eq_zero`), since the Levi form
`L_ξ(u, v) = -[U, V] mod ξ` then pairs its value trivially with all of `ξ x` and is nondegenerate.
Consequently two differentiable contact vector fields with the same class `[X x] ∈ T_x M ⧸ ξ x`
at every point are equal (`TauCeti.PreservesDistribution.eq_of_forall_mkQ_eq`). Together with the
closure of smooth contact vector fields under the Lie bracket
(`TauCeti.PreservesDistribution.mlieBracket`), the class of `[X, Y]` modulo `ξ` is therefore a
bracket of the sections `[X]`, `[Y]` of the contact line that come from smooth contact vector
fields, defined without choosing a contact form or a coorientation.

**Contact forms.** Let `α` be a one-form vanishing nowhere, with kernel `ξ = ker α`. A vector
field `X` preserves `ker α` exactly when `L_X α` vanishes on `ker α` at every point
(`TauCeti.SmoothForm.preservesDistribution_kerDistribution_iff_mlieDerivForm`), that is, when
`L_X α` is a multiple of `α`. When `α` is a contact form, the differentiable contact vector fields
of `ker α` are therefore exactly the contact Hamiltonian vector fields of their Hamiltonians `α(X)`:

`X` preserves `ker α` ↔ `X = X_(α(X))`

(`TauCeti.SmoothForm.IsContactForm.preservesDistribution_kerDistribution_iff`,
`TauCeti.SmoothForm.IsContactForm.preservesDistribution_kerDistribution_iff_eq`). In this
trivialization the contact-line bracket is the Jacobi bracket of the Hamiltonians,

`α([X, Y]) = {α(X), α(Y)}_α`

(`TauCeti.SmoothForm.IsContactForm.apply_mlieBracket_eq_jacobiBracket`). Since the left side is
defined by `ξ` alone, the Jacobi brackets of two contact forms with the same kernel are related by
the multiplier between the forms, as in `TauCeti.SmoothForm.IsContactForm.jacobiBracket_of_eq_smul`.

## Main results

* `TauCeti.PreservesDistribution.apply_eq_zero`: a contact vector field tangent to a contact
  structure near a point vanishes there; `TauCeti.PreservesDistributionAt.apply_eq_zero` only
  assumes that the field preserves the contact structure at that point.
* `TauCeti.PreservesDistribution.eq_of_forall_mkQ_eq`: a contact vector field is determined by its
  section of the contact line.
* `TauCeti.SmoothForm.preservesDistribution_kerDistribution_iff_mlieDerivForm`: `X` preserves
  `ker α` exactly when `L_X α` vanishes on `ker α`.
* `TauCeti.SmoothForm.IsContactHamiltonianVectorField.preservesDistribution`: contact Hamiltonian
  vector fields are contact vector fields.
* `TauCeti.SmoothForm.IsContactForm.preservesDistribution_kerDistribution_iff`: for a contact form,
  the contact vector fields of `ker α` are the contact Hamiltonian vector fields.
* `TauCeti.SmoothForm.IsContactForm.apply_mlieBracket_eq_jacobiBracket`: the bracket of contact
  vector fields is the Jacobi bracket of their Hamiltonians.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.3 (contact vector fields and contact Hamiltonians).
* P. Libermann, C.-M. Marle, *Symplectic Geometry and Analytical Mechanics*, D. Reidel, 1987,
  Chapter V, Sections 13–14 (infinitesimal automorphisms of a contact structure and the Lie
  algebra of sections of the contact line).
-/

public section

open Filter VectorField
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {X Y : Π x : M, TangentSpace I x}

/-! ### Contact vector fields of a contact structure -/

section ContactDistribution

variable [IsManifold I 2 M] {D : Π x : M, Submodule ℝ (TangentSpace I x)}

/-- **A vector field preserving a contact structure at a point and tangent to it there vanishes.**
If a vector field `X` preserves a smooth contact structure `D` at `x`, is differentiable at `x` and
is tangent to `D` near `x`, then `X x = 0`: the Levi form of `D` pairs `X x` trivially with all of
`D x`. -/
theorem PreservesDistributionAt.apply_eq_zero (hD : IsContactDistribution I ∞ D) {x : M}
    (hX : PreservesDistributionAt I D X x) (hXd : MDiffAt (T% X) x)
    (hXD : ∀ᶠ y in 𝓝 x, X y ∈ D y) : X x = 0 := by
  have hDs := hD.isContMDiffDistribution
  -- The Levi form vanishes on `X x`: test it against a smooth extension of each `v ∈ D x`.
  have hL : distributionLeviForm D x ⟨X x, hXD.self_of_nhds⟩ = 0 := by
    ext v
    obtain ⟨U, hU, hxU, W, hW, hWD, hWx⟩ := hDs.exists_contMDiffOn_apply_eq v
    have hWd : MDiffAt (T% W) x := (hW.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
    rw [show v = ⟨W x, hWD x hxU⟩ from Subtype.ext hWx.symm, LinearMap.zero_apply]
    exact (distributionLeviForm_apply_eq_zero_iff hDs (by simp) hXd hWd hXD
      (eventually_of_mem (hU.mem_nhds hxU) hWD)).2 (preservesDistributionAt_iff.1 hX hU hxU hW hWD)
  have h := (hD.bijective_distributionLeviForm x).injective (hL.trans (map_zero _).symm)
  exact congrArg Subtype.val h

namespace PreservesDistribution

/-- **A contact vector field tangent to the contact structure vanishes.** If a vector field `X`
preserves a smooth contact structure `D`, is differentiable at `x` and is tangent to `D` near `x`,
then `X x = 0`: the Levi form of `D` pairs `X x` trivially with all of `D x`. -/
theorem apply_eq_zero (hD : IsContactDistribution I ∞ D) (hX : PreservesDistribution I D X)
    {x : M} (hXd : MDiffAt (T% X) x) (hXD : ∀ᶠ y in 𝓝 x, X y ∈ D y) : X x = 0 :=
  (hX.preservesDistributionAt x).apply_eq_zero hD hXd hXD

/-- **A contact vector field is determined by its section of the contact line.** Two
differentiable vector fields preserving a smooth contact structure `D`, whose classes in the
contact line `T_y M ⧸ D y` agree at every point `y`, are equal. -/
theorem eq_of_forall_mkQ_eq (hD : IsContactDistribution I ∞ D) (hX : PreservesDistribution I D X)
    (hY : PreservesDistribution I D Y) (hXd : MDiff (T% X)) (hYd : MDiff (T% Y))
    (h : ∀ y, (D y).mkQ (X y) = (D y).mkQ (Y y)) : X = Y := by
  have hsub : MDiff (T% (X - Y)) := mdifferentiable_sub_section hXd hYd
  funext y
  rw [← sub_eq_zero]
  exact (hX.sub hY hXd hYd).apply_eq_zero hD (hsub y)
    (Eventually.of_forall fun z ↦ (Submodule.Quotient.eq _).1 (h z))

end PreservesDistribution

end ContactDistribution

/-! ### Kernels of one-forms -/

namespace SmoothForm

variable [IsManifold I ∞ M] {α : SmoothForm I M ℝ 1} {f : M → ℝ}

/-- **A vector field preserves `ker α` exactly when `L_X α` vanishes on `ker α`**, that is, when
`L_X α` is a multiple of `α`. The one-form `α` is required to vanish nowhere, so that `ker α` is a
smooth hyperplane field; it need not be a contact form. -/
theorem preservesDistribution_kerDistribution_iff_mlieDerivForm (hα : ∀ x, α.val x ≠ 0) :
    PreservesDistribution I α.kerDistribution X ↔
      ∀ x, ∀ v ∈ α.kerDistribution x, mlieDerivForm X α.val x ![v] = 0 := by
  -- The formula `L_X α (W) = X(α(W)) - α([X, W])` for `W` tangent to `ker α` near the point,
  -- where `α(W)` vanishes near the point, so that its derivative vanishes.
  have key {x : M} {W : Π y : M, TangentSpace I y} (hWd : MDiffAt (T% W) x)
      (hW : ∀ᶠ y in 𝓝 x, W y ∈ α.kerDistribution y) :
      mlieDerivForm X α.val x ![W x] = -α.val x ![mlieBracket I X W x] := by
    rw [mlieDerivForm_apply_one (α.mdifferentiableAt x) hWd,
      Filter.EventuallyEq.mvfderiv_eq (f := fun _ ↦ (0 : ℝ))
        (hW.mono fun y hy ↦ mem_kerDistribution.1 hy), mvfderiv_const,
      zero_apply, zero_sub]
  constructor
  · intro hX x v hv
    let _ : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
    obtain ⟨U, hU, hxU, W, hW, hWD, hWx⟩ :=
      (isContMDiffDistribution_kerDistribution (n := ∞) hα).exists_contMDiffOn_apply_eq
        (⟨v, hv⟩ : α.kerDistribution x)
    have hWd : MDiffAt (T% W) x := (hW.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
    have hWx' : W x = v := hWx
    rw [← hWx', key hWd (eventually_of_mem (hU.mem_nhds hxU) hWD),
      mem_kerDistribution.1 (preservesDistribution_iff.1 hX hU hW hWD x hxU), neg_zero]
  · refine fun h ↦ preservesDistribution_iff.2 fun U hU V hV hVD x hx ↦ ?_
    have hVd : MDiffAt (T% V) x := (hV.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have hx' := h x (V x) (hVD x hx)
    rw [key hVd (eventually_of_mem (hU.mem_nhds hx) hVD), neg_eq_zero] at hx'
    exact mem_kerDistribution.2 hx'

omit [FiniteDimensional ℝ E] in
/-- **Contact Hamiltonian vector fields are contact vector fields**: a differentiable contact
Hamiltonian vector field of a one-form `α` preserves `ker α`. -/
theorem IsContactHamiltonianVectorField.preservesDistribution
    (hX : α.IsContactHamiltonianVectorField f X) (hXd : MDiff (T% X)) :
    PreservesDistribution I α.kerDistribution X :=
  preservesDistribution_iff.2 fun _ hU _ hV hVD x hx ↦ hX.mlieBracket_mem_kerDistribution (hXd x)
    ((hV.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
    (eventually_of_mem (hU.mem_nhds hx) hVD)

namespace IsContactForm

variable (hα : α.IsContactForm)
include hα

/-- **The contact vector fields of a contact form are its contact Hamiltonian vector fields.** A
differentiable vector field `X` preserves the contact structure `ker α` exactly when it is a contact
Hamiltonian vector field of its Hamiltonian `α(X)`. -/
theorem preservesDistribution_kerDistribution_iff (hXd : MDiff (T% X)) :
    PreservesDistribution I α.kerDistribution X ↔
      α.IsContactHamiltonianVectorField (fun y ↦ α.val y ![X y]) X := by
  refine ⟨fun hX ↦ hα.isContactHamiltonianVectorField_iff_kerDistribution.2 fun x ↦
    ⟨rfl, fun v hv ↦ ?_⟩, fun hX ↦ hX.preservesDistribution hXd⟩
  -- Cartan's formula `L_X α = ι_X dα + d(α(X))`, where `L_X α` vanishes on `ker α`.
  have h := mlieDerivForm_apply_eq_mextDeriv_add (fun _ ↦ rfl) (α.mdifferentiableAt x) (hXd x) v
  rw [(preservesDistribution_kerDistribution_iff_mlieDerivForm hα.apply_ne_zero).1 hX x v
    hv] at h
  linarith

/-- **A contact vector field of a contact form is the contact Hamiltonian vector field of its
Hamiltonian**: a differentiable vector field `X` preserves `ker α` exactly when
`X = X_(α(X))`. -/
theorem preservesDistribution_kerDistribution_iff_eq (hXd : MDiff (T% X)) :
    PreservesDistribution I α.kerDistribution X ↔
      X = α.contactHamiltonianVectorField fun y ↦ α.val y ![X y] :=
  (hα.preservesDistribution_kerDistribution_iff hXd).trans hα.isContactHamiltonianVectorField_iff_eq

/-- **The Jacobi bracket is the Lie bracket of contact vector fields.** For differentiable vector
fields `X` and `Y` preserving the contact structure `ker α`, the bracket `[X, Y]` has Hamiltonian
the Jacobi bracket of their Hamiltonians: `α([X, Y]) = {α(X), α(Y)}_α`. -/
theorem apply_mlieBracket_eq_jacobiBracket (hX : PreservesDistribution I α.kerDistribution X)
    (hY : PreservesDistribution I α.kerDistribution Y) (hXd : MDiff (T% X)) (hYd : MDiff (T% Y))
    (x : M) : α.val x ![mlieBracket I X Y x] =
      α.jacobiBracket (fun y ↦ α.val y ![X y]) (fun y ↦ α.val y ![Y y]) x := by
  have hXH := (hα.preservesDistribution_kerDistribution_iff hXd).1 hX
  have hYH := (hα.preservesDistribution_kerDistribution_iff hYd).1 hY
  rw [hXH.apply_mlieBracket hYH (hXd x) (hYd x), jacobiBracket_def,
    ← hα.isContactHamiltonianVectorField_iff_eq.1 hXH,
    ← hα.isContactHamiltonianVectorField_iff_eq.1 hYH]

end IsContactForm

end SmoothForm

end TauCeti
