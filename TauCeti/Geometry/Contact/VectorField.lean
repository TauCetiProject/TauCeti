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

**Local contact forms.** The same identities hold pointwise for a one-form `α` that defines `ξ`
only near a point `x`, as every contact structure has near each point, coorientable or not. Such
an `α` is a contact form at `x`
(`TauCeti.IsContactDistribution.isContactFormAt_of_eventually_kerDistribution_eq`). If a vector
field `X`, differentiable at `x`, preserves `ξ` at `x`, then `L_X α` vanishes on `ξ_x`
(`TauCeti.PreservesDistributionAt.mlieDerivForm_apply_eq_zero`), so `X` satisfies at `x` the
contact Hamiltonian equation `ι_X dα = (R_α f) α - df` of `f = α(X)`
(`TauCeti.PreservesDistributionAt.mextDeriv_apply_eq`) and `X x = X_f(x)`
(`TauCeti.PreservesDistributionAt.apply_eq_contactHamiltonianVectorField`). For two such vector
fields, `α([X, Y]) = {α(X), α(Y)}_α` at `x`
(`TauCeti.PreservesDistributionAt.apply_mlieBracket_eq_jacobiBracket`).

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
* `TauCeti.PreservesDistributionAt.apply_eq_contactHamiltonianVectorField`,
  `TauCeti.PreservesDistributionAt.apply_mlieBracket_eq_jacobiBracket`: at a point, for a one-form
  defining the contact structure near that point, a contact vector field equals the contact
  Hamiltonian vector field of its Hamiltonian, and its bracket with another is the Jacobi bracket
  of their Hamiltonians.

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

/-! ### Contact vector fields in a local contact form -/

section LocalForm

variable [IsManifold I ∞ M] {D : Π x : M, Submodule ℝ (TangentSpace I x)}
  {α : SmoothForm I M ℝ 1} {x : M}

open SmoothForm

namespace PreservesDistributionAt

omit [FiniteDimensional ℝ E] in
/-- **The Lie derivative of a local defining form vanishes on the distribution.** If the kernel
of `α` is the smooth distribution `D` near `x` and `X` preserves `D` at `x`, then `L_X α` vanishes
on `D x`. -/
theorem mlieDerivForm_apply_eq_zero {k : ℕ} (hD : IsContMDiffDistribution I ∞ k D)
    (hX : PreservesDistributionAt I D X x) (hαD : ∀ᶠ y in 𝓝 x, α.kerDistribution y = D y)
    {v : TangentSpace I x} (hv : v ∈ D x) : mlieDerivForm X α.val x ![v] = 0 := by
  obtain ⟨U, hU, hxU, W, hW, hWD, hWx⟩ := hD.exists_contMDiffOn_apply_eq (⟨v, hv⟩ : D x)
  have hWx' : W x = v := hWx
  have hWd : MDiffAt (T% W) x := (hW.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
  -- `W` is tangent to `ker α` near `x`, so `L_X α (W) = -α([X, W])`, and `[X, W]` lies in
  -- `D x = ker α_x`.
  have hWα : ∀ᶠ y in 𝓝 x, W y ∈ α.kerDistribution y := by
    filter_upwards [hαD, hU.mem_nhds hxU] with y hy hyU
    exact hy ▸ hWD y hyU
  have hbr : mlieBracket I X W x ∈ α.kerDistribution x := by
    rw [hαD.self_of_nhds]
    exact preservesDistributionAt_iff.1 hX hU hxU hW hWD
  rw [← hWx', mlieDerivForm_apply_eq_neg_apply_mlieBracket hWd hWα, mem_kerDistribution.1 hbr,
    neg_zero]

/-- **A contact vector field satisfies the contact Hamiltonian equation of a local contact form.**
If the kernel of `α` is the smooth contact structure `D` near `x` and a vector field `X`,
differentiable at `x`, preserves `D` at `x`, then `ι_X dα = (R_α f) α - df` at `x`, where
`f = α(X)`. -/
theorem mextDeriv_apply_eq (hD : IsContactDistribution I ∞ D)
    (hX : PreservesDistributionAt I D X x) (hXd : MDiffAt (T% X) x)
    (hαD : ∀ᶠ y in 𝓝 x, α.kerDistribution y = D y) (w : TangentSpace I x) :
    mextDeriv α.val x ![X x, w] =
      mvfderiv I (fun y ↦ α.val y ![X y]) x (α.reebVectorField x) * α.val x ![w] -
        mvfderiv I (fun y ↦ α.val y ![X y]) x w := by
  have hc := hD.isContactFormAt_of_eventually_kerDistribution_eq (by simp) hαD
  -- Test Cartan's formula `L_X α = ι_X dα + d(α(X))` on the component of `w` in `ker α_x`, where
  -- `L_X α` vanishes; the Reeb component lies in the kernel of `dα_x`.
  set v := w - α.val x ![w] • α.reebVectorField x
  have hv : v ∈ D x := by
    rw [← hαD.self_of_nhds]
    exact sub_smul_reebVectorField_mem_kerDistribution_of_isContactFormAt hc w
  have h := mlieDerivForm_apply_eq_mextDeriv_add (fun _ ↦ rfl) (α.mdifferentiableAt x) hXd v
  rw [hX.mlieDerivForm_apply_eq_zero hD.isContMDiffDistribution hαD hv] at h
  have hR := mextDeriv_reebVectorField_right_of_isContactFormAt hc (X x)
  rw [mextDeriv_eq_bilinFormAt] at hR
  simp only [v, mextDeriv_eq_bilinFormAt, map_sub, map_smul, hR, smul_eq_mul] at h ⊢
  linarith

/-- **A contact vector field is the contact Hamiltonian vector field of its Hamiltonian in a local
contact form.** If the kernel of `α` is the smooth contact structure `D` near `x` and a vector field
`X`, differentiable at `x`, preserves `D` at `x`, then `X x = X_f(x)` for `f = α(X)`. -/
theorem apply_eq_contactHamiltonianVectorField (hD : IsContactDistribution I ∞ D)
    (hX : PreservesDistributionAt I D X x) (hXd : MDiffAt (T% X) x)
    (hαD : ∀ᶠ y in 𝓝 x, α.kerDistribution y = D y) :
    X x = α.contactHamiltonianVectorField (fun y ↦ α.val y ![X y]) x := by
  have hc := hD.isContactFormAt_of_eventually_kerDistribution_eq (by simp) hαD
  refine (isInvertible_contactFlat_of_isContactFormAt hc).injective ?_
  rw [contactFlat_contactHamiltonianVectorField_of_isContactFormAt hc]
  exact (contactFlat_apply_eq_smul_sub_mvfderiv_iff_of_isContactFormAt hc _ _).2
    ⟨rfl, hX.mextDeriv_apply_eq hD hXd hαD⟩

/-- **The bracket of contact vector fields in a local contact form is the Jacobi bracket.** If the
kernel of `α` is the smooth contact structure `D` near `x` and the vector fields `X` and `Y`,
differentiable at `x`, preserve `D` at `x`, then `α([X, Y]) = {α(X), α(Y)}_α` at `x`. -/
theorem apply_mlieBracket_eq_jacobiBracket (hD : IsContactDistribution I ∞ D)
    (hX : PreservesDistributionAt I D X x) (hY : PreservesDistributionAt I D Y x)
    (hXd : MDiffAt (T% X) x) (hYd : MDiffAt (T% Y) x)
    (hαD : ∀ᶠ y in 𝓝 x, α.kerDistribution y = D y) :
    α.val x ![mlieBracket I X Y x] =
      α.jacobiBracket (fun y ↦ α.val y ![X y]) (fun y ↦ α.val y ![Y y]) x := by
  -- The invariant formula `dα(X, Y) = X(α(Y)) - Y(α(X)) - α([X, Y])`, with the derivatives of the
  -- Hamiltonians along `X` and `Y` given by the contact Hamiltonian equations at `x`.
  have h := SmoothForm.mextDeriv_apply_one (φ := α) hXd hYd
  have hXY := hX.mextDeriv_apply_eq hD hXd hαD (Y x)
  have hYX := hY.mextDeriv_apply_eq hD hYd hαD (X x)
  rw [jacobiBracket_def, ← hX.apply_eq_contactHamiltonianVectorField hD hXd hαD,
    ← hY.apply_eq_contactHamiltonianVectorField hD hYd hαD]
  rw [mextDeriv_apply_swap α.val x (Y x)] at hYX
  linarith

end PreservesDistributionAt

end LocalForm

/-! ### Kernels of one-forms -/

namespace SmoothForm

variable [IsManifold I ∞ M] {α : SmoothForm I M ℝ 1} {f : M → ℝ}

/-- **A vector field preserves `ker α` exactly when `L_X α` vanishes on `ker α`**, that is, when
`L_X α` is a multiple of `α`. The one-form `α` is required to vanish nowhere, so that `ker α` is a
smooth hyperplane field; it need not be a contact form. -/
theorem preservesDistribution_kerDistribution_iff_mlieDerivForm (hα : ∀ x, α.val x ≠ 0) :
    PreservesDistribution I α.kerDistribution X ↔
      ∀ x, ∀ v ∈ α.kerDistribution x, mlieDerivForm X α.val x ![v] = 0 := by
  constructor
  · intro hX x v hv
    let _ : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
    exact (hX.preservesDistributionAt x).mlieDerivForm_apply_eq_zero
      (isContMDiffDistribution_kerDistribution (n := ∞) hα) (.of_forall fun _ ↦ rfl) hv
  · refine fun h ↦ preservesDistribution_iff.2 fun U hU V hV hVD x hx ↦ ?_
    have hVd : MDiffAt (T% V) x := (hV.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have hx' := h x (V x) (hVD x hx)
    rw [mlieDerivForm_apply_eq_neg_apply_mlieBracket hVd (eventually_of_mem (hU.mem_nhds hx) hVD),
      neg_eq_zero] at hx'
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
  refine ⟨fun hX ↦ hα.isContactHamiltonianVectorField_iff_eq.2 (funext fun x ↦ ?_),
    fun hX ↦ hX.preservesDistribution hXd⟩
  let _ : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  exact (hX.preservesDistributionAt x).apply_eq_contactHamiltonianVectorField
    (hα.isContactDistribution_kerDistribution (n := ∞)) (hXd x) (.of_forall fun _ ↦ rfl)

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
  let _ : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  exact (hX.preservesDistributionAt x).apply_mlieBracket_eq_jacobiBracket
    (hα.isContactDistribution_kerDistribution (n := ∞)) (hY.preservesDistributionAt x) (hXd x)
    (hYd x) (.of_forall fun _ ↦ rfl)

end IsContactForm

end SmoothForm

end TauCeti
