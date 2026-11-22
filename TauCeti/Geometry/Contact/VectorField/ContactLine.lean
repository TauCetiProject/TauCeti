/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.VectorField
public import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Contact vector fields of sections of the contact line

Let `ξ` be a smooth contact structure on a Hausdorff manifold `M`, and let `L = TM ⧸ ξ` be its
contact line. No contact form, coorientation or orientation of `L` is chosen, so `ξ` need not be
the kernel of any global one-form. Represent a section of `L` by a smooth vector field `V`, the
section `x ↦ [V x]`. This file shows that **every smooth section of the contact line is the class
of a unique smooth contact vector field**
(`TauCeti.IsContactDistribution.exists_preservesDistribution_sub_mem`): there is exactly one smooth
vector field `X` preserving `ξ` (`TauCeti.PreservesDistribution`) with `X - V` tangent to `ξ`.
Together with the injectivity of `X ↦ [X]` on contact vector fields
(`TauCeti.PreservesDistribution.eq_of_forall_mkQ_eq`), this identifies the smooth contact vector
fields of `ξ` with the smooth sections of its contact line. The Lie bracket of contact vector
fields is therefore a bracket on sections of `L`, the line-valued Jacobi bracket of `ξ`.

**Construction.** Near a point `x₀`, `ξ` is the kernel of a one-form `α` that is a contact form
at every point of its domain (`TauCeti.IsContactDistribution.exists_isContactFormAt`). Multiplying
`α` by a smooth bump function which equals `1` near `x₀` gives a global smooth one-form `β`,
contact near `x₀` with kernel `ξ` there. The contact Hamiltonian vector field `X_f` of
`f = β(V)` (`TauCeti.SmoothForm.contactHamiltonianVectorField`) is smooth near `x₀`, satisfies
`β(X_f) = f = β(V)`, so `X_f - V` is tangent to `ξ` near `x₀`, and preserves `ξ` at every point
near `x₀`
(`TauCeti.SmoothForm.mlieBracket_contactHamiltonianVectorField_mem_kerDistribution`). Two such
local solutions agree where both are defined: their difference preserves `ξ` there and is tangent
to `ξ`, so it vanishes by nondegeneracy of the Levi form
(`TauCeti.PreservesDistributionAt.apply_eq_zero`). Hence the local solutions glue to a global
smooth contact vector field. Smoothness and preservation of `ξ` are local
(`TauCeti.preservesDistribution_iff_forall_preservesDistributionAt`).

The contact vector field of `V` is `TauCeti.contactVectorField I ξ V`. It depends only on the
section `[V]` (`TauCeti.contactVectorField_congr`), is additive and homogeneous in `V`, fixes
every smooth contact vector field, and the bracket of two of them is again one:
`X_([X_V, X_W]) = [X_V, X_W]` (`TauCeti.contactVectorField_mlieBracket`). For a global contact form
`α` with kernel `ξ`, it is the contact Hamiltonian vector field of `α(V)`
(`TauCeti.SmoothForm.IsContactForm.contactVectorField_kerDistribution`), so in the trivialization
of `L` by `α` the bracket of the sections `[V]`, `[W]` is the Jacobi bracket
`{α(V), α(W)}_α` (`TauCeti.SmoothForm.IsContactForm.apply_mlieBracket_contactVectorField`).

**Local contact forms.** When `ξ` is not coorientable there is no global contact form, but every
point has a one-form `α` whose kernel is `ξ` nearby
(`TauCeti.IsContactDistribution.exists_smoothForm_ker_eq_isContactFormAt`), which trivializes `L`
near that point by `[V] ↦ α(V)`. In each such local trivialization the bracket of sections is the
Jacobi bracket of `α`: `α([X_V, X_W]) = {α(V), α(W)}_α` near the point
(`TauCeti.IsContactDistribution.apply_mlieBracket_contactVectorField`). On the overlap with a
second local contact form `β`, where `β = u α` with `u = β(R_α)`, the two local brackets satisfy the
transition law `{β(V), β(W)}_β = u {α(V), α(W)}_α`
(`TauCeti.IsContactDistribution.jacobiBracket_eq_apply_reebVectorField_mul_jacobiBracket`); the
factor `u` may be negative. Conversely, a vector field `Z` represents the bracket section
`[[X_V, X_W]]` exactly when `α(Z) = {α(V), α(W)}_α` at every point, for every local contact form
`α` there (`TauCeti.IsContactDistribution.mlieBracket_contactVectorField_sub_mem_iff`): the bracket
of sections of the contact line is the unique bracket whose local representatives are the Jacobi
brackets of the local contact forms.

## Main definitions

* `TauCeti.contactVectorField I ξ V`: the smooth contact vector field in the class of `V` modulo
  `ξ`.

## Main results

* `TauCeti.IsContactDistribution.exists_preservesDistribution_sub_mem`: every smooth section of the
  contact line is the class of a smooth contact vector field.
* `TauCeti.eq_contactVectorField_iff`: `X_V` is the only differentiable vector field preserving
  `ξ` in the class of `V`.
* `TauCeti.contactVectorField_congr`: `X_V` only depends on the section `[V]` of `TM ⧸ ξ`.
* `TauCeti.contactVectorField_mlieBracket`: the bracket of contact vector fields of sections.
* `TauCeti.SmoothForm.IsContactForm.contactVectorField_kerDistribution`: for a contact form,
  `X_V = X_(α(V))`.
* `TauCeti.IsContactDistribution.apply_mlieBracket_contactVectorField`: the bracket of sections
  in a local contact form is its Jacobi bracket.
* `TauCeti.IsContactDistribution.jacobiBracket_eq_apply_reebVectorField_mul_jacobiBracket`: the
  transition law of the local brackets.
* `TauCeti.IsContactDistribution.mlieBracket_contactVectorField_sub_mem_iff`: the bracket of
  sections is characterized by its local Jacobi brackets.

## References

* P. Libermann, C.-M. Marle, *Symplectic Geometry and Analytical Mechanics*, D. Reidel, 1987,
  Chapter V, Sections 13–14 (infinitesimal automorphisms of a contact structure and the Lie
  algebra of sections of the contact line).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.3 (contact vector fields and contact Hamiltonians).
-/

public section

noncomputable section

open Bundle Filter Set VectorField
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {D : Π x : M, Submodule ℝ (TangentSpace I x)}
  {V W X : Π x : M, TangentSpace I x}

/-! ### Local contact vector fields -/

/-- **A local contact vector field in a given class.** Near every point `x₀` of a smooth contact
structure `D` on a Hausdorff manifold, a smooth vector field `V` is congruent modulo `D` to a vector
field which is smooth and preserves `D` at every point near `x₀`: a contact Hamiltonian vector field
of a cut-off local contact form. -/
private theorem exists_local [T2Space M] (hD : IsContactDistribution I ∞ D)
    (hV : CMDiff ∞ (T% V)) (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ X : Π x : M, TangentSpace I x, ∀ x ∈ U,
      CMDiffAt ∞ (T% X) x ∧ PreservesDistributionAt I D X x ∧ X x - V x ∈ D x := by
  let _ : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  -- A local defining form `α` of `D`, contact at every point of its domain `U₀`.
  obtain ⟨U₀, hU₀, hx₀, α, hα, hαD⟩ := hD.exists_isContactFormAt (by simp) x₀
  -- Cut `α` off by a bump function `b` supported in `U₀` and equal to `1` near `x₀`.
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.1
    (hU₀.mem_nhds hx₀)
  have hβ : IsSmoothForm I ∞ (fun y ↦ b y • α y) := by
    rw [isSmoothForm_def]
    exact b.contMDiff.contMDiffOn.smul_section_of_tsupport hU₀ hb hα
  let β : SmoothForm I M ℝ 1 := ⟨_, hβ.mem_smoothBundleForms⟩
  -- On the open set `U` where `b = 1` near each point, `β` agrees with `α` near each point.
  set U := U₀ ∩ {y | ∀ᶠ z in 𝓝 y, b z = 1}
  have hU : IsOpen U := hU₀.inter isOpen_setOfPred_eventually_nhds
  have hloc {y : M} (hy : y ∈ U) : ∀ᶠ z in 𝓝 y, β.val z = α z :=
    hy.2.mono fun z hz ↦ by
      -- `β.val` is `fun y ↦ b y • α y` by construction.
      change b z • α z = α z
      rw [hz, one_smul]
  have hcontact : ∀ y ∈ U, IsContactFormAt β.val y := fun y hy ↦
    (isContactFormAt_congr (hloc hy).self_of_nhds fun v _ w _ ↦ by
      rw [mextDeriv_congr_of_eventuallyEq (hloc hy)]).2 (hαD y hy.1).2
  have hker : ∀ y ∈ U, β.kerDistribution y = D y := fun y hy ↦ by
    rw [← (hαD y hy.1).1, SmoothForm.kerDistribution_eq_ker]
    ext v
    rw [RoughForm.mem_ker, RoughForm.mem_ker, (hloc hy).self_of_nhds]
  -- The contact Hamiltonian vector field of `β(V)` solves the problem on `U`.
  refine ⟨U, hU, ⟨hx₀, b.eventuallyEq_one⟩, β.contactHamiltonianVectorField fun y ↦ β.val y ![V y],
    fun x hx ↦ ?_⟩
  have hc : ∀ᶠ y in 𝓝 x, IsContactFormAt β.val y := eventually_of_mem (hU.mem_nhds hx) hcontact
  have hXs : CMDiffAt ∞ (T% (β.contactHamiltonianVectorField fun y ↦ β.val y ![V y])) x :=
    SmoothForm.contMDiffAt_contactHamiltonianVectorField le_rfl hc
      ((β.contMDiffAt_apply_vectorField (hV x)).of_le (by simp))
  refine ⟨hXs, preservesDistributionAt_iff.2 fun U' hU' hxU' W hW hWD ↦ ?_, ?_⟩
  · rw [← hker x hx]
    refine SmoothForm.mlieBracket_contactHamiltonianVectorField_mem_kerDistribution hc
      (hXs.mdifferentiableAt (by simp))
      ((hW.contMDiffAt (hU'.mem_nhds hxU')).mdifferentiableAt (by simp)) ?_
    filter_upwards [hU.mem_nhds hx, hU'.mem_nhds hxU'] with y hy hy'
    rw [hker y hy]
    exact hWD y hy'
  · rw [← hker x hx]
    exact SmoothForm.sub_mem_kerDistribution_iff.2
      (SmoothForm.apply_contactHamiltonianVectorField_of_isContactFormAt (hcontact x hx) _)

/-! ### Every section of the contact line comes from a contact vector field -/

/-- **Every smooth section of the contact line is the class of a smooth contact vector field.**
For a smooth contact structure `D` on a Hausdorff manifold and a smooth vector field `V`, there is
a smooth vector field `X` preserving `D` with `X - V` tangent to `D`. It is unique among
differentiable vector fields (`TauCeti.PreservesDistribution.eq_of_forall_mkQ_eq`). No contact
form or coorientation of `D` is needed. -/
theorem IsContactDistribution.exists_preservesDistribution_sub_mem [T2Space M]
    (hD : IsContactDistribution I ∞ D) (hV : CMDiff ∞ (T% V)) :
    ∃ X : Π x : M, TangentSpace I x, CMDiff ∞ (T% X) ∧ PreservesDistribution I D X ∧
      ∀ x, X x - V x ∈ D x := by
  choose U hU hxU Y hY using exists_local hD hV
  -- Two local solutions agree where both are defined: their difference preserves `D` there and
  -- is tangent to `D`, so it vanishes.
  have hagree (x₀ : M) : ∀ y ∈ U x₀, Y y y = Y x₀ y := fun y hy ↦ by
    have hyd := ((hY y y (hxU y)).1).mdifferentiableAt (by simp)
    have hx₀d := ((hY x₀ y hy).1).mdifferentiableAt (by simp)
    rw [← sub_eq_zero, ← Pi.sub_apply (Y y)]
    refine ((hY y y (hxU y)).2.1.sub (hY x₀ y hy).2.1 hyd hx₀d).apply_eq_zero hD
      (mdifferentiableAt_sub_section hyd hx₀d) ?_
    filter_upwards [(hU y).mem_nhds (hxU y), (hU x₀).mem_nhds hy] with z hz hz'
    simpa using sub_mem (hY y z hz).2.2 (hY x₀ z hz').2.2
  have heq (x₀ : M) : (fun y ↦ Y y y) =ᶠ[𝓝 x₀] Y x₀ :=
    eventually_of_mem ((hU x₀).mem_nhds (hxU x₀)) (hagree x₀)
  refine ⟨fun y ↦ Y y y, fun x₀ ↦ ?_,
    preservesDistribution_iff_forall_preservesDistributionAt.2 fun x₀ ↦
      (hY x₀ x₀ (hxU x₀)).2.1.congr_of_eventuallyEq (heq x₀).symm,
    fun x ↦ (hY x x (hxU x)).2.2⟩
  exact (hY x₀ x₀ (hxU x₀)).1.congr_of_eventuallyEq ((heq x₀).mono fun y hy ↦ by simp [hy])

/-! ### The contact vector field of a section of the contact line -/

omit [FiniteDimensional ℝ E] in
variable (I) in
/-- The **contact vector field** of a vector field `V` for a distribution `D`: the smooth vector
field which preserves `D` and is congruent to `V` modulo `D`. For a smooth contact structure on a
Hausdorff manifold and a smooth `V` it exists and is unique (`TauCeti.eq_contactVectorField_iff`),
and it only depends on the section `[V]` of the contact line `TM ⧸ D`
(`TauCeti.contactVectorField_congr`). It is defined as `0` when no such vector field exists. -/
def contactVectorField (D : Π x : M, Submodule ℝ (TangentSpace I x))
    (V : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  open Classical in
  if h : ∃ X : Π x : M, TangentSpace I x, CMDiff ∞ (T% X) ∧ PreservesDistribution I D X ∧
      ∀ x, X x - V x ∈ D x then h.choose else 0

omit [FiniteDimensional ℝ E] in
/-- When some smooth vector field preserving `D` is congruent to `V` modulo `D`, the contact
vector field of `V` is one. -/
private theorem contactVectorField_spec_of_exists
    (h : ∃ X : Π x : M, TangentSpace I x, CMDiff ∞ (T% X) ∧ PreservesDistribution I D X ∧
      ∀ x, X x - V x ∈ D x) :
    CMDiff ∞ (T% (contactVectorField I D V)) ∧
      PreservesDistribution I D (contactVectorField I D V) ∧
        ∀ x, contactVectorField I D V x - V x ∈ D x := by
  rw [contactVectorField, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

section ContactVectorField

variable [T2Space M] (hD : IsContactDistribution I ∞ D)
include hD

private theorem contactVectorField_spec (hV : CMDiff ∞ (T% V)) :
    CMDiff ∞ (T% (contactVectorField I D V)) ∧
      PreservesDistribution I D (contactVectorField I D V) ∧
        ∀ x, contactVectorField I D V x - V x ∈ D x :=
  contactVectorField_spec_of_exists (hD.exists_preservesDistribution_sub_mem hV)

/-- The contact vector field of a smooth vector field is smooth. -/
theorem contMDiff_contactVectorField (hV : CMDiff ∞ (T% V)) :
    CMDiff ∞ (T% (contactVectorField I D V)) :=
  (contactVectorField_spec hD hV).1

/-- The contact vector field of a smooth vector field preserves the contact structure. -/
theorem preservesDistribution_contactVectorField (hV : CMDiff ∞ (T% V)) :
    PreservesDistribution I D (contactVectorField I D V) :=
  (contactVectorField_spec hD hV).2.1

/-- The contact vector field of `V` is congruent to `V` modulo the contact structure. -/
theorem contactVectorField_sub_mem (hV : CMDiff ∞ (T% V)) (x : M) :
    contactVectorField I D V x - V x ∈ D x :=
  (contactVectorField_spec hD hV).2.2 x

/-- The contact vector field of `V` represents the same section of the contact line as `V`. -/
theorem mkQ_contactVectorField (hV : CMDiff ∞ (T% V)) (x : M) :
    (D x).mkQ (contactVectorField I D V x) = (D x).mkQ (V x) :=
  (Submodule.Quotient.eq _).2 (contactVectorField_sub_mem hD hV x)

/-- **Characterization of the contact vector field of a section.** A differentiable vector field
is the contact vector field of `V` exactly when it preserves the contact structure and is
congruent to `V` modulo it. -/
theorem eq_contactVectorField_iff (hV : CMDiff ∞ (T% V)) (hXd : MDiff (T% X)) :
    X = contactVectorField I D V ↔ PreservesDistribution I D X ∧ ∀ x, X x - V x ∈ D x := by
  refine ⟨fun h ↦ h ▸ ⟨preservesDistribution_contactVectorField hD hV,
    contactVectorField_sub_mem hD hV⟩, fun ⟨hX, hXV⟩ ↦ ?_⟩
  refine hX.eq_of_forall_mkQ_eq hD (preservesDistribution_contactVectorField hD hV) hXd
    ((contMDiff_contactVectorField hD hV).mdifferentiable (by simp)) fun x ↦ ?_
  rw [mkQ_contactVectorField hD hV]
  exact (Submodule.Quotient.eq _).2 (hXV x)

/-- **The contact vector field only depends on the section of the contact line.** -/
theorem contactVectorField_congr (hV : CMDiff ∞ (T% V)) (hW : CMDiff ∞ (T% W))
    (h : ∀ x, V x - W x ∈ D x) : contactVectorField I D V = contactVectorField I D W :=
  (eq_contactVectorField_iff hD hW ((contMDiff_contactVectorField hD hV).mdifferentiable
    (by simp))).2 ⟨preservesDistribution_contactVectorField hD hV, fun x ↦ by
      simpa using add_mem (contactVectorField_sub_mem hD hV x) (h x)⟩

/-- A smooth contact vector field is its own contact vector field. -/
theorem contactVectorField_eq_self (hX : CMDiff ∞ (T% X)) (hXD : PreservesDistribution I D X) :
    contactVectorField I D X = X :=
  ((eq_contactVectorField_iff hD hX (hX.mdifferentiable (by simp))).2
    ⟨hXD, fun x ↦ by simp⟩).symm

/-- The contact vector field of a sum of sections is the sum of their contact vector fields. -/
theorem contactVectorField_add (hV : CMDiff ∞ (T% V)) (hW : CMDiff ∞ (T% W)) :
    contactVectorField I D (V + W) = contactVectorField I D V + contactVectorField I D W := by
  have hVd := (contMDiff_contactVectorField hD hV).mdifferentiable (n := ∞) (by simp)
  have hWd := (contMDiff_contactVectorField hD hW).mdifferentiable (n := ∞) (by simp)
  refine ((eq_contactVectorField_iff hD (hV.add_section hW)
    (mdifferentiable_add_section hVd hWd)).2 ⟨(preservesDistribution_contactVectorField hD hV).add
      (preservesDistribution_contactVectorField hD hW) hVd hWd, fun x ↦ ?_⟩).symm
  have h := add_mem (contactVectorField_sub_mem hD hV x) (contactVectorField_sub_mem hD hW x)
  rwa [Pi.add_apply, Pi.add_apply, add_sub_add_comm]

/-- The contact vector field of a constant multiple of a section is the constant multiple of its
contact vector field. -/
theorem contactVectorField_const_smul (hV : CMDiff ∞ (T% V)) (c : ℝ) :
    contactVectorField I D (c • V) = c • contactVectorField I D V := by
  refine ((eq_contactVectorField_iff hD (hV.const_smul_section (a := c))
    (((contMDiff_contactVectorField hD hV).const_smul_section (a := c)).mdifferentiable
      (by simp))).2 ⟨(preservesDistribution_contactVectorField hD hV).const_smul c,
        fun x ↦ ?_⟩).symm
  simpa [smul_sub] using Submodule.smul_mem _ c (contactVectorField_sub_mem hD hV x)

/-- **The bracket of contact vector fields of sections.** The Lie bracket of the contact vector
fields of two sections of the contact line is its own contact vector field. So the contact vector
fields of sections are closed under the Lie bracket, and `[V], [W] ↦ [[X_V, X_W]]` is a bracket on
the sections of the contact line, the line-valued Jacobi bracket of the contact structure. -/
theorem contactVectorField_mlieBracket (hV : CMDiff ∞ (T% V)) (hW : CMDiff ∞ (T% W)) :
    contactVectorField I D (mlieBracket I (contactVectorField I D V) (contactVectorField I D W)) =
      mlieBracket I (contactVectorField I D V) (contactVectorField I D W) := by
  let _ : IsManifold I ((⊤ : ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  let _ : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have hVs := contMDiff_contactVectorField hD hV
  have hWs := contMDiff_contactVectorField hD hW
  exact contactVectorField_eq_self hD (fun x ↦ ContMDiffAt.mlieBracket_vectorField
    (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (hVs x) (hWs x) (by simp))
    ((preservesDistribution_contactVectorField hD hV).mlieBracket
      (preservesDistribution_contactVectorField hD hW) hVs hWs)

end ContactVectorField

/-! ### Contact forms -/

namespace SmoothForm.IsContactForm

variable {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm)
include hα

/-- **For a contact form, the contact vector field of a section is a contact Hamiltonian vector
field.** If the contact structure is the kernel of a contact form `α`, the contact vector field of
`V` is the contact Hamiltonian vector field of `α(V)`, the function representing the section `[V]`
of the contact line in the trivialization given by `α`. -/
theorem contactVectorField_kerDistribution (hV : CMDiff ∞ (T% V)) :
    contactVectorField I α.kerDistribution V =
      α.contactHamiltonianVectorField fun y ↦ α.val y ![V y] := by
  let _ : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have hXs := hα.contMDiff_contactHamiltonianVectorField le_rfl
    ((α.contMDiff_apply_vectorField hV).of_le (by simp))
  have hXd := hXs.mdifferentiable (by simp)
  have hXD := (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField
    fun y ↦ α.val y ![V y]).preservesDistribution hXd
  have hXV (x : M) : α.contactHamiltonianVectorField (fun y ↦ α.val y ![V y]) x - V x ∈
      α.kerDistribution x :=
    sub_mem_kerDistribution_iff.2 (hα.apply_contactHamiltonianVectorField _ x)
  -- The contact Hamiltonian vector field is a solution, and solutions are unique.
  obtain ⟨hs, hp, hsub⟩ := contactVectorField_spec_of_exists ⟨_, hXs, hXD, hXV⟩
  refine hp.eq_of_forall_mkQ_eq (hα.isContactDistribution_kerDistribution (n := ∞)) hXD
    (hs.mdifferentiable (by simp)) hXd fun x ↦ (Submodule.Quotient.eq _).2 ?_
  simpa using sub_mem (hsub x) (hXV x)

/-- **The bracket of sections of the contact line, in the trivialization of a contact form.** For
a contact form `α`, the bracket of the contact vector fields of `V` and `W` represents the section
whose `α`-component is the Jacobi bracket `{α(V), α(W)}_α`. -/
theorem apply_mlieBracket_contactVectorField (hV : CMDiff ∞ (T% V)) (hW : CMDiff ∞ (T% W))
    (x : M) :
    α.val x ![mlieBracket I (contactVectorField I α.kerDistribution V)
      (contactVectorField I α.kerDistribution W) x] =
        α.jacobiBracket (fun y ↦ α.val y ![V y]) (fun y ↦ α.val y ![W y]) x := by
  rw [hα.contactVectorField_kerDistribution hV, hα.contactVectorField_kerDistribution hW]
  exact hα.apply_mlieBracket_contactHamiltonianVectorField
    (hα.mdifferentiable_contactHamiltonianVectorField
      ((α.contMDiff_apply_vectorField hV).of_le (by simp)) x)
    (hα.mdifferentiable_contactHamiltonianVectorField
      ((α.contMDiff_apply_vectorField hW).of_le (by simp)) x)

end SmoothForm.IsContactForm

/-! ### Local contact forms -/

namespace IsContactDistribution

variable [T2Space M] (hD : IsContactDistribution I ∞ D) {α β : SmoothForm I M ℝ 1} {x : M}
include hD

open SmoothForm

/-- **The bracket of sections of the contact line in a local contact form.** If the kernel of `α`
is the smooth contact structure `D` near `x`, the bracket of the contact vector fields of the
sections `[V]` and `[W]` of the contact line is read in the trivialization `α` as the Jacobi bracket
`{α(V), α(W)}_α` at `x`. No global contact form or coorientation is needed. -/
theorem apply_mlieBracket_contactVectorField (hV : CMDiff ∞ (T% V)) (hW : CMDiff ∞ (T% W))
    (hαD : ∀ᶠ y in 𝓝 x, α.kerDistribution y = D y) :
    α.val x ![mlieBracket I (contactVectorField I D V) (contactVectorField I D W) x] =
      α.jacobiBracket (fun y ↦ α.val y ![V y]) (fun y ↦ α.val y ![W y]) x := by
  -- Near `x`, the Hamiltonian of a contact vector field `X_V` is `α(V)`, since `X_V - V` lies in
  -- `D = ker α` there.
  have hham {U : Π x : M, TangentSpace I x} (hU : CMDiff ∞ (T% U)) :
      (fun y ↦ α.val y ![contactVectorField I D U y]) =ᶠ[𝓝 x] fun y ↦ α.val y ![U y] := by
    filter_upwards [hαD] with y hy
    have h := mem_kerDistribution.1 (hy ▸ contactVectorField_sub_mem hD hU y)
    rwa [ContinuousAlternatingMap.map_vecCons_sub, sub_eq_zero] at h
  rw [((preservesDistribution_contactVectorField hD hV).preservesDistributionAt x)
    |>.apply_mlieBracket_eq_jacobiBracket hD
      ((preservesDistribution_contactVectorField hD hW).preservesDistributionAt x)
      ((contMDiff_contactVectorField hD hV).mdifferentiableAt (by simp))
      ((contMDiff_contactVectorField hD hW).mdifferentiableAt (by simp)) hαD]
  exact (hham hV).jacobiBracket_eq α (hham hW)

/-- **The transition law of the local brackets of the contact line.** If `α` and `β` are both
local contact forms of the smooth contact structure `D` near `x`, then `β_x = u α_x` with
`u = β(R_α)`, and the brackets of the sections `[V]` and `[W]` in the two trivializations satisfy
`{β(V), β(W)}_β = u {α(V), α(W)}_α` at `x`. The factor `u` may be negative. -/
theorem jacobiBracket_eq_apply_reebVectorField_mul_jacobiBracket (hV : CMDiff ∞ (T% V))
    (hW : CMDiff ∞ (T% W)) (hαD : ∀ᶠ y in 𝓝 x, α.kerDistribution y = D y)
    (hβD : ∀ᶠ y in 𝓝 x, β.kerDistribution y = D y) :
    β.jacobiBracket (fun y ↦ β.val y ![V y]) (fun y ↦ β.val y ![W y]) x =
      β.val x ![α.reebVectorField x] *
        α.jacobiBracket (fun y ↦ α.val y ![V y]) (fun y ↦ α.val y ![W y]) x := by
  rw [← hD.apply_mlieBracket_contactVectorField hV hW hαD,
    ← hD.apply_mlieBracket_contactVectorField hV hW hβD]
  exact DFunLike.congr_fun (apply_eq_smul_of_kerDistribution_le
    (hαD.self_of_nhds.trans hβD.self_of_nhds.symm).le (apply_reebVectorField_of_isContactFormAt
      (hD.isContactFormAt_of_eventually_kerDistribution_eq (by simp) hαD))) _

/-- **The bracket of sections of the contact line is determined by the local Jacobi brackets.** A
vector field `Z` represents the bracket `[[X_V, X_W]]` of the sections `[V]` and `[W]` of the
contact line exactly when, at every point `x` and for every local contact form `α` of `D` near `x`,
`α(Z) = {α(V), α(W)}_α` at `x`. -/
theorem mlieBracket_contactVectorField_sub_mem_iff (hV : CMDiff ∞ (T% V))
    (hW : CMDiff ∞ (T% W)) {Z : Π x : M, TangentSpace I x} :
    (∀ x, mlieBracket I (contactVectorField I D V) (contactVectorField I D W) x - Z x ∈ D x) ↔
      ∀ (α : SmoothForm I M ℝ 1) (x : M), (∀ᶠ y in 𝓝 x, α.kerDistribution y = D y) →
        α.val x ![Z x] = α.jacobiBracket (fun y ↦ α.val y ![V y]) (fun y ↦ α.val y ![W y]) x := by
  -- In a local contact form at `x`, membership in `D x` is the vanishing of `α_x`.
  have key {α : SmoothForm I M ℝ 1} {x : M} (hαD : ∀ᶠ y in 𝓝 x, α.kerDistribution y = D y) :
      mlieBracket I (contactVectorField I D V) (contactVectorField I D W) x - Z x ∈ D x ↔
        α.val x ![Z x] =
          α.jacobiBracket (fun y ↦ α.val y ![V y]) (fun y ↦ α.val y ![W y]) x := by
    rw [← hαD.self_of_nhds, mem_kerDistribution, ContinuousAlternatingMap.map_vecCons_sub,
      hD.apply_mlieBracket_contactVectorField hV hW hαD, sub_eq_zero, eq_comm]
  refine ⟨fun h α x hαD ↦ (key hαD).1 (h x), fun h x ↦ ?_⟩
  obtain ⟨U, hU, hxU, α, hα⟩ := hD.exists_smoothForm_ker_eq_isContactFormAt x
  have hαD : ∀ᶠ y in 𝓝 x, α.kerDistribution y = D y :=
    eventually_of_mem (hU.mem_nhds hxU) fun y hy ↦
      (SmoothForm.kerDistribution_eq_ker α y).trans (hα y hy).1
  exact (key hαD).2 (h α x hαD)

end IsContactDistribution

end TauCeti
