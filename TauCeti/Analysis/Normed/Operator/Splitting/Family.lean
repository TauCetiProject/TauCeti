/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Splitting.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Coordinates for families of split kernels

If `A x` paired with a fixed coordinate `q` is invertible, then `q` identifies
`ker (A x)` with a fixed space `G`. These identifications are continuous on the
actual kernel locus in `X × E`, not just fibrewise. The inverse parametrization
is `ContinuousLinearMap.kerSection`; it has the regularity of the operator family.

This gives local product charts for kernels of surjective operator families.
For stabilized Fredholm operators the model `G` is finite dimensional, so these
charts are the local input for the determinant bundle construction.

The construction uses Mathlib's smooth inversion of bounded operators and the
fixed-operator kernel section from `Splitting.Basic`.
-/

public section

open Set Topology
open scoped ContDiff

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The kernel section depends smoothly on the operator and the complementary coordinate
where their pair is invertible. -/
@[fun_prop]
theorem contDiffAt_kerSection {A : E →L[𝕜] F} {q : E →L[𝕜] G} {n : ℕ∞ω}
    (h : (A.prod q).IsInvertible) :
    ContDiffAt 𝕜 n (fun p : (E →L[𝕜] F) × (E →L[𝕜] G) ↦ p.1.kerSection p.2) (A, q) := by
  have hp : ContDiff 𝕜 n (fun p : (E →L[𝕜] F) × (E →L[𝕜] G) ↦ p.1.prod p.2) := by
    exact (prodL (𝕜 := 𝕜) (E := E) (F := F) (G := G) 𝕜).contDiff
  simp_rw [kerSection_def]
  exact (h.contDiffAt_map_inverse.comp (A, q) hp.contDiffAt).clm_comp
    (contDiffAt_const (c := inr 𝕜 F G))

variable {X : Type*} [TopologicalSpace X] {A : X → E →L[𝕜] F} {q : E →L[𝕜] G}

/-- Kernel sections are continuous on any continuous family of invertible pairs. -/
theorem continuous_kerSection (hA : Continuous A) (h : ∀ x, ((A x).prod q).IsInvertible) :
    Continuous (fun x ↦ (A x).kerSection q) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  exact (contDiffAt_kerSection (n := 0) (h x)).continuousAt.comp
    (f := fun x ↦ (A x, q)) (hA.continuousAt.prodMk continuousAt_const)

/-- Product coordinates on the actual kernel locus, with its subspace topology.
The base coordinate is unchanged, and the fibre coordinate is the fixed map `q`. -/
noncomputable def kernelHomeomorph (A : X → E →L[𝕜] F) (q : E →L[𝕜] G)
    (hA : Continuous A) (h : ∀ x, ((A x).prod q).IsInvertible) :
    {p : X × E | A p.1 p.2 = 0} ≃ₜ X × G where
  toFun p := (p.val.1, q p.val.2)
  invFun p := ⟨(p.1, (A p.1).kerSection q p.2), apply_kerSection (h p.1) p.2⟩
  left_inv p := Subtype.ext (Prod.ext rfl (kerSection_apply_of_mem_ker (h p.val.1) p.property))
  right_inv p := Prod.ext rfl (apply_kerSection_right (h p.1) p.2)
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk
      (((continuous_kerSection hA h).comp continuous_fst).clm_apply continuous_snd)

@[simp]
theorem kernelHomeomorph_apply (hA : Continuous A) (h : ∀ x, ((A x).prod q).IsInvertible)
    (p : {p : X × E | A p.1 p.2 = 0}) :
    kernelHomeomorph A q hA h p = (p.val.1, q p.val.2) :=
  (rfl)

@[simp]
theorem coe_kernelHomeomorph_symm_apply (hA : Continuous A)
    (h : ∀ x, ((A x).prod q).IsInvertible) (p : X × G) :
    ((kernelHomeomorph A q hA h).symm p).val = (p.1, (A p.1).kerSection q p.2) :=
  (rfl)

/-- On an overlap, changing the complementary coordinate acts by the bounded linear map
`q' ∘ kerSection (A x) q` on the fibre, with no change of base point. -/
theorem kernelHomeomorph_change_apply {G' : Type*}
    [NormedAddCommGroup G'] [NormedSpace 𝕜 G'] {q' : E →L[𝕜] G'}
    (hA : Continuous A) (h : ∀ x, ((A x).prod q).IsInvertible)
    (h' : ∀ x, ((A x).prod q').IsInvertible) (p : X × G) :
    kernelHomeomorph A q' hA h' ((kernelHomeomorph A q hA h).symm p) =
      (p.1, (q' ∘L (A p.1).kerSection q) p.2) :=
  (rfl)

/-- An invertible pair remains invertible on an open neighbourhood for a family continuous
at the base point. The same complementary coordinate gives kernel coordinates throughout
that neighbourhood. -/
theorem exists_isOpen_isInvertible_prod {x₀ : X} (hA : ContinuousAt A x₀)
    (h : ((A x₀).prod q).IsInvertible) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∀ x ∈ U, ((A x).prod q).IsInvertible := by
  have hp : ContinuousAt (fun x ↦ (A x).prod q) x₀ :=
    (prodL (𝕜 := 𝕜) (E := E) (F := F) (G := G) 𝕜).continuousAt.comp
      (hA.prodMk continuousAt_const)
  obtain ⟨U, hUsub, hU, hx₀⟩ := mem_nhds_iff.mp (hp.eventually h.eventually_nhds)
  exact ⟨U, hU, hx₀, fun _ hx ↦ hUsub hx⟩

end ContinuousLinearMap
