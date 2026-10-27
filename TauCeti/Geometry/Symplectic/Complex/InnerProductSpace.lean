/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic

/-!
# The complex inner product of an orthogonal complex structure

An orthogonal almost complex structure `J` on a real inner product space gives a complex
inner product `⟨v,w⟩ = ⟪v,w⟫_ℝ + i ⟪J v,w⟫_ℝ` on `J.complexModule`.
The construction preserves the original norm and real scalar action. It is a named choice of
structure rather than a global instance, since it depends on `J`.

This is the usual Hermitian metric associated with an orthogonal complex structure; see
H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The complex inner product induced by an orthogonal complex structure, using the original
norm on `V` and the scalar action `J.complexModule`. Its real part is the original inner product.
-/
@[implicit_reducible]
noncomputable def complexInnerProductSpace (J : AlmostComplexStructure V)
    (hJ : ∀ v, ‖J v‖ = ‖v‖) : InnerProductSpace ℂ V := by
  letI := J.complexModule
  let c : InnerProductSpace.Core ℂ V := by
    have hinner (v w : V) : ⟪J v, J w⟫ = ⟪v, w⟫ :=
      ({ J.toLinearMap with norm_map' := hJ } : V →ₗᵢ[ℝ] V).inner_map_map v w
    have hswap (v w : V) : ⟪J v, w⟫ = -⟪v, J w⟫ :=
      J.bilinForm_apply_left_eq_neg_apply_right (g := innerₗ V) hinner v w
    refine
      { inner := fun v w ↦ ⟨⟪v, w⟫, ⟪J v, w⟫⟩
        conj_inner_symm := ?_
        re_inner_nonneg := fun v ↦ real_inner_self_nonneg
        add_left := ?_
        smul_left := ?_
        definite := ?_ }
    · intro v w
      apply Complex.ext
      · exact real_inner_comm _ _
      · simp only [Complex.conj_im]
        rw [hswap, neg_neg, real_inner_comm]
    · intro v w x
      apply Complex.ext <;> simp [inner_add_left, map_add]
    · intro v w z
      rw [J.complexModule_smul_def]
      apply Complex.ext <;>
        simp [inner_add_left, inner_smul_left, map_add, map_smul, hswap]; ring
    · intro v hv
      exact inner_self_eq_zero.mp (congrArg Complex.re hv)
  have hnorm (v : V) : Real.sqrt ⟪v, v⟫ = ‖v‖ :=
    (norm_eq_sqrt_real_inner v).symm
  -- Use the core norm only to establish scalar compatibility; the resulting structure below
  -- keeps the original normed additive group, hence also its topology and real scalar action.
  have hsmul (z : ℂ) (v : V) :
      Real.sqrt ⟪z • v, z • v⟫ = ‖z‖ * Real.sqrt ⟪v, v⟫ := by
    let := c.toNormedAddCommGroup
    let : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
    exact norm_smul z v
  letI : NormedSpace ℂ V :=
    { norm_smul_le := fun z v ↦ by simpa only [hnorm] using (hsmul z v).le }
  exact
    { inner := c.inner
      conj_inner_symm := c.conj_inner_symm
      add_left := c.add_left
      smul_left := c.smul_left
      norm_sq_eq_re_inner := fun v ↦ norm_sq_eq_re_inner (𝕜 := ℝ) v }

/-- The induced complex inner product uses exactly the complex scalar action determined by `J`.
This equation identifies the inherited module even when the construction is opaque downstream.
-/
lemma complexInnerProductSpace_toModule (J : AlmostComplexStructure V)
    (hJ : ∀ v, ‖J v‖ = ‖v‖) :
    (J.complexInnerProductSpace hJ).toNormedSpace.toModule = J.complexModule := by
  rfl

/-- The Hermitian structure extends the caller's original real scalar action. -/
lemma complexInnerProductSpace_isScalarTower (J : AlmostComplexStructure V)
    (hJ : ∀ v, ‖J v‖ = ‖v‖) :
    letI := J.complexInnerProductSpace hJ
    IsScalarTower ℝ ℂ V := by
  let := J.complexInnerProductSpace hJ
  exact J.complexModule_isScalarTower

/-- The scalar action inherited from the Hermitian structure is the action defined by `J`. -/
lemma complexInnerProductSpace_smul_def (J : AlmostComplexStructure V)
    (hJ : ∀ v, ‖J v‖ = ‖v‖) (z : ℂ) (v : V) :
    letI := J.complexInnerProductSpace hJ
    z • v = z.re • v + z.im • J v := by
  let := J.complexInnerProductSpace hJ
  exact J.complexModule_smul_def z v

/-- The Hermitian metric has real part the original metric and imaginary part `⟪J v,w⟫_ℝ`.
-/
lemma complexInnerProductSpace_inner (J : AlmostComplexStructure V)
    (hJ : ∀ v, ‖J v‖ = ‖v‖) (v w : V) :
    letI := J.complexInnerProductSpace hJ
    inner ℂ v w = (inner ℝ v w : ℂ) + Complex.I * (inner ℝ (J v) w : ℂ) := by
  let := J.complexInnerProductSpace hJ
  apply Complex.ext <;> simp <;> rfl

end TauCeti.AlmostComplexStructure
