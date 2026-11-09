/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Trivializations over the whole base

A trivialization `e` of a fibre bundle `E` whose base set is the whole base is a homeomorphism
`E ≃ₜ B × F`. Read through `Bundle.Trivial.homeomorphProd`, it is a homeomorphism of total spaces
`E ≃ₜ TotalSpace F (Bundle.Trivial B F)` onto the trivial bundle
(`Bundle.Trivialization.homeomorphTrivial`). It covers the identity of the base, sends `v` to the
fibre coordinate of `e v`, and its inverse is the partial inverse of `e`
(`Bundle.Trivialization.homeomorphTrivial_apply`,
`Bundle.Trivialization.homeomorphTrivial_symm_apply`). For a linear trivialization of a
vector bundle over a nontrivially normed field `𝕜`, on the fibre over `b` it is the continuous
linear equivalence `e.continuousLinearEquivAt 𝕜 b`, with inverse its symmetric
(`Bundle.Trivialization.homeomorphTrivial_apply_eq_continuousLinearEquivAt`,
`Bundle.Trivialization.homeomorphTrivial_symm_apply_eq_continuousLinearEquivAt`).

More generally, any linear trivialization sends a vector over its base set to a nonzero vector
exactly when the vector is nonzero (`Bundle.Trivialization.snd_apply_ne_zero_iff`). For two linear
trivializations whose base sets contain `b`, the fibre equivalence `E_b ≃ F` of the second is that
of the first followed by the coordinate change from the first to the second
(`Bundle.Trivialization.continuousLinearEquivAt_trans_coordChangeL`).

exactly when the vector is nonzero (`Bundle.Trivialization.snd_apply_ne_zero_iff`). We also record
the product trivialization's fibrewise inverse (`Bundle.Trivialization.prod_symm_apply'`), the
preferred trivialization of a direct-sum fibre bundle (`FiberBundle.trivializationAt_prod`), and
scalar restriction of linear trivializations and coordinate changes
(`Bundle.Trivialization.isLinear_restrictScalars`,
`Bundle.Trivialization.restrictScalars_coordChangeL`).
-/

public section

noncomputable section

open Bundle

namespace Bundle.Trivialization

variable {B : Type*} [TopologicalSpace B] {F : Type*} [TopologicalSpace F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] (e : Trivialization F (π F E))

/-- The homeomorphism `E ≃ₜ B × F` of a trivialization over the whole base, read as a
homeomorphism onto the total space of the trivial bundle. -/
def homeomorphTrivial (he : e.baseSet = Set.univ) :
    TotalSpace F E ≃ₜ TotalSpace F (Bundle.Trivial B F) :=
  (e.toHomeomorphOfSourceEqUnivTargetEqUniv (by simp [e.source_eq, he])
    (by simp [e.target_eq, he])).trans (Bundle.Trivial.homeomorphProd B F).symm

@[simp]
theorem homeomorphTrivial_apply (he : e.baseSet = Set.univ) (v : TotalSpace F E) :
    e.homeomorphTrivial he v = TotalSpace.mk' F v.proj (e v).2 := by
  rw [homeomorphTrivial, Homeomorph.trans_apply, Homeomorph.symm_apply_eq]
  exact Prod.ext (e.coe_fst' (he ▸ Set.mem_univ v.proj)) rfl

@[simp]
theorem homeomorphTrivial_symm_apply (he : e.baseSet = Set.univ)
    (w : TotalSpace F (Bundle.Trivial B F)) :
    (e.homeomorphTrivial he).symm w = e.toPartialHomeomorph.symm (w.proj, w.2) := by
  rfl

section Linear

variable (R : Type*) [Semiring R] {F : Type*} [TopologicalSpace F] [AddCommMonoid F] [Module R F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module R (E b)] (e : Trivialization F (π F E)) [e.IsLinear R]

include R in
/-- A linear trivialization sends a vector over its base set to a nonzero vector exactly when the
vector is nonzero. -/
theorem snd_apply_ne_zero_iff {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    (e v).2 ≠ 0 ↔ v.2 ≠ 0 := by
  simpa only [linearEquivAt_apply] using (e.linearEquivAt R v.proj hv).map_ne_zero_iff

end Linear

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] (e : Trivialization F (π F E)) [e.IsLinear 𝕜]

theorem homeomorphTrivial_apply_eq_continuousLinearEquivAt (he : e.baseSet = Set.univ)
    (v : TotalSpace F E) :
    e.homeomorphTrivial he v = TotalSpace.mk' F v.proj (e.continuousLinearEquivAt 𝕜 v.proj
      (he ▸ Set.mem_univ _) v.2) :=
  congrArg (Bundle.Trivial.homeomorphProd B F).symm
    (e.apply_eq_prod_continuousLinearEquivAt 𝕜 v.proj (he ▸ Set.mem_univ _) v.2)

theorem homeomorphTrivial_symm_apply_eq_continuousLinearEquivAt (he : e.baseSet = Set.univ)
    (w : TotalSpace F (Bundle.Trivial B F)) :
    (e.homeomorphTrivial he).symm w = TotalSpace.mk' F w.proj
      ((e.continuousLinearEquivAt 𝕜 w.proj (he ▸ Set.mem_univ _)).symm w.2) := by
  rw [Homeomorph.symm_apply_eq, homeomorphTrivial_apply_eq_continuousLinearEquivAt 𝕜]
  exact congrArg (TotalSpace.mk' F w.proj) (ContinuousLinearEquiv.apply_symm_apply _ _).symm

variable (e' : Trivialization F (π F E)) [e'.IsLinear 𝕜] {b : B}

/-- **The fibre equivalences of two trivializations differ by the coordinate change**: for linear
trivializations `e` and `e'` whose base sets contain `b`, the equivalence `E_b ≃ F` given by `e`,
followed by the coordinate change from `e` to `e'`, is the one given by `e'`. -/
theorem continuousLinearEquivAt_trans_coordChangeL (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) :
    (e.continuousLinearEquivAt 𝕜 b hb).trans (e.coordChangeL 𝕜 e' b) =
      e'.continuousLinearEquivAt 𝕜 b hb' := by
  rw [← comp_continuousLinearEquivAt_eq_coord_change e e' ⟨hb, hb'⟩]
  ext x
  simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply]

end Bundle.Trivialization

namespace Bundle.Trivialization

variable {B : Type*} [TopologicalSpace B]

/-- Over `e₁.baseSet ∩ e₂.baseSet`, the fibrewise inverse `(e₁.prod e₂).symm` acts componentwise. -/
theorem prod_symm_apply' {F₁ F₂ : Type*} {E₁ E₂ : B → Type*} [TopologicalSpace F₁]
    [TopologicalSpace F₂] [TopologicalSpace (TotalSpace F₁ E₁)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, Zero (E₁ x)] [∀ x, Zero (E₂ x)]
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂)) {x : B}
    (hx : x ∈ e₁.baseSet ∩ e₂.baseSet) (w : F₁ × F₂) :
    (e₁.prod e₂).symm x w = (e₁.symm x w.1, e₂.symm x w.2) :=
  (TotalSpace.mk_inj (F := F₁ × F₂) (E := E₁ ×ᵇ E₂)).mp <|
    ((e₁.prod e₂).mk_symm hx w).trans (e₁.prod_symm_apply e₂ x w.1 w.2)

/-- The preferred trivialization of `E₁ ×ᵇ E₂` at `b` is `(trivializationAt F₁ E₁ b).prod
(trivializationAt F₂ E₂ b)`. -/
theorem _root_.FiberBundle.trivializationAt_prod (F₁ : Type*) (E₁ : B → Type*) (F₂ : Type*)
    (E₂ : B → Type*) [TopologicalSpace F₁] [TopologicalSpace F₂]
    [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [∀ x, Zero (E₁ x)] [∀ x, Zero (E₂ x)] [∀ x, TopologicalSpace (E₁ x)]
    [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₁ E₁] [FiberBundle F₂ E₂] (b : B) :
    FiberBundle.trivializationAt (F₁ × F₂) (E₁ ×ᵇ E₂) b =
      (FiberBundle.trivializationAt F₁ E₁ b).prod (FiberBundle.trivializationAt F₂ E₂ b) :=
  -- `FiberBundle.prod` defines `trivializationAt'` directly as `(trivializationAt F₁ E₁ b).prod …`.
  (rfl)

/-- A `𝕜`-linear trivialization is also `𝕜'`-linear for any compatible scalar action `𝕜'`. -/
theorem isLinear_restrictScalars (𝕜' 𝕜 : Type*) [Semiring 𝕜'] [Semiring 𝕜] [SMul 𝕜' 𝕜]
    {F : Type*} {E : B → Type*} [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)]
    [AddCommMonoid F] [Module 𝕜' F] [Module 𝕜 F] [IsScalarTower 𝕜' 𝕜 F]
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜' (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, IsScalarTower 𝕜' 𝕜 (E x)] (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    e.IsLinear 𝕜' where
  linear b hb :=
    { map_add := (e.linear 𝕜 hb).map_add
      map_smul r v := by rw [← smul_one_smul 𝕜 r v, (e.linear 𝕜 hb).map_smul, smul_one_smul] }

/-- Restricting scalars of a `𝕜`-linear coordinate change recovers the `𝕜'`-linear coordinate
change. -/
theorem restrictScalars_coordChangeL (𝕜' 𝕜 : Type*)
    [NontriviallyNormedField 𝕜'] [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜' 𝕜]
    {F : Type*} {E : B → Type*} [NormedAddCommGroup F] [NormedSpace 𝕜' F] [NormedSpace 𝕜 F]
    [IsScalarTower 𝕜' 𝕜 F] [TopologicalSpace (TotalSpace F E)]
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜' (E x)] [∀ x, Module 𝕜 (E x)]
    (e e' : Trivialization F (π F E)) [e.IsLinear 𝕜'] [e'.IsLinear 𝕜'] [e.IsLinear 𝕜]
    [e'.IsLinear 𝕜] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (e.coordChangeL 𝕜 e' b : F →L[𝕜] F).restrictScalars 𝕜' = e.coordChangeL 𝕜' e' b := by
  ext v; simp [Trivialization.coordChangeL_apply' e e' hb]

end Bundle.Trivialization
