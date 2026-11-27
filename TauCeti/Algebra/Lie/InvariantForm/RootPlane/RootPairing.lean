/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.InvariantForm.CartanInteger
public import TauCeti.LinearAlgebra.BilinearForm.Coroot
public import TauCeti.Algebra.Lie.InvariantForm.Reflection
public import TauCeti.Algebra.Lie.InvariantForm.RootPlane.Center
public import Mathlib.LinearAlgebra.RootSystem.Basic
import TauCeti.LinearAlgebra.Dual.Basic

/-!
# The root pairing of a compact Lie algebra

Let `B` be a symmetric positive definite invariant form on a finite-dimensional real Lie algebra
`L`, the Lie algebra of a compact Lie group for instance, and let
`L = t + E₁ + ⋯ + E_r` be a root-plane decomposition
(`TauCeti.IsRootPlaneDecomposition B t α E J`) with nonzero planes and nonzero roots `α_i ∈ t*`:
every `H ∈ t` acts on `E_i` by `ad H = α_i(H) J_i`. This is the real root decomposition of the Lie
algebra of a compact Lie group with respect to a maximal torus
(`TauCeti.Lie.IsMaximalTorus.exists_isRootPlaneDecomposition`). The **real roots** are the forms
`±α_i`, the set `range α ∪ -range α`. This file shows that they form a finite crystallographic root
pairing for the evaluation pairing of `t*` with `t`
(`TauCeti.IsRootPlaneDecomposition.rootPairing`), with the coroots of the invariant metric.

* **Coroots.** For the vector `a ∈ t` representing a real root `γ` through `B`, the coroot is
  `γ^∨ = 2 a / B(a, a)` (`LinearMap.BilinForm.coroot`), with `γ(γ^∨) = 2`. Coroots determine
  their roots, and the coroot of a reflected root is the reflected coroot
  (`LinearMap.BilinForm.coroot_sub_smul`), because the reflections are isometries of `B`.
* **Roots of nonzero root planes are real roots.** Let `E'` be a nonzero root plane of
  `t` with a nonzero root `γ`. If `γ` were neither `α_i` nor `-α_i`, then `γ(H)² ≠ α_i(H)²` for
  some `H`, so `E'` would be orthogonal to `E_i` (`TauCeti.IsRootPlane.le_orthogonal`); it is
  also orthogonal to `t`. As `t` and the planes span `L`, a nonzero `w ∈ E'` would have
  `B(w, w) = 0`. Hence `γ = ±α_i` for some `i`
  (`TauCeti.IsRootPlaneDecomposition.exists_eq_or_eq_neg_of_isRootPlane`).
* **The roots are closed under the reflections.** The reflection of a real root in another is the
  root of a nonzero root plane (`TauCeti.IsRootPlane.exists_isRootPlane_sub_smul`), so it is again
  a real root (`TauCeti.IsRootPlaneDecomposition.sub_smul_mem`).
* **Integrality.** The pairings `δ(γ^∨)` are the Cartan integers, integers by
  `TauCeti.IsRootPlane.exists_int_two_mul_apply_eq_mul`, so the root pairing is crystallographic
  (`TauCeti.IsRootPlaneDecomposition.isCrystallographic_rootPairing`).

The roots span the annihilator of the centre in `t*`
(`TauCeti.IsRootPlaneDecomposition.rootSpan_rootPairing`), not all of `t*` when `L` has a centre,
so this is a root pairing on `(t*, t)` and not a root system there. Reducedness, that `2γ` is never
a root, needs the one-dimensionality of the complex root spaces and is not proved here.

## Main definitions

* `TauCeti.IsRootPlaneDecomposition.rootPairing`: the root pairing of the real roots `±α_i` on
  `(t*, t)`.

## Main results

* `TauCeti.IsRootPlaneDecomposition.exists_eq_or_eq_neg_of_isRootPlane`: the root of a nonzero root
  plane with nonzero root is `±α_i` for some `i`.
* `TauCeti.IsRootPlaneDecomposition.sub_smul_mem`: the real roots are closed under the root
  reflections.
* `TauCeti.IsRootPlaneDecomposition.isCrystallographic_rootPairing`: the root pairing is
  crystallographic.
* `TauCeti.IsRootPlaneDecomposition.rootSpan_rootPairing`: the roots span the forms on `t`
  vanishing on its central elements.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, §2 (the roots of a compact Lie group form a root
  system).
-/

public section

open Module Set
open scoped Pointwise

/-! ### The real roots of a root-plane decomposition -/

namespace TauCeti.IsRootPlaneDecomposition

section Field

variable {K L ι : Type*} [Field K] [PartialOrder K] [LieRing L] [LieAlgebra K L]
  {B : LinearMap.BilinForm K L} {t : Submodule K L} {α : ι → Dual K t} {E : ι → Submodule K L}
  {J : ∀ i, Module.End K (E i)}

/-- **The root of every nonzero root plane is a real root `±α_i`.** Let `B` be an invariant form
with `B(w, w) ≠ 0` for `w ≠ 0`, and `L = t + E₁ + ⋯ + E_r` a root-plane decomposition. If `E'` is a
nonzero root plane of `t` with a nonzero root `γ`, then `γ` is one of the roots `±α_i`. -/
theorem exists_eq_or_eq_neg_of_isRootPlane (hD : IsRootPlaneDecomposition B t α E J)
    (hB : B.lieInvariant L) (hBa : B.toQuadraticMap.Anisotropic) {γ : Dual K t}
    {E' : Submodule K L} {J' : Module.End K E'} (hE' : IsRootPlane B t γ E' J') (hE'0 : E' ≠ ⊥)
    (hγ : γ ≠ 0) : ∃ i, γ = α i ∨ γ = -α i := by
  by_contra! h
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE'0
  -- `B(·, w)` vanishes on `t` and on every plane, hence everywhere.
  have hle : t ⊔ ⨆ i, E i ≤ LinearMap.ker (B.flip w) := by
    refine sup_le (fun H hH ↦ ?_) (iSup_le fun i v hv ↦ ?_)
    · exact hE'.apply_eq_zero_of_forall_lie_eq_zero hB hγ
        (fun H' ↦ hD.lie_eq_zero H'.property hH) ⟨w, hw⟩
    · obtain ⟨H, hH⟩ : ∃ H, α i H ^ 2 ≠ γ H ^ 2 := by
        by_contra! hsq
        rcases Module.Dual.eq_or_eq_neg_of_forall_sq_eq fun H ↦ (hsq H).symm with h' | h'
        · exact (h i).1 h'
        · exact (h i).2 h'
      exact (hD.isRootPlane i).le_orthogonal hE' hB hH hw v hv
  have hww : B w w = 0 := hle (hD.sup_eq_top ▸ Submodule.mem_top)
  exact hw0 (hBa w hww)

end Field

variable {L ι : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {B : LinearMap.BilinForm ℝ L} {t : Submodule ℝ L} {α : ι → Dual ℝ t} {E : ι → Submodule ℝ L}
  {J : ∀ i, Module.End ℝ (E i)}

omit [FiniteDimensional ℝ L] in
/-- Each real root `±α_i` is the root of a nonzero root plane: `E_i` with the rotation `±J_i`. -/
theorem exists_isRootPlane_of_mem (hD : IsRootPlaneDecomposition B t α E J)
    (hE : ∀ i, E i ≠ ⊥) {γ : Dual ℝ t} (hγ : γ ∈ range α ∪ -range α) :
    ∃ (E' : Submodule ℝ L) (J' : Module.End ℝ E'), IsRootPlane B t γ E' J' ∧ E' ≠ ⊥ := by
  rcases hγ with ⟨i, rfl⟩ | ⟨i, hi⟩
  · exact ⟨E i, J i, hD.isRootPlane i, hE i⟩
  · rw [← neg_neg γ, ← hi]
    exact ⟨E i, -J i, (hD.isRootPlane i).neg, hE i⟩

omit [FiniteDimensional ℝ L] in
/-- The real roots are nonzero when the roots `α_i` are. -/
private theorem ne_zero_of_mem (hα : ∀ i, α i ≠ 0) {γ : Dual ℝ t} (hγ : γ ∈ range α ∪ -range α) :
    γ ≠ 0 := by
  rcases hγ with ⟨i, rfl⟩ | ⟨i, hi⟩
  · exact hα i
  · rintro rfl
    exact hα i (by simpa using hi)

/-- **The real roots are closed under the root reflections.** For a symmetric positive definite
invariant form and a root-plane decomposition with nonzero planes and nonzero roots, the reflection
`s_γ(δ) = δ - δ(γ^∨) γ` of a real root `δ` in a real root `γ` is again a real root. -/
theorem sub_smul_mem (hD : IsRootPlaneDecomposition B t α E J) (hBs : B.IsSymm)
    (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant L) (hE : ∀ i, E i ≠ ⊥)
    (hα : ∀ i, α i ≠ 0) [Finite ι] {γ δ : Dual ℝ t} (hγ : γ ∈ range α ∪ -range α)
    (hδ : δ ∈ range α ∪ -range α) :
    δ - δ (B.coroot hBp.anisotropic γ) • γ ∈ range α ∪ -range α := by
  obtain ⟨Eγ, Jγ, hEγ, hEγ0⟩ := hD.exists_isRootPlane_of_mem hE hγ
  obtain ⟨Eδ, Jδ, hEδ, hEδ0⟩ := hD.exists_isRootPlane_of_mem hE hδ
  obtain ⟨a, ha⟩ := LinearMap.BilinForm.exists_forall_apply_eq hBp.anisotropic γ
  obtain ⟨E', J', hE', hE'0⟩ := hEγ.exists_isRootPlane_sub_smul hEδ hBs hBp hB
    (fun z hz ↦ hD.mem_of_forall_lie_eq_zero hα hz) hEγ0 hEδ0 ha
  rw [LinearMap.BilinForm.apply_coroot_eq_of_forall_apply_eq hBp.anisotropic ha, ha]
  -- The reflection of the nonzero `δ` is nonzero.
  have hne : δ - (2 * δ a / γ a) • γ ≠ 0 := by
    intro h0
    have hγa : γ a ≠ 0 := by
      rw [← ha]
      exact LinearMap.BilinForm.apply_self_ne_zero_of_forall_apply_eq hBp.anisotropic
        (ne_zero_of_mem hα hγ) ha
    have hδ' : δ = (2 * δ a / γ a) • γ := sub_eq_zero.mp h0
    have h2 : δ a = 2 * δ a := by
      conv_lhs => rw [hδ']
      rw [LinearMap.smul_apply, smul_eq_mul]
      field_simp
    have hδa : δ a = 0 := by linarith
    exact ne_zero_of_mem hα hδ (by rw [hδ', hδa]; simp)
  obtain ⟨i, hi | hi⟩ := hD.exists_eq_or_eq_neg_of_isRootPlane hB hBp.anisotropic hE' hE'0 hne
  · exact Or.inl ⟨i, hi.symm⟩
  · exact Or.inr ⟨i, by simp [hi]⟩

/-! ### The root pairing -/

/-- The coroot map on the real roots, as an embedding. -/
noncomputable def corootEmbedding (hBp : B.toQuadraticMap.PosDef) (hα : ∀ i, α i ≠ 0) :
    ↥(range α ∪ -range α) ↪ t where
  toFun γ := B.coroot hBp.anisotropic γ
  inj' γ δ h := Subtype.ext <|
    LinearMap.BilinForm.coroot_injOn (ne_zero_of_mem hα γ.property)
      (ne_zero_of_mem hα δ.property) h

@[simp]
theorem corootEmbedding_apply (hBp : B.toQuadraticMap.PosDef) (hα : ∀ i, α i ≠ 0)
    (γ : ↥(range α ∪ -range α)) : corootEmbedding hBp hα γ = B.coroot hBp.anisotropic γ :=
  (rfl)

/-- **The root pairing of a compact Lie algebra.** For a symmetric positive definite invariant form
`B` on a finite-dimensional real Lie algebra and a root-plane decomposition
`L = t + E₁ + ⋯ + E_r` with nonzero planes and nonzero roots, the root pairing indexed by the real
roots `±α_i`, on `(t*, t)` with the evaluation pairing, with roots `γ` and coroots
`γ^∨ = 2 a / B(a, a)` for the vector `a ∈ t` representing `γ`. -/
noncomputable def rootPairing [Finite ι] (hD : IsRootPlaneDecomposition B t α E J)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant L) (hE : ∀ i, E i ≠ ⊥)
    (hα : ∀ i, α i ≠ 0) : RootPairing ↥(range α ∪ -range α) ℝ (Dual ℝ t) t :=
  have : Finite ↥(range α ∪ -range α) := ((finite_range α).union (finite_range α).neg).to_subtype
  RootPairing.mk' LinearMap.id (Function.Embedding.subtype _) (corootEmbedding hBp hα)
    (fun γ ↦ LinearMap.BilinForm.apply_coroot (hB := hBp.anisotropic)
      (ne_zero_of_mem hα γ.property))
    (by
      rintro γ - ⟨δ, rfl⟩
      exact ⟨⟨_, hD.sub_smul_mem hBs hBp hB hE hα γ.property δ.property⟩, by
        simp [preReflection_apply]⟩)
    (by
      rintro γ - ⟨δ, rfl⟩
      exact ⟨⟨_, hD.sub_smul_mem hBs hBp hB hE hα γ.property δ.property⟩, by
        simp [preReflection_apply, LinearMap.BilinForm.coroot_sub_smul hBs]⟩)

variable [Finite ι] (hD : IsRootPlaneDecomposition B t α E J) (hBs : B.IsSymm)
  (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant L) (hE : ∀ i, E i ≠ ⊥)
  (hα : ∀ i, α i ≠ 0)

@[simp]
theorem rootPairing_toLinearMap_apply (f : Dual ℝ t) (H : t) :
    (hD.rootPairing hBs hBp hB hE hα).toLinearMap f H = f H :=
  (rfl)

@[simp]
theorem rootPairing_root (γ : ↥(range α ∪ -range α)) :
    (hD.rootPairing hBs hBp hB hE hα).root γ = γ :=
  (rfl)

@[simp]
theorem rootPairing_coroot (γ : ↥(range α ∪ -range α)) :
    (hD.rootPairing hBs hBp hB hE hα).coroot γ = B.coroot hBp.anisotropic γ :=
  (rfl)

/-- The pairing of the root `δ` with the coroot of `γ` is `δ(γ^∨)`. -/
@[simp]
theorem rootPairing_pairing (δ γ : ↥(range α ∪ -range α)) :
    (hD.rootPairing hBs hBp hB hE hα).pairing δ γ = (δ : Dual ℝ t) (B.coroot hBp.anisotropic γ) :=
  (rfl)

/-- **The root pairing of a compact Lie algebra is crystallographic**: the pairings `δ(γ^∨)` are
the Cartan integers `2 B(a, b) / B(a, a)`, which are integers. -/
instance isCrystallographic_rootPairing :
    (hD.rootPairing hBs hBp hB hE hα).IsCrystallographic := by
  refine ⟨fun δ γ ↦ ?_⟩
  obtain ⟨Eγ, Jγ, hEγ, hEγ0⟩ := hD.exists_isRootPlane_of_mem hE γ.property
  obtain ⟨Eδ, Jδ, hEδ, hEδ0⟩ := hD.exists_isRootPlane_of_mem hE δ.property
  obtain ⟨a, ha⟩ := LinearMap.BilinForm.exists_forall_apply_eq hBp.anisotropic (γ : Dual ℝ t)
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_forall_apply_eq hBp.anisotropic (δ : Dual ℝ t)
  obtain ⟨n, hn⟩ := hEγ.exists_int_two_mul_apply_eq_mul hEδ hBs hBp hB
    (fun z hz ↦ hD.mem_of_forall_lie_eq_zero hα hz) hEγ0 hEδ0 ha hb
  have haa := LinearMap.BilinForm.apply_self_ne_zero_of_forall_apply_eq hBp.anisotropic
    (ne_zero_of_mem hα γ.property) ha
  refine ⟨n, ?_⟩
  rw [rootPairing_pairing,
    LinearMap.BilinForm.apply_coroot_eq_of_forall_apply_eq hBp.anisotropic ha, ← hb, hBs.eq b a,
    algebraMap_int_eq, eq_intCast]
  field_simp
  linarith

/-- **The roots span the annihilator of the centre.** The real roots span the forms on `t`
vanishing on the central elements of `t`. -/
theorem rootSpan_rootPairing :
    (hD.rootPairing hBs hBp hB hE hα).rootSpan ℝ =
      ((LieAlgebra.center ℝ L).toSubmodule.comap t.subtype).dualAnnihilator := by
  rw [← hD.span_range_eq_dualAnnihilator hE, RootPairing.rootSpan]
  have : range (hD.rootPairing hBs hBp hB hE hα).root = range α ∪ -range α := by
    ext γ
    simp only [rootPairing_root, mem_range, Subtype.exists, exists_prop, exists_eq_right]
  rw [this, Submodule.span_union, Submodule.span_neg, sup_idem]

end TauCeti.IsRootPlaneDecomposition
