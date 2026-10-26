/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The wedge product on de Rham cohomology

By the Leibniz rule `d (φ ∧ ψ) = dφ ∧ ψ + (-1) ^ k • φ ∧ dψ`, the wedge of two closed smooth
real-valued forms is closed, and the wedge of an exact form with a closed form, in either order,
is exact. Hence the wedge descends to a bilinear map
`H^k_dR(M) → H^l_dR(M) → H^(k+l)_dR(M)` on de Rham cohomology, characterized by
`[φ] ∧ [ψ] = [φ ∧ ψ]` on classes of closed forms.

The wedge of a form with a compactly supported form is supported in the support of the second
factor. The same Leibniz argument then shows that the wedge of a closed form with a compactly
supported closed form is compactly supported and closed, and is the exterior derivative of a
compactly supported form as soon as either factor is exact (compactly supported exact, for the
second factor). Hence the wedge also descends to a bilinear map
`H^k_dR(M) → H^l_c(M) → H^(k+l)_c(M)` into compactly supported de Rham cohomology. Followed by
integration, this gives the Poincaré pairing.

The construction applies to manifolds of class `C²` with corners and does not require finite
dimensionality, separation, or completeness of the model space.

## Main declarations

* `TauCeti.SmoothForm.wedge_mem_closedForms`: the wedge of closed forms is closed.
* `TauCeti.SmoothForm.wedge_mem_exactForms_of_left_mem`,
  `TauCeti.SmoothForm.wedge_mem_exactForms_of_right_mem`: the wedge of an exact form with a
  closed form, in either order, is exact.
* `TauCeti.deRhamCohomology.wedge`: the wedge product on de Rham cohomology.
* `TauCeti.deRhamCohomology.wedge_mk`: its value on classes of closed forms.
* `TauCeti.SmoothForm.wedge_mem_compactlySupportedClosedForms`,
  `TauCeti.SmoothForm.wedge_mem_exactCompactlySupportedForms_of_left_mem`,
  `TauCeti.SmoothForm.wedge_mem_exactCompactlySupportedForms_of_right_mem`: the compactly
  supported analogues.
* `TauCeti.compactlySupportedDeRhamCohomology.wedge`: the wedge of a de Rham class with a
  compactly supported class, with its value on classes
  `TauCeti.compactlySupportedDeRhamCohomology.wedge_mk`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] {k l : ℕ}

namespace SmoothForm

/-- A smooth form which, up to the identification of degrees `n = m + 1`, is the exterior
derivative of a smooth `m`-form `β` has every degree-indexed property that `dβ` has. -/
private theorem of_apply_eq_mextDeriv {n m : ℕ} (h : n = m + 1) {φ : SmoothForm I M ℝ n}
    (β : SmoothForm I M ℝ m)
    (hφ : ∀ x (v : Fin (m + 1) → TangentSpace I x), φ.1 x (v ∘ Fin.cast h) = mextDeriv β.1 x v)
    (P : (n : ℕ) → SmoothForm I M ℝ n → Prop) (hβ : P (m + 1) (mextDerivₗ I m β)) : P n φ := by
  subst h
  suffices hφβ : φ = mextDerivₗ I m β from hφβ ▸ hβ
  refine Subtype.ext (funext fun x ↦ ?_)
  ext v
  simpa [Fin.cast_eq_self] using hφ x v

/-- A smooth form is exact when, up to the identification of degrees `n = m + 1`, it is the
exterior derivative of a smooth `m`-form. -/
private theorem mem_exactForms_of_apply_eq {n m : ℕ} (h : n = m + 1) {φ : SmoothForm I M ℝ n}
    (β : SmoothForm I M ℝ m)
    (hφ : ∀ x (v : Fin (m + 1) → TangentSpace I x), φ.1 x (v ∘ Fin.cast h) = mextDeriv β.1 x v) :
    φ ∈ exactForms I M n :=
  of_apply_eq_mextDeriv h β hφ (fun n φ ↦ φ ∈ exactForms I M n)
    (by rw [exactForms_succ]; exact LinearMap.mem_range_self _ β)

/-- A smooth form is the exterior derivative of a compactly supported form when, up to the
identification of degrees `n = m + 1`, it is the exterior derivative of a compactly supported
smooth `m`-form. -/
private theorem mem_exactCompactlySupportedForms_of_apply_eq {n m : ℕ} (h : n = m + 1)
    {φ : SmoothForm I M ℝ n} {β : SmoothForm I M ℝ m} (hβc : β ∈ compactlySupportedForms I M m)
    (hφ : ∀ x (v : Fin (m + 1) → TangentSpace I x), φ.1 x (v ∘ Fin.cast h) = mextDeriv β.1 x v) :
    φ ∈ exactCompactlySupportedForms I M n :=
  of_apply_eq_mextDeriv h β hφ (fun n φ ↦ φ ∈ exactCompactlySupportedForms I M n)
    (by rw [exactCompactlySupportedForms_succ]; exact Submodule.mem_map_of_mem hβc)

/-- The Leibniz rule with a closed left factor: `d (φ ∧ β) = (-1) ^ k • φ ∧ dβ`.

The right-hand side is a `(k + (l + 1))`-form while the left-hand side is a `(k + l + 1)`-form,
so its argument is reindexed along the associativity equality `k + (l + 1) = k + l + 1`, as in
`mextDeriv_wedge`. -/
private theorem mextDeriv_wedge_of_left_closed {φ : SmoothForm I M ℝ k}
    (hφ : mextDeriv φ.1 = 0) (β : SmoothForm I M ℝ l) (x : M)
    (v : Fin (k + l + 1) → TangentSpace I x) :
    mextDeriv (φ.1.wedge β.1) x v =
      (-1 : ℝ) ^ k • φ.1.wedge (mextDeriv β.1) x
        (v ∘ Fin.cast (Nat.add_assoc k l 1).symm) := by
  have h := mextDeriv_wedge_apply φ β x v
  rw [hφ] at h
  simpa using h

/-- The wedge of two closed smooth forms is closed. -/
theorem wedge_mem_closedForms {φ : SmoothForm I M ℝ k} {ψ : SmoothForm I M ℝ l}
    (hφ : φ ∈ closedForms I M k) (hψ : ψ ∈ closedForms I M l) :
    wedge φ ψ ∈ closedForms I M (k + l) := by
  rw [mem_closedForms] at hφ hψ ⊢
  ext x v
  have h := mextDeriv_wedge_apply φ ψ x v
  rw [hφ, hψ] at h
  simpa using h

/-- The wedge of an exact smooth form with a closed smooth form is exact. -/
theorem wedge_mem_exactForms_of_left_mem {φ : SmoothForm I M ℝ k} {ψ : SmoothForm I M ℝ l}
    (hφ : φ ∈ exactForms I M k) (hψ : ψ ∈ closedForms I M l) :
    wedge φ ψ ∈ exactForms I M (k + l) := by
  cases k with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot] at hφ
    rw [hφ, LinearMap.map_zero₂]
    exact zero_mem _
  | succ k =>
    rw [exactForms_succ, LinearMap.mem_range] at hφ
    obtain ⟨α, rfl⟩ := hφ
    rw [mem_closedForms] at hψ
    -- `d (α ∧ ψ) = dα ∧ ψ` because `ψ` is closed.
    refine mem_exactForms_of_apply_eq (by omega) (wedge α ψ) fun x v ↦ ?_
    have h := mextDeriv_wedge_apply α ψ x v
    rw [hψ] at h
    simpa [mextDerivₗ_apply] using h.symm

/-- The wedge of a closed smooth form with an exact smooth form is exact. -/
theorem wedge_mem_exactForms_of_right_mem {φ : SmoothForm I M ℝ k} {ψ : SmoothForm I M ℝ l}
    (hφ : φ ∈ closedForms I M k) (hψ : ψ ∈ exactForms I M l) :
    wedge φ ψ ∈ exactForms I M (k + l) := by
  cases l with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot] at hψ
    rw [hψ, map_zero]
    exact zero_mem _
  | succ l =>
    rw [exactForms_succ, LinearMap.mem_range] at hψ
    obtain ⟨β, rfl⟩ := hψ
    rw [mem_closedForms] at hφ
    -- `d ((-1) ^ k • φ ∧ β) = φ ∧ dβ` because `φ` is closed.
    refine mem_exactForms_of_apply_eq rfl ((-1 : ℝ) ^ k • wedge φ β) fun x v ↦ ?_
    simp [mextDeriv_wedge_of_left_closed hφ, ← mul_assoc, ← mul_pow]

/-- The wedge of a smooth form with a compactly supported smooth form is compactly supported. -/
theorem wedge_mem_compactlySupportedForms (φ : SmoothForm I M ℝ k) {ψ : SmoothForm I M ℝ l}
    (hψ : ψ ∈ compactlySupportedForms I M l) :
    wedge φ ψ ∈ compactlySupportedForms I M (k + l) := by
  rw [mem_compactlySupportedForms] at hψ ⊢
  rw [coe_wedge, RoughForm.wedge_def]
  exact hψ.of_isClosed_subset (_root_.isClosed_tsupport (α := E [⋀^Fin (k + l)]→L[ℝ] ℝ) _)
    (RoughForm.tsupport_wedgeWith_subset_right _ φ.1 ψ.1)

/-- The wedge of a closed smooth form with a compactly supported closed smooth form is
compactly supported and closed. -/
theorem wedge_mem_compactlySupportedClosedForms {φ : SmoothForm I M ℝ k}
    {ψ : SmoothForm I M ℝ l} (hφ : φ ∈ closedForms I M k)
    (hψ : ψ ∈ compactlySupportedClosedForms I M l) :
    wedge φ ψ ∈ compactlySupportedClosedForms I M (k + l) :=
  (mem_compactlySupportedClosedForms I).mpr
    ⟨wedge_mem_compactlySupportedForms φ ((mem_compactlySupportedClosedForms I).mp hψ).1,
      wedge_mem_closedForms hφ ((mem_compactlySupportedClosedForms I).mp hψ).2⟩

/-- The wedge of an exact smooth form with a compactly supported closed smooth form is the
exterior derivative of a compactly supported form. -/
theorem wedge_mem_exactCompactlySupportedForms_of_left_mem {φ : SmoothForm I M ℝ k}
    {ψ : SmoothForm I M ℝ l} (hφ : φ ∈ exactForms I M k)
    (hψ : ψ ∈ compactlySupportedClosedForms I M l) :
    wedge φ ψ ∈ exactCompactlySupportedForms I M (k + l) := by
  cases k with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot] at hφ
    rw [hφ, LinearMap.map_zero₂]
    exact zero_mem _
  | succ k =>
    rw [exactForms_succ, LinearMap.mem_range] at hφ
    obtain ⟨α, rfl⟩ := hφ
    obtain ⟨hψc, hψ⟩ := (mem_compactlySupportedClosedForms I).mp hψ
    rw [mem_closedForms] at hψ
    -- `d (α ∧ ψ) = dα ∧ ψ` because `ψ` is closed, and `α ∧ ψ` is compactly supported.
    refine mem_exactCompactlySupportedForms_of_apply_eq (by omega)
      (wedge_mem_compactlySupportedForms α hψc) fun x v ↦ ?_
    have h := mextDeriv_wedge_apply α ψ x v
    rw [hψ] at h
    simpa [mextDerivₗ_apply] using h.symm

/-- The wedge of a closed smooth form with the exterior derivative of a compactly supported
form is the exterior derivative of a compactly supported form. -/
theorem wedge_mem_exactCompactlySupportedForms_of_right_mem {φ : SmoothForm I M ℝ k}
    {ψ : SmoothForm I M ℝ l} (hφ : φ ∈ closedForms I M k)
    (hψ : ψ ∈ exactCompactlySupportedForms I M l) :
    wedge φ ψ ∈ exactCompactlySupportedForms I M (k + l) := by
  cases l with
  | zero =>
    rw [exactCompactlySupportedForms_zero, Submodule.mem_bot] at hψ
    rw [hψ, map_zero]
    exact zero_mem _
  | succ l =>
    rw [exactCompactlySupportedForms_succ, Submodule.mem_map] at hψ
    obtain ⟨β, hβ, rfl⟩ := hψ
    rw [mem_closedForms] at hφ
    -- `d ((-1) ^ k • φ ∧ β) = φ ∧ dβ` because `φ` is closed, and `φ ∧ β` is compactly supported.
    refine mem_exactCompactlySupportedForms_of_apply_eq rfl (β := (-1 : ℝ) ^ k • wedge φ β)
      (Submodule.smul_mem _ _ (wedge_mem_compactlySupportedForms φ hβ)) fun x v ↦ ?_
    simp [mextDeriv_wedge_of_left_closed hφ, ← mul_assoc, ← mul_pow]

end SmoothForm

namespace deRhamCohomology

/-- The wedge of two closed forms, followed by the cycle-class map. -/
private def wedgeClass (k l : ℕ) :
    closedForms I M k →ₗ[ℝ] closedForms I M l →ₗ[ℝ] deRhamCohomology I M (k + l) :=
  LinearMap.mk₂ ℝ
    (fun φ ψ ↦ mk I (k + l) ⟨_, SmoothForm.wedge_mem_closedForms φ.2 ψ.2⟩)
    (fun φ φ' ψ ↦ by
      rw [← map_add]
      congr 1
      exact Subtype.ext (LinearMap.map_add₂ _ _ _ _))
    (fun c φ ψ ↦ by
      rw [← map_smul]
      congr 1
      exact Subtype.ext (LinearMap.map_smul₂ _ _ _ _))
    (fun φ ψ ψ' ↦ by
      rw [← map_add]
      congr 1
      exact Subtype.ext (map_add _ _ _))
    (fun c φ ψ ↦ by
      rw [← map_smul]
      congr 1
      exact Subtype.ext (map_smul _ _ _))

private theorem wedgeClass_apply (φ : closedForms I M k) (ψ : closedForms I M l) :
    wedgeClass k l φ ψ = mk I (k + l) ⟨_, SmoothForm.wedge_mem_closedForms φ.2 ψ.2⟩ :=
  LinearMap.mk₂_apply ℝ _ φ ψ

/-- Exact forms in the second factor are killed by the wedge followed by the cycle-class map. -/
private theorem ker_mk_le_ker_wedgeClass_flip (k l : ℕ) :
    LinearMap.ker (mk I (M := M) l) ≤ LinearMap.ker (wedgeClass k l).flip := by
  intro ψ hψ
  rw [LinearMap.mem_ker, mk_eq_zero_iff] at hψ
  rw [LinearMap.mem_ker]
  ext φ
  rw [LinearMap.flip_apply, wedgeClass_apply, LinearMap.zero_apply, mk_eq_zero_iff]
  exact SmoothForm.wedge_mem_exactForms_of_right_mem φ.2 hψ

/-- The wedge of a closed form with a cohomology class, linear in both arguments. -/
private def wedgeClassRight (k l : ℕ) :
    deRhamCohomology I M l →ₗ[ℝ] closedForms I M k →ₗ[ℝ] deRhamCohomology I M (k + l) :=
  LinearMap.liftOfSurjective (R := ℝ) (M := closedForms I M l)
    (M₂ := deRhamCohomology I M l)
    (M₃ := closedForms I M k →ₗ[ℝ] deRhamCohomology I M (k + l)) (f := mk I (M := M) l)
    (mk_surjective I l) ⟨(wedgeClass k l).flip, ker_mk_le_ker_wedgeClass_flip k l⟩

private theorem wedgeClassRight_mk (φ : closedForms I M k) (ψ : closedForms I M l) :
    wedgeClassRight k l (mk I l ψ) φ = wedgeClass k l φ ψ := by
  rw [wedgeClassRight, LinearMap.equivOfSurjective_apply, LinearMap.flip_apply]

/-- Exact forms in the first factor are killed by the wedge followed by the cycle-class map. -/
private theorem ker_mk_le_ker_wedgeClassRight_flip (k l : ℕ) :
    LinearMap.ker (mk I (M := M) k) ≤ LinearMap.ker (wedgeClassRight k l).flip := by
  intro φ hφ
  rw [LinearMap.mem_ker, mk_eq_zero_iff] at hφ
  rw [LinearMap.mem_ker]
  ext c
  obtain ⟨ψ, rfl⟩ := mk_surjective I l c
  rw [LinearMap.flip_apply, wedgeClassRight_mk, wedgeClass_apply, LinearMap.zero_apply,
    mk_eq_zero_iff]
  exact SmoothForm.wedge_mem_exactForms_of_left_mem hφ ψ.2

variable (I M) in
/-- The wedge product on de Rham cohomology, `H^k_dR(M) → H^l_dR(M) → H^(k+l)_dR(M)`,
induced by the wedge of closed smooth forms. -/
def wedge (k l : ℕ) :
    deRhamCohomology I M k →ₗ[ℝ] deRhamCohomology I M l →ₗ[ℝ] deRhamCohomology I M (k + l) :=
  LinearMap.liftOfSurjective (R := ℝ) (M := closedForms I M k)
    (M₂ := deRhamCohomology I M k)
    (M₃ := deRhamCohomology I M l →ₗ[ℝ] deRhamCohomology I M (k + l)) (f := mk I (M := M) k)
    (mk_surjective I k) ⟨(wedgeClassRight k l).flip, ker_mk_le_ker_wedgeClassRight_flip k l⟩

/-- The wedge of the classes of two closed forms is the class of their wedge. -/
@[simp]
theorem wedge_mk (φ : closedForms I M k) (ψ : closedForms I M l) :
    wedge I M k l (mk I k φ) (mk I l ψ) =
      mk I (k + l) ⟨_, SmoothForm.wedge_mem_closedForms φ.2 ψ.2⟩ := by
  rw [wedge, LinearMap.equivOfSurjective_apply, LinearMap.flip_apply, wedgeClassRight_mk,
    wedgeClass_apply]

end deRhamCohomology

namespace compactlySupportedDeRhamCohomology

/-- The wedge of a closed form with a compactly supported closed form, followed by the
compactly supported cycle-class map. -/
private def wedgeClass (k l : ℕ) :
    closedForms I M k →ₗ[ℝ] compactlySupportedClosedForms I M l →ₗ[ℝ]
      compactlySupportedDeRhamCohomology I M (k + l) :=
  LinearMap.mk₂ ℝ
    (fun φ ψ ↦ mk I (k + l) ⟨_, SmoothForm.wedge_mem_compactlySupportedClosedForms φ.2 ψ.2⟩)
    (fun φ φ' ψ ↦ by
      rw [← map_add]
      congr 1
      exact Subtype.ext (LinearMap.map_add₂ _ _ _ _))
    (fun c φ ψ ↦ by
      rw [← map_smul]
      congr 1
      exact Subtype.ext (LinearMap.map_smul₂ _ _ _ _))
    (fun φ ψ ψ' ↦ by
      rw [← map_add]
      congr 1
      exact Subtype.ext (map_add _ _ _))
    (fun c φ ψ ↦ by
      rw [← map_smul]
      congr 1
      exact Subtype.ext (map_smul _ _ _))

private theorem wedgeClass_apply (φ : closedForms I M k) (ψ : compactlySupportedClosedForms I M l) :
    wedgeClass k l φ ψ =
      mk I (k + l) ⟨_, SmoothForm.wedge_mem_compactlySupportedClosedForms φ.2 ψ.2⟩ :=
  LinearMap.mk₂_apply ℝ _ φ ψ

/-- Compactly supported exact forms in the second factor are killed by the wedge followed by the
class map. -/
private theorem ker_mk_le_ker_wedgeClass_flip (k l : ℕ) :
    LinearMap.ker (mk I (M := M) l) ≤ LinearMap.ker (wedgeClass k l).flip := by
  intro ψ hψ
  rw [LinearMap.mem_ker, mk_eq_zero_iff] at hψ
  rw [LinearMap.mem_ker]
  ext φ
  rw [LinearMap.flip_apply, wedgeClass_apply, LinearMap.zero_apply, mk_eq_zero_iff]
  exact SmoothForm.wedge_mem_exactCompactlySupportedForms_of_right_mem φ.2 hψ

/-- The wedge of a closed form with a compactly supported class, linear in both arguments. -/
private def wedgeClassRight (k l : ℕ) :
    compactlySupportedDeRhamCohomology I M l →ₗ[ℝ] closedForms I M k →ₗ[ℝ]
      compactlySupportedDeRhamCohomology I M (k + l) :=
  LinearMap.liftOfSurjective (R := ℝ) (M := compactlySupportedClosedForms I M l)
    (M₂ := compactlySupportedDeRhamCohomology I M l)
    (M₃ := closedForms I M k →ₗ[ℝ] compactlySupportedDeRhamCohomology I M (k + l))
    (f := mk I (M := M) l) (mk_surjective I l)
    ⟨(wedgeClass k l).flip, ker_mk_le_ker_wedgeClass_flip k l⟩

private theorem wedgeClassRight_mk (φ : closedForms I M k)
    (ψ : compactlySupportedClosedForms I M l) :
    wedgeClassRight k l (mk I l ψ) φ = wedgeClass k l φ ψ := by
  rw [wedgeClassRight, LinearMap.equivOfSurjective_apply, LinearMap.flip_apply]

/-- Exact forms in the first factor are killed by the wedge followed by the class map. -/
private theorem ker_mk_le_ker_wedgeClassRight_flip (k l : ℕ) :
    LinearMap.ker (deRhamCohomology.mk I (M := M) k) ≤
      LinearMap.ker (wedgeClassRight k l).flip := by
  intro φ hφ
  rw [LinearMap.mem_ker, deRhamCohomology.mk_eq_zero_iff] at hφ
  rw [LinearMap.mem_ker]
  ext c
  obtain ⟨ψ, rfl⟩ := mk_surjective I l c
  rw [LinearMap.flip_apply, wedgeClassRight_mk, wedgeClass_apply, LinearMap.zero_apply,
    mk_eq_zero_iff]
  exact SmoothForm.wedge_mem_exactCompactlySupportedForms_of_left_mem hφ ψ.2

variable (I M) in
/-- The wedge product `H^k_dR(M) → H^l_c(M) → H^(k+l)_c(M)` of a de Rham class with a
compactly supported class, induced by the wedge of a closed smooth form with a compactly
supported closed smooth form. -/
def wedge (k l : ℕ) :
    deRhamCohomology I M k →ₗ[ℝ] compactlySupportedDeRhamCohomology I M l →ₗ[ℝ]
      compactlySupportedDeRhamCohomology I M (k + l) :=
  LinearMap.liftOfSurjective (R := ℝ) (M := closedForms I M k)
    (M₂ := deRhamCohomology I M k)
    (M₃ := compactlySupportedDeRhamCohomology I M l →ₗ[ℝ]
      compactlySupportedDeRhamCohomology I M (k + l))
    (f := deRhamCohomology.mk I (M := M) k) (deRhamCohomology.mk_surjective I k)
    ⟨(wedgeClassRight k l).flip, ker_mk_le_ker_wedgeClassRight_flip k l⟩

/-- The wedge of the class of a closed form with the class of a compactly supported closed form
is the compactly supported class of their wedge. -/
@[simp]
theorem wedge_mk (φ : closedForms I M k) (ψ : compactlySupportedClosedForms I M l) :
    wedge I M k l (deRhamCohomology.mk I k φ) (mk I l ψ) =
      mk I (k + l) ⟨_, SmoothForm.wedge_mem_compactlySupportedClosedForms φ.2 ψ.2⟩ := by
  rw [wedge, LinearMap.equivOfSurjective_apply, LinearMap.flip_apply, wedgeClassRight_mk,
    wedgeClass_apply]

end compactlySupportedDeRhamCohomology

end TauCeti
