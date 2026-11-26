/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# De Rham cohomology of a union of disjoint open sets

Let `s i` be open subsets of a manifold `M` and `W = ⨆ i, s i` their union. A form on `W` is
determined by its restrictions to the `s i`
(`TauCeti.SmoothForm.injective_pi_mpullback_inclusion_iSup`). When the `s i` are pairwise
disjoint, every family of forms on the `s i` is the family of restrictions of a form on `W`
(`TauCeti.SmoothForm.surjective_pi_mpullback_inclusion_iSup`): at a point of `W` take the value of
the form on the unique `s i` containing it. Smoothness is local, so the glued form is smooth.

Since the exterior derivative commutes with restriction, the same holds for closed and exact
forms, and the restrictions identify the de Rham cohomology of `W` with the product of the de
Rham cohomologies of the `s i`, in every degree
(`TauCeti.deRhamCohomology.bijective_pi_map_inclusion_iSup`). No finiteness, separation or
countability assumption is needed. This is the disjoint-union step of a Mayer–Vietoris induction
over open sets (`TauCeti.mayerVietoris_induction`) comparing de Rham cohomology with another
cohomology theory, such as the de Rham theorem.

## Main results

* `TauCeti.SmoothForm.bijective_pi_mpullback_inclusion_iSup`: smooth forms on a union of pairwise
  disjoint open sets are the families of smooth forms on the members.
* `TauCeti.deRhamCohomology.bijective_pi_map_inclusion_iSup`: the de Rham cohomology of a union of
  pairwise disjoint open sets is the product of the de Rham cohomologies of the members.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18 (the disjoint-union step in the proof of Theorem 18.14).
-/

public section

noncomputable section

open Function TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {ι : Type*} {s : ι → Opens M}

namespace SmoothForm

variable [IsManifold I 1 M]

/-- A smooth form on a union of open sets is determined by its restrictions to the members. -/
theorem injective_pi_mpullback_inclusion_iSup :
    Injective (LinearMap.pi fun i ↦ mpullback (I := I) (I' := I) (F := F) (k := k)
      (Opens.inclusion (le_iSup s i)) (contMDiff_inclusion _)) := by
  refine (injective_iff_map_eq_zero _).mpr fun φ hφ ↦ Subtype.ext (funext fun x ↦ ?_)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
  obtain ⟨y, rfl⟩ : ∃ y : s i, Opens.inclusion (le_iSup s i) y = x :=
    ⟨⟨x, hi⟩, (Set.inclusion_mk _ _).trans (Subtype.coe_eta _ _)⟩
  have h := congrFun (congrArg Subtype.val (congrFun hφ i)) y
  simp only [LinearMap.pi_apply, coe_mpullback, mpullback_inclusion_apply, ZeroMemClass.coe_zero,
    Pi.zero_apply] at h ⊢
  exact h

/-- Smooth forms on pairwise disjoint open sets `s i` are the restrictions of a smooth form on
their union: its value at a point is that of the form on the unique `s i` containing it. -/
theorem surjective_pi_mpullback_inclusion_iSup (hs : Pairwise (Disjoint on s)) :
    Surjective (LinearMap.pi fun i ↦ mpullback (I := I) (I' := I) (F := F) (k := k)
      (Opens.inclusion (le_iSup s i)) (contMDiff_inclusion _)) := by
  intro φ
  have hmem (x : (⨆ i, s i : Opens M)) : ∃ i, (x : M) ∈ s i := Opens.mem_iSup.mp x.property
  set γ : RoughForm I (⨆ i, s i : Opens M) F k := fun x ↦
    (φ (hmem x).choose).val ⟨x, (hmem x).choose_spec⟩ with hγdef
  -- The point `y` of `s i` lies in no other member, so `γ` takes the value of `φ i` there.
  have hγ (i : ι) : TauCeti.mpullback I I (Opens.inclusion (le_iSup s i)) γ = (φ i).val := by
    funext y
    have key (x : (⨆ i, s i : Opens M)) (hx : (x : M) = y) (j : ι) (hj : (x : M) ∈ s j) :
        (φ j).val ⟨x, hj⟩ = (φ i).val y := by
      obtain ⟨y, hy⟩ := y
      subst hx
      obtain rfl : j = i := by
        by_contra hji
        exact Set.disjoint_left.mp (Opens.coe_disjoint.mpr (hs hji)) hj hy
      rfl
    rw [mpullback_inclusion_apply, hγdef]
    exact key _ (Set.coe_inclusion _ y) _ _
  have hγs : IsSmoothForm I ∞ γ :=
    IsSmoothForm.of_mpullback_inclusion (le_iSup s) hmem fun i ↦ hγ i ▸ (φ i).isSmoothForm
  exact ⟨⟨γ, hγs.mem_smoothBundleForms⟩,
    funext fun i ↦ Subtype.ext ((coe_mpullback _ _ _).trans (hγ i))⟩

/-- **Smooth forms on a disjoint union of open sets.** Restriction identifies the smooth forms
on a union of pairwise disjoint open sets `s i` with the families of smooth forms on the `s i`. -/
theorem bijective_pi_mpullback_inclusion_iSup (hs : Pairwise (Disjoint on s)) :
    Bijective (LinearMap.pi fun i ↦ mpullback (I := I) (I' := I) (F := F) (k := k)
      (Opens.inclusion (le_iSup s i)) (contMDiff_inclusion _)) :=
  ⟨injective_pi_mpullback_inclusion_iSup, surjective_pi_mpullback_inclusion_iSup hs⟩

end SmoothForm

namespace deRhamCohomology

variable [IsManifold I 2 M]

/-- A smooth form on a union of open sets whose restrictions to the members are all closed is
closed. -/
private theorem mem_closedForms_of_forall {γ : SmoothForm I (⨆ i, s i : Opens M) ℝ k}
    (h : ∀ i, SmoothForm.mpullback (Opens.inclusion (le_iSup s i)) (contMDiff_inclusion _) γ ∈
      closedForms I (s i) k) :
    γ ∈ closedForms I (⨆ i, s i : Opens M) k := by
  rw [mem_closedForms_iff_mextDerivₗ_eq_zero]
  refine SmoothForm.injective_pi_mpullback_inclusion_iSup (s := s) (funext fun i ↦ ?_)
  rw [LinearMap.pi_apply, ← SmoothForm.mextDerivₗ_mpullback,
    (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mp (h i)]
  simp

/-- A closed form on a union of open sets whose restrictions to the members are exact is exact,
when the members are pairwise disjoint: primitives on the members glue to a primitive. -/
private theorem mem_exactForms_of_forall (hs : Pairwise (Disjoint on s))
    {φ : closedForms I (⨆ i, s i : Opens M) k}
    (h : ∀ i, (closedForms.mpullback (Opens.inclusion (le_iSup s i)) (contMDiff_inclusion _) k
      φ).val ∈ exactForms I (s i) k) :
    φ.val ∈ exactForms I (⨆ i, s i : Opens M) k := by
  cases k with
  | zero =>
    simp only [exactForms_zero, Submodule.mem_bot, closedForms.coe_mpullback] at h ⊢
    refine SmoothForm.injective_pi_mpullback_inclusion_iSup (s := s) (funext fun i ↦ ?_)
    simp [h i]
  | succ k =>
    simp only [exactForms_succ, LinearMap.mem_range, closedForms.coe_mpullback] at h ⊢
    choose ψ hψ using h
    obtain ⟨η, hη⟩ := SmoothForm.surjective_pi_mpullback_inclusion_iSup (I := I) hs ψ
    refine ⟨η, SmoothForm.injective_pi_mpullback_inclusion_iSup (s := s) (funext fun i ↦ ?_)⟩
    simp [← SmoothForm.mextDerivₗ_mpullback, ← hψ i, ← congrFun hη i]

/-- **De Rham cohomology of a disjoint union of open sets.** Restriction identifies the de Rham
cohomology of a union of pairwise disjoint open sets `s i` with the product of the de Rham
cohomologies of the `s i`, in every degree. -/
theorem bijective_pi_map_inclusion_iSup (hs : Pairwise (Disjoint on s)) (k : ℕ) :
    Bijective (LinearMap.pi fun i ↦ map (I := I) (I' := I) (Opens.inclusion (le_iSup s i))
      (contMDiff_inclusion _) k) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun c hc ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨φ, rfl⟩ := mk_surjective I k c
    refine (mk_eq_zero_iff I k φ).mpr (mem_exactForms_of_forall hs fun i ↦ ?_)
    have hi := congrFun hc i
    rwa [LinearMap.pi_apply, map_mk, Pi.zero_apply, mk_eq_zero_iff] at hi
  · choose φ hφ using fun i ↦ mk_surjective I k (c i)
    obtain ⟨γ, hγ⟩ := SmoothForm.surjective_pi_mpullback_inclusion_iSup (I := I) (F := ℝ) hs
      fun i ↦ (φ i).val
    have hγc : γ ∈ closedForms I (⨆ i, s i : Opens M) k :=
      mem_closedForms_of_forall fun i ↦ by
        have hγi := congrFun hγ i
        rw [LinearMap.pi_apply] at hγi
        exact hγi ▸ (φ i).property
    refine ⟨mk I k ⟨γ, hγc⟩, funext fun i ↦ ?_⟩
    rw [LinearMap.pi_apply, map_mk, ← hφ i]
    congr 1
    exact Subtype.ext ((closedForms.coe_mpullback _ _ _ _).trans (congrFun hγ i))

end deRhamCohomology

end TauCeti
