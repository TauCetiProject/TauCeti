/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import TauCeti.Topology.Connected.FiniteFamily
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Conjugation of continuous polynomial root branches

Suppose a polynomial family on a connected parameter space has a continuous labelling of all
its roots, pointwise distinct, and its coefficients intertwine a continuous involution of the
parameters with complex conjugation. Conjugation then acts on the labels by one unique
involutive permutation, independent of the parameter. At any parameter fixed by the involution,
a branch is real precisely when its label is fixed by this permutation. In particular a branch
which is real at one fixed parameter is real at every fixed parameter.

For Puiseux branches, the parameter involution conjugates the complex base coordinates and the
power-substitution variable. The punctured product is connected and the roots are distinct
there. The conclusions concern the given branches; their construction and their extension
across the missing hyperplane are separate results.

`existsUnique_root_conj_perm_of_subset_closure` extends this permutation to a larger
parameter set on which the branches are continuous. Distinctness is needed only on the
preconnected dense subset; roots may collide on its boundary.

For real polynomial families, persistence of collisions also gives a local realness criterion
without distinctness: a labelled root is real nearby exactly when it is real at the center.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 4.
-/

public section

open Filter Polynomial Set Topology ComplexConjugate

namespace TauCeti

/-- In a finite continuous complete labelling of the complex roots of a real polynomial
family, the real labels are locally constant if collisions persist locally. Repeated labels
are allowed, and neither connectedness nor coefficient continuity is required. -/
theorem eventually_root_im_eq_zero_iff_of_persistent_collisions {B ι : Type*}
    [TopologicalSpace B] [Finite ι] {F : B → ℝ[X]} {r : ι → B → ℂ} {b₀ : B}
    (hr : ∀ i, ContinuousAt (r i) b₀)
    (hroot : ∀ᶠ b in 𝓝 b₀, ∀ z, ((F b).map (algebraMap ℝ ℂ)).IsRoot z ↔
      ∃ i, r i b = z)
    (hcollision : ∀ i j, r j b₀ = r i b₀ → r j =ᶠ[𝓝 b₀] r i) :
    ∀ᶠ b in 𝓝 b₀, ∀ i, (r i b).im = 0 ↔ (r i b₀).im = 0 := by
  rw [eventually_all]
  intro i
  by_cases hi : (r i b₀).im = 0
  · have hmem : ∀ᶠ b in 𝓝 b₀, conj (r i b) ∈ range (fun j ↦ r j b) := by
      filter_upwards [hroot] with b hb
      have hz := (hb (r i b)).2 ⟨i, rfl⟩
      rw [IsRoot.def, eval_map_algebraMap] at hz
      apply (hb _).1
      rw [IsRoot.def, eval_map_algebraMap, aeval_conj, hz, map_zero]
    have heq := eventuallyEq_of_continuousAt_mem_range hr
      (Complex.continuous_conj.continuousAt.comp (hr i)) hmem
      (Complex.conj_eq_iff_im.mpr hi).symm (hcollision i)
    filter_upwards [heq] with b hb
    exact iff_of_true (Complex.conj_eq_iff_im.mp hb.symm) hi
  · have hne := (Complex.continuous_im.continuousAt.comp (hr i)).eventually_ne hi
    exact hne.mono fun _ hb ↦ iff_of_false hb hi

variable {B ι : Type*} [TopologicalSpace B] [PreconnectedSpace B] [Finite ι]
  {F : B → ℂ[X]} {r : ι → B → ℂ} {τ : B → B}

/-- Conjugation acts on a continuous, pointwise distinct complete labelling of the roots by a
unique permutation, and that permutation is an involution. The coefficient symmetry is expressed
by mapping the polynomial by complex conjugation; no analyticity or monicity is required. -/
theorem existsUnique_root_conj_perm
    (hr : ∀ i, Continuous (r i)) (hinj : ∀ b, Function.Injective (fun i => r i b))
    (hroot : ∀ b z, (F b).IsRoot z ↔ ∃ i, r i b = z)
    (hτ : Continuous τ) (hττ : Function.Involutive τ)
    (hF : ∀ b, F (τ b) = (F b).map (starRingEnd ℂ)) (b₀ : B) :
    ∃! σ : Equiv.Perm ι, Function.Involutive σ ∧
      ∀ i b, r (σ i) b = conj (r i (τ b)) := by
  classical
  have hmem (i : ι) (b : B) : conj (r i (τ b)) ∈ range (fun j => r j b) := by
    have hz := (hroot (τ b) _).2 ⟨i, rfl⟩
    have hmap := congrArg (fun p : ℂ[X] => p.eval (conj (r i (τ b)))) (hF (τ b))
    simp only [hττ b, eval_map_apply, hz.eq_zero, map_zero] at hmap
    exact (hroot b _).1 hmap
  choose p hp using fun i => hmem i b₀
  have hall (i : ι) (b : B) : r (p i) b = conj (r i (τ b)) :=
    congrFun (eq_of_continuous_mem_range hr ((Complex.continuous_conj.comp (hr i)).comp hτ)
      hinj (hmem i) b₀ (hp i)) b
  have hpp : Function.Involutive p := by
    intro i
    apply hinj b₀
    simp only [hall, hττ b₀, Complex.conj_conj]
  let σ : Equiv.Perm ι := Equiv.ofBijective p hpp.bijective
  refine ⟨σ, ⟨hpp, hall⟩, ?_⟩
  intro σ' hσ'
  ext i
  exact hinj b₀ ((hσ'.2 i b₀).trans (hall i b₀).symm)

omit [TopologicalSpace B] [PreconnectedSpace B] [Finite ι] in
/-- For a distinct root labelling on which conjugation acts by a permutation, a root is real
exactly when its label is fixed by that permutation. This is a pointwise criterion. -/
theorem root_conj_perm_apply_eq_self_iff_im_eq_zero {b : B}
    (hinj : Function.Injective (fun i => r i b)) {σ : Equiv.Perm ι}
    (hσ : ∀ i, r (σ i) b = conj (r i b)) (i : ι) :
    σ i = i ↔ (r i b).im = 0 := by
  rw [← hinj.eq_iff, hσ, Complex.conj_eq_iff_im]

/-- A branch real at one conjugation-fixed parameter is real at every conjugation-fixed
parameter, even when the fixed locus itself is disconnected. -/
theorem root_im_eq_zero_iff_of_fixed
    (hr : ∀ i, Continuous (r i)) (hinj : ∀ b, Function.Injective (fun i => r i b))
    (hroot : ∀ b z, (F b).IsRoot z ↔ ∃ i, r i b = z)
    (hτ : Continuous τ) (hττ : Function.Involutive τ)
    (hF : ∀ b, F (τ b) = (F b).map (starRingEnd ℂ))
    {b₀ b₁ : B} (hb₀ : τ b₀ = b₀) (hb₁ : τ b₁ = b₁) (i : ι) :
    (r i b₀).im = 0 ↔ (r i b₁).im = 0 := by
  obtain ⟨σ, ⟨-, hσ⟩, -⟩ := existsUnique_root_conj_perm hr hinj hroot hτ hττ hF b₀
  have h₀ := root_conj_perm_apply_eq_self_iff_im_eq_zero (hinj b₀)
    (fun j => by simpa [hb₀] using hσ j b₀) i
  have h₁ := root_conj_perm_apply_eq_self_iff_im_eq_zero (hinj b₁)
    (fun j => by simpa [hb₁] using hσ j b₁) i
  exact h₀.symm.trans h₁

end TauCeti

namespace TauCeti

variable {B ι : Type*} [TopologicalSpace B] [Finite ι]
  {S T : Set B} {F : B → ℂ[X]} {r : ι → B → ℂ} {τ : B → B}

/-- Conjugation of a complete, distinct root labelling on a preconnected subset extends
uniquely to its continuous branches on a larger set contained in its closure. Roots may
collide on the larger set. Polynomial symmetry and root coverage are required only on the
dense subset. -/
theorem existsUnique_root_conj_perm_of_subset_closure
    (hS : IsPreconnected S) (hST : S ⊆ T) (hTS : T ⊆ closure S)
    (hr : ∀ i, ContinuousOn (r i) T)
    (hinj : ∀ b ∈ S, Function.Injective (fun i => r i b))
    (hroot : ∀ b ∈ S, ∀ z, (F b).IsRoot z ↔ ∃ i, r i b = z)
    (hτ : ContinuousOn τ T) (hτS : MapsTo τ S S) (hτT : MapsTo τ T T)
    (hττ : ∀ b ∈ S, τ (τ b) = b)
    (hF : ∀ b ∈ S, F (τ b) = (F b).map (starRingEnd ℂ)) (b₀ : S) :
    ∃! σ : Equiv.Perm ι, Function.Involutive σ ∧
      ∀ i b, b ∈ T → r (σ i) b = conj (r i (τ b)) := by
  let := Subtype.preconnectedSpace hS
  let τS : S → S := fun b => ⟨τ b, hτS b.property⟩
  have hτSc : Continuous τS :=
    ((hτ.mono hST).domRestrict).subtype_mk _
  have hτSτS : Function.Involutive τS := fun b => Subtype.ext (hττ b b.property)
  obtain ⟨σ, ⟨hσσ, hσ⟩, huniq⟩ := existsUnique_root_conj_perm
    (fun i => ((hr i).mono hST).domRestrict) (fun b => hinj b b.property)
    (fun b z => hroot b b.property z) hτSc hτSτS
    (fun b => hF b b.property) b₀
  refine ⟨σ, ⟨hσσ, ?_⟩, ?_⟩
  · intro i
    have heq : EqOn (r (σ i)) (fun b => conj (r i (τ b))) S :=
      fun b hb => hσ i ⟨b, hb⟩
    exact heq.of_subset_closure (hr (σ i))
      (Complex.continuous_conj.comp_continuousOn ((hr i).comp hτ hτT)) hST hTS
  · intro σ' hσ'
    exact huniq σ' ⟨hσ'.1, fun i b => hσ'.2 i b (hST b.property)⟩

end TauCeti
