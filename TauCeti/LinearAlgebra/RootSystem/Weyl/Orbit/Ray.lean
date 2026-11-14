/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import TauCeti.LinearAlgebra.Ray
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import TauCeti.LinearAlgebra.RootSystem.Positive
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Rays and translates of Weyl orbits of weights

Two facts about the Weyl orbit `W λ` of a weight `λ` of a root pairing over a linearly ordered
field. When the Weyl group is finite, no two distinct weights of `W λ` lie in the same ray, so a
vector in `W λ` is determined by its direction. Adding a weight `χ` fixed by the Weyl group maps
`W λ` into `W (λ + χ)`, since `w λ + χ = w (λ + χ)`.

These are the hypotheses under which a path with velocities in `W λ` has a unique distinguished
presentation, and its central shift by `χ` has velocities in `W (λ + χ)`; see
`TauCeti/RepresentationTheory/LSPath/Distinguished.lean`.

Each Weyl orbit is stable under root reflections. For a root pairing over `ℤ`, an additive map
`f` from the weight lattice to a vector space carries
the reflection `s_i` in the root `αᵢ` to the reflection in `f αᵢ` along a linear form agreeing
with the coroot `αᵢ^∨`, so the image `f (W λ)` is stable under the latter. This is the hypothesis
under which the root operators preserve paths with velocities in `f (W λ)`; see
`TauCeti/RepresentationTheory/LSPath/OrbitStable.lean`. When `P` has finitely many roots and
linear forms on `V` induce all simple coroots of a base `b`, `f` is automatically injective on
`W λ` and no two distinct vectors of `f (W λ)` lie on a common ray, even without global
injectivity of `f` on central weights.

## Main results

* `RootPairing.pairwise_not_sameRay_orbit_weylGroup`: when the Weyl group is finite, no two
  distinct weights of a Weyl orbit lie in the same ray.
* `RootPairing.mapsTo_add_orbit_weylGroup`: adding a Weyl-invariant weight `χ` maps `W λ` into
  `W (λ + χ)`.
* `RootPairing.mapsTo_preReflection_image_orbit_weylGroup`: the image `f (W λ)` of a Weyl orbit
  in a vector space is stable under the reflection in an image root `f αᵢ`, along a linear form
  agreeing with the coroot `αᵢ^∨`.
* `RootPairing.eq_of_sameRay_apply_of_mem_orbit_weylGroup`,
  `RootPairing.injOn_orbit_weylGroup_of_coroot'` and
  `RootPairing.pairwise_not_sameRay_image_orbit_weylGroup_of_coroot'`: when linear forms induce the
  simple coroots of a base on `f`, `f` is injective on `W λ` and separates rays of `f (W λ)`.
-/

public section

namespace RootPairing

section Field

variable {ι 𝕜 V N : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V] [AddCommGroup N] [Module 𝕜 N] (P : RootPairing ι 𝕜 V N)

/-- When the Weyl group is finite, no two distinct weights of a Weyl orbit lie in the same ray.
So a path with velocities in `W λ` has at most one distinguished presentation for `W λ`. -/
theorem pairwise_not_sameRay_orbit_weylGroup [Finite P.weylGroup] (lam : V) :
    (MulAction.orbit P.weylGroup lam).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v :=
  fun _ hu _ hv huv h ↦ huv (h.eq_of_mem_orbit hu hv (Set.finite_range _))

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Adding a weight `χ` fixed by the Weyl group maps the Weyl orbit `W λ` to `W (λ + χ)`, since
`w λ + χ = w (λ + χ)`. So the central shift by `χ` transports paths with velocities in `W λ` to
paths with velocities in `W (λ + χ)`. -/
theorem mapsTo_add_orbit_weylGroup {χ : V} (hχ : ∀ w : P.weylGroup, w • χ = χ) (lam : V) :
    Set.MapsTo (· + χ) (MulAction.orbit P.weylGroup lam)
      (MulAction.orbit P.weylGroup (lam + χ)) := by
  rintro _ ⟨w, rfl⟩
  exact ⟨w, by simp only [smul_add, hχ]⟩

end Field

section CommRing

variable {ι R V N : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R V N)

/-- A Weyl orbit is stable under reflection in any root along its coroot. -/
theorem mapsTo_preReflection_orbit_weylGroup (i : ι) (lam : V) :
    Set.MapsTo (Module.preReflection (P.root i) (P.coroot' i))
      (MulAction.orbit P.weylGroup lam) (MulAction.orbit P.weylGroup lam) := by
  intro v hv
  simpa [P.reflection_apply, Module.preReflection_apply] using
    MulAction.mapsTo_smul_orbit (weylGroup.ofIdx P i) lam hv

end CommRing

section Realization

variable {ι M N 𝕜 V : Type*} [AddCommGroup M] [AddCommGroup N] (P : RootPairing ι ℤ M N)
  [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] {f : M →+ V}

/-- An additive map `f` from the weight lattice intertwines the reflection `s_i` in the root `αᵢ`
with the reflection in the image root `f αᵢ` along a linear form `F` agreeing with the coroot
`αᵢ^∨` on the weight lattice. -/
theorem map_reflection_eq_preReflection (i : ι) {F : Module.Dual 𝕜 V}
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (m : M) :
    f (P.reflection i m) = Module.preReflection (f (P.root i)) F (f m) := by
  simp [P.reflection_apply, Module.preReflection_apply, hF, Int.cast_smul_eq_zsmul]

/-- The image `f (W λ)` of a Weyl orbit under an additive map `f` from the weight lattice is
stable under the reflection in the image root `f αᵢ` along a linear form `F` agreeing with the
coroot `αᵢ^∨` on the weight lattice. -/
theorem mapsTo_preReflection_image_orbit_weylGroup (i : ι) {F : Module.Dual 𝕜 V}
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    Set.MapsTo (Module.preReflection (f (P.root i)) F) (f '' MulAction.orbit P.weylGroup lam)
      (f '' MulAction.orbit P.weylGroup lam) := by
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  refine ⟨_, ⟨weylGroup.ofIdx P i * w, rfl⟩, ?_⟩
  dsimp only
  rw [mul_smul, weylGroup.ofIdx_smul, Equiv.reflection_smul,
    P.map_reflection_eq_preReflection i hF]

/-- Two weights in the same Weyl orbit of a finite integral root pairing are equal as soon as they
have the same pairings with the simple coroots of a base: their difference lies in both the root
span and the kernel of the root form. -/
theorem eq_of_mem_orbit_weylGroup_of_forall_coroot'_eq [Finite ι] (b : P.Base) {lam m₁ m₂ : M}
    (hm₁ : m₁ ∈ MulAction.orbit P.weylGroup lam) (hm₂ : m₂ ∈ MulAction.orbit P.weylGroup lam)
    (h : ∀ i ∈ b.support, P.coroot' i m₁ = P.coroot' i m₂) : m₁ = m₂ := by
  cases nonempty_fintype ι
  have hspan : ∀ g ∈ P.weylGroup, ∀ x : M, g • x - x ∈ P.rootSpan ℤ := by
    intro g hg
    induction hg using weylGroup.induction with
    | mem i =>
      intro x
      rw [Equiv.reflection_smul, P.reflection_apply, sub_sub_cancel_left]
      exact neg_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    | one => intro x; simp
    | mul g₁ g₂ _ _ ih₁ ih₂ =>
      intro x
      rw [mul_smul, show g₁ • g₂ • x - x = (g₁ • (g₂ • x) - g₂ • x) + (g₂ • x - x) by abel]
      exact add_mem (ih₁ (g₂ • x)) (ih₂ x)
  obtain ⟨w₁, rfl⟩ := hm₁
  obtain ⟨w₂, rfl⟩ := hm₂
  have hdiff : w₁ • lam - w₂ • lam ∈ P.rootSpan ℤ := by
    rw [show w₁ • lam - w₂ • lam = ((w₁ : P.Aut) • lam - lam) - ((w₂ : P.Aut) • lam - lam) by
      simp [Subgroup.smul_def]]
    exact sub_mem (hspan _ w₁.2 lam) (hspan _ w₂.2 lam)
  have heq (j : ι) : (P.toLinearMap (w₁ • lam)) (P.coroot j) =
      (P.toLinearMap (w₂ • lam)) (P.coroot j) := by
    have hz : P.coroot' j (w₁ • lam - w₂ • lam) = 0 :=
      P.coroot'_eq_zero_of_forall_mem_support b (fun i hi ↦ by rw [map_sub, h i hi, sub_self]) j
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  have hker : w₁ • lam - w₂ • lam ∈ LinearMap.ker P.RootForm := by
    rw [LinearMap.mem_ker]
    ext z
    simp [rootForm_apply_apply, heq]
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp P.disjoint_rootSpan_ker_rootForm _ hdiff hker)

/-- **If linear forms on `V` induce all simple coroots on `f(M)`, two weights in a Weyl orbit whose
images under `f` lie in the same ray are equal.** Neither injectivity of `f` on central weights nor
spanning of the roots is needed: every coroot is an integer combination of the simple coroots, and
the sum of squared coroot pairings is constant on each Weyl orbit. -/
theorem eq_of_sameRay_apply_of_mem_orbit_weylGroup [Finite ι] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {P : RootPairing ι ℤ M N} (b : P.Base)
    {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (m : M), F i (f m) = (P.coroot' i m : 𝕜))
    {lam m₁ m₂ : M} (hm₁ : m₁ ∈ MulAction.orbit P.weylGroup lam)
    (hm₂ : m₂ ∈ MulAction.orbit P.weylGroup lam) (hray : SameRay 𝕜 (f m₁) (f m₂)) :
    m₁ = m₂ := by
  cases nonempty_fintype ι
  by_cases hf₁ : f m₁ = 0
  · have hz : ∀ i ∈ b.support, P.coroot' i m₁ = 0 := fun i hi ↦ by
      have hc := hF ⟨i, hi⟩ m₁
      rw [hf₁, map_zero] at hc
      exact_mod_cast hc.symm
    obtain ⟨w₁, rfl⟩ := hm₁
    obtain ⟨w₂, rfl⟩ := hm₂
    calc
      w₁ • lam = (w₂ * w₁⁻¹) • (w₁ • lam) :=
        (TauCeti.smul_eq_self_of_forall_coroot'_eq_zero b hz (w₂ * w₁⁻¹)).symm
      _ = w₂ • lam := by rw [mul_smul, inv_smul_smul]
  by_cases hf₂ : f m₂ = 0
  · have hz : ∀ i ∈ b.support, P.coroot' i m₂ = 0 := fun i hi ↦ by
      have hc := hF ⟨i, hi⟩ m₂
      rw [hf₂, map_zero] at hc
      exact_mod_cast hc.symm
    obtain ⟨w₁, rfl⟩ := hm₁
    obtain ⟨w₂, rfl⟩ := hm₂
    calc
      w₁ • lam = (w₁ * w₂⁻¹) • (w₂ • lam) := by rw [mul_smul, inv_smul_smul]
      _ = w₂ • lam := TauCeti.smul_eq_self_of_forall_coroot'_eq_zero b hz (w₁ * w₂⁻¹)
  obtain ⟨r, hr, hrf⟩ := hray.exists_pos_left hf₁ hf₂
  have hsimple (i : ι) (hi : i ∈ b.support) :
      (P.coroot' i m₂ : 𝕜) = r * (P.coroot' i m₁ : 𝕜) := by
    rw [← hF ⟨i, hi⟩ m₂, ← hF ⟨i, hi⟩ m₁, ← hrf, map_smul, smul_eq_mul]
  have hall (j : ι) : (P.coroot' j m₂ : 𝕜) = r * (P.coroot' j m₁ : 𝕜) := by
    suffices ∀ n ∈ Submodule.span ℤ (P.coroot '' b.support),
        (P.toLinearMap m₂ n : 𝕜) = r * (P.toLinearMap m₁ n : 𝕜) from
      this _ (b.coroot_mem_span_int j)
    intro n hn
    induction hn using Submodule.span_induction with
    | mem n hn =>
      obtain ⟨i, hi, rfl⟩ := hn
      exact hsimple i hi
    | zero => simp
    | add n n' _ _ ih ih' =>
      simp only [map_add, Int.cast_add, ih, ih', mul_add]
    | smul z n _ ih =>
      simp only [map_zsmul, zsmul_eq_mul, Int.cast_mul, ih]
      ring
  have hnorm (m : M) (hm : m ∈ MulAction.orbit P.weylGroup lam) :
      ∑ j : ι, (P.coroot' j m : 𝕜) ^ 2 = ∑ j : ι, (P.coroot' j lam : 𝕜) ^ 2 := by
    obtain ⟨w, rfl⟩ := hm
    rw [← (P.weylGroupToPerm w).sum_comp]
    simp only [P.coroot'_weylGroupToPerm_smul]
  have hsum : ∑ j : ι, (P.coroot' j m₁ : 𝕜) ^ 2 =
      r ^ 2 * ∑ j : ι, (P.coroot' j m₁ : 𝕜) ^ 2 := by
    calc
      ∑ j : ι, (P.coroot' j m₁ : 𝕜) ^ 2 = ∑ j : ι, (P.coroot' j m₂ : 𝕜) ^ 2 :=
        (hnorm m₁ hm₁).trans (hnorm m₂ hm₂).symm
      _ = ∑ j : ι, (r * (P.coroot' j m₁ : 𝕜)) ^ 2 := by simp only [hall]
      _ = r ^ 2 * ∑ j : ι, (P.coroot' j m₁ : 𝕜) ^ 2 := by simp [mul_pow, Finset.mul_sum]
  refine P.eq_of_mem_orbit_weylGroup_of_forall_coroot'_eq b hm₁ hm₂ fun i _ ↦ ?_
  by_cases hS : ∑ j : ι, (P.coroot' j m₁ : 𝕜) ^ 2 = 0
  · have h0 : ∀ j ∈ (Finset.univ : Finset ι), (P.coroot' j m₁ : 𝕜) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp hS
    have hi₁ : (P.coroot' i m₁ : 𝕜) = 0 := sq_eq_zero_iff.mp (h0 i (Finset.mem_univ i))
    have hi₂ : (P.coroot' i m₂ : 𝕜) = 0 := by rw [hall i, hi₁, mul_zero]
    exact Int.cast_injective (α := 𝕜) (hi₁.trans hi₂.symm)
  · have hr2 : r ^ 2 = 1 := mul_right_cancel₀ hS (by simpa [one_mul] using hsum.symm)
    have hr1 : r = 1 := by nlinarith
    exact Int.cast_injective (α := 𝕜) (by simpa [hr1] using (hall i).symm)

/-- When linear forms on `V` induce the simple coroots of a base `b`, `f` is injective on every
Weyl orbit `W λ`, even if `f` is not injective on central weights. -/
theorem injOn_orbit_weylGroup_of_coroot' [Finite ι] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {P : RootPairing ι ℤ M N} (b : P.Base) {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (m : M), F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    Set.InjOn f (MulAction.orbit P.weylGroup lam) :=
  fun _ hm₁ _ hm₂ hfeq ↦
    eq_of_sameRay_apply_of_mem_orbit_weylGroup b hF hm₁ hm₂ (hfeq ▸ SameRay.rfl)

/-- Spelling of `RootPairing.injOn_orbit_weylGroup_of_coroot'` with `Set.range (· • lam)`. -/
theorem injOn_range_smul_of_coroot' [Finite ι] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {P : RootPairing ι ℤ M N} (b : P.Base) {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (m : M), F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam) :=
  injOn_orbit_weylGroup_of_coroot' b hF lam

/-- **No two distinct vectors in the realized Weyl orbit `f (W λ)` lie on a common ray** whenever
linear forms on `V` induce the simple coroots of a base `b`. -/
theorem pairwise_not_sameRay_image_orbit_weylGroup_of_coroot' [Finite ι] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {P : RootPairing ι ℤ M N} (b : P.Base)
    {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (m : M), F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    (f '' MulAction.orbit P.weylGroup lam).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v := by
  rintro _ ⟨m₁, hm₁, rfl⟩ _ ⟨m₂, hm₂, rfl⟩ hne hray
  exact hne (congrArg f (eq_of_sameRay_apply_of_mem_orbit_weylGroup b hF hm₁ hm₂ hray))

/-- Spelling of `RootPairing.pairwise_not_sameRay_image_orbit_weylGroup_of_coroot'` for
`Set.range (fun w ↦ f (w • lam))`. -/
theorem pairwise_not_sameRay_range_smul_of_coroot' [Finite ι] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {P : RootPairing ι ℤ M N} (b : P.Base)
    {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (m : M), F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v := by
  rintro _ ⟨w₁, rfl⟩ _ ⟨w₂, rfl⟩ hne hray
  exact pairwise_not_sameRay_image_orbit_weylGroup_of_coroot' b hF lam
    ⟨_, ⟨w₁, rfl⟩, rfl⟩ ⟨_, ⟨w₂, rfl⟩, rfl⟩ hne hray

end Realization

end RootPairing
