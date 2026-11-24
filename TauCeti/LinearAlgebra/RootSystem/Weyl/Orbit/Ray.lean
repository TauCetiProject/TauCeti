/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import TauCeti.LinearAlgebra.Ray
import TauCeti.LinearAlgebra.RootSystem.PairingInvariance
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
`TauCeti/RepresentationTheory/LSPath/OrbitStable.lean`. When `f` admits a compatible family of
simple-coroot forms, it is automatically injective on each Weyl orbit and separates distinct orbit
points by rays.

## Main results

* `RootPairing.pairwise_not_sameRay_orbit_weylGroup`: when the Weyl group is finite, no two
  distinct weights of a Weyl orbit lie in the same ray.
* `RootPairing.mapsTo_add_orbit_weylGroup`: adding a Weyl-invariant weight `χ` maps `W λ` into
  `W (λ + χ)`.
* `RootPairing.mapsTo_preReflection_image_orbit_weylGroup`: the image `f (W λ)` of a Weyl orbit
  in a vector space is stable under the reflection in an image root `f αᵢ`, along a linear form
  agreeing with the coroot `αᵢ^∨`.
* `RootPairing.injOn_orbit_of_compatible`: an additive map from the weight lattice equipped with
  compatible simple-coroot forms is injective on each Weyl orbit.
* `RootPairing.pairwise_not_sameRay_image_orbit_of_compatible`: no two distinct points in the
  image of a Weyl orbit under a compatible realization lie on the same ray.
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

/-- An additive map from the weight lattice that pulls back a family of linear forms to the simple
coroots is injective on every Weyl orbit. -/
theorem injOn_orbit_of_compatible (b : P.Base) [Finite ι] [CharZero 𝕜]
    {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : M), F i (f x) = (P.coroot' i x : 𝕜)) (lam : M) :
    Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam) := by
  rintro _ ⟨w₁, rfl⟩ _ ⟨w₂, rfl⟩ heq
  have hsub : f (w₁ • lam - w₂ • lam) = 0 := by rw [map_sub, heq, sub_self]
  have hzero : ∀ i ∈ b.support, P.coroot' i (w₁ • lam - w₂ • lam) = 0 := fun i hi ↦ by
    apply Int.cast_injective (α := 𝕜)
    rw [← hF ⟨i, hi⟩, hsub, map_zero, Int.cast_zero]
  have hroot : w₁ • lam - w₂ • lam ∈ P.rootSpan ℤ := by
    simpa only [sub_sub_sub_cancel_right] using
      sub_mem (weylGroup.smul_sub_mem_rootSpan w₁ lam) (weylGroup.smul_sub_mem_rootSpan w₂ lam)
  exact sub_eq_zero.mp <| P.eq_zero_of_mem_rootSpan_of_forall_coroot'_eq_zero hroot
    (P.coroot'_eq_zero_of_forall_mem_support b hzero)

/-- In any compatible realization `(𝕜, V, f, F)`, no two distinct points of a realized Weyl orbit
lie on the same ray. -/
theorem pairwise_not_sameRay_image_orbit_of_compatible (b : P.Base) [Finite ι]
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : M), F i (f x) = (P.coroot' i x : 𝕜)) (lam : M) :
    (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v := by
  rintro _ ⟨w₁, rfl⟩ _ ⟨w₂, rfl⟩ hne hray
  -- If every simple coroot kills an orbit point, the Weyl group fixes it, so the orbit is a
  -- singleton, contradicting `hne`.
  have hcollapse {w : P.weylGroup} (hzero : ∀ i ∈ b.support, P.coroot' i (w • lam) = 0) :
      False := by
    have hinv := TauCeti.smul_eq_self_of_forall_coroot'_eq_zero b hzero w⁻¹
    rw [inv_smul_smul] at hinv
    have hfix (u : P.weylGroup) : u • lam = w • lam :=
      (TauCeti.smul_eq_self_of_forall_coroot'_eq_zero b (fun i hi ↦ hinv ▸ hzero i hi) u).trans
        hinv
    exact hne (congrArg f ((hfix w₁).trans (hfix w₂).symm))
  have hw_ne_zero (w : P.weylGroup) : f (w • lam) ≠ 0 := fun h0 ↦
    hcollapse fun i hi ↦ Int.cast_injective (α := 𝕜) (by
      rw [← hF ⟨i, hi⟩, h0, map_zero, Int.cast_zero])
  obtain ⟨r₁, r₂, hr₁, hr₂, hsmul⟩ := hray.exists_pos (hw_ne_zero w₁) (hw_ne_zero w₂)
  have hcoroot : ∀ j : ι,
      r₁ * (P.coroot' j (w₁ • lam) : 𝕜) = r₂ * (P.coroot' j (w₂ • lam) : 𝕜) := by
    simpa only [eq_intCast] using
      P.mul_coroot'_eq_of_forall_mem_support b (𝕜 := 𝕜) fun i hi ↦ by
        simpa only [eq_intCast, map_smul, smul_eq_mul, hF ⟨i, hi⟩] using congrArg (F ⟨i, hi⟩) hsmul
  let := Fintype.ofFinite ι
  have hS : r₁ ^ 2 * ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2 =
      r₂ ^ 2 * ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2 := by
    calc r₁ ^ 2 * ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2
        = ∑ j : ι, (r₁ * (P.coroot' j (w₁ • lam) : 𝕜)) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = ∑ j : ι, (r₂ * (P.coroot' j (w₂ • lam) : 𝕜)) ^ 2 :=
          Finset.sum_congr rfl fun j _ ↦ congrArg (· ^ 2) (hcoroot j)
      _ = r₂ ^ 2 * ∑ j : ι, (P.coroot' j (w₂ • lam) : 𝕜) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = r₂ ^ 2 * ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2 := by
          simpa only [eq_intCast] using
            congrArg (r₂ ^ 2 * ·)
              ((P.sum_coroot'_sq_smul (𝕜 := 𝕜) w₂ lam).trans
                (P.sum_coroot'_sq_smul (𝕜 := 𝕜) w₁ lam).symm)
  by_cases hsum0 : ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2 = 0
  · rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg _] at hsum0
    exact hcollapse fun i _ ↦ Int.cast_eq_zero.mp (sq_eq_zero_iff.mp (hsum0 i (Finset.mem_univ i)))
  · have hr : r₁ = r₂ := (sq_eq_sq₀ hr₁.le hr₂.le).mp (mul_right_cancel₀ hsum0 hS)
    rw [hr] at hsmul
    exact hne (smul_right_injective V hr₂.ne' hsmul)

end Realization

end RootPairing
