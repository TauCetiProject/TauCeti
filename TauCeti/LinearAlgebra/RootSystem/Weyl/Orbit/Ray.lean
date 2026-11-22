/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import TauCeti.LinearAlgebra.Ray
public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections
import TauCeti.LinearAlgebra.RootSystem.Inversions.Length

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
`TauCeti/RepresentationTheory/LSPath/OrbitStable.lean`.

If such forms are given for all simple roots of a base, every element of the Weyl group acts on
`f (M)` through a linear automorphism of the vector space, a product of these reflections. So
`f (W λ)` is a finite orbit of a group of linear automorphisms, and again no two of its distinct
points lie in the same ray, whether or not `f` is injective.

## Main results

* `RootPairing.pairwise_not_sameRay_orbit_weylGroup`: when the Weyl group is finite, no two
  distinct weights of a Weyl orbit lie in the same ray.
* `RootPairing.mapsTo_add_orbit_weylGroup`: adding a Weyl-invariant weight `χ` maps `W λ` into
  `W (λ + χ)`.
* `RootPairing.mapsTo_preReflection_image_orbit_weylGroup`: the image `f (W λ)` of a Weyl orbit
  in a vector space is stable under the reflection in an image root `f αᵢ`, along a linear form
  agreeing with the coroot `αᵢ^∨`.
* `RootPairing.exists_linearEquiv_apply_eq_smul`: given such forms for the simple roots of a
  base, every Weyl-group element acts on `f (M)` through a linear automorphism.
* `RootPairing.pairwise_not_sameRay_image_orbit_weylGroup`: given such forms for the simple roots
  of a base, no two distinct points of the image `f (W λ)` lie in the same ray.
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

variable [Finite ι] [P.IsReduced] (b : P.Base) {F : b.support → Module.Dual 𝕜 V}

/-- Given linear forms `F i` agreeing with the simple coroots on the weight lattice, every element
`w` of the Weyl group acts on `f (M)` through a linear automorphism of `V`: a product of the
reflections in the image simple roots `f αᵢ` along the forms `F i`. -/
theorem exists_linearEquiv_apply_eq_smul
    (hF : ∀ (i : b.support) (m : M), F i (f m) = (P.coroot' i m : 𝕜)) (w : P.weylGroup) :
    ∃ R : V ≃ₗ[𝕜] V, ∀ m, R (f m) = f (w • m) := by
  obtain ⟨l, rfl⟩ := TauCeti.exists_wordProd_eq P b w
  induction l with
  | nil => exact ⟨LinearEquiv.refl 𝕜 V, fun m ↦ by simp⟩
  | cons i l ih =>
    obtain ⟨R, hR⟩ := ih
    have h2 : F i (f (P.root i)) = 2 := by
      rw [hF, P.root_coroot'_eq_pairing, P.pairing_same, Int.cast_ofNat]
    refine ⟨R.trans (Module.reflection h2), fun m ↦ ?_⟩
    rw [LinearEquiv.trans_apply, hR, Module.reflection_apply, TauCeti.wordProd_cons, mul_smul,
      weylGroup.ofIdx_smul, Equiv.reflection_smul, P.map_reflection_eq_preReflection i (hF i),
      Module.preReflection_apply]

/-- **No two distinct points of a realized Weyl orbit lie in the same ray.** Given linear forms
`F i` agreeing with the simple coroots on the weight lattice, the image `f (W λ)` of a Weyl orbit
is a finite orbit of the group of linear automorphisms of `V` that act on `f (M)` through the Weyl
group. The map `f` need not be injective. -/
theorem pairwise_not_sameRay_image_orbit_weylGroup [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (hF : ∀ (i : b.support) (m : M), F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    (f '' MulAction.orbit P.weylGroup lam).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v := by
  -- The linear automorphisms of `V` acting on `f (M)` through some element of the Weyl group.
  let G : Subgroup (V ≃ₗ[𝕜] V) :=
    { carrier := {R | ∃ w : P.weylGroup, ∀ m, R (f m) = f (w • m)}
      mul_mem' := by
        rintro R R' ⟨w, hw⟩ ⟨w', hw'⟩
        exact ⟨w * w', fun m ↦ by rw [mul_apply_eq_comp, hw', hw, mul_smul]⟩
      one_mem' := ⟨1, fun m ↦ by simp⟩
      inv_mem' := by
        rintro R ⟨w, hw⟩
        refine ⟨w⁻¹, fun m ↦ ?_⟩
        rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq, hw, smul_inv_smul] }
  have horbit : MulAction.orbit G (f lam) = f '' MulAction.orbit P.weylGroup lam := by
    ext v
    constructor
    · rintro ⟨⟨R, w, hw⟩, rfl⟩
      exact ⟨w • lam, ⟨w, rfl⟩, (hw lam).symm⟩
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      obtain ⟨R, hR⟩ := P.exists_linearEquiv_apply_eq_smul b hF w
      exact ⟨⟨R, w, hR⟩, hR lam⟩
  have := P.finite_weylGroup_of_base b
  have hfin : (MulAction.orbit G (f lam)).Finite :=
    horbit ▸ (Set.finite_range _).image f
  rw [← horbit]
  exact fun u hu v hv huv h ↦ huv (h.eq_of_mem_orbit hu hv hfin)

end Realization

end RootPairing
