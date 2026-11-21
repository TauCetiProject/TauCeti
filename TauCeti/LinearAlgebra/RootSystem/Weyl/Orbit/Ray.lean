/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import TauCeti.LinearAlgebra.Ray
import TauCeti.LinearAlgebra.RootSystem.SimpleReflections

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

## Main results

* `RootPairing.pairwise_not_sameRay_orbit_weylGroup`: when the Weyl group is finite, no two
  distinct weights of a Weyl orbit lie in the same ray.
* `RootPairing.mapsTo_add_orbit_weylGroup`: adding a Weyl-invariant weight `χ` maps `W λ` into
  `W (λ + χ)`.
* `RootPairing.mapsTo_preReflection_image_orbit_weylGroup`: the image `f (W λ)` of a Weyl orbit
  in a vector space is stable under the reflection in an image root `f αᵢ`, along a linear form
  agreeing with the coroot `αᵢ^∨`.
* `RootPairing.pairwise_not_sameRay_image_orbit_weylGroup_of_closure_eq_top`,
  `RootPairing.pairwise_not_sameRay_image_orbit_weylGroup`, and
  `RootPairing.pairwise_not_sameRay_image_orbit_weylGroup_of_base`: when the Weyl group is finite
  and generating root reflections are realized by linear forms agreeing with their coroots, no two
  distinct points of a realized Weyl orbit `f (W λ)` lie in the same ray.
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
`αᵢ^∨`. -/
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

/-- If `s` generates `W` and each `s_i` (`i ∈ s`) acts via `F i` agreeing with `αᵢ^∨`, no two
distinct points of `f (W λ)` lie in the same ray when `W` is finite. -/
theorem pairwise_not_sameRay_image_orbit_weylGroup_of_closure_eq_top
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Finite P.weylGroup] {s : Set ι}
    (hs : Subgroup.closure (weylGroup.ofIdx P '' s) = ⊤) {F : s → Module.Dual 𝕜 V}
    (hF : ∀ (i : s) m, F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    (f '' MulAction.orbit P.weylGroup lam).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v := by
  have htwo (i : s) : F i (f (P.root i)) = 2 := by
    simpa only [P.root_coroot'_eq_pairing, P.pairing_same, Int.cast_ofNat] using hF i (P.root i)
  let r (i : s) : V ≃ₗ[𝕜] V := Module.reflection (htwo i)
  let H : Subgroup (P.weylGroup × (V ≃ₗ[𝕜] V)) :=
    Subgroup.closure (Set.range fun i : s ↦ (weylGroup.ofIdx P i, r i))
  let G : Subgroup (V ≃ₗ[𝕜] V) := H.map (MonoidHom.snd P.weylGroup (V ≃ₗ[𝕜] V))
  have hH_intertwine {wg : P.weylGroup × (V ≃ₗ[𝕜] V)} (hwg : wg ∈ H) (m : M) :
      wg.2 • f m = f (wg.1 • m) := by
    induction hwg using Subgroup.closure_induction generalizing m with
    | mem _ hx =>
      rcases hx with ⟨i, rfl⟩
      rw [weylGroup.ofIdx_smul, Equiv.reflection_smul, P.map_reflection_eq_preReflection i (hF i)]
      rfl
    | one => simp
    | mul _ _ _ _ ih₁ ih₂ => simp only [Prod.snd_mul, Prod.fst_mul, mul_smul, ih₂, ih₁]
    | inv _ _ ih =>
      simp only [Prod.snd_inv, Prod.fst_inv]
      rw [inv_smul_eq_iff, ih, smul_inv_smul]
  have hfst : H.map (MonoidHom.fst P.weylGroup (V ≃ₗ[𝕜] V)) = ⊤ := by
    rw [MonoidHom.map_closure, ← hs]
    congr 1
    ext w
    simp
  have horbit : f '' MulAction.orbit P.weylGroup lam = MulAction.orbit G (f lam) := by
    ext v
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      obtain ⟨⟨w', g⟩, hwg, hww'⟩ := Subgroup.mem_map.mp (hfst ▸ Subgroup.mem_top w)
      obtain rfl : w' = w := hww'
      exact ⟨⟨g, ⟨(w', g), hwg, rfl⟩⟩, hH_intertwine hwg lam⟩
    · rintro ⟨⟨g, wg, hwg, hgg'⟩, rfl⟩
      exact ⟨wg.1 • lam, ⟨wg.1, rfl⟩, hgg' ▸ (hH_intertwine hwg lam).symm⟩
  have hfin : (MulAction.orbit G (f lam)).Finite := horbit ▸ (Set.finite_range _).image f
  rw [horbit]
  exact fun _ hu _ hv huv h ↦ huv (h.eq_of_mem_orbit hu hv hfin)

/-- When `W` is finite and every root reflection is realized along a linear form agreeing with its
coroot, no two distinct points of `f (W λ)` lie in the same ray. -/
theorem pairwise_not_sameRay_image_orbit_weylGroup
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Finite P.weylGroup] {F : ι → Module.Dual 𝕜 V}
    (hF : ∀ i m, F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    (f '' MulAction.orbit P.weylGroup lam).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v := by
  refine P.pairwise_not_sameRay_image_orbit_weylGroup_of_closure_eq_top (s := Set.univ)
    (eq_top_iff.mpr ?_) (F := fun i ↦ F i) (fun i m ↦ hF i m) lam
  rintro ⟨w, hw⟩ -
  induction hw using weylGroup.induction with
  | mem i => exact Subgroup.subset_closure ⟨i, trivial, rfl⟩
  | one => exact one_mem _
  | mul x y hx hy ihx ihy => exact Submonoid.mk_mul_mk _ x y hx hy ▸ mul_mem ihx ihy

/-- When `W` is finite and the simple root reflections of a base `b` are realized along linear
forms agreeing with the simple coroots, no two distinct points of `f (W λ)` lie in the same ray. -/
theorem pairwise_not_sameRay_image_orbit_weylGroup_of_base
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Finite ι] [P.IsReduced] [Finite P.weylGroup]
    (b : P.Base) {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) m, F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    (f '' MulAction.orbit P.weylGroup lam).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v := by
  refine P.pairwise_not_sameRay_image_orbit_weylGroup_of_closure_eq_top (s := (b.support : Set ι))
    ?_ hF lam
  convert (TauCeti.weylGroup_eq_closure_simple P b).symm
  ext w
  simp

end Realization

end RootPairing
