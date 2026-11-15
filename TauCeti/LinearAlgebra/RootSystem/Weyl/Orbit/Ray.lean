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

Facts about the Weyl orbit `W λ` of a weight `λ` of a root pairing and its additive realizations in
vector spaces over fields. When the Weyl group is finite, no two distinct weights of `W λ` lie in
the same ray, so a vector in `W λ` is determined by its direction. Adding a weight `χ` fixed by the
Weyl group maps `W λ` into `W (λ + χ)`, since `w λ + χ = w (λ + χ)`.

These are the hypotheses under which a path with velocities in `W λ` has a unique distinguished
presentation, and its central shift by `χ` has velocities in `W (λ + χ)`; see
`TauCeti/RepresentationTheory/LSPath/Distinguished.lean`.

Each Weyl orbit is stable under root reflections. For a root pairing over `ℤ`, an additive map
`f` from the weight lattice to a vector space carries
the reflection `s_i` in the root `αᵢ` to the reflection in `f αᵢ` along a linear form agreeing
with the coroot `αᵢ^∨`, so the image `f (W λ)` is stable under the latter. This is the hypothesis
under which the root operators preserve paths with velocities in `f (W λ)`; see
`TauCeti/RepresentationTheory/LSPath/OrbitStable.lean`. When `P` is finite and linear forms on `V`
agree with all simple coroots of a base on `f (M)`, `f` is automatically injective on `W λ` and no
two distinct vectors in `f (W λ)` lie in the same ray over a linearly ordered field, even without
injectivity of `f` on central weights.

## Main results

* `RootPairing.pairwise_not_sameRay_orbit_weylGroup`: when the Weyl group is finite, no two
  distinct weights of a Weyl orbit lie in the same ray.
* `RootPairing.mapsTo_add_orbit_weylGroup`: adding a Weyl-invariant weight `χ` maps `W λ` into
  `W (λ + χ)`.
* `RootPairing.weylGroup_smul_sub_mem_rootSpan`: `w • λ - λ` lies in the root span.
* `RootPairing.mapsTo_preReflection_image_orbit_weylGroup`: the image `f (W λ)` of a Weyl orbit
  in a vector space is stable under the reflection in an image root `f αᵢ`, along a linear form
  agreeing with the coroot `αᵢ^∨`.
* `RootPairing.injOn_orbit_weylGroup_of_apply_eq_coroot'` and
  `RootPairing.pairwise_not_sameRay_image_orbit_weylGroup`: simple-coroot-compatible forms force
  `f` to separate `W λ` and prevent distinct vectors in `f (W λ)` from lying on a common ray.
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

/-- Acting by a Weyl-group element changes any weight by an element of the root span. -/
theorem weylGroup_smul_sub_mem_rootSpan (w : P.weylGroup) (lam : V) :
    w • lam - lam ∈ P.rootSpan R := by
  obtain ⟨g, hg⟩ := w
  rw [Subgroup.mk_smul]
  induction hg using weylGroup.induction generalizing lam with
  | mem i =>
    rw [Equiv.reflection_smul, reflection_apply, sub_sub_cancel_left]
    exact neg_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  | one => simp
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    rw [mul_smul, show g₁ • g₂ • lam - lam = (g₁ • (g₂ • lam) - g₂ • lam) + (g₂ • lam - lam) by
      abel]
    exact add_mem (ih₁ (g₂ • lam)) (ih₂ lam)

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

/-- If linear forms on a characteristic-zero vector space agree with all simple coroots of a base
along `f`, then `f` is injective on every Weyl orbit, even when `f` kills central weights. -/
theorem injOn_orbit_weylGroup_of_apply_eq_coroot' [Finite ι] [CharZero 𝕜] (b : P.Base)
    {F : b.support → Module.Dual 𝕜 V} (hF : ∀ i m, F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    Set.InjOn f (MulAction.orbit P.weylGroup lam) := by
  rintro _ ⟨w₁, rfl⟩ _ ⟨w₂, rfl⟩ h
  have hmem : w₁ • lam - w₂ • lam ∈ P.rootSpan ℤ := by
    rw [show w₁ • lam - w₂ • lam = (w₁ • lam - lam) - (w₂ • lam - lam) by abel]
    exact sub_mem (P.weylGroup_smul_sub_mem_rootSpan w₁ lam)
      (P.weylGroup_smul_sub_mem_rootSpan w₂ lam)
  have hcor : ∀ i ∈ b.support, P.coroot' i (w₁ • lam - w₂ • lam) = 0 := by
    intro i hi
    have hFi : F ⟨i, hi⟩ (f (w₁ • lam - w₂ • lam)) = 0 := by rw [map_sub, h, sub_self, map_zero]
    rw [hF ⟨i, hi⟩] at hFi
    exact Int.cast_eq_zero.mp hFi
  exact sub_eq_zero.mp (P.eq_zero_of_mem_rootSpan_of_forall_coroot'_eq_zero hmem
    (P.coroot'_eq_zero_of_forall_mem_support b hcor))

/-- Over a linearly ordered field, if linear forms on `V` agree with all simple coroots of a base
along `f`, then no two distinct vectors in the realized Weyl orbit `f (W λ)` lie in the same ray. -/
theorem pairwise_not_sameRay_image_orbit_weylGroup [Finite ι] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] (b : P.Base) {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ i m, F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    (f '' MulAction.orbit P.weylGroup lam).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v := by
  cases nonempty_fintype ι
  rintro _ ⟨_, ⟨w₁, rfl⟩, rfl⟩ _ ⟨_, ⟨w₂, rfl⟩, rfl⟩ huv hray
  dsimp only at huv hray ⊢
  apply huv
  -- If all simple coroots vanish on `w₁ • lam`, the Weyl group fixes it, so the two images agree.
  by_cases hzero : ∀ i : b.support, P.coroot' i (w₁ • lam) = 0
  · have hfix := TauCeti.smul_eq_self_of_forall_coroot'_eq_zero b (fun i hi ↦ hzero ⟨i, hi⟩)
    rw [show w₂ • lam = (w₂ * w₁⁻¹) • (w₁ • lam) by simp [mul_smul], hfix]
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hzero
  -- Symmetrically, if `f (w₂ • lam) = 0`, all simple coroots vanish on `w₂ • lam`.
  by_cases hv0 : f (w₂ • lam) = 0
  · have hzero₂ : ∀ i ∈ b.support, P.coroot' i (w₂ • lam) = 0 := fun i hi ↦
      Int.cast_eq_zero.mp (by rw [← hF ⟨i, hi⟩, hv0, map_zero])
    have hfix := TauCeti.smul_eq_self_of_forall_coroot'_eq_zero b hzero₂
    rw [show w₁ • lam = (w₁ * w₂⁻¹) • (w₂ • lam) by simp [mul_smul], hfix]
  have hu0 : f (w₁ • lam) ≠ 0 := fun hu0 ↦ hi₀ <|
    Int.cast_eq_zero.mp (by rw [← hF i₀, hu0, map_zero])
  -- Otherwise `f (w₂ • lam)` is a positive scalar multiple of `f (w₁ • lam)`.
  obtain ⟨r₁, r₂, hr₁, hr₂, hrel⟩ := hray.exists_pos hu0 hv0
  set r : 𝕜 := r₁ / r₂ with hr_def
  have hrpos : 0 < r := div_pos hr₁ hr₂
  have hrv : f (w₂ • lam) = r • f (w₁ • lam) := by
    rw [hr_def, div_eq_inv_mul, mul_smul, hrel, inv_smul_smul₀ hr₂.ne']
  have hscale (i : b.support) :
      (P.coroot' i (w₂ • lam) : 𝕜) = r * (P.coroot' i (w₁ • lam) : 𝕜) := by
    rw [← hF i, hrv, map_smul, smul_eq_mul, hF i]
  -- Cross-multiplying with `i₀` extends proportionality from simple coroots to all coroots.
  set a : ℤ := P.coroot' i₀ (w₁ • lam) with ha_def
  set c : ℤ := P.coroot' i₀ (w₂ • lam) with hc_def
  have hprop_supp : ∀ i ∈ b.support,
      P.coroot' i (a • (w₂ • lam) - c • (w₁ • lam)) = 0 := by
    intro i hi
    apply Int.cast_eq_zero (α := 𝕜).mp
    have hi_scale := hscale ⟨i, hi⟩
    have hi₀_scale : (c : 𝕜) = r * a := hscale i₀
    simp only [map_sub, map_zsmul, smul_eq_mul, Int.cast_sub, Int.cast_mul]
    rw [hi_scale, hi₀_scale]
    ring
  have hprop (j : ι) : a * P.coroot' j (w₂ • lam) = c * P.coroot' j (w₁ • lam) := by
    have hj := P.coroot'_eq_zero_of_forall_mem_support b hprop_supp j
    simp only [map_sub, map_zsmul, smul_eq_mul] at hj
    exact sub_eq_zero.mp hj
  -- Weyl invariance of the sum of squared coroot pairings forces `a = c`, hence `r = 1`.
  have hsum_inv (w : P.weylGroup) :
      ∑ j : ι, P.coroot' j (w • lam) ^ 2 = ∑ j : ι, P.coroot' j lam ^ 2 := by
    rw [← (P.weylGroupToPerm w).sum_comp]
    exact Finset.sum_congr rfl fun j _ ↦ congrArg (· ^ 2) (P.coroot'_weylGroupToPerm_smul w j lam)
  set S : ℤ := ∑ j : ι, P.coroot' j (w₁ • lam) ^ 2
  have hS_eq : ∑ j : ι, P.coroot' j (w₂ • lam) ^ 2 = S := by
    simp only [S, hsum_inv]
  have hS_pos : 0 < S :=
    Finset.sum_pos' (fun j _ ↦ sq_nonneg _) ⟨i₀.1, Finset.mem_univ _, sq_pos_of_ne_zero hi₀⟩
  have hsq : a ^ 2 * S = c ^ 2 * S := by
    calc
      a ^ 2 * S = ∑ j : ι, (a * P.coroot' j (w₂ • lam)) ^ 2 := by
        rw [← hS_eq, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = ∑ j : ι, (c * P.coroot' j (w₁ • lam)) ^ 2 :=
        Finset.sum_congr rfl fun j _ ↦ by rw [hprop j]
      _ = c ^ 2 * S := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hac_sq : a ^ 2 = c ^ 2 := mul_right_cancel₀ hS_pos.ne' hsq
  have hac_pos : 0 < (a : 𝕜) * c := by
    rw [hc_def, hscale i₀, ← ha_def]
    nlinarith [sq_pos_of_ne_zero (Int.cast_ne_zero (α := 𝕜).mpr hi₀)]
  have hac : a = c := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hac_sq with h | h
    · exact h
    · exfalso
      rw [h, Int.cast_neg, neg_mul] at hac_pos
      nlinarith [sq_nonneg (c : 𝕜)]
  have hr1 : r = 1 := by
    have hca : (c : 𝕜) = r * a := hscale i₀
    rw [← hac] at hca
    exact mul_right_cancel₀ (Int.cast_ne_zero.mpr hi₀) (by linarith)
  rw [hrv, hr1, one_smul]

end Realization

end RootPairing
