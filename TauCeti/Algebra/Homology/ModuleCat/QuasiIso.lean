/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Homology.GradedCochainComplex

/-!
# Quasi-isomorphisms of complexes of modules, on elements

A chain map `φ : K ⟶ L` of complexes of modules is a quasi-isomorphism in degree `n` exactly when
every degree-`n` cycle of `L` is the image of a cycle of `K` up to a boundary, and every degree-`n`
cycle of `K` whose image is a boundary is itself a boundary
(`HomologicalComplex.moduleCat_quasiIsoAt_iff`). These are surjectivity and injectivity of the
induced map on homology, written on representatives.

For the cochain complexes `TauCeti.gradedCochainComplex` assembled from graded modules, the two
conditions in all degrees combine into one statement about homogeneous elements
(`TauCeti.quasiIso_gradedCochainComplexHom_iff`): every relative cycle `(x, y)`, with `dM x = 0`
and `f x = dN y`, is a relative boundary `(dM u, f u + dN v)`. This is the acyclicity of the
mapping cone of `f`, written without constructing the cone, and it is the form in which a
quasi-isomorphism can be propagated along a filtration one generator degree at a time.

## Main results

* `HomologicalComplex.moduleCat_quasiIsoAt_iff`: quasi-isomorphisms in one degree, on elements.
* `TauCeti.quasiIso_gradedCochainComplexHom_iff`: quasi-isomorphisms of graded cochain complexes
  are the maps whose relative cycles are relative boundaries.
-/

public section

open CategoryTheory

namespace HomologicalComplex

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat R) c}

/-- **Quasi-isomorphisms of complexes of modules, on elements.** A chain map `φ` of complexes of
modules is a quasi-isomorphism in degree `n` exactly when every degree-`n` cycle `y` of `L` is
`φ x + d b` for a cycle `x` of `K`, and every degree-`n` cycle `x` of `K` whose image `φ x` is a
boundary is itself a boundary. Here `p = c.prev n` and `m = c.next n`. -/
theorem moduleCat_quasiIsoAt_iff (φ : K ⟶ L) {n p m : ι} (hp : c.prev n = p)
    (hm : c.next n = m) :
    QuasiIsoAt φ n ↔
      (∀ y : L.X n, L.d n m y = 0 →
        ∃ x : K.X n, K.d n m x = 0 ∧ ∃ b : L.X p, L.d p n b = y - φ.f n x) ∧
      (∀ x : K.X n, K.d n m x = 0 → ∀ b : L.X p, L.d p n b = φ.f n x →
        ∃ a : K.X p, K.d p n a = x) := by
  -- A cycle has zero homology class exactly when it is a boundary, on underlying elements.
  have hzero {M : HomologicalComplex (ModuleCat R) c} (x : M.X n) (hx : M.d n m x = 0) :
      M.homologyπ n (M.moduleCatCyclesMk x m hm hx) = 0 ↔ ∃ b : M.X p, M.d p n b = x := by
    rw [M.moduleCat_homologyπ_eq_zero_iff hp]
    refine exists_congr fun b ↦ ?_
    rw [← (M.moduleCat_iCycles_injective n).eq_iff, iCycles_moduleCatCyclesMk,
      moduleCat_iCycles_toCycles_apply]
  have hmap (x : K.X n) (hx : K.d n m x = 0) :
      homologyMap φ n (K.homologyπ n (K.moduleCatCyclesMk x m hm hx)) =
        L.homologyπ n (L.moduleCatCyclesMk (φ.f n x) m hm
          (by rw [Hom.comm_apply, hx, map_zero])) :=
    homologyMap_homologyπ_moduleCatCyclesMk φ x m hm hx
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun y hy ↦ ?_, fun x hx b hb ↦ ?_⟩
    · obtain ⟨z, hz⟩ := hsurj (L.homologyπ n (L.moduleCatCyclesMk y m hm hy))
      obtain ⟨x, hx, rfl⟩ := K.exists_homologyπ_moduleCatCyclesMk_eq m hm z
      have hyx : L.d n m (y - φ.f n x) = 0 := by
        rw [map_sub, hy, Hom.comm_apply, hx, map_zero, sub_zero]
      refine ⟨x, hx, (hzero _ hyx).1 ?_⟩
      have hsub : L.moduleCatCyclesMk (y - φ.f n x) m hm hyx =
          L.moduleCatCyclesMk y m hm hy - L.moduleCatCyclesMk (φ.f n x) m hm
            (by rw [Hom.comm_apply, hx, map_zero]) :=
        L.moduleCat_iCycles_injective n (by simp only [map_sub, iCycles_moduleCatCyclesMk])
      rw [hsub, map_sub, ← hmap x hx, hz, sub_self]
    · exact (hzero x hx).1 (hinj ((hmap x hx).trans
        (((hzero _ _).2 ⟨b, hb⟩).trans (map_zero _).symm)))
  · rintro ⟨hsurj, hinj⟩
    refine ⟨(injective_iff_map_eq_zero (homologyMap φ n).hom).2 fun z hz ↦ ?_, fun z ↦ ?_⟩
    · obtain ⟨x, hx, rfl⟩ := K.exists_homologyπ_moduleCatCyclesMk_eq m hm z
      have hz' : homologyMap φ n (K.homologyπ n (K.moduleCatCyclesMk x m hm hx)) = 0 := hz
      rw [hmap, hzero] at hz'
      obtain ⟨b, hb⟩ := hz'
      exact (hzero x hx).2 (hinj x hx b hb)
    · obtain ⟨y, hy, rfl⟩ := L.exists_homologyπ_moduleCatCyclesMk_eq m hm z
      obtain ⟨x, hx, b, hb⟩ := hsurj y hy
      refine ⟨K.homologyπ n (K.moduleCatCyclesMk x m hm hx), ?_⟩
      rw [hmap]
      exact L.moduleCat_homologyπ_eq_of_iCycles_sub_eq_d (-b) (by
        rw [iCycles_moduleCatCyclesMk, iCycles_moduleCatCyclesMk, map_neg, hb, neg_sub])

end HomologicalComplex

namespace TauCeti

universe uR uM

variable {R : Type uR} {M N : Type uM} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  {ℳ : ℤ → Submodule R M} {dM : M →ₗ[R] M}
  {hdeg : LinearMap.IsHomogeneous dM ℳ ℳ 1} {hsq : ∀ p (x : ℳ p), dM (dM x) = 0}
  {𝒩 : ℤ → Submodule R N} {dN : N →ₗ[R] N}
  {hdegN : LinearMap.IsHomogeneous dN 𝒩 𝒩 1} {hsqN : ∀ p (x : 𝒩 p), dN (dN x) = 0}

/-- **Quasi-isomorphisms of graded cochain complexes, on homogeneous elements.** The cochain map
induced by a degree-preserving map `f` commuting with the differentials is a quasi-isomorphism
exactly when every relative cycle is a relative boundary: whenever `x ∈ ℳ (n + 1)` and
`y ∈ 𝒩 n` satisfy `dM x = 0` and `f x = dN y`, there are `u ∈ ℳ n` and `v ∈ 𝒩 (n - 1)` with
`dM u = x` and `f u + dN v = y`. This is the acyclicity of the mapping cone of `f`. -/
theorem quasiIso_gradedCochainComplexHom_iff (f : M →ₗ[R] N)
    (hf : LinearMap.IsHomogeneous f ℳ 𝒩 0) (hcomm : dN ∘ₗ f = f ∘ₗ dM) :
    QuasiIso (gradedCochainComplexHom (hdeg := hdeg) (hsq := hsq) (hdegN := hdegN)
        (hsqN := hsqN) f hf hcomm) ↔
      ∀ n (x : M) (y : N), x ∈ ℳ (n + 1) → y ∈ 𝒩 n → dM x = 0 → f x = dN y →
        ∃ u ∈ ℳ n, ∃ v ∈ 𝒩 (n - 1), dM u = x ∧ f u + dN v = y := by
  set φ := gradedCochainComplexHom (hdeg := hdeg) (hsq := hsq) (hdegN := hdegN)
    (hsqN := hsqN) f hf hcomm
  -- The terms of both complexes are the grading pieces, with differentials `dM`, `dN` and
  -- components `f`, through `gradedCochainComplexXEquiv`.
  have hK {p q : ℤ} (hpq : p + 1 = q) (x : (gradedCochainComplex ℳ dM hdeg hsq).X p) :
      (gradedCochainComplexXEquiv q ((gradedCochainComplex ℳ dM hdeg hsq).d p q x) : M) =
        dM (gradedCochainComplexXEquiv p x) :=
    gradedCochainComplexXEquiv_d_of_add_one_eq hpq x
  have hL {p q : ℤ} (hpq : p + 1 = q) (y : (gradedCochainComplex 𝒩 dN hdegN hsqN).X p) :
      (gradedCochainComplexXEquiv q ((gradedCochainComplex 𝒩 dN hdegN hsqN).d p q y) : N) =
        dN (gradedCochainComplexXEquiv p y) :=
    gradedCochainComplexXEquiv_d_of_add_one_eq hpq y
  have hφ (p : ℤ) (x : (gradedCochainComplex ℳ dM hdeg hsq).X p) :
      (gradedCochainComplexXEquiv p (φ.f p x) : N) = f (gradedCochainComplexXEquiv p x) :=
    gradedCochainComplexXEquiv_gradedCochainComplexHom_f_apply f hf hcomm p x
  have hfd (x : M) : dN (f x) = f (dM x) := LinearMap.congr_fun hcomm x
  have hqi (n : ℤ) := HomologicalComplex.moduleCat_quasiIsoAt_iff φ (CochainComplex.prev ℤ n)
    (CochainComplex.next ℤ n)
  rw [_root_.quasiIso_iff]
  constructor
  · intro hq n x y hx hy hdx hfx
    -- `x` is a cycle whose image is a boundary, hence a boundary `dM u₀`.
    obtain ⟨a, ha⟩ := ((hqi (n + 1)).1 (hq (n + 1))).2
      ((gradedCochainComplexXEquiv (n + 1)).symm ⟨x, hx⟩)
      ((gradedCochainComplexXEquiv (n + 1 + 1)).injective (Subtype.ext (by
        rw [hK (p := n + 1) rfl, LinearEquiv.apply_symm_apply, map_zero]
        exact hdx)))
      ((gradedCochainComplexXEquiv (n + 1 - 1)).symm ⟨y, by rwa [add_sub_cancel_right]⟩)
      ((gradedCochainComplexXEquiv (n + 1)).injective (Subtype.ext (by
        rw [hL (sub_add_cancel (n + 1) 1), hφ, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply]
        exact hfx.symm)))
    set u₀ : M := (gradedCochainComplexXEquiv (n + 1 - 1) a : M)
    have hu₀ : u₀ ∈ ℳ n := by
      simpa only [add_sub_cancel_right] using (gradedCochainComplexXEquiv (n + 1 - 1) a).2
    have hdu₀ : dM u₀ = x := by
      have := congrArg (fun z ↦ (gradedCochainComplexXEquiv (n + 1) z : M)) ha
      simpa only [hK (sub_add_cancel (n + 1) 1), LinearEquiv.apply_symm_apply] using this
    -- `y - f u₀` is a cycle, hence `f c + dN v` for a cycle `c`.
    have hyu : y - f u₀ ∈ 𝒩 n := (𝒩 n).sub_mem hy (by simpa using hf.map_mem hu₀)
    have hcyc : dN (y - f u₀) = 0 := by rw [map_sub, hfd, hdu₀, hfx, sub_self]
    obtain ⟨c, hc, b, hb⟩ := ((hqi n).1 (hq n)).1
      ((gradedCochainComplexXEquiv n).symm ⟨y - f u₀, hyu⟩)
      ((gradedCochainComplexXEquiv (n + 1)).injective (Subtype.ext (by
        rw [hL (p := n) rfl, LinearEquiv.apply_symm_apply, map_zero]
        exact hcyc)))
    have hdc : dM (gradedCochainComplexXEquiv n c) = 0 := by
      have := congrArg (fun z ↦ (gradedCochainComplexXEquiv (n + 1) z : M)) hc
      simpa only [hK (p := n) rfl, map_zero, Submodule.coe_zero] using this
    have hdb : dN (gradedCochainComplexXEquiv (n - 1) b) =
        y - f u₀ - f (gradedCochainComplexXEquiv n c) := by
      have := congrArg (fun z ↦ (gradedCochainComplexXEquiv n z : N)) hb
      simpa only [hL (sub_add_cancel n 1), map_sub, Submodule.coe_sub, hφ,
        LinearEquiv.apply_symm_apply] using this
    refine ⟨u₀ + gradedCochainComplexXEquiv n c, (ℳ n).add_mem hu₀ (SetLike.coe_mem _),
      gradedCochainComplexXEquiv (n - 1) b, SetLike.coe_mem _, ?_, ?_⟩
    · rw [map_add, hdu₀, hdc, add_zero]
    · rw [map_add, hdb]
      abel
  · intro H n
    refine (hqi n).2 ⟨fun y hy ↦ ?_, fun x hx b hb ↦ ?_⟩
    · -- A cycle `y`: the relative cycle `(0, y)` is a relative boundary `(dM u, f u + dN v)`.
      have hdy : dN (gradedCochainComplexXEquiv n y) = 0 := by
        have := congrArg (fun z ↦ (gradedCochainComplexXEquiv (n + 1) z : N)) hy
        simpa only [hL (p := n) rfl, map_zero, Submodule.coe_zero] using this
      obtain ⟨u, hu, v, hv, hdu, huv⟩ := H n 0 (gradedCochainComplexXEquiv n y)
        (zero_mem _) (SetLike.coe_mem _) (map_zero dM) (by rw [map_zero, hdy])
      refine ⟨(gradedCochainComplexXEquiv n).symm ⟨u, hu⟩,
        (gradedCochainComplexXEquiv (n + 1)).injective (Subtype.ext ?_),
        (gradedCochainComplexXEquiv (n - 1)).symm ⟨v, hv⟩,
        (gradedCochainComplexXEquiv n).injective (Subtype.ext ?_)⟩
      · rw [hK (p := n) rfl, LinearEquiv.apply_symm_apply, map_zero]
        exact hdu
      · rw [hL (sub_add_cancel n 1), LinearEquiv.apply_symm_apply, map_sub, Submodule.coe_sub,
          hφ, LinearEquiv.apply_symm_apply, ← huv]
        exact (add_sub_cancel_left _ _).symm
    · -- A cycle `x` with `φ x = d b`: the relative cycle `(x, b)` is a relative boundary.
      have hx' : (gradedCochainComplexXEquiv n x : M) ∈ ℳ (n - 1 + 1) := by
        simpa only [sub_add_cancel] using SetLike.coe_mem (gradedCochainComplexXEquiv n x)
      have hdx : dM (gradedCochainComplexXEquiv n x) = 0 := by
        have := congrArg (fun z ↦ (gradedCochainComplexXEquiv (n + 1) z : M)) hx
        simpa only [hK (p := n) rfl, map_zero, Submodule.coe_zero] using this
      have hfx :
          f (gradedCochainComplexXEquiv n x) = dN (gradedCochainComplexXEquiv (n - 1) b) := by
        have := congrArg (fun z ↦ (gradedCochainComplexXEquiv n z : N)) hb
        simpa only [hL (sub_add_cancel n 1), hφ] using this.symm
      obtain ⟨u, hu, v, -, hdu, -⟩ := H (n - 1) _ _ hx' (SetLike.coe_mem _) hdx hfx
      refine ⟨(gradedCochainComplexXEquiv (n - 1)).symm ⟨u, hu⟩,
        (gradedCochainComplexXEquiv n).injective (Subtype.ext ?_)⟩
      rw [hK (sub_add_cancel n 1), LinearEquiv.apply_symm_apply]
      exact hdu

end TauCeti
