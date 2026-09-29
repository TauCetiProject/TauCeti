/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.MonoidAlgebra.Basic
public import TauCeti.Algebra.MonoidAlgebra.RelationModule.Basic
public import TauCeti.Algebra.Module.ProjectiveCover.Surjection

/-!
# Relation modules of a finite group over a local ring

Let `G` be a finite group and `R` a local ring. A generating family `g : ι → G` indexed by a finite
type gives Lyndon's exact sequence `0 → relationModule R G g → R[G]^ι → I_G → 0`. This file proves
that for two generating families `g` and `g'` indexed by the same type the presentation maps
`R[G]^ι → I_G` differ by an automorphism of `R[G]^ι`, so that the relation module depends, up to
isomorphism, only on the group and the number of generators. For `R = ℤ_p` this is the
independence of `R^ab(p)` from the chosen generators used in the computation of the generator rank
of the absolute Galois group of a `p`-adic field (NSW (5.6.6), (7.4.1)).

Schanuel's lemma alone gives `relationModule R G g × R[G]^ι ≃ relationModule R G g' × R[G]^ι`, and
the free summand would still have to be cancelled. The proof here reduces modulo the maximal ideal
`𝔪` instead. Over the residue field `k` the group algebra `k[G]` is finite-dimensional, hence
Artinian, and the two presentation maps have the same image, so they differ by an automorphism
`θ₀` of `k[G]^ι` (`TauCeti.exists_linearEquiv_comp_eq_of_range_eq`, which rests on projective
covers and Krull–Schmidt cancellation over `k[G]`). Lift the images of the basis vectors under
`θ₀`, and correct the lifts by families reducing to zero — possible because the augmentation ideal
is a direct summand of `R[G]` as an `R`-module — so that the lifted map `θ` still intertwines the
two presentations. It reduces to `θ₀`, so it is onto by Nakayama's lemma over `R`, `R[G]^ι` being
a finitely generated `R`-module, and hence bijective. No completeness of `R` is needed.

## Main results

* `TauCeti.MonoidAlgebra.exists_linearEquiv_linearCombination_comp_eq`: the presentation maps
  `e_i ↦ g_i - 1` and `e_i ↦ g'_i - 1` of two generating families differ by an automorphism.
* `TauCeti.MonoidAlgebra.relationModule_linearEquiv_of_closure`: two generating families of the
  same size have isomorphic relation modules.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition, (5.6.6),
  (5.6.10) and (7.4.1).
* K. W. Gruenberg, *Relation modules of finite groups*, CBMS Regional Conference Series in
  Mathematics 25, American Mathematical Society (1976).
-/

public section

open MonoidAlgebra IsLocalRing

namespace TauCeti.MonoidAlgebra

universe u v w

variable (R : Type u) [CommRing R] [IsLocalRing R] {G : Type v} [Group G] {ι : Type w} [Fintype ι]

variable [Finite G]

omit [Fintype ι] in
/-- **Nakayama's lemma for `R[G]^ι`.** An `R[G]`-linear endomorphism of `R[G]^ι` that is onto
modulo the maximal ideal is bijective. -/
private theorem bijective_of_forall_exists_mapRingHom_residue_eq [Finite ι]
    (θ : (ι → MonoidAlgebra R G) →ₗ[MonoidAlgebra R G] (ι → MonoidAlgebra R G))
    (h : ∀ y : ι → MonoidAlgebra R G, ∃ x, ∀ i,
      mapRingHom G (residue R) (θ x i) = mapRingHom G (residue R) (y i)) :
    Function.Bijective θ := by
  classical
  have := Fintype.ofFinite ι
  -- `R[G]^ι` is a finitely generated `R`-module and `θ` is onto modulo `𝔪 • R[G]^ι`.
  have hle : (⊤ : Submodule R (ι → MonoidAlgebra R G)) ≤
      LinearMap.range (θ.restrictScalars R) ⊔ maximalIdeal R • ⊤ := by
    intro y _
    obtain ⟨x, hx⟩ := h y
    refine Submodule.mem_sup.mpr ⟨θ x, ⟨x, rfl⟩, y - θ x, ?_, add_sub_cancel _ _⟩
    rw [← Finset.univ_sum_single (y - θ x)]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_top_le_comap_smul_top _
      (LinearMap.single R (fun _ ↦ MonoidAlgebra R G) i) ?_
    rw [← ker_residue, ← mapRingHom_eq_zero_iff, Pi.sub_apply, map_sub, hx, sub_self]
  have hsurj : Function.Surjective θ := LinearMap.range_eq_top.mp (top_unique
    (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson ⊥)
      hle))
  exact ⟨OrzechProperty.injective_of_surjective_endomorphism (θ.restrictScalars R) hsurj, hsurj⟩

/-- **Lyndon's sequence is right exact modulo `𝔪`.** An element of the augmentation ideal that
reduces to zero modulo the maximal ideal is the image, under `e_i ↦ g_i - 1` for a generating
family, of a family that reduces to zero. -/
private theorem exists_linearCombination_eq_of_mapRingHom_residue_eq_zero {g : ι → G}
    (hg : Subgroup.closure (Set.range g) = ⊤) {x : MonoidAlgebra R G}
    (hx : augmentation R G x = 0) (hx' : mapRingHom G (residue R) x = 0) :
    ∃ z : ι → MonoidAlgebra R G, (∀ i, mapRingHom G (residue R) (z i) = 0) ∧
      Fintype.linearCombination (MonoidAlgebra R G) (fun i ↦ single (g i) (1 : R) - 1) z = x := by
  have := Fintype.ofFinite G
  -- Each `h - 1` is the image of some `y h`; then `x = ∑ₕ xₕ (h - 1)` is the image of
  -- `∑ₕ xₕ • y h`, whose coefficients `xₕ` lie in `𝔪`.
  have hy (h : G) : ∃ y, Fintype.linearCombination (MonoidAlgebra R G)
      (fun i ↦ single (g i) (1 : R) - 1) y = single h (1 : R) - 1 := by
    rw [← LinearMap.mem_range, range_linearCombination_eq_ker_augmentation hg, RingHom.mem_ker,
      map_sub, augmentation_single, map_one, sub_self]
  choose y hy using hy
  rw [mapRingHom_eq_zero_iff, ker_residue] at hx'
  have hc (h : G) : x.coeff h ∈ maximalIdeal R := mem_ideal_smul_top_iff.mp hx' h
  have hsum : ∑ h, single h (x.coeff h) = x := by
    rw [← Finsupp.sum_fintype _ _ fun _ ↦ single_zero _, sum_coeff_single]
  refine ⟨∑ h, x.coeff h • y h, fun i ↦ ?_, ?_⟩
  · rw [mapRingHom_eq_zero_iff, ker_residue]
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact Submodule.sum_mem _ fun h _ ↦ Submodule.smul_mem_smul (hc h) Submodule.mem_top
  · have haug : ∑ h, x.coeff h = 0 := by
      rw [← hsum, map_sum] at hx
      simpa using hx
    simp only [map_sum, LinearMap.map_smul_of_tower, hy, smul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_smul, haug, zero_smul, sub_zero]
    simpa [smul_single'] using hsum

omit [Finite G] in
/-- Reduction modulo the maximal ideal commutes with `e_i ↦ g_i - 1`. -/
private theorem mapRingHom_residue_linearCombination (g : ι → G) (c : ι → MonoidAlgebra R G) :
    mapRingHom G (residue R)
        (Fintype.linearCombination (MonoidAlgebra R G) (fun i ↦ single (g i) (1 : R) - 1) c) =
      Fintype.linearCombination (MonoidAlgebra (ResidueField R) G)
        (fun i ↦ single (g i) (1 : ResidueField R) - 1) fun i ↦ mapRingHom G (residue R) (c i) := by
  simp [Fintype.linearCombination_apply, mapRingHom_single]

/-- **Two generating families of the same size give isomorphic presentations.** For generating
families `g` and `g'` of a finite group `G`, indexed by the same finite type, and a local ring `R`,
the maps `R[G]^ι → R[G]`, `e_i ↦ g_i - 1` and `e_i ↦ g'_i - 1`, differ by an automorphism of
`R[G]^ι`. -/
theorem exists_linearEquiv_linearCombination_comp_eq {g g' : ι → G}
    (hg : Subgroup.closure (Set.range g) = ⊤) (hg' : Subgroup.closure (Set.range g') = ⊤) :
    ∃ θ : (ι → MonoidAlgebra R G) ≃ₗ[MonoidAlgebra R G] (ι → MonoidAlgebra R G),
      Fintype.linearCombination (MonoidAlgebra R G) (fun i ↦ single (g' i) (1 : R) - 1) ∘ₗ
          θ.toLinearMap =
        Fintype.linearCombination (MonoidAlgebra R G) (fun i ↦ single (g i) (1 : R) - 1) := by
  classical
  set a := Fintype.linearCombination (MonoidAlgebra R G) fun i ↦ single (g i) (1 : R) - 1
  set b := Fintype.linearCombination (MonoidAlgebra R G) fun i ↦ single (g' i) (1 : R) - 1
  set red := mapRingHom G (residue R)
  have hred : Function.Surjective red := map_surjective _ (residue_surjective (R := R))
  -- Over the residue field the group algebra is Artinian, so the two presentations differ by an
  -- automorphism `θ₀` there.
  have : IsArtinianRing (MonoidAlgebra (ResidueField R) G) :=
    IsArtinianRing.of_finite (ResidueField R) _
  obtain ⟨θ₀, hθ₀⟩ := exists_linearEquiv_comp_eq_of_range_eq
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_of_tower (ResidueField R) inferInstance,
        isArtinian_of_tower (ResidueField R) inferInstance⟩)
    (a := Fintype.linearCombination (MonoidAlgebra (ResidueField R) G)
      fun i ↦ single (g i) (1 : ResidueField R) - 1)
    (b := Fintype.linearCombination (MonoidAlgebra (ResidueField R) G)
      fun i ↦ single (g' i) (1 : ResidueField R) - 1)
    (by rw [range_linearCombination_eq_ker_augmentation hg,
      range_linearCombination_eq_ker_augmentation hg'])
  -- Lift the images `θ₀ eⱼ` to `w j`, and correct each lift by a family `z j` reducing to zero so
  -- that `b (w j + z j) = a eⱼ`.
  choose w hw using fun j i ↦ hred (θ₀ (Pi.single j 1) i)
  have hcorr (j : ι) : ∃ z : ι → MonoidAlgebra R G, (∀ i, red (z i) = 0) ∧
      b z = a (Pi.single j 1) - b (w j) := by
    refine exists_linearCombination_eq_of_mapRingHom_residue_eq_zero R hg' ?_ ?_
    · rw [map_sub, sub_eq_zero]
      exact (range_linearCombination_le_ker_augmentation g (LinearMap.mem_range_self a _)).trans
        (range_linearCombination_le_ker_augmentation g' (LinearMap.mem_range_self b _)).symm
    · have he : (fun i ↦ red ((Pi.single j 1 : ι → MonoidAlgebra R G) i)) = Pi.single j 1 := by
        ext1 i
        rcases eq_or_ne i j with rfl | hij <;> simp [*]
      rw [map_sub, sub_eq_zero, mapRingHom_residue_linearCombination,
        mapRingHom_residue_linearCombination, he, funext (hw j)]
      exact (LinearMap.congr_fun hθ₀ _).symm
  choose z hz hbz using hcorr
  let θ := Fintype.linearCombination (MonoidAlgebra R G) fun j ↦ w j + z j
  have hθ : b ∘ₗ θ = a := by
    refine LinearMap.pi_ext' fun j ↦ LinearMap.ext_ring ?_
    simp [θ, Fintype.linearCombination_apply_single, hbz]
  -- Modulo `𝔪`, `θ` is `θ₀`, which is onto; so `θ` is bijective by Nakayama's lemma.
  have hθred (x : ι → MonoidAlgebra R G) (i : ι) : red (θ x i) = θ₀ (fun j ↦ red (x j)) i := by
    have hx : (fun j ↦ red (x j)) = ∑ j, red (x j) • Pi.single j 1 := by
      ext1 k
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx]
    simp [θ, Fintype.linearCombination_apply, Finset.sum_apply, hz, hw]
  refine ⟨.ofBijective θ (bijective_of_forall_exists_mapRingHom_residue_eq R θ fun y ↦ ?_), hθ⟩
  choose x hx using fun i ↦ hred (θ₀.symm (fun j ↦ red (y j)) i)
  exact ⟨x, fun i ↦ by rw [hθred, funext hx, LinearEquiv.apply_symm_apply]⟩

/-- **The relation module depends only on the number of generators.** Two generating families of a
finite group `G`, indexed by the same finite type, have isomorphic relation modules over the group
algebra `R[G]` of `G` over a local ring `R`. -/
theorem relationModule_linearEquiv_of_closure {g g' : ι → G}
    (hg : Subgroup.closure (Set.range g) = ⊤) (hg' : Subgroup.closure (Set.range g') = ⊤) :
    Nonempty (relationModule R G g ≃ₗ[MonoidAlgebra R G] relationModule R G g') := by
  obtain ⟨θ, hθ⟩ := exists_linearEquiv_linearCombination_comp_eq R hg hg'
  refine ⟨θ.ofSubmodules _ _ ?_⟩
  rw [relationModule_def, relationModule_def, ← hθ, LinearMap.ker_comp,
    Submodule.map_comap_eq_of_surjective θ.surjective]

end TauCeti.MonoidAlgebra
