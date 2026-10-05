/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Reduced
public import TauCeti.AlgebraicTopology.Sphere.Puncture
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The complement of an embedded cube is acyclic

If `h : Iᵏ → Sⁿ` is an embedding of a cube into a sphere, then the complement `Sⁿ ∖ h(Iᵏ)` has
the reduced singular homology of a point. This is the first half of Hatcher's Proposition 2B.1;
the second half, that the complement of an embedded `k`-sphere has the reduced homology of an
`(n - k - 1)`-sphere, follows from it by the same Mayer–Vietoris argument, and with it the
Jordan–Brouwer separation theorem: an embedded `(n - 1)`-sphere separates `Sⁿ` into exactly two
path components.

The proof works in any Hausdorff space `Y` in which the complement of every point has vanishing
reduced homology, by induction on `k`. Write `Iᵏ⁺¹ = I × Iᵏ` and, for `s ⊆ I`, let `W s` be the
complement of the image of the slab `s × Iᵏ`. By induction, `W {t}` is acyclic for every `t`. A
class `α` of `W I` therefore vanishes in `W J` for every short enough interval `J` around a point,
since a singular cycle has compact support (`TauCeti.exists_singularHomologyMap_inclusion_eq_zero`),
and if it vanishes in `W [a, b]` and `W [b, c]` then it vanishes in `W [a, c]`, by the
Mayer–Vietoris sequence of `W [a, c] = W [a, b] ∩ W [b, c]` inside `W {b}`
(`TopCat.eq_zero_of_comp_reducedSingularHomologyFunctor_map_inclusion`). Hatcher concludes by
repeated bisection; here the set of `s` with `α` vanishing in `W [0, s]` is shown to be open and
closed in `I`, hence all of it.

Coefficients are a module over a ring, since the compactness step is an argument about elements.

## Main results

* `TauCeti.isZero_reducedSingularHomologyFunctor_compl_range_cube`: in a Hausdorff space whose
  point complements are acyclic, the complement of an embedded cube is acyclic.
* `TauCeti.isZero_reducedSingularHomologyFunctor_sphere_compl_range_cube`: the complement of a cube
  embedded in the unit sphere of a real normed space is acyclic.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.B, Proposition 2B.1(a).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Topology Set TopCat

universe w

namespace TauCeti

section Cube

open unitInterval Metric

variable {A : Type w} [Ring A] (M : ModuleCat.{w} A)

variable {Y : Type w} {k : ℕ} (h : (Fin (k + 1) → I) → Y)

/-- The complement of the image of the slab of the cube `Iᵏ⁺¹` whose first coordinate lies in
`s`. -/
private def slabCompl (s : Set I) : Set Y := (h '' ((fun c ↦ c 0) ⁻¹' s))ᶜ

variable {h}

private lemma isOpen_slabCompl [TopologicalSpace Y] [T2Space Y] (hc : Continuous h) {s : Set I}
    (hs : IsClosed s) : IsOpen (slabCompl h s) :=
  ((hs.preimage (continuous_apply 0)).isCompact.image hc).isClosed.isOpen_compl

private lemma slabCompl_subset_slabCompl {s t : Set I} (hst : s ⊆ t) :
    slabCompl h t ⊆ slabCompl h s :=
  compl_subset_compl.2 (image_mono fun _ hc ↦ hst hc)

private lemma slabCompl_union_slabCompl (hi : Function.Injective h) (s t : Set I) :
    slabCompl h s ∪ slabCompl h t = slabCompl h (s ∩ t) := by
  rw [slabCompl, slabCompl, slabCompl, ← compl_inter, ← image_inter hi, preimage_inter]

private lemma slabCompl_inter_slabCompl (s t : Set I) :
    slabCompl h s ∩ slabCompl h t = slabCompl h (s ∪ t) := by
  rw [slabCompl, slabCompl, slabCompl, ← compl_union, ← image_union, preimage_union]

private lemma slabCompl_singleton (t : I) : slabCompl h {t} = (range (h ∘ Fin.cons t))ᶜ := by
  rw [slabCompl, range_comp]
  congr 2
  ext c
  exact ⟨fun hc ↦ ⟨Fin.tail c, by rw [← mem_singleton_iff.1 hc, Fin.cons_self_tail]⟩,
    by rintro ⟨x, rfl⟩; exact Fin.cons_zero (α := fun _ ↦ I) t x⟩

private lemma slabCompl_univ : slabCompl h univ = (range h)ᶜ := by
  simp [slabCompl]

/-- A point outside the image of a slice lies outside the image of a thin slab around it. -/
private lemma slabCompl_singleton_subset_iUnion (hi : Function.Injective h) (t : I) :
    slabCompl h {t} ⊆ ⋃ m : ℕ, slabCompl h (closedBall t (1 / (m + 1))) := by
  intro y hy
  by_contra hne
  simp only [mem_iUnion, not_exists, slabCompl, mem_compl_iff, not_not] at hne
  obtain ⟨c, -, rfl⟩ := hne 0
  refine hy ⟨c, ?_, rfl⟩
  have hdist : ∀ m : ℕ, dist (c 0) t ≤ 1 / (m + 1) := fun m ↦ by
    obtain ⟨c', hc', hcc'⟩ := hne m
    rw [hi hcc'] at hc'
    exact hc'
  exact dist_le_zero.1 (ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat hdist)

private lemma monotone_slabCompl_closedBall (t : I) :
    Monotone fun m : ℕ ↦ slabCompl h (closedBall t (1 / (m + 1))) :=
  fun _ _ hmm' ↦ slabCompl_subset_slabCompl
    (closedBall_subset_closedBall (Nat.one_div_le_one_div hmm'))

variable [TopologicalSpace Y]

variable (h) in
/-- The map on reduced homology induced by the inclusion of the complement of the whole cube into
the complement of the slab over `s`. -/
private abbrev slabRestrict (n : ℕ) (s : Set I) :
    (reducedSingularHomologyFunctor M n).obj (of ↥(slabCompl h univ)) ⟶
      (reducedSingularHomologyFunctor M n).obj (of ↥(slabCompl h s)) :=
  (reducedSingularHomologyFunctor M n).map
    (ofHom (ContinuousMap.inclusion (slabCompl_subset_slabCompl (subset_univ s))))

/-- Restricting further: the map to the complement of a smaller slab factors through the map to
the complement of a larger one. -/
private lemma slabRestrict_apply_of_subset {n : ℕ} {s s' : Set I} (hss' : s ⊆ s')
    (α : (reducedSingularHomologyFunctor M n).obj (of ↥(slabCompl h univ))) :
    slabRestrict M h n s α = (reducedSingularHomologyFunctor M n).map
      (ofHom (ContinuousMap.inclusion (slabCompl_subset_slabCompl hss')))
        (slabRestrict M h n s' α) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ofHom_inclusion_comp_ofHom_inclusion]

variable [T2Space Y]

/-- **Gluing along a slice.** If a class of the complement of the cube vanishes in the
complements of the slabs over `[0, a]` and over `[a, b]`, it vanishes in the complement of the slab
over `[0, b]`: these two complements intersect in the third, and their union, the complement of the
slice over `a`, is acyclic, so this is exactness of the Mayer–Vietoris sequence. -/
private lemma slabRestrict_Icc_eq_zero (hc : Continuous h) (hi : Function.Injective h) {n : ℕ}
    {a b : I} (hab : a ≤ b)
    (hslice : IsZero ((reducedSingularHomologyFunctor M (n + 1)).obj (of ↥(slabCompl h {a}))))
    {α : (reducedSingularHomologyFunctor M n).obj (of ↥(slabCompl h univ))}
    (ha : slabRestrict M h n (Icc 0 a) α = 0) (hb : slabRestrict M h n (Icc a b) α = 0) :
    slabRestrict M h n (Icc 0 b) α = 0 := by
  have h0a : (0 : I) ≤ a := nonneg'
  have hx := eq_zero_of_comp_reducedSingularHomologyFunctor_map_inclusion M (Y := of Y)
    (isOpen_slabCompl hc isClosed_Icc) (isOpen_slabCompl hc isClosed_Icc)
    (slabCompl_subset_slabCompl (Icc_subset_Icc_right hab))
    (slabCompl_subset_slabCompl (Icc_subset_Icc_left h0a))
    ((slabCompl_inter_slabCompl _ _).trans (by rw [Icc_union_Icc_eq_Icc h0a hab])).subset
    ((slabCompl_union_slabCompl hi _ _).trans (by rw [Icc_inter_Icc_eq_singleton h0a hab]))
    hslice (ModuleCat.ofHom (LinearMap.toSpanSingleton A _ (slabRestrict M h n (Icc 0 b) α)))
    ?_ ?_
  · simpa using congr(($hx).hom 1)
  all_goals
    ext
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, one_smul, ModuleCat.hom_zero, LinearMap.zero_apply]
  · rw [← slabRestrict_apply_of_subset M (Icc_subset_Icc_right hab), ha]
  · rw [← slabRestrict_apply_of_subset M (Icc_subset_Icc_left h0a), hb]

/-- **Compactness.** If the complement of the slice over `t` is acyclic, then a class of the
complement of the cube vanishes in the complement of the slab over some interval around `t`: it
vanishes in the complement of the slice, which is the increasing union of these complements. -/
private lemma exists_slabRestrict_closedBall_eq_zero (hc : Continuous h)
    (hi : Function.Injective h) {n : ℕ} {t : I}
    (hslice : IsZero ((reducedSingularHomologyFunctor M n).obj (of ↥(slabCompl h {t}))))
    (α : (reducedSingularHomologyFunctor M n).obj (of ↥(slabCompl h univ))) :
    ∃ ε > 0, slabRestrict M h n (closedBall t ε) α = 0 := by
  have hUV (m : ℕ) : slabCompl h (closedBall t (1 / (m + 1))) ⊆ slabCompl h {t} :=
    slabCompl_subset_slabCompl (singleton_subset_iff.2 (mem_closedBall_self (by positivity)))
  -- Pass to unreduced homology, where the compactness statement is formulated.
  let ι := reducedSingularHomologyι M n
  obtain ⟨m, hm0, hm⟩ := exists_singularHomologyMap_inclusion_eq_zero M n (Y := of Y)
    (monotone_slabCompl_closedBall t) hUV
    (fun m ↦ (isOpen_slabCompl hc isClosed_closedBall).preimage continuous_subtype_val)
    (slabCompl_singleton_subset_iUnion hi t) (i := 0) (ι.app _ (slabRestrict M h n _ α)) (by
      rw [← ConcreteCategory.comp_apply, ← ι.naturality, ConcreteCategory.comp_apply,
        (ModuleCat.subsingleton_of_isZero hslice).elim
          ((reducedSingularHomologyFunctor M n).map _ _) 0, map_zero])
  refine ⟨1 / (m + 1), by positivity, ?_⟩
  apply (ModuleCat.mono_iff_injective (ι.app _)).1 inferInstance
  rw [map_zero, ← hm, ← ConcreteCategory.comp_apply (ι.app _)
    (((singularHomologyFunctor _ n).obj M).map _), ← ι.naturality, ConcreteCategory.comp_apply,
    ← slabRestrict_apply_of_subset M (closedBall_subset_closedBall (Nat.one_div_le_one_div hm0))]

/-- **The inductive step.** If the complement of the image of every slice `{t} × Iᵏ` of an
embedded cube `Iᵏ⁺¹` has vanishing reduced homology, so does the complement of the whole cube.

By compactness, a class `α` of the complement of the cube vanishes in the complement of the slab
over a short enough interval around any point, and by the Mayer–Vietoris sequence its vanishing
over two adjacent intervals implies its vanishing over their union. So the set of `s` for which `α`
vanishes over `[0, s]` is open and closed, hence all of `I`. -/
private lemma isZero_reducedSingularHomologyFunctor_slabCompl_univ (hc : Continuous h)
    (hi : Function.Injective h)
    (hslice : ∀ (t : I) (n : ℕ),
      IsZero ((reducedSingularHomologyFunctor M n).obj (of ↥(slabCompl h {t}))))
    (n : ℕ) : IsZero ((reducedSingularHomologyFunctor M n).obj (of ↥(slabCompl h univ))) := by
  suffices hzero : ∀ α : (reducedSingularHomologyFunctor M n).obj (of ↥(slabCompl h univ)),
      α = 0 from
    @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun α β ↦ (hzero α).trans (hzero β).symm⟩
  intro α
  have hmono {s s' : Set I} (hss' : s ⊆ s') (hs' : slabRestrict M h n s' α = 0) :
      slabRestrict M h n s α = 0 := by
    rw [slabRestrict_apply_of_subset M hss', hs', map_zero]
  -- Whether `α` vanishes over `[0, s]` does not change near any `s`.
  have hlc : IsLocallyConstant fun s : I ↦ slabRestrict M h n (Icc 0 s) α = 0 := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun s ↦ ?_
    obtain ⟨ε, hε, hPs⟩ := exists_slabRestrict_closedBall_eq_zero M hc hi (hslice s n) α
    have hsub {a b : I} (ha : a ∈ closedBall s ε) (hb : b ∈ closedBall s ε) :
        Icc a b ⊆ closedBall s ε := by
      intro x hx
      have hax : (a : ℝ) ≤ x := hx.1
      have hxb : (x : ℝ) ≤ b := hx.2
      simp only [mem_closedBall, Subtype.dist_eq, Real.dist_eq, abs_le] at ha hb ⊢
      constructor <;> linarith
    filter_upwards [ball_mem_nhds s hε] with s' hs'
    have hs's : s' ∈ closedBall s ε := ball_subset_closedBall hs'
    have hss : s ∈ closedBall s ε := mem_closedBall_self hε.le
    rcases le_total s s' with hss' | hs's'
    · exact propext ⟨hmono (Icc_subset_Icc_right hss'), fun h' ↦
        slabRestrict_Icc_eq_zero M hc hi hss' (hslice s (n + 1)) h' (hmono (hsub hss hs's) hPs)⟩
    · exact propext ⟨fun h' ↦ slabRestrict_Icc_eq_zero M hc hi hs's' (hslice s' (n + 1)) h'
        (hmono (hsub hs's hss) hPs), hmono (Icc_subset_Icc_right hs's')⟩
  have h0 : slabRestrict M h n (Icc 0 0) α = 0 := by
    obtain ⟨ε, hε, hP⟩ := exists_slabRestrict_closedBall_eq_zero M hc hi (hslice 0 n) α
    exact hmono (by simp [hε.le]) hP
  have h1 : slabRestrict M h n univ α = 0 :=
    hmono (s' := Icc 0 1) (fun _ _ ↦ ⟨nonneg', le_one'⟩)
      ((hlc.apply_eq_of_preconnectedSpace 0 1) ▸ h0)
  -- Over all of `I`, the restriction is the identity.
  have hid : slabRestrict M h n univ = 𝟙 _ := by
    rw [slabRestrict, ← CategoryTheory.Functor.map_id]
    -- The inclusion of a set into itself is the identity map, by definition.
    congr 1
  rwa [hid, ModuleCat.id_apply] at h1

end Cube

section Main

open unitInterval Metric

variable {A : Type w} [Ring A] (M : ModuleCat.{w} A)

/-- **The complement of an embedded cube is acyclic.** Let `Y` be a Hausdorff space in which the
complement of every point has vanishing reduced homology. Then the complement of the image of any
embedding of a cube `Iᵏ` into `Y` has vanishing reduced homology, with coefficients in any module.
Since the cube is compact and `Y` is Hausdorff, a continuous injection of it is an embedding.

This is Hatcher, *Algebraic Topology*, Proposition 2B.1(a), for `Y` a sphere; the proof is by
induction on `k`, cutting the cube into slabs along its first coordinate. -/
theorem isZero_reducedSingularHomologyFunctor_compl_range_cube {Y : Type w} [TopologicalSpace Y]
    [T2Space Y]
    (hY : ∀ (y : Y) (n : ℕ), IsZero ((reducedSingularHomologyFunctor M n).obj (of ↥({y}ᶜ : Set Y))))
    {k : ℕ} {h : (Fin k → I) → Y} (hc : Continuous h) (hi : Function.Injective h) (n : ℕ) :
    IsZero ((reducedSingularHomologyFunctor M n).obj (of ↥(range h)ᶜ)) := by
  induction k generalizing n with
  | zero => rw [range_unique]; exact hY _ n
  | succ k ih =>
    rw [← slabCompl_univ]
    refine isZero_reducedSingularHomologyFunctor_slabCompl_univ M hc hi (fun t m ↦ ?_) n
    rw [slabCompl_singleton]
    exact ih (hc.comp (continuous_const.finCons continuous_id))
      (hi.comp (Fin.cons_right_injective (α := fun _ ↦ I) t)) m

/-- **The complement of a cube embedded in a sphere is acyclic** (Hatcher, *Algebraic Topology*,
Proposition 2B.1(a)): for every embedding `h` of a cube `Iᵏ` into the unit sphere of a real normed
space, the reduced singular homology of the complement of its image vanishes in every degree. -/
theorem isZero_reducedSingularHomologyFunctor_sphere_compl_range_cube {E : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {h : (Fin k → I) → sphere (0 : E) 1}
    (hc : Continuous h) (hi : Function.Injective h) (n : ℕ) :
    IsZero ((reducedSingularHomologyFunctor M n).obj (of ↥(range h)ᶜ)) :=
  isZero_reducedSingularHomologyFunctor_compl_range_cube M
    (fun p n ↦ have := contractibleSpace_sphere_compl_singleton p
      isZero_reducedSingularHomologyFunctor_of_contractibleSpace M _ n) hc hi n

end Main

end TauCeti
