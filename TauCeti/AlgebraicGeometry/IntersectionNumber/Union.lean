/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.BaseChange

/-!
# Degrees of line bundles on unions of closed subschemes

Let `X` be a scheme over a field `k` and let `V(I)`, `V(J)` be closed subschemes of `X` meeting in
a scheme `V(I ⊔ J)` finite over `k` (for instance in finitely many points, when `X` is locally of
finite type over `k`: `Scheme.IdealSheafData.isFinite_subschemeι_comp_of_finite_support`). Then the
degree of a line bundle on the union `V(I ⊓ J)` is the sum of its degrees on `V(I)` and on
`V(J)`:

`(a · V(I ⊓ J)) = (a · V(I)) + (a · V(J))`

(`TauCeti.AlgebraicGeometry.LineBundleClass.intersectionNumber_subschemeι_inf`), as soon as line
bundles on `V(I)` and `V(J)` have finite-dimensional `H⁰` and `H¹`. Here `(a · C)` is the
Euler-characteristic degree of the pullback of `a` to `C`
(`TauCeti.AlgebraicGeometry.LineBundleClass.intersectionNumber`).

The proof tensors the Mayer–Vietoris sequence
`0 ⟶ 𝒪_{V(I ⊓ J)} ⟶ 𝒪_{V(I)} ⊞ 𝒪_{V(J)} ⟶ 𝒪_{V(I ⊔ J)} ⟶ 0`
(`AlgebraicGeometry.Scheme.IdealSheafData.shortExact_mayerVietoris`) with a line bundle `L`. By the
projection formula its terms are the direct images of the restrictions of `L`. The last one lives
on the finite scheme `V(I ⊔ J)`, where `L` is trivial, so it has no `H¹` and its Euler
characteristic `dim_k Γ(V(I ⊔ J), 𝒪)` does not depend on `L`. Hence the Euler characteristics are
additive along the sequence,

`χ(L|_{V(I ⊓ J)}) + dim_k Γ(V(I ⊔ J), 𝒪) = χ(L|_{V(I)}) + χ(L|_{V(J)})`

(`FiniteLocallyFreeSheaf.FixedRank.eulerCharBelow_pullback_subschemeι_inf_add`), and subtracting
the same identity for `𝒪_X` gives additivity of degrees. No vanishing of `H²` is needed, so `X`
is not assumed to be a curve, and no hypothesis on the singularities of `V(I)` and `V(J)`
enters.

By induction this gives additivity of degrees over a closed cover. Let `X` be a reduced scheme,
quasi-compact and locally of finite type over `k`, covered by a nonempty finite
family of closed subsets which pairwise meet in finitely many points, and such that line bundles
restricted to the reduced closed subschemes on these subsets have finite-dimensional `H⁰` and `H¹`.
Then the degree of a line bundle on `X` is the sum of its
degrees on these reduced closed subschemes
(`TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_eq_sum_intersectionNumber_vanishingIdeal`).
Applied to a reduced proper curve over `k`, such as a nodal curve, and the cover by its irreducible
components, this expresses the degree of a line bundle as the sum of its degrees on the components,
as soon as the components meet in finitely many points and line bundles on them have
finite-dimensional cohomology.

## References

* [The Stacks Project, Section 33.44, Tag 0AYQ](https://stacks.math.columbia.edu/tag/0AYQ):
  degrees of invertible modules on proper curves, and their additivity over the irreducible
  components.
* [The Stacks Project, Lemma 33.4.6, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J): the
  exact sequence `0 → 𝒪_{Y ∪ Z} → 𝒪_Y × 𝒪_Z → 𝒪_{Y ∩ Z} → 0` of two closed subschemes.
* R. Hartshorne, *Algebraic Geometry*, Lemma III.2.10: the cohomology of a sheaf supported on a
  closed subscheme.
-/

public section

open CategoryTheory Limits MonoidalCategory TopologicalSpace AlgebraicGeometry
open Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

open Scheme.IdealSheafData

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-! ### Degrees on a union of closed subschemes -/

variable {k} (I J : X.IdealSheafData) [IsFinite ((I ⊔ J).subschemeι ≫ X ↘ Spec (.of k))]

/-- The finiteness hypothesis on `V(I)` for a line bundle `L`, for the vector bundle underlying
`L`. -/
private lemma finiteDimensional_cohomology_pullback_toFixedRankOne {L : InvertibleSheaf X}
    (hI : ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj i)) :
    ∀ i < 2, FiniteDimensional k (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj
      ((InvertibleSheaf.toFixedRankOne X).obj L).obj).obj i) := fun i hi ↦ by
  rw [InvertibleSheaf.toFixedRankOne_obj_obj, InvertibleSheaf.pullback_toFiniteLocallyFree_obj_obj]
  exact hI i hi

namespace InvertibleSheaf

/-- **Finiteness of cohomology on a union.** If the closed subschemes `V(I)` and `V(J)` meet in a
scheme finite over `k`, and the restrictions of a line bundle `L` to them have finite-dimensional
cohomology, then so do `H⁰` and `H¹` of its restriction to `V(I ⊓ J)`. -/
theorem finiteDimensional_cohomology_pullback_subschemeι_inf (L : InvertibleSheaf X)
    (hI : ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj i))
    (hJ : ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback J.subschemeι).obj L).obj i))
    {i : ℕ} (hi : i < 2) : FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (I ⊓ J).subschemeι).obj L).obj i) := by
  have h := ((InvertibleSheaf.toFixedRankOne X).obj
    L).finiteDimensional_cohomology_pullback_subschemeι_inf k I J
      (finiteDimensional_cohomology_pullback_toFixedRankOne I hI)
      (finiteDimensional_cohomology_pullback_toFixedRankOne J hJ) hi
  rwa [InvertibleSheaf.toFixedRankOne_obj_obj,
    InvertibleSheaf.pullback_toFiniteLocallyFree_obj_obj] at h

end InvertibleSheaf

namespace LineBundleClass

/-- **Additivity of degrees on a union of closed subschemes.** If the closed subschemes `V(I)` and
`V(J)` of a scheme over `k` meet in a scheme finite over `k`, and the restrictions to them of line
bundles on `X` have finite-dimensional cohomology, then the degree of a line-bundle class on the
union `V(I ⊓ J)` is the sum of its degrees on `V(I)` and on `V(J)`. -/
theorem intersectionNumber_subschemeι_inf
    (hI : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj i))
    (hJ : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback J.subschemeι).obj L).obj i))
    (a : LineBundleClass X) :
    intersectionNumber k (I ⊓ J).subschemeι a =
      intersectionNumber k I.subschemeι a + intersectionNumber k J.subschemeι a := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  have key (L : InvertibleSheaf X) := by
    have h := ((InvertibleSheaf.toFixedRankOne X).obj
      L).eulerCharBelow_pullback_subschemeι_inf_add k I J
        (finiteDimensional_cohomology_pullback_toFixedRankOne I (hI L))
        (finiteDimensional_cohomology_pullback_toFixedRankOne J (hJ L)) default
    simp only [InvertibleSheaf.toFixedRankOne_obj_obj,
      InvertibleSheaf.pullback_toFiniteLocallyFree_obj_obj] at h
    exact h
  have hL := key L
  have hT := key (InvertibleSheaf.trivial X)
  rw [intersectionNumber_mk_eq_eulerCharBelow_sub, intersectionNumber_mk_eq_eulerCharBelow_sub,
    intersectionNumber_mk_eq_eulerCharBelow_sub]
  linarith

variable [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- Additivity of degrees, with the finiteness of cohomology, over the union of a nonempty finite
family of closed subsets which pairwise meet in finitely many points. -/
private lemma intersectionNumber_vanishingIdeal_finset_sup (s : Finset (Closeds X))
    (hmeet : ∀ Z ∈ s, ∀ W ∈ s, Z ≠ W → ((Z ⊓ W : Closeds X) : Set X).Finite)
    (hcoh : ∀ Z ∈ s, ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (vanishingIdeal Z).subschemeι).obj L).obj i))
    (t : Finset (Closeds X)) (ht : t.Nonempty) (hts : t ⊆ s) :
    (∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k (Cohomology
      ((InvertibleSheaf.pullback (vanishingIdeal (t.sup id)).subschemeι).obj L).obj i)) ∧
    ∀ a : LineBundleClass X, intersectionNumber k (vanishingIdeal (t.sup id)).subschemeι a =
      ∑ Z ∈ t, intersectionNumber k (vanishingIdeal Z).subschemeι a := by
  induction ht using Finset.Nonempty.cons_induction with
  | singleton W =>
    rw [Finset.sup_singleton, id_eq]
    exact ⟨hcoh W (hts (Finset.mem_singleton_self W)), fun a ↦ (Finset.sum_singleton _ _).symm⟩
  | cons W t hW _ ih =>
    obtain ⟨ihc, ihd⟩ := ih ((Finset.subset_cons hW).trans hts)
    have hWs := hts (Finset.mem_cons_self W t)
    -- `W` meets the union of the members of `t` in finitely many points.
    have : IsFinite ((vanishingIdeal W ⊔ vanishingIdeal (t.sup id)).subschemeι ≫
        X ↘ Spec (.of k)) := by
      refine isFinite_subschemeι_comp_of_finite_support k _ ?_
      rw [support_sup, Closeds.coe_inf, coe_support_vanishingIdeal, coe_support_vanishingIdeal,
        Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.inter_iUnion₂]
      refine t.finite_toSet.biUnion fun Z hZ ↦ ?_
      exact hmeet W hWs Z (hts (Finset.subset_cons hW hZ)) (ne_of_mem_of_not_mem hZ hW).symm
    rw [Finset.sup_cons, id_eq, vanishingIdeal_sup]
    refine ⟨fun L i hi ↦ InvertibleSheaf.finiteDimensional_cohomology_pullback_subschemeι_inf _ _ L
      (hcoh W hWs L) (ihc L) hi, fun a ↦ ?_⟩
    rw [Finset.sum_cons, ← ihd a]
    exact intersectionNumber_subschemeι_inf _ _ (hcoh W hWs) ihc a

/-- **Additivity of degrees over a closed cover.** Let `X` be a reduced scheme over a field `k`,
quasi-compact and locally of finite type over `k`, covered by a nonempty finite
family `s` of closed subsets which pairwise meet in finitely many points, and such that line
bundles restricted to the reduced closed subschemes on the members of `s` have finite-dimensional
`H⁰` and `H¹`. Then the degree of a line-bundle class on `X` is the sum of its degrees on these
reduced closed subschemes. For a reduced proper curve, such as a nodal curve, and the cover by its
irreducible components, this is the additivity of degrees over the components, once the components
meet in finitely many points and line bundles on them have finite-dimensional cohomology. -/
theorem eulerDegree_eq_sum_intersectionNumber_vanishingIdeal [QuasiCompact (X ↘ Spec (.of k))]
    [IsReduced X] (s : Finset (Closeds X)) (hs : s.Nonempty)
    (hcover : s.sup id = ⊤)
    (hmeet : ∀ Z ∈ s, ∀ W ∈ s, Z ≠ W → ((Z ⊓ W : Closeds X) : Set X).Finite)
    (hcoh : ∀ Z ∈ s, ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (vanishingIdeal Z).subschemeι).obj L).obj i))
    (a : LineBundleClass X) :
    eulerDegree k a = ∑ Z ∈ s, intersectionNumber k (vanishingIdeal Z).subschemeι a := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have h := (intersectionNumber_vanishingIdeal_finset_sup s hmeet hcoh s hs subset_rfl).2 a
  -- The members of `s` cover the reduced scheme `X`, so the ideal sheaf of their union is `⊥`.
  rw [hcover, vanishingIdeal_top, Scheme.nilradical_eq_bot] at h
  rw [← h, intersectionNumber_def]
  exact (eulerDegree_pullback_of_isIso (k := k) _ (comp_over _ _) a).symm

end LineBundleClass

end

end TauCeti.AlgebraicGeometry
