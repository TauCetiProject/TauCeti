/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.MayerVietoris
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Degrees of line bundles on unions of closed subschemes

Let `X` be a scheme over a field `k` and let `V(I)`, `V(J)` be closed subschemes of `X` meeting in
finitely many points, so that `V(I ⊔ J)` is finite over `k`. Then the degree of a line bundle on
the union `V(I ⊓ J)` is the sum of its degrees on `V(I)` and on `V(J)`:

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

By induction, on a reduced scheme `X` covered by a nonempty finite family of closed subsets which
pairwise meet in finitely many points, the degree of a line bundle is the sum of its degrees on the
reduced closed subschemes on these subsets
(`TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_eq_sum_intersectionNumber_vanishingIdeal`).
Applied to a reduced proper curve over `k`, such as a nodal curve, and the cover by its irreducible
components, this expresses the degree of a line bundle as the sum of its degrees on the components,
as soon as the components meet in finitely many points and line bundles on them have
finite-dimensional cohomology.

## References

* [The Stacks Project, Section 33.44, Tag 0AYQ](https://stacks.math.columbia.edu/tag/0AYQ):
  degrees of invertible modules on proper curves, and their additivity over the irreducible
  components.
* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.6 and Lemma III.2.10: the exact sequence of
  two closed subschemes and the cohomology of a sheaf supported on a closed subscheme.
-/

public section

open CategoryTheory Limits MonoidalCategory TopologicalSpace AlgebraicGeometry
open Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- A closed subscheme with finitely many points of a scheme quasi-compact and locally of finite
type over a field is finite over the field. -/
theorem isFinite_subschemeι_comp_of_finite [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (I : X.IdealSheafData)
    (hI : (I.support : Set X).Finite) : IsFinite (I.subschemeι ≫ X ↘ Spec (.of k)) := by
  -- The closed immersion `V(I) ⟶ X` maps the points of `V(I)` injectively into `I.support`.
  have : Finite I.subscheme := by
    have := hI.to_subtype
    refine Finite.of_injective (β := I.support)
      (fun z ↦ ⟨I.subschemeι z, by
        rw [← SetLike.mem_coe, ← I.range_subschemeι]; exact Set.mem_range_self z⟩) fun _ _ h ↦ ?_
    exact I.subschemeι.isClosedEmbedding.injective (congrArg Subtype.val h)
  have := LocallyQuasiFinite.of_finite_preimage_singleton (I.subschemeι ≫ X ↘ Spec (.of k))
    fun _ ↦ Set.toFinite _
  exact IsFinite.of_locallyQuasiFinite _

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry

open Scheme.IdealSheafData

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-! ### Euler characteristics along the Mayer–Vietoris sequence -/

/-- The projection formula for the closed immersion `V(I) ⟶ X`:
`E ⊗ ι_* 𝒪_{V(I)} ≅ ι_* (ι^* E)`. -/
private def tensorPushforwardSubschemeIso (E : FiniteLocallyFreeSheaf X) (I : X.IdealSheafData) :
    E.obj ⊗ I.pushforwardSubscheme ≅ (Scheme.Modules.pushforward I.subschemeι).obj
      ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj E).obj :=
  eqToIso (congrArg (fun F ↦ E.obj ⊗ (Scheme.Modules.pushforward I.subschemeι).obj F)
      (TauCeti.SheafOfModules.tensorUnit_eq I.subscheme.sheaf).symm) ≪≫
    FiniteLocallyFreeSheaf.tensorPushforwardUnitIso I.subschemeι E

private lemma eulerCharBelow_tensor_pushforwardSubscheme (E : FiniteLocallyFreeSheaf X)
    (I : X.IdealSheafData) (n : ℕ) :
    eulerCharBelow k X (E.obj ⊗ I.pushforwardSubscheme) n =
      eulerCharBelow k I.subscheme
        ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj E).obj n := by
  rw [eulerCharBelow_congr k (tensorPushforwardSubschemeIso E I) n,
    Scheme.Hom.eulerCharBelow_pushforward I.subschemeι k]

private lemma finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff
    (E : FiniteLocallyFreeSheaf X) (I : X.IdealSheafData) (i : ℕ) :
    FiniteDimensional k (Cohomology (E.obj ⊗ I.pushforwardSubscheme) i) ↔
      FiniteDimensional k
        (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj E).obj i) :=
  (finiteDimensional_cohomology_congr k (tensorPushforwardSubschemeIso E I) i).trans
    (Scheme.Hom.moduleFinite_cohomology_pushforward_iff I.subschemeι k _ i)

section MayerVietoris

variable {r : ℕ} (E : FiniteLocallyFreeSheaf.FixedRank X r) (I J : X.IdealSheafData)
  [IsFinite ((I ⊔ J).subschemeι ≫ X ↘ Spec (.of k))]
  (hI : ∀ i < 2, FiniteDimensional k
    (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj E.obj).obj i))
  (hJ : ∀ i < 2, FiniteDimensional k
    (Cohomology ((FiniteLocallyFreeSheaf.pullback J.subschemeι).obj E.obj).obj i))

/-- The Mayer–Vietoris sequence of `V(I)` and `V(J)` tensored with `E`. -/
private abbrev tensorMayerVietoris : ShortComplex X.Modules :=
  (mayerVietoris I J).map (tensorLeft E.obj.obj)

private lemma shortExact_tensorMayerVietoris : (tensorMayerVietoris E I J).ShortExact :=
  shortExact_map_tensorLeft E.obj.obj (shortExact_mayerVietoris I J)

/-- The middle term of the tensored sequence is `E ⊗ 𝒪_{V(I)} ⊞ E ⊗ 𝒪_{V(J)}`. -/
private def tensorMayerVietorisX₂Iso :
    (tensorMayerVietoris E I J).X₂ ≅
      (E.obj.obj ⊗ I.pushforwardSubscheme) ⊞ (E.obj.obj ⊗ J.pushforwardSubscheme) :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft E.obj.obj)
  (tensorLeft E.obj.obj).mapBiprod I.pushforwardSubscheme J.pushforwardSubscheme

omit [IsFinite ((I ⊔ J).subschemeι ≫ X ↘ Spec (.of k))] in
include hI hJ in
private lemma finiteDimensional_cohomology_tensorMayerVietoris_X₂ {i : ℕ} (hi : i < 2) :
    FiniteDimensional k (Cohomology (tensorMayerVietoris E I J).X₂ i) := by
  have := (finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k E.obj I i).mpr
    (hI i hi)
  have := (finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k E.obj J i).mpr
    (hJ i hi)
  exact (finiteDimensional_cohomology_congr k (tensorMayerVietorisX₂Iso E I J) i).mpr
    inferInstance

include hI hJ in
private lemma finiteDimensional_cohomology_tensorMayerVietoris_X₁ {i : ℕ} (hi : i < 2) :
    FiniteDimensional k (Cohomology (tensorMayerVietoris E I J).X₁ i) := by
  have hS := shortExact_tensorMayerVietoris E I J
  have h₂ (i : ℕ) (hi : i < 2) :=
    finiteDimensional_cohomology_tensorMayerVietoris_X₂ k E I J hI hJ hi
  have : FiniteDimensional k (Cohomology (tensorMayerVietoris E I J).X₃ 0) :=
    finiteDimensional_cohomology_zero_tensor_pushforward k (I ⊔ J) E
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · have := hS.mono_f
    have := h₂ 0 (by omega)
    exact finiteDimensional_cohomology_zero_of_mono k X (tensorMayerVietoris E I J).f
  · have := h₂ 1 (by omega)
    exact finiteDimensional_cohomology_X₁ k X hS 0 1 rfl

include hI hJ in
/-- **Finiteness of cohomology on a union.** If the closed subschemes `V(I)` and `V(J)` meet in a
scheme finite over `k`, and the restrictions of a vector bundle `E` to them have
finite-dimensional cohomology, then so do `H⁰` and `H¹` of its restriction to `V(I ⊓ J)`. -/
theorem FiniteLocallyFreeSheaf.FixedRank.finiteDimensional_cohomology_pullback_subschemeι_inf
    {i : ℕ} (hi : i < 2) : FiniteDimensional k
      (Cohomology ((FiniteLocallyFreeSheaf.pullback (I ⊓ J).subschemeι).obj E.obj).obj i) :=
  (finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k E.obj (I ⊓ J) i).mp
    (finiteDimensional_cohomology_tensorMayerVietoris_X₁ k E I J hI hJ hi)

include hI hJ in
/-- **Euler characteristics on a union of closed subschemes.** If the closed subschemes `V(I)`
and `V(J)` of `X` meet in a scheme finite over `k`, and the restrictions of a vector bundle `E` of
constant rank `r` to them have finite-dimensional cohomology, then
`χ(E|_{V(I ⊓ J)}) + r · dim_k Γ(V(I ⊔ J), 𝒪) = χ(E|_{V(I)}) + χ(E|_{V(J)})`, with
`χ = dim H⁰ - dim H¹` and the dimension written as the rank of `V(I ⊔ J) ⟶ Spec k` at `s`. -/
theorem FiniteLocallyFreeSheaf.FixedRank.eulerCharBelow_pullback_subschemeι_inf_add
    (s : Spec (.of k)) :
    eulerCharBelow k (I ⊓ J).subscheme
        ((FiniteLocallyFreeSheaf.pullback (I ⊓ J).subschemeι).obj E.obj).obj 2 +
        r * ((I ⊔ J).subschemeι ≫ X ↘ Spec (.of k)).finrank s =
      eulerCharBelow k I.subscheme
          ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj E.obj).obj 2 +
        eulerCharBelow k J.subscheme
          ((FiniteLocallyFreeSheaf.pullback J.subschemeι).obj E.obj).obj 2 := by
  have hS := shortExact_tensorMayerVietoris E I J
  have h₃ : Subsingleton (Cohomology (tensorMayerVietoris E I J).X₃ 1) :=
    subsingleton_cohomology_one_tensor_pushforward k (I ⊔ J) E
  -- The connecting map out of `H¹` of the last term, which vanishes, is zero.
  have hδ : cohomologyδBaseLinear k X hS 1 2 rfl = 0 :=
    LinearMap.ext fun x ↦ by
      rw [h₃.elim x 0, map_zero, LinearMap.zero_apply]
  have h := eulerCharBelow_eq_add_of_cohomologyδ_eq_zero k hS 1
    (fun i hi _ ↦ finiteDimensional_cohomology_tensorMayerVietoris_X₁ k E I J hI hJ hi)
    (fun i hi ↦ finiteDimensional_cohomology_tensorMayerVietoris_X₂ k E I J hI hJ hi) hδ
  rw [eulerCharBelow_congr k (tensorMayerVietorisX₂Iso E I J) 2,
    eulerCharBelow_biprod k _ _ 2
      (fun i hi ↦ (finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k E.obj I i).mpr
        (hI i hi))
      (fun i hi ↦ (finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k E.obj J i).mpr
        (hJ i hi)),
    eulerCharBelow_tensor_pushforwardSubscheme, eulerCharBelow_tensor_pushforwardSubscheme] at h
  -- The first and last terms are `E ⊗ 𝒪_{V(I ⊓ J)}` and `E ⊗ 𝒪_{V(I ⊔ J)}`.
  have h₁ : eulerCharBelow k X (tensorMayerVietoris E I J).X₁ 2 =
      eulerCharBelow k (I ⊓ J).subscheme
        ((FiniteLocallyFreeSheaf.pullback (I ⊓ J).subschemeι).obj E.obj).obj 2 :=
    eulerCharBelow_tensor_pushforwardSubscheme k E.obj (I ⊓ J) 2
  have h₃ : eulerCharBelow k X (tensorMayerVietoris E I J).X₃ 2 =
      r * ((I ⊔ J).subschemeι ≫ X ↘ Spec (.of k)).finrank s :=
    eulerCharBelow_tensor_pushforward k (I ⊔ J) E s
  rw [h₁, h₃] at h
  exact h.symm

end MayerVietoris

/-! ### Degrees on a union of closed subschemes -/

/-- The restriction of the vector bundle underlying a line bundle `L` is the restriction of `L`. -/
private lemma pullback_toFixedRankOne_obj_obj {Y : Scheme.{u}} (f : Y ⟶ X)
    (L : InvertibleSheaf X) :
    ((FiniteLocallyFreeSheaf.pullback f).obj ((InvertibleSheaf.toFixedRankOne X).obj L).obj).obj =
      ((InvertibleSheaf.pullback f).obj L).obj := by
  rw [FiniteLocallyFreeSheaf.pullback_obj_obj, InvertibleSheaf.toFixedRankOne_obj_obj,
    ObjectProperty.ιOfLE_obj_obj, InvertibleSheaf.pullback_obj_obj]

variable {k} (I J : X.IdealSheafData) [IsFinite ((I ⊔ J).subschemeι ≫ X ↘ Spec (.of k))]
  (hI : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
    (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj i))
  (hJ : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
    (Cohomology ((InvertibleSheaf.pullback J.subschemeι).obj L).obj i))

omit [IsFinite ((I ⊔ J).subschemeι ≫ X ↘ Spec (.of k))] in
include hI hJ in
/-- The finiteness hypotheses on `V(I)` and `V(J)`, for the vector bundle underlying `L`. -/
private lemma finiteDimensional_cohomology_pullback_toFixedRankOne (L : InvertibleSheaf X) :
    (∀ i < 2, FiniteDimensional k (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj
      ((InvertibleSheaf.toFixedRankOne X).obj L).obj).obj i)) ∧
    ∀ i < 2, FiniteDimensional k (Cohomology ((FiniteLocallyFreeSheaf.pullback J.subschemeι).obj
      ((InvertibleSheaf.toFixedRankOne X).obj L).obj).obj i) := by
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · rw [pullback_toFixedRankOne_obj_obj]
    exact hI L i hi
  · rw [pullback_toFixedRankOne_obj_obj]
    exact hJ L i hi

namespace InvertibleSheaf

include hI hJ in
/-- **Finiteness of cohomology on a union.** If the closed subschemes `V(I)` and `V(J)` meet in a
scheme finite over `k`, and the restrictions to them of line bundles on `X` have
finite-dimensional cohomology, then so do `H⁰` and `H¹` of their restrictions to `V(I ⊓ J)`. -/
theorem finiteDimensional_cohomology_pullback_subschemeι_inf (L : InvertibleSheaf X) {i : ℕ}
    (hi : i < 2) : FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (I ⊓ J).subschemeι).obj L).obj i) := by
  obtain ⟨h₁, h₂⟩ := finiteDimensional_cohomology_pullback_toFixedRankOne I J hI hJ L
  have h := ((InvertibleSheaf.toFixedRankOne X).obj
    L).finiteDimensional_cohomology_pullback_subschemeι_inf k I J h₁ h₂ hi
  rwa [pullback_toFixedRankOne_obj_obj] at h

end InvertibleSheaf

namespace LineBundleClass

/-- The intersection number of the class of `L` with a closed subscheme `V(I)` is
`χ(L|_{V(I)}) - χ(𝒪_X|_{V(I)})`. -/
private lemma intersectionNumber_subschemeι_mk (I : X.IdealSheafData) (L : InvertibleSheaf X) :
    intersectionNumber k I.subschemeι (mk L) =
      eulerCharBelow k I.subscheme ((InvertibleSheaf.pullback I.subschemeι).obj L).obj 2 -
        eulerCharBelow k I.subscheme
          ((InvertibleSheaf.pullback I.subschemeι).obj (InvertibleSheaf.trivial X)).obj 2 := by
  have h := intersectionNumber_one k I.subschemeι
  rw [← mk_trivial, intersectionNumber_mk, InvertibleSheaf.eulerDegree_def] at h
  rw [intersectionNumber_mk, InvertibleSheaf.eulerDegree_def]
  linarith

include hI hJ in
/-- **Additivity of degrees on a union of closed subschemes.** If the closed subschemes `V(I)` and
`V(J)` of a scheme over `k` meet in a scheme finite over `k`, and the restrictions to them of line
bundles on `X` have finite-dimensional cohomology, then the degree of a line-bundle class on the
union `V(I ⊓ J)` is the sum of its degrees on `V(I)` and on `V(J)`. -/
theorem intersectionNumber_subschemeι_inf (a : LineBundleClass X) :
    intersectionNumber k (I ⊓ J).subschemeι a =
      intersectionNumber k I.subschemeι a + intersectionNumber k J.subschemeι a := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  have key (L : InvertibleSheaf X) := by
    obtain ⟨h₁, h₂⟩ := finiteDimensional_cohomology_pullback_toFixedRankOne I J hI hJ L
    have h := ((InvertibleSheaf.toFixedRankOne X).obj
      L).eulerCharBelow_pullback_subschemeι_inf_add k I J h₁ h₂ default
    rw [pullback_toFixedRankOne_obj_obj, pullback_toFixedRankOne_obj_obj,
      pullback_toFixedRankOne_obj_obj] at h
    exact h
  have hL := key L
  have hT := key (InvertibleSheaf.trivial X)
  rw [intersectionNumber_subschemeι_mk, intersectionNumber_subschemeι_mk,
    intersectionNumber_subschemeι_mk]
  linarith

omit [X.Over (Spec (.of k))] in
/-- The ideal sheaf of a finite union of closed subsets is the intersection of their ideal
sheaves. -/
private lemma finset_inf_vanishingIdeal (t : Finset (Closeds X)) :
    t.inf vanishingIdeal = vanishingIdeal (t.sup id) := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons W t hW ih => rw [Finset.inf_cons, Finset.sup_cons, ih, id, vanishingIdeal_sup]

variable [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]

/-- Additivity of degrees, with the finiteness of cohomology, over the union of a nonempty finite
family of closed subsets which pairwise meet in finitely many points. -/
private lemma intersectionNumber_finset_inf (s : Finset (Closeds X))
    (hmeet : ∀ Z ∈ s, ∀ W ∈ s, Z ≠ W → ((Z ⊓ W : Closeds X) : Set X).Finite)
    (hcoh : ∀ Z ∈ s, ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (vanishingIdeal Z).subschemeι).obj L).obj i))
    (t : Finset (Closeds X)) (ht : t.Nonempty) (hts : t ⊆ s) :
    (∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (t.inf vanishingIdeal).subschemeι).obj L).obj i)) ∧
    ∀ a : LineBundleClass X, intersectionNumber k (t.inf vanishingIdeal).subschemeι a =
      ∑ Z ∈ t, intersectionNumber k (vanishingIdeal Z).subschemeι a := by
  revert hts
  induction ht using Finset.Nonempty.cons_induction with
  | singleton W =>
    intro hts
    rw [Finset.inf_singleton]
    exact ⟨hcoh W (hts (Finset.mem_singleton_self W)), fun a ↦ (Finset.sum_singleton _ _).symm⟩
  | cons W t hW _ ih =>
    intro hts
    obtain ⟨ihc, ihd⟩ := ih ((Finset.subset_cons hW).trans hts)
    have hWs := hts (Finset.mem_cons_self W t)
    -- `V(I_W)` meets the union of the members of `t` in finitely many points.
    have : IsFinite ((vanishingIdeal W ⊔ t.inf vanishingIdeal).subschemeι ≫
        X ↘ Spec (.of k)) := by
      refine isFinite_subschemeι_comp_of_finite k _ ?_
      rw [support_sup, finset_inf_vanishingIdeal, Closeds.coe_inf, coe_support_vanishingIdeal,
        coe_support_vanishingIdeal, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion,
        Set.inter_iUnion₂]
      refine t.finite_toSet.biUnion fun Z hZ ↦ ?_
      exact hmeet W hWs Z (hts (Finset.subset_cons hW hZ)) (ne_of_mem_of_not_mem hZ hW).symm
    rw [Finset.inf_cons]
    refine ⟨fun L i hi ↦ InvertibleSheaf.finiteDimensional_cohomology_pullback_subschemeι_inf _ _
      (hcoh W hWs) ihc L hi, fun a ↦ ?_⟩
    rw [Finset.sum_cons, ← ihd a]
    exact intersectionNumber_subschemeι_inf _ _ (hcoh W hWs) ihc a

/-- **Additivity of degrees over a closed cover.** Let `X` be a reduced scheme, quasi-compact and
locally of finite type over a field `k`, covered by a nonempty finite family `s` of closed subsets
which pairwise meet in finitely many points, and such that line bundles restricted to the reduced
closed subschemes on the members of `s` have finite-dimensional `H⁰` and `H¹`. Then the degree of
a line-bundle class on `X` is the sum of its degrees on these reduced closed subschemes. For a
reduced proper curve, such as a nodal curve, and its irreducible components, this is the
additivity of degrees over the components. -/
theorem eulerDegree_eq_sum_intersectionNumber_vanishingIdeal [IsReduced X]
    [QuasiSeparatedSpace X] (s : Finset (Closeds X)) (hs : s.Nonempty) (hcover : s.sup id = ⊤)
    (hmeet : ∀ Z ∈ s, ∀ W ∈ s, Z ≠ W → ((Z ⊓ W : Closeds X) : Set X).Finite)
    (hcoh : ∀ Z ∈ s, ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (vanishingIdeal Z).subschemeι).obj L).obj i))
    (a : LineBundleClass X) :
    eulerDegree k a = ∑ Z ∈ s, intersectionNumber k (vanishingIdeal Z).subschemeι a := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have h := (intersectionNumber_finset_inf s hmeet hcoh s hs subset_rfl).2 a
  -- The members of `s` cover the reduced scheme `X`, so their ideal sheaves meet in `⊥`.
  have hbot : s.inf vanishingIdeal = (⊥ : X.IdealSheafData) := by
    rw [finset_inf_vanishingIdeal, hcover, vanishingIdeal_top, Scheme.nilradical_eq_bot]
  rw [hbot] at h
  rw [← h, intersectionNumber_def]
  exact (eulerDegree_pullback_of_isIso (k := k) _ (comp_over _ _) a).symm

end LineBundleClass

end

end TauCeti.AlgebraicGeometry
