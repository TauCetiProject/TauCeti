/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import TauCeti.CategoryTheory.Limits.Lattice
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.ModuleCat
public import TauCeti.Topology.Sheaves.Cech.Colimit

/-!
# Čech cohomology of locally zero presheaves on compact spaces

Let `P` be a presheaf of modules on a compact normal space `X` (for instance a compact Hausdorff
space) such that `P(∅) = 0` and every section of `P` is locally zero: a section over `W` restricts
to zero on some neighborhood of each point of `W`. This holds when the sheafification of `P`
vanishes. Then the Čech cohomology of `P` vanishes in every degree.

In fact every Čech cochain of every open cover, cocycle or not, is killed by a refinement
(`TauCeti.Topology.exists_cechComplexMap_f_eq_zero_of_locally_eq_zero`). Pass to a finite subcover
`U i`. Each point `x` has a neighborhood on which every component of the cochain, at a tuple of
indices whose members all contain `x`, restricts to zero. On a normal space there is a
point-neighborhood refinement by such neighborhoods `W x ⊆ U (r x)` for which `x ∈ U (r z)` whenever
`W x` meets `W z` (`TauCeti.Topology.PointOpenCover.exists_refinement_mem_of_mem_of_mem`). If
`W x₀ ∩ ⋯ ∩ W xₙ` is nonempty, then `x₀` lies in every `U (r xₖ)`, so the component at
`(r x₀, …, r xₙ)` vanishes on `W x₀`, which contains the intersection. If the intersection is
empty, the restricted component lies in `P(∅) = 0`.

The hypothesis `P(∅) = 0` cannot be dropped: on a two-point discrete space, the presheaf with
`P(∅) = ℤ` and all other values zero has zero sheafification but nonzero degree `1` Čech
cohomology. These vanishing results are the input for comparing the Čech cohomology of a presheaf
with that of its sheafification.

## Main results

* `TauCeti.Topology.exists_cechComplexMap_f_eq_zero_of_locally_eq_zero`: every Čech cochain of a
  locally zero presheaf with `P(∅) = 0`, for any small open cover of a compact normal space, is
  killed by some point-neighborhood refinement.
* `TauCeti.Topology.isZero_cechCohomology_obj_of_locally_eq_zero`: such a presheaf has zero Čech
  cohomology in every degree.
* `TauCeti.Topology.isZero_cechCohomology_obj_of_isZero_sheafify`: a presheaf of modules with
  `P(∅) = 0` and zero sheafification has zero Čech cohomology in every degree.

## References

* The Stacks Project, Cohomology of Sheaves, the shrinking argument in the proof of
  Lemma 20.16.2 (tag 09V2).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Topology

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} [CompactSpace X] [NormalSpace X] {R : Type u} [Ring R]
  (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)

/-- **Cochains of a locally zero presheaf die after refinement.** Let `P` be a presheaf of modules
on a compact normal space with `P(∅) = 0`, every section of which restricts to zero on a
neighborhood of each point of its domain. Then every degree `n` Čech cochain of `P` for a small
open cover `U` is sent to zero by the map induced by some point-neighborhood refinement of `U`. -/
theorem exists_cechComplexMap_f_eq_zero_of_locally_eq_zero (h₀ : IsZero (P.obj (op ⊥)))
    (hP : ∀ (W : Opens X) (s : P.obj (op W)) (x : X), x ∈ W →
      ∃ (V : Opens X) (hVW : V ≤ W), x ∈ V ∧ P.map (homOfLE hVW).op s = 0)
    {ι : Type u} (U : ι → Opens X) (hU : IsOpenCover U) (n : ℕ)
    (c : ((cechComplexFunctor U).obj P).X n) :
    ∃ (V : PointOpenCover X) (φ : V.toFormalCoproduct ⟶ FormalCoproduct.mk _ U),
      (TauCeti.CategoryTheory.cechComplexMap P φ).f n c = 0 := by
  classical
  obtain ⟨s, hs⟩ := hU.exists_finite_of_compactSpace
  -- at a point of the intersection of members of the finite subcover, the component of `c` at
  -- their tuple vanishes on a neighborhood `O a x` of the point
  choose O hOU hxO hO using fun (a : Fin (n + 1) → s) (x : X)
    (hx : x ∈ (∏ᶜ fun j ↦ U (a j) : Opens X)) ↦
      hP _ (Pi.π (fun b : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (b j))))
        (fun j ↦ (a j : ι)) c) x hx
  -- the points lying in all of these, of which there are finitely many, form a neighborhood of `x`
  have hN (x : X) : ∀ᶠ y in 𝓝 x, ∀ a hx, y ∈ O a x hx :=
    Filter.eventually_all.2 fun a ↦ Filter.eventually_all.2 fun hx ↦
      (O a x hx).isOpen.eventually_mem (hxO a x hx)
  obtain ⟨W, r, hWU, hWW⟩ :=
    PointOpenCover.exists_refinement_mem_of_mem_of_mem (fun i : s ↦ U i) hs hN
  let φ : W.toFormalCoproduct ⟶ FormalCoproduct.mk _ U :=
    ⟨fun x ↦ r x, fun x ↦ homOfLE (hWU x).1⟩
  refine ⟨W, φ, ?_⟩
  -- it suffices to show that the component at every tuple `b` of points vanishes; this goal is
  -- phrased through `Fan.mk`, whose projection at `⟨b⟩` is `Pi.π _ b` only up to unfolding the
  -- index type `(FormalCoproduct.cech _).I` to `Fin (n + 1) → X`, so `rw [cechComplexMap_f_π]`
  -- fails with an application type mismatch at `b` (and with `Concrete.limit_ext` instead,
  -- `rw [← ConcreteCategory.comp_apply]` finds no match), while `congr_hom` accepts the lemma up
  -- to definitional unfolding
  refine Concrete.isLimit_ext _ (productIsProduct
    fun b : Fin (n + 1) → X ↦ P.obj (op (∏ᶜ fun j ↦ W.opens (b j)))) _ _ fun ⟨b⟩ ↦ ?_
  refine (ConcreteCategory.congr_hom (TauCeti.CategoryTheory.cechComplexMap_f_π P φ n b) c).trans
    (Eq.trans ?_ (map_zero _).symm)
  by_cases hT : ∃ y, y ∈ (∏ᶜ fun j ↦ W.opens (b j) : Opens X)
  · obtain ⟨y, hy⟩ := hT
    have hyb (j : Fin (n + 1)) : y ∈ W.opens (b j) :=
      leOfHom (Pi.π (fun j ↦ W.opens (b j)) j) hy
    -- the first point `b 0` lies in every member `U (r (b j))`
    have hb : b 0 ∈ (∏ᶜ fun j ↦ U (r (b j)) : Opens X) := by
      rw [CompleteLattice.finite_product_eq_finset_image_inf, ← SetLike.mem_coe,
        Opens.coe_finset_inf]
      simpa using fun j ↦ hWW (b 0) y (b j) (hyb 0) (hyb j)
    -- so the component restricts to zero on `W (b 0)`, which contains the intersection
    have hTO : (∏ᶜ fun j ↦ W.opens (b j) : Opens X) ≤ O (fun j ↦ r (b j)) (b 0) hb :=
      (leOfHom (Pi.π (fun j ↦ W.opens (b j)) 0)).trans fun y hy ↦ (hWU (b 0)).2 hy _ hb
    have : (Limits.Pi.map fun j ↦ φ.φ (b j)) = homOfLE hTO ≫ homOfLE (hOU _ (b 0) hb) :=
      Subsingleton.elim _ _
    rw [this, op_comp, P.map_comp]
    exact (congrArg (P.map (homOfLE hTO).op).hom (hO _ (b 0) hb)).trans (map_zero _)
  · -- an empty intersection has no nonzero sections
    have : IsZero (P.obj (op (∏ᶜ fun j ↦ W.opens (b j) : Opens X))) := by
      rwa [show (∏ᶜ fun j ↦ W.opens (b j) : Opens X) = ⊥ from
        eq_bot_iff.2 fun y hy ↦ (hT ⟨y, hy⟩).elim]
    exact (ModuleCat.subsingleton_of_isZero this).elim _ _

/-- **Locally zero presheaves have no Čech cohomology.** On a compact normal space, a presheaf of
modules with `P(∅) = 0`, every section of which restricts to zero on a neighborhood of each point
of its domain, has zero Čech cohomology in every degree. -/
theorem isZero_cechCohomology_obj_of_locally_eq_zero (h₀ : IsZero (P.obj (op ⊥)))
    (hP : ∀ (W : Opens X) (s : P.obj (op W)) (x : X), x ∈ W →
      ∃ (V : Opens X) (hVW : V ≤ W), x ∈ V ∧ P.map (homOfLE hVW).op s = 0) (n : ℕ) :
    IsZero ((cechCohomology X (ModuleCat.{u} R) n).obj P) := by
  refine TauCeti.CategoryTheory.isZero_cechCohomology_obj_of_forall_exists_homologyMap_eq_zero
    _ _ n P fun U z ↦ ?_
  -- a class is represented by a cocycle, which some refinement kills
  let K := (cechComplexFunctor U.opens).obj P
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance z
  obtain ⟨V, φ, hc⟩ :=
    exists_cechComplexMap_f_eq_zero_of_locally_eq_zero P h₀ hP U.opens U.isOpenCover n
      (K.iCycles n c)
  refine ⟨V, ⟨φ⟩, φ, ?_⟩
  have h : HomologicalComplex.cyclesMap (TauCeti.CategoryTheory.cechComplexMap P φ) n c = 0 := by
    apply (ModuleCat.mono_iff_injective (HomologicalComplex.iCycles _ n)).1 inferInstance
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
      hc, map_zero]
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, h, map_zero]

/-- **Presheaves with zero sheafification have no Čech cohomology.** On a compact normal space,
for instance a compact Hausdorff space, a presheaf of modules `P` with `P(∅) = 0` whose
sheafification vanishes has zero Čech cohomology in every degree. The hypothesis `P(∅) = 0` is
needed: the Čech complex of a cover sees the values of `P` on empty intersections. -/
theorem isZero_cechCohomology_obj_of_isZero_sheafify
    [HasWeakSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} R)]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective (ModuleCat.{u} R)]
    (h₀ : IsZero (P.obj (op ⊥))) (hP : IsZero (sheafify (Opens.grothendieckTopology X) P))
    (n : ℕ) : IsZero ((cechCohomology X (ModuleCat.{u} R) n).obj P) := by
  refine isZero_cechCohomology_obj_of_locally_eq_zero P h₀ (fun W s x hx ↦ ?_) n
  -- `s` and `0` have the same image in the zero sheafification, so they agree locally
  obtain ⟨V, f, hf, hxV⟩ := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) P) s 0
    ((ModuleCat.subsingleton_of_isZero (hP.obj _)).elim _ _) x hx
  exact ⟨V, leOfHom f, hxV, hf.trans (map_zero _)⟩

end TauCeti.Topology
