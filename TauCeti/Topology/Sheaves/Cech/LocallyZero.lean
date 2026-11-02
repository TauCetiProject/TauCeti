/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import TauCeti.Topology.Sheaves.Cech.Colimit

/-!
# Locally zero presheaves have no Čech cohomology on compact normal spaces

Let `P` be a presheaf of `R`-modules on a topological space `X` whose sections are all locally
zero: every section over `U` restricts to zero on some neighborhood of each point of `U`. For the
underlying presheaf of abelian groups this says exactly that its sheafification vanishes
(`TopCat.Presheaf.isZero_presheafToSheaf_obj_iff`). Suppose moreover that `P(∅) = 0`. If `X` is
compact and normal, for instance compact Hausdorff, then the Čech cohomology of `P`, the colimit
over all open covers, vanishes in every degree (`isZero_cechCohomology_obj_of_locallyZero`).

The vanishing holds already at the level of cochains of finite covers: on a normal space, every
Čech cochain of `P` for a finite open cover becomes zero after pulling it back along a suitable
point-neighborhood refinement (`exists_cechComplexMap_f_apply_eq_zero`). The refinement is the
one of `TauCeti.Topology.PointOpenCover.exists_refinement_mem_of_mem_of_mem`, built from a
shrinking of the cover and from neighborhoods on which the finitely many components of the
cochain vanish: whenever the neighborhoods of the points of a tuple `b` meet, the first point
`b 0` lies in all the members of the cover indexed by the refined tuple, so the corresponding
component of the cochain vanishes on the neighborhood of `b 0`; otherwise the intersection is
empty and the component lies in `P(∅) = 0`. On a compact space every cover has a finite
subcover, so every Čech cohomology class dies in the colimit.

The hypothesis `P(∅) = 0` cannot be dropped: on a two-point discrete space, the presheaf with
`P(∅) = ℤ` and all other values zero is locally zero, but its Čech cohomology for the cover by
the two points is `ℤ` in degree `1`. The kernel and the cokernel of the map from a presheaf to its
sheafification are locally zero, which makes the vanishing theorem the input for comparing the
Čech cohomology of a presheaf with that of its sheafification.

## Main results

* `TauCeti.Topology.exists_cechComplexMap_f_apply_eq_zero`: on a normal space, every Čech cochain
  of a locally zero presheaf with `P(∅) = 0` for a finite open cover is killed by some
  point-neighborhood refinement.
* `TauCeti.Topology.isZero_cechCohomology_obj_of_locallyZero`: on a compact normal space, the Čech
  cohomology of such a presheaf vanishes in every degree.

## References

* The Stacks Project, Cohomology of Sheaves, the shrinking argument in the proof of
  Lemma 20.16.2 (tag 09V2).
* R. Godement, *Topologie algébrique et théorie des faisceaux*, Hermann, 1958, Chapter II, §5.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite TauCeti.CategoryTheory

universe v u

namespace TauCeti.Topology

variable {X : TopCat.{u}} {R : Type v} [Ring R] {P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R}

/-- On a normal space, let `P` be a presheaf of modules with `P(∅) = 0` all of whose sections are
locally zero. Then every Čech cochain `c` of `P` for a finite open cover `U` is killed by pulling
it back along some refinement of `U` by a point-neighborhood cover. -/
theorem exists_cechComplexMap_f_apply_eq_zero [NormalSpace X]
    (h₀ : IsZero (P.obj (op ⊥)))
    (hP : ∀ (x : X) (U : Opens X) (s : P.obj (op U)), x ∈ U →
      ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ P.map (homOfLE h).op s = 0)
    {ι : Type u} [Finite ι] {U : ι → Opens X} (hU : IsOpenCover U) {n : ℕ}
    (c : ((cechComplexFunctor U).obj P).X n) :
    ∃ (W : PointOpenCover X) (φ : W.toFormalCoproduct ⟶ FormalCoproduct.mk ι U),
      (cechComplexMap P φ).f n c = 0 := by
  classical
  -- the component of `c` at a tuple `a`, restricted to the intersection `O a` of the `U (a j)`
  let O (a : Fin (n + 1) → ι) : Opens X :=
    ⟨⋂ j, (U (a j) : Set X), isOpen_iInter_of_finite fun j ↦ (U (a j)).isOpen⟩
  let ιO (a : Fin (n + 1) → ι) : O a ⟶ ∏ᶜ fun j ↦ U (a j) :=
    Pi.lift fun j ↦ homOfLE (Set.iInter_subset _ j)
  let r (a : Fin (n + 1) → ι) : P.obj (op (O a)) :=
    P.map (ιO a).op (Pi.π (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) a c)
  -- a neighborhood `N x a` of `x` on which `r a` vanishes, whenever `x ∈ O a`
  have hN (x : X) (a : Fin (n + 1) → ι) : ∃ V : Opens X, x ∈ V ∧
      ∀ hx : x ∈ O a, ∃ h : V ≤ O a, P.map (homOfLE h).op (r a) = 0 := by
    by_cases hx : x ∈ O a
    · obtain ⟨V, h, hxV, hV⟩ := hP x _ (r a) hx
      exact ⟨V, hxV, fun _ ↦ ⟨h, hV⟩⟩
    · exact ⟨⊤, trivial, fun h ↦ (hx h).elim⟩
  choose N hxN hN using hN
  let N' : PointOpenCover X :=
    ⟨fun x ↦ ⟨⋂ a, (N x a : Set X), isOpen_iInter_of_finite fun a ↦ (N x a).isOpen⟩,
      fun x ↦ Set.mem_iInter.2 (hxN x)⟩
  obtain ⟨W, τ, hWN, hWU, hτ⟩ := PointOpenCover.exists_refinement_mem_of_mem_of_mem hU N'
  let φ : FormalCoproduct.mk X W.opens ⟶ FormalCoproduct.mk ι U := ⟨τ, fun x ↦ homOfLE (hWU x)⟩
  refine ⟨W, φ, ?_⟩
  refine Concrete.limit_ext _ _ 0 fun ⟨b⟩ ↦ ?_
  have key := ConcreteCategory.congr_hom (cechComplexMap_f_π P φ n b) c
  refine (key.trans ?_).trans (map_zero _).symm
  by_cases hQ : ∃ y, y ∈ (∏ᶜ fun j ↦ W.opens (b j) : Opens X)
  · -- if the members `W (b j)` meet, then `b 0 ∈ O (τ ∘ b)` and the component vanishes on
    -- `W (b 0) ⊆ N (b 0) (τ ∘ b)`
    obtain ⟨y, hy⟩ := hQ
    have hyW (j : Fin (n + 1)) : y ∈ W.opens (b j) := (Pi.π (fun j ↦ W.opens (b j)) j).le hy
    have hx₀ : b 0 ∈ O (τ ∘ b) := Set.mem_iInter.2 fun j ↦ hτ _ _ y (hyW 0) (hyW j)
    obtain ⟨h, hr⟩ := hN (b 0) (τ ∘ b) hx₀
    have hle : (∏ᶜ fun j ↦ W.opens (b j)) ≤ N (b 0) (τ ∘ b) :=
      (Pi.π (fun j ↦ W.opens (b j)) 0).le.trans
        ((hWN (b 0)).trans fun _ hz ↦ Set.mem_iInter.1 hz (τ ∘ b))
    have e : P.map (Limits.Pi.map fun j ↦ φ.φ (b j)).op =
        P.map (ιO (τ ∘ b)).op ≫ P.map (homOfLE h).op ≫ P.map (homOfLE hle).op := by
      rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
      exact congrArg (fun g ↦ P.map (Quiver.Hom.op g)) (Subsingleton.elim _ _)
    rw [e]
    exact (congrArg (P.map (homOfLE hle).op) hr).trans (map_zero _)
  · -- otherwise the component lies in a module isomorphic to `P(∅) = 0`
    have hbot : (∏ᶜ fun j ↦ W.opens (b j)) = ⊥ := eq_bot_iff.2 fun y hy ↦ (hQ ⟨y, hy⟩).elim
    have hQ₀ := h₀.of_iso (P.mapIso (eqToIso hbot).op).symm
    exact (ModuleCat.subsingleton_of_isZero hQ₀).elim _ _

/-- **Locally zero presheaves have no Čech cohomology.** On a compact normal space, for instance a
compact Hausdorff space, let `P` be a presheaf of modules with `P(∅) = 0` all of whose sections
are locally zero. Then the Čech cohomology of `P` vanishes in every degree. -/
theorem isZero_cechCohomology_obj_of_locallyZero [CompactSpace X] [NormalSpace X]
    (h₀ : IsZero (P.obj (op ⊥)))
    (hP : ∀ (x : X) (U : Opens X) (s : P.obj (op U)), x ∈ U →
      ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ P.map (homOfLE h).op s = 0) (n : ℕ) :
    IsZero ((cechCohomology X (ModuleCat.{u} R) n).obj P) := by
  -- a class `[k]` on a point-neighborhood cover `U` is pulled back to a finite subcover, whose
  -- refinement `W` given by `exists_cechComplexMap_f_apply_eq_zero` kills the cocycle `k`
  refine (IsZero.iff_id_eq_zero _).2 (cechCohomology_obj_hom_ext fun U ↦ ?_)
  rw [Category.comp_id, comp_zero]
  refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
  obtain ⟨k, rfl⟩ := (ModuleCat.epi_iff_surjective
    (((cechComplexFunctor U.opens).obj P).homologyπ n)).1 inferInstance z
  obtain ⟨s, hs⟩ := U.isOpenCover.exists_finite_of_compactSpace
  let ψ : FormalCoproduct.mk s (fun i ↦ U.opens i.1) ⟶ U.toFormalCoproduct :=
    ⟨Subtype.val, fun _ ↦ 𝟙 _⟩
  obtain ⟨W, φ, hφ⟩ := exists_cechComplexMap_f_apply_eq_zero h₀ hP hs
    ((cechComplexMap P ψ).f n (((cechComplexFunctor U.opens).obj P).iCycles n k))
  have hk : HomologicalComplex.cyclesMap (cechComplexMap P (φ ≫ ψ)) n k = 0 := by
    apply (ModuleCat.mono_iff_injective (HomologicalComplex.iCycles _ n)).1 inferInstance
    have hnat := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (cechComplexMap P (φ ≫ ψ)) n) k
    simp only [ConcreteCategory.comp_apply] at hnat
    rw [hnat]
    simp only [cechComplexMap_comp, HomologicalComplex.comp_f, ConcreteCategory.comp_apply, hφ,
      map_zero]
  have key : HomologicalComplex.homologyMap (cechComplexMap P (φ ≫ ψ)) n
      (((cechComplexFunctor U.opens).obj P).homologyπ n k) = 0 :=
    (ConcreteCategory.comp_apply _ _ k).symm.trans <| by
      rw [HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply, hk, map_zero]
  replace key : (cechComplexHomologyMap (ModuleCat.{u} R) n (φ ≫ ψ)).app P
      (((cechComplexFunctor U.opens).obj P).homologyπ n k) = 0 :=
    (ConcreteCategory.congr_hom (cechComplexHomologyMap_app _ n (φ ≫ ψ) P) _).trans key
  rw [← (NatTrans.comp_app _ _ P).symm.trans (NatTrans.congr_app
    (cechComplexHomologyMap_comp_cechCohomologyι (ModuleCat.{u} R) PointOpenCover.toFormalCoproduct
      (fun _ _ h ↦ h) n (⟨φ ≫ ψ⟩ : U ≤ W) (φ ≫ ψ)) P)]
  exact (ConcreteCategory.comp_apply _ _ _).trans <|
    ((congrArg _ key).trans (map_zero _)).trans (LinearMap.zero_apply _).symm

end TauCeti.Topology
