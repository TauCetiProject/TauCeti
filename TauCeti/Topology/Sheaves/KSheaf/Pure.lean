/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import TauCeti.Topology.Sheaves.KSheaf.Homotopy
public import TauCeti.Topology.Sheaves.KSheaf.ToPresheaf
public import TauCeti.Topology.Sets.Compacts

/-!
# Pure homotopy K-sheaves

A homotopy K-sheaf `F` of cochain complexes on a Hausdorff space `X`
(`TopCat.KPresheaf.IsHomotopyKSheaf`) is *pure* (Pardon, Definition A.5.1;
`TopCat.KPresheaf.IsPure`) if

* its stalks `F({x})` have cohomology only in degree `0`, and
* its cohomology is locally bounded below: every point has a neighbourhood `U` and an integer `N`
  such that `H^i(F(K)) = 0` for all compact `K ⊆ U` and all `i ≤ N`.

In Pardon's construction of virtual fundamental cycles, the partial virtual cochain complexes of a
locally orientable implicit atlas are pure, and purity is what identifies their cohomology with
Čech cohomology of the sheaf `H^0 F`. The first step is Pardon's Lemma A.5.3, proved here for
complexes of modules over a ring on a locally compact Hausdorff space: a pure homotopy K-sheaf has
no cohomology in negative degrees on any compact set (`TopCat.KPresheaf.IsPure.exactAt_of_neg`),
and its cohomology in degree `0` is a K-sheaf
(`TopCat.KPresheaf.IsPure.isKSheaf_homology_zero`).

The proof rests on two facts about homotopy K-sheaves.

* **Stalkwise vanishing propagates up one degree**
  (`TopCat.KPresheaf.IsHomotopyKSheaf.exactAt_of_forall_exactAt_singleton`). Let `W ⊆ X` be a
  set such that `H^i(F(K)) = 0` for all compact `K ⊆ W`. If the stalks `H^(i + 1)(F({x}))` vanish
  for `x ∈ W`, then `H^(i + 1)(F(K)) = 0` for all compact `K ⊆ W`. A class on `K` extends to a
  compact neighbourhood of `K`, and near each point of `K` it then vanishes, because cohomology
  commutes with the colimit over compact neighbourhoods. Finitely many of these neighbourhoods
  cover `K`, and by the Mayer–Vietoris axiom and the vanishing in degree `i` a class on a union of
  two compact sets in `W` is determined by its restrictions to them. The same argument shows that
  a K-sheaf of modules with zero stalks is zero
  (`TopCat.KPresheaf.IsKSheaf.isZero_obj_of_forall_isZero_singleton`).
* **Vanishing below a degree is local**
  (`TopCat.KPresheaf.IsHomotopyKSheaf.exactAt_of_forall_mem_nhds`): if every point has a
  neighbourhood on whose compact subsets the cohomology vanishes in degrees `≤ n`, then it vanishes
  in degrees `≤ n` on every compact set. A compact set is a finite union of compact sets inside
  such neighbourhoods, and the Mayer–Vietoris axiom glues the vanishing.

For a pure `F`, the first fact, applied near a point from its local lower bound `N` up to degree
`-1`, gives vanishing in negative degrees near every point, and the second makes it global. Then
Pardon's Lemma A.2.12 (`TopCat.KPresheaf.IsHomotopyKSheaf.isKSheaf_homology`) applies in degree
`0`.

The stalkwise argument chases elements through filtered colimits, so it is stated for modules over
a ring rather than in an arbitrary abelian category: in a general Grothendieck abelian category an
object mapping to zero in a filtered colimit need not already map to zero at some stage.

## Main definitions

* `TopCat.KPresheaf.IsPure`: pure homotopy K-sheaves.

## Main results

* `TopCat.KPresheaf.IsHomotopyKSheaf.exactAt_of_forall_exactAt_singleton`: stalkwise vanishing
  propagates one degree up.
* `TopCat.KPresheaf.IsKSheaf.isZero_obj_of_forall_isZero_singleton`: a K-sheaf of modules with
  zero stalks is zero.
* `TopCat.KPresheaf.IsPure.exactAt_of_neg`, `TopCat.KPresheaf.IsPure.isKSheaf_homology_zero`:
  Pardon's Lemma A.5.3.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Appendix A.5, Definition A.5.1 and
  Lemma A.5.3.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace HomologicalComplex Topology

universe w v u

namespace TopCat.KPresheaf

variable {X : TopCat.{w}} [T2Space X]

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] {F : KPresheaf (CochainComplex C ℤ) X}

/-- A K-presheaf `F` of cochain complexes on a Hausdorff space is *pure* (Pardon,
Definition A.5.1) if it is a homotopy K-sheaf, the cohomology of each stalk `F({x})` vanishes
outside degree `0`, and its cohomology is locally bounded below: every point has a neighbourhood
`U` and an integer `N` such that the cohomology of `F(K)` vanishes in degrees `≤ N` for every
compact `K ⊆ U`. -/
structure IsPure (F : KPresheaf (CochainComplex C ℤ) X) : Prop extends F.IsHomotopyKSheaf where
  exactAt_singleton (x : X) {i : ℤ} (hi : i ≠ 0) : (F.obj (op {x})).ExactAt i
  exists_mem_nhds_exactAt (x : X) : ∃ U ∈ 𝓝 x, ∃ N : ℤ, ∀ K : Compacts X, (K : Set X) ⊆ U →
    ∀ i ≤ N, (F.obj (op K)).ExactAt i

end Abelian

section Module

variable {R : Type w} [Ring R]

/-- The restrictions of `G` form a pullback square on every bicartesian square of compact sets
whose union lies in `W`. -/
private def IsPullbackOn (G : KPresheaf (ModuleCat.{w} R) X) (W : Set X) : Prop :=
  ∀ ⦃K₁ K₂ K₃ K₄ : Compacts X⦄ (h : Lattice.BicartSq K₁ K₂ K₃ K₄), (K₄ : Set X) ⊆ W →
    IsPullback (G.map (opHomOfLE h.le₂₄)) (G.map (opHomOfLE h.le₃₄)) (G.map (opHomOfLE h.le₁₂))
      (G.map (opHomOfLE h.le₁₃))

/-- A class on a compact set `K ⊆ W` vanishes if its restrictions to the pieces `K ∩ L a` of a
finite cover vanish, provided restrictions to two compact sets form a pullback square on their
union inside `W`. -/
private theorem eq_zero_of_forall_map_inf_eq_zero (G : KPresheaf (ModuleCat.{w} R) X)
    {W : Set X} (hbot : IsZero (G.obj (op ⊥)))
    (hpb : IsPullbackOn G W)
    {ι : Type*} (L : ι → Compacts X) (s : Finset ι) :
    ∀ K : Compacts X, (K : Set X) ⊆ W → (K : Set X) ⊆ ⋃ a ∈ s, (L a : Set X) →
      ∀ x : G.obj (op K), (∀ a ∈ s, (G.map (opHomOfLE (inf_le_left : K ⊓ L a ≤ K))).hom x = 0) →
        x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro K _ hK x _
    obtain rfl : K = ⊥ := Compacts.ext (by simpa using hK)
    exact (ModuleCat.subsingleton_of_isZero hbot).elim _ _
  | insert a s _ ih =>
    intro K hKW hK x hx
    -- split `K` into `K ∩ L a` and `K ∩ ⋃ s`
    let K' : Compacts X := K ⊓ s.sup L
    have sq : Lattice.BicartSq ((K ⊓ L a) ⊓ K') (K ⊓ L a) K' K := by
      refine ⟨Compacts.ext ?_, rfl⟩
      simp only [K', Compacts.coe_sup, Compacts.coe_inf, Compacts.coe_finset_sup,
        Finset.sup_set_eq_biUnion, ← Set.inter_union_distrib_left]
      simpa [Finset.set_biUnion_insert] using hK
    -- a class killed by both restrictions of a pullback square is zero
    refine Types.ext_of_isPullback ((CategoryTheory.forget _).map_isPullback (hpb sq hKW))
      (x₁ := x) (y₁ := 0) (by simpa using hx a (Finset.mem_insert_self a s)) ?_
    suffices (G.map (opHomOfLE sq.le₃₄)).hom x = 0 by simpa using this
    refine ih K' (by rw [Compacts.coe_inf]; exact Set.inter_subset_left.trans hKW)
      (by simp [K', Compacts.coe_finset_sup])
      _ fun b hb ↦ ?_
    -- restricting from `K` to `K' ∩ L b` factors through `K ∩ L b`
    rw [map_opHomOfLE_comp_map_opHomOfLE_apply, ← map_opHomOfLE_comp_map_opHomOfLE_apply G
      (inf_le_left : K ⊓ L b ≤ K) (inf_le_inf_right _ inf_le_left),
      hx b (Finset.mem_insert_of_mem hb), map_zero]

variable [WeaklyLocallyCompactSpace X]

/-- A K-presheaf of modules vanishes on the compact subsets of `W` if it vanishes at `∅`, its
values are colimits over compact neighbourhoods, its stalks at the points of `W` vanish, and
restrictions to two compact sets form a pullback square on their union inside `W`. -/
private theorem isZero_obj_of_forall_isZero_singleton_aux (G : KPresheaf (ModuleCat.{w} R) X)
    {W : Set X} (hbot : IsZero (G.obj (op ⊥)))
    (hpb : IsPullbackOn G W)
    (hcolim : ∀ K : Compacts X, Nonempty (IsColimit (G.coconeOfCompacts K)))
    (hstalk : ∀ x ∈ W, IsZero (G.obj (op {x}))) (K : Compacts X) (hKW : (K : Set X) ⊆ W) :
    IsZero (G.obj (op K)) := by
  suffices h : ∀ x : G.obj (op K), x = 0 by
    have : Subsingleton (G.obj (op K)) := ⟨fun x y ↦ (h x).trans (h y).symm⟩
    exact ModuleCat.isZero_of_subsingleton _
  intro x
  -- `x` is the restriction of a class `y` on a compact neighbourhood `L` of `K`
  obtain ⟨hc⟩ := hcolim K
  obtain ⟨⟨L, hL⟩, y, rfl⟩ := Concrete.isColimit_exists_rep _ hc x
  rw [coconeOfCompacts_ι_app]
  -- near each point `p` of `K`, the class `y` vanishes, since the stalk at `p` does
  have hloc : ∀ p ∈ K, ∃ M : Compacts X, (M : Set X) ∈ 𝓝 p ∧
      ∃ hM : M ≤ L, (G.map (opHomOfLE hM)).hom y = 0 := by
    intro p hp
    obtain ⟨hcp⟩ := hcolim {p}
    have hLp : L ∈ ({p} : Compacts X).compactNhds := by
      intro q
      rw [(Compacts.mem_singleton _ _).1 q.property]
      exact hL ⟨p, hp⟩
    obtain ⟨k, f, _, hfg⟩ := Concrete.isColimit_exists_of_rep_eq _ hcp
      (i := op ⟨L, hLp⟩) (j := op ⟨L, hLp⟩) y 0
      ((ModuleCat.subsingleton_of_isZero (hstalk p (hKW hp))).elim _ _)
    refine ⟨k.unop, k.unop.property ⟨p, (Compacts.mem_singleton _ _).2 rfl⟩, leOfHom f.unop, ?_⟩
    rw [Subsingleton.elim (opHomOfLE _) ((Set.mono_coe _).functor.map f.unop).op]
    simpa using hfg
  choose! M hM hML hMy using hloc
  obtain ⟨t, ht, hKt⟩ := K.isCompact.elim_nhds_subcover (fun p ↦ M p) hM
  refine eq_zero_of_forall_map_inf_eq_zero G hbot hpb M t K hKW hKt
    ((G.map (opHomOfLE (Compacts.subset_of_mem_compactNhds hL))).hom y) fun p hp ↦ ?_
  -- restricting from `L` to `K ∩ M p` factors through `M p`
  refine (map_opHomOfLE_comp_map_opHomOfLE_apply G (Compacts.subset_of_mem_compactNhds hL)
    inf_le_left y).trans ?_
  rw [← map_opHomOfLE_comp_map_opHomOfLE_apply G (hML p (ht p hp)) inf_le_right, hMy p (ht p hp),
    map_zero]

/-- A K-sheaf of modules on a locally compact Hausdorff space whose stalks `G({x})` all vanish is
zero. -/
theorem IsKSheaf.isZero_obj_of_forall_isZero_singleton {G : KPresheaf (ModuleCat.{w} R) X}
    (hG : G.IsKSheaf) (h : ∀ x : X, IsZero (G.obj (op {x}))) (K : Compacts X) :
    IsZero (G.obj (op K)) :=
  isZero_obj_of_forall_isZero_singleton_aux G (W := Set.univ)
    hG.nonempty_isTerminal.some.isZero (fun _ _ _ _ h' _ ↦ hG.isPullback h')
    hG.nonempty_isColimit_coconeOfCompacts (fun x _ ↦ h x) K (Set.subset_univ _)

/-- In a homotopy K-sheaf of complexes of modules on a locally compact Hausdorff space, let `W` be
a set such that the cohomology of `F(K)` vanishes in degree `i` for every compact `K ⊆ W`. If the
cohomology of the stalks `F({x})` vanishes in degree `i + 1` at every point of `W`, then the
cohomology of `F(K)` vanishes in degree `i + 1` for every compact `K ⊆ W`. -/
theorem IsHomotopyKSheaf.exactAt_of_forall_exactAt_singleton
    {F : KPresheaf (CochainComplex (ModuleCat.{w} R) ℤ) X} (hF : F.IsHomotopyKSheaf) {W : Set X}
    {i j : ℤ} (hij : i + 1 = j) (hi : ∀ K : Compacts X, (K : Set X) ⊆ W → (F.obj (op K)).ExactAt i)
    (hj : ∀ x ∈ W, (F.obj (op {x})).ExactAt j) (K : Compacts X) (hKW : (K : Set X) ⊆ W) :
    (F.obj (op K)).ExactAt j := by
  rw [exactAt_iff_isZero_homology]
  refine isZero_obj_of_forall_isZero_singleton_aux (F ⋙ homologyFunctor _ _ j)
    (hF.acyclic_bot j).isZero_homology (fun _ _ _ _ h hW ↦ ?_) (fun K ↦ ?_)
    (fun x hx ↦ (exactAt_iff_isZero_homology _ _).1 (hj x hx)) K hKW
  · have := hF.quasiIso_mayerVietorisDesc h
    exact F.isPullback_homologyMap h hij
      (hi _ ((SetLike.coe_subset_coe.2 (h.le₁₂.trans h.le₂₄)).trans hW))
  · obtain ⟨_, hc, _⟩ := hF.exists_isColimit_quasiIso_desc K
    exact F.nonempty_isColimit_coconeOfCompacts_homology K hc j

/-- **Pardon, Lemma A.5.3.** A pure homotopy K-sheaf of complexes of modules on a locally compact
Hausdorff space has no cohomology in negative degrees on any compact set. -/
theorem IsPure.exactAt_of_neg {F : KPresheaf (CochainComplex (ModuleCat.{w} R) ℤ) X}
    (hF : F.IsPure) (K : Compacts X) {i : ℤ} (hi : i < 0) : (F.obj (op K)).ExactAt i := by
  refine hF.exactAt_of_forall_mem_nhds (n := -1) (fun x ↦ ?_) K (by omega)
  obtain ⟨U, hU, N, hN⟩ := hF.exists_mem_nhds_exactAt x
  refine ⟨U, hU, fun K' hK' i' hi' ↦ ?_⟩
  -- near `x`, the vanishing propagates from degree `N` up to degree `-1` through the stalks
  have step (k : ℕ) : ∀ i ≤ N + k, i < 0 → ∀ K : Compacts X, (K : Set X) ⊆ U →
      (F.obj (op K)).ExactAt i := by
    induction k with
    | zero => exact fun i hi _ K hK ↦ hN K hK i (by omega)
    | succ k ih =>
      intro i hi hi0 K hK
      by_cases hik : i ≤ N + k
      · exact ih i hik hi0 K hK
      · exact hF.exactAt_of_forall_exactAt_singleton (sub_add_cancel i 1)
          (fun K hK ↦ ih (i - 1) (by omega) (by omega) K hK)
          (fun x _ ↦ hF.exactAt_singleton x hi0.ne) K hK
  exact step (i' - N).toNat i' (by omega) (by omega) K' hK'

/-- **Pardon, Lemma A.5.3.** The cohomology in degree `0` of a pure homotopy K-sheaf of complexes
of modules on a locally compact Hausdorff space, `K ↦ H^0(F(K))`, is a K-sheaf. -/
theorem IsPure.isKSheaf_homology_zero {F : KPresheaf (CochainComplex (ModuleCat.{w} R) ℤ) X}
    (hF : F.IsPure) : IsKSheaf (F ⋙ homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) 0) :=
  IsHomotopyKSheaf.isKSheaf_homology F hF.toIsHomotopyKSheaf (neg_add_cancel 1) fun K ↦
    hF.exactAt_of_neg K (by omega)

end Module

end TopCat.KPresheaf
