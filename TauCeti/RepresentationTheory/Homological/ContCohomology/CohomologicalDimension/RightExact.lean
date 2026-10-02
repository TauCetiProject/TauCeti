/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ClosedSubgroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.AllDegrees
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Right exactness of `Hⁿ` on finite discrete `G`-modules killed by `p` kills `Hⁿ⁺¹`

Let `G` be a profinite group, `p` a natural number and `n` a degree. Suppose that the functor
`Hⁿ(G, -)` is right exact on the finite discrete `G`-modules killed by `p`: for every short exact
sequence `0 → A → B → C → 0` of such modules the map `Hⁿ(G, B) → Hⁿ(G, C)` is surjective. Then
`Hⁿ⁺¹(G, M)` vanishes for every finite discrete `G`-module `M` killed by `p`.

The argument is the standard effaceability argument. A class `x` of `Hⁿ⁺¹(G, M)` restricts to zero
on some open subgroup `V` of `G` (`TauCeti.ContinuousCohomology.exists_openSubgroup_res_eq_zero`).
The unit `M → Coind_V^G M` of coinduction embeds `M` into a module which is again finite and killed
by `p`, with a finite quotient `Q` killed by `p`, and under Shapiro's lemma the image of `x` in
`Hⁿ⁺¹(G, Coind_V^G M) ≅ Hⁿ⁺¹(V, M)` is its restriction to `V`
(`TauCeti.ContinuousCohomology.coeffMap_unit_comp_shapiroMap`), which is zero. So `x` is the
image under the connecting map of a class of `Hⁿ(G, Q)`, and right exactness lifts that class to
`Hⁿ(G, Coind_V^G M)`, where the connecting map kills it. Hence `x = 0`.

For a pro-`p` group this bounds the `p`-cohomological dimension: `cd_p G ≤ n`
(`TauCeti.IsProP.cohomologicalDimensionAt_le_of_forall_coeffMap_proj_surjective`, in
`TauCeti.Topology.Algebra.Group.Profinite.ProP.CohomologicalDimension`). This is the final step of
Tate's proof that an infinite Demushkin group has cohomological dimension `2`, recorded in Serre's
Bourbaki exposé, §9.1: the duality pairings make `H²(G, -)` right exact on the finite
`𝔽_p[G]`-modules, and right exactness kills `H³`.

## Main results

* `TauCeti.subsingleton_continuousCohomology_succ_of_forall_coeffMap_proj_surjective`: if
  `Hⁿ(G, -)` is right exact on the finite discrete `G`-modules killed by `p`, then `Hⁿ⁺¹(G, M)`
  vanishes for every such module `M`.

## References

* J.-P. Serre, *Structure de certains pro-`p`-groupes (d'après Demuškin)*, Séminaire Bourbaki,
  exp. 252 (1963), §9.1, for the argument of Tate.
* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.1, Prop. 11, and §3.3, for the effaceability
  arguments.
-/

public section

open CategoryTheory TauCeti.ContCohomology TauCeti.ContinuousCohomology

namespace TauCeti

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Right exactness of `Hⁿ` on finite discrete `G`-modules killed by `p` kills `Hⁿ⁺¹`.** Let `G`
be a profinite group and `p` a natural number. If for every short exact sequence `0 → A → B → C → 0`
of finite discrete `G`-modules killed by `p` the map `Hⁿ(G, B) → Hⁿ(G, C)` is surjective, then
`Hⁿ⁺¹(G, M)` vanishes for every finite discrete `G`-module `M` killed by `p`. -/
theorem subsingleton_continuousCohomology_succ_of_forall_coeffMap_proj_surjective {n : ℕ}
    (h : ∀ (A B C : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
      [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
      [DistribMulAction G B] [ContinuousSMul G B] [Finite B]
      [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
      [DistribMulAction G C] [ContinuousSMul G C] [Finite C]
      (S : DiscreteShortExact G A B C),
      (∀ a : A, p • a = 0) → (∀ b : B, p • b = 0) → (∀ c : C, p • c = 0) →
      Function.Surjective
        (coeffMap (ofDiscreteModuleMap S.proj.toIntLinearMap S.proj_equivariant) n))
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M] (hM : ∀ m : M, p • m = 0) :
    Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G M)) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  -- `x` restricts to zero on some open subgroup `V`
  obtain ⟨V, hV⟩ := exists_openSubgroup_res_eq_zero (ofDiscreteModule_isSmoothDiscrete ℤ G M) x
  -- the short exact sequence `0 → M → Coind_V^G M → Coind_V^G M ⧸ M → 0` of the unit
  -- `ι : M → Coind_V^G M` of coinduction
  set S := coindShortExact G V.toSubgroup M
  let ι : M →+ DiscreteCoind G V.toSubgroup M :=
    (DiscreteCoind.unit G V.toSubgroup M).toAddMonoidHom
  have hι : ∀ (g : G) (m : M), ι (g • m) = g • ι m := fun g m =>
    _root_.map_smul (DiscreteCoind.unit G V.toSubgroup M) g m
  -- `Coind_V^G M` is killed by `p`, hence so is its quotient
  have hBp : ∀ f : DiscreteCoind G V.toSubgroup M, p • f = 0 := DiscreteCoind.nsmul_eq_zero hM
  -- the image of `x` in `Hⁿ⁺¹(G, Coind_V^G M)` is zero, being its restriction to `V` under
  -- Shapiro's lemma
  have hιx : coeffMap (ofDiscreteModuleMap ι.toIntLinearMap hι) (n + 1) x = 0 := by
    refine (bijective_shapiroMap V.toSubgroup V.isClosed M (n + 1)).1 ?_
    rw [_root_.map_zero, ← ConcreteCategory.comp_apply, coeffMap_unit_comp_shapiroMap]
    exact hV
  -- so `x` is a connecting image of a class of `Hⁿ(G, Coind_V^G M ⧸ M)`
  have hS : ofDiscreteModuleMap S.incl.toIntLinearMap S.incl_equivariant =
      ofDiscreteModuleMap ι.toIntLinearMap hι :=
    TopRep.hom_ext <| DFunLike.ext _ _ fun m =>
      DFunLike.congr_fun (coindShortExact_incl G V.toSubgroup M) m
  obtain ⟨w, hw⟩ := (S.longExact_exact₁ n _).1 (hS ▸ hιx)
  -- right exactness lifts that class to `Hⁿ(G, Coind_V^G M)`, where the connecting map kills it
  obtain ⟨v, hv⟩ := h M (DiscreteCoind G V.toSubgroup M) (DimensionShiftQuotient G V.toSubgroup M)
    S hM hBp (S.nsmul_eq_zero_right hBp) w
  rw [← hw, ← hv, ← ConcreteCategory.comp_apply, S.coeffMap_proj_comp_delta]
  exact rfl

end TauCeti
