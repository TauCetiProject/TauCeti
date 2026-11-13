/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Separated

/-!
# Coordinate groups through quotients that embed in a separated group

Let `S` be a system of equations over `G` and `N` a normal subgroup of `G[X]` between `S` and its
radical over a group `H` receiving the coefficients. If the quotient `G[X] / N` embeds, over `G`,
in a group separated by `H`, then `N` is the radical of `S`, and the coordinate group `G_{R(S)}` of
`S` embeds, over `G`, in the same group. This is how [VAR-I] computes radicals: for `N = ncl(S)`
it is Lemma 3 there, and the radical of a standard quadratic equation with a solution in general
position is found by embedding `G[X] / ncl(S)` in an iterated extension of centralizers of `G`
(VAR-I, §1). Some radicals are strictly larger than the normal closure of the system, so `N` is
allowed to lie strictly between them: over `F(a, b)`, the radical of `x² a²` is the normal closure
of `x a`, an example worked out at the end of the file.

## Main results

* `TauCeti.GroupAlgGeom.GX.Rad_eq_of_injective`: if `S ⊆ N ≤ Rad_H(S)` and `G[X] / N` embeds over
  `G` in a group separated by `H`, then `Rad_H(S) = N`.
* `TauCeti.GroupAlgGeom.exists_gHom_coordGroup_injective_of_quotient`: under the same hypotheses,
  the coordinate group of `S` over `H` embeds over `G` in that group.

## References

* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1,
  Lemma 3.
-/

public section

open Monoid.Coprod Subgroup

namespace TauCeti.GroupAlgGeom

variable {G : Type*} [Group G] {X : Type*}

/-- If a normal subgroup `N` of `G[X]` lies between a system `S` and its radical over `H`, and
`G[X] / N` embeds, over `G`, in a group separated by `H`, then `N` is the radical of `S`.

For `N = ncl(S)` this is one direction of `SystemGroup.isSeparatedBy_coeff_iff` ([VAR-I],
Lemma 3); here `N` may be strictly larger than the normal closure of `S`. -/
theorem GX.Rad_eq_of_injective {H E : Type*} [Group H] [Group E] {ι : G →* H} {j : G →* E}
    (hE : IsSeparatedBy j ι) {S : Set (GX G X)} {N : Subgroup (GX G X)} [N.Normal] (hSN : S ⊆ N)
    (hN : N ≤ Rad ι S) (f : GHom (GX.quotientCoeff N) j) (hf : Function.Injective f) :
    Rad ι S = N :=
  -- `G[X] ⧸ N` is separated by `H`, so `N` is its own radical.
  le_antisymm ((Rad_monotone ι hSN).trans
    ((GX.isSeparatedBy_quotientCoeff_iff N).1 (hE.of_injective f hf)).le) hN

/-- If a normal subgroup `N` of `G[X]` lies between a system `S` and its radical over `H`, and
`G[X] / N` embeds, over `G`, in a group separated by `H`, then the coordinate group of `S` over `H`
embeds, over `G`, in the same group. The embedding is the given one, the coordinate group being
`G[X] / N` by `GX.Rad_eq_of_injective`. -/
theorem exists_gHom_coordGroup_injective_of_quotient {H E : Type*} [Group H] [Group E] {ι : G →* H}
    {j : G →* E} (hE : IsSeparatedBy j ι) {S : Set (GX G X)} {N : Subgroup (GX G X)} [N.Normal]
    (hSN : S ⊆ N) (hN : N ≤ Rad ι S) (f : GHom (GX.quotientCoeff N) j) (hf : Function.Injective f) :
    ∃ f' : GHom (CoordGroup.coeff ι S) j, Function.Injective f' := by
  obtain rfl := GX.Rad_eq_of_injective hE hSN hN f hf
  rw [CoordGroup.coeff_def]
  exact ⟨f, hf⟩

/-! ### Example: the equation `x² a² = 1` over `F(a, b)` -/

section Example

open FreeGroup

/-- Over `F(a, b)` with one variable `x`, the radical of `x² a²` is the normal closure `N` of
`x a`, which strictly contains the normal closure of `x² a²`
(`inr_of_mul_inl_notMem_normalClosure_pow_mul_inl`): `N` is the ideal of the point `x = a⁻¹`, so
evaluation at that point embeds `G[x] / N` in `F(a, b)`. -/
example :
    Rad (.id (FreeGroup (Fin 2)))
        {(inr (of ()) : GX (FreeGroup (Fin 2)) Unit) ^ 2 * inl (of 0 ^ 2)} =
      normalClosure {inr (of ()) * inl (of 0)} := by
  set N := normalClosure {(inr (of ()) : GX (FreeGroup (Fin 2)) Unit) * inl (of 0)}
  -- `N` is the ideal of the point `x = a⁻¹`.
  have hN : I (.id (FreeGroup (Fin 2))) {MonoidHom.id _ ∘ fun _ : Unit => (of 0)⁻¹} = N := by
    rw [I_singleton_comp Function.injective_id]
    simp [N, Set.range_unique]
  have hv : (fun _ => (of 0)⁻¹) ∈ V (.id (FreeGroup (Fin 2))) (N : Set (GX _ Unit)) :=
    hN ▸ subset_V_I _ rfl
  refine GX.Rad_eq_of_injective (IsDiscriminatedBy.self _).isSeparatedBy ?_ ?_
    (GX.quotientEvalGHom _ hv) ?_
  · rw [← hN, subset_I_iff]
    simp
  · rw [Rad_pow_mul_inl_pow two_ne_zero]
    exact normalClosure_le_Rad _
  · -- The kernel of evaluation at `x = a⁻¹` is the ideal of that point.
    refine (injective_iff_map_eq_one _).2 fun q hq => ?_
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.eq_one_iff, ← hN]
    simpa using hq

end Example

end TauCeti.GroupAlgGeom
