/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Iterated
import TauCeti.GroupTheory.FiniteAbelian.TorsionFree

/-!
# Coordinate groups over abelian groups

Over an abelian group `G` the coordinate group of a consistent system of equations is as simple
as it can be. Let `G` be torsion-free, `X` finite and `S ⊆ G[X]` a system with a solution `v₀` in
`G`. For a solution `v`, evaluating an equation at `v` is evaluating it at `v₀` times evaluating
it, with all coefficients replaced by `1`, at `v / v₀`. Recording these quotients at all solutions
maps `G[X]` onto a finitely generated subgroup of the torsion-free abelian group `G^{V(S)}`, a free
abelian group `ℤᵏ`, and together with evaluation at `v₀` this identifies the coordinate group
`G_{R(S)}` with `G × ℤᵏ` over `G`
(`TauCeti.GroupAlgGeom.CoordGroup.exists_bijective_gHom_prod_of_isMulCommutative`). Compare
[Shev], §17.1, where the coordinate groups over finitely generated abelian groups are described.

If moreover `G` is residually free and `k > 0`, then `G` is nontrivial, so it contains an element
`u` that is not a proper power, and `G × ℤᵏ` is the extension `G(u, ℤᵏ)` of the centralizer `G`
of `u`. So the coordinate group embeds, over `G`, in an iterated extension of centralizers of `G`
(`TauCeti.GroupAlgGeom.exists_ice_embedding_coordGroup_of_isMulCommutative`). This is the abelian
case of the theorem of Kharlampovich and Myasnikov that the coordinate group of a consistent
quadratic equation over a fully residually free group embeds in an iterated extension of
centralizers ([VAR-I], Theorem 1); for abelian `G` it holds for every consistent system in finitely
many variables.

## Main results

* `TauCeti.GroupAlgGeom.CoordGroup.exists_bijective_gHom_prod_of_isMulCommutative`: over an
  abelian torsion-free group `G`, the coordinate group of a consistent system in finitely many
  variables is `G`-isomorphic to `G × ℤᵏ` for some `k`.
* `TauCeti.GroupAlgGeom.exists_ice_embedding_coordGroup_of_isMulCommutative`: over an abelian
  residually free group `G`, the coordinate group of a consistent system in finitely many
  variables embeds, over `G`, in an iterated extension of centralizers of `G`.

## References

* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1,
  Theorem 1.
* [Shev] A. Shevlyakov, *Lectures notes in universal algebraic geometry*, arXiv:1601.02743
  (2016), §17.1, Proposition 17.5 and Corollary 17.7.
-/

public section

open Monoid.Coprod Subgroup

namespace TauCeti.GroupAlgGeom

open LimitGroup

universe u

variable {G : Type u} [Group G] {X : Type*}

-- Over an abelian group, an equation lies in the radical of a system `S` with a solution `v₀`
-- exactly when it vanishes at `v₀` and, with its coefficients replaced by `1`, at every quotient
-- `v / v₀` of solutions.
open scoped IsMulCommutative in
private theorem Rad_eq_ker_inf_ker [IsMulCommutative G] {S : Set (GX G X)} {v₀ : X → G}
    (hv₀ : v₀ ∈ V (.id G) S) : Rad (.id G) S = (eval (.id G) v₀).ker ⊓
      (eval (1 : G →* (V (.id G) S → G)) fun x v => v.val x / v₀ x).ker := by
  -- The coordinate of the tuple of quotients at a solution `v` is evaluation at `v / v₀`.
  have hp (w : GX G X) (v : V (.id G) S) :
      eval (1 : G →* (V (.id G) S → G)) (fun x v => v.val x / v₀ x) w v = eval 1 (v.val / v₀) w
          := by
    simpa [Function.comp_def, Pi.div_def] using
      hom_eval (ι := 1) (v := fun x (v : V (.id G) S) => v.val x / v₀ x) (Pi.evalMonoidHom _ v) w
  ext w
  simp only [mem_Rad, mem_inf, MonoidHom.mem_ker]
  refine ⟨fun h => ⟨h v₀ hv₀, funext fun v => ?_⟩, fun ⟨h₀, h₁⟩ v hv => ?_⟩
  · simpa [hp, h v.val v.property, h v₀ hv₀] using (eval_eq_eval_mul_eval_one_div
      (.id G) v₀ v.val w).symm
  · simpa [eval_eq_eval_mul_eval_one_div (.id G) v₀ v w, h₀, hp] using congr_fun h₁ ⟨v, hv⟩

open scoped IsMulCommutative in
/-- Over an abelian torsion-free group `G`, the coordinate group of a consistent system of
equations in finitely many variables is `G × ℤᵏ` over `G`, for some `k`: some `G`-homomorphism
from the coordinate group to `G × ℤᵏ`, with `G` included as the first factor, is bijective. -/
theorem CoordGroup.exists_bijective_gHom_prod_of_isMulCommutative [IsMulCommutative G]
    [IsMulTorsionFree G] [Finite X] {S : Set (GX G X)} (hS : (V (.id G) S).Nonempty) :
    ∃ (k : ℕ) (f : GHom (CoordGroup.coeff (.id G) S) (.inl G (Fin k → Multiplicative ℤ))),
      Function.Bijective f := by
  obtain ⟨v₀, hv₀⟩ := hS
  -- `δ` evaluates, with trivial coefficients, at the quotients `v / v₀` of the solutions `v`.
  let p : X → V (.id G) S → G := fun x v => v.val x / v₀ x
  let δ : GX G X →* (V (.id G) S → G) := eval 1 p
  obtain ⟨k, -, ⟨e⟩⟩ := Subgroup.exists_mulEquiv_closure_of_pairwise_commute
    (s := (Set.finite_range p).toFinset) fun a _ b _ _ => Commute.all a b
  have hrange : δ.range = closure ((Set.finite_range p).toFinset : Set _) := by
    rw [Set.Finite.coe_toFinset, range_eval, closure_union, ← MonoidHom.coe_range, closure_eq,
      MonoidHom.range_one, bot_sup_eq]
  let ψ : δ.range ≃* (Fin k → Multiplicative ℤ) :=
    (MulEquiv.subgroupCongr hrange).trans (e.trans (MulEquiv.piMultiplicative _))
  let Φ : GX G X →* G × (Fin k → Multiplicative ℤ) :=
    (eval (.id G) v₀).prod ((ψ : δ.range →* _).comp δ.rangeRestrict)
  have hΦ (g : G) : Φ (inl g) = (g, 1) := by
    have : δ.rangeRestrict (inl g) = 1 := Subtype.ext (by simp [δ])
    simp [Φ, this]
  have hker : Rad (.id G) S = Φ.ker := by
    rw [MonoidHom.ker_prod, MonoidHom.ker_mulEquiv_comp, MonoidHom.ker_rangeRestrict]
    exact Rad_eq_ker_inf_ker hv₀
  have hsurj : Function.Surjective Φ := by
    rintro ⟨g, z⟩
    obtain ⟨⟨_, w, rfl⟩, hw⟩ := ψ.surjective z
    refine ⟨inl (g * (eval (.id G) v₀ w)⁻¹) * w, ?_⟩
    rw [map_mul, hΦ]
    -- `hw` is about the class of `w` in the range of `δ`, which is `δ.rangeRestrict w`.
    exact Prod.ext (by simp [Φ]) (by simp only [Prod.snd_mul, one_mul]; exact hw)
  rw [CoordGroup.coeff_def]
  obtain ⟨f, hf, -⟩ := GX.exists_bijective_gHom_of_eq_ker
    (⟨Φ, hΦ⟩ : GHom inl (.inl G (Fin k → Multiplicative ℤ))) hsurj hker
  exact ⟨k, f, hf⟩

open scoped IsMulCommutative in
/-- Over an abelian residually free group `G`, the coordinate group of a consistent system of
equations in finitely many variables embeds, over `G`, in an iterated extension of centralizers of
`G`. -/
theorem exists_ice_embedding_coordGroup_of_isMulCommutative (hG : IsResiduallyFree G)
    [IsMulCommutative G] [Finite X] (S : Set (GX G X)) (hS : (V (MonoidHom.id G) S).Nonempty) :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id G) S) j), Function.Injective f := by
  rcases subsingleton_or_nontrivial G with hG1 | hG1
  · -- Over the trivial group a solution `v` is the only point, so evaluation at `v` is injective.
    obtain ⟨v, hv⟩ := hS
    exact ⟨G, _, .id G, .refl, CoordGroup.evalGHom v hv, CoordGroup.evalGHom_injective hv
      fun w _ => Set.mem_singleton_iff.2 (Subsingleton.elim w v)⟩
  have := hG.isMulTorsionFree
  obtain ⟨k, f, hf⟩ := CoordGroup.exists_bijective_gHom_prod_of_isMulCommutative hS
  -- It remains to see that `G × ℤᵏ` is an iterated extension of centralizers of `G`.
  suffices h : ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (e : G × (Fin k → Multiplicative ℤ) ≃* E), ∀ g, e (MonoidHom.inl _ _ g) = j g by
    obtain ⟨E, _, j, c, e, he⟩ := h
    refine ⟨E, _, j, c, (GHom.ofMulEquiv e he).comp f, ?_⟩
    rw [GHom.coe_comp]
    exact (GHom.ofMulEquiv_bijective e he).injective.comp hf.injective
  rcases k.eq_zero_or_pos with rfl | hk
  · -- `G × ℤ⁰ = G`: the empty chain.
    exact ⟨G, _, .id G, .refl, .prodUnique, fun g => by simp⟩
  · -- A nontrivial residually free group has an element `u` that is not a proper power; `u` is
    -- central, and `G × ℤᵏ = G(u, ℤᵏ)` is one admissible extension of a centralizer.
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    obtain ⟨u, -, -, -, hu, -⟩ := hG.exists_maximalRoot hg
    exact ⟨CentralizerExt u k, _, CentralizerExt.of,
      ICE.single (isAdmissibleCentralizerStep_iff.2 ⟨hu, hk⟩),
      (CentralizerExt.equivProdOfMemCenter (mem_center_iff.2 fun g => mul_comm g u)).symm,
      fun g => by simp [MulEquiv.symm_apply_eq]⟩

section Examples

/-- Over the trivial group every system in finitely many variables is consistent, and its
coordinate group embeds in an iterated extension of centralizers of the trivial group. -/
example [Finite X] (S : Set (GX Unit X)) :
    ∃ (E : Type) (_ : Group E) (j : Unit →* E) (_ : ICE Unit E j)
      (f : GHom (CoordGroup.coeff (.id Unit) S) j), Function.Injective f :=
  exists_ice_embedding_coordGroup_of_isMulCommutative
    isFullyResiduallyFree_of_subsingleton.isResiduallyFree S
    ⟨1, mem_V.2 fun _ _ => Subsingleton.elim _ _⟩

end Examples

end TauCeti.GroupAlgGeom
