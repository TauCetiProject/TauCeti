/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Monomial
public import TauCeti.GroupTheory.QuotientGroup.ThirdIso

/-!
# Naturality of the monomial homomorphism

Let `φ : G →* G'` be a group homomorphism, `U ≤ G` and `U' ≤ G'` subgroups, and
`e : G ⧸ U ≃ G' ⧸ U'` a bijection of coset spaces induced by `φ`, so that `e ⟦g⟧ = ⟦φ g⟧`. Such an
`e` exists exactly when `U = U'.comap φ` and every coset of `U'` meets the range of `φ`; then `φ`
restricts to a homomorphism `ψ : U →* U'`. The image `φ '' s` of a left transversal `s` of `U` is
a left transversal `s'` of `U'` (`Subgroup.LeftTransversal.map`), whose representative of `e x` is
the image of the representative of `x`. The monomial homomorphisms of `s` and `s'` are related by

```text
Φ_{s'} (φ g) = congr e (map ψ (Φ_s g)),
```

that is, `φ` applied to the transversal words in every coordinate, followed by relabeling the
coordinates along `e` (`Subgroup.monomialHom_map`).

The case that motivates this file is inflation: for a normal subgroup `N` contained in `U`, the
quotient map `G → G ⧸ N` induces the bijection `G ⧸ U ≃ (G ⧸ N) ⧸ U.map (mk' N)` of
`QuotientGroup.quotientEquivQuotientMapOfLE`, so the monomial homomorphism of the image of `U` in
`G ⧸ N`, evaluated on the class of `g`, is the image of the monomial homomorphism of `U` at `g`
(`Subgroup.monomialHom_quotient`). This is the group-level identity behind the compatibility of
Evens' multiplicative transfer with inflation.

## Main definitions

* `Subgroup.LeftTransversal.map`: the image `φ '' s` of a left transversal of `U`, as a left
  transversal of `U'`.

## Main results

* `Subgroup.monomialHom_map`: naturality of the monomial homomorphism along `φ`.
* `Subgroup.monomialHom_quotient`: the inflation case.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §§2–3 and §6.
-/

public section

namespace Subgroup

open TauCeti

variable {G G' : Type*} [Group G] [Group G'] {U : Subgroup G} {U' : Subgroup G'}

section LeftTransversalMap

variable (s : U.LeftTransversal) (φ : G →* G') (e : G ⧸ U ≃ G' ⧸ U')
  (he : ∀ g : G, e g = (φ g : G' ⧸ U'))

/-- The image `φ '' s` of a left transversal `s` of `U` under a homomorphism `φ : G →* G'`
inducing a bijection `e` of coset spaces, as a left transversal of `U'`. Its representative of
`e x` is the image of the representative of `x` (`Subgroup.leftTransversalRep_map_apply`). -/
noncomputable def LeftTransversal.map : U'.LeftTransversal :=
  ⟨Set.range fun y ↦ φ (leftTransversalRep U s (e.symm y)),
    isComplement_range_left fun y ↦ by rw [← he, leftTransversalRep_mk, e.apply_symm_apply]⟩

/-- The representatives of the image transversal are the images of the representatives. -/
theorem leftTransversalRep_map :
    leftTransversalRep U' (s.map φ e he) = fun y ↦ φ (leftTransversalRep U s (e.symm y)) :=
  leftTransversalRep_range U' _ fun y ↦ by rw [← he, leftTransversalRep_mk, e.apply_symm_apply]

/-- The representative of `e x` in the image transversal is the image of the representative
of `x`. -/
@[simp]
theorem leftTransversalRep_map_apply (x : G ⧸ U) :
    leftTransversalRep U' (s.map φ e he) (e x) = φ (leftTransversalRep U s x) := by
  simp only [leftTransversalRep_map, Equiv.symm_apply_apply]

/-- The image transversal is the image of `s` under `φ`. -/
@[simp]
theorem LeftTransversal.coe_map : ((s.map φ e he : U'.LeftTransversal) : Set G') = φ '' s := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, leftTransversalRep_mem U s _, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨e (g : G ⧸ U), ?_⟩
    -- The representative chosen by `s` for the coset of an element of `s` is that element.
    simp only [Equiv.symm_apply_apply, leftTransversalRep_apply]
    exact congrArg (fun x : (s : Set G) ↦ φ x) (s.2.leftQuotientEquiv.apply_symm_apply ⟨g, hg⟩)

end LeftTransversalMap

/-- **Naturality of the monomial homomorphism.** Let `φ : G →* G'` induce the bijection `e` of
coset spaces and restrict to `ψ : U →* U'`. The monomial homomorphism of the image transversal
`s.map φ e he` at `φ g` is the monomial homomorphism of `s` at `g` with `ψ` applied to its
coordinates and the coordinates relabeled along `e`. -/
theorem monomialHom_map (φ : G →* G') (ψ : U →* U') (hψ : ∀ u, (ψ u : G') = φ u)
    (e : G ⧸ U ≃ G' ⧸ U') (he : ∀ g : G, e g = (φ g : G' ⧸ U')) (s : U.LeftTransversal)
    (g : G) :
    U'.monomialHom (s.map φ e he) (φ g) =
      WreathProduct.congr e (WreathProduct.map ψ (U.monomialHom s g)) := by
  apply SemidirectProduct.ext
  · -- Coordinates: `φ` carries the transversal word of `s` to that of the image transversal.
    funext y
    obtain ⟨x, rfl⟩ := e.surjective y
    apply Subtype.ext
    simp only [monomialHom_left, WreathProduct.congr_left, Equiv.symm_apply_apply,
      WreathProduct.map_left, hψ]
    exact lWord_map U _ U' _ φ e he (leftTransversalRep_map_apply s φ e he) x g
  · -- Permutations: `e` intertwines translation by `g` with translation by `φ g`.
    apply Equiv.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    induction x using QuotientGroup.induction_on with
    | H x =>
      simp only [monomialHom_right, WreathProduct.congr_right, WreathProduct.map_right,
        Equiv.permCongr_apply, Equiv.symm_apply_apply]
      simp only [MulAction.Quotient.smul_mk, smul_eq_mul, he, map_mul]

/-- **The monomial homomorphism and inflation.** For a normal subgroup `N` contained in `U`, the
monomial homomorphism of the image of `U` in `G ⧸ N`, for the image of a transversal `s` of `U`
and evaluated on the class of `g`, is the monomial homomorphism of `s` at `g` reduced modulo `N`
in every coordinate, with the cosets of `U` relabeled as those of its image by
`QuotientGroup.quotientEquivQuotientMapOfLE`. -/
theorem monomialHom_quotient (N : Subgroup G) [N.Normal] (hNU : N ≤ U) (s : U.LeftTransversal)
    (g : G) :
    (U.map (QuotientGroup.mk' N)).monomialHom
        (s.map (QuotientGroup.mk' N) (QuotientGroup.quotientEquivQuotientMapOfLE hNU)
          (QuotientGroup.quotientEquivQuotientMapOfLE_mk hNU)) (g : G ⧸ N) =
      WreathProduct.congr (QuotientGroup.quotientEquivQuotientMapOfLE hNU)
        (WreathProduct.map ((QuotientGroup.mk' N).subgroupMap U) (U.monomialHom s g)) :=
  monomialHom_map (QuotientGroup.mk' N) _ (MonoidHom.subgroupMap_apply_coe _ U) _ _ s g

end Subgroup
