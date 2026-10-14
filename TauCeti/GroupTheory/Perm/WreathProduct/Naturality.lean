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
a left transversal `s'` of `U'` (`Subgroup.LeftTransversal.map`, in
`TauCeti/GroupTheory/TransversalWord.lean`), whose representative of `e x` is
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
    simp only [monomialHom_right, WreathProduct.congr_right, WreathProduct.map_right,
      Equiv.permCongr_apply, Equiv.symm_apply_apply, apply_smul_of_apply_mk U φ e he]

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
