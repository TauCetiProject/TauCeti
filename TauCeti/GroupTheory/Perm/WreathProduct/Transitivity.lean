/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Monomial

/-!
# Transitivity of the monomial homomorphism

Let `V ≤ U ≤ G` be subgroups, `s` a left transversal of `U` in `G` and `t` a left transversal of
`V` in `U`. The monomial homomorphism of `V`, taken for the composite transversal
`Subgroup.compositeLeftTransversal`, is obtained in three steps from those of `U` and of `V` in
`U`:

```text
G ──Φ_U──▶ U ≀ Sym(G ⧸ U) ──Φ_V^U──▶ (V ≀ Sym(U ⧸ V)) ≀ Sym(G ⧸ U)
  ──flatten──▶ V ≀ Sym((G ⧸ U) × (U ⧸ V)) ≅ V ≀ Sym(G ⧸ V).
```

The second map applies the monomial homomorphism of `V` in `U` in every coordinate, the third
is `TauCeti.WreathProduct.flatten`, and the last relabels `(G ⧸ U) × (U ⧸ V)` as `G ⧸ V` by
Mathlib's `Subgroup.quotientEquivProdOfLE'` and identifies `V.subgroupOf U` with `V`. On
coordinates this is the composite transversal word `TauCeti.lWord_compositeTransversal`, and on
permutations it is the description of the translation action of `G` on `G ⧸ V` in the tower
coordinates.

This is the group-theoretic form of the transitivity of Evens' multiplicative transfer: the norm
from `V` to `G` is computed through the monomial homomorphism of `V`, and this identity splits it
as the norm from `U` to `G` of the norm from `V` to `U`.

## Main results

* `Subgroup.monomialHom_compositeLeftTransversal`: the monomial homomorphism of a subgroup tower
  `V ≤ U ≤ G` for the composite transversal is the flattened composite of the monomial
  homomorphisms of `U ≤ G` and `V ≤ U`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §6.
-/

public section

namespace Subgroup

open TauCeti

variable {G : Type*} [Group G] {U V : Subgroup G} (hVU : V ≤ U)

/-- **Transitivity of the monomial homomorphism.** For `V ≤ U ≤ G`, a left transversal `s` of
`U` and a left transversal `t` of `V` in `U`, the monomial homomorphism of `V` for the composite
transversal is the monomial homomorphism of `U`, followed coordinatewise by that of `V` in `U`,
flattened to the index set `(G ⧸ U) × (U ⧸ V)`, and relabeled to `G ⧸ V` by the tower coordinates
`Subgroup.quotientEquivProdOfLE'` with `V.subgroupOf U` identified with `V`. -/
theorem monomialHom_compositeLeftTransversal (s : U.LeftTransversal)
    (t : (V.subgroupOf U).LeftTransversal) (g : G) :
    V.monomialHom (compositeLeftTransversal hVU s t) g =
      WreathProduct.congr (quotientEquivProdOfLE' hVU (leftTransversalRep U s)
          (leftTransversalRep_mk U s)).symm
        (WreathProduct.map (subgroupOfEquivOfLe hVU).toMonoidHom
          (WreathProduct.flatten
            (WreathProduct.map ((V.subgroupOf U).monomialHom t) (U.monomialHom s g)))) := by
  set e := quotientEquivProdOfLE' hVU (leftTransversalRep U s) (leftTransversalRep_mk U s)
    with he
  apply SemidirectProduct.ext
  · -- Base coordinates: the word of the composite transversal is the iterated word.
    funext q
    apply Subtype.ext
    simpa [e] using lWord_compositeTransversal U (leftTransversalRep U s) hVU
      (leftTransversalRep_mk U s) (leftTransversalRep (V.subgroupOf U) t) q g
  · -- Permutations: translation by `g` in the tower coordinates, read off from the translation
    -- by `g⁻¹⁻¹` and the inverse law `lWord_inv` of the transversal word.
    apply Equiv.ext
    intro q
    have key := quotientEquivProdOfLE'_inv_smul_symm U (leftTransversalRep U s) hVU
      (leftTransversalRep_mk U s) (e q).1 (e q).2 g⁻¹
    rw [inv_inv, Prod.mk.eta, ← he, e.symm_apply_apply] at key
    simp only [monomialHom_right, WreathProduct.congr_right, Equiv.permCongr_apply,
      Equiv.symm_symm, WreathProduct.map_right, WreathProduct.flatten_right_apply,
      WreathProduct.map_left, monomialHom_left]
    rw [Equiv.eq_symm_apply, key]
    congr 2
    exact Subtype.ext (by simp [lWord_inv])

end Subgroup
