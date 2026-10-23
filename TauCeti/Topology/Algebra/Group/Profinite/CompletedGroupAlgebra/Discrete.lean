/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import TauCeti.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Basic

/-!
# The completed group algebra of a discrete group

For a group `Γ` with the discrete topology, the trivial subgroup is an open normal subgroup
(`TauCeti.openNormalSubgroupBot`), and it lies below every other one. The level of the completed
group algebra `R[[Γ]]` at it is therefore the whole inverse system: the projection onto
`R[Γ ⧸ ⊥]` is bijective. Composed with `Γ ⧸ ⊥ ≃* Γ`, this identifies the completed group algebra
of a discrete group with its ordinary group algebra,

```text
R[[Γ]] ≃ₐ[R] R[Γ],
```

an isomorphism of `R`-algebras sending each group element to itself, under which the level at an
arbitrary open normal subgroup `U` is the pushforward along `Γ → Γ ⧸ U`. For a finite group this
is the statement that the completed group algebra of a finite profinite group is its group
algebra. When moreover `R` is a topological ring, the inverse-limit topology on `R[[Γ]]` is the
product topology on the coefficients: reading off the coefficients is a homeomorphism
`R[[Γ]] → (Γ → R)`.

The trivial group is the extreme case: there `R[[Γ]]` is `R` itself, that is, the structure map
`R → R[[Γ]]` is bijective.

## Main definitions

* `TauCeti.completedGroupAlgebra.equivMonoidAlgebra R Γ`: for a discrete group `Γ`, the
  `R`-algebra isomorphism `R[[Γ]] ≃ₐ[R] R[Γ]`.

## Main results

* `TauCeti.completedGroupAlgebra.proj_openNormalSubgroupBot_bijective`: for discrete `Γ`, the
  projection onto the level at the trivial subgroup is bijective.
* `TauCeti.completedGroupAlgebra.proj_eq_mapDomain_equivMonoidAlgebra`: the level at `U` of an
  element is the pushforward of its image in `R[Γ]` along `Γ → Γ ⧸ U`.
* `TauCeti.completedGroupAlgebra.equivMonoidAlgebra_of`: the isomorphism sends the group element
  `γ` to the basis element at `γ`.
* `TauCeti.completedGroupAlgebra.isHomeomorph_coeff_equivMonoidAlgebra`: for finite discrete `Γ`
  and a topological ring `R`, taking coefficients in `R[Γ]` is a homeomorphism
  `R[[Γ]] → (Γ → R)`.
* `TauCeti.completedGroupAlgebra.algebraMap_bijective_of_subsingleton`: for the trivial group,
  the structure map `R → R[[Γ]]` is bijective.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 5.3.
-/

public section

namespace TauCeti

namespace completedGroupAlgebra

universe u v

variable (R : Type u) [CommRing R] (Γ : Type v) [Group Γ] [TopologicalSpace Γ]

section Discrete

variable [DiscreteTopology Γ]

/-- For a discrete group `Γ`, the projection of `R[[Γ]]` onto its level at the trivial subgroup is
bijective: that level lies below every other one, so it determines all of them. -/
theorem proj_openNormalSubgroupBot_bijective :
    Function.Bijective (proj R Γ (openNormalSubgroupBot Γ)) := by
  refine ⟨fun x y h ↦ ext fun U ↦ ?_, proj_surjective R Γ _⟩
  rw [← mapDomain_mapOfLE_proj (openNormalSubgroupBot_le (U := U)), h, mapDomain_mapOfLE_proj]

/-- The identification `Γ ⧸ ⊥ ≃* Γ`, for the trivial open normal subgroup of a discrete group. -/
private noncomputable def quotientBotEquiv :
    Γ ⧸ (openNormalSubgroupBot Γ).toSubgroup ≃* Γ :=
  (QuotientGroup.quotientMulEquivOfEq (openNormalSubgroupBot_toSubgroup Γ)).trans
    QuotientGroup.quotientBot

/-- `quotientBotEquiv` sends the class of `γ` to `γ`. -/
private theorem quotientBotEquiv_mk (γ : Γ) :
    quotientBotEquiv Γ (γ : Γ ⧸ (openNormalSubgroupBot Γ).toSubgroup) = γ := by
  rw [quotientBotEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    ← MulEquiv.eq_symm_apply, QuotientGroup.quotientBot_symm_apply]

/-- The **completed group algebra of a discrete group is its group algebra**: for `Γ` discrete,
the projection onto the level at the trivial subgroup, followed by `Γ ⧸ ⊥ ≃* Γ`, is an
isomorphism of `R`-algebras `R[[Γ]] ≃ₐ[R] R[Γ]`. It sends group elements to group elements
(`equivMonoidAlgebra_of`), and the level of `x` at `U` is the pushforward of its image along
`Γ → Γ ⧸ U` (`proj_eq_mapDomain_equivMonoidAlgebra`). This applies in particular to every finite
group with the discrete topology, the finite profinite groups. -/
noncomputable def equivMonoidAlgebra : completedGroupAlgebra R Γ ≃ₐ[R] MonoidAlgebra R Γ :=
  (AlgEquiv.ofBijective _ (proj_openNormalSubgroupBot_bijective R Γ)).trans
    (MonoidAlgebra.domCongr R R (quotientBotEquiv Γ))

variable {R Γ}

/-- `equivMonoidAlgebra` is the projection onto the level at the trivial subgroup, transported
along `quotientBotEquiv`. -/
private theorem equivMonoidAlgebra_apply (x : completedGroupAlgebra R Γ) :
    equivMonoidAlgebra R Γ x =
      MonoidAlgebra.domCongr R R (quotientBotEquiv Γ) (proj R Γ (openNormalSubgroupBot Γ) x) := by
  rw [equivMonoidAlgebra, AlgEquiv.trans_apply, AlgEquiv.ofBijective_apply]

/-- The level at `U` of an element of the completed group algebra of a discrete group is the
pushforward of its image in the group algebra along the quotient map `Γ → Γ ⧸ U`. -/
theorem proj_eq_mapDomain_equivMonoidAlgebra (U : OpenNormalSubgroup Γ)
    (x : completedGroupAlgebra R Γ) :
    proj R Γ U x =
      MonoidAlgebra.mapDomain (QuotientGroup.mk : Γ → Γ ⧸ U.toSubgroup)
        (equivMonoidAlgebra R Γ x) := by
  rw [equivMonoidAlgebra_apply, ← AlgEquiv.coe_toAlgHom, MonoidAlgebra.domCongr_toAlgHom,
    MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_mapDomain,
    ← mapDomain_mapOfLE_proj (openNormalSubgroupBot_le (U := U)) x]
  congr 1
  funext q
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
  simp [quotientBotEquiv_mk]

/-- The level at `U` of the preimage of `y ∈ R[Γ]` in the completed group algebra of a discrete
group is the pushforward of `y` along the quotient map `Γ → Γ ⧸ U`. -/
@[simp]
theorem proj_equivMonoidAlgebra_symm (U : OpenNormalSubgroup Γ) (y : MonoidAlgebra R Γ) :
    proj R Γ U ((equivMonoidAlgebra R Γ).symm y) =
      MonoidAlgebra.mapDomain (QuotientGroup.mk : Γ → Γ ⧸ U.toSubgroup) y := by
  rw [proj_eq_mapDomain_equivMonoidAlgebra, AlgEquiv.apply_symm_apply]

/-- The identification of the completed group algebra of a discrete group with its group algebra
sends the group element `γ` to the basis element at `γ`. -/
@[simp]
theorem equivMonoidAlgebra_of (γ : Γ) :
    equivMonoidAlgebra R Γ (of R Γ γ) = MonoidAlgebra.single γ 1 := by
  rw [equivMonoidAlgebra_apply, proj_of, MonoidAlgebra.domCongr_single, quotientBotEquiv_mk]

/-- The preimage of the monomial `r` at `γ` under the identification of the completed group
algebra of a discrete group with its group algebra is `r` times the group element `γ`. -/
@[simp]
theorem equivMonoidAlgebra_symm_single (γ : Γ) (r : R) :
    (equivMonoidAlgebra R Γ).symm (MonoidAlgebra.single γ r) = r • of R Γ γ := by
  rw [AlgEquiv.symm_apply_eq, map_smul, equivMonoidAlgebra_of, MonoidAlgebra.smul_single',
    mul_one]

end Discrete

section Finite

variable [DiscreteTopology Γ] [Finite Γ] [TopologicalSpace R] [IsTopologicalRing R]

/-- For a **finite** discrete group `Γ` over a topological ring `R`, the inverse-limit topology on
`R[[Γ]]` is the product topology on the coefficients: taking the coefficients of the image in the
group algebra `R[Γ]` is a homeomorphism `R[[Γ]] → (Γ → R)`. Its inverse sends `f` to
`∑ γ, f γ • of R Γ γ`. -/
theorem isHomeomorph_coeff_equivMonoidAlgebra :
    IsHomeomorph fun x : completedGroupAlgebra R Γ ↦ ⇑(equivMonoidAlgebra R Γ x).coeff := by
  have := Fintype.ofFinite Γ
  set c : completedGroupAlgebra R Γ → Γ → R := fun x ↦ ⇑(equivMonoidAlgebra R Γ x).coeff
  have hinj : Function.Injective c := fun x y h ↦
    (equivMonoidAlgebra R Γ).injective (MonoidAlgebra.coeff_injective (DFunLike.coe_injective h))
  have hright : Function.RightInverse (fun f : Γ → R ↦ ∑ γ, f γ • of R Γ γ) c := fun f ↦ by
    funext δ
    classical
    simp [c, map_sum, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hcont : Continuous c := continuous_pi fun δ ↦ by
    have hδ : ∀ x : completedGroupAlgebra R Γ, c x δ =
        (proj R Γ (openNormalSubgroupBot Γ) x).coeff ((quotientBotEquiv Γ).symm δ) := fun x ↦ by
      simp [c, equivMonoidAlgebra_apply, MonoidAlgebra.coeff_domCongr]
    simpa only [hδ] using continuous_coeff_proj R Γ _ _
  exact (Homeomorph.mk ⟨c, fun f ↦ ∑ γ, f γ • of R Γ γ, hright.leftInverse_of_injective hinj,
    hright⟩ hcont (continuous_finsetSum _ fun γ _ ↦
      (continuous_apply γ).smul continuous_const)).isHomeomorph

end Finite

section Subsingleton

variable [Subsingleton Γ]

/-- The completed group algebra of the trivial group is the coefficient ring: the structure map
`R → R[[Γ]]` is bijective. -/
theorem algebraMap_bijective_of_subsingleton :
    Function.Bijective (algebraMap R (completedGroupAlgebra R Γ)) := by
  let e : completedGroupAlgebra R Γ ≃ₐ[R] R :=
    (equivMonoidAlgebra R Γ).trans (MonoidAlgebra.uniqueAlgEquiv R Γ)
  have h : algebraMap R (completedGroupAlgebra R Γ) = e.symm.toAlgHom.toRingHom :=
    congrArg AlgHom.toRingHom (Subsingleton.elim (Algebra.ofId R _) e.symm.toAlgHom)
  rw [h]
  exact e.symm.bijective

end Subsingleton

end completedGroupAlgebra

end TauCeti
