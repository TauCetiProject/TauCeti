/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Transitivity
public import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Relative trace between coinduced modules

For `V ≤ U ≤ G`, a `U`-module `A` need not have a `G`-action. Nevertheless there is a
`G`-equivariant trace `Coind_V^G A → Coind_U^G A` when `V` has finite index in `U`.
It uses `DiscreteCoind.transEquiv`, `DiscreteCoind.map`, and `DiscreteCoind.trace`:
the trace inside `U` is coinduced to `G` through transitivity of coinduction.
Its value at `g` is `∑ t : U/V, t • f (t⁻¹ g)`.

The actions on `A` of `V` and its copy `V.subgroupOf U` are explicit parameters, with
their compatibility stated by `hsmul`. This preserves the coefficient instances chosen
by callers. Relative compactness of `U` suffices for the transitivity equivalence.

For example, take `V = 1` and `U = C₂ = ⟨s⟩`, with `A = ℤ` and the sign action
`s • a = -a`. The representatives `1, s` and the equality `s⁻¹ = s` give
`relativeTrace f (g) = f (g) - f (s * g)`. Thus the coefficient action contributes
the minus sign even though the outer group acts on coinduced functions by translation.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (1.6.4), with the terminology footnote on p. 61.
* L. Ribes, P. Zalesskii, *Profinite Groups*, second edition, Theorem 6.10.5.
-/

public section

namespace TauCeti.DiscreteCoind

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U V : Subgroup G) (hVU : V ≤ U) (A : Type*) [AddCommGroup A]
  [DistribMulAction U A] [DistribMulAction V A]
  (hsmul : ∀ (v : V.subgroupOf U) (w : V) (a : A),
    ((v : U) : G) = (w : G) → w • a = v • a)
  (hU : IsCompact (closure (U : Set G))) [(V.subgroupOf U).FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The relative trace from coinduction at `V` to coinduction at `U`, obtained by
coinducing the trace `Coind_V^U A → A`. No action of `G` on `A` is required. -/
noncomputable def relativeTrace : DiscreteCoind G V A →+[G] DiscreteCoind G U A where
  toAddMonoidHom :=
    (map (G := G) (DiscreteCoind.trace U (V.subgroupOf U) A).toIntLinearMap
      (by
        intro u f
        exact _root_.map_smul (DiscreteCoind.trace U (V.subgroupOf U) A) u f)).toAddMonoidHom.comp
        (transEquiv (Subgroup.map_subgroupOf_eq_of_le hVU) hsmul hU).symm.toAddMonoidHom
  map_smul' g f := by
    -- The bundled composite has the values of its two additive maps.
    change map _ _ ((transEquiv _ _ _).symm (g • f)) =
      g • map _ _ ((transEquiv _ _ _).symm f)
    rw [transEquiv_symm_smul]
    exact map_smul (G := G) (U := U) (R := ℤ)
      (DiscreteCoind.trace U (V.subgroupOf U) A).toIntLinearMap
      (by intro u a; exact _root_.map_smul (DiscreteCoind.trace U (V.subgroupOf U) A) u a)
      g _

/-- The relative trace at `g` is the inner trace of `u ↦ f (u g)` under transitivity. -/
theorem relativeTrace_apply (f : DiscreteCoind G V A) (g : G) :
    relativeTrace U V hVU A hsmul hU f g =
      DiscreteCoind.trace U (V.subgroupOf U) A
        ((transEquiv (Subgroup.map_subgroupOf_eq_of_le hVU) hsmul hU).symm f g) := by
  exact map_apply _ _ _ _

/-- The finite-sum formula for the relative trace. The cosets and action belong to `U`;
only the argument of the coinduced function belongs to `G`. -/
theorem relativeTrace_apply_eq_sum (f : DiscreteCoind G V A) (g : G) :
    relativeTrace U V hVU A hsmul hU f g =
      ∑ x : U ⧸ V.subgroupOf U, x.out • f (((x.out⁻¹ : U) : G) * g) := by
  simp only [relativeTrace_apply, trace_apply, transEquiv_symm_apply]

/-- Relative trace after the transitivity equivalence is pointwise coinduction of
the trace inside `U`. This equation connects the relative trace to coefficient maps. -/
theorem relativeTrace_transEquiv (f : DiscreteCoind G U (DiscreteCoind U (V.subgroupOf U) A)) :
    relativeTrace U V hVU A hsmul hU
        (transEquiv (Subgroup.map_subgroupOf_eq_of_le hVU) hsmul hU f) =
      map (G := G) (DiscreteCoind.trace U (V.subgroupOf U) A).toIntLinearMap
        (by intro u a; exact _root_.map_smul (DiscreteCoind.trace U (V.subgroupOf U) A) u a) f := by
  ext g
  rw [relativeTrace_apply, AddEquiv.symm_apply_apply]
  exact (map_apply (G := G) (U := U) (R := ℤ)
    (DiscreteCoind.trace U (V.subgroupOf U) A).toIntLinearMap
    (by intro u a; exact _root_.map_smul (DiscreteCoind.trace U (V.subgroupOf U) A) u a)
    f g).symm

end TauCeti.DiscreteCoind
