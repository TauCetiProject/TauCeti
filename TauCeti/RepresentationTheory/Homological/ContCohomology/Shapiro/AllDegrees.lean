/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.Canonical
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Transitivity
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DimensionShifting.Basic

/-!
# Shapiro's lemma in every degree

For a closed subgroup `U` of a profinite group `G` and a discrete `U`-module `A`, the canonical
Shapiro map `TauCeti.ContinuousCohomology.shapiroMap`,

```text
Hⁿ(G, Coind_U^G A) ⟶ Hⁿ(U, A),
```

is an isomorphism in every degree `n`. This is **Shapiro's lemma** for Mathlib's canonical
continuous cohomology; the isomorphism is `TauCeti.ContinuousCohomology.shapiroIso`.

The degrees `0` and `1` are the base cases, where the canonical map agrees with the explicit
low-degree Shapiro isomorphisms (`TauCeti.ContinuousCohomology.bijective_shapiroMap_of_le_two`).
The step from degree `n + 1` to degree `n + 2` is dimension shifting. The short exact sequence
`0 → A → Coind_1^U A → Q → 0` of `TauCeti.ContCohomology.coindBotShortExact`, with
`Q = Coind_1^U A ⧸ A`, and its coinduction to `G` fit into the commuting square

```text
Hⁿ⁺¹(G, Coind_U^G Q) ---δ---> Hⁿ⁺²(G, Coind_U^G A)
         |                             |
     shapiroMap                    shapiroMap
         v                             v
     Hⁿ⁺¹(U, Q) ----------δ--------> Hⁿ⁺²(U, A)
```

of `TauCeti.ContCohomology.DiscreteShortExact.delta_shapiroMap`. Both connecting maps are
isomorphisms, because both middle terms are acyclic in positive degrees: `Coind_1^U A` by
`TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int`, and
`Coind_U^G (Coind_1^U A)` because transitivity of coinduction identifies it with `Coind_1^G A`
(`TauCeti.DiscreteCoind.transIsoBot`). The left vertical map is an isomorphism by induction, applied
to the module `Q`, so the right one is too.

Closedness of `U` enters through the base cases, which use the explicit Shapiro isomorphisms for a
closed subgroup, and through the coinduction of a short exact sequence, whose surjectivity on the
right needs a closed subgroup.

## Main definitions

* `TauCeti.ContinuousCohomology.shapiroIso`: **Shapiro's lemma in every degree**,
  `Hⁿ(G, Coind_U^G A) ≅ Hⁿ(U, A)` for a closed subgroup `U` of a profinite group `G`, with forward
  map the canonical Shapiro map (`shapiroIso_hom`).

## Main results

* `TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_discreteCoind_discreteCoind_bot`:
  `Coind_U^G (Coind_1^U A)` is acyclic in every positive degree.
* `TauCeti.ContinuousCohomology.isIso_shapiroMap`,
  `TauCeti.ContinuousCohomology.bijective_shapiroMap`: the canonical Shapiro map is an isomorphism,
  resp. bijective, in every degree.
* `TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_discreteCoind_iff`: `Hⁿ(U, A)`
  vanishes exactly when `Hⁿ(G, Coind_U^G A)` does.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (1.6.4), with the footnote on p. 61 recording that NSW write `Ind` for the coinduced module, and
  (1.3.7) for the dimension-shifting argument.
* L. Ribes, P. Zalesskii, *Profinite Groups*, Thm. 6.10.5.
* J.-P. Serre, *Galois Cohomology*, Ch. I, §2.5.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

open TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G)

/-! ### Acyclicity of `Coind_U^G (Coind_1^U A)` -/

section Acyclic

variable (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A]

/-- **`Coind_U^G (Coind_1^U A)` is acyclic in every positive degree**, for a compact group `G` and
any subgroup `U`: transitivity of coinduction identifies it with `Coind_1^G A`, whose
positive-degree cohomology vanishes. -/
instance subsingleton_continuousCohomology_discreteCoind_discreteCoind_bot (n : ℕ) :
    Subsingleton (continuousCohomology (n + 1)
      (ofDiscreteModule ℤ G (DiscreteCoind G U (DiscreteCoind U (⊥ : Subgroup U) A)))) :=
  -- `Coind_1^G A` needs an action of the trivial subgroup of `G` on `A`; any one will do, and
  -- `A` carries none by default, so the trivial action is supplied.
  letI : DistribMulAction (⊥ : Subgroup G) A :=
    { smul := fun _ a => a
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  subsingleton_continuousCohomology_of_iso
    (DiscreteCoind.transIsoBot U A isClosed_closure.isCompact) (n + 1)

end Acyclic

/-! ### Shapiro's lemma -/

section Shapiro

variable [TotallyDisconnectedSpace G] (hU : IsClosed (U : Set G))
  (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A] [ContinuousSMul U A]

include hU

/-- **Shapiro's lemma in every degree, as an isomorphism of `TopModuleCat ℤ`**: for a closed
subgroup `U` of a profinite group `G` and a discrete `U`-module `A`, the canonical Shapiro map
`Hⁿ(G, Coind_U^G A) ⟶ Hⁿ(U, A)` is an isomorphism. -/
theorem isIso_shapiroMap (n : ℕ) : IsIso (shapiroMap U A n) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  induction n generalizing A with
  | zero => exact TopModuleCat.isIso_of_bijective _ (bijective_shapiroMap_zero U A)
  | succ n ih =>
    cases n with
    | zero => exact TopModuleCat.isIso_of_bijective _ (bijective_shapiroMap_one U A hU)
    | succ n =>
      -- The Shapiro map in degree `n + 2` is conjugate, through the connecting maps of
      -- `0 → A → Coind_1^U A → Q → 0` and of its coinduction to `G`, to the Shapiro map of
      -- `Q = Coind_1^U A ⧸ A` in degree `n + 1`, which is an isomorphism by induction.
      have := ih (DimensionShiftQuotient U A)
      have := isIso_coindBotShortExact_delta U A (n + 1) n.succ_pos
      have := ((coindBotShortExact U A).coind U hU).isIso_delta (n + 1)
      rw [(IsIso.eq_inv_comp _).2 ((coindBotShortExact U A).delta_shapiroMap hU (n + 1))]
      infer_instance

/-- **Shapiro's lemma in every degree**: for a closed subgroup `U` of a profinite group `G` and a
discrete `U`-module `A`, the canonical Shapiro map `Hⁿ(G, Coind_U^G A) ⟶ Hⁿ(U, A)` is bijective. -/
theorem bijective_shapiroMap (n : ℕ) : Function.Bijective (shapiroMap U A n) :=
  haveI := isIso_shapiroMap U hU A n
  ConcreteCategory.bijective_of_isIso _

/-- **The Shapiro isomorphism** `Hⁿ(G, Coind_U^G A) ≅ Hⁿ(U, A)` in every degree, for a closed
subgroup `U` of a profinite group `G` and a discrete `U`-module `A`. Its forward map is the
canonical Shapiro map, restriction to `U` followed by evaluation at `1` on the coefficients
(`shapiroIso_hom`, `TauCeti.ContinuousCohomology.shapiroMap_eq_res_comp_coeffMap`). -/
noncomputable def shapiroIso (n : ℕ) :
    continuousCohomology n (ofDiscreteModule ℤ G (DiscreteCoind G U A)) ≅
      continuousCohomology n (ofDiscreteModule ℤ U A) :=
  haveI := isIso_shapiroMap U hU A n
  asIso (shapiroMap U A n)

/-- The forward map of the Shapiro isomorphism is the canonical Shapiro map. -/
@[simp]
theorem shapiroIso_hom (n : ℕ) : (shapiroIso U hU A n).hom = shapiroMap U A n := (rfl)

/-- The inverse of the Shapiro isomorphism followed by the canonical Shapiro map is the identity. -/
@[simp]
theorem shapiroIso_inv_shapiroMap (n : ℕ) :
    (shapiroIso U hU A n).inv ≫ shapiroMap U A n = 𝟙 _ := by
  rw [← shapiroIso_hom U hU A n, Iso.inv_hom_id]

/-- The canonical Shapiro map followed by the inverse of the Shapiro isomorphism is the identity. -/
@[simp]
theorem shapiroMap_shapiroIso_inv (n : ℕ) :
    shapiroMap U A n ≫ (shapiroIso U hU A n).inv = 𝟙 _ := by
  rw [← shapiroIso_hom U hU A n, Iso.hom_inv_id]

/-- **Vanishing transfers along Shapiro's lemma**: `Hⁿ(U, A)` vanishes exactly when
`Hⁿ(G, Coind_U^G A)` does. -/
theorem subsingleton_continuousCohomology_discreteCoind_iff (n : ℕ) :
    Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G (DiscreteCoind G U A))) ↔
      Subsingleton (continuousCohomology n (ofDiscreteModule ℤ U A)) :=
  (Equiv.ofBijective _ (bijective_shapiroMap U hU A n)).subsingleton_congr

end Shapiro

end TauCeti.ContinuousCohomology
