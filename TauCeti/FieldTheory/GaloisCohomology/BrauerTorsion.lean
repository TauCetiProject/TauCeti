/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Coefficients
public import TauCeti.FieldTheory.GaloisCohomology.Hilbert90
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact

/-!
# `H²(G_K, μₙ)` is the `n`-torsion of the cohomological Brauer group

Let `K` be a field, `Kˢ` a separable closure, `G_K = AbsoluteGaloisGroup K`, and `n` a natural
number invertible in `K`. The inclusion `μₙ ⊆ (Kˢ)ˣ` induces

```text
H²(G_K, μₙ) → H²(G_K, (Kˢ)ˣ),
```

and this map is injective with image the `n`-torsion of `H²(G_K, (Kˢ)ˣ)`. Both facts are read off
the long exact sequence of the Kummer sequence `1 → μₙ → (Kˢ)ˣ → (Kˢ)ˣ → 1`
(`TauCeti.kummerShortExact`):

```text
H¹(G_K, (Kˢ)ˣ) →δ¹→ H²(G_K, μₙ) → H²(G_K, (Kˢ)ˣ) →n→ H²(G_K, (Kˢ)ˣ).
```

* Injectivity is exactness at `H²(G_K, μₙ)` together with Hilbert 90,
  `H¹(G_K, (Kˢ)ˣ) = 0` (`TauCeti.subsingleton_H1_unitsCoeff`).
* The image is exactness at `H²(G_K, (Kˢ)ˣ)`, once the map induced by the `n`-th power map of
  `(Kˢ)ˣ` is recognised as multiplication by `n` on `H²`
  (`TauCeti.explicitCoeff2_kummerShortExact_proj`).

The argument runs in the explicit low-degree model, where the long exact sequence lives, and the
result is transported to Mathlib's `continuousCohomology 2` through the comparison
`TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology` and its naturality in coefficient
maps, `TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology_coeffMap`.

This is how the degree-`n` part of the Brauer group is seen cohomologically: for a local field the
local invariant identifies the `n`-torsion of `H²(G_K, (Kˢ)ˣ)` with `(1/n)ℤ/ℤ`, and composing with
the injection here gives `H²(G_K, μₙ) ≃ ℤ/n`.

## Main definitions

* `TauCeti.kummerCoeffToUnits`: the inclusion `μₙ ⊆ (Kˢ)ˣ` as a morphism of canonical coefficient
  objects.
* `TauCeti.h2KummerToUnits`: the induced map `H²(G_K, μₙ) → H²(G_K, (Kˢ)ˣ)` on Mathlib's continuous
  cohomology.

## Main results

* `TauCeti.explicitCoeff2_kummerShortExact_incl_injective` and
  `TauCeti.mem_range_explicitCoeff2_kummerShortExact_incl_iff`: injectivity and the image, on the
  explicit model.
* `TauCeti.h2KummerToUnits_injective`: `H²(G_K, μₙ) → H²(G_K, (Kˢ)ˣ)` is injective.
* `TauCeti.h2KummerToUnits_range`: its image is the `n`-torsion.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1) and the
  exact sequence following it.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology

universe u

/-! ### The explicit model -/

section Explicit

variable (K : Type u) [Field K] {n : ℕ} (hn : IsUnit (n : K))

/-- The map on explicit `H²` induced by the `n`-th power map of `(Kˢ)ˣ` is multiplication by `n`:
in additive notation the power map is `n • ·`, and a coefficient map acts on cocycles by
postcomposition. -/
theorem explicitCoeff2_kummerShortExact_proj (x : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    explicitCoeff2 _ _ (kummerShortExact K n hn).projDistribMulActionHom
      continuous_of_discreteTopology x = n • x := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [explicitCoeff2_mk, ← QuotientAddGroup.mk_nsmul]
    refine congrArg _ (Subtype.ext (funext fun p => ?_))
    refine (cocyclesMap2_apply _ _ _ _ _ _ _ _ c p.1 p.2).trans ?_
    simp [DiscreteShortExact.projDistribMulActionHom_apply, unitsCoeffPow_eq_nsmul]

/-- **`H²(G_K, μₙ) → H²(G_K, (Kˢ)ˣ)` is injective**, on the explicit model: its kernel is the image
of `δ¹` from `H¹(G_K, (Kˢ)ˣ)`, which vanishes by Hilbert 90. -/
theorem explicitCoeff2_kummerShortExact_incl_injective :
    Function.Injective (explicitCoeff2 _ _ (kummerShortExact K n hn).inclDistribMulActionHom
      continuous_of_discreteTopology) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have hx' : x ∈ (kummerShortExact K n hn).explicitDelta1.range := by
    rw [(kummerShortExact K n hn).explicitLongExact_H2A]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  rw [Subsingleton.elim y 0, map_zero]

/-- **The image of `H²(G_K, μₙ)` in `H²(G_K, (Kˢ)ˣ)` is the `n`-torsion**, on the explicit model:
it is the kernel of the map induced by the `n`-th power map, which is multiplication by `n`. -/
theorem mem_range_explicitCoeff2_kummerShortExact_incl_iff
    (x : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    x ∈ (explicitCoeff2 _ _ (kummerShortExact K n hn).inclDistribMulActionHom
      continuous_of_discreteTopology).range ↔ n • x = 0 := by
  rw [(kummerShortExact K n hn).explicitLongExact_H2B, AddMonoidHom.mem_ker,
    explicitCoeff2_kummerShortExact_proj]

end Explicit

/-! ### The canonical object -/

variable (K : Type u) [Field K] (n : ℕ)

/-- The inclusion `μₙ ⊆ (Kˢ)ˣ` as a morphism of canonical coefficient objects over `G_K`. -/
def kummerCoeffToUnits :
    ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K n) ⟶
      ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K) :=
  ofDiscreteModuleMap (kummerCoeffIncl K n).toIntLinearMap (kummerCoeffIncl_equivariant K n)

/-- The morphism `kummerCoeffToUnits` is the inclusion `μₙ ⊆ (Kˢ)ˣ` on elements. -/
@[simp]
theorem kummerCoeffToUnits_hom_apply (x : KummerCoeff K n) :
    (kummerCoeffToUnits K n).hom x = kummerCoeffIncl K n x :=
  (rfl)

/-- **The map `H²(G_K, μₙ) → H²(G_K, (Kˢ)ˣ)`** induced by the inclusion `μₙ ⊆ (Kˢ)ˣ`, on Mathlib's
continuous cohomology. It is how the mod-`n` part of `H²` sits inside the cohomological Brauer
group: injective (`TauCeti.h2KummerToUnits_injective`) with image the `n`-torsion
(`TauCeti.h2KummerToUnits_range`) when `n` is invertible in `K`. -/
def h2KummerToUnits :
    continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K n)) ⟶
      continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  ContinuousCohomology.coeffMap (kummerCoeffToUnits K n) 2

-- Not `@[simp]`: `h2KummerToUnits` is the intended normal form, and this lemma unfolds it.
/-- The defining equation of `h2KummerToUnits`: it is the canonical coefficient map of
`kummerCoeffToUnits` in degree two. -/
theorem h2KummerToUnits_def :
    h2KummerToUnits K n = ContinuousCohomology.coeffMap (kummerCoeffToUnits K n) 2 :=
  (rfl)

variable {K n}

/-- The comparison with the explicit model carries the explicit coefficient map of `μₙ ⊆ (Kˢ)ˣ` to
`h2KummerToUnits`. -/
theorem h2KummerToUnits_explicitH2AddEquivContinuousCohomology (hn : IsUnit (n : K))
    (x : H2 (AbsoluteGaloisGroup K) (KummerCoeff K n)) :
    (h2KummerToUnits K n).hom (explicitH2AddEquivContinuousCohomology _ _ x) =
      explicitH2AddEquivContinuousCohomology _ _
        (explicitCoeff2 _ _ (kummerShortExact K n hn).inclDistribMulActionHom
          continuous_of_discreteTopology x) := by
  have hmap : kummerCoeffToUnits K n =
      ofDiscreteModuleMap
        (kummerShortExact K n hn).inclDistribMulActionHom.toAddMonoidHom.toIntLinearMap
        fun g m ↦ map_smul (kummerShortExact K n hn).inclDistribMulActionHom g m := by
    rw [kummerCoeffToUnits]
    congr 1
    ext m
    simp [DiscreteShortExact.inclDistribMulActionHom_apply]
  rw [h2KummerToUnits_def, hmap]
  exact explicitH2AddEquivContinuousCohomology_coeffMap _ _ _
    (kummerShortExact K n hn).inclDistribMulActionHom x

/-- **`H²(G_K, μₙ) → H²(G_K, (Kˢ)ˣ)` is injective** for `n` invertible in `K`. This is Hilbert 90
read through the long exact sequence of the Kummer sequence: the term before it is
`H¹(G_K, (Kˢ)ˣ)`, which vanishes. -/
theorem h2KummerToUnits_injective (hn : IsUnit (n : K)) :
    Function.Injective (h2KummerToUnits K n).hom := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := (explicitH2AddEquivContinuousCohomology _ _).surjective x
  obtain ⟨y, rfl⟩ := (explicitH2AddEquivContinuousCohomology _ _).surjective y
  rw [h2KummerToUnits_explicitH2AddEquivContinuousCohomology hn,
    h2KummerToUnits_explicitH2AddEquivContinuousCohomology hn] at hxy
  exact congrArg _ (explicitCoeff2_kummerShortExact_incl_injective K hn
    ((explicitH2AddEquivContinuousCohomology _ _).injective hxy))

/-- **The image of `H²(G_K, μₙ)` in `H²(G_K, (Kˢ)ˣ)` is the `n`-torsion** for `n` invertible in
`K`. This is exactness of the long exact sequence of the Kummer sequence at `H²(G_K, (Kˢ)ˣ)`, the
next map being multiplication by `n`. -/
theorem h2KummerToUnits_range (hn : IsUnit (n : K))
    (x : continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K))) :
    (∃ y, (h2KummerToUnits K n).hom y = x) ↔ n • x = 0 := by
  obtain ⟨x, rfl⟩ := (explicitH2AddEquivContinuousCohomology _ _).surjective x
  rw [← map_nsmul, EmbeddingLike.map_eq_zero_iff,
    ← mem_range_explicitCoeff2_kummerShortExact_incl_iff K hn]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := (explicitH2AddEquivContinuousCohomology _ _).surjective y
    rw [h2KummerToUnits_explicitH2AddEquivContinuousCohomology hn] at hy
    exact ⟨y, (explicitH2AddEquivContinuousCohomology _ _).injective hy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, h2KummerToUnits_explicitH2AddEquivContinuousCohomology hn y⟩

end TauCeti
