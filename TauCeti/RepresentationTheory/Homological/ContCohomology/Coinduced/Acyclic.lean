/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Topology.EpiMono
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CompactDiscrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# Acyclicity of `Coind_1^G A` in every degree

For a compact group `G` and a discrete abelian group `A`, the coinduced module
`Coind_1^G A = TauCeti.DiscreteCoind G ⊥ A` of the trivial subgroup, the locally constant maps
`G → A` under right translation, has vanishing continuous cohomology in every positive degree:

```text
Hⁿ⁺¹(G, Coind_1^G A) = 0,
```

for Mathlib's canonical `continuousCohomology`. This is the all-degree form of
`TauCeti.ContCohomology.subsingleton_H1_discreteCoind_bot` and
`TauCeti.ContCohomology.subsingleton_H2_discreteCoind_bot`, and it is the input to dimension
shifting in every degree.

The proof does not use Shapiro's lemma. Mathlib computes `Hⁿ(G, X)` as the homology of the
`G`-invariants of the shifted coinduced resolution `C(G, C(G, …, C(G, X)))`, whose differential
is defined recursively by `d (n + 1) F x = F - d n (F x)`. Two observations drive the argument.

* The full, non-invariant, coinduced resolution of *any* representation is contracted by
  evaluation at `1`: `d n (F 1) + (d (n + 1) F) 1 = F` (`TopRep.d_apply_one_add_d_apply_one`, in
  `TauCeti/RepresentationTheory/Homological/ContCohomology/Resolution.lean`). This is immediate
  from the recursion, but evaluation at `1` is not equivariant, so it does not act on the
  invariants.
* For the coefficients `X = Coind_1^G A`, an invariant element `F` of level `m` of the resolution
  is determined by *evaluation at `1` inside every level*, `x₁ ↦ ⋯ ↦ xₘ ↦ F x₁ ⋯ xₘ 1`, which lands
  in level `m` of the coinduced resolution of `A` with the trivial action (`evalLevel`). The
  inverse spreads a level `Φ` of that resolution back over `G`, as
  `x₁ ↦ ⋯ ↦ xₘ ↦ (y ↦ Φ (y x₁) ⋯ (y xₘ))` (`coindLevel`). Evaluation is a chain map
  (`evalLevel_d`), because the differential is natural in the underlying modules and does not see
  the action.

A cocycle `F` of degree `n + 1` is thus sent by evaluation to a cocycle `Φ` of the resolution of
`A`, which is `d (Φ 1)` by the contraction; spreading `Φ 1` back over `G` gives an invariant
cochain whose differential is the spread of `d (Φ 1) = Φ` (`d_coindLevel_const`), which is `F`.

Compactness of `G` enters in two places. Every level of the resolution is discrete
(`TauCeti.discreteTopology_resolutionX`), which makes `evalLevel` and `coindLevel` continuous, and
`G` is locally compact, which makes evaluation `C(G, Z) × G → Z` continuous and hence lets the
two-variable family `shear` be curried. Neither total disconnectedness of `G` nor any continuity
of the action is needed, and `A` is a bare abelian group: the resolution of `A` is formed for the
discrete topology, which the final statement does not mention.

## Main definitions

* `TauCeti.ContCohomology.evalLevel`: evaluation at `1` inside every level of the coinduced
  resolution of `Coind_1^G A`.
* `TauCeti.ContCohomology.coindLevel`: spreading a level of the resolution of `A` over `G`, built
  from the family `TauCeti.ContCohomology.shear`, `x ↦ (y ↦ Ψ y (y * x))`.

## Main results

* `TauCeti.ContCohomology.evalLevel_d`: evaluation at `1` is a chain map.
* `TauCeti.ContCohomology.eq_coindLevel_const_evalLevel` and
  `TauCeti.ContCohomology.eq_of_evalLevel_eq`: an invariant element is recovered from, hence
  determined by, its evaluation at `1`.
* `TauCeti.ContCohomology.d_coindLevel_const`: spreading a constant family commutes with the
  differentials.
* `TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot`:
  **`Hⁿ⁺¹(G, Coind_1^G A) = 0`** for every `n`, for a compact group `G`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.3.7), whose
  proof through the standard resolution is the one written here on Mathlib's coinduced
  resolution. NSW write `Ind` for the coinduced module.
* L. Ribes, P. Zalesskii, *Profinite Groups*, Thm. 6.10.5 and Cor. 6.10.6.
-/

public section

open CategoryTheory TopRep

namespace TauCeti.ContCohomology

section Shear

variable {X : Type*} [TopologicalSpace X] [Mul X] [ContinuousMul X] [LocallyCompactSpace X]
  {Z : Type*} [TopologicalSpace Z]

/-- The family `x ↦ (y ↦ Ψ y (y * x))` attached to a two-variable continuous map `Ψ`. Local
compactness makes evaluation continuous, which is what makes the family jointly continuous. -/
noncomputable def shear (Ψ : C(X, C(X, Z))) : C(X, C(X, Z)) :=
  ContinuousMap.curry ⟨fun p : X × X => Ψ p.2 (p.2 * p.1),
    continuous_eval.comp ((Ψ.continuous.comp continuous_snd).prodMk
      (continuous_snd.mul continuous_fst))⟩

@[simp]
theorem shear_apply_apply (Ψ : C(X, C(X, Z))) (x y : X) : shear Ψ x y = Ψ y (y * x) := (rfl)

end Shear

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction (⊥ : Subgroup G) A]

/-- The coefficient object `Coind_1^G A` of this file, as a topological representation. -/
local notation "𝒞" => ofDiscreteModule ℤ G (DiscreteCoind G ⊥ A)

/-- `A` with the trivial action of `G`, as a topological representation. -/
local notation "𝒯" => TopRep.of (ContRepresentation.trivial ℤ G A)

/-! ### Evaluation at `1` inside every level -/

/-- **Evaluation at `1` inside every level** of the coinduced resolution of `Coind_1^G A`:
`evalLevel 0 f = f 1` and `evalLevel (m + 1) F x = evalLevel m (F x)`. It lands in the coinduced
resolution of `A` with the trivial action, and it is not `G`-equivariant. -/
noncomputable def evalLevel : (m : ℕ) → (resolutionX 𝒞 m).V →L[ℤ] (resolutionX 𝒯 m).V
  | 0 => ⟨(DiscreteCoind.eval G ⊥ A).toIntLinearMap, continuous_of_discreteTopology⟩
  | m + 1 => ContinuousLinearMap.compLeftContinuous ℤ G (evalLevel m)

@[simp]
theorem evalLevel_zero_apply (f : DiscreteCoind G ⊥ A) : evalLevel G A 0 f = f 1 :=
  DiscreteCoind.eval_apply f

@[simp]
theorem evalLevel_succ_apply (m : ℕ) (F : (resolutionX 𝒞 (m + 1)).V) (x : G) :
    evalLevel G A (m + 1) F x = evalLevel G A m (F x) := (rfl)

/-- **Evaluation at `1` is a chain map** from the coinduced resolution of `Coind_1^G A` to the
coinduced resolution of `A`. -/
@[simp]
theorem evalLevel_d : ∀ (m : ℕ) (F : (resolutionX 𝒞 m).V),
    evalLevel G A (m + 1) ((d 𝒞 m).hom F) = (d 𝒯 m).hom (evalLevel G A m F)
  | 0, _ => ContinuousMap.ext fun _ => rfl
  | m + 1, F => ContinuousMap.ext fun x => by
    rw [evalLevel_succ_apply, TopRep.hom_d_succ_apply_apply, map_sub, evalLevel_d m,
      TopRep.hom_d_succ_apply_apply, evalLevel_succ_apply]

/-- In degree zero, an element of `Coind_1^G A` whose translates evaluate at `1` to `Ψ` is `Ψ`
itself. -/
theorem eq_ofContinuousMap_of_forall_evalLevel_smul (f : DiscreteCoind G ⊥ A) (Ψ : C(G, A))
    (h : ∀ y : G, evalLevel G A 0 (y • f) = Ψ y) : f = DiscreteCoind.ofContinuousMap G A Ψ :=
  DiscreteCoind.ext fun y => by
    have hy := h y
    rwa [evalLevel_zero_apply, DiscreteCoind.coe_smul, one_mul,
      ← DiscreteCoind.ofContinuousMap_apply G A Ψ y] at hy

/-! ### Spreading a level of the resolution of `A` over `G` -/

variable [CompactSpace G]

/-- **Spreading a level over `G`.** For `Ψ : C(G, C(G, …, C(G, A)))` with `m` inner factors,
`coindLevel m Ψ` is the element `x₁ ↦ ⋯ ↦ xₘ ↦ (y ↦ Ψ y (y x₁) ⋯ (y xₘ))` of level `m` of the
coinduced resolution of `Coind_1^G A`: `coindLevel 0 Ψ` is `Ψ` read as a locally constant map,
and `coindLevel (m + 1) Ψ x = coindLevel m (y ↦ Ψ y (y x))`. On a constant family `Ψ = Φ` it
inverts `evalLevel` on the invariant elements (`eq_coindLevel_const_evalLevel`). -/
noncomputable def coindLevel : (m : ℕ) → C(G, (resolutionX 𝒯 m).V) → (resolutionX 𝒞 m).V
  | 0 => DiscreteCoind.ofContinuousMap G A
  | m + 1 => fun Ψ =>
    (⟨coindLevel m, continuous_of_discreteTopology⟩ :
      C(C(G, (resolutionX 𝒯 m).V), (resolutionX 𝒞 m).V)).comp (shear Ψ)

@[simp]
theorem coindLevel_zero (Ψ : C(G, A)) :
    coindLevel G A 0 Ψ = DiscreteCoind.ofContinuousMap G A Ψ :=
  (rfl)

@[simp]
theorem coindLevel_succ_apply (m : ℕ) (Ψ : C(G, (resolutionX 𝒯 (m + 1)).V)) (x : G) :
    coindLevel G A (m + 1) Ψ x = coindLevel G A m (shear Ψ x) :=
  (rfl)

/-- Evaluation at `1` recovers the parameter of `coindLevel` at `1`. -/
@[simp]
theorem evalLevel_coindLevel : ∀ (m : ℕ) (Ψ : C(G, (resolutionX 𝒯 m).V)),
    evalLevel G A m (coindLevel G A m Ψ) = Ψ 1
  | 0, Ψ => (DiscreteCoind.eval_apply _).trans (DiscreteCoind.ofContinuousMap_apply G A Ψ 1)
  | m + 1, Ψ => ContinuousMap.ext fun x => by
    rw [evalLevel_succ_apply, coindLevel_succ_apply, evalLevel_coindLevel m, shear_apply_apply,
      one_mul]

/-- The action of `G` on the coinduced resolution translates the parameter of `coindLevel`:
`g • coindLevel m Ψ = coindLevel m (y ↦ Ψ (y * g))`. -/
@[simp]
theorem ρ_coindLevel : ∀ (m : ℕ) (g : G) (Ψ : C(G, (resolutionX 𝒯 m).V)),
    (resolutionX 𝒞 m).ρ g (coindLevel G A m Ψ) =
      coindLevel G A m (Ψ.comp (ContinuousMap.mulRight g))
  | 0, g, Ψ => DiscreteCoind.smul_ofContinuousMap G A g Ψ
  | m + 1, g, Ψ => ContinuousMap.ext fun x => by
    rw [TopRep.resolutionX_succ_ρ_apply_apply, coindLevel_succ_apply, ρ_coindLevel m,
      coindLevel_succ_apply]
    congr 1
    ext y
    simp [mul_assoc]

/-- **Reconstruction of a level from its translates.** An element `F` of level `m` of the coinduced
resolution of `Coind_1^G A` whose translates `g • F` evaluate at `1` to `Ψ g` is `coindLevel m Ψ`.
-/
theorem eq_coindLevel_of_forall_evalLevel_ρ : ∀ (m : ℕ) (F : (resolutionX 𝒞 m).V)
    (Ψ : C(G, (resolutionX 𝒯 m).V)),
    (∀ y : G, evalLevel G A m ((resolutionX 𝒞 m).ρ y F) = Ψ y) → F = coindLevel G A m Ψ
  | 0, F, Ψ, h => eq_ofContinuousMap_of_forall_evalLevel_smul G A F Ψ h
  | m + 1, F, Ψ, h => ContinuousMap.ext fun x => by
    rw [coindLevel_succ_apply]
    refine eq_coindLevel_of_forall_evalLevel_ρ m (F x) (shear Ψ x) fun y => ?_
    have hy := congrArg (fun Φ : (resolutionX 𝒯 (m + 1)).V => Φ (y * x)) (h y)
    rw [evalLevel_succ_apply, TopRep.resolutionX_succ_ρ_apply_apply, inv_mul_cancel_left] at hy
    rw [shear_apply_apply]
    exact hy

/-- **An invariant level is recovered from its evaluation at `1`**: an invariant `F` is
`coindLevel m` of the constant family at `evalLevel m F`. -/
theorem eq_coindLevel_const_evalLevel (m : ℕ) (F : (resolutionX 𝒞 m).V)
    (hF : ∀ g : G, (resolutionX 𝒞 m).ρ g F = F) :
    F = coindLevel G A m (ContinuousMap.const G (evalLevel G A m F)) :=
  eq_coindLevel_of_forall_evalLevel_ρ G A m F _ fun y => by rw [hF y]; rfl

/-- Evaluation at `1` is injective on the invariant elements of every level. -/
theorem eq_of_evalLevel_eq (m : ℕ) {F F' : (resolutionX 𝒞 m).V}
    (hF : ∀ g : G, (resolutionX 𝒞 m).ρ g F = F) (hF' : ∀ g : G, (resolutionX 𝒞 m).ρ g F' = F')
    (h : evalLevel G A m F = evalLevel G A m F') : F = F' := by
  rw [eq_coindLevel_const_evalLevel G A m F hF, eq_coindLevel_const_evalLevel G A m F' hF', h]

/-- The constant family at a level of the resolution of `A` spreads to an invariant element. -/
theorem ρ_coindLevel_const (m : ℕ) (g : G) (Φ : (resolutionX 𝒯 m).V) :
    (resolutionX 𝒞 m).ρ g (coindLevel G A m (ContinuousMap.const G Φ)) =
      coindLevel G A m (ContinuousMap.const G Φ) := by
  rw [ρ_coindLevel, ContinuousMap.const_comp]

/-- **Spreading a constant family commutes with the differentials**: the differential of the
coinduced resolution of `Coind_1^G A` carries `coindLevel m` of the constant family at `Φ` to
`coindLevel (m + 1)` of the constant family at `d m Φ`. With `evalLevel_d`, this makes
`coindLevel` on constant families a chain map, inverse to `evalLevel` on the invariant elements. -/
@[simp]
theorem d_coindLevel_const (m : ℕ) (Φ : (resolutionX 𝒯 m).V) :
    (d 𝒞 m).hom (coindLevel G A m (ContinuousMap.const G Φ)) =
      coindLevel G A (m + 1) (ContinuousMap.const G ((d 𝒯 m).hom Φ)) := by
  refine (eq_coindLevel_const_evalLevel G A (m + 1) _ fun g => ?_).trans ?_
  · rw [← TopRep.hom_comm_apply, ρ_coindLevel_const]
  · rw [evalLevel_d, evalLevel_coindLevel, ContinuousMap.const_apply]

/-! ### Acyclicity -/

/-- The acyclicity theorem, with the discrete topology on `A` available as an instance for the
resolution of `A`. -/
private theorem subsingleton_continuousCohomology_discreteCoind_bot_aux (n : ℕ) :
    Subsingleton (continuousCohomology (n + 1) 𝒞) := by
  refine subsingleton_of_forall_eq 0 fun c => ?_
  obtain ⟨z, rfl⟩ := HomologicalComplex.homologyπ_surjective (homogeneousCochains 𝒞) (n + 1) c
  rw [HomologicalComplex.homologyπ_eq_zero_iff _ _ (CochainComplex.prev_nat_succ n)]
  -- the cocycle, an invariant element of level `n + 2` killed by the differential
  have hF : (d 𝒞 (n + 2)).hom (Subtype.val ((homogeneousCochains 𝒞).iCycles (n + 1) z)) = 0 := by
    have h : ((homogeneousCochains 𝒞).d (n + 1) (n + 2)).hom
        ((homogeneousCochains 𝒞).iCycles (n + 1) z) = 0 :=
      ConcreteCategory.congr_hom ((homogeneousCochains 𝒞).iCycles_d (n + 1) (n + 2)) z
    have h' := congrArg Subtype.val h
    rwa [homogeneousCochains.d_apply, Submodule.coe_zero] at h'
  -- its evaluation is a cocycle of the resolution of `A`, hence the differential of its value at
  -- `1`
  have hΦ : (d 𝒯 (n + 2)).hom
      (evalLevel G A (n + 2) (Subtype.val ((homogeneousCochains 𝒞).iCycles (n + 1) z))) = 0 := by
    rw [← evalLevel_d, hF, map_zero]
  have hΦ' := TopRep.d_apply_one_add_d_apply_one 𝒯 (n + 1)
    (evalLevel G A (n + 2) (Subtype.val ((homogeneousCochains 𝒞).iCycles (n + 1) z)))
  rw [hΦ, ContinuousMap.zero_apply, add_zero] at hΦ'
  -- spread that value back over `G`: an invariant cochain of degree `n`
  refine ⟨⟨coindLevel G A (n + 1) (ContinuousMap.const G
    (evalLevel G A (n + 2) (Subtype.val ((homogeneousCochains 𝒞).iCycles (n + 1) z)) 1)),
    fun g => ρ_coindLevel_const G A (n + 1) g _⟩, ?_⟩
  -- its differential spreads `d (Φ 1) = Φ` over `G`, which is the invariant cocycle itself
  refine TopModuleCat.injective_of_mono ((homogeneousCochains 𝒞).iCycles (n + 1)) ?_
  refine (ConcreteCategory.congr_hom ((homogeneousCochains 𝒞).toCycles_i n (n + 1)) _).trans ?_
  refine Subtype.ext ?_
  rw [homogeneousCochains.d_apply, d_coindLevel_const, hΦ']
  exact (eq_coindLevel_const_evalLevel G A (n + 2) _
    ((homogeneousCochains 𝒞).iCycles (n + 1) z).2).symm

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- **`Coind_1^G A` is acyclic in every positive degree.** For a compact group `G` and an abelian
group `A`, the continuous cohomology `Hⁿ⁺¹(G, Coind_1^G A)` of the locally constant maps `G → A`
under right translation vanishes for every `n`. The action of the trivial subgroup `⊥` on `A`
carried by `Coind_1^G A` is arbitrary, for instance the restriction of an action of `G` on `A`: the
equivariance condition it imposes is vacuous, so it does not change the underlying group of
locally constant maps. -/
instance subsingleton_continuousCohomology_discreteCoind_bot (n : ℕ) :
    Subsingleton (continuousCohomology (n + 1) 𝒞) :=
  -- the proof runs through the coinduced resolution of `A`, which needs `A` discrete
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  subsingleton_continuousCohomology_discreteCoind_bot_aux G A n

end TauCeti.ContCohomology
