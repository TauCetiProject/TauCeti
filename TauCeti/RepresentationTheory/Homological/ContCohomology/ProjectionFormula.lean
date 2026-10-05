/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product

/-!
# The projection formula for the explicit low-degree cup products

The corestriction of a finite-index subgroup `U ≤ G` is not linear over the cohomology of `G`, but
it is a map of modules over it: restricting a class of `G` to `U`, cupping there, and corestricting
back is the same as cupping with the corestricted class. That is the **projection formula**

```text
cor (res a ⌣ b) = a ⌣ cor b,        cor (b ⌣ res n) = cor b ⌣ n,
```

proved here in all six low-degree shapes.

In the five shapes with a degree-`0` factor that factor is invariant, so partial application of the
pairing at it is an *equivariant* additive map — `TauCeti.ContCohomology.pairingLeft` in the first
display and `TauCeti.ContCohomology.pairingRight` in the second — and the cup with a degree-`0`
class is the coefficient map that equivariant map induces. In positive degrees the projection
formula is therefore exactly naturality of the corestriction cochain in an equivariant coefficient
map, `TauCeti.ContCohomology.map_cochainsCor1` and `map_cochainsCor2`, and in those five shapes it
holds already on cochains, with no coboundary correction. Those two cochain identities are stated
for a variable transversal, so the statements below transport to any other transversal through
`TauCeti.ContCohomology.explicitCor1_eq_transversal` and `explicitCor2_eq_transversal`. In the
`(1,0)` and `(2,0)` shapes
the translation factors `g •` and `(g * h) •` of the cup formula are absorbed by the invariance of
the degree-`0` factor before that naturality is applied; in degree `0` the same absorption is
`TauCeti.ContCohomology.pairingLeft_smul` applied to each summand of the norm.

The `(1,1)` shape, the one shape of the six without a degree-`0` factor, is the one shape where
the two sides do *not* agree on cochains: the degree-two corestriction pairs the transversal word
of the first variable with the *translated* transversal word of the second, so the two sides
differ by a coboundary. That coboundary is exhibited by the explicit `1`-cochain
`TauCeti.ContCohomology.cup11ProjectionHomotopy`,

```text
kᵗ(γ) = ∑ u : G ⧸ U, μ (a (t u)) (t u • b (ℓᵗ_u γ)),
```

whose `d¹` is the difference of the two sides
(`TauCeti.ContCohomology.cup11ProjectionHomotopy_spec`); the identity on classes follows.

## Main statements

* `TauCeti.ContCohomology.explicitCup_projection`: the `(0,1)` shape
  `cor¹ (res⁰ a ⌣ b) = a ⌣ cor¹ b`. The roadmap's `Suggested.lean` fixes the unsuffixed name for
  this shape, which is why the five companions below carry their bidegree and this one does not.
* `TauCeti.ContCohomology.explicitCup_projection00`,
  `TauCeti.ContCohomology.explicitCup_projection10`,
  `TauCeti.ContCohomology.explicitCup_projection02` and
  `TauCeti.ContCohomology.explicitCup_projection20`: the same identity in the four remaining
  low-degree shapes with a degree-`0` factor.
* `TauCeti.ContCohomology.explicitCup_projection11`: the `(1,1)` shape
  `cor² (res¹ a ⌣ b) = a ⌣ cor¹ b`, deduced from
  `TauCeti.ContCohomology.cup11ProjectionHomotopy_spec`.
* `TauCeti.ContCohomology.explicitCup_projection10_res_left` and
  `TauCeti.ContCohomology.explicitCup_projection20_res_left`: the `(1,0)` and `(2,0)` shapes with
  the restriction on the cocycle factor, `cor (res a ⌣ n) = a ⌣ cor⁰ n`, deduced from the
  homotopies `TauCeti.ContCohomology.cup10ProjectionHomotopy_spec` and
  `TauCeti.ContCohomology.cup20ProjectionHomotopy_spec`. With the six shapes above, the projection
  formula with the restriction on the first factor holds in every bidegree of total degree at most
  two.

This implements the projection-formula item of the "compatibilities" milestone of Layer 8 of the
human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.3)(iv): the
  projection formula for the cup product and the corestriction.
* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., 7.9.6 and 7.9.7.
* K. Brown, *Cohomology of Groups*, V (3.8).
-/

public section

namespace TauCeti.ContCohomology

universe u v w x

section DegreeZero

/-! ### The degree-zero shape

`H⁰` is a subgroup and not a quotient, so neither a topology on `G` nor continuity of the pairing
is involved. -/

variable (G : Type u) [Group G]
  (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (N : Type w) [AddCommGroup N] [DistribMulAction G N]
  (P : Type x) [AddCommGroup P] [DistribMulAction G P]
  (U : Subgroup G) [U.FiniteIndex]
  (μ : M →+ N →+ P)
  (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)

/-- **The `(0,0)` projection formula**, `cor⁰ (res⁰ a ⌣ n) = a ⌣ cor⁰ n`: the norm of a pairing
with a `G`-invariant first argument is that pairing applied to the norm. The whole content is that
the transversal factors cross the pairing, which is
`TauCeti.ContCohomology.pairingLeft_smul`. -/
theorem explicitCup_projection00 (a : H0 G M) (n : H0 U N) :
    explicitCor0 G P U
        (explicitCup00 U M N P μ (fun g m y => hequiv (g : G) m y) (explicitRes0 G M U a) n) =
      explicitCup00 G M N P μ hequiv a (explicitCor0 G N U n) := by
  refine Subtype.ext ?_
  simp only [coe_explicitCor0, coe_explicitCup00, coe_explicitRes0]
  rw [map_sum]
  exact Finset.sum_congr rfl fun u _ => (pairingLeft_smul μ hequiv a _ _).symm

end DegreeZero

section DegreeOne

/-! ### The degree-one shapes

Openness of `U` enters exactly as in `TauCeti.ContCohomology.explicitCor1`: it is what makes the
corestriction of a continuous cochain continuous. -/

section ExplicitCup01

variable (G : Type u) [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  (N : Type w) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type x) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)

include hU hμ hequiv

/-- **The `(0,1)` projection formula**, `cor¹ (res⁰ a ⌣ b) = a ⌣ cor¹ b` for an open subgroup `U`
of finite index. The roadmap's `Suggested.lean` fixes the name `explicitCup_projection` for this
shape, and it fixes the normalization of the four companion shapes. -/
theorem explicitCup_projection (a : H0 G M) (b : H1 U N) :
    explicitCor1 G P U hU
        (explicitCup01 U M N P μ hμ (fun g m y => hequiv (g : G) m y)
          (explicitRes0 G M U a) b) =
      explicitCup01 G M N P μ hμ hequiv a (explicitCor1 G N U hU b) := by
  -- Replace `res⁰ a` by an element whose underlying coefficient is literally `a`, so that the
  -- cup cochains on the two sides are pairings against the same element of `M`.
  have hres : explicitRes0 G M U a = ⟨(a : M), fun g : U => a.2 (g : G)⟩ :=
    Subtype.ext (coe_explicitRes0 G M U a)
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [hres, explicitCup01_mk, explicitCor1_mk, explicitCor1_mk, explicitCup01_mk]
    refine congrArg (fun z : Z1 G P => (z : H1 G P)) (Subtype.ext ?_)
    simp only [coe_cocyclesCor1]
    funext γ
    exact (map_cochainsCor1 G N U Quotient.out Quotient.out_eq (μ (a : M))
      (fun g y => pairingLeft_smul μ hequiv a g y) (c : U → N) γ).symm

end ExplicitCup01

section ExplicitCup10

variable (G : Type u) [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type w) [AddCommGroup N] [TopologicalSpace N] [DistribMulAction G N]
  (P : Type x) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)

include hU hμ hequiv

/-- **The `(1,0)` projection formula**, `cor¹ (b ⌣ res⁰ n) = cor¹ b ⌣ n`. The translation factors
of the `(1,0)` cochain formula act trivially on the invariant `n`, which is what leaves a plain
naturality statement behind. -/
theorem explicitCup_projection10 (b : H1 U M) (n : H0 G N) :
    explicitCor1 G P U hU
        (explicitCup10 U M N P μ hμ (fun g m y => hequiv (g : G) m y) b
          (explicitRes0 G N U n)) =
      explicitCup10 G M N P μ hμ hequiv (explicitCor1 G M U hU b) n := by
  have hn : ∀ g : G, g • (n : N) = (n : N) := n.2
  have hres : explicitRes0 G N U n = ⟨(n : N), fun g : U => n.2 (g : G)⟩ :=
    Subtype.ext (coe_explicitRes0 G N U n)
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [hres, explicitCup10_mk, explicitCor1_mk, explicitCor1_mk, explicitCup10_mk]
    refine congrArg (fun z : Z1 G P => (z : H1 G P)) (Subtype.ext ?_)
    simp only [coe_cocyclesCor1, Subgroup.smul_def, hn]
    funext γ
    have key := map_cochainsCor1 G M U Quotient.out Quotient.out_eq (μ.flip (n : N))
      (fun g m => pairingRight_smul μ hequiv n g m) (c : U → M) γ
    simp only [AddMonoidHom.flip_apply] at key
    exact key.symm

end ExplicitCup10

end DegreeOne

section DegreeTwo

/-! ### The degree-two shapes

The `2`-cochains of the subgroup are functions on `U × U`, so the cup products over `U` need `U`
to be a topological group. Degree one needs separately continuous multiplication on `G`;
degree two uses `[IsTopologicalGroup G]` to obtain the corresponding structure on `U`. -/

section ExplicitCup02

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  (N : Type w) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type x) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)

include hU hμ hequiv

/-- **The `(0,2)` projection formula**, `cor² (res⁰ a ⌣ b) = a ⌣ cor² b`. -/
theorem explicitCup_projection02 (a : H0 G M) (b : H2 U N) :
    explicitCor2 G P U hU
        (explicitCup02 U M N P μ hμ (fun g m y => hequiv (g : G) m y)
          (explicitRes0 G M U a) b) =
      explicitCup02 G M N P μ hμ hequiv a (explicitCor2 G N U hU b) := by
  have hres : explicitRes0 G M U a = ⟨(a : M), fun g : U => a.2 (g : G)⟩ :=
    Subtype.ext (coe_explicitRes0 G M U a)
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [hres, explicitCup02_mk, explicitCor2_mk, explicitCor2_mk, explicitCup02_mk]
    refine congrArg (fun z : Z2 G P => (z : H2 G P)) (Subtype.ext ?_)
    simp only [coe_cocyclesCor2]
    funext q
    obtain ⟨γ, η⟩ := q
    exact (map_cochainsCor2 G N U Quotient.out Quotient.out_eq (μ (a : M))
      (fun g y => pairingLeft_smul μ hequiv a g y) (c : U × U → N) γ η).symm

end ExplicitCup02

section ExplicitCup20

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type w) [AddCommGroup N] [TopologicalSpace N] [DistribMulAction G N]
  (P : Type x) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)

include hU hμ hequiv

/-- **The `(2,0)` projection formula**, `cor² (b ⌣ res⁰ n) = cor² b ⌣ n`. -/
theorem explicitCup_projection20 (b : H2 U M) (n : H0 G N) :
    explicitCor2 G P U hU
        (explicitCup20 U M N P μ hμ (fun g m y => hequiv (g : G) m y) b
          (explicitRes0 G N U n)) =
      explicitCup20 G M N P μ hμ hequiv (explicitCor2 G M U hU b) n := by
  have hn : ∀ g : G, g • (n : N) = (n : N) := n.2
  have hres : explicitRes0 G N U n = ⟨(n : N), fun g : U => n.2 (g : G)⟩ :=
    Subtype.ext (coe_explicitRes0 G N U n)
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [hres, explicitCup20_mk, explicitCor2_mk, explicitCor2_mk, explicitCup20_mk]
    refine congrArg (fun z : Z2 G P => (z : H2 G P)) (Subtype.ext ?_)
    simp only [coe_cocyclesCor2, Subgroup.smul_def, hn]
    funext q
    obtain ⟨γ, η⟩ := q
    have key := map_cochainsCor2 G M U Quotient.out Quotient.out_eq (μ.flip (n : N))
      (fun g m => pairingRight_smul μ hequiv n g m) (c : U × U → M) γ η
    simp only [AddMonoidHom.flip_apply] at key
    exact key.symm

end ExplicitCup20

end DegreeTwo

section CupOneOneHomotopy

/-! ### The `(1,1)` homotopy

The `(1,1)` shape is the one shape of the six in which neither factor is invariant, and the two
sides of the projection formula are genuinely different cochains. Their difference is a
coboundary, and this section writes down a primitive for it. Nothing here needs a topology: the
identity `TauCeti.ContCohomology.cup11ProjectionHomotopy_spec` is an identity of plain cochains,
just like the corestriction cochain identities it is proved from. -/

section Def

variable (G : Type u) [Group G]
  (M : Type v) [AddCommGroup M]
  (N : Type w) [AddCommGroup N] [DistribMulAction G N]
  (P : Type x) [AddCommGroup P]
  (U : Subgroup G) [U.FiniteIndex]
  (μ : M →+ N →+ P)
  (t : G ⧸ U → G) (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **The `(1,1)` projection-formula homotopy** for a transversal `t`,

```text
kᵗ(γ) = ∑ u : G ⧸ U, μ (α (t u)) (t u • β (ℓᵗ_u γ)),
```

where `ℓᵗ` is the transversal word `TauCeti.lWord`. It is the corestriction sum of the pairing of
`α` against `β`, evaluated at the transversal representatives in the first variable and at the
transversal words in the second. Its `d¹` is the difference of the two sides of the `(1,1)`
projection formula, `TauCeti.ContCohomology.cup11ProjectionHomotopy_spec`. -/
noncomputable def cup11ProjectionHomotopy (α : G → M) (β : U → N) (γ : G) : P :=
  ∑ u : G ⧸ U, μ (α (t u)) (t u • β ⟨lWord U t u γ, lWord_mem U t ht u γ⟩)

/-- The defining formula for the `(1,1)` projection-formula homotopy. -/
@[simp]
theorem cup11ProjectionHomotopy_apply (α : G → M) (β : U → N) (γ : G) :
    cup11ProjectionHomotopy G M N P U μ t ht α β γ =
      ∑ u : G ⧸ U, μ (α (t u)) (t u • β ⟨lWord U t u γ, lWord_mem U t ht u γ⟩) := (rfl)

/-- The homotopy at a product: by the `1`-cocycle law of `β`, `kᵗ(γη)` is `kᵗ(γ)` plus the sum
pairing `α (t (γ • u))` against `(γ * t u) • β (ℓᵗ_u η)`. -/
private theorem cup11ProjectionHomotopy_mul (α : G → M) {β : U → N}
    (hβ : groupCohomology.IsCocycle₁ β) (γ η : G) :
    cup11ProjectionHomotopy G M N P U μ t ht α β (γ * η) =
      cup11ProjectionHomotopy G M N P U μ t ht α β γ +
        ∑ u : G ⧸ U, μ (α (t (γ • u)))
          ((γ * t u) • β ⟨lWord U t u η, lWord_mem U t ht u η⟩) := by
  -- The cocycle law of `β` at `ℓᵗ_u(γ) * ℓᵗ_{γ⁻¹ • u}(η) = ℓᵗ_u(γ * η)` splits each summand.
  simp only [cup11ProjectionHomotopy_apply, smul_apply_lWord_mul_of_isCocycle₁ G N U t ht hβ γ η,
    map_add, Finset.sum_add_distrib]
  -- Reindex the second sum by translation by `γ`.
  refine congrArg _ (Fintype.sum_equiv (MulAction.toPerm γ) _ _ fun u => ?_).symm
  simp only [MulAction.toPerm_apply, inv_smul_smul]

end Def

variable (G : Type u) [Group G]
  (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (N : Type w) [AddCommGroup N] [DistribMulAction G N]
  (P : Type x) [AddCommGroup P] [DistribMulAction G P]
  (U : Subgroup G) [U.FiniteIndex]
  (μ : M →+ N →+ P)
  (t : G ⧸ U → G) (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Translating the homotopy: `γ • kᵗ(η)` pairs `γ • α (t u)` against `(γ * t u) • β (ℓᵗ_u η)`. -/
private theorem smul_cup11ProjectionHomotopy
    (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y) (α : G → M) (β : U → N)
    (γ η : G) :
    γ • cup11ProjectionHomotopy G M N P U μ t ht α β η =
      ∑ u : G ⧸ U, μ (γ • α (t u)) ((γ * t u) • β ⟨lWord U t u η, lWord_mem U t ht u η⟩) := by
  simp only [cup11ProjectionHomotopy_apply, Finset.smul_sum, ← hequiv, mul_smul]

/-- The corestriction side of the `(1,1)` projection formula, reindexed by translation by `γ` so
that its second pairing argument is `(γ * t u) • β (ℓᵗ_u η)`; the cocycle law of `α` then turns
its first pairing argument into `γ • α (t u) - α (t (γ • u)) + α γ`. -/
private theorem cochainsCor2_cup11_res_eq_sum
    (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y) {α : G → M}
    (hα : groupCohomology.IsCocycle₁ α) (β : U → N) (γ η : G) :
    cochainsCor2 G P U t ht (fun q : U × U => μ (α (q.1 : G)) ((q.1 : G) • β q.2)) (γ, η) =
      ∑ u : G ⧸ U, μ (γ • α (t u) - α (t (γ • u)) + α γ)
        ((γ * t u) • β ⟨lWord U t u η, lWord_mem U t ht u η⟩) := by
  rw [cochainsCor2_apply]
  refine (Fintype.sum_equiv (MulAction.toPerm γ) _ _ fun u => ?_).symm
  simp only [MulAction.toPerm_apply, inv_smul_smul]
  rw [← smul_apply_lWord_of_isCocycle₁ G M U t hα, ← hequiv, smul_smul, transversal_smul_mul_lWord]

/-- **The `(1,1)` projection formula on cochains, up to the explicit coboundary.** For a `1`-cocycle
`α` of `G` and a `1`-cocycle `β` of `U`, the difference between the corestriction of the cup of
`α|_U` with `β` and the cup of `α` with the corestriction of `β` is `d¹` of
`TauCeti.ContCohomology.cup11ProjectionHomotopy`. -/
theorem cup11ProjectionHomotopy_spec
    (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)
    {α : G → M} (hα : groupCohomology.IsCocycle₁ α)
    {β : U → N} (hβ : groupCohomology.IsCocycle₁ β) (γ η : G) :
    γ • cup11ProjectionHomotopy G M N P U μ t ht α β η -
        cup11ProjectionHomotopy G M N P U μ t ht α β (γ * η) +
        cup11ProjectionHomotopy G M N P U μ t ht α β γ =
      cochainsCor2 G P U t ht (fun q : U × U => μ (α (q.1 : G)) ((q.1 : G) • β q.2)) (γ, η) -
        μ (α γ) (γ • cochainsCor1 G N U t ht β η) := by
  -- The whole content is the transversal identity `TauCeti.transversal_smul_mul_lWord`, applied
  -- twice: once to move the factor `t u •` of the corestriction across the pairing on the
  -- left-hand side, and once, through the cocycle law for `α`, to turn the value
  -- `t (γ • u) • α (ℓᵗ_{γ • u} γ)` that appears there into `γ • α (t u) - α (t (γ • u)) + α γ`.
  -- The first two of those three terms are what `d¹` of the homotopy contributes and the third is
  -- the right-hand side.
  -- The rewrites below index all four sums so that their second pairing argument is
  -- `(γ * t u) • β (ℓᵗ_u η)`; only the first argument differs.
  rw [smul_cup11ProjectionHomotopy G M N P U μ t ht hequiv,
    cup11ProjectionHomotopy_mul G M N P U μ t ht α hβ,
    cochainsCor2_cup11_res_eq_sum G M N P U μ t ht hequiv hα]
  simp only [cochainsCor1_apply, Finset.smul_sum, map_sum, mul_smul, map_sub, map_add,
    AddMonoidHom.sub_apply, AddMonoidHom.add_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

end CupOneOneHomotopy

section CupOneOne

/-! ### The `(1,1)` shape

Continuity of the homotopy is what makes it a primitive in `B²`, which is the image of the
*continuous* `1`-cochains, and it comes — as everywhere in this file — from openness of `U`
through `TauCeti.continuous_lWord`. -/

section ContinuousHomotopy

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M]
  (N : Type w) [AddCommGroup N] [TopologicalSpace N] [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type x) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
  (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (t : G ⧸ U → G) (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

include hU hμ

/-- The `(1,1)` projection-formula homotopy of continuous data is continuous. As for the
corestriction cochains themselves, no continuity is required of the transversal `t`. -/
theorem continuous_cup11ProjectionHomotopy (α : G → M) {β : U → N} (hβ : Continuous β) :
    Continuous (cup11ProjectionHomotopy G M N P U μ t ht α β) := by
  -- Put the cochain in the pointwise-sum form `continuous_finsetSum` expects.
  rw [funext (cup11ProjectionHomotopy_apply G M N P U μ t ht α β)]
  exact continuous_finsetSum _ fun u _ =>
    hμ.comp (continuous_const.prodMk
      ((hβ.comp ((continuous_lWord U t hU u).subtype_mk _)).const_smul (t u)))

end ContinuousHomotopy

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type w) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type x) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

include hU hμ hequiv

/-- **The `(1,1)` projection formula**, `cor² (res¹ a ⌣ b) = a ⌣ cor¹ b`. Unlike the five shapes
with a degree-`0` factor, this one is not an identity of cochains: the two sides differ by `d¹` of
`TauCeti.ContCohomology.cup11ProjectionHomotopy`, which is
`TauCeti.ContCohomology.cup11ProjectionHomotopy_spec`. -/
theorem explicitCup_projection11 (a : H1 G M) (b : H1 U N) :
    explicitCor2 G P U hU
        (explicitCup11 U M N P μ hμ (fun g m y => hequiv (g : G) m y)
          (explicitRes1 G M U a) b) =
      explicitCup11 G M N P μ hμ hequiv a (explicitCor1 G N U hU b) := by
  induction a using QuotientAddGroup.induction_on with
  | _ α =>
    induction b using QuotientAddGroup.induction_on with
    | _ c =>
      simp only [explicitRes1_mk, explicitCor1_mk, explicitCup11_mk, explicitCor2_mk,
        H2pi_eq_iff]
      refine mem_B2_iff'.2 ⟨cup11ProjectionHomotopy G M N P U μ Quotient.out Quotient.out_eq
        (α : G → M) (c : U → N),
        continuous_cup11ProjectionHomotopy G M N P U hU μ hμ Quotient.out Quotient.out_eq
          (α : G → M) (mem_Z1_iff.1 c.2).1, fun γ η => ?_⟩
      -- Restriction is evaluation of the cochain at the inclusion, by `cocyclesMap1_apply`.
      simp only [Pi.sub_apply, coe_cocyclesCor2, coe_cocyclesCor1, cocyclesMap1_apply,
        Subgroup.smul_def]
      exact cup11ProjectionHomotopy_spec G M N P U μ Quotient.out Quotient.out_eq hequiv
        (mem_Z1_iff.1 α.2).2 (mem_Z1_iff.1 c.2).2 γ η

end CupOneOne

section ResLeftHomotopy

/-! ### Restricting the positive-degree factor: the homotopies

In the `(1,0)` and `(2,0)` shapes above the restricted factor is the invariant one. With the
restriction on the cocycle instead, `cor (res a ⌣ n) = a ⌣ cor⁰ n`, the two sides again differ on
cochains, and this section writes down the primitives. As for the `(1,1)` homotopy, nothing here
needs a topology.

The invariance of `n` under `U` is what makes every translate `(t u * ℓᵗ_u γ) • n` equal to
`t u • n`, so that all the sums below have the fixed second pairing argument `t u • n`; what moves
is only the first argument, and there the cocycle law of `α` does the work. -/

section Def

variable (G : Type u) [Group G]
  (M : Type v) [AddCommGroup M]
  (N : Type w) [AddCommGroup N] [DistribMulAction G N]
  (P : Type x) [AddCommGroup P]
  (U : Subgroup G) [U.FiniteIndex]
  (μ : M →+ N →+ P)
  (t : G ⧸ U → G)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **The `(1,0)` projection-formula homotopy** for restriction on the cocycle factor and a
transversal `t`, the `0`-cochain `∑ u : G ⧸ U, μ (α (t u)) (t u • n)`. Its `d⁰` is the difference
of the two sides of `cor¹ (res¹ α ⌣ n) = α ⌣ cor⁰ n`,
`TauCeti.ContCohomology.cup10ProjectionHomotopy_spec`. -/
noncomputable def cup10ProjectionHomotopy (α : G → M) (n : N) : P :=
  ∑ u : G ⧸ U, μ (α (t u)) (t u • n)

/-- The defining formula for the `(1,0)` projection-formula homotopy. -/
@[simp]
theorem cup10ProjectionHomotopy_apply (α : G → M) (n : N) :
    cup10ProjectionHomotopy G M N P U μ t α n = ∑ u : G ⧸ U, μ (α (t u)) (t u • n) := (rfl)

/-- **The `(2,0)` projection-formula homotopy** for restriction on the cocycle factor and a
transversal `t`,

```text
kᵗ(γ) = ∑ u : G ⧸ U, μ (α (t u, ℓᵗ_u γ) - α (γ, t (γ⁻¹ • u))) (t u • n),
```

where `ℓᵗ` is the transversal word `TauCeti.lWord`. Its `d¹` is the difference of the two sides of
`cor² (res² α ⌣ n) = α ⌣ cor⁰ n`, `TauCeti.ContCohomology.cup20ProjectionHomotopy_spec`. -/
noncomputable def cup20ProjectionHomotopy (α : G × G → M) (n : N) (γ : G) : P :=
  ∑ u : G ⧸ U, μ (α (t u, lWord U t u γ) - α (γ, t (γ⁻¹ • u))) (t u • n)

/-- The defining formula for the `(2,0)` projection-formula homotopy. -/
@[simp]
theorem cup20ProjectionHomotopy_apply (α : G × G → M) (n : N) (γ : G) :
    cup20ProjectionHomotopy G M N P U μ t α n γ =
      ∑ u : G ⧸ U, μ (α (t u, lWord U t u γ) - α (γ, t (γ⁻¹ • u))) (t u • n) := (rfl)

end Def

section TransversalSubgroup

variable (G : Type u) [Group G]
  (M : Type v) [AddCommGroup M]
  (N : Type w) [AddCommGroup N] [DistribMulAction G N]
  (P : Type x) [AddCommGroup P]
  (U : Subgroup G)
  (μ : M →+ N →+ P)
  (t : G ⧸ U → G) (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)

include ht

/-- For a `U`-invariant `n`, the translate `(γ * t (γ⁻¹ • u)) • n` is `t u • n`: the group element
is `t u * ℓᵗ_u γ`, and the transversal word acts trivially. -/
private theorem mul_transversal_inv_smul_smul {n : N} (hn : n ∈ H0 U N) (u : G ⧸ U) (γ : G) :
    (γ * t (γ⁻¹ • u)) • n = t u • n := by
  rw [← transversal_mul_lWord U t u γ, mul_smul]
  exact congrArg (t u • ·) ((FixedPoints.mem_addSubgroup U N n).1 hn ⟨_, lWord_mem U t ht u γ⟩)

variable [U.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Summing the values `(γ * t u) • n` of a `U`-invariant `n` against coefficients `c u` is
summing `t u • n` against the reindexed coefficients `c (γ⁻¹ • u)`: the reindexing step shared by
the two homotopy identities. -/
private theorem sum_smul_mul_transversal_smul {n : N} (hn : n ∈ H0 U N) (c : G ⧸ U → M) (γ : G) :
    ∑ u : G ⧸ U, μ (c u) ((γ * t u) • n) = ∑ u : G ⧸ U, μ (c (γ⁻¹ • u)) (t u • n) := by
  refine (Fintype.sum_equiv (MulAction.toPerm γ⁻¹) _ _ fun u => ?_).symm
  rw [MulAction.toPerm_apply, mul_transversal_inv_smul_smul G N U t ht hn]

end TransversalSubgroup

section CocycleHelper

variable (G : Type u) [Group G]
  (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (U : Subgroup G)
  (t : G ⧸ U → G)

/-- The `2`-cocycle identity behind the `(2,0)` homotopy: at `x = t u`, `y = ℓᵗ_u γ`,
`z = ℓᵗ_{γ⁻¹ • u} η`, with `x * y = γ * t (γ⁻¹ • u)` and `y * z = ℓᵗ_u (γη)`, the cocycle law of
`α` at the three triples `(x, y, z)`, `(γ, t (γ⁻¹ • u), z)` and `(γ, η, t ((γη)⁻¹ • u))` expresses
`t u • α (y, z) - α (γ, η)` through the values of the homotopy's coefficient
`c_u(γ) = α (t u, ℓᵗ_u γ) - α (γ, t (γ⁻¹ • u))`. -/
private theorem transversal_smul_apply_lWord_sub_of_isCocycle₂ {α : G × G → M}
    (hα : groupCohomology.IsCocycle₂ α) (u : G ⧸ U) (γ η : G) :
    t u • α (lWord U t u γ, lWord U t (γ⁻¹ • u) η) - α (γ, η) =
      γ • (α (t (γ⁻¹ • u), lWord U t (γ⁻¹ • u) η) - α (η, t (η⁻¹ • γ⁻¹ • u))) -
        (α (t u, lWord U t u (γ * η)) - α (γ * η, t ((γ * η)⁻¹ • u))) +
        (α (t u, lWord U t u γ) - α (γ, t (γ⁻¹ • u))) := by
  have h₁ := hα (t u) (lWord U t u γ) (lWord U t (γ⁻¹ • u) η)
  have h₂ := hα γ (t (γ⁻¹ • u)) (lWord U t (γ⁻¹ • u) η)
  have h₃ := hα γ η (t (η⁻¹ • γ⁻¹ • u))
  rw [transversal_mul_lWord, lWord_mul_lWord] at h₁
  rw [transversal_mul_lWord] at h₂
  rw [mul_inv_rev, mul_smul]
  -- `h₁` expresses `t u • α (y, z)`, `h₂` expresses `α (γ * t (γ⁻¹ • u), z)` and `h₃` expresses
  -- `α (γ, η * t ((γη)⁻¹ • u))`; eliminating the latter two from the first leaves the claim.
  have e₁ : t u • α (lWord U t u γ, lWord U t (γ⁻¹ • u) η) =
      α (γ * t (γ⁻¹ • u), lWord U t (γ⁻¹ • u) η) + α (t u, lWord U t u γ) -
        α (t u, lWord U t u (γ * η)) := eq_sub_of_add_eq h₁.symm
  have e₂ : α (γ * t (γ⁻¹ • u), lWord U t (γ⁻¹ • u) η) =
      γ • α (t (γ⁻¹ • u), lWord U t (γ⁻¹ • u) η) + α (γ, η * t (η⁻¹ • γ⁻¹ • u)) -
        α (γ, t (γ⁻¹ • u)) := eq_sub_of_add_eq h₂
  have e₃ : α (γ, η * t (η⁻¹ • γ⁻¹ • u)) =
      α (γ * η, t (η⁻¹ • γ⁻¹ • u)) + α (γ, η) - γ • α (η, t (η⁻¹ • γ⁻¹ • u)) :=
    eq_sub_of_add_eq ((add_comm _ _).trans h₃.symm)
  rw [e₁, e₂, e₃, smul_sub]
  abel

end CocycleHelper

variable (G : Type u) [Group G]
  (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (N : Type w) [AddCommGroup N] [DistribMulAction G N]
  (P : Type x) [AddCommGroup P] [DistribMulAction G P]
  (U : Subgroup G) [U.FiniteIndex]
  (μ : M →+ N →+ P)
  (t : G ⧸ U → G) (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

include ht

/-- **The `(1,0)` projection formula with restriction on the cocycle, on cochains, up to the
explicit coboundary.** For a `1`-cocycle `α` of `G` and a `U`-invariant `n`, the difference between
the corestriction of the cup of `α|_U` with `n` and the cup of `α` with the norm of `n` is `d⁰` of
`TauCeti.ContCohomology.cup10ProjectionHomotopy`. -/
theorem cup10ProjectionHomotopy_spec
    (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)
    {α : G → M} (hα : groupCohomology.IsCocycle₁ α) {n : N} (hn : n ∈ H0 U N) (γ : G) :
    γ • cup10ProjectionHomotopy G M N P U μ t α n - cup10ProjectionHomotopy G M N P U μ t α n =
      cochainsCor1 G P U t ht (fun u : U => μ (α (u : G)) ((u : G) • n)) γ -
        μ (α γ) (γ • ∑ u : G ⧸ U, t u • n) := by
  have hn' : ∀ x ∈ U, x • n = n := fun x hx => (FixedPoints.mem_addSubgroup U N n).1 hn ⟨x, hx⟩
  -- Move the factor `t u •` of the corestriction across the pairing; the transversal word acts
  -- trivially on `n`, and the cocycle law of `α` at `t u * ℓᵗ_u γ = γ * t (γ⁻¹ • u)` expands the
  -- first argument.
  have hcor : cochainsCor1 G P U t ht (fun u : U => μ (α (u : G)) ((u : G) • n)) γ =
      ∑ u : G ⧸ U, μ (γ • α (t (γ⁻¹ • u)) - α (t u) + α γ) (t u • n) := by
    rw [cochainsCor1_apply]
    refine Finset.sum_congr rfl fun u _ => ?_
    have h := smul_apply_lWord_of_isCocycle₁ G M U t hα γ (γ⁻¹ • u)
    rw [smul_inv_smul] at h
    rw [Subtype.coe_mk, hn' _ (lWord_mem U t ht u γ), ← hequiv, h]
  -- The two remaining sums are reindexed by translation by `γ`.
  have hk : γ • cup10ProjectionHomotopy G M N P U μ t α n =
      ∑ u : G ⧸ U, μ (γ • α (t (γ⁻¹ • u))) (t u • n) := by
    rw [cup10ProjectionHomotopy_apply, Finset.smul_sum]
    simp only [← hequiv, smul_smul]
    exact sum_smul_mul_transversal_smul G M N P U μ t ht hn (fun u => γ • α (t u)) γ
  have hcup : μ (α γ) (γ • ∑ u : G ⧸ U, t u • n) = ∑ u : G ⧸ U, μ (α γ) (t u • n) := by
    rw [Finset.smul_sum, map_sum]
    simp only [smul_smul]
    exact sum_smul_mul_transversal_smul G M N P U μ t ht hn (fun _ => α γ) γ
  rw [hcor, hk, hcup, cup10ProjectionHomotopy_apply]
  simp only [map_sub, map_add, AddMonoidHom.sub_apply, AddMonoidHom.add_apply,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  abel

/-- Translating the `(2,0)` homotopy: `γ • kᵗ(η)` is the sum over `u` of `γ • c_{γ⁻¹ • u}(η)`
paired against `t u • n`, where `c_u(η) = α (t u, ℓᵗ_u η) - α (η, t (η⁻¹ • u))` is the coefficient
of the homotopy. -/
private theorem smul_cup20ProjectionHomotopy
    (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y) (α : G × G → M) {n : N}
    (hn : n ∈ H0 U N) (γ η : G) :
    γ • cup20ProjectionHomotopy G M N P U μ t α n η =
      ∑ u : G ⧸ U, μ (γ • (α (t (γ⁻¹ • u), lWord U t (γ⁻¹ • u) η) - α (η, t (η⁻¹ • γ⁻¹ • u))))
        (t u • n) := by
  rw [cup20ProjectionHomotopy_apply, Finset.smul_sum]
  refine (Finset.sum_congr rfl fun u _ => ?_).trans (sum_smul_mul_transversal_smul G M N P U μ t
    ht hn (fun u => γ • (α (t u, lWord U t u η) - α (η, t (η⁻¹ • u)))) γ)
  rw [← hequiv, smul_smul]


/-- **The `(2,0)` projection formula with restriction on the cocycle, on cochains, up to the
explicit coboundary.** For a `2`-cocycle `α` of `G` and a `U`-invariant `n`, the difference between
the corestriction of the cup of `α|_U` with `n` and the cup of `α` with the norm of `n` is `d¹` of
`TauCeti.ContCohomology.cup20ProjectionHomotopy`. -/
theorem cup20ProjectionHomotopy_spec
    (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)
    {α : G × G → M} (hα : groupCohomology.IsCocycle₂ α) {n : N} (hn : n ∈ H0 U N) (γ η : G) :
    γ • cup20ProjectionHomotopy G M N P U μ t α n η -
        cup20ProjectionHomotopy G M N P U μ t α n (γ * η) +
        cup20ProjectionHomotopy G M N P U μ t α n γ =
      cochainsCor2 G P U t ht
          (fun q : U × U => μ (α ((q.1 : G), (q.2 : G))) (((q.1 * q.2 : U) : G) • n)) (γ, η) -
        μ (α (γ, η)) ((γ * η) • ∑ u : G ⧸ U, t u • n) := by
  have hn' : ∀ x ∈ U, x • n = n := fun x hx => (FixedPoints.mem_addSubgroup U N n).1 hn ⟨x, hx⟩
  -- The norm of `n` is `G`-invariant, and the product of two transversal words acts trivially on
  -- `n`; so both terms on the right are sums with second pairing argument `t u • n`.
  have hnorm : (γ * η) • ∑ u : G ⧸ U, t u • n = ∑ u : G ⧸ U, t u • n :=
    (FixedPoints.mem_addSubgroup G N _).1 (sum_transversal_smul_mem_H0 G N U t ht hn) (γ * η)
  have hcor : cochainsCor2 G P U t ht
      (fun q : U × U => μ (α ((q.1 : G), (q.2 : G))) (((q.1 * q.2 : U) : G) • n)) (γ, η) =
        ∑ u : G ⧸ U, μ (t u • α (lWord U t u γ, lWord U t (γ⁻¹ • u) η)) (t u • n) := by
    rw [cochainsCor2_apply]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Subgroup.coe_mul]
    rw [hn' _ (U.mul_mem (lWord_mem U t ht u γ) (lWord_mem U t ht (γ⁻¹ • u) η)), ← hequiv]
  rw [hcor, hnorm, map_sum, smul_cup20ProjectionHomotopy G M N P U μ t ht hequiv α hn,
    cup20ProjectionHomotopy_apply, cup20ProjectionHomotopy_apply, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h := congrArg (fun m : M => μ m (t u • n))
    (transversal_smul_apply_lWord_sub_of_isCocycle₂ G M U t hα u γ η)
  simpa only [map_sub, map_add, AddMonoidHom.sub_apply, AddMonoidHom.add_apply] using h.symm

end ResLeftHomotopy

section ResLeft

/-! ### Restricting the positive-degree factor

The two shapes `(1,0)` and `(2,0)` of the projection formula with the restriction on the cocycle
factor, `cor (res a ⌣ n) = a ⌣ cor⁰ n`. Together with the six shapes above these give the
projection formula with the restriction on the first factor in every bidegree `(p, q)` with
`p + q ≤ 2`. -/

section ContinuousHomotopy

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  (N : Type w) [AddCommGroup N] [TopologicalSpace N] [DistribMulAction G N]
  (P : Type x) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
  (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

include hU hμ

/-- The `(2,0)` projection-formula homotopy of a continuous cocycle is continuous: the transversal
word is continuous by `TauCeti.continuous_lWord`, and `γ ↦ t (γ⁻¹ • u)` is locally constant because
`U` is open. -/
theorem continuous_cup20ProjectionHomotopy (t : G ⧸ U → G) {α : G × G → M} (hα : Continuous α)
    (n : N) : Continuous (cup20ProjectionHomotopy G M N P U μ t α n) := by
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  -- Put the cochain in the pointwise-sum form `continuous_finsetSum` expects.
  rw [funext (cup20ProjectionHomotopy_apply G M N P U μ t α n)]
  refine continuous_finsetSum _ fun u _ => hμ.comp (Continuous.prodMk ?_ continuous_const)
  exact (hα.comp (continuous_const.prodMk (continuous_lWord U t hU u))).sub
    (hα.comp (continuous_id.prodMk
      (continuous_of_discreteTopology.comp (continuous_inv.smul continuous_const))))

end ContinuousHomotopy

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type w) [AddCommGroup N] [TopologicalSpace N] [DistribMulAction G N]
  (P : Type x) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

include hU hμ hequiv

/-- **The `(1,0)` projection formula with restriction on the cocycle**,
`cor¹ (res¹ a ⌣ n) = a ⌣ cor⁰ n`. The two sides differ on cochains by `d⁰` of
`TauCeti.ContCohomology.cup10ProjectionHomotopy`, which is
`TauCeti.ContCohomology.cup10ProjectionHomotopy_spec`. -/
theorem explicitCup_projection10_res_left (a : H1 G M) (n : H0 U N) :
    explicitCor1 G P U hU
        (explicitCup10 U M N P μ hμ (fun g m y => hequiv (g : G) m y) (explicitRes1 G M U a) n) =
      explicitCup10 G M N P μ hμ hequiv a (explicitCor0 G N U n) := by
  induction a using QuotientAddGroup.induction_on with
  | _ α =>
    simp only [explicitRes1_mk, explicitCup10_mk, explicitCor1_mk, H1pi_eq_iff]
    refine mem_B1_iff.2 ⟨cup10ProjectionHomotopy G M N P U μ Quotient.out (α : G → M) (n : N),
      fun γ => ?_⟩
    -- Restriction is evaluation of the cochain at the inclusion, by `cocyclesMap1_apply`.
    simp only [Pi.sub_apply, coe_cocyclesCor1, cocyclesMap1_apply, Subgroup.smul_def,
      coe_explicitCor0]
    exact cup10ProjectionHomotopy_spec G M N P U μ Quotient.out Quotient.out_eq hequiv
      (mem_Z1_iff.1 α.2).2 n.2 γ

/-- **The `(2,0)` projection formula with restriction on the cocycle**,
`cor² (res² a ⌣ n) = a ⌣ cor⁰ n`. The two sides differ on cochains by `d¹` of
`TauCeti.ContCohomology.cup20ProjectionHomotopy`, which is
`TauCeti.ContCohomology.cup20ProjectionHomotopy_spec`. -/
theorem explicitCup_projection20_res_left (a : H2 G M) (n : H0 U N) :
    explicitCor2 G P U hU
        (explicitCup20 U M N P μ hμ (fun g m y => hequiv (g : G) m y) (explicitRes2 G M U a) n) =
      explicitCup20 G M N P μ hμ hequiv a (explicitCor0 G N U n) := by
  induction a using QuotientAddGroup.induction_on with
  | _ α =>
    simp only [explicitRes2_mk, explicitCup20_mk, explicitCor2_mk, H2pi_eq_iff]
    refine mem_B2_iff'.2 ⟨cup20ProjectionHomotopy G M N P U μ Quotient.out (α : G × G → M) (n : N),
      continuous_cup20ProjectionHomotopy G M N P U hU μ hμ Quotient.out
        (mem_Z2_iff.1 α.2).1 (n : N), fun γ η => ?_⟩
    -- Restriction is evaluation of the cochain at the inclusion, by `cocyclesMap2_apply`.
    have hres : ((cocyclesMap2 G M U M (ContinuousMonoidHom.subgroupSubtype U) (AddMonoidHom.id M)
        continuous_id (id_subgroupSubtype_smul G M U) α : Z2 U M) : U × U → M) =
          fun q => (α : G × G → M) ((q.1 : G), (q.2 : G)) :=
      funext fun q => cocyclesMap2_apply G M U M _ _ _ _ α q.1 q.2
    simp only [Pi.sub_apply, coe_cocyclesCor2, hres, Subgroup.smul_def, coe_explicitCor0]
    exact cup20ProjectionHomotopy_spec G M N P U μ Quotient.out Quotient.out_eq hequiv
      (mem_Z2_iff.1 α.2).2 n.2 γ η

end ResLeft

end TauCeti.ContCohomology
