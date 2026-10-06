/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DeltaNaturality

/-!
# The connecting maps and the explicit low-degree cup products

The Leibniz rule `δ (x ⌣ y) = δ x ⌣ y + (-1)^p (x ⌣ δ y)` is not a statement until one says
*which* short exact sequences of coefficients the two connecting maps belong to, and how the
pairing relates them. Cupping with a fixed class in the second variable and cupping with a fixed
class in the first variable are two different constructions, each attached to a short exact
sequence in its own variable, so this file proves two families of identities rather than one sum
rule.

In the **first variable** the input is a short exact sequence `0 → A' → A → A'' → 0` of discrete
`G`-modules, a topological `G`-module `B`, a short exact sequence `0 → C' → C → C'' → 0`, and
three `G`-equivariant biadditive pairings

```text
μ  : A  →+ B →+ C,      μ' : A' →+ B →+ C',      μ'' : A'' →+ B →+ C''
```

with `μ (incl a') b = incl (μ' a' b)` and `μ'' (proj a) b = proj (μ a b)`, that is a map of short
exact sequences after pairing with `B`. For `x ∈ H^p(G, A'')` and `y ∈ H^q(G, B)` the identity is

```text
δ (x ⌣ y) = δ x ⌣ y     in H^{p+q+1}(G, C').
```

In the **second variable** the sequence is `0 → B' → B → B'' → 0`, the fixed module is `A`, the
pairings are `μ : A →+ B →+ C`, `μ' : A →+ B' →+ C'` and `μ'' : A →+ B'' →+ C''`, and for
`x ∈ H^p(G, A)` and `y ∈ H^q(G, B'')` the identity carries the sign of the degree it moves past:

```text
δ (x ⌣ y) = (-1)^p (x ⌣ δ y)   in H^{p+q+1}(G, C').
```

Six instances have all three of `p`, `q` and `p + q + 1` at most `2`, so six theorems exhaust what
the low-degree model can state.

The third family moves a connecting map from one variable to the other. Its input is a **pair**
of short exact sequences `0 → A₁ → A → A₂ → 0` and `0 → B₂ → B → B₁ → 0` of discrete
`G`-modules, compatibly paired into one topological `G`-module `C` by `μ : A →+ B →+ C`,
`μ₁ : A₁ →+ B₁ →+ C` and `μ₂ : A₂ →+ B₂ →+ C` with

```text
μ (incl a₁) b = μ₁ a₁ (proj b),      μ a (incl b₂) = μ₂ (proj a) b₂,
```

so that the sub-object `A₁` is orthogonal to the sub-object `B₂` and pairs with the quotient
`B₁`, while the quotient `A₂` pairs with the sub-object `B₂`. No nondegeneracy is assumed; the
motivating instance is a short exact sequence and its dual sequence under an evaluation pairing.
For `x ∈ H^p(G, A₂)` and
`y ∈ H^q(G, B₁)` the two connecting maps are adjoint up to the Leibniz sign:

```text
δ x ⌣ y = (-1)^(p+1) (x ⌣ δ y)   in H^{p+q+1}(G, C),
```

because `δ x ⌣ y + (-1)^p (x ⌣ δ y)` is the coboundary of the cup of lifts. Three bidegrees
have `p + q + 1 ≤ 2`, so three theorems exhaust this family too. These are the identities that
make the duality maps `H^i(G, M) → H^{2-i}(G, M')^∨` of a Demushkin group commute with the long
exact sequences, the step of Tate's argument that Serre records.

## Main statements

* `TauCeti.ContCohomology.explicitDelta0_explicitCup00_left`,
  `explicitDelta1_explicitCup01_left` and `explicitDelta1_explicitCup10_left`: the three
  first-variable identities, in bidegrees `(0,0)`, `(0,1)` and `(1,0)`.
* `TauCeti.ContCohomology.explicitDelta0_explicitCup00_right`,
  `explicitDelta1_explicitCup01_right` and `explicitDelta1_explicitCup10_right`: the three
  second-variable identities, in bidegrees `(0,0)`, `(0,1)` and `(1,0)`, the last with its sign.
* `TauCeti.ContCohomology.explicitCup10_explicitDelta0_eq_neg_explicitCup01_explicitDelta0`,
  `explicitCup11_explicitDelta0_eq_neg_explicitCup02_explicitDelta1` and
  `explicitCup20_explicitDelta1_eq_explicitCup11_explicitDelta0`: the three adjointness
  identities for a pair of compatibly paired short exact sequences, in bidegrees `(0,0)`, `(0,1)`
  and `(1,0)`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.4.3) and
  (1.4.5): the compatibility of the cup product with the connecting homomorphisms.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I §0, the cup-product properties
  (0.1.1)-(0.1.6), stated with the same sign conventions.
* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.1: Tate's duality argument, which uses the adjointness identities
  to compare the long exact sequences of a finite module and of its dual.
-/

public section

namespace TauCeti.ContCohomology

section FirstVariable

-- These compatibility theorems are deliberately not simp lemmas: their left-hand sides do not
-- determine the source sequence or the pairings on the middle and sub-object coefficients.

variable {G : Type*} [Group G] [TopologicalSpace G]
  {A' : Type*} [AddCommGroup A'] [TopologicalSpace A'] [DiscreteTopology A']
    [DistribMulAction G A'] [ContinuousSMul G A']
  {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A]
  {A'' : Type*} [AddCommGroup A''] [TopologicalSpace A''] [DiscreteTopology A'']
    [DistribMulAction G A''] [ContinuousSMul G A'']
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [DistribMulAction G B] [ContinuousSMul G B]
  {C' : Type*} [AddCommGroup C'] [TopologicalSpace C'] [DiscreteTopology C']
    [DistribMulAction G C'] [ContinuousSMul G C']
  {C : Type*} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C]
  {C'' : Type*} [AddCommGroup C''] [TopologicalSpace C''] [DiscreteTopology C'']
    [DistribMulAction G C''] [ContinuousSMul G C'']
  (SA : DiscreteShortExact G A' A A'') (SC : DiscreteShortExact G C' C C'')
  (μ : A →+ B →+ C) (μ' : A' →+ B →+ C') (μ'' : A'' →+ B →+ C'')
  (hμ : Continuous fun p : A × B => μ p.1 p.2)
  (hμ' : Continuous fun p : A' × B => μ' p.1 p.2)
  (hμ'' : Continuous fun p : A'' × B => μ'' p.1 p.2)
  (hequiv : ∀ (g : G) (a : A) (b : B), μ (g • a) (g • b) = g • μ a b)
  (hequiv' : ∀ (g : G) (a : A') (b : B), μ' (g • a) (g • b) = g • μ' a b)
  (hequiv'' : ∀ (g : G) (a : A'') (b : B), μ'' (g • a) (g • b) = g • μ'' a b)
  (hincl : ∀ (a : A') (b : B), μ (SA.incl a) b = SC.incl (μ' a b))
  (hproj : ∀ (a : A) (b : B), μ'' (SA.proj a) b = SC.proj (μ a b))

include hequiv hincl hproj in
omit [ContinuousSMul G A''] [IsTopologicalAddGroup B] [ContinuousSMul G B]
  [ContinuousSMul G C''] in
/-- **`δ⁰` passes through the `(0,0)` cup in the first variable.** For an invariant `x` of `A''`
and an invariant `y` of `B`, the class `δ⁰ (x ⌣ y) ∈ H¹(G, C')` is `δ⁰ x ⌣ y`, the `(1,0)` cup
against the pairing `μ'` of the sub-objects. -/
theorem explicitDelta0_explicitCup00_left (x : H0 G A'') (y : H0 G B) :
    SC.explicitDelta0 (explicitCup00 G A'' B C'' μ'' hequiv'' x y) =
      explicitCup10 G A' B C' μ' hμ' hequiv' (SA.explicitDelta0 x) y := by
  rw [explicitCup10_apply,
    SA.explicitDelta0_coeffMap SC (pairingRight μ' hequiv' y) (pairingRight μ hequiv y)
      (pairingRight μ'' hequiv'' y)
      (fun a => by simp only [pairingRight_apply]; exact hincl a (y : B))
      (fun a => by simp only [pairingRight_apply]; exact hproj a (y : B)) x]
  exact congrArg SC.explicitDelta0
    (Subtype.ext (by simp only [coe_explicitCup00, coe_explicitCoeff0, pairingRight_apply]))

include hμ hequiv hincl hproj in
omit [ContinuousSMul G A''] in
/-- **`δ¹` passes through the `(0,1)` cup in the first variable.** For an invariant `x` of `A''`
and a class `y ∈ H¹(G, B)`, the class `δ¹ (x ⌣ y) ∈ H²(G, C')` is the `(1,1)` cup `δ⁰ x ⌣ y`. -/
theorem explicitDelta1_explicitCup01_left [ContinuousMul G] (x : H0 G A'') (y : H1 G B) :
    SC.explicitDelta1 (explicitCup01 G A'' B C'' μ'' hμ'' hequiv'' x y) =
      explicitCup11 G A' B C' μ' hμ' hequiv' (SA.explicitDelta0 x) y := by
  induction y using QuotientAddGroup.induction_on with
  | _ β =>
    obtain ⟨a, ha⟩ := SA.proj_surjective (x : A'')
    have hamem : SA.proj a ∈ H0 G A'' := ha ▸ x.2
    obtain ⟨α, -, hαi⟩ :=
      SA.exists_continuous_incl_comp_eq (continuous_d0_apply (G := G) a)
        (DiscreteShortExact.proj_d0_eq_zero hamem)
    have hαi' : ∀ g : G, SA.incl (α g) = g • a - a := fun g => (hαi g).trans (d0_apply a g)
    have hα : α ∈ Z1 G A' := SA.mem_Z1_of_incl_comp_eq_d0 hαi'
    have hβ1 : groupCohomology.IsCocycle₁ (β : G → B) := (mem_Z1_iff.1 β.2).2
    have hecont : Continuous fun g : G => μ a ((β : G → B) g) :=
      hμ.comp (continuous_const.prodMk (mem_Z1_iff.1 β.2).1)
    -- The `(1,1)` cup cochain of `α` against `β` lies over `d¹` of the paired lift `μ a ∘ β`,
    -- by the `1`-cocycle identity for `β`.
    have hcup : ∀ g h : G, SC.incl (μ' (α g) (g • (β : G → B) h)) =
        g • μ a ((β : G → B) h) - μ a ((β : G → B) (g * h)) + μ a ((β : G → B) g) := fun g h => by
      rw [← hincl, hαi' g, map_sub, AddMonoidHom.sub_apply, hequiv g a ((β : G → B) h),
        hβ1 g h, map_add]
      abel
    have hcupZ : (fun q : G × G => μ' (α q.1) (q.1 • (β : G → B) q.2)) ∈ Z2 G C' :=
      cup11_mem_Z2 G A' B C' μ' hμ' hequiv' hα β.2
    have he : ∀ g : G, SC.proj (μ a ((β : G → B) g)) = μ'' (x : A'') ((β : G → B) g) :=
      fun g => by rw [← hproj, ha]
    have hleft := SC.explicitDelta1_apply
      (⟨fun g => μ'' (x : A'') ((β : G → B) g),
        cup01_mem_Z1 G A'' B C'' μ'' hμ'' hequiv'' x β.2⟩ : Z1 G C'')
      hecont he hcupZ hcup
    have hright := SA.explicitDelta0_apply x ha hα hαi'
    simp only [QuotientAddGroup.mk'_apply] at hleft hright
    rw [explicitCup01_mk, hleft, hright, explicitCup11_mk]

include hequiv hincl hproj in
omit [IsTopologicalAddGroup B] [ContinuousSMul G B] in
/-- **`δ¹` passes through the `(1,0)` cup in the first variable.** For a class `x ∈ H¹(G, A'')`
and an invariant `y` of `B`, the class `δ¹ (x ⌣ y) ∈ H²(G, C')` is the `(2,0)` cup
`δ¹ x ⌣ y`. -/
theorem explicitDelta1_explicitCup10_left [ContinuousMul G] (x : H1 G A'') (y : H0 G B) :
    SC.explicitDelta1 (explicitCup10 G A'' B C'' μ'' hμ'' hequiv'' x y) =
      explicitCup20 G A' B C' μ' hμ' hequiv' (SA.explicitDelta1 x) y := by
  rw [explicitCup10_apply, explicitCup20_apply,
    SA.explicitDelta1_coeffMap SC (pairingRight μ' hequiv' y) (pairingRight μ hequiv y)
      (pairingRight μ'' hequiv'' y)
      (fun a => by simp only [pairingRight_apply]; exact hincl a (y : B))
      (fun a => by simp only [pairingRight_apply]; exact hproj a (y : B)) x]

end FirstVariable

section SecondVariable

-- As above, the left-hand sides do not determine the sequence and pairings needed on the right.

variable {G : Type*} [Group G] [TopologicalSpace G]
  {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A] [ContinuousSMul G A]
  {B' : Type*} [AddCommGroup B'] [TopologicalSpace B'] [DiscreteTopology B']
    [DistribMulAction G B'] [ContinuousSMul G B']
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B]
  {B'' : Type*} [AddCommGroup B''] [TopologicalSpace B''] [DiscreteTopology B'']
    [DistribMulAction G B''] [ContinuousSMul G B'']
  {C' : Type*} [AddCommGroup C'] [TopologicalSpace C'] [DiscreteTopology C']
    [DistribMulAction G C'] [ContinuousSMul G C']
  {C : Type*} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C]
  {C'' : Type*} [AddCommGroup C''] [TopologicalSpace C''] [DiscreteTopology C'']
    [DistribMulAction G C''] [ContinuousSMul G C'']
  (SB : DiscreteShortExact G B' B B'') (SC : DiscreteShortExact G C' C C'')
  (μ : A →+ B →+ C) (μ' : A →+ B' →+ C') (μ'' : A →+ B'' →+ C'')
  (hμ : Continuous fun p : A × B => μ p.1 p.2)
  (hμ' : Continuous fun p : A × B' => μ' p.1 p.2)
  (hμ'' : Continuous fun p : A × B'' => μ'' p.1 p.2)
  (hequiv : ∀ (g : G) (a : A) (b : B), μ (g • a) (g • b) = g • μ a b)
  (hequiv' : ∀ (g : G) (a : A) (b : B'), μ' (g • a) (g • b) = g • μ' a b)
  (hequiv'' : ∀ (g : G) (a : A) (b : B''), μ'' (g • a) (g • b) = g • μ'' a b)
  (hincl : ∀ (a : A) (b : B'), μ a (SB.incl b) = SC.incl (μ' a b))
  (hproj : ∀ (a : A) (b : B), μ'' a (SB.proj b) = SC.proj (μ a b))

include hequiv hincl hproj in
omit [IsTopologicalAddGroup A] [ContinuousSMul G A] [ContinuousSMul G B'']
  [ContinuousSMul G C''] in
/-- **`δ⁰` passes through the `(0,0)` cup in the second variable.** For an invariant `x` of `A`
and an invariant `y` of `B''`, the class `δ⁰ (x ⌣ y) ∈ H¹(G, C')` is the `(0,1)` cup
`x ⌣ δ⁰ y`; the sign `(-1)^p` is `1` because `x` has degree `0`. -/
theorem explicitDelta0_explicitCup00_right (x : H0 G A) (y : H0 G B'') :
    SC.explicitDelta0 (explicitCup00 G A B'' C'' μ'' hequiv'' x y) =
      explicitCup01 G A B' C' μ' hμ' hequiv' x (SB.explicitDelta0 y) := by
  rw [explicitCup01_apply,
    SB.explicitDelta0_coeffMap SC (pairingLeft μ' hequiv' x) (pairingLeft μ hequiv x)
      (pairingLeft μ'' hequiv'' x)
      (fun b => by simp only [pairingLeft_apply]; exact hincl (x : A) b)
      (fun b => by simp only [pairingLeft_apply]; exact hproj (x : A) b) y]
  exact congrArg SC.explicitDelta0
    (Subtype.ext (by simp only [coe_explicitCup00, coe_explicitCoeff0, pairingLeft_apply]))

include hequiv hincl hproj in
omit [IsTopologicalAddGroup A] [ContinuousSMul G A] in
/-- **`δ¹` passes through the `(0,1)` cup in the second variable.** For an invariant `x` of `A`
and a class `y ∈ H¹(G, B'')`, the class `δ¹ (x ⌣ y) ∈ H²(G, C')` is the `(0,2)` cup
`x ⌣ δ¹ y`. -/
theorem explicitDelta1_explicitCup01_right [ContinuousMul G] (x : H0 G A) (y : H1 G B'') :
    SC.explicitDelta1 (explicitCup01 G A B'' C'' μ'' hμ'' hequiv'' x y) =
      explicitCup02 G A B' C' μ' hμ' hequiv' x (SB.explicitDelta1 y) := by
  rw [explicitCup01_apply, explicitCup02_apply,
    SB.explicitDelta1_coeffMap SC (pairingLeft μ' hequiv' x) (pairingLeft μ hequiv x)
      (pairingLeft μ'' hequiv'' x)
      (fun b => by simp only [pairingLeft_apply]; exact hincl (x : A) b)
      (fun b => by simp only [pairingLeft_apply]; exact hproj (x : A) b) y]

include hμ hequiv hincl hproj in
omit [ContinuousSMul G B''] in
/-- **`δ¹` passes through the `(1,0)` cup in the second variable, with a sign.** For a class
`x ∈ H¹(G, A)` and an invariant `y` of `B''`, the class `δ¹ (x ⌣ y) ∈ H²(G, C')` is
`-(x ⌣ δ⁰ y)`, the sign `(-1)^p` at `p = 1`. -/
theorem explicitDelta1_explicitCup10_right [ContinuousMul G] (x : H1 G A) (y : H0 G B'') :
    SC.explicitDelta1 (explicitCup10 G A B'' C'' μ'' hμ'' hequiv'' x y) =
      -explicitCup11 G A B' C' μ' hμ' hequiv' x (SB.explicitDelta0 y) := by
  -- A double flip is definitionally the original pairing; only its proof witnesses differ.
  change SC.explicitDelta1 (explicitCup10 G A B'' C'' μ''.flip.flip _ _ x y) = _
  rw [← explicitCup01_eq_cup10_flip G B'' A C'' μ''.flip
    (continuous_flip μ'' hμ'') (equivariant_flip μ'' hequiv''),
    explicitDelta1_explicitCup01_left SB SC μ.flip μ'.flip μ''.flip
      (continuous_flip μ hμ) (continuous_flip μ' hμ') (continuous_flip μ'' hμ'')
      (equivariant_flip μ hequiv) (equivariant_flip μ' hequiv')
      (equivariant_flip μ'' hequiv'') (fun b a => hincl a b) (fun b a => hproj a b),
    ← neg_inj, neg_neg, explicitCup11_eq_neg_flip]
  simp only [neg_neg]
  congr 1

end SecondVariable

section CompatiblyPaired

/-! ### A pair of compatibly paired short exact sequences

The connecting maps of `0 → A₁ → A → A₂ → 0` and of `0 → B₂ → B → B₁ → 0` are adjoint under
pairings that make `A₁` orthogonal to `B₂`. Every coefficient module of the two sequences is
discrete here, so the joint continuity of each pairing is automatic and is not taken as a
hypothesis, and the equivariance of `μ₁` and `μ₂` follows from that of `μ` through the two
compatibilities, so only `μ` is assumed equivariant; the common target `C` is any topological
`G`-module. -/

-- As above, the left-hand sides do not determine the second sequence and the other pairings.

variable {G : Type*} [Group G]
  {A₁ : Type*} [AddCommGroup A₁] [TopologicalSpace A₁] [DiscreteTopology A₁]
    [DistribMulAction G A₁]
  {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {A₂ : Type*} [AddCommGroup A₂] [TopologicalSpace A₂] [DiscreteTopology A₂]
    [DistribMulAction G A₂]
  {B₂ : Type*} [AddCommGroup B₂] [TopologicalSpace B₂] [DiscreteTopology B₂]
    [DistribMulAction G B₂]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {B₁ : Type*} [AddCommGroup B₁] [TopologicalSpace B₁] [DiscreteTopology B₁]
    [DistribMulAction G B₁]
  {C : Type*} [AddCommGroup C]
  (SA : DiscreteShortExact G A₁ A A₂) (SB : DiscreteShortExact G B₂ B B₁)
  (μ : A →+ B →+ C) (μ₁ : A₁ →+ B₁ →+ C) (μ₂ : A₂ →+ B₂ →+ C)
  (hincl : ∀ (a : A₁) (b : B), μ (SA.incl a) b = μ₁ a (SB.proj b))
  (hproj : ∀ (a : A) (b : B₂), μ a (SB.incl b) = μ₂ (SA.proj a) b)

include hincl in
/-- The pairing of the sub-object `A₁` with the quotient `B₁`, read on a preimage in `B`. -/
private theorem pairing_incl_smul {a : A₁} {b : B} {y : B₁} (hb : SB.proj b = y) (g : G) :
    μ₁ a (g • y) = μ (SA.incl a) (g • b) := by
  rw [hincl, SB.proj_equivariant, hb]

include hproj in
/-- The pairing of the quotient `A₂` with the sub-object `B₂`, read on a preimage in `A`. -/
private theorem pairing_proj_incl {a : A} {x : A₂} (ha : SA.proj a = x) (b : B₂) :
    μ₂ x b = μ a (SB.incl b) := by
  rw [hproj, ha]

variable [DistribMulAction G C]
  (hequiv : ∀ (g : G) (a : A) (b : B), μ (g • a) (g • b) = g • μ a b)

include hequiv hincl in
/-- **The pairing of the sub-object `A₁` with the quotient `B₁` is equivariant.** Lift `b` to
`B` and read `μ₁` through `μ` on `SA.incl a`. -/
theorem equivariant_of_incl (g : G) (a : A₁) (b : B₁) : μ₁ (g • a) (g • b) = g • μ₁ a b := by
  obtain ⟨b, rfl⟩ := SB.proj_surjective b
  rw [← SB.proj_equivariant, ← hincl, ← hincl, SA.incl_equivariant, hequiv]

include hequiv hproj in
/-- **The pairing of the quotient `A₂` with the sub-object `B₂` is equivariant.** Lift `a` to
`A` and read `μ₂` through `μ` on `SB.incl b`. -/
theorem equivariant_of_proj (g : G) (a : A₂) (b : B₂) : μ₂ (g • a) (g • b) = g • μ₂ a b := by
  obtain ⟨a, rfl⟩ := SA.proj_surjective a
  rw [← SA.proj_equivariant, ← hproj, ← hproj, SB.incl_equivariant, hequiv]

variable [TopologicalSpace G] [ContinuousSMul G A₁] [ContinuousSMul G A] [ContinuousSMul G A₂]
  [ContinuousSMul G B₂] [ContinuousSMul G B] [ContinuousSMul G B₁]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul G C]

include hequiv hincl hproj

omit [ContinuousSMul G A₂] [ContinuousSMul G B₁] in
/-- **The two `δ⁰` are anti-adjoint under the `(1,0)` and `(0,1)` cups.** For invariants `x` of `A₂`
and `y` of `B₁`, the class `δ⁰ x ⌣ y ∈ H¹(G, C)` is `-(x ⌣ δ⁰ y)`. -/
theorem explicitCup10_explicitDelta0_eq_neg_explicitCup01_explicitDelta0
    (x : H0 G A₂) (y : H0 G B₁) :
    explicitCup10 G A₁ B₁ C μ₁ continuous_of_discreteTopology
        (equivariant_of_incl SA SB μ μ₁ hincl hequiv) (SA.explicitDelta0 x) y =
      -explicitCup01 G A₂ B₂ C μ₂ continuous_of_discreteTopology
        (equivariant_of_proj SA SB μ μ₂ hproj hequiv) x (SB.explicitDelta0 y) := by
  obtain ⟨a, ha⟩ := SA.proj_surjective (x : A₂)
  obtain ⟨α, -, hαi⟩ :=
    SA.exists_continuous_incl_comp_eq (continuous_d0_apply (G := G) a)
      (DiscreteShortExact.proj_d0_eq_zero (ha ▸ x.2))
  have hαi' : ∀ g : G, SA.incl (α g) = g • a - a := fun g => (hαi g).trans (d0_apply a g)
  have hα : α ∈ Z1 G A₁ := SA.mem_Z1_of_incl_comp_eq_d0 hαi'
  obtain ⟨b, hb⟩ := SB.proj_surjective (y : B₁)
  obtain ⟨β, -, hβi⟩ :=
    SB.exists_continuous_incl_comp_eq (continuous_d0_apply (G := G) b)
      (DiscreteShortExact.proj_d0_eq_zero (hb ▸ y.2))
  have hβi' : ∀ g : G, SB.incl (β g) = g • b - b := fun g => (hβi g).trans (d0_apply b g)
  have hβ : β ∈ Z1 G B₂ := SB.mem_Z1_of_incl_comp_eq_d0 hβi'
  have hx := SA.explicitDelta0_apply x ha hα hαi'
  have hy := SB.explicitDelta0_apply y hb hβ hβi'
  simp only [QuotientAddGroup.mk'_apply] at hx hy
  rw [hx, hy, explicitCup10_mk, explicitCup01_mk, ← QuotientAddGroup.mk_neg, H1pi_eq_iff,
    mem_B1_iff]
  -- The difference of the two cup cochains is `d⁰` of the paired lifts `μ a b`.
  refine ⟨μ a b, fun g => ?_⟩
  simp only [AddSubgroup.coe_neg, Pi.sub_apply, Pi.neg_apply, sub_neg_eq_add,
    pairing_incl_smul SA SB μ μ₁ hincl hb, pairing_proj_incl SA SB μ μ₂ hproj ha, hαi', hβi',
    map_sub, AddMonoidHom.sub_apply, ← hequiv]
  abel

omit [ContinuousSMul G A₂] in
/-- **`δ⁰` and `δ¹` are anti-adjoint under the `(1,1)` and `(0,2)` cups.** For an invariant `x`
of `A₂` and a class `y ∈ H¹(G, B₁)`, the class `δ⁰ x ⌣ y ∈ H²(G, C)` is `-(x ⌣ δ¹ y)`. -/
theorem explicitCup11_explicitDelta0_eq_neg_explicitCup02_explicitDelta1 [ContinuousMul G]
    (x : H0 G A₂) (y : H1 G B₁) :
    explicitCup11 G A₁ B₁ C μ₁ continuous_of_discreteTopology
        (equivariant_of_incl SA SB μ μ₁ hincl hequiv) (SA.explicitDelta0 x) y =
      -explicitCup02 G A₂ B₂ C μ₂ continuous_of_discreteTopology
        (equivariant_of_proj SA SB μ μ₂ hproj hequiv) x (SB.explicitDelta1 y) := by
  induction y using QuotientAddGroup.induction_on with
  | _ β =>
    obtain ⟨a, ha⟩ := SA.proj_surjective (x : A₂)
    obtain ⟨α, -, hαi⟩ :=
      SA.exists_continuous_incl_comp_eq (continuous_d0_apply (G := G) a)
        (DiscreteShortExact.proj_d0_eq_zero (ha ▸ x.2))
    have hαi' : ∀ g : G, SA.incl (α g) = g • a - a := fun g => (hαi g).trans (d0_apply a g)
    have hα : α ∈ Z1 G A₁ := SA.mem_Z1_of_incl_comp_eq_d0 hαi'
    obtain ⟨hβc, hβ1⟩ := mem_Z1_iff.1 β.2
    obtain ⟨e, hec, he⟩ := exists_continuous_lift SB.proj_surjective hβc
    obtain ⟨b, -, hbi⟩ :=
      SB.exists_continuous_incl_comp_eq (continuous_d1_apply hec) (SB.proj_d1_eq_zero he hβ1)
    have hbi' : ∀ g h : G, SB.incl (b (g, h)) = g • e h - e (g * h) + e g :=
      fun g h => (hbi (g, h)).trans (d1_apply e g h)
    have hb : b ∈ Z2 G B₂ := SB.mem_Z2_of_incl_comp_eq_d1 hec hbi'
    have hx := SA.explicitDelta0_apply x ha hα hαi'
    have hy := SB.explicitDelta1_apply β hec he hb hbi'
    simp only [QuotientAddGroup.mk'_apply] at hx hy
    rw [hx, hy, explicitCup11_mk, explicitCup02_mk, ← QuotientAddGroup.mk_neg, H2pi_eq_iff,
      mem_B2_iff']
    -- The difference of the two cup cochains is `d¹` of the paired lifts `g ↦ μ a (e g)`.
    refine ⟨fun g => μ a (e g), (continuous_of_discreteTopology (f := μ a)).comp hec,
      fun g h => ?_⟩
    simp only [AddSubgroup.coe_neg, Pi.sub_apply, Pi.neg_apply, sub_neg_eq_add,
      pairing_incl_smul SA SB μ μ₁ hincl (he h), pairing_proj_incl SA SB μ μ₂ hproj ha, hαi',
      hbi', map_sub, map_add, AddMonoidHom.sub_apply, ← hequiv]
    abel

omit [ContinuousSMul G B₁] in
/-- **`δ¹` and `δ⁰` are adjoint under the `(2,0)` and `(1,1)` cups.** For a class
`x ∈ H¹(G, A₂)` and an invariant `y` of `B₁`, the class `δ¹ x ⌣ y ∈ H²(G, C)` is `x ⌣ δ⁰ y`;
the sign `(-1)^(p+1)` is `1` because `x` has degree `1`. -/
theorem explicitCup20_explicitDelta1_eq_explicitCup11_explicitDelta0 [ContinuousMul G]
    (x : H1 G A₂) (y : H0 G B₁) :
    explicitCup20 G A₁ B₁ C μ₁ continuous_of_discreteTopology
        (equivariant_of_incl SA SB μ μ₁ hincl hequiv) (SA.explicitDelta1 x) y =
      explicitCup11 G A₂ B₂ C μ₂ continuous_of_discreteTopology
        (equivariant_of_proj SA SB μ μ₂ hproj hequiv) x (SB.explicitDelta0 y) := by
  induction x using QuotientAddGroup.induction_on with
  | _ α =>
    obtain ⟨hαc, hα1⟩ := mem_Z1_iff.1 α.2
    obtain ⟨e, hec, he⟩ := exists_continuous_lift SA.proj_surjective hαc
    obtain ⟨a, -, hai⟩ :=
      SA.exists_continuous_incl_comp_eq (continuous_d1_apply hec) (SA.proj_d1_eq_zero he hα1)
    have hai' : ∀ g h : G, SA.incl (a (g, h)) = g • e h - e (g * h) + e g :=
      fun g h => (hai (g, h)).trans (d1_apply e g h)
    have ha : a ∈ Z2 G A₁ := SA.mem_Z2_of_incl_comp_eq_d1 hec hai'
    obtain ⟨b, hb⟩ := SB.proj_surjective (y : B₁)
    obtain ⟨β, -, hβi⟩ :=
      SB.exists_continuous_incl_comp_eq (continuous_d0_apply (G := G) b)
        (DiscreteShortExact.proj_d0_eq_zero (hb ▸ y.2))
    have hβi' : ∀ g : G, SB.incl (β g) = g • b - b := fun g => (hβi g).trans (d0_apply b g)
    have hβ : β ∈ Z1 G B₂ := SB.mem_Z1_of_incl_comp_eq_d0 hβi'
    have hx := SA.explicitDelta1_apply α hec he ha hai'
    have hy := SB.explicitDelta0_apply y hb hβ hβi'
    simp only [QuotientAddGroup.mk'_apply] at hx hy
    rw [hx, hy, explicitCup20_mk, explicitCup11_mk, H2pi_eq_iff, mem_B2_iff']
    -- The difference of the two cup cochains is `d¹` of the paired lifts `g ↦ μ (e g) (g • b)`.
    have hc : Continuous fun g : G => μ (e g) (g • b) :=
      (continuous_of_discreteTopology (f := fun p : A × B => μ p.1 p.2)).comp
        (hec.prodMk (continuous_id.smul continuous_const))
    refine ⟨fun g => μ (e g) (g • b), hc, fun g h => ?_⟩
    -- Read both cup cochains on the lifts `e` and `b` before expanding the actions.
    simp only [Pi.sub_apply, pairing_incl_smul SA SB μ μ₁ hincl hb,
      pairing_proj_incl SA SB μ μ₂ hproj (he g), hai', SB.incl_equivariant, hβi']
    simp only [smul_sub, mul_smul, map_sub, map_add, AddMonoidHom.sub_apply,
      AddMonoidHom.add_apply, ← hequiv]
    abel

end CompatiblyPaired

end TauCeti.ContCohomology
