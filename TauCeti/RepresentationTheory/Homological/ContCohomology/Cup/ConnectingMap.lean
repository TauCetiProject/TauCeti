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

## Main statements

* `TauCeti.ContCohomology.explicitDelta0_explicitCup00_left`,
  `explicitDelta1_explicitCup01_left` and `explicitDelta1_explicitCup10_left`: the three
  first-variable identities, in bidegrees `(0,0)`, `(0,1)` and `(1,0)`.
* `TauCeti.ContCohomology.explicitDelta0_explicitCup00_right`,
  `explicitDelta1_explicitCup01_right` and `explicitDelta1_explicitCup10_right`: the three
  second-variable identities, in bidegrees `(0,0)`, `(0,1)` and `(1,0)`, the last with its sign.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.4.3) and
  (1.4.5): the compatibility of the cup product with the connecting homomorphisms.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I §0, the cup-product properties
  (0.1.1)-(0.1.6), stated with the same sign conventions.
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

end TauCeti.ContCohomology
