/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality

/-!
# Cup products in low degrees on the explicit model

For a monoid `G`, a cup product on continuous cochains is relative to a `G`-equivariant
biadditive pairing `μ : M →+ N →+ P` with `μ (g • m) (g • n) = g • μ m n` that is jointly
continuous. This file builds the six low-degree shapes

```text
(p, q) ∈ {(0,0), (0,1), (1,0), (0,2), (1,1), (2,0)},   p + q ≤ 2,
```

of the general inhomogeneous formula
`(a ⌣ b)(g₁, …, g_{p+q}) = μ (a (g₁, …, g_p)) ((g₁ ⋯ g_p) • b (g_{p+1}, …, g_{p+q}))`, namely

```text
(0,0):  m ⌣ n = μ m n,                        (0,1):  (m ⌣ b) g = μ m (b g),
(1,0):  (a ⌣ n) g = μ (a g) (g • n),          (0,2):  (m ⌣ b) (g, h) = μ m (b (g, h)),
(1,1):  (a ⌣ b) (g, h) = μ (a g) (g • b h),   (2,0):  (a ⌣ n) (g, h) = μ (a (g, h)) ((g * h) • n).
```

Graded commutativity lives in
`TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product.Comm`, and associativity
lives in `TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product.Assoc`.

## Main definitions

* `TauCeti.ContCohomology.pairingLeft` and `TauCeti.ContCohomology.pairingRight`: partial
  application of the pairing at an *invariant* element, as an equivariant additive homomorphism.
  This is what makes the five shapes with a degree-`0` factor instances of the coefficient maps
  `TauCeti.ContCohomology.explicitCoeff0`, `explicitCoeff1` and `explicitCoeff2`.
* `TauCeti.ContCohomology.explicitCup00`, `explicitCup01`, `explicitCup10`, `explicitCup02`,
  `explicitCup11`, `explicitCup20`: the six shapes, each biadditive by construction, with the
  `_mk` theorems fixing the cochain formula on classes of cocycles.

## Main statements

* `TauCeti.ContCohomology.cup01_mem_Z1`, `cup10_mem_Z1`, `cup02_mem_Z2`, `cup11_mem_Z2` and
  `cup20_mem_Z2`: a cocycle cupped with a cocycle is a cocycle, the cochain-level heart of each
  shape.
* `TauCeti.ContCohomology.cup11_mem_B2_left` and `cup11_mem_B2_right`: the `(1,1)` cup descends
  through coboundaries in each variable. These are the only descent statements proved by hand:
  the other five shapes descend because they *are* coefficient maps, whose descent is
  `TauCeti.ContCohomology.cochainsMap1_mem_B1` and `cochainsMap2_mem_B2`.

## Implementation notes

The translation factor `g •` in the `(1,0)`, `(1,1)` and `(2,0)` formulas is the one the general
inhomogeneous formula carries, and it is kept in the statements even though a degree-`0` class is
invariant and the factor is therefore invisible in the `(1,0)` and `(2,0)` shapes. Keeping it is
what makes those two shapes the specializations of the general formula needed in the
associativity identities.

The `(1,1)` shape is the only one that is not a coefficient map, and the only one whose descent
through coboundaries needs a homotopy. Its two primitives are

```text
a ∈ B¹, a = d⁰ m :  (a ⌣ b) = d¹ (x ↦ μ m (b x)),
b ∈ B¹, b = d⁰ n :  (a ⌣ b) = d¹ (x ↦ -μ (a x) (x • n)),
```

proved in `TauCeti.ContCohomology.cup11_mem_B2_left` and `cup11_mem_B2_right`.

The `(1,1)` cocycle and coboundary proofs use `change` only to beta-reduce the cup cochain
inside `groupCohomology.IsCocycle₂` and `mem_B2_iff'`.

Continuity of the cup cochains is where continuity of `μ` is used: the degree-zero slice cocycle
lemmas `cup01_mem_Z1`, `cup10_mem_Z1`, `cup02_mem_Z2`, `cup20_mem_Z2` and `cup11_mem_B2_left`
require only continuity in the varying variable, while `cup11_mem_Z2`, `cup11_mem_B2_right`, and
the bundled cup products carry joint continuity of `μ`. Continuity is automatic when `M` and `N`
are discrete, which is the case in every arithmetic application, but it is carried as a hypothesis
rather than derived so that the shapes are available at the general topological coefficients the
explicit complex is built for.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., I §4: the cup
  product on inhomogeneous cochains and its low-degree formulas.
* K. Brown, *Cohomology of Groups*, V §3: the cochain-level cup product.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uN uP

section PairingLeft

variable {G : Type uG} [Monoid G]
  {M : Type uM} [AddCommGroup M] [DistribMulAction G M]

/-- The pairing with an invariant first argument absorbs the action from the second. -/
theorem pairingLeft_smul {N : Type uN} [AddZeroClass N] [SMul G N]
    {P : Type uP} [AddCommMonoid P] [SMul G P] (μ : M →+ N →+ P)
    (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
    (m : H0 G M) (g : G) (x : N) :
    μ (m : M) (g • x) = g • μ (m : M) x := by
  rw [← hequiv, m.property g]

variable {N : Type uN} [AddMonoid N] [DistribMulAction G N]
  {P : Type uP} [AddCommMonoid P] [DistribMulAction G P]
  (μ : M →+ N →+ P)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- Partial application of an equivariant pairing at an **invariant** element of the first
factor. Invariance is what makes `μ m : N →+ P` equivariant, and hence what makes the `(0, q)`
cup shapes coefficient maps. -/
def pairingLeft (m : H0 G M) : N →+[G] P where
  toAddMonoidHom := μ (m : M)
  map_smul' := pairingLeft_smul μ hequiv m

/-- The underlying additive homomorphism of `TauCeti.ContCohomology.pairingLeft`. -/
@[simp]
theorem coe_pairingLeft (m : H0 G M) :
    ((pairingLeft μ hequiv m : N →+[G] P) : N →+ P) = μ (m : M) :=
  (rfl)

/-- The defining formula for `TauCeti.ContCohomology.pairingLeft`. -/
@[simp]
theorem pairingLeft_apply (m : H0 G M) (x : N) : pairingLeft μ hequiv m x = μ (m : M) x :=
  (rfl)

/-- A jointly continuous pairing is continuous in the second variable. -/
theorem continuous_pairingLeft [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    (hμ : Continuous fun p : M × N => μ p.1 p.2) (m : H0 G M) :
    Continuous (pairingLeft μ hequiv m) :=
  hμ.uncurry_left (f := (μ · ·)) (m : M)

end PairingLeft

section PairingRight

variable {G : Type uG} [Monoid G]
  {N : Type uN} [AddCommGroup N] [DistribMulAction G N]

/-- The pairing with an invariant second argument absorbs the action from the first. -/
theorem pairingRight_smul {M : Type uM} [AddZeroClass M] [SMul G M]
    {P : Type uP} [AddCommMonoid P] [SMul G P] (μ : M →+ N →+ P)
    (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
    (n : H0 G N) (g : G) (m : M) :
    μ (g • m) (n : N) = g • μ m (n : N) := by
  rw [← hequiv, n.property g]

variable {M : Type uM} [AddMonoid M] [DistribMulAction G M]
  {P : Type uP} [AddCommMonoid P] [DistribMulAction G P]
  (μ : M →+ N →+ P)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- Partial application of an equivariant pairing at an **invariant** element of the second
factor. -/
def pairingRight (n : H0 G N) : M →+[G] P where
  toAddMonoidHom := μ.flip (n : N)
  map_smul' := pairingRight_smul μ hequiv n

/-- The underlying additive homomorphism of `TauCeti.ContCohomology.pairingRight` is the flip of
the pairing. -/
@[simp]
theorem coe_pairingRight (n : H0 G N) :
    ((pairingRight μ hequiv n : M →+[G] P) : M →+ P) = μ.flip (n : N) :=
  (rfl)

/-- The defining formula for `TauCeti.ContCohomology.pairingRight`. -/
@[simp]
theorem pairingRight_apply (n : H0 G N) (m : M) : pairingRight μ hequiv n m = μ m (n : N) :=
  (rfl)

/-- A jointly continuous pairing is continuous in the first variable. -/
theorem continuous_pairingRight [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    (hμ : Continuous fun p : M × N => μ p.1 p.2) (n : H0 G N) :
    Continuous (pairingRight μ hequiv n) :=
  hμ.uncurry_right (f := (μ · ·)) (n : N)

end PairingRight

section CupZeroZero

variable (G : Type uG) [Monoid G]
  (M : Type uM) [AddCommGroup M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [DistribMulAction G N]
  (P : Type uP) [AddCommGroup P] [DistribMulAction G P]
  (μ : M →+ N →+ P)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- **The `(0,0)` cup product**, `m ⌣ n = μ m n`: the pairing of two invariant elements is
invariant. No topology is involved, `H⁰` being a subgroup and not a quotient. -/
def explicitCup00 : H0 G M →+ H0 G N →+ H0 G P :=
  AddMonoidHom.mk' (fun m => explicitCoeff0 G N (pairingLeft μ hequiv m))
    fun m m' => AddMonoidHom.ext fun n => Subtype.ext <| by
      simp [coe_explicitCoeff0]

/-- The `(0,0)` cup is the pairing itself. -/
@[simp]
theorem coe_explicitCup00 (m : H0 G M) (n : H0 G N) :
    (explicitCup00 G M N P μ hequiv m n : P) = μ (m : M) (n : N) :=
  coe_explicitCoeff0 G N (pairingLeft μ hequiv m) n

end CupZeroZero

section CupZeroOne

/-- **The `(0,1)` cup of an invariant element with a continuous `1`-cocycle is a continuous
`1`-cocycle.** -/
theorem cup01_mem_Z1 (G : Type uG) [Monoid G] [TopologicalSpace G]
    (M : Type uM) [AddCommGroup M] [DistribMulAction G M]
    (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
      [DistribSMul G N]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
      [DistribSMul G P]
    (μ : M →+ N →+ P)
    (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
    (m : H0 G M) (hm : Continuous (μ (m : M))) {b : G → N} (hb : b ∈ Z1 G N) :
    (fun g => μ (m : M) (b g)) ∈ Z1 G P := by
  have h : (fun g => μ (m : M) (b g)) =
      cochainsMap1 (ContinuousMonoidHom.id G : G →* G) (μ (m : M)) b := by
    ext g
    simp
  rw [h]
  exact cochainsMap1_mem_Z1 G N G P (ContinuousMonoidHom.id G) (μ (m : M))
    hm (pairingLeft_smul μ hequiv m) hb

variable (G : Type uG) [Monoid G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- **The `(0,1)` cup product**, `(m ⌣ b) g = μ m (b g)`. For invariant `m` this is the
coefficient map induced by `μ m`. -/
noncomputable def explicitCup01 : H0 G M →+ H1 G N →+ H1 G P :=
  AddMonoidHom.mk'
    (fun m => explicitCoeff1 G N (pairingLeft μ hequiv m) (continuous_pairingLeft μ hequiv hμ m))
    fun m m' => AddMonoidHom.ext fun x => by
      induction x using QuotientAddGroup.induction_on with
      | _ c =>
        rw [AddMonoidHom.add_apply, explicitCoeff1_mk, explicitCoeff1_mk, explicitCoeff1_mk,
          ← QuotientAddGroup.mk_add]
        exact congrArg (fun z : Z1 G P => (z : H1 G P))
          (Subtype.ext (funext fun g => by simp [coe_cocyclesMap1]))

/-- The `(0,1)` cup is the coefficient map induced by the pairing at an invariant element. -/
theorem explicitCup01_apply (m : H0 G M) :
    explicitCup01 G M N P μ hμ hequiv m =
      explicitCoeff1 G N (pairingLeft μ hequiv m) (continuous_pairingLeft μ hequiv hμ m) :=
  (rfl)

/-- The cochain formula for the `(0,1)` cup on the class of a continuous `1`-cocycle. -/
@[simp]
theorem explicitCup01_mk (m : H0 G M) (b : Z1 G N) :
    explicitCup01 G M N P μ hμ hequiv m (b : H1 G N) =
      ((⟨fun g => μ (m : M) ((b : G → N) g),
        cup01_mem_Z1 G M N P μ hequiv m (hμ.uncurry_left (f := (μ · ·)) (m : M))
          b.property⟩ : Z1 G P) : H1 G P) := by
  rw [explicitCup01_apply, explicitCoeff1_mk]
  exact congrArg (fun z : Z1 G P => (z : H1 G P))
    (Subtype.ext (funext fun g => by simp [coe_cocyclesMap1]))

end CupZeroOne

section CupOneZero

/-- **The `(1,0)` cup of a continuous `1`-cocycle with an invariant element is a continuous
`1`-cocycle.** The translation factor `g •` is the one the general inhomogeneous formula carries;
it disappears only because `n` is invariant. -/
theorem cup10_mem_Z1 (G : Type uG) [Monoid G] [TopologicalSpace G]
    (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [DistribSMul G M]
    (N : Type uN) [AddCommGroup N] [DistribMulAction G N]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
      [DistribSMul G P]
    (μ : M →+ N →+ P)
    (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
    {a : G → M} (ha : a ∈ Z1 G M) (n : H0 G N) (hn : Continuous (μ.flip (n : N))) :
    (fun g => μ (a g) (g • (n : N))) ∈ Z1 G P := by
  have h : (fun g => μ (a g) (g • (n : N))) =
      cochainsMap1 (ContinuousMonoidHom.id G : G →* G) (μ.flip (n : N)) a := by
    ext g
    simp [n.property g]
  rw [h]
  exact cochainsMap1_mem_Z1 G M G P (ContinuousMonoidHom.id G) (μ.flip (n : N))
    hn (pairingRight_smul μ hequiv n) ha

variable (G : Type uG) [Monoid G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DistribMulAction G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- **The `(1,0)` cup product**, `(a ⌣ n) g = μ (a g) (g • n)`. For invariant `n` this is the
coefficient map induced by `m ↦ μ m n`. -/
noncomputable def explicitCup10 : H1 G M →+ H0 G N →+ H1 G P :=
  AddMonoidHom.flip <| AddMonoidHom.mk'
    (fun n => explicitCoeff1 G M (pairingRight μ hequiv n) (continuous_pairingRight μ hequiv hμ n))
    fun n n' => AddMonoidHom.ext fun x => by
      induction x using QuotientAddGroup.induction_on with
      | _ c =>
        rw [AddMonoidHom.add_apply, explicitCoeff1_mk, explicitCoeff1_mk, explicitCoeff1_mk,
          ← QuotientAddGroup.mk_add]
        exact congrArg (fun z : Z1 G P => (z : H1 G P))
          (Subtype.ext (funext fun g => by simp [coe_cocyclesMap1]))

/-- The `(1,0)` cup is the coefficient map induced by the pairing at an invariant element. -/
theorem explicitCup10_apply (a : H1 G M) (n : H0 G N) :
    explicitCup10 G M N P μ hμ hequiv a n =
      explicitCoeff1 G M (pairingRight μ hequiv n) (continuous_pairingRight μ hequiv hμ n) a :=
  (rfl)

/-- The cochain formula for the `(1,0)` cup on the class of a continuous `1`-cocycle. -/
@[simp]
theorem explicitCup10_mk (a : Z1 G M) (n : H0 G N) :
    explicitCup10 G M N P μ hμ hequiv (a : H1 G M) n =
      ((⟨fun g => μ ((a : G → M) g) (g • (n : N)),
        cup10_mem_Z1 G M N P μ hequiv a.property n
          (hμ.uncurry_right (f := (μ · ·)) (n : N))⟩ : Z1 G P) : H1 G P) := by
  rw [explicitCup10_apply, explicitCoeff1_mk]
  exact congrArg (fun z : Z1 G P => (z : H1 G P))
    (Subtype.ext (funext fun g => by simp [coe_cocyclesMap1, n.property g]))

end CupOneZero

section CupZeroTwo

/-- **The `(0,2)` cup of an invariant element with a continuous `2`-cocycle is a continuous
`2`-cocycle.** -/
theorem cup02_mem_Z2 (G : Type uG) [Monoid G] [TopologicalSpace G]
    (M : Type uM) [AddCommGroup M] [DistribMulAction G M]
    (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
      [DistribSMul G N]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
      [DistribSMul G P]
    (μ : M →+ N →+ P)
    (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
    (m : H0 G M) (hm : Continuous (μ (m : M))) {b : G × G → N} (hb : b ∈ Z2 G N) :
    (fun q : G × G => μ (m : M) (b q)) ∈ Z2 G P := by
  have h : (fun q : G × G => μ (m : M) (b q)) =
      cochainsMap2 (ContinuousMonoidHom.id G : G →* G) (μ (m : M)) b := by
    ext ⟨g, h⟩
    simp
  rw [h]
  exact cochainsMap2_mem_Z2 G N G P (ContinuousMonoidHom.id G) (μ (m : M))
    hm (pairingLeft_smul μ hequiv m) hb

variable (G : Type uG) [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- **The `(0,2)` cup product**, `(m ⌣ b) (g, h) = μ m (b (g, h))`. -/
noncomputable def explicitCup02 : H0 G M →+ H2 G N →+ H2 G P :=
  AddMonoidHom.mk'
    (fun m => explicitCoeff2 G N (pairingLeft μ hequiv m) (continuous_pairingLeft μ hequiv hμ m))
    fun m m' => AddMonoidHom.ext fun x => by
      induction x using QuotientAddGroup.induction_on with
      | _ c =>
        rw [AddMonoidHom.add_apply, explicitCoeff2_mk, explicitCoeff2_mk, explicitCoeff2_mk,
          ← QuotientAddGroup.mk_add]
        exact congrArg (fun z : Z2 G P => (z : H2 G P))
          (Subtype.ext (funext fun q => by obtain ⟨g, h⟩ := q; simp [coe_cocyclesMap2]))

/-- The `(0,2)` cup is the coefficient map induced by the pairing at an invariant element. -/
theorem explicitCup02_apply (m : H0 G M) :
    explicitCup02 G M N P μ hμ hequiv m =
      explicitCoeff2 G N (pairingLeft μ hequiv m) (continuous_pairingLeft μ hequiv hμ m) :=
  (rfl)

/-- The cochain formula for the `(0,2)` cup on the class of a continuous `2`-cocycle. -/
@[simp]
theorem explicitCup02_mk (m : H0 G M) (b : Z2 G N) :
    explicitCup02 G M N P μ hμ hequiv m (b : H2 G N) =
      ((⟨fun q : G × G => μ (m : M) ((b : G × G → N) q),
        cup02_mem_Z2 G M N P μ hequiv m (hμ.uncurry_left (f := (μ · ·)) (m : M))
          b.property⟩ : Z2 G P) : H2 G P) := by
  rw [explicitCup02_apply, explicitCoeff2_mk]
  exact congrArg (fun z : Z2 G P => (z : H2 G P))
    (Subtype.ext (funext fun q => by obtain ⟨g, h⟩ := q; simp [coe_cocyclesMap2]))

end CupZeroTwo

section CupTwoZero

/-- **The `(2,0)` cup of a continuous `2`-cocycle with an invariant element is a continuous
`2`-cocycle.** -/
theorem cup20_mem_Z2 (G : Type uG) [Monoid G] [TopologicalSpace G]
    (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [DistribSMul G M]
    (N : Type uN) [AddCommGroup N] [DistribMulAction G N]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
      [DistribSMul G P]
    (μ : M →+ N →+ P)
    (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
    {a : G × G → M} (ha : a ∈ Z2 G M) (n : H0 G N) (hn : Continuous (μ.flip (n : N))) :
    (fun q : G × G => μ (a q) ((q.1 * q.2) • (n : N))) ∈ Z2 G P := by
  have h : (fun q : G × G => μ (a q) ((q.1 * q.2) • (n : N))) =
      cochainsMap2 (ContinuousMonoidHom.id G : G →* G) (μ.flip (n : N)) a := by
    ext ⟨g, h⟩
    simp [n.property (g * h)]
  rw [h]
  exact cochainsMap2_mem_Z2 G M G P (ContinuousMonoidHom.id G) (μ.flip (n : N))
    hn (pairingRight_smul μ hequiv n) ha

variable (G : Type uG) [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DistribMulAction G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- **The `(2,0)` cup product**, `(a ⌣ n) (g, h) = μ (a (g, h)) ((g * h) • n)`. This is the last
of the six shapes: no explicit cup goes above total degree `2`. -/
noncomputable def explicitCup20 : H2 G M →+ H0 G N →+ H2 G P :=
  AddMonoidHom.flip <| AddMonoidHom.mk'
    (fun n => explicitCoeff2 G M (pairingRight μ hequiv n) (continuous_pairingRight μ hequiv hμ n))
    fun n n' => AddMonoidHom.ext fun x => by
      induction x using QuotientAddGroup.induction_on with
      | _ c =>
        rw [AddMonoidHom.add_apply, explicitCoeff2_mk, explicitCoeff2_mk, explicitCoeff2_mk,
          ← QuotientAddGroup.mk_add]
        exact congrArg (fun z : Z2 G P => (z : H2 G P))
          (Subtype.ext (funext fun q => by obtain ⟨g, h⟩ := q; simp [coe_cocyclesMap2]))

/-- The `(2,0)` cup is the coefficient map induced by the pairing at an invariant element. -/
theorem explicitCup20_apply (a : H2 G M) (n : H0 G N) :
    explicitCup20 G M N P μ hμ hequiv a n =
      explicitCoeff2 G M (pairingRight μ hequiv n) (continuous_pairingRight μ hequiv hμ n) a :=
  (rfl)

/-- The cochain formula for the `(2,0)` cup on the class of a continuous `2`-cocycle. -/
@[simp]
theorem explicitCup20_mk (a : Z2 G M) (n : H0 G N) :
    explicitCup20 G M N P μ hμ hequiv (a : H2 G M) n =
      ((⟨fun q : G × G => μ ((a : G × G → M) q) ((q.1 * q.2) • (n : N)),
        cup20_mem_Z2 G M N P μ hequiv a.property n
          (hμ.uncurry_right (f := (μ · ·)) (n : N))⟩ : Z2 G P) : H2 G P) := by
  rw [explicitCup20_apply, explicitCoeff2_mk]
  exact congrArg (fun z : Z2 G P => (z : H2 G P))
    (Subtype.ext (funext fun q => by
      obtain ⟨g, h⟩ := q; simp [coe_cocyclesMap2, n.property (g * h)]))

end CupTwoZero

section CupOneOne

/-- **The `(1,1)` cup of two continuous `1`-cocycles is a continuous `2`-cocycle.** This is the
cochain-level heart of the only shape that is not a coefficient map: the translation factor `g •`
on the second cocycle is what turns the two `1`-cocycle identities into the `2`-cocycle
identity. -/
theorem cup11_mem_Z2 (G : Type uG) [Semigroup G] [TopologicalSpace G]
    (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [DistribSMul G M]
    (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
      [DistribSMul G N] [ContinuousSMul G N]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
      [DistribSMul G P]
    (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
    (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
    {a : G → M} (ha : a ∈ Z1 G M) {b : G → N} (hb : b ∈ Z1 G N) :
    (fun q : G × G => μ (a q.1) (q.1 • b q.2)) ∈ Z2 G P := by
  obtain ⟨hac, ha1⟩ := mem_Z1_iff.1 ha
  obtain ⟨hbc, hb1⟩ := mem_Z1_iff.1 hb
  refine mem_Z2_iff.2 ⟨hμ.comp ((hac.comp continuous_fst).prodMk
    (continuous_fst.smul (hbc.comp continuous_snd))), fun g h j => ?_⟩
  have hsmul : (g * h) • b j = g • (h • b j) := by
    have h1 := hb1 (g * h) j
    rw [mul_assoc, hb1 g (h * j), hb1 h j, hb1 g h, smul_add, add_assoc] at h1
    exact add_right_cancel h1.symm
  -- beta-reduce the cup cochain; see the implementation notes.
  change μ (a (g * h)) ((g * h) • b j) + μ (a g) (g • b h) =
    g • μ (a h) (h • b j) + μ (a g) (g • b (h * j))
  simp only [ha1 g h, hb1 h j, hsmul, map_add, AddMonoidHom.add_apply, smul_add, hequiv]
  abel

/-- **The `(1,1)` cup descends through coboundaries in the first variable**: if `a = d⁰ m` then
`a ⌣ b = d¹ (x ↦ μ m (b x))`. -/
theorem cup11_mem_B2_left (G : Type uG) [Mul G] [TopologicalSpace G]
    (M : Type uM) [AddCommGroup M] [DistribSMul G M]
    (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
      [DistribSMul G N]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
      [DistribSMul G P]
    (μ : M →+ N →+ P) (hμ : ∀ m : M, Continuous (μ m))
    (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
    {a : G → M} (ha : a ∈ B1 G M) {b : G → N} (hb : b ∈ Z1 G N) :
    (fun q : G × G => μ (a q.1) (q.1 • b q.2)) ∈ B2 G P := by
  obtain ⟨m, hm⟩ := mem_B1_iff.1 ha
  obtain ⟨hbc, hb1⟩ := mem_Z1_iff.1 hb
  refine mem_B2_iff'.2 ⟨fun x => μ m (b x), (hμ m).comp hbc, fun g h => ?_⟩
  -- beta-reduce the cup cochain; see the implementation notes.
  change g • μ m (b h) - μ m (b (g * h)) + μ m (b g) = μ (a g) (g • b h)
  rw [← hm g, hb1 g h]
  simp only [map_add, map_sub, AddMonoidHom.sub_apply, hequiv]
  abel

/-- **The `(1,1)` cup descends through coboundaries in the second variable**: if `b = d⁰ n` then
`a ⌣ b = d¹ (x ↦ -μ (a x) (x • n))`. -/
theorem cup11_mem_B2_right (G : Type uG) [Mul G] [TopologicalSpace G]
    (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [DistribSMul G M]
    (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DistribSMul G N] [IsScalarTower G G N]
      [ContinuousSMul G N]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
      [DistribSMul G P]
    (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
    (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
    {a : G → M} (ha : a ∈ Z1 G M) {b : G → N} (hb : b ∈ B1 G N) :
    (fun q : G × G => μ (a q.1) (q.1 • b q.2)) ∈ B2 G P := by
  obtain ⟨n, hn⟩ := mem_B1_iff.1 hb
  obtain ⟨hac, ha1⟩ := mem_Z1_iff.1 ha
  refine mem_B2_iff'.2 ⟨fun x => -μ (a x) (x • n),
    (hμ.comp (hac.prodMk (continuous_id.smul continuous_const))).neg, fun g h => ?_⟩
  -- beta-reduce the cup cochain; see the implementation notes.
  change g • -μ (a h) (h • n) - -μ (a (g * h)) ((g * h) • n) + -μ (a g) (g • n) =
    μ (a g) (g • b h)
  have hsmul : (g * h) • n = g • (h • n) := by
    rw [← smul_eq_mul, smul_assoc]
  rw [← hn h, ha1 g h, hsmul]
  simp only [smul_sub, smul_neg, map_add, map_sub, AddMonoidHom.add_apply, hequiv]
  abel

variable (G : Type uG) [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- The `(1,1)` cup on cocycles, biadditive by construction. -/
private noncomputable def cocyclesCup11 : Z1 G M →+ Z1 G N →+ Z2 G P where
  toFun a :=
    { toFun := fun b =>
        ⟨fun q : G × G => μ ((a : G → M) q.1) (q.1 • (b : G → N) q.2),
          cup11_mem_Z2 G M N P μ hμ hequiv a.property b.property⟩
      map_zero' := Subtype.ext (funext fun _ => by simp)
      map_add' := fun _ _ => Subtype.ext (funext fun _ => by simp [smul_add]) }
  map_zero' := AddMonoidHom.ext fun _ => Subtype.ext (funext fun _ => by simp)
  map_add' _ _ := AddMonoidHom.ext fun _ => Subtype.ext (funext fun _ => by simp)

/-- **The `(1,1)` cup product**, the descent of the cochain formula
`(a ⌣ b) (g, h) = μ (a g) (g • b h)`. This is the only one of the six shapes that is not a
coefficient map. -/
noncomputable def explicitCup11 : H1 G M →+ H1 G N →+ H2 G P :=
  QuotientAddGroup.lift _
    { toFun := fun a =>
        QuotientAddGroup.lift _
          ((QuotientAddGroup.mk' ((B2 G P).addSubgroupOf (Z2 G P))).comp
            (cocyclesCup11 G M N P μ hμ hequiv a))
          fun b hb => (QuotientAddGroup.eq_zero_iff _).2 <| AddSubgroup.mem_addSubgroupOf.2 <|
            cup11_mem_B2_right G M N P μ hμ hequiv a.property (AddSubgroup.mem_addSubgroupOf.1 hb)
      map_zero' := AddMonoidHom.ext fun x => by
        induction x using QuotientAddGroup.induction_on with
        | _ b =>
          exact congrArg (fun z : Z2 G P => (z : H2 G P))
            (DFunLike.congr_fun (map_zero (cocyclesCup11 G M N P μ hμ hequiv)) b)
      map_add' := fun a a' => AddMonoidHom.ext fun x => by
        induction x using QuotientAddGroup.induction_on with
        | _ b =>
          rw [AddMonoidHom.add_apply]
          exact (congrArg (fun z : Z2 G P => (z : H2 G P))
            (DFunLike.congr_fun (map_add (cocyclesCup11 G M N P μ hμ hequiv) a a') b)).trans
            (QuotientAddGroup.mk_add _ _ _) }
    fun a ha => AddMonoidHom.ext fun x => by
      induction x using QuotientAddGroup.induction_on with
      | _ b =>
        exact (QuotientAddGroup.eq_zero_iff _).2 <| AddSubgroup.mem_addSubgroupOf.2 <|
          cup11_mem_B2_left G M N P μ (fun m => hμ.uncurry_left (f := (μ · ·)) m)
            hequiv (AddSubgroup.mem_addSubgroupOf.1 ha) b.property

/-- The cochain formula for the `(1,1)` cup on the classes of two continuous `1`-cocycles. -/
@[simp]
theorem explicitCup11_mk (a : Z1 G M) (b : Z1 G N) :
    explicitCup11 G M N P μ hμ hequiv (a : H1 G M) (b : H1 G N) =
      ((⟨fun q : G × G => μ ((a : G → M) q.1) (q.1 • (b : G → N) q.2),
        cup11_mem_Z2 G M N P μ hμ hequiv a.property b.property⟩ : Z2 G P) : H2 G P) :=
  (rfl)

end CupOneOne

end TauCeti.ContCohomology
