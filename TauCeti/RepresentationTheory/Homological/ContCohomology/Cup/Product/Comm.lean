/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Hom.Instances
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product.Basic
public import TauCeti.Topology.Algebra.Group.Hom

/-!
# Graded commutativity of explicit low-degree cup products

For a `G`-equivariant biadditive pairing `μ : M →+ N →+ P`, the opposite pairing is Mathlib's
`μ.flip : N →+ M →+ P`, `μ.flip n m = μ m n`. This file proves graded commutativity

```text
a ⌣_μ b = (-1)^{pq} (b ⌣_{μᵒᵖ} a)
```

for every bidegree `(p, q)` with `p + q ≤ 2` on the explicit low-degree model built in
`TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product.Basic`.

## Main statements

* `TauCeti.ContCohomology.explicitCup00_comm`, `explicitCup01_eq_cup10_flip`,
  `explicitCup02_eq_cup20_flip` and `explicitCup11_eq_neg_flip`: **graded commutativity** in each
  bidegree with `p + q ≤ 2`. In the three shapes with a degree-`0` factor, the sign is `1` and the
  identity already holds on cochains (`cup01_eq_cup10_flip`, `cup02_eq_cup20_flip`), a degree-`0`
  class being invariant. In bidegree `(1,1)` it holds on classes with the sign `-1`.
* `TauCeti.ContCohomology.cup11_add_cup11_flip_eq_d1` and `cup11_add_cup11_flip_mem_B2`: the
  explicit homotopy `(a ⌣_μ b) + (b ⌣_{μᵒᵖ} a) = d¹ (g ↦ -μ (a g) (b g))` behind graded
  commutativity in bidegree `(1,1)`.
* `TauCeti.ContCohomology.explicitCup11_comm_of_neg_eq_self`: the `2`-torsion specialization, in
  which the `(1,1)` cup is symmetric.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., I §4, (1.4.4).
* K. Brown, *Cohomology of Groups*, V §3, (3.6).
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uN uP

section CommZeroZero

variable (G : Type uG) [Monoid G]
  (M : Type uM) [AddCommGroup M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [DistribMulAction G N]
  (P : Type uP) [AddCommGroup P] [DistribMulAction G P]
  (μ : M →+ N →+ P)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- **Graded commutativity in bidegree `(0,0)`.** The sign `(-1)^{pq}` is `1`, and the two
cochains, here two elements of `P`, are literally equal. -/
theorem explicitCup00_comm (m : H0 G M) (n : H0 G N) :
    explicitCup00 G M N P μ hequiv m n =
      explicitCup00 G N M P μ.flip
        (μ.flip_map_smul hequiv) n m :=
  Subtype.ext (by simp)

end CommZeroZero

section CommCochain

/-! The two cochain identities below require no topology or action on the second factor: a
degree-`0` class is invariant. -/

variable (G : Type uG) [Monoid G]
  (M : Type uM) [AddCommGroup M] [DistribMulAction G M]
  (N : Type uN) [AddZeroClass N]
  (P : Type uP) [AddCommMonoid P]
  (μ : M →+ N →+ P)

/-- **Graded commutativity in bidegree `(0,1)`, at cochain level.** The `(1,0)` cup of a cochain
`b` with the invariant `m` along the opposite pairing is the `(0,1)` cup of `m` with `b`: the
translation factor `g •` the `(1,0)` formula carries acts on `m`, which is invariant. -/
theorem cup01_eq_cup10_flip (m : H0 G M) (b : G → N) :
    (fun g => μ (m : M) (b g)) = fun g => μ.flip (b g) (g • (m : M)) := by
  funext g
  rw [AddMonoidHom.flip_apply, m.property g]

/-- **Graded commutativity in bidegree `(0,2)`, at cochain level**, the degree-`2` counterpart of
`TauCeti.ContCohomology.cup01_eq_cup10_flip`. -/
theorem cup02_eq_cup20_flip (m : H0 G M) (b : G × G → N) :
    (fun q : G × G => μ (m : M) (b q)) =
      fun q : G × G => μ.flip (b q) ((q.1 * q.2) • (m : M)) := by
  funext q
  rw [AddMonoidHom.flip_apply, m.property (q.1 * q.2)]

end CommCochain

section CommZeroOne

variable (G : Type uG) [Monoid G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- **Graded commutativity in bidegree `(0,1)`.** The sign `(-1)^{pq}` is `1`, and by
`TauCeti.ContCohomology.cup01_eq_cup10_flip` the identity already holds on cochains. -/
theorem explicitCup01_eq_cup10_flip (m : H0 G M) (b : H1 G N) :
    explicitCup01 G M N P μ hμ hequiv m b =
      explicitCup10 G N M P μ.flip
        (μ.continuous_flip hμ)
        (μ.flip_map_smul hequiv) b m := by
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitCup01_mk, explicitCup10_mk]
    exact congrArg (fun z : Z1 G P => (z : H1 G P))
      (Subtype.ext (cup01_eq_cup10_flip G M N P μ m (c : G → N)))

end CommZeroOne

section CommZeroTwo

variable (G : Type uG) [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- **Graded commutativity in bidegree `(0,2)`.** The sign `(-1)^{pq}` is `1`, and by
`TauCeti.ContCohomology.cup02_eq_cup20_flip` the identity already holds on cochains. -/
theorem explicitCup02_eq_cup20_flip (m : H0 G M) (b : H2 G N) :
    explicitCup02 G M N P μ hμ hequiv m b =
      explicitCup20 G N M P μ.flip
        (μ.continuous_flip hμ)
        (μ.flip_map_smul hequiv) b m := by
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitCup02_mk, explicitCup20_mk]
    exact congrArg (fun z : Z2 G P => (z : H2 G P))
      (Subtype.ext (cup02_eq_cup20_flip G M N P μ m (c : G × G → N)))

end CommZeroTwo

section Homotopy

/-- **The homotopy behind graded commutativity in bidegree `(1,1)`.** The two cochains
`a ⌣_μ b` and `b ⌣_{μᵒᵖ} a` need not be equal in general; their sum is the coboundary of the
`1`-cochain `g ↦ -μ (a g) (b g)`. -/
theorem cup11_add_cup11_flip_eq_d1 (G : Type uG) [Mul G] [TopologicalSpace G]
    (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [DistribSMul G M]
    (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
      [DistribSMul G N]
    (P : Type uP) [AddCommGroup P] [DistribSMul G P]
    (μ : M →+ N →+ P)
    (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
    {a : G → M} (ha : a ∈ Z1 G M) {b : G → N} (hb : b ∈ Z1 G N) :
    ((fun q : G × G => μ (a q.1) (q.1 • b q.2)) +
        fun q : G × G => μ.flip (b q.1) (q.1 • a q.2)) =
      d1 G P fun g => -μ (a g) (b g) := by
  obtain ⟨-, ha1⟩ := mem_Z1_iff.1 ha
  obtain ⟨-, hb1⟩ := mem_Z1_iff.1 hb
  funext q
  obtain ⟨g, h⟩ := q
  simp only [Pi.add_apply, AddMonoidHom.flip_apply, d1_apply, ha1 g h, hb1 g h, map_add,
    AddMonoidHom.add_apply, smul_neg, hequiv]
  abel

/-- **The sum of the two `(1,1)` cup cochains is a coboundary**, by
`TauCeti.ContCohomology.cup11_add_cup11_flip_eq_d1`; its primitive is continuous because `μ` is
jointly continuous. -/
theorem cup11_add_cup11_flip_mem_B2 (G : Type uG) [Mul G] [TopologicalSpace G]
    (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [DistribSMul G M]
    (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
      [DistribSMul G N]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
      [DistribSMul G P]
    (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
    (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
    {a : G → M} (ha : a ∈ Z1 G M) {b : G → N} (hb : b ∈ Z1 G N) :
    ((fun q : G × G => μ (a q.1) (q.1 • b q.2)) +
      fun q : G × G => μ.flip (b q.1) (q.1 • a q.2)) ∈ B2 G P :=
  mem_B2_iff.2 ⟨fun g => -μ (a g) (b g),
    (hμ.comp ((mem_Z1_iff.1 ha).1.prodMk (mem_Z1_iff.1 hb).1)).neg,
    (cup11_add_cup11_flip_eq_d1 G M N P μ hequiv ha hb).symm⟩

end Homotopy

section CommOneOne

variable (G : Type uG) [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- **Graded commutativity in bidegree `(1,1)`**, `a ⌣_μ b = -(b ⌣_{μᵒᵖ} a)`, the sign
`(-1)^{pq}` now being `-1`. This is an identity of classes and not of cochains: the two cochains
differ by the coboundary exhibited in
`TauCeti.ContCohomology.cup11_add_cup11_flip_eq_d1`. -/
theorem explicitCup11_eq_neg_flip (a : H1 G M) (b : H1 G N) :
    explicitCup11 G M N P μ hμ hequiv a b =
      -explicitCup11 G N M P μ.flip
        (μ.continuous_flip hμ)
        (μ.flip_map_smul hequiv) b a := by
  induction a using QuotientAddGroup.induction_on with
  | _ x =>
    induction b using QuotientAddGroup.induction_on with
    | _ y =>
      rw [explicitCup11_mk, explicitCup11_mk, eq_neg_iff_add_eq_zero, ← QuotientAddGroup.mk_add,
        H2pi_eq_zero_iff]
      exact cup11_add_cup11_flip_mem_B2 G M N P μ hμ hequiv x.property y.property

/-- **Graded commutativity in bidegree `(1,1)` for `2`-torsion coefficients**: when every element
of `P` is its own negative the `(1,1)` cup is symmetric on classes. This is the form the
`𝔽₂`-valued arithmetic applications use, where every sign is `1`. -/
theorem explicitCup11_comm_of_neg_eq_self (hP : ∀ x : P, -x = x) (a : H1 G M) (b : H1 G N) :
    explicitCup11 G M N P μ hμ hequiv a b =
      explicitCup11 G N M P μ.flip
        (μ.continuous_flip hμ)
        (μ.flip_map_smul hequiv) b a := by
  have h2 := nsmul_H2_eq_zero (G := G) (M := P) (n := 2)
    (fun x => by rw [two_nsmul, add_eq_zero_iff_eq_neg, hP])
    (explicitCup11 G N M P μ.flip (μ.continuous_flip hμ) (μ.flip_map_smul hequiv) b a)
  rw [two_nsmul, add_eq_zero_iff_eq_neg] at h2
  rw [explicitCup11_eq_neg_flip G M N P μ hμ hequiv a b, ← h2]

end CommOneOne

end TauCeti.ContCohomology
