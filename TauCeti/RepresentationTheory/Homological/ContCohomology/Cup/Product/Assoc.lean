/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product.Basic

/-!
# Associativity of explicit low-degree cup products

Typing the two sides of an associativity statement needs four `G`-equivariant biadditive pairings
`μ₁ : A →+ B →+ D`, `μ₂ : D →+ C →+ E`, `ν₁ : B →+ C →+ F` and `ν₂ : A →+ F →+ E`. The coefficient
identity `μ₂ (μ₁ a b) c = ν₂ a (ν₁ b c)` is the hypothesis under which the two well-typed
composites are equal:

```text
(x ⌣_{μ₁} y) ⌣_{μ₂} z = x ⌣_{ν₂} (y ⌣_{ν₁} z).
```

This file proves all ten tridegrees `(p, q, r)` with `p + q + r ≤ 2` on the explicit low-degree
model built in `TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product.Basic`, together
with their specialization to a topological `G`-ring `R` with all four pairings given by
multiplication.

## Main statements

* `TauCeti.ContCohomology.explicitCup_assoc000` and its nine siblings: **associativity** in each
  tridegree `(p, q, r)` with `p + q + r ≤ 2`, the three digits of the name being that tridegree.
  Each holds already on cochains.
* `TauCeti.ContCohomology.explicitCup_assoc000_mul` and its nine siblings: the same ten identities
  for a topological `G`-ring `R`, all four pairings its multiplication.

## Implementation notes

Where the right-hand side cups `y` and `z` together first, the left-hand side carries the
translation factor of the general inhomogeneous formula on `y` and on `z` separately while the
right-hand side carries a single one on `y ⌣_{ν₁} z`. The equivariance of `ν₁` is what merges
them, and that is what the proofs of `explicitCup_assoc100`, `explicitCup_assoc200`,
`explicitCup_assoc110` and `explicitCup_assoc101` use it for.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., I §4.
* K. Brown, *Cohomology of Groups*, V §3, (3.5).
-/

public section

namespace TauCeti.ContCohomology

universe uG uA uB uC uD uE uF uR

section Assoc

variable (G : Type uG) [Monoid G]
  (A : Type uA) [AddCommGroup A] [DistribMulAction G A]
  (B : Type uB) [AddCommGroup B] [DistribMulAction G B]
  (C : Type uC) [AddCommGroup C] [DistribMulAction G C]
  (D : Type uD) [AddCommGroup D] [DistribMulAction G D]
  (E : Type uE) [AddCommGroup E] [DistribMulAction G E]
  (F : Type uF) [AddCommGroup F] [DistribMulAction G F]
  (μ₁ : A →+ B →+ D) (hequiv₁ : ∀ (g : G) (a : A) (b : B), μ₁ (g • a) (g • b) = g • μ₁ a b)
  (μ₂ : D →+ C →+ E) (hequiv₂ : ∀ (g : G) (d : D) (c : C), μ₂ (g • d) (g • c) = g • μ₂ d c)
  (ν₁ : B →+ C →+ F) (hequiv₃ : ∀ (g : G) (b : B) (c : C), ν₁ (g • b) (g • c) = g • ν₁ b c)
  (ν₂ : A →+ F →+ E) (hequiv₄ : ∀ (g : G) (a : A) (f : F), ν₂ (g • a) (g • f) = g • ν₂ a f)
  (hassoc : ∀ (a : A) (b : B) (c : C), μ₂ (μ₁ a b) c = ν₂ a (ν₁ b c))

include hassoc

/-- **Associativity of the cup product in tridegree `(0,0,0)`**, where all three classes are
invariant elements and the identity is the coefficient identity itself. -/
theorem explicitCup_assoc000 (x : H0 G A) (y : H0 G B) (z : H0 G C) :
    explicitCup00 G D C E μ₂ hequiv₂ (explicitCup00 G A B D μ₁ hequiv₁ x y) z =
      explicitCup00 G A F E ν₂ hequiv₄ x (explicitCup00 G B C F ν₁ hequiv₃ y z) :=
  Subtype.ext (by simp [hassoc])

section PositiveDegree

variable [TopologicalSpace G]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [TopologicalSpace D] [TopologicalSpace E] [TopologicalSpace F]
  [IsTopologicalAddGroup E] [ContinuousSMul G E]

section FirstZero

/-! The tridegrees `(0,0,r)`: the first two factors are invariant, so `μ₁` is used only through
the `(0,0)` cup and no continuity of it is needed. -/

variable [IsTopologicalAddGroup C] [ContinuousSMul G C]
  [IsTopologicalAddGroup F] [ContinuousSMul G F]
  (hμ₂ : Continuous fun p : D × C => μ₂ p.1 p.2)
  (hν₁ : Continuous fun p : B × C => ν₁ p.1 p.2)
  (hν₂ : Continuous fun p : A × F => ν₂ p.1 p.2)

/-- **Associativity of the cup product in tridegree `(0,0,1)`.** -/
theorem explicitCup_assoc001 (x : H0 G A) (y : H0 G B) (z : H1 G C) :
    explicitCup01 G D C E μ₂ hμ₂ hequiv₂ (explicitCup00 G A B D μ₁ hequiv₁ x y) z =
      explicitCup01 G A F E ν₂ hν₂ hequiv₄ x (explicitCup01 G B C F ν₁ hν₁ hequiv₃ y z) := by
  induction z using QuotientAddGroup.induction_on with
  | _ c =>
    simp only [explicitCup01_mk]
    exact congrArg (fun w : Z1 G E => (w : H1 G E))
      (Subtype.ext (funext fun _ => by simp [hassoc]))

/-- **Associativity of the cup product in tridegree `(0,0,2)`**, the degree-`2` counterpart of
`TauCeti.ContCohomology.explicitCup_assoc001`. -/
theorem explicitCup_assoc002 [ContinuousMul G] (x : H0 G A) (y : H0 G B) (z : H2 G C) :
    explicitCup02 G D C E μ₂ hμ₂ hequiv₂ (explicitCup00 G A B D μ₁ hequiv₁ x y) z =
      explicitCup02 G A F E ν₂ hν₂ hequiv₄ x (explicitCup02 G B C F ν₁ hν₁ hequiv₃ y z) := by
  induction z using QuotientAddGroup.induction_on with
  | _ c =>
    simp only [explicitCup02_mk]
    exact congrArg (fun w : Z2 G E => (w : H2 G E))
      (Subtype.ext (funext fun _ => by simp [hassoc]))

end FirstZero

section Middle

/-! The tridegrees `(0,q,0)`: the outer factors are invariant. -/

variable [IsTopologicalAddGroup B] [ContinuousSMul G B]
  [IsTopologicalAddGroup D] [ContinuousSMul G D]
  [IsTopologicalAddGroup F] [ContinuousSMul G F]
  (hμ₁ : Continuous fun p : A × B => μ₁ p.1 p.2)
  (hμ₂ : Continuous fun p : D × C => μ₂ p.1 p.2)
  (hν₁ : Continuous fun p : B × C => ν₁ p.1 p.2)
  (hν₂ : Continuous fun p : A × F => ν₂ p.1 p.2)

/-- **Associativity of the cup product in tridegree `(0,1,0)`.** -/
theorem explicitCup_assoc010 (x : H0 G A) (y : H1 G B) (z : H0 G C) :
    explicitCup10 G D C E μ₂ hμ₂ hequiv₂ (explicitCup01 G A B D μ₁ hμ₁ hequiv₁ x y) z =
      explicitCup01 G A F E ν₂ hν₂ hequiv₄ x (explicitCup10 G B C F ν₁ hν₁ hequiv₃ y z) := by
  induction y using QuotientAddGroup.induction_on with
  | _ b =>
    simp only [explicitCup01_mk, explicitCup10_mk]
    exact congrArg (fun w : Z1 G E => (w : H1 G E))
      (Subtype.ext (funext fun _ => by simp [hassoc]))

/-- **Associativity of the cup product in tridegree `(0,2,0)`**, the degree-`2` counterpart of
`TauCeti.ContCohomology.explicitCup_assoc010`. -/
theorem explicitCup_assoc020 [ContinuousMul G] (x : H0 G A) (y : H2 G B) (z : H0 G C) :
    explicitCup20 G D C E μ₂ hμ₂ hequiv₂ (explicitCup02 G A B D μ₁ hμ₁ hequiv₁ x y) z =
      explicitCup02 G A F E ν₂ hν₂ hequiv₄ x (explicitCup20 G B C F ν₁ hν₁ hequiv₃ y z) := by
  induction y using QuotientAddGroup.induction_on with
  | _ b =>
    simp only [explicitCup02_mk, explicitCup20_mk]
    exact congrArg (fun w : Z2 G E => (w : H2 G E))
      (Subtype.ext (funext fun _ => by simp [hassoc]))

end Middle

section LastZero

/-! The tridegrees `(p,0,0)`: the last two factors are invariant, so `ν₁` is used only through the
`(0,0)` cup. The translation factor of the general formula sits on `ν₁ b c`, and it is
`hequiv₃` that moves it onto the two factors separately. -/

variable [IsTopologicalAddGroup A] [ContinuousSMul G A]
  [IsTopologicalAddGroup D] [ContinuousSMul G D]
  (hμ₁ : Continuous fun p : A × B => μ₁ p.1 p.2)
  (hμ₂ : Continuous fun p : D × C => μ₂ p.1 p.2)
  (hν₂ : Continuous fun p : A × F => ν₂ p.1 p.2)

/-- **Associativity of the cup product in tridegree `(1,0,0)`.** -/
theorem explicitCup_assoc100 (x : H1 G A) (y : H0 G B) (z : H0 G C) :
    explicitCup10 G D C E μ₂ hμ₂ hequiv₂ (explicitCup10 G A B D μ₁ hμ₁ hequiv₁ x y) z =
      explicitCup10 G A F E ν₂ hν₂ hequiv₄ x (explicitCup00 G B C F ν₁ hequiv₃ y z) := by
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    simp only [explicitCup10_mk]
    exact congrArg (fun w : Z1 G E => (w : H1 G E))
      (Subtype.ext (funext fun _ => by simp [hassoc, hequiv₃]))

/-- **Associativity of the cup product in tridegree `(2,0,0)`**, the degree-`2` counterpart of
`TauCeti.ContCohomology.explicitCup_assoc100`. -/
theorem explicitCup_assoc200 [ContinuousMul G] (x : H2 G A) (y : H0 G B) (z : H0 G C) :
    explicitCup20 G D C E μ₂ hμ₂ hequiv₂ (explicitCup20 G A B D μ₁ hμ₁ hequiv₁ x y) z =
      explicitCup20 G A F E ν₂ hν₂ hequiv₄ x (explicitCup00 G B C F ν₁ hequiv₃ y z) := by
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    simp only [explicitCup20_mk]
    exact congrArg (fun w : Z2 G E => (w : H2 G E))
      (Subtype.ext (funext fun _ => by simp [hassoc, hequiv₃]))

end LastZero

section DegreeTwo

variable [ContinuousMul G]
  [IsTopologicalAddGroup D] [ContinuousSMul G D]
  [IsTopologicalAddGroup F] [ContinuousSMul G F]
  (hμ₁ : Continuous fun p : A × B => μ₁ p.1 p.2)
  (hμ₂ : Continuous fun p : D × C => μ₂ p.1 p.2)
  (hν₁ : Continuous fun p : B × C => ν₁ p.1 p.2)
  (hν₂ : Continuous fun p : A × F => ν₂ p.1 p.2)

/-- **Associativity of the cup product in tridegree `(0,1,1)`.** The `(1,1)` cup appears on the
right-hand side and its translation factor is common to both sides, the outer factor being
invariant. -/
theorem explicitCup_assoc011 [IsTopologicalAddGroup B] [ContinuousSMul G B]
    [IsTopologicalAddGroup C] [ContinuousSMul G C]
    (x : H0 G A) (y : H1 G B) (z : H1 G C) :
    explicitCup11 G D C E μ₂ hμ₂ hequiv₂ (explicitCup01 G A B D μ₁ hμ₁ hequiv₁ x y) z =
      explicitCup02 G A F E ν₂ hν₂ hequiv₄ x (explicitCup11 G B C F ν₁ hν₁ hequiv₃ y z) := by
  induction y using QuotientAddGroup.induction_on with
  | _ b =>
    induction z using QuotientAddGroup.induction_on with
    | _ c =>
      simp only [explicitCup01_mk, explicitCup11_mk, explicitCup02_mk]
      exact congrArg (fun w : Z2 G E => (w : H2 G E))
        (Subtype.ext (funext fun _ => by simp [hassoc]))

/-- **Associativity of the cup product in tridegree `(1,1,0)`.** This is the instance that forces
the `(1,0)` shape into the family: the right-hand side cups the invariant `z` onto `y` in
bidegree `(1,0)` before pairing with `x`. The two translation factors match by `mul_smul` and the
equivariance of `ν₁`. -/
theorem explicitCup_assoc110 [IsTopologicalAddGroup A] [ContinuousSMul G A]
    [IsTopologicalAddGroup B] [ContinuousSMul G B]
    (x : H1 G A) (y : H1 G B) (z : H0 G C) :
    explicitCup20 G D C E μ₂ hμ₂ hequiv₂ (explicitCup11 G A B D μ₁ hμ₁ hequiv₁ x y) z =
      explicitCup11 G A F E ν₂ hν₂ hequiv₄ x (explicitCup10 G B C F ν₁ hν₁ hequiv₃ y z) := by
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    induction y using QuotientAddGroup.induction_on with
    | _ b =>
      simp only [explicitCup11_mk, explicitCup20_mk, explicitCup10_mk]
      exact congrArg (fun w : Z2 G E => (w : H2 G E))
        (Subtype.ext (funext fun _ => by simp [hassoc, mul_smul, hequiv₃]))

/-- **Associativity of the cup product in tridegree `(1,0,1)`**, the last of the ten instances
with `p + q + r ≤ 2`. -/
theorem explicitCup_assoc101 [IsTopologicalAddGroup A] [ContinuousSMul G A]
    [IsTopologicalAddGroup C] [ContinuousSMul G C]
    (x : H1 G A) (y : H0 G B) (z : H1 G C) :
    explicitCup11 G D C E μ₂ hμ₂ hequiv₂ (explicitCup10 G A B D μ₁ hμ₁ hequiv₁ x y) z =
      explicitCup11 G A F E ν₂ hν₂ hequiv₄ x (explicitCup01 G B C F ν₁ hν₁ hequiv₃ y z) := by
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    induction z using QuotientAddGroup.induction_on with
    | _ c =>
      simp only [explicitCup10_mk, explicitCup11_mk, explicitCup01_mk]
      exact congrArg (fun w : Z2 G E => (w : H2 G E))
        (Subtype.ext (funext fun _ => by simp [hassoc, hequiv₃]))

end DegreeTwo

end PositiveDegree

end Assoc

section AssocRing

/-! ### Associativity for a topological `G`-ring

One coefficient ring `R` acted on by ring endomorphisms, all four pairings its multiplication
`AddMonoidHom.mul`, and the coefficient identity `mul_assoc`. The continuity and equivariance a
pairing has to come with are `continuous_mul` and `smul_mul'`, which apply to `AddMonoidHom.mul`
as they stand. Each of the ten statements below is the corresponding general statement instantiated
there. -/

variable (G : Type uG) [Monoid G]
  (R : Type uR) [Ring R] [MulSemiringAction G R]

/-- **Associativity of the ring cup product in tridegree `(0,0,0)`.** -/
theorem explicitCup_assoc000_mul (x y z : H0 G R) :
    explicitCup00 G R R R AddMonoidHom.mul (fun g a b => (smul_mul' g a b).symm)
        (explicitCup00 G R R R AddMonoidHom.mul (fun g a b => (smul_mul' g a b).symm) x y) z =
      explicitCup00 G R R R AddMonoidHom.mul (fun g a b => (smul_mul' g a b).symm) x
        (explicitCup00 G R R R AddMonoidHom.mul (fun g a b => (smul_mul' g a b).symm) y z) :=
  explicitCup_assoc000 G R R R R R R _ _ _ _ _ _ _ _ mul_assoc x y z

variable [TopologicalSpace G] [TopologicalSpace R] [IsTopologicalRing R] [ContinuousSMul G R]

/-- **Associativity of the ring cup product in tridegree `(0,0,1)`.** -/
theorem explicitCup_assoc001_mul (x y : H0 G R) (z : H1 G R) :
    explicitCup01 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm)
        (explicitCup00 G R R R AddMonoidHom.mul (fun g a b => (smul_mul' g a b).symm) x y) z =
      explicitCup01 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm) x
        (explicitCup01 G R R R AddMonoidHom.mul continuous_mul
          (fun g a b => (smul_mul' g a b).symm) y z) :=
  explicitCup_assoc001 G R R R R R R _ _ _ _ _ _ _ _ mul_assoc _ _ _ x y z

/-- **Associativity of the ring cup product in tridegree `(0,1,0)`.** -/
theorem explicitCup_assoc010_mul (x : H0 G R) (y : H1 G R) (z : H0 G R) :
    explicitCup10 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm)
        (explicitCup01 G R R R AddMonoidHom.mul continuous_mul
          (fun g a b => (smul_mul' g a b).symm) x y) z =
      explicitCup01 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm) x
        (explicitCup10 G R R R AddMonoidHom.mul continuous_mul
          (fun g a b => (smul_mul' g a b).symm) y z) :=
  explicitCup_assoc010 G R R R R R R _ _ _ _ _ _ _ _ mul_assoc _ _ _ _ x y z

/-- **Associativity of the ring cup product in tridegree `(1,0,0)`.** -/
theorem explicitCup_assoc100_mul (x : H1 G R) (y z : H0 G R) :
    explicitCup10 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm)
        (explicitCup10 G R R R AddMonoidHom.mul continuous_mul
          (fun g a b => (smul_mul' g a b).symm) x y) z =
      explicitCup10 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm) x
        (explicitCup00 G R R R AddMonoidHom.mul (fun g a b => (smul_mul' g a b).symm) y z) :=
  explicitCup_assoc100 G R R R R R R _ _ _ _ _ _ _ _ mul_assoc _ _ _ x y z

variable [ContinuousMul G]

/-- **Associativity of the ring cup product in tridegree `(0,0,2)`.** -/
theorem explicitCup_assoc002_mul (x y : H0 G R) (z : H2 G R) :
    explicitCup02 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm)
        (explicitCup00 G R R R AddMonoidHom.mul (fun g a b => (smul_mul' g a b).symm) x y) z =
      explicitCup02 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm) x
        (explicitCup02 G R R R AddMonoidHom.mul continuous_mul
          (fun g a b => (smul_mul' g a b).symm) y z) :=
  explicitCup_assoc002 G R R R R R R _ _ _ _ _ _ _ _ mul_assoc _ _ _ x y z

/-- **Associativity of the ring cup product in tridegree `(0,2,0)`.** -/
theorem explicitCup_assoc020_mul (x : H0 G R) (y : H2 G R) (z : H0 G R) :
    explicitCup20 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm)
        (explicitCup02 G R R R AddMonoidHom.mul continuous_mul
          (fun g a b => (smul_mul' g a b).symm) x y) z =
      explicitCup02 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm) x
        (explicitCup20 G R R R AddMonoidHom.mul continuous_mul
          (fun g a b => (smul_mul' g a b).symm) y z) :=
  explicitCup_assoc020 G R R R R R R _ _ _ _ _ _ _ _ mul_assoc _ _ _ _ x y z

/-- **Associativity of the ring cup product in tridegree `(2,0,0)`.** -/
theorem explicitCup_assoc200_mul (x : H2 G R) (y z : H0 G R) :
    explicitCup20 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm)
        (explicitCup20 G R R R AddMonoidHom.mul continuous_mul
          (fun g a b => (smul_mul' g a b).symm) x y) z =
      explicitCup20 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm) x
        (explicitCup00 G R R R AddMonoidHom.mul (fun g a b => (smul_mul' g a b).symm) y z) :=
  explicitCup_assoc200 G R R R R R R _ _ _ _ _ _ _ _ mul_assoc _ _ _ x y z

/-- **Associativity of the ring cup product in tridegree `(0,1,1)`.** -/
theorem explicitCup_assoc011_mul (x : H0 G R) (y z : H1 G R) :
    explicitCup11 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm)
        (explicitCup01 G R R R AddMonoidHom.mul continuous_mul
          (fun g a b => (smul_mul' g a b).symm) x y) z =
      explicitCup02 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm) x
        (explicitCup11 G R R R AddMonoidHom.mul continuous_mul
          (fun g a b => (smul_mul' g a b).symm) y z) :=
  explicitCup_assoc011 G R R R R R R _ _ _ _ _ _ _ _ mul_assoc _ _ _ _ x y z

/-- **Associativity of the ring cup product in tridegree `(1,1,0)`.** -/
theorem explicitCup_assoc110_mul (x y : H1 G R) (z : H0 G R) :
    explicitCup20 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm)
        (explicitCup11 G R R R AddMonoidHom.mul continuous_mul
          (fun g a b => (smul_mul' g a b).symm) x y) z =
      explicitCup11 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm) x
        (explicitCup10 G R R R AddMonoidHom.mul continuous_mul
          (fun g a b => (smul_mul' g a b).symm) y z) :=
  explicitCup_assoc110 G R R R R R R _ _ _ _ _ _ _ _ mul_assoc _ _ _ _ x y z

/-- **Associativity of the ring cup product in tridegree `(1,0,1)`.** -/
theorem explicitCup_assoc101_mul (x : H1 G R) (y : H0 G R) (z : H1 G R) :
    explicitCup11 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm)
        (explicitCup10 G R R R AddMonoidHom.mul continuous_mul
          (fun g a b => (smul_mul' g a b).symm) x y) z =
      explicitCup11 G R R R AddMonoidHom.mul continuous_mul
        (fun g a b => (smul_mul' g a b).symm) x
        (explicitCup01 G R R R AddMonoidHom.mul continuous_mul
          (fun g a b => (smul_mul' g a b).symm) y z) :=
  explicitCup_assoc101 G R R R R R R _ _ _ _ _ _ _ _ mul_assoc _ _ _ _ x y z

end AssocRing

end TauCeti.ContCohomology
