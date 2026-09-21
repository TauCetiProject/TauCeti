/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product

/-!
# Naturality of the explicit low-degree cup products in compatible pairs

A compatible pair `(φ : H →ₜ* G, f : M →+ M')` in the sense of
`TauCeti/RepresentationTheory/Homological/ContCohomology/ExplicitFunctoriality.lean` pulls a cup
product back to a cup product as soon as the two pairings are intertwined by the three coefficient
maps, `f_P (μ m x) = μ' (f_M m) (f_N x)`:

```text
(φ, f_P)^* (x ⌣_μ y) = (φ, f_M)^* x ⌣_{μ'} (φ, f_N)^* y.
```

Each of the six shapes `(p, q)` with `p + q ≤ 2` gets one such theorem.

## Main statements

* `TauCeti.ContCohomology.explicitMap0_explicitCup00`, `explicitMap1_explicitCup01`,
  `explicitMap1_explicitCup10`, `explicitMap2_explicitCup02`, `explicitMap2_explicitCup20` and
  `explicitMap2_explicitCup11`: **naturality in compatible pairs**, one theorem per shape.
* `TauCeti.ContCohomology.explicitCoeff0_explicitCup00`, `explicitCoeff1_explicitCup01`,
  `explicitCoeff1_explicitCup10`, `explicitCoeff2_explicitCup02`, `explicitCoeff2_explicitCup20`
  and `explicitCoeff2_explicitCup11`: **naturality in the pairing**, the instance at the pair
  `(id, f)`, deduced from the general theorems through
  `TauCeti.ContCohomology.explicitCoeff1_eq_explicitMap1` and its siblings.

## Implementation notes

The other named instance, the pair `(S ↪ G, id)`, is compatibility with restriction; it is
deduced from these theorems in
`TauCeti/RepresentationTheory/Homological/ContCohomology/Cup/Restriction.lean`, where the
statements are `simp` lemmas.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.4.2): naturality
  of the cup product in the coefficients.
-/

public section

namespace TauCeti.ContCohomology

universe uG uH uM uN uP

section NaturalityZeroZero

variable (G : Type uG) [Group G]
  (M : Type uM) [AddCommGroup M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [DistribMulAction G N]
  (P : Type uP) [AddCommGroup P] [DistribMulAction G P]
  (μ : M →+ N →+ P)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
  (H : Type uH) [Group H]
  (M' : Type*) [AddCommGroup M'] [DistribMulAction H M']
  (N' : Type*) [AddCommGroup N'] [DistribMulAction H N']
  (P' : Type*) [AddCommGroup P'] [DistribMulAction H P']
  (μ' : M' →+ N' →+ P')
  (hequiv' : ∀ (h : H) (m : M') (x : N'), μ' (h • m) (h • x) = h • μ' m x)
  (φ : H →* G) (fM : M →+ M') (fN : N →+ N') (fP : P →+ P')
  (hfM : ∀ (h : H) (m : M), fM (φ h • m) = h • fM m)
  (hfN : ∀ (h : H) (x : N), fN (φ h • x) = h • fN x)
  (hfP : ∀ (h : H) (x : P), fP (φ h • x) = h • fP x)
  (hpair : ∀ (m : M) (x : N), fP (μ m x) = μ' (fM m) (fN x))

include hpair in
/-- **Naturality of the `(0,0)` cup product in compatible pairs.** In degree zero the cup product
*is* the pairing, so the statement is the intertwining hypothesis read on invariant elements. -/
theorem explicitMap0_explicitCup00 (m : H0 G M) (x : H0 G N) :
    explicitMap0 G P φ fP hfP (explicitCup00 G M N P μ hequiv m x) =
      explicitCup00 H M' N' P' μ' hequiv'
        (explicitMap0 G M φ fM hfM m) (explicitMap0 G N φ fN hfN x) :=
  Subtype.ext (by simp [hpair])

end NaturalityZeroZero

section NaturalityZeroOne

variable (G : Type uG) [Group G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
  (H : Type uH) [Group H] [TopologicalSpace H]
  (M' : Type*) [AddCommGroup M'] [TopologicalSpace M'] [DistribMulAction H M']
  (N' : Type*) [AddCommGroup N'] [TopologicalSpace N'] [IsTopologicalAddGroup N']
    [DistribMulAction H N'] [ContinuousSMul H N']
  (P' : Type*) [AddCommGroup P'] [TopologicalSpace P'] [IsTopologicalAddGroup P']
    [DistribMulAction H P'] [ContinuousSMul H P']
  (μ' : M' →+ N' →+ P') (hμ' : Continuous fun p : M' × N' => μ' p.1 p.2)
  (hequiv' : ∀ (h : H) (m : M') (x : N'), μ' (h • m) (h • x) = h • μ' m x)
  (φ : H →ₜ* G) (fM : M →+ M') (fN : N →+ N') (fP : P →+ P')
  (hcN : Continuous fN) (hcP : Continuous fP)
  (hfM : ∀ (h : H) (m : M), fM (φ h • m) = h • fM m)
  (hfN : ∀ (h : H) (x : N), fN (φ h • x) = h • fN x)
  (hfP : ∀ (h : H) (x : P), fP (φ h • x) = h • fP x)
  (hpair : ∀ (m : M) (x : N), fP (μ m x) = μ' (fM m) (fN x))

include hpair in
/-- **Naturality of the `(0,1)` cup product in compatible pairs.** -/
theorem explicitMap1_explicitCup01 (m : H0 G M) (b : H1 G N) :
    explicitMap1 G P H P' φ fP hcP hfP (explicitCup01 G M N P μ hμ hequiv m b) =
      explicitCup01 H M' N' P' μ' hμ' hequiv'
        (explicitMap0 G M (φ : H →* G) fM hfM m)
        (explicitMap1 G N H N' φ fN hcN hfN b) := by
  -- `coe_explicitMap0` is supplied as a local equation rather than left to `simp`: the group map
  -- of the degree-zero pullback is the `MonoidHom` coercion of `φ`, which `simp` will not match
  -- against the `ContinuousMonoidHom` application appearing in `hfM`.
  have hcoe : ((explicitMap0 G M (φ : H →* G) fM hfM m : M')) = fM (m : M) :=
    coe_explicitMap0 G M (φ : H →* G) fM hfM m
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    simp only [explicitCup01_mk, explicitMap1_mk]
    exact congrArg (fun z : Z1 H P' => (z : H1 H P'))
      (Subtype.ext (funext fun h => by simp [cocyclesMap1_coe, hcoe, hpair]))

end NaturalityZeroOne

section NaturalityOneZero

variable (G : Type uG) [Group G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DistribMulAction G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
  (H : Type uH) [Group H] [TopologicalSpace H]
  (M' : Type*) [AddCommGroup M'] [TopologicalSpace M'] [IsTopologicalAddGroup M']
    [DistribMulAction H M'] [ContinuousSMul H M']
  (N' : Type*) [AddCommGroup N'] [TopologicalSpace N'] [DistribMulAction H N']
  (P' : Type*) [AddCommGroup P'] [TopologicalSpace P'] [IsTopologicalAddGroup P']
    [DistribMulAction H P'] [ContinuousSMul H P']
  (μ' : M' →+ N' →+ P') (hμ' : Continuous fun p : M' × N' => μ' p.1 p.2)
  (hequiv' : ∀ (h : H) (m : M') (x : N'), μ' (h • m) (h • x) = h • μ' m x)
  (φ : H →ₜ* G) (fM : M →+ M') (fN : N →+ N') (fP : P →+ P')
  (hcM : Continuous fM) (hcP : Continuous fP)
  (hfM : ∀ (h : H) (m : M), fM (φ h • m) = h • fM m)
  (hfN : ∀ (h : H) (x : N), fN (φ h • x) = h • fN x)
  (hfP : ∀ (h : H) (x : P), fP (φ h • x) = h • fP x)
  (hpair : ∀ (m : M) (x : N), fP (μ m x) = μ' (fM m) (fN x))

include hpair in
/-- **Naturality of the `(1,0)` cup product in compatible pairs.** -/
theorem explicitMap1_explicitCup10 (a : H1 G M) (n : H0 G N) :
    explicitMap1 G P H P' φ fP hcP hfP (explicitCup10 G M N P μ hμ hequiv a n) =
      explicitCup10 H M' N' P' μ' hμ' hequiv'
        (explicitMap1 G M H M' φ fM hcM hfM a)
        (explicitMap0 G N (φ : H →* G) fN hfN n) := by
  -- As in the `(0,1)` shape, `coe_explicitMap0` is supplied explicitly because `simp` cannot
  -- match the `MonoidHom` coercion of `φ` against the `ContinuousMonoidHom` application in `hfN`.
  have hcoe : ((explicitMap0 G N (φ : H →* G) fN hfN n : N')) = fN (n : N) :=
    coe_explicitMap0 G N (φ : H →* G) fN hfN n
  induction a using QuotientAddGroup.induction_on with
  | _ c =>
    simp only [explicitCup10_mk, explicitMap1_mk]
    exact congrArg (fun z : Z1 H P' => (z : H1 H P'))
      (Subtype.ext (funext fun h => by simp [cocyclesMap1_coe, hcoe, hpair, hfN]))

end NaturalityOneZero

section NaturalityZeroTwo

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
  (H : Type uH) [Group H] [TopologicalSpace H] [ContinuousMul H]
  (M' : Type*) [AddCommGroup M'] [TopologicalSpace M'] [DistribMulAction H M']
  (N' : Type*) [AddCommGroup N'] [TopologicalSpace N'] [IsTopologicalAddGroup N']
    [DistribMulAction H N'] [ContinuousSMul H N']
  (P' : Type*) [AddCommGroup P'] [TopologicalSpace P'] [IsTopologicalAddGroup P']
    [DistribMulAction H P'] [ContinuousSMul H P']
  (μ' : M' →+ N' →+ P') (hμ' : Continuous fun p : M' × N' => μ' p.1 p.2)
  (hequiv' : ∀ (h : H) (m : M') (x : N'), μ' (h • m) (h • x) = h • μ' m x)
  (φ : H →ₜ* G) (fM : M →+ M') (fN : N →+ N') (fP : P →+ P')
  (hcN : Continuous fN) (hcP : Continuous fP)
  (hfM : ∀ (h : H) (m : M), fM (φ h • m) = h • fM m)
  (hfN : ∀ (h : H) (x : N), fN (φ h • x) = h • fN x)
  (hfP : ∀ (h : H) (x : P), fP (φ h • x) = h • fP x)
  (hpair : ∀ (m : M) (x : N), fP (μ m x) = μ' (fM m) (fN x))

include hpair in
/-- **Naturality of the `(0,2)` cup product in compatible pairs.** -/
theorem explicitMap2_explicitCup02 (m : H0 G M) (b : H2 G N) :
    explicitMap2 G P H P' φ fP hcP hfP (explicitCup02 G M N P μ hμ hequiv m b) =
      explicitCup02 H M' N' P' μ' hμ' hequiv'
        (explicitMap0 G M (φ : H →* G) fM hfM m)
        (explicitMap2 G N H N' φ fN hcN hfN b) := by
  -- `coe_explicitMap0` is supplied as a local equation rather than left to `simp`: the group map
  -- of the degree-zero pullback is the `MonoidHom` coercion of `φ`, which `simp` will not match
  -- against the `ContinuousMonoidHom` application appearing in `hfM`.
  have hcoe : ((explicitMap0 G M (φ : H →* G) fM hfM m : M')) = fM (m : M) :=
    coe_explicitMap0 G M (φ : H →* G) fM hfM m
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    simp only [explicitCup02_mk, explicitMap2_mk]
    exact congrArg (fun z : Z2 H P' => (z : H2 H P'))
      (Subtype.ext (funext fun q => by
        obtain ⟨h, k⟩ := q
        simp [cocyclesMap2_coe, hcoe, hpair]))

end NaturalityZeroTwo

section NaturalityTwoZero

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DistribMulAction G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
  (H : Type uH) [Group H] [TopologicalSpace H] [ContinuousMul H]
  (M' : Type*) [AddCommGroup M'] [TopologicalSpace M'] [IsTopologicalAddGroup M']
    [DistribMulAction H M'] [ContinuousSMul H M']
  (N' : Type*) [AddCommGroup N'] [TopologicalSpace N'] [DistribMulAction H N']
  (P' : Type*) [AddCommGroup P'] [TopologicalSpace P'] [IsTopologicalAddGroup P']
    [DistribMulAction H P'] [ContinuousSMul H P']
  (μ' : M' →+ N' →+ P') (hμ' : Continuous fun p : M' × N' => μ' p.1 p.2)
  (hequiv' : ∀ (h : H) (m : M') (x : N'), μ' (h • m) (h • x) = h • μ' m x)
  (φ : H →ₜ* G) (fM : M →+ M') (fN : N →+ N') (fP : P →+ P')
  (hcM : Continuous fM) (hcP : Continuous fP)
  (hfM : ∀ (h : H) (m : M), fM (φ h • m) = h • fM m)
  (hfN : ∀ (h : H) (x : N), fN (φ h • x) = h • fN x)
  (hfP : ∀ (h : H) (x : P), fP (φ h • x) = h • fP x)
  (hpair : ∀ (m : M) (x : N), fP (μ m x) = μ' (fM m) (fN x))

include hpair in
/-- **Naturality of the `(2,0)` cup product in compatible pairs.** -/
theorem explicitMap2_explicitCup20 (a : H2 G M) (n : H0 G N) :
    explicitMap2 G P H P' φ fP hcP hfP (explicitCup20 G M N P μ hμ hequiv a n) =
      explicitCup20 H M' N' P' μ' hμ' hequiv'
        (explicitMap2 G M H M' φ fM hcM hfM a)
        (explicitMap0 G N (φ : H →* G) fN hfN n) := by
  -- As in the `(0,1)` shape, `coe_explicitMap0` is supplied explicitly because `simp` cannot
  -- match the `MonoidHom` coercion of `φ` against the `ContinuousMonoidHom` application in `hfN`.
  have hcoe : ((explicitMap0 G N (φ : H →* G) fN hfN n : N')) = fN (n : N) :=
    coe_explicitMap0 G N (φ : H →* G) fN hfN n
  have hmul : ∀ (h k : H) (x : N), fN ((φ h * φ k) • x) = (h * k) • fN x := fun h k x => by
    rw [← map_mul]
    exact hfN (h * k) x
  induction a using QuotientAddGroup.induction_on with
  | _ c =>
    simp only [explicitCup20_mk, explicitMap2_mk]
    exact congrArg (fun z : Z2 H P' => (z : H2 H P'))
      (Subtype.ext (funext fun q => by
        obtain ⟨h, k⟩ := q
        simp [cocyclesMap2_coe, hcoe, hpair, hmul]))

end NaturalityTwoZero

section NaturalityOneOne

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
  (H : Type uH) [Group H] [TopologicalSpace H] [ContinuousMul H]
  (M' : Type*) [AddCommGroup M'] [TopologicalSpace M'] [IsTopologicalAddGroup M']
    [DistribMulAction H M'] [ContinuousSMul H M']
  (N' : Type*) [AddCommGroup N'] [TopologicalSpace N'] [IsTopologicalAddGroup N']
    [DistribMulAction H N'] [ContinuousSMul H N']
  (P' : Type*) [AddCommGroup P'] [TopologicalSpace P'] [IsTopologicalAddGroup P']
    [DistribMulAction H P'] [ContinuousSMul H P']
  (μ' : M' →+ N' →+ P') (hμ' : Continuous fun p : M' × N' => μ' p.1 p.2)
  (hequiv' : ∀ (h : H) (m : M') (x : N'), μ' (h • m) (h • x) = h • μ' m x)
  (φ : H →ₜ* G) (fM : M →+ M') (fN : N →+ N') (fP : P →+ P')
  (hcM : Continuous fM) (hcN : Continuous fN) (hcP : Continuous fP)
  (hfM : ∀ (h : H) (m : M), fM (φ h • m) = h • fM m)
  (hfN : ∀ (h : H) (x : N), fN (φ h • x) = h • fN x)
  (hfP : ∀ (h : H) (x : P), fP (φ h • x) = h • fP x)
  (hpair : ∀ (m : M) (x : N), fP (μ m x) = μ' (fM m) (fN x))

include hpair in
/-- **Naturality of the `(1,1)` cup product in compatible pairs.** This is the only shape in
which neither factor is invariant, so the cup is not a coefficient map. -/
theorem explicitMap2_explicitCup11 (a : H1 G M) (b : H1 G N) :
    explicitMap2 G P H P' φ fP hcP hfP (explicitCup11 G M N P μ hμ hequiv a b) =
      explicitCup11 H M' N' P' μ' hμ' hequiv'
        (explicitMap1 G M H M' φ fM hcM hfM a)
        (explicitMap1 G N H N' φ fN hcN hfN b) := by
  induction a using QuotientAddGroup.induction_on with
  | _ x =>
    induction b using QuotientAddGroup.induction_on with
    | _ y =>
      simp only [explicitCup11_mk, explicitMap1_mk, explicitMap2_mk]
      exact congrArg (fun z : Z2 H P' => (z : H2 H P'))
        (Subtype.ext (funext fun q => by
          obtain ⟨h, k⟩ := q
          simp [cocyclesMap1_coe, cocyclesMap2_coe, hpair, hfN]))

end NaturalityOneOne

section NaturalityCoefficients

/-! The coefficient-map instances of the six naturality theorems, NSW (1.4.2): the compatible pair
is `(id, f)`, the group does not move, and the intertwining hypothesis is naturality of the cup
product in the pairing. -/

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (M' : Type*) [AddCommGroup M'] [TopologicalSpace M'] [IsTopologicalAddGroup M']
    [DistribMulAction G M'] [ContinuousSMul G M']
  (N' : Type*) [AddCommGroup N'] [TopologicalSpace N'] [IsTopologicalAddGroup N']
    [DistribMulAction G N'] [ContinuousSMul G N']
  (P' : Type*) [AddCommGroup P'] [TopologicalSpace P'] [IsTopologicalAddGroup P']
    [DistribMulAction G P'] [ContinuousSMul G P']
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
  (μ' : M' →+ N' →+ P') (hμ' : Continuous fun p : M' × N' => μ' p.1 p.2)
  (hequiv' : ∀ (g : G) (m : M') (x : N'), μ' (g • m) (g • x) = g • μ' m x)
  (fM : M →+[G] M') (fN : N →+[G] N') (fP : P →+[G] P')
  (hcM : Continuous fM) (hcN : Continuous fN) (hcP : Continuous fP)
  (hpair : ∀ (m : M) (x : N), fP (μ m x) = μ' (fM m) (fN x))

include hpair

omit [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousSMul G M] [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousSMul G N]
  [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousSMul G P] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousSMul G M'] [TopologicalSpace N']
  [IsTopologicalAddGroup N'] [ContinuousSMul G N'] [TopologicalSpace P']
  [IsTopologicalAddGroup P'] [ContinuousSMul G P'] in
/-- **Naturality of the `(0,0)` cup product in the coefficient maps** (NSW (1.4.2)). -/
theorem explicitCoeff0_explicitCup00 (m : H0 G M) (x : H0 G N) :
    explicitCoeff0 G P fP (explicitCup00 G M N P μ hequiv m x) =
      explicitCup00 G M' N' P' μ' hequiv'
        (explicitCoeff0 G M fM m) (explicitCoeff0 G N fN x) :=
  Subtype.ext (by simp [hpair])

omit [ContinuousMul G] [IsTopologicalAddGroup M] [ContinuousSMul G M]
  [IsTopologicalAddGroup M'] [ContinuousSMul G M'] in
/-- **Naturality of the `(0,1)` cup product in the coefficient maps** (NSW (1.4.2)). -/
theorem explicitCoeff1_explicitCup01 (m : H0 G M) (b : H1 G N) :
    explicitCoeff1 G P fP hcP (explicitCup01 G M N P μ hμ hequiv m b) =
      explicitCup01 G M' N' P' μ' hμ' hequiv'
        (explicitCoeff0 G M fM m) (explicitCoeff1 G N fN hcN b) := by
  simp only [explicitCoeff0_eq_explicitMap0, explicitCoeff1_eq_explicitMap1]
  exact explicitMap1_explicitCup01 G M N P μ hμ hequiv G M' N' P' μ' hμ' hequiv'
    (ContinuousMonoidHom.id G) fM fN fP hcN hcP (fun g m => fM.map_smul g m)
    (fun g x => fN.map_smul g x) (fun g x => fP.map_smul g x) hpair m b

omit [ContinuousMul G] [IsTopologicalAddGroup N] [ContinuousSMul G N]
  [IsTopologicalAddGroup N'] [ContinuousSMul G N'] in
/-- **Naturality of the `(1,0)` cup product in the coefficient maps** (NSW (1.4.2)). -/
theorem explicitCoeff1_explicitCup10 (a : H1 G M) (n : H0 G N) :
    explicitCoeff1 G P fP hcP (explicitCup10 G M N P μ hμ hequiv a n) =
      explicitCup10 G M' N' P' μ' hμ' hequiv'
        (explicitCoeff1 G M fM hcM a) (explicitCoeff0 G N fN n) := by
  simp only [explicitCoeff0_eq_explicitMap0, explicitCoeff1_eq_explicitMap1]
  exact explicitMap1_explicitCup10 G M N P μ hμ hequiv G M' N' P' μ' hμ' hequiv'
    (ContinuousMonoidHom.id G) fM fN fP hcM hcP (fun g m => fM.map_smul g m)
    (fun g x => fN.map_smul g x) (fun g x => fP.map_smul g x) hpair a n

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] [IsTopologicalAddGroup M']
  [ContinuousSMul G M'] in
/-- **Naturality of the `(0,2)` cup product in the coefficient maps** (NSW (1.4.2)). -/
theorem explicitCoeff2_explicitCup02 (m : H0 G M) (b : H2 G N) :
    explicitCoeff2 G P fP hcP (explicitCup02 G M N P μ hμ hequiv m b) =
      explicitCup02 G M' N' P' μ' hμ' hequiv'
        (explicitCoeff0 G M fM m) (explicitCoeff2 G N fN hcN b) := by
  simp only [explicitCoeff0_eq_explicitMap0, explicitCoeff2_eq_explicitMap2]
  exact explicitMap2_explicitCup02 G M N P μ hμ hequiv G M' N' P' μ' hμ' hequiv'
    (ContinuousMonoidHom.id G) fM fN fP hcN hcP (fun g m => fM.map_smul g m)
    (fun g x => fN.map_smul g x) (fun g x => fP.map_smul g x) hpair m b

omit [IsTopologicalAddGroup N] [ContinuousSMul G N] [IsTopologicalAddGroup N']
  [ContinuousSMul G N'] in
/-- **Naturality of the `(2,0)` cup product in the coefficient maps** (NSW (1.4.2)). -/
theorem explicitCoeff2_explicitCup20 (a : H2 G M) (n : H0 G N) :
    explicitCoeff2 G P fP hcP (explicitCup20 G M N P μ hμ hequiv a n) =
      explicitCup20 G M' N' P' μ' hμ' hequiv'
        (explicitCoeff2 G M fM hcM a) (explicitCoeff0 G N fN n) := by
  simp only [explicitCoeff0_eq_explicitMap0, explicitCoeff2_eq_explicitMap2]
  exact explicitMap2_explicitCup20 G M N P μ hμ hequiv G M' N' P' μ' hμ' hequiv'
    (ContinuousMonoidHom.id G) fM fN fP hcM hcP (fun g m => fM.map_smul g m)
    (fun g x => fN.map_smul g x) (fun g x => fP.map_smul g x) hpair a n

/-- **Naturality of the `(1,1)` cup product in the coefficient maps** (NSW (1.4.2)). -/
theorem explicitCoeff2_explicitCup11 (a : H1 G M) (b : H1 G N) :
    explicitCoeff2 G P fP hcP (explicitCup11 G M N P μ hμ hequiv a b) =
      explicitCup11 G M' N' P' μ' hμ' hequiv'
        (explicitCoeff1 G M fM hcM a) (explicitCoeff1 G N fN hcN b) := by
  simp only [explicitCoeff1_eq_explicitMap1, explicitCoeff2_eq_explicitMap2]
  exact explicitMap2_explicitCup11 G M N P μ hμ hequiv G M' N' P' μ' hμ' hequiv'
    (ContinuousMonoidHom.id G) fM fN fP hcM hcN hcP (fun g m => fM.map_smul g m)
    (fun g x => fN.map_smul g x) (fun g x => fP.map_smul g x) hpair a b

end NaturalityCoefficients

end TauCeti.ContCohomology
