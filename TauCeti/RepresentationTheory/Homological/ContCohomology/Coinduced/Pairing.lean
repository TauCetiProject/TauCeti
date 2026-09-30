/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete

/-!
# Pairings with a coinduced module

Let `U` be a subgroup of a topological group `G` and let
`μ : M →+ N →+ P` be a `G`-equivariant biadditive pairing of discrete `G`-modules. Pairing
an element of `M` with every value of a coinduced function gives a natural pairing

```text
M × Coind_U^G N → Coind_U^G P,
    (m, f) ↦ (g ↦ μ (g • m) (f g)).
```

The translate `g • m` is forced by equivariance. It makes evaluation at `1` recover `μ`, and
makes the coinduced pairing commute with the trace:

```text
ev (m ⋆ f) = μ m (ev f),      tr (m ⋆ f) = μ m (tr f).
```

These two identities are the coefficient-level input to the projection formula for
corestriction and cup products.

## Main definitions

* `TauCeti.DiscreteCoind.pairing`: the biadditive pairing with a coinduced module.

## Main results

* `TauCeti.DiscreteCoind.eval_pairing`: evaluation at `1` commutes with the pairing.
* `TauCeti.DiscreteCoind.trace_pairing`: the coinduced trace commutes with the pairing.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3, (3.8).
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §5, (1.5.3)(iv).
-/

public section

namespace TauCeti.DiscreteCoind

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G]
  (U : Subgroup G)
  {M N P : Type u}
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  [ContinuousSMul G M]
  [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N] [DistribMulAction G N]
  [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P] [DistribMulAction G P]
  (μ : M →+ N →+ P)
  (hμ : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n)

/-- Pairing an element of a discrete `G`-module with a coinduced function, pointwise after
translating the first argument:
`pairing μ m f g = μ (g • m) (f g)`. -/
def pairing : M →+ DiscreteCoind G U N →+ DiscreteCoind G U P where
  toFun m :=
    { toFun := fun f => mk G U P (fun g => μ (g • m) (f g))
        ((IsLocallyConstant.iff_continuous _).2
          ((continuous_of_discreteTopology :
              Continuous fun q : M × N => μ q.1 q.2).comp
            ((continuous_id.smul continuous_const).prodMk
              ((IsLocallyConstant.iff_continuous _).1 f.isLocallyConstant))))
        fun u g => by
          rw [f.apply_mul]
          simpa only [mul_smul, Subgroup.smul_def] using hμ (u : G) (g • m) (f g)
      map_zero' := ext fun g => by simp
      map_add' := fun f f' => ext fun g => by simp }
  map_zero' := AddMonoidHom.ext fun f => ext fun g => by simp
  map_add' := fun m m' => AddMonoidHom.ext fun f => ext fun g => by simp [smul_add]

omit [ContinuousMul G] in
@[simp]
theorem pairing_apply (m : M) (f : DiscreteCoind G U N) (g : G) :
    pairing (hμ := hμ) U μ m f g = μ (g • m) (f g) := (rfl)

/-- The pairing with a coinduced module is `G`-equivariant. -/
theorem pairing_smul (g : G) (m : M) (f : DiscreteCoind G U N) :
    pairing (hμ := hμ) U μ (g • m) (g • f) =
      g • pairing (hμ := hμ) U μ m f := by
  ext x
  simp only [pairing_apply, coe_smul, mul_smul]

omit [ContinuousMul G] in
/-- Evaluation at `1` commutes with the pairing with a coinduced module. -/
theorem eval_pairing (m : M) (f : DiscreteCoind G U N) :
    eval G U P (pairing (hμ := hμ) U μ m f) = μ m (eval G U N f) := by
  simp

variable [U.FiniteIndex]

/-- The coinduced trace commutes with the pairing:
`tr (g ↦ μ (g • m) (f g)) = μ m (tr f)`. This is the coefficient identity behind the
projection formula in cohomology. -/
theorem trace_pairing (m : M) (f : DiscreteCoind G U N) :
    trace G U P (pairing (hμ := hμ) U μ m f) = μ m (trace G U N f) := by
  simp only [trace_apply, pairing_apply, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← hμ x.out (x.out⁻¹ • m) (f x.out⁻¹), smul_inv_smul]

end TauCeti.DiscreteCoind
