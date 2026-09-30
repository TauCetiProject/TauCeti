/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete

/-!
# Pairings with a coinduced module

Let `U` be an open subgroup of a topological group `G` and let
`μ : M →+ N →+ P` be a `G`-equivariant biadditive pairing of `G`-modules, where `P` is discrete
with continuous `U`-action. Pairing an element of `M` with every value of a coinduced function
gives a natural pairing

```text
M × Coind_U^G N → Coind_U^G P,
    (m, f) ↦ (g ↦ μ (g • m) (f g)).
```

The translate `g • m` is forced by equivariance. The resulting function is `U`-equivariant, hence
locally constant because `U` is open and the stabilizers of `P` are open; no topology on `M` or
`N` is needed, so the construction applies to an arbitrary topological representation `M`.
Evaluation at `1` recovers `μ`, and the coinduced pairing commutes with the trace:

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
  (U : Subgroup G) (hU : IsOpen (U : Set G))
  {M N P : Type u}
  [AddCommGroup M] [DistribMulAction G M]
  [AddCommGroup N] [DistribMulAction G N]
  [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P] [DistribMulAction G P]
  [ContinuousSMul U P]
  (μ : M →+ N →+ P)
  (hμ : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n)

include hU in
/-- A `U`-equivariant function to a discrete module with open stabilizers is locally constant
when `U` is open: it is constant on the open neighbourhood `Stab(k g) * g` of `g`. -/
private theorem isLocallyConstant_of_apply_mul (k : G → P)
    (hk : ∀ (u : U) (g : G), k (u * g) = u • k g) : IsLocallyConstant k := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  let S : Set U := MulAction.stabilizer U (k g)
  have hS : IsOpen S := stabilizer_isOpen U (k g)
  have hopen : IsOpen ((fun u : U ↦ (u : G) * g) '' S) :=
    ((isOpenMap_mul_right g).comp hU.isOpenMap_subtype_val) S hS
  have hg : g ∈ (fun u : U ↦ (u : G) * g) '' S := ⟨1, by simp [S], by simp⟩
  filter_upwards [hopen.mem_nhds hg] with x hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [hk]
  exact hu

omit [ContinuousMul G] [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul U P] in
include hμ in
/-- The `U`-equivariance of `g ↦ μ (g • m) (f g)`, the defining law of a coinduced function. -/
private theorem pairing_apply_mul (m : M) (f : DiscreteCoind G U N) (u : U) (g : G) :
    μ (((u : G) * g) • m) (f ((u : G) * g)) = u • μ (g • m) (f g) := by
  rw [f.apply_mul]
  simpa only [mul_smul, Subgroup.smul_def] using hμ (u : G) (g • m) (f g)

/-- Pairing an element of a `G`-module with a coinduced function, pointwise after
translating the first argument:
`pairing μ m f g = μ (g • m) (f g)`. -/
def pairing : M →+ DiscreteCoind G U N →+ DiscreteCoind G U P where
  toFun m :=
    { toFun := fun f => mk G U P (fun g => μ (g • m) (f g))
        (isLocallyConstant_of_apply_mul U hU _ (pairing_apply_mul U μ hμ m f))
        (pairing_apply_mul U μ hμ m f)
      map_zero' := ext fun g => by simp
      map_add' := fun f f' => ext fun g => by simp }
  map_zero' := AddMonoidHom.ext fun f => ext fun g => by simp
  map_add' := fun m m' => AddMonoidHom.ext fun f => ext fun g => by simp [smul_add]

@[simp]
theorem pairing_apply (m : M) (f : DiscreteCoind G U N) (g : G) :
    pairing U hU μ hμ m f g = μ (g • m) (f g) := (rfl)

/-- The pairing with a coinduced module is `G`-equivariant. -/
theorem pairing_smul (g : G) (m : M) (f : DiscreteCoind G U N) :
    pairing U hU μ hμ (g • m) (g • f) =
      g • pairing U hU μ hμ m f := by
  ext x
  simp only [pairing_apply, coe_smul, mul_smul]

/-- Evaluation at `1` commutes with the pairing with a coinduced module. -/
theorem eval_pairing (m : M) (f : DiscreteCoind G U N) :
    eval G U P (pairing U hU μ hμ m f) = μ m (eval G U N f) := by
  simp

variable [U.FiniteIndex]

/-- The coinduced trace commutes with the pairing:
`tr (g ↦ μ (g • m) (f g)) = μ m (tr f)`. This is the coefficient identity behind the
projection formula in cohomology. -/
theorem trace_pairing (m : M) (f : DiscreteCoind G U N) :
    trace G U P (pairing U hU μ hμ m f) = μ m (trace G U N f) := by
  simp only [trace_apply, pairing_apply, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← hμ x.out (x.out⁻¹ • m) (f x.out⁻¹), smul_inv_smul]

end TauCeti.DiscreteCoind
