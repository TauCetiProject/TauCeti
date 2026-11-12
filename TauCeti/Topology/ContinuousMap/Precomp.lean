/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Precomposition with a proper surjection

If `q : A → B` is a proper continuous surjection, then precomposition with `q` embeds the space
`C(B, X)` of continuous maps, with the compact-open topology, in `C(A, X)`. The reason is that the
preimage of a compact subset of `B` under `q` is compact, so every subbasic compact-open condition
on `B` is the pullback of a subbasic compact-open condition on `A`.

The main example is a continuous surjection from a compact space to a Hausdorff space, which is
proper by `Continuous.isProperMap`. Combined with the fact that a proper surjection is a quotient
map, this identifies mapping spaces out of a quotient such as `I^n / ∂I^n ≅ S^n` (for `n ≥ 1`)
with subspaces of mapping spaces out of the cube.

## Main declarations

* `ContinuousMap.isInducing_precomp_of_surjective`: precomposition with a proper continuous
  surjection `q : A → B` is inducing, on the compact-open topologies.
* `ContinuousMap.isEmbedding_precomp_of_surjective`: the same, as an embedding.
* `ContinuousMap.homeomorphFactorsThrough`, with `homeomorphFactorsThrough_apply` and
  `homeomorphFactorsThrough_symm_apply_comp`: for such a `q`, `C(B, X)` is homeomorphic to the
  subspace of maps `A → X` that are constant on the fibres of `q`.
-/

public section

open Set Topology

namespace ContinuousMap

variable {A B X : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]

/-- Precomposition with a proper continuous surjection `q` is inducing for the compact-open
topologies. -/
theorem isInducing_precomp_of_surjective (q : C(A, B)) (hq : IsProperMap q)
    (hsurj : Function.Surjective q) :
    IsInducing (fun f : C(B, X) => f.comp q) := by
  refine ⟨le_antisymm (continuous_iff_le_induced.mp (continuous_precomp q)) ?_⟩
  refine le_generateFrom ?_
  rintro _ ⟨K, hK, U, hU, rfl⟩
  have hpre : IsOpen {g : C(A, X) | MapsTo g (q ⁻¹' K) U} :=
    isOpen_setOfPred_mapsTo (hq.isCompact_preimage hK) hU
  refine ⟨_, hpre, ?_⟩
  ext f
  constructor
  · intro h b hb
    obtain ⟨a, rfl⟩ := hsurj b
    exact h hb
  · intro h a ha
    exact h ha

/-- Precomposition with a proper continuous surjection `q` is an embedding. -/
theorem isEmbedding_precomp_of_surjective (q : C(A, B)) (hq : IsProperMap q)
    (hsurj : Function.Surjective q) :
    IsEmbedding (fun f : C(B, X) => f.comp q) :=
  ⟨isInducing_precomp_of_surjective q hq hsurj, fun _ _ h => (cancel_right hsurj).1 h⟩

/-- Maps out of the quotient `B` of `A` by a proper continuous surjection `q` are the maps out of
`A` that are constant on the fibres of `q`: precomposition with `q` is a homeomorphism from
`C(B, X)` onto the subspace of such maps. -/
noncomputable def homeomorphFactorsThrough (q : C(A, B)) (hq : IsProperMap q)
    (hsurj : Function.Surjective q) :
    C(B, X) ≃ₜ {g : C(A, X) // Function.FactorsThrough g q} :=
  have hqm : IsQuotientMap q := hq.isClosedMap.isQuotientMap q.continuous hsurj
  have hcont : Continuous (hqm.liftEquiv (Z := X)).symm :=
    continuous_induced_rng.2 (continuous_precomp q)
  (hqm.liftEquiv (Z := X)).symm.toHomeomorphOfIsInducing
    (IsInducing.of_comp hcont continuous_subtype_val (isInducing_precomp_of_surjective q hq hsurj))

/-- The map out of `A` attached to `f : C(B, X)` by `homeomorphFactorsThrough` is `f ∘ q`. -/
@[simp]
theorem homeomorphFactorsThrough_apply (q : C(A, B)) (hq : IsProperMap q)
    (hsurj : Function.Surjective q) (f : C(B, X)) :
    (homeomorphFactorsThrough q hq hsurj f : C(A, X)) = f.comp q := by
  rw [homeomorphFactorsThrough]
  -- the underlying function of the equivalence is `lift`'s inverse, i.e. precomposition with `q`
  rfl

/-- The inverse of `homeomorphFactorsThrough` evaluates, at the image under `q` of a point, to the
value at that point of the map out of the source. -/
@[simp]
theorem homeomorphFactorsThrough_symm_apply_comp (q : C(A, B)) (hq : IsProperMap q)
    (hsurj : Function.Surjective q) (g : {g : C(A, X) // Function.FactorsThrough g q}) (a : A) :
    (homeomorphFactorsThrough q hq hsurj).symm g (q a) = g.1 a := by
  have h := congrArg (fun f : {g : C(A, X) // Function.FactorsThrough g q} => f.1 a)
    ((homeomorphFactorsThrough q hq hsurj).apply_symm_apply g)
  rwa [homeomorphFactorsThrough_apply] at h

end ContinuousMap
