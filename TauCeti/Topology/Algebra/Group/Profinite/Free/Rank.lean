/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Rank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Topology.Instances.ZMod
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basis
import TauCeti.Topology.Algebra.Group.Profinite.ProP.ContinuousDual

/-!
# The generator rank of a free pro-`p` group on a finite type

The canonical generators of `freeProP p X` generate it topologically
(`freeProP.topologicalClosure_closure_range_of_eq_top`), so for finite `X` the free pro-`p` group
is topologically finitely generated (`isTopologicallyFinitelyGenerated_freeProP`). In the Frattini
quotient `freeProP p X ⧸ proPFrattini p (freeProP p X)`, an `𝔽_p`-vector space, the classes of
the generators are linearly independent: any assignment of exponents modulo `p` to the generators
is realised by a continuous character of the free pro-`p` group, through its universal property.
For finite `X` the classes also span, by Burnside's basis theorem, so they form a basis indexed by
`X`. The Frattini quotient is therefore `𝔽_p^X`, and the topological generator rank of
`freeProP p X` is the cardinality of `X`, in natural-number and in cardinal form.

Finiteness of `X` is essential for the rank statement. For infinite `X` the classes of the
generators are still linearly independent, but they span only a dense subspace of the Frattini
quotient, whose dimension is that of the space of all maps `X → 𝔽_p` rather than `#X`
(Ribes–Zalesskii, Section 3.3); the free objects of infinite rank are indexed by a profinite space
rather than by a discrete type.

## Main definitions

* `TauCeti.freeProP.frattiniQuotientBasis`: for finite `X`, the basis of the Frattini quotient of
  `freeProP p X` formed by the classes of the generators.

## Main results

* `TauCeti.freeProP.linearIndependent_frattiniQuotient_of`: for every `X`, the classes of the
  generators in the Frattini quotient are linearly independent over `𝔽_p`.
* `TauCeti.freeProP.finrank_quotient_proPFrattini`: for finite `X`, the Frattini quotient has
  `𝔽_p`-dimension `Nat.card X`.
* `TauCeti.topologicalGeneratorRankNat_freeProP`, `TauCeti.topologicalGeneratorRank_freeProP`:
  for finite `X`, the free pro-`p` group on `X` has topological generator rank `Nat.card X`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.8 and 3.3.
-/

public section

namespace TauCeti

open scoped Cardinal

universe u

variable (p : ℕ) {X : Type u}

namespace freeProP

variable [Fact p.Prime] (X)

/-- The continuous character of the free pro-`p` group on `X` with values in `𝔽_p^X` that reads
off the exponent of each generator modulo `p`: it sends the generator at `x` to the indicator
function of `x`. -/
private noncomputable def toPiZMod [DecidableEq X] :
    freeProP p X →ₜ* Multiplicative (X → ZMod p) :=
  lift (ZModModule.isPGroup_multiplicative (n := p) (G := X → ZMod p)).isProP fun x ↦
    Multiplicative.ofAdd (Pi.single x 1)

/-- The exponent-reading character kills the Frattini subgroup, because each of its coordinates
is a continuous character into a group of order `p`. -/
private theorem proPFrattini_le_ker_toPiZMod [DecidableEq X] :
    proPFrattini p (freeProP p X) ≤ (toPiZMod p X).ker := by
  intro g hg
  refine MonoidHom.mem_ker.mpr (Multiplicative.toAdd.injective (funext fun x₀ ↦ ?_))
  let ev : Multiplicative (X → ZMod p) →ₜ* Multiplicative (ZMod p) :=
    { toMonoidHom := (Pi.evalAddMonoidHom (fun _ : X ↦ ZMod p) x₀).toMultiplicative
      continuous_toFun := continuous_ofAdd.comp ((continuous_apply x₀).comp continuous_toAdd) }
  have hev (y : Multiplicative (X → ZMod p)) : ev y = Multiplicative.ofAdd (y.toAdd x₀) := rfl
  have h := MonoidHom.mem_ker.mp
    (proPFrattini_le_ker (H := Multiplicative (ZMod p)) (by simp) (ev.comp (toPiZMod p X)) hg)
  simpa [hev] using h

/-- The `𝔽_p`-linear map from the Frattini quotient of the free pro-`p` group on `X` to `𝔽_p^X`
induced by the exponent-reading character. -/
private noncomputable def frattiniQuotientToPi [DecidableEq X] :
    Additive (freeProP p X ⧸ proPFrattini p (freeProP p X)) →ₗ[ZMod p] (X → ZMod p) :=
  ((QuotientGroup.lift (proPFrattini p (freeProP p X)) (toPiZMod p X).toMonoidHom
    (proPFrattini_le_ker_toPiZMod p X)).toAdditiveLeft).toZModLinearMap p

private theorem frattiniQuotientToPi_of [DecidableEq X] (x : X) :
    frattiniQuotientToPi p X
      (Additive.ofMul ((of x : freeProP p X) : freeProP p X ⧸ proPFrattini p (freeProP p X))) =
        Pi.single x 1 := by
  simp [frattiniQuotientToPi, toPiZMod]

/-- **The classes of the generators in the Frattini quotient are linearly independent** over
`𝔽_p`, for a generating type `X` of any cardinality. -/
theorem linearIndependent_frattiniQuotient_of :
    LinearIndependent (ZMod p) fun x : X ↦
      Additive.ofMul (QuotientGroup.mk' (proPFrattini p (freeProP p X)) (of x)) := by
  classical
  refine LinearIndependent.of_comp (frattiniQuotientToPi p X) ?_
  simpa [Function.comp_def, frattiniQuotientToPi_of] using
    Pi.linearIndependent_single_one X (ZMod p)

variable [Finite X]

/-- **The Frattini quotient of a free pro-`p` group of finite rank is `𝔽_p^X`.** For finite `X`
the classes of the generators form a basis of the Frattini quotient of `freeProP p X`, indexed
by `X`. -/
noncomputable def frattiniQuotientBasis :
    Module.Basis X (ZMod p) (Additive (freeProP p X ⧸ proPFrattini p (freeProP p X))) :=
  Module.Basis.mk (linearIndependent_frattiniQuotient_of p X) <| by
    have := (isTopologicallyFinitelyGenerated_freeProP p X).finite_quotient_proPFrattini p
    have hspan := (topologicallyGenerates_iff_frattiniQuotient_span_eq_top (isProP_freeProP p X)
      (Set.range (of : X → freeProP p X))).mp (topologicalClosure_closure_range_of_eq_top p X)
    rw [← Set.range_comp] at hspan
    exact hspan.ge

/-- The basis vector of the Frattini quotient at `x` is the class of the generator at `x`. -/
@[simp]
theorem frattiniQuotientBasis_apply (x : X) :
    frattiniQuotientBasis p X x =
      Additive.ofMul (QuotientGroup.mk' (proPFrattini p (freeProP p X)) (of x)) :=
  Module.Basis.mk_apply _ _ x

/-- The Frattini quotient of the free pro-`p` group on a finite type `X` has dimension
`Nat.card X` over `𝔽_p`. -/
@[simp]
theorem finrank_quotient_proPFrattini :
    Module.finrank (ZMod p) (Additive (freeProP p X ⧸ proPFrattini p (freeProP p X))) =
      Nat.card X :=
  Module.finrank_eq_nat_card_basis (frattiniQuotientBasis p X)

end freeProP

variable [Fact p.Prime] [Finite X]

/-- **The free pro-`p` group on a finite type `X` has topological generator rank `Nat.card X`**,
in natural-number form. -/
@[simp]
theorem topologicalGeneratorRankNat_freeProP (h : IsTopologicallyFinitelyGenerated (freeProP p X)) :
    topologicalGeneratorRankNat (freeProP p X) h = Nat.card X := by
  rw [(isProP_freeProP p X).topologicalGeneratorRankNat_eq_finrank_quotient_proPFrattini h,
    freeProP.finrank_quotient_proPFrattini]

/-- **The free pro-`p` group on a finite type `X` has topological generator rank `#X`**, in
cardinal form. -/
@[simp]
theorem topologicalGeneratorRank_freeProP : topologicalGeneratorRank (freeProP p X) = #X := by
  rw [← topologicalGeneratorRankNat_eq_topologicalGeneratorRank
    (isTopologicallyFinitelyGenerated_freeProP p X), topologicalGeneratorRankNat_freeProP,
    Nat.cast_card]

end TauCeti
