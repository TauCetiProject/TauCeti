/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order
import Mathlib.Topology.KrullDimension

/-!
# Principal divisors on Noetherian integral schemes

For a Noetherian integral scheme `X`, this file combines Mathlib's local orders of vanishing into
the global order system on the codimension-one points of `X`. The only global issue is finite
support. A nonzero rational function is a unit on some nonempty affine open `U`; its order
therefore vanishes on `U`. The codimension-one points outside `U` are finite, by Mathlib's
`NoetherianSpace.finite_coheight_one_of_closure_ne_univ` applied to the closed complement.

The main results are:

* `SchemeWeilDivisor.finite_setOfPred_not_mem`: a nonempty open misses only finitely many
  codimension-one points;
* `SchemeWeilDivisor.finite_support_orderAt`: the orders of a nonzero rational function have
  finite support;
* `WeilDivisor.OrderSystem.ofScheme`: the resulting order system, whose generic
  `OrderSystem.principalDivisor` is the scheme-theoretic principal divisor;
* `SchemeWeilDivisor.isEffective_add_principalDivisor_iff`: the coefficientwise criterion for a
  divisor plus a principal divisor to be effective.

This file completes the global step left open by
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Order.lean`. The proof reuses Mathlib's
`exists_isUnit_germ_eq`, `Scheme.ord_of_isUnit`, and
`NoetherianSpace.finite_coheight_one_of_closure_ne_univ`. No formalization is vendored.
-/

public section

open AlgebraicGeometry Order TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}}

noncomputable section

/-- A nonempty open subset of an irreducible scheme with Noetherian underlying space contains all
but finitely many codimension-one points. -/
lemma finite_setOfPred_not_mem [IrreducibleSpace X] [NoetherianSpace X]
    (U : X.Opens) [Nonempty U] :
    {x : CodimensionOnePoint X | (x : X) ∉ U}.Finite := by
  have hU := U.isOpen.isClosed_compl
  have : QuasiSober ((U : Set X)ᶜ : Set X) := hU.isClosedEmbedding_subtypeVal.quasiSober
  refine ((NoetherianSpace.finite_coheight_one_of_closure_ne_univ (p := (U : Set X)ᶜ) ?_).preimage
    Subtype.val_injective.injOn).subset fun x hx ↦ ⟨hx, x.2⟩
  rw [hU.closure_eq]
  exact fun h ↦ (Set.nonempty_coe_sort.mp ‹Nonempty U›).ne_empty (compl_eq_top.mp h)

variable [IsIntegral X] [IsNoetherian X]

/-- The orders of a nonzero rational function on a Noetherian integral scheme are nonzero at only
finitely many codimension-one points. -/
lemma finite_support_orderAt (f : Additive X.functionFieldˣ) :
    (Function.support fun x : CodimensionOnePoint X ↦ orderAt x f).Finite := by
  obtain ⟨U, _, a, hU, ha, haUnit⟩ :=
    exists_isUnit_germ_eq X ((Additive.toMul f : X.functionFieldˣ) : X.functionField)
      (Units.ne_zero _)
  let : Nonempty U := hU
  refine (finite_setOfPred_not_mem U).subset ?_
  intro x hx
  simp only [Set.mem_ofPred_eq]
  intro hxU
  exact hx <| by
    simpa only [orderAt_apply, ← ha] using X.ord_of_isUnit haUnit hxU

end

end SchemeWeilDivisor

namespace WeilDivisor.OrderSystem

/-- The orders of vanishing of nonzero rational functions at codimension-one points, assembled
into the order system whose principal divisors are scheme-theoretic Weil divisors. -/
noncomputable def ofScheme (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X] :
    OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ) where
  ord := SchemeWeilDivisor.orderAt
  finite_support := SchemeWeilDivisor.finite_support_orderAt

/-- The order map in the scheme-theoretic order system is the locally defined order map. -/
@[simp]
lemma ofScheme_ord {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (x : CodimensionOnePoint X) :
    (ofScheme X).ord x = SchemeWeilDivisor.orderAt x :=
  (rfl)

end WeilDivisor.OrderSystem

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- A divisor plus a principal divisor is effective exactly when the corresponding rational
function has order at least the negative of the divisor coefficient at every codimension-one
point. -/
lemma isEffective_add_principalDivisor_iff
    (D : SchemeWeilDivisor X) (g : Additive X.functionFieldˣ) :
    WeilDivisor.IsEffective
        (D + (WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) ↔
      ∀ x : CodimensionOnePoint X,
        -WeilDivisor.coeff D x ≤
          X.ord ((Additive.toMul g : X.functionFieldˣ) : X.functionField) x := by
  rw [WeilDivisor.isEffective_iff]
  apply forall_congr'
  intro x
  rw [WeilDivisor.coeff_add, WeilDivisor.OrderSystem.coeff_principalDivisor,
    WeilDivisor.OrderSystem.ofScheme_ord, orderAt_apply]
  omega

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
