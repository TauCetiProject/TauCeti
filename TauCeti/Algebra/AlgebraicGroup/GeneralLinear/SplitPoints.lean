/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.WeilRestriction
public import TauCeti.RingTheory.Etale.Galois
import Mathlib.Algebra.Group.Pi.Units

/-!
# Split points of the Weil restriction of the general linear group

Over a separably closed field, a finite étale algebra splits as a product of copies of the
coefficient field. The points of its Weil restriction of `GLₙ` accordingly form a product of
general linear groups, with each component obtained by applying the corresponding embedding
to the matrix entries.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.i.
-/

public section

open Matrix WithConv
open scoped TensorProduct

namespace TauCeti.Algebra.WeilRestriction

variable (K B Ω : Type*) [Field K] [CommRing B] [Algebra K B] [Module.Finite K B]
  [Algebra.Etale K B] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (n : ℕ)

/-- The points of `Res_{B/K} GLₙ` over a separably closed field `Ω` form one copy of
`GLₙ(Ω)` for every `K`-algebra map `B → Ω`. -/
noncomputable def generalLinearSplitPoints :
    WithConv (WeilRestriction K B (GeneralLinear.coordinateHopfAlgebra B n) →ₐ[K] Ω) ≃*
      ((B →ₐ[K] Ω) → GL (Fin n) Ω) :=
  (generalLinearPoints K B n Ω).trans
    ((GeneralLinearGroup.mapEquiv (Fin n)
      ((Algebra.TensorProduct.comm K B Ω).toRingEquiv.trans
        (Algebra.Etale.tensorProductEquivPi K Ω B).toRingEquiv)).trans
      ((Units.mapEquiv Matrix.piRingEquiv.toMulEquiv).trans MulEquiv.piUnits))

variable {K B Ω n}

/-- The component at `τ` is evaluation of the matrix of tensor-product entries along
`b ⊗ ω ↦ τ(b)ω`. -/
theorem generalLinearSplitPoints_apply
    (x : WithConv (WeilRestriction K B (GeneralLinear.coordinateHopfAlgebra B n) →ₐ[K] Ω))
    (τ : B →ₐ[K] Ω) :
    generalLinearSplitPoints K B Ω n x τ =
      GeneralLinearGroup.map (Algebra.TensorProduct.productMap τ (AlgHom.id K Ω) :
        B ⊗[K] Ω →+* Ω) (generalLinearPoints K B n Ω x) := by
  apply Units.ext
  ext i j
  exact Algebra.Etale.tensorProductEquivPi_comm _ _

end TauCeti.Algebra.WeilRestriction
