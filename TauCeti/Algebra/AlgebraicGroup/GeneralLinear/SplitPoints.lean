/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.WeilRestriction
public import TauCeti.RingTheory.Etale.Galois

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
      (GeneralLinearGroup.piEquiv (n := Fin n) fun _ : B →ₐ[K] Ω ↦ Ω))

variable {K B Ω n}

/-- The component at `τ` is evaluation of the matrix of tensor-product entries along
`b ⊗ ω ↦ τ(b)ω`. -/
@[simp]
theorem generalLinearSplitPoints_apply
    (x : WithConv (WeilRestriction K B (GeneralLinear.coordinateHopfAlgebra B n) →ₐ[K] Ω))
    (τ : B →ₐ[K] Ω) :
    generalLinearSplitPoints K B Ω n x τ =
      GeneralLinearGroup.map (Algebra.TensorProduct.productMap τ (AlgHom.id K Ω) :
        B ⊗[K] Ω →+* Ω) (generalLinearPoints K B n Ω x) := by
  apply Units.ext
  ext i j
  -- The general linear group equivalences apply the scalar splitting entrywise.
  exact Algebra.Etale.tensorProductEquivPi_comm (generalLinearPoints K B n Ω x i j) τ

/-- In matrix coordinates, the inverse splitting assembles the tuple over the product ring
and transports it back along the étale splitting. -/
@[simp]
theorem generalLinearSplitPoints_symm_apply (g : (B →ₐ[K] Ω) → GL (Fin n) Ω) :
    generalLinearPoints K B n Ω ((generalLinearSplitPoints K B Ω n).symm g) =
      GeneralLinearGroup.mapEquiv (Fin n) ((Algebra.TensorProduct.comm K B Ω).toRingEquiv.trans
        (Algebra.Etale.tensorProductEquivPi K Ω B).toRingEquiv).symm
        ((GeneralLinearGroup.piEquiv (n := Fin n) fun _ : B →ₐ[K] Ω ↦ Ω).symm g) := by
  simp only [generalLinearSplitPoints, MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply,
    GeneralLinearGroup.symm_mapEquiv]

end TauCeti.Algebra.WeilRestriction
