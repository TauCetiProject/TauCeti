/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct
public import TauCeti.Algebra.Coalgebra.Comodule.Trivial

/-!
# Tensor products of group-like comodules

Tensoring modules with group-like weights `g` and `h` gives the weight `g * h`.
The scalar tensor equivalence intertwines the coactions attached to group-like elements
`g`, `h` and `z` exactly when `z = g * h`.
-/

public section

open TauCeti TauCeti.Comodule
open scoped TensorProduct

namespace GroupLike

variable {R B : Type*} [CommSemiring R] [Semiring B] [Bialgebra R B]

/-- The diagonal tensor coaction of modules with weights `g` and `h` is the coaction
with weight `g * h`. Both source coactions are explicit, allowing coincident carriers. -/
theorem tensor_coact {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (g h : GroupLike R B) :
    letI : Comodule R B (M ⊗[R] N) :=
      @Comodule.tensor R B M N _ _ _ _ _ (groupLike g) _ _ (groupLike h)
    coact (R := R) (C := B) (M := M ⊗[R] N) = groupLikeCoact (g * h) := by
  apply TensorProduct.ext'
  intro m n
  rw [@Comodule.tensor_coact R B M N _ _ _ _ _ (groupLike g) _ _ (groupLike h),
    @tensorCoact_tmul R B M N _ _ _ _ _ (groupLike g) _ _ (groupLike h)]
  simp [groupLikeCoact]

/-- The canonical scalar tensor equivalence intertwines the rank-one coactions for
`g`, `h` and `z` exactly when `z = g * h`. The two source coactions are supplied explicitly
to the native tensor construction, so they can differ despite having the same carrier. -/
-- Simplify the criterion before the individual coactions unfold.
@[simp↓]
theorem tensor_lid_map_coact_iff (g h z : GroupLike R B) :
    letI : Comodule R B (R ⊗[R] R) :=
      @Comodule.tensor R B R R _ _ _ _ _ (groupLike g) _ _ (groupLike h)
    letI : Comodule R B R := groupLike z
    TensorProduct.map (TensorProduct.lid R R).toLinearMap LinearMap.id ∘ₗ
        coact (R := R) (C := B) (M := R ⊗[R] R) =
      coact (R := R) (C := B) (M := R) ∘ₗ (TensorProduct.lid R R).toLinearMap ↔
        z = g * h := by
  let : Comodule R B (R ⊗[R] R) :=
    @Comodule.tensor R B R R _ _ _ _ _ (groupLike g) _ _ (groupLike h)
  let : Comodule R B R := groupLike z
  rw [tensor_coact g h, ← GroupLike.val_inj, GroupLike.val_mul]
  constructor
  · intro hc
    have hc' := congrArg (fun f => TensorProduct.lid R B (f (1 ⊗ₜ[R] 1))) hc
    simpa [LinearMap.comp_apply, groupLikeCoact] using hc'.symm
  · intro hz
    apply TensorProduct.ext'
    intro m n
    simp [groupLikeCoact, hz]

end GroupLike
