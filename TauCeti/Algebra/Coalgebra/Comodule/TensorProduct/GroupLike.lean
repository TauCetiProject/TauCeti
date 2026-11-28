/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct
public import TauCeti.Algebra.Coalgebra.Comodule.Trivial

/-!
# Tensor products of rank-one comodules

The scalar tensor equivalence intertwines the coactions attached to group-like elements
`g`, `h` and `z` exactly when `z = g * h`.
-/

public section

open TauCeti TauCeti.Comodule
open scoped TensorProduct

namespace GroupLike

variable {R B : Type*} [CommSemiring R] [Semiring B] [Bialgebra R B]

/-- The canonical scalar tensor equivalence intertwines the rank-one coactions for
`g`, `h` and `z` exactly when `z = g * h`. The two source coactions are supplied explicitly
to the native tensor construction, so they can differ despite having the same carrier. -/
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
  rw [← GroupLike.val_inj, GroupLike.val_mul]
  have hcoact (m n : R) :
      coact (R := R) (C := B) (M := R ⊗[R] R) (m ⊗ₜ[R] n) =
        (m ⊗ₜ[R] n) ⊗ₜ[R] ((g : B) * (h : B)) := by
    -- The scalar carriers agree, so pass both distinct source coactions explicitly.
    rw [@tensor_coact R B R R _ _ _ _ _ (groupLike g) _ _ (groupLike h),
      @tensorCoact_tmul R B R R _ _ _ _ _ (groupLike g) _ _ (groupLike h)]
    simp only [groupLike_coact_apply, tensorCombine_tmul_tmul]
  constructor
  · intro hc
    have hc' := congrArg (fun f => TensorProduct.lid R B (f (1 ⊗ₜ[R] 1))) hc
    simpa [LinearMap.comp_apply, hcoact] using hc'.symm
  · intro hz
    apply TensorProduct.ext'
    intro m n
    simp only [LinearMap.comp_apply, hcoact, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.lid_tmul, groupLike_coact_apply, hz]

end GroupLike
