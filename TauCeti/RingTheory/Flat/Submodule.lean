/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Extension of scalars along a flat algebra preserves kernels and intersections

Let `A` be a flat algebra over `R`. Then `Submodule.baseChange A` carries the kernel of an
`R`-linear map to the kernel of its base change, and consequently carries an intersection of
submodules to the intersection of their base changes.

Mathlib records the order-theoretic half of this picture for a *faithfully* flat algebra
(`Submodule.baseChange_le_iff`, `Submodule.baseChangeOrderEmbedding`) and the module-theoretic
input for a flat one (`Module.Flat.ker_lTensor_eq`). What is added here is the submodule reading
of that input and the intersection formula it yields, so that base change is a morphism of
lattices and not only of orders. Intersections are where flatness is genuinely needed: a
submodule and its base change are ranges, and only flatness makes the base change of an inclusion
into an inclusion.

The intersection formula is deduced by writing `p ⊓ q` as the kernel of the map
`M → (M ⧸ p) × (M ⧸ q)` and commuting the base change past the product with
`TensorProduct.prodRight`.

## Main results

* `TauCeti.LinearMap.ker_baseChange_prod`: the kernel of the base change of a pair of maps.
* `TauCeti.Submodule.baseChange_ker`: base change carries a kernel to a kernel.
* `TauCeti.Submodule.baseChange_inf`: base change preserves intersections.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {R M N P : Type*} (A : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

namespace LinearMap

/-- The base change of a pair of maps has the intersection of the two base-changed kernels as its
kernel: tensoring with `A` commutes with the product on the target. This holds for any algebra
`A`; no flatness is involved. -/
theorem ker_baseChange_prod (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    LinearMap.ker ((f.prod g).baseChange A) =
      LinearMap.ker (f.baseChange A) ⊓ LinearMap.ker (g.baseChange A) := by
  have key : (TensorProduct.prodRight R A A N P).toLinearMap ∘ₗ (f.prod g).baseChange A =
      (f.baseChange A).prod (g.baseChange A) := by
    refine LinearMap.ext fun x ↦ ?_
    induction x using TensorProduct.induction_on with
    | zero => simp [Prod.ext_iff]
    | tmul a m => simp
    | add x y hx hy =>
      simp only [LinearMap.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
  rw [← LinearMap.ker_prod, ← key, LinearMap.ker_comp,
    LinearMap.ker_eq_bot.2 (TensorProduct.prodRight R A A N P).injective, Submodule.comap_bot]

end LinearMap

namespace Submodule

variable [Module.Flat R A]

/-- Extension of scalars along a flat algebra carries the kernel of a map to the kernel of its
base change. -/
theorem baseChange_ker (f : M →ₗ[R] N) :
    (LinearMap.ker f).baseChange A = LinearMap.ker (f.baseChange A) :=
  (Module.Flat.ker_lTensor_eq A A f).symm

/-- Extension of scalars along a flat algebra preserves intersections of submodules. -/
theorem baseChange_inf (p q : Submodule R M) :
    (p ⊓ q).baseChange A = p.baseChange A ⊓ q.baseChange A := by
  have hp : p.baseChange A = LinearMap.ker (p.mkQ.baseChange A) := by
    rw [← baseChange_ker, Submodule.ker_mkQ]
  have hq : q.baseChange A = LinearMap.ker (q.mkQ.baseChange A) := by
    rw [← baseChange_ker, Submodule.ker_mkQ]
  have hpq : p ⊓ q = LinearMap.ker (p.mkQ.prod q.mkQ) := by
    rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  rw [hp, hq, ← LinearMap.ker_baseChange_prod, hpq, baseChange_ker]

end Submodule

end TauCeti
