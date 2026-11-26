/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Hodge.TensorProduct
public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Tate

/-!
# Hodge components of Tate twists

For a real representation `V` of the Deligne torus `S` and `m : ℤ`, the Tate twist is
`V(m) = V ⊗[ℝ] ℝ(m)`, where `ℝ(m)` is the Tate comodule `TauCeti.DeligneTorus.tateComodule`, of
the single Hodge type `(-m, -m)`. Since Hodge types add on tensor products
(`TauCeti.DeligneTorus.hodgeComponent_tensor`), twisting shifts Hodge types by `(-m, -m)`:

```text
V(m)^{p,q} = V^{p+m,q+m} ⊗ ℝ(m).
```

The statement is proved for the Tate coaction on any real vector space `M` in place of `ℝ`.

## Main results

* `TauCeti.DeligneTorus.hodgeComponent_tensor_tateComodule`: `(V ⊗ M(m))^{p,q}` is the image of
  `V^{p+m,q+m} ⊗ (ℂ ⊗ M)`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, pp. 26–27.
-/

public section

open WithConv TauCeti.Algebra
open scoped TensorProduct

namespace TauCeti.DeligneTorus

variable {V M : Type*} [AddCommGroup V] [Module ℝ V] [Comodule ℝ S V]
  [AddCommGroup M] [Module ℝ M]

attribute [local instance] Comodule.tensor

/-- **The Hodge components of a Tate twist.** For the Tate coaction `M(m)` on a real vector
space `M`, the Hodge component `(V ⊗ M(m))^{p,q}` is the image of `V^{p+m,q+m} ⊗ (ℂ ⊗ M)` in
`ℂ ⊗[ℝ] (V ⊗[ℝ] M)`: twisting by `ℝ(m)` shifts Hodge types by `(-m, -m)`. -/
theorem hodgeComponent_tensor_tateComodule (m p q : ℤ) :
    letI := tateComodule M m
    hodgeComponent (V ⊗[ℝ] M) p q =
      ((hodgeComponent V (p + m) (q + m)).map₂ (TensorProduct.mk ℂ (ℂ ⊗[ℝ] V) (ℂ ⊗[ℝ] M))
          ⊤).map
        (TensorProduct.AlgebraTensorModule.distribBaseChange ℝ ℂ V M).symm.toLinearMap := by
  let _ := tateComodule M m
  rw [hodgeComponent_tensor]
  refine le_antisymm (iSup_le fun ab ↦ ?_) (le_iSup_of_le (p + m, q + m) ?_)
  · rw [hodgeComponent_tateComodule]
    split_ifs with h
    · have h1 : ab.1 = p + m := by omega
      have h2 : ab.2 = q + m := by omega
      rw [h1, h2]
    · simp
  · rw [hodgeComponent_tateComodule, ite_eq_left (by omega)]

end TauCeti.DeligneTorus
