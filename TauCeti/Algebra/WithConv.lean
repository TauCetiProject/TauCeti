/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.WithConv

/-!
# Additional instances on the convolution type synonym `WithConv`

`Mathlib.Algebra.WithConv` equips the type synonym `WithConv A` with `Unique` and `Nontrivial`
instances transferred from `A`, but omits `Subsingleton`. Transferring `Subsingleton` across
`WithConv.equiv A` makes `WithConv (k →ₐ[k] R)` a subsingleton for every coefficient `k`-algebra
`R` (via `AlgHom.subsingleton_id`), expressing that the trivial affine group scheme `Spec k` has a
single `R`-point.

## Main declarations

* `WithConv.instSubsingleton`: `WithConv A` is a subsingleton whenever `A` is.

## References

* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin (1969), §4.0.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Graduate Texts in Mathematics 66,
  Springer (1979), §1.4.
-/

public section

namespace WithConv

/-- `WithConv A` is a subsingleton whenever `A` is. In particular, `WithConv (k →ₐ[k] R)` is a
subsingleton for every coefficient `k`-algebra `R`. -/
instance instSubsingleton {A : Type*} [Subsingleton A] : Subsingleton (WithConv A) :=
  (WithConv.equiv A).subsingleton

end WithConv
