/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Chevalley.Automorphism

/-!
# The Weyl automorphisms of a Chevalley system

Let `x` be a normalised family of root vectors in a Lie algebra `L` with nondegenerate Killing
form, and `α` a root. The vectors `(α^∨, x α, x (-α))` form an `sl₂` triple, and its Weyl
automorphism

```text
w_α = exp (ad (x α)) ∘ exp (ad (-x (-α))) ∘ exp (ad (x α))
```

(`TauCeti.weylAut`) is the Lie-algebra form of Chevalley's group element
`n_α = x_α(1) x_{-α}(-1) x_α(1)`. On the Cartan subalgebra `H` it is the coreflection
`y ↦ y - α(y) α^∨`, so it normalises `H` and permutes the weights by the reflection `s_α`
(`TauCeti.IsSl2System.map_weylAut_eq_self` and `TauCeti.IsSl2System.weightPerm_weylAut_apply`).

If `x` is moreover a Chevalley system for an involution `ω`, then `ω` exchanges `x α` with
`-x (-α)` and therefore commutes with `w_α` (`LieHom.map_weylAut`). The general sign theorem for
normalising automorphisms commuting with `ω`
(`TauCeti.IsChevalleySystem.aut_apply_eq_or_eq_neg`) then gives

```text
w_α (x β) = ± x (s_α β)
```

for every root `β`: the Weyl automorphisms permute the root vectors of a Chevalley system up to
sign. This is the Lie-algebra identity behind the root subgroups of a Chevalley group at
non-simple roots: every root is a Weyl translate of a simple root, so every root vector is, up to
sign, the image of a simple root vector under a composite of Weyl automorphisms of simple roots,
and in a representation such a composite is conjugation by a product of the elements `n_α`.

## Main results

* `TauCeti.IsChevalleySystem.weylAut_apply_eq_or_eq_neg`: for a Chevalley system the Weyl
  automorphism of the triple of a root `α` carries the root vector of `β` to the root vector of
  `s_α β`, up to sign.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4, where the signs are the constants `η_{r,s}`.
-/

public section

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [LieAlgebra ℚ L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  [IsTriangularizable K H L]

namespace IsChevalleySystem

variable {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : IsChevalleySystem ω x)

include hx

/-- **The Weyl automorphisms permute the root vectors of a Chevalley system up to sign.** For
roots `α` and `β`, the Weyl automorphism of the triple `(α^∨, x α, x (-α))` sends `x β` to
`x (s_α β)` or to `-x (s_α β)`, where `s_α β` is the reflection of `β` in `α`.

The Chevalley involution exchanges `x α` with `-x (-α)`, so it commutes with the Weyl
automorphism, and the sign theorem for normalising automorphisms applies. -/
theorem weylAut_apply_eq_or_eq_neg (i j : H.root) :
    weylAut (hx.toIsSl2System.isSl2Triple i (LieSubalgebra.isNonZero_coe_root i))
          (hx.toIsSl2System.isNilpotent_ad_rootVector i).exists_pow_apply_eq_zero
          (hx.toIsSl2System.isNilpotent_ad_rootVector (-i)).exists_pow_apply_eq_zero (x j) =
        x ((rootSystem H).reflectionPerm i j) ∨
      weylAut (hx.toIsSl2System.isSl2Triple i (LieSubalgebra.isNonZero_coe_root i))
          (hx.toIsSl2System.isNilpotent_ad_rootVector i).exists_pow_apply_eq_zero
          (hx.toIsSl2System.isNilpotent_ad_rootVector (-i)).exists_pow_apply_eq_zero (x j) =
        -x ((rootSystem H).reflectionPerm i j) := by
  have hα := LieSubalgebra.isNonZero_coe_root i
  have hW := hx.toIsSl2System.map_weylAut_eq_self hα
  have hcomm (z : L) := ((ω : L →ₗ⁅K⁆ L).map_weylAut (hx.toIsSl2System.isSl2Triple i hα)
    (hx.toIsSl2System.isNilpotent_ad_rootVector i).exists_pow_apply_eq_zero
    (hx.toIsSl2System.isNilpotent_ad_rootVector (-i)).exists_pow_apply_eq_zero
    (hx.map_root i) (by rw [LieEquiv.coe_toLieHom, hx.map_root, neg_neg]) z).symm
  -- the permuted weight is the reflected root
  have hperm : weightPerm _ hW (j : Weight K H L) =
      ((rootSystem H).reflectionPerm i j : Weight K H L) := by
    ext y
    have := LinearMap.congr_fun (((rootSystem H).root_reflectionPerm i j).trans
      ((rootSystem H).reflection_apply_root i j)) y
    rw [hx.toIsSl2System.weightPerm_weylAut_apply hα]
    simp only [rootSystem_pairing_apply, rootSystem_root_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Weight.toLinear_apply, smul_eq_mul] at this
    rw [this, mul_comm]
  simpa only [hperm] using hx.aut_apply_eq_or_eq_neg _ hW hcomm j

end IsChevalleySystem

end TauCeti
