/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import TauCeti.LinearAlgebra.Matrix.SiegelTransvection
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Form
import Mathlib.Tactic.LinearCombination

/-!
# Siegel (Eichler) transformations in the unitary group of a hermitian form

Let `R` be a commutative ring with an involution `star`, `J` a hermitian matrix over `R`, and
`h(v, w) = star v ⬝ᵥ J *ᵥ w` its sesquilinear form. For an isotropic vector `x`, a vector `w`
with `h(x, w) = 0` and a scalar `c` with `c + star c + h(w, w) = 0`, the Siegel transformation
(or Eichler transformation)

```text
S(x, w, c) : v ↦ v + h(x, v) (w + c x) - h(w, v) x
```

of `Matrix.siegelTransvection` (for the involution `starRingEnd R` and the sign `1`) preserves
`h` (`Matrix.star_siegelTransvection_mul_mul_self`), so it is an element of the unitary group
`Matrix.unitaryGroupOf J`, with inverse `S(x, -w, star c)`
(`Matrix.unitaryGroupOf.siegelTransvection`). Nothing is assumed of `R` beyond commutativity, and
`J` need not be invertible; this is the generality in which these transformations, with integral
data, serve for Witt's theorem over rings such as the integral finite adeles of a CM field.

With `w = -u` and `c = -ς`, `S(x, w, c)` is the Eichler map
`v ↦ v + h(u, v) x - h(x, v) (u + ς x)`, and the condition on `c` becomes `ς + star ς = h(u, u)`.

## Main definitions

* `Matrix.unitaryGroupOf.siegelTransvection`: for hermitian `J`, isotropic `x`, `h(x, w) = 0` and
  `c + star c + h(w, w) = 0`, the Siegel transformation `S(x, w, c)` as an element of
  `unitaryGroupOf J`.

## Main results

* `Matrix.star_siegelTransvection_mul_mul_self`: `star S J S = J` under the same hypotheses.

## Attribution

Placing the Eichler map in the unitary group of `J` follows `New.exists_unitary_eq_eichlerMap`
from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC),
file `src/Lib/Adelic/Witt/WittTheorem.lean`.

## References

* M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Grundlehren der mathematischen
  Wissenschaften 63, Springer (1952).
* A. J. Hahn and O. T. O'Meara, *The Classical Groups and K-Theory*, Grundlehren der
  mathematischen Wissenschaften 291, Springer (1989).
-/

public section

namespace Matrix

variable {R n : Type*} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n]
  {J : Matrix n n R} {x w : n → R} {c : R}

/-- **Admissible Siegel transformations preserve a hermitian form.** For hermitian `J`, an
isotropic `x` with `h(x, w) = 0` and `c + star c + h(w, w) = 0`, the Siegel transformation
`S(x, w, c)` for the involution `star` satisfies `star S J S = J`. -/
theorem star_siegelTransvection_mul_mul_self (hJ : J.IsHermitian) (hx : star x ⬝ᵥ J *ᵥ x = 0)
    (hxw : star x ⬝ᵥ J *ᵥ w = 0) (hc : c + star c + star w ⬝ᵥ J *ᵥ w = 0) :
    star (J.siegelTransvection (starRingEnd R) 1 x w c) * J *
      J.siegelTransvection (starRingEnd R) 1 x w c = J := by
  have hstar (M : Matrix n n R) : star M = (M.map (starRingEnd R))ᵀ := by
    ext; simp [starRingEnd_apply]
  have hQ : (J.map (starRingEnd R))ᵀ = (1 : R) • J := by rw [one_smul, ← hstar, hJ.star_eq]
  rw [hstar]
  exact transpose_map_siegelTransvection_mul_mul_self star_involutive hQ hx hxw
    (by rwa [one_mul, one_mul])

namespace unitaryGroupOf

/-- **The Siegel (Eichler) transformation as an element of the unitary group.** For hermitian `J`,
an isotropic `x` with `h(x, w) = 0` and `c + star c + h(w, w) = 0`, the Siegel transformation
`S(x, w, c) : v ↦ v + h(x, v) (w + c x) - h(w, v) x` is an element of `unitaryGroupOf J`, with
inverse `S(x, -w, star c)`. -/
def siegelTransvection (hJ : J.IsHermitian) (hx : star x ⬝ᵥ J *ᵥ x = 0)
    (hxw : star x ⬝ᵥ J *ᵥ w = 0) (hc : c + star c + star w ⬝ᵥ J *ᵥ w = 0) :
    unitaryGroupOf J :=
  have hinv : J.siegelTransvection (starRingEnd R) 1 x w c *
      J.siegelTransvection (starRingEnd R) 1 x (-w) (star c) = 1 := by
    have hwx : star w ⬝ᵥ J *ᵥ x = 0 := by rw [← hJ.star_dotProduct_mulVec_comm, hxw, star_zero]
    have hc' : -c - 1 * (star w ⬝ᵥ J *ᵥ w) = star c := by
      linear_combination (-1 : R) * hc
    rw [← hc']
    exact siegelTransvection_mul_siegelTransvection_neg_eq_one hx hxw hwx c
  ⟨⟨J.siegelTransvection (starRingEnd R) 1 x w c,
      J.siegelTransvection (starRingEnd R) 1 x (-w) (star c), hinv, mul_eq_one_comm.mp hinv⟩,
    mem_unitaryGroupOf_iff.2 (star_siegelTransvection_mul_mul_self hJ hx hxw hc)⟩

/-- The matrix of the Siegel transformation in the unitary group is `S(x, w, c)`. -/
@[simp]
theorem val_siegelTransvection (hJ : J.IsHermitian) (hx : star x ⬝ᵥ J *ᵥ x = 0)
    (hxw : star x ⬝ᵥ J *ᵥ w = 0) (hc : c + star c + star w ⬝ᵥ J *ᵥ w = 0) :
    ((siegelTransvection hJ hx hxw hc : GL n R) : Matrix n n R) =
      J.siegelTransvection (starRingEnd R) 1 x w c :=
  (rfl)

/-- The matrix of the inverse of the Siegel transformation in the unitary group is
`S(x, -w, star c)`. This is not a simp lemma: simp rewrites the left-hand side to the matrix
inverse of `S(x, w, c)` through `val_siegelTransvection`. -/
theorem val_inv_siegelTransvection (hJ : J.IsHermitian) (hx : star x ⬝ᵥ J *ᵥ x = 0)
    (hxw : star x ⬝ᵥ J *ᵥ w = 0) (hc : c + star c + star w ⬝ᵥ J *ᵥ w = 0) :
    ((((siegelTransvection hJ hx hxw hc)⁻¹ : unitaryGroupOf J) : GL n R) : Matrix n n R) =
      J.siegelTransvection (starRingEnd R) 1 x (-w) (star c) :=
  (rfl)

end unitaryGroupOf

end Matrix
