/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent

/-!
# Convolution acts additively on cotangent spaces

For counit-preserving algebra maps from a bialgebra to a commutative bialgebra, convolution
becomes addition after applying the cotangent displacement. In particular, the multiplication-by-`n`
map of an affine monoid induces multiplication by `n` on its cotangent space at the identity.

The displacement formulas need no cocommutativity. For bundled bialgebra maps, the source is
cocommutative so that their convolution is again a bialgebra map.

## References

* J. Tate and F. Oort, *Group schemes of prime order*, Ann. Sci. École Norm. Sup. (4) 3 (1970),
  1–21, §1, for the convolution description of multiplication-by-`n`:
  https://www.numdam.org/item/ASENS_1970_4_3_1_1_0/.
-/

public section

open Coalgebra TensorProduct WithConv

namespace TauCeti.Bialgebra

variable {R A B : Type*} [CommRing R] [CommRing B] [Bialgebra R B]

section Displacement

variable [Semiring A] [Bialgebra R A]

/-- The cotangent displacement of the convolution of two counit-preserving algebra maps is
the sum of their cotangent displacements. Neither cocommutativity nor an antipode is needed. -/
theorem cotangentMap_convMul (f g : WithConv (A →ₐ[R] B))
    (hf : ∀ a, counit (R := R) (f.ofConv a) = counit (R := R) a)
    (hg : ∀ a, counit (R := R) (g.ofConv a) = counit (R := R) a) (a : A) :
    cotangentMap R B ((f * g).ofConv a) =
      cotangentMap R B (f.ofConv a) + cotangentMap R B (g.ofConv a) := by
  have h : (cotangentMap R B).comp
      (Algebra.TensorProduct.lift f.ofConv g.ofConv (fun _ _ ↦ .all ..)).toLinearMap =
      ((cotangentMap R B).comp g.ofConv.toLinearMap).comp
        ((TensorProduct.lid R A).toLinearMap.comp ((counit (R := R)).rTensor A)) +
      ((cotangentMap R B).comp f.ofConv.toLinearMap).comp
        ((TensorProduct.rid R A).toLinearMap.comp ((counit (R := R)).lTensor A)) := by
    ext x y
    simp [cotangentMap_mul, hf, hg]
  rw [AlgHom.convMul_apply]
  simpa [add_comm] using DFunLike.congr_fun h (comul a)

/-- The cotangent displacement of a convolution power of a counit-preserving algebra map is
the corresponding natural-number multiple of its cotangent displacement. -/
theorem cotangentMap_convPow (f : WithConv (A →ₐ[R] B))
    (hf : ∀ a, counit (R := R) (f.ofConv a) = counit (R := R) a) (n : ℕ) (a : A) :
    cotangentMap R B ((f ^ n).ofConv a) = n • cotangentMap R B (f.ofConv a) := by
  have hε : _root_.AlgHom.mapValue (_root_.Bialgebra.counitAlgHom R B) f = 1 := by
    ext x
    simpa using hf x
  have hpow (m : ℕ) (x : A) :
      counit (R := R) ((f ^ m).ofConv x) = counit (R := R) x := by
    have h := map_pow (_root_.AlgHom.mapValue (_root_.Bialgebra.counitAlgHom R B)) f m
    rw [hε, one_pow] at h
    simpa using congrArg (fun z ↦ z.ofConv x) h
  induction n with
  | zero => simp [Algebra.algebraMap_eq_smul_one]
  | succ n ih => rw [pow_succ, cotangentMap_convMul (f ^ n) f (hpow n) hf, ih, succ_nsmul]

end Displacement

section Map

variable [CommRing A] [Bialgebra R A]

/-- The trivial bialgebra point induces zero on cotangent spaces. -/
@[simp]
theorem cotangentSpaceMap_convOne :
    cotangentSpaceMap (1 : WithConv (A →ₐc[R] B)).ofConv = 0 := by
  ext x
  obtain ⟨a, rfl⟩ := cotangentMap_surjective R A x
  simp [Algebra.algebraMap_eq_smul_one]

variable [Coalgebra.IsCocomm R A]

/-- Convolution of bialgebra maps induces addition on cotangent spaces. -/
@[simp]
theorem cotangentSpaceMap_convMul (f g : WithConv (A →ₐc[R] B)) :
    cotangentSpaceMap (f * g).ofConv =
      cotangentSpaceMap f.ofConv + cotangentSpaceMap g.ofConv := by
  ext x
  obtain ⟨a, rfl⟩ := cotangentMap_surjective R A x
  simpa [← BialgHom.toAlgHom_convMul] using
    cotangentMap_convMul (toConv f.ofConv.toAlgHom) (toConv g.ofConv.toAlgHom)
      (CoalgHomClass.counit_comp_apply f.ofConv) (CoalgHomClass.counit_comp_apply g.ofConv) a

/-- A convolution power of a bialgebra map induces the corresponding multiple of its map
on cotangent spaces. -/
@[simp]
theorem cotangentSpaceMap_convPow (f : WithConv (A →ₐc[R] B)) (n : ℕ) :
    cotangentSpaceMap (f ^ n).ofConv = n • cotangentSpaceMap f.ofConv := by
  induction n with
  | zero => simp [cotangentSpaceMap_convOne]
  | succ n ih => rw [pow_succ, cotangentSpaceMap_convMul, ih, succ_nsmul]

end Map

end TauCeti.Bialgebra
