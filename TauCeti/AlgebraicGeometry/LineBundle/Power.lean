/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

/-!
# Tensor powers of line bundles

For a line bundle `L` on a scheme `X` and `n : ℕ`, the tensor power `L^{⊗n}` is the line bundle
defined recursively by `L^{⊗0} = 𝒪_X` and `L^{⊗(n+1)} = L^{⊗n} ⊗ L`.
These powers retain invertibility as bundled line bundles and provide the objects used in
global generation and ample twisting. They use `InvertibleSheaf.tensorProduct`, the operation
defining multiplication in `LineBundleClass`, rather than the monoidal product of `X.Modules`.
The comparisons below assert existence of isomorphisms; they do not specify coherent morphisms.

Ported from `roed-math/TauCeti-w2-fresh`, branch
`lookahead/StableReduction/relative-ampleness`, commit `efa6fc8f3735`.

## Main declarations

* `TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorPow L n`: the tensor power `L^{⊗n}`.
* `TauCeti.AlgebraicGeometry.LineBundleClass.mk_tensorPow`: the class of `L^{⊗n}` is the `n`-th
  power of the class of `L` in the Picard group.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.nonempty_tensorPow_obj_iso`: tensor powers of
  isomorphic line bundles are isomorphic.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.nonempty_tensorPow_add_iso` and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.nonempty_tensorPow_tensorPow_iso`: the exponent laws
  `L^{⊗(m + n)} ≅ L^{⊗m} ⊗ L^{⊗n}` and `(L^{⊗m})^{⊗n} ≅ L^{⊗(m * n)}`.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.nonempty_pullback_tensorPow_iso`: pullback commutes
  with tensor powers up to isomorphism.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.6 (the Picard group).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

namespace InvertibleSheaf

/-- The tensor power `L^{⊗n}` of a line bundle, defined by `L^{⊗0} = 𝒪_X` and
`L^{⊗(n+1)} = L^{⊗n} ⊗ L`. -/
noncomputable def tensorPow (L : InvertibleSheaf X) : ℕ → InvertibleSheaf X
  | 0 => trivial X
  | n + 1 => tensorProduct (L.tensorPow n) L

/-- The zeroth tensor power of a line bundle is the trivial line bundle. -/
@[simp]
lemma tensorPow_zero (L : InvertibleSheaf X) : L.tensorPow 0 = trivial X :=
  (rfl)

/-- The `(n + 1)`-st tensor power of `L` is `L^{⊗n} ⊗ L`. -/
lemma tensorPow_succ (L : InvertibleSheaf X) (n : ℕ) :
    L.tensorPow (n + 1) = tensorProduct (L.tensorPow n) L :=
  (rfl)

end InvertibleSheaf

namespace LineBundleClass

/-- The class of the tensor power `L^{⊗n}` is the `n`-th power of the class of `L`. -/
@[simp]
lemma mk_tensorPow (L : InvertibleSheaf X) (n : ℕ) : mk (L.tensorPow n) = mk L ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [InvertibleSheaf.tensorPow_succ, ih, pow_succ]

end LineBundleClass

namespace InvertibleSheaf

/-- The underlying sheaves of `L^{⊗n}` and `K^{⊗n}` are isomorphic whenever the underlying sheaves
of `L` and `K` are. -/
theorem nonempty_tensorPow_obj_iso {L K : InvertibleSheaf X} (h : Nonempty (L.obj ≅ K.obj))
    (n : ℕ) : Nonempty ((L.tensorPow n).obj ≅ (K.tensorPow n).obj) := by
  rw [← LineBundleClass.mk_eq_mk_iff] at h ⊢
  simp [h]

/-- The tensor power `L^{⊗(m + n)}` is isomorphic to `L^{⊗m} ⊗ L^{⊗n}`. -/
theorem nonempty_tensorPow_add_iso (L : InvertibleSheaf X) (m n : ℕ) :
    Nonempty ((L.tensorPow (m + n)).obj ≅ (tensorProduct (L.tensorPow m) (L.tensorPow n)).obj) := by
  rw [← LineBundleClass.mk_eq_mk_iff]
  simp [pow_add]

/-- The tensor power `(L^{⊗m})^{⊗n}` is isomorphic to `L^{⊗(m * n)}`. -/
theorem nonempty_tensorPow_tensorPow_iso (L : InvertibleSheaf X) (m n : ℕ) :
    Nonempty (((L.tensorPow m).tensorPow n).obj ≅ (L.tensorPow (m * n)).obj) := by
  rw [← LineBundleClass.mk_eq_mk_iff]
  simp [pow_mul]

/-- **Pullback commutes with tensor powers.** For `f : X ⟶ Y` and a line bundle `L` on `Y`, the
pullback of `L^{⊗n}` is isomorphic to `(f^* L)^{⊗n}`. -/
theorem nonempty_pullback_tensorPow_iso (f : X ⟶ Y) (L : InvertibleSheaf Y) (n : ℕ) :
    Nonempty (((pullback f).obj (L.tensorPow n)).obj ≅ (((pullback f).obj L).tensorPow n).obj) := by
  rw [← LineBundleClass.mk_eq_mk_iff, ← LineBundleClass.pullback_mk]
  simp

end InvertibleSheaf

end AlgebraicGeometry

end TauCeti
