/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.LineBundle.Monoidal

/-!
# Tensor powers of line bundles

For a line bundle `L` on a scheme `X` and `n : ℕ`, the tensor power `L^{⊗n}` is the line bundle
given by `TauCeti.tensorPow`, with `L^{⊗0} = 𝒪_X` and `L^{⊗(n+1)} = L ⊗ L^{⊗n}`.
These powers retain invertibility as bundled line bundles and provide the objects used in
global generation and ample twisting. They use the inherited monoidal product, so their
underlying sheaves are the same tensor powers used for powers of sections.
An isomorphism `e : L ≅ K` induces the isomorphism `TauCeti.tensorPowMapIso e n` of tensor powers,
functorial in `e`, and the powers of the trivial line bundle are trivial by a specified
isomorphism. These are the operations on tensor powers needed to compare `n`-th roots
`M^{⊗n} ≅ L` of a line bundle. The exponent laws and the compatibility with pullback below are
still only stated as the existence of isomorphisms.

Ported from `roed-math/TauCeti-w2-fresh`, branch
`lookahead/StableReduction/relative-ampleness`, commit `efa6fc8f3735`.

## Main declarations

* `TauCeti.tensorPow L n`: the tensor power `L^{⊗n}`.
* `TauCeti.AlgebraicGeometry.LineBundleClass.mk_tensorPow`: the class of `L^{⊗n}` is the `n`-th
  power of the class of `L` in the Picard group.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.nonempty_tensorPow_obj_iso`: tensor powers of
  isomorphic line bundles are isomorphic, via `TauCeti.tensorPowMapIso`.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorPowTrivialIso X n`: the isomorphism
  `𝒪_X^{⊗n} ≅ 𝒪_X`.
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

variable (X) in
/-- The `n`-th tensor power of the trivial line bundle is the trivial line bundle: transport to
the monoidal unit and remove its tensor powers with `TauCeti.tensorPowUnitIso`. -/
noncomputable def tensorPowTrivialIso (n : ℕ) : TauCeti.tensorPow (trivial X) n ≅ trivial X :=
  TauCeti.tensorPowMapIso (trivialIsoTensorUnit X) n ≪≫ TauCeti.tensorPowUnitIso n ≪≫
    (trivialIsoTensorUnit X).symm

variable (X) in
/-- The isomorphism `𝒪_X^{⊗n} ≅ 𝒪_X` is `TauCeti.tensorPowUnitIso n` transported along the
identification `trivialIsoTensorUnit X` of `𝒪_X` with the monoidal unit. -/
theorem tensorPowTrivialIso_def (n : ℕ) :
    tensorPowTrivialIso X n = TauCeti.tensorPowMapIso (trivialIsoTensorUnit X) n ≪≫
      TauCeti.tensorPowUnitIso n ≪≫ (trivialIsoTensorUnit X).symm :=
  (rfl)

end InvertibleSheaf

namespace LineBundleClass

/-- The class of the tensor power `L^{⊗n}` is the `n`-th power of the class of `L`. -/
@[simp]
lemma mk_tensorPow (L : InvertibleSheaf X) (n : ℕ) : mk (TauCeti.tensorPow L n) = mk L ^ n := by
  induction n with
  | zero => exact mk_tensorUnit X
  | succ n ih => simp [ih, pow_succ, mul_comm]

end LineBundleClass

namespace InvertibleSheaf

/-- The underlying sheaves of `L^{⊗n}` and `K^{⊗n}` are isomorphic whenever the underlying sheaves
of `L` and `K` are. -/
theorem nonempty_tensorPow_obj_iso {L K : InvertibleSheaf X} (h : Nonempty (L.obj ≅ K.obj))
    (n : ℕ) : Nonempty ((TauCeti.tensorPow L n).obj ≅ (TauCeti.tensorPow K n).obj) :=
  h.map fun e ↦ (SheafOfModules.isInvertible X).ι.mapIso
    (TauCeti.tensorPowMapIso (ObjectProperty.isoMk _ e) n)

/-- The tensor power `L^{⊗(m + n)}` is isomorphic to `L^{⊗m} ⊗ L^{⊗n}`. -/
theorem nonempty_tensorPow_add_iso (L : InvertibleSheaf X) (m n : ℕ) :
    Nonempty ((TauCeti.tensorPow L (m + n)).obj ≅
      (tensorProduct (TauCeti.tensorPow L m) (TauCeti.tensorPow L n)).obj) := by
  rw [← LineBundleClass.mk_eq_mk_iff]
  simp [pow_add]

/-- The tensor power `(L^{⊗m})^{⊗n}` is isomorphic to `L^{⊗(m * n)}`. -/
theorem nonempty_tensorPow_tensorPow_iso (L : InvertibleSheaf X) (m n : ℕ) :
    Nonempty ((TauCeti.tensorPow (TauCeti.tensorPow L m) n).obj ≅
      (TauCeti.tensorPow L (m * n)).obj) := by
  rw [← LineBundleClass.mk_eq_mk_iff]
  simp [pow_mul]

/-- **Pullback commutes with tensor powers.** For `f : X ⟶ Y` and a line bundle `L` on `Y`, the
pullback of `L^{⊗n}` is isomorphic to `(f^* L)^{⊗n}`. -/
theorem nonempty_pullback_tensorPow_iso (f : X ⟶ Y) (L : InvertibleSheaf Y) (n : ℕ) :
    Nonempty (((pullback f).obj (TauCeti.tensorPow L n)).obj ≅
      (TauCeti.tensorPow ((pullback f).obj L) n).obj) := by
  rw [← LineBundleClass.mk_eq_mk_iff, ← LineBundleClass.pullback_mk]
  simp

end InvertibleSheaf

end AlgebraicGeometry

end TauCeti
