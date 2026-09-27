/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology

/-!
# Cup products of mod-two Kummer classes

For a field `K` in which `2` is invertible, multiplication in `𝔽₂` gives a pairing on the
trivial coefficient object. Composing its degree-`(1,1)` cup product with the Kummer isomorphism
gives the bilinear pairing

```text
Kˣ/(Kˣ)² × Kˣ/(Kˣ)² → H²(G_K, 𝔽₂),   ([a], [b]) ↦ [a] ⌣ [b].
```

The source is the additive square-class group `TauCeti.SquareClassGroup K`; consequently
biadditivity and invariance under changing representatives are carried by the type. The
representative formula `TauCeti.kummerCup_squareClass_squareClass` identifies this pairing with
the cup of the classes constructed in `TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic`.

## Main definitions

* `TauCeti.trivialF2TopPairing`: multiplication on the trivial integral `𝔽₂` coefficient object.
* `TauCeti.kummerCup`: the bilinear cup pairing on square classes.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (6.2.2).
-/

public section

noncomputable section

namespace TauCeti

open _root_.ContinuousCohomology

universe u

variable (G : Type u) [Monoid G]

/-- Multiplication on the trivial `𝔽₂` coefficient object, as a continuous equivariant
pairing over `ℤ`. This is the coefficient pairing used by the mod-two Kummer cup. -/
noncomputable def trivialF2TopPairing :
    TopPairing (trivialF2 G) (trivialF2 G) (trivialF2 G) := by
  let intModule : Module ℤ (trivialF2 G).V := (trivialF2 G).hV2
  letI := intModule
  exact
    { bil := LinearMap.mk₂ ℤ
        (fun x y ↦ trivialF2Pairing G x y)
        (fun x y z ↦ DFunLike.congr_fun
          (map_add (trivialF2Pairing G) x y) z)
        (fun n x y ↦ by
          -- `TopRep` stores a particular integral module instance. Naming it here lets us
          -- expose its scalar action as the underlying additive group's `zsmul`.
          change (trivialF2Pairing G) (intModule.smul n x) y =
            intModule.smul n (trivialF2Pairing G x y)
          rw [int_smul_eq_zsmul intModule, int_smul_eq_zsmul intModule]
          exact DFunLike.congr_fun (map_zsmul (trivialF2Pairing G) n x) y)
        (fun x y z ↦ map_add (trivialF2Pairing G x) y z)
        (fun n x y ↦ by
          -- As above, expose the stored integral action in terms of `zsmul` before applying
          -- additivity of the second-variable homomorphism.
          change (trivialF2Pairing G x) (intModule.smul n y) =
            intModule.smul n (trivialF2Pairing G x y)
          rw [int_smul_eq_zsmul intModule, int_smul_eq_zsmul intModule]
          exact map_zsmul (trivialF2Pairing G x) n y)
      cont := continuous_of_discreteTopology
      equivariant g x y := by
        rw [LinearMap.mk₂_apply]
        exact trivialF2Pairing_smul_smul G g x y }

/-- The coefficient pairing decodes as multiplication in `ZMod 2`. -/
@[simp]
theorem trivialF2Equiv_trivialF2TopPairing (x y : (trivialF2 G).V) :
    trivialF2Equiv G ((trivialF2TopPairing G).bil x y) =
      trivialF2Equiv G x * trivialF2Equiv G y := by
  rw [trivialF2TopPairing, LinearMap.mk₂_apply, trivialF2Pairing_apply,
    AddEquiv.apply_symm_apply]

variable (K : Type u) [Field K] [Invertible (2 : K)]

/-- **The mod-two Kummer cup pairing on square classes.** It sends `([a], [b])` to the cup
product of their Kummer classes in `H²(G_K, 𝔽₂)`. -/
noncomputable def kummerCup :
    SquareClassGroup K →+ SquareClassGroup K →+
      continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K)) where
  toFun x :=
    { toFun := fun y ↦ (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerSquareClassEquiv K x) (kummerSquareClassEquiv K y)
      map_zero' := by simp
      map_add' := by simp }
  map_zero' := by
    ext y
    simp
  map_add' x y := by
    ext z
    simp

/-- The Kummer cup pairing is the cup product after applying the square-class Kummer
isomorphism in both variables. -/
theorem kummerCup_apply (x y : SquareClassGroup K) :
    kummerCup K x y = (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
      (kummerSquareClassEquiv K x) (kummerSquareClassEquiv K y) :=
  (rfl)

/-- The Kummer cup on representatives is the cup product of their Kummer classes. -/
@[simp]
theorem kummerCup_squareClass_squareClass (a b : Kˣ) :
    kummerCup K (squareClass a) (squareClass b) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass a) (kummerClass b) := by
  rw [kummerCup_apply, kummerSquareClassEquiv_squareClass, kummerSquareClassEquiv_squareClass]

end TauCeti
