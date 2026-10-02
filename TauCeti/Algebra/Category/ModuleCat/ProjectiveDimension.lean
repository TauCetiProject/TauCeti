/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.FiniteLength

/-!
# Projective dimension bounds along composition series

A common bound on the projective dimensions of simple modules also bounds every
module of finite length. This lets short resolutions of simple modules control higher
Ext groups of arbitrary finite-length modules, without choosing resolutions of their
successive extensions.

The argument uses Mathlib's extension-closure theorem
`ShortComplex.ShortExact.hasProjectiveDimensionLT_X₂` and the simple-quotient induction
principle of `IsFiniteLength`.

The finite-length induction adapts the formal proof pattern of
`TauCeti.isEulerAdmissible_of_isFiniteLength` in
`TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.FiniteLength`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable {R : Type u} [Ring R]

/-- A bound on the projective dimension of every simple module bounds every module
of finite length. Neither Artinianity of the ring nor finite generation of the ring
over a field is needed. -/
theorem _root_.ModuleCat.hasProjectiveDimensionLT_of_isFiniteLength
    (X : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ S : ModuleCat.{v} R, IsSimpleModule R S → HasProjectiveDimensionLT S n)
    (hX : IsFiniteLength R X) : HasProjectiveDimensionLT X n := by
  suffices key : ∀ (M : Type v) [AddCommGroup M] [Module R M], IsFiniteLength R M →
      HasProjectiveDimensionLT (ModuleCat.of R M) n from key X hX
  intro M _ _ hM
  induction hM with
  | @of_subsingleton M _ _ _ =>
    let _ := (ModuleCat.isZero_of_subsingleton (ModuleCat.of R M)).hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge _ 0 n (Nat.zero_le n)
  | @of_simple_quotient M _ _ N _ _ ih =>
    let T : ShortComplex (ModuleCat.{v} R) :=
      ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ) (by
        ext x
        exact (LinearMap.exact_subtype_mkQ N).apply_apply_eq_zero x)
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T
      (LinearMap.exact_subtype_mkQ N) N.injective_subtype N.mkQ_surjective
    exact hT.hasProjectiveDimensionLT_X₂ n ih
      (h (ModuleCat.of R (M ⧸ N)) inferInstance)

end TauCeti
