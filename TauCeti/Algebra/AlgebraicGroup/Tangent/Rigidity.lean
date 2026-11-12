/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.LieAlgebra
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.BaseChange
public import TauCeti.Algebra.Lie.Killing.Perfect

/-!
# Homomorphisms determined by their differentials

Two homomorphisms from a connected finite-type affine group over an algebraically closed field
of characteristic zero agree if their differentials agree. Their scheme-theoretic equalizer
has the full Lie algebra. Cartier's theorem makes it smooth, so it is the whole source group.

A homomorphism from a connected finite-type affine group over an algebraically closed field
of characteristic zero is trivial if its differential at the identity is zero. This follows
by comparing it with the trivial homomorphism, whose differential is zero.

The statement is expressed contravariantly on coordinate Hopf algebras: `f : H ⟶ K`
represents a morphism from `Spec K` to `Spec H`. Triviality is the counit followed by the
unit. No finite-type hypothesis on the target group `Spec H` is needed.

Consequently, over any characteristic-zero field a homomorphism from a geometrically connected
finite-type affine group with nondegenerate Killing form to a commutative affine group is
trivial: its differential maps a perfect Lie algebra to an abelian one. This supplies the
vanishing of commutative images for semisimple groups.

The equalizer comparison uses `HopfIdeal.mem_lieSubalgebra_equalizer_iff` and the smooth
closed-subgroup criterion `HopfIdeal.eq_bot_of_lieSubalgebra_eq_top`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {H : _root_.CommHopfAlgCat.{u} k} {K : FiniteTypeCommHopfAlgCat.{u, u} k}
variable [ConnectedSpace (PrimeSpectrum K)]

/-- Two homomorphisms from a connected finite-type affine group over an algebraically closed
field of characteristic zero agree if their differentials at the identity agree. The target
group need not be of finite type. -/
theorem _root_.CommHopfAlgCat.Hom.eq_of_derivationCompLieHom_eq
    (f g : H ⟶ K.obj)
    (hfg : derivationCompLieHom (B := k) f.hom = derivationCompLieHom (B := k) g.hom) :
    f = g := by
  let _ : Algebra.Smooth k K :=
    (smoothCommHopfAlgProperty_iff K.obj).mp (smoothCommHopfAlgProperty_of_charZero k K.obj)
  let I := equalizerHopfIdeal f g
  let _ : Algebra.Smooth k (K ⧸ I.toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k
      (_root_.CommHopfAlgCat.of k (K ⧸ I.toIdeal)))
  apply (equalizerHopfIdeal_eq_bot_iff f g).mp
  apply HopfIdeal.eq_bot_of_lieSubalgebra_eq_top I
  ext d
  simp only [I, equalizerHopfIdeal_def, HopfIdeal.mem_lieSubalgebra_equalizer_iff,
    hfg, LieSubalgebra.mem_top]

/-- Over an algebraically closed field of characteristic zero, a morphism from a connected
finite-type affine group with zero differential is trivial. The target group need not be
of finite type. -/
theorem _root_.CommHopfAlgCat.Hom.eq_unit_comp_counit_of_derivationCompLieHom_eq_zero
    (f : H ⟶ K.obj)
    (hf : derivationCompLieHom (B := k) f.hom = 0) :
    f = _root_.CommHopfAlgCat.ofHom
      ((Bialgebra.unitBialgHom k K).comp (Bialgebra.counitBialgHom k H)) := by
  apply f.eq_of_derivationCompLieHom_eq
  rw [hf]
  ext d a
  -- Mathlib has no application lemma for the unit bialgebra morphism.
  simp [derivationCompLieHom_apply, derivationComp_apply, Bialgebra.unitBialgHom]
  -- The remaining zeros use different counit coefficient synonyms.
  rfl

end TauCeti.CommHopfAlgCat

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k] [CharZero k]
variable {H : _root_.CommHopfAlgCat.{u} k} {K : FiniteTypeCommHopfAlgCat.{u, u} k}
variable [Coalgebra.IsCocomm k H]

/-- A homomorphism from a geometrically connected affine group with nondegenerate Killing form
to a commutative affine group is trivial in characteristic zero. The target group need not
be of finite type. -/
theorem eq_unit_comp_counit_of_isKilling
    [LieAlgebra.IsKilling k (Derivation k K (Bialgebra.CounitAlgebra k K k))]
    (hK : geometricallyConnectedCommHopfAlgProperty k K.obj) (f : H ⟶ K.obj) :
    f = _root_.CommHopfAlgCat.ofHom
      ((Bialgebra.unitBialgHom k K).comp (Bialgebra.counitBialgHom k H)) := by
  let F := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := F) K
  let _ : ConnectedSpace (PrimeSpectrum G) := hK.connectedSpace_algebraicClosureBaseChange
  let _ : LieAlgebra.IsKilling F
      (Derivation F G (Bialgebra.CounitAlgebra F G F)) :=
    (isKilling_lie_baseChange_iff (k := k) (K := F) (H := K)).mpr inferInstance
  have hf := _root_.CommHopfAlgCat.Hom.eq_unit_comp_counit_of_derivationCompLieHom_eq_zero
    (K := G) (baseChangeMap (K := F) f)
    (LieHom.eq_zero_of_derivedSeries_one_eq_top
      (derivationCompLieHom (B := F) (baseChangeMap (K := F) f).hom)
      (derivedSeries_one_eq_top_of_isKilling F _))
  apply baseChangeMap_injective_hom (K := F) (algebraMap k F).injective
  rw [baseChangeMap_unit_comp_counit]
  exact hf

end TauCeti.CommHopfAlgCat
