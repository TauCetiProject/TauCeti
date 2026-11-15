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
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Dimension

/-!
# Homomorphisms determined by their differentials

Two homomorphisms from a connected finite-type affine group over an algebraically closed field
of characteristic zero—or, over any characteristic-zero field, from a geometrically connected
finite-type affine group—agree if their differentials agree. Their scheme-theoretic equalizer
has the full Lie algebra. Cartier's theorem makes it smooth, so `HopfIdeal.finrank_quotientLie_lt`
forces it to be the whole source group.

A homomorphism from a connected finite-type affine group over an algebraically closed field
of characteristic zero (or a geometrically connected one over any characteristic-zero field) is
trivial if its differential at the identity is zero. This follows
by comparing it with the trivial homomorphism, whose differential is zero.

The statement is expressed contravariantly on coordinate Hopf algebras: `f : H ⟶ K`
represents a morphism from `Spec K` to `Spec H`. Triviality is the counit followed by the
unit. No finite-type hypothesis on the target group `Spec H` is needed.

Consequently, over any characteristic-zero field a homomorphism from a geometrically connected
finite-type affine group with nondegenerate Killing form to a commutative affine group is
trivial: its differential maps a perfect Lie algebra to an abelian one. This supplies the
vanishing of commutative images for semisimple groups.

The equalizer comparison uses `HopfIdeal.mem_lieSubalgebra_equalizer_iff` and the smooth
closed-subgroup criterion `HopfIdeal.eq_bot_of_lieSubalgebra_eq_top_of_geometricallyConnected`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
* A. Borel, *Linear Algebraic Groups*, 2nd ed., §7.1.
-/

public section

open CategoryTheory

namespace TauCeti.HopfIdeal

universe u

/-- Over any field of characteristic zero, a closed subgroup scheme of a geometrically connected
finite-type affine group with the full ambient Lie algebra is the whole group (`I = ⊥`). -/
theorem eq_bot_of_lieSubalgebra_eq_top_of_geometricallyConnected
    {k : Type u} [Field k] [CharZero k] {K : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k K]
    (hK : geometricallyConnectedCommHopfAlgProperty k K) (I : HopfIdeal k K)
    (hI : I.lieSubalgebra (B := k) = ⊤) : I = ⊥ := by
  by_contra hne
  let _ : Algebra.Smooth k K :=
    (smoothCommHopfAlgProperty_iff K).mp (smoothCommHopfAlgProperty_of_charZero k K)
  let _ : Algebra.Smooth k (K ⧸ I.toIdeal) := (smoothCommHopfAlgProperty_iff _).mp
    (smoothCommHopfAlgProperty_of_charZero k (_root_.CommHopfAlgCat.of k (K ⧸ I.toIdeal)))
  have hlt := I.finrank_quotientLie_lt hK hne
  rw [(quotientLieEquiv (B := k) I).toLinearEquiv.finrank_eq, hI,
    LieSubalgebra.topEquiv.toLinearEquiv.finrank_eq] at hlt
  exact lt_irrefl _ hlt

end TauCeti.HopfIdeal

namespace CommHopfAlgCat.Hom

universe u

variable {k : Type u} [Field k] [CharZero k] {H K : CommHopfAlgCat.{u} k} [Algebra.FiniteType k K]

/-- Over any field of characteristic zero, two homomorphisms from a geometrically connected
finite-type affine group agree if their differentials at the identity agree. -/
theorem eq_of_derivationCompLieHom_eq_of_geometricallyConnected
    (hK : TauCeti.geometricallyConnectedCommHopfAlgProperty k K) (f g : H ⟶ K)
    (hfg : TauCeti.derivationCompLieHom (B := k) f.hom =
      TauCeti.derivationCompLieHom (B := k) g.hom) : f = g :=
  (TauCeti.CommHopfAlgCat.equalizerHopfIdeal_eq_bot_iff f g).mp <|
    TauCeti.HopfIdeal.eq_bot_of_lieSubalgebra_eq_top_of_geometricallyConnected hK _ <| by
      ext d; simp only [TauCeti.CommHopfAlgCat.equalizerHopfIdeal_def,
        TauCeti.HopfIdeal.mem_lieSubalgebra_equalizer_iff, hfg, LieSubalgebra.mem_top]

/-- Over any field of characteristic zero, a morphism from a geometrically connected finite-type
affine group with zero differential is trivial. -/
theorem eq_unit_comp_counit_of_derivationCompLieHom_eq_zero_of_geometricallyConnected
    (hK : TauCeti.geometricallyConnectedCommHopfAlgProperty k K) (f : H ⟶ K)
    (hf : TauCeti.derivationCompLieHom (B := k) f.hom = 0) :
    f = CommHopfAlgCat.ofHom
      ((Bialgebra.unitBialgHom k K).comp (Bialgebra.counitBialgHom k H)) := by
  apply f.eq_of_derivationCompLieHom_eq_of_geometricallyConnected hK
  rw [hf]; ext d a
  -- Mathlib has no application lemma for `Bialgebra.unitBialgHom`, and the counit zeros are defeq.
  simp [TauCeti.derivationCompLieHom_apply, TauCeti.derivationComp_apply, Bialgebra.unitBialgHom]
  rfl

end CommHopfAlgCat.Hom

namespace TauCeti.CommHopfAlgCat

universe u

/-- **Factorization of a homomorphism into a closed subgroup via Lie algebras (Borel §7.1).** -/
theorem existsUnique_hom_of_surjective_of_derivationCompLieHom_eq
    {k A B : Type u} [Field k] [CharZero k] {K : _root_.CommHopfAlgCat.{u} k}
    [Algebra.FiniteType k K] [CommRing A] [HopfAlgebra k A] [CommRing B] [HopfAlgebra k B]
    (hK : geometricallyConnectedCommHopfAlgProperty k K) (q : A →ₐc[k] B)
    (hq : Function.Surjective q) (ρ : A →ₐc[k] K)
    (L : Derivation k K (Bialgebra.CounitAlgebra k K k) →ₗ⁅k⁆
      Derivation k B (Bialgebra.CounitAlgebra k B k))
    (hdiff : (derivationCompLieHom (B := k) q).comp L = derivationCompLieHom (B := k) ρ) :
    ∃! φ : _root_.CommHopfAlgCat.of k B ⟶ K,
      φ.hom.comp q = ρ ∧ derivationCompLieHom (B := k) φ.hom = L := by
  let I := HopfIdeal.kerOfSurjective q hq
  have hImap : I.map ρ = ⊥ := by
    apply HopfIdeal.eq_bot_of_lieSubalgebra_eq_top_of_geometricallyConnected hK
    rw [eq_top_iff]; rintro d -
    rw [HopfIdeal.lieSubalgebra_map, LieSubalgebra.mem_comap, ← hdiff, LieHom.comp_apply,
      derivationCompLieHom_apply, HopfIdeal.mem_lieSubalgebra_iff]
    intro x hx; apply (Bialgebra.CounitAlgebra.algEquivSelf k A k).injective
    rw [algEquivSelf_derivationComp_apply, BialgHom.coe_toAlgHom,
      (HopfIdeal.mem_kerOfSurjective q hq).mp (HopfIdeal.mem_toIdeal.mp hx), map_zero, map_zero,
      map_zero]
  have hker : I.toIdeal ≤ RingHom.ker ρ.toAlgHom.toRingHom := fun x hx ↦
    RingHom.mem_ker.mpr ((HopfIdeal.map_eq_bot_iff I ρ).mp hImap hx)
  let φ₀ : B →ₐc[k] K := (Bialgebra.Quotient.liftBialgHom I.toIdeal ρ hker).comp
    ((HopfIdeal.kerLiftBialgEquiv q hq).symm : B →ₐc[k] _)
  have hφ₀q : φ₀.comp q = ρ := BialgHom.ext fun x ↦ by
    have hsymm : (HopfIdeal.kerLiftBialgEquiv q hq).symm (q x) = Ideal.Quotient.mk I.toIdeal x :=
      EquivLike.injective (HopfIdeal.kerLiftBialgEquiv q hq) <| by
        rw [(HopfIdeal.kerLiftBialgEquiv q hq).apply_symm_apply,
          HopfIdeal.kerLiftBialgEquiv_apply, HopfIdeal.kerLiftBialgHom_mk]
    rw [BialgHom.comp_apply, BialgHom.comp_apply, BialgEquiv.coe_toBialgHom, hsymm,
      Bialgebra.Quotient.liftBialgHom_mk]
  have hφ₀diff : derivationCompLieHom (B := k) (_root_.CommHopfAlgCat.ofHom φ₀).hom = L := by
    ext d : 1; apply derivationCompLieHom_injective_of_surjective (B := k) q hq
    rw [← LieHom.comp_apply, ← derivationCompLieHom_comp, _root_.CommHopfAlgCat.hom_ofHom, hφ₀q,
      ← hdiff, LieHom.comp_apply]
  exact ⟨_root_.CommHopfAlgCat.ofHom φ₀, ⟨hφ₀q, hφ₀diff⟩, fun φ ⟨_, hφ⟩ ↦
    φ.eq_of_derivationCompLieHom_eq_of_geometricallyConnected hK _ (hφ.trans hφ₀diff.symm)⟩

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {H : _root_.CommHopfAlgCat.{u} k} {K : FiniteTypeCommHopfAlgCat.{u, u} k}
variable [ConnectedSpace (PrimeSpectrum K)]

/-- Two homomorphisms from a connected finite-type affine group over an algebraically closed
field of characteristic zero agree if their differentials at the identity agree. The target
group need not be of finite type. -/
theorem _root_.CommHopfAlgCat.Hom.eq_of_derivationCompLieHom_eq
    (f g : H ⟶ K.obj)
    (hfg : derivationCompLieHom (B := k) f.hom = derivationCompLieHom (B := k) g.hom) :
    f = g :=
  f.eq_of_derivationCompLieHom_eq_of_geometricallyConnected
    ((geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k K.obj).mpr inferInstance) g hfg

/-- Over an algebraically closed field of characteristic zero, a morphism from a connected
finite-type affine group with zero differential is trivial. The target group need not be
of finite type. -/
theorem _root_.CommHopfAlgCat.Hom.eq_unit_comp_counit_of_derivationCompLieHom_eq_zero
    (f : H ⟶ K.obj)
    (hf : derivationCompLieHom (B := k) f.hom = 0) :
    f = _root_.CommHopfAlgCat.ofHom
      ((Bialgebra.unitBialgHom k K).comp (Bialgebra.counitBialgHom k H)) :=
  f.eq_unit_comp_counit_of_derivationCompLieHom_eq_zero_of_geometricallyConnected
    ((geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k K.obj).mpr inferInstance) hf

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
      ((Bialgebra.unitBialgHom k K).comp (Bialgebra.counitBialgHom k H)) :=
  f.eq_unit_comp_counit_of_derivationCompLieHom_eq_zero_of_geometricallyConnected hK
    (LieHom.eq_zero_of_derivedSeries_one_eq_top (derivationCompLieHom (B := k) f.hom)
      (derivedSeries_one_eq_top_of_isKilling k _))

end TauCeti.CommHopfAlgCat
