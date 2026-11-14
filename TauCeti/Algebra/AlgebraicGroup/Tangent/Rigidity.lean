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
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange

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

Over an arbitrary field of characteristic zero, scalar extension to the algebraic closure extends
both rigidity principles to geometrically connected finite-type affine groups: morphisms are
determined by their differentials, and any closed subgroup scheme with the full Lie algebra is the
whole group. Consequently, a homomorphism from a geometrically connected finite-type affine group
with nondegenerate Killing form to a commutative affine group is trivial.

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

open scoped TensorProduct

universe u

variable {k : Type u} [Field k] [CharZero k]
variable {H : _root_.CommHopfAlgCat.{u} k} {K : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Over any field of characteristic zero, two homomorphisms from a geometrically connected
finite-type affine group agree if their differentials at the identity agree. Neither algebraic
closure of `k` nor finite generation of the target coordinate Hopf algebra `H` is needed. -/
theorem _root_.CommHopfAlgCat.Hom.eq_of_derivationCompLieHom_eq_of_geometricallyConnected
    (hK : geometricallyConnectedCommHopfAlgProperty k K.obj) (f g : H ⟶ K.obj)
    (hfg : derivationCompLieHom (B := k) f.hom = derivationCompLieHom (B := k) g.hom) :
    f = g := by
  let F := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := F) K
  let _ : ConnectedSpace (PrimeSpectrum G) := hK.connectedSpace_algebraicClosureBaseChange
  apply baseChangeMap_injective_hom (K := F) (algebraMap k F).injective
  apply _root_.CommHopfAlgCat.Hom.eq_of_derivationCompLieHom_eq (K := G)
  ext d y
  obtain ⟨z, rfl⟩ := (Derivation.tangentScalarExtensionEquiv (R := k) (A := K) (B := F)).trans
    (tangentBaseChangeLieEquiv (R := k) (K := F) (H := K)).toLinearEquiv |>.surjective d
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ =>
      simpa only [map_add, add_apply] using congrArg₂ (· + ·) hz₁ hz₂
  | tmul a w =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ hy₁ hy₂ => simpa only [map_add] using congrArg₂ (· + ·) hy₁ hy₂
      | tmul b h =>
          apply (Bialgebra.CounitAlgebra.algEquivSelf F (F ⊗[k] H) F).injective
          have eval_map (φ : H ⟶ K.obj) :
              Bialgebra.CounitAlgebra.algEquivSelf F (F ⊗[k] H) F
                ((derivationCompLieHom (B := F) (baseChangeMap (K := F) φ).hom
                  (tangentBaseChangeLieEquiv (Derivation.tangentScalarExtensionEquiv (a ⊗ₜ[k] w))))
                  (b ⊗ₜ[k] h)) =
                b * (a * algebraMap k F (Bialgebra.CounitAlgebra.algEquivSelf k H k
                  (derivationCompLieHom (B := k) φ.hom
                    (Derivation.cotangentLinearEquiv (R := k) (A := K) (B := k) w) h))) := by
            rw [derivationCompLieHom_apply, algEquivSelf_derivationComp_apply,
              BialgHom.coe_toAlgHom, baseChangeMap_apply_tmul, tangentBaseChangeLieEquiv_tmul,
              AlgEquiv.apply_symm_apply,
              Derivation.algEquivSelf_tangentScalarExtensionEquiv_tmul_apply,
              derivationCompLieHom_apply, algEquivSelf_derivationComp_apply,
              Derivation.algEquivSelf_cotangentLinearEquiv_apply, BialgHom.coe_toAlgHom]
          simp only [LinearEquiv.trans_apply, LieEquiv.coe_toLinearEquiv]
          rw [eval_map f, eval_map g, hfg]

/-- Over any field of characteristic zero, a closed subgroup scheme of a geometrically connected
finite-type affine group whose Lie algebra is the full ambient Lie algebra is the whole group
(`I = ⊥`). Cartier's theorem supplies smoothness over the algebraic closure, and faithful flatness
descends equality of Hopf ideals. -/
theorem _root_.TauCeti.HopfIdeal.eq_bot_of_lieSubalgebra_eq_top_of_geometricallyConnected
    (hK : geometricallyConnectedCommHopfAlgProperty k K.obj) (I : HopfIdeal k K)
    (hI : I.lieSubalgebra (B := k) = ⊤) : I = ⊥ := by
  let F := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := F) K
  let IF : HopfIdeal F G := baseChangeHopfIdeal (K := F) (H := K.obj) I
  let _ : ConnectedSpace (PrimeSpectrum G) := hK.connectedSpace_algebraicClosureBaseChange
  let _ : Algebra.Smooth F (G ⧸ IF.toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero F
      (_root_.CommHopfAlgCat.of F (G ⧸ IF.toIdeal)))
  have hIF : IF = ⊥ := by
    apply HopfIdeal.eq_bot_of_lieSubalgebra_eq_top (H := G) IF
    rw [eq_top_iff]
    rintro d -
    have hspan : IF.toIdeal =
        Ideal.span ((Algebra.TensorProduct.includeRight : K →ₐ[k] F ⊗[k] K) ''
          (I.toIdeal : Set K)) := by
      rw [baseChangeHopfIdeal_toIdeal, Ideal.map]
    rw [HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span IF hspan]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := (Derivation.tangentScalarExtensionEquiv (R := k) (A := K) (B := F)).trans
      (tangentBaseChangeLieEquiv (R := k) (K := F) (H := K)).toLinearEquiv |>.surjective d
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ =>
        simpa only [map_add, add_apply, add_zero] using congrArg₂ (· + ·) hz₁ hz₂
    | tmul a w =>
        apply (Bialgebra.CounitAlgebra.algEquivSelf F (F ⊗[k] K) F).injective
        simp only [LinearEquiv.trans_apply, LieEquiv.coe_toLinearEquiv, map_zero,
          Algebra.TensorProduct.includeRight_apply]
        rw [tangentBaseChangeLieEquiv_tmul, AlgEquiv.apply_symm_apply, one_mul,
          Derivation.algEquivSelf_tangentScalarExtensionEquiv_tmul_apply,
          ← Derivation.algEquivSelf_cotangentLinearEquiv_apply]
        have hw : Derivation.cotangentLinearEquiv (R := k) (A := K) (B := k) w ∈
            I.lieSubalgebra (B := k) := hI ▸ LieSubalgebra.mem_top _
        have hwx : Derivation.cotangentLinearEquiv (R := k) (A := K) (B := k) w x = 0 :=
          (HopfIdeal.mem_lieSubalgebra_iff _ _).mp hw x hx
        rw [hwx, map_zero, map_zero, mul_zero]
  apply baseChangeHopfIdeal_injective (K := F) (H := K.obj)
  refine hIF.trans (HopfIdeal.ext fun y ↦ ?_).symm
  rw [← HopfIdeal.mem_toIdeal, ← HopfIdeal.mem_toIdeal, baseChangeHopfIdeal_toIdeal,
    HopfIdeal.bot_toIdeal, HopfIdeal.bot_toIdeal, Ideal.map_bot]

/-- **Factorization of a homomorphism into a closed subgroup via Lie algebras (Borel §7.1).** Over
any field of characteristic zero, let `q : A →ₐc[k] B` be a surjective bialgebra morphism between
commutative Hopf algebras (a closed immersion `Spec B ↪ Spec A`) and let `ρ : A →ₐc[k] K.obj` be a
homomorphism from a geometrically connected finite-type affine group `Spec K` into `Spec A`. If
`derivationCompLieHom ρ` factors through `derivationCompLieHom q` via a Lie algebra morphism `L`,
then `ρ` factors through `q` via a unique group morphism `φ : B ⟶ K.obj`, and `φ` has differential
`L`. -/
theorem existsUnique_hom_of_surjective_of_derivationCompLieHom_eq
    {A B : Type u} [CommRing A] [HopfAlgebra k A] [CommRing B] [HopfAlgebra k B]
    (hK : geometricallyConnectedCommHopfAlgProperty k K.obj)
    (q : A →ₐc[k] B) (hq : Function.Surjective q) (ρ : A →ₐc[k] K.obj)
    (L : Derivation k K (Bialgebra.CounitAlgebra k K k) →ₗ⁅k⁆
      Derivation k B (Bialgebra.CounitAlgebra k B k))
    (hdiff : (derivationCompLieHom (B := k) q).comp L = derivationCompLieHom (B := k) ρ) :
    ∃! φ : _root_.CommHopfAlgCat.of k B ⟶ K.obj,
      derivationCompLieHom (B := k) φ.hom = L := by
  let I := HopfIdeal.kerOfSurjective q hq
  have hImap : I.map ρ = ⊥ := by
    apply HopfIdeal.eq_bot_of_lieSubalgebra_eq_top_of_geometricallyConnected hK
    rw [eq_top_iff]
    rintro d -
    rw [HopfIdeal.lieSubalgebra_map, LieSubalgebra.mem_comap, ← hdiff, LieHom.comp_apply,
      derivationCompLieHom_apply, HopfIdeal.mem_lieSubalgebra_iff]
    intro x hx
    have hqx : q x = 0 := (HopfIdeal.mem_kerOfSurjective q hq).mp (HopfIdeal.mem_toIdeal.mp hx)
    apply (Bialgebra.CounitAlgebra.algEquivSelf k A k).injective
    rw [algEquivSelf_derivationComp_apply, BialgHom.coe_toAlgHom, hqx, map_zero, map_zero,
      map_zero]
  have hker : I.toIdeal ≤ RingHom.ker ρ.toAlgHom.toRingHom := fun x hx ↦
    RingHom.mem_ker.mpr ((HopfIdeal.map_eq_bot_iff I ρ).mp hImap hx)
  let φ₀ : B →ₐc[k] K.obj :=
    (Bialgebra.Quotient.liftBialgHom I.toIdeal ρ hker).comp
      ((HopfIdeal.kerLiftBialgEquiv q hq).symm : B →ₐc[k] _)
  have hφ₀q : φ₀.comp q = ρ := by
    ext x
    have hsymm : (HopfIdeal.kerLiftBialgEquiv q hq).symm (q x) =
        Ideal.Quotient.mk I.toIdeal x := by
      apply EquivLike.injective (HopfIdeal.kerLiftBialgEquiv q hq)
      rw [(HopfIdeal.kerLiftBialgEquiv q hq).apply_symm_apply,
        HopfIdeal.kerLiftBialgEquiv_apply, HopfIdeal.kerLiftBialgHom_mk]
    rw [BialgHom.comp_apply, BialgHom.comp_apply, BialgEquiv.coe_toBialgHom, hsymm,
      Bialgebra.Quotient.liftBialgHom_mk]
  have hφ₀diff : derivationCompLieHom (B := k) (_root_.CommHopfAlgCat.ofHom φ₀).hom = L := by
    ext d : 1
    apply derivationCompLieHom_injective_of_surjective (B := k) q hq
    rw [← LieHom.comp_apply, ← derivationCompLieHom_comp, _root_.CommHopfAlgCat.hom_ofHom, hφ₀q,
      ← hdiff, LieHom.comp_apply]
  exact ⟨_root_.CommHopfAlgCat.ofHom φ₀, hφ₀diff, fun φ hφ ↦
    _root_.CommHopfAlgCat.Hom.eq_of_derivationCompLieHom_eq_of_geometricallyConnected hK φ _
      (hφ.trans hφ₀diff.symm)⟩

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
