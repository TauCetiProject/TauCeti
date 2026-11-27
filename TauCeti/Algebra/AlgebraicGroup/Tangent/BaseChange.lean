/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Base change of the cotangent space at the identity

For a commutative bialgebra `A` over `R`, the cotangent space at the identity
`ω = I ⧸ I ^ 2`, with `I = ker ε` the augmentation ideal, is the conormal module `e^* Ω¹` of the
affine monoid `Spec A` along its identity section `e`; for a Hopf algebra it is the module of
invariant differentials of the affine group `Spec A`. This file proves that its formation
commutes with **every** base change `R → S`: the canonical map
`S ⊗[R] (I ⧸ I ^ 2) → I_S ⧸ I_S ^ 2`, where `I_S` is the augmentation ideal of `S ⊗[R] A`, is an
isomorphism of `S`-modules.

No flatness or finiteness is needed. Mathlib's `Ideal.tensorCotangentEquiv` gives the comparison
for the base change of an arbitrary ideal only when `S` is flat over `R`. For an augmentation ideal
the counit splits `A = R ⊕ I`, and the inverse map is the base change of the universal
displacement `a ↦ [a - ε a]` (`TauCeti.Bialgebra.cotangentMap`), which satisfies the Leibniz rule
for the action through the counit and therefore kills `I_S ^ 2`.

For the coordinate Hopf algebra of a finite locally free group scheme `H` over `Spec R`, this is
the base change isomorphism `ω_H ⊗ O_{S'} ≅ ω_{H_{S'}}` for the conormal module `ω_H = e^* Ω¹`,
along an arbitrary affine `S' = Spec S → Spec R`, including the reduction maps
`O_C → O_C ⧸ p ^ n` used for truncated levels of p-divisible groups.

## Main declarations

* `TauCeti.Bialgebra.cotangentSpaceBaseChangeEquiv`: the `S`-linear equivalence
  `S ⊗[R] CotangentSpace R A ≃ₗ[S] CotangentSpace S (S ⊗[R] A)`.
* `TauCeti.Bialgebra.cotangentSpaceBaseChangeEquiv_tmul_cotangentMap`: the equivalence sends
  `s ⊗ [a - ε a]` to `s • [1 ⊗ a - ε a]`.
* `TauCeti.Bialgebra.cotangentSpaceBaseChangeEquiv_symm_cotangentMap`: its inverse sends the
  class of `w ∈ S ⊗[R] A` to the base change of the universal displacement applied to `w`.
* `TauCeti.Bialgebra.cotangentSpaceBaseChangeEquiv_baseChange_cotangentSpaceMap`: naturality in
  bialgebra morphisms `A → A'`.

## References

* L. Fargues, *La filtration canonique des points de torsion des groupes p-divisibles*,
  Ann. Sci. ÉNS 44 (2011), §2.1.1.
-/

public section

namespace TauCeti

open _root_.Coalgebra TensorProduct

namespace Bialgebra

variable (R S A : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Bialgebra R A]

/-- The base change of the universal displacement satisfies the Leibniz rule for the action of
`S ⊗[R] A` on `S ⊗[R] CotangentSpace R A` through the counit. -/
private lemma baseChange_cotangentMap_mul (x y : S ⊗[R] A) :
    (cotangentMap R A).baseChange S (x * y) =
      counit (R := S) x • (cotangentMap R A).baseChange S y +
        counit (R := S) y • (cotangentMap R A).baseChange S x := by
  induction x with
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx', add_smul, smul_add]; abel
  | tmul s a =>
    induction y with
    | add y y' hy hy' => simp only [mul_add, map_add, hy, hy', add_smul, smul_add]; abel
    | tmul t b =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul,
        cotangentMap_mul, TensorProduct.counit_tmul, CommSemiring.counit_apply, tmul_add,
        ← smul_tmul, smul_tmul', smul_eq_mul, Algebra.smul_def]
      ac_rfl

/-- The inverse of the base change comparison: the base change of the universal displacement,
restricted to the augmentation ideal of `S ⊗[R] A`, kills products and so descends to the
cotangent space. -/
private noncomputable def cotangentSpaceBaseChangeInv :
    CotangentSpace S (S ⊗[R] A) →ₗ[S] S ⊗[R] CotangentSpace R A :=
  Ideal.Cotangent.lift
    (((cotangentMap R A).baseChange S).comp
      ((AugmentationIdeal S (S ⊗[R] A)).subtype.restrictScalars S))
    fun x y => by
      have hx : counit (R := S) (x : S ⊗[R] A) = 0 := by
        simpa using RingHom.mem_ker.mp x.prop
      have hy : counit (R := S) (y : S ⊗[R] A) = 0 := by
        simpa using RingHom.mem_ker.mp y.prop
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.coe_subtype,
        MulMemClass.coe_mul, baseChange_cotangentMap_mul, hx, hy, zero_smul, add_zero]

private lemma cotangentSpaceBaseChangeInv_toCotangent (x : AugmentationIdeal S (S ⊗[R] A)) :
    cotangentSpaceBaseChangeInv R S A ((AugmentationIdeal S (S ⊗[R] A)).toCotangent x) =
      (cotangentMap R A).baseChange S x :=
  Ideal.Cotangent.lift_toCotangent _ _ x

private lemma cotangentSpaceBaseChangeInv_cotangentMap (w : S ⊗[R] A) :
    cotangentSpaceBaseChangeInv R S A (cotangentMap S (S ⊗[R] A) w) =
      (cotangentMap R A).baseChange S w := by
  rw [cotangentMap_apply, cotangentSpaceBaseChangeInv_toCotangent]
  simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]

/-- The `R`-linear comparison `CotangentSpace R A → CotangentSpace S (S ⊗[R] A)` induced by
`a ↦ 1 ⊗ a`, which sends the augmentation ideal of `A` into that of `S ⊗[R] A`. -/
private noncomputable def cotangentSpaceToBaseChange :
    CotangentSpace R A →ₗ[R] CotangentSpace S (S ⊗[R] A) :=
  Ideal.mapCotangent _ _ (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) fun a ha ↦ by
    have ha : counit (R := R) a = 0 := by simpa using RingHom.mem_ker.mp ha
    simp [RingHom.mem_ker, ha]

private lemma cotangentSpaceToBaseChange_cotangentMap (a : A) :
    cotangentSpaceToBaseChange R S A (cotangentMap R A a) =
      cotangentMap S (S ⊗[R] A) ((1 : S) ⊗ₜ[R] a) := by
  rw [cotangentMap_apply, cotangentMap_apply, cotangentSpaceToBaseChange,
    Ideal.mapCotangent_toCotangent]
  congr 1
  ext
  simp only [map_sub, AlgHom.commutes, Algebra.TensorProduct.includeRight_apply,
    TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def, mul_one,
    ← IsScalarTower.algebraMap_apply]

/-- The forward comparison applied to the base change of the universal displacement of `w` is the
universal displacement of `w` in `S ⊗[R] A`. -/
private lemma liftBaseChange_baseChange_cotangentMap (w : S ⊗[R] A) :
    (cotangentSpaceToBaseChange R S A).liftBaseChange S ((cotangentMap R A).baseChange S w) =
      cotangentMap S (S ⊗[R] A) w := by
  induction w with
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | tmul s a =>
    rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul,
      cotangentSpaceToBaseChange_cotangentMap, ← LinearMap.map_smul, smul_tmul', smul_eq_mul,
      mul_one]

/-- **Base change of the cotangent space at the identity.** For a commutative bialgebra `A` over
`R` and any commutative `R`-algebra `S`, the cotangent space at the identity of `S ⊗[R] A` over
`S` is the base change of that of `A`. On generators, `s ⊗ [a - ε a]` corresponds to
`s • [1 ⊗ a - ε a]` (`TauCeti.Bialgebra.cotangentSpaceBaseChangeEquiv_tmul_cotangentMap`).
Unlike `Ideal.tensorCotangentEquiv`, no flatness of `S` over `R` is needed. -/
noncomputable def cotangentSpaceBaseChangeEquiv :
    S ⊗[R] CotangentSpace R A ≃ₗ[S] CotangentSpace S (S ⊗[R] A) :=
  LinearEquiv.ofLinearMap ((cotangentSpaceToBaseChange R S A).liftBaseChange S)
    (cotangentSpaceBaseChangeInv R S A)
    (by
      ext c
      obtain ⟨x, rfl⟩ := (AugmentationIdeal S (S ⊗[R] A)).toCotangent_surjective c
      simp [cotangentSpaceBaseChangeInv_toCotangent, liftBaseChange_baseChange_cotangentMap,
        cotangentMap_augmentation])
    (by
      refine AlgebraTensorModule.ext fun s c => ?_
      obtain ⟨a, rfl⟩ := cotangentMap_surjective R A c
      simp [cotangentSpaceToBaseChange_cotangentMap, cotangentSpaceBaseChangeInv_cotangentMap,
        smul_tmul'])

/-- The base change comparison sends `s ⊗ [a - ε a]` to `s • [1 ⊗ a - ε a]`. -/
@[simp]
theorem cotangentSpaceBaseChangeEquiv_tmul_cotangentMap (s : S) (a : A) :
    cotangentSpaceBaseChangeEquiv R S A (s ⊗ₜ cotangentMap R A a) =
      s • cotangentMap S (S ⊗[R] A) ((1 : S) ⊗ₜ[R] a) := by
  rw [cotangentSpaceBaseChangeEquiv, LinearEquiv.coe_ofLinearMap, LinearMap.liftBaseChange_tmul,
    cotangentSpaceToBaseChange_cotangentMap]

/-- The inverse of the base change comparison sends the class of `w ∈ S ⊗[R] A` to the base change
of the universal displacement applied to `w`. This characterizes the comparison, since the
classes of elements of `S ⊗[R] A` exhaust its cotangent space. -/
@[simp]
theorem cotangentSpaceBaseChangeEquiv_symm_cotangentMap (w : S ⊗[R] A) :
    (cotangentSpaceBaseChangeEquiv R S A).symm (cotangentMap S (S ⊗[R] A) w) =
      (cotangentMap R A).baseChange S w := by
  rw [LinearEquiv.symm_apply_eq, cotangentSpaceBaseChangeEquiv, LinearEquiv.coe_ofLinearMap,
    liftBaseChange_baseChange_cotangentMap]

/-- The base change comparison sends the base change of the universal displacement to the
universal displacement of `S ⊗[R] A`. -/
@[simp]
theorem cotangentSpaceBaseChangeEquiv_baseChange_cotangentMap (w : S ⊗[R] A) :
    cotangentSpaceBaseChangeEquiv R S A ((cotangentMap R A).baseChange S w) =
      cotangentMap S (S ⊗[R] A) w := by
  rw [← cotangentSpaceBaseChangeEquiv_symm_cotangentMap, LinearEquiv.apply_symm_apply]

section Map

variable {R S A} {A' : Type*} [CommRing A'] [Bialgebra R A']

/-- **Naturality of the base change comparison.** For a bialgebra morphism `φ : A → A'`, the base
change of the cotangent map of `φ` corresponds to the cotangent map of the base-changed morphism
`S ⊗[R] A → S ⊗[R] A'`. -/
theorem cotangentSpaceBaseChangeEquiv_baseChange_cotangentSpaceMap (φ : A →ₐc[R] A')
    (z : S ⊗[R] CotangentSpace R A) :
    cotangentSpaceBaseChangeEquiv R S A' ((cotangentSpaceMap φ).baseChange S z) =
      cotangentSpaceMap (_root_.Bialgebra.TensorProduct.map (BialgHom.id S S) φ)
        (cotangentSpaceBaseChangeEquiv R S A z) := by
  induction z with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul s c =>
    obtain ⟨a, rfl⟩ := cotangentMap_surjective R A c
    simp [_root_.Bialgebra.TensorProduct.map_tmul]

end Map

end Bialgebra

end TauCeti
