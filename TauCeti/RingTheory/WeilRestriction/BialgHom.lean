/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.FiniteStability
public import TauCeti.RingTheory.WeilRestriction.Basic

import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.Algebra.Bialgebra.BaseChange
import TauCeti.Algebra.TensorProduct.BaseChange
import TauCeti.RingTheory.TensorProduct.ComponentIdeal

/-!
# The Hom-scheme of homomorphisms out of a finite locally free monoid scheme

Let `A` be a commutative ring, `H` a commutative `A`-bialgebra that is finitely generated and
projective as an `A`-module, and `H'` a commutative `A`-bialgebra of finite presentation. Thus
`G = Spec H` is a finite locally free affine monoid scheme over `Spec A` (a finite locally free
group scheme when `H` is a Hopf algebra) and `G' = Spec H'` is an affine monoid scheme of finite
presentation. This file constructs a finitely presented `A`-algebra `BialgHomAlgebra A H H'`
representing the functor sending an `A`-algebra `T` to the set of `T`-bialgebra homomorphisms
`T ⊗[A] H' → T ⊗[A] H`, that is, to the set of homomorphisms `G_T → G'_T` of monoid schemes over
`Spec T`. Geometrically, `Spec (BialgHomAlgebra A H H')` is the affine scheme of homomorphisms
`Hom(G, G')`.

The construction specialises the Weil restriction `TauCeti.Algebra.WeilRestriction`. The `T`-points
of the Weil restriction of `H ⊗[A] H'` along `H` are the `A`-algebra homomorphisms
`f : H' → T ⊗[A] H`, that is, the morphisms of schemes `G_T → G'_T`. Such an `f` extends to a
bialgebra homomorphism exactly when it is compatible with the counits and the comultiplications.
At an element `x` of `H'`, compatibility with the counits is an equality in `T`. Compatibility with
the comultiplications is an equality in `T ⊗[A] (H ⊗[A] H)`, cut out by the finitely many components
of the difference (`TensorProduct.componentIdeal`) because `H ⊗[A] H` is finite projective. The
conditions at a finite set of algebra generators of `H'` imply all the others, so they cut out a
finitely generated ideal of the Weil restriction, and `BialgHomAlgebra A H H'` is the quotient by
this ideal.

## Main definitions

* `TauCeti.Algebra.BialgHomAlgebra A H H'`: an `A`-algebra representing
  `T ↦ (T ⊗[A] H' →ₐc[T] T ⊗[A] H)`.
* `TauCeti.Algebra.BialgHomAlgebra.homEquiv A H H' T`: the bijection
  `(BialgHomAlgebra A H H' →ₐ[A] T) ≃ (T ⊗[A] H' →ₐc[T] T ⊗[A] H)`.
* `TauCeti.Algebra.BialgHomAlgebra.universalBialgHom A H H'`: the universal bialgebra
  homomorphism, corresponding to the identity.

## Main results

* `TauCeti.Algebra.BialgHomAlgebra.homEquiv_apply_tmul`: `homEquiv` sends `g` to the base change
  of the universal bialgebra homomorphism along `g`; in particular it is natural in `T`.
* `TauCeti.Algebra.BialgHomAlgebra.hom_ext`: homomorphisms out of `BialgHomAlgebra A H H'` are
  determined by the bialgebra homomorphisms they classify.
* `TauCeti.Algebra.BialgHomAlgebra.instFinitePresentation`: `BialgHomAlgebra A H H'` is of finite
  presentation over `A`.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, §7.6, for the Weil restriction.
-/

public noncomputable section

open Algebra TensorProduct Bialgebra Coalgebra

namespace TauCeti.Algebra

variable {A H H' : Type*} [CommRing A] [CommRing H] [CommRing H'] [Bialgebra A H]
  [Bialgebra A H']

namespace BialgHomAlgebra

variable {T : Type*} [CommRing T] [Algebra A T]

-- `f` composed with the comultiplication of `H`, as a map `H' → T ⊗[A] (H ⊗[A] H)`.
private def comulLeft (f : H' →ₐ[A] T ⊗[A] H) : H' →ₐ[A] T ⊗[A] (H ⊗[A] H) :=
  (Algebra.TensorProduct.map (AlgHom.id A T) (comulAlgHom A H)).comp f

-- The comultiplication of `H'` followed by `f ⊗ f` and the multiplication of `T`, as a map
-- `H' → T ⊗[A] (H ⊗[A] H)`.
private def comulRight (f : H' →ₐ[A] T ⊗[A] H) : H' →ₐ[A] T ⊗[A] (H ⊗[A] H) :=
  (Algebra.TensorProduct.productMap
    ((Algebra.TensorProduct.map (AlgHom.id A T) Algebra.TensorProduct.includeLeft).comp f)
    ((Algebra.TensorProduct.map (AlgHom.id A T) Algebra.TensorProduct.includeRight).comp f)).comp
    (comulAlgHom A H')

-- Moving `(F ⊗ F) ∘ comul` on `1 ⊗ x` to `T ⊗[A] (H ⊗[A] H)`.
private lemma distribBaseChange_symm_map_comul (F : T ⊗[A] H' →ₐ[T] T ⊗[A] H) (x : H') :
    (AlgebraTensorModule.distribBaseChange A T H H).symm
        (Algebra.TensorProduct.map F F (comul (R := T) (1 ⊗ₜ[A] x))) =
      comulRight ((AlgHom.liftEquiv A T H' (T ⊗[A] H)).symm F) x := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, comulRight, AlgHom.comp_apply,
    comulAlgHom_apply]
  induction comul (R := A) x using TensorProduct.inductionOn with
  | add z w hz hw => simp only [tmul_add, map_add, hz, hw]
  | tmul a b => simp [TauCeti.distribBaseChange_symm_tmul_eq_mul]

-- The condition, at the elements of `S ⊆ H'`, for `f : H' →ₐ[A] T ⊗[A] H` to extend to a
-- `T`-bialgebra homomorphism `T ⊗[A] H' → T ⊗[A] H`: compatibility with the counits and with
-- the comultiplications.
private def IsBialgPointOn (S : Set H') (f : H' →ₐ[A] T ⊗[A] H) : Prop :=
  ∀ x ∈ S, counitAlgHom T (T ⊗[A] H) (f x) = algebraMap A T (counit x) ∧
    comulLeft f x = comulRight f x

-- The conditions on a set of algebra generators imply them everywhere.
private lemma isBialgPointOn_univ_of_adjoin_eq_top {S : Set H'} (hS : adjoin A S = ⊤)
    {f : H' →ₐ[A] T ⊗[A] H} (hf : IsBialgPointOn S f) : IsBialgPointOn Set.univ f := by
  have hcounit : ((counitAlgHom T (T ⊗[A] H)).restrictScalars A).comp f =
      (Algebra.ofId A T).comp (counitAlgHom A H') :=
    AlgHom.ext_of_adjoin_eq_top hS fun x hx ↦ by simpa using (hf x hx).1
  have hcomul : comulLeft f = comulRight f :=
    AlgHom.ext_of_adjoin_eq_top hS fun x hx ↦ (hf x hx).2
  exact fun x _ ↦ ⟨by simpa using congr($hcounit x), congr($hcomul x)⟩

variable (A H H' T) in
-- The `T`-bialgebra homomorphisms `T ⊗[A] H' → T ⊗[A] H` are the `A`-algebra homomorphisms
-- `H' → T ⊗[A] H` compatible with the counits and the comultiplications.
private def bialgHomEquiv :
    {f : H' →ₐ[A] T ⊗[A] H // IsBialgPointOn Set.univ f} ≃ (T ⊗[A] H' →ₐc[T] T ⊗[A] H) where
  toFun f := BialgHom.ofAlgHom (AlgHom.liftEquiv A T H' (T ⊗[A] H) f.1)
    (Algebra.TensorProduct.ext_ring <| AlgHom.ext fun x ↦ by
      simpa using (f.2 x trivial).1)
    (Algebra.TensorProduct.ext_ring <| AlgHom.ext fun x ↦
      (AlgebraTensorModule.distribBaseChange A T H H).symm.injective <| by
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
          Algebra.TensorProduct.includeRight_apply, comulAlgHom_apply]
        rw [distribBaseChange_symm_map_comul, TauCeti.Bialgebra.distribBaseChange_symm_comul,
          Equiv.symm_apply_apply, AlgHom.liftEquiv_tmul, one_smul]
        exact ((f.2 x trivial).2).symm)
  invFun F := ⟨(AlgHom.liftEquiv A T H' (T ⊗[A] H)).symm F, fun x _ ↦ by
    refine ⟨by simp [Algebra.smul_def], ?_⟩
    have h := congr((AlgebraTensorModule.distribBaseChange A T H H).symm
      ($(BialgHom.map_comp_comulAlgHom F) (1 ⊗ₜ[A] x)))
    simp only [AlgHom.comp_apply, comulAlgHom_apply, distribBaseChange_symm_map_comul,
      TauCeti.Bialgebra.distribBaseChange_symm_comul] at h
    simpa [comulLeft] using h.symm⟩
  left_inv f := Subtype.ext ((AlgHom.liftEquiv A T H' (T ⊗[A] H)).symm_apply_apply f.1)
  right_inv F := BialgHom.coe_toAlgHom_injective
    ((AlgHom.liftEquiv A T H' (T ⊗[A] H)).apply_symm_apply F.toAlgHom)

private lemma map_comp_comulLeft {W : Type*} [CommRing W] [Algebra A W] (g : W →ₐ[A] T)
    (f : H' →ₐ[A] W ⊗[A] H) :
    (Algebra.TensorProduct.map g (AlgHom.id A (H ⊗[A] H))).comp (comulLeft f) =
      comulLeft ((Algebra.TensorProduct.map g (AlgHom.id A H)).comp f) := by
  simp only [comulLeft, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id,
    AlgHom.id_comp]

private lemma map_comp_comulRight {W : Type*} [CommRing W] [Algebra A W] (g : W →ₐ[A] T)
    (f : H' →ₐ[A] W ⊗[A] H) :
    (Algebra.TensorProduct.map g (AlgHom.id A (H ⊗[A] H))).comp (comulRight f) =
      comulRight ((Algebra.TensorProduct.map g (AlgHom.id A H)).comp f) := by
  -- base change along `g` commutes with maps of the second factor
  have hmap (φ : H →ₐ[A] H ⊗[A] H) :
      (Algebra.TensorProduct.map g (AlgHom.id A (H ⊗[A] H))).comp
          (Algebra.TensorProduct.map (AlgHom.id A W) φ) =
        (Algebra.TensorProduct.map (AlgHom.id A T) φ).comp
          (Algebra.TensorProduct.map g (AlgHom.id A H)) := by
    simp only [← Algebra.TensorProduct.map_comp, AlgHom.comp_id, AlgHom.id_comp]
  rw [comulRight, comulRight, ← AlgHom.comp_assoc]
  congr 1
  refine Algebra.TensorProduct.ext' fun a b ↦ ?_
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.productMap_apply_tmul, map_mul,
    ← AlgHom.comp_apply _ (Algebra.TensorProduct.map (AlgHom.id A W) _), hmap]

section WeilRestriction

variable [Module.Finite A H] [Module.Projective A H] [FinitePresentation A H']

variable (A H H' T) in
-- The `T`-points of the Weil restriction of `H ⊗[A] H'` along `H` are the `A`-algebra
-- homomorphisms `H' → T ⊗[A] H`.
private def pointEquiv :
    (WeilRestriction A H (H ⊗[A] H') →ₐ[A] T) ≃ (H' →ₐ[A] T ⊗[A] H) :=
  (WeilRestriction.homEquiv A H (H ⊗[A] H') T).trans <|
    (AlgHom.liftEquiv A H H' (H ⊗[A] T)).symm.trans <|
      AlgEquiv.arrowCongr AlgEquiv.refl (Algebra.TensorProduct.comm A H T)

-- `pointEquiv` is natural in `T`.
private lemma pointEquiv_comp {T' : Type*} [CommRing T'] [Algebra A T']
    (g : WeilRestriction A H (H ⊗[A] H') →ₐ[A] T) (h : T →ₐ[A] T') :
    pointEquiv A H H' T' (h.comp g) =
      (Algebra.TensorProduct.map h (AlgHom.id A H)).comp (pointEquiv A H H' T g) := by
  ext x
  simp only [pointEquiv, Equiv.trans_apply, WeilRestriction.homEquiv_apply, AlgEquiv.arrowCongr,
    Equiv.coe_fn_mk, AlgHom.comp_apply, AlgHom.liftEquiv_symm_apply]
  -- moving the factor `H` to the right commutes with base change along `h`
  have key (z : H ⊗[A] WeilRestriction A H (H ⊗[A] H')) :
      Algebra.TensorProduct.comm A H T' (Algebra.TensorProduct.lTensor (S := H) H (h.comp g) z) =
        Algebra.TensorProduct.map h (AlgHom.id A H)
          (Algebra.TensorProduct.comm A H T (Algebra.TensorProduct.lTensor (S := H) H g z)) := by
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul a t => simp
  exact key _

variable (A H H') in
-- The universal point of the Weil restriction of `H ⊗[A] H'` along `H`.
private def univPoint : H' →ₐ[A] WeilRestriction A H (H ⊗[A] H') ⊗[A] H :=
  pointEquiv A H H' _ (AlgHom.id A _)

private lemma pointEquiv_eq (g : WeilRestriction A H (H ⊗[A] H') →ₐ[A] T) :
    pointEquiv A H H' T g =
      (Algebra.TensorProduct.map g (AlgHom.id A H)).comp (univPoint A H H') := by
  simpa [univPoint] using pointEquiv_comp (AlgHom.id A _) g

variable (A H H') in
-- The ideal of the Weil restriction cutting out the conditions `IsBialgPointOn S` on the
-- universal point: the counit condition at `x ∈ S` is the vanishing of an element of the Weil
-- restriction, and the comultiplication condition that of an element of its base change to the
-- finite projective module `H ⊗[A] H`.
private def homIdealOn (S : Set H') : Ideal (WeilRestriction A H (H ⊗[A] H')) :=
  Ideal.span (Set.range fun x : S ↦ counitAlgHom _ (_ ⊗[A] H) (univPoint A H H' x) -
      algebraMap A _ (counit (x : H'))) ⊔
    ⨆ x : S, componentIdeal (comulLeft (univPoint A H H') x - comulRight (univPoint A H H') x)

private lemma homIdealOn_le_ker_iff (S : Set H') (g : WeilRestriction A H (H ⊗[A] H') →ₐ[A] T) :
    homIdealOn A H H' S ≤ RingHom.ker g ↔ IsBialgPointOn S (pointEquiv A H H' T g) := by
  rw [pointEquiv_eq]
  simp only [homIdealOn, sup_le_iff, Ideal.span_le, Set.range_subset_iff, iSup_le_iff,
    componentIdeal_le_ker_iff, SetLike.mem_coe, RingHom.mem_ker, IsBialgPointOn,
    Subtype.forall, ← forall₂_and]
  refine forall₂_congr fun x _ ↦ and_congr ?_ ?_
  · rw [map_sub, AlgHom.commutes, sub_eq_zero, AlgHom.comp_apply,
      TauCeti.Bialgebra.counitAlgHom_map]
  · -- on `W ⊗[A] (H ⊗[A] H)`, base change along `g` is `g ⊗ (H ⊗[A] H)`
    have hg (y : WeilRestriction A H (H ⊗[A] H') ⊗[A] (H ⊗[A] H)) :
        g.toLinearMap.rTensor (H ⊗[A] H) y =
          Algebra.TensorProduct.map g (AlgHom.id A (H ⊗[A] H)) y := by
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul w h => simp
    rw [map_sub, sub_eq_zero, hg, hg, ← map_comp_comulLeft, ← map_comp_comulRight,
      AlgHom.comp_apply, AlgHom.comp_apply]

-- The conditions on all of `H'` are cut out by the conditions on a set of generators.
private lemma homIdealOn_univ {S : Set H'} (hS : adjoin A S = ⊤) :
    homIdealOn A H H' Set.univ = homIdealOn A H H' S := by
  -- compare the two ideals through the quotient maps
  have hle {I J : Ideal (WeilRestriction A H (H ⊗[A] H'))}
      (h : I ≤ RingHom.ker (Ideal.Quotient.mkₐ A J)) : I ≤ J :=
    fun a ha ↦ Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using h ha)
  have hker (J : Ideal (WeilRestriction A H (H ⊗[A] H'))) :
      J ≤ RingHom.ker (Ideal.Quotient.mkₐ A J) :=
    fun a ha ↦ by simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  refine le_antisymm (hle ?_) (hle ?_)
  · exact (homIdealOn_le_ker_iff _ _).2 <| isBialgPointOn_univ_of_adjoin_eq_top hS <|
      (homIdealOn_le_ker_iff _ _).1 (hker _)
  · exact (homIdealOn_le_ker_iff _ _).2 fun x _ ↦ (homIdealOn_le_ker_iff _ _).1 (hker _) x trivial

private lemma homIdealOn_univ_fg : (homIdealOn A H H' Set.univ).FG := by
  obtain ⟨s, hs⟩ := FiniteType.out (R := A) (A := H')
  rw [homIdealOn_univ hs]
  exact (Submodule.fg_span (Set.finite_range _)).sup
    (Submodule.fg_iSup _ fun _ ↦ componentIdeal_fg _)

variable (A H H' T) in
-- The universal property of the quotient of the Weil restriction by `homIdealOn A H H' univ`.
private def homEquivAux :
    (WeilRestriction A H (H ⊗[A] H') ⧸ homIdealOn A H H' Set.univ →ₐ[A] T) ≃
      (T ⊗[A] H' →ₐc[T] T ⊗[A] H) where
  toFun φ := bialgHomEquiv A H H' T ⟨pointEquiv A H H' T (φ.comp (Ideal.Quotient.mkₐ A _)),
    (homIdealOn_le_ker_iff _ _).1 fun a ha ↦ by
      simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]⟩
  invFun F := Ideal.Quotient.liftₐ _ ((pointEquiv A H H' T).symm ((bialgHomEquiv A H H' T).symm F))
    fun _ ha ↦ (homIdealOn_le_ker_iff _ _).2 (by simpa using ((bialgHomEquiv A H H' T).symm F).2) ha
  left_inv φ := Ideal.Quotient.algHom_ext A <| by simp [Ideal.Quotient.liftₐ_comp]
  right_inv F := by
    rw [← Equiv.eq_symm_apply]
    exact Subtype.ext <|
      (congrArg _ (Ideal.Quotient.liftₐ_comp _ _ _)).trans (Equiv.apply_symm_apply _ _)

-- The defining formula of `homEquivAux`, unfolding `bialgHomEquiv` and `AlgHom.liftEquiv`.
private lemma homEquivAux_apply_tmul
    (φ : WeilRestriction A H (H ⊗[A] H') ⧸ homIdealOn A H H' Set.univ →ₐ[A] T) (t : T) (x : H') :
    homEquivAux A H H' T φ (t ⊗ₜ x) =
      t • pointEquiv A H H' T (φ.comp (Ideal.Quotient.mkₐ A _)) x :=
  AlgHom.liftEquiv_tmul _ _ _

end WeilRestriction

end BialgHomAlgebra

variable (A H H')
variable [Module.Finite A H] [Module.Projective A H] [FinitePresentation A H']

/-- The **Hom-scheme of homomorphisms** from the affine monoid scheme `Spec H` to `Spec H'` over
`Spec A`, as an `A`-algebra. Here `H` is a commutative `A`-bialgebra that is finite projective as an
`A`-module, so that `Spec H → Spec A` is finite locally free, and `H'` is a commutative
`A`-bialgebra of finite presentation. The algebra `BialgHomAlgebra A H H'` represents the functor
sending an `A`-algebra `T` to the set of `T`-bialgebra homomorphisms `T ⊗[A] H' → T ⊗[A] H`, see
`BialgHomAlgebra.homEquiv`; geometrically, these are the homomorphisms of monoid schemes
`Spec (T ⊗[A] H) → Spec (T ⊗[A] H')` over `Spec T`, and of group schemes when `H` and `H'` are Hopf
algebras. It is a quotient of the Weil restriction of `H ⊗[A] H'` along `H`, which represents all
morphisms of schemes, by the finitely generated ideal expressing compatibility with the counits
and the comultiplications; in particular it is of finite presentation over `A`. -/
def BialgHomAlgebra : Type _ :=
  WeilRestriction A H (H ⊗[A] H') ⧸ BialgHomAlgebra.homIdealOn A H H' Set.univ
deriving CommRing, Algebra A

namespace BialgHomAlgebra

variable (T : Type*) [CommRing T] [Algebra A T]

/-- The universal property of `BialgHomAlgebra A H H'`: the bijection between `A`-algebra
homomorphisms `BialgHomAlgebra A H H' →ₐ[A] T` and `T`-bialgebra homomorphisms
`T ⊗[A] H' →ₐc[T] T ⊗[A] H`. It is natural in `T`, see `BialgHomAlgebra.homEquiv_apply_tmul`. -/
def homEquiv : (BialgHomAlgebra A H H' →ₐ[A] T) ≃ (T ⊗[A] H' →ₐc[T] T ⊗[A] H) :=
  homEquivAux A H H' T

/-- The universal bialgebra homomorphism, corresponding to the identity of `BialgHomAlgebra A H H'`
under `BialgHomAlgebra.homEquiv`. -/
def universalBialgHom :
    BialgHomAlgebra A H H' ⊗[A] H' →ₐc[BialgHomAlgebra A H H'] BialgHomAlgebra A H H' ⊗[A] H :=
  homEquiv A H H' _ (AlgHom.id A _)

variable {A H H' T}

-- The quotient map from the Weil restriction.
private def mk : WeilRestriction A H (H ⊗[A] H') →ₐ[A] BialgHomAlgebra A H H' :=
  Ideal.Quotient.mkₐ A _

-- `homEquiv` is `homEquivAux`, read on the quotient `BialgHomAlgebra A H H'`.
private lemma homEquiv_apply_tmul_mk (g : BialgHomAlgebra A H H' →ₐ[A] T) (t : T) (x : H') :
    homEquiv A H H' T g (t ⊗ₜ x) = t • pointEquiv A H H' T (g.comp mk) x :=
  homEquivAux_apply_tmul g t x

/-- `BialgHomAlgebra.homEquiv` sends `g` to the base change along `g` of the universal bialgebra
homomorphism. -/
@[simp]
theorem homEquiv_apply_tmul (g : BialgHomAlgebra A H H' →ₐ[A] T) (t : T) (x : H') :
    homEquiv A H H' T g (t ⊗ₜ x) =
      t • Algebra.TensorProduct.map g (AlgHom.id A H) (universalBialgHom A H H' (1 ⊗ₜ x)) := by
  rw [universalBialgHom, homEquiv_apply_tmul_mk, homEquiv_apply_tmul_mk, one_smul, AlgHom.id_comp,
    ← AlgHom.comp_apply, ← pointEquiv_comp]

/-- Two `A`-algebra homomorphisms out of `BialgHomAlgebra A H H'` are equal if the base changes of
the universal bialgebra homomorphism along them agree on `H'`, that is, if they classify the same
bialgebra homomorphism under `BialgHomAlgebra.homEquiv`. -/
theorem hom_ext {g₁ g₂ : BialgHomAlgebra A H H' →ₐ[A] T}
    (h : ∀ x : H',
      Algebra.TensorProduct.map g₁ (AlgHom.id A H) (universalBialgHom A H H' (1 ⊗ₜ x)) =
        Algebra.TensorProduct.map g₂ (AlgHom.id A H) (universalBialgHom A H H' (1 ⊗ₜ x))) :
    g₁ = g₂ :=
  (homEquiv A H H' T).injective <| BialgHom.coe_toAlgHom_injective <|
    Algebra.TensorProduct.ext_ring <| AlgHom.ext fun x ↦ by simpa [homEquiv_apply_tmul] using h x

/-- `BialgHomAlgebra A H H'` is of finite presentation over `A`. -/
instance instFinitePresentation : FinitePresentation A (BialgHomAlgebra A H H') :=
  -- `BialgHomAlgebra A H H'` is by definition the quotient of the Weil restriction
  FinitePresentation.quotient homIdealOn_univ_fg

end BialgHomAlgebra

end TauCeti.Algebra
