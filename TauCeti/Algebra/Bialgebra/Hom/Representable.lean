/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import TauCeti.RingTheory.WeilRestriction
import TauCeti.Algebra.Coalgebra.BaseChange

/-!
# The scheme of homomorphisms from a finite locally free monoid scheme

Let `R` be a commutative ring, `G` a commutative `R`-bialgebra that is finitely generated and
projective as an `R`-module, and `H` a commutative `R`-bialgebra of finite presentation. Thus
`Spec G` is an affine monoid scheme that is finite locally free over `Spec R`, and `Spec H` is an
affine monoid scheme of finite presentation over `Spec R`. For an `R`-algebra `T`, homomorphisms of
monoid schemes `Spec (T ⊗[R] G) → Spec (T ⊗[R] H)` over `Spec T` are the `T`-bialgebra
homomorphisms `T ⊗[R] H →ₐc[T] T ⊗[R] G`. This file constructs an `R`-algebra of finite
presentation `TauCeti.Bialgebra.HomAlgebra R H G` representing the functor

```text
T ↦ (T ⊗[R] H →ₐc[T] T ⊗[R] G).
```

When `G` and `H` are Hopf algebras, a bialgebra homomorphism between them commutes with the
antipodes, so `Spec (HomAlgebra R H G)` is the affine scheme of homomorphisms of group schemes
from `Spec G` to `Spec H`.

The construction starts from the Weil restriction `WeilRestriction R G (G ⊗[R] H)`, whose
`T`-points are the `R`-algebra homomorphisms `f : H → T ⊗[R] G`
(`TauCeti.Algebra.WeilRestriction.tensorHomEquiv`), that is, the `T`-algebra homomorphisms
`T ⊗[R] H → T ⊗[R] G`. Compatibility with the counits says that two points of `Spec H` with values
in `T` agree, and compatibility with the comultiplications says that two points of the Weil
restriction along `G ⊗[R] G` agree. Both conditions are therefore equalities between composites
of the classifying map with two fixed algebra homomorphisms, and it suffices to impose them on
finitely many generators. So they cut out a finitely generated ideal of the Weil restriction.

## Main definitions

* `TauCeti.Bialgebra.HomAlgebra R H G`: an `R`-algebra representing the functor
  `T ↦ (T ⊗[R] H →ₐc[T] T ⊗[R] G)`.
* `TauCeti.Bialgebra.HomAlgebra.homEquiv R H G T`: the bijection
  `(HomAlgebra R H G →ₐ[R] T) ≃ (T ⊗[R] H →ₐc[T] T ⊗[R] G)`.

## Main results

* `TauCeti.Bialgebra.HomAlgebra.homEquiv_comp_one_tmul`: `homEquiv` is natural in `T`.
* `TauCeti.Bialgebra.HomAlgebra.instFinitePresentation`: `HomAlgebra R H G` is of finite
  presentation over `R`.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, §7.6, for the Weil restriction.
-/

public noncomputable section

open scoped TensorProduct

open Algebra.TensorProduct (map)

namespace TauCeti.Bialgebra

namespace HomAlgebra

section Conditions

variable {R T H G : Type*} [CommRing R] [CommRing T] [Algebra R T] [CommRing H] [CommRing G]
  [_root_.Bialgebra R H] [_root_.Bialgebra R G]

variable (R T G) in
-- The `R`-algebra homomorphism `(T ⊗[R] G) ⊗[R] (T ⊗[R] G) → T ⊗[R] (G ⊗[R] G)` multiplying the
-- two factors `T`.
private def mulBase : (T ⊗[R] G) ⊗[R] (T ⊗[R] G) →ₐ[R] T ⊗[R] (G ⊗[R] G) :=
  Algebra.TensorProduct.productMap (map (AlgHom.id R T) Algebra.TensorProduct.includeLeft)
    (map (AlgHom.id R T) Algebra.TensorProduct.includeRight)

private lemma mulBase_tmul (a b : T) (x y : G) :
    mulBase R T G ((a ⊗ₜ x) ⊗ₜ (b ⊗ₜ y)) = (a * b) ⊗ₜ (x ⊗ₜ y) := by
  simp [mulBase, Algebra.TensorProduct.productMap_apply_tmul]

-- `mulBase` is natural in `T`.
private lemma map_comp_mulBase {T' : Type*} [CommRing T'] [Algebra R T'] (k : T →ₐ[R] T') :
    (map k (AlgHom.id R (G ⊗[R] G))).comp (mulBase R T G) =
      (mulBase R T' G).comp (map (map k (AlgHom.id R G)) (map k (AlgHom.id R G))) := by
  ext <;> simp [Algebra.TensorProduct.one_def, mulBase_tmul]

-- On the image of `(T ⊗[R] G) ⊗[R] (T ⊗[R] G) → (T ⊗[R] G) ⊗[T] (T ⊗[R] G)`, the inverse of
-- `distribBaseChange` is `mulBase`.
private lemma distribBaseChange_symm_tmul (u v : T ⊗[R] G) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R T G G).symm (u ⊗ₜ[T] v) =
      mulBase R T G (u ⊗ₜ[R] v) := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => simp only [TensorProduct.add_tmul, map_add, hu, hu']
  | tmul a x =>
    induction v using TensorProduct.inductionOn with
    | add v v' hv hv' => simp only [TensorProduct.tmul_add, map_add, hv, hv']
    | tmul b y => simp [mulBase_tmul]

-- `TauCeti.Coalgebra.baseChange_comul`, with the scalar extension of the comultiplication written
-- as an algebra homomorphism.
private lemma comulAlgHom_baseChange (z : T ⊗[R] G) :
    _root_.Bialgebra.comulAlgHom T (T ⊗[R] G) z =
      TensorProduct.AlgebraTensorModule.distribBaseChange R T G G
        (map (AlgHom.id R T) (_root_.Bialgebra.comulAlgHom R G) z) := by
  rw [_root_.Bialgebra.comulAlgHom_apply, TauCeti.Coalgebra.baseChange_comul, LinearMap.comp_apply]
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul a x => simp

-- Compatibility with the comultiplications, restricted to `H`.
private lemma map_comp_comulAlgHom_eq_iff (F : T ⊗[R] H →ₐ[T] T ⊗[R] G) :
    (map F F).comp (_root_.Bialgebra.comulAlgHom T (T ⊗[R] H)) =
        (_root_.Bialgebra.comulAlgHom T (T ⊗[R] G)).comp F ↔
      (mulBase R T G).comp ((map ((AlgHom.liftEquiv R T H _).symm F)
          ((AlgHom.liftEquiv R T H _).symm F)).comp (_root_.Bialgebra.comulAlgHom R H)) =
        (map (AlgHom.id R T) (_root_.Bialgebra.comulAlgHom R G)).comp
          ((AlgHom.liftEquiv R T H _).symm F) := by
  set f := (AlgHom.liftEquiv R T H (T ⊗[R] G)).symm F
  have key (y : H ⊗[R] H) :
      map F F (TensorProduct.AlgebraTensorModule.distribBaseChange R T H H (1 ⊗ₜ y)) =
        TensorProduct.AlgebraTensorModule.distribBaseChange R T G G
          (mulBase R T G (map f f y)) := by
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, ← distribBaseChange_symm_tmul,
        LinearEquiv.apply_symm_apply]
      simp [f]
  -- both sides are determined by their values on `1 ⊗ h`, computed by `key` and
  -- `comulAlgHom_baseChange`
  rw [← (AlgHom.liftEquiv R T H _).symm.injective.eq_iff, AlgHom.ext_iff, AlgHom.ext_iff]
  refine forall_congr' fun h ↦ ?_
  simp only [AlgHom.liftEquiv_symm_apply, AlgHom.comp_apply, comulAlgHom_baseChange]
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, key,
    (TensorProduct.AlgebraTensorModule.distribBaseChange R T G G).injective.eq_iff]
  simp only [f, AlgHom.liftEquiv_symm_apply]

-- Compatibility with the counits, restricted to `H`.
private lemma counitAlgHom_comp_eq_iff (F : T ⊗[R] H →ₐ[T] T ⊗[R] G) :
    (_root_.Bialgebra.counitAlgHom T (T ⊗[R] G)).comp F =
        _root_.Bialgebra.counitAlgHom T (T ⊗[R] H) ↔
      ((_root_.Bialgebra.counitAlgHom T (T ⊗[R] G)).restrictScalars R).comp
          ((AlgHom.liftEquiv R T H _).symm F) =
        (Algebra.ofId R T).comp (_root_.Bialgebra.counitAlgHom R H) := by
  rw [← (AlgHom.liftEquiv R T H T).symm.injective.eq_iff, AlgHom.ext_iff, AlgHom.ext_iff]
  simp [Algebra.algebraMap_eq_smul_one]

end Conditions

section Construction

open Algebra.FiniteType (out)

variable (R H G : Type*) [CommRing R] [CommRing H] [CommRing G] [_root_.Bialgebra R H]
  [_root_.Bialgebra R G] [Algebra.FinitePresentation R H] [Module.Finite R G]
  [Module.Projective R G]

-- The scheme of morphisms `Spec G → Spec H` over `Spec R`: its `T`-points are the algebra
-- homomorphisms `H → T ⊗[R] G`.
private abbrev Ambient := TauCeti.Algebra.WeilRestriction R G (G ⊗[R] H)

-- The scheme of morphisms `Spec (G ⊗[R] G) → Spec H` over `Spec R`, in which the compatibility
-- with the comultiplications is an equation.
private abbrev Ambient₂ := TauCeti.Algebra.WeilRestriction R (G ⊗[R] G) ((G ⊗[R] G) ⊗[R] H)

-- The universal point `H → Ambient ⊗[R] G`.
private def univ : H →ₐ[R] Ambient R H G ⊗[R] G :=
  TauCeti.Algebra.WeilRestriction.tensorHomEquiv R G H _ (AlgHom.id R _)

-- The two sides of the compatibility with the comultiplications, as maps classifying points of
-- `Ambient₂` with values in `Ambient`.
private def comulLeft : Ambient₂ R H G →ₐ[R] Ambient R H G :=
  (TauCeti.Algebra.WeilRestriction.tensorHomEquiv R (G ⊗[R] G) H _).symm
    ((map (AlgHom.id R _) (_root_.Bialgebra.comulAlgHom R G)).comp (univ R H G))

private def comulRight : Ambient₂ R H G →ₐ[R] Ambient R H G :=
  (TauCeti.Algebra.WeilRestriction.tensorHomEquiv R (G ⊗[R] G) H _).symm
    ((mulBase R _ G).comp
      ((map (univ R H G) (univ R H G)).comp (_root_.Bialgebra.comulAlgHom R H)))

-- The two sides of the compatibility with the counits, as points of `H` with values in `Ambient`.
private def counitLeft : H →ₐ[R] Ambient R H G :=
  ((_root_.Bialgebra.counitAlgHom (Ambient R H G) (Ambient R H G ⊗[R] G)).restrictScalars R).comp
    (univ R H G)

private def counitRight : H →ₐ[R] Ambient R H G :=
  (Algebra.ofId R _).comp (_root_.Bialgebra.counitAlgHom R H)

-- The ideal of `Ambient` cut out by the two compatibilities, imposed on finite sets of generators.
private def ideal : Ideal (Ambient R H G) :=
  Ideal.span ((fun x ↦ comulLeft R H G x - comulRight R H G x) '' ↑(out (R := R)
      (A := Ambient₂ R H G)).choose ∪
    (fun h ↦ counitLeft R H G h - counitRight R H G h) '' ↑(out (R := R) (A := H)).choose)

private lemma ideal_fg : (ideal R H G).FG :=
  Submodule.fg_span <| ((Finset.finite_toSet _).image _).union ((Finset.finite_toSet _).image _)

variable {R H G} {T : Type*} [CommRing T] [Algebra R T]

-- Two algebra homomorphisms out of a finite type algebra agree once they agree on the chosen
-- generators.
private lemma comp_eq_comp_iff {A : Type*} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (g : Ambient R H G →ₐ[R] T) (a b : A →ₐ[R] Ambient R H G) :
    (∀ x ∈ (out (R := R) (A := A)).choose, g (a x - b x) = 0) ↔ g.comp a = g.comp b := by
  refine ⟨fun h ↦ AlgHom.ext_of_adjoin_eq_top (out (R := R) (A := A)).choose_spec fun x hx ↦ ?_,
    fun h x _ ↦ by rw [map_sub, sub_eq_zero]; exact AlgHom.congr_fun h x⟩
  simpa [sub_eq_zero] using h x hx

private lemma ideal_le_ker_iff (g : Ambient R H G →ₐ[R] T) :
    ideal R H G ≤ RingHom.ker g ↔ g.comp (comulLeft R H G) = g.comp (comulRight R H G) ∧
      g.comp (counitLeft R H G) = g.comp (counitRight R H G) := by
  simp only [ideal, Ideal.span_le, Set.union_subset_iff, Set.image_subset_iff]
  simp only [Set.subset_def, Set.mem_preimage, SetLike.mem_coe, RingHom.mem_ker]
  rw [← comp_eq_comp_iff, ← comp_eq_comp_iff]

-- The `T`-algebra homomorphism `T ⊗[R] H → T ⊗[R] G` classified by `g`.
private def toAlgHom (g : Ambient R H G →ₐ[R] T) : T ⊗[R] H →ₐ[T] T ⊗[R] G :=
  AlgHom.liftEquiv R T H _ (TauCeti.Algebra.WeilRestriction.tensorHomEquiv R G H T g)

private lemma tensorHomEquiv_eq (g : Ambient R H G →ₐ[R] T) :
    TauCeti.Algebra.WeilRestriction.tensorHomEquiv R G H T g =
      (map g (AlgHom.id R G)).comp (univ R H G) := by
  rw [univ, ← TauCeti.Algebra.WeilRestriction.tensorHomEquiv_comp, AlgHom.comp_id]

private lemma tensorHomEquiv_comp_comulLeft (g : Ambient R H G →ₐ[R] T) :
    TauCeti.Algebra.WeilRestriction.tensorHomEquiv R (G ⊗[R] G) H T (g.comp (comulLeft R H G)) =
      (map (AlgHom.id R T) (_root_.Bialgebra.comulAlgHom R G)).comp
        ((map g (AlgHom.id R G)).comp (univ R H G)) := by
  rw [comulLeft, TauCeti.Algebra.WeilRestriction.tensorHomEquiv_comp, Equiv.apply_symm_apply,
    ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    ← Algebra.TensorProduct.map_comp, AlgHom.comp_id, AlgHom.id_comp, AlgHom.comp_id,
    AlgHom.id_comp]

private lemma tensorHomEquiv_comp_comulRight (g : Ambient R H G →ₐ[R] T) :
    TauCeti.Algebra.WeilRestriction.tensorHomEquiv R (G ⊗[R] G) H T (g.comp (comulRight R H G)) =
      (mulBase R T G).comp ((map ((map g (AlgHom.id R G)).comp (univ R H G))
        ((map g (AlgHom.id R G)).comp (univ R H G))).comp (_root_.Bialgebra.comulAlgHom R H)) := by
  rw [comulRight, TauCeti.Algebra.WeilRestriction.tensorHomEquiv_comp, Equiv.apply_symm_apply,
    ← AlgHom.comp_assoc, map_comp_mulBase, Algebra.TensorProduct.map_comp]
  simp only [AlgHom.comp_assoc]

private lemma comp_counitLeft (g : Ambient R H G →ₐ[R] T) :
    g.comp (counitLeft R H G) =
      ((_root_.Bialgebra.counitAlgHom T (T ⊗[R] G)).restrictScalars R).comp
        ((map g (AlgHom.id R G)).comp (univ R H G)) := by
  have hg : g.comp ((_root_.Bialgebra.counitAlgHom (Ambient R H G)
      (Ambient R H G ⊗[R] G)).restrictScalars R) =
        ((_root_.Bialgebra.counitAlgHom T (T ⊗[R] G)).restrictScalars R).comp
          (map g (AlgHom.id R G)) :=
    Algebra.TensorProduct.ext' fun a x ↦ by simp [Algebra.smul_def]
  rw [counitLeft, ← AlgHom.comp_assoc, hg, AlgHom.comp_assoc]

private lemma comp_counitRight (g : Ambient R H G →ₐ[R] T) :
    g.comp (counitRight R H G) = (Algebra.ofId R T).comp (_root_.Bialgebra.counitAlgHom R H) := by
  ext; simp [counitRight]

-- `g` kills the ideal exactly when the homomorphism it classifies is a bialgebra homomorphism.
private lemma ideal_le_ker_iff_toAlgHom (g : Ambient R H G →ₐ[R] T) :
    ideal R H G ≤ RingHom.ker g ↔
      (_root_.Bialgebra.counitAlgHom T (T ⊗[R] G)).comp (toAlgHom g) =
          _root_.Bialgebra.counitAlgHom T (T ⊗[R] H) ∧
        (map (toAlgHom g) (toAlgHom g)).comp (_root_.Bialgebra.comulAlgHom T (T ⊗[R] H)) =
          (_root_.Bialgebra.comulAlgHom T (T ⊗[R] G)).comp (toAlgHom g) := by
  rw [ideal_le_ker_iff, counitAlgHom_comp_eq_iff, map_comp_comulAlgHom_eq_iff, and_comm,
    ← (TauCeti.Algebra.WeilRestriction.tensorHomEquiv R (G ⊗[R] G) H T).injective.eq_iff,
    tensorHomEquiv_comp_comulLeft, tensorHomEquiv_comp_comulRight, comp_counitLeft,
    comp_counitRight]
  simp only [toAlgHom, Equiv.symm_apply_apply, tensorHomEquiv_eq,
    eq_comm (a := map (AlgHom.id R T) _ |>.comp _)]

private lemma toAlgHom_symm (F : T ⊗[R] H →ₐ[T] T ⊗[R] G) :
    toAlgHom ((TauCeti.Algebra.WeilRestriction.tensorHomEquiv R G H T).symm
      ((AlgHom.liftEquiv R T H _).symm F)) = F := by
  simp [toAlgHom]

variable (R H G) in
-- The representing algebra, before it is wrapped in the irreducible `HomAlgebra`.
private abbrev Rep := Ambient R H G ⧸ ideal R H G

variable (R H G T) in
private def quotEquiv : (Rep R H G →ₐ[R] T) ≃ (T ⊗[R] H →ₐc[T] T ⊗[R] G) where
  toFun g :=
    have hg := (ideal_le_ker_iff_toAlgHom (g.comp (Ideal.Quotient.mkₐ R (ideal R H G)))).1
      fun x hx ↦ by
        rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    BialgHom.ofAlgHom (toAlgHom (g.comp (Ideal.Quotient.mkₐ R (ideal R H G)))) hg.1 hg.2
  invFun F := Ideal.Quotient.liftₐ (ideal R H G)
    ((TauCeti.Algebra.WeilRestriction.tensorHomEquiv R G H T).symm
      ((AlgHom.liftEquiv R T H _).symm F)) fun x hx ↦ by
    refine RingHom.mem_ker.1 ((ideal_le_ker_iff_toAlgHom _).2 ?_ hx)
    rw [toAlgHom_symm]
    exact ⟨BialgHom.counitAlgHom_comp F, BialgHom.map_comp_comulAlgHom F⟩
  left_inv g := Ideal.Quotient.algHom_ext R <| by
    dsimp only
    rw [Ideal.Quotient.liftₐ_comp, Equiv.symm_apply_eq]
    ext h
    simp [toAlgHom]
  right_inv F := BialgHom.coe_toAlgHom_injective <| by
    ext h
    simp [toAlgHom, Ideal.Quotient.liftₐ_comp]

private lemma quotEquiv_comp_one_tmul {T' : Type*} [CommRing T'] [Algebra R T']
    (g : Rep R H G →ₐ[R] T) (k : T →ₐ[R] T') (h : H) :
    quotEquiv R H G T' (k.comp g) (1 ⊗ₜ h) =
      map k (AlgHom.id R G) (quotEquiv R H G T g (1 ⊗ₜ h)) := by
  simp only [quotEquiv, Equiv.coe_fn_mk, BialgHom.ofAlgHom_apply, toAlgHom,
    AlgHom.liftEquiv_tmul, one_smul, TauCeti.Algebra.WeilRestriction.tensorHomEquiv_comp,
    AlgHom.comp_apply]
  rw [← AlgHom.comp_apply (map k _), ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]

end Construction

end HomAlgebra

variable (R H G : Type*) [CommRing R] [CommRing H] [CommRing G] [_root_.Bialgebra R H]
  [_root_.Bialgebra R G] [Algebra.FinitePresentation R H] [Module.Finite R G]
  [Module.Projective R G]

/-- The coordinate ring of the scheme of homomorphisms from the finite locally free monoid scheme
`Spec G` to the monoid scheme `Spec H` of finite presentation: an `R`-algebra representing the
functor sending an `R`-algebra `T` to the set `T ⊗[R] H →ₐc[T] T ⊗[R] G` of `T`-bialgebra
homomorphisms, see `HomAlgebra.homEquiv`. -/
def HomAlgebra : Type _ :=
  HomAlgebra.Rep R H G
deriving CommRing, Algebra R

namespace HomAlgebra

variable (T : Type*) [CommRing T] [Algebra R T]

/-- The universal property of `HomAlgebra R H G`: `R`-algebra homomorphisms
`HomAlgebra R H G →ₐ[R] T` correspond to `T`-bialgebra homomorphisms
`T ⊗[R] H →ₐc[T] T ⊗[R] G`, naturally in `T` (see `HomAlgebra.homEquiv_comp_one_tmul`). -/
def homEquiv : (HomAlgebra R H G →ₐ[R] T) ≃ (T ⊗[R] H →ₐc[T] T ⊗[R] G) :=
  quotEquiv R H G T

variable {R H G T}

/-- Naturality of `HomAlgebra.homEquiv` in the `R`-algebra `T`: for `k : T →ₐ[R] T'`, the
bialgebra homomorphism classified by `k.comp g` is the base change along `k` of the one classified
by `g`. As both are `T'`-linear, it is enough to compare them on `1 ⊗ h`. -/
theorem homEquiv_comp_one_tmul {T' : Type*} [CommRing T'] [Algebra R T']
    (g : HomAlgebra R H G →ₐ[R] T) (k : T →ₐ[R] T') (h : H) :
    homEquiv R H G T' (k.comp g) (1 ⊗ₜ h) =
      map k (AlgHom.id R G) (homEquiv R H G T g (1 ⊗ₜ h)) :=
  quotEquiv_comp_one_tmul g k h

/-- `HomAlgebra R H G` is of finite presentation over `R`. -/
instance instFinitePresentation : Algebra.FinitePresentation R (HomAlgebra R H G) :=
  Algebra.FinitePresentation.quotient (ideal_fg R H G)

end HomAlgebra

end TauCeti.Bialgebra
