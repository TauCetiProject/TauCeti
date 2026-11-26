/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.ClassFunction.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Conjugation.Basic
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra

import TauCeti.Algebra.TensorProduct.MapLinear

/-!
# The conjugation action of an affine group on itself as a comodule algebra

Let `H` be a commutative Hopf algebra over a commutative semiring `R`, the coordinate ring of the
affine group `G = Spec H`. The group `G` acts on itself on the right by conjugation,
`(x, g) ↦ g⁻¹ * x * g`. This file records that action as a right comodule algebra structure on
`H` over itself (`TauCeti.HopfAlgebra.conjugationComoduleAlgebra`), and names its coinvariants:
the **conjugation-invariant functions** `O(G)^G`
(`TauCeti.HopfAlgebra.conjugationInvariants`), the coordinate ring of the conjugation quotient
`G // G`.

The left-action coordinate morphism `TauCeti.HopfAlgebra.conjugationAlgHom` puts the conjugating
variable first. The right coaction here puts the acted-on variable first, as the convention of
`TauCeti.ComoduleAlgebra` requires, and conjugates by the inverse point so that coassociativity
holds without commutativity of `G`. Both actions have the same invariants
(`TauCeti.HopfAlgebra.mem_conjugationInvariants_iff_conjugationAlgHom`).

An invariant function takes the same value at conjugate points: for every commutative
`R`-algebra `A` and all `g, x ∈ G(A)`, `f(g x g⁻¹) = f(x)`
(`TauCeti.HopfAlgebra.conjugationInvariants_apply_conj`). Restricting points of `G` to the
invariants is therefore constant on `G(A)`-conjugacy classes
(`TauCeti.HopfAlgebra.comp_val_conjugationInvariants_conj`); this is the conjugation invariance
of the quotient map `χ_G : G → G // G` on points.

## Main declarations

* `TauCeti.HopfAlgebra.conjugationCoactAlgHom`: the coordinate morphism of right conjugation.
* `TauCeti.HopfAlgebra.productMap_comp_conjugationCoactAlgHom`: on points it is
  `(x, g) ↦ g⁻¹ * x * g`.
* `TauCeti.HopfAlgebra.conjugationComoduleAlgebra`: the conjugation action as a comodule algebra.
* `TauCeti.HopfAlgebra.conjugationInvariants`: the conjugation-invariant functions.
* `TauCeti.HopfAlgebra.mem_conjugationInvariants_iff_forall_conj`: a function is invariant
  exactly when it is constant on conjugacy classes of points with values in every commutative
  algebra.
* `TauCeti.HopfAlgebra.conjugationInvariants_eq_classFunctions`: the invariant functions are the
  class functions.

## References

* J. S. Milne, *Algebraic Groups* (2017), §3.5 and §10.20.
* R. Steinberg, *Regular elements of semisimple algebraic groups*, Publ. Math. IHÉS **25** (1965),
  §6.
-/

public section

open TensorProduct WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable {R : Type u} {H : Type v} [CommSemiring R] [CommSemiring H]
variable [_root_.HopfAlgebra R H]

variable (R H) in
/-- The coordinate algebra morphism `H → H ⊗[R] H` of the right conjugation action
`(x, g) ↦ g⁻¹ * x * g` of an affine group on itself. The first tensor factor is the acted-on
variable and the second the acting variable: as a universal point it is `i₂⁻¹ * i₁ * i₂`. -/
noncomputable def conjugationCoactAlgHom : H →ₐ[R] H ⊗[R] H :=
  ((toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H))⁻¹ *
      toConv (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H) *
      toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)).ofConv

/-- The conjugation coaction is the convolution product `i₂⁻¹ * i₁ * i₂` of the two universal
tensor-factor points. -/
theorem toConv_conjugationCoactAlgHom :
    toConv (conjugationCoactAlgHom R H) =
      (toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H))⁻¹ *
        toConv (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H) *
        toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H) := by
  rw [conjugationCoactAlgHom, toConv_ofConv]

/-- **Evaluation of the conjugation coaction against an arbitrary algebra map out of the tensor
square**: it conjugates the first restriction by the inverse of the second. -/
theorem comp_conjugationCoactAlgHom {A : Type w} [CommSemiring A] [Algebra R A]
    (psi : H ⊗[R] H →ₐ[R] A) :
    psi.comp (conjugationCoactAlgHom R H) =
      ((toConv (psi.comp Algebra.TensorProduct.includeRight))⁻¹ *
        toConv (psi.comp Algebra.TensorProduct.includeLeft) *
        toConv (psi.comp Algebra.TensorProduct.includeRight)).ofConv := by
  have h := congrArg (fun g : WithConv (H →ₐ[R] H ⊗[R] H) ↦ (AlgHom.mapValue psi g).ofConv)
    (toConv_ofConv ((toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H))⁻¹ *
      toConv (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H) *
      toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)))
  rw [conjugationCoactAlgHom]
  simpa only [map_mul, map_inv, AlgHom.mapValue_apply, ofConv_toConv] using h

/-- Evaluating the conjugation coaction at an acted-on point `x` and an acting point `g` gives
`g⁻¹ * x * g`. -/
@[simp]
theorem productMap_comp_conjugationCoactAlgHom {A : Type w} [CommSemiring A] [Algebra R A]
    (x g : WithConv (H →ₐ[R] A)) :
    (Algebra.TensorProduct.productMap x.ofConv g.ofConv).comp (conjugationCoactAlgHom R H) =
      (g⁻¹ * x * g).ofConv := by
  simp [comp_conjugationCoactAlgHom]

/-- The identity element acts trivially: the right counit law of the conjugation coaction. -/
theorem map_counitAlgHom_comp_conjugationCoactAlgHom :
    (Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.counitAlgHom R H)).comp
        (conjugationCoactAlgHom R H) =
      Algebra.TensorProduct.includeLeft := by
  have hone : toConv ((Algebra.TensorProduct.map (AlgHom.id R H)
      (Bialgebra.counitAlgHom R H)).comp Algebra.TensorProduct.includeRight) =
      (1 : WithConv (H →ₐ[R] H ⊗[R] R)) := by
    apply ofConv_injective
    ext p
    simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.convOne_apply,
      Algebra.TensorProduct.algebraMap_apply, Bialgebra.counitAlgHom_apply]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  rw [comp_conjugationCoactAlgHom, hone, inv_one, one_mul, mul_one,
    Algebra.TensorProduct.map_comp_includeLeft, AlgHom.comp_id, ofConv_toConv]

/-- The action-associativity law of the conjugation coaction: conjugating by `g₁` and then by `g₂`
is conjugating by `g₁ * g₂`. -/
theorem assoc_comp_map_conjugationCoactAlgHom :
    (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
        ((Algebra.TensorProduct.map (conjugationCoactAlgHom R H) (AlgHom.id R H)).comp
          (conjugationCoactAlgHom R H)) =
      (Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.comulAlgHom R H)).comp
        (conjugationCoactAlgHom R H) := by
  set assoc := (Algebra.TensorProduct.assoc R R R H H H).toAlgHom
  -- The acted-on point `x` and the two acting points `g₁`, `g₂` of the triple tensor algebra.
  let x : WithConv (H →ₐ[R] H ⊗[R] (H ⊗[R] H)) := toConv Algebra.TensorProduct.includeLeft
  let g₁ : WithConv (H →ₐ[R] H ⊗[R] (H ⊗[R] H)) :=
    toConv (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft)
  let g₂ : WithConv (H →ₐ[R] H ⊗[R] (H ⊗[R] H)) :=
    toConv (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight)
  have hx : toConv ((assoc.comp Algebra.TensorProduct.includeLeft).comp
      Algebra.TensorProduct.includeLeft) = x := by
    apply congrArg toConv
    ext h
    simp [assoc, Algebra.TensorProduct.one_def]
  have hg₁ : toConv ((assoc.comp Algebra.TensorProduct.includeLeft).comp
      Algebra.TensorProduct.includeRight) = g₁ := by
    apply congrArg toConv
    ext h
    simp [assoc]
  have hg₂ : toConv ((assoc.comp (Algebra.TensorProduct.map (conjugationCoactAlgHom R H)
      (AlgHom.id R H))).comp Algebra.TensorProduct.includeRight) = g₂ := by
    apply congrArg toConv
    ext h
    simp [assoc, Algebra.TensorProduct.one_def]
  have hleft : (assoc.comp (Algebra.TensorProduct.map (conjugationCoactAlgHom R H)
      (AlgHom.id R H))).comp Algebra.TensorProduct.includeLeft =
      (assoc.comp Algebra.TensorProduct.includeLeft).comp (conjugationCoactAlgHom R H) := by
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeLeft, AlgHom.comp_assoc]
  have hcomul : toConv ((Algebra.TensorProduct.map (AlgHom.id R H)
      (Bialgebra.comulAlgHom R H)).comp Algebra.TensorProduct.includeRight) = g₁ * g₂ := by
    rw [Algebra.TensorProduct.map_comp_includeRight, AlgHom.toConv_comp_comulAlgHom]
  have hmapLeft : (Algebra.TensorProduct.map (AlgHom.id R H)
      (Bialgebra.comulAlgHom R H)).comp Algebra.TensorProduct.includeLeft =
      (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] (H ⊗[R] H)) := by
    rw [Algebra.TensorProduct.map_comp_includeLeft, AlgHom.comp_id]
  rw [← AlgHom.comp_assoc, comp_conjugationCoactAlgHom,
    comp_conjugationCoactAlgHom, hleft, comp_conjugationCoactAlgHom, toConv_ofConv, hx, hg₁, hg₂,
    hcomul, hmapLeft]
  apply congrArg ofConv
  rw [toConv_ofConv]
  -- Conjugating by `g₁` and then by `g₂` is conjugating by `g₁ * g₂`, in any group.
  have conj_conj {G : Type _} [Group G] (x a b : G) :
      b⁻¹ * (a⁻¹ * x * a) * b = (a * b)⁻¹ * x * (a * b) := by
    group
  exact conj_conj x g₁ g₂

/-- **The conjugation action of an affine group on itself, as a comodule algebra structure on
`H` over itself.** Its coaction is `TauCeti.HopfAlgebra.conjugationCoactAlgHom`. It is not an
instance, since `H` already carries the regular comodule algebra structure
`TauCeti.ComoduleAlgebra.instSelf` of right translation. -/
@[implicit_reducible]
noncomputable def conjugationComoduleAlgebra : ComoduleAlgebra R H H where
  coact := (conjugationCoactAlgHom R H).toLinearMap
  coassoc := by
    have h := congrArg AlgHom.toLinearMap (assoc_comp_map_conjugationCoactAlgHom (R := R) (H := H))
    refine LinearMap.ext fun a ↦ ?_
    have ha := LinearMap.congr_fun h a
    simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, AlgEquiv.toAlgHom_toLinearMap] at ha
    rw [Algebra.TensorProduct.map_apply_eq_map, Algebra.TensorProduct.map_apply_eq_map,
      AlgHom.toLinearMap_id] at ha
    rw [← LinearMap.rTensor_def, ← LinearMap.lTensor_def,
      Algebra.TensorProduct.assoc_toLinearEquiv, TensorProduct.AlgebraTensorModule.assoc_eq] at ha
    exact ha
  lTensor_counit_comp_coact := by
    refine LinearMap.ext fun a ↦ ?_
    have ha := AlgHom.congr_fun (map_counitAlgHom_comp_conjugationCoactAlgHom (R := R) (H := H)) a
    rw [AlgHom.comp_apply, Algebra.TensorProduct.map_apply_eq_map, AlgHom.toLinearMap_id] at ha
    rw [Bialgebra.toLinearMap_counitAlgHom, ← LinearMap.lTensor_def] at ha
    exact ha
  coact_one := map_one (conjugationCoactAlgHom R H)
  coact_mul := map_mul (conjugationCoactAlgHom R H)

/-- The coaction of the conjugation comodule algebra is the conjugation coaction. -/
theorem conjugationComoduleAlgebra_coact_apply (a : H) :
    letI := conjugationComoduleAlgebra (R := R) (H := H)
    Comodule.coact (R := R) (C := H) a = conjugationCoactAlgHom R H a :=
  (rfl)

/-- The coaction algebra morphism of the conjugation comodule algebra is the conjugation
coaction. -/
theorem conjugationComoduleAlgebra_coactAlgHom :
    letI := conjugationComoduleAlgebra (R := R) (H := H)
    ComoduleAlgebra.coactAlgHom R H H = conjugationCoactAlgHom R H :=
  AlgHom.ext fun a ↦
    @ComoduleAlgebra.coactAlgHom_apply R H H _ _ _ _ _ conjugationComoduleAlgebra a

variable (R H) in
/-- The **conjugation-invariant functions** `O(G)^G` on the affine group `G = Spec H`: the
coinvariants of the conjugation comodule algebra. They are the coordinate ring of the conjugation
quotient `G // G`. -/
noncomputable def conjugationInvariants : Subalgebra R H :=
  letI := conjugationComoduleAlgebra (R := R) (H := H)
  ComoduleAlgebra.coinvariants R H H

variable (R H) in
/-- The conjugation invariants are the coinvariants of the conjugation comodule algebra. -/
theorem conjugationInvariants_def :
    conjugationInvariants R H =
      letI := conjugationComoduleAlgebra (R := R) (H := H)
      ComoduleAlgebra.coinvariants R H H :=
  (rfl)

/-- A function is conjugation invariant exactly when the conjugation coaction sends it to
`f ⊗ 1`. -/
theorem mem_conjugationInvariants {f : H} :
    f ∈ conjugationInvariants R H ↔ conjugationCoactAlgHom R H f = f ⊗ₜ[R] 1 := by
  let := conjugationComoduleAlgebra (R := R) (H := H)
  exact ComoduleAlgebra.mem_coinvariants

/-- A conjugation invariant is a unit of the invariants exactly when it is a unit of `H`: the
inverse of an invariant unit is again invariant (`TauCeti.ComoduleAlgebra.isUnit_coinvariants_iff`).
-/
theorem isUnit_conjugationInvariants_iff {f : conjugationInvariants R H} :
    IsUnit f ↔ IsUnit (f : H) :=
  letI := conjugationComoduleAlgebra (R := R) (H := H)
  ComoduleAlgebra.isUnit_coinvariants_iff

/-- **An invariant function is constant on conjugacy classes of points**: for every commutative
`R`-algebra `A` and all `A`-points `g` and `x`, `f(g * x * g⁻¹) = f(x)`. -/
theorem conjugationInvariants_apply_conj {f : H} (hf : f ∈ conjugationInvariants R H)
    {A : Type w} [CommSemiring A] [Algebra R A] (g x : WithConv (H →ₐ[R] A)) :
    (g * x * g⁻¹).ofConv f = x.ofConv f := by
  have h := AlgHom.congr_fun
    (productMap_comp_conjugationCoactAlgHom (R := R) (H := H) x g⁻¹) f
  rw [AlgHom.comp_apply, mem_conjugationInvariants.1 hf, inv_inv] at h
  simpa using h.symm

/-- **The quotient map is conjugation invariant on points.** Restricting an `A`-point of `G` to
the conjugation-invariant functions, the `A`-point of `G // G` it defines, is constant on
`G(A)`-conjugacy classes. -/
theorem comp_val_conjugationInvariants_conj {A : Type w} [CommSemiring A] [Algebra R A]
    (g x : WithConv (H →ₐ[R] A)) :
    (g * x * g⁻¹).ofConv.comp (conjugationInvariants R H).val =
      x.ofConv.comp (conjugationInvariants R H).val :=
  AlgHom.ext fun f ↦ conjugationInvariants_apply_conj f.property g x

/-- A function is conjugation invariant exactly when it is constant on conjugacy classes of
points with values in every commutative `R`-algebra in the universe of `H`. -/
theorem mem_conjugationInvariants_iff_forall_conj {f : H} :
    f ∈ conjugationInvariants R H ↔
      ∀ (A : Type v) [CommSemiring A] [Algebra R A] (g x : WithConv (H →ₐ[R] A)),
        (g * x * g⁻¹).ofConv f = x.ofConv f := by
  refine ⟨fun hf A _ _ g x ↦ conjugationInvariants_apply_conj hf g x, fun h ↦ ?_⟩
  rw [mem_conjugationInvariants]
  have hc := h (H ⊗[R] H) (toConv Algebra.TensorProduct.includeRight)⁻¹
    (toConv Algebra.TensorProduct.includeLeft)
  rw [inv_inv] at hc
  simpa [conjugationCoactAlgHom] using hc

/-- The conjugation invariants are also the invariants of the left conjugation coaction
`TauCeti.HopfAlgebra.conjugationAlgHom`, whose conjugating variable comes first. -/
theorem mem_conjugationInvariants_iff_conjugationAlgHom {f : H} :
    f ∈ conjugationInvariants R H ↔
      conjugationAlgHom (R := R) (H := H) f = (1 : H) ⊗ₜ[R] f := by
  rw [mem_conjugationInvariants_iff_forall_conj]
  refine ⟨fun h ↦ ?_, fun h A _ _ g x ↦ ?_⟩
  · have hc := h (H ⊗[R] H) (toConv Algebra.TensorProduct.includeLeft)
      (toConv Algebra.TensorProduct.includeRight)
    rw [← ofConv_toConv (conjugationAlgHom (R := R) (H := H)), toConv_conjugationAlgHom]
    simpa [Bialgebra.TensorProduct.includeLeft_toAlgHom,
      Bialgebra.TensorProduct.includeRight_toAlgHom] using hc
  · have hc := AlgHom.congr_fun
      (productMap_comp_conjugationAlgHom (R := R) (H := H) g x) f
    rw [AlgHom.comp_apply, h] at hc
    simpa using hc.symm

variable (R H) in
/-- **The conjugation-invariant functions are the class functions**: the coinvariants of the right
conjugation coaction are the equalizer `TauCeti.HopfAlgebra.classFunctions` of the left
conjugation coordinate map and the second-factor inclusion. -/
theorem conjugationInvariants_eq_classFunctions :
    conjugationInvariants R H = classFunctions R H :=
  SetLike.ext fun _ ↦
    mem_conjugationInvariants_iff_conjugationAlgHom.trans mem_classFunctions_iff.symm

end HopfAlgebra

end TauCeti
