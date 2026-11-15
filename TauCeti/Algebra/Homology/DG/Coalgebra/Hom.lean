/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GradedFunLike
public import TauCeti.Algebra.Homology.DG.Coalgebra.Defs

/-!
# Morphisms of noncounital differential graded coalgebras

A morphism of noncounital differential graded coalgebras is a degree-zero linear map which commutes
with the coproducts and the differentials.  This file bundles those maps as
`TauCeti.NonCounitalDGCoalgHom` and supplies their extensionality, identity, composition, and
Koszul-twist compatibility lemmas.

## Main definitions

* `TauCeti.NonCounitalDGCoalgHom`: a morphism of noncounital differential graded coalgebras.
* `TauCeti.NonCounitalDGCoalgHom.id` and `TauCeti.NonCounitalDGCoalgHom.comp`: identity and
  composition.

## Main results

* `TauCeti.NonCounitalDGCoalgHom.map_comul` and `TauCeti.NonCounitalDGCoalgHom.map_d`:
  intertwining of coproducts and differentials.
* `TauCeti.NonCounitalDGCoalgHom.map_koszulTwist`: degree-zero morphisms commute with Koszul
  twists.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Chapter 1.
-/

public section

open TensorProduct

namespace TauCeti

universe uR uC uD uE uF

variable {R : Type uR} {C : Type uC} {D : Type uD} {E : Type uE}
  [CommRing R]
  [AddCommGroup C] [Module R C]
  [AddCommGroup D] [Module R D]
  [AddCommGroup E] [Module R E]
  {GC : InternalGrading R C ℤ} {GD : InternalGrading R D ℤ} {GE : InternalGrading R E ℤ}
  {ΔC : C →ₗ[R] C ⊗[R] C} {ΔD : D →ₗ[R] D ⊗[R] D} {ΔE : E →ₗ[R] E ⊗[R] E}
  {dC : C →ₗ[R] C} {dD : D →ₗ[R] D} {dE : E →ₗ[R] E}

/-- A morphism of noncounital differential graded coalgebras: a degree-zero `R`-linear map which
intertwines the coproducts and the differentials. -/
structure NonCounitalDGCoalgHom (hC : IsNonCounitalDGCoalgebra GC ΔC dC)
    (hD : IsNonCounitalDGCoalgebra GD ΔD dD) extends C →ₗ[R] D where
  /-- A morphism of noncounital DG coalgebras preserves the internal degree. -/
  map_mem' : ∀ {p : ℤ} {c : C}, c ∈ GC.piece p → toLinearMap c ∈ GD.piece p
  /-- A morphism of noncounital DG coalgebras commutes with the coproducts. -/
  comul_comp' : ΔD ∘ₗ toLinearMap = TensorProduct.map toLinearMap toLinearMap ∘ₗ ΔC
  /-- A morphism of noncounital DG coalgebras commutes with the differentials. -/
  map_d' (c : C) : dD (toLinearMap c) = toLinearMap (dC c)

namespace NonCounitalDGCoalgHom

variable {hC : IsNonCounitalDGCoalgebra GC ΔC dC}
  {hD : IsNonCounitalDGCoalgebra GD ΔD dD}
  {hE : IsNonCounitalDGCoalgebra GE ΔE dE}

/-- Morphisms of noncounital DG coalgebras are determined by their underlying linear maps. -/
theorem toLinearMap_injective :
    Function.Injective (toLinearMap : NonCounitalDGCoalgHom hC hD → C →ₗ[R] D) := by
  rintro ⟨f, _, _, _⟩ ⟨g, _, _, _⟩ h
  cases h
  rfl

instance : FunLike (NonCounitalDGCoalgHom hC hD) C D where
  coe f := f.toLinearMap
  coe_injective _ _ h := toLinearMap_injective <| LinearMap.ext fun c ↦ congrFun h c

instance : GradedFunLike (NonCounitalDGCoalgHom hC hD) GC.piece GD.piece where
  map_mem f := f.map_mem'

instance : LinearMapClass (NonCounitalDGCoalgHom hC hD) R C D where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

instance : CoeOut (NonCounitalDGCoalgHom hC hD) (C →ₗ[R] D) :=
  ⟨toLinearMap⟩

@[simp]
theorem coe_toLinearMap (f : NonCounitalDGCoalgHom hC hD) :
    ⇑f.toLinearMap = f := (rfl)

@[simp]
theorem coe_mk (f : C →ₗ[R] D) (hm hc hd) :
    ⇑(NonCounitalDGCoalgHom.mk f hm hc hd : NonCounitalDGCoalgHom hC hD) = f := (rfl)

/-- Two morphisms of noncounital DG coalgebras are equal if they agree on every element. -/
@[ext]
theorem ext {f g : NonCounitalDGCoalgHom hC hD} (h : ∀ c, f c = g c) : f = g :=
  toLinearMap_injective <| LinearMap.ext h

/-- A morphism of noncounital DG coalgebras commutes with the coproducts, as an equality of linear
maps. -/
theorem comul_comp (f : NonCounitalDGCoalgHom hC hD) :
    ΔD ∘ₗ (f : C →ₗ[R] D) = TensorProduct.map (f : C →ₗ[R] D) (f : C →ₗ[R] D) ∘ₗ ΔC :=
  f.comul_comp'

/-- A morphism of noncounital DG coalgebras commutes pointwise with the coproducts. -/
@[simp]
theorem map_comul (f : NonCounitalDGCoalgHom hC hD) (c : C) :
    ΔD (f c) = TensorProduct.map (f : C →ₗ[R] D) (f : C →ₗ[R] D) (ΔC c) :=
  LinearMap.congr_fun f.comul_comp c

/-- A morphism of noncounital DG coalgebras commutes with the differentials. -/
@[simp]
theorem map_d (f : NonCounitalDGCoalgHom hC hD) (c : C) :
    dD (f c) = f (dC c) :=
  f.map_d' c

/-- A morphism of noncounital DG coalgebras is homogeneous of degree zero. -/
theorem isHomogeneous (f : NonCounitalDGCoalgHom hC hD) :
    LinearMap.IsHomogeneous (f : C →ₗ[R] D) GC.piece GD.piece 0 :=
  LinearMap.isHomogeneous_def.mpr fun _ _ hc ↦ by simpa only [add_zero] using f.map_mem' hc

/-- A morphism of noncounital DG coalgebras commutes with the Koszul twist, since it has degree
zero. -/
@[simp]
theorem map_koszulTwist (f : NonCounitalDGCoalgHom hC hD) (q : ℤ) (c : C) :
    f (GC.koszulTwist q c) = GD.koszulTwist q (f c) := by
  simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
    coe_toLinearMap] using (f.isHomogeneous.koszulTwist_apply q c).symm

/-- Linear-map form of `map_koszulTwist`. -/
theorem koszulTwist_comp (f : NonCounitalDGCoalgHom hC hD) (q : ℤ) :
    GD.koszulTwist q ∘ₗ (f : C →ₗ[R] D) = (f : C →ₗ[R] D) ∘ₗ GC.koszulTwist q := by
  ext c
  exact (f.map_koszulTwist q c).symm

/-- The identity morphism of a noncounital differential graded coalgebra. -/
protected def id (hC : IsNonCounitalDGCoalgebra GC ΔC dC) : NonCounitalDGCoalgHom hC hC where
  toLinearMap := LinearMap.id
  map_mem' hc := hc
  comul_comp' := by rw [TensorProduct.map_id, LinearMap.id_comp, LinearMap.comp_id]
  map_d' _ := rfl

@[simp]
theorem id_toLinearMap (hC : IsNonCounitalDGCoalgebra GC ΔC dC) :
    (NonCounitalDGCoalgHom.id hC).toLinearMap = LinearMap.id := (rfl)

@[simp]
theorem coe_id (hC : IsNonCounitalDGCoalgebra GC ΔC dC) :
    ⇑(NonCounitalDGCoalgHom.id hC) = _root_.id := (rfl)

@[simp]
theorem id_apply (hC : IsNonCounitalDGCoalgebra GC ΔC dC) (c : C) :
    NonCounitalDGCoalgHom.id hC c = c := (rfl)

/-- Composition of morphisms of noncounital differential graded coalgebras. -/
def comp (g : NonCounitalDGCoalgHom hD hE) (f : NonCounitalDGCoalgHom hC hD) :
    NonCounitalDGCoalgHom hC hE where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  map_mem' hc := g.map_mem' (f.map_mem' hc)
  comul_comp' := by
    rw [← LinearMap.comp_assoc, g.comul_comp', LinearMap.comp_assoc, f.comul_comp',
      TensorProduct.map_comp, LinearMap.comp_assoc]
  map_d' c := (g.map_d' (f c)).trans (congrArg g (f.map_d' c))

@[simp]
theorem comp_toLinearMap (g : NonCounitalDGCoalgHom hD hE) (f : NonCounitalDGCoalgHom hC hD) :
    (g.comp f).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap := (rfl)

@[simp]
theorem coe_comp (g : NonCounitalDGCoalgHom hD hE) (f : NonCounitalDGCoalgHom hC hD) :
    ⇑(g.comp f) = g ∘ f := (rfl)

@[simp]
theorem comp_apply (g : NonCounitalDGCoalgHom hD hE) (f : NonCounitalDGCoalgHom hC hD) (c : C) :
    g.comp f c = g (f c) := (rfl)

@[simp]
theorem comp_id (f : NonCounitalDGCoalgHom hC hD) :
    f.comp (NonCounitalDGCoalgHom.id hC) = f := by
  ext c
  rfl

@[simp]
theorem id_comp (f : NonCounitalDGCoalgHom hC hD) :
    (NonCounitalDGCoalgHom.id hD).comp f = f := by
  ext c
  rfl

/-- Composition of morphisms of noncounital DG coalgebras is associative. -/
@[simp]
theorem comp_assoc {F : Type uF} [AddCommGroup F] [Module R F]
    {GF : InternalGrading R F ℤ} {ΔF : F →ₗ[R] F ⊗[R] F} {dF : F →ₗ[R] F}
    {hF : IsNonCounitalDGCoalgebra GF ΔF dF}
    (k : NonCounitalDGCoalgHom hE hF) (g : NonCounitalDGCoalgHom hD hE)
    (f : NonCounitalDGCoalgHom hC hD) :
    (k.comp g).comp f = k.comp (g.comp f) := by
  ext c
  rfl

end NonCounitalDGCoalgHom

end TauCeti
