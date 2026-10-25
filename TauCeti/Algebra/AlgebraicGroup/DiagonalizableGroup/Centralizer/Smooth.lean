/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra.FixedPointIdeal
import TauCeti.Algebra.TensorProduct.MapLinear

/-!
# Smoothness of centralizers of diagonalizable subgroups

Let `G = Spec H` be an affine group scheme over a commutative ring `R` and let `π : H →ₐc[R] R[X]`
present a homomorphism `D(X) → G` from the diagonalizable group of a commutative group `X`. This
file proves that the centralizer `Z_G(D(X))` is formally smooth whenever `G` is, and hence smooth
when `G` is a smooth affine group of finite type over a Noetherian ring, for example a field.

The proof identifies the centralizer with a fixed-point subscheme. The group `D(X)` acts on `G` by
conjugation, `(g, t) ↦ π(t) g π(t)⁻¹`, which makes `H` a comodule algebra over `R[X]`
(`BialgHom.conjugationComoduleAlgebra`). Its fixed points are exactly the points of `G` commuting
with `D(X)`, so the centralizer ideal is the fixed-point ideal of this action
(`BialgHom.centralizerHopfIdeal_toIdeal_eq_fixedPointIdeal`). The fixed-point subscheme of a
formally smooth affine scheme under a diagonalizable action is formally smooth
(`TauCeti.ComoduleAlgebra.formallySmooth_quotient_fixedPointIdeal`).

No reductivity, connectedness, finite-type or field hypothesis is used, and `π` need not be
injective on points. The statement applies in particular to the centralizer of a maximal torus and
to the centralizer of the kernel of a root, and recovers smoothness of the dynamic Levi subgroup
`Z_G(λ)` of a cocharacter, which is the centralizer of its image.

## Main declarations

* `BialgHom.conjugationCoactAlgHom`: the coordinate map of the conjugation action of `D(X)` on
  `G`.
* `BialgHom.conjugationComoduleAlgebra`: the conjugation action as a comodule algebra structure on
  `H` over `R[X]`.
* `BialgHom.centralizerHopfIdeal_toIdeal_eq_fixedPointIdeal`: the centralizer is the fixed-point
  subscheme of the conjugation action.
* `BialgHom.formallySmooth_quotient_centralizerHopfIdeal`: **the centralizer of a diagonalizable
  subgroup of a formally smooth affine group is formally smooth.**
* `BialgHom.smoothCommHopfAlgProperty_quotient_centralizerHopfIdeal`: **the centralizer of a
  diagonalizable subgroup of a smooth affine group of finite type over a Noetherian ring is
  smooth.**

## References

* SGA 3, Exposé XI, Corollaire 5.3.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, Proposition A.8.10(2).
* J. S. Milne, *Algebraic Groups* (2017), Theorem 13.1.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace BialgHom

open TauCeti

universe u v w x

variable {R : Type u} {H : Type v} {X : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]
variable (π : H →ₐc[R] MonoidAlgebra R X)

/-! ## The conjugation action of `D(X)` on `G` -/

/-- The coordinate map `H → H ⊗[R] R[X]` of the conjugation action `(g, t) ↦ π(t) g π(t)⁻¹` of the
diagonalizable group `D(X)` on `G`. The first tensor factor is the acted-on variable of `G`, the
second the acting variable of `D(X)`. -/
noncomputable def conjugationCoactAlgHom : H →ₐ[R] H ⊗[R] MonoidAlgebra R X :=
  (Algebra.TensorProduct.comm R (MonoidAlgebra R X) H).toAlgHom.comp
    ((Algebra.TensorProduct.map π.toAlgHom (AlgHom.id R H)).comp
      (HopfAlgebra.conjugationAlgHom (R := R) (H := H)))

/-- **Evaluation of the conjugation action against an arbitrary algebra map out of
`H ⊗[R] R[X]`**: it conjugates the restriction to `H` by the image in `G` of the restriction to
`R[X]`. -/
theorem comp_conjugationCoactAlgHom {B : Type x} [CommRing B] [Algebra R B]
    (ψ : H ⊗[R] MonoidAlgebra R X →ₐ[R] B) :
    ψ.comp (conjugationCoactAlgHom π) =
      (mapDomain π (toConv (ψ.comp Algebra.TensorProduct.includeRight)) *
          toConv (ψ.comp Algebra.TensorProduct.includeLeft) *
          (mapDomain π (toConv (ψ.comp Algebra.TensorProduct.includeRight)))⁻¹).ofConv := by
  rw [conjugationCoactAlgHom, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
    HopfAlgebra.comp_conjugationAlgHom]
  have hleft : toConv (((ψ.comp (Algebra.TensorProduct.comm R (MonoidAlgebra R X) H).toAlgHom).comp
      (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id R H))).comp
        Algebra.TensorProduct.includeLeft) =
      mapDomain π (toConv (ψ.comp Algebra.TensorProduct.includeRight)) := by
    rw [mapDomain_apply, ofConv_toConv]
    apply congrArg toConv
    ext h
    simp
  have hright : toConv (((ψ.comp (Algebra.TensorProduct.comm R (MonoidAlgebra R X) H).toAlgHom).comp
      (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id R H))).comp
        Algebra.TensorProduct.includeRight) =
      toConv (ψ.comp Algebra.TensorProduct.includeLeft) := by
    apply congrArg toConv
    ext h
    simp
  rw [hleft, hright]

/-- An algebra map out of `H ⊗[R] R[X]` is unchanged by the conjugation action exactly when its
restriction to `H` commutes with the image in `G` of its restriction to `R[X]`. -/
private theorem comp_conjugationCoactAlgHom_eq_iff_commute {B : Type x} [CommRing B]
    [Algebra R B] (ψ : H ⊗[R] MonoidAlgebra R X →ₐ[R] B) :
    ψ.comp (conjugationCoactAlgHom π) = ψ.comp Algebra.TensorProduct.includeLeft ↔
      Commute (toConv (ψ.comp Algebra.TensorProduct.includeLeft))
        (mapDomain π (toConv (ψ.comp Algebra.TensorProduct.includeRight))) := by
  rw [comp_conjugationCoactAlgHom, ← ofConv_toConv (ψ.comp Algebra.TensorProduct.includeLeft),
    ofConv_injective.eq_iff, mul_inv_eq_iff_eq_mul, ofConv_toConv, commute_iff_eq, eq_comm]

/-- The action-associativity law of the conjugation action, tested against an arbitrary algebra
map `ψ` out of the triple tensor product. Testing against `ψ` keeps every point in a convolution
group with a commutative value algebra of its own. -/
private theorem comp_assoc_comp_map_conjugationCoactAlgHom {B : Type x} [CommRing B]
    [Algebra R B] (ψ : H ⊗[R] (MonoidAlgebra R X ⊗[R] MonoidAlgebra R X) →ₐ[R] B) :
    ψ.comp ((Algebra.TensorProduct.assoc R R R H (MonoidAlgebra R X)
        (MonoidAlgebra R X)).toAlgHom.comp
          ((Algebra.TensorProduct.map (conjugationCoactAlgHom π)
            (AlgHom.id R (MonoidAlgebra R X))).comp (conjugationCoactAlgHom π))) =
      ψ.comp ((Algebra.TensorProduct.map (AlgHom.id R H)
        (Bialgebra.comulAlgHom R (MonoidAlgebra R X))).comp (conjugationCoactAlgHom π)) := by
  let ψ' := ψ.comp (Algebra.TensorProduct.assoc R R R H (MonoidAlgebra R X)
    (MonoidAlgebra R X)).toAlgHom
  -- The universal point `g` of `G` and the two universal points `u₁`, `u₂` of `D(X)`.
  let g : WithConv (H →ₐ[R] B) := toConv (ψ.comp Algebra.TensorProduct.includeLeft)
  let u₁ : WithConv (MonoidAlgebra R X →ₐ[R] B) :=
    toConv ((ψ.comp Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeLeft)
  let u₂ : WithConv (MonoidAlgebra R X →ₐ[R] B) :=
    toConv ((ψ.comp Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeRight)
  have hg : toConv ((ψ'.comp Algebra.TensorProduct.includeLeft).comp
      Algebra.TensorProduct.includeLeft) = g := by
    apply congrArg toConv
    ext h
    simp [ψ', Algebra.TensorProduct.one_def]
  have hu₁ : toConv ((ψ'.comp Algebra.TensorProduct.includeLeft).comp
      Algebra.TensorProduct.includeRight) = u₁ := by
    apply congrArg toConv
    ext p
    simp [ψ']
  have hu₂ : toConv ((ψ'.comp (Algebra.TensorProduct.map (conjugationCoactAlgHom π)
      (AlgHom.id R (MonoidAlgebra R X)))).comp Algebra.TensorProduct.includeRight) = u₂ := by
    apply congrArg toConv
    ext p
    simp [ψ', Algebra.TensorProduct.one_def]
  have hcomul : toConv ((ψ.comp (Algebra.TensorProduct.map (AlgHom.id R H)
      (Bialgebra.comulAlgHom R (MonoidAlgebra R X)))).comp Algebra.TensorProduct.includeRight) =
      u₁ * u₂ := by
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeRight, ← AlgHom.comp_assoc,
      Bialgebra.toConv_comp_comulAlgHom]
  have hleft : (ψ.comp (Algebra.TensorProduct.map (AlgHom.id R H)
      (Bialgebra.comulAlgHom R (MonoidAlgebra R X)))).comp Algebra.TensorProduct.includeLeft =
      ψ.comp Algebra.TensorProduct.includeLeft := by
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeLeft, AlgHom.comp_id]
  have hcomm : mapDomain π u₂ * mapDomain π u₁ = mapDomain π u₁ * mapDomain π u₂ := by
    rw [← map_mul, ← map_mul, (Commute.all u₂ u₁).eq]
  -- Both sides are conjugation of `g` by the image of `u₁ u₂`.
  have hL : ψ.comp ((Algebra.TensorProduct.assoc R R R H (MonoidAlgebra R X)
      (MonoidAlgebra R X)).toAlgHom.comp ((Algebra.TensorProduct.map (conjugationCoactAlgHom π)
        (AlgHom.id R (MonoidAlgebra R X))).comp (conjugationCoactAlgHom π))) =
      (mapDomain π u₂ * (mapDomain π u₁ * g * (mapDomain π u₁)⁻¹) *
        (mapDomain π u₂)⁻¹).ofConv := by
    have e1 : ψ.comp ((Algebra.TensorProduct.assoc R R R H (MonoidAlgebra R X)
        (MonoidAlgebra R X)).toAlgHom.comp ((Algebra.TensorProduct.map (conjugationCoactAlgHom π)
          (AlgHom.id R (MonoidAlgebra R X))).comp (conjugationCoactAlgHom π))) =
        (ψ'.comp (Algebra.TensorProduct.map (conjugationCoactAlgHom π)
          (AlgHom.id R (MonoidAlgebra R X)))).comp (conjugationCoactAlgHom π) := by
      simp only [ψ', AlgHom.comp_assoc]
    have e2 : (ψ'.comp (Algebra.TensorProduct.map (conjugationCoactAlgHom π)
        (AlgHom.id R (MonoidAlgebra R X)))).comp Algebra.TensorProduct.includeLeft =
        (ψ'.comp Algebra.TensorProduct.includeLeft).comp (conjugationCoactAlgHom π) := by
      rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeLeft]
      simp only [ψ', AlgHom.comp_assoc]
    rw [e1, comp_conjugationCoactAlgHom, e2, comp_conjugationCoactAlgHom, toConv_ofConv, hg, hu₁,
      hu₂]
  have hR : ψ.comp ((Algebra.TensorProduct.map (AlgHom.id R H)
      (Bialgebra.comulAlgHom R (MonoidAlgebra R X))).comp (conjugationCoactAlgHom π)) =
      (mapDomain π u₁ * mapDomain π u₂ * g * (mapDomain π u₁ * mapDomain π u₂)⁻¹).ofConv := by
    rw [← AlgHom.comp_assoc, comp_conjugationCoactAlgHom, hcomul, hleft, map_mul]
  rw [hL, hR]
  apply congrArg ofConv
  calc mapDomain π u₂ * (mapDomain π u₁ * g * (mapDomain π u₁)⁻¹) * (mapDomain π u₂)⁻¹ =
      (mapDomain π u₂ * mapDomain π u₁) * g * (mapDomain π u₂ * mapDomain π u₁)⁻¹ := by group
    _ = mapDomain π u₁ * mapDomain π u₂ * g * (mapDomain π u₁ * mapDomain π u₂)⁻¹ := by
      rw [hcomm]

/-- The identity of `D(X)` acts trivially, as an equation of algebra maps. -/
private theorem map_counit_comp_conjugationCoactAlgHom :
    (Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.counitAlgHom R (MonoidAlgebra R X))).comp
        (conjugationCoactAlgHom π) =
      Algebra.TensorProduct.includeLeft := by
  have hone : toConv ((Algebra.TensorProduct.map (AlgHom.id R H)
      (Bialgebra.counitAlgHom R (MonoidAlgebra R X))).comp Algebra.TensorProduct.includeRight) =
      (1 : WithConv (MonoidAlgebra R X →ₐ[R] H ⊗[R] R)) := by
    apply ofConv_injective
    ext p
    simp [AlgHom.convOne_apply, Algebra.TensorProduct.algebraMap_apply]
  rw [comp_conjugationCoactAlgHom, hone, map_one, one_mul, inv_one, mul_one,
    Algebra.TensorProduct.map_comp_includeLeft, AlgHom.comp_id, ofConv_toConv]

/-- **The conjugation action of `D(X)` on `G`, as a comodule algebra structure on `H` over
`R[X]`.** Its coaction is `BialgHom.conjugationCoactAlgHom`. -/
@[implicit_reducible]
noncomputable def conjugationComoduleAlgebra : ComoduleAlgebra R (MonoidAlgebra R X) H where
  coact := (conjugationCoactAlgHom π).toLinearMap
  coassoc := by
    have h := congrArg AlgHom.toLinearMap
      (comp_assoc_comp_map_conjugationCoactAlgHom π
        (B := H ⊗[R] (MonoidAlgebra R X ⊗[R] MonoidAlgebra R X)) (AlgHom.id R _))
    rw [AlgHom.id_comp, AlgHom.id_comp] at h
    refine LinearMap.ext fun a ↦ ?_
    have ha := LinearMap.congr_fun h a
    simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, AlgEquiv.toAlgHom_toLinearMap] at ha
    rw [Algebra.TensorProduct.map_apply_eq_map, Algebra.TensorProduct.map_apply_eq_map,
      AlgHom.toLinearMap_id, AlgHom.toLinearMap_id] at ha
    rw [Bialgebra.toLinearMap_comulAlgHom, ← LinearMap.rTensor_def, ← LinearMap.lTensor_def,
      Algebra.TensorProduct.assoc_toLinearEquiv, TensorProduct.AlgebraTensorModule.assoc_eq] at ha
    exact ha
  lTensor_counit_comp_coact := by
    refine LinearMap.ext fun a ↦ ?_
    have ha := AlgHom.congr_fun (map_counit_comp_conjugationCoactAlgHom π) a
    rw [AlgHom.comp_apply, Algebra.TensorProduct.map_apply_eq_map, AlgHom.toLinearMap_id] at ha
    rw [Bialgebra.toLinearMap_counitAlgHom, ← LinearMap.lTensor_def] at ha
    exact ha
  coact_one := map_one (conjugationCoactAlgHom π)
  coact_mul := map_mul (conjugationCoactAlgHom π)

/-- The coaction of the conjugation comodule algebra is the conjugation action. -/
theorem conjugationComoduleAlgebra_coact_apply (a : H) :
    letI := conjugationComoduleAlgebra π
    Comodule.coact (R := R) (C := MonoidAlgebra R X) a = conjugationCoactAlgHom π a := by
  rfl

/-! ## The centralizer as a fixed-point subscheme -/

/-- **A point of `G` lies in the centralizer exactly when it is a fixed point of the conjugation
action of `D(X)`.** -/
theorem centralizerHopfIdeal_le_ker_iff_fixedPointIdeal_le_ker {B : Type x} [CommRing B]
    [Algebra R B] (q : H →ₐ[R] B) :
    (centralizerHopfIdeal π).toIdeal ≤ RingHom.ker q ↔
      letI := conjugationComoduleAlgebra π
      Comodule.fixedPointIdeal R X H ≤ RingHom.ker q := by
  let := conjugationComoduleAlgebra π
  rw [Comodule.fixedPointIdeal_le_ker_iff,
    centralizerHopfIdeal_le_ker_iff_commute_of_injective π (toConv q) (AlgHom.id R _)
      Function.injective_id, AlgHom.id_comp, AlgHom.id_comp, AlgHom.mapValue_apply,
    ofConv_toConv]
  -- The fixed-point equation says that conjugation by the universal point of `D(X)` fixes `q`.
  have key := comp_conjugationCoactAlgHom_eq_iff_commute π
    (Algebra.TensorProduct.map q (AlgHom.id R (MonoidAlgebra R X)))
  rw [Algebra.TensorProduct.map_comp_includeLeft, Algebra.TensorProduct.map_comp_includeRight,
    AlgHom.comp_id, AlgHom.ext_iff] at key
  simpa [conjugationComoduleAlgebra_coact_apply] using key.symm

/-- **The centralizer of a diagonalizable subgroup is the fixed-point subscheme of its conjugation
action.** -/
theorem centralizerHopfIdeal_toIdeal_eq_fixedPointIdeal :
    (centralizerHopfIdeal π).toIdeal =
      letI := conjugationComoduleAlgebra π
      Comodule.fixedPointIdeal R X H := by
  let := conjugationComoduleAlgebra π
  have hker (I : Ideal H) : RingHom.ker (Ideal.Quotient.mkₐ R I) = I := Ideal.Quotient.mkₐ_ker R I
  apply le_antisymm
  · simpa only [hker] using (centralizerHopfIdeal_le_ker_iff_fixedPointIdeal_le_ker π
      (Ideal.Quotient.mkₐ R (Comodule.fixedPointIdeal R X H))).mpr (hker _).ge
  · simpa only [hker] using (centralizerHopfIdeal_le_ker_iff_fixedPointIdeal_le_ker π
      (Ideal.Quotient.mkₐ R (centralizerHopfIdeal π).toIdeal)).mp (hker _).ge

/-! ## Smoothness -/

/-- **The centralizer of a diagonalizable subgroup of a formally smooth affine group is formally
smooth.** No finite-type, field, connectedness or reductivity hypothesis is needed. -/
instance formallySmooth_quotient_centralizerHopfIdeal [Algebra.FormallySmooth R H] :
    Algebra.FormallySmooth R (H ⧸ (centralizerHopfIdeal π).toIdeal) := by
  let := conjugationComoduleAlgebra π
  rw [centralizerHopfIdeal_toIdeal_eq_fixedPointIdeal]
  infer_instance

section FiniteType

variable [IsNoetherianRing R] {H : FiniteTypeCommHopfAlgCat.{u, v} R}

/-- **The centralizer of a diagonalizable subgroup of a smooth affine group of finite type over a
Noetherian ring is smooth.** -/
theorem smoothCommHopfAlgProperty_quotient_centralizerHopfIdeal [Algebra.Smooth R H]
    (π : H →ₐc[R] MonoidAlgebra R X) :
    smoothCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient H (centralizerHopfIdeal π)).obj := by
  rw [smoothCommHopfAlgProperty_iff]
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end FiniteType

end BialgHom
