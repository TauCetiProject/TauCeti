/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Induced.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
import TauCeti.LinearAlgebra.TensorProduct.Tower

/-!
# Pointwise equivariance of cotensor induction

For a map `q : C →ₐc[R] D` of commutative coordinate bialgebras over a commutative ring `R`,
the cotensor equalizer defining induction consists exactly of the regular functions satisfying
`F(hg) = h F(g)` on points with values in commutative `R`-algebras. Evaluating at the universal
pair of points already detects this condition. In particular the criterion uses scheme-valued
points, not just points over fields. The forward formulas also hold for noncommutative
coordinate bialgebras. Evaluation itself needs only a coalgebra map and an algebra structure
on its source.

The cofree coaction gives right translation on these functions. For Hopf algebras,
applying the antipode to the coordinate factor gives Jantzen's convention `f(gh) = h⁻¹ f(g)`
by `Comodule.pointCochain_lTensor_antipode`, and the same action becomes left translation
`(a f)(g) = f(a⁻¹g)`. Evaluation at the identity agrees with the counit evaluation in
Frobenius reciprocity.

There is no finiteness or flatness assumption on the coefficient module, and the coordinate
map need not be surjective. Flatness of `C` is used only to form the induced comodule.

## References

* J. C. Jantzen, *Representations of Algebraic Groups I*, SFB/MPI 85-9 (1985),
  §§3.3–3.7, pp. 52–58.
-/

public noncomputable section

open scoped TensorProduct
open TensorProduct WithConv

namespace CoalgHom

open TauCeti TauCeti.Comodule

universe u v w x y

variable {R : Type u} [CommRing R]
  {C : Type v} {D : Type w}
  [AddCommMonoid D] [Module R D] [Coalgebra R D]
  {M : Type x} [AddCommMonoid M] [Module R M] [Comodule R D M]
  {A : Type y} [CommSemiring A] [Algebra R A]

section Algebra

variable [Semiring C] [Algebra R C] [Coalgebra R C] [Module.Flat R C]
  (f : C →ₗc[R] D)

/-- Evaluation of a scalar-extended induced function at an algebra-valued point. This is
counit evaluation after the point acts, hence is linear over the value algebra. -/
def inducedPointEval (g : WithConv (C →ₐ[R] A)) :
    A ⊗[R] induced f M →ₗ[A] A ⊗[R] M :=
  let := Corestrict (M := induced f M) f
  (inducedEval f).toLinearMap.baseChange A ∘ₗ
    endOfPoint (induced f M) g.ofConv

/-- Evaluation is counit evaluation after applying the point action. -/
theorem inducedPointEval_def (g : WithConv (C →ₐ[R] A)) :
    let := Corestrict (M := induced f M) f
    inducedPointEval (M := M) f g =
      (inducedEval f).toLinearMap.baseChange A ∘ₗ
        endOfPoint (induced f M) g.ofConv := (rfl)

/-- On a pure tensor, evaluation pushes the coordinate factor through the point. -/
@[simp]
theorem inducedPointEval_tmul (g : WithConv (C →ₐ[R] A)) (a : A)
    (t : induced f M) :
    inducedPointEval f g (a ⊗ₜ[R] t) = a • pointCochain M g.ofConv (t : M ⊗[R] C) := by
  let := Corestrict (M := induced f M) f
  have h := rTensor_inducedEval_coact f t
  simp only [inducedPointEval, LinearMap.comp_apply, endOfPoint_tmul, map_smul]
  rw [← pointCochain_apply, LinearMap.baseChange_pointCochain, h]

/-- The lift in Frobenius reciprocity evaluates as `F(g) = u(g n)`, for a morphism
`u` from the corestricted source to the coefficient comodule. Substituting `g⁻¹` gives
Jantzen's formula `f(g) = u(g⁻¹ n)` for inverted evaluation. At `g = 1` it simplifies
to the scalar extension of `u`, by `endOfPoint_convOne`. -/
@[simp]
theorem inducedPointEval_inducedLift {N : Type*} [AddCommMonoid N] [Module R N]
    [Comodule R C N] (u : letI := Corestrict (M := N) f; Hom R D N M)
    (g : WithConv (C →ₐ[R] A)) (z : A ⊗[R] N) :
    letI := Corestrict (M := N) f
    inducedPointEval f g ((inducedLift f u).toLinearMap.baseChange A z) =
      u.toLinearMap.baseChange A (endOfPoint N g.ofConv z) := by
  let := Corestrict (M := N) f
  let := Corestrict (M := induced f M) f
  have hf := (inducedEquiv f).apply_symm_apply u
  rw [inducedEquiv_symm_apply, inducedEquiv_apply] at hf
  have he := congrArg Hom.toLinearMap hf
  simp only [Hom.comp_toLinearMap, corestrictHom_toLinearMap] at he
  have hn := LinearMap.congr_fun
    (baseChange_comp_endOfPoint (inducedLift f u) g.ofConv) z
  simp only [LinearMap.comp_apply] at hn
  simp only [inducedPointEval_def, LinearMap.comp_apply]
  rw [← hn, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, he]

/-- Evaluation commutes with a morphism of coefficient comodules. -/
@[simp]
theorem inducedPointEval_inducedMap {M' : Type*} [AddCommMonoid M'] [Module R M']
    [Comodule R D M'] (u : Hom R D M M') (g : WithConv (C →ₐ[R] A))
    (z : A ⊗[R] induced f M) :
    inducedPointEval f g ((inducedMap f u).toLinearMap.baseChange A z) =
      u.toLinearMap.baseChange A (inducedPointEval f g z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul a t =>
    simp only [LinearMap.baseChange_tmul, Hom.coe_toLinearMap, inducedPointEval_tmul,
      coe_inducedMap_apply, map_smul, LinearMap.baseChange_pointCochain]

end Algebra

section Bialgebra

variable [Semiring C] [Bialgebra R C] [Module.Flat R C] (f : C →ₗc[R] D)

/-- Evaluation at the identity is the scalar extension of the counit evaluation in
Frobenius reciprocity. -/
@[simp]
theorem inducedPointEval_one :
    let := Corestrict (M := induced f M) f
    inducedPointEval (M := M) (A := A) f 1 =
      (inducedEval f).toLinearMap.baseChange A := by
  simp [inducedPointEval, endOfPoint_convOne]

/-- The point action on induction is right translation: `(a F)(g) = F(ga)`. -/
@[simp]
theorem inducedPointEval_endOfPoint (g a : WithConv (C →ₐ[R] A))
    (z : A ⊗[R] induced f M) :
    inducedPointEval f g (endOfPoint (induced f M) a.ofConv z) =
      inducedPointEval f (g * a) z := by
  simp only [inducedPointEval, endOfPoint_convMul, LinearMap.comp_apply]

/-- Evaluation commutes with extension of the value algebra. -/
@[simp]
theorem rTensor_inducedPointEval {B : Type*} [CommSemiring B] [Algebra R B]
    (φ : A →ₐ[R] B) (g : WithConv (C →ₐ[R] A))
    (z : A ⊗[R] induced f M) :
    φ.toLinearMap.rTensor M (inducedPointEval f g z) =
      inducedPointEval f (AlgHom.mapValue φ g)
        (φ.toLinearMap.rTensor (induced f M) z) := by
  simp only [inducedPointEval, LinearMap.comp_apply, LinearMap.rTensor_baseChange]
  congr 1
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    AlgHom.mapValue_apply, ofConv_toConv] using
    LinearMap.congr_fun (rTensor_comp_endOfPoint _ φ g.ofConv) z

end Bialgebra

section Hopf

variable [Semiring C] [HopfAlgebra R C] [Module.Flat R C] (f : C →ₗc[R] D)

/-- After inverting the argument, the same induced action is left translation:
`(a f)(g) = f(a⁻¹g)`. -/
theorem inducedPointEval_inv_endOfPoint (g a : WithConv (C →ₐ[R] A))
    (z : A ⊗[R] induced f M) :
    inducedPointEval f g⁻¹ (endOfPoint (induced f M) a.ofConv z) =
      inducedPointEval f (a⁻¹ * g)⁻¹ z := by
  rw [inducedPointEval_endOfPoint, mul_inv_rev, inv_inv]

end Hopf

end CoalgHom

namespace BialgHom

open TauCeti TauCeti.Comodule CoalgHom

universe u v w x y

section Bialgebra

variable {R : Type u} [CommRing R]
  {C : Type v} [Semiring C] [Bialgebra R C]
  {D : Type w} [Semiring D] [Bialgebra R D]
  {M : Type x} [AddCommMonoid M] [Module R M] [Comodule R D M]
  (q : C →ₐc[R] D)
  {A : Type y} [CommSemiring A] [Algebra R A]

attribute [local instance] cofree

variable [Module.Flat R C]

/-- The cotensor condition implies `F(hg) = h F(g)` on points over every commutative
`R`-algebra, in any universe, over the base ring `R`. -/
theorem pointCochain_mapDomain_mul_of_mem_induced {t : M ⊗[R] C}
    (ht : t ∈ induced q.toCoalgHom M)
    (h : WithConv (D →ₐ[R] A)) (g : WithConv (C →ₐ[R] A)) :
    pointCochain M (q.mapDomain h * g).ofConv t =
      endOfPoint M h.ofConv (pointCochain M g.ofConv t) := by
  have heq := congrArg (fun z ↦ LinearMap.liftBaseChange A (pointCochain M h.ofConv)
    (pointCochain (M ⊗[R] D) g.ofConv z)) ((mem_induced_iff q.toCoalgHom).mp ht)
  rw [liftBaseChange_pointCochain_rTensor_coact] at heq
  -- `erw` matches Mathlib's class coercion with the coalgebra projection.
  erw [← BialgHom.toAlgHom_toLinearMap q, liftBaseChange_pointCochain_rTensor_comul] at heq
  simpa only [BialgHom.mapDomain_apply, toConv_ofConv] using heq.symm

/-- Evaluation is equivariant on the scalar extension of the induced comodule,
with values in `A ⊗[R] M`. -/
theorem inducedPointEval_mapDomain_mul (h : WithConv (D →ₐ[R] A))
    (g : WithConv (C →ₐ[R] A)) (z : A ⊗[R] induced q.toCoalgHom M) :
    q.toCoalgHom.inducedPointEval (q.mapDomain h * g) z =
      endOfPoint M h.ofConv (q.toCoalgHom.inducedPointEval g z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul a t =>
    rw [inducedPointEval_tmul, inducedPointEval_tmul,
      pointCochain_mapDomain_mul_of_mem_induced q t.property, map_smul]

end Bialgebra

section CommBialgebra

variable {R : Type u} [CommRing R]
  {C : Type v} [CommSemiring C] [Bialgebra R C]
  {D : Type w} [CommSemiring D] [Bialgebra R D]
  {M : Type x} [AddCommMonoid M] [Module R M] [Comodule R D M]
  (q : C →ₐc[R] D) [Module.Flat R C]

/-- Testing equivariance at the two tensor-factor points detects the cotensor equalizer. -/
theorem mem_induced_iff_pointCochain_mapDomain_mul_universal
    (t : M ⊗[R] C) :
    t ∈ induced q.toCoalgHom M ↔
      pointCochain M
          (q.mapDomain (toConv (Algebra.TensorProduct.includeLeft (R := R) (S := R)
            (A := D) (B := C))) *
            toConv Algebra.TensorProduct.includeRight).ofConv t =
        endOfPoint M (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := D) (B := C))
          (pointCochain M Algebra.TensorProduct.includeRight t) := by
  refine ⟨fun ht ↦ pointCochain_mapDomain_mul_of_mem_induced q ht _ _, fun ht ↦ ?_⟩
  apply (mem_induced_iff q.toCoalgHom).mpr
  apply (TensorProduct.assoc R M D C).injective
  apply (TensorProduct.comm R M (D ⊗[R] C)).injective
  rw [← liftBaseChange_pointCochain_pointCochain_includeLeft_includeRight,
    ← liftBaseChange_pointCochain_pointCochain_includeLeft_includeRight,
    liftBaseChange_pointCochain_rTensor_coact]
  -- `erw` matches Mathlib's class coercion with the coalgebra projection.
  erw [← BialgHom.toAlgHom_toLinearMap q, liftBaseChange_pointCochain_rTensor_comul]
  simpa only [BialgHom.mapDomain_apply, ofConv_toConv] using ht.symm

/-- A regular function belongs to cotensor induction exactly when `F(hg) = h F(g)` for
all points over commutative `R`-algebras in `Type (max v w)`. This universe suffices
because it contains `D ⊗[R] C`, the universal tensor-factor test. The forward rule
`pointCochain_mapDomain_mul_of_mem_induced` applies to value algebras in any universe. -/
theorem mem_induced_iff_forall_pointCochain_mapDomain_mul
    (t : M ⊗[R] C) :
    t ∈ induced q.toCoalgHom M ↔
      ∀ (A : Type max v w) [CommSemiring A] [Algebra R A]
        (h : WithConv (D →ₐ[R] A)) (g : WithConv (C →ₐ[R] A)),
        pointCochain M (q.mapDomain h * g).ofConv t =
          endOfPoint M h.ofConv (pointCochain M g.ofConv t) := by
  refine ⟨fun ht A _ _ h g ↦ pointCochain_mapDomain_mul_of_mem_induced q ht h g, fun ht ↦ ?_⟩
  exact (mem_induced_iff_pointCochain_mapDomain_mul_universal q t).mpr
    (ht (D ⊗[R] C) (toConv (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := D) (B := C)))
      (toConv Algebra.TensorProduct.includeRight))

end CommBialgebra

section Hopf

variable {R : Type u} [CommRing R]
  {C : Type v} [Semiring C] [HopfAlgebra R C]
  {D : Type w} [Semiring D] [HopfAlgebra R D]
  {M : Type x} [AddCommMonoid M] [Module R M] [Comodule R D M]
  (q : C →ₐc[R] D) [Module.Flat R C]
  {A : Type y} [CommSemiring A] [Algebra R A]

/-- Inverting the argument changes the cotensor convention to Jantzen's convention:
`f(gh) = h⁻¹ f(g)` for `f(g) = F(g⁻¹)`. -/
theorem pointCochain_mul_mapDomain_lTensor_antipode_of_mem_induced {t : M ⊗[R] C}
    (ht : t ∈ induced q.toCoalgHom M)
    (g : WithConv (C →ₐ[R] A)) (h : WithConv (D →ₐ[R] A)) :
    pointCochain M (g * q.mapDomain h).ofConv ((_root_.HopfAlgebraStruct.antipode R).lTensor M t) =
      endOfPoint M (h⁻¹).ofConv
        (pointCochain M g.ofConv ((_root_.HopfAlgebraStruct.antipode R).lTensor M t)) := by
  rw [pointCochain_lTensor_antipode, pointCochain_lTensor_antipode, mul_inv_rev, ← map_inv]
  exact pointCochain_mapDomain_mul_of_mem_induced q ht h⁻¹ g⁻¹

end Hopf

section CommHopf

variable {R : Type u} [CommRing R]
  {C : Type v} [CommSemiring C] [HopfAlgebra R C]
  {D : Type w} [CommSemiring D] [HopfAlgebra R D]
  {M : Type x} [AddCommMonoid M] [Module R M] [Comodule R D M]
  (q : C →ₐc[R] D) [Module.Flat R C]

/-- A cochain satisfies Jantzen's equation `f(gh) = h⁻¹ f(g)` exactly when applying
its coordinate antipode gives an induced function. The value algebras in `Type (max v w)`
contain the universal tensor-factor test. -/
theorem lTensor_antipode_mem_induced_iff_forall_pointCochain_mul_mapDomain
    (t : M ⊗[R] C) :
    (_root_.HopfAlgebraStruct.antipode R).lTensor M t ∈ induced q.toCoalgHom M ↔
      ∀ (A : Type max v w) [CommSemiring A] [Algebra R A]
        (g : WithConv (C →ₐ[R] A)) (h : WithConv (D →ₐ[R] A)),
        pointCochain M (g * q.mapDomain h).ofConv t =
          endOfPoint M (h⁻¹).ofConv (pointCochain M g.ofConv t) := by
  rw [mem_induced_iff_forall_pointCochain_mapDomain_mul]
  constructor
  · intro ht A _ _ g h
    simpa only [pointCochain_lTensor_antipode, mul_inv_rev, map_inv, inv_inv] using
      ht A h⁻¹ g⁻¹
  · intro ht A _ _ h g
    simpa only [pointCochain_lTensor_antipode, mul_inv_rev, map_inv, inv_inv] using
      ht A g⁻¹ h⁻¹

end CommHopf

end BialgHom
