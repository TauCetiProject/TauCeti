/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Morphism
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Regular
public import TauCeti.Algebra.Coalgebra.Subcomodule.DirectedUnion
public import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Recovering a map from natural tensor coactions

A natural family of coactions on tensor products of finite comodules determines a map
on the tensor product of their coefficient coalgebras. On finite subcomodules of the
regular comodules, this map is the contraction against the two restricted counits.
Compatibility with inclusions permits gluing, and naturality along coefficient morphisms
identifies its values on arbitrary matrix coefficients. The resulting map preserves
comultiplication and counit, and it is the unique coalgebra map with this coefficient formula.
The supplied coactions are recovered by the ordinary tensor shuffle followed by this map.

This is the coefficient construction used to recover multiplication from a tensor product
on a category of comodules, without presupposing a multiplication on its coalgebra.

## References

* P. Deligne and J. S. Milne, *Tannakian Categories*, proof of Proposition 2.16.
* M. Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct
open TensorProduct

namespace TauCeti

universe u v w x

variable {k : Type u} [Field k]
variable {B : Type v} {C : Type w} {D : Type x}
variable [AddCommGroup B] [Module k B] [Coalgebra k B]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup D] [Module k D] [Coalgebra k D]

/-- Right coactions on the underlying tensor spaces of two finite comodules,
natural under tensor products of comodule morphisms. -/
structure TensorCoaction where
  /-- The supplied coaction on each tensor space. -/
  comodule (M : FGComoduleCat.{u, v, v} k B) (N : FGComoduleCat.{u, w, w} k C) :
    Comodule k D (M ⊗[k] N)
  /-- Naturality for a pair of comodule morphisms. -/
  naturality {M M' : FGComoduleCat.{u, v, v} k B}
    {N N' : FGComoduleCat.{u, w, w} k C}
    (f : Comodule.Hom k B M M') (g : Comodule.Hom k C N N') :
    map (map f.toLinearMap g.toLinearMap) LinearMap.id ∘ₗ (comodule M N).coact =
      (comodule M' N').coact ∘ₗ map f.toLinearMap g.toLinearMap

namespace TensorCoaction

/-- Natural tensor coactions are determined by their component coactions. -/
@[ext]
theorem ext {ρ σ : TensorCoaction (k := k) (B := B) (C := C) (D := D)}
    (h : ∀ M N, (ρ.comodule M N).coact = (σ.comodule M N).coact) : ρ = σ := by
  cases ρ with
  | mk a ha =>
    cases σ with
    | mk b hb =>
      have hab : a = b := funext fun M => funext fun N => Comodule.ext (h M N)
      cases hab
      rfl

variable (ρ : TensorCoaction (k := k) (B := B) (C := C) (D := D))

/-- The coefficient of the supplied coaction at two vectors and two covectors. -/
def coefficient (M : FGComoduleCat.{u, v, v} k B)
    (N : FGComoduleCat.{u, w, w} k C) (φ : Module.Dual k M) (ψ : Module.Dual k N)
    (m : M) (n : N) : D :=
  letI := ρ.comodule M N
  Comodule.matrixCoefficient (C := D) (dualDistrib k M N (φ ⊗ₜ[k] ψ)) (m ⊗ₜ[k] n)

/-- A tensor coefficient contracts the supplied coaction against the tensor of the two covectors. -/
theorem coefficient_def (M : FGComoduleCat.{u, v, v} k B)
    (N : FGComoduleCat.{u, w, w} k C) (φ : Module.Dual k M) (ψ : Module.Dual k N)
    (m : M) (n : N) :
    ρ.coefficient M N φ ψ m n =
      TensorProduct.lid k D
        (map (dualDistrib k M N (φ ⊗ₜ[k] ψ)) LinearMap.id
          ((ρ.comodule M N).coact (m ⊗ₜ[k] n))) := by
  let := ρ.comodule M N
  rw [coefficient, Comodule.matrixCoefficient_def]

/-- Tensor coefficients are natural under a pair of comodule morphisms. -/
theorem coefficient_naturality {M M' : FGComoduleCat.{u, v, v} k B}
    {N N' : FGComoduleCat.{u, w, w} k C}
    (f : Comodule.Hom k B M M') (g : Comodule.Hom k C N N')
    (φ : Module.Dual k M') (ψ : Module.Dual k N') (m : M) (n : N) :
    ρ.coefficient M' N' φ ψ (f m) (g n) =
      ρ.coefficient M N (φ.comp f.toLinearMap) (ψ.comp g.toLinearMap) m n := by
  let := ρ.comodule M N
  let := ρ.comodule M' N'
  let t : Comodule.Hom k D (M ⊗[k] N) (M' ⊗[k] N') :=
    ⟨map f.toLinearMap g.toLinearMap, ρ.naturality f g⟩
  have ht : t (m ⊗ₜ[k] n) = f m ⊗ₜ[k] g n := by simp [t]
  have hφ : (dualDistrib k M' N' (φ ⊗ₜ[k] ψ)).comp t.toLinearMap =
      dualDistrib k M N ((φ.comp f.toLinearMap) ⊗ₜ[k] (ψ.comp g.toLinearMap)) := by
    ext x y
    simp [t]
  simpa only [coefficient, ht, hφ] using
    (Comodule.matrixCoefficient_map t (dualDistrib k M' N' (φ ⊗ₜ[k] ψ)) (m ⊗ₜ[k] n))

private abbrev FiniteRegular (A : Type*) [AddCommGroup A] [Module k A] [Coalgebra k A] :=
  Subcomodule.finiteSubcomodules (R := k) (C := A) (M := A)

private instance finiteRegular_finite {A : Type*}
    [AddCommGroup A] [Module k A] [Coalgebra k A] (S : FiniteRegular (k := k) A) :
    Module.Finite k S.val := Subcomodule.mem_finiteSubcomodules.mp S.property

private noncomputable abbrev regularObj {A : Type*}
    [AddCommGroup A] [Module k A] [Coalgebra k A] (S : FiniteRegular (k := k) A) :
    FGComoduleCat k A := FGComoduleCat.of (R := k) (C := A) S.val

private noncomputable abbrev regularMap (S : FiniteRegular (k := k) B)
    (T : FiniteRegular (k := k) C) : S.val ⊗[k] T.val →ₗ[k] D :=
  letI := ρ.comodule (regularObj S) (regularObj T)
  Comodule.matrixCoefficientLinear (C := D)
    (dualDistrib k S.val T.val
      (((Coalgebra.counit (R := k) (A := B)).comp (SMulMemClass.subtype S.val)) ⊗ₜ[k]
        ((Coalgebra.counit (R := k) (A := C)).comp (SMulMemClass.subtype T.val))))

-- This identifies the contraction on a regular tensor space with the family coefficient.
private theorem regularMap_tmul (S : FiniteRegular (k := k) B)
    (T : FiniteRegular (k := k) C) (s : S.val) (t : T.val) :
    ρ.regularMap S T (s ⊗ₜ[k] t) =
      ρ.coefficient (regularObj S) (regularObj T)
        ((Coalgebra.counit (R := k) (A := B)).comp (SMulMemClass.subtype S.val))
        ((Coalgebra.counit (R := k) (A := C)).comp (SMulMemClass.subtype T.val)) s t := rfl

private noncomputable def regularInclusion {A : Type*}
    [AddCommGroup A] [Module k A] [Coalgebra k A]
    (S S' : FiniteRegular (k := k) A) (h : S.val ≤ S'.val) :
    Comodule.Hom k A (regularObj S) (regularObj S') :=
  (Subcomodule.subtype S.val).codRestrict S'.val (fun s => by simpa using h s.property)

private theorem regularInclusion_toLinearMap {A : Type*}
    [AddCommGroup A] [Module k A] [Coalgebra k A]
    (S S' : FiniteRegular (k := k) A) (h : S.val ≤ S'.val) :
    (regularInclusion S S' h).toLinearMap = Submodule.inclusion h := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  have hval := Comodule.Hom.codRestrict_apply (Subcomodule.subtype S.val) S'.val
    (fun s => by simpa using h s.property) s
  rw [Subcomodule.subtype_apply] at hval
  exact hval.trans (Submodule.coe_inclusion h s).symm

private theorem regularInclusion_apply {A : Type*}
    [AddCommGroup A] [Module k A] [Coalgebra k A]
    (S S' : FiniteRegular (k := k) A) (h : S.val ≤ S'.val) (s : S.val) :
    regularInclusion S S' h s = Submodule.inclusion h s :=
  DFunLike.congr_fun (regularInclusion_toLinearMap S S' h) s

private theorem subtype_comp_regularInclusion {A : Type*}
    [AddCommGroup A] [Module k A] [Coalgebra k A]
    (S S' : FiniteRegular (k := k) A) (h : S.val ≤ S'.val) :
    (SMulMemClass.subtype S'.val).comp (regularInclusion S S' h).toLinearMap =
      SMulMemClass.subtype S.val := by
  rw [regularInclusion_toLinearMap]
  exact Submodule.subtype_comp_inclusion S.val.toSubmodule S'.val.toSubmodule h

private theorem regularMap_left (S S' : FiniteRegular (k := k) B)
    (h : S.val ≤ S'.val) (T : FiniteRegular (k := k) C) (s : S.val) (t : T.val) :
    ρ.regularMap S' T (Submodule.inclusion h s ⊗ₜ[k] t) =
      ρ.regularMap S T (s ⊗ₜ[k] t) := by
  rw [regularMap_tmul, regularMap_tmul]
  have hc := ρ.coefficient_naturality (M := regularObj S) (M' := regularObj S')
    (N := regularObj T) (N' := regularObj T) (regularInclusion S S' h)
    (Comodule.Hom.id k C T.val)
    ((Coalgebra.counit (R := k) (A := B)).comp (SMulMemClass.subtype S'.val))
    ((Coalgebra.counit (R := k) (A := C)).comp (SMulMemClass.subtype T.val)) s t
  simp only [Comodule.Hom.id_toLinearMap, LinearMap.comp_id] at hc
  rw [LinearMap.comp_assoc, subtype_comp_regularInclusion] at hc
  simpa only [regularInclusion_apply, Comodule.Hom.id_apply,
    Comodule.Hom.id_toLinearMap, LinearMap.comp_id] using hc

private theorem regularMap_right (S : FiniteRegular (k := k) B)
    (T T' : FiniteRegular (k := k) C) (h : T.val ≤ T'.val) (s : S.val) (t : T.val) :
    ρ.regularMap S T' (s ⊗ₜ[k] Submodule.inclusion h t) =
      ρ.regularMap S T (s ⊗ₜ[k] t) := by
  rw [regularMap_tmul, regularMap_tmul]
  have hc := ρ.coefficient_naturality (M := regularObj S) (M' := regularObj S)
    (N := regularObj T) (N' := regularObj T') (Comodule.Hom.id k B S.val)
    (regularInclusion T T' h)
    ((Coalgebra.counit (R := k) (A := B)).comp (SMulMemClass.subtype S.val))
    ((Coalgebra.counit (R := k) (A := C)).comp (SMulMemClass.subtype T'.val)) s t
  simp only [Comodule.Hom.id_toLinearMap, LinearMap.comp_id] at hc
  rw [LinearMap.comp_assoc, subtype_comp_regularInclusion] at hc
  simpa only [regularInclusion_apply, Comodule.Hom.id_apply,
    Comodule.Hom.id_toLinearMap, LinearMap.comp_id] using hc

private noncomputable def regularLeft (S : FiniteRegular (k := k) B) :
    S.val →ₗ[k] C →ₗ[k] D :=
  LinearMap.flip (Subcomodule.finiteSubcomoduleLift
    (fun T => LinearMap.flip (curry (ρ.regularMap S T)))
    (by
      intro T T' h
      ext t s
      exact (ρ.regularMap_right S T T' h s t).symm))

private theorem regularLeft_apply (S : FiniteRegular (k := k) B)
    (T : FiniteRegular (k := k) C) (s : S.val) (t : T.val) :
    ρ.regularLeft S s t = ρ.regularMap S T (s ⊗ₜ[k] t) := by
  unfold regularLeft
  exact congrArg (fun f : S.val →ₗ[k] D => f s)
    (Subcomodule.finiteSubcomoduleLift_apply _ _ T t)

private theorem regularLeft_compatible (S S' : FiniteRegular (k := k) B) (h : S.val ≤ S'.val) :
    ρ.regularLeft S = (ρ.regularLeft S').comp (Submodule.inclusion h) := by
  ext s c
  obtain ⟨T, hT, hc⟩ := Subcomodule.exists_finite_subcomodule_mem (R := k) (C := C) c
  let T' : FiniteRegular (k := k) C := ⟨T, Subcomodule.mem_finiteSubcomodules.mpr hT⟩
  rw [← Subtype.coe_mk c hc, regularLeft_apply ρ S T', LinearMap.comp_apply,
    regularLeft_apply ρ S' T']
  exact (ρ.regularMap_left S S' h T' s ⟨c, hc⟩).symm

/-- The linear map reconstructed from the natural tensor coactions by contraction on
finite regular subcomodules. -/
noncomputable def linearMap : B ⊗[k] C →ₗ[k] D :=
  TensorProduct.lift (Subcomodule.finiteSubcomoduleLift (ρ.regularLeft) ρ.regularLeft_compatible)

private theorem linearMap_regular (S : FiniteRegular (k := k) B)
    (T : FiniteRegular (k := k) C) (s : S.val) (t : T.val) :
    ρ.linearMap ((s : B) ⊗ₜ[k] (t : C)) = ρ.regularMap S T (s ⊗ₜ[k] t) := by
  unfold linearMap
  rw [TensorProduct.lift.tmul, Subcomodule.finiteSubcomoduleLift_apply, regularLeft_apply]

/-- The reconstructed map sends tensors of arbitrary finite-comodule coefficients to
coefficients of the supplied tensor coaction. -/
@[simp]
theorem linearMap_matrixCoefficient (M : FGComoduleCat.{u, v, v} k B)
    (N : FGComoduleCat.{u, w, w} k C) (φ : Module.Dual k M) (ψ : Module.Dual k N)
    (m : M) (n : N) :
    ρ.linearMap (Comodule.matrixCoefficient (C := B) φ m ⊗ₜ[k]
      Comodule.matrixCoefficient (C := C) ψ n) = ρ.coefficient M N φ ψ m n := by
  let S : FiniteRegular (k := k) B :=
    ⟨(Comodule.matrixCoefficientSubcoalgebra (R := k) (C := B) (M := M)).toRegularSubcomodule,
      Subcomodule.mem_finiteSubcomodules.mpr inferInstance⟩
  let T : FiniteRegular (k := k) C :=
    ⟨(Comodule.matrixCoefficientSubcoalgebra (R := k) (C := C) (M := N)).toRegularSubcomodule,
      Subcomodule.mem_finiteSubcomodules.mpr inferInstance⟩
  let f := Comodule.matrixCoefficientSubcoalgebraHom (C := B) φ
  let g := Comodule.matrixCoefficientSubcoalgebraHom (C := C) ψ
  have hf : (Coalgebra.counit (R := k) (A := B)).comp
      ((SMulMemClass.subtype S.val).comp f.toLinearMap) = φ := by
    ext m
    simp [S, f]
  have hg : (Coalgebra.counit (R := k) (A := C)).comp
      ((SMulMemClass.subtype T.val).comp g.toLinearMap) = ψ := by
    ext n
    simp [T, g]
  have h := ρ.coefficient_naturality (M := M) (M' := regularObj S)
    (N := N) (N' := regularObj T) f g
    ((Coalgebra.counit (R := k) (A := B)).comp (SMulMemClass.subtype S.val))
    ((Coalgebra.counit (R := k) (A := C)).comp (SMulMemClass.subtype T.val)) m n
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hf, hg] at h
  have hs : (f m : B) = Comodule.matrixCoefficient (C := B) φ m := by simp [f]
  have ht : (g n : C) = Comodule.matrixCoefficient (C := C) ψ n := by simp [g]
  rw [← hs, ← ht, linearMap_regular ρ S T]
  rw [regularMap_tmul]
  exact h

/-- The coefficient formula uniquely characterizes the reconstructed linear map. -/
theorem linearMap_unique (F : B ⊗[k] C →ₗ[k] D)
    (hF : ∀ (M : FGComoduleCat.{u, v, v} k B) (N : FGComoduleCat.{u, w, w} k C)
      (φ : Module.Dual k M) (ψ : Module.Dual k N) (m : M) (n : N),
      F (Comodule.matrixCoefficient (C := B) φ m ⊗ₜ[k]
        Comodule.matrixCoefficient (C := C) ψ n) = ρ.coefficient M N φ ψ m n) :
    F = ρ.linearMap := by
  apply Comodule.tensorProduct_linearMap_ext_matrixCoefficient
  intro M N φ ψ m n
  rw [hF, linearMap_matrixCoefficient]

/-- Expanding the supplied tensor coaction in bases of its two factors recovers its
coefficients through the reconstructed map. -/
theorem coact_tmul_eq_sum_basis (M : FGComoduleCat.{u, v, v} k B)
    (N : FGComoduleCat.{u, w, w} k C) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι k M) (c : Module.Basis κ k N) (m : M) (n : N) :
    (ρ.comodule M N).coact (m ⊗ₜ[k] n) =
      ∑ i, ∑ j, (b i ⊗ₜ[k] c j) ⊗ₜ[k]
        ρ.linearMap (Comodule.matrixCoefficient (C := B) (b.coord i) m ⊗ₜ[k]
          Comodule.matrixCoefficient (C := C) (c.coord j) n) := by
  classical
  let := ρ.comodule M N
  have hcoord (i : ι) (j : κ) : (b.tensorProduct c).coord (i, j) =
      dualDistrib k M N (b.coord i ⊗ₜ[k] c.coord j) := by
    ext x y
    simp [Module.Basis.coord_apply, mul_comm]
  rw [Comodule.coact_eq_sum_basis_matrixCoefficient (C := D) (b.tensorProduct c)]
  simp only [Fintype.sum_prod_type, Module.Basis.tensorProduct_apply, hcoord,
    linearMap_matrixCoefficient, coefficient]

/-- The supplied coaction is the tensor shuffle of the two original coactions,
followed by the reconstructed map on the coefficient factors. -/
theorem coact_tmul (M : FGComoduleCat.{u, v, v} k B)
    (N : FGComoduleCat.{u, w, w} k C) (m : M) (n : N) :
    (ρ.comodule M N).coact (m ⊗ₜ[k] n) =
      map LinearMap.id ρ.linearMap
        (AlgebraTensorModule.tensorTensorTensorComm k k k k M B N C
          (Comodule.coact (C := B) m ⊗ₜ[k] Comodule.coact (C := C) n)) := by
  classical
  let b := Module.finBasis k M
  let c := Module.finBasis k N
  rw [ρ.coact_tmul_eq_sum_basis M N b c,
    Comodule.coact_eq_sum_basis_matrixCoefficient (C := B) b,
    Comodule.coact_eq_sum_basis_matrixCoefficient (C := C) c]
  simp only [sum_tmul, tmul_sum, map_sum, AlgebraTensorModule.tensorTensorTensorComm_tmul,
    map_tmul, LinearMap.id_apply]
  exact Finset.sum_comm

private theorem comul_coefficient (M : FGComoduleCat.{u, v, v} k B)
    (N : FGComoduleCat.{u, w, w} k C) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι k M) (c : Module.Basis κ k N)
    (φ : Module.Dual k M) (ψ : Module.Dual k N) (m : M) (n : N) :
    Coalgebra.comul (ρ.coefficient M N φ ψ m n) =
      ∑ i, ∑ j, ρ.coefficient M N φ ψ (b i) (c j) ⊗ₜ[k]
        ρ.coefficient M N (b.coord i) (c.coord j) m n := by
  let := ρ.comodule M N
  rw [coefficient, Comodule.comul_matrixCoefficient, ρ.coact_tmul_eq_sum_basis M N b c]
  simp only [map_sum, map_tmul, LinearMap.id_apply, Comodule.matrixCoefficientLinear_apply,
    linearMap_matrixCoefficient, coefficient]

private theorem map_comul :
    map ρ.linearMap ρ.linearMap ∘ₗ Coalgebra.comul = Coalgebra.comul ∘ₗ ρ.linearMap := by
  apply Comodule.tensorProduct_linearMap_ext_matrixCoefficient
  intro M N φ ψ m n
  classical
  let b := Module.finBasis k M
  let c := Module.finBasis k N
  simp only [LinearMap.comp_apply, linearMap_matrixCoefficient, TensorProduct.comul_tmul,
    Comodule.comul_matrixCoefficient_eq_sum b, Comodule.comul_matrixCoefficient_eq_sum c,
    ρ.comul_coefficient M N b c, sum_tmul, tmul_sum, map_sum,
    AlgebraTensorModule.tensorTensorTensorComm_tmul, map_tmul, linearMap_matrixCoefficient]
  exact Finset.sum_comm

private theorem counit_comp :
    Coalgebra.counit ∘ₗ ρ.linearMap = Coalgebra.counit := by
  apply Comodule.tensorProduct_linearMap_ext_matrixCoefficient
  intro M N φ ψ m n
  let := ρ.comodule M N
  simp only [LinearMap.comp_apply, linearMap_matrixCoefficient, coefficient,
    Comodule.counit_matrixCoefficient, dualDistrib_apply, TensorProduct.counit_tmul,
    smul_eq_mul, mul_comm]

/-- The unique coalgebra map whose values on coefficient tensors are the coefficients
of the supplied natural tensor coactions. -/
noncomputable def coalgHom : B ⊗[k] C →ₗc[k] D where
  toLinearMap := ρ.linearMap
  counit_comp := ρ.counit_comp
  map_comp_comul := ρ.map_comul

/-- The underlying linear map of the reconstructed coalgebra map. -/
@[simp]
theorem coalgHom_toLinearMap : (ρ.coalgHom : B ⊗[k] C →ₗ[k] D) = ρ.linearMap := (rfl)

/-- The reconstructed coalgebra map has the prescribed value on every coefficient tensor. -/
@[simp]
theorem coalgHom_matrixCoefficient (M : FGComoduleCat.{u, v, v} k B)
    (N : FGComoduleCat.{u, w, w} k C) (φ : Module.Dual k M) (ψ : Module.Dual k N)
    (m : M) (n : N) :
    ρ.coalgHom (Comodule.matrixCoefficient (C := B) φ m ⊗ₜ[k]
      Comodule.matrixCoefficient (C := C) ψ n) = ρ.coefficient M N φ ψ m n :=
  ρ.linearMap_matrixCoefficient M N φ ψ m n

/-- The coefficient formula uniquely characterizes the reconstructed coalgebra map. -/
theorem coalgHom_unique (F : B ⊗[k] C →ₗc[k] D)
    (hF : ∀ (M : FGComoduleCat.{u, v, v} k B) (N : FGComoduleCat.{u, w, w} k C)
      (φ : Module.Dual k M) (ψ : Module.Dual k N) (m : M) (n : N),
      F (Comodule.matrixCoefficient (C := B) φ m ⊗ₜ[k]
        Comodule.matrixCoefficient (C := C) ψ n) = ρ.coefficient M N φ ψ m n) :
    F = ρ.coalgHom :=
  CoalgHom.linearMapOfClass_injective (ρ.linearMap_unique F.toLinearMap hF)

end TensorCoaction

/-- The constant coaction associated to a group-like element, on every tensor space. -/
def _root_.GroupLike.tensorCoaction (g : GroupLike k D) :
    TensorCoaction (k := k) (B := B) (C := C) (D := D) where
  comodule M N := Comodule.groupLike g
  naturality f g := by
    ext m n
    simp

/-- The constant tensor family assigns the group-like comodule to each tensor space. -/
@[simp]
theorem _root_.GroupLike.tensorCoaction_comodule (g : GroupLike k D)
    (M : FGComoduleCat.{u, v, v} k B) (N : FGComoduleCat.{u, w, w} k C) :
    (g.tensorCoaction (B := B) (C := C)).comodule M N = Comodule.groupLike g := (rfl)

/-- Coefficients of the constant tensor coaction are evaluation times its group-like element. -/
@[simp]
theorem _root_.GroupLike.tensorCoaction_coefficient (g : GroupLike k D)
    (M : FGComoduleCat.{u, v, v} k B) (N : FGComoduleCat.{u, w, w} k C)
    (φ : Module.Dual k M) (ψ : Module.Dual k N) (m : M) (n : N) :
    (g.tensorCoaction (B := B) (C := C)).coefficient M N φ ψ m n =
      (φ m * ψ n) • (g : D) := by
  rw [TensorCoaction.coefficient, GroupLike.tensorCoaction_comodule]
  simp

/-- Over the scalar coalgebras, the constant coaction reconstructs the map taking
`1 ⊗ 1` to the specified group-like element. -/
@[simp]
theorem _root_.GroupLike.tensorCoaction_coalgHom_one
    {E : Type*} [AddCommGroup E] [Module k E] [Coalgebra k E] (g : GroupLike k E) :
    (g.tensorCoaction (B := k) (C := k)).coalgHom (1 ⊗ₜ[k] 1) = g := by
  let M := FGComoduleCat.of (R := k) (C := k) k
  have h := (g.tensorCoaction (B := k) (C := k)).coalgHom_matrixCoefficient M M
    (Coalgebra.counit (R := k) (A := k)) (Coalgebra.counit (R := k) (A := k)) 1 1
  simpa [M, Comodule.matrixCoefficient_def] using h

end TauCeti
