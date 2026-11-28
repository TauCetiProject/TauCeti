/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Exact
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
import TauCeti.Algebra.AlgebraicGroup.FaithfullyFlatDescent
import TauCeti.RingTheory.Flat.Amitsur
import Mathlib.Algebra.Module.Projective

/-!
# Regular sections of extensions by vector groups

A short exact sequence of affine group schemes with kernel `Spec (Sym P)`, where `P` is
projective, admits a section of its underlying affine schemes. The section can be chosen
to preserve the identity. It need not be a group homomorphism.

`IsShortExact.regularVectorSection` supplies the section, with the simp lemmas
`IsShortExact.regularVectorSection_comp` and
`IsShortExact.counit_comp_regularVectorSection`.

The quotient map itself is a faithfully flat cover. The difference of its two tautological
points is an additive descent cocycle. Amitsur exactness and projectivity give a vector
translation making the tautological point descend through
`AlgHom.faithfullyFlatDescentMulEquiv`. A constant translation then normalizes its value
at the identity. The scalar cocycle calculation uses `Amitsur.exact_d₀_d₁` through
`Amitsur.exists_includeLeftSubRight_eq`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§15.9–15.10 and the proof of Theorem 16.26.
* The Stacks Project, Lemma 35.3.6, Tag 023M.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat.IsShortExact

universe u

variable {R : Type u} [CommRing R] {D E : _root_.CommHopfAlgCat.{u} R}
  {P : Type u} [AddCommGroup P] [Module R P]
  {p : D ⟶ E} {i : E ⟶ _root_.CommHopfAlgCat.of R (SymmetricAlgebra R P)}

private noncomputable def vectorInl (i : E ⟶ _root_.CommHopfAlgCat.of R (SymmetricAlgebra R P))
    (A : Type u) [CommRing A] [Algebra R A] :
    Multiplicative (P →ₗ[R] A) →* WithConv (E →ₐ[R] A) :=
  (BialgHom.mapDomain i.hom).comp AdditiveGroup.pointsMulEquiv.symm.toMonoidHom

private theorem vectorInl_injective (h : IsShortExact p i)
    (A : Type u) [CommRing A] [Algebra R A] :
    Function.Injective (vectorInl i A) :=
  (BialgHom.mapDomain_injective_of_surjective i.hom h.surjective).comp
    AdditiveGroup.pointsMulEquiv.symm.injective

private theorem mapValue_vectorInl {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (b : P →ₗ[R] A) :
    AlgHom.mapValue φ (vectorInl i A (Multiplicative.ofAdd b)) =
      vectorInl i B (Multiplicative.ofAdd (φ.toLinearMap.comp b)) := by
  unfold vectorInl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← MonoidHom.comp_apply, ← BialgHom.mapValue_mapDomain,
    MonoidHom.comp_apply, AdditiveGroup.mapValue_pointsMulEquiv_symm_apply]
  simp only [toAdd_ofAdd]

private theorem exists_vectorInl_eq (h : IsShortExact p i)
    {A : Type u} [CommRing A] [Algebra R A] (z : WithConv (E →ₐ[R] A))
    (hz : BialgHom.mapDomain p.hom z = 1) :
    ∃ b : P →ₗ[R] A, vectorInl i A (Multiplicative.ofAdd b) = z := by
  have heq : (BialgHom.mapDomain (A := A) p.hom).ker =
      (BialgHom.mapDomain (A := A) i.hom).range :=
    h.ker_mapPointsFunctor_app_eq_range (CommAlgCat.of R A)
  have hmem : z ∈ (BialgHom.mapDomain (A := A) i.hom).range := by
    rw [← heq]
    exact hz
  obtain ⟨n, hn⟩ := hmem
  exact ⟨(AdditiveGroup.pointsMulEquiv n).toAdd, by
    simpa only [vectorInl, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      ofAdd_toAdd, MulEquiv.symm_apply_apply] using hn⟩

section Cover

variable [Algebra D E] [IsScalarTower R D E]

private theorem localDifference_cocycle (h : IsShortExact p i)
    (b : P →ₗ[R] E ⊗[D] E)
    (hb : vectorInl i (E ⊗[D] E) (Multiplicative.ofAdd b) =
      toConv ((Algebra.TensorProduct.includeRight : E →ₐ[D] E ⊗[D] E).restrictScalars R) *
        (toConv (AlgHom.restrictScalars R
          (Algebra.TensorProduct.includeLeft : E →ₐ[D] E ⊗[D] E)))⁻¹) (v : P) :
    (Algebra.TensorProduct.includeLeft : E →ₐ[D] E ⊗[D] E).toLinearMap.lTensor E (b v) -
      (Algebra.TensorProduct.includeRight : E →ₐ[D] E ⊗[D] E).toLinearMap.lTensor E (b v) +
        1 ⊗ₜ[D] b v = 0 := by
  let f : E ⊗[D] E →ₐ[R] E ⊗[D] (E ⊗[D] E) :=
    AlgHom.restrictScalars R
      (Algebra.TensorProduct.map (AlgHom.id D E) Algebra.TensorProduct.includeLeft)
  let g : E ⊗[D] E →ₐ[R] E ⊗[D] (E ⊗[D] E) :=
    AlgHom.restrictScalars R
      (Algebra.TensorProduct.map (AlgHom.id D E) Algebra.TensorProduct.includeRight)
  let j : E ⊗[D] E →ₐ[R] E ⊗[D] (E ⊗[D] E) :=
    (Algebra.TensorProduct.includeRight : E ⊗[D] E →ₐ[D] E ⊗[D] (E ⊗[D] E)).restrictScalars R
  have hc : j.toLinearMap.comp b + f.toLinearMap.comp b = g.toLinearMap.comp b := by
    apply Multiplicative.ofAdd.injective
    apply vectorInl_injective h (E ⊗[D] (E ⊗[D] E))
    rw [ofAdd_add, map_mul, ← mapValue_vectorInl, ← mapValue_vectorInl,
      ← mapValue_vectorInl, hb]
    simp only [map_mul, map_inv]
    have h₁ : j.comp ((Algebra.TensorProduct.includeLeft : E →ₐ[D] E ⊗[D] E).restrictScalars R) =
        f.comp ((Algebra.TensorProduct.includeRight : E →ₐ[D] E ⊗[D] E).restrictScalars R) := by
      ext x
      simp [j, f]
    have h₂ : f.comp ((Algebra.TensorProduct.includeLeft : E →ₐ[D] E ⊗[D] E).restrictScalars R) =
        g.comp ((Algebra.TensorProduct.includeLeft : E →ₐ[D] E ⊗[D] E).restrictScalars R) := by
      ext x
      simp [f, g]
    have h₃ : j.comp ((Algebra.TensorProduct.includeRight : E →ₐ[D] E ⊗[D] E).restrictScalars R) =
        g.comp ((Algebra.TensorProduct.includeRight : E →ₐ[D] E ⊗[D] E).restrictScalars R) := by
      ext x
      simp [j, g]
    simp only [AlgHom.mapValue_apply, h₁, h₂, h₃]
    simp
  have hv := DFunLike.congr_fun hc v
  simp only [LinearMap.add_apply, LinearMap.comp_apply] at hv
  have hf (x : E ⊗[D] E) : f x =
      (Algebra.TensorProduct.includeLeft : E →ₐ[D] E ⊗[D] E).toLinearMap.lTensor E x := by
    induction x using TensorProduct.inductionOn with
    | tmul x y => simp [f]
    | add x y hx hy => simp_all
  have hg (x : E ⊗[D] E) : g x =
      (Algebra.TensorProduct.includeRight : E →ₐ[D] E ⊗[D] E).toLinearMap.lTensor E x := by
    induction x using TensorProduct.inductionOn with
    | tmul x y => simp [g]
    | add x y hx hy => simp_all
  rw [← hf, ← hg]
  simp only [j, AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars',
    Algebra.TensorProduct.includeRight_apply] at hv
  linear_combination hv

private theorem exists_localCorrection [Module.Projective R P] [Module.FaithfullyFlat D E]
    (h : IsShortExact p i) (b : P →ₗ[R] E ⊗[D] E)
    (hb : vectorInl i (E ⊗[D] E) (Multiplicative.ofAdd b) =
      toConv ((Algebra.TensorProduct.includeRight : E →ₐ[D] E ⊗[D] E).restrictScalars R) *
        (toConv (AlgHom.restrictScalars R
          (Algebra.TensorProduct.includeLeft : E →ₐ[D] E ⊗[D] E)))⁻¹) :
    ∃ a : P →ₗ[R] E, ∀ v, Algebra.TensorProduct.includeLeftSubRight D E (a v) = b v := by
  let δ := (Algebra.TensorProduct.includeLeftSubRight D E).restrictScalars R
  have hmem (v : P) : b v ∈ δ.range :=
    Amitsur.exists_includeLeftSubRight_eq (b v) (localDifference_cocycle h b hb v)
  obtain ⟨a, ha⟩ := Module.projective_lifting_property δ.rangeRestrict
    (b.codRestrict δ.range hmem) δ.surjective_rangeRestrict
  exact ⟨a, fun v ↦ congrArg Subtype.val (DFunLike.congr_fun ha v)⟩

private theorem correctedPoint_compatible
    (b : P →ₗ[R] E ⊗[D] E) (a : P →ₗ[R] E)
    (hb : vectorInl i (E ⊗[D] E) (Multiplicative.ofAdd b) =
      toConv ((Algebra.TensorProduct.includeRight : E →ₐ[D] E ⊗[D] E).restrictScalars R) *
        (toConv (AlgHom.restrictScalars R
          (Algebra.TensorProduct.includeLeft : E →ₐ[D] E ⊗[D] E)))⁻¹)
    (ha : ∀ v, Algebra.TensorProduct.includeLeftSubRight D E (a v) = b v) :
    vectorInl i E (Multiplicative.ofAdd a) * toConv (AlgHom.id R E) ∈
      AlgHom.descentSubgroup (R := R) (H := E) D E := by
  let l := (Algebra.TensorProduct.includeLeft : E →ₐ[D] E ⊗[D] E).restrictScalars R
  let r := (Algebra.TensorProduct.includeRight : E →ₐ[D] E ⊗[D] E).restrictScalars R
  have heq : l.toLinearMap.comp a = r.toLinearMap.comp a + b := by
    ext v
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, AlgHom.toLinearMap_apply,
      l, r, AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply] using
      (sub_eq_iff_eq_add.mp (ha v)).trans (add_comm _ _)
  have hb' : vectorInl i (E ⊗[D] E) (Multiplicative.ofAdd b) * toConv l = toConv r :=
    (eq_mul_inv_iff_mul_eq).mp hb
  have hc : AlgHom.mapValue l
      (vectorInl i E (Multiplicative.ofAdd a) * toConv (AlgHom.id R E)) =
      AlgHom.mapValue r
        (vectorInl i E (Multiplicative.ofAdd a) * toConv (AlgHom.id R E)) := by
    simp only [map_mul]
    rw [mapValue_vectorInl, mapValue_vectorInl]
    simp only [AlgHom.mapValue_apply, AlgHom.comp_id]
    rw [heq, ofAdd_add, map_mul, mul_assoc, hb']
  rw [AlgHom.mem_descentSubgroup_iff_apply]
  intro e
  simpa only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    l, r, AlgHom.coe_restrictScalars'] using
    DFunLike.congr_fun (congrArg WithConv.ofConv hc) e

end Cover

private theorem exists_section [Module.Projective R P] (h : IsShortExact p i) :
    ∃ s : E →ₐ[R] D, s.comp p.hom.toAlgHom = AlgHom.id R D := by
  let := p.hom.toAlgHom.toAlgebra
  have : IsScalarTower R D E :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (p.hom.toAlgHom.commutes r).symm
  have : Module.FaithfullyFlat D E := h.faithfullyFlat
  let l := (Algebra.TensorProduct.includeLeft : E →ₐ[D] E ⊗[D] E).restrictScalars R
  let r := (Algebra.TensorProduct.includeRight : E →ₐ[D] E ⊗[D] E).restrictScalars R
  have hbase : BialgHom.mapDomain p.hom (toConv r) =
      BialgHom.mapDomain p.hom (toConv l) := by
    apply WithConv.ofConv_injective
    ext d
    have hd : p.hom d = d • (1 : E) := Algebra.algebraMap_eq_smul_one d
    simp [BialgHom.mapDomain_apply, l, r, hd]
  obtain ⟨b, hb⟩ := exists_vectorInl_eq h (toConv r * (toConv l)⁻¹) (by
    simp only [map_mul, map_inv, hbase, mul_inv_cancel])
  obtain ⟨a, ha⟩ := exists_localCorrection h b hb
  let t := vectorInl i E (Multiplicative.ofAdd a) * toConv (AlgHom.id R E)
  let t' : AlgHom.descentSubgroup (R := R) (H := E) D E :=
    ⟨t, correctedPoint_compatible b a hb ha⟩
  let s := (AlgHom.faithfullyFlatDescentMulEquiv (R := R) (H := E) D E).symm t'
  have hs : AlgHom.mapValue (IsScalarTower.toAlgHom R D E) s = t := by
    simpa only [AlgHom.mapValue_apply, s] using
      AlgHom.mapValue_faithfullyFlatDescentMulEquiv_symm_apply D E t'
  refine ⟨s.ofConv, ?_⟩
  have hinl : BialgHom.mapDomain p.hom (vectorInl i E (Multiplicative.ofAdd a)) = 1 := by
    have heq : (BialgHom.mapDomain (A := E) p.hom).ker =
        (BialgHom.mapDomain (A := E) i.hom).range :=
      h.ker_mapPointsFunctor_app_eq_range (CommAlgCat.of R E)
    rw [← MonoidHom.mem_ker, heq]
    exact ⟨AdditiveGroup.pointsMulEquiv.symm (Multiplicative.ofAdd a), rfl⟩
  apply WithConv.toConv_injective
  apply (AlgHom.mapValue_injective (H := D) (φ := IsScalarTower.toAlgHom R D E)
    (FaithfulSMul.algebraMap_injective D E))
  rw [← BialgHom.mapDomain_apply, ← BialgHom.mapDomain_mapValue_apply, hs]
  simp only [t, map_mul, hinl, one_mul, BialgHom.mapDomain_apply,
    AlgHom.id_comp, AlgHom.mapValue_apply]
  rfl

/-- A regular section of a vector extension can be chosen to send the identity to the
identity. No smoothness, finite type, or characteristic assumption is required. -/
theorem exists_regularVectorSection [Module.Projective R P]
    (h : IsShortExact p i) :
    ∃ s : E →ₐ[R] D, s.comp p.hom.toAlgHom = AlgHom.id R D ∧
      (Bialgebra.counitAlgHom R D).comp s = Bialgebra.counitAlgHom R E := by
  obtain ⟨s, hs⟩ := exists_section h
  let e := AlgHom.mapValue (Bialgebra.counitAlgHom R D) (toConv s)
  let c := AlgHom.mapValue (Algebra.ofId R D) e
  have hps : BialgHom.mapDomain p.hom (toConv s) = toConv (AlgHom.id R D) := by
    simp only [BialgHom.mapDomain_apply, hs]
  have hpe : BialgHom.mapDomain p.hom e = 1 := by
    rw [BialgHom.mapDomain_mapValue_apply, hps]
    apply WithConv.ofConv_injective
    simp [AlgHom.mapValue_apply, Bialgebra.ofConv_one_eq_counitAlgHom]
  have hpc : BialgHom.mapDomain p.hom c = 1 := by
    rw [BialgHom.mapDomain_mapValue_apply, hpe, map_one]
  have hec : AlgHom.mapValue (Bialgebra.counitAlgHom R D) c = e := by
    apply WithConv.ofConv_injective
    ext x
    simp [c, AlgHom.mapValue_apply]
  refine ⟨(c⁻¹ * toConv s).ofConv, ?_, ?_⟩
  · apply WithConv.toConv_injective
    rw [toConv_ofConv, ← BialgHom.mapDomain_apply, map_mul, map_inv, hpc, hps,
      inv_one, one_mul]
  · have he : AlgHom.mapValue (Bialgebra.counitAlgHom R D) (c⁻¹ * toConv s) = 1 := by
      simp only [map_mul, map_inv, hec]
      exact inv_mul_cancel e
    simpa only [AlgHom.mapValue_apply, Bialgebra.ofConv_one_eq_counitAlgHom] using
      congrArg WithConv.ofConv he

/-- A chosen identity-preserving regular section of an affine vector extension. -/
noncomputable def regularVectorSection [Module.Projective R P] (h : IsShortExact p i) :
    E →ₐ[R] D := h.exists_regularVectorSection.choose

/-- The chosen regular section is a right inverse of the quotient map on schemes. -/
@[simp]
theorem regularVectorSection_comp [Module.Projective R P] (h : IsShortExact p i) :
    h.regularVectorSection.comp p.hom.toAlgHom = AlgHom.id R D :=
  h.exists_regularVectorSection.choose_spec.1

/-- The chosen regular section preserves the identity. -/
@[simp]
theorem counit_comp_regularVectorSection [Module.Projective R P] (h : IsShortExact p i) :
    (Bialgebra.counitAlgHom R D).comp h.regularVectorSection = Bialgebra.counitAlgHom R E :=
  h.exists_regularVectorSection.choose_spec.2

end TauCeti.CommHopfAlgCat.IsShortExact
