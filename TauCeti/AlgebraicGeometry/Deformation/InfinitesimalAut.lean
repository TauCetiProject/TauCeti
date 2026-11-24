/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.Algebra.DualNumber.TensorProduct
public import TauCeti.AlgebraicGeometry.AugmentationPoint.Basic
public import TauCeti.RingTheory.Derivation.DualNumber

/-!
# Infinitesimal automorphisms of a scheme over the dual numbers

Let `X` be a scheme with a morphism `f : X ⟶ Spec R`. Its trivial first-order deformation is the
base change `X[ε] = X ×_{Spec R} Spec R[ε]`, a scheme over `Spec R[ε]`, and `X` sits inside it
over the section `ε ↦ 0`. The **infinitesimal automorphisms** of `X` are the automorphisms of
`X[ε]` over `Spec R[ε]` that restrict to the identity of `X`.

For an affine scheme `X = Spec A` over `Spec R`, these are the `R`-derivations of `A`: the
derivation `d` gives the spectrum of the automorphism `a + b ε ↦ a + (b + d a) ε` of
`A[ε] ≅ A ⊗[R] R[ε]`, and addition of derivations corresponds to composition. This is the
affine case of the identification of infinitesimal automorphisms with global derivations of
the structure sheaf; the algebra is `TauCeti.derivationEquivInfinitesimalDualNumberAut`.

## Main definitions

* `TauCeti.AlgebraicGeometry.dualNumberDeformation f`: the base change of `f : X ⟶ Spec R` to
  `Spec R[ε]`, as a scheme over `Spec R[ε]`.
* `TauCeti.AlgebraicGeometry.dualNumberDeformationι f`: the inclusion of `X` over `ε ↦ 0`.
* `TauCeti.AlgebraicGeometry.infinitesimalAut f`: the automorphisms of the base change over
  `Spec R[ε]` that restrict to the identity of `X`.
* `TauCeti.AlgebraicGeometry.derivationMulEquivInfinitesimalAut R A`: for `X = Spec A`, the
  derivations `Der_R(A, A)`, with addition written multiplicatively, are the infinitesimal
  automorphisms.

## References

* R. Hartshorne, *Deformation Theory*, Graduate Texts in Mathematics 257, Springer, 2010,
  Chapter 1, for infinitesimal automorphisms as derivations.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct DualNumber TrivSqZeroExt

namespace TauCeti.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

/-! ### The trivial first-order deformation -/

section Deformation

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The **trivial first-order deformation** `X[ε] = X ×_{Spec R} Spec R[ε]` of a scheme `X` over
`Spec R`, as a scheme over `Spec R[ε]` through the second projection. -/
abbrev dualNumberDeformation : Over (Spec (.of R[ε])) :=
  Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R[ε]))))

/-- The inclusion `X ⟶ X[ε]` over the section `Spec R ⟶ Spec R[ε]`, `ε ↦ 0`. -/
def dualNumberDeformationι : X ⟶ (dualNumberDeformation f).left :=
  pullback.lift (𝟙 X) (f ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R : R[ε] →+* R)))
    (by rw [Category.assoc, ← AlgHom.specSplitEpi_section, SplitEpi.id, Category.comp_id,
      Category.id_comp])

@[reassoc (attr := simp)]
theorem dualNumberDeformationι_fst :
    dualNumberDeformationι f ≫ pullback.fst _ _ = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem dualNumberDeformationι_snd :
    dualNumberDeformationι f ≫ pullback.snd _ _ =
      f ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R : R[ε] →+* R)) :=
  pullback.lift_snd _ _ _

/-- The **infinitesimal automorphisms** of a scheme `X` over `Spec R`: the automorphisms of its
trivial first-order deformation `X[ε]` over `Spec R[ε]` that restrict to the identity of `X`
along the inclusion over `ε ↦ 0`. -/
def infinitesimalAut : Subgroup (Aut (dualNumberDeformation f)) where
  carrier := {e | dualNumberDeformationι f ≫ e.asIso.hom.left = dualNumberDeformationι f}
  one_mem' := by simp
  mul_mem' {e e'} he he' := by
    simp only [Set.mem_ofPred_eq, Aut.mul_asIso, Iso.trans_hom, Over.comp_left] at he he' ⊢
    rw [reassoc_of% he', he]
  inv_mem' {e} he := by
    simp only [Set.mem_ofPred_eq, Aut.inv_asIso, Iso.symm_hom] at he ⊢
    conv_lhs => rw [← he]
    rw [Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.comp_id]

theorem mem_infinitesimalAut_iff (e : Aut (dualNumberDeformation f)) :
    e ∈ infinitesimalAut f ↔
      dualNumberDeformationι f ≫ e.asIso.hom.left = dualNumberDeformationι f :=
  Iff.rfl

end Deformation

/-! ### The affine case -/

section Affine

variable (R) (A : Type u) [CommRing A] [Algebra R A]

/-- The base change `A ⊗[R] R[ε] ≃ₐ[R] A[ε]`, specialized to the base ring. -/
private abbrev tensorEquiv : A ⊗[R] R[ε] ≃ₐ[R] A[ε] :=
  dualNumberAlgebraTensorAlgEquiv R R A

/-- The reduction `A ⊗[R] R[ε] → A`, `a ⊗ x ↦ a x₀`, along `ε ↦ 0`. -/
private abbrev reduction : A ⊗[R] R[ε] →+* A :=
  (TrivSqZeroExt.fstHom R A A : A[ε] →+* A).comp (tensorEquiv R A : A ⊗[R] R[ε] →+* A[ε])

/-- The ring automorphism of `A ⊗[R] R[ε]` corresponding to an automorphism of `A[ε]`. -/
private abbrev tensorConj (τ : A[ε] ≃ₐ[R] A[ε]) : A ⊗[R] R[ε] ≃ₐ[R] A ⊗[R] R[ε] :=
  ((tensorEquiv R A).trans τ).trans (tensorEquiv R A).symm

/-- The trivial first-order deformation `(Spec A)[ε]` of `Spec A` over `Spec R`. -/
abbrev affineDualNumberDeformation : Over (Spec (.of R[ε])) :=
  dualNumberDeformation (Spec.map (CommRingCat.ofHom (algebraMap R A)))

variable {A}

/-- The inclusion over `ε ↦ 0`, read in `Spec (A ⊗[R] R[ε])`, is the spectrum of the reduction
`a ⊗ x ↦ a x₀`. -/
private theorem dualNumberDeformationι_pullbackSpecIso_hom :
    dualNumberDeformationι (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≫
        (pullbackSpecIso R A R[ε]).hom =
      Spec.map (CommRingCat.ofHom (reduction R A)) := by
  rw [← Iso.eq_comp_inv]
  refine pullback.hom_ext ?_ ?_
  · rw [dualNumberDeformationι_fst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rw [show (reduction R A).comp Algebra.TensorProduct.includeLeftRingHom = RingHom.id A by
      ext a; simp]
    exact Spec.map_id (CommRingCat.of A) |>.symm
  · rw [dualNumberDeformationι_snd, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    · change algebraMap R A (algebraMap R R[ε] x).fst =
        (tensorEquiv R A ((1 : A) ⊗ₜ algebraMap R R[ε] x)).fst
      simp
    · change algebraMap R A (ε : R[ε]).fst = (tensorEquiv R A ((1 : A) ⊗ₜ (ε : R[ε]))).fst
      simp

/-- The ring endomorphism of `A ⊗[R] R[ε]` whose spectrum is an endomorphism of `(Spec A)[ε]`,
read through `pullbackSpecIso`. -/
private def tensorHom (e : Aut (affineDualNumberDeformation R A)) :
    CommRingCat.of (A ⊗[R] R[ε]) ⟶ CommRingCat.of (A ⊗[R] R[ε]) :=
  Spec.preimage ((pullbackSpecIso R A R[ε]).inv ≫ e.asIso.hom.left ≫
    (pullbackSpecIso R A R[ε]).hom)

private theorem spec_map_tensorHom (e : Aut (affineDualNumberDeformation R A)) :
    Spec.map (tensorHom R e) = (pullbackSpecIso R A R[ε]).inv ≫ e.asIso.hom.left ≫
      (pullbackSpecIso R A R[ε]).hom :=
  Spec.map_preimage _

private theorem tensorHom_mul (e e' : Aut (affineDualNumberDeformation R A)) :
    tensorHom R (e * e') = tensorHom R e ≫ tensorHom R e' := by
  refine Spec.map_injective ?_
  simp [Spec.map_comp, spec_map_tensorHom]

private theorem tensorHom_one :
    tensorHom R (1 : Aut (affineDualNumberDeformation R A)) = 𝟙 _ := by
  refine Spec.map_injective ?_
  simp [spec_map_tensorHom]

private theorem tensorHom_inv_mul (e : Aut (affineDualNumberDeformation R A)) :
    tensorHom R e⁻¹ ≫ tensorHom R e = 𝟙 _ := by
  rw [← tensorHom_mul, inv_mul_cancel, tensorHom_one]

private theorem tensorHom_mul_inv (e : Aut (affineDualNumberDeformation R A)) :
    tensorHom R e ≫ tensorHom R e⁻¹ = 𝟙 _ := by
  rw [← tensorHom_mul, mul_inv_cancel, tensorHom_one]

/-- An automorphism of `(Spec A)[ε]` over `Spec R[ε]` fixes the coefficients `1 ⊗ x`. -/
private theorem tensorHom_tmul (e : Aut (affineDualNumberDeformation R A)) (x : R[ε]) :
    (tensorHom R e).hom (1 ⊗ₜ x) = 1 ⊗ₜ x := by
  have h : Spec.map (tensorHom R e) ≫ Spec.map (CommRingCat.ofHom (R := R[ε])
      (S := A ⊗[R] R[ε]) (RingHomClass.toRingHom Algebra.TensorProduct.includeRight)) =
      Spec.map (CommRingCat.ofHom (R := R[ε]) (S := A ⊗[R] R[ε])
        (RingHomClass.toRingHom Algebra.TensorProduct.includeRight)) := by
    rw [spec_map_tensorHom, Category.assoc, Category.assoc, pullbackSpecIso_hom_snd,
      ← pullbackSpecIso_inv_snd]
    exact (pullbackSpecIso R A R[ε]).inv ≫= Over.w e.asIso.hom
  rw [← Spec.map_comp] at h
  exact congr($(Spec.map_injective h).hom x)

/-- The ring automorphism of `A ⊗[R] R[ε]` underlying an automorphism of `(Spec A)[ε]`. -/
private def tensorAlgEquiv (e : Aut (affineDualNumberDeformation R A)) :
    A ⊗[R] R[ε] ≃ₐ[R] A ⊗[R] R[ε] where
  toFun := (tensorHom R e).hom
  invFun := (tensorHom R e⁻¹).hom
  left_inv x := congr($(tensorHom_mul_inv R e).hom x)
  right_inv x := congr($(tensorHom_inv_mul R e).hom x)
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' r := by
    simpa [Algebra.TensorProduct.algebraMap_apply', Algebra.algebraMap_eq_smul_one,
      Algebra.TensorProduct.one_def] using tensorHom_tmul R e (algebraMap R R[ε] r)

/-- The automorphism of `A[ε]` underlying an automorphism of `(Spec A)[ε]` over `Spec R[ε]`. -/
def toDualNumberAlgEquiv (e : Aut (affineDualNumberDeformation R A)) :
    A[ε] ≃ₐ[R] A[ε] :=
  ((tensorEquiv R A).symm.trans (tensorAlgEquiv R e)).trans (tensorEquiv R A)

/-- The automorphism of `A[ε]` underlying an automorphism of `(Spec A)[ε]` fixes `ε`. -/
@[simp]
theorem toDualNumberAlgEquiv_eps (e : Aut (affineDualNumberDeformation R A)) :
    toDualNumberAlgEquiv R e ε = ε := by
  have h := tensorHom_tmul R e ε
  simp [toDualNumberAlgEquiv, tensorAlgEquiv, h]

/-- The automorphism of `(Spec A)[ε]` over `Spec R[ε]` given by an automorphism of `A[ε]`
fixing `ε`: its spectrum, read through `A ⊗[R] R[ε] ≅ A[ε]` and `pullbackSpecIso`. -/
def ofDualNumberAlgEquiv (τ : A[ε] ≃ₐ[R] A[ε]) (hτ : τ ε = ε) :
    Aut (affineDualNumberDeformation R A) :=
  .of <| Over.isoMk (pullbackSpecIso R A R[ε] ≪≫
      Scheme.Spec.mapIso (tensorConj R A τ).toRingEquiv.toCommRingCatIso.op ≪≫
        (pullbackSpecIso R A R[ε]).symm) <| by
    have h' : ((tensorConj R A τ).toAlgHom.comp Algebra.TensorProduct.includeRight :
        R[ε] →ₐ[R] A ⊗[R] R[ε]) = Algebra.TensorProduct.includeRight :=
      DualNumber.algHom_ext (by simp [hτ])
    have h : (tensorConj R A τ : A ⊗[R] R[ε] →+* A ⊗[R] R[ε]).comp
        (RingHomClass.toRingHom Algebra.TensorProduct.includeRight) =
        RingHomClass.toRingHom Algebra.TensorProduct.includeRight :=
      congrArg AlgHom.toRingHom h'
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom, Category.assoc,
      Over.mk_hom, pullbackSpecIso_inv_snd]
    rw [← pullbackSpecIso_hom_snd]
    congr 1
    change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- On the underlying scheme, `ofDualNumberAlgEquiv τ` is the spectrum of `τ`, read through
`A ⊗[R] R[ε] ≃ A[ε]` and `pullbackSpecIso`. -/
theorem ofDualNumberAlgEquiv_asIso_hom_left (τ : A[ε] ≃ₐ[R] A[ε]) (hτ : τ ε = ε) :
    (ofDualNumberAlgEquiv R τ hτ).asIso.hom.left =
      (pullbackSpecIso R A R[ε]).hom ≫ Spec.map (CommRingCat.ofHom
        ((((dualNumberAlgebraTensorAlgEquiv R R A).trans τ).trans
          (dualNumberAlgebraTensorAlgEquiv R R A).symm : A ⊗[R] R[ε] ≃ₐ[R] A ⊗[R] R[ε]) :
            A ⊗[R] R[ε] →+* A ⊗[R] R[ε])) ≫ (pullbackSpecIso R A R[ε]).inv := by
  simp [ofDualNumberAlgEquiv]

private theorem tensorHom_ofDualNumberAlgEquiv (τ : A[ε] ≃ₐ[R] A[ε]) (hτ : τ ε = ε) :
    tensorHom R (ofDualNumberAlgEquiv R τ hτ) =
      CommRingCat.ofHom (tensorConj R A τ : A ⊗[R] R[ε] →+* A ⊗[R] R[ε]) := by
  refine Spec.map_injective ?_
  rw [spec_map_tensorHom]
  simp [ofDualNumberAlgEquiv]

@[simp]
theorem toDualNumberAlgEquiv_ofDualNumberAlgEquiv (τ : A[ε] ≃ₐ[R] A[ε]) (hτ : τ ε = ε) :
    toDualNumberAlgEquiv R (ofDualNumberAlgEquiv R τ hτ) = τ := by
  ext z <;> simp [toDualNumberAlgEquiv, tensorAlgEquiv, tensorHom_ofDualNumberAlgEquiv]

@[simp]
theorem ofDualNumberAlgEquiv_toDualNumberAlgEquiv
    (e : Aut (affineDualNumberDeformation R A)) :
    ofDualNumberAlgEquiv R (toDualNumberAlgEquiv R e) (toDualNumberAlgEquiv_eps R e) = e := by
  have h : CommRingCat.ofHom (tensorConj R A (toDualNumberAlgEquiv R e) :
      A ⊗[R] R[ε] →+* A ⊗[R] R[ε]) = tensorHom R e := by
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    simp [toDualNumberAlgEquiv, tensorAlgEquiv]
  rw [← tensorHom_ofDualNumberAlgEquiv R _ (toDualNumberAlgEquiv_eps R e)] at h
  ext1
  refine Iso.ext (Over.OverMorphism.ext ?_)
  have h' := congrArg Spec.map h
  rw [spec_map_tensorHom, spec_map_tensorHom] at h'
  simpa using h'

private theorem hom_left_comp_pullbackSpecIso_hom (e : Aut (affineDualNumberDeformation R A)) :
    e.asIso.hom.left ≫ (pullbackSpecIso R A R[ε]).hom =
      (pullbackSpecIso R A R[ε]).hom ≫ Spec.map (tensorHom R e) := by
  rw [spec_map_tensorHom, Iso.hom_inv_id_assoc]

/-- An automorphism `e` of `(Spec A)[ε]` over `Spec R[ε]`, read through `pullbackSpecIso`, is the
spectrum of `toDualNumberAlgEquiv e`, read through `A ⊗[R] R[ε] ≃ A[ε]`. -/
theorem spec_map_toDualNumberAlgEquiv (e : Aut (affineDualNumberDeformation R A)) :
    Spec.map (CommRingCat.ofHom
        ((((dualNumberAlgebraTensorAlgEquiv R R A).trans (toDualNumberAlgEquiv R e)).trans
          (dualNumberAlgebraTensorAlgEquiv R R A).symm : A ⊗[R] R[ε] ≃ₐ[R] A ⊗[R] R[ε]) :
            A ⊗[R] R[ε] →+* A ⊗[R] R[ε])) =
      (pullbackSpecIso R A R[ε]).inv ≫ e.asIso.hom.left ≫ (pullbackSpecIso R A R[ε]).hom := by
  rw [← spec_map_tensorHom]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  simp [toDualNumberAlgEquiv, tensorAlgEquiv]

/-- An automorphism of `(Spec A)[ε]` over `Spec R[ε]` restricts to the identity of `Spec A` exactly
when the corresponding automorphism of `A[ε]` reduces to the identity modulo `ε`. -/
theorem mem_infinitesimalAut_iff_fst (e : Aut (affineDualNumberDeformation R A)) :
    e ∈ infinitesimalAut (Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔
      ∀ z, (toDualNumberAlgEquiv R e z).fst = z.fst := by
  rw [mem_infinitesimalAut_iff, ← cancel_mono (pullbackSpecIso R A R[ε]).hom, Category.assoc,
    hom_left_comp_pullbackSpecIso_hom, reassoc_of% dualNumberDeformationι_pullbackSpecIso_hom,
    dualNumberDeformationι_pullbackSpecIso_hom, ← Spec.map_comp, Spec.map_injective.eq_iff]
  constructor
  · intro h z
    have := congr($(h).hom ((tensorEquiv R A).symm z))
    simpa [toDualNumberAlgEquiv, tensorAlgEquiv] using this
  · intro h
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    have := h (tensorEquiv R A x)
    simpa [toDualNumberAlgEquiv, tensorAlgEquiv] using this

/-- Composition of automorphisms of `(Spec A)[ε]` corresponds to composition of the automorphisms
of `A[ε]` in the opposite order. -/
theorem toDualNumberAlgEquiv_mul (e e' : Aut (affineDualNumberDeformation R A)) :
    toDualNumberAlgEquiv R (e * e') = toDualNumberAlgEquiv R e' * toDualNumberAlgEquiv R e := by
  ext z <;> simp [toDualNumberAlgEquiv, tensorAlgEquiv, tensorHom_mul]

@[simp]
theorem toDualNumberAlgEquiv_one :
    toDualNumberAlgEquiv R (1 : Aut (affineDualNumberDeformation R A)) = 1 := by
  ext z <;> simp [toDualNumberAlgEquiv, tensorAlgEquiv, tensorHom_one]

theorem toDualNumberAlgEquiv_injective :
    Function.Injective (toDualNumberAlgEquiv R (A := A)) := by
  intro e e' h
  rw [← ofDualNumberAlgEquiv_toDualNumberAlgEquiv R e,
    ← ofDualNumberAlgEquiv_toDualNumberAlgEquiv R e']
  congr 1

/-- The infinitesimal automorphism of `(Spec A)[ε]` attached to a derivation `d` of `A`: the
spectrum of `a + b ε ↦ a + (b + d a) ε`. -/
def infinitesimalAutOfDerivation (d : Derivation R A A) :
    infinitesimalAut (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  ⟨ofDualNumberAlgEquiv R d.toDualNumberAut (by simp),
    (mem_infinitesimalAut_iff_fst R _).2 fun z ↦ by
      rw [toDualNumberAlgEquiv_ofDualNumberAlgEquiv, Derivation.toDualNumberAut_fst]⟩

/-- The automorphism of `A[ε]` underlying the infinitesimal automorphism attached to `d` is
`a + b ε ↦ a + (b + d a) ε`. -/
@[simp]
theorem toDualNumberAlgEquiv_infinitesimalAutOfDerivation (d : Derivation R A A) :
    toDualNumberAlgEquiv R (infinitesimalAutOfDerivation R d).val = d.toDualNumberAut := by
  unfold infinitesimalAutOfDerivation
  exact toDualNumberAlgEquiv_ofDualNumberAlgEquiv R _ (by simp)

variable (A) in
/-- The infinitesimal automorphisms attached to derivations, as a homomorphism from the
derivations with addition written multiplicatively. -/
private def infinitesimalAutOfDerivationHom :
    Multiplicative (Derivation R A A) →*
      infinitesimalAut (Spec.map (CommRingCat.ofHom (algebraMap R A))) where
  toFun d := infinitesimalAutOfDerivation R d.toAdd
  map_one' := by
    refine Subtype.ext (toDualNumberAlgEquiv_injective R ?_)
    simp
  map_mul' d d' := by
    refine Subtype.ext (toDualNumberAlgEquiv_injective R ?_)
    simp only [toDualNumberAlgEquiv_infinitesimalAutOfDerivation, toAdd_mul,
      Subgroup.coe_mul, toDualNumberAlgEquiv_mul]
    rw [add_comm, Derivation.toDualNumberAut_add]

variable (A) in
/-- **Infinitesimal automorphisms of an affine scheme are derivations.** For an `R`-algebra `A`,
the `R`-derivations of `A`, with addition written multiplicatively, are the automorphisms of the
trivial first-order deformation `(Spec A)[ε]` over `Spec R[ε]` that restrict to the identity of
`Spec A`: a derivation `d` gives the spectrum of `a + b ε ↦ a + (b + d a) ε`. -/
def derivationMulEquivInfinitesimalAut :
    Multiplicative (Derivation R A A) ≃*
      infinitesimalAut (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  MulEquiv.ofBijective (infinitesimalAutOfDerivationHom R A)
    ⟨fun d d' h ↦ by
      have h' := congrArg (fun e ↦ toDualNumberAlgEquiv R (Subtype.val e)) h
      simp only [infinitesimalAutOfDerivationHom, MonoidHom.coe_mk, OneHom.coe_mk,
        toDualNumberAlgEquiv_infinitesimalAutOfDerivation] at h'
      refine (derivationEquivInfinitesimalDualNumberAut (R := R) (A := A)).injective
        (Subtype.ext ?_)
      simpa using h',
    fun e ↦ by
      obtain ⟨d, hd⟩ := (derivationEquivInfinitesimalDualNumberAut (R := R) (A := A)).surjective
        ⟨toDualNumberAlgEquiv R e.val, by
          simpa using (mem_infinitesimalAut_iff_fst R e.val).1 e.property⟩
      refine ⟨d, Subtype.ext (toDualNumberAlgEquiv_injective R ?_)⟩
      have := congrArg Subtype.val hd
      simpa [infinitesimalAutOfDerivationHom] using this⟩

@[simp]
theorem derivationMulEquivInfinitesimalAut_apply (d : Multiplicative (Derivation R A A)) :
    derivationMulEquivInfinitesimalAut R A d = infinitesimalAutOfDerivation R d.toAdd := by
  simp [derivationMulEquivInfinitesimalAut, infinitesimalAutOfDerivationHom]

end Affine

end TauCeti.AlgebraicGeometry
