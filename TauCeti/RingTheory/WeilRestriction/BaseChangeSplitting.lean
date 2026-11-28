/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.TotallySplit
public import TauCeti.RingTheory.WeilRestriction.Basic
public import TauCeti.RingTheory.PiTensorProduct.Map

/-!
# Splitting the coordinate algebra of a Weil restriction

If a field extension `Ω/K` splits the finite `K`-algebra `B`, the base change of
`Res_{B/K} C` to `Ω` is the tensor product of the algebras obtained by extending scalars in
`C` along the algebra maps `B →ₐ[K] Ω`. Thus the corresponding affine scheme becomes the
product of its conjugates. The isomorphism is obtained from the representing property on
every commutative `Ω`-algebra. See Bruhat and Tits, *Groupes réductifs sur un corps local II*,
Publ. Math. IHÉS 60 (1984), §1.5.14–1.5.16.
-/

public section

open scoped TensorProduct
open Algebra.TensorProduct
open TauCeti.Algebra.IsFiniteSplit

namespace TauCeti.Algebra.WeilRestriction

section Conjugate

variable {K B Ω : Type*} [CommRing K] [CommRing B] [Algebra K B]
  [CommRing Ω] [Algebra K Ω]
variable (C : Type*) [CommRing C] [Algebra B C]

/-- The conjugate of a `B`-algebra `C` along a map `τ : B →ₐ[K] Ω` is the base
change `Ω ⊗[B] C` for the scalar map `τ`. -/
def Conjugate (τ : B →ₐ[K] Ω) : Type _ :=
  letI := τ.toRingHom.toAlgebra
  Ω ⊗[B] C

-- Elaborate the tensor product construction locally so that `Conjugate` stays opaque to importers.
noncomputable instance (τ : B →ₐ[K] Ω) : CommRing (Conjugate C τ) :=
  private_decl% (by
    unfold Conjugate
    letI := τ.toRingHom.toAlgebra
    infer_instance)

noncomputable instance (τ : B →ₐ[K] Ω) : Algebra Ω (Conjugate C τ) :=
  private_decl% (letI : Algebra B Ω := τ.toRingHom.toAlgebra
    id (α := Algebra Ω (Conjugate C τ))
      (Algebra.TensorProduct.leftAlgebra : Algebra Ω (Ω ⊗[B] C)))

/-- The inclusion of `C` into its conjugate along `τ`. -/
noncomputable def conjugateInclude (τ : B →ₐ[K] Ω) : C →+* Conjugate C τ :=
  private_decl% (letI : Algebra B Ω := τ.toRingHom.toAlgebra
    (includeRight : C →ₐ[B] Ω ⊗[B] C).toRingHom)

variable {T : Type*} [CommRing T] [Algebra Ω T]

/-- An `Ω`-algebra map from the conjugate along `τ` to `T` corresponds to a ring map
`C → T` extending the composite `B → Ω → T`. -/
def conjugateHomEquiv (τ : B →ₐ[K] Ω) :
    (Conjugate C τ →ₐ[Ω] T) ≃
      {f : C →+* T // f.comp (algebraMap B C) = (algebraMap Ω T).comp (τ : B →+* Ω)} :=
  private_decl% (by
    letI := τ.toRingHom.toAlgebra
    letI := ((algebraMap Ω T).comp (τ : B →+* Ω)).toAlgebra
    letI : IsScalarTower B Ω T := IsScalarTower.of_algebraMap_eq' rfl
    let e : (C →ₐ[B] T) ≃
        {f : C →+* T // f.comp (algebraMap B C) = (algebraMap Ω T).comp (τ : B →+* Ω)} :=
      { toFun := fun f ↦ ⟨f.toRingHom, RingHom.ext fun b : B ↦ f.commutes b⟩
        invFun := fun f ↦ { f.val with commutes' := fun b : B ↦ RingHom.congr_fun f.property b }
        left_inv := fun f ↦ AlgHom.ext fun _ ↦ rfl
        right_inv := fun f ↦ Subtype.ext rfl }
    exact id (α := (Conjugate C τ →ₐ[Ω] T) ≃ _)
      ((liftEquivRight B Ω C T).symm.trans e))

variable {C} in
/-- Restriction to `C` evaluates a map on the inclusion into the conjugate. -/
@[simp]
theorem conjugateHomEquiv_apply (τ : B →ₐ[K] Ω)
    (f : Conjugate C τ →ₐ[Ω] T) (c : C) :
    (conjugateHomEquiv C τ f : C →+* T) c = f (conjugateInclude C τ c) :=
  (rfl)

variable {C} in
/-- The map induced by `f` from the conjugate agrees with `f` on the copy of `C`. -/
@[simp]
theorem conjugateHomEquiv_symm_apply (τ : B →ₐ[K] Ω)
    (f : {f : C →+* T // f.comp (algebraMap B C) = (algebraMap Ω T).comp τ}) (c : C) :
    (conjugateHomEquiv C τ).symm f (conjugateInclude C τ c) = f.val c := by
  rw [← conjugateHomEquiv_apply, Equiv.apply_symm_apply]

variable {C} in
/-- Two maps out of a conjugate agree if their restrictions to `C` agree. -/
@[ext]
theorem conjugateHom_ext {τ : B →ₐ[K] Ω} {f g : Conjugate C τ →ₐ[Ω] T}
    (h : f.toRingHom.comp (conjugateInclude C τ) = g.toRingHom.comp (conjugateInclude C τ)) :
    f = g :=
  (conjugateHomEquiv C τ).injective <| Subtype.ext <| RingHom.ext fun c ↦ by
    simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      conjugateHomEquiv_apply] using
      RingHom.congr_fun h c

/-- The inclusion of `C` sends a base scalar `b` to the scalar `τ b` in the conjugate. -/
@[simp]
theorem conjugateInclude_algebraMap (τ : B →ₐ[K] Ω) (b : B) :
    conjugateInclude C τ (algebraMap B C b) = algebraMap Ω (Conjugate C τ) (τ b) := by
  simpa only [RingHom.comp_apply, AlgHom.coe_toRingHom, conjugateHomEquiv_apply, AlgHom.id_apply]
    using RingHom.congr_fun (conjugateHomEquiv C τ (AlgHom.id Ω (Conjugate C τ))).property b

end Conjugate

variable (K B Ω C : Type*) [Field K] [CommRing B] [Algebra K B]
  [Field Ω] [Algebra K Ω] [CommRing C] [Algebra B C]
variable {T T' : Type*} [CommRing T] [Algebra Ω T] [CommRing T'] [Algebra Ω T']
variable [Module.Finite K B] [Algebra.IsFiniteSplit Ω (Ω ⊗[K] B)]
variable [Algebra K T] [IsScalarTower K Ω T] [Algebra K T'] [IsScalarTower K Ω T']

private noncomputable def baseChangeSplittingHomEquiv :
    ((Ω ⊗[K] WeilRestriction K B C) →ₐ[Ω] T) ≃
      ((τ : B →ₐ[K] Ω) → Conjugate C τ →ₐ[Ω] T) :=
  (liftEquivRight K Ω (WeilRestriction K B C) T).symm.trans <|
    (homEquiv K B C T).trans <|
      (algHomTensorProductEquivPi K Ω B C T).trans <|
        Equiv.piCongrRight fun τ ↦ (conjugateHomEquiv C τ).symm

variable {K B Ω C}

private theorem baseChangeSplittingHomEquiv_apply
    (f : (Ω ⊗[K] WeilRestriction K B C) →ₐ[Ω] T) (τ : B →ₐ[K] Ω) (c : C) :
    baseChangeSplittingHomEquiv K B Ω C f τ (conjugateInclude C τ c) =
      Algebra.TensorProduct.productMap
        ((IsScalarTower.toAlgHom K Ω T).comp τ) (AlgHom.id K T)
        (homEquiv K B C T ((f.restrictScalars K).comp includeRight) c) := by
  simp only [baseChangeSplittingHomEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply, Pi.map_apply,
    liftEquivRight_symm_apply, conjugateHomEquiv_symm_apply, algHomTensorProductEquivPi_apply]

private theorem baseChangeSplittingHomEquiv_comp (g : T →ₐ[Ω] T')
    (f : (Ω ⊗[K] WeilRestriction K B C) →ₐ[Ω] T) (τ : B →ₐ[K] Ω) :
    baseChangeSplittingHomEquiv K B Ω C (g.comp f) τ =
      g.comp (baseChangeSplittingHomEquiv K B Ω C f τ) := by
  apply conjugateHom_ext
  apply RingHom.ext
  intro c
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.comp_apply,
    baseChangeSplittingHomEquiv_apply]
  have h : ((g.comp f).restrictScalars K).comp includeRight =
      (g.restrictScalars K).comp ((f.restrictScalars K).comp includeRight) :=
    AlgHom.ext fun _ ↦ rfl
  rw [h, homEquiv_comp]
  let φ := (IsScalarTower.toAlgHom K Ω T').comp τ
  let ψ := (IsScalarTower.toAlgHom K Ω T).comp τ
  let gK := g.restrictScalars K
  have hφ : gK.comp ψ = φ := AlgHom.ext fun b ↦ g.commutes (τ b)
  have hmap : (productMap φ (AlgHom.id K T')).comp (lTensor B gK) =
      gK.comp (productMap ψ (AlgHom.id K T)) := by
    rw [comp_productMap, hφ, AlgHom.comp_id]
    exact Algebra.TensorProduct.ext' (by simp)
  exact AlgHom.congr_fun hmap (homEquiv K B C T ((f.restrictScalars K).comp includeRight) c)

variable (K B Ω C)

/-- Over a splitting field of `B`, the base change of `Res_{B/K} C` is the tensor product
over `Ω` of the conjugates of `C` along the `K`-algebra maps `B →ₐ[K] Ω`. -/
noncomputable def baseChangeSplittingAlgEquiv :
    Ω ⊗[K] WeilRestriction K B C ≃ₐ[Ω] ⨂[Ω] τ : B →ₐ[K] Ω, Conjugate C τ := by
  classical
  letI := Fintype.ofFinite (B →ₐ[K] Ω)
  let T := ⨂[Ω] τ : B →ₐ[K] Ω, Conjugate C τ
  letI : Algebra K T := Algebra.compHom T (algebraMap K Ω)
  -- Use the scalar action from the composite algebra in the tower instance.
  letI : SMul K T := (inferInstance : Algebra K T).toSMul
  letI : IsScalarTower K Ω T := IsScalarTower.of_algebraMap_eq' rfl
  let forward := (baseChangeSplittingHomEquiv K B Ω C (T := T)).symm PiTensorProduct.singleAlgHom
  let parts := baseChangeSplittingHomEquiv K B Ω C (AlgHom.id Ω (Ω ⊗[K] WeilRestriction K B C))
  let backward := PiTensorProduct.productMap parts
  have hforward τ : baseChangeSplittingHomEquiv K B Ω C forward τ =
      PiTensorProduct.singleAlgHom τ :=
    congrFun (Equiv.apply_symm_apply (baseChangeSplittingHomEquiv K B Ω C) _) τ
  have hleft : backward.comp forward = AlgHom.id Ω _ := by
    apply (baseChangeSplittingHomEquiv K B Ω C).injective
    funext τ
    rw [baseChangeSplittingHomEquiv_comp, hforward, PiTensorProduct.productMap_comp_singleAlgHom]
  have hright : forward.comp backward = AlgHom.id Ω _ := by
    apply PiTensorProduct.algHom_ext
    intro τ
    rw [AlgHom.comp_assoc, PiTensorProduct.productMap_comp_singleAlgHom, AlgHom.id_comp]
    simpa only [parts, ← baseChangeSplittingHomEquiv_comp, AlgHom.comp_id] using hforward τ
  exact AlgEquiv.ofAlgHom forward backward hright hleft

variable {K B Ω C}

/-- The inverse of the splitting sends the copy of `c` in the `τ`-factor to the
universal point at `c` evaluated along `τ` on the coefficient factor. -/
@[simp↓]
theorem baseChangeSplittingAlgEquiv_symm_singleAlgHom_conjugateInclude
    [decEq : DecidableEq (B →ₐ[K] Ω)] (τ : B →ₐ[K] Ω) (c : C) :
    (baseChangeSplittingAlgEquiv K B Ω C).symm
        (PiTensorProduct.singleAlgHom τ (conjugateInclude C τ c)) =
      Algebra.TensorProduct.productMap
        ((IsScalarTower.toAlgHom K Ω (Ω ⊗[K] WeilRestriction K B C)).comp τ)
        includeRight (universalPoint K B C c) := by
  -- The splitting was constructed with `Classical.decEq`; unfolding needs the same instance.
  have h : decEq = Classical.decEq (B →ₐ[K] Ω) := Subsingleton.elim _ _
  cases h
  classical
  let := Fintype.ofFinite (B →ₐ[K] Ω)
  rw [baseChangeSplittingAlgEquiv, AlgEquiv.ofAlgHom_symm_apply,
    PiTensorProduct.productMap_singleAlgHom, baseChangeSplittingHomEquiv_apply]
  simp only [homEquiv_apply, AlgHom.comp_apply]
  let S := Ω ⊗[K] WeilRestriction K B C
  let φ := (IsScalarTower.toAlgHom K Ω S).comp τ
  have hmap : (productMap φ (AlgHom.id K S)).comp
      (lTensor B (((AlgHom.id Ω S).restrictScalars K).comp includeRight)) =
        productMap φ includeRight :=
    Algebra.TensorProduct.ext' (by simp)
  exact AlgHom.congr_fun hmap (universalPoint K B C c)

/-- Acting by `σ` on the scalars of the base-changed Weil restriction carries the copy
of `c` in the factor at `τ` to its copy in the factor at `σ ∘ τ`. Together with its action
on `Ω`, this describes the semilinear permutation of the conjugates. -/
theorem baseChangeSplittingAlgEquiv_map_singleAlgHom_conjugateInclude
    [DecidableEq (B →ₐ[K] Ω)] (σ : Ω ≃ₐ[K] Ω) (τ : B →ₐ[K] Ω) (c : C) :
    let e := baseChangeSplittingAlgEquiv K B Ω C
    e (Algebra.TensorProduct.map (σ : Ω →ₐ[K] Ω) (AlgHom.id K (WeilRestriction K B C))
        (e.symm (PiTensorProduct.singleAlgHom τ (conjugateInclude C τ c)))) =
      PiTensorProduct.singleAlgHom ((σ : Ω →ₐ[K] Ω).comp τ)
        (conjugateInclude C ((σ : Ω →ₐ[K] Ω).comp τ) c) := by
  apply (baseChangeSplittingAlgEquiv K B Ω C).symm.injective
  simp only [AlgEquiv.symm_apply_apply,
    baseChangeSplittingAlgEquiv_symm_singleAlgHom_conjugateInclude]
  let S := Ω ⊗[K] WeilRestriction K B C
  let ι := IsScalarTower.toAlgHom K Ω S
  have hmap : (Algebra.TensorProduct.map (σ : Ω →ₐ[K] Ω) (AlgHom.id K _)).comp
      (productMap (ι.comp τ) includeRight) =
        productMap (ι.comp ((σ : Ω →ₐ[K] Ω).comp τ)) includeRight := by
    rw [comp_productMap]
    congr 1
    exact AlgHom.ext fun b ↦ by simp
  exact AlgHom.congr_fun hmap (universalPoint K B C c)

end TauCeti.Algebra.WeilRestriction
