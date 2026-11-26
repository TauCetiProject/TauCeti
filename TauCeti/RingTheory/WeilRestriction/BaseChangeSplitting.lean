/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TotallySplit
public import TauCeti.RingTheory.WeilRestriction.Basic
public import TauCeti.RingTheory.PiTensorProduct.Map
import TauCeti.RingTheory.Etale.Galois

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

namespace TauCeti.Algebra.WeilRestriction

section Conjugate

variable {K B Ω : Type*} [CommRing K] [CommRing B] [Algebra K B]
  [CommRing Ω] [Algebra K Ω]
variable (C : Type*) [CommRing C] [Algebra B C]

/-- The conjugate of a `B`-algebra `C` along a map `τ : B →ₐ[K] Ω` is the base
change `Ω ⊗[B] C` for the scalar map `τ`. -/
@[expose] def Conjugate (τ : B →ₐ[K] Ω) : Type _ :=
  letI := τ.toRingHom.toAlgebra
  Ω ⊗[B] C

noncomputable instance (τ : B →ₐ[K] Ω) : CommRing (Conjugate C τ) := by
  unfold Conjugate
  letI := τ.toRingHom.toAlgebra
  infer_instance

noncomputable instance (τ : B →ₐ[K] Ω) : Algebra Ω (Conjugate C τ) := by
  unfold Conjugate
  letI := τ.toRingHom.toAlgebra
  infer_instance

/-- The inclusion of `C` into its conjugate along `τ`. -/
noncomputable def conjugateInclude (τ : B →ₐ[K] Ω) : C →+* Conjugate C τ :=
  @Algebra.TensorProduct.includeRight B Ω C _ _ τ.toRingHom.toAlgebra _ _ |>.toRingHom

variable {T : Type*} [CommRing T] [Algebra Ω T]

/-- An `Ω`-algebra map from the conjugate along `τ` to `T` corresponds to a ring map
`C → T` extending the composite `B → Ω → T`. -/
def conjugateHomEquiv (τ : B →ₐ[K] Ω) :
    (Conjugate C τ →ₐ[Ω] T) ≃
      {f : C →+* T // f.comp (algebraMap B C) = (algebraMap Ω T).comp (τ : B →+* Ω)} := by
  letI := τ.toRingHom.toAlgebra
  letI := ((algebraMap Ω T).comp (τ : B →+* Ω)).toAlgebra
  letI : IsScalarTower B Ω T := IsScalarTower.of_algebraMap_eq' rfl
  let e : (C →ₐ[B] T) ≃
      {f : C →+* T // f.comp (algebraMap B C) = (algebraMap Ω T).comp (τ : B →+* Ω)} :=
    { toFun := fun f ↦ ⟨f.toRingHom, RingHom.ext fun b : B ↦ f.commutes b⟩
      invFun := fun f ↦ { f.val with commutes' := fun b : B ↦ RingHom.congr_fun f.property b }
      left_inv := fun f ↦ AlgHom.ext fun _ ↦ rfl
      right_inv := fun f ↦ Subtype.ext rfl }
  exact (liftEquivRight B Ω C T).symm.trans e

variable {C} in
/-- Restriction to `C` evaluates a map on the inclusion into the conjugate. -/
@[simp]
theorem conjugateHomEquiv_apply (τ : B →ₐ[K] Ω)
    (f : Conjugate C τ →ₐ[Ω] T) (c : C) :
    (conjugateHomEquiv C τ f : C →+* T) c = f (conjugateInclude C τ c) :=
  (rfl)

/-- The inclusion of `C` sends a base scalar `b` to the scalar `τ b` in the conjugate. -/
@[simp]
theorem conjugateInclude_algebraMap (τ : B →ₐ[K] Ω) (b : B) :
    conjugateInclude C τ (algebraMap B C b) = algebraMap Ω (Conjugate C τ) (τ b) := by
  exact RingHom.congr_fun (conjugateHomEquiv C τ (AlgHom.id Ω (Conjugate C τ))).property b

end Conjugate

variable (K B Ω C : Type*) [Field K] [CommRing B] [Algebra K B]
  [Field Ω] [Algebra K Ω] [CommRing C] [Algebra B C]
variable {T T' : Type*} [CommRing T] [Algebra Ω T] [CommRing T'] [Algebra Ω T']
variable [Module.Finite K B] [Algebra.IsFiniteSplit Ω (Ω ⊗[K] B)]

private noncomputable def baseChangeSplittingHomEquiv :
    ((Ω ⊗[K] WeilRestriction K B C) →ₐ[Ω] T) ≃
      ((τ : B →ₐ[K] Ω) → Conjugate C τ →ₐ[Ω] T) := by
  letI := Algebra.compHom T (algebraMap K Ω)
  letI : IsScalarTower K Ω T := IsScalarTower.of_algebraMap_eq' rfl
  let e : B ⊗[K] T ≃ₐ[K] ((B →ₐ[K] Ω) → T) :=
    (Algebra.TensorProduct.comm K B T).trans
      ((Algebra.Etale.tensorProductEquivPiBaseChange K Ω B T).restrictScalars K)
  have he (b : B) (τ : B →ₐ[K] Ω) :
      e (algebraMap B (B ⊗[K] T) b) τ = algebraMap Ω T (τ b) := by
    simp [e, Algebra.TensorProduct.algebraMap_apply]
  refine (liftEquivRight K Ω (WeilRestriction K B C) T).symm.trans <|
    (homEquiv K B C T).trans (?_ : (C →ₐ[B] B ⊗[K] T) ≃ _)
  exact
    { toFun := fun g τ ↦ (conjugateHomEquiv C τ).symm
        ⟨(Pi.evalRingHom _ τ).comp (e.toRingEquiv.toRingHom.comp g.toRingHom),
          RingHom.ext fun b ↦ by
            -- Unbundle the composed ring homomorphisms to use the algebra-map law of `g`.
            change e (g (algebraMap B C b)) τ = algebraMap Ω T (τ b)
            rw [g.commutes, he]⟩
      invFun := fun f ↦
        { toRingHom := e.symm.toRingEquiv.toRingHom.comp
            (RingHom.pi fun τ ↦ (conjugateHomEquiv C τ (f τ)).val)
          commutes' := fun b ↦ e.symm_apply_eq.mpr <| funext fun τ ↦
            (RingHom.congr_fun (conjugateHomEquiv C τ (f τ)).property b).trans (he b τ).symm }
      left_inv := fun g ↦ AlgHom.ext fun c ↦ e.symm_apply_eq.mpr <| funext fun τ ↦ by
        simp only [RingHom.pi_apply, Equiv.apply_symm_apply, RingHom.comp_apply,
          Pi.evalRingHom_apply]
        rfl
      right_inv := fun f ↦ funext fun τ ↦ (conjugateHomEquiv C τ).injective <|
        (Equiv.apply_symm_apply _ _).trans <| Subtype.ext <| RingHom.ext fun c ↦
          congrFun (e.apply_symm_apply fun σ ↦ (conjugateHomEquiv C σ (f σ)).val c) τ }

variable {K B Ω C}

private theorem baseChangeSplittingHomEquiv_apply
    (f : (Ω ⊗[K] WeilRestriction K B C) →ₐ[Ω] T) (τ : B →ₐ[K] Ω) (c : C) :
    letI := Algebra.compHom T (algebraMap K Ω)
    letI : IsScalarTower K Ω T := IsScalarTower.of_algebraMap_eq' rfl
    baseChangeSplittingHomEquiv K B Ω C f τ (conjugateInclude C τ c) =
      Algebra.TensorProduct.productMap
        ((IsScalarTower.toAlgHom K Ω T).comp τ) (AlgHom.id K T)
        (homEquiv K B C T ((f.restrictScalars K).comp includeRight) c) := by
  let := Algebra.compHom T (algebraMap K Ω)
  let : IsScalarTower K Ω T := IsScalarTower.of_algebraMap_eq' rfl
  rw [← conjugateHomEquiv_apply]
  simp only [baseChangeSplittingHomEquiv, Equiv.trans_apply, liftEquivRight_symm_apply,
    Equiv.coe_fn_mk, Equiv.apply_symm_apply, RingHom.comp_apply, Pi.evalRingHom_apply]
  -- Unbundle the ring map so that tensor induction sees the argument to the splitting.
  change Algebra.Etale.tensorProductEquivPiBaseChange K Ω B T
    (Algebra.TensorProduct.comm K B T
      (homEquiv K B C T ((f.restrictScalars K).comp includeRight) c)) τ = _
  generalize homEquiv K B C T ((f.restrictScalars K).comp includeRight) c = x
  induction x using _root_.TensorProduct.inductionOn with
  | tmul b t => simp
  | add x y hx hy => simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hx hy

private theorem baseChangeSplittingHomEquiv_comp (g : T →ₐ[Ω] T')
    (f : (Ω ⊗[K] WeilRestriction K B C) →ₐ[Ω] T) (τ : B →ₐ[K] Ω) :
    baseChangeSplittingHomEquiv K B Ω C (g.comp f) τ =
      g.comp (baseChangeSplittingHomEquiv K B Ω C f τ) := by
  apply (conjugateHomEquiv C τ).injective
  ext c
  let := Algebra.compHom T (algebraMap K Ω)
  let := Algebra.compHom T' (algebraMap K Ω)
  let : IsScalarTower K Ω T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K Ω T' := IsScalarTower.of_algebraMap_eq' rfl
  simp only [conjugateHomEquiv_apply, AlgHom.comp_apply, baseChangeSplittingHomEquiv_apply]
  have h : ((g.comp f).restrictScalars K).comp includeRight =
      (g.restrictScalars K).comp ((f.restrictScalars K).comp includeRight) := (rfl)
  rw [h, homEquiv_comp]
  simp only [AlgHom.comp_apply]
  generalize homEquiv K B C T ((f.restrictScalars K).comp includeRight) c = x
  induction x using _root_.TensorProduct.inductionOn with
  | tmul b t => simp
  | add x y hx hy => simp [hx, hy]

variable (K B Ω C)

private noncomputable def baseChangeSplittingToTensor :
    Ω ⊗[K] WeilRestriction K B C →ₐ[Ω] ⨂[Ω] τ : B →ₐ[K] Ω, Conjugate C τ := by
  classical
  exact (baseChangeSplittingHomEquiv K B Ω C).symm PiTensorProduct.singleAlgHom

/-- Over a splitting field of `B`, the base change of `Res_{B/K} C` is the tensor product
over `Ω` of the conjugates of `C` along the `K`-algebra maps `B →ₐ[K] Ω`. -/
noncomputable def baseChangeSplittingAlgEquiv :
    Ω ⊗[K] WeilRestriction K B C ≃ₐ[Ω] ⨂[Ω] τ : B →ₐ[K] Ω, Conjugate C τ := by
  classical
  letI := Fintype.ofFinite (B →ₐ[K] Ω)
  let forward := baseChangeSplittingToTensor K B Ω C
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
  have h : decEq = Classical.decEq (B →ₐ[K] Ω) := Subsingleton.elim _ _
  cases h
  classical
  let := Fintype.ofFinite (B →ₐ[K] Ω)
  rw [baseChangeSplittingAlgEquiv, AlgEquiv.ofAlgHom_symm_apply,
    PiTensorProduct.productMap_singleAlgHom, baseChangeSplittingHomEquiv_apply]
  simp only [homEquiv_apply, AlgHom.comp_apply]
  induction universalPoint K B C c using _root_.TensorProduct.inductionOn with
  | tmul b x => simp
  | add x y hx hy => simp [hx, hy]

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
  induction universalPoint K B C c using _root_.TensorProduct.inductionOn with
  | tmul b x => simp [Algebra.TensorProduct.algebraMap_apply]
  | add x y hx hy => simp [hx, hy]

end TauCeti.Algebra.WeilRestriction
