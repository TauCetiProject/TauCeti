/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.TransposeExt
public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.ShortExact
public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.FiniteLength
public import TauCeti.Algebra.Homology.Ext.Copresentation
import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Stable.Basic

/-!
# Computing the right transpose by Ext¹ of the Matlis duals

Dualizing a length-one projective resolution gives an injective copresentation. The
covariant Hom-cokernel comparison then identifies the transpose of a right module `N`
with `Ext¹(D A, D N)`. The left action comes from pullback along duals of left multiplications
on the right regular module.
-/

public section

open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

universe u v w

namespace ModuleCat

private def regularEnd {A : Type u} [Ring A] : A →+* End (of Aᵐᵒᵖ A) :=
  ((RingEquiv.moduleEndSelfOp A).trans (endRingEquiv (of Aᵐᵒᵖ A)).symm).toRingHom

private theorem regularEnd_asHom {A : Type u} [Ring A] (a : A) :
    (regularEnd a).asHom = ofHom (LinearMap.mulLeft Aᵐᵒᵖ a) :=
  (rfl)

variable (R : Type w) [CommRing R] (E : Type v) [AddCommGroup E] [Module R E]
  {A : Type (max u v)} [Ring A] [Algebra R A]

/-- Ext from the Matlis dual of the right regular module, with the left action given by
pullback along duals of left multiplication. -/
@[expose]
def ExtFromMatlisDualRegular (M : ModuleCat.{max u v} A) (n : ℕ) :=
  Ext (matlisDualOpObj R E (ModuleCat.of.{max u v} Aᵐᵒᵖ A)) M n

noncomputable instance (M : ModuleCat.{max u v} A) (n : ℕ) :
    AddCommGroup (ExtFromMatlisDualRegular R E M n) := inferInstanceAs (AddCommGroup (Ext _ M n))

/-- Forget the left action to recover the ordinary Ext group. -/
noncomputable def ExtFromMatlisDualRegular.toExt {M : ModuleCat.{max u v} A} {n : ℕ} :
    ExtFromMatlisDualRegular R E M n ≃+
      Ext (matlisDualOpObj R E (ModuleCat.of.{max u v} Aᵐᵒᵖ A)) M n :=
  AddEquiv.refl _

section Action

variable {M : ModuleCat.{max u v} A} {n : ℕ}


/-- Left multiplication acts on Ext from the dual of the right regular module by pullback. -/
noncomputable def matlisDualRegularExtAction :
    A →+* AddMonoid.End (Ext (matlisDualOpObj R E (ModuleCat.of.{max u v} Aᵐᵒᵖ A)) M n) where
  toFun a := (Ext.mk₀ (matlisDualOpMap R E (regularEnd.{max u v} a).asHom)).precomp M (zero_add n)
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    have h : matlisDualOpMap R E (𝟙 (ModuleCat.of.{max u v} Aᵐᵒᵖ A)) = 𝟙 _ :=
      (matlisDualOp R E).map_id (Opposite.op (ModuleCat.of.{max u v} Aᵐᵒᵖ A))
    change _ = x
    simp [h]
  map_mul' a b := by
    apply AddMonoidHom.ext
    intro x
    -- Multiplication of additive endomorphisms is function composition.
    change _ = (Ext.mk₀ (matlisDualOpMap R E (regularEnd a).asHom)).comp
      ((Ext.mk₀ (matlisDualOpMap R E (regularEnd b).asHom)).comp x (zero_add n)) (zero_add n)
    simp [End.mul_asHom]
  map_zero' := by
    apply AddMonoidHom.ext
    intro x
    have h : matlisDualOpMap R E
        (0 : ModuleCat.of.{max u v} Aᵐᵒᵖ A ⟶ ModuleCat.of.{max u v} Aᵐᵒᵖ A) = 0 :=
      (matlisDualOp R E).map_zero _ _
    change _ = 0
    simp [h]
  map_add' a b := by
    apply AddMonoidHom.ext
    intro x
    -- Addition of additive endomorphisms is pointwise.
    change _ = (Ext.mk₀ (matlisDualOpMap R E (regularEnd a).asHom)).comp x (zero_add n) +
      (Ext.mk₀ (matlisDualOpMap R E (regularEnd b).asHom)).comp x (zero_add n)
    simp [matlisDualOpMap_add, Ext.mk₀_add]

noncomputable instance (M : ModuleCat.{max u v} A) (n : ℕ) :
    Module A (ExtFromMatlisDualRegular R E M n) :=
  Module.compHom (Ext (matlisDualOpObj R E (ModuleCat.of.{max u v} Aᵐᵒᵖ A)) M n)
    (matlisDualRegularExtAction R E (M := M) (n := n))

end Action

/-- The left action on Ext is pullback along the dual of left multiplication. -/
@[simp]
theorem ExtFromMatlisDualRegular.toExt_smul {M : ModuleCat.{max u v} A} {n : ℕ}
    (a : A) (x : ExtFromMatlisDualRegular R E M n) :
    toExt R E (a • x) =
      (Ext.mk₀ (matlisDualOpMap R E (ofHom (LinearMap.mulLeft Aᵐᵒᵖ a)))).comp (toExt R E x)
        (zero_add n) := by
  -- The module structure is restriction along the ring map of pullback operators.
  change (Ext.mk₀ (matlisDualOpMap R E (regularEnd.{max u v} a).asHom)).comp
    (toExt R E x) (zero_add n) = _
  rw [regularEnd_asHom]

end ModuleCat

namespace TauCeti.FiniteProjectivePresentation

variable (R : Type w) [CommRing R] (E : Type v) [AddCommGroup E] [Module R E]
  [Small.{v} R] [Module.Injective R E] {A : Type (max u v)} [Ring A] [Algebra R A]
  {N : ModuleCat.{max u v} Aᵐᵒᵖ} (Q : FiniteProjectivePresentation N)
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)

local notation "D" => ModuleCat.matlisDualOpObj R E

private instance :
    Injective (Q.shortComplex.op.map (ModuleCat.matlisDualOp R E)).X₂ :=
  (ExactStructure.abelian_isInjective_iff _).mp
    (isInjective_matlisDualOpObj_of_projective R E Q.P₀)

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

variable (hB : @IsFiniteLength R _ (ModuleCat.of.{max u v} Aᵐᵒᵖ A) _
  (ModuleCat.moduleOfAlgebra R (ModuleCat.of.{max u v} Aᵐᵒᵖ A)))

/-- The transpose of a length-one right projective resolution computes `Ext¹(D A, D N)`
via the dual injective copresentation. For a resolution of `N = D M`, this computes
the inverse Auslander–Reiten translate of `M`. -/
noncomputable def rightTransposeEquivExtDual (hp : Function.Injective Q.p) :
    Q.rightTranspose ≃ₗ[R] Ext (D (ModuleCat.of.{max u v} Aᵐᵒᵖ A)) (D N) 1 := by
  let hS := (Q.shortExact_shortComplex hp).matlisDualOp R E
  let e := ModuleCat.matlisDualOpHomCokernelEquiv (B := ModuleCat.of.{max u v} Aᵐᵒᵖ A)
    hE hB Q.shortComplex.f
  exact (Q.rightTransposeHomCokernelEquiv R).trans
    (e.trans (covariantHomCokernelEquivExt R hS (D (ModuleCat.of.{max u v} Aᵐᵒᵖ A))))

/-- Under the dual comparison, a functional represents the pullback of the dual short exact
sequence along the dual of the functional. -/
@[simp]
theorem rightTransposeEquivExtDual_mk (hp : Function.Injective Q.p) (g : Q.P₁ →ₗ[Aᵐᵒᵖ] A) :
    Q.rightTransposeEquivExtDual R E hE hB hp (Submodule.Quotient.mk g) =
      (Ext.mk₀ (ModuleCat.matlisDualOpMap R E (ModuleCat.ofHom g))).comp
        ((Q.shortExact_shortComplex hp).matlisDualOp R E).extClass (zero_add 1) := by
  rw [rightTransposeEquivExtDual, LinearEquiv.trans_apply, rightTransposeHomCokernelEquiv_mk]
  -- The mapped complex has the bundled Matlis-dual maps as its components.
  erw [LinearEquiv.trans_apply, ModuleCat.matlisDualOpHomCokernelEquiv_mk,
    covariantHomCokernelEquivExt_mk]
  rfl

/-- The left action on the transpose corresponds to pulling back along the dual of left
multiplication on the right regular module. -/
theorem rightTransposeEquivExtDual_smul (hp : Function.Injective Q.p) (a : A)
    (x : Q.rightTranspose) :
    Q.rightTransposeEquivExtDual R E hE hB hp (a • x) =
      (Ext.mk₀ (ModuleCat.matlisDualOpMap R E (ModuleCat.ofHom (LinearMap.mulLeft Aᵐᵒᵖ a)))).comp
        (Q.rightTransposeEquivExtDual R E hE hB hp x) (zero_add 1) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, rightTransposeEquivExtDual_mk, rightTransposeEquivExtDual_mk,
    LinearMap.smul_eq_mulLeft_comp, ModuleCat.ofHom_comp, ModuleCat.matlisDualOpMap_comp]
  exact (Ext.mk₀_comp_mk₀_assoc _ _ _).symm

/-- Precomposition on relation modules agrees, under the dual comparison, with pushforward along
the dual of the map of presented modules. -/
theorem rightTransposeEquivExtDual_comp {N' : ModuleCat.{max u v} Aᵐᵒᵖ}
    (P : FiniteProjectivePresentation N') (hQ : Function.Injective Q.p)
    (hP : Function.Injective P.p) (φ : Q.shortComplex ⟶ P.shortComplex)
    (x : P.rightTranspose) :
    Q.rightTransposeEquivExtDual R E hE hB hQ (Q.rightTransposeMap P φ x) =
      (P.rightTransposeEquivExtDual R E hE hB hP x).comp
        (Ext.mk₀ (ModuleCat.matlisDualOpMap R E φ.τ₃)) (add_zero 1) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let Df : (ModuleCat.{max u v} Aᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat.{max u v} A :=
    ModuleCat.matlisDualOp R E
  let ψ : P.shortComplex.op.map Df ⟶ Q.shortComplex.op.map Df :=
    Df.mapShortComplex.map (ShortComplex.opMap φ)
  -- The opposite complex swaps the first and third components before taking their duals.
  have hψ₁ : ψ.τ₁ = ModuleCat.matlisDualOpMap R E φ.τ₃ := rfl
  have hψ₃ : ψ.τ₃ = ModuleCat.matlisDualOpMap R E φ.τ₁ := rfl
  have hclass :=
    ((P.shortExact_shortComplex hP).matlisDualOp R E).extClass_naturality
      ((Q.shortExact_shortComplex hQ).matlisDualOp R E) ψ
  rw [rightTransposeMap_mk, rightTransposeEquivExtDual_mk, rightTransposeEquivExtDual_mk,
    ModuleCat.ofHom_comp, ModuleCat.ofHom_hom, ModuleCat.matlisDualOpMap_comp]
  have h := congrArg (fun α ↦ (Ext.mk₀ (ModuleCat.matlisDualOpMap R E (ModuleCat.ofHom g))).comp
    α (zero_add 1)) hclass.symm
  rw [hψ₁, hψ₃] at h
  exact (Ext.mk₀_comp_mk₀_assoc _ _ _).symm.trans
    (h.trans (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm)

/-- The dual Ext computation as an equivalence of left `A`-modules. -/
noncomputable def rightTransposeLinearEquivExtDual (hp : Function.Injective Q.p) :
    Q.rightTranspose ≃ₗ[A] ModuleCat.ExtFromMatlisDualRegular R E (D N) 1 where
  toAddEquiv := (Q.rightTransposeEquivExtDual R E hE hB hp).toAddEquiv.trans
    (ModuleCat.ExtFromMatlisDualRegular.toExt R E).symm
  map_smul' a x := (ModuleCat.ExtFromMatlisDualRegular.toExt R E).injective (by
    let e := ModuleCat.ExtFromMatlisDualRegular.toExt R E (M := D N) (n := 1)
    let f := Q.rightTransposeEquivExtDual R E hE hB hp
    -- Compute in ordinary Ext after applying the forgetful equivalence.
    change e (e.symm (f (a • x))) = e (a • e.symm (f x))
    rw [e.apply_symm_apply, ModuleCat.ExtFromMatlisDualRegular.toExt_smul, e.apply_symm_apply]
    exact Q.rightTransposeEquivExtDual_smul R E hE hB hp a x)

/-- Forgetting the left action gives the same dual Ext class as the scalar comparison. -/
@[simp]
theorem rightTransposeLinearEquivExtDual_toExt (hp : Function.Injective Q.p)
    (x : Q.rightTranspose) :
    ModuleCat.ExtFromMatlisDualRegular.toExt R E
        (Q.rightTransposeLinearEquivExtDual R E hE hB hp x) =
      Q.rightTransposeEquivExtDual R E hE hB hp x := by
  exact (ModuleCat.ExtFromMatlisDualRegular.toExt R E).apply_symm_apply _

end TauCeti.FiniteProjectivePresentation
