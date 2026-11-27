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
import TauCeti.Algebra.Category.ModuleCat.End
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
  toFun a := (Ext.mk₀ (matlisDualOpMap R E (rightRegularEnd.{max u v} a).asHom)).precomp M
    (zero_add n)
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    have h : matlisDualOpMap R E (𝟙 (ModuleCat.of.{max u v} Aᵐᵒᵖ A)) = 𝟙 _ :=
      (matlisDualOp R E).map_id (Opposite.op (ModuleCat.of.{max u v} Aᵐᵒᵖ A))
    -- The identity additive endomorphism evaluates to its argument.
    change _ = x
    simp [h]
  map_mul' a b := by
    apply AddMonoidHom.ext
    intro x
    -- Multiplication of additive endomorphisms is function composition.
    change _ = (Ext.mk₀ (matlisDualOpMap R E (rightRegularEnd a).asHom)).comp
      ((Ext.mk₀ (matlisDualOpMap R E (rightRegularEnd b).asHom)).comp x (zero_add n))
        (zero_add n)
    simp [End.mul_asHom, -rightRegularEnd_asHom]
  map_zero' := by
    apply AddMonoidHom.ext
    intro x
    have h : matlisDualOpMap R E
        (0 : ModuleCat.of.{max u v} Aᵐᵒᵖ A ⟶ ModuleCat.of.{max u v} Aᵐᵒᵖ A) = 0 :=
      (matlisDualOp R E).map_zero _ _
    -- The zero additive endomorphism evaluates to zero.
    change _ = 0
    simp [h]
  map_add' a b := by
    apply AddMonoidHom.ext
    intro x
    -- Addition of additive endomorphisms is pointwise.
    change _ = (Ext.mk₀ (matlisDualOpMap R E (rightRegularEnd a).asHom)).comp x (zero_add n) +
      (Ext.mk₀ (matlisDualOpMap R E (rightRegularEnd b).asHom)).comp x (zero_add n)
    simp [matlisDualOpMap_add, Ext.mk₀_add, -rightRegularEnd_asHom]

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
  change (Ext.mk₀ (matlisDualOpMap R E (rightRegularEnd.{max u v} a).asHom)).comp
    (toExt R E x) (zero_add n) = _
  rw [rightRegularEnd_asHom]

/-- An additive Ext comparison compatible with pullback by dual left multiplications is
an equivalence of left `A`-modules. -/
private noncomputable def ExtFromMatlisDualRegular.linearEquivOfCompat
    {V : Type*} [AddCommGroup V] [Module A V] {M : ModuleCat.{max u v} A} {n : ℕ}
    (e : V ≃+ Ext (matlisDualOpObj R E (ModuleCat.of.{max u v} Aᵐᵒᵖ A)) M n)
    (he : ∀ (a : A) (x : V), e (a • x) =
      (Ext.mk₀ (matlisDualOpMap R E (ofHom (LinearMap.mulLeft Aᵐᵒᵖ a)))).comp (e x)
        (zero_add n)) :
    V ≃ₗ[A] ExtFromMatlisDualRegular R E M n where
  toAddEquiv := e.trans (toExt R E).symm
  map_smul' a x := (toExt R E).injective (by
    -- The additive comparison is followed by the inverse forgetful equivalence.
    change toExt R E ((toExt R E).symm (e (a • x))) =
      toExt R E (a • (toExt R E).symm (e x))
    rw [AddEquiv.apply_symm_apply, toExt_smul, AddEquiv.apply_symm_apply]
    exact he a x)

/-- Forgetting the action after constructing the compatible linear equivalence recovers
the original additive comparison. -/
@[simp]
private theorem ExtFromMatlisDualRegular.linearEquivOfCompat_toExt
    {V : Type*} [AddCommGroup V] [Module A V] {M : ModuleCat.{max u v} A} {n : ℕ}
    (e : V ≃+ Ext (matlisDualOpObj R E (ModuleCat.of.{max u v} Aᵐᵒᵖ A)) M n)
    (he : ∀ (a : A) (x : V), e (a • x) =
      (Ext.mk₀ (matlisDualOpMap R E (ofHom (LinearMap.mulLeft Aᵐᵒᵖ a)))).comp (e x)
        (zero_add n)) (x : V) :
    toExt R E (linearEquivOfCompat R E e he x) = e x :=
  (toExt R E).apply_symm_apply _

/-- An isomorphism of targets preserves the left action on Ext from the dual regular module. -/
noncomputable def ExtFromMatlisDualRegular.linearEquivOfIso
    {M M' : ModuleCat.{max u v} A} (e : M ≅ M') (n : ℕ) :
    ExtFromMatlisDualRegular R E M n ≃ₗ[A] ExtFromMatlisDualRegular R E M' n := by
  let eExt := TauCeti.extAddEquivOfIso
    (Iso.refl (matlisDualOpObj R E (ModuleCat.of.{max u v} Aᵐᵒᵖ A))) e n
  -- Changing the target commutes with precomposition in the source.
  have hpre (f : matlisDualOpObj R E (ModuleCat.of.{max u v} Aᵐᵒᵖ A) ⟶
      matlisDualOpObj R E (ModuleCat.of.{max u v} Aᵐᵒᵖ A))
      (x : Ext (matlisDualOpObj R E (ModuleCat.of.{max u v} Aᵐᵒᵖ A)) M n) :
      eExt ((Ext.mk₀ f).comp x (zero_add n)) =
        (Ext.mk₀ f).comp (eExt x) (zero_add n) := by
    simp only [eExt, TauCeti.extAddEquivOfIso_apply, Iso.refl_inv, Ext.mk₀_id_comp,
      Ext.comp_assoc_of_third_deg_zero]
  refine linearEquivOfCompat R E ((toExt R E).trans eExt) ?_
  intro a x
  simp only [AddEquiv.trans_apply, toExt_smul, hpre]

/-- The target-isomorphism comparison acts on ordinary Ext by transport along that isomorphism. -/
@[simp]
theorem ExtFromMatlisDualRegular.linearEquivOfIso_toExt
    {M M' : ModuleCat.{max u v} A} (e : M ≅ M') (n : ℕ)
    (x : ExtFromMatlisDualRegular R E M n) :
    toExt R E (linearEquivOfIso R E e n x) =
      TauCeti.extAddEquivOfIso (Iso.refl _) e n (toExt R E x) := by
  unfold linearEquivOfIso
  exact linearEquivOfCompat_toExt R E _ _ x

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
  let hS := (Q.shortExact_shortComplex hp).matlisDualOp R E
  -- Mapping the opposite complex gives dual maps in the reversed order.
  exact (congrArg (covariantHomCokernelEquivExt R hS (D (ModuleCat.of.{max u v} Aᵐᵒᵖ A)))
    (ModuleCat.matlisDualOpHomCokernelEquiv_mk hE hB Q.shortComplex.f (ModuleCat.ofHom g))).trans
      (covariantHomCokernelEquivExt_mk R hS _ (ModuleCat.matlisDualOpMap R E (ModuleCat.ofHom g)))

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
    Q.rightTranspose ≃ₗ[A] ModuleCat.ExtFromMatlisDualRegular R E (D N) 1 :=
  ModuleCat.ExtFromMatlisDualRegular.linearEquivOfCompat R E
    (Q.rightTransposeEquivExtDual R E hE hB hp).toAddEquiv
    (Q.rightTransposeEquivExtDual_smul R E hE hB hp)

/-- Forgetting the left action gives the same dual Ext class as the scalar comparison. -/
@[simp]
theorem rightTransposeLinearEquivExtDual_toExt (hp : Function.Injective Q.p)
    (x : Q.rightTranspose) :
    ModuleCat.ExtFromMatlisDualRegular.toExt R E
        (Q.rightTransposeLinearEquivExtDual R E hE hB hp x) =
      Q.rightTransposeEquivExtDual R E hE hB hp x := by
  exact ModuleCat.ExtFromMatlisDualRegular.linearEquivOfCompat_toExt R E _ _ x

end TauCeti.FiniteProjectivePresentation
