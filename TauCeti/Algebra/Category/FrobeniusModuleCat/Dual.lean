/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import TauCeti.Algebra.Category.FrobeniusModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Dualizable

/-!
# Duals of finite projective linearized Frobenius modules

Let `M` be a linearized Frobenius module over `(S, σ)`, with linearization
`L : S ⊗_{S,σ} M ≅ M` and Frobenius `F m = L (1 ⊗ m)`. Its *dual Frobenius* is the
`σ`-semilinear map `F^∨` on the linear forms `Module.Dual S M` with
`F^∨ f (L (s ⊗ m)) = s * σ (f m)`, equivalently `F^∨ f (F m) = σ (f m)`. It is defined for every
`M`, as the linear form `s ⊗ m ↦ s * σ (f m)` precomposed with `L⁻¹`, and is determined by the
second formula because the image of `F` spans `M`. No inverse of `σ` is used.

When `M` is finite projective, the linearization `s ⊗ f ↦ s • F^∨ f` of `F^∨` is an isomorphism, so
the linear forms with `F^∨` form a linearized Frobenius module `M.dual`. The inverse is written with
a finite dual basis `(eᵢ, cᵢ)` of `M` as `g ↦ ∑ᵢ g (F eᵢ) • (1 ⊗ cᵢ)`. The evaluation
`f ⊗ m ↦ f m` and the coevaluation `1 ↦ ∑ᵢ eᵢ ⊗ cᵢ` of the underlying modules are morphisms of
linearized Frobenius modules. For the evaluation this is the formula `F^∨ f (F m) = σ (f m)`.
For the coevaluation, `M ⊗ M^∨` is identified with `End M`, under which `F ⊗ F^∨` becomes
conjugation by `F`, and the identity agrees with its conjugate on the image of `F`. Hence `M.dual`
is a right dual of `M` in the monoidal category `TauCeti.FrobeniusModuleCat σ`.

## Main definitions

* `TauCeti.FrobeniusModuleCat.dualFrobenius`: the dual Frobenius `F^∨` on linear forms.
* `TauCeti.FrobeniusModuleCat.dual`: the dual of a finite projective linearized Frobenius module.
* `TauCeti.FrobeniusModuleCat.exactPairingDual`: the exact pairing of `M` with `M.dual`, and the
  resulting `HasRightDual` instance.

## Main results

* `TauCeti.FrobeniusModuleCat.dualFrobenius_apply_frobenius`: `F^∨ f (F m) = σ (f m)`.
* `TauCeti.FrobeniusModuleCat.eq_dualFrobenius_iff`: this formula characterizes `F^∨ f`.
* `TauCeti.FrobeniusModuleCat.evaluation_hom_f` and
  `TauCeti.FrobeniusModuleCat.coevaluation_hom_f`: the evaluation and coevaluation of the dual are
  those of the underlying modules.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Convention 1.5.1.
-/

public section

open CategoryTheory MonoidalCategory TensorProduct ChangeOfRings

universe u

namespace TauCeti.FrobeniusModuleCat

variable {S : Type u} [CommRing S] {σ : S →+* S} (M : FrobeniusModuleCat σ)

/-- The linear form `L (s ⊗ m) ↦ s * σ (f m)` underlying the dual Frobenius. -/
private noncomputable def dualFrobeniusAux (f : Module.Dual S M.carrier) :
    Module.Dual S M.carrier :=
  (M.linearization.inv ≫ (ModuleCat.extendScalarsHomEquivSemilinearMap σ M.carrier
    (ModuleCat.of S S)).symm (σ.toSemilinearMap.comp f)).hom

private theorem dualFrobeniusAux_apply_frobenius (f : Module.Dual S M.carrier) (m : M.carrier) :
    dualFrobeniusAux M f (M.frobenius m) = σ (f m) := by
  rw [dualFrobeniusAux, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [linearization_inv_frobenius]
  exact (ModuleCat.extendScalarsHomEquivSemilinearMap_symm_apply_tmul σ _ 1 m).trans (one_mul _)

/-- The *dual Frobenius* of a linearized Frobenius module: the `σ`-semilinear map on linear forms
with `F^∨ f (L (s ⊗ m)) = s * σ (f m)`, that is `F^∨ f (F m) = σ (f m)`
(`TauCeti.FrobeniusModuleCat.dualFrobenius_apply_frobenius`). -/
noncomputable def dualFrobenius : Module.Dual S M.carrier →ₛₗ[σ] Module.Dual S M.carrier where
  toFun := dualFrobeniusAux M
  map_add' f g := LinearMap.ext_on_range M.span_range_frobenius fun m ↦ by
    simp [dualFrobeniusAux_apply_frobenius]
  map_smul' s f := LinearMap.ext_on_range M.span_range_frobenius fun m ↦ by
    simp [dualFrobeniusAux_apply_frobenius]

/-- The dual Frobenius pairs with the Frobenius through `σ`: `F^∨ f (F m) = σ (f m)`. -/
@[simp]
theorem dualFrobenius_apply_frobenius (f : Module.Dual S M.carrier) (m : M.carrier) :
    M.dualFrobenius f (M.frobenius m) = σ (f m) :=
  dualFrobeniusAux_apply_frobenius M f m

/-- The dual Frobenius is characterized by its values on the image of the Frobenius, which spans
the module. -/
theorem eq_dualFrobenius_iff {f g : Module.Dual S M.carrier} :
    g = M.dualFrobenius f ↔ ∀ m, g (M.frobenius m) = σ (f m) :=
  ⟨fun h m ↦ h ▸ M.dualFrobenius_apply_frobenius f m, fun h ↦
    LinearMap.ext_on_range M.span_range_frobenius fun m ↦ (h m).trans
      (M.dualFrobenius_apply_frobenius f m).symm⟩

/-- Under the identification of `M ⊗ M^∨` with `End M`, the map `F ⊗ F^∨` is conjugation by `F`:
if `x` corresponds to `φ`, then `(F ⊗ F^∨) x` sends `F y` to `F (φ y)`. -/
private theorem dualTensorHom_comm_map_frobenius_apply_frobenius
    (x : M.carrier ⊗[S] Module.Dual S M.carrier) (y : M.carrier) :
    dualTensorHom S M.carrier M.carrier (TensorProduct.comm S M.carrier (Module.Dual S M.carrier)
        (TensorProduct.map M.frobenius M.dualFrobenius x)) (M.frobenius y) =
      M.frobenius (dualTensorHom S M.carrier M.carrier
        (TensorProduct.comm S M.carrier (Module.Dual S M.carrier) x) y) := by
  induction x using TensorProduct.inductionOn with
  | tmul m f => simp
  | add x x' hx hx' => simp_all

/-- The map `S → S ⊗_{S,σ} N`, `r ↦ r • (1 ⊗ x)`, as the inverse linearization of the unit followed
by the scalar extension of `r ↦ r • x`. -/
private noncomputable def smulOneTmul {N : ModuleCat.{u} S} (x : N) :
    𝟙_ (ModuleCat.{u} S) ⟶ (ModuleCat.extendScalars σ).obj N :=
  (𝟙_ (FrobeniusModuleCat σ)).linearization.inv ≫
    (ModuleCat.extendScalars σ).map (ModuleCat.ofHom (LinearMap.toSpanSingleton S N x))

private theorem smulOneTmul_apply {N : ModuleCat.{u} S} (x : N) (r : S) :
    (smulOneTmul (σ := σ) x).hom r =
      r • ModuleCat.extendScalarsHomEquivSemilinearMap σ N _ (𝟙 _) x := by
  -- `σ r` is the Frobenius of `r` in the unit, so its inverse linearization is `1 ⊗ r`.
  have hσ (a : S) : (smulOneTmul (σ := σ) x).hom (σ a) =
      ModuleCat.extendScalarsHomEquivSemilinearMap σ N _ (𝟙 _) (a • x) := by
    rw [← tensorUnit_frobenius_apply]
    -- Unfold the composite; the unit's carrier is `S` only up to unfolding, hence `erw`.
    change ((ModuleCat.extendScalars σ).map _).hom
      ((𝟙_ (FrobeniusModuleCat σ)).linearization.inv.hom _) = _
    erw [linearization_inv_frobenius]
    rw [ModuleCat.extendScalarsHomEquivSemilinearMap_apply]
    -- `(extendScalars σ).map g` sends `1 ⊗ a` to `1 ⊗ g a`, here with `g a = a • x`.
    exact ModuleCat.ExtendScalars.map_tmul σ (ModuleCat.ofHom (LinearMap.toSpanSingleton S N x)) 1 a
  have h := hσ 1
  rw [map_one, one_smul] at h
  conv_lhs => rw [← mul_one r, ← smul_eq_mul, map_smul, h]

variable [Module.Finite S M.carrier] [Module.Projective S M.carrier]

/-- For a finite projective linearized Frobenius module, the linearization
`s ⊗ f ↦ s • F^∨ f` of the dual Frobenius is an isomorphism. -/
instance isIso_linearization_dualFrobenius :
    IsIso ((ModuleCat.extendScalarsHomEquivSemilinearMap σ
      (ModuleCat.of S (Module.Dual S M.carrier)) (ModuleCat.of S (Module.Dual S M.carrier))).symm
        M.dualFrobenius) := by
  -- The inverse is `g ↦ ∑ k, g (F (e k)) • (1 ⊗ c k)` for a finite dual basis `(e k, c k)` of `M`.
  set D := ModuleCat.of S (Module.Dual S M.carrier)
  set E := ModuleCat.extendScalarsHomEquivSemilinearMap σ D D
  -- The semilinear map `f ↦ 1 ⊗ f`.
  set ι := ModuleCat.extendScalarsHomEquivSemilinearMap σ D _
    (𝟙 ((ModuleCat.extendScalars σ).obj D))
  have hι (x : D) : ι x = (1 : S) ⊗ₜ[S,σ] x :=
    ModuleCat.extendScalarsHomEquivSemilinearMap_apply σ _ x
  obtain ⟨n, π, j, -, -, hπj⟩ := Module.Finite.exists_comp_eq_id_of_projective S M.carrier
  set e : Fin n → M.carrier := fun k ↦ π fun i ↦ if k = i then 1 else 0
  set c : Fin n → Module.Dual S M.carrier := fun k ↦ LinearMap.proj k ∘ₗ j
  have hx (x : M.carrier) : ∑ k, c k x • e k = x :=
    (LinearMap.pi_apply_eq_sum_univ π (j x)).symm.trans (LinearMap.congr_fun hπj x)
  have hf (f : Module.Dual S M.carrier) : ∑ k, f (e k) • c k = f := by
    ext x
    conv_rhs => rw [← hx x]
    simp [mul_comm]
  -- `Λ (1 ⊗ f) = F^∨ f`.
  have hΛ (f : D) : (E.symm M.dualFrobenius).hom (ι f) = M.dualFrobenius f :=
    (congrArg (E.symm M.dualFrobenius).hom (hι f)).trans
      ((ModuleCat.extendScalarsHomEquivSemilinearMap_apply σ _ f).symm.trans
        (congrArg (· f) (E.apply_symm_apply M.dualFrobenius)))
  let G : D ⟶ (ModuleCat.extendScalars σ).obj D :=
    ∑ k, ModuleCat.ofHom (LinearMap.applyₗ (M.frobenius (e k))) ≫ smulOneTmul (c k)
  have hG (g : D) : G.hom g = ∑ k, g (M.frobenius (e k)) • ι (c k) := by
    simp only [G, ModuleCat.hom_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    exact smulOneTmul_apply (N := D) (c k) _
  refine ⟨G, ModuleCat.ExtendScalars.hom_ext fun f ↦ ?_,
    ModuleCat.hom_ext (LinearMap.ext fun g ↦ ?_)⟩
  · have key : (E.symm M.dualFrobenius ≫ G).hom (ι f) = ι f := by
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, hΛ, hG]
      calc ∑ k, M.dualFrobenius f (M.frobenius (e k)) • ι (c k)
          = ∑ k, ι (f (e k) • c k) := Finset.sum_congr rfl fun k _ ↦ by
            rw [map_smulₛₗ, ← M.dualFrobenius_apply_frobenius f (e k)]
        _ = ι f := by rw [← map_sum, hf]
    rw [hι] at key
    exact key
  · rw [ModuleCat.hom_comp, LinearMap.comp_apply, hG, map_sum]
    simp only [map_smul, hΛ, ModuleCat.hom_id, LinearMap.id_apply]
    refine LinearMap.ext_on_range M.span_range_frobenius fun y ↦ ?_
    conv_rhs => rw [← hx y]
    simp [mul_comm]

/-- The *dual* of a finite projective linearized Frobenius module: the dual module
`Module.Dual S M` with the dual Frobenius `F^∨`. -/
@[expose] noncomputable def dual : FrobeniusModuleCat σ :=
  ofFrobenius (ModuleCat.of S (Module.Dual S M.carrier)) M.dualFrobenius

/-- The underlying module of the dual is the module of linear forms. -/
@[simp] theorem dual_carrier : M.dual.carrier = ModuleCat.of S (Module.Dual S M.carrier) := (rfl)

/-- The Frobenius of the dual is the dual Frobenius. -/
@[simp] theorem frobenius_dual : M.dual.frobenius = M.dualFrobenius :=
  frobenius_ofFrobenius _ _

/-- The Frobenius of `M ⊗ M^∨` is `F ⊗ F^∨`, and that of `M^∨ ⊗ M` is `F^∨ ⊗ F`. -/
private theorem tensor_dual_frobenius :
    (∀ x : M.carrier ⊗[S] Module.Dual S M.carrier,
      (M ⊗ M.dual).frobenius x = TensorProduct.map M.frobenius M.dualFrobenius x) ∧
    ∀ x : Module.Dual S M.carrier ⊗[S] M.carrier,
      (M.dual ⊗ M).frobenius x = TensorProduct.map M.dualFrobenius M.frobenius x := by
  -- After the rewrites both sides are the same `TensorProduct.map`, but on the left it is typed on
  -- the carrier of the tensor product of linearized Frobenius modules, and on the right on the
  -- tensor product of `M` with `Module.Dual S M`. These types agree by unfolding the monoidal
  -- structure and `dual_carrier`, which `rfl` does.
  refine ⟨fun x ↦ ?_, fun x ↦ ?_⟩ <;> rw [tensor_frobenius, frobenius_dual] <;> rfl

/-- The canonical element `∑ eᵢ ⊗ eᵢ^∨` of `M ⊗ M^∨` is fixed by the Frobenius `F ⊗ F^∨`. -/
private theorem map_frobenius_coevaluation_one :
    TensorProduct.map M.frobenius M.dualFrobenius
        ((η_ M.carrier (ModuleCat.of S (Module.Dual S M.carrier))).hom 1) =
      (η_ M.carrier (ModuleCat.of S (Module.Dual S M.carrier))).hom 1 := by
  set c := (η_ M.carrier (ModuleCat.of S (Module.Dual S M.carrier))).hom 1
  have hinj : Function.Injective fun x ↦ dualTensorHom S M.carrier M.carrier
      (TensorProduct.comm S M.carrier (Module.Dual S M.carrier) x) :=
    dualTensorHom_bijective.1.comp (TensorProduct.comm S _ _).injective
  refine hinj (LinearMap.ext_on_range M.span_range_frobenius fun y ↦ ?_)
  simp only [dualTensorHom_comm_map_frobenius_apply_frobenius]
  rw [ModuleCat.dualTensorHom_comm_coevaluation_dual]
  rfl

/-- The evaluation `M^∨ ⊗ M → S`, `f ⊗ m ↦ f m`, intertwines `F^∨ ⊗ F` with `σ`. -/
private theorem evaluation_frobenius (x : Module.Dual S M.carrier ⊗[S] M.carrier) :
    (ε_ M.carrier (ModuleCat.of S (Module.Dual S M.carrier))).hom ((M.dual ⊗ M).frobenius x) =
      (𝟙_ (FrobeniusModuleCat σ)).frobenius
        ((ε_ M.carrier (ModuleCat.of S (Module.Dual S M.carrier))).hom x) := by
  rw [M.tensor_dual_frobenius.2, tensorUnit_frobenius_apply]
  induction x using TensorProduct.inductionOn with
  | tmul f m =>
    rw [map_tmul, ModuleCat.evaluation_dual_tmul, ModuleCat.evaluation_dual_tmul,
      dualFrobenius_apply_frobenius]
  | add x x' hx hx' => simp only [map_add, hx, hx']

/-- The coevaluation `S → M ⊗ M^∨`, `1 ↦ ∑ eᵢ ⊗ eᵢ^∨`, intertwines `σ` with `F ⊗ F^∨`. -/
private theorem coevaluation_frobenius (r : S) :
    (η_ M.carrier (ModuleCat.of S (Module.Dual S M.carrier))).hom
        ((𝟙_ (FrobeniusModuleCat σ)).frobenius r) =
      (M ⊗ M.dual).frobenius ((η_ M.carrier (ModuleCat.of S (Module.Dual S M.carrier))).hom r) := by
  set η' := (η_ M.carrier (ModuleCat.of S (Module.Dual S M.carrier))).hom
  have hη (a : S) : η' a = a • η' 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [tensorUnit_frobenius_apply, M.tensor_dual_frobenius.1, hη, hη r, map_smulₛₗ,
    map_frobenius_coevaluation_one]

/-- A finite projective linearized Frobenius module and its dual form an exact pairing, with the
evaluation and coevaluation of the underlying modules. -/
@[instance_reducible]
noncomputable def exactPairingDual : ExactPairing M M.dual :=
  letI : ExactPairing ((forget σ).obj M) ((forget σ).obj M.dual) :=
    ModuleCat.exactPairingDual M.carrier
  .ofFaithful (forget σ)
    (homMkOfFrobenius (ε_ M.carrier (ModuleCat.of S (Module.Dual S M.carrier)))
      M.evaluation_frobenius)
    (homMkOfFrobenius (η_ M.carrier (ModuleCat.of S (Module.Dual S M.carrier)))
      M.coevaluation_frobenius)
    (by
      simp only [forget_map, forget_δ, forget_ε]
      exact homMkOfFrobenius_hom_f _ _)
    (by
      simp only [forget_map, forget_η, forget_μ]
      exact homMkOfFrobenius_hom_f _ _)

noncomputable instance : ExactPairing M M.dual := M.exactPairingDual

/-- A finite projective linearized Frobenius module has a right dual, its dual module with the
dual Frobenius. -/
noncomputable instance hasRightDual : HasRightDual M where
  rightDual := M.dual

/-- The chosen right dual is `M.dual`. -/
@[simp] theorem rightDual_eq : Mᘁ = M.dual := (rfl)

/-- The evaluation of the dual is the evaluation `f ⊗ m ↦ f m` of the underlying modules. -/
@[simp]
theorem evaluation_hom_f :
    (ε_ M M.dual).hom.f = ε_ M.carrier (ModuleCat.of S (Module.Dual S M.carrier)) :=
  homMkOfFrobenius_hom_f _ _

/-- The evaluation of the dual sends `f ⊗ m` to `f m`. -/
theorem evaluation_hom_f_tmul (f : Module.Dual S M.carrier) (m : M.carrier) :
    (ε_ M M.dual).hom.f.hom (f ⊗ₜ m) = f m := by
  rw [evaluation_hom_f]
  exact ModuleCat.evaluation_dual_tmul M.carrier f m

/-- The coevaluation of the dual is the coevaluation `1 ↦ ∑ eᵢ ⊗ eᵢ^∨` of the underlying
modules. -/
@[simp]
theorem coevaluation_hom_f :
    (η_ M M.dual).hom.f = η_ M.carrier (ModuleCat.of S (Module.Dual S M.carrier)) :=
  homMkOfFrobenius_hom_f _ _

end TauCeti.FrobeniusModuleCat
