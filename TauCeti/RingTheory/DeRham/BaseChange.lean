/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DeRham.Pullback
public import TauCeti.RingTheory.Kaehler.BaseChange
public import TauCeti.LinearAlgebra.ExteriorPower.Localization
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive

/-!
# Base change of the ordinary de Rham complex

Let `A → A'` be a map of commutative rings, `B` an `A`-algebra and `B' = A' ⊗[A] B` its base
change, given as any commutative square satisfying `Algebra.IsPushout A A' B B'`. Then the
differential forms of `B'` over `A'` are the base change of those of `B` over `A`:
`A' ⊗[A] Ωⁿ_(B/A) ≃ Ωⁿ_(B'/A')`, sending `a' ⊗ c • dv₀ ∧ ⋯ ∧ dvₙ₋₁` to
`a'c • dv₀ ∧ ⋯ ∧ dvₙ₋₁`. These equivalences commute with the de Rham differentials, so they
assemble into an isomorphism of cochain complexes of `A'`-modules between the extension of
scalars of `Ω•_(B/A)` along `A → A'` and `Ω•_(B'/A')`; they also preserve wedge products. No
flatness is needed: the comparison holds degreewise for the ordinary (underived) tensor product.

The degreewise equivalence is the composite of three identifications:
`A' ⊗[A] Ωⁿ_(B/A) ≃ B' ⊗[B] Ωⁿ_(B/A)` (`Algebra.IsPushout.cancelBaseChange`), the base change of
exterior powers `B' ⊗[B] ⋀[B]^n M ≃ ⋀[B']^n (B' ⊗[B] M)` (`IsBaseChange.exteriorPowerEquiv`), and
the base change of Kähler differentials `B' ⊗[B] Ω[B⁄A] ≃ Ω[B'⁄A']`
(`KaehlerDifferential.isBaseChange_map`, from `KaehlerDifferential.tensorKaehlerEquiv`).

## Main definitions

* `TauCeti.DeRham.baseChangeEquiv A A' B B' n`: the `A'`-linear equivalence
  `A' ⊗[A] Ωⁿ_(B/A) ≃ Ωⁿ_(B'/A')`.
* `TauCeti.DeRham.complexBaseChangeIso A A' B B'`: the isomorphism of cochain complexes between
  the extension of scalars of `Ω•_(B/A)` along `A → A'` and `Ω•_(B'/A')`.

## Main results

* `TauCeti.DeRham.baseChangeEquiv_tmul_elementary`: the value on `a' ⊗ c • dv₀ ∧ ⋯ ∧ dvₙ₋₁`.
* `TauCeti.DeRham.baseChangeEquiv_tmul`: the equivalence is the `A'`-linear extension of pullback
  along `B → B'` followed by the map induced by `Ω[B'⁄A] → Ω[B'⁄A']`.
* `TauCeti.DeRham.baseChangeEquiv_d`: the equivalence commutes with the de Rham differentials.
* `TauCeti.DeRham.baseChangeEquiv_wedge`: the equivalence preserves wedge products.
* `TauCeti.DeRham.zeroEquiv_baseChangeEquiv`, `TauCeti.DeRham.oneEquiv_baseChangeEquiv`: in degree
  zero it is the pushout identification `A' ⊗[A] B ≃ B'`, and in degree one it is Mathlib's
  `KaehlerDifferential.tensorKaehlerEquivBase`.

## References

* B. Bhatt, *p-adic derived de Rham cohomology*, arXiv:1204.6560, proof of Proposition 2.7.
* The Stacks Project, Section 10.132 (Tag 0FKF), the algebraic de Rham complex.
-/

universe u

namespace TauCeti.DeRham

open CategoryTheory _root_.KaehlerDifferential _root_.exteriorPower TensorProduct
open scoped ChangeOfRings

section Forms

variable (A A' B B' : Type*) [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.IsPushout A A' B B']

public section

/-- **Base change of differential forms.** For a base change `B' = A' ⊗[A] B`, the
`A'`-linear equivalence `A' ⊗[A] Ωⁿ_(B/A) ≃ Ωⁿ_(B'/A')`. It sends
`a' ⊗ c • dv₀ ∧ ⋯ ∧ dvₙ₋₁` to `a'c • dv₀ ∧ ⋯ ∧ dvₙ₋₁` (`baseChangeEquiv_tmul_elementary`) and
commutes with the de Rham differentials (`baseChangeEquiv_d`). -/
noncomputable def baseChangeEquiv (n : ℕ) : A' ⊗[A] Forms A B n ≃ₗ[A'] Forms A' B' n :=
  (Algebra.IsPushout.cancelBaseChange A A' B B' (Forms A B n)).symm ≪≫ₗ
    ((isBaseChange_map A A' B B').exteriorPowerEquiv n).restrictScalars A'

variable {A A' B B'}

/-- The base change of a wedge of `1`-forms: `a' ⊗ ω₀ ∧ ⋯ ∧ ωₙ₋₁` goes to
`a' • ω₀' ∧ ⋯ ∧ ωₙ₋₁'`, where `ωᵢ'` is the image of `ωᵢ` under
`KaehlerDifferential.map A A' B B' : Ω[B⁄A] → Ω[B'⁄A']`. -/
@[simp]
theorem baseChangeEquiv_tmul_ιMulti {n : ℕ} (a' : A') (ω : Fin n → Ω[B⁄A]) :
    baseChangeEquiv A A' B B' n (a' ⊗ₜ ιMulti B n ω) =
      a' • ιMulti B' n (map A A' B B' ∘ ω) := by
  simp [baseChangeEquiv, Function.comp_def, algebraMap_smul]

/-- Base change is semilinear in the `B`-scalars of a form:
`a' ⊗ c • ω` goes to the image of `c` in `B'` times the image of `a' ⊗ ω`. -/
theorem baseChangeEquiv_tmul_smul {n : ℕ} (a' : A') (c : B) (ω : Forms A B n) :
    baseChangeEquiv A A' B B' n (a' ⊗ₜ (c • ω)) =
      algebraMap B B' c • baseChangeEquiv A A' B B' n (a' ⊗ₜ ω) := by
  simp only [baseChangeEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    Algebra.IsPushout.cancelBaseChange_symm_tmul, TensorProduct.tmul_smul]
  rw [← algebraMap_smul B' c, map_smul]

/-- **Base change of elementary forms**: `a' ⊗ c • dv₀ ∧ ⋯ ∧ dvₙ₋₁` goes to
`a'c • dv₀ ∧ ⋯ ∧ dvₙ₋₁`, with `c` and the `vᵢ` mapped into `B'`. -/
@[simp]
theorem baseChangeEquiv_tmul_elementary {n : ℕ} (a' : A') (c : B) (v : Fin n → B) :
    baseChangeEquiv A A' B B' n (a' ⊗ₜ elementary A c v) =
      elementary A' (algebraMap A' B' a' * algebraMap B B' c) (algebraMap B B' ∘ v) := by
  rw [elementary_def, baseChangeEquiv_tmul_smul, baseChangeEquiv_tmul_ιMulti, elementary_def,
    ← algebraMap_smul B' a', smul_smul, mul_comm]
  simp [Function.comp_def]

/-- The inverse base change sends the elementary form of images of `c` and the `vᵢ` to
`1 ⊗ c • dv₀ ∧ ⋯ ∧ dvₙ₋₁`. -/
@[simp]
theorem baseChangeEquiv_symm_elementary {n : ℕ} (c : B) (v : Fin n → B) :
    (baseChangeEquiv A A' B B' n).symm (elementary A' (algebraMap B B' c) (algebraMap B B' ∘ v)) =
      1 ⊗ₜ elementary A c v := by
  rw [LinearEquiv.symm_apply_eq, baseChangeEquiv_tmul_elementary, map_one, one_mul]

/-- `A'`-linear maps out of `A' ⊗[A] Ωⁿ_(B/A)` agree once they agree on every
`1 ⊗ c • dv₀ ∧ ⋯ ∧ dvₙ₋₁`. -/
theorem baseChange_forms_hom_ext {n : ℕ} {M : Type*} [AddCommGroup M] [Module A M] [Module A' M]
    [IsScalarTower A A' M] {f g : A' ⊗[A] Forms A B n →ₗ[A'] M}
    (h : ∀ (c : B) (v : Fin n → B), f (1 ⊗ₜ elementary A c v) = g (1 ⊗ₜ elementary A c v)) :
    f = g :=
  TensorProduct.AlgebraTensorModule.curry_injective <| LinearMap.ext_ring <| forms_hom_ext h

/-- Base change of forms is the `A'`-linear extension of the comparison
`Ωⁿ_(B/A) → Ωⁿ_(B'/A) → Ωⁿ_(B'/A')`: pullback along `B → B'`, followed by the map induced by
`Ω[B'⁄A] → Ω[B'⁄A']`. -/
theorem baseChangeEquiv_tmul {n : ℕ} (a' : A') (ω : Forms A B n) :
    baseChangeEquiv A A' B B' n (a' ⊗ₜ ω) =
      a' • exteriorPower.map n (map A A' B' B') (pullback (IsScalarTower.toAlgHom A B B') n ω) := by
  have h : (baseChangeEquiv A A' B B' n).toLinearMap =
      ((exteriorPower.map n (map A A' B' B')).restrictScalars A ∘ₗ
        pullbackLinear (IsScalarTower.toAlgHom A B B') n).liftBaseChange A' :=
    baseChange_forms_hom_ext fun c v => by
      simp only [LinearEquiv.coe_coe, LinearMap.liftBaseChange_tmul, one_smul,
        LinearMap.comp_apply, LinearMap.coe_restrictScalars, pullbackLinear_apply,
        pullback_elementary, baseChangeEquiv_tmul_elementary]
      simp [elementary_def, exteriorPower.map_apply_ιMulti, Function.comp_def, algebraMap_smul]
  simpa using LinearMap.congr_fun h (a' ⊗ₜ ω)

/-- **Base change preserves wedge products**: `(ab) ⊗ (α ∧ β)` goes to the wedge product of the
images of `a ⊗ α` and `b ⊗ β`. -/
theorem baseChangeEquiv_wedge {m n : ℕ} (a b : A') (α : Forms A B m) (β : Forms A B n) :
    baseChangeEquiv A A' B B' (m + n)
        ((a * b) ⊗ₜ GradedMonoid.GMul.mul (A := fun i => Forms A B i) α β) =
      GradedMonoid.GMul.mul (A := fun i => Forms A' B' i) (baseChangeEquiv A A' B B' m (a ⊗ₜ α))
        (baseChangeEquiv A A' B B' n (b ⊗ₜ β)) := by
  ext
  simp only [baseChangeEquiv_tmul, pullback_wedge, SetLike.coe_gMul, SetLike.val_smul_of_tower,
    coe_map, map_mul, smul_mul_smul_comm]

/-- **Base change commutes with the de Rham differential**: the base change of `d` along
`A → A'` corresponds to the de Rham differential of `B'` over `A'`. -/
@[simp]
theorem baseChangeEquiv_d {n : ℕ} (x : A' ⊗[A] Forms A B n) :
    baseChangeEquiv A A' B B' (n + 1) ((d A B n).baseChange A' x) =
      d A' B' n (baseChangeEquiv A A' B B' n x) := by
  have h : (baseChangeEquiv A A' B B' (n + 1)).toLinearMap ∘ₗ (d A B n).baseChange A' =
      d A' B' n ∘ₗ (baseChangeEquiv A A' B B' n).toLinearMap :=
    baseChange_forms_hom_ext fun c v => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
        d_elementary, baseChangeEquiv_tmul_ιMulti, baseChangeEquiv_tmul_elementary, Fin.comp_cons]
      simp [Function.comp_def]
  exact LinearMap.congr_fun h x

/-- In degree zero, base change of forms is the pushout identification `A' ⊗[A] B ≃ B'`:
under `Ω⁰ ≃ B` and `Ω⁰ ≃ B'`, it sends `a' ⊗ b` to `a' • b`. -/
@[simp]
theorem zeroEquiv_baseChangeEquiv (a' : A') (ω : Forms A B 0) :
    zeroEquiv B' Ω[B'⁄A'] (baseChangeEquiv A A' B B' 0 (a' ⊗ₜ ω)) =
      a' • algebraMap B B' (zeroEquiv B Ω[B⁄A] ω) := by
  obtain ⟨b, rfl⟩ : ∃ b : B, b • ιMulti B 0 ![] = ω :=
    ⟨zeroEquiv B Ω[B⁄A] ω, (zeroEquiv B Ω[B⁄A]).injective <| by simp⟩
  rw [baseChangeEquiv_tmul_smul, baseChangeEquiv_tmul_ιMulti, ← algebraMap_smul B' a', smul_smul]
  simp [Algebra.smul_def, mul_comm]

/-- In degree one, base change of forms is Mathlib's `KaehlerDifferential.tensorKaehlerEquivBase`
under the identifications `Ω¹ ≃ Ω[B⁄A]` and `Ω¹ ≃ Ω[B'⁄A']`. -/
@[simp]
theorem oneEquiv_baseChangeEquiv (x : A' ⊗[A] Forms A B 1) :
    oneEquiv B' Ω[B'⁄A'] (baseChangeEquiv A A' B B' 1 x) =
      tensorKaehlerEquivBase A A' B B'
        (((oneEquiv B Ω[B⁄A]).toLinearMap.restrictScalars A).lTensor A' x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a' ω =>
    obtain ⟨θ, rfl⟩ : ∃ θ : Ω[B⁄A], ιMulti B 1 (fun _ => θ) = ω :=
      ⟨oneEquiv B Ω[B⁄A] ω, (oneEquiv B Ω[B⁄A]).injective <| by simp⟩
    rw [baseChangeEquiv_tmul_ιMulti, ← algebraMap_smul B' a', map_smul, algebraMap_smul]
    simp [Function.comp_def]

end

end Forms

section Complex

variable (A A' B B' : Type u) [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.IsPushout A A' B B']

public section

/-- The square expressing that the degreewise base change of forms commutes with the de Rham
differentials, after extension of scalars along `A → A'`. -/
private theorem extendScalars_map_d_comp (n : ℕ) :
    (ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of A (Forms A B n)) ≪≫
          (baseChangeEquiv A A' B B' n).toModuleIso).hom ≫ ModuleCat.ofHom (d A' B' n) =
      (ModuleCat.extendScalars (algebraMap A A')).map (ModuleCat.ofHom (d A B n)) ≫
        (ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of A (Forms A B (n + 1))) ≪≫
          (baseChangeEquiv A A' B B' (n + 1)).toModuleIso).hom := by
  rw [Iso.trans_hom, Iso.trans_hom, ModuleCat.extendScalarsAlgebraMapIso_hom_naturality_assoc,
    Category.assoc, cancel_epi, ModuleCat.hom_ofHom]
  exact ModuleCat.hom_ext (LinearMap.ext fun x => (baseChangeEquiv_d x).symm)

/-- **Base change of the de Rham complex.** For a base change `B' = A' ⊗[A] B`, extending the
scalars of the de Rham complex `Ω•_(B/A)` along `A → A'` gives `Ω•_(B'/A')`; in degree `n` the
isomorphism is `baseChangeEquiv A A' B B' n` (`complexBaseChangeIso_hom_f_tmul`). -/
noncomputable def complexBaseChangeIso :
    ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex _).obj (complex A B) ≅
      complex A' B' :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of A (Forms A B n)) ≪≫
      (baseChangeEquiv A A' B B' n).toModuleIso)
    (by
      rintro n _ rfl
      -- After `complex_d`, both squares are stated between the modules of forms, which are the
      -- objects of the de Rham complexes by definition (`complex_X`).
      rw [Functor.mapHomologicalComplex_obj_d, complex_d, complex_d]
      exact extendScalars_map_d_comp A A' B B' n)

/-- In degree `n`, the base change isomorphism of de Rham complexes is `baseChangeEquiv`:
it sends `a' ⊗ ω` to `baseChangeEquiv A A' B B' n (a' ⊗ ω)`. Not a `simp` lemma: `simp` first
retypes the element through `Functor.mapHomologicalComplex_obj_X`. -/
theorem complexBaseChangeIso_hom_f_tmul (n : ℕ) (a' : A') (ω : Forms A B n) :
    ((complexBaseChangeIso A A' B B').hom.f n).hom (a' ⊗ₜ[A, algebraMap A A'] ω) =
      baseChangeEquiv A A' B B' n (a' ⊗ₜ ω) := by
  simp only [complexBaseChangeIso, HomologicalComplex.Hom.isoOfComponents_hom_f]
  -- The component is typed in `(complex A' B').X n`, which is the module of forms only up to
  -- `complex_X`; `erw` matches the composite through this definitional equality.
  erw [Iso.trans_hom, ModuleCat.comp_apply, ModuleCat.extendScalarsAlgebraMapIso_hom_tmul]
  rfl

end

end Complex

end TauCeti.DeRham
