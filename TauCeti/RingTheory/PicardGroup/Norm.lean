/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Invertible
public import TauCeti.LinearAlgebra.ExteriorPower.Localization
public import TauCeti.RingTheory.Norm.Projective
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import TauCeti.LinearAlgebra.TensorProduct.Hom

/-!
# Norms of invertible modules along finite projective algebras

Let `B` be a commutative `A`-algebra which is finite projective of constant rank `d` as an
`A`-module, and let `L` be an invertible `B`-module. As an `A`-module, `L` is again finite
projective of rank `d`. Following the Stacks Project, the **norm** of `L` is the `A`-module

`Norm_{B/A}(L) = Hom_A(⋀^d B, ⋀^d L)`

of homomorphisms between the top exterior powers (`TauCeti.ModuleNorm A B d L`). Both exterior
powers are invertible `A`-modules, so `Norm_{B/A}(L)` is an invertible `A`-module
(`TauCeti.ModuleNorm.invertible`).

Every `s : L` has a **norm** `TauCeti.ModuleNorm.normMap A B d s : Norm_{B/A}(L)`, the map induced
on top exterior powers by the `A`-linear map `B → L, b ↦ b • s`. It is multiplicative for the norm
`Algebra.projectiveNorm A : B →* A` of the algebra (`TauCeti.ModuleNorm.normMap_smul`):

`normMap (b • s) = projectiveNorm A b • normMap s`,

and the norm of a generator of `L` generates `Norm_{B/A}(L)`
(`TauCeti.ModuleNorm.span_normMap_eq_top_of_span_eq_top`). For `L = B`, the norm of `b` is
multiplication by `projectiveNorm A b` (`TauCeti.ModuleNorm.toHom_normMap_self`), so on trivial
invertible modules the construction recovers the norm of the algebra. A `B`-linear isomorphism
`L ≃ L'` induces an isomorphism of norms which is compatible with the norm maps
(`TauCeti.ModuleNorm.congr_normMap`).

The formation of the norm commutes with base change
(`TauCeti.ModuleNorm.baseChangeEquiv`). Let `A → A'` be a ring map, `B' = A' ⊗[A] B` (in the
form `Algebra.IsPushout A A' B B'`), and let `f : L → L'` be an `A`-linear map which exhibits `L'`
as the base change of `L` to `A'`. Then

`A' ⊗[A] Norm_{B/A}(L) ≃ Norm_{B'/A'}(L')`.

If `L'` is a `B'`-module and `f (b • s) = b • f s` for `b : B`, this is compatible with the norm
maps: `a ⊗ normMap s ↦ a • normMap (f s)` (`TauCeti.ModuleNorm.baseChangeEquiv_tmul_normMap`).
Neither the rank nor the invertibility of `L` is needed for this. Exterior powers commute with base
change (`IsBaseChange.exteriorPower`), and so do modules of linear maps out of the finite
projective module `⋀^d B` (`IsBaseChange.linearMapLeftRight_of_projective`). Since
`f` is only required to be a base change, this applies in particular to localizations of `A`,
which is how the norms over the affine opens of a base are compared.

These are the local trivialisations of the norm of an invertible sheaf along a finite locally free
morphism: over an affine open of the base on which the morphism has constant rank, a local
generator `s` of the sheaf gives the local generator `normMap s` of its norm, and two local
generators differ by a unit of `B` whose norm is the transition function.

## Main definitions

* `TauCeti.ModuleNorm A B d L`: the norm `Hom_A(⋀^d B, ⋀^d L)` of a `B`-module `L`.
* `TauCeti.ModuleNorm.normMap A B d`: the norm `L → Norm_{B/A}(L)`.
* `TauCeti.ModuleNorm.congr`: the isomorphism of norms induced by a `B`-linear isomorphism.
* `TauCeti.ModuleNorm.baseChangeEquiv`: the isomorphism `A' ⊗[A] Norm_{B/A}(L) ≃ Norm_{B'/A'}(L')`
  for a base change `A → A'`.

## Main results

* `TauCeti.ModuleNorm.invertible`: the norm of an invertible module is invertible.
* `TauCeti.ModuleNorm.normMap_smul`: the norm map is multiplicative for `Algebra.projectiveNorm`.
* `TauCeti.ModuleNorm.span_normMap_eq_top_of_span_eq_top`: the norm of a generator is a generator.
* `TauCeti.ModuleNorm.toHom_normMap_self`: for `L = B` the norm map is the norm of the algebra.
* `TauCeti.ModuleNorm.baseChangeEquiv_tmul_normMap`: the base change isomorphism is compatible
  with the norm maps.

## References

* The Stacks Project, Divisors, Section *Norms of invertible modules*, Lemma 0BCY.
-/

public section

open Module

namespace TauCeti

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (d : ℕ) (L : Type*)
  [AddCommGroup L] [Module A L] [Module B L] [IsScalarTower A B L]

/-- The **norm** `Norm_{B/A}(L) = Hom_A(⋀^d B, ⋀^d L)` of a `B`-module `L` along an `A`-algebra
`B`. It is meant for `B` finite projective of constant rank `d` over `A` and `L` invertible over
`B`, when it is an invertible `A`-module (`TauCeti.ModuleNorm.invertible`). -/
def ModuleNorm : Type _ :=
  ⋀[A]^d B →ₗ[A] ⋀[A]^d L

namespace ModuleNorm

noncomputable instance : AddCommGroup (ModuleNorm A B d L) :=
  inferInstanceAs (AddCommGroup (⋀[A]^d B →ₗ[A] ⋀[A]^d L))

noncomputable instance : Module A (ModuleNorm A B d L) :=
  inferInstanceAs (Module A (⋀[A]^d B →ₗ[A] ⋀[A]^d L))

/-- The norm `Norm_{B/A}(L)` is the module of `A`-linear maps `⋀^d B → ⋀^d L`. -/
noncomputable def toHom : ModuleNorm A B d L ≃ₗ[A] (⋀[A]^d B →ₗ[A] ⋀[A]^d L) :=
  LinearEquiv.refl A _

/-- The **norm** of `s : L` in `Norm_{B/A}(L)`: the map induced on top exterior powers by the
`A`-linear map `B → L, b ↦ b • s`. -/
noncomputable def normMap {L : Type*} [AddCommGroup L] [Module A L] [Module B L]
    [IsScalarTower A B L] (s : L) : ModuleNorm A B d L :=
  (toHom A B d L).symm (exteriorPower.map d ((LinearMap.toSpanSingleton B L s).restrictScalars A))

variable {A B d L}

@[simp]
theorem toHom_normMap (s : L) :
    toHom A B d L (normMap A B d s) =
      exteriorPower.map d ((LinearMap.toSpanSingleton B L s).restrictScalars A) :=
  LinearEquiv.apply_symm_apply _ _

section Rank

variable [Module.Finite A B] [Module.Projective A B]

/-- The norm map is multiplicative for the norm of the algebra:
`normMap (b • s) = projectiveNorm A b • normMap s`. -/
theorem normMap_smul (hd : ∀ p, rankAtStalk (R := A) B p = d) (b : B) (s : L) :
    normMap A B d (b • s) = Algebra.projectiveNorm A b • normMap A B d s := by
  apply (toHom A B d L).injective
  have hcomp : (LinearMap.toSpanSingleton B L (b • s)).restrictScalars A =
      (LinearMap.toSpanSingleton B L s).restrictScalars A ∘ₗ Algebra.lmul A B b := by
    ext c
    simp [mul_smul, smul_comm c b s]
  rw [toHom_normMap, map_smul, toHom_normMap, hcomp, exteriorPower.map_comp,
    exteriorPower.map_eq_projectiveDet_smul_id hd]
  simp [LinearMap.comp_smul, Algebra.projectiveNorm_apply]

/-- For `L = B`, the norm of `b` is multiplication by the norm `projectiveNorm A b` of the
algebra. -/
theorem toHom_normMap_self (hd : ∀ p, rankAtStalk (R := A) B p = d) (b : B) :
    toHom A B d B (normMap A B d b) = Algebra.projectiveNorm A b • LinearMap.id := by
  have h1 : (LinearMap.toSpanSingleton B B (1 : B)).restrictScalars A = LinearMap.id := by
    ext
    simp
  have h := normMap_smul (L := B) hd b 1
  rw [smul_eq_mul, mul_one] at h
  rw [h, map_smul, toHom_normMap, h1, exteriorPower.map_id]

variable [Module.Invertible B L]

/-- The norm of an invertible `B`-module along a finite projective algebra `B` of constant rank `d`
is an invertible `A`-module. -/
theorem invertible (hd : ∀ p, rankAtStalk (R := A) B p = d) :
    Module.Invertible A (ModuleNorm A B d L) := by
  have := exteriorPower.invertible_of_rankAtStalk_eq hd
  have := exteriorPower.invertible_of_invertible_of_rankAtStalk_eq (M := L) hd
  exact .congr ((dualTensorHomEquiv A (⋀[A]^d B) (⋀[A]^d L)).trans (toHom A B d L).symm)

/-- The norm of a generator `s` of an invertible `B`-module generates the norm module. -/
theorem span_normMap_eq_top_of_span_eq_top (hd : ∀ p, rankAtStalk (R := A) B p = d) {s : L}
    (hs : Submodule.span B {s} = ⊤) :
    Submodule.span A {normMap A B d s} = ⊤ := by
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton B L s) := by
    rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, hs]
  -- The generator `s` identifies `B` with `L`, so `normMap s` is an isomorphism `⋀^d B ≃ ⋀^d L`.
  let e : B ≃ₗ[A] L :=
    (LinearEquiv.ofBijective _ (Module.Invertible.bijective_of_surjective hsurj)).restrictScalars A
  have he : exteriorPower.map d (e.symm : L →ₗ[A] B) ∘ₗ toHom A B d L (normMap A B d s) =
      LinearMap.id := by
    rw [toHom_normMap, ← exteriorPower.map_comp, ← exteriorPower.map_id]
    congr 1
    ext c
    exact e.symm_apply_apply c
  have := exteriorPower.invertible_of_invertible_of_rankAtStalk_eq (M := L) hd
  refine eq_top_iff.mpr fun ψ _ ↦ Submodule.mem_span_singleton.mpr ?_
  -- An endomorphism of the invertible module `⋀^d L` is multiplication by its determinant.
  obtain ⟨c, hc⟩ : ∃ c : A, toHom A B d L ψ ∘ₗ exteriorPower.map d (e.symm : L →ₗ[A] B) =
      c • LinearMap.id :=
    ⟨_, LinearMap.eq_projectiveDet_smul_id Module.Invertible.rankAtStalk_eq_one _⟩
  refine ⟨c, (toHom A B d L).injective ?_⟩
  rw [← LinearMap.comp_id (toHom A B d L ψ), ← he, ← LinearMap.comp_assoc, hc]
  simp [LinearMap.smul_comp]

end Rank

section Congr

variable {L' L'' : Type*} [AddCommGroup L'] [Module A L'] [Module B L'] [IsScalarTower A B L']
  [AddCommGroup L''] [Module A L''] [Module B L''] [IsScalarTower A B L'']

/-- A `B`-linear isomorphism `L ≃ L'` induces an isomorphism `Norm_{B/A}(L) ≃ Norm_{B/A}(L')`,
by composition with the induced isomorphism `⋀^d L ≃ ⋀^d L'` of top exterior powers. -/
noncomputable def congr (e : L ≃ₗ[B] L') : ModuleNorm A B d L ≃ₗ[A] ModuleNorm A B d L' :=
  let e' : L ≃ₗ[A] L' := e.restrictScalars A
  (toHom A B d L).trans <| (LinearEquiv.arrowCongr (LinearEquiv.refl A _)
    (LinearEquiv.ofLinearMap (exteriorPower.map d (e' : L →ₗ[A] L'))
      (exteriorPower.map d (e'.symm : L' →ₗ[A] L))
      (by rw [← exteriorPower.map_comp, e'.comp_symm, exteriorPower.map_id])
      (by rw [← exteriorPower.map_comp, e'.symm_comp, exteriorPower.map_id]))).trans
    (toHom A B d L').symm

@[simp]
theorem toHom_congr (e : L ≃ₗ[B] L') (ψ : ModuleNorm A B d L) :
    toHom A B d L' (congr e ψ) =
      exteriorPower.map d ((e : L →ₗ[B] L').restrictScalars A) ∘ₗ toHom A B d L ψ :=
  LinearMap.ext fun _ ↦ (rfl)

/-- The isomorphism of norms induced by `e : L ≃ L'` sends the norm of `s` to the norm of
`e s`. -/
@[simp]
theorem congr_normMap (e : L ≃ₗ[B] L') (s : L) :
    congr e (normMap A B d s) = normMap A B d (e s) := by
  apply (toHom A B d L').injective
  rw [toHom_congr, toHom_normMap, toHom_normMap, ← exteriorPower.map_comp]
  congr 1
  ext
  simp

@[simp]
theorem congr_refl : congr (LinearEquiv.refl B L) = LinearEquiv.refl A (ModuleNorm A B d L) := by
  have h : ((LinearEquiv.refl B L : L →ₗ[B] L).restrictScalars A) = LinearMap.id := by
    ext
    simp
  ext ψ : 1
  apply (toHom A B d L).injective
  rw [toHom_congr, LinearEquiv.refl_apply, h, exteriorPower.map_id, LinearMap.id_comp]

theorem congr_trans (e : L ≃ₗ[B] L') (e' : L' ≃ₗ[B] L'') :
    congr (e.trans e') = (congr e).trans (congr e' : ModuleNorm A B d L' ≃ₗ[A] _) := by
  ext ψ : 1
  apply (toHom A B d L'').injective
  rw [LinearEquiv.trans_apply, toHom_congr, toHom_congr, toHom_congr, ← LinearMap.comp_assoc,
    ← exteriorPower.map_comp]
  congr 2

end Congr

section BaseChange

open scoped TensorProduct

variable {A' B' : Type*} [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra A' B'] [Algebra A B']
  [Algebra B B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.IsPushout A A' B B']
  {L' : Type*} [AddCommGroup L'] [Module A' L'] [Module A L'] [IsScalarTower A A' L']
  [Module.Finite A B] [Module.Projective A B] {f : L →ₗ[A] L'}

omit [Module B L] [IsScalarTower A B L] in
-- `Hom_{A'}(⋀^d B', ⋀^d L')` is the base change of `Norm_{B/A}(L) = Hom_A(⋀^d B, ⋀^d L)`: both
-- exterior powers commute with base change, and `⋀^d B` is finite projective.
private theorem isBaseChange_toHom (hf : IsBaseChange A' f) :
    IsBaseChange A' (((Algebra.IsPushout.out (R := A) (S := A') (R' := B)
      (S' := B')).exteriorPower d).linearMapLeftRightHom
        ((hf.exteriorPowerEquiv d).toLinearMap.restrictScalars A ∘ₗ TensorProduct.mk A A' _ 1) ∘ₗ
          (toHom A B d L).toLinearMap) :=
  ((Algebra.IsPushout.out.exteriorPower d).linearMapLeftRight_of_projective
      (hf.exteriorPower d)).comp_equiv _ _

variable (d) in
/-- **The norm commutes with base change.** Let `B' = A' ⊗[A] B` be the base change of `B` along
`A → A'`, and let the `A`-linear map `f : L → L'` exhibit `L'` as the base change of `L` to `A'`.
Then `A' ⊗[A] Norm_{B/A}(L) ≃ Norm_{B'/A'}(L')`: a map `ψ : ⋀^d B → ⋀^d L` is sent to its
`A'`-linear extension `⋀^d B' → ⋀^d L'` (`toHom_baseChangeEquiv_tmul_apply`). When `L'` is a
`B'`-module and `f` is compatible with `B → B'`, it sends `a ⊗ normMap s` to `a • normMap (f s)`
(`baseChangeEquiv_tmul_normMap`). -/
noncomputable def baseChangeEquiv (hf : IsBaseChange A' f) :
    A' ⊗[A] ModuleNorm A B d L ≃ₗ[A'] ModuleNorm A' B' d L' :=
  (isBaseChange_toHom hf).equiv ≪≫ₗ (toHom A' B' d L').symm

omit [Module B L] [IsScalarTower A B L] in
/-- The base change isomorphism sends `a ⊗ ψ` to the `A'`-linear map `⋀^d B' → ⋀^d L'` which
extends `a • ψ` along the comparisons `⋀^d B → ⋀^d B'` and `⋀^d L → ⋀^d L'` of exterior powers
with their base changes. -/
theorem toHom_baseChangeEquiv_tmul_apply (hf : IsBaseChange A' f) (a : A')
    (ψ : ModuleNorm A B d L) (x : ⋀[A]^d B) :
    toHom A' B' d L' (baseChangeEquiv d hf (a ⊗ₜ ψ))
        ((Algebra.IsPushout.out (R := A) (S := A') (R' := B) (S' := B')).exteriorPowerEquiv d
          (1 ⊗ₜ x)) =
      a • hf.exteriorPowerEquiv d (1 ⊗ₜ toHom A B d L ψ x) := by
  simp only [baseChangeEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    IsBaseChange.equiv_tmul, LinearMap.smul_apply, LinearMap.comp_apply]
  -- `x ↦ 1 ⊗ x` is the base change map `⋀^d B → ⋀^d B'` along which the extension is taken.
  exact congrArg (a • ·) (IsBaseChange.linearMapLeftRightHom_comp_apply _ _ _ x)

/-- The base change isomorphism of norms is compatible with the norm maps: if `L'` is a
`B'`-module and `f (b • s) = b • f s` for `b : B`, it sends `a ⊗ normMap s` to
`a • normMap (f s)`. -/
@[simp]
theorem baseChangeEquiv_tmul_normMap [Module B' L'] [IsScalarTower A' B' L']
    (hf : IsBaseChange A' f) (hfB : ∀ (b : B) (s : L), f (b • s) = algebraMap B B' b • f s)
    (a : A') (s : L) :
    baseChangeEquiv d hf (a ⊗ₜ normMap A B d s) = a • normMap A' B' d (f s) := by
  apply (toHom A' B' d L').injective
  have hB : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := Algebra.IsPushout.out
  refine (hB.exteriorPower d).algHom_ext _ _ fun x ↦ ?_
  -- `b ↦ b • f s` extends `b ↦ b • s` along `B → B'` and `f`.
  have h : ((LinearMap.toSpanSingleton B' L' (f s)).restrictScalars A').restrictScalars A ∘ₗ
      (IsScalarTower.toAlgHom A B B').toLinearMap =
        f ∘ₗ (LinearMap.toSpanSingleton B L s).restrictScalars A := by
    ext b
    simp [hfB]
  have := LinearMap.congr_fun (hB.exteriorPowerEquiv_naturality hf d _ _ h) (1 ⊗ₜ x)
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
    LinearEquiv.coe_coe, LinearMap.baseChange_tmul] at this ⊢
  rw [toHom_baseChangeEquiv_tmul_apply, map_smul, toHom_normMap, toHom_normMap,
    LinearMap.smul_apply, ← this]

end BaseChange

end ModuleNorm

end TauCeti
