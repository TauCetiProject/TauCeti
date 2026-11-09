/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.FieldTheory.Galois.Infinite
import TauCeti.Algebra.TensorProduct.BaseChange
import TauCeti.RepresentationTheory.GaloisDescent.Injective
import TauCeti.RepresentationTheory.GaloisDescent.Range
import TauCeti.RepresentationTheory.GaloisDescent.Span

/-!
# Galois descent of a field along a semilinear action

Let `L / k` be a finite Galois extension and let `F` be a field containing `L`. A *semilinear
action* of `Gal(L/k)` on `F` is a group homomorphism `ρ : Gal(L/k) →* (F ≃ₐ[k] F)` such that each
`ρ σ` restricts to `σ` on `L`:

`ρ σ (a • x) = σ a • ρ σ x`   for `a ∈ L` and `x ∈ F`.

This is the form a Weil descent datum takes once the conjugates of `F` along `σ ∈ Gal(L/k)` are
all realised on the field `F` itself: an isomorphism from the conjugate of `F` along `σ` to `F` is
a field automorphism of `F` acting on `L` as `σ`, and the cocycle condition on a family of such
isomorphisms says that `σ ↦ ρ σ` is a group homomorphism.

The fixed field `F₀ = F ^ ρ` of the action is a `k`-form of `F`: extending its scalars back to `L`
recovers `F`,

`L ⊗[k] F₀ ≃ₐ[L] F`,   `a ⊗ x ↦ a • x`

(`TauCeti.GaloisDescent.fixedFieldBaseChangeEquiv`). Surjectivity says that `F` is spanned over
`L` by `F₀`, and injectivity that `F₀` and `L` are linearly disjoint over `k`; both are the Galois
descent theorems for semilinear representations of `TauCeti.RepresentationTheory.GaloisDescent`,
applied to the `k`-linear representation of `Gal(L/k)` on `F` underlying `ρ`. No finiteness of
`F` over `L` is needed, so the result applies to function fields, where `F` has transcendence
degree one over `L`.

Conversely, a `k`-form `E` of `F`, an intermediate field for which `a ⊗ x ↦ a • x` is a bijection
`L ⊗[k] E → F`, carries the semilinear action `TauCeti.GaloisDescent.baseChangeAction` of
`Gal(L/k)` on its first factor, and this is the only semilinear action fixing `E` pointwise
(`TauCeti.GaloisDescent.eq_baseChangeAction`). Its fixed field is `E`
(`TauCeti.GaloisDescent.fixedField_baseChangeAction`), and the action attached to the fixed field
of a semilinear action `ρ` is `ρ`
(`TauCeti.GaloisDescent.baseChangeAction_fixedField`).
So semilinear actions of `Gal(L/k)` on `F` and `k`-forms of `F` determine each other. In
particular a field automorphism of `L / k` extends to `F` fixing a given `k`-form, which is how a
model of a curve over `k` is seen to be fixed by `Gal(L/k)`.

If `L` is relatively algebraically closed in `F`, then `k` is relatively algebraically closed in
`F₀` (`TauCeti.GaloisDescent.isIntegrallyClosedIn_fixedField`), for any Galois extension `L / k`,
finite or not: an element of `F₀` algebraic over `k` is algebraic over `L`, hence lies in `L`, and
being fixed by every `σ` it lies in `k`. For function fields this says that the exact constant
field descends.

## Main results

* `TauCeti.GaloisDescent.span_fixedField_eq_top`: `F` is spanned over `L` by the fixed field.
* `TauCeti.GaloisDescent.liftEquiv_fixedField_bijective`: the multiplication map
  `L ⊗[k] F₀ → F` is bijective.
* `TauCeti.GaloisDescent.fixedFieldBaseChangeEquiv`: the resulting isomorphism
  `L ⊗[k] F₀ ≃ₐ[L] F`, with `TauCeti.GaloisDescent.fixedFieldBaseChangeEquiv_tmul` and
  `TauCeti.GaloisDescent.fixedFieldBaseChangeEquiv_symm_apply_coe`.
* `TauCeti.GaloisDescent.baseChangeAction`: the semilinear action of a `k`-form, with
  `TauCeti.GaloisDescent.fixedField_baseChangeAction` and
  `TauCeti.GaloisDescent.baseChangeAction_fixedField`: semilinear actions and
  `k`-forms correspond.
* `TauCeti.GaloisDescent.isIntegrallyClosedIn_fixedField`: relative algebraic closure descends.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  (1.9) Theorem and (1.10) Lemma.
* J.-M. Couveignes, *Calcul et rationalité de fonctions de Belyi en genre 0*, Annales de
  l'Institut Fourier 44 (1994), Théorème 3 (critère de Weil).
* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64 (Galois descent).
-/

public section

open IntermediateField

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable {k L F : Type*} [Field k] [Field L] [Field F] [Algebra k L] [Algebra k F]

/-- The `k`-linear representation of `Gal(L/k)` on `F` underlying a semilinear action. -/
private noncomputable abbrev toRepresentation (ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)) :
    Representation k (L ≃ₐ[k] L) F :=
  (AlgEquiv.toLinearMapHom k F).comp ρ

variable [Algebra L F]

/-- A semilinear automorphism multiplies a scalar multiple by the conjugate scalar. -/
private theorem apply_smul {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a)) (σ : L ≃ₐ[k] L) (a : L)
    (x : F) : ρ σ (a • x) = σ a • ρ σ x := by
  rw [Algebra.smul_def, map_mul, hρ, ← Algebra.smul_def]

/-- **The fixed field spans.** For a semilinear action `ρ` of the automorphism group of `L / k`
on `F`, every element of `F` is an `L`-linear combination of elements fixed by the action. Only
finiteness of the automorphism group of `L / k` is used. -/
theorem span_fixedField_eq_top [Finite (L ≃ₐ[k] L)] {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a)) :
    Submodule.span L (fixedField ρ.range : Set F) = ⊤ := by
  have hinv : ((toRepresentation ρ).invariants : Set F) = fixedField ρ.range := by
    ext x
    simp [Representation.mem_invariants, mem_fixedField_iff]
  rw [← hinv]
  exact span_invariants_eq_top (apply_smul hρ)

variable [IsScalarTower k L F]

/-- **The exact constant field descends.** If `L` is relatively algebraically closed in `F`, then
`k` is relatively algebraically closed in the fixed field of a semilinear action of `Gal(L/k)` on
`F`. The extension `L / k` may be infinite. -/
theorem isIntegrallyClosedIn_fixedField [IsGalois k L] {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hL : IsIntegrallyClosedIn L F) : IsIntegrallyClosedIn k (fixedField ρ.range) := by
  refine (isIntegrallyClosedIn_iff).mpr ⟨(algebraMap k _).injective, fun {x} hx ↦ ?_⟩
  -- An element of `F^ρ` integral over `k` is integral over `L`, hence comes from `L`.
  obtain ⟨a, ha⟩ := hL.isIntegral_iff.mp
    ((hx.map (fixedField ρ.range).val).tower_top (A := L))
  -- That element of `L` is fixed by `Gal(L/k)`, hence lies in `k`.
  have hfix : ∀ σ : L ≃ₐ[k] L, σ a = a := fun σ ↦ (algebraMap L F).injective <| by
    rw [← hρ, ha]
    exact (mem_fixedField_iff _ _).mp x.2 (ρ σ) ⟨σ, rfl⟩
  obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp ((InfiniteGalois.mem_bot_iff_fixed a).mpr hfix)
  exact ⟨c, Subtype.ext <| by simpa [← IsScalarTower.algebraMap_apply] using ha⟩

section FixedField

variable [FiniteDimensional k L] [IsGalois k L]

/-- **Galois descent of a field.** For a semilinear action `ρ` of `Gal(L/k)` on `F`, the
multiplication map `L ⊗[k] F^ρ → F`, `a ⊗ x ↦ a • x`, is bijective. -/
theorem liftEquiv_fixedField_bijective {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a)) :
    Function.Bijective
      (AlgHom.liftEquiv k L (fixedField ρ.range) F (fixedField ρ.range).val) := by
  let f := AlgHom.liftEquiv k L (fixedField ρ.range) F (fixedField ρ.range).val
  refine ⟨?_, ?_⟩
  · have h := liftBaseChange_injective_of_invariant (L := L) (ρ := toRepresentation ρ)
      (f := (fixedField ρ.range).val.toLinearMap) Subtype.val_injective fun σ a x ↦ by
        simp [apply_smul hρ, (mem_fixedField_iff _ _).mp x.2 (ρ σ) ⟨σ, rfl⟩]
    rwa [← AlgHom.liftEquiv_toLinearMap] at h
  · apply (LinearMap.range_eq_top (f := f.toLinearMap)).mp
    refine top_unique ?_
    rw [← span_fixedField_eq_top hρ, Submodule.span_le]
    intro x hx
    exact ⟨1 ⊗ₜ[k] ⟨x, hx⟩, by simp [f]⟩

/-- **Galois descent of a field.** A semilinear action `ρ` of `Gal(L/k)` on `F` exhibits its fixed
field as a `k`-form of `F`: extending scalars from `k` to `L` recovers `F`, by
`a ⊗ x ↦ a • x`. -/
noncomputable def fixedFieldBaseChangeEquiv {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a)) :
    L ⊗[k] fixedField ρ.range ≃ₐ[L] F :=
  AlgEquiv.ofBijective _ (liftEquiv_fixedField_bijective hρ)

/-- `TauCeti.GaloisDescent.fixedFieldBaseChangeEquiv` sends `a ⊗ x` to `a • x`. -/
@[simp]
theorem fixedFieldBaseChangeEquiv_tmul {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a)) (a : L)
    (x : fixedField ρ.range) :
    fixedFieldBaseChangeEquiv hρ (a ⊗ₜ x) = a • (x : F) := by
  simp [fixedFieldBaseChangeEquiv]

/-- The inverse of `TauCeti.GaloisDescent.fixedFieldBaseChangeEquiv` sends an element of the fixed
field to its pure tensor with `1`. -/
@[simp]
theorem fixedFieldBaseChangeEquiv_symm_apply_coe {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a)) (x : fixedField ρ.range) :
    (fixedFieldBaseChangeEquiv hρ).symm (x : F) = 1 ⊗ₜ x :=
  (AlgEquiv.symm_apply_eq _).mpr (by simp)

end FixedField

/-! ### The semilinear action of a `k`-form -/

section Form

variable {E : IntermediateField k F}

/-- The identification `L ⊗[k] E ≃ F` of a `k`-form `E` of `F`, over `k`. -/
private noncomputable abbrev formEquiv (hE : Function.Bijective (AlgHom.liftEquiv k L E F E.val)) :
    L ⊗[k] E ≃ₐ[k] F :=
  (AlgEquiv.ofBijective _ hE).restrictScalars k

/-- The **semilinear action of a `k`-form**. If `E` is a `k`-form of `F`, in the sense that
`a ⊗ x ↦ a • x` is a bijection `L ⊗[k] E → F`, then `Gal(L/k)` acts on `F = L ⊗[k] E` through the
first factor (`TauCeti.ScalarAut.toAlgAut`): `σ (a • x) = σ a • x` for `a ∈ L` and `x ∈ E`
(`TauCeti.GaloisDescent.baseChangeAction_apply_smul`). -/
noncomputable def baseChangeAction (hE : Function.Bijective (AlgHom.liftEquiv k L E F E.val)) :
    (L ≃ₐ[k] L) →* (F ≃ₐ[k] F) :=
  (AlgEquiv.autCongr (formEquiv hE)).toMonoidHom.comp (ScalarAut.toAlgAut (A := E))

/-- The semilinear action of a `k`-form `E` acts on `a • x`, for `a ∈ L` and `x ∈ E`, through
`a`. -/
@[simp]
theorem baseChangeAction_apply_smul (hE : Function.Bijective (AlgHom.liftEquiv k L E F E.val))
    (σ : L ≃ₐ[k] L) (a : L) (x : E) : baseChangeAction hE σ (a • (x : F)) = σ a • (x : F) := by
  have h (b : L) : b • (x : F) = formEquiv hE (b ⊗ₜ x) := by simp
  rw [h, h]
  -- Cancel `formEquiv hE` against its inverse before evaluating it on the pure tensor.
  simp [baseChangeAction, -AlgHom.liftEquiv_tmul]

/-- The action of a `k`-form fixes the elements of the form. -/
@[simp]
theorem baseChangeAction_apply_coe (hE : Function.Bijective (AlgHom.liftEquiv k L E F E.val))
    (σ : L ≃ₐ[k] L) (x : E) : baseChangeAction hE σ (x : F) = x := by
  simpa using baseChangeAction_apply_smul hE σ 1 x

/-- The action of a `k`-form is semilinear: it acts on `L` through `Gal(L/k)`. -/
@[simp]
theorem baseChangeAction_algebraMap (hE : Function.Bijective (AlgHom.liftEquiv k L E F E.val))
    (σ : L ≃ₐ[k] L) (a : L) : baseChangeAction hE σ (algebraMap L F a) = algebraMap L F (σ a) := by
  simpa [Algebra.smul_def] using baseChangeAction_apply_smul hE σ a 1

/-- **A semilinear action is determined by a `k`-form it fixes.** A semilinear action of
`Gal(L/k)` on `F` fixing every element of a `k`-form `E` is the action of `E`. -/
theorem eq_baseChangeAction (hE : Function.Bijective (AlgHom.liftEquiv k L E F E.val))
    {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hfix : ∀ σ (x : E), ρ σ x = x) : ρ = baseChangeAction hE := by
  ext σ y
  obtain ⟨t, rfl⟩ := hE.2 y
  induction t using TensorProduct.inductionOn with
  | tmul a x => simp [apply_smul hρ, hfix]
  | add t u ht hu => simp only [map_add, ht, hu]

variable [FiniteDimensional k L] [IsGalois k L]

/-- **The fixed field of the action of a `k`-form is the form.** Together with
`TauCeti.GaloisDescent.baseChangeAction_fixedField`, this makes
`E ↦ baseChangeAction` and `ρ ↦ fixedField ρ.range` mutually inverse between the `k`-forms of `F`
and the semilinear actions of `Gal(L/k)` on `F`. -/
theorem fixedField_baseChangeAction (hE : Function.Bijective (AlgHom.liftEquiv k L E F E.val)) :
    fixedField (baseChangeAction hE).range = E := by
  have h := range_eq_invariants_of_liftBaseChange_surjective
    (ρ := toRepresentation (baseChangeAction hE)) (f := E.val.toLinearMap)
    (apply_smul (baseChangeAction_algebraMap hE)) (fun σ x ↦ baseChangeAction_apply_coe hE σ x)
    (by rw [← AlgHom.liftEquiv_toLinearMap, AlgHom.coe_toLinearMap]; exact hE.2)
  ext x
  simpa [Representation.mem_invariants] using (SetLike.ext_iff.mp h x).symm

/-- **A semilinear action is the action of its fixed field.** -/
theorem baseChangeAction_fixedField {ρ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F)}
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a)) :
    baseChangeAction (liftEquiv_fixedField_bijective hρ) = ρ :=
  (eq_baseChangeAction (liftEquiv_fixedField_bijective hρ) hρ fun σ x ↦
    (mem_fixedField_iff _ _).mp x.2 (ρ σ) ⟨σ, rfl⟩).symm

end Form

end TauCeti.GaloisDescent
