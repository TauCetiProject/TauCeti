/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import TauCeti.AlgebraicGeometry.DifferentialOperator.Basic
public import TauCeti.RingTheory.Derivation.Localization

/-!
# Derivations as differential operators on an affine scheme

Let `k → R` be a map of commutative rings, so that `Spec R` is a scheme over `Spec k`. A
`k`-derivation `δ` of `R` extends to every localization `R_p` at a prime
(`Derivation.extendOfIsLocalization`), and applying these extensions pointwise to a section of
the structure sheaf, a locally constant fraction `r / t`, gives the section locally equal to
`(t δ r - r δ t) / t ^ 2`. This defines a derivation `Derivation.specSections δ V` of the
sections over every open `V` of `Spec R`, compatible with restriction, hence a global section
`Derivation.toStructureEnd δ` of the sheaf of differential operators of `Spec R`, of order at
most one, which acts on global sections as `δ`.

For `R = k[X]` and `δ` the derivative this gives the checks of the sheaf of differential
operators of `Spec k[X]`: the derivative has order at most one, and not zero unless `k` is the
zero ring; its square has order at most two, and not one when `2 ≠ 0` in `k`.
-/

public section

open CategoryTheory Opposite TopologicalSpace Polynomial

universe u

namespace AlgebraicGeometry

open StructureSheaf

attribute [local instance] Scheme.algebraOfOver

variable {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]

variable (δ : Derivation k R R)

/-- The extension of `δ` to the localization of `R` at the prime `x`. -/
private noncomputable def stalkDerivation (x : PrimeSpectrum R) :
    Derivation k (Localizations R x) (Localizations R x) :=
  ((Algebra.linearMap R (Localizations R x)).compDer δ).extendOfIsLocalization x.asIdeal.primeCompl

private theorem stalkDerivation_algebraMap (x : PrimeSpectrum R) (r : R) :
    stalkDerivation δ x (algebraMap R _ r) = algebraMap R _ (δ r) :=
  Derivation.extendOfIsLocalization_algebraMap _ _ _

/-- The quotient rule for the extension of `δ` to a localization at a prime. -/
private theorem stalkDerivation_mk (x : PrimeSpectrum R) (r : R) (t : x.asIdeal.primeCompl) :
    stalkDerivation δ x (LocalizedModule.mk r t) =
      LocalizedModule.mk (t * δ r - r * δ t) (t * t) := by
  have hmk : ∀ (a : R) (s : x.asIdeal.primeCompl),
      (LocalizedModule.mk a s : Localizations R x) = IsLocalization.mk' _ a s := fun a s ↦ by
    rw [← Localization.mk_eq_mk']
    rfl
  rw [hmk, hmk, IsLocalization.eq_mk'_iff_mul_eq]
  have h₁ := (stalkDerivation δ x).leibniz (IsLocalization.mk' (Localizations R x) r t)
    (algebraMap R _ t)
  have h₂ := IsLocalization.mk'_spec (Localizations R x) r t
  rw [h₂, stalkDerivation_algebraMap, stalkDerivation_algebraMap, smul_eq_mul, smul_eq_mul] at h₁
  simp only [Submonoid.coe_mul, map_mul, map_sub]
  linear_combination (-algebraMap R (Localizations R x) t) * h₁ -
    algebraMap R (Localizations R x) (δ t) * h₂

/-- Applying the extensions of `δ` pointwise to a section over `V`. -/
private noncomputable def specSectionsFun (V : (Spec R).Opens) (s : Γ(Spec R, V)) :
    Γ(Spec R, V) :=
  ⟨fun x ↦ stalkDerivation δ x.val (s.val x), fun x ↦ by
    obtain ⟨W, hxW, i, r, t, h⟩ := s.property x
    exact ⟨W, hxW, i, t * δ r - r * δ t, t * t, fun y ↦
      ⟨y.val.asIdeal.primeCompl.mul_mem (h y).1 (h y).1,
        (congrArg (stalkDerivation δ _) (h y).2).trans (stalkDerivation_mk δ _ r ⟨t, (h y).1⟩)⟩⟩⟩

private theorem specSectionsFun_apply (V : (Spec R).Opens) (s : Γ(Spec R, V)) (x : V) :
    (specSectionsFun δ V s).val x = stalkDerivation δ x.val (s.val x) :=
  rfl

/-- The derivation of the sections of the structure sheaf of `Spec R` over `V` induced by a
`k`-derivation `δ` of `R`: on the germ of a section at a prime `x` it is the extension of `δ` to
the localization of `R` at `x`. -/
noncomputable def _root_.Derivation.specSections (V : (Spec R).Opens) :
    Derivation k Γ(Spec R, V) Γ(Spec R, V) where
  toFun := specSectionsFun δ V
  map_add' _ _ := Subtype.ext (funext fun x ↦ map_add (stalkDerivation δ x.val) _ _)
  map_smul' c s := Subtype.ext (funext fun x ↦
    (congrArg (stalkDerivation δ x.val) (Scheme.spec_sections_smul_apply V c s x)).trans
      (((stalkDerivation δ x.val).map_smul c _).trans
        (Scheme.spec_sections_smul_apply V c (specSectionsFun δ V s) x).symm))
  map_one_eq_zero' := Subtype.ext (funext fun x ↦ (stalkDerivation δ x.val).map_one_eq_zero)
  leibniz' _ _ := Subtype.ext (funext fun x ↦ (stalkDerivation δ x.val).leibniz _ _)

/-- On the germ of a section at `x`, `δ.specSections` acts by the extension of `δ` to `R_x`. -/
@[simp]
theorem _root_.Derivation.specSections_apply (V : (Spec R).Opens) (s : Γ(Spec R, V)) (x : V) :
    (δ.specSections V s).val x =
      (((Algebra.linearMap R (Localizations R x.val)).compDer δ).extendOfIsLocalization
        (@Ideal.primeCompl R _ x.val.asIdeal x.val.isPrime)) (s.val x) :=
  (rfl)

/-- On the image of `R` in the sections over `V`, `δ.specSections V` is `δ`. -/
theorem _root_.Derivation.specSections_algebraMap (V : (Spec R).Opens) (r : R) :
    δ.specSections V (algebraMap R Γ(Spec R, V) r) = algebraMap R Γ(Spec R, V) (δ r) :=
  Subtype.ext (funext fun x ↦ stalkDerivation_algebraMap δ x.val r)

/-- The derivations `δ.specSections` commute with restriction. -/
theorem _root_.Derivation.presheaf_map_specSections {V W : (Spec R).Opens} (i : W ⟶ V)
    (s : Γ(Spec R, V)) :
    (Spec R).presheaf.map i.op (δ.specSections V s) =
      δ.specSections W ((Spec R).presheaf.map i.op s) :=
  (rfl)

/-- A `k`-derivation `δ` of `R` as a global differential operator on `Spec R`: its component on
an open `V` is `δ.specSections V`. -/
noncomputable def _root_.Derivation.toStructureEnd : (Spec R).StructureEnd k ⊤ :=
  .ofApp (fun V ↦ (δ.specSections V.left : Γ(Spec R, V.left) →ₗ[k] Γ(Spec R, V.left)))
    fun j s ↦ δ.presheaf_map_specSections j.left s

@[simp]
theorem _root_.Derivation.endApp_toStructureEnd (V : Over (⊤ : (Spec R).Opens)) :
    Scheme.endApp δ.toStructureEnd V = δ.specSections V.left :=
  Scheme.endApp_ofApp _ (fun j s ↦ δ.presheaf_map_specSections j.left s) V

/-- A derivation is a differential operator of order at most one. -/
theorem _root_.Derivation.toStructureEnd_mem_differentialOperators_one :
    δ.toStructureEnd ∈ ((Spec R).differentialOperators k 1).obj (op ⊤) :=
    Scheme.mem_differentialOperators_iff.2 fun V ↦ by
  rw [Derivation.endApp_toStructureEnd]
  exact (δ.specSections V.left).mem_differentialOperators_one

theorem _root_.Derivation.toStructureEnd_mem_differentialOperatorsSubring :
    δ.toStructureEnd ∈ (Spec R).differentialOperatorsSubring k ⊤ :=
  Scheme.mem_differentialOperatorsSubring_of_mem δ.toStructureEnd_mem_differentialOperators_one

/-- On global sections, `δ.toStructureEnd` acts as `δ`. -/
theorem _root_.Derivation.endApp_toStructureEnd_algebraMap (r : R) :
    Scheme.endApp δ.toStructureEnd (Over.mk (𝟙 ⊤)) (algebraMap R Γ(Spec R, ⊤) r) =
      algebraMap R Γ(Spec R, ⊤) (δ r) := by
  rw [Derivation.endApp_toStructureEnd]
  exact δ.specSections_algebraMap ⊤ r

/-- An endomorphism of the structure sheaf of `Spec R` of order at most `m`, acting on global
sections as `P`, makes `P` an operator of order at most `m` on `R`. -/
private theorem mem_differentialOperators_of_endApp_algebraMap {m : ℕ}
    {E : (Spec R).StructureEnd k ⊤} (hE : E ∈ ((Spec R).differentialOperators k m).obj (op ⊤))
    {P : R →ₗ[k] R} (hP : ∀ r, Scheme.endApp E (Over.mk (𝟙 ⊤)) (algebraMap R Γ(Spec R, ⊤) r) =
      algebraMap R Γ(Spec R, ⊤) (P r)) :
    P ∈ TauCeti.differentialOperators k R R R m := by
  -- the open `(Over.mk (𝟙 ⊤)).left` is `⊤`; writing it this way keeps the `k`-algebra structure
  -- `Scheme.algebraOfOver` rather than Mathlib's structure on global sections of affine schemes
  let φ : R →+* Γ(Spec R, (Over.mk (𝟙 ⊤)).left) := algebraMap R Γ(Spec R, ⊤)
  let f : R →ₛₗ[φ] Γ(Spec R, (Over.mk (𝟙 ⊤)).left) :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := map_mul φ }
  have hinj : Function.Injective φ := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.injective
  exact TauCeti.mem_differentialOperators_of_intertwining (ι := Unit) (fun _ ↦ φ) (fun _ ↦ f)
    (fun _ ↦ f) (fun y hy ↦ hinj ((hy ()).trans (map_zero φ).symm)) (fun _ r ↦ (hP r).symm)
    fun _ ↦ Scheme.mem_differentialOperators_iff.1 hE (Over.mk (𝟙 ⊤))

end AlgebraicGeometry

/-! ### The affine line -/

open _root_.AlgebraicGeometry

namespace TauCeti

attribute [local instance] Scheme.algebraOfOver

/-- The derivative on `k[X]`, as a global differential operator on the affine line
`Spec k[X]` over `Spec k`. -/
noncomputable abbrev derivativeEnd (k : Type u) [CommRing k] :
    (Spec (CommRingCat.of k[X])).StructureEnd k ⊤ :=
  (derivative' : Derivation k k[X] k[X]).toStructureEnd

/-- The derivative on the affine line has order at most one. -/
theorem derivativeEnd_mem_differentialOperators_one (k : Type u) [CommRing k] :
    derivativeEnd k ∈ ((Spec (CommRingCat.of k[X])).differentialOperators k 1).obj (op ⊤) :=
  Derivation.toStructureEnd_mem_differentialOperators_one _

/-- The derivative on the affine line over a nonzero ring does not have order zero. -/
theorem derivativeEnd_notMem_differentialOperators_zero (k : Type u) [CommRing k] [Nontrivial k] :
    derivativeEnd k ∉ ((Spec (CommRingCat.of k[X])).differentialOperators k 0).obj (op ⊤) :=
  fun h ↦ by
    -- an operator of order zero commutes with multiplication by `X`, but `[∂, X] 1 = 1`
    have h₀ := (mem_differentialOperators_of_endApp_algebraMap h fun r ↦
      Derivation.endApp_toStructureEnd_algebraMap _ r)
    simpa using TauCeti.mem_differentialOperators_zero_iff.1 h₀ X 1

/-- The second derivative on the affine line has order at most two. -/
theorem derivativeEnd_mul_self_mem_differentialOperators_two (k : Type u) [CommRing k] :
    derivativeEnd k * derivativeEnd k ∈
      ((Spec (CommRingCat.of k[X])).differentialOperators k 2).obj (op ⊤) :=
  Scheme.mul_mem_differentialOperators (derivativeEnd_mem_differentialOperators_one k)
    (derivativeEnd_mem_differentialOperators_one k)

/-- The second derivative on the affine line does not have order at most one when `2 ≠ 0`
in `k`. -/
theorem derivativeEnd_mul_self_notMem_differentialOperators_one (k : Type u) [CommRing k]
    (h : (2 : k) ≠ 0) :
    derivativeEnd k * derivativeEnd k ∉
      ((Spec (CommRingCat.of k[X])).differentialOperators k 1).obj (op ⊤) :=
  fun hD ↦ TauCeti.derivative_comp_derivative_notMem_differentialOperators_one h
    (mem_differentialOperators_of_endApp_algebraMap hD fun r ↦ by
      rw [Scheme.endApp_mul, LinearMap.comp_apply, Derivation.endApp_toStructureEnd_algebraMap,
        Derivation.endApp_toStructureEnd_algebraMap]
      rfl)

end TauCeti
