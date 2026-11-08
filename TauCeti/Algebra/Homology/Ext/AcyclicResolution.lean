/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Computing `Ext` from a resolution acyclic for `Hom(P, -)`

Let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be a resolution of an object `F` of an abelian category, and let `P`
be an object such that `Extᵏ⁺¹(P, Kʲ) = 0` for all `j` and `k`. Then the complex `Hom(P, K)`
computes `Extⁿ(P, F)`: every class is the class of a cocycle `P ⟶ Kⁿ`, the class is additive in the
cocycle, and it vanishes exactly on the coboundaries. For an injective resolution this is Mathlib's
`CategoryTheory.InjectiveResolution.extMk`; here the terms of `K` need only be acyclic for `P`.
On a site with `P` the free abelian sheaf on an object `V`, `Hom(P, K)` is the complex of sections
`K(V)`, and the terms may be flasque sheaves on a space instead of injective sheaves.

Write `Zⁿ` for the cycles of `K` in degree `n`. The resolution splits into the short exact
sequences `0 ⟶ F ⟶ K⁰ ⟶ Z¹ ⟶ 0` and `0 ⟶ Zⁿ ⟶ Kⁿ ⟶ Zⁿ⁺¹ ⟶ 0`. The Yoneda product of their
extension classes is the class `CochainComplex.resolutionExtClass` in `Extⁿ⁺¹(Zⁿ⁺¹, F)` of the
exact sequence `0 ⟶ F ⟶ K⁰ ⟶ ⋯ ⟶ Kⁿ ⟶ Zⁿ⁺¹ ⟶ 0`. A cocycle `f : P ⟶ Kⁿ⁺¹` factors through
`Zⁿ⁺¹`, and composing with this class gives an element of `Extⁿ⁺¹(P, F)`
(`CochainComplex.extMk`). By dimension shifting, composition with the class is bijective on
`Extᵏ⁺¹(P, Zⁿ⁺¹)`, and on `Ext⁰(P, Zⁿ⁺¹)` it is onto with kernel the maps factoring through
`Kⁿ`. Hence every class arises from a cocycle (`CochainComplex.extMk_surjective`), and a cocycle
gives zero exactly when it is a coboundary (`CochainComplex.extMk_succ_eq_zero_iff`).

## Main definitions

* `CochainComplex.resolutionExtClass`: the class in `Extⁿ⁺¹(Zⁿ⁺¹, F)` of the truncated
  resolution.
* `CochainComplex.extMk`: the class in `Extⁿ(P, F)` of a cocycle `P ⟶ Kⁿ`.

## Main results

* `CochainComplex.resolutionExtClass_postcomp_bijective`: dimension shifting along the truncated
  resolution, from `CategoryTheory.ShortComplex.ShortExact.extClass_postcomp_bijective`.
* `CochainComplex.extMk_add`, `CochainComplex.extMk_zero`, `CochainComplex.extMk_neg` and
  `CochainComplex.extMk_sub`: `extMk` is additive in the cocycle.
* `CochainComplex.mk₀_comp_extMk`: `extMk` is natural in `P`.
* `CochainComplex.resolutionExtClass_comp_mk₀` and `CochainComplex.extMk_comp_mk₀`: the class of
  the truncated resolution and `extMk` are natural in morphisms of resolutions.
* `CochainComplex.extMk_surjective`, `CochainComplex.extMk_zero_eq_zero_iff` and
  `CochainComplex.extMk_succ_eq_zero_iff`: `extMk` identifies `Extⁿ(P, F)` with the cohomology
  of `Hom(P, K)`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.1.2A.
* The Stacks Project, Derived Categories, Lemma 13.15.6 (tag 05T8) and Lemma 13.16.7 (tag 015E).
-/

public section

open CategoryTheory Limits Abelian

universe w v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {F : C} (K : CochainComplex C ℕ) (ι : F ⟶ K.X 0) [Mono ι] (hι : ι ≫ K.d 0 1 = 0)
  (hι' : (ShortComplex.mk ι (K.d 0 1) hι).Exact) (hK : ∀ j, K.ExactAt (j + 1))

omit [HasExt C] in
include hι' hK in
/-- The first short exact sequence `0 ⟶ F ⟶ K⁰ ⟶ Z¹ ⟶ 0` of the resolution. -/
lemma shortExact_resolution_zero :
    (ShortComplex.mk ι (K.toCycles 0 1) (K.comp_toCycles_eq_zero 1 ι hι)).ShortExact :=
  K.shortExact_toCycles ι hι hι' (by simp) (hK 0)

omit [HasExt C] in
include hK in
/-- The short exact sequence `0 ⟶ Zⁿ⁺¹ ⟶ Kⁿ⁺¹ ⟶ Zⁿ⁺² ⟶ 0` of the resolution. -/
lemma shortExact_resolution_succ (n : ℕ) :
    (ShortComplex.mk (K.iCycles (n + 1)) (K.toCycles (n + 1) (n + 2))
      (K.iCycles_toCycles _ _)).ShortExact :=
  K.cyclesShortComplex_def (n + 1) (n + 2) ▸
    K.cyclesShortComplex_shortExact (n + 1) (n + 2) (by simp) (hK (n + 1))

/-- The class in `Extⁿ⁺¹(Zⁿ⁺¹, F)` of the exact sequence `0 ⟶ F ⟶ K⁰ ⟶ ⋯ ⟶ Kⁿ ⟶ Zⁿ⁺¹ ⟶ 0`
obtained by truncating the resolution `F ⟶ K` at the cycles `Zⁿ⁺¹` in degree `n + 1`. It is the
Yoneda product of the extension classes of the short exact sequences
`0 ⟶ Zʲ ⟶ Kʲ ⟶ Zʲ⁺¹ ⟶ 0`, `j ≤ n`, with `Z⁰ = F`. -/
noncomputable def resolutionExtClass : (n : ℕ) → Ext.{w} (K.cycles (n + 1)) F (n + 1)
  | 0 => (K.shortExact_resolution_zero ι hι hι' hK).extClass
  | n + 1 => (K.shortExact_resolution_succ hK n).extClass.comp (resolutionExtClass n) (by omega)

@[simp]
lemma resolutionExtClass_zero :
    K.resolutionExtClass ι hι hι' hK 0 = (K.shortExact_resolution_zero ι hι hι' hK).extClass :=
  (rfl)

lemma resolutionExtClass_succ (n : ℕ) :
    K.resolutionExtClass ι hι hι' hK (n + 1) =
      (K.shortExact_resolution_succ hK n).extClass.comp (K.resolutionExtClass ι hι hι' hK n)
        (by omega) :=
  (rfl)

variable {K} {F' : C} {K' : CochainComplex C ℕ} (ι' : F' ⟶ K'.X 0) [Mono ι']
  (hι₁ : ι' ≫ K'.d 0 1 = 0) (hι₁' : (ShortComplex.mk ι' (K'.d 0 1) hι₁).Exact)
  (hK' : ∀ j, K'.ExactAt (j + 1)) {φ : F ⟶ F'} {ψ : K ⟶ K'} (hψ : ι ≫ ψ.f 0 = φ ≫ ι')

include hψ in
/-- The class of the truncated resolution is natural in morphisms of resolutions: for a chain map
`ψ : K ⟶ K'` lifting `φ : F ⟶ F'`, pushing the class for `K` forward along `φ` gives the class for
`K'` pulled back along the induced map `Zⁿ⁺¹ ⟶ Z'ⁿ⁺¹` of cycles. -/
lemma resolutionExtClass_comp_mk₀ (n : ℕ) :
    (K.resolutionExtClass ι hι hι' hK n).comp (Ext.mk₀ φ) (add_zero _) =
      (Ext.mk₀ (HomologicalComplex.cyclesMap ψ (n + 1))).comp
        (K'.resolutionExtClass ι' hι₁ hι₁' hK' n) (zero_add _) := by
  induction n with
  | zero =>
    exact (K.shortExact_resolution_zero ι hι hι' hK).extClass_naturality
      (K'.shortExact_resolution_zero ι' hι₁ hι₁' hK')
      { τ₁ := φ
        τ₂ := ψ.f 0
        τ₃ := HomologicalComplex.cyclesMap ψ 1
        comm₁₂ := hψ.symm
        comm₂₃ := by simp [← cancel_mono (K'.iCycles 1)] }
  | succ n ih =>
    rw [resolutionExtClass_succ, resolutionExtClass_succ, Ext.comp_assoc_of_third_deg_zero, ih,
      ← Ext.comp_assoc_of_second_deg_zero, (K.shortExact_resolution_succ hK n).extClass_naturality
      (K'.shortExact_resolution_succ hK' n)
      { τ₁ := HomologicalComplex.cyclesMap ψ (n + 1)
        τ₂ := ψ.f (n + 1)
        τ₃ := HomologicalComplex.cyclesMap ψ (n + 2)
        comm₁₂ := by simp
        comm₂₃ := by simp [← cancel_mono (K'.iCycles (n + 2))] }]
    exact Ext.comp_assoc _ _ _ _ _ (by omega)

variable (P : C) (hP : ∀ j k, Subsingleton (Ext.{w} P (K.X j) (k + 1)))

include hP in
/-- Composition with the class of the truncated resolution is bijective in positive degrees, when
the terms of the resolution are acyclic for `P`. -/
theorem resolutionExtClass_postcomp_bijective (n : ℕ) {k m : ℕ} (h : k + 1 + (n + 1) = m) :
    Function.Bijective ((K.resolutionExtClass ι hι hι' hK n).postcomp P h) := by
  induction n generalizing k m with
  | zero =>
    exact (K.shortExact_resolution_zero ι hι hι' hK).extClass_postcomp_bijective P h
      (hP 0 k) (by subst h; exact hP 0 (k + 1))
  | succ n ih =>
    have e : (K.resolutionExtClass ι hι hι' hK (n + 1)).postcomp P h =
        ((K.resolutionExtClass ι hι hι' hK n).postcomp P (by omega : k + 1 + 1 + (n + 1) = m)).comp
          ((K.shortExact_resolution_succ hK n).extClass.postcomp P rfl) := by
      ext x
      exact (Ext.comp_assoc _ _ _ rfl (by omega) (by omega)).symm
    rw [e]
    exact (ih (k := k + 1) (by omega)).comp
      ((K.shortExact_resolution_succ hK n).extClass_postcomp_bijective P rfl (hP (n + 1) k)
        (hP (n + 1) (k + 1)))

include hP in
/-- Composition with the class of the truncated resolution maps `Ext⁰(P, Zⁿ⁺¹)` onto
`Extⁿ⁺¹(P, F)`. -/
theorem resolutionExtClass_postcomp_surjective (n : ℕ) :
    Function.Surjective ((K.resolutionExtClass ι hι hι' hK n).postcomp P (zero_add _)) := by
  cases n with
  | zero =>
    exact fun x ↦ Ext.covariant_sequence_exact₁ P (K.shortExact_resolution_zero ι hι hι' hK)
      x (by subsingleton [hP 0 0]) rfl
  | succ n =>
    intro x
    obtain ⟨y, rfl⟩ := (K.resolutionExtClass_postcomp_bijective ι hι hι' hK P hP n
      (by omega : 0 + 1 + (n + 1) = n + 1 + 1)).2 x
    obtain ⟨z, rfl⟩ := Ext.covariant_sequence_exact₁ P (K.shortExact_resolution_succ hK n) y
      (by subsingleton [hP (n + 1) 0]) rfl
    refine ⟨z, ?_⟩
    simp only [AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply]
    rw [resolutionExtClass_succ]
    exact (Ext.comp_assoc (a₁₂ := 1) (a₂₃ := n + 1 + 1) (a := n + 1 + 1) z _ _ rfl (by omega)
      (by omega)).symm

include hP in
/-- An element of `Ext⁰(P, Zⁿ⁺¹)` is killed by composition with the class of the truncated
resolution exactly when it factors through `Kⁿ`. -/
theorem resolutionExtClass_postcomp_eq_zero_iff (n : ℕ) (x : Ext.{w} P (K.cycles (n + 1)) 0) :
    x.comp (K.resolutionExtClass ι hι hι' hK n) (zero_add _) = 0 ↔
      ∃ y : Ext.{w} P (K.X n) 0, y.comp (Ext.mk₀ (K.toCycles n (n + 1))) (add_zero 0) = x := by
  cases n with
  | zero =>
    have hS := K.shortExact_resolution_zero ι hι hι' hK
    refine ⟨fun hx ↦ Ext.covariant_sequence_exact₃ P hS x rfl hx, ?_⟩
    rintro ⟨y, rfl⟩
    have : (Ext.mk₀ (K.toCycles 0 1)).comp hS.extClass (zero_add 1) = 0 := hS.comp_extClass
    rw [resolutionExtClass_zero, Ext.comp_assoc_of_second_deg_zero, this, Ext.comp_zero]
  | succ n =>
    have hS := K.shortExact_resolution_succ hK n
    have hinj := (K.resolutionExtClass_postcomp_bijective ι hι hι' hK P hP n
      (by omega : 0 + 1 + (n + 1) = n + 1 + 1)).1
    rw [resolutionExtClass_succ, ← Ext.comp_assoc _ _ _ rfl (by omega) (by omega)]
    refine ⟨fun hx ↦ Ext.covariant_sequence_exact₃ P hS x rfl
      (hinj (by simpa using hx)), ?_⟩
    rintro ⟨y, rfl⟩
    rw [Ext.comp_assoc_of_second_deg_zero]
    have : (Ext.mk₀ (K.toCycles (n + 1) (n + 1 + 1))).comp hS.extClass (zero_add 1) = 0 :=
      hS.comp_extClass
    rw [this, Ext.comp_zero, Ext.zero_comp]

variable {P}

/-- The class in `Extⁿ(P, F)` of a cocycle `f : P ⟶ Kⁿ` of the complex `Hom(P, K)`, for a
resolution `F ⟶ K`. In degree `0` it is the factorization of `f` through `F`; in degree `n + 1`
it is the factorization of `f` through the cycles `Zⁿ⁺¹`, composed with the class
`resolutionExtClass` of the truncated resolution. -/
noncomputable def extMk : {n : ℕ} → (f : P ⟶ K.X n) → f ≫ K.d n (n + 1) = 0 → Ext.{w} P F n
  | 0, f, hf => Ext.mk₀ (hι'.lift f hf)
  | n + 1, f, hf => (Ext.mk₀ (K.liftCycles f (n + 2) (by simp) hf)).comp
      (K.resolutionExtClass ι hι hι' hK n) (zero_add _)

lemma extMk_of_deg_zero (f : P ⟶ K.X 0) (hf : f ≫ K.d 0 (0 + 1) = 0) :
    K.extMk ι hι hι' hK f hf = Ext.mk₀ (hι'.lift f hf) :=
  (rfl)

lemma extMk_of_deg_succ {n : ℕ} (f : P ⟶ K.X (n + 1)) (hf : f ≫ K.d (n + 1) (n + 1 + 1) = 0) :
    K.extMk ι hι hι' hK f hf = (Ext.mk₀ (K.liftCycles f (n + 2) (by simp) hf)).comp
      (K.resolutionExtClass ι hι hι' hK n) (zero_add _) :=
  (rfl)

/-- The class of a sum of cocycles is the sum of their classes. -/
lemma extMk_add {n : ℕ} (f g : P ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0)
    (hg : g ≫ K.d n (n + 1) = 0) :
    K.extMk ι hι hι' hK (f + g) (by simp [hf, hg]) =
      K.extMk ι hι hι' hK f hf + K.extMk ι hι hι' hK g hg := by
  cases n with
  | zero =>
    simp only [extMk_of_deg_zero, ← Ext.mk₀_add]
    congr 1
    simp [← cancel_mono ι, hι'.lift_f]
  | succ n =>
    simp only [extMk_of_deg_succ, ← Ext.add_comp, ← Ext.mk₀_add]
    congr 2
    simp [← cancel_mono (K.iCycles (n + 1))]

/-- The zero cocycle has class zero. -/
@[simp]
lemma extMk_zero {n : ℕ} :
    K.extMk ι hι hι' hK (0 : P ⟶ K.X n) zero_comp = 0 := by
  have h := K.extMk_add ι hι hι' hK (0 : P ⟶ K.X n) 0 zero_comp zero_comp
  simp only [add_zero] at h
  exact left_eq_add.1 h

/-- The class of the negative of a cocycle is the negative of its class. -/
lemma extMk_neg {n : ℕ} (f : P ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    K.extMk ι hι hι' hK (-f) (by simp [hf]) = -K.extMk ι hι hι' hK f hf := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← K.extMk_add]
  simp only [neg_add_cancel, extMk_zero]

/-- The class of a difference of cocycles is the difference of their classes. -/
lemma extMk_sub {n : ℕ} (f g : P ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0)
    (hg : g ≫ K.d n (n + 1) = 0) :
    K.extMk ι hι hι' hK (f - g) (by simp [hf, hg]) =
      K.extMk ι hι hι' hK f hf - K.extMk ι hι hι' hK g hg := by
  simp only [sub_eq_add_neg, ← K.extMk_neg ι hι hι' hK g hg, ← K.extMk_add]

/-- The class of a cocycle is natural in `P`: precomposing it with `g : P' ⟶ P` gives the class of
the cocycle `g ≫ f`. -/
lemma mk₀_comp_extMk {n : ℕ} (f : P ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) {P' : C}
    (g : P' ⟶ P) :
    (Ext.mk₀ g).comp (K.extMk ι hι hι' hK f hf) (zero_add _) =
      K.extMk ι hι hι' hK (g ≫ f) (by simp [hf]) := by
  cases n with
  | zero =>
    rw [extMk_of_deg_zero, extMk_of_deg_zero, Ext.mk₀_comp_mk₀]
    congr 1
    simp [← cancel_mono ι, hι'.lift_f]
  | succ n =>
    rw [extMk_of_deg_succ, extMk_of_deg_succ, ← Ext.comp_assoc_of_second_deg_zero,
      Ext.mk₀_comp_mk₀]
    congr 2
    simp [← cancel_mono (K.iCycles (n + 1))]

include hψ in
/-- The class of a cocycle is natural in morphisms of resolutions: for a chain map `ψ : K ⟶ K'`
lifting `φ : F ⟶ F'`, pushing the class of `f : P ⟶ Kⁿ` forward along `φ` gives the class of the
cocycle `f ≫ ψⁿ` of `Hom(P, K')`. -/
lemma extMk_comp_mk₀ {n : ℕ} (f : P ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    (K.extMk ι hι hι' hK f hf).comp (Ext.mk₀ φ) (add_zero n) =
      K'.extMk ι' hι₁ hι₁' hK' (f ≫ ψ.f n)
        (by rw [Category.assoc, ψ.comm, reassoc_of% hf, zero_comp]) := by
  cases n with
  | zero =>
    rw [extMk_of_deg_zero, extMk_of_deg_zero, Ext.mk₀_comp_mk₀]
    congr 1
    simp [← cancel_mono ι', ← hψ, hι'.lift_f_assoc, hι₁'.lift_f]
  | succ n =>
    rw [extMk_of_deg_succ, extMk_of_deg_succ, Ext.comp_assoc_of_third_deg_zero,
      resolutionExtClass_comp_mk₀ ι hι hι' hK ι' hι₁ hι₁' hK' hψ,
      ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
    congr 2
    simp

include hP in
/-- **Every class in `Extⁿ(P, F)` is the class of a cocycle** of `Hom(P, K)`, for a resolution
`F ⟶ K` whose terms are acyclic for `P`. -/
theorem extMk_surjective {n : ℕ} (α : Ext.{w} P F n) :
    ∃ (f : P ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0), K.extMk ι hι hι' hK f hf = α := by
  cases n with
  | zero =>
    refine ⟨Ext.homEquiv₀ α ≫ ι, by simp [hι], ?_⟩
    rw [extMk_of_deg_zero, ← Ext.mk₀_homEquiv₀_apply α]
    congr 1
    simp [← cancel_mono ι, hι'.lift_f]
  | succ n =>
    obtain ⟨x, rfl⟩ := K.resolutionExtClass_postcomp_surjective ι hι hι' hK P hP n α
    refine ⟨Ext.homEquiv₀ x ≫ K.iCycles (n + 1), by simp, ?_⟩
    rw [extMk_of_deg_succ]
    simp only [AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply]
    congr 1
    rw [← Ext.mk₀_homEquiv₀_apply x]
    congr 1
    simp [← cancel_mono (K.iCycles (n + 1))]

/-- In degree `0` the class of a cocycle vanishes only for the zero cocycle. -/
theorem extMk_zero_eq_zero_iff (f : P ⟶ K.X 0) (hf : f ≫ K.d 0 (0 + 1) = 0) :
    K.extMk ι hι hι' hK f hf = 0 ↔ f = 0 := by
  rw [extMk_of_deg_zero, Ext.mk₀_eq_zero_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← hι'.lift_f f hf, h, zero_comp]
  · subst h
    simp [← cancel_mono ι, hι'.lift_f]

include hP in
/-- **A cocycle has zero class exactly when it is a coboundary**, for a resolution `F ⟶ K` whose
terms are acyclic for `P`. -/
theorem extMk_succ_eq_zero_iff {n : ℕ} (f : P ⟶ K.X (n + 1))
    (hf : f ≫ K.d (n + 1) (n + 1 + 1) = 0) :
    K.extMk ι hι hι' hK f hf = 0 ↔ ∃ g : P ⟶ K.X n, g ≫ K.d n (n + 1) = f := by
  rw [extMk_of_deg_succ, K.resolutionExtClass_postcomp_eq_zero_iff ι hι hι' hK P hP]
  refine ⟨fun ⟨y, hy⟩ ↦ ⟨Ext.homEquiv₀ y, ?_⟩, fun ⟨g, hg⟩ ↦ ⟨Ext.mk₀ g, ?_⟩⟩
  · rw [← Ext.mk₀_homEquiv₀_apply y, Ext.mk₀_comp_mk₀] at hy
    have := congrArg (· ≫ K.iCycles (n + 1)) (Ext.homEquiv₀.symm.injective hy)
    simpa using this
  · rw [Ext.mk₀_comp_mk₀]
    congr 1
    simp [← cancel_mono (K.iCycles (n + 1)), hg]

end CochainComplex
