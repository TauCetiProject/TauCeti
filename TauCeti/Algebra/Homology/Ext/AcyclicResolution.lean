/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
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

The statement is also packaged as an additive equivalence `Extⁿ(P, F) ≃+ Hⁿ(G(K))`
(`CochainComplex.extAddEquivHomologyOfResolution`), for any additive functor `G : C ⥤ Ab`
corepresented by `P` in place of `Hom(P, -)`. A cycle of `G(K)` is a cocycle of `Hom(P, K)`,
and `CochainComplex.extMk` descends to the cohomology of `G(K)`. Allowing such `G` covers the
functor of sections over an object `V` of a site, corepresented by the free abelian sheaf `ℤ[V]`
on `V`, whose values need not lie in the universe of the morphism groups `Hom(ℤ[V], -)`.

## Main definitions

* `CochainComplex.resolutionExtClass`: the class in `Extⁿ⁺¹(Zⁿ⁺¹, F)` of the truncated
  resolution.
* `CochainComplex.extMk`: the class in `Extⁿ(P, F)` of a cocycle `P ⟶ Kⁿ`.
* `CochainComplex.extAddEquivHomologyOfResolution`: the additive equivalence
  `Extⁿ(P, F) ≃+ Hⁿ(G(K))` for an additive functor `G` corepresented by `P`.

## Main results

* `CochainComplex.resolutionExtClass_postcomp_bijective`: dimension shifting along the truncated
  resolution, from `CategoryTheory.ShortComplex.ShortExact.extClass_postcomp_bijective`.
* `CochainComplex.extMk_add`, `CochainComplex.extMk_zero`, `CochainComplex.extMk_neg` and
  `CochainComplex.extMk_sub`: `extMk` is additive in the cocycle.
* `CochainComplex.mk₀_comp_extMk`: `extMk` is natural in `P`.
* `CochainComplex.extMk_surjective`, `CochainComplex.extMk_zero_eq_zero_iff` and
  `CochainComplex.extMk_succ_eq_zero_iff`: `extMk` identifies `Extⁿ(P, F)` with the cohomology
  of `Hom(P, K)`.
* `CochainComplex.extAddEquivHomologyOfResolution_extMk`: the equivalence sends the class of a
  cocycle to the cohomology class of the corresponding cycle of `G(K)`.
* `CochainComplex.extAddEquivHomologyOfResolution_naturality`: the equivalence is natural in the
  corepresenting object: precomposition with `a : P' ⟶ P` corresponds to the map induced in
  cohomology by a compatible natural transformation `G ⟶ G'`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.1.2A.
* The Stacks Project, Derived Categories, Lemma 13.15.6 (tag 05T8) and Lemma 13.16.7 (tag 015E).
-/

public section

open CategoryTheory Limits Abelian

universe t w v u

namespace CategoryTheory.Functor.CorepresentableBy

/-! ### Corepresentations of additive functors to `Ab`

For an additive functor `G : C ⥤ Ab` corepresented by `P`, the bijection `(P ⟶ X) ≃ G(X)` of the
corepresentation is additive. -/

variable {C : Type u} [Category.{v} C] [Preadditive C] {G : C ⥤ AddCommGrpCat.{t}} [G.Additive]
  {P : C} (R : (G ⋙ forget AddCommGrpCat).CorepresentableBy P)

/-- The corepresentation of an additive functor `G : C ⥤ Ab` sends the zero morphism to zero. -/
lemma homEquiv_zero {X : C} : R.homEquiv (0 : P ⟶ X) = (0 : G.obj X) := by
  rw [R.homEquiv_eq, Functor.comp_map, G.map_zero]
  rfl

/-- The inverse of the corepresentation of an additive functor `G : C ⥤ Ab` sends zero to the zero
morphism. -/
lemma homEquiv_symm_zero {X : C} : R.homEquiv.symm (0 : G.obj X) = 0 :=
  R.homEquiv.symm_apply_eq.2 R.homEquiv_zero.symm

/-- The inverse of the corepresentation `(P ⟶ X) ≃ G(X)` of an additive functor `G : C ⥤ Ab` is
additive. -/
lemma homEquiv_symm_add {X : C} (x y : G.obj X) :
    R.homEquiv.symm (x + y) = R.homEquiv.symm x + R.homEquiv.symm y := by
  have h (z : G.obj X) : G.map (R.homEquiv.symm z) (R.homEquiv (𝟙 P)) = z :=
    (R.homEquiv_eq _).symm.trans (R.homEquiv.apply_symm_apply z)
  rw [R.homEquiv.symm_apply_eq, R.homEquiv_eq, Functor.comp_map, G.map_add]
  exact (congrArg₂ (· + ·) (h x) (h y)).symm

end CategoryTheory.Functor.CorepresentableBy

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

variable {K} (P : C) (hP : ∀ j k, Subsingleton (Ext.{w} P (K.X j) (k + 1)))

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

section Homology

/-! ### The cohomology of `G(K)` for a functor `G` corepresented by `P`

Let `G : C ⥤ Ab` be an additive functor corepresented by `P`, for instance `Hom(P, -)`, or the
sections over `V` of abelian sheaves on a site, corepresented by the free abelian sheaf on `V`.
A cycle of the complex `G(K)` in degree `n` is a cocycle `P ⟶ Kⁿ` of `Hom(P, K)`, and its class
`CochainComplex.extMk` identifies the cohomology of `G(K)` in degree `n` with `Extⁿ(P, F)`. -/

variable (G : C ⥤ AddCommGrpCat.{t}) [G.Additive]
  (R : (G ⋙ forget AddCommGrpCat).CorepresentableBy P)

omit [HasExt C] in
include R in
/-- A cycle of `G(K)` corresponds under the corepresentation to a cocycle of `Hom(P, K)`. -/
private lemma homEquiv_symm_iCycles_comp_d (n : ℕ)
    (c : ((G.mapHomologicalComplex _).obj K).cycles n) :
    R.homEquiv.symm (((G.mapHomologicalComplex _).obj K).iCycles n c) ≫ K.d n (n + 1) = 0 := by
  apply R.homEquiv.injective
  rw [R.homEquiv_comp, Equiv.apply_symm_apply, R.homEquiv_eq (0 : P ⟶ K.X (n + 1))]
  simpa using ConcreteCategory.congr_hom (((G.mapHomologicalComplex _).obj K).iCycles_d n (n + 1)) c

/-- The class in `Extⁿ(P, F)` of a cycle of `G(K)` in degree `n`. -/
private noncomputable def cyclesExtClass (n : ℕ) :
    ((G.mapHomologicalComplex _).obj K).cycles n →+ Ext.{w} P F n where
  toFun c := K.extMk ι hι hι' hK (R.homEquiv.symm (((G.mapHomologicalComplex _).obj K).iCycles n c))
    (homEquiv_symm_iCycles_comp_d G R n c)
  map_zero' := by
    simp only [map_zero, R.homEquiv_symm_zero, extMk_zero]
  map_add' c c' := by
    simp only [map_add, R.homEquiv_symm_add]
    exact K.extMk_add ι hι hι' hK _ _ (homEquiv_symm_iCycles_comp_d G R n c)
      (homEquiv_symm_iCycles_comp_d G R n c')

private lemma cyclesExtClass_apply (n : ℕ) (c : ((G.mapHomologicalComplex _).obj K).cycles n) :
    cyclesExtClass ι hι hι' hK G R n c = K.extMk ι hι hι' hK
      (R.homEquiv.symm (((G.mapHomologicalComplex _).obj K).iCycles n c))
      (homEquiv_symm_iCycles_comp_d G R n c) :=
  (rfl)

private lemma cyclesExtClass_eq_extMk {n : ℕ} (c : ((G.mapHomologicalComplex _).obj K).cycles n)
    (f : P ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0)
    (hc : ((G.mapHomologicalComplex _).obj K).iCycles n c = R.homEquiv f) :
    cyclesExtClass ι hι hι' hK G R n c = K.extMk ι hι hι' hK f hf := by
  simp only [cyclesExtClass_apply, hc, Equiv.symm_apply_apply]

omit [HasExt C] in
private lemma iCycles_toCycles_apply (k : ℕ) (y : G.obj (K.X k)) :
    ((G.mapHomologicalComplex _).obj K).iCycles (k + 1)
      (((G.mapHomologicalComplex _).obj K).toCycles k (k + 1) y) = G.map (K.d k (k + 1)) y :=
  ConcreteCategory.congr_hom (((G.mapHomologicalComplex _).obj K).toCycles_i k (k + 1)) y

include hP in
private lemma surjective_cyclesExtClass (n : ℕ) :
    Function.Surjective (cyclesExtClass ι hι hι' hK G R (P := P) n) := by
  intro α
  obtain ⟨f, hf, rfl⟩ := K.extMk_surjective ι hι hι' hK hP α
  -- the cocycle `f` of `Hom(P, K)` is a cycle of `G(K)`
  refine ⟨(((G.mapHomologicalComplex _).obj K).sc n).abCyclesIso.inv ⟨R.homEquiv f, ?_⟩,
    cyclesExtClass_eq_extMk ι hι hι' hK G R _ f hf (ShortComplex.abCyclesIso_inv_apply_iCycles _ _)⟩
  have hd : G.map (K.d n ((ComplexShape.up ℕ).next n)) (R.homEquiv f) = 0 := by
    rw [CochainComplex.next]
    exact (R.homEquiv_comp _ f).symm.trans (by rw [hf, R.homEquiv_zero])
  -- The differential `(sc n).g` of `G(K)` is `G(dⁿ)` on `G(Kⁿ)` by the definitions of
  -- `HomologicalComplex.sc` and `Functor.mapHomologicalComplex`. The goal states membership of
  -- `R.homEquiv f : G(Kⁿ)` in its kernel only up to this unfolding, so it is not rewritable with
  -- `HomologicalComplex.shortComplexFunctor_obj_g`, and `exact` checks the identification.
  exact AddMonoidHom.mem_ker.2 hd

include hP in
/-- A cycle of `G(K)` has zero class in `Extⁿ(P, F)` exactly when it is a boundary. -/
private lemma cyclesExtClass_eq_zero_iff (n : ℕ)
    (c : ((G.mapHomologicalComplex _).obj K).cycles n) :
    cyclesExtClass ι hι hι' hK G R n c = 0 ↔
      ((G.mapHomologicalComplex _).obj K).homologyπ n c = 0 := by
  have hi := (AddCommGrpCat.mono_iff_injective (((G.mapHomologicalComplex _).obj K).iCycles n)).1
    inferInstance
  rw [cyclesExtClass_apply]
  cases n with
  | zero =>
    have hπ := (AddCommGrpCat.mono_iff_injective
      (((G.mapHomologicalComplex _).obj K).homologyπ 0)).1 inferInstance
    simp only [extMk_zero_eq_zero_iff, Equiv.symm_apply_eq, R.homEquiv_zero,
      (injective_iff_map_eq_zero' _).1 hi, (injective_iff_map_eq_zero' _).1 hπ]
  | succ k =>
    have hex : ((G.mapHomologicalComplex _).obj K).homologyπ (k + 1) c = 0 ↔
        ∃ y, ((G.mapHomologicalComplex _).obj K).toCycles k (k + 1) y = c :=
      (ShortComplex.ab_exact_iff_function_exact (ShortComplex.mk _ _
        (((G.mapHomologicalComplex _).obj K).toCycles_comp_homologyπ k (k + 1)))).1
          (ShortComplex.exact_of_g_is_cokernel _
            (((G.mapHomologicalComplex _).obj K).homologyIsCokernel k (k + 1) (by simp))) c
    rw [K.extMk_succ_eq_zero_iff ι hι hι' hK hP, hex]
    refine ⟨fun ⟨g, hg⟩ ↦ ⟨R.homEquiv g, hi ?_⟩, fun ⟨y, hy⟩ ↦ ⟨R.homEquiv.symm y, ?_⟩⟩
    · rw [iCycles_toCycles_apply]
      exact (R.homEquiv_comp _ g).symm.trans (by rw [hg, Equiv.apply_symm_apply])
    · rw [Equiv.eq_symm_apply, R.homEquiv_comp, Equiv.apply_symm_apply, ← hy,
        iCycles_toCycles_apply]
      rfl

/-- The map `Extⁿ(P, F) →+ Hⁿ(G(K))` sending the class of a cycle to its cohomology class. -/
private noncomputable def extToHomology (n : ℕ) :
    Ext.{w} P F n →+ ((G.mapHomologicalComplex _).obj K).homology n :=
  (cyclesExtClass ι hι hι' hK G R n).liftOfSurjective
    (surjective_cyclesExtClass ι hι hι' hK hP G R n)
    ⟨(((G.mapHomologicalComplex _).obj K).homologyπ n).hom, fun c hc ↦ AddMonoidHom.mem_ker.2
      ((cyclesExtClass_eq_zero_iff ι hι hι' hK hP G R n c).1 (AddMonoidHom.mem_ker.1 hc))⟩

private lemma extToHomology_cyclesExtClass (n : ℕ)
    (c : ((G.mapHomologicalComplex _).obj K).cycles n) :
    extToHomology ι hι hι' hK hP G R n (cyclesExtClass ι hι hι' hK G R n c) =
      ((G.mapHomologicalComplex _).obj K).homologyπ n c :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c

private lemma bijective_extToHomology (n : ℕ) :
    Function.Bijective (extToHomology ι hι hι' hK hP G R n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨c, rfl⟩ := surjective_cyclesExtClass ι hι hι' hK hP G R n x
    rw [extToHomology_cyclesExtClass] at hx
    exact (cyclesExtClass_eq_zero_iff ι hι hι' hK hP G R n c).2 hx
  · obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective
      (((G.mapHomologicalComplex _).obj K).homologyπ n)).1 inferInstance y
    exact ⟨_, extToHomology_cyclesExtClass ι hι hι' hK hP G R n c⟩

/-- **`Ext` from an acyclic resolution, through a corepresentable functor.** Let `G : C ⥤ Ab` be
an additive functor corepresented by `P`, and let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be a resolution of `F`
with `Extᵏ⁺¹(P, Kʲ) = 0` for all `j` and `k`. Then `Extⁿ(P, F)` is the cohomology of the complex
`G(K)` in degree `n`. The class of a cocycle `f : P ⟶ Kⁿ` corresponds to the cohomology class of
the cycle `R.homEquiv f` (`CochainComplex.extAddEquivHomologyOfResolution_extMk`). -/
noncomputable def extAddEquivHomologyOfResolution (n : ℕ) :
    Ext.{w} P F n ≃+ ((G.mapHomologicalComplex _).obj K).homology n :=
  AddEquiv.ofBijective _ (bijective_extToHomology ι hι hι' hK hP G R n)

/-- `CochainComplex.extAddEquivHomologyOfResolution` sends the class `CochainComplex.extMk` of a
cocycle `f : P ⟶ Kⁿ` of `Hom(P, K)` to the cohomology class of the corresponding cycle of
`G(K)`. -/
lemma extAddEquivHomologyOfResolution_extMk {n : ℕ} (f : P ⟶ K.X n)
    (hf : f ≫ K.d n (n + 1) = 0) (c : ((G.mapHomologicalComplex _).obj K).cycles n)
    (hc : ((G.mapHomologicalComplex _).obj K).iCycles n c = R.homEquiv f) :
    extAddEquivHomologyOfResolution ι hι hι' hK hP G R n (K.extMk ι hι hι' hK f hf) =
      ((G.mapHomologicalComplex _).obj K).homologyπ n c := by
  rw [← cyclesExtClass_eq_extMk ι hι hι' hK G R c f hf hc, extAddEquivHomologyOfResolution,
    AddEquiv.ofBijective_apply, extToHomology_cyclesExtClass]

section Naturality

/-! ### Naturality in the corepresenting object

Let `a : P' ⟶ P`, and let `τ : G ⟶ G'` be a natural transformation to an additive functor `G'`
corepresented by `P'` which corresponds to precomposition with `a` under the corepresentations.
For the sections functors of a site, `a` is the map of free abelian sheaves induced by a morphism
`V' ⟶ V` and `τ` is the restriction of sections. -/

variable {P' : C} (hP' : ∀ j k, Subsingleton (Ext.{w} P' (K.X j) (k + 1))) (a : P' ⟶ P)
  {G' : C ⥤ AddCommGrpCat.{t}} [G'.Additive] (R' : (G' ⋙ forget AddCommGrpCat).CorepresentableBy P')
  (τ : G ⟶ G') (hτ : ∀ {X : C} (f : P ⟶ X), R'.homEquiv (a ≫ f) = τ.app X (R.homEquiv f))

include hτ in
/-- **Naturality of `Ext` from an acyclic resolution** in the corepresenting object: if
`τ : G ⟶ G'` corresponds to precomposition with `a : P' ⟶ P` under the corepresentations, then
`CochainComplex.extAddEquivHomologyOfResolution` carries precomposition with `a` on `Extⁿ(P, F)`
to the map induced by `τ` on the cohomology of `G(K) ⟶ G'(K)`. -/
theorem extAddEquivHomologyOfResolution_naturality (n : ℕ) (x : Ext.{w} P F n) :
    extAddEquivHomologyOfResolution ι hι hι' hK hP' G' R' n ((Ext.mk₀ a).comp x (zero_add n)) =
      HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex τ _).app K) n
        (extAddEquivHomologyOfResolution ι hι hι' hK hP G R n x) := by
  obtain ⟨c, rfl⟩ := surjective_cyclesExtClass ι hι hι' hK hP G R n x
  -- `c` is the cycle of the cocycle `f : P ⟶ Kⁿ`, and its image under `τ` that of `a ≫ f`
  obtain ⟨f, hc⟩ : ∃ f : P ⟶ K.X n, ((G.mapHomologicalComplex _).obj K).iCycles n c =
      R.homEquiv f := ⟨_, (R.homEquiv.apply_symm_apply _).symm⟩
  have hc' : ((G'.mapHomologicalComplex _).obj K).iCycles n
      (HomologicalComplex.cyclesMap ((NatTrans.mapHomologicalComplex τ _).app K) n c) =
        R'.homEquiv (a ≫ f) := by
    rw [hτ, ← hc]
    exact ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i ((NatTrans.mapHomologicalComplex τ _).app K) n) c
  have hf : f ≫ K.d n (n + 1) = 0 := by
    rw [← R.homEquiv.symm_apply_apply f, ← hc]
    exact homEquiv_symm_iCycles_comp_d G R n c
  rw [cyclesExtClass_eq_extMk ι hι hι' hK G R c f hf hc, mk₀_comp_extMk,
    extAddEquivHomologyOfResolution_extMk ι hι hι' hK hP' G' R' _ _ _ hc',
    extAddEquivHomologyOfResolution_extMk ι hι hι' hK hP G R f hf c hc]
  exact (ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality ((NatTrans.mapHomologicalComplex τ _).app K) n) c).symm

end Naturality

end Homology

end CochainComplex
