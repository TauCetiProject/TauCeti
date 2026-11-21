/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Normalization
public import TauCeti.AlgebraicGeometry.Fibers
public import TauCeti.AlgebraicGeometry.IntersectionNumber.FieldTower
public import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine
public import TauCeti.AlgebraicGeometry.Morphisms.RelativeDimension
public import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Numerically trivial line bundles

Let `X` be a scheme over a field `k`. A line-bundle class `a` on `X` is **numerically trivial**,
`a ≡ 0`, when its intersection number `(a · C)`, the Euler-characteristic degree over `k` of its
restriction to `C`, vanishes for every integral closed curve `C ⊆ X` that is proper over `k`
(`LineBundleClass.IsNumericallyTrivial`). The curves are the closed immersions `C ⟶ X` over `k`
from proper integral one-dimensional `k`-schemes (`AlgebraicGeometry.Scheme.IsCurveOver`), singular
ones included. No hypothesis is put on `X`: for `X` proper over `k` these are all the integral
closed curves of `X`.

For a morphism `f : X ⟶ S` the relative notion `a ≡_f 0` asks that for every point `s` of `S` the
pullback of `a` to the scheme-theoretic fibre `X_s` be numerically trivial over the residue field
`κ(s)` (`LineBundleClass.IsRelNumericallyTrivial`), so that the degree of a curve in a fibre is
taken over the residue field of its image point. This definition puts no hypothesis on `S` either.

The numerically trivial classes form the subgroups `Pic^τ(X/k)` and `Pic^τ(X/S)` of the Picard
group, the kernels of the curve pairings, whose quotients are the numerical groups `Num(X/k)` and
`Num(X/S)`.

## Main definitions

* `LineBundleClass.IsNumericallyTrivial k a`: `a` has degree zero on every integral closed curve
  of `X` proper over `k`.
* `LineBundleClass.numericallyTrivialClasses k X`: the subgroup `Pic^τ(X/k)` of numerically trivial
  classes.
* `LineBundleClass.IsRelNumericallyTrivial f a`: `a ≡_f 0`, numerical triviality on every
  scheme-theoretic fibre of `f`.
* `LineBundleClass.relNumericallyTrivialClasses f`: the subgroup `Pic^τ(X/S)`.

## Main results

* `LineBundleClass.IsNumericallyTrivial.pullback_of_isClosedImmersion`: restriction to a closed
  subscheme preserves numerical triviality, and pullback along an isomorphism over `k` reflects it
  (`LineBundleClass.isNumericallyTrivial_pullback_iff_of_isIso`).
* `LineBundleClass.IsNumericallyTrivial.restrictScalars` and
  `LineBundleClass.isNumericallyTrivial_iff_of_finiteDimensional`: for a field extension `K / k`
  and a scheme over `K`, numerical triviality over `K` implies numerical triviality over `k`, and
  the two agree when `K / k` is finite, because restriction of scalars multiplies degrees by
  `[K : k]`.
* `LineBundleClass.IsNumericallyTrivial.eulerDegree_eq_zero`: a numerically trivial class on a
  curve has degree zero; on the projective line the numerically trivial classes are trivial
  (`TauCeti.AlgebraicGeometry.projectiveLine.numericallyTrivialClasses_eq_bot`), so `𝒪(m) ≡ 0`
  only for `m = 0`.
* `LineBundleClass.isRelNumericallyTrivial_pullback`: every class `f^* N` pulled back from the base
  is relatively numerically trivial; in particular every class is numerically trivial relative to
  the identity.
* `LineBundleClass.IsRelNumericallyTrivial.pullback_of_isClosedImmersion`: for a closed immersion
  `g : Z ⟶ X`, `a ≡_f 0` implies `g^* a ≡_{g ≫ f} 0`.
* `LineBundleClass.isRelNumericallyTrivial_iff_isNumericallyTrivial`: relative to the structure
  morphism `X ⟶ Spec k`, relative numerical triviality is numerical triviality over `k`, through
  the identification of `X` with its fibre over the point of `Spec k`.

## References

* S. L. Kleiman, *The Picard scheme*, in *Fundamental algebraic geometry*, Mathematical Surveys and
  Monographs 123, AMS, 2005, Definition 6.1 and Section 6.
* B. Bhatt et al., *Globally +-regular varieties and the minimal model program for threefolds in
  mixed characteristic*, Publ. Math. IHÉS 138 (2023), Section 2.5 and Remark 2.22.
* R. Lazarsfeld, *Positivity in algebraic geometry I*, Ergebnisse der Mathematik 48, Springer,
  2004, Section 1.1.C.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open Module (finrank)

universe u

namespace TauCeti.AlgebraicGeometry

namespace LineBundleClass

section Absolute

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))]

/-- A line-bundle class `a` on a scheme `X` over a field `k` is **numerically trivial** when its
intersection number over `k` with every integral closed curve of `X` proper over `k` is zero: for
every proper integral one-dimensional `k`-scheme `C` and every closed immersion `ι : C ⟶ X` over
`k`, the degree `(a · C) = deg_k (ι^* a)` vanishes. Singular curves are included. -/
def IsNumericallyTrivial (a : LineBundleClass X) : Prop :=
  ∀ (C : Scheme.{u}) [C.Over (Spec (.of k))] [C.IsCurveOver k] (ι : C ⟶ X) [IsClosedImmersion ι]
    [ι.IsOver (Spec (.of k))], intersectionNumber k ι a = 0

/-- A class is numerically trivial exactly when its intersection number with every integral closed
curve proper over `k` vanishes. -/
theorem isNumericallyTrivial_iff (a : LineBundleClass X) :
    a.IsNumericallyTrivial k ↔
      ∀ (C : Scheme.{u}) [C.Over (Spec (.of k))] [C.IsCurveOver k] (ι : C ⟶ X)
        [IsClosedImmersion ι] [ι.IsOver (Spec (.of k))], intersectionNumber k ι a = 0 :=
  Iff.rfl

variable {k} in
/-- A numerically trivial class has intersection number zero with every integral closed curve
proper over `k`. -/
theorem IsNumericallyTrivial.intersectionNumber_eq_zero {a : LineBundleClass X}
    (h : a.IsNumericallyTrivial k) (C : Scheme.{u}) [C.Over (Spec (.of k))] [C.IsCurveOver k]
    (ι : C ⟶ X) [IsClosedImmersion ι] [ι.IsOver (Spec (.of k))] :
    intersectionNumber k ι a = 0 :=
  h C ι

/-- The trivial class is numerically trivial. -/
@[simp]
theorem isNumericallyTrivial_one : (1 : LineBundleClass X).IsNumericallyTrivial k :=
  fun _ _ _ ι _ _ ↦ intersectionNumber_one k ι

variable {k}

/-- A product of numerically trivial classes is numerically trivial. -/
theorem IsNumericallyTrivial.mul {a b : LineBundleClass X} (ha : a.IsNumericallyTrivial k)
    (hb : b.IsNumericallyTrivial k) : (a * b).IsNumericallyTrivial k := by
  intro C _ _ ι _ _
  rw [intersectionNumber_mul_of_isIntegral, ha C ι, hb C ι, add_zero]

/-- The inverse of a numerically trivial class is numerically trivial. -/
theorem IsNumericallyTrivial.inv {a : LineBundleClass X} (ha : a.IsNumericallyTrivial k) :
    a⁻¹.IsNumericallyTrivial k := by
  intro C _ _ ι _ _
  rw [intersectionNumber_inv_of_isIntegral, ha C ι, neg_zero]

/-- A class is numerically trivial exactly when its inverse is. -/
@[simp]
theorem isNumericallyTrivial_inv_iff {a : LineBundleClass X} :
    a⁻¹.IsNumericallyTrivial k ↔ a.IsNumericallyTrivial k :=
  ⟨fun h ↦ inv_inv a ▸ h.inv, IsNumericallyTrivial.inv⟩

variable (k X) in
/-- The subgroup `Pic^τ(X/k)` of numerically trivial line-bundle classes on a scheme `X` over a
field `k`. The quotient by it is the numerical group `Num(X/k)`. -/
def numericallyTrivialClasses : Subgroup (LineBundleClass X) where
  carrier := {a | a.IsNumericallyTrivial k}
  mul_mem' := IsNumericallyTrivial.mul
  one_mem' := isNumericallyTrivial_one k
  inv_mem' := IsNumericallyTrivial.inv

/-- Membership in `Pic^τ(X/k)` is numerical triviality. -/
@[simp]
theorem mem_numericallyTrivialClasses {a : LineBundleClass X} :
    a ∈ numericallyTrivialClasses k X ↔ a.IsNumericallyTrivial k :=
  Iff.rfl

/-- **Restriction to a closed subscheme.** The pullback of a numerically trivial class along a
closed immersion over `k` is numerically trivial: a curve in the subscheme is a curve in `X`. -/
theorem IsNumericallyTrivial.pullback_of_isClosedImmersion {a : LineBundleClass X}
    (h : a.IsNumericallyTrivial k) (g : Y ⟶ X) [IsClosedImmersion g] [g.IsOver (Spec (.of k))] :
    (pullback g a).IsNumericallyTrivial k := by
  intro C _ _ ι _ _
  rw [intersectionNumber_pullback]
  exact h C (ι ≫ g)

/-- Numerical triviality is invariant under isomorphisms over `k`. -/
@[simp]
theorem isNumericallyTrivial_pullback_iff_of_isIso (g : Y ⟶ X) [IsIso g]
    [g.IsOver (Spec (.of k))] {a : LineBundleClass X} :
    (pullback g a).IsNumericallyTrivial k ↔ a.IsNumericallyTrivial k := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.pullback_of_isClosedImmersion g⟩
  simpa using h.pullback_of_isClosedImmersion (asIso g).inv

/-- A numerically trivial class on a curve over `k` has degree zero, the curve being an integral
closed curve in itself. -/
theorem IsNumericallyTrivial.eulerDegree_eq_zero [X.IsCurveOver k] {a : LineBundleClass X}
    (h : a.IsNumericallyTrivial k) : eulerDegree k a = 0 := by
  simpa [intersectionNumber_def] using h X (𝟙 X)

end Absolute

section RestrictScalars

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.Over (Spec (.of K))]

/-- **Restriction of scalars.** Let `K / k` be a field extension and `X` a scheme over `K`,
regarded as a scheme over `k` through `Spec K ⟶ Spec k`. A class numerically trivial over `K` is
numerically trivial over `k`: every integral closed curve of `X` proper over `k` is proper over
`K`, and its degree over `k` is `[K : k]` times its degree over `K`. -/
theorem IsNumericallyTrivial.restrictScalars
    (hX : (X ↘ Spec (.of K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      X ↘ Spec (.of k)) {a : LineBundleClass X} (h : a.IsNumericallyTrivial K) :
    a.IsNumericallyTrivial k := by
  intro C _ _ ι _ _
  let : C.Over (Spec (.of K)) := ⟨ι ≫ X ↘ Spec (.of K)⟩
  have : ι.IsOver (Spec (.of K)) := ⟨rfl⟩
  have hC : (C ↘ Spec (.of K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      C ↘ Spec (.of k) := by
    rw [← comp_over ι (Spec (.of K)), Category.assoc, hX, comp_over]
  have : IsProper ((C ↘ Spec (.of K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [hC]; infer_instance
  have : IsProper (C ↘ Spec (.of K)) := .of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : C.IsCurveOver K := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, Scheme.IsCurveOver.topologicalKrullDim_eq_one k⟩
  rw [intersectionNumber_eq_finrank_mul ι hC, h C ι, mul_zero]

/-- **Numerical triviality along a finite extension.** Let `K / k` be a finite field extension and
`X` a scheme over `K`, regarded as a scheme over `k`. A class on `X` is numerically trivial over
`k` exactly when it is numerically trivial over `K`: the integral closed curves proper over `k`
and over `K` are the same, and their degrees over `k` are `[K : k] ≠ 0` times their degrees over
`K`. -/
theorem isNumericallyTrivial_iff_of_finiteDimensional [FiniteDimensional k K]
    (hX : (X ↘ Spec (.of K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      X ↘ Spec (.of k)) {a : LineBundleClass X} :
    a.IsNumericallyTrivial k ↔ a.IsNumericallyTrivial K := by
  refine ⟨fun h C _ _ ι _ _ ↦ ?_, IsNumericallyTrivial.restrictScalars K hX⟩
  let : C.Over (Spec (.of k)) :=
    ⟨(C ↘ Spec (.of K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))⟩
  have : ι.IsOver (Spec (.of k)) :=
    ⟨by rw [← hX, ← Category.assoc, comp_over]; rfl⟩
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : IsProper (C ↘ Spec (.of k)) :=
    inferInstanceAs (IsProper ((C ↘ Spec (.of K)) ≫ Spec.map _))
  have : C.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, Scheme.IsCurveOver.topologicalKrullDim_eq_one K⟩
  have h₀ := h C ι
  rw [intersectionNumber_eq_finrank_mul ι rfl] at h₀
  exact (mul_eq_zero.mp h₀).resolve_left (by exact_mod_cast Module.finrank_pos.ne')

end RestrictScalars

section Relative

variable {X Y S : Scheme.{u}}

/-- The scheme-theoretic fibre `X_s` of `f : X ⟶ S` is a scheme over `κ(s)` through
`f.fiberToSpecResidueField s`. This is `Scheme.Hom.fiberOverSpecResidueField` with the base
written as `Spec (.of κ(s))`, the form numerical triviality over `κ(s)` takes. -/
noncomputable local instance (f : X ⟶ S) (s : S) :
    (f.fiber s).Over (Spec (.of (S.residueField s))) :=
  f.fiberOverSpecResidueField s

/-- **Relative numerical triviality** `a ≡_f 0` for a morphism `f : X ⟶ S`: for every point `s`
of `S`, the pullback of `a` to the scheme-theoretic fibre `X_s` is numerically trivial over the
residue field `κ(s)`, the fibre being a scheme over `κ(s)` through
`f.fiberToSpecResidueField s`. Degrees of curves in `X_s` are taken over `κ(s)`. -/
def IsRelNumericallyTrivial (f : X ⟶ S) (a : LineBundleClass X) : Prop :=
  ∀ s : S, (pullback (f.fiberι s) a).IsNumericallyTrivial (S.residueField s)

/-- A class is relatively numerically trivial for `f` exactly when its pullback to every
scheme-theoretic fibre `X_s` is numerically trivial over `κ(s)`. -/
theorem isRelNumericallyTrivial_iff (f : X ⟶ S) (a : LineBundleClass X) :
    IsRelNumericallyTrivial f a ↔
      ∀ s : S, (pullback (f.fiberι s) a).IsNumericallyTrivial (S.residueField s) :=
  Iff.rfl

/-- The trivial class is relatively numerically trivial. -/
@[simp]
theorem isRelNumericallyTrivial_one (f : X ⟶ S) : IsRelNumericallyTrivial f 1 := by
  intro s
  rw [pullback_one]
  exact isNumericallyTrivial_one _

variable {f : X ⟶ S}

/-- A product of relatively numerically trivial classes is relatively numerically trivial. -/
theorem IsRelNumericallyTrivial.mul {a b : LineBundleClass X} (ha : IsRelNumericallyTrivial f a)
    (hb : IsRelNumericallyTrivial f b) : IsRelNumericallyTrivial f (a * b) := by
  intro s
  rw [pullback_mul]
  exact (ha s).mul (hb s)

/-- The inverse of a relatively numerically trivial class is relatively numerically trivial. -/
theorem IsRelNumericallyTrivial.inv {a : LineBundleClass X} (ha : IsRelNumericallyTrivial f a) :
    IsRelNumericallyTrivial f a⁻¹ := by
  intro s
  rw [pullback_inv]
  exact (ha s).inv

/-- A class is relatively numerically trivial exactly when its inverse is. -/
@[simp]
theorem isRelNumericallyTrivial_inv_iff {a : LineBundleClass X} :
    IsRelNumericallyTrivial f a⁻¹ ↔ IsRelNumericallyTrivial f a :=
  ⟨fun h ↦ inv_inv a ▸ h.inv, IsRelNumericallyTrivial.inv⟩

variable (f) in
/-- The subgroup `Pic^τ(X/S)` of relatively numerically trivial line-bundle classes for a morphism
`f : X ⟶ S`. The quotient by it is the relative numerical group `Num(X/S)`. -/
def relNumericallyTrivialClasses : Subgroup (LineBundleClass X) where
  carrier := {a | IsRelNumericallyTrivial f a}
  mul_mem' := IsRelNumericallyTrivial.mul
  one_mem' := isRelNumericallyTrivial_one f
  inv_mem' := IsRelNumericallyTrivial.inv

/-- Membership in `Pic^τ(X/S)` is relative numerical triviality. -/
@[simp]
theorem mem_relNumericallyTrivialClasses {a : LineBundleClass X} :
    a ∈ relNumericallyTrivialClasses f ↔ IsRelNumericallyTrivial f a :=
  Iff.rfl

variable (f) in
/-- **Classes from the base are relatively numerically trivial.** For `f : X ⟶ S` and every class
`b` on `S`, `f^* b ≡_f 0`: on the fibre `X_s` the class `f^* b` is pulled back from `Spec κ(s)`,
whose Picard group is trivial. -/
@[simp]
theorem isRelNumericallyTrivial_pullback (b : LineBundleClass S) :
    IsRelNumericallyTrivial f (pullback f b) := by
  intro s
  rw [pullback_comp, Scheme.Hom.fiber_fac, ← pullback_comp,
    Subsingleton.elim (pullback (S.fromSpecResidueField s) b) 1, pullback_one]
  exact isNumericallyTrivial_one _

/-- Every class is numerically trivial relative to the identity, whose fibres are points. -/
theorem isRelNumericallyTrivial_id (a : LineBundleClass X) : IsRelNumericallyTrivial (𝟙 X) a := by
  simpa using isRelNumericallyTrivial_pullback (𝟙 X) a

/-- **Restriction to a closed subscheme.** For a closed immersion `g : Z ⟶ X`, if `a ≡_f 0` then
`g^* a ≡_{g ≫ f} 0`: the fibre `Z_s` is a closed subscheme of `X_s` over `κ(s)`. -/
theorem IsRelNumericallyTrivial.pullback_of_isClosedImmersion {a : LineBundleClass X}
    (h : IsRelNumericallyTrivial f a) (g : Y ⟶ X) [IsClosedImmersion g] :
    IsRelNumericallyTrivial (g ≫ f) (pullback g a) := by
  intro s
  have hf := h s
  -- The fibre of `g ≫ f` maps to the fibre of `f` over `κ(s)`, as the base change of `g`.
  let j : (g ≫ f).fiber s ⟶ f.fiber s :=
    (f.isPullback_fiberι s).lift ((g ≫ f).fiberι s ≫ g) ((g ≫ f).fiberToSpecResidueField s)
      (by rw [Category.assoc, Scheme.Hom.fiber_fac])
  have hjι : j ≫ f.fiberι s = (g ≫ f).fiberι s ≫ g := IsPullback.lift_fst _ _ _ _
  have hjs : j ≫ f.fiberToSpecResidueField s = (g ≫ f).fiberToSpecResidueField s :=
    IsPullback.lift_snd _ _ _ _
  have hpb : IsPullback j ((g ≫ f).fiberι s) (f.fiberι s) g :=
    IsPullback.of_right (by rw [hjs]; exact ((g ≫ f).isPullback_fiberι s).flip) hjι
      (f.isPullback_fiberι s).flip
  have : IsClosedImmersion j := MorphismProperty.of_isPullback hpb.flip ‹_›
  have : j.IsOver (Spec (.of (S.residueField s))) := ⟨hjs⟩
  rw [pullback_comp, ← hjι, ← pullback_comp]
  exact hf.pullback_of_isClosedImmersion j

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- **Comparison with the absolute notion.** Relative to the structure morphism `X ⟶ Spec k`, a
class is relatively numerically trivial exactly when it is numerically trivial over `k`: the
fibre of `X` over the unique point `s` of `Spec k` is `X` itself, and `κ(s) = k`. -/
theorem isRelNumericallyTrivial_iff_isNumericallyTrivial (a : LineBundleClass X) :
    IsRelNumericallyTrivial (X ↘ Spec (.of k)) a ↔ a.IsNumericallyTrivial k := by
  have key (s : Spec (.of k)) :
      (pullback ((X ↘ Spec (.of k)).fiberι s) a).IsNumericallyTrivial
        ((Spec (.of k)).residueField s) ↔ a.IsNumericallyTrivial k := by
    let e := (Spec (.of k)).fromSpecResidueField s
    -- The structure of `κ(s)` as a `k`-algebra, under which `Spec κ(s) ⟶ Spec k` is `e`.
    let : Algebra k ((Spec (.of k)).residueField s) := (Spec.preimage e).hom.toAlgebra
    have he : Spec.map (CommRingCat.ofHom (algebraMap k ((Spec (.of k)).residueField s))) = e :=
      Spec.map_preimage e
    have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k ((Spec (.of k)).residueField s)))) := by
      rw [he]; infer_instance
    have hbij : Function.Bijective (algebraMap k ((Spec (.of k)).residueField s)) :=
      isIso_SpecMap_iff.mp this
    have : FiniteDimensional k ((Spec (.of k)).residueField s) :=
      .of_surjective (Algebra.linearMap k _) hbij.surjective
    let : ((X ↘ Spec (.of k)).fiber s).Over (Spec (.of k)) :=
      ⟨(X ↘ Spec (.of k)).fiberToSpecResidueField s ≫ e⟩
    have : ((X ↘ Spec (.of k)).fiberι s).IsOver (Spec (.of k)) :=
      ⟨Scheme.Hom.fiber_fac _ s⟩
    have : IsIso ((X ↘ Spec (.of k)).fiberι s) :=
      ((X ↘ Spec (.of k)).isPullback_fiberι s).isIso_fst_of_isIso
    rw [← isNumericallyTrivial_iff_of_finiteDimensional (X := (X ↘ Spec (.of k)).fiber s) _
        (by rw [he]; rfl),
      isNumericallyTrivial_pullback_iff_of_isIso]
  obtain ⟨s⟩ : Nonempty (Spec (.of k)) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  exact ⟨fun h ↦ (key s).mp (h s), fun h t ↦ (key t).mpr h⟩

end Relative

end LineBundleClass

namespace projectiveLine

variable (k : Type u) [Field k]

/-- **Numerical triviality on the projective line.** A line-bundle class on `ℙ¹_k` is numerically
trivial only if it is trivial: its degree vanishes, and degree identifies `Pic(ℙ¹_k)` with `ℤ`.
Thus `𝒪(m)` is numerically trivial exactly for `m = 0`. -/
@[simp]
theorem numericallyTrivialClasses_eq_bot :
    LineBundleClass.numericallyTrivialClasses k (projectiveLine k) = ⊥ := by
  refine eq_bot_iff.mpr fun a ha ↦ Subgroup.mem_bot.mpr ?_
  have h := (picardDegreeEquiv k).injective.eq_iff (a := Additive.ofMul a) (b := 0)
  simp only [picardDegreeEquiv_apply, toMul_ofMul, map_zero, ofMul_eq_zero] at h
  exact h.mp ((LineBundleClass.mem_numericallyTrivialClasses.mp ha).eulerDegree_eq_zero)

end projectiveLine

end TauCeti.AlgebraicGeometry
