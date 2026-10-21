/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Category.GradedModuleCat.Projective
public import TauCeti.Algebra.DirectSum.Exact
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.ForgetGrading.Basic
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.ForgetGrading.ExtZero

/-!
# The natural comparison of graded and ungraded Ext

Let `A` be a graded algebra over a field `k` and let `U` be the functor forgetting the grading of
graded `A`-modules. Since `U` is exact and `U(Y{j})` is the underlying module of `Y`, every class
in `Extⁿ(X, Y{j})` gives a class in `Extⁿ(U X, U Y)`. Summing over the internal degrees gives a
`k`-linear map

```text
⨁ j, Extⁿ(X, Y{j}) → Extⁿ(U X, U Y),
```

`TauCeti.GradedModuleCat.gradedExtForget`. It is natural in both variables and commutes with the
connecting maps of the long exact `Ext` sequences in both variables. In degree zero, when `𝒜` is
a grading of `A` and `X` is finitely generated, it is the decomposition of an ungraded module map
into its homogeneous parts, `TauCeti.GradedModuleCat.gradedExtZeroForgetEquiv`.

If `A` is left Noetherian and `X` is finitely generated, the map is bijective in every degree.
The proof shifts dimension along a finite graded free presentation `0 → K → F → X → 0`, whose
kernel is again finitely generated, using the five lemma on the two contravariant long exact
`Ext` sequences. The resulting isomorphisms make `(U X, U Y)` a comparison pair in the sense of
`TauCeti.IsGradedExtComparison`. For such a pair that is moreover graded Euler-admissible
(`TauCeti.IsGradedEulerAdmissible`), the q-Euler characteristic therefore specializes at `q = 1`
to the ordinary Ext-Euler characteristic.

## Main definitions

* `TauCeti.GradedModuleCat.gradedExtForgetComponent`: the map `Extⁿ(X, Y{j}) → Extⁿ(U X, U Y)`
  in a single internal degree.
* `TauCeti.GradedModuleCat.gradedExtForget`: their sum over all internal degrees.
* `TauCeti.GradedModuleCat.gradedExtForgetEquiv`: the comparison as a linear equivalence, for a
  finitely generated source over a left Noetherian graded algebra.

## Main results

* `TauCeti.GradedModuleCat.gradedExtForgetComponent_extClass_comp` and
  `TauCeti.GradedModuleCat.gradedExtForgetComponent_comp_extClass`: compatibility with the
  connecting maps in the source and in the target.
* `TauCeti.GradedModuleCat.gradedExtForget_comp_lmap_precomp_mk₀`,
  `TauCeti.GradedModuleCat.gradedExtForget_comp_lmap_postcomp_mk₀`,
  `TauCeti.GradedModuleCat.gradedExtForget_comp_lmap_precomp_extClass` and
  `TauCeti.GradedModuleCat.gradedExtForget_comp_lmap_postcomp_extClass`: the same naturality and
  connecting-map compatibilities for the whole direct-sum comparison.
* `TauCeti.GradedModuleCat.gradedExtForget_zero`: in degree zero the comparison is the
  homogeneous decomposition of module maps.
* `TauCeti.GradedModuleCat.gradedExtForget_bijective`: the comparison is bijective for a finitely
  generated source over a left Noetherian graded algebra.
* `TauCeti.GradedModuleCat.isGradedExtComparison_toModuleCat`: such a pair of graded modules is a
  graded `Ext` comparison pair with its underlying modules.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Lecture Notes in Mathematics
  1836, Springer (2004), Section 2.4, for graded `Hom` and `Ext` of a finitely generated module
  over a Noetherian graded ring and their agreement with the ungraded groups.
* The dimension-shifting proof of `TauCeti.GradedModuleCat.gradedExtForget_bijective` follows
  Mathlib's `CategoryTheory.Functor.mapExt_bijective_of_preservesProjectiveObjects`
  (`Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective`), adapted from a single fully
  faithful functor to a direct sum over internal degrees, and from an arbitrary projective
  presentation to a finite graded free one so that the kernel stays finitely generated.
-/

public section

noncomputable section

open scoped DirectSum

namespace TauCeti.GradedModuleCat

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w w' uk uA

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A)

variable [HasExt.{w} (GradedModuleCat.{uA} 𝒜)] [HasExt.{w'} (ModuleCat.{uA} A)]

/-- The map from graded `Ext` in a single internal degree `j` to ungraded `Ext`: forget the
grading of a class in `Extⁿ(X, Y{j})` and identify the underlying module of `Y{j}` with that
of `Y`. -/
def gradedExtForgetComponent (X Y : GradedModuleCat.{uA} 𝒜) (n : ℕ) (j : ℤ) :
    GradedExt.{w} (shift 𝒜) X Y n j →ₗ[k]
      Ext.{w'} (toModuleCat.obj X) (toModuleCat.obj Y) n :=
  (Ext.mk₀ ((shiftPowCompToModuleCatIso 𝒜 j).hom.app Y)).postcompOfLinear k _ (add_zero n) ∘ₗ
    toModuleCat.mapExtLinearMap k X _ n

/-- The value of `gradedExtForgetComponent`: apply the forgetful functor, then compose with the
identification of `U(Y{j})` with `U Y`. -/
theorem gradedExtForgetComponent_apply (X Y : GradedModuleCat.{uA} 𝒜) (n : ℕ) (j : ℤ)
    (x : GradedExt.{w} (shift 𝒜) X Y n j) :
    gradedExtForgetComponent 𝒜 X Y n j x =
      (x.mapExactFunctor toModuleCat).comp
        (Ext.mk₀ ((shiftPowCompToModuleCatIso 𝒜 j).hom.app Y)) (add_zero n) := by
  simp [gradedExtForgetComponent, Functor.mapExtLinearMap_apply]

/-- **The natural comparison of graded and ungraded `Ext`.** The sum over all internal degrees
`j` of the maps `Extⁿ(X, Y{j}) → Extⁿ(X, Y)` forgetting the grading. -/
def gradedExtForget (X Y : GradedModuleCat.{uA} 𝒜) (n : ℕ) :
    (⨁ j : ℤ, GradedExt.{w} (shift 𝒜) X Y n j) →ₗ[k]
      Ext.{w'} (toModuleCat.obj X) (toModuleCat.obj Y) n :=
  DirectSum.toModule k ℤ _ (gradedExtForgetComponent 𝒜 X Y n)

/-- On a single internal degree, `gradedExtForget` is `gradedExtForgetComponent`. -/
@[simp]
theorem gradedExtForget_of (X Y : GradedModuleCat.{uA} 𝒜) (n : ℕ) (j : ℤ)
    (x : GradedExt.{w} (shift 𝒜) X Y n j) :
    gradedExtForget 𝒜 X Y n (DirectSum.of (GradedExt.{w} (shift 𝒜) X Y n) j x) =
      (x.mapExactFunctor toModuleCat).comp
        (Ext.mk₀ ((shiftPowCompToModuleCatIso 𝒜 j).hom.app Y)) (add_zero n) :=
  (DirectSum.toModule_lof k j x).trans (gradedExtForgetComponent_apply 𝒜 X Y n j x)

variable {𝒜}

/-! ### Naturality and connecting maps -/

/-- The comparison is natural in the source. -/
theorem gradedExtForgetComponent_mk₀_comp {X' X Y : GradedModuleCat.{uA} 𝒜} (f : X' ⟶ X)
    {n : ℕ} {j : ℤ} (x : GradedExt.{w} (shift 𝒜) X Y n j) :
    gradedExtForgetComponent 𝒜 X' Y n j ((Ext.mk₀ f).comp x (zero_add n)) =
      (Ext.mk₀ (toModuleCat.map f)).comp (gradedExtForgetComponent 𝒜 X Y n j x)
        (zero_add n) := by
  simp only [gradedExtForgetComponent_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact Ext.comp_assoc_of_third_deg_zero _ _ _ _

/-- The comparison is natural in the target. -/
theorem gradedExtForgetComponent_comp_mk₀ {X Y Y' : GradedModuleCat.{uA} 𝒜} (g : Y ⟶ Y')
    {n : ℕ} {j : ℤ} (x : GradedExt.{w} (shift 𝒜) X Y n j) :
    gradedExtForgetComponent 𝒜 X Y' n j
        (x.comp (Ext.mk₀ (((shift 𝒜) ^ j).functor.map g)) (add_zero n)) =
      (gradedExtForgetComponent 𝒜 X Y n j x).comp (Ext.mk₀ (toModuleCat.map g))
        (add_zero n) := by
  simp only [gradedExtForgetComponent_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  congr 2
  exact (shiftPowCompToModuleCatIso 𝒜 j).hom.naturality g

/-- **The comparison commutes with the connecting maps in the source.** For a short exact
sequence `0 → S₁ → S₂ → S₃ → 0` of graded modules, the connecting map
`Extⁿ(S₁, Y{j}) → Extⁿ⁺¹(S₃, Y{j})` corresponds to the connecting map of the underlying short
exact sequence of modules. -/
theorem gradedExtForgetComponent_extClass_comp {S : ShortComplex (GradedModuleCat.{uA} 𝒜)}
    (hS : S.ShortExact) (Y : GradedModuleCat.{uA} 𝒜) {n m : ℕ} (h : 1 + n = m) {j : ℤ}
    (x : GradedExt.{w} (shift 𝒜) S.X₁ Y n j) :
    gradedExtForgetComponent 𝒜 S.X₃ Y m j (hS.extClass.comp x h) =
      (hS.map_of_exact toModuleCat).extClass.comp (gradedExtForgetComponent 𝒜 S.X₁ Y n j x)
        h := by
  simp only [gradedExtForgetComponent_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  exact Ext.comp_assoc_of_third_deg_zero _ _ _ _

/-- **The comparison commutes with the connecting maps in the target.** For a short exact
sequence `0 → S₁ → S₂ → S₃ → 0` of graded modules, the connecting map
`Extⁿ(X, S₃{j}) → Extⁿ⁺¹(X, S₁{j})` of the shifted sequence corresponds to the connecting map of
the underlying short exact sequence of modules. -/
theorem gradedExtForgetComponent_comp_extClass {S : ShortComplex (GradedModuleCat.{uA} 𝒜)}
    (hS : S.ShortExact) (X : GradedModuleCat.{uA} 𝒜) {n m : ℕ} (h : n + 1 = m) {j : ℤ}
    (x : GradedExt.{w} (shift 𝒜) X S.X₃ n j) :
    gradedExtForgetComponent 𝒜 X S.X₁ m j
        (x.comp (hS.map_of_exact ((shift 𝒜) ^ j).functor).extClass h) =
      (gradedExtForgetComponent 𝒜 X S.X₃ n j x).comp (hS.map_of_exact toModuleCat).extClass
        h := by
  simp only [gradedExtForgetComponent_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass, Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_second_deg_zero]
  congr 1
  exact ShortComplex.ShortExact.extClass_naturality _ _
    (S.mapNatTrans (shiftPowCompToModuleCatIso 𝒜 j).hom)

/-! ### Bijectivity -/

/-- In cohomological degree zero the comparison is the homogeneous decomposition of ungraded
module maps. -/
theorem gradedExtForget_zero (X Y : GradedModuleCat.{uA} 𝒜) [GradedAlgebra 𝒜]
    [Module.Finite A X] :
    gradedExtForget 𝒜 X Y 0 = (gradedExtZeroForgetEquiv 𝒜 X Y).toLinearMap := by
  classical
  refine DirectSum.linearMap_ext k fun j ↦ LinearMap.ext fun x ↦ ?_
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X (((shift 𝒜) ^ j).functor.obj Y)).2 x
  have hf : Ext.linearEquiv₀ (R := k) (Ext.mk₀ f) = f :=
    (Ext.linearEquiv₀ (R := k)).apply_symm_apply f
  simp only [DirectSum.lof_eq_of, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    gradedExtZeroForgetEquiv_of, gradedExtForget_of, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀,
    hf, homShiftPowEquiv_apply]
  congr 1
  ext y
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, shiftPowCompToModuleCatIso_hom_app_hom]
  -- Both sides apply `((shiftPowIso 𝒜 j).hom.app Y).hom` after `f.hom`; the right side is a
  -- composite in `ModuleCat` whose middle object carries the shifted module's instances, which
  -- `ModuleCat.hom_comp` cannot match syntactically.
  rfl

/-- The comparison commutes with precomposition by a graded map, on the whole direct sum. -/
theorem gradedExtForget_comp_lmap_precomp_mk₀ {X' X Y : GradedModuleCat.{uA} 𝒜} (f : X' ⟶ X)
    (n : ℕ) :
    gradedExtForget 𝒜 X' Y n ∘ₗ
        DirectSum.lmap (fun j ↦ (Ext.mk₀ f).precompOfLinear k
          (((shift 𝒜) ^ j).functor.obj Y) (zero_add n)) =
      (Ext.mk₀ (toModuleCat.map f)).precompOfLinear k _ (zero_add n) ∘ₗ
        gradedExtForget 𝒜 X Y n := by
  classical
  refine DirectSum.linearMap_ext k fun j ↦ LinearMap.ext fun x ↦ ?_
  simp [DirectSum.lof_eq_of, gradedExtForget_of, ← gradedExtForgetComponent_apply,
    gradedExtForgetComponent_mk₀_comp]

/-- The comparison commutes with postcomposition by a graded map, on the whole direct sum. -/
theorem gradedExtForget_comp_lmap_postcomp_mk₀ {X Y Y' : GradedModuleCat.{uA} 𝒜} (g : Y ⟶ Y')
    (n : ℕ) :
    gradedExtForget 𝒜 X Y' n ∘ₗ
        DirectSum.lmap (fun j ↦ (Ext.mk₀ (((shift 𝒜) ^ j).functor.map g)).postcompOfLinear k
          X (add_zero n)) =
      (Ext.mk₀ (toModuleCat.map g)).postcompOfLinear k _ (add_zero n) ∘ₗ
        gradedExtForget 𝒜 X Y n := by
  classical
  refine DirectSum.linearMap_ext k fun j ↦ LinearMap.ext fun x ↦ ?_
  simp [DirectSum.lof_eq_of, gradedExtForget_of, ← gradedExtForgetComponent_apply,
    gradedExtForgetComponent_comp_mk₀]

/-- The comparison commutes with the connecting maps in the source, on the whole direct sum. -/
theorem gradedExtForget_comp_lmap_precomp_extClass {S : ShortComplex (GradedModuleCat.{uA} 𝒜)}
    (hS : S.ShortExact) (Y : GradedModuleCat.{uA} 𝒜) (n : ℕ) :
    gradedExtForget 𝒜 S.X₃ Y (n + 1) ∘ₗ
        DirectSum.lmap (fun j ↦ hS.extClass.precompOfLinear k
          (((shift 𝒜) ^ j).functor.obj Y) (add_comm 1 n)) =
      (hS.map_of_exact toModuleCat).extClass.precompOfLinear k _ (add_comm 1 n) ∘ₗ
        gradedExtForget 𝒜 S.X₁ Y n := by
  classical
  refine DirectSum.linearMap_ext k fun j ↦ LinearMap.ext fun x ↦ ?_
  simp [DirectSum.lof_eq_of, gradedExtForget_of, ← gradedExtForgetComponent_apply,
    gradedExtForgetComponent_extClass_comp]

/-- The comparison commutes with the connecting maps in the target, on the whole direct sum. -/
theorem gradedExtForget_comp_lmap_postcomp_extClass {S : ShortComplex (GradedModuleCat.{uA} 𝒜)}
    (hS : S.ShortExact) (X : GradedModuleCat.{uA} 𝒜) (n : ℕ) :
    gradedExtForget 𝒜 X S.X₁ (n + 1) ∘ₗ
        DirectSum.lmap (M := GradedExt.{w} (shift 𝒜) X S.X₃ n)
          (N := GradedExt.{w} (shift 𝒜) X S.X₁ (n + 1))
          (fun j ↦ (hS.map_of_exact ((shift 𝒜) ^ j).functor).extClass.postcompOfLinear k X rfl) =
      (hS.map_of_exact toModuleCat).extClass.postcompOfLinear k _ rfl ∘ₗ
        gradedExtForget 𝒜 X S.X₃ n := by
  classical
  refine DirectSum.linearMap_ext k fun j ↦ LinearMap.ext fun x ↦ ?_
  simp only [ShortComplex.map_X₃, ShortComplex.map_X₁, LinearMap.coe_comp, Function.comp_apply,
    DirectSum.lof_eq_of, DirectSum.lmap_of, LinearMap.flip_apply,
    Ext.bilinearCompOfLinear_apply_apply, gradedExtForget_of, ← gradedExtForgetComponent_apply,
    coe_postcompOfLinear]
  exact gradedExtForgetComponent_comp_extClass hS X rfl x

/-- **Graded and ungraded `Ext` agree after summing over internal degrees.** Over a left
Noetherian graded algebra, for a finitely generated graded module `X` and any graded module `Y`,
the comparison `⨁ⱼ Extⁿ(X, Y{j}) → Extⁿ(X, Y)` forgetting the grading is bijective in every
cohomological degree. -/
theorem gradedExtForget_bijective [GradedAlgebra 𝒜] [IsNoetherianRing A]
    (X Y : GradedModuleCat.{uA} 𝒜) [Module.Finite A X] (n : ℕ) :
    Function.Bijective (gradedExtForget 𝒜 X Y n) := by
  induction n generalizing X with
  | zero =>
    rw [gradedExtForget_zero]
    exact (gradedExtZeroForgetEquiv 𝒜 X Y).bijective
  | succ n ih =>
    -- Dimension shifting along a finite graded free presentation `0 → K → F → X → 0`.
    obtain ⟨I, _, d, π, hπ⟩ := exists_finite_free_surjection.{uk, uA, uA} X
    have : Module.Finite A (kernelObj π) :=
      inferInstanceAs (Module.Finite A (LinearMap.ker π.hom))
    let S := ShortComplex.mk (kernelι π) π (kernelι_comp π)
    have hS : S.ShortExact :=
      { exact := exact_iff.2 (by simpa [S, hom_kernelι] using LinearMap.exact_subtype_ker_map π.hom)
        mono_f := (mono_iff_injective _).2 (by simp [S, hom_kernelι])
        epi_g := (epi_iff_surjective _).2 hπ }
    have : Module.Projective A (free 𝒜 d) := inferInstanceAs (Module.Projective A (⨁ _ : I, A))
    have : Projective S.X₂ := projective_of_module_projective _
    have : Projective (S.map toModuleCat).X₂ :=
      have : Module.Projective A (S.map toModuleCat).X₂ := ‹Module.Projective A (free 𝒜 d)›
      ModuleCat.projective_of_categoryTheory_projective _
    have hS' := hS.map_of_exact toModuleCat
    refine LinearMap.bijective_of_surjective_of_bijective_of_right_exact
      (DirectSum.lmap fun j ↦ (Ext.mk₀ S.f).precompOfLinear k
        (((shift 𝒜) ^ j).functor.obj Y) (zero_add n))
      (DirectSum.lmap fun j ↦ hS.extClass.precompOfLinear k
        (((shift 𝒜) ^ j).functor.obj Y) (add_comm 1 n))
      ((Ext.mk₀ (toModuleCat.map S.f)).precompOfLinear k _ (zero_add n))
      (hS'.extClass.precompOfLinear k _ (add_comm 1 n))
      (gradedExtForget 𝒜 S.X₂ Y n) (gradedExtForget 𝒜 S.X₁ Y n)
      (gradedExtForget 𝒜 S.X₃ Y (n + 1))
      (gradedExtForget_comp_lmap_precomp_mk₀ S.f n).symm
      (gradedExtForget_comp_lmap_precomp_extClass hS Y n).symm
      (Function.Exact.directSum fun j ↦ (ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.contravariant_sequence_exact₁' hS _ n (n + 1) (add_comm 1 n)))
      ((ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.contravariant_sequence_exact₁' hS' _ n (n + 1) (add_comm 1 n)))
      (ih S.X₂).2 (ih S.X₁)
      ((DirectSum.lmap_surjective _).2 fun j x₃ ↦
        Ext.contravariant_sequence_exact₃ hS _ x₃
          (Ext.subsingleton_of_projective _ _ _ |>.elim _ _) (add_comm 1 n))
      (fun x₃ ↦ Ext.contravariant_sequence_exact₃ hS' _ x₃
          (Ext.subsingleton_of_projective _ _ _ |>.elim _ _) (add_comm 1 n))

/-- **The natural comparison of graded and ungraded `Ext`**, as a linear equivalence: over a
left Noetherian graded algebra, for a finitely generated graded module `X`, the direct sum over
all internal degrees of `Extⁿ(X, Y{j})` is `Extⁿ(X, Y)` of the underlying modules. -/
def gradedExtForgetEquiv [GradedAlgebra 𝒜] [IsNoetherianRing A]
    (X Y : GradedModuleCat.{uA} 𝒜) [Module.Finite A X] (n : ℕ) :
    (⨁ j : ℤ, GradedExt.{w} (shift 𝒜) X Y n j) ≃ₗ[k]
      Ext.{w'} (toModuleCat.obj X) (toModuleCat.obj Y) n :=
  LinearEquiv.ofBijective (gradedExtForget 𝒜 X Y n) (gradedExtForget_bijective X Y n)

@[simp]
theorem gradedExtForgetEquiv_apply [GradedAlgebra 𝒜] [IsNoetherianRing A]
    (X Y : GradedModuleCat.{uA} 𝒜) [Module.Finite A X] (n : ℕ)
    (x : ⨁ j : ℤ, GradedExt.{w} (shift 𝒜) X Y n j) :
    gradedExtForgetEquiv X Y n x = gradedExtForget 𝒜 X Y n x := by
  simp [gradedExtForgetEquiv]

/-- Over a left Noetherian graded algebra, a finitely generated graded module and any graded
module form a graded `Ext` comparison pair with their underlying modules. -/
theorem isGradedExtComparison_toModuleCat [GradedAlgebra 𝒜] [IsNoetherianRing A]
    (X Y : GradedModuleCat.{uA} 𝒜) [Module.Finite A X] :
    IsGradedExtComparison.{w, w'} k (shift 𝒜) X Y (toModuleCat.obj X) (toModuleCat.obj Y) :=
  ⟨fun n ↦ ⟨gradedExtForgetEquiv X Y n⟩⟩

end TauCeti.GradedModuleCat
