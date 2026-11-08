/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.HomCokernel.Basic
public import TauCeti.Algebra.Homology.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Computing Ext¹ from a projective presentation

For a short exact sequence `S : 0 → P₁ → P₀ → M → 0` with `P₀` projective,
`homCokernelEquivExt` identifies the explicit quotient
`Hom(P₁, Y) / im(Hom(P₀, Y))` with `Ext¹(M, Y)`. The quotient is defined
independently of derived categories in `TauCeti.CategoryTheory.Linear.HomCokernel.Basic`.
The comparison is natural in `Y` and identifies the quotients obtained from any
two projective presentations of `M`. No projectivity of `P₁` is needed to compute
degree one.

Mathlib's extension class defines the connecting morphism in the contravariant
long exact Ext sequence. For a projective middle term, this morphism is surjective
with kernel the maps extending to that term, giving the quotient identification.
In higher degrees, composition with the extension class of such a sequence is a bijection
`Ext^{n+1}(P₁, Y) ⟶ Ext^{n+2}(M, Y)` (`TauCeti.precomp_extClass_bijective`). Its two halves
transfer vanishing between `Ext^{n+1}(P₁, Y)` and `Ext^{n+2}(M, Y)`
(`CategoryTheory.ShortComplex.ShortExact.ext_X₃_eq_zero_of_ext_X₁_eq_zero` and
`CategoryTheory.ShortComplex.ShortExact.ext_X₁_eq_zero_of_ext_X₃_eq_zero`), and
iterating them along a chain of short exact sequences gives
`TauCeti.ext_X₃_eq_zero_of_forall_exists_f_comp_eq`. When `P₁` is projective too, all of
`Ext^*(M, Y)` vanishes exactly when restriction `Hom(P₀, Y) → Hom(P₁, Y)` is bijective
(`CategoryTheory.ShortComplex.ShortExact.forall_subsingleton_ext_X₃_iff_bijective`).

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe u v w t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S T : ShortComplex C}

section Ring

variable (R : Type t) [Ring R] [Linear R C] (hS : S.ShortExact) (Y : C)

/-- The connecting map `Hom(S.X₁, Y) → Ext¹(S.X₃, Y)` of a short exact sequence. -/
noncomputable def homBoundary : (S.X₁ ⟶ Y) →ₗ[R] Ext.{w} S.X₃ Y 1 where
  toFun f := hS.extClass.comp (Ext.mk₀ f) (add_zero 1)
  map_add' := by simp [Ext.mk₀_add]
  map_smul' := by simp [Ext.mk₀_smul]

/-- The Hom connecting map pushes the extension class forward along its argument. -/
@[simp]
theorem homBoundary_apply (f : S.X₁ ⟶ Y) :
    homBoundary R hS Y f = hS.extClass.comp (Ext.mk₀ f) (add_zero 1) :=
  (rfl)

/-- The kernel of the connecting map consists exactly of maps extending to `S.X₂`. -/
theorem ker_homBoundary :
    (homBoundary R hS Y).ker = (Linear.leftComp R Y S.f).range := by
  ext f
  simp only [LinearMap.mem_ker, homBoundary_apply, LinearMap.mem_range,
    Linear.leftComp_apply]
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := Ext.contravariant_sequence_exact₁ hS Y (Ext.mk₀ f) rfl hf
    refine ⟨Ext.linearEquiv₀ (R := R) g, ?_⟩
    apply (Ext.mk₀_bijective _ _).1
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_linearEquiv₀_apply]
    exact hg
  · rintro ⟨g, rfl⟩
    rw [← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Ext.mk₀ g)

/-- If the middle term is projective, every extension class is a Hom boundary. -/
theorem homBoundary_surjective [Projective S.X₂] :
    Function.Surjective (homBoundary R hS Y) := by
  intro e
  obtain ⟨f, hf⟩ := Ext.contravariant_sequence_exact₃ hS Y e (n₀ := 0)
    (Ext.eq_zero_of_projective _) rfl
  exact ⟨Ext.linearEquiv₀ (R := R) f, by simpa using hf⟩

/-- The Hom cokernel of a projective presentation computes `Ext¹` as an `R`-module. -/
noncomputable def homCokernelEquivExt [Projective S.X₂] :
    HomCokernel R S.f Y ≃ₗ[R] Ext.{w} S.X₃ Y 1 :=
  (Submodule.quotEquivOfEq _ _ (ker_homBoundary R hS Y).symm).trans
    ((homBoundary R hS Y).quotKerEquivOfSurjective (homBoundary_surjective R hS Y))

/-- The comparison sends the class of a map to the corresponding pushout extension class. -/
@[simp]
theorem homCokernelEquivExt_mk [Projective S.X₂] (f : S.X₁ ⟶ Y) :
    homCokernelEquivExt R hS Y (Submodule.Quotient.mk f) =
      hS.extClass.comp (Ext.mk₀ f) (add_zero 1) := by
  simp [homCokernelEquivExt]

/-- Under the inverse comparison, a pushout extension is represented by its defining map. -/
@[simp]
theorem homCokernelEquivExt_symm_comp_mk₀ [Projective S.X₂] (f : S.X₁ ⟶ Y) :
    (homCokernelEquivExt R hS Y).symm
        (hS.extClass.comp (Ext.mk₀ f) (add_zero 1)) = Submodule.Quotient.mk f := by
  rw [← homCokernelEquivExt_mk R hS Y, LinearEquiv.symm_apply_apply]

variable {Y}

/-- The Hom-cokernel computation of `Ext¹` is natural in the target object. -/
@[simp]
theorem homCokernelEquivExt_naturality [Projective S.X₂] {Z : C} (g : Y ⟶ Z)
    (x : HomCokernel R S.f Y) :
    homCokernelEquivExt R hS Z (HomCokernel.map R S.f g x) =
      (homCokernelEquivExt R hS Y x).comp (Ext.mk₀ g) (add_zero 1) := by
  induction x using Submodule.Quotient.induction_on with
  | _ f => simp

variable (Y)

/-- Projective presentations of isomorphic objects give canonically equivalent Hom cokernels.
The comparison identifies the extension classes represented in the two presentations. -/
noncomputable def homCokernelEquiv (hT : T.ShortExact) [Projective S.X₂] [Projective T.X₂]
    (e : S.X₃ ≅ T.X₃) : HomCokernel R S.f Y ≃ₗ[R] HomCokernel R T.f Y :=
  (homCokernelEquivExt R hS Y).trans <|
    (extLinearEquivOfIso R e (Iso.refl Y) 1).trans (homCokernelEquivExt R hT Y).symm

/-- Comparing presentations preserves their extension classes, after transport along `e`. -/
@[simp]
theorem homCokernelEquivExt_homCokernelEquiv (hT : T.ShortExact)
    [Projective S.X₂] [Projective T.X₂] (e : S.X₃ ≅ T.X₃) (x : HomCokernel R S.f Y) :
    homCokernelEquivExt R hT Y (homCokernelEquiv R hS Y hT e x) =
      (Ext.mk₀ e.inv).comp (homCokernelEquivExt R hS Y x) (zero_add 1) := by
  simp [homCokernelEquiv]

variable {Y} in
/-- Presentation comparisons are natural in the target object. -/
@[simp]
theorem homCokernelEquiv_naturality (hT : T.ShortExact) [Projective S.X₂] [Projective T.X₂]
    (e : S.X₃ ≅ T.X₃) {Z : C} (g : Y ⟶ Z) (x : HomCokernel R S.f Y) :
    homCokernelEquiv R hS Z hT e (HomCokernel.map R S.f g x) =
      HomCokernel.map R T.f g (homCokernelEquiv R hS Y hT e x) := by
  apply (homCokernelEquivExt R hT Z).injective
  simp

/-- Comparing a presentation with itself induces the identity on its Hom cokernel. -/
@[simp]
theorem homCokernelEquiv_refl [Projective S.X₂] :
    homCokernelEquiv R hS Y hS (Iso.refl S.X₃) = LinearEquiv.refl R _ := by
  apply LinearEquiv.ext
  intro x
  apply (homCokernelEquivExt R hS Y).injective
  simp

/-- Reversing the isomorphism of resolved objects reverses the presentation comparison. -/
@[simp]
theorem homCokernelEquiv_symm (hT : T.ShortExact) [Projective S.X₂] [Projective T.X₂]
    (e : S.X₃ ≅ T.X₃) :
    (homCokernelEquiv R hS Y hT e).symm = homCokernelEquiv R hT Y hS e.symm := by
  apply LinearEquiv.ext
  intro x
  apply (homCokernelEquivExt R hS Y).injective
  apply (extLinearEquivOfIso R e (Iso.refl Y) 1).injective
  simp only [extLinearEquivOfIso_apply, Iso.refl_hom, Ext.comp_mk₀_id]
  rw [← homCokernelEquivExt_homCokernelEquiv R hS Y hT e]
  simp

/-- Presentation comparisons compose according to the isomorphisms of resolved objects. -/
@[simp]
theorem homCokernelEquiv_trans {U : ShortComplex C} (hT : T.ShortExact) (hU : U.ShortExact)
    [Projective S.X₂] [Projective T.X₂] [Projective U.X₂]
    (e : S.X₃ ≅ T.X₃) (f : T.X₃ ≅ U.X₃) :
    (homCokernelEquiv R hS Y hT e).trans (homCokernelEquiv R hT Y hU f) =
      homCokernelEquiv R hS Y hU (e ≪≫ f) := by
  apply LinearEquiv.ext
  intro x
  apply (homCokernelEquivExt R hU Y).injective
  simp

end Ring

/-- **Dimension shifting against a projective middle term**: if `S` is short exact with `S.X₂`
projective, composition with the extension class is a bijection
`Ext^{n+1}(S.X₁, Y) ⟶ Ext^{n+2}(S.X₃, Y)`. -/
theorem precomp_extClass_bijective (hS : S.ShortExact) [Projective S.X₂] (Y : C) (n : ℕ) :
    Function.Bijective (Ext.precomp hS.extClass Y (show 1 + (n + 1) = n + 2 by lia)) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun e ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₁ hS Y x (n₁ := n + 2) (by lia) hx
    rw [Ext.eq_zero_of_projective y, Ext.comp_zero]
  · obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y e (Ext.eq_zero_of_projective _)
      (n₀ := n + 1) (by lia)
    exact ⟨x, rfl⟩

end TauCeti

namespace CategoryTheory.ShortComplex.ShortExact

open CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {S : ShortComplex C}

/-- **Dimension shifting to the cokernel**: if `S` is short exact with projective middle term,
then `Ext^{n+2}(S.X₃, Y) = 0` as soon as `Ext^{n+1}(S.X₁, Y) = 0`. -/
theorem ext_X₃_eq_zero_of_ext_X₁_eq_zero (hS : S.ShortExact) [Projective S.X₂] {Y : C} {n : ℕ}
    (h : ∀ x : Ext.{w} S.X₁ Y (n + 1), x = 0) (e : Ext.{w} S.X₃ Y (n + 2)) : e = 0 := by
  obtain ⟨x, rfl⟩ := (TauCeti.precomp_extClass_bijective hS Y n).2 e
  rw [h x, map_zero]

/-- **Dimension shifting to the kernel**: if `S` is short exact with projective middle term,
then `Ext^{n+1}(S.X₁, Y) = 0` as soon as `Ext^{n+2}(S.X₃, Y) = 0`. -/
theorem ext_X₁_eq_zero_of_ext_X₃_eq_zero (hS : S.ShortExact) [Projective S.X₂] {Y : C} {n : ℕ}
    (h : ∀ e : Ext.{w} S.X₃ Y (n + 2), e = 0) (x : Ext.{w} S.X₁ Y (n + 1)) : x = 0 :=
  (TauCeti.precomp_extClass_bijective hS Y n).1 (by rw [h (Ext.precomp _ _ _ x), map_zero])

/-- **`Ext` out of an object with a projective resolution of length one.** Let `S` be short
exact with `S.X₁` and `S.X₂` projective. Then every `Extⁿ(S.X₃, Y)` vanishes exactly when
restriction along `S.f` is a bijection `Hom(S.X₂, Y) → Hom(S.X₁, Y)`: its kernel is
`Hom(S.X₃, Y)`, its cokernel is `Ext¹(S.X₃, Y)`, and `Ext^{n+2}(S.X₃, Y) = 0`. -/
theorem forall_subsingleton_ext_X₃_iff_bijective (hS : S.ShortExact) [Projective S.X₁]
    [Projective S.X₂] (Y : C) :
    (∀ n, Subsingleton (Ext.{w} S.X₃ Y n)) ↔ Function.Bijective fun φ : S.X₂ ⟶ Y ↦ S.f ≫ φ := by
  have := hS.epi_g
  have h₀ : Subsingleton (Ext.{w} S.X₃ Y 0) ↔ Function.Injective fun φ : S.X₂ ⟶ Y ↦ S.f ≫ φ := by
    rw [Ext.homEquiv₀.subsingleton_congr]
    refine ⟨fun _ φ₁ φ₂ h ↦ ?_, fun h ↦ ⟨fun ψ₁ ψ₂ ↦ ?_⟩⟩
    · obtain ⟨ψ, hψ⟩ := Limits.CokernelCofork.IsColimit.desc' hS.gIsCokernel (φ₁ - φ₂)
        (by simpa [Preadditive.comp_sub, sub_eq_zero] using h)
      rw [← sub_eq_zero, ← hψ, Subsingleton.elim (α := S.X₃ ⟶ Y) ψ 0, Limits.comp_zero]
    · rw [← cancel_epi S.g]
      exact h (by simp only [S.zero_assoc, Limits.zero_comp])
  have h₁ : Subsingleton (Ext.{w} S.X₃ Y 1) ↔ Function.Surjective fun φ : S.X₂ ⟶ Y ↦ S.f ≫ φ := by
    have hcomm : (Ext.mk₀ S.f).precomp Y (add_zero 0) ∘ Ext.mk₀ =
        Ext.mk₀ ∘ fun φ : S.X₂ ⟶ Y ↦ S.f ≫ φ :=
      funext fun φ ↦ Ext.mk₀_comp_mk₀ S.f φ
    rw [Ext.one_subsingleton_iff_of_projective Y S hS ‹_›,
      ← Function.Surjective.of_comp_iff _ (Ext.mk₀_bijective _ _).surjective, hcomm,
      Function.Surjective.of_comp_iff' (Ext.mk₀_bijective _ _)]
  refine ⟨fun h ↦ ⟨h₀.1 (h 0), h₁.1 (h 1)⟩, fun ⟨hi, hs⟩ n ↦ ?_⟩
  match n with
  | 0 => exact h₀.2 hi
  | 1 => exact h₁.2 hs
  | n + 2 =>
    exact ⟨fun x y ↦ by
      rw [hS.ext_X₃_eq_zero_of_ext_X₁_eq_zero Ext.eq_zero_of_projective x,
        hS.ext_X₃_eq_zero_of_ext_X₁_eq_zero Ext.eq_zero_of_projective y]⟩

end CategoryTheory.ShortComplex.ShortExact

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- **`Ext` vanishing along a chain of short exact sequences.** Let `Sₘ`, for `m : ℤ`, be short
exact sequences with projective middle terms, with `Sₘ.X₃ ≅ Sₘ₊₁.X₁`, such that every morphism
`Sₘ.X₁ ⟶ Y` extends along `Sₘ.f`. Then `Ext^{n+1}(Sₘ.X₃, Y) = 0` for all `m` and `n`: in degree
one by `CategoryTheory.ShortComplex.ShortExact.ext_eq_zero_of_exists_f_comp_eq`, and in higher
degrees by dimension shifting along `Sₘ`. The cycles of a totally acyclic complex are the main
example. -/
theorem ext_X₃_eq_zero_of_forall_exists_f_comp_eq {S : ℤ → ShortComplex C}
    (hS : ∀ m, (S m).ShortExact) [∀ m, Projective (S m).X₂]
    (e : ∀ m, (S m).X₃ ≅ (S (m + 1)).X₁) {Y : C}
    (h : ∀ m (φ : (S m).X₁ ⟶ Y), ∃ ψ : (S m).X₂ ⟶ Y, (S m).f ≫ ψ = φ) (n : ℕ) (m : ℤ)
    (x : Ext.{w} (S m).X₃ Y (n + 1)) : x = 0 := by
  induction n generalizing m with
  | zero => exact (hS m).ext_eq_zero_of_exists_f_comp_eq (h m) x
  | succ n ih =>
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
    exact (hS (k + 1)).ext_X₃_eq_zero_of_ext_X₁_eq_zero (ext_eq_zero_of_iso (e k).symm (ih k)) x

end TauCeti
