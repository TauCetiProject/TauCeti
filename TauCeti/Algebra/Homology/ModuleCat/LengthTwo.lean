/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# Length-two projective resolutions of module cokernels

For maps `f : P₂ →ₗ[A] P₁` and `g : P₁ →ₗ[A] P₀` whose composite is zero,
`ModuleCatLengthTwo.complex` is the chain complex supported in degrees zero, one and two.
If the modules are projective, `f` is injective and `range f = ker g`,
`ModuleCatLengthTwo.projectiveResolution` resolves `P₀ ⧸ range g`.

This packages the categorical assembly used by the signed and signless preprojective Koszul
resolutions.

## References

* `TauCeti.RepresentationTheory.Quiver.Preprojective.Resolution`, for the categorical assembly
  of the signed preprojective Koszul resolution.
-/

public section

namespace TauCeti.ModuleCatLengthTwo

open CategoryTheory

universe u v

variable {A : Type u} [Ring A]
  (P₀ P₁ P₂ : Type v) [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁] [AddCommGroup P₂] [Module A P₂]

/-- The three given modules in degrees zero, one and two, followed by zero modules. -/
noncomputable abbrev term : ℕ → ModuleCat.{v} A
  | 0 => ModuleCat.of A P₀
  | 1 => ModuleCat.of A P₁
  | 2 => ModuleCat.of A P₂
  | _ + 3 => ModuleCat.of A PUnit

variable {P₀ P₁ P₂} (f : P₂ →ₗ[A] P₁) (g : P₁ →ₗ[A] P₀)

/-- The given maps as consecutive differentials, followed by zero maps. -/
noncomputable def differential : ∀ n : ℕ,
    term (A := A) P₀ P₁ P₂ (n + 1) ⟶ term (A := A) P₀ P₁ P₂ n
  | 0 => ModuleCat.ofHom g
  | 1 => ModuleCat.ofHom f
  | _ + 2 => 0

@[simp]
theorem differential_zero : differential f g 0 = ModuleCat.ofHom g := (rfl)

@[simp]
theorem differential_one : differential f g 1 = ModuleCat.ofHom f := (rfl)

@[simp]
theorem differential_add_two (n : ℕ) : differential f g (n + 2) = 0 := (rfl)

variable (hcomp : g.comp f = 0)

include hcomp in
private theorem differential_comp_succ : ∀ n : ℕ,
    differential f g (n + 1) ≫ differential f g n = 0
  | 0 => ModuleCat.hom_ext hcomp
  | 1 => by simp [differential]
  | _ + 2 => by simp [differential]

/-- The chain complex with the specified three modules and two differentials. -/
noncomputable def complex : ChainComplex (ModuleCat.{v} A) ℕ :=
  ChainComplex.of (term (A := A) P₀ P₁ P₂) (differential f g) (differential_comp_succ f g hcomp)

/-- The terms of the bundled complex are the specified modules. -/
@[simp]
theorem complex_X (n : ℕ) : (complex f g hcomp).X n = term (A := A) P₀ P₁ P₂ n := (rfl)

/-- The bundled terms identified with the three specified modules. -/
noncomputable def complexXIso (n : ℕ) :
    (complex f g hcomp).X n ≅ term (A := A) P₀ P₁ P₂ n := Iso.refl _

/-- The bundled differential is the specified linear map. -/
@[simp]
theorem complex_d (n : ℕ) : (complex f g hcomp).d (n + 1) n =
    (complexXIso f g hcomp (n + 1)).hom ≫ differential f g n ≫
      (complexXIso f g hcomp n).inv :=
  ChainComplex.of_d _ _ _

/-- The quotient map augments the three-term complex to the cokernel of its last map. -/
noncomputable def augmentation : complex f g hcomp ⟶
    (ChainComplex.single₀ _).obj (ModuleCat.of A (P₀ ⧸ LinearMap.range g)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (LinearMap.range g).mkQ,
      ModuleCat.hom_ext (LinearMap.range_mkQ_comp g)⟩

/-- The augmentation in degree zero is the cokernel quotient map. -/
@[simp]
theorem augmentation_f_zero :
    (complexXIso f g hcomp 0).inv ≫ (augmentation f g hcomp).f 0 =
    ModuleCat.ofHom (LinearMap.range g).mkQ := by
  apply ModuleCat.hom_ext
  ext x
  rfl

variable (hexact : LinearMap.range f = LinearMap.ker g) (hinj : Function.Injective f)

include hexact hinj in
private theorem range_differential_succ_eq_ker : ∀ n : ℕ,
    LinearMap.range (differential f g (n + 1)).hom =
      LinearMap.ker (differential f g n).hom
  | 0 => hexact
  | 1 => by
    simp only [differential, ModuleCat.hom_zero, LinearMap.range_zero]
    exact ((LinearMap.ker_eq_bot).2 hinj).symm
  | _ + 2 => Subsingleton.elim _ _

variable [Module.Projective A P₀] [Module.Projective A P₁] [Module.Projective A P₂]

include hexact hinj in
/-- An exact three-term complex of projective modules with injective first map resolves
its cokernel, with the given maps as differentials and the quotient map as augmentation. -/
noncomputable def projectiveResolution :
    ProjectiveResolution (ModuleCat.of A (P₀ ⧸ LinearMap.range g)) := by
  let hcomp : g.comp f = 0 := LinearMap.range_le_ker_iff.mp hexact.le
  refine
    { complex := complex f g hcomp
      projective := ?_
      «π» := augmentation f g hcomp
      quasiIso := ?_ }
  · intro n
    rcases n with _ | (_ | (_ | n))
    · exact inferInstanceAs (Projective (ModuleCat.of A P₀))
    · exact inferInstanceAs (Projective (ModuleCat.of A P₁))
    · exact inferInstanceAs (Projective (ModuleCat.of A P₂))
    · exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of A PUnit)).projective
  · constructor
    intro n
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      refine ⟨?_, ?_⟩
      · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        simp only [HomologicalComplex.shortComplexFunctor'_obj_f]
        exact (Submodule.ker_mkQ (LinearMap.range g)).symm
      · rw [ModuleCat.epi_iff_surjective]
        exact Submodule.mkQ_surjective _
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
        HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
        ShortComplex.moduleCat_exact_iff_range_eq_ker]
      simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
        HomologicalComplex.shortComplexFunctor'_obj_g]
      rw [complex_d f g hcomp (n + 1), complex_d f g hcomp n]
      exact range_differential_succ_eq_ker f g hexact hinj n


/-- The resolution uses the specified three-term complex. -/
@[simp]
theorem projectiveResolution_complex :
    (projectiveResolution f g hexact hinj).complex = complex f g hcomp := (rfl)

/-- The projective terms of the resolution identified with the given modules. -/
noncomputable def projectiveResolutionXIso (n : ℕ) :
    (projectiveResolution f g hexact hinj).complex.X n ≅
      term (A := A) P₀ P₁ P₂ n :=
  Iso.refl _

/-- The resolution differentials are the given linear maps, using the term identifications. -/
@[simp]
theorem projectiveResolution_d (n : ℕ) :
    (projectiveResolution f g hexact hinj).complex.d (n + 1) n =
      (projectiveResolutionXIso f g hexact hinj (n + 1)).hom ≫ differential f g n ≫
        (projectiveResolutionXIso f g hexact hinj n).inv := by
  -- The term identifications are identities after expanding the constructed resolution.
  dsimp only [projectiveResolutionXIso, projectiveResolution]
  exact complex_d f g _ n

/-- The zeroth resolution map is the cokernel quotient map. -/
@[simp]
theorem projectiveResolution_π_f_zero :
    (projectiveResolutionXIso f g hexact hinj 0).inv ≫
        (projectiveResolution f g hexact hinj).π.f 0 =
      ModuleCat.ofHom (LinearMap.range g).mkQ := by
  -- The term identifications are identities after expanding the constructed resolution.
  dsimp only [projectiveResolutionXIso, projectiveResolution]
  exact augmentation_f_zero f g _

end TauCeti.ModuleCatLengthTwo
