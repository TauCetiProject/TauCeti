/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.RingTheory.SimpleModule.InjectiveProjective

/-!
# Descent of bilinear and perfect pairings to homology

For short complexes `S : X₁ ⟶ X₂ ⟶ X₃` and `T : Y₁ ⟶ Y₂ ⟶ Y₃` of `R`-modules, a middle-term
pairing `p₂ : X₂ →ₗ[R] Y₂ →ₗ[R] R` vanishing on boundaries against cycles descends to
`S.homologyPairing T p₂ hf hg`. Over a self-injective commutative ring (`Module.Baer R R`) or a
field, a compatible triple `(p₁, p₂, p₃)` of perfect pairings makes the descended homology pairing
perfect (`isPerfPair_homologyPairing_of_baer`, `isPerfPair_homologyPairing`), specializing via `sc'`
to cohomology pairings `CochainComplex.homologyPairing` in complementary degrees `(d, n - d)`.

## References

* A. Dold, *Lectures on Algebraic Topology*, Chapter VI, §7.
-/

public section
noncomputable section

open CategoryTheory Function

universe u v w

namespace CategoryTheory.ShortComplex

section CommRing

variable {R : Type u} [CommRing R]
variable (S : ShortComplex (ModuleCat.{v} R)) (T : ShortComplex (ModuleCat.{w} R))

private def concreteHomologyPairing (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0) :
    S.moduleCatLeftHomologyData.H →ₗ[R] T.moduleCatLeftHomologyData.H →ₗ[R] R :=
  (p₂.compl₁₂ (LinearMap.ker S.g.hom).subtype (LinearMap.ker T.g.hom).subtype).liftQ₂
    (LinearMap.range S.moduleCatToCycles) (LinearMap.range T.moduleCatToCycles)
    (by rintro _ ⟨x, rfl⟩; exact LinearMap.ext fun y ↦ hf x y.val y.property)
    (by rintro _ ⟨y, rfl⟩; exact LinearMap.ext fun x ↦ hg x.val y x.property)

/-- The bilinear pairing on homology induced by a middle-term pairing `p₂` whose left and right
restrictions vanish against boundaries of the opposite short complex. -/
def homologyPairing (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0) :
    S.homology →ₗ[R] T.homology →ₗ[R] R :=
  (concreteHomologyPairing S T p₂ hf hg).compl₁₂
    S.moduleCatHomologyIso.toLinearEquiv.toLinearMap
    T.moduleCatHomologyIso.toLinearEquiv.toLinearMap

/-- On classes of cycles, `ShortComplex.homologyPairing` evaluates `p₂` on the middle terms. -/
@[simp] theorem homologyPairing_homologyπ (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0)
    (x : S.cycles) (y : T.cycles) :
    S.homologyPairing T p₂ hf hg (S.homologyπ.hom x) (T.homologyπ.hom y) =
      p₂ (S.iCycles.hom x) (T.iCycles.hom y) := by
  rw [← S.moduleCatCyclesIso_hom_i, ← T.moduleCatCyclesIso_hom_i]
  simp [homologyPairing, concreteHomologyPairing, ModuleCat.Hom.hom]

/-- Flipping `ShortComplex.homologyPairing` exchanges the two short complexes and flips `p₂`. -/
@[simp] theorem flip_homologyPairing (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0) :
    (S.homologyPairing T p₂ hf hg).flip =
      T.homologyPairing S p₂.flip (fun y x hx ↦ by rw [LinearMap.flip_apply]; exact hg x y hx)
        (fun y x hy ↦ by rw [LinearMap.flip_apply]; exact hf x y hy) := by
  ext b a
  have hS : Surjective S.homologyπ.hom := (ModuleCat.epi_iff_surjective S.homologyπ).1 inferInstance
  have hT : Surjective T.homologyπ.hom := (ModuleCat.epi_iff_surjective T.homologyπ).1 inferInstance
  obtain ⟨x, rfl⟩ := hS a; obtain ⟨y, rfl⟩ := hT b
  rw [LinearMap.flip_apply, homologyPairing_homologyπ, homologyPairing_homologyπ,
    LinearMap.flip_apply]

/-- `ShortComplex.homologyPairing` is natural with respect to morphisms of short complexes whose
middle components are adjoint under the pairings. -/
theorem homologyPairing_homologyMap {S' : ShortComplex (ModuleCat.{v} R)}
    {T' : ShortComplex (ModuleCat.{w} R)} (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0)
    (p₂' : S'.X₂ →ₗ[R] T'.X₂ →ₗ[R] R)
    (hf' : ∀ (x : S'.X₁) (y : T'.X₂), T'.g.hom y = 0 → p₂' (S'.f.hom x) y = 0)
    (hg' : ∀ (x : S'.X₂) (y : T'.X₁), S'.g.hom x = 0 → p₂' x (T'.f.hom y) = 0)
    (φ : S ⟶ S') (ψ : T' ⟶ T)
    (hφψ : ∀ (x : S.X₂) (y : T'.X₂), p₂' (φ.τ₂.hom x) y = p₂ x (ψ.τ₂.hom y))
    (a : S.homology) (b : T'.homology) :
    S'.homologyPairing T' p₂' hf' hg' ((ShortComplex.homologyMap φ).hom a) b =
      S.homologyPairing T p₂ hf hg a ((ShortComplex.homologyMap ψ).hom b) := by
  have hS : Surjective S.homologyπ.hom := (ModuleCat.epi_iff_surjective S.homologyπ).1 inferInstance
  have hT : Surjective T'.homologyπ.hom :=
    (ModuleCat.epi_iff_surjective T'.homologyπ).1 inferInstance
  obtain ⟨x, rfl⟩ := hS a; obtain ⟨y, rfl⟩ := hT b
  rw [← ModuleCat.comp_apply, ShortComplex.homologyπ_naturality, ModuleCat.comp_apply,
    ← ModuleCat.comp_apply T'.homologyπ, ShortComplex.homologyπ_naturality, ModuleCat.comp_apply,
    homologyPairing_homologyπ, homologyPairing_homologyπ,
    ← ModuleCat.comp_apply, ShortComplex.cyclesMap_i, ModuleCat.comp_apply,
    ← ModuleCat.comp_apply (ShortComplex.cyclesMap ψ), ShortComplex.cyclesMap_i,
    ModuleCat.comp_apply, hφψ]

/-- A linear map into a Baer module `Q` vanishing on `ker g` factors through `g`. -/
private theorem exists_comp_eq_of_ker_le_ker {M N Q : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q] (hQ : Module.Baer R Q)
    (g : M →ₗ[R] N) (f : M →ₗ[R] Q) (hker : LinearMap.ker g ≤ LinearMap.ker f) :
    ∃ μ : N →ₗ[R] Q, μ.comp g = f := by
  obtain ⟨μ, hμ⟩ := hQ.extension_property (LinearMap.range g).subtype Subtype.val_injective
    (((LinearMap.ker g).liftQ f hker).comp g.quotKerEquivRange.symm.toLinearMap)
  refine ⟨μ, LinearMap.ext fun y ↦ ?_⟩
  have hy := DFunLike.congr_fun hμ ⟨g y, LinearMap.mem_range_self g y⟩
  simpa [LinearMap.quotKerEquivRange_symm_apply_image] using hy

private theorem concreteHomologyPairing_bijective_left (hR : Module.Baer R R)
    (p₁ : S.X₁ →ₗ[R] T.X₃ →ₗ[R] R) (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (p₃ : S.X₃ →ₗ[R] T.X₁ →ₗ[R] R) [p₁.IsPerfPair] [p₂.IsPerfPair] [p₃.IsPerfPair]
    (h₁ : ∀ (x : S.X₁) (y : T.X₂), p₂ (S.f.hom x) y = p₁ x (T.g.hom y))
    (h₃ : ∀ (x : S.X₂) (y : T.X₁), p₂ x (T.f.hom y) = p₃ (S.g.hom x) y)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0) :
    Bijective (concreteHomologyPairing S T p₂ hf hg) := by
  refine ⟨?_, fun φ ↦ ?_⟩
  · -- Injectivity: `p₂ c` vanishes on `ker T.g`, so it factors through `T.g` via `hR` and `p₁⁻¹`
    -- exhibits `c` as a boundary in `S`.
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]; intro q hq
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range S.moduleCatToCycles) q
    have hc : LinearMap.ker T.g.hom ≤ LinearMap.ker (p₂ c.val) := fun y hy ↦
      DFunLike.congr_fun hq ((LinearMap.range T.moduleCatToCycles).mkQ ⟨y, hy⟩)
    obtain ⟨μ, hμ⟩ := exists_comp_eq_of_ker_le_ker hR T.g.hom (p₂ c.val) hc
    refine (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).mpr
      ⟨p₁.toPerfPair.symm μ, Subtype.ext <| (LinearMap.IsPerfPair.bijective_left p₂).injective <|
        LinearMap.ext fun y ↦ ?_⟩
    rw [moduleCatToCycles, LinearMap.codRestrict_apply, h₁, ← DFunLike.congr_fun hμ y,
      LinearMap.comp_apply]
    exact DFunLike.congr_fun (p₁.apply_symm_toPerfPair_self μ) (T.g.hom y)
  · -- Surjectivity: extend `φ` from `ker T.g` to `Φ : T.X₂ →ₗ[R] R` via `hR`; vanishing of `Φ` on
    -- `range T.f` places `p₂⁻¹ Φ` in `ker S.g` via `p₃`.
    let φ₀ := φ.comp (LinearMap.range T.moduleCatToCycles).mkQ
    obtain ⟨Φ, hΦ⟩ := hR.extension_property (LinearMap.ker T.g.hom).subtype Subtype.val_injective φ₀
    let x : S.X₂ := p₂.toPerfPair.symm Φ
    have hxΦ : p₂ x = Φ := p₂.apply_symm_toPerfPair_self Φ
    have hx : x ∈ LinearMap.ker S.g.hom :=
      (LinearMap.IsPerfPair.bijective_left p₃).injective <| by
        rw [map_zero]; ext y₁
        have hz : (LinearMap.range T.moduleCatToCycles).mkQ (T.moduleCatToCycles y₁) = 0 :=
          (Submodule.Quotient.mk_eq_zero _).mpr ⟨y₁, rfl⟩
        have hΦ' := DFunLike.congr_fun hΦ (T.moduleCatToCycles y₁)
        simp only [φ₀, LinearMap.comp_apply, Submodule.coe_subtype, moduleCatToCycles,
          LinearMap.codRestrict_apply, hz, map_zero] at hΦ'
        rw [LinearMap.zero_apply, ← h₃, hxΦ, hΦ']
    refine ⟨(LinearMap.range S.moduleCatToCycles).mkQ ⟨x, hx⟩, LinearMap.ext fun q ↦ ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range T.moduleCatToCycles) q
    rw [concreteHomologyPairing, Submodule.mkQ_apply, Submodule.mkQ_apply, LinearMap.liftQ₂_mk,
      LinearMap.compl₁₂_apply, Submodule.coe_subtype, Submodule.coe_subtype, ← Submodule.mkQ_apply,
      hxΦ]
    exact DFunLike.congr_fun hΦ y

/-- Over a self-injective commutative ring (`Module.Baer R R`), a triple of compatible perfect
pairings between two short complexes descends to a perfect pairing on homology. -/
theorem isPerfPair_homologyPairing_of_baer (hR : Module.Baer R R)
    (p₁ : S.X₁ →ₗ[R] T.X₃ →ₗ[R] R) (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (p₃ : S.X₃ →ₗ[R] T.X₁ →ₗ[R] R) [p₁.IsPerfPair] [p₂.IsPerfPair] [p₃.IsPerfPair]
    (h₁ : ∀ (x : S.X₁) (y : T.X₂), p₂ (S.f.hom x) y = p₁ x (T.g.hom y))
    (h₃ : ∀ (x : S.X₂) (y : T.X₁), p₂ x (T.f.hom y) = p₃ (S.g.hom x) y)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0 :=
      fun x y hy ↦ by rw [h₁, hy, map_zero])
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0 :=
      fun x y hx ↦ by rw [h₃, hx, map_zero, LinearMap.zero_apply]) :
    (S.homologyPairing T p₂ hf hg).IsPerfPair := by
  have _ : (concreteHomologyPairing S T p₂ hf hg).IsPerfPair :=
    ⟨concreteHomologyPairing_bijective_left S T hR p₁ p₂ p₃ h₁ h₃ hf hg, by
      have hflip : (concreteHomologyPairing S T p₂ hf hg).flip =
          concreteHomologyPairing T S p₂.flip (fun y x hx ↦ hg x y hx)
            (fun y x hy ↦ hf x y hy) := by
        ext b a; induction a using Submodule.Quotient.induction_on with
        | H _ => induction b using Submodule.Quotient.induction_on with
          | H _ => simp [concreteHomologyPairing]
      rw [hflip]
      exact concreteHomologyPairing_bijective_left T S hR p₃.flip p₂.flip p₁.flip
        (fun y x ↦ h₃ x y) (fun y x ↦ h₁ x y) _ _⟩
  rw [homologyPairing]; infer_instance

end CommRing

/-- Over a field, a triple of compatible perfect pairings between two short complexes descends to a
perfect pairing on homology. -/
theorem isPerfPair_homologyPairing {k : Type u} [Field k]
    (S : ShortComplex (ModuleCat.{v} k)) (T : ShortComplex (ModuleCat.{w} k))
    (p₁ : S.X₁ →ₗ[k] T.X₃ →ₗ[k] k) (p₂ : S.X₂ →ₗ[k] T.X₂ →ₗ[k] k) (p₃ : S.X₃ →ₗ[k] T.X₁ →ₗ[k] k)
    [p₁.IsPerfPair] [p₂.IsPerfPair] [p₃.IsPerfPair]
    (h₁ : ∀ (x : S.X₁) (y : T.X₂), p₂ (S.f.hom x) y = p₁ x (T.g.hom y))
    (h₃ : ∀ (x : S.X₂) (y : T.X₁), p₂ x (T.f.hom y) = p₃ (S.g.hom x) y)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0 :=
      fun x y hy ↦ by rw [h₁, hy, map_zero])
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0 :=
      fun x y hx ↦ by rw [h₃, hx, map_zero, LinearMap.zero_apply]) :
    (S.homologyPairing T p₂ hf hg).IsPerfPair :=
  isPerfPair_homologyPairing_of_baer S T (Module.Baer.of_isSemisimpleRing k k) p₁ p₂ p₃ h₁ h₃ hf hg

end CategoryTheory.ShortComplex

namespace CochainComplex

open CategoryTheory

section CommRing

variable {R : Type u} [CommRing R]
variable (C : CochainComplex (ModuleCat.{v} R) ℤ) (D : CochainComplex (ModuleCat.{w} R) ℤ) (n : ℤ)

private theorem sc'_pairing_left (p : ∀ d : ℤ, C.X d →ₗ[R] D.X (n - d) →ₗ[R] R)
    (hp : ∀ {a a' : ℤ}, a + 1 = a' → ∀ (x : C.X a) (y : D.X (n - a')),
      p a' ((C.d a a').hom x) y + a.negOnePow • p a x ((D.d (n - a') (n - a)).hom y) = 0)
    (d : ℤ) (x : (C.sc' (d - 1) d (d + 1)).X₁)
    (y : (D.sc' (n - (d + 1)) (n - d) (n - (d - 1))).X₂) :
    p d ((C.sc' (d - 1) d (d + 1)).f.hom x) y =
      ((-(d - 1).negOnePow) • p (d - 1)) x
        ((D.sc' (n - (d + 1)) (n - d) (n - (d - 1))).g.hom y) := by
  simpa only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g, Units.neg_smul, LinearMap.neg_apply,
    LinearMap.smul_apply] using eq_neg_of_add_eq_zero_left (hp (by omega : (d - 1) + 1 = d) x y)

private theorem sc'_pairing_right (p : ∀ d : ℤ, C.X d →ₗ[R] D.X (n - d) →ₗ[R] R)
    (hp : ∀ {a a' : ℤ}, a + 1 = a' → ∀ (x : C.X a) (y : D.X (n - a')),
      p a' ((C.d a a').hom x) y + a.negOnePow • p a x ((D.d (n - a') (n - a)).hom y) = 0)
    (d : ℤ) (x : (C.sc' (d - 1) d (d + 1)).X₂)
    (y : (D.sc' (n - (d + 1)) (n - d) (n - (d - 1))).X₁) :
    p d x ((D.sc' (n - (d + 1)) (n - d) (n - (d - 1))).f.hom y) =
      ((-d.negOnePow) • p (d + 1)) ((C.sc' (d - 1) d (d + 1)).g.hom x) y := by
  simpa only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g, smul_smul, Int.units_mul_self, one_smul,
    smul_neg, Units.neg_smul, LinearMap.neg_apply, LinearMap.smul_apply] using
    congrArg (d.negOnePow • ·) (eq_neg_of_add_eq_zero_right (hp (rfl : d + 1 = d + 1) x y))

/-- Descend a graded Leibniz-compatible family of cochain pairings in complementary degrees `d` and
`n - d` to canonical cohomology. -/
def homologyPairing (p : ∀ d : ℤ, C.X d →ₗ[R] D.X (n - d) →ₗ[R] R)
    (hp : ∀ {a a' : ℤ}, a + 1 = a' → ∀ (x : C.X a) (y : D.X (n - a')),
      p a' ((C.d a a').hom x) y + a.negOnePow • p a x ((D.d (n - a') (n - a)).hom y) = 0)
    (d : ℤ) : C.homology d →ₗ[R] D.homology (n - d) →ₗ[R] R :=
  ((C.sc' (d - 1) d (d + 1)).homologyPairing (D.sc' (n - (d + 1)) (n - d) (n - (d - 1))) (p d)
    (fun x y hy ↦ by rw [sc'_pairing_left C D n p hp d x y, hy, map_zero])
    (fun x y hx ↦ by
      rw [sc'_pairing_right C D n p hp d x y, hx, map_zero, LinearMap.zero_apply])).compl₁₂
    (C.homologyIsoSc' (d - 1) d (d + 1) (by simp) (by simp)).toLinearEquiv.toLinearMap
    (D.homologyIsoSc' (n - (d + 1)) (n - d) (n - (d - 1)) (by simp; omega)
      (by simp; omega)).toLinearEquiv.toLinearMap

/-- On cohomology classes of cocycles, `CochainComplex.homologyPairing` evaluates `p d`. -/
@[simp] theorem homologyPairing_homologyπ (p : ∀ d : ℤ, C.X d →ₗ[R] D.X (n - d) →ₗ[R] R)
    (hp : ∀ {a a' : ℤ}, a + 1 = a' → ∀ (x : C.X a) (y : D.X (n - a')),
      p a' ((C.d a a').hom x) y + a.negOnePow • p a x ((D.d (n - a') (n - a)).hom y) = 0)
    (d : ℤ) (x : C.cycles d) (y : D.cycles (n - d)) :
    C.homologyPairing D n p hp d ((C.homologyπ d).hom x) ((D.homologyπ (n - d)).hom y) =
      p d ((C.iCycles d).hom x) ((D.iCycles (n - d)).hom y) := by
  simp only [homologyPairing, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, Iso.toLinearEquiv_apply]
  rw [← ModuleCat.comp_apply, HomologicalComplex.π_homologyIsoSc'_hom, ModuleCat.comp_apply,
    ← ModuleCat.comp_apply (D.homologyπ _), HomologicalComplex.π_homologyIsoSc'_hom,
    ModuleCat.comp_apply, ShortComplex.homologyPairing_homologyπ,
    ← ModuleCat.comp_apply, HomologicalComplex.cyclesIsoSc'_hom_iCycles,
    ← ModuleCat.comp_apply, HomologicalComplex.cyclesIsoSc'_hom_iCycles]

/-- Over a self-injective commutative ring (`Module.Baer R R`), a degreewise perfect cochain
pairing satisfying the graded Leibniz rule descends to a perfect pairing on cohomology. -/
theorem isPerfPair_homologyPairing_of_baer (hR : Module.Baer R R)
    (p : ∀ d : ℤ, C.X d →ₗ[R] D.X (n - d) →ₗ[R] R) [∀ d, (p d).IsPerfPair]
    (hp : ∀ {a a' : ℤ}, a + 1 = a' → ∀ (x : C.X a) (y : D.X (n - a')),
      p a' ((C.d a a').hom x) y + a.negOnePow • p a x ((D.d (n - a') (n - a)).hom y) = 0)
    (d : ℤ) : (C.homologyPairing D n p hp d).IsPerfPair := by
  have _ := ShortComplex.isPerfPair_homologyPairing_of_baer
    (C.sc' (d - 1) d (d + 1)) (D.sc' (n - (d + 1)) (n - d) (n - (d - 1))) hR
    ((-(d - 1).negOnePow) • p (d - 1)) (p d) ((-d.negOnePow) • p (d + 1))
    (sc'_pairing_left C D n p hp d) (sc'_pairing_right C D n p hp d)
  rw [homologyPairing]; infer_instance

end CommRing

/-- Over a field, a degreewise perfect cochain pairing satisfying the graded Leibniz rule descends
to a perfect pairing on cohomology in every complementary pair of degrees `d` and `n - d`. -/
theorem isPerfPair_homologyPairing {k : Type u} [Field k]
    (C : CochainComplex (ModuleCat.{v} k) ℤ) (D : CochainComplex (ModuleCat.{w} k) ℤ) (n : ℤ)
    (p : ∀ d : ℤ, C.X d →ₗ[k] D.X (n - d) →ₗ[k] k) [∀ d, (p d).IsPerfPair]
    (hp : ∀ {a a' : ℤ}, a + 1 = a' → ∀ (x : C.X a) (y : D.X (n - a')),
      p a' ((C.d a a').hom x) y + a.negOnePow • p a x ((D.d (n - a') (n - a)).hom y) = 0)
    (d : ℤ) : (C.homologyPairing D n p hp d).IsPerfPair :=
  isPerfPair_homologyPairing_of_baer C D n (Module.Baer.of_isSemisimpleRing k k) p hp d

end CochainComplex
