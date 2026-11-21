/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.Algebra.Ring.NegOnePow
public import TauCeti.LinearAlgebra.PerfectPairing.Pi

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

private theorem moduleCatHomologyIso_π.{u'} (U : ShortComplex (ModuleCat.{u'} R)) (x : U.cycles) :
    U.moduleCatHomologyIso.hom.hom (U.homologyπ.hom x) =
      (LinearMap.range U.moduleCatToCycles).mkQ (U.moduleCatCyclesIso.hom.hom x) ∧
    (LinearMap.ker U.g.hom).subtype (U.moduleCatCyclesIso.hom.hom x) = U.iCycles.hom x :=
  ⟨by simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, moduleCatLeftHomologyData_π_hom] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom U.π_moduleCatCyclesIso_hom) x,
   by simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, moduleCatLeftHomologyData_i_hom] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom U.moduleCatCyclesIso_hom_i) x⟩

private theorem homologyMap_π.{u'} {U V : ShortComplex (ModuleCat.{u'} R)} (η : U ⟶ V)
    (z : U.cycles) :
    (ShortComplex.homologyMap η).hom (U.homologyπ.hom z) =
      V.homologyπ.hom ((ShortComplex.cyclesMap η).hom z) ∧
    V.iCycles.hom ((ShortComplex.cyclesMap η).hom z) = η.τ₂.hom (U.iCycles.hom z) :=
  ⟨by simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ShortComplex.homologyπ_naturality η)) z,
   by simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ShortComplex.cyclesMap_i η)) z⟩

variable (S : ShortComplex (ModuleCat.{v} R)) (T : ShortComplex (ModuleCat.{w} R))

private def concreteHomologyPairing (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0) :
    S.moduleCatLeftHomologyData.H →ₗ[R] T.moduleCatLeftHomologyData.H →ₗ[R] R :=
  (p₂.compl₁₂ (LinearMap.ker S.g.hom).subtype (LinearMap.ker T.g.hom).subtype).liftQ₂
    (LinearMap.range S.moduleCatToCycles) (LinearMap.range T.moduleCatToCycles)
    (by rintro _ ⟨x, rfl⟩; exact LinearMap.ext fun y ↦ hf x y.1 y.2)
    (by rintro _ ⟨y, rfl⟩; exact LinearMap.ext fun x ↦ hg x.1 y x.2)

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
@[simp]
theorem homologyPairing_homologyπ (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0)
    (x : S.cycles) (y : T.cycles) :
    S.homologyPairing T p₂ hf hg (S.homologyπ.hom x) (T.homologyπ.hom y) =
      p₂ (S.iCycles.hom x) (T.iCycles.hom y) := by
  rw [homologyPairing, LinearMap.compl₁₂_apply]
  change concreteHomologyPairing S T p₂ hf hg
    (S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom x))
    (T.moduleCatHomologyIso.hom.hom (T.homologyπ.hom y)) = _
  rw [(moduleCatHomologyIso_π S x).1, (moduleCatHomologyIso_π T y).1]
  exact congrArg₂ (fun u v ↦ p₂ u v) (moduleCatHomologyIso_π S x).2 (moduleCatHomologyIso_π T y).2

/-- Flipping `ShortComplex.homologyPairing` exchanges the two short complexes and flips `p₂`. -/
@[simp]
theorem flip_homologyPairing (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0) :
    (S.homologyPairing T p₂ hf hg).flip =
      T.homologyPairing S p₂.flip
        (fun y x hx ↦ by rw [LinearMap.flip_apply]; exact hg x y hx)
        (fun y x hy ↦ by rw [LinearMap.flip_apply]; exact hf x y hy) := by
  ext b a
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).1 inferInstance a
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).1 inferInstance b
  rw [← show S.homologyπ.hom x = a from hx, ← show T.homologyπ.hom y = b from hy,
    LinearMap.flip_apply, homologyPairing_homologyπ, homologyPairing_homologyπ,
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
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).1 inferInstance a
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective T'.homologyπ).1 inferInstance b
  rw [← show S.homologyπ.hom x = a from hx, ← show T'.homologyπ.hom y = b from hy,
    (homologyMap_π φ x).1, (homologyMap_π ψ y).1, homologyPairing_homologyπ,
    homologyPairing_homologyπ, (homologyMap_π φ x).2, (homologyMap_π ψ y).2, hφψ]

private theorem concreteHomologyPairing_bijective_left (hR : Module.Baer R R)
    (p₁ : S.X₁ →ₗ[R] T.X₃ →ₗ[R] R) (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (p₃ : S.X₃ →ₗ[R] T.X₁ →ₗ[R] R) [p₁.IsPerfPair] [p₂.IsPerfPair] [p₃.IsPerfPair]
    (h₁ : ∀ (x : S.X₁) (y : T.X₂), p₂ (S.f.hom x) y = p₁ x (T.g.hom y))
    (h₃ : ∀ (x : S.X₂) (y : T.X₁), p₂ x (T.f.hom y) = p₃ (S.g.hom x) y)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0) :
    Bijective (concreteHomologyPairing S T p₂ hf hg) := by
  refine ⟨?_, fun φ ↦ ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range S.moduleCatToCycles) q
    have hc : LinearMap.ker T.g.hom ≤ LinearMap.ker (p₂ c.1) := fun y hy ↦
      DFunLike.congr_fun hq ((LinearMap.range T.moduleCatToCycles).mkQ ⟨y, hy⟩)
    obtain ⟨μ, hμ⟩ := hR.extension_property (LinearMap.range T.g.hom).subtype Subtype.val_injective
      (((LinearMap.ker T.g.hom).liftQ (p₂ c.1) hc).comp T.g.hom.quotKerEquivRange.symm.toLinearMap)
    have hμg (y : T.X₂) : μ (T.g.hom y) = p₂ c.1 y := by
      have hr : (LinearMap.range T.g.hom).subtype (T.g.hom.rangeRestrict y) = T.g.hom y := rfl
      have hqeq : T.g.hom.quotKerEquivRange.symm (T.g.hom.rangeRestrict y) =
          Submodule.Quotient.mk y := T.g.hom.quotKerEquivRange.symm_apply_eq.mpr rfl
      rw [← hr, ← LinearMap.comp_apply, hμ]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hqeq, Submodule.liftQ_apply]
    refine (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).mpr
      ⟨p₁.toPerfPair.symm μ, Subtype.ext <| (LinearMap.IsPerfPair.bijective_left p₂).injective <|
        LinearMap.ext fun y ↦ ?_⟩
    change p₂ (S.f.hom (p₁.toPerfPair.symm μ)) y = p₂ c.1 y
    rw [h₁, ← hμg]; exact DFunLike.congr_fun (p₁.apply_symm_toPerfPair_self μ) (T.g.hom y)
  · let φ₀ := φ.comp (LinearMap.range T.moduleCatToCycles).mkQ
    obtain ⟨Φ, hΦ⟩ := hR.extension_property (LinearMap.ker T.g.hom).subtype Subtype.val_injective φ₀
    let x : S.X₂ := p₂.toPerfPair.symm Φ
    have hxΦ : p₂ x = Φ := p₂.apply_symm_toPerfPair_self Φ
    have hx : x ∈ LinearMap.ker S.g.hom :=
      (LinearMap.IsPerfPair.bijective_left p₃).injective <| by
        rw [map_zero]; ext y₁
        have hmem : (LinearMap.ker T.g.hom).subtype (T.moduleCatToCycles y₁) = T.f.hom y₁ := rfl
        have hz : (LinearMap.range T.moduleCatToCycles).mkQ (T.moduleCatToCycles y₁) = 0 :=
          (Submodule.Quotient.mk_eq_zero _).mpr ⟨y₁, rfl⟩
        rw [LinearMap.zero_apply, ← h₃, hxΦ, ← hmem, ← LinearMap.comp_apply, hΦ]
        simp only [φ₀, LinearMap.comp_apply, hz, map_zero]
    refine ⟨(LinearMap.range S.moduleCatToCycles).mkQ ⟨x, hx⟩, LinearMap.ext fun q ↦ ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range T.moduleCatToCycles) q
    change p₂ x y.1 = φ ((LinearMap.range T.moduleCatToCycles).mkQ y)
    rw [hxΦ]; exact DFunLike.congr_fun hΦ y

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
    { bijective_left := concreteHomologyPairing_bijective_left S T hR p₁ p₂ p₃ h₁ h₃ hf hg
      bijective_right := by
        have hflip : (concreteHomologyPairing S T p₂ hf hg).flip =
            concreteHomologyPairing T S p₂.flip (fun y x hx ↦ hg x y hx)
              (fun y x hy ↦ hf x y hy) := by
          ext b a
          induction a using Submodule.Quotient.induction_on with
          | H _ => induction b using Submodule.Quotient.induction_on with | H _ => rfl
        rw [hflip]
        exact concreteHomologyPairing_bijective_left T S hR p₃.flip p₂.flip p₁.flip
          (fun y x ↦ h₃ x y) (fun y x ↦ h₁ x y) _ _ }
  rw [homologyPairing]; infer_instance

end CommRing

private theorem moduleBaer_of_field (k : Type u) [Field k] : Module.Baer k k := by
  intro I g; rcases I.eq_bot_or_top with rfl | rfl
  · refine ⟨0, fun x hx ↦ ?_⟩
    obtain rfl : x = 0 := (Submodule.mem_bot k).mp hx; exact (map_zero g).symm
  · exact ⟨g.comp Submodule.topEquiv.symm.toLinearMap, fun _ _ ↦ rfl⟩

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
  isPerfPair_homologyPairing_of_baer S T (moduleBaer_of_field k) p₁ p₂ p₃ h₁ h₃ hf hg

end CategoryTheory.ShortComplex

namespace CochainComplex

open CategoryTheory

section CommRing

variable {R : Type u} [CommRing R]

private theorem sc'_π.{u'} (K : CochainComplex (ModuleCat.{u'} R) ℤ) (i j k : ℤ)
    (hij : (ComplexShape.up ℤ).prev j = i) (hjk : (ComplexShape.up ℤ).next j = k)
    (z : K.cycles j) :
    (K.homologyIsoSc' i j k hij hjk).toLinearEquiv ((K.homologyπ j).hom z) =
      (K.sc' i j k).homologyπ.hom ((K.cyclesIsoSc' i j k hij hjk).hom.hom z) ∧
    (K.sc' i j k).iCycles.hom ((K.cyclesIsoSc' i j k hij hjk).hom.hom z) = (K.iCycles j).hom z :=
  ⟨by simpa only [Iso.toLinearEquiv_apply, ModuleCat.hom_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (K.π_homologyIsoSc'_hom i j k hij hjk)) z,
   by simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (K.cyclesIsoSc'_hom_iCycles i j k hij hjk)) z⟩

variable (C : CochainComplex (ModuleCat.{v} R) ℤ) (D : CochainComplex (ModuleCat.{w} R) ℤ) (n : ℤ)

/-- Descend a graded Leibniz-compatible family of cochain pairings in complementary degrees `d` and
`n - d` to canonical cohomology. -/
def homologyPairing (p : ∀ d : ℤ, C.X d →ₗ[R] D.X (n - d) →ₗ[R] R)
    (hp : ∀ {a a' : ℤ}, a + 1 = a' → ∀ (x : C.X a) (y : D.X (n - a')),
      p a' ((C.d a a').hom x) y + a.negOnePow • p a x ((D.d (n - a') (n - a)).hom y) = 0)
    (d : ℤ) : C.homology d →ₗ[R] D.homology (n - d) →ₗ[R] R :=
  ((C.sc' (d - 1) d (d + 1)).homologyPairing (D.sc' (n - (d + 1)) (n - d) (n - (d - 1))) (p d)
    (fun x y hy ↦ by
      simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
        HomologicalComplex.shortComplexFunctor'_obj_g] at hy ⊢
      simpa only [hy, map_zero, smul_zero, add_zero] using hp (by omega : (d - 1) + 1 = d) x y)
    (fun x y hx ↦ by
      simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
        HomologicalComplex.shortComplexFunctor'_obj_g] at hx ⊢
      have h := hp (rfl : d + 1 = d + 1) x y
      rw [hx, map_zero, LinearMap.zero_apply, zero_add] at h
      simpa only [smul_smul, Int.units_mul_self, one_smul, smul_zero] using
        congrArg (d.negOnePow • ·) h)).compl₁₂
    (C.homologyIsoSc' (d - 1) d (d + 1) (by simp) (by simp)).toLinearEquiv.toLinearMap
    (D.homologyIsoSc' (n - (d + 1)) (n - d) (n - (d - 1)) (by simp; omega)
      (by simp; omega)).toLinearEquiv.toLinearMap

/-- On cohomology classes of cocycles, `CochainComplex.homologyPairing` evaluates `p d`. -/
@[simp]
theorem homologyPairing_homologyπ (p : ∀ d : ℤ, C.X d →ₗ[R] D.X (n - d) →ₗ[R] R)
    (hp : ∀ {a a' : ℤ}, a + 1 = a' → ∀ (x : C.X a) (y : D.X (n - a')),
      p a' ((C.d a a').hom x) y + a.negOnePow • p a x ((D.d (n - a') (n - a)).hom y) = 0)
    (d : ℤ) (x : C.cycles d) (y : D.cycles (n - d)) :
    C.homologyPairing D n p hp d ((C.homologyπ d).hom x) ((D.homologyπ (n - d)).hom y) =
      p d ((C.iCycles d).hom x) ((D.iCycles (n - d)).hom y) := by
  have hC := sc'_π C (d - 1) d (d + 1) (by simp) (by simp) x
  have hD := sc'_π D (n - (d + 1)) (n - d) (n - (d - 1)) (by simp; omega) (by simp; omega) y
  rw [homologyPairing, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    hC.1, hD.1, ShortComplex.homologyPairing_homologyπ, hC.2, hD.2]

/-- Over a self-injective commutative ring (`Module.Baer R R`), a degreewise perfect cochain
pairing satisfying the graded Leibniz rule descends to a perfect pairing on cohomology. -/
theorem isPerfPair_homologyPairing_of_baer (hR : Module.Baer R R)
    (p : ∀ d : ℤ, C.X d →ₗ[R] D.X (n - d) →ₗ[R] R) [∀ d, (p d).IsPerfPair]
    (hp : ∀ {a a' : ℤ}, a + 1 = a' → ∀ (x : C.X a) (y : D.X (n - a')),
      p a' ((C.d a a').hom x) y + a.negOnePow • p a x ((D.d (n - a') (n - a)).hom y) = 0)
    (d : ℤ) : (C.homologyPairing D n p hp d).IsPerfPair := by
  let S := C.sc' (d - 1) d (d + 1); let T := D.sc' (n - (d + 1)) (n - d) (n - (d - 1))
  let p₁ : S.X₁ →ₗ[R] T.X₃ →ₗ[R] R := (-(d - 1).negOnePow) • p (d - 1)
  let p₃ : S.X₃ →ₗ[R] T.X₁ →ₗ[R] R := (-d.negOnePow) • p (d + 1)
  have _ : p₁.IsPerfPair := inferInstanceAs ((-((d - 1).negOnePow)) • p (d - 1)).IsPerfPair
  have _ : p₃.IsPerfPair := inferInstanceAs ((-d.negOnePow) • p (d + 1)).IsPerfPair
  rw [homologyPairing]
  have _ := ShortComplex.isPerfPair_homologyPairing_of_baer S T hR p₁ (p d) p₃
    (fun x y ↦ by
      simpa only [S, T, p₁, HomologicalComplex.shortComplexFunctor'_obj_f,
        HomologicalComplex.shortComplexFunctor'_obj_g, Units.neg_smul, LinearMap.neg_apply,
        LinearMap.smul_apply] using
        eq_neg_of_add_eq_zero_left (hp (by omega : (d - 1) + 1 = d) x y))
    (fun x y ↦ by
      simpa only [S, T, p₃, HomologicalComplex.shortComplexFunctor'_obj_f,
        HomologicalComplex.shortComplexFunctor'_obj_g, smul_smul, Int.units_mul_self, one_smul,
        smul_neg, Units.neg_smul, LinearMap.neg_apply, LinearMap.smul_apply] using
        congrArg (d.negOnePow • ·) (eq_neg_of_add_eq_zero_right (hp (rfl : d + 1 = d + 1) x y)))
  infer_instance

end CommRing

/-- Over a field, a degreewise perfect cochain pairing satisfying the graded Leibniz rule descends
to a perfect pairing on cohomology in every complementary pair of degrees `d` and `n - d`. -/
theorem isPerfPair_homologyPairing {k : Type u} [Field k]
    (C : CochainComplex (ModuleCat.{v} k) ℤ) (D : CochainComplex (ModuleCat.{w} k) ℤ) (n : ℤ)
    (p : ∀ d : ℤ, C.X d →ₗ[k] D.X (n - d) →ₗ[k] k) [∀ d, (p d).IsPerfPair]
    (hp : ∀ {a a' : ℤ}, a + 1 = a' → ∀ (x : C.X a) (y : D.X (n - a')),
      p a' ((C.d a a').hom x) y + a.negOnePow • p a x ((D.d (n - a') (n - a)).hom y) = 0)
    (d : ℤ) : (C.homologyPairing D n p hp d).IsPerfPair :=
  isPerfPair_homologyPairing_of_baer C D n (ShortComplex.moduleBaer_of_field k) p hp d

end CochainComplex
