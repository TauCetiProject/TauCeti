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

Let `S : X₁ ⟶ X₂ ⟶ X₃` and `T : Y₁ ⟶ Y₂ ⟶ Y₃` be short complexes of modules over a commutative
ring `R`. A bilinear pairing `p₂ : X₂ →ₗ[R] Y₂ →ₗ[R] R` that pairs boundaries on each side
orthogonally against cycles on the other descends canonically to a bilinear pairing
`S.homologyPairing T p₂ hf hg : S.homology →ₗ[R] T.homology →ₗ[R] R`.

When `R` is self-injective (`Module.Baer R R`, in particular when `R` is a field) and `p₂` sits in
a compatible triple of perfect pairings `p₁ : X₁ × Y₃ → R`, `p₂ : X₂ × Y₂ → R`,
`p₃ : X₃ × Y₁ → R` intertwining `(S.f, T.g)` and `(S.g, T.f)`, the descended pairing on homology
is again a perfect pairing (`LinearMap.IsPerfPair`), with no finite-dimensionality assumption:
injectivity uses extension of functionals along `im T.g ↪ Y₃` and surjectivity of `p₁`, while
surjectivity extends functionals from `ker T.g` to `Y₂` and checks closedness via injectivity of
`p₃`.

Specializing to complementary short complexes `C.sc' (d - 1) d (d + 1)` and
`D.sc' (n - (d + 1)) (n - d) (n - (d - 1))` of cochain complexes `C` and `D` yields the descent of
graded Leibniz-compatible cochain pairings to cohomology perfect pairings.

## Main definitions and results

* `CategoryTheory.ShortComplex.homologyPairing`: bilinear pairing descended to `S.homology` and
  `T.homology`, evaluated on cycle classes by `homologyPairing_homologyπ` and natural with respect
  to short-complex morphisms (`homologyPairing_homologyMap`).
* `CategoryTheory.ShortComplex.isPerfPair_homologyPairing_of_baer` and
  `CategoryTheory.ShortComplex.isPerfPair_homologyPairing`: perfectness of the descended pairing
  over a self-injective commutative ring and over a field.
* `CochainComplex.homologyPairing`, `CochainComplex.isPerfPair_homologyPairing_of_baer`, and
  `CochainComplex.isPerfPair_homologyPairing`: cochain-complex specialization in complementary
  degrees `d` and `n - d`.

## References

* A. Dold, *Lectures on Algebraic Topology*, Chapter VI, §7, for Kronecker and homology pairings on
  subquotients of chain complexes.
-/

public section
noncomputable section

open CategoryTheory Function

universe u v w

namespace CategoryTheory.ShortComplex

section CommRing

variable {R : Type u} [CommRing R]
  (S : ShortComplex (ModuleCat.{v} R)) (T : ShortComplex (ModuleCat.{w} R))

private def concreteHomologyPairing (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0) :
    S.moduleCatLeftHomologyData.H →ₗ[R] T.moduleCatLeftHomologyData.H →ₗ[R] R :=
  (p₂.compl₁₂ (LinearMap.ker S.g.hom).subtype (LinearMap.ker T.g.hom).subtype).liftQ₂
    (LinearMap.range S.moduleCatToCycles) (LinearMap.range T.moduleCatToCycles)
    (by
      rintro _ ⟨x, rfl⟩
      apply LinearMap.ext fun y ↦ ?_
      exact hf x y.1 y.2)
    (by
      rintro _ ⟨y, rfl⟩
      apply LinearMap.ext fun x ↦ ?_
      exact hg x.1 y x.2)

private theorem concreteHomologyPairing_mk (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0)
    (x : LinearMap.ker S.g.hom) (y : LinearMap.ker T.g.hom) :
    concreteHomologyPairing S T p₂ hf hg
        ((LinearMap.range S.moduleCatToCycles).mkQ x)
        ((LinearMap.range T.moduleCatToCycles).mkQ y) =
      p₂ ((LinearMap.ker S.g.hom).subtype x) ((LinearMap.ker T.g.hom).subtype y) :=
  (rfl)

/-- The bilinear pairing on homology induced by a middle-term pairing `p₂` whose left and right
restrictions vanish against boundaries of the opposite short complex. -/
def homologyPairing (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0) :
    S.homology →ₗ[R] T.homology →ₗ[R] R :=
  (concreteHomologyPairing S T p₂ hf hg).compl₁₂
    S.moduleCatHomologyIso.toLinearEquiv.toLinearMap
    T.moduleCatHomologyIso.toLinearEquiv.toLinearMap

/-- On classes of cycles, `ShortComplex.homologyPairing` evaluates `p₂` on the underlying elements
of the middle terms. -/
@[simp]
theorem homologyPairing_homologyπ (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0)
    (x : S.cycles) (y : T.cycles) :
    S.homologyPairing T p₂ hf hg (S.homologyπ.hom x) (T.homologyπ.hom y) =
      p₂ (S.iCycles.hom x) (T.iCycles.hom y) := by
  have hx : S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom x) =
      (LinearMap.range S.moduleCatToCycles).mkQ (S.moduleCatCyclesIso.hom.hom x) := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, moduleCatLeftHomologyData_π_hom] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom S.π_moduleCatCyclesIso_hom) x
  have hy : T.moduleCatHomologyIso.hom.hom (T.homologyπ.hom y) =
      (LinearMap.range T.moduleCatToCycles).mkQ (T.moduleCatCyclesIso.hom.hom y) := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, moduleCatLeftHomologyData_π_hom] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom T.π_moduleCatCyclesIso_hom) y
  have hxi :
      (LinearMap.ker S.g.hom).subtype (S.moduleCatCyclesIso.hom.hom x) = S.iCycles.hom x := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, moduleCatLeftHomologyData_i_hom] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom S.moduleCatCyclesIso_hom_i) x
  have hyi :
      (LinearMap.ker T.g.hom).subtype (T.moduleCatCyclesIso.hom.hom y) = T.iCycles.hom y := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, moduleCatLeftHomologyData_i_hom] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom T.moduleCatCyclesIso_hom_i) y
  rw [homologyPairing, LinearMap.compl₁₂_apply]
  -- `Iso.toLinearEquiv` on `ModuleCat` evaluates via `.hom.hom`.
  change concreteHomologyPairing S T p₂ hf hg
    (S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom x))
    (T.moduleCatHomologyIso.hom.hom (T.homologyπ.hom y)) = _
  rw [hx, hy, concreteHomologyPairing_mk, hxi, hyi]

/-- Flipping `ShortComplex.homologyPairing` exchanges the two short complexes and flips `p₂`. -/
@[simp]
theorem flip_homologyPairing (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0) :
    (S.homologyPairing T p₂ hf hg).flip =
      T.homologyPairing S p₂.flip
        (fun y x hx ↦ by rw [LinearMap.flip_apply]; exact hg x y hx)
        (fun y x hy ↦ by rw [LinearMap.flip_apply]; exact hf x y hy) := by
  apply LinearMap.ext fun b ↦ LinearMap.ext fun a ↦ ?_
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).1 inferInstance a
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).1 inferInstance b
  have hx' : S.homologyπ.hom x = a := hx
  have hy' : T.homologyπ.hom y = b := hy
  rw [← hx', ← hy', LinearMap.flip_apply, homologyPairing_homologyπ, homologyPairing_homologyπ,
    LinearMap.flip_apply]

/-- `ShortComplex.homologyPairing` is natural with respect to morphisms of short complexes whose
middle components are adjoint under the pairings. -/
theorem homologyPairing_homologyMap {S' : ShortComplex (ModuleCat.{v} R)}
    {T' : ShortComplex (ModuleCat.{w} R)}
    (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
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
  have hx' : S.homologyπ.hom x = a := hx
  have hy' : T'.homologyπ.hom y = b := hy
  rw [← hx', ← hy']
  have hφ : (ShortComplex.homologyMap φ).hom (S.homologyπ.hom x) =
      S'.homologyπ.hom ((ShortComplex.cyclesMap φ).hom x) := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ShortComplex.homologyπ_naturality φ)) x
  have hψ : (ShortComplex.homologyMap ψ).hom (T'.homologyπ.hom y) =
      T.homologyπ.hom ((ShortComplex.cyclesMap ψ).hom y) := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ShortComplex.homologyπ_naturality ψ)) y
  have hφi : S'.iCycles.hom ((ShortComplex.cyclesMap φ).hom x) = φ.τ₂.hom (S.iCycles.hom x) := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ShortComplex.cyclesMap_i φ)) x
  have hψi : T.iCycles.hom ((ShortComplex.cyclesMap ψ).hom y) = ψ.τ₂.hom (T'.iCycles.hom y) := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ShortComplex.cyclesMap_i ψ)) y
  rw [hφ, hψ, homologyPairing_homologyπ, homologyPairing_homologyπ, hφi, hψi, hφψ]

private theorem concreteHomologyPairing_bijective_left (hR : Module.Baer R R)
    (p₁ : S.X₁ →ₗ[R] T.X₃ →ₗ[R] R) (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (p₃ : S.X₃ →ₗ[R] T.X₁ →ₗ[R] R)
    [p₁.IsPerfPair] [p₂.IsPerfPair] [p₃.IsPerfPair]
    (h₁ : ∀ (x : S.X₁) (y : T.X₂), p₂ (S.f.hom x) y = p₁ x (T.g.hom y))
    (h₃ : ∀ (x : S.X₂) (y : T.X₁), p₂ x (T.f.hom y) = p₃ (S.g.hom x) y)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0)
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0) :
    Bijective (concreteHomologyPairing S T p₂ hf hg) := by
  refine ⟨?_, fun φ ↦ ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range S.moduleCatToCycles) q
    have hc : LinearMap.ker T.g.hom ≤ LinearMap.ker (p₂ c.1) := by
      intro y hy
      rw [LinearMap.mem_ker]
      have hval := DFunLike.congr_fun hq ((LinearMap.range T.moduleCatToCycles).mkQ ⟨y, hy⟩)
      rw [concreteHomologyPairing_mk] at hval
      exact hval
    let φRange : LinearMap.range T.g.hom →ₗ[R] R :=
      ((LinearMap.ker T.g.hom).liftQ (p₂ c.1) hc).comp
        (T.g.hom.quotKerEquivRange.symm.toLinearMap)
    obtain ⟨μ, hμ⟩ := hR.extension_property (LinearMap.range T.g.hom).subtype
      Subtype.val_injective φRange
    have hμg (y : T.X₂) : μ (T.g.hom y) = p₂ c.1 y := by
      have hr : (LinearMap.range T.g.hom).subtype (T.g.hom.rangeRestrict y) = T.g.hom y := rfl
      rw [← hr, ← LinearMap.comp_apply, hμ]
      have hqeq : T.g.hom.quotKerEquivRange.symm (T.g.hom.rangeRestrict y) =
          Submodule.Quotient.mk y :=
        T.g.hom.quotKerEquivRange.symm_apply_eq.mpr rfl
      simp only [φRange, LinearMap.comp_apply, LinearEquiv.coe_coe, hqeq, Submodule.liftQ_apply]
    let x₁ : S.X₁ := p₁.toPerfPair.symm μ
    have hx₁ : S.f.hom x₁ = c.1 := by
      apply (LinearMap.IsPerfPair.bijective_left p₂).injective
      apply LinearMap.ext fun y ↦ ?_
      rw [h₁, ← hμg]
      exact DFunLike.congr_fun (p₁.apply_symm_toPerfPair_self μ) (T.g.hom y)
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).mpr
      ⟨x₁, Subtype.ext hx₁⟩
  · let φ₀ : LinearMap.ker T.g.hom →ₗ[R] R :=
      φ.comp (LinearMap.range T.moduleCatToCycles).mkQ
    obtain ⟨Φ, hΦ⟩ := hR.extension_property (LinearMap.ker T.g.hom).subtype
      Subtype.val_injective φ₀
    let x : S.X₂ := p₂.toPerfPair.symm Φ
    have hxΦ : p₂ x = Φ := p₂.apply_symm_toPerfPair_self Φ
    have hx : x ∈ LinearMap.ker S.g.hom := by
      rw [LinearMap.mem_ker]
      apply (LinearMap.IsPerfPair.bijective_left p₃).injective
      rw [map_zero]
      apply LinearMap.ext fun y₁ ↦ ?_
      rw [LinearMap.zero_apply, ← h₃, hxΦ]
      have hmem : (LinearMap.ker T.g.hom).subtype (T.moduleCatToCycles y₁) = T.f.hom y₁ := rfl
      rw [← hmem, ← LinearMap.comp_apply, hΦ]
      simp only [φ₀, LinearMap.comp_apply]
      have hzero : (LinearMap.range T.moduleCatToCycles).mkQ (T.moduleCatToCycles y₁) = 0 := by
        rw [Submodule.mkQ_apply]
        exact (Submodule.Quotient.mk_eq_zero (LinearMap.range T.moduleCatToCycles)).mpr ⟨y₁, rfl⟩
      rw [hzero, map_zero]
    refine ⟨(LinearMap.range S.moduleCatToCycles).mkQ ⟨x, hx⟩, LinearMap.ext fun q ↦ ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range T.moduleCatToCycles) q
    rw [concreteHomologyPairing_mk, Submodule.coe_subtype, hxΦ]
    exact DFunLike.congr_fun hΦ y

/-- Over a self-injective commutative ring (`Module.Baer R R`), a triple of compatible perfect
pairings between two short complexes descends to a perfect pairing on homology. -/
theorem isPerfPair_homologyPairing_of_baer (hR : Module.Baer R R)
    (p₁ : S.X₁ →ₗ[R] T.X₃ →ₗ[R] R) (p₂ : S.X₂ →ₗ[R] T.X₂ →ₗ[R] R)
    (p₃ : S.X₃ →ₗ[R] T.X₁ →ₗ[R] R)
    [p₁.IsPerfPair] [p₂.IsPerfPair] [p₃.IsPerfPair]
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
            concreteHomologyPairing T S p₂.flip
              (fun y x hx ↦ by rw [LinearMap.flip_apply]; exact hg x y hx)
              (fun y x hy ↦ by rw [LinearMap.flip_apply]; exact hf x y hy) := by
          apply LinearMap.ext fun b ↦ LinearMap.ext fun a ↦ ?_
          induction a using Submodule.Quotient.induction_on with
          | H x =>
            induction b using Submodule.Quotient.induction_on with
            | H y => rfl
        rw [hflip]
        exact concreteHomologyPairing_bijective_left T S hR p₃.flip p₂.flip p₁.flip
          (fun y x ↦ by rw [LinearMap.flip_apply, LinearMap.flip_apply]; exact h₃ x y)
          (fun y x ↦ by rw [LinearMap.flip_apply, LinearMap.flip_apply]; exact h₁ x y) _ _ }
  rw [homologyPairing]
  infer_instance

end CommRing

section Field

private theorem moduleBaer_of_field (k : Type u) [Field k] : Module.Baer k k := by
  intro I g
  rcases I.eq_bot_or_top with rfl | rfl
  · refine ⟨0, fun x hx ↦ ?_⟩
    obtain rfl : x = 0 := (Submodule.mem_bot k).mp hx
    exact (map_zero g).symm
  · exact ⟨g.comp Submodule.topEquiv.symm.toLinearMap, fun _ _ ↦ rfl⟩

/-- Over a field, a triple of compatible perfect pairings between two short complexes descends to a
perfect pairing on homology. -/
theorem isPerfPair_homologyPairing {k : Type u} [Field k]
    (S : ShortComplex (ModuleCat.{v} k)) (T : ShortComplex (ModuleCat.{w} k))
    (p₁ : S.X₁ →ₗ[k] T.X₃ →ₗ[k] k) (p₂ : S.X₂ →ₗ[k] T.X₂ →ₗ[k] k)
    (p₃ : S.X₃ →ₗ[k] T.X₁ →ₗ[k] k)
    [p₁.IsPerfPair] [p₂.IsPerfPair] [p₃.IsPerfPair]
    (h₁ : ∀ (x : S.X₁) (y : T.X₂), p₂ (S.f.hom x) y = p₁ x (T.g.hom y))
    (h₃ : ∀ (x : S.X₂) (y : T.X₁), p₂ x (T.f.hom y) = p₃ (S.g.hom x) y)
    (hf : ∀ (x : S.X₁) (y : T.X₂), T.g.hom y = 0 → p₂ (S.f.hom x) y = 0 :=
      fun x y hy ↦ by rw [h₁, hy, map_zero])
    (hg : ∀ (x : S.X₂) (y : T.X₁), S.g.hom x = 0 → p₂ x (T.f.hom y) = 0 :=
      fun x y hx ↦ by rw [h₃, hx, map_zero, LinearMap.zero_apply]) :
    (S.homologyPairing T p₂ hf hg).IsPerfPair :=
  isPerfPair_homologyPairing_of_baer S T (moduleBaer_of_field k) p₁ p₂ p₃ h₁ h₃ hf hg

end Field

end CategoryTheory.ShortComplex

namespace CochainComplex

open CategoryTheory

section CommRing

variable {R : Type u} [CommRing R]
  (C : CochainComplex (ModuleCat.{v} R) ℤ) (D : CochainComplex (ModuleCat.{w} R) ℤ)
  (n : ℤ)

/-- Descend a graded Leibniz-compatible family of cochain pairings in complementary degrees `d` and
`n - d` to canonical cohomology. -/
def homologyPairing (p : ∀ d : ℤ, C.X d →ₗ[R] D.X (n - d) →ₗ[R] R)
    (hp : ∀ {a a' : ℤ}, a + 1 = a' → ∀ (x : C.X a) (y : D.X (n - a')),
      p a' ((C.d a a').hom x) y + a.negOnePow • p a x ((D.d (n - a') (n - a)).hom y) = 0)
    (d : ℤ) :
    C.homology d →ₗ[R] D.homology (n - d) →ₗ[R] R :=
  let S := C.sc' (d - 1) d (d + 1)
  let T := D.sc' (n - (d + 1)) (n - d) (n - (d - 1))
  (S.homologyPairing T (p d)
    (fun x y hy ↦ by
      simp only [S, T, HomologicalComplex.shortComplexFunctor'_obj_f,
        HomologicalComplex.shortComplexFunctor'_obj_g] at hy ⊢
      have h := hp (by omega : (d - 1) + 1 = d) x y
      rw [hy, map_zero, smul_zero, add_zero] at h
      exact h)
    (fun x y hx ↦ by
      simp only [S, T, HomologicalComplex.shortComplexFunctor'_obj_f,
        HomologicalComplex.shortComplexFunctor'_obj_g] at hx ⊢
      have h := hp (rfl : d + 1 = d + 1) x y
      rw [hx, map_zero, LinearMap.zero_apply, zero_add] at h
      simpa only [smul_smul, Int.units_mul_self, one_smul, smul_zero] using
        congrArg (d.negOnePow • ·) h)).compl₁₂
    (C.homologyIsoSc' (d - 1) d (d + 1) (by simp) (by simp)).toLinearEquiv.toLinearMap
    (D.homologyIsoSc' (n - (d + 1)) (n - d) (n - (d - 1)) (by simp; omega)
      (by simp; omega)).toLinearEquiv.toLinearMap

/-- On cohomology classes of cocycles, `CochainComplex.homologyPairing` evaluates the degree-`d`
cochain pairing on the representing cocycles. -/
@[simp]
theorem homologyPairing_homologyπ (p : ∀ d : ℤ, C.X d →ₗ[R] D.X (n - d) →ₗ[R] R)
    (hp : ∀ {a a' : ℤ}, a + 1 = a' → ∀ (x : C.X a) (y : D.X (n - a')),
      p a' ((C.d a a').hom x) y + a.negOnePow • p a x ((D.d (n - a') (n - a)).hom y) = 0)
    (d : ℤ) (x : C.cycles d) (y : D.cycles (n - d)) :
    C.homologyPairing D n p hp d ((C.homologyπ d).hom x) ((D.homologyπ (n - d)).hom y) =
      p d ((C.iCycles d).hom x) ((D.iCycles (n - d)).hom y) := by
  let eC := C.cyclesIsoSc' (d - 1) d (d + 1) (by simp) (by simp)
  let eD := D.cyclesIsoSc' (n - (d + 1)) (n - d) (n - (d - 1)) (by simp; omega) (by simp; omega)
  have hx : (C.homologyIsoSc' (d - 1) d (d + 1) (by simp) (by simp)).toLinearEquiv
      ((C.homologyπ d).hom x) = (C.sc' (d - 1) d (d + 1)).homologyπ.hom (eC.hom.hom x) := by
    simpa only [Iso.toLinearEquiv_apply, ModuleCat.hom_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (C.π_homologyIsoSc'_hom (d - 1) d (d + 1) (by simp) (by simp))) x
  have hy : (D.homologyIsoSc' (n - (d + 1)) (n - d) (n - (d - 1)) (by simp; omega)
      (by simp; omega)).toLinearEquiv ((D.homologyπ (n - d)).hom y) =
      (D.sc' (n - (d + 1)) (n - d) (n - (d - 1))).homologyπ.hom (eD.hom.hom y) := by
    simpa only [Iso.toLinearEquiv_apply, ModuleCat.hom_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (D.π_homologyIsoSc'_hom (n - (d + 1)) (n - d) (n - (d - 1)) (by simp; omega)
          (by simp; omega))) y
  have hxi : (C.sc' (d - 1) d (d + 1)).iCycles.hom (eC.hom.hom x) = (C.iCycles d).hom x := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (C.cyclesIsoSc'_hom_iCycles (d - 1) d (d + 1) (by simp) (by simp))) x
  have hyi : (D.sc' (n - (d + 1)) (n - d) (n - (d - 1))).iCycles.hom (eD.hom.hom y) =
      (D.iCycles (n - d)).hom y := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (D.cyclesIsoSc'_hom_iCycles (n - (d + 1)) (n - d) (n - (d - 1)) (by simp; omega)
          (by simp; omega))) y
  rw [homologyPairing, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    hx, hy, ShortComplex.homologyPairing_homologyπ, hxi, hyi]

/-- Over a self-injective commutative ring (`Module.Baer R R`), a degreewise perfect cochain
pairing satisfying the graded Leibniz rule descends to a perfect pairing on cohomology. -/
theorem isPerfPair_homologyPairing_of_baer (hR : Module.Baer R R)
    (p : ∀ d : ℤ, C.X d →ₗ[R] D.X (n - d) →ₗ[R] R) [∀ d, (p d).IsPerfPair]
    (hp : ∀ {a a' : ℤ}, a + 1 = a' → ∀ (x : C.X a) (y : D.X (n - a')),
      p a' ((C.d a a').hom x) y + a.negOnePow • p a x ((D.d (n - a') (n - a)).hom y) = 0)
    (d : ℤ) :
    (C.homologyPairing D n p hp d).IsPerfPair := by
  let S := C.sc' (d - 1) d (d + 1)
  let T := D.sc' (n - (d + 1)) (n - d) (n - (d - 1))
  let p₁ : S.X₁ →ₗ[R] T.X₃ →ₗ[R] R := (-(d - 1).negOnePow) • p (d - 1)
  let p₃ : S.X₃ →ₗ[R] T.X₁ →ₗ[R] R := (-d.negOnePow) • p (d + 1)
  have _ : p₁.IsPerfPair := inferInstanceAs ((-((d - 1).negOnePow)) • p (d - 1)).IsPerfPair
  have _ : p₃.IsPerfPair := inferInstanceAs ((-d.negOnePow) • p (d + 1)).IsPerfPair
  have _ : (S.homologyPairing T (p d)
      (fun x y hy ↦ by
        simp only [S, T, HomologicalComplex.shortComplexFunctor'_obj_f,
          HomologicalComplex.shortComplexFunctor'_obj_g] at hy ⊢
        have h := hp (by omega : (d - 1) + 1 = d) x y
        rw [hy, map_zero, smul_zero, add_zero] at h
        exact h)
      (fun x y hx ↦ by
        simp only [S, T, HomologicalComplex.shortComplexFunctor'_obj_f,
          HomologicalComplex.shortComplexFunctor'_obj_g] at hx ⊢
        have h := hp (rfl : d + 1 = d + 1) x y
        rw [hx, map_zero, LinearMap.zero_apply, zero_add] at h
        simpa only [smul_smul, Int.units_mul_self, one_smul, smul_zero] using
          congrArg (d.negOnePow • ·) h)).IsPerfPair :=
    ShortComplex.isPerfPair_homologyPairing_of_baer S T hR p₁ (p d) p₃
      (fun x y ↦ by
        simp only [S, T, HomologicalComplex.shortComplexFunctor'_obj_f,
          HomologicalComplex.shortComplexFunctor'_obj_g]
        have h := eq_neg_of_add_eq_zero_left (hp (by omega : (d - 1) + 1 = d) x y)
        simpa only [p₁, Units.neg_smul, LinearMap.neg_apply, LinearMap.smul_apply] using h)
      (fun x y ↦ by
        simp only [S, T, HomologicalComplex.shortComplexFunctor'_obj_f,
          HomologicalComplex.shortComplexFunctor'_obj_g]
        have h := eq_neg_of_add_eq_zero_right (hp (rfl : d + 1 = d + 1) x y)
        have h' := congrArg (d.negOnePow • ·) h
        simpa only [p₃, smul_smul, Int.units_mul_self, one_smul, smul_neg, Units.neg_smul,
          LinearMap.neg_apply, LinearMap.smul_apply] using h')
      _ _
  rw [homologyPairing]
  infer_instance

end CommRing

section Field

/-- Over a field, a degreewise perfect cochain pairing satisfying the graded Leibniz rule descends
to a perfect pairing on cohomology in every complementary pair of degrees `d` and `n - d`. -/
theorem isPerfPair_homologyPairing {k : Type u} [Field k]
    (C : CochainComplex (ModuleCat.{v} k) ℤ) (D : CochainComplex (ModuleCat.{w} k) ℤ)
    (n : ℤ) (p : ∀ d : ℤ, C.X d →ₗ[k] D.X (n - d) →ₗ[k] k) [∀ d, (p d).IsPerfPair]
    (hp : ∀ {a a' : ℤ}, a + 1 = a' → ∀ (x : C.X a) (y : D.X (n - a')),
      p a' ((C.d a a').hom x) y + a.negOnePow • p a x ((D.d (n - a') (n - a)).hom y) = 0)
    (d : ℤ) :
    (C.homologyPairing D n p hp d).IsPerfPair :=
  isPerfPair_homologyPairing_of_baer C D n (ShortComplex.moduleBaer_of_field k) p hp d

end Field

end CochainComplex
