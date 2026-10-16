/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Cochain
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Cyclic cohomology

The cyclic cochains `C_λⁿ(A; M)` of an algebra `A`, the `M`-valued multilinear maps `φ` in
`n + 1` arguments with `φ(aₙ, a₀, …, aₙ₋₁) = (-1)ⁿ φ(a₀, …, aₙ)`, form a subcomplex of the
Hochschild cochains. This file assembles them into Connes' cyclic cochain complex
`cyclicCochainComplex R A M`, a cochain complex of `R`-modules indexed by `ℕ`, and defines the
cyclic cohomology `HCⁿ(A; M)` of a unital algebra as its categorical cohomology. This is Connes'
definition by cyclic cochains; over a ring containing `ℚ` it agrees with the cohomology of the
cyclic bicomplex, which is not treated here.

The cyclic cocycles and coboundaries are also described concretely, as submodules of the cyclic
cochains, and `cyclicCohomology.mk` sends a cocycle to its class: it is surjective, and its kernel
consists exactly of the coboundaries. In degree zero there are no coboundaries and the cocycles are
the traces, so `HC⁰(A; M)` is the module of `M`-valued traces on `A`.

A homomorphism of nonunital algebras `f : A →ₙₐ[R] B` pulls cyclic cochains back along `f`,
giving a cochain map `cyclicCochainComplex R B M ⟶ cyclicCochainComplex R A M` and a map on cyclic
cohomology, contravariantly functorial in `f`. The homomorphism is not required to preserve units,
since the algebra maps from `A` to the differential graded algebras of cycles need not.

The cochain complex is defined for nonunital algebras. Its cohomology is only named cyclic
cohomology for unital `A`: the cyclic cohomology of a nonunital algebra is instead defined through
its forced unitization, and in general differs from the cohomology of this complex.

## Main definitions

* `TauCeti.cyclicCochainComplex`: the cyclic cochain complex.
* `TauCeti.cyclicCocycles`, `TauCeti.cyclicCoboundaries`: cyclic cocycles and coboundaries.
* `TauCeti.cyclicCohomology`: the cyclic cohomology `HCⁿ(A; M)`.
* `TauCeti.cyclicCohomology.mk`: the class of a cyclic cocycle.
* `TauCeti.cyclicCochainComplexMap`, `TauCeti.cyclicCohomology.map`: pullback along a
  homomorphism of nonunital algebras, induced by `TauCeti.cyclicCochainsMap`.

## Main results

* `TauCeti.cyclicCohomology.mk_surjective`, `TauCeti.cyclicCohomology.mk_eq_zero_iff`: cyclic
  cohomology is the quotient of cyclic cocycles by cyclic coboundaries.
* `TauCeti.cyclicCohomology.zeroEquiv`, `TauCeti.mem_cyclicCocycles_zero_iff`: `HC⁰(A; M)` is the
  module of `M`-valued traces on `A`.
* `TauCeti.cyclicCohomology.map_id`, `TauCeti.cyclicCohomology.map_comp`: functoriality.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §2.1.

The concrete description of cohomology classes through `mk` follows the pattern of the de Rham
cohomology file `TauCeti.Geometry.Manifold.DeRham.Basic`.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

section Complex

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Connes' cyclic cochain complex `C_λ⁰ → C_λ¹ → ⋯`: in degree `n` the cyclic `M`-valued
`n`-cochains on `A`, with the Hochschild coboundary as differential. -/
def cyclicCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (cyclicCochains R A M n))
    (fun n ↦ ModuleCat.ofHom (cyclicHochschildCoboundary R A M n))
    fun _ ↦ ModuleCat.hom_ext (cyclicHochschildCoboundary_comp_cyclicHochschildCoboundary R A M)

/-- The degree-`n` term of the cyclic cochain complex is the module of cyclic `n`-cochains. -/
def cyclicCochainComplexXIso (n : ℕ) :
    (cyclicCochainComplex R A M).X n ≅ ModuleCat.of R (cyclicCochains R A M n) :=
  Iso.refl _

/-- Under the identifications `cyclicCochainComplexXIso`, the differential of the cyclic cochain
complex is the Hochschild coboundary. -/
@[reassoc, elementwise]
theorem cyclicCochainComplex_d (n : ℕ) :
    (cyclicCochainComplex R A M).d n (n + 1) ≫ (cyclicCochainComplexXIso R A M (n + 1)).hom =
      (cyclicCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (cyclicHochschildCoboundary R A M n) := by
  simp [cyclicCochainComplex, cyclicCochainComplexXIso]

/-- The cyclic `n`-cocycles: the cyclic cochains annihilated by the Hochschild coboundary. -/
def cyclicCocycles (n : ℕ) : Submodule R (cyclicCochains R A M n) :=
  LinearMap.ker (cyclicHochschildCoboundary R A M n)

/-- A cyclic cochain is a cocycle exactly when its Hochschild coboundary vanishes. -/
@[simp]
theorem mem_cyclicCocycles_iff {n : ℕ} {φ : cyclicCochains R A M n} :
    φ ∈ cyclicCocycles R A M n ↔
      hochschildCoboundary R A M n (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) = 0 := by
  rw [cyclicCocycles, LinearMap.mem_ker, ← Subtype.coe_inj, coe_cyclicHochschildCoboundary_apply,
    ZeroMemClass.coe_zero]

/-- The cyclic `n`-coboundaries: zero in degree zero, and the image of the Hochschild coboundary
of cyclic `n`-cochains in degree `n + 1`. -/
def cyclicCoboundaries : (n : ℕ) → Submodule R (cyclicCochains R A M n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (cyclicHochschildCoboundary R A M n)

/-- There are no nonzero cyclic coboundaries in degree zero. -/
@[simp]
theorem cyclicCoboundaries_zero : cyclicCoboundaries R A M 0 = ⊥ := (rfl)

/-- In positive degree the cyclic coboundaries are the image of the Hochschild coboundary. -/
theorem cyclicCoboundaries_succ (n : ℕ) :
    cyclicCoboundaries R A M (n + 1) = LinearMap.range (cyclicHochschildCoboundary R A M n) :=
  (rfl)

/-- A cyclic `(n + 1)`-cochain is a coboundary exactly when it is the Hochschild coboundary of a
cyclic `n`-cochain. -/
@[simp]
theorem mem_cyclicCoboundaries_succ_iff {n : ℕ} {φ : cyclicCochains R A M (n + 1)} :
    φ ∈ cyclicCoboundaries R A M (n + 1) ↔
      ∃ ψ : cyclicCochains R A M n, cyclicHochschildCoboundary R A M n ψ = φ := by
  rw [cyclicCoboundaries_succ, LinearMap.mem_range]

/-- Every cyclic coboundary is a cyclic cocycle. -/
theorem cyclicCoboundaries_le_cyclicCocycles (n : ℕ) :
    cyclicCoboundaries R A M n ≤ cyclicCocycles R A M n := by
  cases n with
  | zero => simp
  | succ n =>
    exact LinearMap.range_le_ker_iff.2
      (cyclicHochschildCoboundary_comp_cyclicHochschildCoboundary R A M)

/-- A cyclic `0`-cochain is a cocycle exactly when it is a trace. -/
theorem mem_cyclicCocycles_zero_iff {φ : cyclicCochains R A M 0} :
    φ ∈ cyclicCocycles R A M 0 ↔
      ∀ x y : A, (φ : MultilinearMap R (fun _ : Fin 1 ↦ A) M) (fun _ ↦ x * y) =
        (φ : MultilinearMap R (fun _ : Fin 1 ↦ A) M) (fun _ ↦ y * x) := by
  rw [mem_cyclicCocycles_iff, hochschildCoboundary_zero_eq_zero_iff]

section Map

variable {R A M} {B C : Type u} [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B]
  [SMulCommClass R B B] [NonUnitalSemiring C] [Module R C] [IsScalarTower R C C]
  [SMulCommClass R C C]

/-- The pullback of a cyclic cocycle is a cyclic cocycle. -/
theorem cyclicCochainsMap_mem_cyclicCocycles (f : A →ₙₐ[R] B) {n : ℕ}
    {φ : cyclicCochains R B M n} (hφ : φ ∈ cyclicCocycles R B M n) :
    cyclicCochainsMap M (f : A →ₗ[R] B) n φ ∈ cyclicCocycles R A M n := by
  rw [cyclicCocycles, LinearMap.mem_ker, cyclicHochschildCoboundary_cyclicCochainsMap,
    LinearMap.mem_ker.1 hφ, map_zero]

variable (M) in
/-- The cochain map between cyclic cochain complexes induced by a homomorphism of nonunital
algebras. -/
def cyclicCochainComplexMap (f : A →ₙₐ[R] B) :
    cyclicCochainComplex R B M ⟶ cyclicCochainComplex R A M where
  f n := ModuleCat.ofHom (cyclicCochainsMap M (f : A →ₗ[R] B) n)
  comm' := by
    rintro n _ rfl
    ext φ : 2
    simp only [cyclicCochainComplex, CochainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    exact cyclicHochschildCoboundary_cyclicCochainsMap f φ

/-- Under the identifications `cyclicCochainComplexXIso`, the induced cochain map is the pullback
of cyclic cochains. This holds by definition, the identifications being identities. -/
@[reassoc, elementwise]
theorem cyclicCochainComplexMap_f (f : A →ₙₐ[R] B) (n : ℕ) :
    (cyclicCochainComplexMap M f).f n ≫ (cyclicCochainComplexXIso R A M n).hom =
      (cyclicCochainComplexXIso R B M n).hom ≫
        ModuleCat.ofHom (cyclicCochainsMap M (f : A →ₗ[R] B) n) :=
  (rfl)

/-- The identity homomorphism induces the identity cochain map. -/
@[simp]
theorem cyclicCochainComplexMap_id :
    cyclicCochainComplexMap M (NonUnitalAlgHom.id R A) = 𝟙 (cyclicCochainComplex R A M) := by
  ext n : 1
  dsimp only [cyclicCochainComplexMap, HomologicalComplex.id_f]
  -- The identity homomorphism coerces to the identity linear map by definition.
  exact (congrArg ModuleCat.ofHom (cyclicCochainsMap_id M n)).trans ModuleCat.ofHom_id

/-- The induced cochain map is contravariantly functorial. -/
theorem cyclicCochainComplexMap_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    cyclicCochainComplexMap M (g.comp f) =
      cyclicCochainComplexMap M g ≫ cyclicCochainComplexMap M f := by
  ext n : 1
  dsimp only [cyclicCochainComplexMap, HomologicalComplex.comp_f]
  -- The composite homomorphism coerces to the composite linear map by definition.
  exact (congrArg ModuleCat.ofHom
    (cyclicCochainsMap_comp M (f : A →ₗ[R] B) (g : B →ₗ[R] C) n)).trans (ModuleCat.ofHom_comp _ _)

end Map

end Complex

section Cohomology

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M]
  [Module R M]

/-- The cyclic cohomology `HCⁿ(A; M)` of a unital algebra `A` with coefficients in `M`, the
cohomology of the cyclic cochain complex. For `M = R` this is Connes' cyclic cohomology `HCⁿ(A)`. -/
abbrev cyclicCohomology (n : ℕ) : ModuleCat R :=
  (cyclicCochainComplex R A M).homology n

/-- A cyclic cocycle, viewed as a cycle of the cyclic cochain complex. -/
private def toCycles (n : ℕ) :
    ModuleCat.of R (cyclicCocycles R A M n) ⟶ (cyclicCochainComplex R A M).cycles n :=
  (cyclicCochainComplex R A M).liftCycles
    (ModuleCat.ofHom (cyclicCocycles R A M n).subtype ≫ (cyclicCochainComplexXIso R A M n).inv)
    (n + 1) (by simp) (by
      rw [← cancel_mono (cyclicCochainComplexXIso R A M (n + 1)).hom, Category.assoc,
        Category.assoc, cyclicCochainComplex_d, Iso.inv_hom_id_assoc, Limits.zero_comp]
      refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
      -- The composite is the Hochschild coboundary applied to the underlying cochain of `φ`.
      exact φ.2)

private theorem iCycles_toCycles (n : ℕ) (φ : cyclicCocycles R A M n) :
    (cyclicCochainComplex R A M).iCycles n (toCycles R A M n φ) =
      (cyclicCochainComplexXIso R A M n).inv φ.1 := by
  rw [toCycles, ← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
  -- The composite of the inclusion of cocycles with `cyclicCochainComplexXIso` evaluates to `φ`.
  rfl

/-- The cycle of a cyclic cocycle has zero class exactly when the cocycle is the image of the
incoming differential, `m` being the degree preceding `n`. -/
private theorem homologyπ_toCycles_eq_zero_iff {n m : ℕ} (hm : (ComplexShape.up ℕ).prev n = m)
    (φ : cyclicCocycles R A M n) :
    (cyclicCochainComplex R A M).homologyπ n (toCycles R A M n φ) = 0 ↔
      ∃ y, (cyclicCochainComplex R A M).d m n y = (cyclicCochainComplexXIso R A M n).inv φ.1 := by
  let K := cyclicCochainComplex R A M
  rw [K.moduleCat_homologyπ_eq_zero_iff hm]
  refine exists_congr fun y ↦ ?_
  rw [← (K.moduleCat_iCycles_injective n).eq_iff, iCycles_toCycles, ← ModuleCat.comp_apply,
    HomologicalComplex.toCycles_i]

namespace cyclicCohomology

/-- The cyclic cohomology class of a cyclic cocycle. -/
def mk (n : ℕ) : cyclicCocycles R A M n →ₗ[R] cyclicCohomology R A M n :=
  (toCycles R A M n ≫ (cyclicCochainComplex R A M).homologyπ n).hom

/-- The class of a cyclic cocycle is the homology class of the corresponding cycle. -/
private theorem mk_apply (n : ℕ) (φ : cyclicCocycles R A M n) :
    mk R A M n φ = (cyclicCochainComplex R A M).homologyπ n (toCycles R A M n φ) :=
  (rfl)

/-- Every cyclic cohomology class is the class of a cyclic cocycle. -/
theorem mk_surjective (n : ℕ) : Function.Surjective (mk R A M n) := by
  intro z
  let K := cyclicCochainComplex R A M
  obtain ⟨c, rfl⟩ := K.moduleCat_homologyπ_surjective n z
  have hc : (cyclicCochainComplexXIso R A M n).hom (K.iCycles n c) ∈ cyclicCocycles R A M n := by
    have h : K.d n (n + 1) (K.iCycles n c) = 0 := by
      rw [← ConcreteCategory.comp_apply, K.iCycles_d]
      rfl
    rw [cyclicCocycles, LinearMap.mem_ker, ← cyclicCochainComplex_d_apply, h, map_zero]
  refine ⟨⟨_, hc⟩, ?_⟩
  rw [mk_apply]
  congr 1
  apply K.moduleCat_iCycles_injective n
  rw [iCycles_toCycles, Iso.hom_inv_id_apply]

/-- A cyclic cocycle has zero cohomology class exactly when it is a cyclic coboundary. -/
@[simp]
theorem mk_eq_zero_iff (n : ℕ) (φ : cyclicCocycles R A M n) :
    mk R A M n φ = 0 ↔ (φ : cyclicCochains R A M n) ∈ cyclicCoboundaries R A M n := by
  let K := cyclicCochainComplex R A M
  cases n with
  | zero =>
    rw [mk_apply, homologyπ_toCycles_eq_zero_iff R A M CochainComplex.prev_nat_zero,
      K.shape 0 0 (by simp), cyclicCoboundaries_zero, Submodule.mem_bot]
    refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun h ↦ ⟨0, by rw [h, map_zero, map_zero]⟩⟩
    rw [← Iso.inv_hom_id_apply (cyclicCochainComplexXIso R A M 0) φ.1, ← hy]
    simp
  | succ n =>
    rw [mk_apply, homologyπ_toCycles_eq_zero_iff R A M (CochainComplex.prev_nat_succ n),
      mem_cyclicCoboundaries_succ_iff]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(cyclicCochainComplexXIso R A M n).hom y, ?_⟩
      rw [← cyclicCochainComplex_d_apply, hy, Iso.inv_hom_id_apply]
    · rintro ⟨ψ, hψ⟩
      refine ⟨(cyclicCochainComplexXIso R A M n).inv ψ, ?_⟩
      apply (ModuleCat.mono_iff_injective (cyclicCochainComplexXIso R A M (n + 1)).hom).1
        inferInstance
      rw [cyclicCochainComplex_d_apply, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, hψ]

/-- Two cyclic cocycles have the same class exactly when they differ by a cyclic coboundary. -/
theorem mk_eq_mk_iff (n : ℕ) (φ ψ : cyclicCocycles R A M n) :
    mk R A M n φ = mk R A M n ψ ↔
      (φ : cyclicCochains R A M n) - ψ ∈ cyclicCoboundaries R A M n := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff, Submodule.coe_sub]

/-- In degree zero the class map is injective: there are no nonzero cyclic coboundaries. -/
theorem mk_zero_injective : Function.Injective (mk R A M 0) := by
  refine (injective_iff_map_eq_zero _).2 fun φ hφ ↦ ?_
  rw [mk_eq_zero_iff, cyclicCoboundaries_zero, Submodule.mem_bot] at hφ
  exact Subtype.ext hφ

/-- `HC⁰(A; M)` is the module of cyclic `0`-cocycles. Every `0`-cochain is cyclic
(`cyclicCochains_zero`) and the `0`-cocycles are the traces (`mem_cyclicCocycles_zero_iff`), so this
identifies `HC⁰(A; M)` with the module of `M`-valued traces on `A`. -/
def zeroEquiv : cyclicCocycles R A M 0 ≃ₗ[R] cyclicCohomology R A M 0 :=
  LinearEquiv.ofBijective (mk R A M 0) ⟨mk_zero_injective R A M, mk_surjective R A M 0⟩

/-- The equivalence `zeroEquiv` sends a cyclic `0`-cocycle to its class. -/
@[simp]
theorem zeroEquiv_apply (φ : cyclicCocycles R A M 0) : zeroEquiv R A M φ = mk R A M 0 φ :=
  (rfl)

section Map

variable {R A M} {B C : Type u} [Ring B] [Algebra R B] [Ring C] [Algebra R C]

variable (M) in
/-- The map on cyclic cohomology induced by a homomorphism of nonunital algebras between unital
algebras; the homomorphism need not preserve the unit. -/
def map (f : A →ₙₐ[R] B) (n : ℕ) : cyclicCohomology R B M n ⟶ cyclicCohomology R A M n :=
  HomologicalComplex.homologyMap (cyclicCochainComplexMap M f) n

/-- The induced map sends the class of a cocycle to the class of its pullback. -/
@[simp]
theorem map_mk (f : A →ₙₐ[R] B) {n : ℕ} (φ : cyclicCocycles R B M n) :
    map M f n (mk R B M n φ) =
      mk R A M n
        ⟨cyclicCochainsMap M (f : A →ₗ[R] B) n φ, cyclicCochainsMap_mem_cyclicCocycles f φ.2⟩ := by
  rw [map, mk_apply, mk_apply, ← ConcreteCategory.comp_apply,
    HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply]
  congr 1
  apply (cyclicCochainComplex R A M).moduleCat_iCycles_injective n
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
    iCycles_toCycles, iCycles_toCycles]
  -- Both sides are the pullback of `φ`, as `cyclicCochainComplexXIso` is the identity.
  rfl

/-- The identity homomorphism induces the identity on cyclic cohomology. -/
@[simp]
theorem map_id (n : ℕ) : map M (NonUnitalAlgHom.id R A) n = 𝟙 _ := by
  rw [map, cyclicCochainComplexMap_id, HomologicalComplex.homologyMap_id]

/-- Cyclic cohomology is contravariantly functorial. -/
theorem map_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) (n : ℕ) :
    map M (g.comp f) n = map M g n ≫ map M f n := by
  rw [map, map, map, cyclicCochainComplexMap_comp, HomologicalComplex.homologyMap_comp]

end Map

end cyclicCohomology

end Cohomology

end TauCeti
