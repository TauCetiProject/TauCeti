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
# The Hochschild cochain complex and its cohomology

The `M`-valued multilinear cochains `Cⁿ(A; M)` of an algebra `A`, the maps `φ : Aⁿ⁺¹ → M`, form
the Hochschild cochain complex `hochschildCochainComplex R A M` under the Hochschild coboundary
`b`. Here `M` is only an `R`-module, and a degree-`n` cochain takes `n + 1` arguments. Currying the
first argument identifies these cochains with the `Hom_R(A, M)`-valued cochains in `n` arguments,
and `b` with the Hochschild coboundary of the bimodule `Hom_R(A, M)`, whose actions are
`(x f y)(a) = f (y a x)` (`TauCeti.multilinearCurryFirstEquiv_hochschildCoboundary`). So for a
unital algebra `A` the cohomology of this complex is, in Connes' cochain description, the
Hochschild cohomology `HHⁿ(A, Hom_R(A, M))` of `A` with coefficients in `Hom_R(A, M)`, and not the
Hochschild cohomology with coefficients in `M`. For `M = R` it is `HHⁿ(A, A*)`, the Hochschild
cohomology of `A` with coefficients in its dual bimodule.

The complex and its cohomology are defined for nonunital associative algebras. For a nonunital
algebra this is the naive cochain complex, rather than the relative complex of its forced
unitization.

The concrete cocycles and coboundaries are defined over semirings when the `R`-action on `M`
commutes with itself. The categorical complex and cohomology use a commutative ring.

As for cyclic cohomology, `hochschildCohomology.mk` sends a Hochschild cocycle to its class; it
is surjective and its kernel consists exactly of the coboundaries, so linear maps out of
Hochschild cohomology are described by `hochschildCohomology.desc`. In degree zero there are no
coboundaries and the cocycles are the traces.

## Main definitions

* `TauCeti.hochschildCochainComplex`: the Hochschild cochain complex.
* `TauCeti.hochschildCocycles`, `TauCeti.hochschildCoboundaries`: Hochschild cocycles and
  coboundaries.
* `TauCeti.hochschildCohomology`: the cohomology of the Hochschild cochain complex; for a unital
  algebra it is the Hochschild cohomology `HHⁿ(A, Hom_R(A, M))`.
* `TauCeti.hochschildCohomology.mk`: the class of a Hochschild cocycle.
* `TauCeti.hochschildCohomology.desc`: the linear map out of Hochschild cohomology induced by a
  linear map on Hochschild cocycles vanishing on Hochschild coboundaries.
* `TauCeti.hochschildCohomology.map`: contravariant map on Hochschild cohomology induced by a
  nonunital algebra homomorphism.

## Main results

* `TauCeti.hochschildCohomology.mk_surjective`, `TauCeti.hochschildCohomology.mk_eq_zero_iff`:
  Hochschild cohomology is the quotient of the cocycles by the coboundaries.
* `TauCeti.mem_hochschildCocycles_zero_iff`: the Hochschild `0`-cocycles are the traces.
* `TauCeti.hochschildCohomology.map_id`, `TauCeti.hochschildCohomology.map_comp`: functoriality.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §2.2.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

section Cocycles

variable (R : Type*) (A : Type u) (M : Type*) [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- The Hochschild `n`-cocycles: the `n`-cochains annihilated by the Hochschild coboundary. -/
def hochschildCocycles (n : ℕ) : Submodule R (MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦
    A) M) :=
  LinearMap.ker (hochschildCoboundary R A M n)

variable {R A M} in
/-- A cochain is a Hochschild cocycle exactly when its Hochschild coboundary vanishes. -/
@[simp]
theorem mem_hochschildCocycles_iff {n : ℕ} {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1)
    ↦ A) M} :
    φ ∈ hochschildCocycles R A M n ↔ hochschildCoboundary R A M n φ = 0 :=
  LinearMap.mem_ker

/-- The Hochschild `n`-coboundaries: zero in degree zero, and the image of the Hochschild
coboundary of `n`-cochains in degree `n + 1`. -/
def hochschildCoboundaries :
    (n : ℕ) → Submodule R (MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M)
  | 0 => ⊥
  | n + 1 => LinearMap.range (hochschildCoboundary R A M n)

/-- There are no nonzero Hochschild coboundaries in degree zero. -/
@[simp]
theorem hochschildCoboundaries_zero : hochschildCoboundaries R A M 0 = ⊥ := (rfl)

/-- In positive degree the Hochschild coboundaries are the image of the Hochschild coboundary. -/
theorem hochschildCoboundaries_succ (n : ℕ) :
    hochschildCoboundaries R A M (n + 1) = LinearMap.range (hochschildCoboundary R A M n) :=
  (rfl)

variable {R A M} in
/-- An `(n + 1)`-cochain is a Hochschild coboundary exactly when it is the Hochschild coboundary
of an `n`-cochain. -/
@[simp]
theorem mem_hochschildCoboundaries_succ_iff {n : ℕ}
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M} :
    φ ∈ hochschildCoboundaries R A M (n + 1) ↔ ∃ ψ, hochschildCoboundary R A M n ψ = φ :=
  LinearMap.mem_range

/-- Every Hochschild coboundary is a Hochschild cocycle. -/
theorem hochschildCoboundaries_le_hochschildCocycles (n : ℕ) :
    hochschildCoboundaries R A M n ≤ hochschildCocycles R A M n := by
  cases n with
  | zero => simp
  | succ n =>
    exact LinearMap.range_le_ker_iff.2 (hochschildCoboundary_comp_hochschildCoboundary R A M)

variable {R A M} in
/-- A `0`-cochain is a Hochschild cocycle exactly when it is a trace. -/
theorem mem_hochschildCocycles_zero_iff {φ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ A) M} :
    φ ∈ hochschildCocycles R A M 0 ↔ ∀ x y : A, φ (fun _ ↦ x * y) = φ (fun _ ↦ y * x) := by
  rw [mem_hochschildCocycles_iff, hochschildCoboundary_zero_eq_zero_iff]

section PullbackCocycles

variable {R A M} {B : Type*} [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B]
  [SMulCommClass R B B]

/-- Pulling a Hochschild cocycle back along a nonunital algebra homomorphism yields a Hochschild
cocycle. -/
theorem compLinearMap_mem_hochschildCocycles (f : A →ₙₐ[R] B) {n : ℕ}
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M}
    (hφ : φ ∈ hochschildCocycles R B M n) :
    (φ.compLinearMap fun _ ↦ (f : A →ₗ[R] B)) ∈ hochschildCocycles R A M n := by
  rw [mem_hochschildCocycles_iff] at hφ ⊢
  rw [hochschildCoboundary_compLinearMap, hφ, MultilinearMap.zero_compLinearMap]

/-- Pulling a Hochschild coboundary back along a nonunital algebra homomorphism yields a Hochschild
coboundary. -/
theorem compLinearMap_mem_hochschildCoboundaries (f : A →ₙₐ[R] B) {n : ℕ}
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M}
    (hφ : φ ∈ hochschildCoboundaries R B M n) :
    (φ.compLinearMap fun _ ↦ (f : A →ₗ[R] B)) ∈ hochschildCoboundaries R A M n := by
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot] at hφ ⊢
    rw [hφ, MultilinearMap.zero_compLinearMap]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hφ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨ψ.compLinearMap fun _ ↦ (f : A →ₗ[R] B), hochschildCoboundary_compLinearMap f ψ⟩

end PullbackCocycles

end Cocycles

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

section Complex

/-- The Hochschild cochain complex `C⁰ → C¹ → ⋯`: in degree `n` the `M`-valued `n`-cochains on
`A`, the multilinear maps in `n + 1` arguments, with the Hochschild coboundary as differential. -/
def hochschildCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦
      A) M))
    (fun n ↦ ModuleCat.ofHom (hochschildCoboundary R A M n))
    fun _ ↦ ModuleCat.hom_ext (hochschildCoboundary_comp_hochschildCoboundary R A M)

/-- The degree-`n` term of the Hochschild cochain complex is the module of `n`-cochains. -/
def hochschildCochainComplexXIso (n : ℕ) :
    (hochschildCochainComplex R A M).X n ≅
      ModuleCat.of R (MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :=
  Iso.refl _

/-- Under the identifications `hochschildCochainComplexXIso`, the differential of the Hochschild
cochain complex is the Hochschild coboundary. -/
@[reassoc, elementwise]
theorem hochschildCochainComplex_d (n : ℕ) :
    (hochschildCochainComplex R A M).d n (n + 1) ≫
        (hochschildCochainComplexXIso R A M (n + 1)).hom =
      (hochschildCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (hochschildCoboundary R A M n) := by
  simp [hochschildCochainComplex, hochschildCochainComplexXIso]

end Complex

section Cohomology

/-- The cohomology of the Hochschild cochain complex of `A` with `M`-valued cochains in `n + 1`
arguments. For a unital algebra `A`, in Connes' cochain description this is the Hochschild
cohomology `HHⁿ(A, Hom_R(A, M))` of `A` with coefficients in the bimodule `Hom_R(A, M)`, not with
coefficients in `M`; for `M = R` it is `HHⁿ(A, A*)`, with coefficients in the dual bimodule. -/
abbrev hochschildCohomology (n : ℕ) : ModuleCat R :=
  (hochschildCochainComplex R A M).homology n

private theorem mem_hochschildCocycles_iff_complex (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    φ ∈ hochschildCocycles R A M n ↔
      (hochschildCochainComplex R A M).d n (n + 1)
        ((hochschildCochainComplexXIso R A M n).inv φ) = 0 := by
  rw [mem_hochschildCocycles_iff, (hochschildCochainComplex R A M).moduleCat_d_inv_eq_zero_iff
    (hochschildCoboundary R A M) (hochschildCochainComplex_d R A M)]

private theorem mem_hochschildCoboundaries_iff_complex (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    φ ∈ hochschildCoboundaries R A M n ↔
      ∃ y : (hochschildCochainComplex R A M).X ((ComplexShape.up ℕ).prev n),
        (hochschildCochainComplex R A M).d ((ComplexShape.up ℕ).prev n) n y =
          (hochschildCochainComplexXIso R A M n).inv φ :=
  (hochschildCochainComplex R A M).moduleCat_mem_iff_exists_d_eq_inv
    (hochschildCoboundaries R A M) (hochschildCoboundary R A M) (hochschildCochainComplex_d R A M)
    (hochschildCoboundaries_zero R A M) (hochschildCoboundaries_succ R A M) n φ

namespace hochschildCohomology

/-- The Hochschild cohomology class of a Hochschild cocycle. -/
def mk (n : ℕ) : hochschildCocycles R A M n →ₗ[R] hochschildCohomology R A M n :=
  (hochschildCochainComplex R A M).moduleCatCohomologyClassOfIso
    (fun n ↦ MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) (hochschildCocycles R A M)
    (hochschildCochainComplexXIso R A M) (mem_hochschildCocycles_iff_complex R A M) n

/-- The class of a Hochschild cocycle `φ` is the homology class of any cycle of the Hochschild
cochain complex whose underlying cochain is `φ`. -/
theorem mk_eq_homologyπ {n : ℕ} (φ : hochschildCocycles R A M n)
    (z : (hochschildCochainComplex R A M).cycles n)
    (hz : (hochschildCochainComplexXIso R A M n).hom
      ((hochschildCochainComplex R A M).iCycles n z) = φ) :
    mk R A M n φ = (hochschildCochainComplex R A M).homologyπ n z :=
  (hochschildCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_homologyπ
    (fun n ↦ MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) (hochschildCocycles R A M)
    (hochschildCochainComplexXIso R A M) (mem_hochschildCocycles_iff_complex R A M) φ z hz

/-- Every Hochschild cohomology class is the class of a Hochschild cocycle. -/
theorem mk_surjective (n : ℕ) : Function.Surjective (mk R A M n) :=
  (hochschildCochainComplex R A M).moduleCatCohomologyClassOfIso_surjective
    (fun n ↦ MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) (hochschildCocycles R A M)
    (hochschildCochainComplexXIso R A M) (mem_hochschildCocycles_iff_complex R A M) n

/-- A Hochschild cocycle has zero cohomology class exactly when it is a Hochschild
coboundary. -/
@[simp]
theorem mk_eq_zero_iff (n : ℕ) (φ : hochschildCocycles R A M n) :
    mk R A M n φ = 0 ↔
      (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A)
          M) ∈ hochschildCoboundaries R A M n :=
  (hochschildCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_zero_iff
    (fun n ↦ MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) (hochschildCocycles R A M)
    (hochschildCoboundaries R A M) (hochschildCochainComplexXIso R A M)
    (mem_hochschildCocycles_iff_complex R A M) (mem_hochschildCoboundaries_iff_complex R A M) n φ

/-- Two Hochschild cocycles have the same class exactly when they differ by a Hochschild
coboundary. -/
theorem mk_eq_mk_iff (n : ℕ) (φ ψ : hochschildCocycles R A M n) :
    mk R A M n φ = mk R A M n ψ ↔
      (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A)
          M) - ψ ∈ hochschildCoboundaries R A M n :=
  (hochschildCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_iff
    (fun n ↦ MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) (hochschildCocycles R A M)
    (hochschildCoboundaries R A M) (hochschildCochainComplexXIso R A M)
    (mem_hochschildCocycles_iff_complex R A M) (mem_hochschildCoboundaries_iff_complex R A M) n
    φ ψ

section Desc

variable {R A M} {N : Type*} [AddCommGroup N] [Module R N]

/-- Two linear maps out of Hochschild cohomology agree once they agree on classes of cocycles. -/
@[ext]
theorem linearMap_ext {n : ℕ} {f g : hochschildCohomology R A M n →ₗ[R] N}
    (h : f ∘ₗ mk R A M n = g ∘ₗ mk R A M n) : f = g :=
  LinearMap.ext fun z ↦ by
    obtain ⟨φ, rfl⟩ := mk_surjective R A M n z
    exact LinearMap.congr_fun h φ

/-- A linear map on Hochschild cocycles that vanishes on Hochschild coboundaries descends to
Hochschild cohomology. -/
def desc (n : ℕ) (f : hochschildCocycles R A M n →ₗ[R] N)
    (hf : ∀ φ : hochschildCocycles R A M n,
      (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A)
          M) ∈ hochschildCoboundaries R A M n →
        f φ = 0) :
    hochschildCohomology R A M n →ₗ[R] N :=
  (mk R A M n).liftOfSurjective (mk_surjective R A M n)
    ⟨f, fun φ hφ ↦
      LinearMap.mem_ker.2 (hf φ ((mk_eq_zero_iff R A M n φ).1 (LinearMap.mem_ker.1 hφ)))⟩

/-- The descended map sends the class of a cocycle to the value of the original map. -/
@[simp]
theorem desc_mk (n : ℕ) (f : hochschildCocycles R A M n →ₗ[R] N)
    (hf : ∀ φ : hochschildCocycles R A M n,
      (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A)
          M) ∈ hochschildCoboundaries R A M n →
        f φ = 0)
    (φ : hochschildCocycles R A M n) :
    desc n f hf (mk R A M n φ) = f φ :=
  LinearMap.equivOfSurjective_apply _ _

/-- The descended map composed with the class map is the original map. -/
@[simp]
theorem desc_comp_mk (n : ℕ) (f : hochschildCocycles R A M n →ₗ[R] N)
    (hf : ∀ φ : hochschildCocycles R A M n,
      (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A)
          M) ∈ hochschildCoboundaries R A M n →
        f φ = 0) :
    desc n f hf ∘ₗ mk R A M n = f :=
  LinearMap.ext (desc_mk n f hf)

end Desc

section Map

variable {R A M} {B C : Type*} [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B]
  [SMulCommClass R B B] [NonUnitalSemiring C] [Module R C] [IsScalarTower R C C]
  [SMulCommClass R C C]

/-- Pullback of Hochschild cocycles along a nonunital algebra homomorphism. -/
private def cocyclesMap (f : A →ₙₐ[R] B) (n : ℕ) :
    hochschildCocycles R B M n →ₗ[R] hochschildCocycles R A M n :=
  LinearMap.codRestrict _
    ((MultilinearMap.compLinearMapₗ fun _ : Fin (n + 1) ↦ (f : A →ₗ[R] B)) ∘ₗ
      (hochschildCocycles R B M n).subtype)
    fun φ ↦ compLinearMap_mem_hochschildCocycles f φ.2

variable (M) in
/-- The contravariant map on Hochschild cohomology induced by a homomorphism of nonunital
algebras. -/
def map (f : A →ₙₐ[R] B) (n : ℕ) :
    hochschildCohomology R B M n →ₗ[R] hochschildCohomology R A M n :=
  desc n (mk R A M n ∘ₗ cocyclesMap f n) fun _ hφ ↦
    (mk_eq_zero_iff R A M n _).2 (compLinearMap_mem_hochschildCoboundaries f hφ)

/-- The induced map on Hochschild cohomology sends the class of a cocycle to the class of its
pullback. -/
@[simp]
theorem map_mk (f : A →ₙₐ[R] B) {n : ℕ} (φ : hochschildCocycles R B M n) :
    map M f n (mk R B M n φ) =
      mk R A M n ⟨(φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M).compLinearMap
        fun _ ↦ (f : A →ₗ[R] B), compLinearMap_mem_hochschildCocycles f φ.2⟩ :=
  desc_mk _ _ _ φ

/-- The identity homomorphism induces the identity on Hochschild cohomology. -/
@[simp]
theorem map_id (n : ℕ) : map M (NonUnitalAlgHom.id R A) n = LinearMap.id :=
  linearMap_ext <| LinearMap.ext fun φ ↦ by
    simp only [LinearMap.comp_apply, map_mk, LinearMap.id_apply]
    exact congrArg (mk R A M n) (Subtype.ext (MultilinearMap.ext fun x ↦ by simp))

/-- Hochschild cohomology is contravariantly functorial. -/
theorem map_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) (n : ℕ) :
    map M (g.comp f) n = map M f n ∘ₗ map M g n :=
  linearMap_ext <| LinearMap.ext fun φ ↦ by
    simp only [LinearMap.comp_apply, map_mk]
    exact congrArg (mk R A M n) (Subtype.ext (MultilinearMap.ext fun x ↦ by simp))

end Map

end hochschildCohomology

end Cohomology

end TauCeti
