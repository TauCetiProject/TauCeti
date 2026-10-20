/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Cohomology
public import TauCeti.RingTheory.CyclicCohomology.ConnesOperator
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Hochschild cohomology and the maps `I` and `B` of the SBI sequence

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

Connes' cyclic cochain complex is a subcomplex, and its inclusion
`cyclicCochainComplexι R A M` induces `I : HCⁿ(A; M) → HHⁿ(A, Hom_R(A, M))`
(`cyclicCohomology.toHochschild`). In the other direction, Connes' operator
`B : Cⁿ⁺¹ → Cⁿ` takes values in cyclic cochains and anticommutes with `b`, so it sends Hochschild
cocycles to cyclic cocycles and Hochschild coboundaries to cyclic coboundaries; it therefore
induces `B : HHⁿ⁺¹(A, Hom_R(A, M)) → HCⁿ(A; M)` (`hochschildCohomology.connesB`). Since `B`
vanishes on cyclic cochains, the composite `B ∘ I : HCⁿ⁺¹ → HHⁿ⁺¹ → HCⁿ` is zero. When `R`
contains `ℚ`, these are the maps `I` and `B` of Connes' long exact sequence
`⋯ → HCⁿ → HHⁿ → HCⁿ⁻¹ → HCⁿ⁺¹ → HHⁿ⁺¹ → ⋯`,
whose remaining map is the periodicity operator `S`. Over a general ground ring the cohomology of
the cyclic cochains need not fit into such an exact sequence; the maps `I` and `B` and the
identity `B ∘ I = 0` are nevertheless constructed here for every commutative ring `R`.

As for cyclic cohomology, `hochschildCohomology.mk` sends a Hochschild cocycle to its class; it
is surjective and its kernel consists exactly of the coboundaries. In degree zero there are no
coboundaries, every cochain is cyclic and the cocycles are the traces, so
`I : HC⁰(A; M) → HH⁰(A, Hom_R(A, M))` is an isomorphism.

## Main definitions

* `TauCeti.hochschildCochainComplex`: the Hochschild cochain complex.
* `TauCeti.hochschildCocycles`, `TauCeti.hochschildCoboundaries`: Hochschild cocycles and
  coboundaries.
* `TauCeti.hochschildCohomology`: the Hochschild cohomology `HHⁿ(A, Hom_R(A, M))` of a unital
  algebra.
* `TauCeti.hochschildCohomology.mk`: the class of a Hochschild cocycle.
* `TauCeti.cyclicCochainComplexι`: the inclusion of the cyclic cochain complex.
* `TauCeti.cyclicCohomology.toHochschild`: the map `I : HCⁿ(A; M) → HHⁿ(A, Hom_R(A, M))`.
* `TauCeti.hochschildCohomology.connesB`: the map `B : HHⁿ⁺¹(A, Hom_R(A, M)) → HCⁿ(A; M)`.

## Main results

* `TauCeti.hochschildCohomology.mk_surjective`, `TauCeti.hochschildCohomology.mk_eq_zero_iff`:
  Hochschild cohomology is the quotient of the cocycles by the coboundaries.
* `TauCeti.cyclicCohomology.toHochschild_mk`, `TauCeti.hochschildCohomology.connesB_mk`: `I` and
  `B` on representing cocycles.
* `TauCeti.cyclicCohomology.toHochschild_comp_connesB`: `B ∘ I = 0`.
* `TauCeti.cyclicCohomology.isIso_toHochschild_zero`: `I` is an isomorphism in degree zero.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§2.2 and 2.4.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace TauCeti

universe u

section Complex

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The Hochschild cochain complex `C⁰ → C¹ → ⋯`: in degree `n` the `M`-valued `n`-cochains on
`A`, the multilinear maps in `n + 1` arguments, with the Hochschild coboundary as differential. -/
def hochschildCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M))
    (fun n ↦ ModuleCat.ofHom (hochschildCoboundary R A M n))
    fun _ ↦ ModuleCat.hom_ext (hochschildCoboundary_comp_hochschildCoboundary R A M)

/-- The degree-`n` term of the Hochschild cochain complex is the module of `n`-cochains. -/
def hochschildCochainComplexXIso (n : ℕ) :
    (hochschildCochainComplex R A M).X n ≅
      ModuleCat.of R (MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :=
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

/-- The Hochschild `n`-cocycles: the `n`-cochains annihilated by the Hochschild coboundary. -/
def hochschildCocycles (n : ℕ) : Submodule R (MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :=
  LinearMap.ker (hochschildCoboundary R A M n)

variable {R A M} in
/-- A cochain is a Hochschild cocycle exactly when its Hochschild coboundary vanishes. -/
@[simp]
theorem mem_hochschildCocycles_iff {n : ℕ} {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} :
    φ ∈ hochschildCocycles R A M n ↔ hochschildCoboundary R A M n φ = 0 :=
  LinearMap.mem_ker

/-- The Hochschild `n`-coboundaries: zero in degree zero, and the image of the Hochschild
coboundary of `n`-cochains in degree `n + 1`. -/
def hochschildCoboundaries :
    (n : ℕ) → Submodule R (MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M)
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
    {φ : MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M} :
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
theorem mem_hochschildCocycles_zero_iff {φ : MultilinearMap R (fun _ : Fin 1 ↦ A) M} :
    φ ∈ hochschildCocycles R A M 0 ↔ ∀ x y : A, φ (fun _ ↦ x * y) = φ (fun _ ↦ y * x) := by
  rw [mem_hochschildCocycles_iff, hochschildCoboundary_zero_eq_zero_iff]

variable {R A M} in
/-- A cyclic cocycle is a Hochschild cocycle. -/
theorem mem_hochschildCocycles_of_mem_cyclicCocycles {n : ℕ} {φ : cyclicCochains R A M n}
    (hφ : φ ∈ cyclicCocycles R A M n) :
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) ∈ hochschildCocycles R A M n :=
  mem_hochschildCocycles_iff.2 ((mem_cyclicCocycles_iff R A M).1 hφ)

/-- The inclusion of Connes' cyclic cochain complex into the Hochschild cochain complex. -/
def cyclicCochainComplexι : cyclicCochainComplex R A M ⟶ hochschildCochainComplex R A M where
  f n := (cyclicCochainComplexXIso R A M n).hom ≫
    ModuleCat.ofHom (cyclicCochains R A M n).subtype ≫ (hochschildCochainComplexXIso R A M n).inv
  comm' := by
    rintro n _ rfl
    refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
    apply (ModuleCat.mono_iff_injective (hochschildCochainComplexXIso R A M (n + 1)).hom).1
      inferInstance
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hochschildCochainComplex_d_apply,
      Iso.inv_hom_id_apply, cyclicCochainComplex_d_apply, ModuleCat.hom_ofHom,
      Submodule.subtype_apply]
    exact (coe_cyclicHochschildCoboundary_apply R A M _).symm

/-- Under the identifications of the terms of both complexes with modules of cochains, the
inclusion of the cyclic cochain complex is the inclusion of the cyclic cochains. -/
@[reassoc, elementwise]
theorem cyclicCochainComplexι_f (n : ℕ) :
    (cyclicCochainComplexι R A M).f n ≫ (hochschildCochainComplexXIso R A M n).hom =
      (cyclicCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (cyclicCochains R A M n).subtype := by
  simp [cyclicCochainComplexι]

end Complex

section ConnesB

variable {R : Type*} {A : Type u} {M : Type*} [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Connes' operator `B` sends a Hochschild `(n + 1)`-cocycle to a cyclic `n`-cocycle. -/
theorem connesB_mem_cyclicCocycles {n : ℕ} {φ : MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M}
    (hφ : φ ∈ hochschildCocycles R A M (n + 1)) :
    (⟨connesB R A M n φ, connesB_mem_cyclicCochains φ⟩ : cyclicCochains R A M n) ∈
      cyclicCocycles R A M n := by
  have h := hochschildCoboundary_connesB_add_connesB_hochschildCoboundary φ
  rw [mem_hochschildCocycles_iff.1 hφ, map_zero, add_zero] at h
  exact (mem_cyclicCocycles_iff R A M).2 h

/-- Connes' operator `B` sends a Hochschild `(n + 1)`-coboundary to a cyclic `n`-coboundary. -/
theorem connesB_mem_cyclicCoboundaries {n : ℕ}
    {φ : MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M}
    (hφ : φ ∈ hochschildCoboundaries R A M (n + 1)) :
    (⟨connesB R A M n φ, connesB_mem_cyclicCochains φ⟩ : cyclicCochains R A M n) ∈
      cyclicCoboundaries R A M n := by
  obtain ⟨ψ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hφ
  cases n with
  | zero =>
    -- Every `0`-cochain is cyclic, hence so is its coboundary, on which `B` vanishes.
    have hψ : ψ ∈ cyclicCochains R A M 0 := by simp
    simp [connesB_eq_zero_of_mem_cyclicCochains (hochschildCoboundary_mem_cyclicCochains R A M hψ)]
  | succ n =>
    -- `B (b ψ) = b (-B ψ)` is the coboundary of a cyclic cochain.
    refine (mem_cyclicCoboundaries_succ_iff R A M).2
      ⟨-⟨connesB R A M n ψ, connesB_mem_cyclicCochains ψ⟩, Subtype.ext ?_⟩
    rw [map_neg, Submodule.coe_neg, coe_cyclicHochschildCoboundary_apply, neg_eq_iff_add_eq_zero,
      hochschildCoboundary_connesB_add_connesB_hochschildCoboundary]

end ConnesB

section Cohomology

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M]
  [Module R M]

/-- The cohomology of the Hochschild cochain complex of a unital algebra `A` with `M`-valued
cochains in `n + 1` arguments. In Connes' cochain description this is the Hochschild cohomology
`HHⁿ(A, Hom_R(A, M))` of `A` with coefficients in the bimodule `Hom_R(A, M)`, not with
coefficients in `M`; for `M = R` it is `HHⁿ(A, A*)`, with coefficients in the dual bimodule. -/
abbrev hochschildCohomology (n : ℕ) : ModuleCat R :=
  (hochschildCochainComplex R A M).homology n

private theorem mem_hochschildCocycles_iff_complex (n : ℕ)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    φ ∈ hochschildCocycles R A M n ↔
      (hochschildCochainComplex R A M).d n (n + 1)
        ((hochschildCochainComplexXIso R A M n).inv φ) = 0 := by
  rw [mem_hochschildCocycles_iff]
  constructor
  · intro hφ
    apply (ModuleCat.mono_iff_injective (hochschildCochainComplexXIso R A M (n + 1)).hom).1
      inferInstance
    rw [hochschildCochainComplex_d_apply, Iso.inv_hom_id_apply, hφ, map_zero]
  · intro hφ
    have h := congrArg (hochschildCochainComplexXIso R A M (n + 1)).hom hφ
    rw [hochschildCochainComplex_d_apply, Iso.inv_hom_id_apply, map_zero] at h
    exact h

private theorem mem_hochschildCoboundaries_iff_complex (n : ℕ)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    φ ∈ hochschildCoboundaries R A M n ↔
      ∃ y : (hochschildCochainComplex R A M).X ((ComplexShape.up ℕ).prev n),
        (hochschildCochainComplex R A M).d ((ComplexShape.up ℕ).prev n) n y =
          (hochschildCochainComplexXIso R A M n).inv φ := by
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot, CochainComplex.prev_nat_zero,
      (hochschildCochainComplex R A M).shape 0 0 (by simp)]
    constructor
    · rintro rfl
      exact ⟨0, by rw [map_zero, map_zero]⟩
    · rintro ⟨y, hy⟩
      apply (ModuleCat.mono_iff_injective (hochschildCochainComplexXIso R A M 0).inv).1
        inferInstance
      rw [← hy]
      simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
  | succ n =>
    rw [mem_hochschildCoboundaries_succ_iff, CochainComplex.prev_nat_succ]
    constructor
    · rintro ⟨ψ, hψ⟩
      refine ⟨(hochschildCochainComplexXIso R A M n).inv ψ, ?_⟩
      apply (ModuleCat.mono_iff_injective (hochschildCochainComplexXIso R A M (n + 1)).hom).1
        inferInstance
      rw [hochschildCochainComplex_d_apply, Iso.inv_hom_id_apply, hψ, Iso.inv_hom_id_apply]
    · rintro ⟨ψ, hψ⟩
      refine ⟨(hochschildCochainComplexXIso R A M n).hom ψ, ?_⟩
      rw [← hochschildCochainComplex_d_apply, hψ, Iso.inv_hom_id_apply]

private abbrev hochschildToCycles (n : ℕ) (φ : hochschildCocycles R A M n) :=
  (hochschildCochainComplex R A M).moduleCatCyclesMk
    ((hochschildCochainComplexXIso R A M n).inv φ.1) (n + 1) (CochainComplex.next ℕ n)
    ((mem_hochschildCocycles_iff_complex R A M n φ.1).1 φ.2)

private theorem hochschild_iCycles_toCycles (n : ℕ) (φ : hochschildCocycles R A M n) :
    (hochschildCochainComplex R A M).iCycles n (hochschildToCycles R A M n φ) =
      (hochschildCochainComplexXIso R A M n).inv φ.1 :=
  (hochschildCochainComplex R A M).iCycles_moduleCatCyclesMk _ _ _ _ _

namespace hochschildCohomology

/-- The Hochschild cohomology class of a Hochschild cocycle. -/
def mk (n : ℕ) : hochschildCocycles R A M n →ₗ[R] hochschildCohomology R A M n :=
  (hochschildCochainComplex R A M).moduleCatCohomologyClassOfIso
    (fun n ↦ MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) (hochschildCocycles R A M)
    (hochschildCochainComplexXIso R A M) (mem_hochschildCocycles_iff_complex R A M) n

/-- The class of a Hochschild cocycle is the homology class of the corresponding cycle. -/
private theorem mk_apply (n : ℕ) (φ : hochschildCocycles R A M n) :
    mk R A M n φ = (hochschildCochainComplex R A M).homologyπ n (hochschildToCycles R A M n φ) :=
  (hochschildCochainComplex R A M).moduleCatCohomologyClassOfIso_apply
    (fun n ↦ MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) (hochschildCocycles R A M)
    (hochschildCochainComplexXIso R A M) (mem_hochschildCocycles_iff_complex R A M) n φ

/-- The class of a Hochschild cocycle `φ` is the homology class of any cycle of the Hochschild
cochain complex whose underlying cochain is `φ`. -/
theorem mk_eq_homologyπ {n : ℕ} (φ : hochschildCocycles R A M n)
    (z : (hochschildCochainComplex R A M).cycles n)
    (hz : (hochschildCochainComplexXIso R A M n).hom
      ((hochschildCochainComplex R A M).iCycles n z) = φ) :
    mk R A M n φ = (hochschildCochainComplex R A M).homologyπ n z :=
  (hochschildCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_homologyπ
    (fun n ↦ MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) (hochschildCocycles R A M)
    (hochschildCochainComplexXIso R A M) (mem_hochschildCocycles_iff_complex R A M) φ z hz

/-- Every Hochschild cohomology class is the class of a Hochschild cocycle. -/
theorem mk_surjective (n : ℕ) : Function.Surjective (mk R A M n) :=
  (hochschildCochainComplex R A M).moduleCatCohomologyClassOfIso_surjective
    (fun n ↦ MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) (hochschildCocycles R A M)
    (hochschildCochainComplexXIso R A M) (mem_hochschildCocycles_iff_complex R A M) n

/-- A Hochschild cocycle has zero cohomology class exactly when it is a Hochschild
coboundary. -/
@[simp]
theorem mk_eq_zero_iff (n : ℕ) (φ : hochschildCocycles R A M n) :
    mk R A M n φ = 0 ↔
      (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) ∈ hochschildCoboundaries R A M n :=
  (hochschildCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_zero_iff
    (fun n ↦ MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) (hochschildCocycles R A M)
    (hochschildCoboundaries R A M) (hochschildCochainComplexXIso R A M)
    (mem_hochschildCocycles_iff_complex R A M) (mem_hochschildCoboundaries_iff_complex R A M) n φ

/-- Two Hochschild cocycles have the same class exactly when they differ by a Hochschild
coboundary. -/
theorem mk_eq_mk_iff (n : ℕ) (φ ψ : hochschildCocycles R A M n) :
    mk R A M n φ = mk R A M n ψ ↔
      (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) - ψ ∈ hochschildCoboundaries R A M n :=
  (hochschildCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_iff
    (fun n ↦ MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) (hochschildCocycles R A M)
    (hochschildCoboundaries R A M) (hochschildCochainComplexXIso R A M)
    (mem_hochschildCocycles_iff_complex R A M) (mem_hochschildCoboundaries_iff_complex R A M) n
    φ ψ

/-- Connes' operator `B`, from Hochschild `(n + 1)`-cocycles to cyclic `n`-cocycles. -/
private def connesBCocycles (n : ℕ) :
    hochschildCocycles R A M (n + 1) →ₗ[R] cyclicCocycles R A M n :=
  LinearMap.codRestrict _
    (LinearMap.codRestrict _ (TauCeti.connesB R A M n) connesB_mem_cyclicCochains ∘ₗ
      (hochschildCocycles R A M (n + 1)).subtype)
    fun φ ↦ connesB_mem_cyclicCocycles φ.2

private theorem coe_connesBCocycles (n : ℕ) (φ : hochschildCocycles R A M (n + 1)) :
    connesBCocycles R A M n φ =
      ⟨⟨TauCeti.connesB R A M n φ, connesB_mem_cyclicCochains _⟩, connesB_mem_cyclicCocycles φ.2⟩ :=
  (rfl)

/-- The underlying Hochschild cocycle of a cycle of the Hochschild cochain complex. -/
private def cyclesToCocycles (n : ℕ) :
    (hochschildCochainComplex R A M).cycles n →ₗ[R] hochschildCocycles R A M n :=
  LinearMap.codRestrict _
    ((hochschildCochainComplexXIso R A M n).hom.hom ∘ₗ
      ((hochschildCochainComplex R A M).iCycles n).hom)
    fun z ↦ (mem_hochschildCocycles_iff_complex R A M n _).2 <| by
      -- `hochschildCochainComplexXIso` is the identity.
      change (hochschildCochainComplex R A M).d n (n + 1)
        ((hochschildCochainComplex R A M).iCycles n z) = 0
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d]
      rfl

private theorem coe_cyclesToCocycles (n : ℕ) (z : (hochschildCochainComplex R A M).cycles n) :
    (cyclesToCocycles R A M n z : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) =
      (hochschildCochainComplexXIso R A M n).hom ((hochschildCochainComplex R A M).iCycles n z) :=
  (rfl)

/-- The class of `B` of the underlying cocycle of a cycle of the Hochschild cochain complex. -/
private def connesBCycles (n : ℕ) :
    (hochschildCochainComplex R A M).cycles (n + 1) ⟶ cyclicCohomology R A M n :=
  ModuleCat.ofHom (cyclicCohomology.mk R A M n ∘ₗ connesBCocycles R A M n ∘ₗ
    cyclesToCocycles R A M (n + 1))

private theorem connesBCycles_apply (n : ℕ)
    (z : (hochschildCochainComplex R A M).cycles (n + 1)) :
    connesBCycles R A M n z =
      cyclicCohomology.mk R A M n (connesBCocycles R A M n (cyclesToCocycles R A M (n + 1) z)) :=
  (rfl)

/-- The class of `B` of a Hochschild coboundary vanishes. -/
private theorem toCycles_comp_connesBCycles (n : ℕ) :
    (hochschildCochainComplex R A M).toCycles n (n + 1) ≫ connesBCycles R A M n = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, connesBCycles_apply, coe_connesBCocycles,
    ModuleCat.hom_zero, LinearMap.zero_apply, cyclicCohomology.mk_eq_zero_iff]
  refine connesB_mem_cyclicCoboundaries (mem_hochschildCoboundaries_succ_iff.2
    ⟨(hochschildCochainComplexXIso R A M n).hom y, ?_⟩)
  have h := ConcreteCategory.congr_hom ((hochschildCochainComplex R A M).toCycles_i n (n + 1)) y
  rw [ConcreteCategory.comp_apply] at h
  rw [coe_cyclesToCocycles, h, hochschildCochainComplex_d_apply]

/-- The map `B : HHⁿ⁺¹(A, Hom_R(A, M)) → HCⁿ(A; M)` induced by Connes' operator `B`; when `R`
contains `ℚ` it is the map `B` of the SBI sequence. -/
def connesB (n : ℕ) : hochschildCohomology R A M (n + 1) ⟶ cyclicCohomology R A M n :=
  Cofork.IsColimit.desc ((hochschildCochainComplex R A M).homologyIsCokernel n (n + 1) (by simp))
    (connesBCycles R A M n) (by rw [toCycles_comp_connesBCycles, Limits.zero_comp])

private theorem homologyπ_comp_connesB (n : ℕ) :
    (hochschildCochainComplex R A M).homologyπ (n + 1) ≫ connesB R A M n = connesBCycles R A M n :=
  Cofork.IsColimit.π_desc' ((hochschildCochainComplex R A M).homologyIsCokernel n (n + 1) (by simp))
    _ _

/-- The map `B` sends the class of a Hochschild cocycle `φ` to the cyclic class of `B φ`. -/
@[simp]
theorem connesB_mk {n : ℕ} (φ : hochschildCocycles R A M (n + 1)) :
    connesB R A M n (mk R A M (n + 1) φ) =
      cyclicCohomology.mk R A M n
        ⟨⟨TauCeti.connesB R A M n φ, connesB_mem_cyclicCochains _⟩,
          connesB_mem_cyclicCocycles φ.2⟩ := by
  rw [mk_apply, ← ConcreteCategory.comp_apply, homologyπ_comp_connesB, connesBCycles_apply,
    ← coe_connesBCocycles]
  congr 2
  rw [Subtype.ext_iff, coe_cyclesToCocycles, hochschild_iCycles_toCycles, Iso.inv_hom_id_apply]

end hochschildCohomology

namespace cyclicCohomology

/-- The map `I : HCⁿ(A; M) → HHⁿ(A, Hom_R(A, M))` induced by the inclusion of the cyclic cochain
complex into the Hochschild cochain complex; when `R` contains `ℚ` it is the map `I` of the SBI
sequence. -/
def toHochschild (n : ℕ) : cyclicCohomology R A M n ⟶ hochschildCohomology R A M n :=
  HomologicalComplex.homologyMap (cyclicCochainComplexι R A M) n

/-- The map `I` sends the class of a cyclic cocycle to the Hochschild class of the same
cochain. -/
@[simp]
theorem toHochschild_mk {n : ℕ} (φ : cyclicCocycles R A M n) :
    toHochschild R A M n (mk R A M n φ) =
      hochschildCohomology.mk R A M n
        ⟨φ, mem_hochschildCocycles_of_mem_cyclicCocycles φ.2⟩ := by
  -- A cyclic cocycle, viewed in the cyclic cochain complex, is killed by the differential.
  have hφ (ψ : cyclicCocycles R A M n) : (cyclicCochainComplex R A M).d n (n + 1)
      ((cyclicCochainComplexXIso R A M n).inv ψ.1) = 0 := by
    apply (ModuleCat.mono_iff_injective (cyclicCochainComplexXIso R A M (n + 1)).hom).1
      inferInstance
    rw [cyclicCochainComplex_d_apply, Iso.inv_hom_id_apply, map_zero, ← Subtype.coe_inj,
      coe_cyclicHochschildCoboundary_apply, ZeroMemClass.coe_zero]
    exact (mem_cyclicCocycles_iff R A M).1 ψ.2
  -- The naturality of the class map along the inclusion of the cyclic cochain complex.
  have key := HomologicalComplex.homologyMap_moduleCatHomologyClass (CochainComplex.next ℕ n)
    ((cyclicCochainComplexXIso R A M n).inv.hom ∘ₗ (cyclicCocycles R A M n).subtype) (fun ψ ↦ hφ ψ)
    (cyclicCochainComplexι R A M)
    ((hochschildCochainComplexXIso R A M n).inv.hom ∘ₗ (hochschildCocycles R A M n).subtype)
    (fun ψ ↦ (mem_hochschildCocycles_iff_complex R A M n ψ.1).1 ψ.2)
    (((cyclicCochains R A M n).subtype ∘ₗ (cyclicCocycles R A M n).subtype).codRestrict _
      fun ψ ↦ mem_hochschildCocycles_of_mem_cyclicCocycles ψ.2)
    (fun ψ ↦ by
      apply (ModuleCat.mono_iff_injective (hochschildCochainComplexXIso R A M n).hom).1
        inferInstance
      simp [cyclicCochainComplexι_f_apply]
      -- `codRestrict` keeps the underlying cochain.
      rfl) φ
  rw [(cyclicCochainComplex R A M).moduleCatHomologyClass_apply (CochainComplex.next ℕ n)
      ((cyclicCochainComplexXIso R A M n).inv.hom ∘ₗ (cyclicCocycles R A M n).subtype)
      (fun ψ ↦ hφ ψ),
    (hochschildCochainComplex R A M).moduleCatHomologyClass_apply (CochainComplex.next ℕ n)
      ((hochschildCochainComplexXIso R A M n).inv.hom ∘ₗ (hochschildCocycles R A M n).subtype)
      (fun ψ ↦ (mem_hochschildCocycles_iff_complex R A M n ψ.1).1 ψ.2)] at key
  rw [toHochschild, hochschildCohomology.mk_apply,
    mk_eq_homologyπ R A M φ ((cyclicCochainComplex R A M).moduleCatCyclesMk _ (n + 1)
      (CochainComplex.next ℕ n) (hφ φ))
      (by rw [HomologicalComplex.iCycles_moduleCatCyclesMk, Iso.inv_hom_id_apply])]
  exact key

/-- The composite `B ∘ I : HCⁿ⁺¹(A; M) → HHⁿ⁺¹(A, Hom_R(A, M)) → HCⁿ(A; M)` vanishes, since Connes'
operator `B` vanishes on cyclic cochains. This holds over every commutative ring `R`. -/
@[reassoc (attr := simp)]
theorem toHochschild_comp_connesB (n : ℕ) :
    toHochschild R A M (n + 1) ≫ hochschildCohomology.connesB R A M n = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  obtain ⟨φ, rfl⟩ := mk_surjective R A M (n + 1) x
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, toHochschild_mk, hochschildCohomology.connesB_mk,
    ModuleCat.hom_zero, LinearMap.zero_apply, mk_eq_zero_iff]
  convert Submodule.zero_mem _
  ext1
  exact connesB_eq_zero_of_mem_cyclicCochains φ.1.2

/-- In degree zero the map `I : HC⁰(A; M) → HH⁰(A, Hom_R(A, M))` is an isomorphism: every
`0`-cochain is cyclic and there are no coboundaries in degree zero. -/
instance isIso_toHochschild_zero : IsIso (toHochschild R A M 0) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y hxy ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨φ, rfl⟩ := mk_surjective R A M 0 x
    obtain ⟨ψ, rfl⟩ := mk_surjective R A M 0 y
    rw [toHochschild_mk, toHochschild_mk, hochschildCohomology.mk_eq_mk_iff,
      hochschildCoboundaries_zero, Submodule.mem_bot, sub_eq_zero] at hxy
    rw [mk_eq_mk_iff, cyclicCoboundaries_zero, Submodule.mem_bot, sub_eq_zero]
    exact Subtype.ext hxy
  · obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M 0 x
    have hφ : φ.1 ∈ cyclicCochains R A M 0 := by simp
    refine ⟨mk R A M 0 ⟨⟨φ, hφ⟩, (mem_cyclicCocycles_iff R A M).2 φ.2⟩, ?_⟩
    rw [toHochschild_mk]

end cyclicCohomology

end Cohomology

end TauCeti
