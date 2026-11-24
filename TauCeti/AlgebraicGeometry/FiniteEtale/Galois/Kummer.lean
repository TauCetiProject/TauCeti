/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Topology
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Category
public import TauCeti.AlgebraicGeometry.FiniteEtale.Kummer
public import TauCeti.RingTheory.RootsOfUnity.TateModule

import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Kummer monodromy over an affine base

Let `R` be a commutative ring with a unit `t ∈ Rˣ`, and let `Spec Ω ⟶ Spec R` be a geometric point
valued in a separably closed field `Ω` sending `t` to `1`. For any `n` invertible in `R`, the
geometric fibre over `Spec Ω ⟶ Spec R` of the degree-`n` Kummer cover
`Spec R[x] / (x ^ n - t)` is identified with `μ_n(Ω)` (`kummerCoverFiberEquivRootsOfUnity`), of
cardinality `n` (`card_kummerCoverFiber`).

When every `n`-th root of unity of `Ω` lifts to an `n`-th root of unity of `R` (so `R` supplies a
transitive group of deck transformations via `kummerCoverDeck`), naturality of the Galois action
with deck transformations shows that every automorphism `σ ∈ Aut (fiber x)` acts on the Kummer
fibre `μ_n(Ω)` by multiplication by a root of unity `kummerMonodromyLevel σ ∈ μ_n(Ω)`, namely the
image of `1`. Compatibility along the Kummer transition maps `kummerCoverMap` assembles these
finite-level characters into a continuous group homomorphism
`kummerMonodromy : Aut (fiber x) →ₜ* PrimeToPTateModule p Ω`, which is surjective whenever
`Spec R` and the prime-to-`p` Kummer covers are connected.

## Main definitions

* `TauCeti.FiniteEtaleScheme.kummerMonodromyLevel`: the level-`n` Kummer character
  `Aut (fiber x) →* rootsOfUnity n Ω`.
* `TauCeti.FiniteEtaleScheme.kummerMonodromy`: the assembled continuous homomorphism
  `Aut (fiber x) →ₜ* PrimeToPTateModule p Ω`.

## Main results

* `TauCeti.FiniteEtaleScheme.kummerCoverFiberEquivRootsOfUnity_smul`: `Aut (fiber x)` acts on the
  Kummer fibre `μ_n(Ω)` by multiplication by `kummerMonodromyLevel`.
* `TauCeti.FiniteEtaleScheme.card_kummerCoverFiber`: the geometric fibre over `1` of a degree-`n`
  Kummer cover has cardinality `n`.
* `TauCeti.FiniteEtaleScheme.isLocallyConstant_kummerMonodromyLevel`: each finite-level Kummer
  character is locally constant on `Aut (fiber x)`.
* `TauCeti.FiniteEtaleScheme.kummerMonodromyLevel_pow_div`: compatibility of the finite-level
  characters along the power maps `μ_m(Ω) → μ_n(Ω)` for `n ∣ m`.
* `TauCeti.FiniteEtaleScheme.kummerMonodromyLevel_surjective`: surjectivity of a finite-level
  Kummer character when `Spec R` and the degree-`n` Kummer cover are connected.
* `TauCeti.FiniteEtaleScheme.proj_kummerMonodromy`: projecting `kummerMonodromy` to level `m`
  recovers `kummerMonodromyLevel`.
* `TauCeti.FiniteEtaleScheme.kummerMonodromy_surjective`: surjectivity of `kummerMonodromy` when
  `Spec R` and all prime-to-`p` Kummer covers are connected.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental (SGA 1)*, Exposé XIII, §2.
* T. Szamuely, *Galois Groups and Fundamental Groups*, Example 4.6.12 (2).
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped PreGaloisCategory

universe u

namespace TauCeti.FiniteEtaleScheme

section KummerMonodromy

variable {R : CommRingCat.{u}} (t : Rˣ) (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]

/-- On the fibre `μ_n(Ω)` over `1` of a Kummer cover, if every `n`-th root of unity of `Ω` lifts to
an `n`-th root of unity of `R`, then an automorphism `σ` of the geometric fibre functor acts by
multiplication by the image under `σ` of the base point `1 ∈ μ_n(Ω)`: deck transformations commute
with `σ` and act transitively on `μ_n(Ω)`. -/
private theorem kummerCoverFiberEquivRootsOfUnity_smul_aux (n : ℕ) (hn : IsUnit (n : R))
    (ht : algebraMap R Ω t = 1)
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))))
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    kummerCoverFiberEquivRootsOfUnity t Ω n hn ht (σ • y) =
      kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
        (σ • (kummerCoverFiberEquivRootsOfUnity t Ω n hn ht).symm 1) *
        kummerCoverFiberEquivRootsOfUnity t Ω n hn ht y := by
  set e := kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
  obtain ⟨ζ, hζ⟩ := hdeck (e y)
  have hy : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).map
      (kummerCoverDeck t hn ζ).hom (e.symm 1) = y :=
    e.injective <| by
      rw [kummerCoverFiberEquivRootsOfUnity_map_kummerCoverDeck, hζ, e.apply_symm_apply, mul_one]
  rw [← hy, PreGaloisCategory.mulAction_naturality,
    kummerCoverFiberEquivRootsOfUnity_map_kummerCoverDeck, hζ, hy, mul_comm]

/-- **Level-`n` Kummer monodromy.** At a geometric point `Spec Ω ⟶ Spec R` sending the unit `t` to
`1`, when every `n`-th root of unity of `Ω` lifts to `R`, an automorphism of the geometric fibre
functor acts on the degree-`n` Kummer fibre `μ_n(Ω)` by multiplication by a root of unity, giving a
group homomorphism `Aut (fiber x) →* μ_n(Ω)`. -/
noncomputable def kummerMonodromyLevel (n : ℕ) (hn : IsUnit (n : R)) (ht : algebraMap R Ω t = 1)
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n)) :
    Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) →* rootsOfUnity n Ω where
  toFun σ := kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
    (σ • (kummerCoverFiberEquivRootsOfUnity t Ω n hn ht).symm 1)
  map_one' := by simp
  map_mul' σ τ := by
    rw [mul_smul, kummerCoverFiberEquivRootsOfUnity_smul_aux t Ω n hn ht hdeck σ]

/-- The level-`n` Kummer character evaluates an automorphism at the canonical point `1` of the
fibre `μ_n(Ω)`. -/
theorem kummerMonodromyLevel_apply (n : ℕ) (hn : IsUnit (n : R)) (ht : algebraMap R Ω t = 1)
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) :
    kummerMonodromyLevel t Ω n hn ht hdeck σ =
      kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
        (σ • (kummerCoverFiberEquivRootsOfUnity t Ω n hn ht).symm 1) :=
  (rfl)

/-- **Action on the Kummer fibre.** Every `σ ∈ Aut (fiber x)` multiplies elements of the Kummer
fibre `μ_n(Ω)` over `1` by `kummerMonodromyLevel t Ω n hn ht hdeck σ`. -/
theorem kummerCoverFiberEquivRootsOfUnity_smul (n : ℕ) (hn : IsUnit (n : R))
    (ht : algebraMap R Ω t = 1)
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))))
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    kummerCoverFiberEquivRootsOfUnity t Ω n hn ht (σ • y) =
      kummerMonodromyLevel t Ω n hn ht hdeck σ *
        kummerCoverFiberEquivRootsOfUnity t Ω n hn ht y :=
  kummerCoverFiberEquivRootsOfUnity_smul_aux t Ω n hn ht hdeck σ y

/-- Over a separably closed field `Ω` sending `t` to `1`, the geometric fibre of the degree-`n`
Kummer cover has cardinality `n`. -/
theorem card_kummerCoverFiber (n : ℕ) (hn : IsUnit (n : R)) (ht : algebraMap R Ω t = 1) :
    Nat.card ((fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj
      (kummerCover t n hn)) = n := by
  have hnΩ : (n : Ω) ≠ 0 := (by simpa using hn.map (algebraMap R Ω) : IsUnit (n : Ω)).ne_zero
  have : NeZero (n : Ω) := ⟨hnΩ⟩
  have : NeZero n := .of_neZero_natCast Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω n
  rw [Nat.card_congr (kummerCoverFiberEquivRootsOfUnity t Ω n hn ht)]
  exact hζ.card_rootsOfUnity

/-- Each finite-level Kummer character is locally constant on `Aut (fiber x)`. -/
theorem isLocallyConstant_kummerMonodromyLevel (n : ℕ) (hn : IsUnit (n : R))
    (ht : algebraMap R Ω t = 1)
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n)) :
    IsLocallyConstant (kummerMonodromyLevel t Ω n hn ht hdeck) := by
  let e := kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
  have hcont : Continuous fun σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) ↦
      σ • e.symm 1 := continuous_id.smul continuous_const
  exact ((IsLocallyConstant.iff_continuous _).mpr hcont).comp e

/-- For `n ∣ m`, the level-`m` and level-`n` Kummer characters are compatible along the
`(m / n)`-th power map `μ_m(Ω) → μ_n(Ω)`. -/
theorem kummerMonodromyLevel_pow_div {n m : ℕ} (hn : IsUnit (n : R)) (hm : IsUnit (m : R))
    (ht : algebraMap R Ω t = 1)
    (hdeck_n : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    (hdeck_m : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) m))
    (h : n ∣ m) (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) :
    (kummerMonodromyLevel t Ω m hm ht hdeck_m σ : Ωˣ) ^ (m / n) =
      kummerMonodromyLevel t Ω n hn ht hdeck_n σ := by
  let e_n := kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
  let e_m := kummerCoverFiberEquivRootsOfUnity t Ω m hm ht
  have hmap_one : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).map
      (kummerCoverMap t hn hm h) (e_m.symm 1) = e_n.symm 1 := by
    apply e_n.injective
    apply Subtype.ext
    rw [kummerCoverFiberEquivRootsOfUnity_map_kummerCoverMap, e_m.apply_symm_apply,
      e_n.apply_symm_apply]
    simp
  rw [kummerMonodromyLevel_apply,
    ← kummerCoverFiberEquivRootsOfUnity_map_kummerCoverMap t hn hm ht h,
    ← PreGaloisCategory.mulAction_naturality, hmap_one, kummerMonodromyLevel_apply]

/-- Over a connected base `Spec R`, if the degree-`n` Kummer cover is connected, then the level-`n`
Kummer character is surjective: `Aut (fiber x)` acts transitively on the fibre of a connected
cover. -/
theorem kummerMonodromyLevel_surjective [ConnectedSpace (Spec R)] (n : ℕ) (hn : IsUnit (n : R))
    (ht : algebraMap R Ω t = 1)
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    [PreGaloisCategory.IsConnected (kummerCover t n hn)] :
    Function.Surjective (kummerMonodromyLevel t Ω n hn ht hdeck) := fun ζ ↦ by
  let e := kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq
    (Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) (e.symm 1) (e.symm ζ)
  exact ⟨σ, by rw [kummerMonodromyLevel_apply, hσ, e.apply_symm_apply]⟩

/-- **Assembled Kummer monodromy.** The compatible finite-level Kummer characters assemble into a
continuous group homomorphism `Aut (fiber x) →ₜ* PrimeToPTateModule p Ω`. -/
noncomputable def kummerMonodromy (p : ℕ) (ht : algebraMap R Ω t = 1)
    (hunit : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, IsUnit ((m : ℕ) : R))
    (hdeck : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p},
      Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) m)) :
    Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) →ₜ* PrimeToPTateModule p Ω where
  toMonoidHom := PrimeToPTateModule.lift
    (fun m ↦ kummerMonodromyLevel t Ω m (hunit m) ht (hdeck m))
    fun m n σ h ↦ kummerMonodromyLevel_pow_div t Ω (hunit n) (hunit m) ht (hdeck n) (hdeck m) h σ
  continuous_toFun := PrimeToPTateModule.continuous_iff.mpr fun m ↦ by
    simpa only [MonoidHom.toFun_eq_coe, PrimeToPTateModule.proj_lift] using
      isLocallyConstant_kummerMonodromyLevel t Ω m (hunit m) ht (hdeck m)

/-- Projecting `kummerMonodromy` to level `m` recovers `kummerMonodromyLevel`. -/
@[simp]
theorem proj_kummerMonodromy (p : ℕ) (ht : algebraMap R Ω t = 1)
    (hunit : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, IsUnit ((m : ℕ) : R))
    (hdeck : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p},
      Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) m))
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p})
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) :
    PrimeToPTateModule.proj m (kummerMonodromy t Ω p ht hunit hdeck σ) =
      kummerMonodromyLevel t Ω m (hunit m) ht (hdeck m) σ :=
  PrimeToPTateModule.proj_lift _ _ m σ

/-- Over a connected base `Spec R`, if all prime-to-`p` Kummer covers along `t` are connected, then
`kummerMonodromy` is surjective onto `PrimeToPTateModule p Ω`. -/
theorem kummerMonodromy_surjective [ConnectedSpace (Spec R)] (p : ℕ) (ht : algebraMap R Ω t = 1)
    (hunit : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, IsUnit ((m : ℕ) : R))
    (hdeck : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p},
      Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) m))
    (hconn : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p},
      PreGaloisCategory.IsConnected (kummerCover t m (hunit m))) :
    Function.Surjective (kummerMonodromy t Ω p ht hunit hdeck) :=
  PrimeToPTateModule.surjective_of_forall_surjective_proj
    (kummerMonodromy t Ω p ht hunit hdeck).continuous fun m ↦ by
      have := hconn m
      simpa only [proj_kummerMonodromy] using
        kummerMonodromyLevel_surjective t Ω m (hunit m) ht (hdeck m)

end KummerMonodromy

end TauCeti.FiniteEtaleScheme
