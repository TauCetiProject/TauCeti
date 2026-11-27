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

import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Connected
import TauCeti.RingTheory.RootsOfUnity.Basic
import TauCeti.RingTheory.RootsOfUnity.PowFiber

/-!
# Kummer monodromy over an affine base

Let `R` be a commutative ring, `t` a unit of `R`, and `x : Spec Ω ⟶ Spec R` a geometric point,
given by an `R`-algebra structure on a separably closed field `Ω`. For `n` invertible in `R`, the
geometric fibre at `x` of the Kummer cover `Spec R[y]/(y ^ n - t) ⟶ Spec R` is the set of `n`-th
roots of the image of `t` in `Ω` (`TauCeti.FiniteEtaleScheme.kummerCoverFiberEquiv`). It has
cardinality `n` (`card_kummerCoverFiber`), and when `x` sends `t` to `1` it is `μ_n(Ω)`
(`kummerCoverFiberEquivRootsOfUnity`).

Suppose that every `n`-th root of unity of `Ω` comes from an `n`-th root of unity of `R`, as for
`R = K[T, T⁻¹]` with `K` algebraically closed and `n` invertible in `K`. Then the deck
transformations `y ↦ ζ y` act transitively on the fibre
(`TauCeti.FiniteEtaleScheme.exists_fiber_map_kummerCoverDeck_eq`). Since automorphisms of the fibre
functor commute with deck transformations, every `σ ∈ π₁(Spec R, x)` multiplies all the `n`-th
roots of `t` by one and the same root of unity `χₙ(σ) ∈ μ_n(Ω)`. This is the level-`n` *Kummer
character*

`TauCeti.FiniteEtaleScheme.kummerMonodromyLevel : π₁(Spec R, x) →* μ_n(Ω)`,

a locally constant homomorphism, characterized by `σ • y = χₙ(σ) * y` on the fibre
(`TauCeti.FiniteEtaleScheme.kummerCoverFiberEquiv_smul`). Along the maps between Kummer covers the
characters are compatible with the power maps: `χₘ(σ) ^ (m / n) = χₙ(σ)` for `n ∣ m`. Hence, if
the hypotheses hold for every nonzero `m` prime to `p`, the characters assemble into a continuous
homomorphism to the prime-to-`p` Tate module of `Ω`
(`TauCeti.FiniteEtaleScheme.kummerMonodromy`):

`π₁(Spec R, x) →ₜ* lim_{m ≠ 0, (m, p) = 1} μ_m(Ω) = ℤ̂^{(p')}(1)`.

When the Kummer covers are connected, so is the base `Spec R`, and `π₁` acts transitively on their
fibres, so the Kummer characters and the Tate character are surjective. For `R = K[T, T⁻¹]`,
`t = T` and `K` algebraically closed of characteristic exponent `p`, the Kummer covers are the
power maps `z ↦ z ^ m` of `𝔾_m` over `K`, and `kummerMonodromy` is the monodromy of the tower of
these covers.

## Main definitions

* `TauCeti.FiniteEtaleScheme.kummerMonodromyLevel`: the level-`n` Kummer character
  `Aut (fiber x) →* rootsOfUnity n Ω` of the unit `t`.
* `TauCeti.FiniteEtaleScheme.kummerMonodromy`: the compatible family of Kummer characters of
  orders prime to `p`, a continuous homomorphism `Aut (fiber x) →ₜ* PrimeToPTateModule p Ω`.

## Main results

* `TauCeti.FiniteEtaleScheme.kummerCoverFiberEquiv_smul`,
  `TauCeti.FiniteEtaleScheme.kummerMonodromyLevel_eq_iff`: the defining property of the Kummer
  character.
* `TauCeti.FiniteEtaleScheme.kummerMonodromyLevel_apply`,
  `TauCeti.FiniteEtaleScheme.kummerCoverFiberEquivRootsOfUnity_smul`: when `x` sends `t` to `1`,
  the Kummer character is the image of the point `1` of the fibre `μ_n(Ω)`, and `Aut (fiber x)`
  acts on `μ_n(Ω)` by multiplication by it.
* `TauCeti.FiniteEtaleScheme.isLocallyConstant_kummerMonodromyLevel`: the Kummer character is
  locally constant, so continuous for the discrete topology on `μ_n(Ω)`.
* `TauCeti.FiniteEtaleScheme.kummerMonodromyLevel_pow_div`: compatibility with the power maps.
* `TauCeti.FiniteEtaleScheme.proj_kummerMonodromy`: projecting `kummerMonodromy` to level `m`
  recovers `kummerMonodromyLevel`.
* `TauCeti.FiniteEtaleScheme.kummerMonodromyLevel_surjective`,
  `TauCeti.FiniteEtaleScheme.kummerMonodromy_surjective`: surjectivity for connected Kummer
  covers.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental (SGA 1)*, Exposé XIII, §2
  (Corollary 2.12).
* H. W. Lenstra, *Galois theory for schemes*, Section 5.
* T. Szamuely, *Galois Groups and Fundamental Groups*, Example 4.6.12 (2).
-/

public section

open CategoryTheory AlgebraicGeometry PreGaloisCategory

universe u

namespace TauCeti.FiniteEtaleScheme

section KummerMonodromy

variable {R : CommRingCat.{u}} (t : Rˣ) (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]

/-- Two roots of unity that multiply a nonzero `n`-th root of `t` to the same element agree. -/
private theorem eq_of_mul_kummerCoverFiberEquiv_eq {n : ℕ} {hn : IsUnit (n : R)}
    {ζ ξ : rootsOfUnity n Ω}
    {y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)}
    (h : ((ζ : Ωˣ) : Ω) * kummerCoverFiberEquiv t Ω n hn y =
      ((ξ : Ωˣ) : Ω) * kummerCoverFiberEquiv t Ω n hn y) : ζ = ξ :=
  Subtype.ext (Units.ext (mul_right_cancel₀ (kummerCoverFiberEquiv_ne_zero t hn y) h))

/-- An automorphism of the geometric fibre functor multiplies all `n`-th roots of `t` in the
fibre of the Kummer cover by the same root of unity. -/
private theorem exists_kummerCoverFiberEquiv_smul (n : ℕ) (hn : IsUnit (n : R))
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) :
    ∃ ζ : rootsOfUnity n Ω, ∀ y, (kummerCoverFiberEquiv t Ω n hn (σ • y) : Ω) =
      ((ζ : Ωˣ) : Ω) * kummerCoverFiberEquiv t Ω n hn y := by
  obtain ⟨y₀⟩ := nonempty_fiber_kummerCover t (Ω := Ω) hn
  obtain ⟨ξ, hξ⟩ := exists_fiber_map_kummerCoverDeck_eq t hn hdeck y₀ (σ • y₀)
  refine ⟨restrictRootsOfUnity (algebraMap R Ω) n ξ, fun y ↦ ?_⟩
  obtain ⟨η, rfl⟩ := exists_fiber_map_kummerCoverDeck_eq t hn hdeck y₀ y
  -- `σ` commutes with the deck transformation of `η`.
  rw [mulAction_naturality, ← hξ]
  simp only [kummerCoverFiberEquiv_map_kummerCoverDeck, restrictRootsOfUnity_coe_apply]
  ring

/-- **Level-`n` Kummer monodromy**, the Kummer character of the unit `t` at the geometric point
`x : Spec Ω ⟶ Spec R`. For `n` invertible in `R`, assume every `n`-th root of unity of `Ω` comes
from `R`. Then an element `σ` of the étale fundamental group `π₁(Spec R, x) = Aut (fiber x)`
multiplies every `n`-th root of `t` in the geometric fibre of the Kummer cover by the same root of
unity `kummerMonodromyLevel t Ω n hn hdeck σ` (`kummerCoverFiberEquiv_smul`). -/
noncomputable def kummerMonodromyLevel (n : ℕ) (hn : IsUnit (n : R))
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n)) :
    Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) →* rootsOfUnity n Ω :=
  MonoidHom.mk' (fun σ ↦ (exists_kummerCoverFiberEquiv_smul t Ω n hn hdeck σ).choose) fun σ τ ↦ by
    obtain ⟨y₀⟩ := nonempty_fiber_kummerCover t (Ω := Ω) hn
    -- The action of `ρ` on the fibre is multiplication by the chosen root of unity.
    have hρ := fun ρ ↦ (exists_kummerCoverFiberEquiv_smul t Ω n hn hdeck ρ).choose_spec
    refine eq_of_mul_kummerCoverFiberEquiv_eq t Ω (y := y₀) ?_
    rw [← hρ (σ * τ) y₀, mul_smul, hρ σ (τ • y₀), hρ τ y₀]
    simp only [Subgroup.coe_mul, Units.val_mul, mul_assoc]

/-- **The defining property of the Kummer character**: `σ` acts on the `n`-th roots of `t` in the
geometric fibre of the Kummer cover by multiplication by `kummerMonodromyLevel t Ω n hn hdeck σ`. -/
@[simp]
theorem kummerCoverFiberEquiv_smul (n : ℕ) (hn : IsUnit (n : R))
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))))
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    (kummerCoverFiberEquiv t Ω n hn (σ • y) : Ω) =
      ((kummerMonodromyLevel t Ω n hn hdeck σ : Ωˣ) : Ω) * kummerCoverFiberEquiv t Ω n hn y :=
  (exists_kummerCoverFiberEquiv_smul t Ω n hn hdeck σ).choose_spec y

/-- The Kummer character is determined by the action on a single point of the geometric fibre. -/
theorem kummerMonodromyLevel_eq_iff {n : ℕ} {hn : IsUnit (n : R)}
    {hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n)}
    {σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))} {ζ : rootsOfUnity n Ω}
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    kummerMonodromyLevel t Ω n hn hdeck σ = ζ ↔ (kummerCoverFiberEquiv t Ω n hn (σ • y) : Ω) =
      ((ζ : Ωˣ) : Ω) * kummerCoverFiberEquiv t Ω n hn y :=
  ⟨fun h ↦ h ▸ kummerCoverFiberEquiv_smul t Ω n hn hdeck σ y, fun h ↦
    eq_of_mul_kummerCoverFiberEquiv_eq t Ω
      ((kummerCoverFiberEquiv_smul t Ω n hn hdeck σ y).symm.trans h)⟩

/-- **Action on the Kummer fibre over `1`.** When the geometric point sends `t` to `1`, every
`σ ∈ Aut (fiber x)` multiplies elements of the Kummer fibre `μ_n(Ω)` by
`kummerMonodromyLevel t Ω n hn hdeck σ`. -/
@[simp]
theorem kummerCoverFiberEquivRootsOfUnity_smul (n : ℕ) (hn : IsUnit (n : R))
    (ht : algebraMap R Ω t = 1)
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))))
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    kummerCoverFiberEquivRootsOfUnity t Ω n hn ht (σ • y) =
      kummerMonodromyLevel t Ω n hn hdeck σ *
        kummerCoverFiberEquivRootsOfUnity t Ω n hn ht y :=
  Subtype.ext (Units.ext (by simp [kummerCoverFiberEquiv_smul t Ω n hn hdeck]))

/-- When the geometric point sends `t` to `1`, the level-`n` Kummer character evaluates an
automorphism at the canonical point `1` of the fibre `μ_n(Ω)`. -/
theorem kummerMonodromyLevel_apply (n : ℕ) (hn : IsUnit (n : R)) (ht : algebraMap R Ω t = 1)
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) :
    kummerMonodromyLevel t Ω n hn hdeck σ =
      kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
        (σ • (kummerCoverFiberEquivRootsOfUnity t Ω n hn ht).symm 1) := by
  rw [kummerCoverFiberEquivRootsOfUnity_smul t Ω n hn ht hdeck, Equiv.apply_symm_apply, mul_one]

/-- **Continuity of the Kummer character.** The Kummer character is locally constant on the
profinite group `π₁(Spec R, x)`: it only depends on the action on one point of the geometric
fibre of the Kummer cover, which is locally constant. -/
theorem isLocallyConstant_kummerMonodromyLevel (n : ℕ) (hn : IsUnit (n : R))
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n)) :
    IsLocallyConstant (kummerMonodromyLevel t Ω n hn hdeck) := by
  obtain ⟨y⟩ := nonempty_fiber_kummerCover t (Ω := Ω) hn
  have hy : IsLocallyConstant fun σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) ↦
      σ • y :=
    (IsLocallyConstant.iff_continuous _).mpr (continuous_id.smul continuous_const)
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun σ ↦ ?_
  filter_upwards [hy.eventually_eq σ] with τ hτ
  rw [kummerMonodromyLevel_eq_iff t Ω y, hτ, kummerCoverFiberEquiv_smul]

/-- **Compatibility with the power maps.** For `n ∣ m`, the level-`m` Kummer character raised to
the power `m / n` is the level-`n` Kummer character: the map from the Kummer cover of degree `m`
to that of degree `n` raises roots of `t` to the power `m / n`. -/
theorem kummerMonodromyLevel_pow_div {n m : ℕ} (hn : IsUnit (n : R)) (hm : IsUnit (m : R))
    (hdeck_n : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    (hdeck_m : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) m))
    (h : n ∣ m) (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) :
    (kummerMonodromyLevel t Ω m hm hdeck_m σ : Ωˣ) ^ (m / n) =
      kummerMonodromyLevel t Ω n hn hdeck_n σ := by
  obtain ⟨y⟩ := nonempty_fiber_kummerCover t (Ω := Ω) hm
  rw [← coe_rootsOfUnityPowOfDvd_apply h]
  refine congrArg Subtype.val ((kummerMonodromyLevel_eq_iff t Ω
    ((fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).map
      (kummerCoverMap t hn hm h) y)).mpr ?_).symm
  rw [mulAction_naturality]
  simp only [kummerCoverFiberEquiv_map_kummerCoverMap, kummerCoverFiberEquiv_smul t Ω m hm hdeck_m,
    coe_rootsOfUnityPowOfDvd_apply, mul_pow, Units.val_pow_eq_pow_val]

/-- **Surjectivity of the Kummer character.** Under the hypotheses defining the Kummer character
(`n` invertible in `R` and every `n`-th root of unity of `Ω` coming from `R`), if moreover the
Kummer cover is connected, the fundamental group acts transitively on its geometric fibre, so every
`n`-th root of unity of `Ω` is a value of the Kummer character. -/
theorem kummerMonodromyLevel_surjective (n : ℕ) (hn : IsUnit (n : R))
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    [hconn : IsConnected (kummerCover t n hn)] :
    Function.Surjective (kummerMonodromyLevel t Ω n hn hdeck) := by
  -- `Spec R` is connected, as the image of the connected Kummer cover under a surjective map.
  have := (isConnected_iff_connectedSpace _).mp hconn
  have : ConnectedSpace (Spec R) := (kummerCover t n hn).obj.hom.surjective.connectedSpace
    (kummerCover t n hn).obj.hom.continuous
  intro ζ
  obtain ⟨y⟩ := nonempty_fiber_kummerCover t (Ω := Ω) hn
  set e := kummerCoverFiberEquiv t Ω n hn
  have hζ : (((ζ : Ωˣ) : Ω) * e y) ^ n = algebraMap R Ω t := by
    simpa only [rootsOfUnity.smul_eq_mul] using
      (rootsOfUnity.smul_pow ζ (e y : Ω)).trans (e y).property
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut (fiber (Spec.map
    (CommRingCat.ofHom (algebraMap R Ω))))) y (e.symm ⟨_, hζ⟩)
  exact ⟨σ, (kummerMonodromyLevel_eq_iff t Ω y).mpr (by rw [hσ, e.apply_symm_apply])⟩

/-- **Assembled Kummer monodromy.** Suppose that every nonzero `m` prime to `p` is invertible in
`R` (`hunit`) and that every `m`-th root of unity of `Ω` comes from an `m`-th root of unity of `R`
(`hdeck`), so that the Kummer character of the unit `t` of every such order `m` is defined. These
characters are compatible along the power maps, so they define a continuous homomorphism from
`π₁(Spec R, x)` to the Tate module `lim_{m ≠ 0, (m, p) = 1} μ_m(Ω)`. -/
noncomputable def kummerMonodromy (p : ℕ)
    (hunit : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, IsUnit ((m : ℕ) : R))
    (hdeck : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p},
      Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) m)) :
    Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) →ₜ* PrimeToPTateModule p Ω where
  toMonoidHom := PrimeToPTateModule.lift
    (fun m ↦ kummerMonodromyLevel t Ω m (hunit m) (hdeck m))
    fun m n σ h ↦ kummerMonodromyLevel_pow_div t Ω (hunit n) (hunit m) (hdeck n) (hdeck m) h σ
  continuous_toFun := PrimeToPTateModule.continuous_iff.mpr fun m ↦ by
    simpa only [MonoidHom.toFun_eq_coe, PrimeToPTateModule.proj_lift] using
      isLocallyConstant_kummerMonodromyLevel t Ω m (hunit m) (hdeck m)

/-- Projecting `kummerMonodromy` to level `m` recovers `kummerMonodromyLevel`. -/
@[simp]
theorem proj_kummerMonodromy (p : ℕ)
    (hunit : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, IsUnit ((m : ℕ) : R))
    (hdeck : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p},
      Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) m))
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p})
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) :
    PrimeToPTateModule.proj m (kummerMonodromy t Ω p hunit hdeck σ) =
      kummerMonodromyLevel t Ω m (hunit m) (hdeck m) σ :=
  PrimeToPTateModule.proj_lift _ _ m σ

/-- **Surjectivity of Kummer monodromy.** Under the hypotheses defining `kummerMonodromy` (every
nonzero `m` prime to `p` invertible in `R`, and every `m`-th root of unity of `Ω` coming from `R`),
if moreover the Kummer covers of all these orders are connected, `kummerMonodromy` maps the
profinite group `π₁(Spec R, x)` onto the prime-to-`p` Tate module of `Ω`. -/
theorem kummerMonodromy_surjective (p : ℕ)
    (hunit : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, IsUnit ((m : ℕ) : R))
    (hdeck : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p},
      Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) m))
    (hconn : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, IsConnected (kummerCover t m (hunit m))) :
    Function.Surjective (kummerMonodromy t Ω p hunit hdeck) :=
  PrimeToPTateModule.surjective_of_forall_surjective_proj
    (kummerMonodromy t Ω p hunit hdeck).continuous fun m ↦ by
      have := hconn m
      simpa only [proj_kummerMonodromy] using
        kummerMonodromyLevel_surjective t Ω m (hunit m) (hdeck m)

end KummerMonodromy

end TauCeti.FiniteEtaleScheme
