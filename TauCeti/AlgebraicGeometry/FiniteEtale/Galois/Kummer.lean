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

/-!
# The Kummer character of the étale fundamental group

Let `R` be a commutative ring, `t` a unit of `R`, and `x : Spec Ω ⟶ Spec R` a geometric point,
given by an `R`-algebra structure on a separably closed field `Ω`. For `n` invertible in `R`, the
geometric fibre at `x` of the Kummer cover `Spec R[y]/(y ^ n - t) ⟶ Spec R` is the set of `n`-th
roots of the image of `t` in `Ω` (`TauCeti.FiniteEtaleScheme.kummerCoverFiberEquiv`).

Suppose that every `n`-th root of unity of `Ω` comes from an `n`-th root of unity of `R`, as for
`R = K[T, T⁻¹]` with `K` algebraically closed and `n` invertible in `K`. Then the deck
transformations `y ↦ ζ y` act transitively on the fibre
(`TauCeti.FiniteEtaleScheme.exists_fiber_map_kummerCoverDeck_eq`). Since automorphisms of the fibre
functor commute with deck transformations, every `σ ∈ π₁(Spec R, x)` multiplies all the `n`-th
roots of `t` by one and the same root of unity `χₙ(σ) ∈ μ_n(Ω)`. This is the *Kummer character*

`TauCeti.FiniteEtaleScheme.kummerCharacter : π₁(Spec R, x) →* μ_n(Ω)`,

a locally constant homomorphism, characterized by `σ • y = χₙ(σ) * y` on the fibre
(`TauCeti.FiniteEtaleScheme.kummerCoverFiberEquiv_smul`). Along the maps between Kummer covers the
characters are compatible with the power maps: `χₘ(σ) ^ (m / n) = χₙ(σ)` for `n ∣ m`. Hence, if
the hypotheses hold for every nonzero `m` prime to `p`, the characters assemble into a continuous
homomorphism to the prime-to-`p` Tate module of `Ω`
(`TauCeti.FiniteEtaleScheme.kummerTateCharacter`):

`π₁(Spec R, x) →ₜ* lim_{(m, p) = 1} μ_m(Ω) = ℤ̂^{(p')}(1)`.

When the Kummer covers are connected over a connected base, `π₁` acts transitively on their
fibres, so the Kummer characters and the Tate character are surjective. For `R = K[T, T⁻¹]`,
`t = T` and `K` algebraically closed of characteristic exponent `p`, the Kummer covers are the
power maps `z ↦ z ^ m` of `𝔾_m` over `K`, and the Tate character is the monodromy of the tower of
these covers.

## Main definitions

* `TauCeti.FiniteEtaleScheme.kummerCharacter t hn hμ`: the Kummer character
  `π₁(Spec R, x) →* μ_n(Ω)` of the unit `t`.
* `TauCeti.FiniteEtaleScheme.kummerTateCharacter t p hn hμ`: the compatible family of Kummer
  characters of orders prime to `p`, a continuous homomorphism into the prime-to-`p` Tate module
  of `Ω`.

## Main results

* `TauCeti.FiniteEtaleScheme.exists_fiber_map_kummerCoverDeck_eq`: when every `n`-th root of unity
  of `Ω` comes from `R`, the deck transformations act transitively on the geometric fibre.
* `TauCeti.FiniteEtaleScheme.kummerCoverFiberEquiv_smul`,
  `TauCeti.FiniteEtaleScheme.kummerCharacter_eq_iff`: the defining property of the Kummer character.
* `TauCeti.FiniteEtaleScheme.kummerCharacter_pow_div`: compatibility with the power maps.
* `TauCeti.FiniteEtaleScheme.isLocallyConstant_kummerCharacter`: the Kummer character is locally
  constant, so continuous for the discrete topology on `μ_n(Ω)`.
* `TauCeti.FiniteEtaleScheme.kummerCharacter_surjective`,
  `TauCeti.FiniteEtaleScheme.kummerTateCharacter_surjective`: surjectivity for connected Kummer
  covers over a connected base.

## References

* A. Grothendieck, *SGA 1*, Exposé XIII, §2 (Corollary 2.12).
* H. W. Lenstra, *Galois theory for schemes*, Section 5.
-/

public section

open CategoryTheory AlgebraicGeometry PreGaloisCategory

universe u

namespace TauCeti.FiniteEtaleScheme

variable {R : CommRingCat.{u}} (t : Rˣ) {Ω : Type u} [Field Ω] [IsSepClosed Ω] [Algebra R Ω]

section Character

variable {n : ℕ} (hn : IsUnit (n : R))

/-- The geometric fibre of a Kummer cover is nonempty: the separably closed field `Ω` contains an
`n`-th root of the image of `t`, since `n` is invertible in `Ω`. -/
theorem nonempty_fiber_kummerCover :
    Nonempty ((fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :=
  haveI : NeZero (n : Ω) := ⟨by simpa using (hn.map (algebraMap R Ω)).ne_zero⟩
  have ⟨ω, hω⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap R Ω t) n
  ⟨(kummerCoverFiberEquiv t Ω n hn).symm ⟨ω, hω⟩⟩

/-- The `n`-th roots of `t` in `Ω` attached to points of the geometric fibre are nonzero. -/
private theorem kummerCoverFiberEquiv_ne_zero
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    (kummerCoverFiberEquiv t Ω n hn y : Ω) ≠ 0 := by
  intro h
  have := (kummerCoverFiberEquiv t Ω n hn y).2
  rw [h, zero_pow (by rintro rfl; simpa using hn.map (algebraMap R Ω))] at this
  exact (t.isUnit.map (algebraMap R Ω)).ne_zero this.symm

/-- If every `n`-th root of unity of `Ω` comes from an `n`-th root of unity of `R`, the deck
transformations of the Kummer cover act transitively on its geometric fibre: any two `n`-th roots
of `t` in `Ω` differ by an `n`-th root of unity of `R`. -/
theorem exists_fiber_map_kummerCoverDeck_eq
    (hμ : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    (y y' : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    ∃ ζ : rootsOfUnity n R, (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).map
      (kummerCoverDeck t hn ζ).hom y = y' := by
  set e := kummerCoverFiberEquiv t Ω n hn
  have hy := kummerCoverFiberEquiv_ne_zero t hn y
  -- The quotient of the two roots of `t` is an `n`-th root of unity of `Ω`.
  have hω : Units.mk0 ((e y' : Ω) / e y) (div_ne_zero
      (kummerCoverFiberEquiv_ne_zero t hn y') hy) ∈ rootsOfUnity n Ω := by
    rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_mk0, div_pow,
      (e y').2, (e y).2, div_self (t.isUnit.map (algebraMap R Ω)).ne_zero, Units.val_one]
  obtain ⟨ζ, hζ⟩ := hμ ⟨_, hω⟩
  refine ⟨ζ, e.injective (Subtype.ext ?_)⟩
  have hζ' : algebraMap R Ω (ζ : Rˣ) = (e y' : Ω) / e y := by
    simpa using congr(((($hζ : rootsOfUnity n Ω) : Ωˣ) : Ω))
  rw [kummerCoverFiberEquiv_map_kummerCoverDeck, hζ', div_mul_cancel₀ _ hy]

variable {t hn} in
/-- Two roots of unity that multiply a nonzero `n`-th root of `t` to the same element agree. -/
private theorem eq_of_mul_kummerCoverFiberEquiv_eq {ζ ξ : rootsOfUnity n Ω}
    {y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)}
    (h : ((ζ : Ωˣ) : Ω) * kummerCoverFiberEquiv t Ω n hn y =
      ((ξ : Ωˣ) : Ω) * kummerCoverFiberEquiv t Ω n hn y) : ζ = ξ :=
  Subtype.ext (Units.ext (mul_right_cancel₀ (kummerCoverFiberEquiv_ne_zero t hn y) h))

variable (hμ : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))

include hμ in
/-- An automorphism of the geometric fibre functor multiplies all `n`-th roots of `t` in the
fibre of the Kummer cover by the same root of unity. -/
private theorem exists_kummerCoverFiberEquiv_smul
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) :
    ∃ ζ : rootsOfUnity n Ω, ∀ y, (kummerCoverFiberEquiv t Ω n hn (σ • y) : Ω) =
      ((ζ : Ωˣ) : Ω) * kummerCoverFiberEquiv t Ω n hn y := by
  obtain ⟨y₀⟩ := nonempty_fiber_kummerCover t (Ω := Ω) hn
  obtain ⟨ξ, hξ⟩ := exists_fiber_map_kummerCoverDeck_eq t hn hμ y₀ (σ • y₀)
  refine ⟨restrictRootsOfUnity (algebraMap R Ω) n ξ, fun y ↦ ?_⟩
  obtain ⟨η, rfl⟩ := exists_fiber_map_kummerCoverDeck_eq t hn hμ y₀ y
  -- `σ` commutes with the deck transformation of `η`.
  rw [mulAction_naturality, ← hξ, kummerCoverFiberEquiv_map_kummerCoverDeck,
    kummerCoverFiberEquiv_map_kummerCoverDeck, kummerCoverFiberEquiv_map_kummerCoverDeck,
    restrictRootsOfUnity_coe_apply]
  ring

/-- **The Kummer character** of the unit `t` at the geometric point `x : Spec Ω ⟶ Spec R`. If every
`n`-th root of unity of `Ω` comes from `R`, an element `σ` of the étale fundamental group
`π₁(Spec R, x) = Aut (fiber x)` multiplies every `n`-th root of `t` in the geometric fibre of the
Kummer cover by the same root of unity `kummerCharacter t hn hμ σ`
(`kummerCoverFiberEquiv_smul`). -/
noncomputable def kummerCharacter :
    Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) →* rootsOfUnity n Ω :=
  MonoidHom.mk' (fun σ ↦ (exists_kummerCoverFiberEquiv_smul t hn hμ σ).choose) fun σ τ ↦ by
    obtain ⟨y₀⟩ := nonempty_fiber_kummerCover t (Ω := Ω) hn
    refine eq_of_mul_kummerCoverFiberEquiv_eq (y := y₀) ?_
    rw [← (exists_kummerCoverFiberEquiv_smul t hn hμ _).choose_spec, mul_smul,
      (exists_kummerCoverFiberEquiv_smul t hn hμ σ).choose_spec,
      (exists_kummerCoverFiberEquiv_smul t hn hμ τ).choose_spec, Subgroup.coe_mul, Units.val_mul,
      mul_assoc]

/-- **The defining property of the Kummer character**: `σ` acts on the `n`-th roots of `t` in the
geometric fibre of the Kummer cover by multiplication by `kummerCharacter t hn hμ σ`. -/
@[simp]
theorem kummerCoverFiberEquiv_smul (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))))
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    (kummerCoverFiberEquiv t Ω n hn (σ • y) : Ω) =
      ((kummerCharacter t hn hμ σ : Ωˣ) : Ω) * kummerCoverFiberEquiv t Ω n hn y :=
  (exists_kummerCoverFiberEquiv_smul t hn hμ σ).choose_spec y

/-- The Kummer character is determined by the action on a single point of the geometric fibre. -/
theorem kummerCharacter_eq_iff {σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))}
    {ζ : rootsOfUnity n Ω}
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    kummerCharacter t hn hμ σ = ζ ↔ (kummerCoverFiberEquiv t Ω n hn (σ • y) : Ω) =
      ((ζ : Ωˣ) : Ω) * kummerCoverFiberEquiv t Ω n hn y :=
  ⟨fun h ↦ h ▸ kummerCoverFiberEquiv_smul t hn hμ σ y, fun h ↦
    eq_of_mul_kummerCoverFiberEquiv_eq ((kummerCoverFiberEquiv_smul t hn hμ σ y).symm.trans h)⟩

/-- **Compatibility with the power maps.** For `n ∣ m`, the Kummer character of order `m` raised to
the power `m / n` is the Kummer character of order `n`: the map from the Kummer cover of degree `m`
to that of degree `n` raises roots of `t` to the power `m / n`. -/
theorem kummerCharacter_pow_div {m : ℕ} (hm : IsUnit (m : R))
    (hμm : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) m)) (h : n ∣ m)
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) :
    (kummerCharacter t hm hμm σ : Ωˣ) ^ (m / n) = kummerCharacter t hn hμ σ := by
  obtain ⟨y⟩ := nonempty_fiber_kummerCover t (Ω := Ω) hm
  refine (Subtype.ext_iff.1 ((kummerCharacter_eq_iff t hn hμ (ζ := ⟨_, ?_⟩)
    ((fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).map (kummerCoverMap t hn hm h) y)).2
      ?_)).symm
  · rw [mem_rootsOfUnity, ← pow_mul, Nat.div_mul_cancel h, (kummerCharacter t hm hμm σ).2]
  · rw [mulAction_naturality, kummerCoverFiberEquiv_map_kummerCoverMap,
      kummerCoverFiberEquiv_map_kummerCoverMap, kummerCoverFiberEquiv_smul, mul_pow,
      Units.val_pow_eq_pow_val]

/-- **Continuity of the Kummer character.** The Kummer character is locally constant on the
profinite group `π₁(Spec R, x)`: it only depends on the action on one point of the geometric
fibre of the Kummer cover, which is locally constant. -/
theorem isLocallyConstant_kummerCharacter :
    IsLocallyConstant (kummerCharacter t hn hμ) := by
  obtain ⟨y⟩ := nonempty_fiber_kummerCover t (Ω := Ω) hn
  have hy : IsLocallyConstant fun σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) ↦
      σ • y :=
    (IsLocallyConstant.iff_continuous _).2 (continuous_id.smul continuous_const)
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun σ ↦ ?_
  filter_upwards [hy.eventually_eq σ] with τ hτ
  rw [kummerCharacter_eq_iff t hn hμ y, hτ, kummerCoverFiberEquiv_smul]

/-- **Surjectivity of the Kummer character.** If the base is connected and the Kummer cover is
connected, the fundamental group acts transitively on its geometric fibre, so every `n`-th root of
unity of `Ω` is a value of the Kummer character. -/
theorem kummerCharacter_surjective [ConnectedSpace (Spec R)] [IsConnected (kummerCover t n hn)] :
    Function.Surjective (kummerCharacter t hn hμ) := by
  intro ζ
  obtain ⟨y⟩ := nonempty_fiber_kummerCover t (Ω := Ω) hn
  set e := kummerCoverFiberEquiv t Ω n hn
  have hζ : (((ζ : Ωˣ) : Ω) * e y) ^ n = algebraMap R Ω t := by
    rw [mul_pow, ← Units.val_pow_eq_pow_val, ζ.2, Units.val_one, one_mul,
      (e y).2]
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut (fiber (Spec.map
    (CommRingCat.ofHom (algebraMap R Ω))))) y (e.symm ⟨_, hζ⟩)
  exact ⟨σ, (kummerCharacter_eq_iff t hn hμ y).2 (by rw [hσ, e.apply_symm_apply])⟩

end Character

section Tate

variable (p : ℕ) (hn : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, IsUnit ((m : ℕ) : R))
  (hμ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p},
    Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) m))

/-- **The Kummer character with values in the prime-to-`p` Tate module.** The Kummer characters
of the unit `t` of all nonzero orders prime to `p` are compatible along the power maps, so they
define a continuous homomorphism from `π₁(Spec R, x)` to the Tate module
`lim_{(m, p) = 1} μ_m(Ω)`. -/
noncomputable def kummerTateCharacter :
    Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) →ₜ* PrimeToPTateModule p Ω where
  toMonoidHom := PrimeToPTateModule.lift (fun m ↦ kummerCharacter t (hn m) (hμ m))
    fun m n σ h ↦ kummerCharacter_pow_div t (hn n) (hμ n) (hn m) (hμ m) h σ
  continuous_toFun := PrimeToPTateModule.continuous_iff.2 fun m ↦ by
    simpa using isLocallyConstant_kummerCharacter t (hn m) (hμ m)

/-- The components of the Tate-module-valued Kummer character are the Kummer characters. -/
@[simp]
theorem proj_kummerTateCharacter (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p})
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) :
    PrimeToPTateModule.proj m (kummerTateCharacter t p hn hμ σ) =
      kummerCharacter t (hn m) (hμ m) σ :=
  PrimeToPTateModule.proj_lift _ _ m σ

/-- **Surjectivity of the Tate-module-valued Kummer character.** If the base is connected and the
Kummer covers of all nonzero orders prime to `p` are connected, the Kummer character maps the
profinite group `π₁(Spec R, x)` onto the prime-to-`p` Tate module of `Ω`. -/
theorem kummerTateCharacter_surjective [ConnectedSpace (Spec R)]
    [∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, IsConnected (kummerCover t m (hn m))] :
    Function.Surjective (kummerTateCharacter t p hn hμ) :=
  PrimeToPTateModule.surjective_of_forall_surjective_proj (kummerTateCharacter t p hn hμ).continuous
    fun m ↦ by
      simpa only [proj_kummerTateCharacter] using kummerCharacter_surjective t (hn m) (hμ m)

end Tate

end TauCeti.FiniteEtaleScheme
