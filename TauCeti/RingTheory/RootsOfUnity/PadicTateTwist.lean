/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Algebra.Module.Torsion.TateModule
public import TauCeti.RingTheory.RootsOfUnity.TateModule

/-!
# The `p`-adic Tate twist

The `p`-adic Tate twist `ℤ_p(1)` over a commutative monoid `K` is the inverse limit of its
groups of `p ^ n`-th roots of unity along the `p`-th power maps.  Written additively, this is the
Tate module of the unit group:

`PadicTateTwist p K = TateModule p (Additive Kˣ)`.

This file identifies the finite levels with `Additive (rootsOfUnity (p ^ n) K)`.  When `K` has
enough `p`-power roots of unity (for example, a separably closed field in which `p` is nonzero),
the twist is a free `ℤ_p`-module of rank one.
Ring automorphisms act on it componentwise; when all `p`-power roots of unity exist, this action
is scalar multiplication by Mathlib's `p`-adic cyclotomic character.  These are the coefficient
module and action used by `p`-adic Weil pairings.

For `ℓ` nonzero and prime to `p`, the powers `ℓ ^ n` are levels of the prime-to-`p` Tate module
`ℤ̂^{(p')}(1) = lim_{p ∤ m} μ_m`, and keeping the components at these levels is a continuous,
Galois-equivariant homomorphism `ℤ̂^{(p')}(1) → ℤ_ℓ(1)`.

## Main definitions

* `TauCeti.PadicTateTwist`: the inverse limit `ℤ_p(1)`.
* `TauCeti.PadicTateTwist.proj`: projection to `μ_{p^n}`, in additive notation.
* `TauCeti.PadicTateTwist.galoisRepresentation`: the componentwise action of field
  automorphisms.
* `TauCeti.PrimeToPTateModule.toPadicTateTwist`: the `ℓ`-adic component `ℤ̂^{(p')}(1) → ℤ_ℓ(1)`
  of the prime-to-`p` Tate module, for `ℓ` prime to `p`.

## Main results

* `TauCeti.PadicTateTwist.levelAddEquivRootsOfUnity`: the `n`-th level is `μ_{p^n}`.
* `TauCeti.PadicTateTwist.instCompactSpace`: for nonzero `p`, `ℤ_p(1)` is compact over a domain.
* `TauCeti.PadicTateTwist.nonempty_linearEquiv`: when `K` has enough `p`-power roots of unity,
  `ℤ_p(1)` is noncanonically linearly equivalent to `ℤ_p`.
* `TauCeti.PadicTateTwist.galoisRepresentation_apply_eq_smul`: the Galois action is scalar
  multiplication by the cyclotomic character.
* `TauCeti.PadicTateTwist.continuous_galoisRepresentation`: this action is jointly continuous.
* `TauCeti.PrimeToPTateModule.proj_toPadicTateTwist`: the components of the `ℓ`-adic component
  are the components of level `ℓ ^ n`.
* `TauCeti.PrimeToPTateModule.toPadicTateTwist_smul`: the `ℓ`-adic component is
  Galois-equivariant.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

public section

noncomputable section

namespace TauCeti

/-- The `p`-adic Tate twist `ℤ_p(1)`, realised as the Tate module of the multiplicative group.
Its `n`-th component is the group `μ_{p^n}` of `p ^ n`-th roots of unity. -/
abbrev PadicTateTwist (p : ℕ) (K : Type*) [CommMonoid K] := TateModule p (Additive Kˣ)

namespace PadicTateTwist

section Basic

variable {p : ℕ} {K : Type*} [CommMonoid K]

/-- The `p ^ n`-torsion in the additive unit group is the group of `p ^ n`-th roots of unity,
written additively. -/
def levelAddEquivRootsOfUnity (n : ℕ) :
    TateModuleLevel p (Additive Kˣ) n ≃+ Additive (rootsOfUnity (p ^ n) K) where
  toFun x := Additive.ofMul
    ⟨x.1.toMul, by
      rw [mem_rootsOfUnity]
      have hx : p ^ n • (x : Additive Kˣ) = 0 :=
        congrArg Subtype.val (AddSubgroup.torsionBy.nsmul x)
      simpa [toMul_nsmul] using congrArg Additive.toMul hx⟩
  invFun ζ :=
    ⟨Additive.ofMul ζ.toMul, AddSubgroup.torsionBy.nsmul_iff.mpr <|
      Additive.toMul.injective <| by
        simpa [toMul_nsmul] using
          (mem_rootsOfUnity (p ^ n) (ζ.toMul : Kˣ)).mp ζ.toMul.2⟩
  left_inv x := rfl
  right_inv ζ := rfl
  map_add' x y := rfl

/-- The inverse finite-level equivalence forgets the roots-of-unity membership proof. -/
@[simp]
theorem coe_levelAddEquivRootsOfUnity_symm (n : ℕ) (ζ : Additive (rootsOfUnity (p ^ n) K)) :
    ((levelAddEquivRootsOfUnity n).symm ζ : Additive Kˣ) = Additive.ofMul (ζ.toMul : Kˣ) :=
  (rfl)

/-- Projection of `ℤ_p(1)` to its `p ^ n`-th roots-of-unity level. -/
def proj (n : ℕ) : PadicTateTwist p K →+ Additive (rootsOfUnity (p ^ n) K) :=
  (levelAddEquivRootsOfUnity n).toAddMonoidHom.comp (TateModule.proj n)

/-- The roots-of-unity projection is the finite-level equivalence after ordinary projection. -/
theorem proj_def (n : ℕ) (x : PadicTateTwist p K) :
    proj n x = levelAddEquivRootsOfUnity n (TateModule.proj n x) :=
  (rfl)

/-- The roots-of-unity projection is the ordinary Tate-module projection on underlying units. -/
@[simp]
theorem coe_proj (x : PadicTateTwist p K) (n : ℕ) :
    ((proj n x).toMul : Kˣ) = (TateModule.proj n x : Additive Kˣ).toMul :=
  (rfl)

/-- Consecutive components of `ℤ_p(1)` are related by the `p`-th power map. -/
@[simp]
theorem coe_tateModuleProj_succ_pow (x : PadicTateTwist p K) (n : ℕ) :
    ((TateModule.proj (n + 1) x : Additive Kˣ).toMul : Kˣ) ^ p =
      (TateModule.proj n x : Additive Kˣ).toMul := by
  have h := congrArg Subtype.val (TateModule.proj_succ x n)
  rw [tateModuleTransition_apply] at h
  simpa only [toMul_nsmul] using congrArg Additive.toMul h

/-- A point of `ℤ_p(1)` is determined by all of its roots-of-unity components. -/
@[ext]
theorem ext {x y : PadicTateTwist p K} (h : ∀ n, proj n x = proj n y) : x = y :=
  TateModule.ext fun n ↦ (levelAddEquivRootsOfUnity n).injective (h n)

end Basic

section Compact

variable {p : ℕ} {K : Type*} [NeZero p] [CommRing K] [IsDomain K]

/-- For nonzero `p`, every finite level of the `p`-adic Tate twist over a domain is finite. -/
noncomputable instance instFiniteLevel (n : ℕ) :
    Finite (TateModuleLevel p (Additive Kˣ) n) :=
  Finite.of_injective (levelAddEquivRootsOfUnity n) (levelAddEquivRootsOfUnity n).injective

/-- For nonzero `p`, the `p`-adic Tate twist over a domain is compact in its inverse-limit
topology. -/
noncomputable instance instCompactSpace : CompactSpace (PadicTateTwist p K) :=
  inferInstance

end Compact

section RankOne

variable {p : ℕ} {K : Type*} [CommMonoid K]

/-- If `K` has enough `p ^ n`-th roots of unity, then the `n`-th level of `ℤ_p(1)` has `p ^ n`
elements. -/
theorem natCard_tateModuleLevel [NeZero p] (n : ℕ) [HasEnoughRootsOfUnity K (p ^ n)] :
    Nat.card (TateModuleLevel p (Additive Kˣ) n) = p ^ n := by
  rw [Nat.card_congr (levelAddEquivRootsOfUnity n).toEquiv,
    Nat.card_congr Additive.toMul,
    HasEnoughRootsOfUnity.natCard_rootsOfUnity K (p ^ n)]

variable [Fact p.Prime] [∀ n, HasEnoughRootsOfUnity K (p ^ n)]

variable (p K) in
/-- If `K` has enough `p`-power roots of unity, then `ℤ_p(1)` is noncanonically linearly
equivalent to `ℤ_p`. -/
theorem nonempty_linearEquiv : Nonempty (PadicTateTwist p K ≃ₗ[ℤ_[p]] ℤ_[p]) :=
  ⟨(TateModule.nonempty_linearEquiv_of_natCard (r := 1)
      (fun n ↦ by simpa using natCard_tateModuleLevel n)).some.trans
    (LinearEquiv.funUnique (Fin 1) ℤ_[p] ℤ_[p])⟩

/-- If `K` has enough `p`-power roots of unity, then `ℤ_p(1)` is a free `ℤ_p`-module. -/
instance free : Module.Free ℤ_[p] (PadicTateTwist p K) :=
  TateModule.free_of_natCard (r := 1) (fun n ↦ by simpa using natCard_tateModuleLevel n)

/-- If `K` has enough `p`-power roots of unity, then `ℤ_p(1)` is finitely generated over
`ℤ_p`. -/
instance finite : Module.Finite ℤ_[p] (PadicTateTwist p K) :=
  TateModule.finite_of_natCard (r := 1) (fun n ↦ by simpa using natCard_tateModuleLevel n)

variable (p K) in
/-- If `K` has enough `p`-power roots of unity, then `ℤ_p(1)` has rank one over `ℤ_p`. -/
theorem finrank : Module.finrank ℤ_[p] (PadicTateTwist p K) = 1 :=
  TateModule.finrank_eq_of_natCard (r := 1) (fun n ↦ by simpa using natCard_tateModuleLevel n)

end RankOne

section Galois

variable {p : ℕ} {F K : Type*} [Field F] [Field K] [Algebra F K] [Fact p.Prime]

private def unitsMap (σ : K ≃ₐ[F] K) : Additive Kˣ →+ Additive Kˣ :=
  (Units.mapEquiv σ.toRingEquiv.toMulEquiv).toAdditive.toAddMonoidHom

/-- The componentwise action of `Gal(K/F)` on the `p`-adic Tate twist. -/
def galoisRepresentation : Representation ℤ_[p] (K ≃ₐ[F] K) (PadicTateTwist p K) where
  toFun σ := TateModule.mapLinearMap (unitsMap σ)
  map_one' := LinearMap.ext fun x ↦ TateModule.ext fun n ↦ Subtype.ext <| by
    apply Additive.toMul.injective
    apply Units.ext
    simp [unitsMap, TateModule.mapLinearMap_apply, TateModule.proj_map,
      TateModule.levelMap_apply]
  map_mul' σ τ := LinearMap.ext fun x ↦ TateModule.ext fun n ↦ Subtype.ext <| by
    apply Additive.toMul.injective
    apply Units.ext
    simp [unitsMap, TateModule.mapLinearMap_apply, TateModule.proj_map,
      TateModule.levelMap_apply]

/-- The Galois representation applies the field automorphism to every roots-of-unity component. -/
@[simp]
theorem coe_tateModuleProj_galoisRepresentation (σ : K ≃ₐ[F] K) (x : PadicTateTwist p K) (n : ℕ) :
    (((TateModule.proj n (galoisRepresentation (p := p) (F := F) σ x) :
        Additive Kˣ).toMul : Kˣ) : K) =
      σ (((TateModule.proj n x : Additive Kˣ).toMul : Kˣ) : K) := by
  simp [galoisRepresentation, unitsMap, TateModule.mapLinearMap_apply,
    TateModule.proj_map, TateModule.levelMap_apply]

/-- When `K` contains all `p`-power roots of unity, the Galois action on `ℤ_p(1)` is scalar
multiplication by the `p`-adic cyclotomic character. -/
@[simp]
theorem galoisRepresentation_apply_eq_smul
    [∀ n, HasEnoughRootsOfUnity K (p ^ n)] (σ : K ≃ₐ[F] K) (x : PadicTateTwist p K) :
    galoisRepresentation (p := p) (F := F) σ x =
      ((cyclotomicCharacter K p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x := by
  apply PadicTateTwist.ext
  intro n
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  simp only [coe_proj]
  rw [coe_tateModuleProj_galoisRepresentation]
  rw [TateModule.proj_smul]
  have hsmul := TateModule.coe_zmod_smul (p := p) (A := Additive Kˣ)
    (PadicInt.toZModPow n ((cyclotomicCharacter K p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]))
    (TateModule.proj n x)
  rw [hsmul, toMul_nsmul]
  have hxpow : (((TateModule.proj n x : Additive Kˣ).toMul : Kˣ) : K) ^ p ^ n = 1 := by
    have hx := congrArg Additive.toMul
      (congrArg Subtype.val (AddSubgroup.torsionBy.nsmul (TateModule.proj n x)))
    simpa [toMul_nsmul] using congrArg Units.val hx
  exact cyclotomicCharacter.spec p σ.toRingEquiv _
    hxpow

/-- The Galois action on `ℤ_p(1)` is jointly continuous when all `p`-power roots of unity exist. -/
theorem continuous_galoisRepresentation [∀ n, HasEnoughRootsOfUnity K (p ^ n)] :
    Continuous fun q : (K ≃ₐ[F] K) × PadicTateTwist p K ↦
      galoisRepresentation (p := p) (F := F) q.1 q.2 := by
  have hχ : Continuous fun σ : K ≃ₐ[F] K ↦
      ((cyclotomicCharacter K p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) :=
    Units.continuous_val.comp (cyclotomicCharacter.continuous p F K)
  exact ((hχ.comp continuous_fst).smul continuous_snd).congr fun q ↦
    (galoisRepresentation_apply_eq_smul q.1 q.2).symm

end Galois

end PadicTateTwist

/-! ### The `ℓ`-adic component of the prime-to-`p` Tate module -/

namespace PrimeToPTateModule

open PadicTateTwist

section Basic

variable {p : ℕ} {E : Type*} [CommMonoid E] (ℓ : ℕ) [NeZero ℓ]

/-- **The `ℓ`-adic component of the prime-to-`p` Tate module.** For `ℓ` nonzero and prime to `p`,
the powers `ℓ ^ n` are among the levels of `ℤ̂^{(p')}(1) = lim_{p ∤ m} μ_m(E)`, and keeping only
those components is a continuous homomorphism to the `ℓ`-adic Tate twist
`ℤ_ℓ(1) = lim_n μ_{ℓ ^ n}(E)`, written multiplicatively. For a prime `ℓ ≠ p` this is the
specialization of `ℤ̂^{(p')}(1)` at the prime `ℓ`. -/
def toPadicTateTwist (hℓ : ℓ.Coprime p) :
    PrimeToPTateModule p E →ₜ* Multiplicative (PadicTateTwist ℓ E) where
  toMonoidHom := AddMonoidHom.toMultiplicativeRight <| TateModule.lift
    (fun n ↦ (levelAddEquivRootsOfUnity n).symm.toAddMonoidHom.comp
      (MonoidHom.toAdditive (proj ⟨ℓ ^ n, pow_ne_zero n (NeZero.ne ℓ), hℓ.pow_left n⟩)))
    fun n ↦ AddMonoidHom.ext fun x ↦ Subtype.ext <| Additive.toMul.injective <| by
      have h : (proj ⟨ℓ ^ (n + 1), pow_ne_zero _ (NeZero.ne ℓ), hℓ.pow_left _⟩ x.toMul : Eˣ) ^ ℓ =
          proj ⟨ℓ ^ n, pow_ne_zero n (NeZero.ne ℓ), hℓ.pow_left n⟩ x.toMul := by
        have hdiv := proj_pow_div x.toMul
          (m := ⟨ℓ ^ (n + 1), pow_ne_zero _ (NeZero.ne ℓ), hℓ.pow_left _⟩)
          (n := ⟨ℓ ^ n, pow_ne_zero n (NeZero.ne ℓ), hℓ.pow_left n⟩) (pow_dvd_pow ℓ n.le_succ)
        -- The exponent `ℓ ^ (n + 1) / ℓ ^ n` in `proj_pow_div` is `ℓ`.
        convert hdiv using 2
        exact (Nat.mul_div_cancel _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne ℓ)) n)).symm.trans
          (congrArg (· / ℓ ^ n) (pow_succ' ℓ n).symm)
      simp [tateModuleTransition_apply, toMul_nsmul, h]
  continuous_toFun := continuous_ofAdd.comp <| TateModule.continuous_iff.2 fun n ↦ by
    simp_rw [← AddMonoidHom.comp_apply (TateModule.proj n), TateModule.proj_lift]
    exact (isLocallyConstant_proj ⟨ℓ ^ n, pow_ne_zero n (NeZero.ne ℓ), hℓ.pow_left n⟩).comp
      fun ζ ↦ (levelAddEquivRootsOfUnity n).symm (.ofMul ζ)

variable {ℓ} {hℓ : ℓ.Coprime p}

/-- The `ℓ ^ n`-th roots-of-unity component of the `ℓ`-adic component of `x` is the level-`ℓ ^ n`
component of `x`. -/
@[simp]
theorem proj_toPadicTateTwist (x : PrimeToPTateModule p E) (n : ℕ) :
    PadicTateTwist.proj n (toPadicTateTwist ℓ hℓ x).toAdd =
      Additive.ofMul (proj ⟨ℓ ^ n, pow_ne_zero n (NeZero.ne ℓ), hℓ.pow_left n⟩ x) :=
  (congrArg (levelAddEquivRootsOfUnity n) (DFunLike.congr_fun (TateModule.proj_lift _ _ n) _)).trans
    ((levelAddEquivRootsOfUnity n).apply_symm_apply _)

end Basic

section Galois

variable {p : ℕ} {F K : Type*} [Field F] [Field K] [Algebra F K] {ℓ : ℕ} [Fact ℓ.Prime]
  {hℓ : ℓ.Coprime p}

/-- **The `ℓ`-adic component is Galois-equivariant**: it carries the action of `Gal(K/F)` on
`ℤ̂^{(p')}(1)` through the roots of unity to the Galois representation on `ℤ_ℓ(1)`. -/
theorem toPadicTateTwist_smul (σ : K ≃ₐ[F] K) (x : PrimeToPTateModule p K) :
    toPadicTateTwist ℓ hℓ (σ • x) =
      .ofAdd (galoisRepresentation (p := ℓ) σ (toPadicTateTwist ℓ hℓ x).toAdd) := by
  refine Multiplicative.toAdd.injective <| PadicTateTwist.ext fun n ↦ ?_
  refine Additive.toMul.injective <| Subtype.ext <| Units.ext ?_
  rw [proj_toPadicTateTwist, coe_proj, toAdd_ofAdd, coe_tateModuleProj_galoisRepresentation,
    ← coe_proj, proj_toPadicTateTwist]
  exact PrimeToPTateModule.coe_proj_smul σ x _

end Galois

end PrimeToPTateModule

end TauCeti

end
