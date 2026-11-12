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
import Mathlib.NumberTheory.Padics.ProperSpace
import TauCeti.Data.Nat.Factorization.Basic
import TauCeti.Data.ZMod.Pow
import TauCeti.GroupTheory.OrderOfElement.Basic

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
Galois-equivariant homomorphism `ℤ̂^{(p')}(1) → ℤ_ℓ(1)`. Together these components identify
`ℤ̂^{(p')}(1)` with the product `∏_{ℓ ∤ p} ℤ_ℓ(1)` over the primes `ℓ` prime to `p`, for any
commutative monoid. This is the Chinese remainder theorem at each level: a root of unity of order
dividing `m` is determined by its `ℓ`-primary parts `ζ ^ (m / ℓ ^ v_ℓ(m))`, and any family of
`ℓ ^ v_ℓ(m)`-th roots of unity is the family of `ℓ`-primary parts of one `m`-th root of unity.
When all the `ℓ`-power roots of unity exist, each factor is noncanonically `ℤ_ℓ`, so that
`ℤ̂^{(p')}(1)` is, as a topological group, the product `∏_{ℓ ∤ p} ℤ_ℓ`.

## Main definitions

* `TauCeti.PadicTateTwist`: the inverse limit `ℤ_p(1)`.
* `TauCeti.PadicTateTwist.proj`: projection to `μ_{p^n}`, in additive notation.
* `TauCeti.PadicTateTwist.galoisRepresentation`: the componentwise action of field
  automorphisms.
* `TauCeti.PrimeToPTateModule.toPadicTateTwist`: the `ℓ`-adic component `ℤ̂^{(p')}(1) → ℤ_ℓ(1)`
  of the prime-to-`p` Tate module, for `ℓ` prime to `p`.
* `TauCeti.PrimeToPTateModule.continuousMulEquivPiPadicTateTwist`: the isomorphism of topological
  groups `ℤ̂^{(p')}(1) ≃ₜ* ∏_{ℓ ∤ p} ℤ_ℓ(1)` given by all the `ℓ`-adic components.
* `TauCeti.PrimeToPTateModule.piPadicTateTwistReindex`: for a prime `p`, the reindexing of
  `∏_{ℓ ∤ p} ℤ_ℓ(1)` as the product over the primes `ℓ ≠ p`.

## Main results

* `TauCeti.PadicTateTwist.levelAddEquivRootsOfUnity`: the `n`-th level is `μ_{p^n}`.
* `TauCeti.PadicTateTwist.instCompactSpace`: for nonzero `p`, `ℤ_p(1)` is compact over a domain.
* `TauCeti.PadicTateTwist.nonempty_linearEquiv`: when `K` has enough `p`-power roots of unity,
  `ℤ_p(1)` is noncanonically linearly equivalent to `ℤ_p`.
* `TauCeti.PadicTateTwist.nonempty_continuousAddEquiv`: in that case `ℤ_p(1)` is also
  noncanonically isomorphic to `ℤ_p` as a topological group.
* `TauCeti.PadicTateTwist.galoisRepresentation_apply_eq_smul`: the Galois action is scalar
  multiplication by the cyclotomic character.
* `TauCeti.PadicTateTwist.continuous_galoisRepresentation`: this action is jointly continuous.
* `TauCeti.PrimeToPTateModule.proj_toPadicTateTwist`: the components of the `ℓ`-adic component
  are the components of level `ℓ ^ n`.
* `TauCeti.PrimeToPTateModule.toPadicTateTwist_smul`: the `ℓ`-adic component is
  Galois-equivariant.
* `TauCeti.PrimeToPTateModule.proj_continuousMulEquivPiPadicTateTwist_apply`,
  `TauCeti.PrimeToPTateModule.proj_continuousMulEquivPiPadicTateTwist_symm_apply`: the
  decomposition and its inverse on the levels `ℓ ^ n`.

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

variable (p K) in
/-- If `K` has enough `p`-power roots of unity, then `ℤ_p(1)` is noncanonically isomorphic to
`ℤ_p` as a topological group. -/
theorem nonempty_continuousAddEquiv : Nonempty (PadicTateTwist p K ≃ₜ+ ℤ_[p]) := by
  obtain ⟨e⟩ := nonempty_linearEquiv p K
  -- The inverse of a `ℤ_p`-linear equivalence is `a ↦ a • e.symm 1`, which is continuous; it is a
  -- continuous bijection from the compact `ℤ_p` to the Hausdorff `ℤ_p(1)`, hence a homeomorphism.
  have hc : Continuous e.symm := by
    have h : ⇑e.symm = fun a : ℤ_[p] ↦ a • e.symm 1 :=
      funext fun a ↦ by rw [← map_smul, smul_eq_mul, mul_one]
    rw [h]
    exact continuous_id.smul continuous_const
  exact ⟨(ContinuousAddEquiv.mk' (hc.homeoOfEquivCompactToT2 (f := e.symm.toEquiv))
    fun x y ↦ map_add e.symm x y).symm⟩

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

/-! ### The product of the `ℓ`-adic components -/

section Decomposition

variable {p : ℕ} {E : Type*} [CommMonoid E]

/-! The inverse of the decomposition is assembled level by level. Given a family `y` of points
of `ℤ_ℓ(1)`, `piRoot y ℓ n ∈ μ_{ℓ ^ n}(E)` is the level-`n` component of its `ℓ`-th member, and
`piLevel y m ∈ μ_m(E)` is the root of unity whose `ℓ`-primary parts `ζ ^ (m / ℓ ^ v_ℓ(m))` are the
`piRoot y ℓ (v_ℓ(m))`: the product over the primes `ℓ ∣ m` of these roots raised to the inverse of
`m / ℓ ^ v_ℓ(m)` modulo `ℓ ^ v_ℓ(m)`. -/

/-- The level-`n` component of the `ℓ`-th member of `y`, as a unit of `E`, and `1` when `ℓ` is not
a prime prime to `p`. Taking `ℓ` in `ℕ` lets the inverse be written as a product over the prime
factors of a level. -/
private noncomputable def piRoot
    (y : ∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ.Coprime p}, Multiplicative (PadicTateTwist ℓ E))
    (ℓ n : ℕ) : Eˣ :=
  if h : ℓ.Prime ∧ ℓ.Coprime p then
    ((PadicTateTwist.proj n (y ⟨ℓ, h⟩).toAdd).toMul : Eˣ)
  else 1

variable (y : ∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ.Coprime p}, Multiplicative (PadicTateTwist ℓ E))

private theorem piRoot_pow (ℓ n : ℕ) : piRoot y ℓ n ^ ℓ ^ n = 1 := by
  unfold piRoot
  split_ifs with h
  · exact (mem_rootsOfUnity _ _).1 (PadicTateTwist.proj n (y ⟨ℓ, h⟩).toAdd).toMul.2
  · exact one_pow _

private theorem piRoot_pow_sub {ℓ n k : ℕ} (h : n ≤ k) :
    piRoot y ℓ k ^ ℓ ^ (k - n) = piRoot y ℓ n := by
  unfold piRoot
  split_ifs with hℓ
  · have := TateModule.coe_proj_eq_pow_sub_nsmul (y ⟨ℓ, hℓ⟩).toAdd h
    simpa [toMul_nsmul] using (congrArg Additive.toMul this).symm
  · exact one_pow _

private theorem isLocallyConstant_piRoot (ℓ n : ℕ) :
    IsLocallyConstant fun y : ∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ.Coprime p},
      Multiplicative (PadicTateTwist ℓ E) ↦ piRoot y ℓ n := by
  unfold piRoot
  split_ifs with hℓ
  · let ℓ' : {ℓ : ℕ // ℓ.Prime ∧ ℓ.Coprime p} := ⟨ℓ, hℓ⟩
    have hc : Continuous fun y : ∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ.Coprime p},
        Multiplicative (PadicTateTwist ℓ E) ↦ (y ℓ').toAdd :=
      continuous_toAdd.comp (continuous_apply ℓ')
    exact ((TateModule.isLocallyConstant_proj n).comp_continuous hc).comp
      fun z ↦ ((levelAddEquivRootsOfUnity n z).toMul : Eˣ)
  · exact IsLocallyConstant.const _

/-- The `m`-th root of unity whose `ℓ`-primary part is `piRoot y ℓ (v_ℓ(m))` for every prime
`ℓ ∣ m` (`piLevel_pow_ordCompl`). -/
private noncomputable def piLevel (m : ℕ) : Eˣ :=
  ∏ ℓ ∈ m.primeFactors,
    piRoot y ℓ (m.factorization ℓ) ^ ((ordCompl[ℓ] m : ZMod (ordProj[ℓ] m))⁻¹).val

private theorem piLevel_pow_self (m : ℕ) : piLevel y m ^ m = 1 := by
  rw [piLevel, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun ℓ _ ↦ ?_
  rw [← pow_mul, mul_comm, pow_mul, orderOf_dvd_iff_pow_eq_one.1
    ((orderOf_dvd_of_pow_eq_one (piRoot_pow y ℓ _)).trans (Nat.ordProj_dvd m ℓ)), one_pow]

private theorem piLevel_pow_ordCompl {m ℓ : ℕ} (hℓ : ℓ ∈ m.primeFactors) :
    piLevel y m ^ ordCompl[ℓ] m = piRoot y ℓ (m.factorization ℓ) := by
  have hℓp := Nat.prime_of_mem_primeFactors hℓ
  rw [piLevel, ← Finset.prod_pow, Finset.prod_eq_single ℓ]
  · rw [← pow_mul, mul_comm]
    exact pow_mul_val_inv (piRoot_pow y ℓ _)
      ((Nat.coprime_ordCompl hℓp (Nat.mem_primeFactors.1 hℓ).2.2).pow_left _).symm
  · -- The other factors die: `ℓ' ^ v_ℓ'(m)` divides the `ℓ`-free part of `m`.
    intro ℓ' hℓ' hne
    have hℓ'p := Nat.prime_of_mem_primeFactors hℓ'
    obtain ⟨t, ht⟩ := Nat.dvd_ordCompl_of_dvd_not_dvd (p := ℓ) (Nat.ordProj_dvd m ℓ')
      fun h ↦ hne ((Nat.prime_dvd_prime_iff_eq hℓp hℓ'p).1 (hℓp.dvd_of_dvd_pow h)).symm
    rw [← pow_mul, mul_comm, ht, pow_mul, pow_mul, piRoot_pow, one_pow, one_pow]
  · exact fun h ↦ (h hℓ).elim

private theorem piLevel_pow_div {m n : ℕ} (hm : m ≠ 0) (h : n ∣ m) :
    piLevel y m ^ (m / n) = piLevel y n := by
  have hn : n ≠ 0 := ne_zero_of_dvd_ne_zero hm h
  refine eq_of_pow_ordCompl_eq hn ?_ (piLevel_pow_self y n) fun ℓ hℓ hℓn ↦ ?_
  · rw [← pow_mul, Nat.div_mul_cancel h, piLevel_pow_self]
  · have hle : n.factorization ℓ ≤ m.factorization ℓ := (Nat.factorization_le_iff_dvd hn hm).2 h ℓ
    rw [piLevel_pow_ordCompl y (Nat.mem_primeFactors.2 ⟨hℓ, hℓn, hn⟩), ← pow_mul,
      Nat.div_mul_ordCompl_of_dvd ℓ h, pow_mul,
      piLevel_pow_ordCompl y (Nat.mem_primeFactors.2 ⟨hℓ, hℓn.trans h, hm⟩),
      piRoot_pow_sub y hle]

private theorem isLocallyConstant_piLevel (m : ℕ) :
    IsLocallyConstant fun y : ∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ.Coprime p},
      Multiplicative (PadicTateTwist ℓ E) ↦ piLevel y m := by
  unfold piLevel
  induction m.primeFactors using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact IsLocallyConstant.const 1
  | insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]
    exact ((isLocallyConstant_piRoot a _).comp (· ^ _)).mul ih

/-- The point of `ℤ̂^{(p')}(1)` with components `piLevel y m`, the inverse of the decomposition. -/
private noncomputable def ofPi : PrimeToPTateModule p E :=
  mk (fun m ↦ ⟨piLevel y m, (mem_rootsOfUnity _ _).2 (piLevel_pow_self y m)⟩) <|
    mem_primeToPTateModuleSubgroup_iff.2 fun m _ h ↦ piLevel_pow_div y m.2.1 h

private theorem coe_proj_ofPi (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) :
    (proj m (ofPi y) : Eˣ) = piLevel y m := by
  rw [ofPi, proj_mk]

private theorem toPadicTateTwist_ofPi {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓp : ℓ.Coprime p) :
    toPadicTateTwist ℓ hℓp (ofPi y) = y ⟨ℓ, hℓ, hℓp⟩ := by
  refine Multiplicative.toAdd.injective <| PadicTateTwist.ext fun n ↦ ?_
  refine Additive.toMul.injective <| Subtype.ext ?_
  rw [proj_toPadicTateTwist, toMul_ofMul, coe_proj_ofPi]
  have key : piRoot y ℓ n = ((PadicTateTwist.proj n (y ⟨ℓ, hℓ, hℓp⟩).toAdd).toMul : Eˣ) := by
    rw [piRoot, dite_eq_left ⟨hℓ, hℓp⟩]
  rw [← key]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 := piRoot_pow y ℓ 0
    rw [pow_zero, pow_one] at h1
    simp [h1, piLevel]
  · -- At the level `ℓ ^ n` the `ℓ`-free part is `1`, so the `ℓ`-primary part is everything.
    rw [← pow_one (piLevel y _), ← Nat.ordCompl_self_pow hℓ (k := n),
      piLevel_pow_ordCompl y (by simp [Nat.primeFactors_prime_pow hn.ne' hℓ]),
      hℓ.factorization_pow, Finsupp.single_eq_same]

/-- A point of `ℤ̂^{(p')}(1)` is determined by its components at the prime powers. -/
private theorem eq_of_forall_proj_pow_eq {x x' : PrimeToPTateModule p E}
    (h : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ.Coprime p) (n : ℕ),
      proj ⟨ℓ ^ n, pow_ne_zero n hℓ.ne_zero, hℓp.pow_left n⟩ x =
        proj ⟨ℓ ^ n, pow_ne_zero n hℓ.ne_zero, hℓp.pow_left n⟩ x') : x = x' := by
  refine ext fun m ↦ Subtype.ext <| eq_of_pow_ordCompl_eq m.2.1
    ((mem_rootsOfUnity _ _).1 (proj m x).2) ((mem_rootsOfUnity _ _).1 (proj m x').2)
    fun ℓ hℓ hℓm ↦ ?_
  have hdvd : ordProj[ℓ] (m : ℕ) ∣ m := Nat.ordProj_dvd _ _
  rw [proj_pow_div x (n := ⟨_, (Nat.ordProj_pos _ _).ne',
      Nat.Coprime.coprime_dvd_left hdvd m.2.2⟩) hdvd,
    proj_pow_div x' (n := ⟨_, (Nat.ordProj_pos _ _).ne',
      Nat.Coprime.coprime_dvd_left hdvd m.2.2⟩) hdvd]
  exact congrArg Subtype.val (h ℓ hℓ (Nat.Coprime.coprime_dvd_left hℓm m.2.2) _)

variable (p E) in
/-- **The prime-to-`p` Tate module is the product of its `ℓ`-adic components**: the
`ℓ`-adic components `toPadicTateTwist`, over all primes `ℓ` prime to `p`, form an isomorphism of
topological groups `ℤ̂^{(p')}(1) ≃ₜ* ∏_{ℓ ∤ p} ℤ_ℓ(1)`. It holds for every commutative monoid `E`,
by the Chinese remainder theorem at each level `μ_m(E)`. -/
noncomputable def continuousMulEquivPiPadicTateTwist :
    PrimeToPTateModule p E ≃ₜ*
      ∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ.Coprime p}, Multiplicative (PadicTateTwist ℓ E) where
  toFun x ℓ := haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.1.ne_zero⟩; toPadicTateTwist ℓ ℓ.2.2 x
  invFun := ofPi
  left_inv x := eq_of_forall_proj_pow_eq fun ℓ hℓ hℓp n ↦ by
    have : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have h := congrArg (fun z ↦ PadicTateTwist.proj n z.toAdd) (toPadicTateTwist_ofPi
      (fun ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ.Coprime p} ↦
        haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.1.ne_zero⟩; toPadicTateTwist ℓ ℓ.2.2 x) hℓ hℓp)
    simp only [proj_toPadicTateTwist] at h
    exact Additive.ofMul.injective h
  right_inv y := funext fun ℓ ↦
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.1.ne_zero⟩; toPadicTateTwist_ofPi y ℓ.2.1 ℓ.2.2
  map_mul' x x' := funext fun ℓ ↦ map_mul _ x x'
  continuous_toFun := continuous_pi fun ℓ ↦
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.1.ne_zero⟩; (toPadicTateTwist ℓ ℓ.2.2).continuous
  continuous_invFun := continuous_iff.2 fun m ↦ by
    refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
    simpa only [Function.comp_def, coe_proj_ofPi] using isLocallyConstant_piLevel m

/-- The `ℓ`-th member of the decomposition is the `ℓ`-adic component. -/
@[simp]
theorem continuousMulEquivPiPadicTateTwist_apply {ℓ : ℕ} (hℓ : ℓ.Prime ∧ ℓ.Coprime p)
    (x : PrimeToPTateModule p E) :
    continuousMulEquivPiPadicTateTwist p E x ⟨ℓ, hℓ⟩ =
      haveI : NeZero ℓ := ⟨hℓ.1.ne_zero⟩; toPadicTateTwist ℓ hℓ.2 x := by
  unfold continuousMulEquivPiPadicTateTwist
  rfl

/-- The level-`n` component of the `ℓ`-th member of the decomposition of `x` is the level-`ℓ ^ n`
component of `x`. -/
@[simp]
theorem proj_continuousMulEquivPiPadicTateTwist_apply (x : PrimeToPTateModule p E)
    (ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ.Coprime p}) (n : ℕ) :
    PadicTateTwist.proj n (continuousMulEquivPiPadicTateTwist p E x ℓ).toAdd =
      .ofMul (proj ⟨ℓ ^ n, pow_ne_zero n ℓ.2.1.ne_zero, ℓ.2.2.pow_left n⟩ x) := by
  obtain ⟨ℓ, hℓ⟩ := ℓ
  have : NeZero ℓ := ⟨hℓ.1.ne_zero⟩
  rw [continuousMulEquivPiPadicTateTwist_apply hℓ, proj_toPadicTateTwist]

/-- The level-`ℓ ^ n` component of the point with `ℓ`-adic components `y` is the level-`n`
component of `y ℓ`. -/
@[simp]
theorem proj_continuousMulEquivPiPadicTateTwist_symm_apply
    (y : ∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ.Coprime p}, Multiplicative (PadicTateTwist ℓ E))
    (ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ.Coprime p}) (n : ℕ) :
    proj ⟨ℓ ^ n, pow_ne_zero n ℓ.2.1.ne_zero, ℓ.2.2.pow_left n⟩
        ((continuousMulEquivPiPadicTateTwist p E).symm y) =
      (PadicTateTwist.proj n (y ℓ).toAdd).toMul := by
  apply Additive.ofMul.injective
  rw [← proj_continuousMulEquivPiPadicTateTwist_apply, ContinuousMulEquiv.apply_symm_apply,
    ofMul_toMul]

variable (E) in
/-- For a prime `p`, reindexing a product of `ℓ`-adic Tate twists from the primes prime to `p`,
the index of `continuousMulEquivPiPadicTateTwist`, to the primes different from `p`. -/
def piPadicTateTwistReindex (hp : p.Prime) :
    (∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ.Coprime p}, Multiplicative (PadicTateTwist ℓ E)) ≃ₜ*
      ∀ ℓ : {ℓ : Nat.Primes // (ℓ : ℕ) ≠ p}, Multiplicative (PadicTateTwist ℓ E) where
  toFun y ℓ := y ⟨ℓ, ℓ.1.2, (Nat.coprime_primes ℓ.1.2 hp).2 ℓ.2⟩
  invFun z ℓ := z ⟨⟨ℓ, ℓ.2.1⟩, (Nat.coprime_primes ℓ.2.1 hp).1 ℓ.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_pi fun _ ↦ continuous_apply _
  continuous_invFun := continuous_pi fun _ ↦ continuous_apply _

/-- The member of the reindexed family at a prime `ℓ ≠ p` is the original member at `ℓ`. -/
@[simp]
theorem piPadicTateTwistReindex_apply (hp : p.Prime)
    (y : ∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ.Coprime p}, Multiplicative (PadicTateTwist ℓ E))
    (ℓ : {ℓ : Nat.Primes // (ℓ : ℕ) ≠ p}) :
    piPadicTateTwistReindex E hp y ℓ = y ⟨ℓ, ℓ.1.2, (Nat.coprime_primes ℓ.1.2 hp).2 ℓ.2⟩ := by
  unfold piPadicTateTwistReindex
  rfl

end Decomposition

end PrimeToPTateModule

end TauCeti

end
