/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import TauCeti.Data.ZMod.PrincipalUnits
public import TauCeti.NumberTheory.NumberField.Cyclotomic.ClassGroup.Action
public import TauCeti.NumberTheory.Padics.UnitsDecomposition.Basic
public import TauCeti.RepresentationTheory.GroupAlgebra.CharIdempotent
import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
import TauCeti.RepresentationTheory.Intertwining

/-!
# Tame character projectors and eigenspace decomposition of cyclotomic class modules

Let `p` be a prime, `r ≠ 0`, and `K` the `p ^ r`-th rational cyclotomic field. Inside
`(ZMod (p ^ r))ˣ`, the subgroup `Δ_r = rootsOfUnity (p - 1) (ZMod (p ^ r))` of `(p - 1)`-st roots
of unity is cyclic of order `p - 1` and maps isomorphically onto `(ZMod p)ˣ` under reduction modulo
`p` (`ZMod.rootsOfUnityEquivUnitsPrime`). Composing this isomorphism with the `p`-adic Teichmüller
character `TauCeti.padicTeichmuller p : (ZMod p)ˣ →* ℤ_[p]ˣ` produces the canonical faithful tame
character `TauCeti.tameTeichmullerChar p r hr : Δ_r →* ℤ_[p]ˣ`, whose powers
`ω ^ i` (`i : ZMod (p - 1)`) exhaust `Hom(Δ_r, ℤ_[p]ˣ)` (`TauCeti.tameCharEquivZMod`).

Acting through `TauCeti.cyclotomicClassAction ℤ_[p] (p ^ r) K` on
`A_r = ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))`, the character idempotent of `ω ^ i` in
`ℤ_[p][Δ_r]` yields the `i`-th **tame projector**
`TauCeti.cyclotomicClassProjector p r K hr i` and its image, the `i`-th **tame eigenspace**
`TauCeti.cyclotomicClassEigenspace p r K hr i`. Since `p - 1` is a unit in `ℤ_[p]` and `ℤ_[p]`
contains all `(p - 1)`-st roots of unity, these projectors form a complete orthogonal family of
idempotents indexed by `ZMod (p - 1)`, decomposing `A_r` as the internal direct sum of its tame
eigenspaces (`TauCeti.isInternal_cyclotomicClassEigenspace`,
`TauCeti.cyclotomicClassEigenspaceEquiv`).

The projectors commute with every `Δ_r`-equivariant `ℤ_[p]`-linear map, in particular with the full
Galois action of `(ZMod (p ^ r))ˣ` and with relative norms and ideal-class extensions along a
`p`-power cyclotomic tower `K ⊆ L` (`r ≤ s`). For odd `p`, `-1 ∈ Δ_r` acts on the `i`-th eigenspace
by `(-1) ^ i`, so even eigenspaces are fixed by complex conjugation and odd eigenspaces are negated.

## Main definitions

* `TauCeti.tameTeichmullerChar`: the Teichmüller character lifted to
  `rootsOfUnity (p - 1) (ZMod (p ^ r))`.
* `TauCeti.tameCharEquivZMod`: the bijection `ZMod (p - 1) ≃ (Δ_r →* ℤ_[p]ˣ)` sending `i` to
  `ω ^ i`.
* `TauCeti.cyclotomicClassTameRepresentation`: restriction of the cyclotomic class action to
  the tame subgroup `Δ_r`.
* `TauCeti.cyclotomicClassProjector`: the `i`-th tame character projector `e_i` on `A_r`.
* `TauCeti.cyclotomicClassEigenspace`: the `i`-th tame eigenspace `A_r^{(i)}`.
* `TauCeti.cyclotomicClassEigenspaceEquiv`: the direct-sum isomorphism
  `(⨁ i : ZMod (p - 1), A_r^{(i)}) ≃ₗ[ℤ_[p]] A_r`, with
  `TauCeti.cyclotomicClassEigenspaceEquiv_apply`, `TauCeti.cyclotomicClassEigenspaceEquiv_lof`, and
  `TauCeti.coe_cyclotomicClassEigenspaceEquiv_symm_apply`.

## Main results

* `TauCeti.tameTeichmullerChar_comp_rootsOfUnityPrimePowEquiv` and
  `TauCeti.tameTeichmullerChar_zpow_eq_iff`: compatibility across prime-power levels and
  periodicity `ω ^ i = ω ^ j ↔ (p - 1 : ℤ) ∣ i - j`.
* `TauCeti.cyclotomicClassProjector_eq_sum`, `TauCeti.mem_cyclotomicClassEigenspace_iff`, and
  `TauCeti.range_cyclotomicClassProjector`: explicit formula and eigenspace characterization.
* `TauCeti.cyclotomicClassProjector_comp_self`, `TauCeti.cyclotomicClassProjector_comp_of_not_dvd`,
  and `TauCeti.sum_cyclotomicClassProjector`: complete orthogonal idempotent relations.
* `TauCeti.isInternal_cyclotomicClassEigenspace`: internal direct-sum decomposition of `A_r`.
* `TauCeti.cyclotomicClassAction_neg_one_of_mem_eigenspace_even` and
  `TauCeti.cyclotomicClassAction_neg_one_of_mem_eigenspace_odd`: action of `-1` by parity
  for odd `p`.
* `TauCeti.relNormBaseChange_cyclotomicClassProjector` and
  `TauCeti.extendedBaseChange_cyclotomicClassProjector`: compatibility of tame projectors with
  relative norms and class extensions in cyclotomic towers.
-/

public section

open NumberField
open scoped NumberField TensorProduct DirectSum

namespace TauCeti

section TameCharacters

variable (p r : ℕ) [hp : Fact p.Prime] (hr : r ≠ 0)

/-- **The Teichmüller character on the tame subgroup** `Δ_r = rootsOfUnity (p - 1) (ZMod (p ^ r))`,
obtained by reducing modulo `p` via `ZMod.rootsOfUnityEquivUnitsPrime` and applying
`TauCeti.padicTeichmuller p`. -/
noncomputable def tameTeichmullerChar :
    rootsOfUnity (p - 1) (ZMod (p ^ r)) →* ℤ_[p]ˣ :=
  (padicTeichmuller p).comp (ZMod.rootsOfUnityEquivUnitsPrime p r hr).toMonoidHom

@[simp]
theorem tameTeichmullerChar_apply (a : rootsOfUnity (p - 1) (ZMod (p ^ r))) :
    tameTeichmullerChar p r hr a =
      padicTeichmuller p (ZMod.unitsMap (dvd_pow_self p hr) a.val) := by
  rw [tameTeichmullerChar, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ZMod.rootsOfUnityEquivUnitsPrime_apply]

/-- **Compatibility of the tame Teichmüller character across prime-power levels.** Composing the
level-`r` character with `ZMod.rootsOfUnityPrimePowEquiv` recovers the level-`s` character. -/
theorem tameTeichmullerChar_comp_rootsOfUnityPrimePowEquiv {s : ℕ} (hs : s ≠ 0) :
    (tameTeichmullerChar p r hr).comp (ZMod.rootsOfUnityPrimePowEquiv p hs hr).toMonoidHom =
      tameTeichmullerChar p s hs := by
  ext1 a
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, tameTeichmullerChar,
    ZMod.rootsOfUnityEquivUnitsPrime_rootsOfUnityPrimePowEquiv]

theorem tameTeichmullerChar_rootsOfUnityPrimePowEquiv {s : ℕ} (hs : s ≠ 0)
    (a : rootsOfUnity (p - 1) (ZMod (p ^ s))) :
    tameTeichmullerChar p r hr (ZMod.rootsOfUnityPrimePowEquiv p hs hr a) =
      tameTeichmullerChar p s hs a :=
  DFunLike.congr_fun (tameTeichmullerChar_comp_rootsOfUnityPrimePowEquiv p r hr hs) a

/-- The lifted Teichmüller character on `Δ_r` is injective. -/
theorem tameTeichmullerChar_injective : Function.Injective (tameTeichmullerChar p r hr) :=
  (padicTeichmuller_injective (p := p)).comp (ZMod.rootsOfUnityEquivUnitsPrime p r hr).injective

/-- For an odd prime `p`, the lifted Teichmüller character sends `-1 ∈ Δ_r` to `-1`. -/
theorem tameTeichmullerChar_neg_one (hp2 : p ≠ 2) :
    tameTeichmullerChar p r hr ⟨-1, ZMod.neg_one_mem_rootsOfUnity_prime_pow hp2 r⟩ = -1 := by
  have hneg : ZMod.unitsMap (dvd_pow_self p hr) (-1 : (ZMod (p ^ r))ˣ) = -1 := by
    apply Units.ext
    simp [ZMod.unitsMap]
  rw [tameTeichmullerChar_apply, hneg, padicTeichmuller_neg_one hp2]

/-- The lifted Teichmüller character has order `p - 1` in the character group `Hom(Δ_r, ℤ_[p]ˣ)`. -/
theorem orderOf_tameTeichmullerChar : orderOf (tameTeichmullerChar p r hr) = p - 1 := by
  have hpow : tameTeichmullerChar p r hr ^ (p - 1) = 1 := by
    refine MonoidHom.ext fun a ↦ ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow]
    have ha : a ^ (p - 1) = 1 := Subtype.ext ((mem_rootsOfUnity (p - 1) a.val).mp a.property)
    rw [ha, map_one]
  refine dvd_antisymm (orderOf_dvd_of_pow_eq_one hpow) ?_
  have : IsCyclic (rootsOfUnity (p - 1) (ZMod (p ^ r))) :=
    ZMod.isCyclic_rootsOfUnity_prime_pow p r hr
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity (p - 1) (ZMod (p ^ r)))
  have hordg : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, ZMod.natCard_rootsOfUnity_prime_pow p r hr]
  conv_lhs => rw [← hordg]
  refine orderOf_dvd_of_pow_eq_one (tameTeichmullerChar_injective p r hr ?_)
  rw [map_pow, map_one]
  exact DFunLike.congr_fun (pow_orderOf_eq_one (tameTeichmullerChar p r hr)) g

/-- **Periodicity of powers of the Teichmüller character**: `ω ^ i = ω ^ j` if and only if
`i ≡ j (mod p - 1)`. -/
theorem tameTeichmullerChar_zpow_eq_iff (i j : ℤ) :
    tameTeichmullerChar p r hr ^ i = tameTeichmullerChar p r hr ^ j ↔
      ((p - 1 : ℕ) : ℤ) ∣ i - j := by
  -- Bridge `MonoidHom.instZPow` to the `Group` instance's `DivInvMonoid.toZPow`.
  have hzpow (z : ℤ) :
      tameTeichmullerChar p r hr ^ z =
        @HPow.hPow _ _ _ (@instHPow _ _ DivInvMonoid.toZPow.toPow)
          (tameTeichmullerChar p r hr) z := by
    obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg <;> refine MonoidHom.ext fun a ↦ ?_ <;>
      simp [zpow_natCast]
  rw [hzpow i, hzpow j, ← mul_inv_eq_one, ← zpow_sub, ← orderOf_dvd_iff_zpow_eq_one,
    orderOf_tameTeichmullerChar]

/-- **Every `ℤ_[p]`-valued character of the tame subgroup is a power of `ω`.** The map
`i ↦ ω ^ i` gives a bijection `ZMod (p - 1) ≃ (Δ_r →* ℤ_[p]ˣ)`. -/
noncomputable def tameCharEquivZMod :
    ZMod (p - 1) ≃ (rootsOfUnity (p - 1) (ZMod (p ^ r)) →* ℤ_[p]ˣ) := by
  classical
  have : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩
  have := hasEnoughRootsOfUnity_padicInt_exponent_rootsOfUnity_prime_pow p r hr
  refine Equiv.ofBijective (fun i : ZMod (p - 1) ↦ tameTeichmullerChar p r hr ^ (i.val : ℤ)) ?_
  have hinj : Function.Injective
      (fun i : ZMod (p - 1) ↦ tameTeichmullerChar p r hr ^ (i.val : ℤ)) := by
    intro i j hij
    have hdvd : ((p - 1 : ℕ) : ℤ) ∣ (i.val : ℤ) - (j.val : ℤ) :=
      (tameTeichmullerChar_zpow_eq_iff p r hr i.val j.val).mp hij
    have hmod : ((i.val : ℤ) : ZMod (p - 1)) = ((j.val : ℤ) : ZMod (p - 1)) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (by simpa using dvd_neg.mpr hdvd)
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hmod
  have hcard : Fintype.card (ZMod (p - 1)) =
      Fintype.card (rootsOfUnity (p - 1) (ZMod (p ^ r)) →* ℤ_[p]ˣ) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ ℤ_[p],
      ZMod.natCard_rootsOfUnity_prime_pow p r hr]
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩

@[simp]
theorem tameCharEquivZMod_apply (i : ZMod (p - 1)) :
    tameCharEquivZMod p r hr i = tameTeichmullerChar p r hr ^ (i.val : ℤ) :=
  (rfl)

end TameCharacters

section Projectors

variable (p r : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p ^ r} ℚ K]

/-- **The tame cyclotomic class representation**: restriction of
`TauCeti.cyclotomicClassAction ℤ_[p] (p ^ r) K` to the tame subgroup
`rootsOfUnity (p - 1) (ZMod (p ^ r))`. -/
noncomputable def cyclotomicClassTameRepresentation :
    Representation ℤ_[p] (rootsOfUnity (p - 1) (ZMod (p ^ r)))
      (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  (cyclotomicClassAction ℤ_[p] (p ^ r) K).comp
    (rootsOfUnity (p - 1) (ZMod (p ^ r))).subtype

@[simp]
theorem cyclotomicClassTameRepresentation_apply (a : rootsOfUnity (p - 1) (ZMod (p ^ r))) :
    cyclotomicClassTameRepresentation p r K a =
      cyclotomicClassAction ℤ_[p] (p ^ r) K a.val :=
  (rfl)

variable (hr : r ≠ 0)

open scoped Classical in
/-- **The `i`-th tame character projector** `e_i` on `ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))`,
defined as the action of the character idempotent `e_{ω^i}` of `ℤ_[p][Δ_r]`. -/
noncomputable def cyclotomicClassProjector (i : ℤ) :
    Module.End ℤ_[p] (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  (cyclotomicClassTameRepresentation p r K).asAlgebraHom
    (charIdempotent (tameTeichmullerChar p r hr ^ i))

open scoped Classical in
theorem cyclotomicClassProjector_eq (i : ℤ) :
    cyclotomicClassProjector p r K hr i =
      (cyclotomicClassTameRepresentation p r K).asAlgebraHom
        (charIdempotent (tameTeichmullerChar p r hr ^ i)) :=
  (rfl)

/-- **The `i`-th tame eigenspace** `A_r^{(i)}` of `ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))`: the
joint eigenspace on which every `a ∈ Δ_r` acts by `ω(a) ^ i`. -/
noncomputable def cyclotomicClassEigenspace (i : ℤ) :
    Submodule ℤ_[p] (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  (cyclotomicClassTameRepresentation p r K).charEigenspace (tameTeichmullerChar p r hr ^ i)

open scoped Classical in
/-- **Explicit formula for the `i`-th tame character projector**:
`e_i = (p - 1)⁻¹ ∑_{a ∈ Δ_r} ω(a) ^ (-i) • σ_a`. -/
theorem cyclotomicClassProjector_eq_sum (i : ℤ) :
    cyclotomicClassProjector p r K hr i =
      Ring.inverse ((p - 1 : ℕ) : ℤ_[p]) •
        ∑ a : rootsOfUnity (p - 1) (ZMod (p ^ r)),
          (((padicTeichmuller p (ZMod.unitsMap (dvd_pow_self p hr) a.val) ^ (-i) : ℤ_[p]ˣ) :
              ℤ_[p])) •
            cyclotomicClassAction ℤ_[p] (p ^ r) K a.val := by
  rw [cyclotomicClassProjector, Representation.asAlgebraHom_charIdempotent,
    ZMod.natCard_rootsOfUnity_prime_pow p r hr]
  congr 1
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [cyclotomicClassTameRepresentation_apply, MonoidHom.zpow_apply, tameTeichmullerChar_apply,
    zpow_neg]

/-- **Eigencharacter criterion for `A_r^{(i)}`**: a vector lies in the `i`-th tame eigenspace
exactly when every `a ∈ Δ_r` acts on it by `ω(a) ^ i`. -/
theorem mem_cyclotomicClassEigenspace_iff (i : ℤ)
    {x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))} :
    x ∈ cyclotomicClassEigenspace p r K hr i ↔
      ∀ a : rootsOfUnity (p - 1) (ZMod (p ^ r)),
        cyclotomicClassAction ℤ_[p] (p ^ r) K a.val x =
          (((padicTeichmuller p (ZMod.unitsMap (dvd_pow_self p hr) a.val) ^ i : ℤ_[p]ˣ) : ℤ_[p])) •
            x := by
  simp only [cyclotomicClassEigenspace, Representation.mem_charEigenspace_iff,
    cyclotomicClassTameRepresentation_apply, MonoidHom.zpow_apply, tameTeichmullerChar_apply]

/-- The `i`-th tame projector takes values in the `i`-th tame eigenspace. -/
theorem cyclotomicClassProjector_apply_mem (i : ℤ) (x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    cyclotomicClassProjector p r K hr i x ∈ cyclotomicClassEigenspace p r K hr i := by
  classical
  exact Representation.asAlgebraHom_charIdempotent_apply_mem _ _ x

/-- The `i`-th tame projector fixes every element of the `i`-th tame eigenspace. -/
theorem cyclotomicClassProjector_apply_of_mem {i : ℤ}
    {x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))} (hx : x ∈ cyclotomicClassEigenspace p r K hr i) :
    cyclotomicClassProjector p r K hr i x = x := by
  classical
  exact Representation.asAlgebraHom_charIdempotent_apply_of_mem _
    (isUnit_natCard_rootsOfUnity_prime_pow p r hr) hx

/-- **The range of the `i`-th tame projector is the `i`-th tame eigenspace.** -/
theorem range_cyclotomicClassProjector (i : ℤ) :
    LinearMap.range (cyclotomicClassProjector p r K hr i) =
      cyclotomicClassEigenspace p r K hr i := by
  classical
  exact Representation.range_asAlgebraHom_charIdempotent _
    (isUnit_natCard_rootsOfUnity_prime_pow p r hr) _

/-- **Periodicity of tame projectors modulo `p - 1`.** -/
theorem cyclotomicClassProjector_eq_of_dvd {i j : ℤ} (h : ((p - 1 : ℕ) : ℤ) ∣ i - j) :
    cyclotomicClassProjector p r K hr i = cyclotomicClassProjector p r K hr j := by
  rw [cyclotomicClassProjector, cyclotomicClassProjector,
    (tameTeichmullerChar_zpow_eq_iff p r hr i j).mpr h]

/-- **Periodicity of tame eigenspaces modulo `p - 1`.** -/
theorem cyclotomicClassEigenspace_eq_of_dvd {i j : ℤ} (h : ((p - 1 : ℕ) : ℤ) ∣ i - j) :
    cyclotomicClassEigenspace p r K hr i = cyclotomicClassEigenspace p r K hr j := by
  rw [← range_cyclotomicClassProjector, ← range_cyclotomicClassProjector,
    cyclotomicClassProjector_eq_of_dvd p r K hr h]

/-- **Idempotence of tame projectors**: `e_i ∘ e_i = e_i`. -/
@[simp]
theorem cyclotomicClassProjector_comp_self (i : ℤ) :
    (cyclotomicClassProjector p r K hr i).comp (cyclotomicClassProjector p r K hr i) =
      cyclotomicClassProjector p r K hr i := by
  classical
  rw [← Module.End.mul_eq_comp, cyclotomicClassProjector, ← map_mul,
    (isIdempotentElem_charIdempotent _).eq]

/-- **Orthogonality of distinct tame projectors**: `e_i ∘ e_j = 0` when `i ≢ j (mod p - 1)`. -/
theorem cyclotomicClassProjector_comp_of_not_dvd {i j : ℤ} (h : ¬((p - 1 : ℕ) : ℤ) ∣ i - j) :
    (cyclotomicClassProjector p r K hr i).comp (cyclotomicClassProjector p r K hr j) = 0 := by
  classical
  have hne : tameTeichmullerChar p r hr ^ i ≠ tameTeichmullerChar p r hr ^ j :=
    mt (tameTeichmullerChar_zpow_eq_iff p r hr i j).mp h
  rw [← Module.End.mul_eq_comp, cyclotomicClassProjector, cyclotomicClassProjector, ← map_mul,
    charIdempotent_mul_charIdempotent_of_ne hne, map_zero]

/-- **Completeness of tame projectors**: `∑_{i ∈ ZMod (p - 1)} e_i = id`. -/
theorem sum_cyclotomicClassProjector [NeZero (p - 1)] :
    ∑ i : ZMod (p - 1), cyclotomicClassProjector p r K hr i.val = LinearMap.id := by
  classical
  have := hasEnoughRootsOfUnity_padicInt_exponent_rootsOfUnity_prime_pow p r hr
  obtain ⟨-, hsum⟩ :=
    (completeOrthogonalIdempotents_charIdempotent
      (isUnit_natCard_rootsOfUnity_prime_pow p r hr)).map
      (cyclotomicClassTameRepresentation p r K).asAlgebraHom.toRingHom
  have heq : ∑ i : ZMod (p - 1), cyclotomicClassProjector p r K hr i.val =
      ∑ χ : rootsOfUnity (p - 1) (ZMod (p ^ r)) →* ℤ_[p]ˣ,
        (cyclotomicClassTameRepresentation p r K).asAlgebraHom (charIdempotent χ) :=
    Fintype.sum_equiv (tameCharEquivZMod p r hr) _ _ fun i ↦ by
      rw [tameCharEquivZMod_apply, cyclotomicClassProjector]
  simp only [Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hsum
  rw [heq, hsum, Module.End.one_eq_id]

/-- **Internal direct-sum decomposition into tame eigenspaces**:
`ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K)) = ⨁_{i : ZMod (p - 1)} A_r^{(i)}`. -/
theorem isInternal_cyclotomicClassEigenspace :
    DirectSum.IsInternal
      (fun i : ZMod (p - 1) ↦ cyclotomicClassEigenspace p r K hr i.val) := by
  classical
  have := hasEnoughRootsOfUnity_padicInt_exponent_rootsOfUnity_prime_pow p r hr
  have hint := Representation.isInternal_charEigenspace (cyclotomicClassTameRepresentation p r K)
    (isUnit_natCard_rootsOfUnity_prime_pow p r hr)
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint ⊢
  obtain ⟨hindep, hsup⟩ := hint
  refine ⟨?_, ?_⟩
  · exact hindep.comp (tameCharEquivZMod p r hr).injective
  · exact ((tameCharEquivZMod p r hr).surjective.iSup_comp _).trans hsup

/-- **The tame eigenspace decomposition as a `ℤ_[p]`-linear equivalence**:
`(⨁ i : ZMod (p - 1), A_r^{(i)}) ≃ₗ[ℤ_[p]] A_r`. -/
noncomputable def cyclotomicClassEigenspaceEquiv :
    (⨁ i : ZMod (p - 1), cyclotomicClassEigenspace p r K hr i.val) ≃ₗ[ℤ_[p]]
      (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap _)
    (isInternal_cyclotomicClassEigenspace p r K hr)

/-- `TauCeti.cyclotomicClassEigenspaceEquiv` acts by summing the eigenspace inclusions via
`DirectSum.coeLinearMap`. -/
theorem cyclotomicClassEigenspaceEquiv_apply
    (x : ⨁ i : ZMod (p - 1), cyclotomicClassEigenspace p r K hr i.val) :
    cyclotomicClassEigenspaceEquiv p r K hr x =
      DirectSum.coeLinearMap
        (fun i : ZMod (p - 1) ↦ cyclotomicClassEigenspace p r K hr i.val) x :=
  (rfl)

/-- On a single summand `DirectSum.of`, `TauCeti.cyclotomicClassEigenspaceEquiv` is the submodule
inclusion. -/
@[simp]
theorem cyclotomicClassEigenspaceEquiv_of [DecidableEq (ZMod (p - 1))] (i : ZMod (p - 1))
    (x : cyclotomicClassEigenspace p r K hr i.val) :
    cyclotomicClassEigenspaceEquiv p r K hr
        (DirectSum.of (fun j : ZMod (p - 1) ↦ cyclotomicClassEigenspace p r K hr j.val) i x) =
      (x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  DirectSum.coeLinearMap_of (fun j : ZMod (p - 1) ↦ cyclotomicClassEigenspace p r K hr j.val) i x

/-- On a single linear summand `DirectSum.lof`, `TauCeti.cyclotomicClassEigenspaceEquiv` is the
submodule inclusion. -/
theorem cyclotomicClassEigenspaceEquiv_lof [DecidableEq (ZMod (p - 1))] (i : ZMod (p - 1))
    (x : cyclotomicClassEigenspace p r K hr i.val) :
    cyclotomicClassEigenspaceEquiv p r K hr
        (DirectSum.lof ℤ_[p] (ZMod (p - 1))
          (fun j : ZMod (p - 1) ↦ cyclotomicClassEigenspace p r K hr j.val) i x) =
      (x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) := by
  rw [DirectSum.lof_eq_of, cyclotomicClassEigenspaceEquiv_of]

/-- **Inverse components of the tame eigenspace decomposition.** The `i`-th component of
`(cyclotomicClassEigenspaceEquiv p r K hr).symm x` equals
`cyclotomicClassProjector p r K hr i.val x`. -/
@[simp]
theorem coe_cyclotomicClassEigenspaceEquiv_symm_apply
    (x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) (i : ZMod (p - 1)) :
    (((cyclotomicClassEigenspaceEquiv p r K hr).symm x i :
        cyclotomicClassEigenspace p r K hr i.val) :
      ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) =
      cyclotomicClassProjector p r K hr i.val x := by
  classical
  have : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩
  have hproj : ∀ z : ⨁ j : ZMod (p - 1), cyclotomicClassEigenspace p r K hr j.val,
      ((z i : cyclotomicClassEigenspace p r K hr i.val) :
          ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) =
        cyclotomicClassProjector p r K hr i.val
          (cyclotomicClassEigenspaceEquiv p r K hr z) := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      rw [cyclotomicClassEigenspaceEquiv_of]
      rcases eq_or_ne j i with rfl | hji
      · rw [DirectSum.of_eq_same, cyclotomicClassProjector_apply_of_mem p r K hr y.property]
      · rw [DirectSum.of_eq_of_ne _ _ _ hji.symm, ZeroMemClass.coe_zero,
          cyclotomicClassProjector_eq]
        exact (Representation.asAlgebraHom_charIdempotent_apply_of_mem_of_ne _
          (fun h ↦ hji ((tameCharEquivZMod p r hr).injective h.symm)) y.property).symm
    | add u v hu hv =>
      rw [DirectSum.add_apply, Submodule.coe_add, map_add, map_add, hu, hv]
  simpa only [LinearEquiv.apply_symm_apply] using
    hproj ((cyclotomicClassEigenspaceEquiv p r K hr).symm x)

/-- **Action of `-1` on the `i`-th tame eigenspace** for an odd prime `p`. -/
theorem cyclotomicClassAction_neg_one_of_mem_eigenspace (hp2 : p ≠ 2)
    {i : ℤ} {x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))}
    (hx : x ∈ cyclotomicClassEigenspace p r K hr i) :
    cyclotomicClassAction ℤ_[p] (p ^ r) K (-1) x =
      ((((-1 : ℤ_[p]ˣ) ^ i : ℤ_[p]ˣ) : ℤ_[p])) • x := by
  have h := (Representation.mem_charEigenspace_iff _ _).mp hx
    ⟨-1, ZMod.neg_one_mem_rootsOfUnity_prime_pow hp2 r⟩
  rw [cyclotomicClassTameRepresentation_apply, MonoidHom.zpow_apply,
    tameTeichmullerChar_neg_one p r hr hp2] at h
  exact h

/-- For an odd prime `p`, `-1` acts trivially on every even tame eigenspace. -/
theorem cyclotomicClassAction_neg_one_of_mem_eigenspace_even
    (hp2 : p ≠ 2) {i : ℤ} (hi : Even i) {x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))}
    (hx : x ∈ cyclotomicClassEigenspace p r K hr i) :
    cyclotomicClassAction ℤ_[p] (p ^ r) K (-1) x = x := by
  rw [cyclotomicClassAction_neg_one_of_mem_eigenspace p r K hr hp2 hx,
    hi.neg_one_zpow, Units.val_one, one_smul]

/-- For an odd prime `p`, `-1` acts by negation on every odd tame eigenspace. -/
theorem cyclotomicClassAction_neg_one_of_mem_eigenspace_odd
    (hp2 : p ≠ 2) {i : ℤ} (hi : Odd i) {x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))}
    (hx : x ∈ cyclotomicClassEigenspace p r K hr i) :
    cyclotomicClassAction ℤ_[p] (p ^ r) K (-1) x = -x := by
  rw [cyclotomicClassAction_neg_one_of_mem_eigenspace p r K hr hp2 hx,
    hi.neg_one_zpow, Units.val_neg, Units.val_one, neg_one_smul]

/-- Every `Δ_r`-equivariant `ℤ_[p]`-linear endomorphism commutes with every tame projector. -/
theorem map_cyclotomicClassProjector_of_comm
    (f : Module.End ℤ_[p] (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))))
    (hf : ∀ a : rootsOfUnity (p - 1) (ZMod (p ^ r)),
      f.comp (cyclotomicClassAction ℤ_[p] (p ^ r) K a.val) =
        (cyclotomicClassAction ℤ_[p] (p ^ r) K a.val).comp f)
    (i : ℤ) (x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    f (cyclotomicClassProjector p r K hr i x) = cyclotomicClassProjector p r K hr i (f x) := by
  classical
  let φ : Representation.IntertwiningMap (cyclotomicClassTameRepresentation p r K)
      (cyclotomicClassTameRepresentation p r K) :=
    { toLinearMap := f
      isIntertwining' a := hf a }
  exact φ.apply_asAlgebraHom (charIdempotent (tameTeichmullerChar p r hr ^ i)) x

/-- Every Galois automorphism `σ_b` (`b ∈ (ZMod (p ^ r))ˣ`) commutes with every tame projector. -/
theorem cyclotomicClassAction_cyclotomicClassProjector
    (b : (ZMod (p ^ r))ˣ) (i : ℤ) (x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    cyclotomicClassAction ℤ_[p] (p ^ r) K b (cyclotomicClassProjector p r K hr i x) =
      cyclotomicClassProjector p r K hr i (cyclotomicClassAction ℤ_[p] (p ^ r) K b x) := by
  refine map_cyclotomicClassProjector_of_comm p r K hr _ (fun a ↦ ?_) i x
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, mul_comm]

/-- Every tame eigenspace is invariant under the full Galois group `(ZMod (p ^ r))ˣ`. -/
theorem cyclotomicClassAction_mem_cyclotomicClassEigenspace
    (b : (ZMod (p ^ r))ˣ) {i : ℤ} {x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))}
    (hx : x ∈ cyclotomicClassEigenspace p r K hr i) :
    cyclotomicClassAction ℤ_[p] (p ^ r) K b x ∈ cyclotomicClassEigenspace p r K hr i := by
  rw [← cyclotomicClassProjector_apply_of_mem p r K hr hx,
    cyclotomicClassAction_cyclotomicClassProjector]
  exact cyclotomicClassProjector_apply_mem p r K hr i _

end Projectors

section Tower

variable {p r s : ℕ} [Fact p.Prime]
  (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [IsCyclotomicExtension {p ^ r} ℚ K] [IsCyclotomicExtension {p ^ s} ℚ L] [Algebra K L]

open scoped Classical in
/-- Reindex a sum over the level-`s` tame subgroup along `ZMod.rootsOfUnityPrimePowEquiv` when the
summand depends on `a` through its reductions modulo `p` and `p ^ r`. -/
private theorem sum_rootsOfUnityPrimePow_unitsMap {V : Type*} [AddCommMonoid V]
    (hrs : r ≤ s) (hr : r ≠ 0) (hs : s ≠ 0) (Φ : (ZMod p)ˣ → (ZMod (p ^ r))ˣ → V) :
    (∑ a : rootsOfUnity (p - 1) (ZMod (p ^ s)),
        Φ (ZMod.unitsMap (dvd_pow_self p hs) a.val)
          (ZMod.unitsMap (pow_dvd_pow p hrs) a.val)) =
      ∑ b : rootsOfUnity (p - 1) (ZMod (p ^ r)),
        Φ (ZMod.unitsMap (dvd_pow_self p hr) b.val) b.val :=
  Fintype.sum_equiv (ZMod.rootsOfUnityPrimePowEquiv p hs hr).toEquiv _ _ fun a ↦ by
    rw [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
      ← ZMod.rootsOfUnityEquivUnitsPrime_apply p s hs a,
      ← ZMod.rootsOfUnityEquivUnitsPrime_apply p r hr,
      ZMod.rootsOfUnityEquivUnitsPrime_rootsOfUnityPrimePowEquiv,
      ZMod.coe_rootsOfUnityPrimePowEquiv hrs hs hr a]

/-- **Relative norm commutes with the tame character projectors** in a `p`-power cyclotomic
tower. -/
theorem relNormBaseChange_cyclotomicClassProjector (hrs : r ≤ s) (hr : r ≠ 0) (hs : s ≠ 0) (i : ℤ)
    (x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 L))) :
    ClassGroup.relNormBaseChange ℤ_[p] (𝓞 K) (𝓞 L) (cyclotomicClassProjector p s L hs i x) =
      cyclotomicClassProjector p r K hr i (ClassGroup.relNormBaseChange ℤ_[p] (𝓞 K) (𝓞 L) x) := by
  classical
  rw [cyclotomicClassProjector_eq_sum p s L hs i, cyclotomicClassProjector_eq_sum p r K hr i]
  simp only [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, map_smul, map_sum,
    relNormBaseChange_cyclotomicClassAction (pow_dvd_pow p hrs) K L]
  congr 1
  exact sum_rootsOfUnityPrimePow_unitsMap hrs hr hs fun u g ↦
    (((padicTeichmuller p u ^ (-i) : ℤ_[p]ˣ) : ℤ_[p])) •
      cyclotomicClassAction ℤ_[p] (p ^ r) K g (ClassGroup.relNormBaseChange ℤ_[p] (𝓞 K) (𝓞 L) x)

/-- **Class extension commutes with the tame character projectors** in a `p`-power cyclotomic
tower. -/
theorem extendedBaseChange_cyclotomicClassProjector (hrs : r ≤ s) (hr : r ≠ 0) (hs : s ≠ 0) (i : ℤ)
    (x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    cyclotomicClassProjector p s L hs i (ClassGroup.extendedBaseChange ℤ_[p] (𝓞 K) (𝓞 L) x) =
      ClassGroup.extendedBaseChange ℤ_[p] (𝓞 K) (𝓞 L) (cyclotomicClassProjector p r K hr i x) := by
  classical
  rw [cyclotomicClassProjector_eq_sum p s L hs i, cyclotomicClassProjector_eq_sum p r K hr i]
  simp only [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, map_smul, map_sum,
    extendedBaseChange_cyclotomicClassAction (pow_dvd_pow p hrs) K L]
  congr 1
  exact sum_rootsOfUnityPrimePow_unitsMap hrs hr hs fun u g ↦
    (((padicTeichmuller p u ^ (-i) : ℤ_[p]ˣ) : ℤ_[p])) •
      ClassGroup.extendedBaseChange ℤ_[p] (𝓞 K) (𝓞 L) (cyclotomicClassAction ℤ_[p] (p ^ r) K g x)

/-- Relative norm carries the `i`-th tame eigenspace at level `s` into that at level `r`. -/
theorem relNormBaseChange_mem_cyclotomicClassEigenspace (hrs : r ≤ s) (hr : r ≠ 0) (hs : s ≠ 0)
    {i : ℤ} {x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 L))}
    (hx : x ∈ cyclotomicClassEigenspace p s L hs i) :
    ClassGroup.relNormBaseChange ℤ_[p] (𝓞 K) (𝓞 L) x ∈
      cyclotomicClassEigenspace p r K hr i := by
  rw [← cyclotomicClassProjector_apply_of_mem p s L hs hx,
    relNormBaseChange_cyclotomicClassProjector K L hrs hr hs]
  exact cyclotomicClassProjector_apply_mem p r K hr i _

/-- Class extension carries the `i`-th tame eigenspace at level `r` into that at level `s`. -/
theorem extendedBaseChange_mem_cyclotomicClassEigenspace (hrs : r ≤ s) (hr : r ≠ 0) (hs : s ≠ 0)
    {i : ℤ} {x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))}
    (hx : x ∈ cyclotomicClassEigenspace p r K hr i) :
    ClassGroup.extendedBaseChange ℤ_[p] (𝓞 K) (𝓞 L) x ∈
      cyclotomicClassEigenspace p s L hs i := by
  rw [← cyclotomicClassProjector_apply_of_mem p r K hr hx,
    ← extendedBaseChange_cyclotomicClassProjector K L hrs hr hs]
  exact cyclotomicClassProjector_apply_mem p s L hs i _

end Tower

end TauCeti
