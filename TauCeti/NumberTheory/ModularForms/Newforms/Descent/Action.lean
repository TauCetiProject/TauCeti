/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MoebiusZMod
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.UpperTriFactorization
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Cosets

/-!
# The level-descent matrices are permuted by `Γ₀(N / p)`

`Newforms/Descent/Cosets.lean` defines the family `descendMatrix p N` that Miyake's level
descent at a prime `p` runs over, and leaves open both that the family is a set of coset
representatives and that the associated slash sum descends the level. This file proves neither of
those; it supplies a prerequisite for both: for `p ∣ N`, right multiplication by an element of
`Γ₀(N / p)` permutes the family, up to left multiplication by an element of `Γ₀(N)`, and the
`Γ₀(N)` witness has the lower-right entry of `γ` modulo `N / p`. The two cases `p² ∣ N` and
`p ∥ N` have different index maps and are proved separately.

The permutation is named rather than left existential, because that is what the descent
consumes: a slash by `γ ∈ Γ₀(N / p)` sends the summand at `v` to the summand at the image of `v`,
and the sum is unchanged only because that map is a bijection of the index set.

## The case `p² ∣ N`

The hypothesis enters twice. It collapses `descendMatrixCount p N` to `p`, so every index is
that of an upper-triangular member; and it gives `p ∣ N / p`, which places `γ` in `Γ₀(p)`, and
that is what makes the offset map `HeckeRing.GL2.upperTriShift` a bijection (`descendShift`).

## The case `p ∥ N`: the index line

With `p + 1` members the natural index set is the projective line over `ZMod p`: the
upper-triangular member `[1, j; 0, p]` sits at the affine point `j`, the extra member
`[1, 0; 0, p] γ_p` (for `γ_p = descendExtraGamma p N`) at `∞` (`descendIndexEquiv`). On that
line the descent's index map `j ↦ (b + j d) / (a + j c)` is the Möbius action of `moebiusGL`
(`LinearAlgebra/Matrix/GeneralLinearGroup/MoebiusZMod.lean`) at `γ` reduced modulo `p`, so it is
a bijection for free (`descendIndexShift_bijective`): the affine index with `a + j c ≡ 0` — which
exists exactly when `p ∤ c` — goes to `∞`, and `∞` comes back to `d / c`.

## The case `p ∥ N`: the factorisation

Every case is the general upper-triangular factorisation
`HeckeRing.GL2.exists_mem_Gamma0_upperTriRep_mul_of_isUnit`, applied to `γ` twisted by `γ_p`:
to `γ` itself at an affine index with `a + j c` a unit, to `γ γ_p⁻¹` at the degenerate affine
index, to `γ_p γ` at `∞` when `p ∤ c`, and to `γ_p γ γ_p⁻¹` at `∞` when `p ∣ c`. Since
`γ_p ≡ S = [0, -1; 1, 0] (mod p)` the twists have computable residues, which is what makes the
denominators units and pins the target indices; since `γ_p ≡ 1 (mod N / p)` every witness has
the lower-right entry of `γ` modulo `N / p`, which is what transporting a nebentypus needs.

## Main definitions

* `TauCeti.descendShift`: at `p² ∣ N`, `HeckeRing.GL2.upperTriShift` carried to
  `Fin (descendMatrixCount p N)` along `descendMatrixCount p N = p`.
* `TauCeti.descendIndexEquiv`: at `p ∥ N`, `Fin (descendMatrixCount p N) ≃ OnePoint (ZMod p)`.
* `TauCeti.descendIndexGL`: `moebiusGL` of `γ` modulo `p`, the element whose action is the
  descent's index map at `p ∥ N`.
* `TauCeti.descendIndexShift`: that action read back on the index set.

## Main results

* `TauCeti.cast_descendShift`, `TauCeti.descendShift_bijective`: at `p² ∣ N` the index map is
  `upperTriShift` transported, and a bijection.
* `TauCeti.exists_mem_Gamma0_descendMatrix_mul`: at `p² ∣ N`,
  `descendMatrix p N v * γ = α * descendMatrix p N (descendShift … v)` for some `α ∈ Γ₀(N)`
  whose lower-right entry is `γ 1 1 - γ 1 0 * shift v`.
* `TauCeti.descendIndexShift_bijective`: at `p ∥ N` the index map is a bijection.
* `TauCeti.exists_mem_Gamma0_descendMatrix_mul_of_not_sq_dvd`: at `p ∥ N`,
  `descendMatrix p N v * γ = α * descendMatrix p N (descendIndexShift … v)` for some
  `α ∈ Γ₀(N)` with `α 1 1 ≡ γ 1 1 (mod N / p)`; assembled from four private cases, one per value
  of the index map.
* `TauCeti.descendIndexShift_val_of_isUnit`, `TauCeti.descendIndexShift_val_of_eq_zero`,
  `TauCeti.descendIndexShift_val_of_le_of_ne_zero` and
  `TauCeti.descendIndexShift_val_of_le_of_eq_zero`: the value of the index map in each case.

## Scope

A statement uniform in the two cases is not made. The completeness of the family as a coset
system, the invariance of the slash sum and the behaviour at cusps are separate statements and
none of them is claimed here.

Corresponds to `descendCosetList_action_upper_tri_clean` (the `p² ∣ N` case) and to
`descendCosetList_action_upper_tri_extra`, `descendCosetList_action_extra` and
`descendCosetList_action` (the `p² ∤ N` branch, including its `Gamma0MapUnits` compatibility) of
the AINTLIB `LeanModularForms` project
(`LeanModularForms/StrongMultiplicityOne/DescentCosets.lean`, Chris Birkbeck, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>). The source
handles the pole by a direct matrix computation and proves bijectivity of the index map by an
injectivity argument on `Fin (p + 1)`; here both come from the projective line.
-/

public section

open CongruenceSubgroup HeckeRing.GL2 Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups OnePoint

namespace TauCeti

variable {p N : ℕ}

/-- **The offset map on the descent index set.** `HeckeRing.GL2.upperTriShift` carried across
`descendMatrixCount p N = p`, which holds because `p² ∣ N`. This is the map the descent's slash
sum reindexes along. -/
def descendShift (p N : ℕ) [NeZero p] (hpsq : p ^ 2 ∣ N) (γ : SL(2, ℤ))
    (v : Fin (descendMatrixCount p N)) : Fin (descendMatrixCount p N) :=
  (finCongr (descendMatrixCount_of_sq_dvd hpsq)).symm
    (upperTriShift p γ (finCongr (descendMatrixCount_of_sq_dvd hpsq) v))

/-- **The defining property of `descendShift`**: transported to `Fin p`, it is
`HeckeRing.GL2.upperTriShift`. Read the map off this rather than off the definition, whose
`finCongr` plumbing carries a proof argument. Stated with `Fin.cast` because that, not
`finCongr`, is the `simp` normal form. -/
@[simp] theorem cast_descendShift [NeZero p] (hpsq : p ^ 2 ∣ N) (γ : SL(2, ℤ))
    (v : Fin (descendMatrixCount p N)) :
    Fin.cast (descendMatrixCount_of_sq_dvd hpsq) (descendShift p N hpsq γ v)
      = upperTriShift p γ (Fin.cast (descendMatrixCount_of_sq_dvd hpsq) v) :=
  Equiv.apply_symm_apply (finCongr (descendMatrixCount_of_sq_dvd hpsq)) _

/-- The same, on underlying naturals, which is the form the `descendMatrix` branches read. -/
@[simp] theorem descendShift_val [NeZero p] (hpsq : p ^ 2 ∣ N) (γ : SL(2, ℤ))
    (v : Fin (descendMatrixCount p N)) : (descendShift p N hpsq γ v : ℕ)
      = (upperTriShift p γ (Fin.cast (descendMatrixCount_of_sq_dvd hpsq) v) : ℕ) :=
  congrArg Fin.val (cast_descendShift hpsq γ v)

/-- **The offset map is a bijection of the descent index set.** The hypothesis is `γ ∈ Γ₀(p)`,
which is all bijectivity needs. The descent acts by `γ ∈ Γ₀(N / p)`, and `p² ∣ N` puts that group
inside `Γ₀(p)`: a descent caller turns `p² ∣ N` into `p ∣ N / p` with
`Nat.dvd_div_of_mul_dvd` and feeds that to `Gamma0_le_Gamma0_of_dvd`. Reindexing the descent's
slash sum along this map is what the bijection is for. -/
theorem descendShift_bijective [NeZero p] (hpsq : p ^ 2 ∣ N) {γ : SL(2, ℤ)}
    (hγp : γ ∈ Gamma0 p) : Function.Bijective (descendShift p N hpsq γ) :=
  (finCongr (descendMatrixCount_of_sq_dvd (N := N) hpsq)).symm.bijective.comp
    ((upperTriShift_bijective hγp).comp
      (finCongr (descendMatrixCount_of_sq_dvd (N := N) hpsq)).bijective)

/-- **The descent family is permuted by `Γ₀(N / p)` when `p² ∣ N`.** For `γ ∈ Γ₀(N / p)`, the
product `descendMatrix p N v * γ` is an element of `Γ₀(N)` times the member of the family at
`descendShift p N hpsq γ v` — and that map is a bijection, by `descendShift_bijective`.

The target index is named rather than existentially quantified, because reindexing the descent's
slash sum needs the permutation itself, not merely that some member of the family appears.

The lower-right entry of `α` is given as an equation, as `exists_mem_Gamma0_upperTriRep_mul`
gives it, rather than as a congruence: the modulus at which it is useful varies with the caller.
Transporting a nebentypus through the descent reads off from it that `α` and `γ` agree modulo
`N / p`, since `N / p ∣ γ 1 0`. -/
theorem exists_mem_Gamma0_descendMatrix_mul (p N : ℕ) [NeZero p] (hpsq : p ^ 2 ∣ N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p)) (v : Fin (descendMatrixCount p N)) :
    ∃ α : SL(2, ℤ), α ∈ Gamma0 N ∧
      (α 1 1 : ℤ) = γ 1 1 - γ 1 0 * ((descendShift p N hpsq γ v : ℕ) : ℤ) ∧
      descendMatrix p N v * mapGL ℝ γ =
        mapGL ℝ α * descendMatrix p N (descendShift p N hpsq γ v) := by
  have hpN : p ∣ N := dvd_trans (dvd_pow_self p two_ne_zero) hpsq
  have hcount : descendMatrixCount p N = p := descendMatrixCount_of_sq_dvd hpsq
  have hv : v.val < p := lt_of_lt_of_le v.isLt hcount.le
  -- the second hypothesis is `N ∣ p c`, from `(N / p) ∣ c` and `p · (N / p) = N`
  have hpc := intCast_mul_apply_one_zero_eq_zero_of_mem_Gamma0_div hpN hγ
  obtain ⟨α, hα, hd, hmul⟩ :=
    exists_mem_Gamma0_upperTriRep_mul
      (Gamma0_le_Gamma0_of_dvd (Nat.dvd_div_of_mul_dvd (by rwa [← pow_two])) hγ) hpc ⟨v.val, hv⟩
  have hv' : ((descendShift p N hpsq γ v : Fin (descendMatrixCount p N)) : ℕ) < p :=
    lt_of_lt_of_le (descendShift p N hpsq γ v).isLt hcount.le
  -- the target index, named rather than left to definitional reduction through `finCongr`
  have htgt : (⟨(descendShift p N hpsq γ v : ℕ), hv'⟩ : Fin p) = upperTriShift p γ ⟨v.val, hv⟩ :=
    Fin.ext (descendShift_val hpsq γ v)
  refine ⟨α, hα, ?_, ?_⟩
  · rw [hd]
    exact congrArg (fun n : ℕ ↦ (γ 1 1 : ℤ) - γ 1 0 * (n : ℤ)) (congrArg Fin.val htgt).symm
  -- the real identity is the image of the rational one under `GL₂(ℚ) → GL₂(ℝ)`
  · simpa only [descendMatrix_of_lt hv, descendMatrix_of_lt hv', htgt, map_mul, map_mapGL]
      using congrArg (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)) hmul

/-! ## When `p` exactly divides `N` -/

/-- A prime is nonzero. Primality is what the projective line over `ZMod p` needs, and it supplies
the `NeZero p` that the descent family and the offset map need throughout this file. -/
local instance neZero_of_fact_prime [Fact p.Prime] : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

/-- **When `p²` does not divide `N`, the descent's index set is the projective line over
`ZMod p`.** `descendMatrixCount p N` is `p + 1` then, and `Fin (p + 1) ≃ Option (Fin p) ≃
Option (ZMod p)`, which is `OnePoint (ZMod p)`: the upper-triangular members are the affine
points and the extra representative is `∞`. -/
def descendIndexEquiv (p N : ℕ) [NeZero p] (hpsq : ¬ p ^ 2 ∣ N) :
    Fin (descendMatrixCount p N) ≃ OnePoint (ZMod p) :=
  (finCongr (descendMatrixCount_of_not_sq_dvd hpsq)).trans
    (finSuccEquivLast.trans (ZMod.finEquiv p).toEquiv.optionCongr)

/-- An index below `p` is the affine point it names. -/
@[simp] theorem descendIndexEquiv_apply_of_lt [NeZero p] (hpsq : ¬ p ^ 2 ∣ N)
    {v : Fin (descendMatrixCount p N)} (hv : v.val < p) :
    descendIndexEquiv p N hpsq v = (((v : ℕ) : ZMod p) : OnePoint (ZMod p)) := by
  have hcast : Fin.cast (descendMatrixCount_of_not_sq_dvd hpsq) v = Fin.castSucc ⟨v.val, hv⟩ :=
    Fin.ext rfl
  rw [descendIndexEquiv]
  -- `OnePoint (ZMod p)` is `Option (ZMod p)` by definition and the composite is typed at the
  -- former, so `Equiv.trans_apply` does not fire on its outer composition; `change` restates the
  -- value at `Option`, where the evaluation lemmas of the three factors apply.
  change (ZMod.finEquiv p).toEquiv.optionCongr
    (finSuccEquivLast (Fin.cast (descendMatrixCount_of_not_sq_dvd hpsq) v)) = _
  rw [hcast, finSuccEquivLast_castSucc, Equiv.optionCongr_apply, Option.map_some]
  exact congrArg some (ZMod.finEquiv_apply ⟨v.val, hv⟩)

/-- The index `p` is the point at infinity. -/
@[simp] theorem descendIndexEquiv_apply_of_le [NeZero p] (hpsq : ¬ p ^ 2 ∣ N)
    {v : Fin (descendMatrixCount p N)} (hv : p ≤ v.val) :
    descendIndexEquiv p N hpsq v = ∞ := by
  have hcast : Fin.cast (descendMatrixCount_of_not_sq_dvd hpsq) v = Fin.last p := by
    have hlt := v.isLt
    have hcount := descendMatrixCount_of_not_sq_dvd (p := p) hpsq
    exact Fin.ext (by rw [Fin.val_cast, Fin.val_last]; omega)
  rw [descendIndexEquiv]
  -- as in `descendIndexEquiv_apply_of_lt`: restate at `Option` so that the factors evaluate
  change (ZMod.finEquiv p).toEquiv.optionCongr
    (finSuccEquivLast (Fin.cast (descendMatrixCount_of_not_sq_dvd hpsq) v)) = _
  rw [hcast, finSuccEquivLast_last, Equiv.optionCongr_apply, Option.map_none]
  rfl

/-- The index of an affine point is its representative below `p`. -/
@[simp] theorem descendIndexEquiv_symm_coe_val [NeZero p] (hpsq : ¬ p ^ 2 ∣ N) (k : ZMod p) :
    ((descendIndexEquiv p N hpsq).symm (k : OnePoint (ZMod p)) : ℕ) = k.val := by
  have hk : k.val < descendMatrixCount p N := by
    rw [descendMatrixCount_of_not_sq_dvd hpsq]
    exact k.val_lt.trans (Nat.lt_succ_self p)
  have : (descendIndexEquiv p N hpsq).symm (k : OnePoint (ZMod p)) = ⟨k.val, hk⟩ := by
    rw [Equiv.symm_apply_eq, descendIndexEquiv_apply_of_lt hpsq (v := ⟨k.val, hk⟩) k.val_lt]
    simp
  rw [this]

/-- The index of the point at infinity is `p`. -/
@[simp] theorem descendIndexEquiv_symm_infty_val [NeZero p] (hpsq : ¬ p ^ 2 ∣ N) :
    ((descendIndexEquiv p N hpsq).symm ∞ : ℕ) = p := by
  have hp : p < descendMatrixCount p N := by
    rw [descendMatrixCount_of_not_sq_dvd hpsq]
    exact Nat.lt_succ_self p
  have : (descendIndexEquiv p N hpsq).symm ∞ = ⟨p, hp⟩ := by
    rw [Equiv.symm_apply_eq, descendIndexEquiv_apply_of_le hpsq (v := ⟨p, hp⟩) le_rfl]
  rw [this]

/-- **The Möbius element of the descent at `γ`**: `moebiusGL` of `γ` reduced modulo `p`, whose
action on the projective line is the descent's index map `j ↦ (b + j d) / (a + j c)`. -/
noncomputable def descendIndexGL (p : ℕ) [Fact p.Prime] (γ : SL(2, ℤ)) : GL (Fin 2) (ZMod p) :=
  moebiusGL ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod p))) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]
    exact one_ne_zero)

/-- The value of the descent's Möbius element at an affine point, in the entries of `γ`. -/
theorem descendIndexGL_smul_coe [Fact p.Prime] (γ : SL(2, ℤ)) (k : ZMod p) :
    descendIndexGL p γ • (k : OnePoint (ZMod p))
      = if ((γ 1 0 : ℤ) : ZMod p) * k + ((γ 0 0 : ℤ) : ZMod p) = 0 then ∞
        else ((((γ 1 1 : ℤ) : ZMod p) * k + ((γ 0 1 : ℤ) : ZMod p))
          / (((γ 1 0 : ℤ) : ZMod p) * k + ((γ 0 0 : ℤ) : ZMod p)) : ZMod p) := by
  rw [descendIndexGL, moebiusGL_smul_some]
  simp only [Matrix.map_apply, eq_intCast]

/-- The value of the descent's Möbius element at the point at infinity. -/
theorem descendIndexGL_smul_infty [Fact p.Prime] (γ : SL(2, ℤ)) :
    descendIndexGL p γ • (∞ : OnePoint (ZMod p))
      = if ((γ 1 0 : ℤ) : ZMod p) = 0 then ∞
        else (((γ 1 1 : ℤ) : ZMod p) / ((γ 1 0 : ℤ) : ZMod p) : ZMod p) := by
  rw [descendIndexGL, moebiusGL_smul_infty]
  simp only [Matrix.map_apply, eq_intCast]

/-- **An affine index with `a + j c` a unit goes to the offset map's value.** -/
@[simp] theorem descendIndexGL_smul_coe_of_isUnit [Fact p.Prime] {γ : SL(2, ℤ)} {j : Fin p}
    (hA : ((γ 0 0 : ℤ) : ZMod p) + ((j : ℕ) : ZMod p) * ((γ 1 0 : ℤ) : ZMod p) ≠ 0) :
    descendIndexGL p γ • (((j : ℕ) : ZMod p) : OnePoint (ZMod p))
      = (((upperTriShift p γ j : ℕ) : ZMod p) : OnePoint (ZMod p)) := by
  have hA' : IsUnit (((γ 0 0 : ℤ) : ZMod p) + ((j : ℕ) : ZMod p) * ((γ 1 0 : ℤ) : ZMod p)) :=
    isUnit_iff_ne_zero.mpr hA
  have hne : ((γ 1 0 : ℤ) : ZMod p) * ((j : ℕ) : ZMod p) + ((γ 0 0 : ℤ) : ZMod p) ≠ 0 := by
    have := hA'.ne_zero
    intro hz
    exact this (by linear_combination hz)
  rw [descendIndexGL_smul_coe]
  split_ifs with hc
  · exact absurd hc hne
  · rw [OnePoint.coe_eq_coe, div_eq_iff hne]
    linear_combination -(mul_upperTriShift_natCast hA')

/-- **The degenerate affine index goes to infinity.** When `a + j c ≡ 0`, the offset map has no
affine target — which is why the index set is the projective line, not `Fin p`. -/
@[simp] theorem descendIndexGL_smul_coe_of_eq_zero [Fact p.Prime] {γ : SL(2, ℤ)} {j : Fin p}
    (h : (((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p)) = 0) :
    descendIndexGL p γ • (((j : ℕ) : ZMod p) : OnePoint (ZMod p)) = ∞ := by
  rw [descendIndexGL_smul_coe]
  push_cast at h
  split_ifs with hc
  · rfl
  · exact absurd (by linear_combination h) hc

/-- **Infinity comes back to `d / c` when `p ∤ c`.** -/
@[simp] theorem descendIndexGL_smul_infty_of_ne_zero [Fact p.Prime] {γ : SL(2, ℤ)}
    (hc : ((γ 1 0 : ℤ) : ZMod p) ≠ 0) :
    descendIndexGL p γ • (∞ : OnePoint (ZMod p))
      = ((((γ 1 1 : ℤ) : ZMod p) / ((γ 1 0 : ℤ) : ZMod p) : ZMod p) : OnePoint (ZMod p)) := by
  rw [descendIndexGL_smul_infty]
  split_ifs with h
  · exact absurd h hc
  · rfl

/-- **Infinity is fixed when `p ∣ c`.** -/
@[simp] theorem descendIndexGL_smul_infty_of_eq_zero [Fact p.Prime] {γ : SL(2, ℤ)}
    (hc : ((γ 1 0 : ℤ) : ZMod p) = 0) : descendIndexGL p γ • (∞ : OnePoint (ZMod p)) = ∞ := by
  rw [descendIndexGL_smul_infty]
  split_ifs
  rfl

/-- **The index map when `p²` does not divide `N`**: the Möbius action of `descendIndexGL p γ` on
the projective line, read through `descendIndexEquiv`. It is a bijection
(`descendIndexShift_bijective`), and the descent's factorisation sends the member of the family
at `v` to the member at `descendIndexShift p N hpsq γ v`. -/
noncomputable def descendIndexShift (p N : ℕ) [Fact p.Prime] (hpsq : ¬ p ^ 2 ∣ N)
    (γ : SL(2, ℤ)) (v : Fin (descendMatrixCount p N)) : Fin (descendMatrixCount p N) :=
  (descendIndexEquiv p N hpsq).symm (descendIndexGL p γ • descendIndexEquiv p N hpsq v)

/-- **The index map is a bijection**, because a group action is. -/
theorem descendIndexShift_bijective [Fact p.Prime] (hpsq : ¬ p ^ 2 ∣ N)
    (γ : SL(2, ℤ)) : Function.Bijective (descendIndexShift p N hpsq γ) := by
  have h : descendIndexShift p N hpsq γ = ((descendIndexEquiv p N hpsq).trans
      ((MulAction.toPerm (descendIndexGL p γ)).trans (descendIndexEquiv p N hpsq).symm)) :=
    funext fun v ↦ rfl
  rw [h]
  exact Equiv.bijective _

/-- **The value of the index map at an affine index whose denominator is a unit**: the offset map's
value. -/
@[simp] theorem descendIndexShift_val_of_isUnit [Fact p.Prime] (hpsq : ¬ p ^ 2 ∣ N)
    {γ : SL(2, ℤ)} {v : Fin (descendMatrixCount p N)} (hv : v.val < p)
    (hA : ((γ 0 0 : ℤ) : ZMod p) + ((v : ℕ) : ZMod p) * ((γ 1 0 : ℤ) : ZMod p) ≠ 0) :
    (descendIndexShift p N hpsq γ v : ℕ) = (upperTriShift p γ ⟨v.val, hv⟩ : ℕ) := by
  rw [descendIndexShift, descendIndexEquiv_apply_of_lt hpsq hv,
    descendIndexGL_smul_coe_of_isUnit (j := ⟨v.val, hv⟩) (by simpa using hA),
    descendIndexEquiv_symm_coe_val, ZMod.val_natCast_of_lt (upperTriShift p γ ⟨v.val, hv⟩).isLt]

/-- **The value of the index map at the degenerate affine index**: the extra index `p`. -/
@[simp] theorem descendIndexShift_val_of_eq_zero [Fact p.Prime] (hpsq : ¬ p ^ 2 ∣ N)
    {γ : SL(2, ℤ)} {v : Fin (descendMatrixCount p N)} (hv : v.val < p)
    (h0 : (((γ 0 0 + (v : ℕ) * γ 1 0 : ℤ) : ZMod p)) = 0) :
    (descendIndexShift p N hpsq γ v : ℕ) = p := by
  rw [descendIndexShift, descendIndexEquiv_apply_of_lt hpsq hv,
    descendIndexGL_smul_coe_of_eq_zero (j := ⟨v.val, hv⟩) h0, descendIndexEquiv_symm_infty_val]

/-- **The value of the index map at the extra index when `p ∣ c`**: the extra index itself. -/
@[simp] theorem descendIndexShift_val_of_le_of_eq_zero [Fact p.Prime] (hpsq : ¬ p ^ 2 ∣ N)
    {γ : SL(2, ℤ)} {v : Fin (descendMatrixCount p N)} (hv : p ≤ v.val)
    (hc : ((γ 1 0 : ℤ) : ZMod p) = 0) : (descendIndexShift p N hpsq γ v : ℕ) = p := by
  rw [descendIndexShift, descendIndexEquiv_apply_of_le hpsq hv,
    descendIndexGL_smul_infty_of_eq_zero hc, descendIndexEquiv_symm_infty_val]

/-! ## The residues of the extra matrix and of its twists -/

/-- Modulo `p`, `γ γ_p⁻¹` reduces as `γ S⁻¹` does. -/
private theorem map_mul_inv_descendExtraGamma (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N)
    (γ : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) (γ * (descendExtraGamma p N)⁻¹)
      = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) (γ * ModularGroup.S⁻¹) := by
  rw [map_mul, map_inv, descendExtraGamma_map_intCast_zmod_eq_S hp hpN hpsq, ← map_inv, ← map_mul]

/-- Modulo `p`, `γ_p γ` reduces as `S γ` does. -/
private theorem map_descendExtraGamma_mul (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N)
    (γ : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) (descendExtraGamma p N * γ)
      = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) (ModularGroup.S * γ) := by
  rw [map_mul, descendExtraGamma_map_intCast_zmod_eq_S hp hpN hpsq, ← map_mul]

/-- Modulo `p`, `γ_p γ γ_p⁻¹` reduces as `S γ S⁻¹` does. -/
private theorem map_descendExtraGamma_mul_mul_inv (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) (γ : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p))
        (descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹)
      = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p))
          (ModularGroup.S * γ * ModularGroup.S⁻¹) := by
  rw [map_mul, map_mul, map_inv, descendExtraGamma_map_intCast_zmod_eq_S hp hpN hpsq, ← map_inv,
    ← map_mul, ← map_mul]

/-- The residues of `γ γ_p⁻¹` modulo `p`: those of `γ S⁻¹ = [-b, a; -d, c]`. -/
private theorem mul_inv_descendExtraGamma_apply_intCast_zmod (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) (γ : SL(2, ℤ)) :
    (((γ * (descendExtraGamma p N)⁻¹) 0 0 : ℤ) : ZMod p) = -((γ 0 1 : ℤ) : ZMod p) ∧
      (((γ * (descendExtraGamma p N)⁻¹) 0 1 : ℤ) : ZMod p) = ((γ 0 0 : ℤ) : ZMod p) ∧
      (((γ * (descendExtraGamma p N)⁻¹) 1 0 : ℤ) : ZMod p) = -((γ 1 1 : ℤ) : ZMod p) ∧
      (((γ * (descendExtraGamma p N)⁻¹) 1 1 : ℤ) : ZMod p) = ((γ 1 0 : ℤ) : ZMod p) := by
  have h : ∀ i j, (((γ * (descendExtraGamma p N)⁻¹) i j : ℤ) : ZMod p)
      = (((γ * ModularGroup.S⁻¹) i j : ℤ) : ZMod p) := fun i j ↦ by
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast] using
      congr_fun₂ (congrArg Subtype.val (map_mul_inv_descendExtraGamma hp hpN hpsq γ)) i j
  refine ⟨?_, ?_, ?_, ?_⟩ <;> [rw [h 0 0]; rw [h 0 1]; rw [h 1 0]; rw [h 1 1]] <;>
    simp [coe_mul, coe_inv, adjugate_fin_two, ModularGroup.coe_S, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- The residues of `γ_p γ` modulo `p`: those of `S γ = [-c, -d; a, b]`. -/
private theorem descendExtraGamma_mul_apply_intCast_zmod (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) (γ : SL(2, ℤ)) :
    (((descendExtraGamma p N * γ) 0 0 : ℤ) : ZMod p) = -((γ 1 0 : ℤ) : ZMod p) ∧
      (((descendExtraGamma p N * γ) 0 1 : ℤ) : ZMod p) = -((γ 1 1 : ℤ) : ZMod p) ∧
      (((descendExtraGamma p N * γ) 1 0 : ℤ) : ZMod p) = ((γ 0 0 : ℤ) : ZMod p) ∧
      (((descendExtraGamma p N * γ) 1 1 : ℤ) : ZMod p) = ((γ 0 1 : ℤ) : ZMod p) := by
  have h : ∀ i j, (((descendExtraGamma p N * γ) i j : ℤ) : ZMod p)
      = (((ModularGroup.S * γ) i j : ℤ) : ZMod p) := fun i j ↦ by
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast] using
      congr_fun₂ (congrArg Subtype.val (map_descendExtraGamma_mul hp hpN hpsq γ)) i j
  refine ⟨?_, ?_, ?_, ?_⟩ <;> [rw [h 0 0]; rw [h 0 1]; rw [h 1 0]; rw [h 1 1]] <;>
    simp [coe_mul, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]

/-- The residues of `γ_p γ γ_p⁻¹` modulo `p`: those of `S γ S⁻¹ = [d, -c; -b, a]`. -/
private theorem descendExtraGamma_mul_mul_inv_apply_intCast_zmod (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) (γ : SL(2, ℤ)) :
    (((descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) 0 0 : ℤ) : ZMod p)
        = ((γ 1 1 : ℤ) : ZMod p) ∧
      (((descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) 0 1 : ℤ) : ZMod p)
        = -((γ 1 0 : ℤ) : ZMod p) := by
  have h : ∀ i j, (((descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) i j : ℤ) : ZMod p)
      = (((ModularGroup.S * γ * ModularGroup.S⁻¹) i j : ℤ) : ZMod p) := fun i j ↦ by
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast] using
      congr_fun₂ (congrArg Subtype.val (map_descendExtraGamma_mul_mul_inv hp hpN hpsq γ)) i j
  refine ⟨?_, ?_⟩ <;> [rw [h 0 0]; rw [h 0 1]] <;>
    simp [coe_mul, coe_inv, adjugate_fin_two, ModularGroup.coe_S, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-! ## The four cases of the factorisation -/

/-- **An affine index with `a + j c` a unit stays affine**, at the offset map's value: the
factorisation is the upper-triangular one, unchanged. -/
private theorem exists_mem_Gamma0_descendMatrix_mul_of_isUnit [Fact p.Prime] (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p))
    {v : Fin (descendMatrixCount p N)} (hv : v.val < p)
    (hA : IsUnit (((γ 0 0 + (v : ℕ) * γ 1 0 : ℤ) : ZMod p))) :
    ∃ α : SL(2, ℤ), α ∈ Gamma0 N ∧ ((α 1 1 : ℤ) : ZMod (N / p)) = ((γ 1 1 : ℤ) : ZMod (N / p)) ∧
      descendMatrix p N v * mapGL ℝ γ
        = mapGL ℝ α * descendMatrix p N (descendIndexShift p N hpsq γ v) := by
  obtain ⟨α, hα, hd, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul_of_isUnit (j := ⟨v.val, hv⟩) hA
    (intCast_mul_apply_one_zero_eq_zero_of_mem_Gamma0_div hpN hγ)
  have hidx := descendIndexShift_val_of_isUnit hpsq hv (by push_cast at hA; exact hA.ne_zero)
  have hv' : (descendIndexShift p N hpsq γ v : ℕ) < p :=
    hidx ▸ (upperTriShift p γ ⟨v.val, hv⟩).isLt
  have htgt : (⟨(descendIndexShift p N hpsq γ v : ℕ), hv'⟩ : Fin p)
      = upperTriShift p γ ⟨v.val, hv⟩ := Fin.ext hidx
  refine ⟨α, hα, intCast_apply_one_one_eq_of_mem_Gamma0_of_eq hγ hd, ?_⟩
  simpa only [descendMatrix_of_lt hv, descendMatrix_of_lt hv', htgt, map_mul, map_mapGL]
    using congrArg (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)) hmul

/-- At the degenerate affine index the twist `γ γ_p⁻¹ ≡ γ S⁻¹` has unit denominator
`-(b + j d)` — both `a + j c` and `b + j d` cannot vanish, by `a d - b c = 1` — and its offset map
sends `j` to `0`. -/
private theorem mul_inv_descendExtraGamma_isUnit_and_upperTriShift_eq [Fact p.Prime]
    (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} {j : Fin p}
    (h0 : (((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p)) = 0) :
    IsUnit ((((γ * (descendExtraGamma p N)⁻¹) 0 0
        + (j : ℕ) * (γ * (descendExtraGamma p N)⁻¹) 1 0 : ℤ) : ZMod p)) ∧
      upperTriShift p (γ * (descendExtraGamma p N)⁻¹) j = ⟨0, NeZero.pos p⟩ := by
  have hp : p.Prime := Fact.out
  obtain ⟨hδ00, hδ01, hδ10, hδ11⟩ := mul_inv_descendExtraGamma_apply_intCast_zmod hp hpN hpsq γ
  have hdet : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod p) = 1 := by
    rw [Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ, Int.cast_one]
  have hA' : IsUnit ((((γ * (descendExtraGamma p N)⁻¹) 0 0 : ℤ) : ZMod p)
      + ((j : ℕ) : ZMod p) * (((γ * (descendExtraGamma p N)⁻¹) 1 0 : ℤ) : ZMod p)) := by
    rw [hδ00, hδ10]
    refine isUnit_iff_ne_zero.mpr fun hz ↦ one_ne_zero (α := ZMod p) ?_
    push_cast at h0 hdet
    linear_combination -hdet + ((γ 1 1 : ℤ) : ZMod p) * h0 + ((γ 1 0 : ℤ) : ZMod p) * hz
  refine ⟨by push_cast; exact hA', ?_⟩
  rw [upperTriShift_eq_iff hA', hδ01, hδ11]
  simp only [Nat.cast_zero, mul_zero]
  push_cast at h0
  exact h0.symm

/-- At `∞` with `p ∤ c` the twist `γ_p γ ≡ S γ` has unit denominator `-c` at `0`, and its offset
map sends `0` to `d / c`. -/
private theorem descendExtraGamma_mul_isUnit_and_upperTriShift_eq [Fact p.Prime]
    (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hc : ((γ 1 0 : ℤ) : ZMod p) ≠ 0) :
    IsUnit ((((descendExtraGamma p N * γ) 0 0
        + ((⟨0, NeZero.pos p⟩ : Fin p) : ℕ) * (descendExtraGamma p N * γ) 1 0 : ℤ) : ZMod p)) ∧
      ((upperTriShift p (descendExtraGamma p N * γ) ⟨0, NeZero.pos p⟩ : ℕ) : ZMod p)
        = ((γ 1 1 : ℤ) : ZMod p) / ((γ 1 0 : ℤ) : ZMod p) := by
  have hp : p.Prime := Fact.out
  obtain ⟨hδ00, hδ01, -, -⟩ := descendExtraGamma_mul_apply_intCast_zmod hp hpN hpsq γ
  have hA' : IsUnit ((((descendExtraGamma p N * γ) 0 0 : ℤ) : ZMod p)
      + (((⟨0, NeZero.pos p⟩ : Fin p) : ℕ) : ZMod p)
        * (((descendExtraGamma p N * γ) 1 0 : ℤ) : ZMod p)) := by
    simp only [Nat.cast_zero, zero_mul, add_zero, hδ00]
    exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hc)
  refine ⟨by push_cast; simpa only [Nat.cast_zero, zero_mul, add_zero] using hA', ?_⟩
  have h := mul_upperTriShift_natCast hA'
  simp only [Nat.cast_zero, zero_mul, add_zero, hδ00, hδ01] at h
  rw [eq_div_iff hc]
  linear_combination -h

/-- **The value of the index map at the extra index when `p ∤ c`**: the offset map of the twist
`γ_p γ` at `0`, that is `d / c`. -/
@[simp] theorem descendIndexShift_val_of_le_of_ne_zero [Fact p.Prime] (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} {v : Fin (descendMatrixCount p N)} (hv : p ≤ v.val)
    (hc : ((γ 1 0 : ℤ) : ZMod p) ≠ 0) : (descendIndexShift p N hpsq γ v : ℕ)
      = (upperTriShift p (descendExtraGamma p N * γ) ⟨0, NeZero.pos p⟩ : ℕ) := by
  obtain ⟨-, hshift⟩ := descendExtraGamma_mul_isUnit_and_upperTriShift_eq hpN hpsq hc
  rw [descendIndexShift, descendIndexEquiv_apply_of_le hpsq hv,
    descendIndexGL_smul_infty_of_ne_zero hc, descendIndexEquiv_symm_coe_val, ← hshift,
    ZMod.val_natCast_of_lt
      (upperTriShift p (descendExtraGamma p N * γ) ⟨0, NeZero.pos p⟩).isLt]

/-- At `∞` with `p ∣ c` the twist `γ_p γ γ_p⁻¹ ≡ S γ S⁻¹` has unit denominator `d` at `0` — as
`a d ≡ 1` — and its offset map sends `0` to `-c / d ≡ 0`. -/
private theorem descendExtraGamma_mul_mul_inv_isUnit_and_upperTriShift_eq [Fact p.Prime]
    (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hc : ((γ 1 0 : ℤ) : ZMod p) = 0) :
    IsUnit ((((descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) 0 0
        + ((⟨0, NeZero.pos p⟩ : Fin p) : ℕ)
          * (descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) 1 0 : ℤ) : ZMod p)) ∧
      upperTriShift p (descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) ⟨0, NeZero.pos p⟩
        = ⟨0, NeZero.pos p⟩ := by
  have hp : p.Prime := Fact.out
  obtain ⟨hδ00, hδ01⟩ := descendExtraGamma_mul_mul_inv_apply_intCast_zmod hp hpN hpsq γ
  have hdet : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod p) = 1 := by
    rw [Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ, Int.cast_one]
  have hA' : IsUnit ((((descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) 0 0 : ℤ) : ZMod p)
      + (((⟨0, NeZero.pos p⟩ : Fin p) : ℕ) : ZMod p)
        * (((descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) 1 0 : ℤ) : ZMod p)) := by
    simp only [Nat.cast_zero, zero_mul, add_zero, hδ00]
    refine isUnit_iff_ne_zero.mpr fun hz ↦ one_ne_zero (α := ZMod p) ?_
    push_cast at hdet
    linear_combination -hdet + ((γ 0 0 : ℤ) : ZMod p) * hz - ((γ 0 1 : ℤ) : ZMod p) * hc
  refine ⟨by push_cast; simpa only [Nat.cast_zero, zero_mul, add_zero] using hA', ?_⟩
  rw [upperTriShift_eq_iff hA', hδ01, hc]
  simp only [Nat.cast_zero, mul_zero, zero_mul, neg_zero, add_zero]

/-- **The degenerate affine index goes to the extra representative.** The factorisation of the
twist `γ γ_p⁻¹` at `j` lands on `[1, 0; 0, p]`; multiplying it back by `γ_p` lands on the extra
member `[1, 0; 0, p] γ_p`. -/
private theorem exists_mem_Gamma0_descendMatrix_mul_of_eq_zero [Fact p.Prime] (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p))
    {v : Fin (descendMatrixCount p N)} (hv : v.val < p)
    (h0 : (((γ 0 0 + (v : ℕ) * γ 1 0 : ℤ) : ZMod p)) = 0) :
    ∃ α : SL(2, ℤ), α ∈ Gamma0 N ∧ ((α 1 1 : ℤ) : ZMod (N / p)) = ((γ 1 1 : ℤ) : ZMod (N / p)) ∧
      descendMatrix p N v * mapGL ℝ γ
        = mapGL ℝ α * descendMatrix p N (descendIndexShift p N hpsq γ v) := by
  have hp : p.Prime := Fact.out
  have hδ : γ * (descendExtraGamma p N)⁻¹ ∈ Gamma0 (N / p) :=
    Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ (descendExtraGamma_mem_Gamma0 hp hpN hpsq))
  obtain ⟨hA, hshift⟩ :=
    mul_inv_descendExtraGamma_isUnit_and_upperTriShift_eq (j := ⟨v.val, hv⟩) hpN hpsq h0
  obtain ⟨α, hα, hd, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul_of_isUnit hA
    (intCast_mul_apply_one_zero_eq_zero_of_mem_Gamma0_div hpN hδ)
  have hidx := descendIndexShift_val_of_eq_zero hpsq hv h0
  refine ⟨α, hα, (intCast_apply_one_one_eq_of_mem_Gamma0_of_eq hδ hd).trans ?_, ?_⟩
  · have h : map (Int.castRingHom (ZMod (N / p))) (γ * (descendExtraGamma p N)⁻¹)
        = map (Int.castRingHom (ZMod (N / p))) γ := by
      rw [map_mul, map_inv, descendExtraGamma_map_intCast_zmod_div_eq_one hp hpN hpsq, inv_one,
        mul_one]
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast] using
      congr_fun₂ (congrArg Subtype.val h) 1 1
  · have h := congrArg (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)) hmul
    simp only [map_mul, map_mapGL, hshift] at h
    rw [descendMatrix_of_lt hv, descendMatrix_of_le hidx.ge,
      ← inv_mul_cancel_right γ (descendExtraGamma p N), map_mul, map_mul, ← mul_assoc, h,
      mul_assoc]

/-- **The extra representative moves into the affine line when `p ∤ c`**, landing at `d / c`:
the factorisation of the twist `γ_p γ` at `0`. -/
private theorem exists_mem_Gamma0_descendMatrix_mul_of_le_of_ne_zero [Fact p.Prime]
    (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p))
    {v : Fin (descendMatrixCount p N)} (hv : p ≤ v.val) (hc : ((γ 1 0 : ℤ) : ZMod p) ≠ 0) :
    ∃ α : SL(2, ℤ), α ∈ Gamma0 N ∧ ((α 1 1 : ℤ) : ZMod (N / p)) = ((γ 1 1 : ℤ) : ZMod (N / p)) ∧
      descendMatrix p N v * mapGL ℝ γ
        = mapGL ℝ α * descendMatrix p N (descendIndexShift p N hpsq γ v) := by
  have hp : p.Prime := Fact.out
  have hδ : descendExtraGamma p N * γ ∈ Gamma0 (N / p) :=
    Subgroup.mul_mem _ (descendExtraGamma_mem_Gamma0 hp hpN hpsq) hγ
  obtain ⟨hA, -⟩ := descendExtraGamma_mul_isUnit_and_upperTriShift_eq hpN hpsq hc
  obtain ⟨α, hα, hd, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul_of_isUnit hA
    (intCast_mul_apply_one_zero_eq_zero_of_mem_Gamma0_div hpN hδ)
  have hidx := descendIndexShift_val_of_le_of_ne_zero hpN hpsq hv hc
  have hv' : (descendIndexShift p N hpsq γ v : ℕ) < p :=
    hidx ▸ (upperTriShift p (descendExtraGamma p N * γ) ⟨0, NeZero.pos p⟩).isLt
  have htgt : (⟨(descendIndexShift p N hpsq γ v : ℕ), hv'⟩ : Fin p)
      = upperTriShift p (descendExtraGamma p N * γ) ⟨0, NeZero.pos p⟩ := Fin.ext hidx
  refine ⟨α, hα, (intCast_apply_one_one_eq_of_mem_Gamma0_of_eq hδ hd).trans ?_, ?_⟩
  · have h : map (Int.castRingHom (ZMod (N / p))) (descendExtraGamma p N * γ)
        = map (Int.castRingHom (ZMod (N / p))) γ := by
      rw [map_mul, descendExtraGamma_map_intCast_zmod_div_eq_one hp hpN hpsq, one_mul]
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast] using
      congr_fun₂ (congrArg Subtype.val h) 1 1
  · rw [descendMatrix_of_le hv, descendMatrix_of_lt hv', htgt, mul_assoc, ← map_mul]
    simpa only [map_mul, map_mapGL]
      using congrArg (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)) hmul

/-- **The extra representative is fixed when `p ∣ c`**: the factorisation of the twist
`γ_p γ γ_p⁻¹` at `0` lands on `[1, 0; 0, p]`, and multiplying back by `γ_p` returns to the extra
member. -/
private theorem exists_mem_Gamma0_descendMatrix_mul_of_le_of_eq_zero [Fact p.Prime]
    (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p))
    {v : Fin (descendMatrixCount p N)} (hv : p ≤ v.val) (hc : ((γ 1 0 : ℤ) : ZMod p) = 0) :
    ∃ α : SL(2, ℤ), α ∈ Gamma0 N ∧ ((α 1 1 : ℤ) : ZMod (N / p)) = ((γ 1 1 : ℤ) : ZMod (N / p)) ∧
      descendMatrix p N v * mapGL ℝ γ
        = mapGL ℝ α * descendMatrix p N (descendIndexShift p N hpsq γ v) := by
  have hp : p.Prime := Fact.out
  have hγp : descendExtraGamma p N ∈ Gamma0 (N / p) := descendExtraGamma_mem_Gamma0 hp hpN hpsq
  have hδ : descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹ ∈ Gamma0 (N / p) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hγp hγ) (Subgroup.inv_mem _ hγp)
  obtain ⟨hA, hshift⟩ := descendExtraGamma_mul_mul_inv_isUnit_and_upperTriShift_eq hpN hpsq hc
  obtain ⟨α, hα, hd, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul_of_isUnit hA
    (intCast_mul_apply_one_zero_eq_zero_of_mem_Gamma0_div hpN hδ)
  have hidx := descendIndexShift_val_of_le_of_eq_zero hpsq hv hc
  refine ⟨α, hα, (intCast_apply_one_one_eq_of_mem_Gamma0_of_eq hδ hd).trans ?_, ?_⟩
  · have h : map (Int.castRingHom (ZMod (N / p)))
          (descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹)
        = map (Int.castRingHom (ZMod (N / p))) γ := by
      rw [map_mul, map_mul, map_inv,
        descendExtraGamma_map_intCast_zmod_div_eq_one hp hpN hpsq, inv_one, one_mul, mul_one]
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast] using
      congr_fun₂ (congrArg Subtype.val h) 1 1
  · have h := congrArg (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)) hmul
    simp only [map_mul, map_mapGL, hshift] at h
    rw [descendMatrix_of_le hv, descendMatrix_of_le hidx.ge, mul_assoc, ← map_mul,
      ← inv_mul_cancel_right (descendExtraGamma p N * γ) (descendExtraGamma p N), map_mul,
      map_mul, map_mul, ← mul_assoc, h, mul_assoc]

/-- **The descent family is permuted by `Γ₀(N / p)` when `p` exactly divides `N`.** For
`γ ∈ Γ₀(N / p)`, the product `descendMatrix p N v * γ` is an element of `Γ₀(N)` times the member
of the family at `descendIndexShift p N hpsq γ v`, a bijection of the index set by
`descendIndexShift_bijective`; and the `Γ₀(N)` witness has the lower-right entry of `γ` modulo
`N / p`. -/
theorem exists_mem_Gamma0_descendMatrix_mul_of_not_sq_dvd [Fact p.Prime] (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p))
    (v : Fin (descendMatrixCount p N)) :
    ∃ α : SL(2, ℤ), α ∈ Gamma0 N ∧ ((α 1 1 : ℤ) : ZMod (N / p)) = ((γ 1 1 : ℤ) : ZMod (N / p)) ∧
      descendMatrix p N v * mapGL ℝ γ
        = mapGL ℝ α * descendMatrix p N (descendIndexShift p N hpsq γ v) := by
  rcases lt_or_ge v.val p with hv | hv
  · by_cases h0 : (((γ 0 0 + (v : ℕ) * γ 1 0 : ℤ) : ZMod p)) = 0
    · exact exists_mem_Gamma0_descendMatrix_mul_of_eq_zero hpN hpsq hγ hv h0
    · exact exists_mem_Gamma0_descendMatrix_mul_of_isUnit hpN hpsq hγ hv
        (isUnit_iff_ne_zero.mpr h0)
  · by_cases hc : ((γ 1 0 : ℤ) : ZMod p) = 0
    · exact exists_mem_Gamma0_descendMatrix_mul_of_le_of_eq_zero hpN hpsq hγ hv hc
    · exact exists_mem_Gamma0_descendMatrix_mul_of_le_of_ne_zero hpN hpsq hγ hv hc

end TauCeti
