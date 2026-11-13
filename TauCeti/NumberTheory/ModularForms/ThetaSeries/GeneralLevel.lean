/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Character
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.BoundedAtCusp
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.LevelOne
public import TauCeti.NumberTheory.ModularForms.DiamondOperators
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.PositiveOdd.Slash
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.Degeneracy
import TauCeti.NumberTheory.ModularForms.TrivialNebentypus
import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# The Hecke–Schoeneberg theorem

For an even full lattice `L` of rank `2k` and level `N`, its theta series is a modular form
of weight `k` on `Γ₁(N)` with quadratic nebentypus `ZLattice.IsEven.thetaCharacter`. This file
extends the evaluated Gauss-sum transformation law to every matrix of `Γ₀(N)` and bundles the
result as `ZLattice.thetaFormOfLevel`. Membership in `TauCeti.modFormCharSpace` records the
nebentypus in the diamond-eigenspace convention, without introducing a new type of modular form.

The reduction to matrices with positive lower-left and positive odd upper-left entries uses
translation invariance and the character parity `χ(-1) = (-1)^k`. Holomorphy and boundedness
at all rational cusps are supplied by the analytic theory of theta series. The coefficients
are the representation numbers of `L`. Because `Θ_L(i∞) = 1`, `thetaFormOfLevel` is nonzero and is
never a cusp form; nonvanishing implies that its nebentypus is uniquely determined, and every
diamond operator `⟨d⟩` (as well as its zero-extended natural-number form `⟨n⟩`) acts on it with
eigenvalue `χ_L(d)` (resp. `χ_L(n)`).

Pulling a lattice back along a linear isometry preserves `thetaFormOfLevel`, and the theta form of
an orthogonal direct sum `L ⊕ M` is the product of the restrictions of `Θ_L` and `Θ_M` to their
common level `lcm (level L) (level M)`. When the theta character is trivial — in particular when
the signed discriminant `D_L` is a square — `Θ_L` is invariant under the full group `Γ₀(N)` and
descends to a modular form `ZLattice.thetaFormGamma0` on `Γ₀(N)`. When `L` is unimodular both
constructions agree with the level-one theta form, restricted to the congruence subgroup.

## Main definitions

* `ZLattice.thetaFormOfLevel`: the theta series of an even full lattice of rank `2k`, as a modular
  form of weight `k` on `Γ₁(level L)`.
* `ZLattice.thetaFormGamma0`: the descent to `Γ₀(level L)` when `thetaCharacter` is trivial.

## Main statements

* `ZLattice.IsEven.thetaSeries_slash_of_mem_Gamma0`: the Hecke–Schoeneberg transformation law on
  `Γ₀(level L)`.
* `ZLattice.thetaFormOfLevel_mem_modFormCharSpace`,
  `ZLattice.mem_modFormCharSpace_thetaFormOfLevel_iff`: `Θ_L` lies in the character space of `χ_L`,
  and of no other character.
* `ZLattice.diamondOp_thetaFormOfLevel`, `ZLattice.diamondOpNat_thetaFormOfLevel`,
  `ZLattice.diamondOpNat_thetaFormOfLevel_of_coprime`: the diamond eigenvalues
  `⟨d⟩ Θ_L = χ_L(d) Θ_L` and `⟨n⟩ Θ_L = χ_L(n) Θ_L`.
* `ZLattice.not_isCuspForm_thetaFormOfLevel`, `ZLattice.not_isCuspForm_thetaFormGamma0`: `Θ_L` is
  never a cusp form.
* `ZLattice.thetaFormOfLevel_comap`, `ZLattice.thetaFormOfLevel_orthSum`: invariance under linear
  isometries and multiplicativity on orthogonal direct sums.
* `ZLattice.IsEven.thetaSeries_slash_of_mem_Gamma0_of_isSquare`: trivial `Γ₀(level L)`-action when
  `signedDiscr L` is a square.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Chapter IX.
* W. Ebeling, *Lattices and Codes*, third edition, Chapter 3.
-/

public section

open Module Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ}

/-- **The Hecke–Schoeneberg transformation law.** The theta series of an even full lattice of
rank `2k` transforms under every matrix of `Γ₀(level L)` by its quadratic character evaluated
at the lower-right entry. -/
theorem IsEven.thetaSeries_slash_of_mem_Gamma0 (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 (level L)) :
    thetaSeries L ∣[(k : ℤ)] A =
      hL.thetaCharacter (hk.symm ▸ even_two_mul k) (A 1 1 : ℤ) • thetaSeries L := by
  borelize E
  apply TauCeti.ModularForm.slash_eq_smul_of_mem_Gamma0_of_pos_odd
    (by simpa using hL.thetaCharacter_neg_one (hk.symm ▸ even_two_mul k) hk)
    (hL.thetaSeries_slash_T _) ?_ hA
  intro B hB hc ha hao
  obtain ⟨a, haeq⟩ := Int.eq_ofNat_of_zero_le ha.le
  obtain ⟨c, hceq⟩ := Int.eq_ofNat_of_zero_le hc.le
  have haodd : Odd a := by rw [haeq] at hao; exact_mod_cast hao
  have hN : level L ∣ c := by
    have h := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hB
    rw [hceq] at h
    exact_mod_cast h
  exact hL.thetaSeries_slash_eq_thetaCharacter_smul_of_odd
    (hk.symm ▸ even_two_mul k) hk B haeq hceq haodd hN

/-- The theta series of an even full lattice of rank `2k`, as a modular form on
`Γ₁(level L)` of weight `k`. Its character-space membership is
`ZLattice.thetaFormOfLevel_mem_modFormCharSpace`. -/
noncomputable def thetaFormOfLevel (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    ModularForm ((CongruenceSubgroup.Gamma1 (level L)).map (mapGL ℝ)) k where
  toFun := thetaSeries L
  slash_action_eq' A hA := by
    obtain ⟨A, hA, rfl⟩ := hA
    rw [← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash,
      hL.thetaSeries_slash_of_mem_Gamma0 hk (CongruenceSubgroup.Gamma1_in_Gamma0 _ hA)]
    have hd := (CongruenceSubgroup.mem_Gamma1_iff.mp hA).2
    rw [hd, map_one, one_smul]
  holo' := mdifferentiable_thetaSeries L
  bdd_at_cusps' hc := hL.isBoundedAt_thetaSeries hk (hc.mono (Subgroup.map_le_range _ _))

/-- The underlying function of the general-level theta form is the lattice theta series. -/
@[simp]
theorem coe_thetaFormOfLevel (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    ⇑(thetaFormOfLevel hL hk) = thetaSeries L := (rfl)

/-- The general-level theta form lies in the character space of the quadratic theta character.
Equivalently, it satisfies the classical nebentypus law on `Γ₀(level L)`. -/
theorem thetaFormOfLevel_mem_modFormCharSpace (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    thetaFormOfLevel hL hk ∈
      TauCeti.modFormCharSpace k
        (MulChar.equivToUnitHom (hL.thetaCharacter (hk.symm ▸ even_two_mul k))) := by
  apply (TauCeti.mem_modFormCharSpace_iff_nebentypus _ _ _).mpr
  intro A
  simpa only [coe_thetaFormOfLevel, MulChar.coe_equivToUnitHom,
    MonoidHom.coe_toHomUnits, CongruenceSubgroup.Gamma0Map_apply, ModularForm.SL_slash,
    TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL] using
    hL.thetaSeries_slash_of_mem_Gamma0 hk A.property

/-- The coefficients of the theta form in `q = exp (2 π i τ)` are representation numbers. -/
theorem qExpansion_thetaFormOfLevel_coeff (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (m : ℕ) :
    (qExpansion 1 (thetaFormOfLevel hL hk)).coeff m = representationNumber L (2 * m) := by
  rw [coe_thetaFormOfLevel, hL.qExpansion_thetaSeries_coeff]

/-- The general-level theta form is nonzero. -/
@[simp]
theorem thetaFormOfLevel_ne_zero (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    thetaFormOfLevel hL hk ≠ 0 := fun h ↦
  thetaSeries_ne_zero_of_re_eq_zero L UpperHalfPlane.I_re (by
    rw [← coe_thetaFormOfLevel hL hk, h, FunLike.coe_zero]
    rfl)

/-- The general-level theta form is not a cusp form: its value at `∞` is `1`. -/
@[simp]
theorem not_isCuspForm_thetaFormOfLevel (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    ¬ ModularForm.IsCuspForm (thetaFormOfLevel hL hk) := by
  have : NeZero (level L) := ⟨hL.isIntegral.level_pos.ne'⟩
  exact not_isCuspForm_of_coe_eq_thetaSeries L (coe_thetaFormOfLevel hL hk)

/-- Every diamond operator `⟨d⟩` acts on `thetaFormOfLevel` with eigenvalue `χ_L(d)`. -/
@[simp]
theorem diamondOp_thetaFormOfLevel (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (d : (ZMod (level L))ˣ) :
    TauCeti.diamondOp k d (thetaFormOfLevel hL hk) =
      hL.thetaCharacter (hk.symm ▸ even_two_mul k) d • thetaFormOfLevel hL hk := by
  simpa only [MulChar.coe_equivToUnitHom] using
    TauCeti.diamondOp_apply_of_mem_modFormCharSpace (k := k)
      (MulChar.equivToUnitHom (hL.thetaCharacter (hk.symm ▸ even_two_mul k))) d
      (thetaFormOfLevel_mem_modFormCharSpace hL hk)

/-- The natural-indexed diamond operator `⟨n⟩` acts on `thetaFormOfLevel` with eigenvalue `χ_L(n)`
for every `n : ℕ`: both sides vanish when `n` is not coprime to `level L`. -/
@[simp]
theorem diamondOpNat_thetaFormOfLevel (hL : IsEven L) (hk : finrank ℝ E = 2 * k) (n : ℕ) :
    TauCeti.diamondOpNat k n (thetaFormOfLevel hL hk) =
      hL.thetaCharacter (hk.symm ▸ even_two_mul k) n • thetaFormOfLevel hL hk := by
  have : NeZero (level L) := ⟨hL.isIntegral.level_pos.ne'⟩
  by_cases hn : n.Coprime (level L)
  · rw [TauCeti.diamondOpNat_of_coprime _ hn, diamondOp_thetaFormOfLevel, ZMod.coe_unitOfCoprime]
  · have hnu : ¬ IsUnit (n : ZMod (level L)) := by rwa [ZMod.isUnit_iff_coprime]
    rw [TauCeti.diamondOpNat_of_not_coprime _ hn, LinearMap.zero_apply,
      MulChar.map_nonunit _ hnu, zero_smul]

/-- When `n` is coprime to `level L`, the diamond operator `⟨n⟩` acts on `thetaFormOfLevel` by the
Kronecker symbol `(signedDiscr L / n)`. -/
theorem diamondOpNat_thetaFormOfLevel_of_coprime (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    {n : ℕ} (hn : n.Coprime (level L)) :
    TauCeti.diamondOpNat k n (thetaFormOfLevel hL hk) =
      (TauCeti.kroneckerSym (signedDiscr L) n : ℂ) • thetaFormOfLevel hL hk := by
  rw [diamondOpNat_thetaFormOfLevel, ← Int.cast_natCast n,
    hL.thetaCharacter_intCast (hk.symm ▸ even_two_mul k) (Nat.isCoprime_iff_coprime.mpr hn)]

/-- The general-level theta form lies in `modFormCharSpace k χ` if and only if `χ` is the
unit-homomorphism of the lattice's theta character. -/
-- Not `@[simp]`: `TauCeti.mem_modFormCharSpace_iff` is `@[simp]` and already reduces the LHS.
theorem mem_modFormCharSpace_thetaFormOfLevel_iff (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    {χ : (ZMod (level L))ˣ →* ℂˣ} :
    thetaFormOfLevel hL hk ∈ TauCeti.modFormCharSpace k χ ↔
      χ = MulChar.equivToUnitHom (hL.thetaCharacter (hk.symm ▸ even_two_mul k)) :=
  ⟨fun h ↦ TauCeti.eq_of_mem_modFormCharSpace_of_ne_zero h
      (thetaFormOfLevel_mem_modFormCharSpace hL hk) (thetaFormOfLevel_ne_zero hL hk),
    fun h ↦ h ▸ thetaFormOfLevel_mem_modFormCharSpace hL hk⟩

/-- Restricted to `Γ₁(N)` for a multiple `N` of `level L`, `thetaFormOfLevel` has nebentypus
induced from `thetaCharacter` along `level L ∣ N`. -/
theorem restrict_thetaFormOfLevel_mem_modFormCharSpace (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    {N : ℕ} (h : level L ∣ N) :
    (thetaFormOfLevel hL hk).restrict (CongruenceSubgroup.Gamma1_map_le_Gamma1_map_of_dvd h) ∈
      TauCeti.modFormCharSpace k
        (MulChar.equivToUnitHom
          (DirichletCharacter.changeLevel h (hL.thetaCharacter (hk.symm ▸ even_two_mul k)))) := by
  rw [← MulChar.toUnitHom_eq, DirichletCharacter.changeLevel_toUnitHom, MulChar.toUnitHom_eq]
  exact TauCeti.ModularForm.restrict_mem_modFormCharSpace _ h
    (thetaFormOfLevel_mem_modFormCharSpace hL hk)

/-- Transported along a level equality `level L = N`, `thetaFormOfLevel` lies in the character
space of `thetaCharacter` cast to modulus `N`. -/
theorem mcast_thetaFormOfLevel_mem_modFormCharSpace (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    {N : ℕ} (hN : level L = N) :
    (thetaFormOfLevel hL hk).mcast rfl (by rw [hN]) ∈
      TauCeti.modFormCharSpace k
        (MulChar.equivToUnitHom (DirichletCharacter.changeLevel (dvd_of_eq hN)
          (hL.thetaCharacter (hk.symm ▸ even_two_mul k)))) := by
  subst hN
  have hm : (thetaFormOfLevel hL hk).mcast rfl rfl = thetaFormOfLevel hL hk :=
    ModularForm.ext fun _ ↦ rfl
  simpa only [hm, DirichletCharacter.changeLevel_self] using
    thetaFormOfLevel_mem_modFormCharSpace hL hk

/-- For an even unimodular lattice, the general-level construction is the restriction of the
level-one theta form. In this case `level L = 1` by `ZLattice.IsEven.level_eq_one_iff`. -/
theorem thetaFormOfLevel_eq_restrict_thetaForm (hL : IsEven L) (hU : IsUnimodular L)
    (hk : finrank ℝ E = 2 * k) :
    thetaFormOfLevel hL hk =
      (thetaForm hL hU hk).restrict (Subgroup.map_le_range _ _) := by
  apply ModularForm.ext
  exact congrFun (by rw [ModularForm.coe_restrict, coe_thetaForm, coe_thetaFormOfLevel])

/-! ### Functoriality and orthogonal direct sums -/

section Functoriality

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Pulling a lattice back along a linear isometry equivalence `e : F ≃ₗᵢ[ℝ] E` preserves its
general-level theta form. -/
theorem thetaFormOfLevel_comap (hL : IsEven L) (hk : finrank ℝ E = 2 * k) (e : F ≃ₗᵢ[ℝ] E)
    (hL' : IsEven (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) :=
      (isEven_comap_iff L e).mpr hL)
    (hk' : finrank ℝ F = 2 * k := e.toLinearEquiv.finrank_eq.trans hk) :
    (thetaFormOfLevel hL' hk').mcast rfl (by rw [level_comap]) = thetaFormOfLevel hL hk :=
  ModularForm.ext fun _ ↦ by simp

variable {M : Submodule ℤ F} [DiscreteTopology M] [IsZLattice ℝ M] {k' : ℕ}

/-- The general-level theta form of an orthogonal direct sum `L ⊕ M` of even full lattices is the
product of the restrictions of `Θ_L` and `Θ_M` to `Γ₁(lcm (level L) (level M))`, in weight
`k + k'`. -/
theorem thetaFormOfLevel_orthSum (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (hM : IsEven M) (hk' : finrank ℝ F = 2 * k') :
    thetaFormOfLevel (isEven_orthSum_iff.mpr ⟨hL, hM⟩)
        (by rw [(WithLp.linearEquiv 2 ℝ (E × F)).finrank_eq, finrank_prod, hk, hk', mul_add]) =
      ModularForm.mcast (Nat.cast_add k k').symm
        (((thetaFormOfLevel hL hk).restrict
          (CongruenceSubgroup.Gamma1_map_le_Gamma1_map_of_dvd
            (by rw [level_orthSum]; exact Nat.dvd_lcm_left _ _))).mul
          ((thetaFormOfLevel hM hk').restrict
            (CongruenceSubgroup.Gamma1_map_le_Gamma1_map_of_dvd
              (by rw [level_orthSum]; exact Nat.dvd_lcm_right _ _)))) :=
  ModularForm.ext fun _ ↦ by rw [coe_thetaFormOfLevel]; simp

end Functoriality

/-! ### Descent to `Γ₀(level L)` for trivial nebentypus -/

/-- When the theta character of `L` is trivial, its theta series is invariant under every matrix
of `Γ₀(level L)`. -/
theorem IsEven.thetaSeries_slash_of_mem_Gamma0_of_thetaCharacter_eq_one (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) (hχ : hL.thetaCharacter (hk.symm ▸ even_two_mul k) = 1)
    {A : SL(2, ℤ)} (hA : A ∈ CongruenceSubgroup.Gamma0 (level L)) :
    thetaSeries L ∣[(k : ℤ)] A = thetaSeries L := by
  have hu : IsUnit ((A 1 1 : ℤ) : ZMod (level L)) := by
    simpa only [CongruenceSubgroup.Gamma0Map_apply, MonoidHom.coe_toHomUnits] using
      ((CongruenceSubgroup.Gamma0Map (level L)).toHomUnits ⟨A, hA⟩).isUnit
  rw [hL.thetaSeries_slash_of_mem_Gamma0 hk hA, hχ, MulChar.one_apply hu, one_smul]

/-- When `signedDiscr L` is a square, the theta series of `L` is invariant under every matrix of
`Γ₀(level L)`. -/
theorem IsEven.thetaSeries_slash_of_mem_Gamma0_of_isSquare (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) (hD : IsSquare (signedDiscr L)) {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 (level L)) :
    thetaSeries L ∣[(k : ℤ)] A = thetaSeries L :=
  hL.thetaSeries_slash_of_mem_Gamma0_of_thetaCharacter_eq_one hk
    (hL.thetaCharacter_eq_one_of_isSquare _ hD) hA

/-- When `thetaCharacter` is trivial, the theta series of an even full lattice of rank `2k`
descends from `Γ₁(level L)` to a modular form of weight `k` on `Γ₀(level L)`. -/
noncomputable def thetaFormGamma0 (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (hχ : hL.thetaCharacter (hk.symm ▸ even_two_mul k) = 1) :
    ModularForm ((CongruenceSubgroup.Gamma0 (level L)).map (mapGL ℝ)) k :=
  have : NeZero (level L) := ⟨hL.isIntegral.level_pos.ne'⟩
  TauCeti.modFormCharSpaceOneEquiv (level L) k ⟨thetaFormOfLevel hL hk, by
    simpa only [hχ, ← MulChar.mulEquivToUnitHom_apply, map_one] using
      thetaFormOfLevel_mem_modFormCharSpace hL hk⟩

/-- `thetaFormGamma0` has `thetaSeries L` as its underlying function on `ℍ`. -/
@[simp]
theorem coe_thetaFormGamma0 (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (hχ : hL.thetaCharacter (hk.symm ▸ even_two_mul k) = 1) :
    ⇑(thetaFormGamma0 hL hk hχ) = thetaSeries L := by
  have : NeZero (level L) := ⟨hL.isIntegral.level_pos.ne'⟩
  exact (TauCeti.coe_modFormCharSpaceOneEquiv_apply _).trans (coe_thetaFormOfLevel hL hk)

/-- Restricting `thetaFormGamma0` from `Γ₀(level L)` back to `Γ₁(level L)` recovers
`thetaFormOfLevel`. -/
@[simp]
theorem restrict_thetaFormGamma0 (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (hχ : hL.thetaCharacter (hk.symm ▸ even_two_mul k) = 1) :
    (thetaFormGamma0 hL hk hχ).restrict
        (CongruenceSubgroup.Gamma1_map_le_Gamma0_map (level L)) =
      thetaFormOfLevel hL hk :=
  ModularForm.ext fun _ ↦ by simp [ModularForm.coe_restrict]

/-- The coefficients of `thetaFormGamma0` in `q = exp (2 π i τ)` are the representation numbers
`r_L(2m)`. -/
theorem qExpansion_thetaFormGamma0_coeff (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (hχ : hL.thetaCharacter (hk.symm ▸ even_two_mul k) = 1) (m : ℕ) :
    (qExpansion 1 (thetaFormGamma0 hL hk hχ)).coeff m = representationNumber L (2 * m) := by
  rw [coe_thetaFormGamma0, hL.qExpansion_thetaSeries_coeff]

/-- The `Γ₀(level L)` theta form is nonzero. -/
@[simp]
theorem thetaFormGamma0_ne_zero (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (hχ : hL.thetaCharacter (hk.symm ▸ even_two_mul k) = 1) :
    thetaFormGamma0 hL hk hχ ≠ 0 := fun h ↦
  thetaSeries_ne_zero_of_re_eq_zero L UpperHalfPlane.I_re (by
    rw [← coe_thetaFormGamma0 hL hk hχ, h, FunLike.coe_zero]
    rfl)

/-- The `Γ₀(level L)` theta form is not a cusp form: its value at `∞` is `1`. -/
@[simp]
theorem not_isCuspForm_thetaFormGamma0 (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (hχ : hL.thetaCharacter (hk.symm ▸ even_two_mul k) = 1) :
    ¬ ModularForm.IsCuspForm (thetaFormGamma0 hL hk hχ) := by
  have : NeZero (level L) := ⟨hL.isIntegral.level_pos.ne'⟩
  exact not_isCuspForm_of_coe_eq_thetaSeries L (coe_thetaFormGamma0 hL hk hχ)

/-- For an even unimodular lattice, `thetaFormGamma0` agrees with the restriction of the level-one
theta form `thetaForm`. -/
theorem thetaFormGamma0_eq_restrict_thetaForm (hL : IsEven L) (hU : IsUnimodular L)
    (hk : finrank ℝ E = 2 * k) :
    thetaFormGamma0 hL hk (hL.thetaCharacter_eq_one_of_isUnimodular _ hU) =
      (thetaForm hL hU hk).restrict (Subgroup.map_le_range _ _) :=
  ModularForm.ext fun _ ↦ by simp [ModularForm.coe_restrict]

end ZLattice
