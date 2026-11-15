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
public import TauCeti.NumberTheory.ModularForms.TrivialNebentypus
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.PositiveOdd.Slash
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The Hecke–Schoeneberg theorem

For an even full lattice `L` of rank `2k` and level `N`, its theta series is a modular form
of weight `k` on `Γ₁(N)` with quadratic nebentypus `ZLattice.IsEven.thetaCharacter`. This file
extends the evaluated Gauss-sum transformation law to every matrix of `Γ₀(N)` and bundles the
result as `ZLattice.thetaFormOfLevel`. Membership in `TauCeti.modFormCharSpace` records the
nebentypus in the diamond-eigenspace convention, without introducing a new type of modular form,
and `ZLattice.mcast_thetaFormOfLevel_mem_modFormCharSpace` transports this membership across a
computed level `level L = N` to any Dirichlet character modulo `N` agreeing on units with the
Kronecker symbol of `signedDiscr L`.

Because `thetaFormOfLevel` is nonzero, its nebentypus in `TauCeti.modFormCharSpace` is uniquely
determined. In particular, `Θ_L` is slash-invariant in weight `k` under all of `Γ₀(level L)` if
and only if its quadratic theta character is trivial — for instance whenever `signedDiscr L` is a
square (`ZLattice.IsEven.thetaCharacter_eq_one_of_isSquare`). In that case
`TauCeti.modFormCharSpaceOneEquiv` descends `thetaFormOfLevel` from `Γ₁(level L)` to a modular
form `ZLattice.thetaFormGamma0` on the bare congruence subgroup `Γ₀(level L)`.

The reduction to matrices with positive lower-left and positive odd upper-left entries uses
translation invariance and the character parity `χ(-1) = (-1)^k`. Holomorphy and boundedness
at all rational cusps are supplied by the analytic theory of theta series. The coefficients
are the representation numbers of `L`; when `L` is unimodular both bundled constructions agree with
the level-one theta form, viewed on the smaller subgroup. Because its constant term at `∞` is
`1`, the theta form is never a cusp form, and every diamond operator `⟨d⟩` acts on it by the
scalar `χ_L(d)`.

## Main definitions

* `ZLattice.thetaFormOfLevel`: the theta series of an even full lattice `L` of rank `2k`, as a
  weight-`k` modular form on `Γ₁(level L)`.
* `ZLattice.thetaFormGamma0`: when `hL.thetaCharacter _ = 1`, the descent of `thetaFormOfLevel`
  to a weight-`k` modular form on `Γ₀(level L)` via `TauCeti.modFormCharSpaceOneEquiv`.

## Main statements

* `ZLattice.IsEven.thetaSeries_slash_of_mem_Gamma0`,
  `ZLattice.IsEven.thetaSeries_slash_eq_kroneckerSym_smul_of_mem_Gamma0`: the Hecke–Schoeneberg
  transformation law on `Γ₀(level L)` in character and Kronecker-symbol form.
* `ZLattice.thetaFormOfLevel_mem_modFormCharSpace`,
  `ZLattice.thetaFormOfLevel_mem_modFormCharSpace_iff`,
  `ZLattice.mcast_thetaFormOfLevel_mem_modFormCharSpace`: membership of `thetaFormOfLevel` (and
  its cast along `level L = N`) in `TauCeti.modFormCharSpace`, and uniqueness of its nebentypus.
* `ZLattice.diamondOp_thetaFormOfLevel`, `ZLattice.diamondOpNat_thetaFormOfLevel`: diamond-operator
  action on `thetaFormOfLevel`.
* `ZLattice.IsEven.thetaSeries_slash_of_mem_Gamma0_eq_self_iff`: `Θ_L` is `Γ₀(level L)`-invariant
  in weight `k` if and only if `χ_L = 1`.
* `ZLattice.coe_thetaFormGamma0`, `ZLattice.restrict_thetaFormGamma0`,
  `ZLattice.modFormCharSpaceOneEquiv_symm_thetaFormGamma0`,
  `ZLattice.qExpansion_thetaFormGamma0_coeff`, `ZLattice.thetaFormGamma0_ne_zero`,
  `ZLattice.not_isCuspForm_thetaFormGamma0`, `ZLattice.thetaFormGamma0_eq_restrict_thetaForm`:
  coercion, compatibility with `thetaFormOfLevel` and `ZLattice.thetaForm`, Fourier coefficients,
  nonvanishing, and noncuspidality for `thetaFormGamma0`.

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
      hL.thetaCharacter ⟨k, by omega⟩ (A 1 1 : ℤ) • thetaSeries L := by
  borelize E
  apply TauCeti.ModularForm.slash_eq_smul_of_mem_Gamma0_of_pos_odd
    (by simpa using hL.thetaCharacter_neg_one ⟨k, by omega⟩ hk)
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
    ⟨k, by omega⟩ hk B haeq hceq haodd hN

/-- **Kronecker-symbol form of the Hecke–Schoeneberg transformation law.** Since the lower-right
entry of any matrix in `Γ₀(level L)` is coprime to `level L`, the transformation scalar equals the
Kronecker symbol `(signedDiscr L / A 1 1)`. -/
theorem IsEven.thetaSeries_slash_eq_kroneckerSym_smul_of_mem_Gamma0 (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 (level L)) :
    thetaSeries L ∣[(k : ℤ)] A =
      (TauCeti.kroneckerSym (signedDiscr L) (A 1 1) : ℂ) • thetaSeries L := by
  rw [hL.thetaSeries_slash_of_mem_Gamma0 hk hA,
    hL.thetaCharacter_intCast ⟨k, by omega⟩
      (CongruenceSubgroup.isCoprime_apply_one_one_of_mem_Gamma0 hA)]

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
      TauCeti.modFormCharSpace k (MulChar.equivToUnitHom (hL.thetaCharacter ⟨k, by omega⟩)) := by
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
    thetaFormOfLevel hL hk ≠ 0 :=
  ne_zero_of_coe_eq_thetaSeries L (coe_thetaFormOfLevel hL hk)

/-- The general-level theta form is not a cusp form: its constant term at `∞` is `1`. -/
@[simp]
theorem not_isCuspForm_thetaFormOfLevel (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    ¬ ModularForm.IsCuspForm (thetaFormOfLevel hL hk) := by
  have : NeZero (level L) := ⟨hL.isIntegral.level_pos.ne'⟩
  exact not_isCuspForm_of_coe_eq_thetaSeries L (coe_thetaFormOfLevel hL hk)

/-- Every diamond operator `⟨d⟩` acts on the general-level theta form by the eigenvalue
`χ_L(d)`, where `χ_L` is the quadratic theta character of `L`. -/
@[simp]
theorem diamondOp_thetaFormOfLevel (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (d : (ZMod (level L))ˣ) :
    TauCeti.diamondOp (k : ℤ) d (thetaFormOfLevel hL hk) =
      (hL.thetaCharacter ⟨k, by omega⟩ (d : ZMod (level L)) : ℂ) •
        thetaFormOfLevel hL hk := by
  simpa only [MulChar.coe_equivToUnitHom] using
    TauCeti.diamondOp_apply_of_mem_modFormCharSpace (k : ℤ)
      (MulChar.equivToUnitHom (hL.thetaCharacter ⟨k, by omega⟩)) d
      (thetaFormOfLevel_mem_modFormCharSpace hL hk)

/-- Every natural-number diamond operator `⟨n⟩` acts on the general-level theta form by the
eigenvalue `χ_L(n)` (which is `0` when `n` is not coprime to `level L`). -/
@[simp]
theorem diamondOpNat_thetaFormOfLevel (hL : IsEven L) (hk : finrank ℝ E = 2 * k) (n : ℕ) :
    TauCeti.diamondOpNat (N := level L) (k : ℤ) n (thetaFormOfLevel hL hk) =
      (hL.thetaCharacter ⟨k, by omega⟩ (n : ZMod (level L)) : ℂ) •
        thetaFormOfLevel hL hk := by
  rw [TauCeti.diamondOpNat_apply_of_mem_modFormCharSpace _ _ n
    (thetaFormOfLevel_mem_modFormCharSpace hL hk)]
  split_ifs with hn
  · simp only [MulChar.coe_equivToUnitHom, ZMod.coe_unitOfCoprime]
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime]), zero_smul]

/-- For an even unimodular lattice, the general-level construction is the restriction of the
level-one theta form. In this case `level L = 1` by `ZLattice.IsEven.level_eq_one_iff`. -/
theorem thetaFormOfLevel_eq_restrict_thetaForm (hL : IsEven L) (hU : IsUnimodular L)
    (hk : finrank ℝ E = 2 * k) :
    thetaFormOfLevel hL hk =
      (thetaForm hL hU hk).restrict (Subgroup.map_le_range _ _) := by
  apply ModularForm.ext
  exact congrFun (by rw [ModularForm.coe_restrict, coe_thetaForm, coe_thetaFormOfLevel])

/-- Transporting `thetaFormOfLevel` along a computed level `level L = N` lands in the character
space of any Dirichlet character modulo `N` whose values on integers coprime to `N` agree with the
Kronecker symbol of `signedDiscr L`. -/
theorem mcast_thetaFormOfLevel_mem_modFormCharSpace (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    {N : ℕ} (hN : level L = N)
    {hΓ : (CongruenceSubgroup.Gamma1 N).map (mapGL ℝ) =
      (CongruenceSubgroup.Gamma1 (level L)).map (mapGL ℝ)}
    {χ : DirichletCharacter ℂ N}
    (hχ : ∀ a : ℤ, IsCoprime a N → χ a = (TauCeti.kroneckerSym (signedDiscr L) a : ℂ)) :
    (thetaFormOfLevel hL hk).mcast rfl hΓ ∈
      TauCeti.modFormCharSpace k (MulChar.equivToUnitHom χ) := by
  apply (TauCeti.mem_modFormCharSpace_iff_nebentypus _ _ _).mpr
  intro A
  have hA : (A : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 (level L) := hN ▸ A.property
  have haN : IsCoprime ((A : SL(2, ℤ)) 1 1) N :=
    CongruenceSubgroup.isCoprime_apply_one_one_of_mem_Gamma0 A.property
  simpa only [ModularForm.coe_mcast, coe_thetaFormOfLevel, MulChar.coe_equivToUnitHom,
    MonoidHom.coe_toHomUnits, CongruenceSubgroup.Gamma0Map_apply, ModularForm.SL_slash,
    TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← hχ _ haN] using
    hL.thetaSeries_slash_eq_kroneckerSym_smul_of_mem_Gamma0 hk hA

/-! ### Uniqueness of the nebentypus and trivial-character `Γ₀(level L)` forms -/

/-- Because `thetaFormOfLevel` is nonzero, its nebentypus in `TauCeti.modFormCharSpace` is
uniquely determined and equals `MulChar.equivToUnitHom` of `ZLattice.IsEven.thetaCharacter`. -/
theorem thetaFormOfLevel_mem_modFormCharSpace_iff (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (χ : (ZMod (level L))ˣ →* ℂˣ) :
    thetaFormOfLevel hL hk ∈ TauCeti.modFormCharSpace k χ ↔
      χ = MulChar.equivToUnitHom (hL.thetaCharacter ⟨k, by omega⟩) :=
  ⟨fun h ↦ TauCeti.eq_of_mem_modFormCharSpace_of_ne_zero h
    (thetaFormOfLevel_mem_modFormCharSpace hL hk) (thetaFormOfLevel_ne_zero hL hk),
    fun h ↦ h ▸ thetaFormOfLevel_mem_modFormCharSpace hL hk⟩

/-- For a Dirichlet character `ψ` modulo `level L`, the general-level theta form lies in the
`ψ`-character space if and only if `ψ` is the lattice's quadratic theta character. -/
theorem thetaFormOfLevel_mem_modFormCharSpace_equivToUnitHom_iff (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) (ψ : DirichletCharacter ℂ (level L)) :
    thetaFormOfLevel hL hk ∈ TauCeti.modFormCharSpace k (MulChar.equivToUnitHom ψ) ↔
      ψ = hL.thetaCharacter ⟨k, by omega⟩ := by
  rw [thetaFormOfLevel_mem_modFormCharSpace_iff, MulChar.equivToUnitHom.apply_eq_iff_eq]

/-- The general-level theta form has trivial nebentypus if and only if the lattice's quadratic
theta character is `1`. -/
theorem thetaFormOfLevel_mem_modFormCharSpace_one_iff (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) :
    thetaFormOfLevel hL hk ∈
        TauCeti.modFormCharSpace k (1 : (ZMod (level L))ˣ →* ℂˣ) ↔
      hL.thetaCharacter ⟨k, by omega⟩ = 1 := by
  rw [← MulChar.mulEquivToUnitHom.map_one, MulChar.mulEquivToUnitHom_apply,
    thetaFormOfLevel_mem_modFormCharSpace_equivToUnitHom_iff, eq_comm]

/-- The theta series of an even full lattice of rank `2k` is slash-invariant in weight `k` under
all of `Γ₀(level L)` if and only if its quadratic theta character is trivial. -/
theorem IsEven.thetaSeries_slash_of_mem_Gamma0_eq_self_iff (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) :
    (∀ A ∈ CongruenceSubgroup.Gamma0 (level L),
        thetaSeries L ∣[(k : ℤ)] A = thetaSeries L) ↔
      hL.thetaCharacter ⟨k, by omega⟩ = 1 := by
  rw [← thetaFormOfLevel_mem_modFormCharSpace_one_iff hL hk, TauCeti.mem_modFormCharSpace_one_iff]
  refine ⟨fun h γ hγ ↦ ?_, fun h A hA ↦ ?_⟩
  · obtain ⟨A, hA, rfl⟩ := hγ
    simpa only [coe_thetaFormOfLevel, ModularForm.SL_slash,
      TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL] using h A hA
  · simpa only [coe_thetaFormOfLevel, ModularForm.SL_slash,
      TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL] using
      h (mapGL ℝ A) (Subgroup.mem_map_of_mem _ hA)

/-- When the quadratic theta character of an even full lattice of rank `2k` is trivial, its theta
series is invariant in weight `k` under every matrix of `Γ₀(level L)`. -/
theorem IsEven.thetaSeries_slash_of_mem_Gamma0_of_thetaCharacter_eq_one (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) (hχ : hL.thetaCharacter ⟨k, by omega⟩ = 1) {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 (level L)) :
    thetaSeries L ∣[(k : ℤ)] A = thetaSeries L :=
  (hL.thetaSeries_slash_of_mem_Gamma0_eq_self_iff hk).mpr hχ A hA

/-- When the signed discriminant of an even full lattice of rank `2k` is a square, its theta
series is invariant in weight `k` under every matrix of `Γ₀(level L)`. -/
theorem IsEven.thetaSeries_slash_of_mem_Gamma0_of_isSquare (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) (hD : IsSquare (signedDiscr L)) {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 (level L)) :
    thetaSeries L ∣[(k : ℤ)] A = thetaSeries L :=
  hL.thetaSeries_slash_of_mem_Gamma0_of_thetaCharacter_eq_one hk
    (hL.thetaCharacter_eq_one_of_isSquare ⟨k, by omega⟩ hD) hA

/-- **The `Γ₀` theta form of an even lattice with trivial theta character.** When the quadratic
theta character of an even full lattice `L` of rank `2k` is trivial — in particular when
`signedDiscr L` is a square (`ZLattice.IsEven.thetaCharacter_eq_one_of_isSquare`) — its theta
series descends from `Γ₁(level L)` to a modular form of weight `k` on `Γ₀(level L)` via
`TauCeti.modFormCharSpaceOneEquiv`. -/
noncomputable def thetaFormGamma0 (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (hχ : hL.thetaCharacter ⟨k, by omega⟩ = 1) :
    ModularForm ((CongruenceSubgroup.Gamma0 (level L)).map (mapGL ℝ)) k :=
  have : NeZero (level L) := ⟨hL.isIntegral.level_pos.ne'⟩
  TauCeti.modFormCharSpaceOneEquiv (level L) k
    ⟨thetaFormOfLevel hL hk, (thetaFormOfLevel_mem_modFormCharSpace_one_iff hL hk).mpr hχ⟩

/-- The underlying function of the `Γ₀` theta form is the lattice theta series. -/
@[simp]
theorem coe_thetaFormGamma0 (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (hχ : hL.thetaCharacter ⟨k, by omega⟩ = 1) :
    ⇑(thetaFormGamma0 hL hk hχ) = thetaSeries L := by
  have : NeZero (level L) := ⟨hL.isIntegral.level_pos.ne'⟩
  exact (TauCeti.coe_modFormCharSpaceOneEquiv_apply _).trans (coe_thetaFormOfLevel hL hk)

/-- Restricting `thetaFormGamma0` from `Γ₀(level L)` to `Γ₁(level L)` recovers
`thetaFormOfLevel`. -/
@[simp]
theorem restrict_thetaFormGamma0 (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (hχ : hL.thetaCharacter ⟨k, by omega⟩ = 1) :
    (thetaFormGamma0 hL hk hχ).restrict
        (CongruenceSubgroup.Gamma1_map_le_Gamma0_map (level L)) =
      thetaFormOfLevel hL hk := by
  ext τ
  simp

/-- The inverse of `TauCeti.modFormCharSpaceOneEquiv` sends `thetaFormGamma0` to
`thetaFormOfLevel` in the trivial-character subspace. -/
@[simp]
theorem modFormCharSpaceOneEquiv_symm_thetaFormGamma0 [NeZero (level L)] (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) (hχ : hL.thetaCharacter ⟨k, by omega⟩ = 1) :
    (TauCeti.modFormCharSpaceOneEquiv (level L) k).symm (thetaFormGamma0 hL hk hχ) =
      ⟨thetaFormOfLevel hL hk, (thetaFormOfLevel_mem_modFormCharSpace_one_iff hL hk).mpr hχ⟩ := by
  ext1
  rw [TauCeti.coe_modFormCharSpaceOneEquiv_symm_apply, restrict_thetaFormGamma0]

/-- The coefficients of the `Γ₀` theta form in `q = exp (2 π i τ)` are representation numbers. -/
theorem qExpansion_thetaFormGamma0_coeff (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (hχ : hL.thetaCharacter ⟨k, by omega⟩ = 1) (m : ℕ) :
    (qExpansion 1 (thetaFormGamma0 hL hk hχ)).coeff m = representationNumber L (2 * m) := by
  rw [coe_thetaFormGamma0, hL.qExpansion_thetaSeries_coeff]

/-- The `Γ₀` theta form is nonzero. -/
@[simp]
theorem thetaFormGamma0_ne_zero (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (hχ : hL.thetaCharacter ⟨k, by omega⟩ = 1) :
    thetaFormGamma0 hL hk hχ ≠ 0 :=
  ne_zero_of_coe_eq_thetaSeries L (coe_thetaFormGamma0 hL hk hχ)

/-- The `Γ₀` theta form is not a cusp form: its constant term at `∞` is `1`. -/
@[simp]
theorem not_isCuspForm_thetaFormGamma0 (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (hχ : hL.thetaCharacter ⟨k, by omega⟩ = 1) :
    ¬ ModularForm.IsCuspForm (thetaFormGamma0 hL hk hχ) := by
  have : NeZero (level L) := ⟨hL.isIntegral.level_pos.ne'⟩
  exact not_isCuspForm_of_coe_eq_thetaSeries L (coe_thetaFormGamma0 hL hk hχ)

/-- For an even unimodular lattice, `thetaFormGamma0` is the restriction of the level-one theta
form `ZLattice.thetaForm`. -/
theorem thetaFormGamma0_eq_restrict_thetaForm (hL : IsEven L) (hU : IsUnimodular L)
    (hk : finrank ℝ E = 2 * k) :
    thetaFormGamma0 hL hk (hL.thetaCharacter_eq_one_of_isUnimodular _ hU) =
      (thetaForm hL hU hk).restrict (Subgroup.map_le_range _ _) := by
  ext τ
  simp

end ZLattice
