/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Kummer.Character
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia
public import TauCeti.NumberTheory.LocalField.Uniformizer
public import TauCeti.NumberTheory.LocalField.UnitsDecomposition
public import TauCeti.RingTheory.RootsOfUnity.TateModule

/-!
# The tame character of the inertia group

Let `K` be a nonarchimedean local field with residue characteristic `p` and residue field of order
`q`, let `K^{alg}` be its algebraic closure, and let `I_K ≤ G_K = Gal(K^{alg}/K)` be the inertia
subgroup, the automorphisms fixing the maximal unramified extension `K^{ur}`. For `m` prime to `p`,
every `m`-th root of unity of `K^{alg}` lies in `K^{ur}`, since `m` divides `q ^ φ(m) − 1`; so
inertia fixes it. Hence for `a ∈ Kˣ` and any `α ∈ K^{alg}` with `α ^ m = a`,

`σ ↦ σ(α) / α`

is a homomorphism `I_K → μ_m(K^{alg})` that does not depend on the choice of the root `α`: two
roots differ by an `m`-th root of unity, which `σ` fixes. These characters are compatible along
the power maps `μ_m → μ_n`, `ζ ↦ ζ ^ (m / n)`, for `n ∣ m`, because `α ^ (m / n)` is an `n`-th
root of `a`, and they are locally constant for the Krull topology. Together they form the
continuous homomorphism

`tameKummerCharacter K a : I_K →ₜ* ℤ̂^{(p')}(1) = lim_{p ∤ m} μ_m(K^{alg})`

into the prime-to-`p` Tate module `TauCeti.PrimeToPTateModule`. It is multiplicative in `a` and
trivial on the units `𝒪[K]ˣ`: a unit is a `(q − 1)`-st root of unity times a principal unit, the
former has roots of unity of order prime to `p` as its `m`-th roots, and the latter is an `m`-th
power in `K`. So all uniformizers `π` give the same character, the **tame character**

`inertiaTameCharacter K : I_K →ₜ* ℤ̂^{(p')}(1)`, `σ ↦ (σ(π^{1/m})/π^{1/m})_m`,

independent of the uniformizer and of the chosen roots. Classically it is surjective with kernel
the wild inertia group `P_K`, so that it identifies the tame inertia group `I_K/P_K` with
`ℤ̂^{(p')}(1)`; this file constructs the character, and does not prove those two facts.

## Main definitions

* `TauCeti.inertiaKummerCharacter K m hm a`: for `m` prime to `p` and `a ∈ Kˣ`, the character
  `σ ↦ σ(α)/α` of `I_K` with values in `μ_m(K^{alg})`, for any `m`-th root `α` of `a`.
* `TauCeti.tameKummerCharacter K a`: the compatible family of these characters, a continuous
  homomorphism `I_K →ₜ* PrimeToPTateModule p K^{alg}`.
* `TauCeti.inertiaTameCharacter K`: the tame Kummer character of a uniformizer.

## Main results

* `TauCeti.coe_inertiaKummerCharacter_apply`: the value at `σ` is `σ(α)/α` for **every** `m`-th
  root `α` of `a`.
* `TauCeti.inertiaKummerCharacter_eq_one_iff`: the character is trivial exactly when inertia fixes
  the roots of `X ^ m − a`.
* `TauCeti.inertiaKummerCharacter_mul`, `TauCeti.tameKummerCharacter_mul`: the characters are
  multiplicative in `a`.
* `TauCeti.inertiaKummerCharacter_pow_div`: the compatibility along the power maps.
* `TauCeti.inertiaKummerCharacter_eq_one_of_mem_unitFiltration_zero`,
  `TauCeti.tameKummerCharacter_eq_one_of_mem_unitFiltration_zero`: the characters of a unit are
  trivial.
* `TauCeti.inertiaTameCharacter_eq_tameKummerCharacter`,
  `TauCeti.coe_proj_inertiaTameCharacter_apply`: the tame character is the tame Kummer character
  of any uniformizer `π`, with level-`m` component `σ(α)/α` for any root `α` of `X ^ m − π`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Proposition 7 and its corollaries.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (7.5.2).
-/

public section

noncomputable section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-! ### The Kummer character at a finite level -/

section Level

variable {K}

/-- On the inertia subgroup, `σ(α)/α` depends only on `α ^ m`, for `m` prime to `p`: two roots of
the same element differ by an `m`-th root of unity, which inertia fixes. -/
private theorem apply_div_eq_apply_div {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) {m : ℕ} (hm : m.Coprime (ringChar 𝓀[K]))
    {α β : AlgebraicClosure K} (hα : α ≠ 0) (hαβ : α ^ m = β ^ m) : σ α / α = σ β / β := by
  have hβ : β ≠ 0 := by
    rintro rfl
    exact hα (pow_eq_zero_iff (ne_zero_of_coprime_ringChar hm) |>.1
      (hαβ.trans (zero_pow (ne_zero_of_coprime_ringChar hm))))
  have hζ : (β / α) ^ m = 1 := by rw [div_pow, ← hαβ, div_self (pow_ne_zero _ hα)]
  have hfix := apply_eq_self_of_mem_inertiaSubgroup_of_pow_eq_one hσ hm hζ
  have hσα : σ α ≠ 0 := by simpa using hα
  rw [map_div₀, div_eq_div_iff hσα hα] at hfix
  rw [div_eq_div_iff hα hβ]
  linear_combination -hfix

/-- For `m` prime to `p`, the `m`-th roots of an element of `Kˣ` are nonzero. -/
private theorem ne_zero_of_pow_eq_algebraMap {m : ℕ} (hm : m.Coprime (ringChar 𝓀[K])) {a : Kˣ}
    {α : AlgebraicClosure K} (hα : α ^ m = algebraMap K (AlgebraicClosure K) a) : α ≠ 0 :=
  ne_zero_pow (ne_zero_of_coprime_ringChar hm) (by simp [hα])

variable (K) in
/-- A chosen `m`-th root of `a` in the algebraic closure; the Kummer character does not depend on
the choice. -/
private def root (m : ℕ) (hm : m.Coprime (ringChar 𝓀[K])) (a : Kˣ) : AlgebraicClosure K :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) a)
    (Nat.pos_of_ne_zero (ne_zero_of_coprime_ringChar hm))).choose

private theorem root_pow {m : ℕ} (hm : m.Coprime (ringChar 𝓀[K])) (a : Kˣ) :
    root K m hm a ^ m = algebraMap K (AlgebraicClosure K) a :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) a)
    (Nat.pos_of_ne_zero (ne_zero_of_coprime_ringChar hm))).choose_spec

variable (K) in
/-- The quotient `σ(α)/α` for the chosen root `α` of `X ^ m − a`. -/
private def kummerRatio (m : ℕ) (hm : m.Coprime (ringChar 𝓀[K])) (a : Kˣ)
    (σ : Gal(AlgebraicClosure K/K)) : AlgebraicClosure K :=
  σ (root K m hm a) / root K m hm a

/-- On inertia, `kummerRatio` may be computed with any root of `X ^ m − a`. -/
private theorem kummerRatio_eq {m : ℕ} (hm : m.Coprime (ringChar 𝓀[K])) {a : Kˣ}
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K) {α : AlgebraicClosure K}
    (hα : α ^ m = algebraMap K (AlgebraicClosure K) a) :
    kummerRatio K m hm a σ = σ α / α :=
  apply_div_eq_apply_div hσ hm
    (ne_zero_of_pow_eq_algebraMap hm (root_pow hm a))
    ((root_pow hm a).trans hα.symm)

private theorem kummerRatio_one {m : ℕ} (hm : m.Coprime (ringChar 𝓀[K])) (a : Kˣ) :
    kummerRatio K m hm a 1 = 1 :=
  div_self (ne_zero_of_pow_eq_algebraMap hm (root_pow hm a))

private theorem kummerRatio_mul {m : ℕ} (hm : m.Coprime (ringChar 𝓀[K])) (a : Kˣ)
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K) (τ : Gal(AlgebraicClosure K/K)) :
    kummerRatio K m hm a (σ * τ) = kummerRatio K m hm a σ * kummerRatio K m hm a τ := by
  have hα := ne_zero_of_pow_eq_algebraMap hm (root_pow hm a)
  -- `σ(τα)/(τα) = σ(α)/α`, as `τα` is another root of `X ^ m − a`.
  have hτα : (τ (root K m hm a)) ^ m = algebraMap K (AlgebraicClosure K) a := by
    rw [← map_pow, root_pow, AlgEquiv.commutes]
  have h := kummerRatio_eq hm hσ hτα
  have hτα0 : τ (root K m hm a) ≠ 0 := by simpa using hα
  simp only [kummerRatio, AlgEquiv.mul_apply] at h ⊢
  rw [h]
  field_simp

variable (K) in
/-- **The Kummer character of `a` on inertia at level `m`.** For `m` prime to the residue
characteristic `p` of `K` and `a ∈ Kˣ`, the character `σ ↦ σ(α)/α` of the inertia subgroup with
values in the `m`-th roots of unity of `K^{alg}`, where `α` is any root of `X ^ m − a`
(`TauCeti.coe_inertiaKummerCharacter_apply`). -/
def inertiaKummerCharacter (m : ℕ) (hm : m.Coprime (ringChar 𝓀[K])) (a : Kˣ) :
    inertiaSubgroup K →* rootsOfUnity m (AlgebraicClosure K) :=
  haveI : NeZero m := ⟨ne_zero_of_coprime_ringChar hm⟩
  { toFun σ := rootsOfUnity.mkOfPowEq (kummerRatio K m hm a σ.1)
      (apply_div_pow_eq_one (ne_zero_of_pow_eq_algebraMap hm (root_pow hm a))
        (by rw [root_pow]; exact AlgEquiv.commutes σ.1 _))
    map_one' := rootsOfUnity.coe_injective (kummerRatio_one hm a)
    map_mul' σ τ := rootsOfUnity.coe_injective (kummerRatio_mul hm a σ.2 τ.1) }

variable {m : ℕ} {hm : m.Coprime (ringChar 𝓀[K])} {a : Kˣ}

/-- **The Kummer character is `σ(α)/α` for every root `α` of `X ^ m − a`**: the value does not
depend on the choice of the root. -/
theorem coe_inertiaKummerCharacter_apply {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) {α : AlgebraicClosure K}
    (hα : α ^ m = algebraMap K (AlgebraicClosure K) a) :
    ((inertiaKummerCharacter K m hm a ⟨σ, hσ⟩ : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
      σ α / α :=
  kummerRatio_eq hm hσ hα

/-- An element of inertia moves every root `α` of `X ^ m − a` by the value of the Kummer
character: `σ(α) = χ_a(σ) · α`. -/
theorem apply_eq_inertiaKummerCharacter_mul {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) {α : AlgebraicClosure K}
    (hα : α ^ m = algebraMap K (AlgebraicClosure K) a) :
    σ α = ((inertiaKummerCharacter K m hm a ⟨σ, hσ⟩ : (AlgebraicClosure K)ˣ) :
      AlgebraicClosure K) * α := by
  rw [coe_inertiaKummerCharacter_apply hσ hα,
    div_mul_cancel₀ _ (ne_zero_of_pow_eq_algebraMap hm hα)]

/-- The Kummer character is trivial at `σ` exactly when `σ` fixes a root of `X ^ m − a`, and then
it fixes all of them. -/
theorem inertiaKummerCharacter_apply_eq_one_iff {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) {α : AlgebraicClosure K}
    (hα : α ^ m = algebraMap K (AlgebraicClosure K) a) :
    inertiaKummerCharacter K m hm a ⟨σ, hσ⟩ = 1 ↔ σ α = α := by
  rw [← rootsOfUnity.coe_injective.eq_iff, coe_inertiaKummerCharacter_apply hσ hα,
    OneMemClass.coe_one, Units.val_one,
    div_eq_one_iff_eq (ne_zero_of_pow_eq_algebraMap hm hα)]

/-- The Kummer character is trivial exactly when inertia fixes a root of `X ^ m − a`, and then it
fixes all of them. -/
theorem inertiaKummerCharacter_eq_one_iff {α : AlgebraicClosure K}
    (hα : α ^ m = algebraMap K (AlgebraicClosure K) a) :
    inertiaKummerCharacter K m hm a = 1 ↔
      ∀ σ : Gal(AlgebraicClosure K/K), σ ∈ inertiaSubgroup K → σ α = α := by
  refine ⟨fun h σ hσ ↦ (inertiaKummerCharacter_apply_eq_one_iff (hm := hm) hσ hα).1 ?_,
    fun h ↦ ?_⟩
  · rw [h, MonoidHom.one_apply]
  · ext ⟨σ, hσ⟩ : 1
    exact (inertiaKummerCharacter_apply_eq_one_iff (σ := σ) hσ hα).2 (h σ hσ)

/-- The Kummer character is multiplicative in `a`: a product of roots is a root of the product. -/
@[simp]
theorem inertiaKummerCharacter_mul (a b : Kˣ) :
    inertiaKummerCharacter K m hm (a * b) =
      inertiaKummerCharacter K m hm a * inertiaKummerCharacter K m hm b := by
  ext ⟨σ, hσ⟩
  -- `Field.absoluteGaloisGroup K` is a type synonym for `Gal(AlgebraicClosure K/K)`; view `σ` in
  -- the latter so that the `AlgEquiv` lemmas apply to it.
  revert σ
  intro (σ : Gal(AlgebraicClosure K/K)) hσ
  have hab : (root K m hm a * root K m hm b) ^ m =
      algebraMap K (AlgebraicClosure K) (a * b : Kˣ) := by
    rw [mul_pow, root_pow, root_pow, Units.val_mul, map_mul]
  rw [MonoidHom.mul_apply, Subgroup.coe_mul, Units.val_mul,
    coe_inertiaKummerCharacter_apply (σ := σ) hσ hab,
    coe_inertiaKummerCharacter_apply (σ := σ) hσ (root_pow hm a),
    coe_inertiaKummerCharacter_apply (σ := σ) hσ (root_pow hm b), map_mul, mul_div_mul_comm]

/-- The Kummer character of one is trivial. -/
@[simp]
theorem inertiaKummerCharacter_one :
    inertiaKummerCharacter K m hm (1 : Kˣ) = 1 := by
  refine (inertiaKummerCharacter_eq_one_iff (a := (1 : Kˣ))
    (α := (1 : AlgebraicClosure K)) (by simp)).2 ?_
  simp

/-- The Kummer character of an inverse is the inverse Kummer character. -/
@[simp]
theorem inertiaKummerCharacter_inv (a : Kˣ) :
    inertiaKummerCharacter K m hm a⁻¹ = (inertiaKummerCharacter K m hm a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← inertiaKummerCharacter_mul, inv_mul_cancel, inertiaKummerCharacter_one]

/-- The Kummer character of a natural power is the corresponding power of the Kummer
character. -/
@[simp]
theorem inertiaKummerCharacter_pow (a : Kˣ) (n : ℕ) :
    inertiaKummerCharacter K m hm (a ^ n) = (inertiaKummerCharacter K m hm a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- **Compatibility along the power maps.** For `n ∣ m`, the level-`m` Kummer character raised to
the power `m / n` is the level-`n` Kummer character, since `α ^ (m / n)` is an `n`-th root of `a`
whenever `α` is an `m`-th root. -/
theorem inertiaKummerCharacter_pow_div {n : ℕ} (hn : n.Coprime (ringChar 𝓀[K])) (hnm : n ∣ m)
    (σ : inertiaSubgroup K) :
    (inertiaKummerCharacter K m hm a σ : (AlgebraicClosure K)ˣ) ^ (m / n) =
      inertiaKummerCharacter K n hn a σ := by
  obtain ⟨σ, hσ⟩ := σ
  -- `Field.absoluteGaloisGroup K` is a type synonym for `Gal(AlgebraicClosure K/K)`; view `σ` in
  -- the latter so that the `AlgEquiv` lemmas apply to it.
  revert σ
  intro (σ : Gal(AlgebraicClosure K/K)) hσ
  have hα : (root K m hm a ^ (m / n)) ^ n = algebraMap K (AlgebraicClosure K) a := by
    rw [← pow_mul, Nat.div_mul_cancel hnm, root_pow]
  rw [Units.ext_iff, Units.val_pow_eq_pow_val,
    coe_inertiaKummerCharacter_apply (σ := σ) hσ (root_pow hm a),
    coe_inertiaKummerCharacter_apply (σ := σ) hσ hα, div_pow, map_pow]

variable (m hm a) in
/-- The Kummer character is locally constant for the Krull topology: `σ ↦ σ(α)` only depends on
the restriction of `σ` to the finite extension `K(α)`. -/
theorem isLocallyConstant_inertiaKummerCharacter :
    IsLocallyConstant (inertiaKummerCharacter K m hm a) := by
  let _ : TopologicalSpace (AlgebraicClosure K) := ⊥
  have : DiscreteTopology (AlgebraicClosure K) := ⟨rfl⟩
  -- Stabilizers of points are open in the Krull topology, so the orbit maps are locally constant.
  have : ContinuousSMul Gal(AlgebraicClosure K/K) (AlgebraicClosure K) :=
    continuousSMul_iff_stabilizer_isOpen.2 stabilizer_isOpen_of_isIntegral
  have hcont : Continuous fun σ : Gal(AlgebraicClosure K/K) ↦ σ • root K m hm a := by fun_prop
  have horbit : IsLocallyConstant fun σ : Field.absoluteGaloisGroup K ↦
      DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ (root K m hm a) :=
    (IsLocallyConstant.iff_continuous _).2 hcont
  exact IsLocallyConstant.desc _ (fun ζ : rootsOfUnity m (AlgebraicClosure K) ↦
    ((ζ : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))
    ((horbit.comp (· / root K m hm a)).comp_continuous continuous_subtype_val)
    rootsOfUnity.coe_injective

variable (m hm) in
/-- **The Kummer character of a unit is trivial.** For `u ∈ U(K,0) = 𝒪[K]ˣ` and `m` prime to `p`,
inertia fixes the `m`-th roots of `u`: writing `u = ζ v` with `ζ` a `(q - 1)`-st root of unity and
`v` a principal unit, the roots of `ζ` are roots of unity of order prime to `p`, and `v` is an
`m`-th power in `K`. -/
theorem inertiaKummerCharacter_eq_one_of_mem_unitFiltration_zero {u : Kˣ}
    (hu : u ∈ unitFiltration K 0) : inertiaKummerCharacter K m hm u = 1 := by
  set x := unitFiltrationZeroEquivProd K ⟨u, hu⟩
  have hdec : u = (x.1 : Kˣ) * x.2 := by
    rw [← coe_unitFiltrationZeroEquivProd_symm_apply, ContinuousMulEquiv.symm_apply_apply]
  rw [hdec, inertiaKummerCharacter_mul]
  -- The roots of the Teichmüller component are roots of unity of order prime to `p`.
  have hζ : inertiaKummerCharacter K m hm (x.1 : Kˣ) = 1 := by
    refine (inertiaKummerCharacter_eq_one_iff (root_pow hm _)).2 fun σ hσ ↦ ?_
    refine apply_eq_self_of_mem_inertiaSubgroup_of_pow_eq_one hσ
      (Nat.Coprime.mul_left hm (natCard_sub_one_coprime_ringChar K)) ?_
    rw [pow_mul, root_pow, ← map_pow, ← Units.val_pow_eq_pow_val,
      (mem_rootsOfUnity _ _).1 x.1.2, Units.val_one, map_one]
  -- The principal-unit component is an `m`-th power in `K`, whose roots inertia fixes.
  have hv : inertiaKummerCharacter K m hm (x.2 : Kˣ) = 1 := by
    obtain ⟨w, hw⟩ := unitFiltration_one_le_range_powMonoidHom_of_isUnit
      (isUnit_natCast_of_coprime_ringChar hm) x.2.2
    have hroot : (algebraMap K (AlgebraicClosure K) w) ^ m =
        algebraMap K (AlgebraicClosure K) (x.2 : Kˣ) := by
      rw [← map_pow, ← hw, powMonoidHom_apply, Units.val_pow_eq_pow_val]
    exact (inertiaKummerCharacter_eq_one_iff hroot).2 fun σ _ ↦ AlgEquiv.commutes σ _
  rw [hζ, hv, one_mul]

/-- **Independence of the uniformizer.** Any two uniformizers of `K` have the same Kummer character
on inertia, since their ratio is a unit. -/
theorem inertiaKummerCharacter_eq_of_isUniformizer {π π' : Kˣ} (hπ : IsUniformizer K π)
    (hπ' : IsUniformizer K π') :
    inertiaKummerCharacter K m hm π = inertiaKummerCharacter K m hm π' := by
  have h : π = π * π'⁻¹ * π' := by group
  rw [h, inertiaKummerCharacter_mul, inertiaKummerCharacter_eq_one_of_mem_unitFiltration_zero m hm
    (mul_inv_mem_unitFiltration_zero ((isUniformizer_def π).1 hπ) ((isUniformizer_def π').1 hπ')),
    one_mul]

end Level

/-! ### The tame Kummer character with values in the Tate module -/

/-- **The tame Kummer character** of `a ∈ Kˣ`: the continuous homomorphism from the inertia
subgroup of `K` to the prime-to-`p` Tate module `ℤ̂^{(p')}(1) = lim_{p ∤ m} μ_m(K^{alg})`,
`σ ↦ (σ(α_m)/α_m)_m` for any roots `α_m` of `X ^ m − a`. Its components are the characters
`TauCeti.inertiaKummerCharacter K m hm a`. At a uniformizer `a = π` it is the tame character of
`K`. -/
def tameKummerCharacter (a : Kˣ) :
    inertiaSubgroup K →ₜ* PrimeToPTateModule (ringChar 𝓀[K]) (AlgebraicClosure K) where
  toMonoidHom := PrimeToPTateModule.lift (fun m ↦ inertiaKummerCharacter K m m.2.2 a)
    fun _ _ σ h ↦ inertiaKummerCharacter_pow_div _ h σ
  continuous_toFun := PrimeToPTateModule.continuous_iff.2 fun m ↦ by
    simpa only [MonoidHom.toFun_eq_coe, PrimeToPTateModule.proj_lift] using
      isLocallyConstant_inertiaKummerCharacter m m.2.2 a

variable {K}

/-- The component of the tame Kummer character at level `m` is the Kummer character at level
`m`. -/
@[simp]
theorem proj_tameKummerCharacter_apply (a : Kˣ)
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime (ringChar 𝓀[K])}) (σ : inertiaSubgroup K) :
    PrimeToPTateModule.proj m (tameKummerCharacter K a σ) = inertiaKummerCharacter K m m.2.2 a σ :=
  PrimeToPTateModule.proj_lift _ _ m σ

/-- The tame Kummer character is multiplicative in `a`. -/
@[simp]
theorem tameKummerCharacter_mul (a b : Kˣ) :
    tameKummerCharacter K (a * b) = tameKummerCharacter K a * tameKummerCharacter K b := by
  ext σ m : 2
  simp

/-- The tame Kummer character of one is trivial. -/
@[simp]
theorem tameKummerCharacter_one : tameKummerCharacter K (1 : Kˣ) = 1 := by
  ext σ m : 2
  simp

/-- The tame Kummer character of an inverse is the inverse tame Kummer character. -/
@[simp]
theorem tameKummerCharacter_inv (a : Kˣ) :
    tameKummerCharacter K a⁻¹ = (tameKummerCharacter K a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← tameKummerCharacter_mul, inv_mul_cancel, tameKummerCharacter_one]

/-- The tame Kummer character of a natural power is the corresponding power of the tame Kummer
character. -/
@[simp]
theorem tameKummerCharacter_pow (a : Kˣ) (n : ℕ) :
    tameKummerCharacter K (a ^ n) = (tameKummerCharacter K a) ^ n := by
  ext σ m : 2
  simp

/-- The tame Kummer character of a unit is trivial. -/
theorem tameKummerCharacter_eq_one_of_mem_unitFiltration_zero {u : Kˣ}
    (hu : u ∈ unitFiltration K 0) : tameKummerCharacter K u = 1 := by
  ext σ m : 2
  simp [inertiaKummerCharacter_eq_one_of_mem_unitFiltration_zero _ _ hu]

/-- Any two uniformizers of `K` have the same tame Kummer character. -/
theorem tameKummerCharacter_eq_of_isUniformizer {π π' : Kˣ} (hπ : IsUniformizer K π)
    (hπ' : IsUniformizer K π') : tameKummerCharacter K π = tameKummerCharacter K π' := by
  ext σ m : 2
  simp [inertiaKummerCharacter_eq_of_isUniformizer hπ hπ']

/-! ### The tame character -/

variable (K) in
/-- **The tame character** of `K`: the continuous homomorphism `I_K →ₜ* ℤ̂^{(p')}(1)`,
`σ ↦ (σ(π^{1/m})/π^{1/m})_m`, for a uniformizer `π` of `K` and any `m`-th roots `π^{1/m}` of it.
It depends neither on `π` (`TauCeti.inertiaTameCharacter_eq_tameKummerCharacter`) nor on the roots
(`TauCeti.coe_proj_inertiaTameCharacter_apply`). -/
def inertiaTameCharacter :
    inertiaSubgroup K →ₜ* PrimeToPTateModule (ringChar 𝓀[K]) (AlgebraicClosure K) :=
  tameKummerCharacter K (exists_isUniformizer K).choose

/-- The tame character is the tame Kummer character of any uniformizer. -/
theorem inertiaTameCharacter_eq_tameKummerCharacter {π : Kˣ} (hπ : IsUniformizer K π) :
    inertiaTameCharacter K = tameKummerCharacter K π :=
  tameKummerCharacter_eq_of_isUniformizer (exists_isUniformizer K).choose_spec hπ

/-- **The tame character at level `m`.** For a uniformizer `π` of `K`, `m` prime to `p`, and any
root `α` of `X ^ m − π`, the level-`m` component of the tame character at `σ ∈ I_K` is `σ(α)/α`. -/
theorem coe_proj_inertiaTameCharacter_apply {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) {π : Kˣ} (hπ : IsUniformizer K π)
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime (ringChar 𝓀[K])})
    {α : AlgebraicClosure K} (hα : α ^ (m : ℕ) = algebraMap K (AlgebraicClosure K) π) :
    ((PrimeToPTateModule.proj m (inertiaTameCharacter K ⟨σ, hσ⟩) : (AlgebraicClosure K)ˣ) :
      AlgebraicClosure K) = σ α / α := by
  rw [inertiaTameCharacter_eq_tameKummerCharacter hπ, proj_tameKummerCharacter_apply,
    coe_inertiaKummerCharacter_apply hσ hα]

end TauCeti
