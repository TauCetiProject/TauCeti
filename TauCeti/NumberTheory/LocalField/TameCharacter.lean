/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Kummer.Character
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia
public import TauCeti.NumberTheory.LocalField.Uniformizer
public import TauCeti.NumberTheory.LocalField.UnitsDecomposition
public import TauCeti.NumberTheory.LocalField.WildInertia
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

independent of the uniformizer and of the chosen roots. It is surjective, because `X ^ m − π` stays
irreducible over `K^{ur}`, so that `I_K = Gal(K^{alg}/K^{ur})` moves `π^{1/m}` to each of its
conjugates `ζ π^{1/m}`, and `I_K` is compact. Its kernel is the wild inertia group `P_K`, the
automorphisms fixing all the `π^{1/m}` over `K^{ur}`. So it identifies the tame inertia group
`I_K/P_K` with `ℤ̂^{(p')}(1)`, as topological groups. It is equivariant for conjugation by
`G_K`, which acts on `ℤ̂^{(p')}(1)` through its action on the roots of unity: this is the twist
`(1)`.

## Main definitions

* `TauCeti.inertiaKummerCharacter K m hm a`: for `m` prime to `p` and `a ∈ Kˣ`, the character
  `σ ↦ σ(α)/α` of `I_K` with values in `μ_m(K^{alg})`, for any `m`-th root `α` of `a`.
* `TauCeti.tameKummerCharacter K a`: the compatible family of these characters, a continuous
  homomorphism `I_K →ₜ* PrimeToPTateModule p K^{alg}`.
* `TauCeti.inertiaTameCharacter K`: the tame Kummer character of a uniformizer.
* `TauCeti.quotientWildInertiaSubgroupEquiv K`: the isomorphism of topological groups
  `I_K/P_K ≃ₜ* ℤ̂^{(p')}(1)` induced by the tame character.

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
* `TauCeti.inertiaKummerCharacter_surjective`, `TauCeti.inertiaTameCharacter_surjective`: the
  Kummer character of a uniformizer is surjective at each level, and the tame character is
  surjective.
* `TauCeti.inertiaTameCharacter_eq_one_iff`, `TauCeti.ker_inertiaTameCharacter`: the kernel of the
  tame character is the wild inertia subgroup.
* `TauCeti.inertiaTameCharacter_conj`: the tame character is `G_K`-equivariant.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Proposition 7 and its corollaries.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (7.5.2).
-/

public section

noncomputable section

open ValuativeRel Polynomial

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
inertia fixes the `m`-th roots of `u`, which are unramified by
`TauCeti.mem_maximalUnramifiedExtension_of_pow_eq`: writing `u = ζ v` with `ζ` a `(q - 1)`-st root
of unity and `v` a principal unit, the roots of `ζ` are roots of unity of order prime to `p`, and
`v` is an `m`-th power in `K`. -/
theorem inertiaKummerCharacter_eq_one_of_mem_unitFiltration_zero {u : Kˣ}
    (hu : u ∈ unitFiltration K 0) : inertiaKummerCharacter K m hm u = 1 :=
  (inertiaKummerCharacter_eq_one_iff (root_pow hm u)).2 fun _ hσ ↦
    mem_inertiaSubgroup_iff.1 hσ _ <| mem_maximalUnramifiedExtension_of_pow_eq
      ((CharP.prime_ringChar 𝓀[K]).coprime_iff_not_dvd.1 hm.symm) hu
      (root_pow hm u)

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

/-! ### Surjectivity -/

/-- **The Kummer character of a uniformizer is surjective at each level.** For a uniformizer `π`
and `m` prime to `p`, every `m`-th root of unity `ζ` is `σ(α)/α` for some `σ ∈ I_K`, where `α` is
a root of `X ^ m − π`: as `X ^ m − π` is irreducible over `K^{ur}`
(`TauCeti.X_pow_sub_C_irreducible_maximalUnramifiedExtension`), `Gal(K^{alg}/K^{ur}) = I_K`
carries `α` to its conjugate `ζ α`. -/
theorem inertiaKummerCharacter_surjective {π : Kˣ} (hπ : IsUniformizer K π) (m : ℕ)
    (hm : m.Coprime (ringChar 𝓀[K])) :
    Function.Surjective (inertiaKummerCharacter K m hm π) := by
  set E := maximalUnramifiedExtension K (AlgebraicClosure K)
  have hm0 := ne_zero_of_coprime_ringChar hm
  intro ζ
  set z : AlgebraicClosure K := ((ζ : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
  have hz : z ^ m = 1 := by
    simpa [z] using congrArg Units.val ((mem_rootsOfUnity m _).1 ζ.2)
  -- `α` and `z α` are roots of `X ^ m − π`, which is their common minimal polynomial over `E`.
  have hα := root_pow hm π
  have hzα : (z * root K m hm π) ^ m = algebraMap K (AlgebraicClosure K) π := by
    rw [mul_pow, hz, one_mul, hα]
  have hirr := X_pow_sub_C_irreducible_maximalUnramifiedExtension (Ω := AlgebraicClosure K) hπ hm0
  have hmin {β : AlgebraicClosure K} (hβ : β ^ m = algebraMap K (AlgebraicClosure K) π) :
      minpoly E β = X ^ m - C (algebraMap K E π) :=
    (minpoly.eq_of_irreducible_of_monic hirr (by simp [hβ]) (monic_X_pow_sub_C _ hm0)).symm
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := E) (AlgebraicClosure K)).1
    ((hmin hzα).trans (hmin hα).symm)
  replace hτ : τ (root K m hm π) = z * root K m hm π := hτ
  -- An automorphism of `K^{alg}` over `E = K^{ur}` is an element of inertia.
  let σ : Gal(AlgebraicClosure K/K) := τ.restrictScalars K
  have hσ : σ ∈ inertiaSubgroup K := mem_inertiaSubgroup_iff.2 fun x hx ↦ τ.commutes ⟨x, hx⟩
  refine ⟨⟨σ, hσ⟩, Subtype.ext (Units.ext ?_)⟩
  rw [coe_inertiaKummerCharacter_apply hσ hα]
  simp only [σ, AlgEquiv.restrictScalars_apply]
  rw [hτ, mul_div_cancel_right₀ _ (ne_zero_of_pow_eq_algebraMap hm hα)]

variable (K) in
/-- **The tame character is surjective**: `I_K → ℤ̂^{(p')}(1)` is onto, since it is onto at each
finite level (`TauCeti.inertiaKummerCharacter_surjective`) and `I_K` is compact. -/
theorem inertiaTameCharacter_surjective : Function.Surjective (inertiaTameCharacter K) := by
  have : CompactSpace (inertiaSubgroup K) :=
    isCompact_iff_compactSpace.1 (isClosed_inertiaSubgroup K).isCompact
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  refine PrimeToPTateModule.surjective_of_forall_surjective_proj
    (inertiaTameCharacter K).continuous fun m ↦ ?_
  rw [inertiaTameCharacter_eq_tameKummerCharacter hπ]
  simpa only [proj_tameKummerCharacter_apply] using inertiaKummerCharacter_surjective hπ m m.2.2

/-! ### The kernel is wild inertia -/

/-- **The kernel of the tame character is wild inertia**: `σ ∈ I_K` has trivial tame character
exactly when it lies in `P_K`, that is, when it fixes every `m`-th root of a uniformizer for
`p ∤ m` (`TauCeti.mem_wildInertiaSubgroup_iff_of_isUniformizer`). -/
theorem inertiaTameCharacter_eq_one_iff {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) :
    inertiaTameCharacter K ⟨σ, hσ⟩ = 1 ↔ σ ∈ wildInertiaSubgroup K := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  have hp := CharP.prime_ringChar 𝓀[K]
  refine Iff.trans ?_ ((mem_wildInertiaSubgroup_iff_of_isUniformizer hπ (σ := σ)).trans
    (and_iff_right hσ)).symm
  constructor
  · intro h m hm α hα
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
    have hcop : m.Coprime (ringChar 𝓀[K]) := Nat.coprime_comm.1 (hp.coprime_iff_not_dvd.2 hm)
    have h' := coe_proj_inertiaTameCharacter_apply hσ hπ ⟨m, hm0, hcop⟩ hα
    rwa [h, map_one, OneMemClass.coe_one, Units.val_one, eq_comm,
      div_eq_one_iff_eq (ne_zero_of_pow_eq_algebraMap hcop hα)] at h'
  · intro h
    refine PrimeToPTateModule.ext fun m ↦ Subtype.ext (Units.ext ?_)
    have hα := root_pow m.2.2 π
    have hm : ¬ ringChar 𝓀[K] ∣ m := hp.coprime_iff_not_dvd.1 (Nat.coprime_comm.1 m.2.2)
    rw [coe_proj_inertiaTameCharacter_apply hσ hπ m hα, h m hm _ hα,
      div_self (ne_zero_of_pow_eq_algebraMap m.2.2 hα)]
    simp

variable (K) in
/-- The kernel of the tame character is the wild inertia subgroup `P_K`, viewed inside `I_K`. -/
theorem ker_inertiaTameCharacter :
    (inertiaTameCharacter K).toMonoidHom.ker =
      (wildInertiaSubgroup K).subgroupOf (inertiaSubgroup K) := by
  ext ⟨σ, hσ⟩
  -- `Field.absoluteGaloisGroup K` is a type synonym for `Gal(AlgebraicClosure K/K)`; view `σ` in
  -- the latter to match `TauCeti.inertiaTameCharacter_eq_one_iff`.
  revert σ
  intro (σ : Gal(AlgebraicClosure K/K)) hσ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact inertiaTameCharacter_eq_one_iff hσ

/-! ### Tame inertia -/

variable (K) in
/-- **Tame inertia is the prime-to-`p` Tate module**: the tame character induces an isomorphism
of topological groups `I_K / P_K ≃ₜ* ℤ̂^{(p')}(1)` from the tame inertia group, the quotient of
the inertia subgroup by the wild inertia subgroup. -/
def quotientWildInertiaSubgroupEquiv :
    inertiaSubgroup K ⧸ (wildInertiaSubgroup K).subgroupOf (inertiaSubgroup K) ≃ₜ*
      PrimeToPTateModule (ringChar 𝓀[K]) (AlgebraicClosure K) :=
  haveI : CompactSpace (inertiaSubgroup K) :=
    isCompact_iff_compactSpace.1 (isClosed_inertiaSubgroup K).isCompact
  let e := (QuotientGroup.quotientMulEquivOfEq (ker_inertiaTameCharacter K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (inertiaTameCharacter_surjective K))
  -- A continuous bijection from the compact quotient to the Hausdorff Tate module is a
  -- homeomorphism.
  have he : Continuous e :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (inertiaTameCharacter K).continuous
  ContinuousMulEquiv.mk e he (he.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv))

/-- The isomorphism `I_K / P_K ≃ₜ* ℤ̂^{(p')}(1)` sends the class of `σ` to its tame character. -/
@[simp]
theorem quotientWildInertiaSubgroupEquiv_mk (σ : inertiaSubgroup K) :
    quotientWildInertiaSubgroupEquiv K σ = inertiaTameCharacter K σ :=
  (rfl)

/-- The inverse isomorphism `ℤ̂^{(p')}(1) ≃ₜ* I_K / P_K` sends the tame character of `σ` to the
class of `σ`. -/
@[simp]
theorem quotientWildInertiaSubgroupEquiv_symm_inertiaTameCharacter (σ : inertiaSubgroup K) :
    (quotientWildInertiaSubgroupEquiv K).symm (inertiaTameCharacter K σ) = σ := by
  rw [ContinuousMulEquiv.symm_apply_eq, quotientWildInertiaSubgroupEquiv_mk]

/-! ### Equivariance -/

/-- **The tame character is `G_K`-equivariant**: conjugating an element of inertia by `g ∈ G_K`
applies `g` to its tame character, for the action of `G_K` on `ℤ̂^{(p')}(1)` through the roots of
unity of `K^{alg}`. This is the twist `(1)` in `I_K / P_K ≅ ℤ̂^{(p')}(1)`. -/
theorem inertiaTameCharacter_conj (g : Gal(AlgebraicClosure K/K)) {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) :
    inertiaTameCharacter K ⟨g * σ * g⁻¹, (inertiaSubgroup_normal K).conj_mem σ hσ g⟩ =
      g • inertiaTameCharacter K ⟨σ, hσ⟩ := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  refine PrimeToPTateModule.ext fun m ↦ Subtype.ext (Units.ext ?_)
  -- With `α` a root of `X ^ m − π`, so is `g⁻¹ α`, and `g σ g⁻¹ (α) / α = g (σ β / β)` for
  -- `β = g⁻¹ α`.
  have hα := root_pow m.2.2 π
  have hβ : (g⁻¹ (root K m m.2.2 π)) ^ (m : ℕ) = algebraMap K (AlgebraicClosure K) π := by
    rw [← map_pow, hα, AlgEquiv.commutes]
  refine (coe_proj_inertiaTameCharacter_apply _ hπ m hα).trans ?_
  rw [PrimeToPTateModule.coe_proj_smul, coe_proj_inertiaTameCharacter_apply hσ hπ m hβ,
    AlgEquiv.smul_def, map_div₀]
  simp [AlgEquiv.mul_apply]

end TauCeti
