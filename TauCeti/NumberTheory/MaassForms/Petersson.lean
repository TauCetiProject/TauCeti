/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Basic
public import TauCeti.Analysis.Complex.ModularForms.CongruenceSubgroups.QuotientMeasure
public import TauCeti.NumberTheory.MaassForms.Automorphic
public import TauCeti.NumberTheory.MaassForms.CuspIntegral

/-!
# Square-integrability and the Petersson inner product at weight `0`

A Maass form of level `N` and nebentypus `χ` is square-integrable on `Γ₀(N) \ ℍ`, and the
Hilbert-space structure on such forms is the Petersson inner product
`⟨f, g⟩ = ∫_F f * conj g dμ` over a fundamental domain `F`, with `dμ = dx dy / y²`. This file
sets up both at weight `0`.

The group whose fundamental domains are used is the *effective* image
`PΓ₀(N) = gamma0PSL N` of `Γ₀(N)` in `PSL(2, ℝ)`, not `Γ₀(N)` itself: `-I ∈ Γ₀(N)` acts trivially
on `ℍ`, so no subset of `ℍ` is a fundamental domain for `Γ₀(N)`. Both groups have the same orbits,
and the covolume of `PΓ₀(N)` is `[SL(2, ℤ) : Γ₀(N)] · π / 3` (`covolume_gamma0PSL`).

For a function `f` automorphic with nebentypus `χ`, the norm `‖f‖` is invariant under
`PΓ₀(N)`, since `|χ(d)| = 1` at every unit `d`; hence square-integrability on one fundamental
domain is square-integrability on every other (`IsAutomorphic.isSquareIntegrable_iff`), and for
`f`, `g` automorphic with the same nebentypus the integral of `f * conj g` is the same over every
fundamental domain (`IsAutomorphic.petersson_eq_setIntegral`). To have a definite value for every
pair of functions, `petersson N f g` integrates over one fixed fundamental domain, the Dirichlet
domain of `PΓ₀(N)` centred at `2i`. This is a fundamental domain because `2i` has trivial
stabilizer in the image of `PSL(2, ℤ)`: it lies in the interior of the standard fundamental
domain (`TauCeti.ModularGroup.mem_freeLocus_of_mem_fdo`). (The point `i` would not do: `S` fixes
it, and the Dirichlet domain centred at `i` has twice the area of a fundamental domain.)

The product is linear in the first slot and conjugate-linear in the second, conjugate-symmetric,
and positive definite on continuous square-integrable automorphic functions; it is invariant under
every element of `PSL(2, ℝ)` normalizing `PΓ₀(N)`, such as the image of the Fricke matrix
`[0, -1; N, 0]`.

## Main definitions

* `TauCeti.MaassForms.gamma0PSL N`: the image `PΓ₀(N)` of `Γ₀(N)` in `PSL(2, ℝ)`.
* `TauCeti.MaassForms.IsSquareIntegrable N f`: `|f|²` is integrable over some measurable
  fundamental domain of `PΓ₀(N)`.
* `TauCeti.MaassForms.petersson N f g`: the integral of `f * conj g` over the Dirichlet domain of
  `PΓ₀(N)` centred at `2i`.

## Main results

* `TauCeti.MaassForms.covolume_gamma0PSL`, `TauCeti.MaassForms.covolume_gamma0PSL_eq_mul_prod`:
  the covolume of `PΓ₀(N)` is `[SL(2, ℤ) : Γ₀(N)] · π / 3 = (π / 3) · N · ∏_{p ∣ N} (1 + 1 / p)`.
* `TauCeti.MaassForms.isFundamentalDomain_dirichletDomain_gamma0PSL`: the Dirichlet domain of
  `PΓ₀(N)` centred at `2i` is a measurable fundamental domain.
* `TauCeti.MaassForms.IsAutomorphic.isSquareIntegrable_iff`: for an automorphic function,
  square-integrability over any one fundamental domain is square-integrability.
* `TauCeti.MaassForms.IsSquareIntegrable.memLp`,
  `TauCeti.MaassForms.IsSquareIntegrable.integrableOn_mul_conj`: a measurable square-integrable
  automorphic function is in `L²` of every fundamental domain, so the Petersson integrand of two
  of them is integrable.
* `TauCeti.MaassForms.IsAutomorphic.petersson_eq_setIntegral`: the Petersson product of two
  automorphic functions with the same nebentypus may be computed on any fundamental domain.
* `TauCeti.MaassForms.petersson_const_const`: the Petersson product of two constants is their
  product times the covolume; at level `1` the constant `1` has squared norm `π / 3`.
* `TauCeti.MaassForms.IsAutomorphic.petersson_self_eq_zero_iff`: positive definiteness on
  continuous square-integrable automorphic functions.
* `TauCeti.MaassForms.IsAutomorphic.petersson_comp_smul`: invariance under the normalizer of
  `PΓ₀(N)` in `PSL(2, ℝ)`.

## References

* H. Iwaniec, *Spectral Methods of Automorphic Forms*, 2nd ed., Graduate Studies in Mathematics
  **53**, AMS, 2002, §§2.1–2.2 and 3.1 (fundamental domains, the invariant measure, and the inner
  product on automorphic functions).
* A. R. Booker, M. Lee and A. Strömbergsson, *Twist-minimal trace formulas and the Selberg
  eigenvalue conjecture*, J. London Math. Soc. **102** (2020), arXiv:1803.06016, §1.1.
-/

public section

open Complex MeasureTheory MulAction Set UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ComplexConjugate Pointwise ENNReal

namespace TauCeti.MaassForms

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {f g h : ℍ → ℂ}

/-! ### The effective group `PΓ₀(N)` -/

variable (N) in
/-- **The effective group** `PΓ₀(N)`: the image of `Γ₀(N)` in `PSL(2, ℝ)`. It acts on `ℍ` with
the same orbits as `Γ₀(N)`, and, unlike `Γ₀(N)`, it acts faithfully, so it has fundamental
domains. -/
def gamma0PSL : Subgroup PSL(2, ℝ) :=
  (Gamma0 N).map sl2zToPSL2R

variable (N) in
theorem gamma0PSL_def : gamma0PSL N = (Gamma0 N).map sl2zToPSL2R := (rfl)

theorem mem_gamma0PSL {g : PSL(2, ℝ)} :
    g ∈ gamma0PSL N ↔ ∃ γ ∈ Gamma0 N, sl2zToPSL2R γ = g :=
  Subgroup.mem_map

theorem sl2zToPSL2R_mem_gamma0PSL {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    sl2zToPSL2R γ ∈ gamma0PSL N :=
  mem_gamma0PSL.mpr ⟨γ, hγ, rfl⟩

instance : DiscreteTopology (gamma0PSL N) :=
  Subgroup.discreteTopology_map_sl2zToPSL2R _

/-- **The covolume of `PΓ₀(N)`** is `[SL(2, ℤ) : Γ₀(N)] · π / 3`, the index of `Γ₀(N)` times the
area of the level-one quotient. -/
theorem covolume_gamma0PSL [NeZero N] :
    covolume (gamma0PSL N) ℍ = (Gamma0 N).index * ENNReal.ofReal (Real.pi / 3) := by
  rw [gamma0PSL, ← Subgroup.quotientVolume_univ,
    Subgroup.quotientVolume_univ_eq_index_mul_of_neg_one_mem _ (by simp [Gamma0_mem])]

/-- **Dedekind's form of the covolume of `PΓ₀(N)`**: `(π / 3) · N · ∏_{p ∣ N} (1 + 1 / p)`. -/
theorem covolume_gamma0PSL_eq_mul_prod [NeZero N] :
    covolume (gamma0PSL N) ℍ =
      ENNReal.ofReal (Real.pi / 3 * N * ∏ p ∈ N.primeFactors, (1 + (p : ℝ)⁻¹)) := by
  have hp0 {p : ℕ} (hp : p ∈ N.primeFactors) : (p : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hprod : (∏ p ∈ N.primeFactors, (p : ℝ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun _ ↦ hp0
  have hindex : ((Gamma0 N).index : ℝ) = N * ∏ p ∈ N.primeFactors, (1 + (p : ℝ)⁻¹) := by
    have h := congrArg (Nat.cast (R := ℝ)) (Gamma0_index_mul_prod_primeFactors (N := N))
    push_cast at h
    rw [eq_div_of_mul_eq hprod h, mul_div_assoc, ← Finset.prod_div_distrib]
    refine congrArg _ (Finset.prod_congr rfl fun p hp ↦ ?_)
    field_simp [hp0 hp]
  rw [covolume_gamma0PSL, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    hindex]
  ring_nf

/-! ### The centre `2i` and the Dirichlet domain -/

/-- The point `2i` lies in the open standard fundamental domain. -/
private theorem pt_zero_two_mem_fdo : pt 0 2 ∈ ModularGroup.fdo := by
  refine ⟨?_, ?_⟩
  · rw [coe_pt 0 two_pos]
    norm_num [Complex.normSq_apply]
  · rw [re_pt 0 two_pos, abs_zero]
    norm_num

/-- **The Dirichlet domain of `PΓ₀(N)` centred at `2i`** is a measurable fundamental domain. -/
theorem isFundamentalDomain_dirichletDomain_gamma0PSL :
    IsFundamentalDomain (gamma0PSL N) (dirichletDomain (gamma0PSL N) (pt 0 2)) :=
  Subgroup.isFundamentalDomain_dirichletDomain _ <| ModularGroup.mem_freeLocus_of_mem_fdo
    (Subgroup.map_sl2zToPSL2R_le_range_psl2zToPSL2R _) pt_zero_two_mem_fdo

/-! ### Invariance of `|f|` and of `f * conj g` -/

/-- The nebentypus takes values of norm `1` on the lower-right entries of `Γ₀(N)`. -/
private theorem norm_char_apply_one_one {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ‖χ ((γ 1 1 : ℤ) : ZMod N)‖ = 1 :=
  DirichletCharacter.unit_norm_eq_one χ (isUnit_intCast_apply_one_one_of_mem_Gamma0 hγ).unit

/-- **The absolute value of an automorphic function is `PΓ₀(N)`-invariant**, since the
nebentypus has absolute value `1` on units. -/
theorem IsAutomorphic.norm_apply_smul (hf : IsAutomorphic N χ f) {g : PSL(2, ℝ)}
    (hg : g ∈ gamma0PSL N) (z : ℍ) : ‖f (g • z)‖ = ‖f z‖ := by
  obtain ⟨γ, hγ, rfl⟩ := mem_gamma0PSL.mp hg
  rw [sl2zToPSL2R_smul, hf.apply_smul hγ, norm_mul, norm_char_apply_one_one hγ, one_mul]

/-- **For automorphic `f` and `g` with the same nebentypus, `f * conj g` is
`PΓ₀(N)`-invariant**: the factors `χ(d)` and `conj χ(d)` multiply to `|χ(d)|² = 1`. -/
theorem IsAutomorphic.mul_conj_apply_smul (hf : IsAutomorphic N χ f) (hg : IsAutomorphic N χ g)
    {σ : PSL(2, ℝ)} (hσ : σ ∈ gamma0PSL N) (z : ℍ) :
    f (σ • z) * conj (g (σ • z)) = f z * conj (g z) := by
  obtain ⟨γ, hγ, rfl⟩ := mem_gamma0PSL.mp hσ
  rw [sl2zToPSL2R_smul, hf.apply_smul hγ, hg.apply_smul hγ, map_mul,
    mul_mul_mul_comm, RCLike.mul_conj, norm_char_apply_one_one hγ]
  simp

/-! ### Square-integrability -/

variable (N) in
/-- **Square-integrability on `Γ₀(N) \ ℍ`**: `|f|²` is integrable, for the invariant measure
`dx dy / y²`, over some measurable fundamental domain of the effective group `PΓ₀(N)`. For an
automorphic `f` the choice of fundamental domain does not matter
(`IsAutomorphic.isSquareIntegrable_iff`). -/
def IsSquareIntegrable (f : ℍ → ℂ) : Prop :=
  ∃ F : Set ℍ, IsFundamentalDomain (gamma0PSL N) F ∧ IntegrableOn (fun z ↦ ‖f z‖ ^ 2) F

theorem isSquareIntegrable_iff :
    IsSquareIntegrable N f ↔
      ∃ F : Set ℍ, IsFundamentalDomain (gamma0PSL N) F ∧ IntegrableOn (fun z ↦ ‖f z‖ ^ 2) F :=
  Iff.rfl

/-- **Square-integrability of an automorphic function on a given fundamental domain**: for `f`
automorphic with any nebentypus and any measurable fundamental domain `F` of `PΓ₀(N)`, `f` is
square-integrable exactly when `|f|²` is integrable over `F`. -/
theorem IsAutomorphic.isSquareIntegrable_iff (hf : IsAutomorphic N χ f) {F : Set ℍ}
    (hF : IsFundamentalDomain (gamma0PSL N) F) :
    IsSquareIntegrable N f ↔ IntegrableOn (fun z ↦ ‖f z‖ ^ 2) F := by
  have hinv (g : gamma0PSL N) (z : ℍ) : ‖f (g • z)‖ ^ 2 = ‖f z‖ ^ 2 := by
    rw [Subgroup.smul_def, hf.norm_apply_smul g.property]
  exact ⟨fun ⟨F', hF', h⟩ ↦ (hF'.integrableOn_iff hF hinv).mp h, fun h ↦ ⟨F, hF, h⟩⟩

@[simp]
theorem isSquareIntegrable_zero : IsSquareIntegrable N 0 :=
  ⟨_, isFundamentalDomain_dirichletDomain_gamma0PSL, by simp⟩

/-- At positive level every constant is square-integrable: `Γ₀(N) \ ℍ` has finite area. -/
theorem isSquareIntegrable_const [NeZero N] (c : ℂ) : IsSquareIntegrable N fun _ ↦ c := by
  refine ⟨_, isFundamentalDomain_dirichletDomain_gamma0PSL, integrableOn_const ?_⟩
  rw [← isFundamentalDomain_dirichletDomain_gamma0PSL.covolume_eq_volume, covolume_gamma0PSL]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top

theorem IsSquareIntegrable.const_smul (hf : IsSquareIntegrable N f) (c : ℂ) :
    IsSquareIntegrable N (c • f) := by
  obtain ⟨F, hF, h⟩ := hf
  refine ⟨F, hF, ?_⟩
  simpa [norm_mul, mul_pow, IntegrableOn] using h.const_mul (‖c‖ ^ 2)

/-- **A square-integrable automorphic function lies in `L²` of every fundamental domain**, when it
is almost everywhere strongly measurable. -/
theorem IsSquareIntegrable.memLp (hf : IsSquareIntegrable N f) (hfa : IsAutomorphic N χ f)
    (hfm : AEStronglyMeasurable f) {F : Set ℍ} (hF : IsFundamentalDomain (gamma0PSL N) F) :
    MemLp f 2 (volume.restrict F) :=
  (memLp_two_iff_integrable_sq_norm hfm.restrict).mpr ((hfa.isSquareIntegrable_iff hF).mp hf)

/-- **Sums of square-integrable functions are square-integrable**, for almost everywhere strongly
measurable `f` and `g`, with `f` automorphic so that both can be integrated over a common
fundamental domain. -/
theorem IsSquareIntegrable.add (hf : IsSquareIntegrable N f) (hg : IsSquareIntegrable N g)
    (hfa : IsAutomorphic N χ f) (hfm : AEStronglyMeasurable f) (hgm : AEStronglyMeasurable g) :
    IsSquareIntegrable N (f + g) := by
  obtain ⟨F, hF, hg2⟩ := hg
  refine ⟨F, hF, (memLp_two_iff_integrable_sq_norm (hfm.add hgm).restrict).mp ?_⟩
  exact (hf.memLp hfa hfm hF).add ((memLp_two_iff_integrable_sq_norm hgm.restrict).mpr hg2)

/-- **`f * conj g` is integrable on every fundamental domain** for square-integrable, almost
everywhere strongly measurable automorphic `f` and `g`, whose nebentypes may differ: on a
fundamental domain both lie in `L²`, and the product of two `L²` functions is integrable. -/
theorem IsSquareIntegrable.integrableOn_mul_conj {χ' : DirichletCharacter ℂ N}
    (hf : IsSquareIntegrable N f) (hg : IsSquareIntegrable N g) (hfa : IsAutomorphic N χ f)
    (hga : IsAutomorphic N χ' g) (hfm : AEStronglyMeasurable f) (hgm : AEStronglyMeasurable g)
    {F : Set ℍ} (hF : IsFundamentalDomain (gamma0PSL N) F) :
    IntegrableOn (fun z ↦ f z * conj (g z)) F := by
  simpa [IntegrableOn, Pi.mul_def, Pi.star_def, Complex.star_def] using
    (hf.memLp hfa hfm hF).integrable_mul (hg.memLp hga hgm hF).star

/-! ### The Petersson inner product -/

variable (N) in
/-- **The Petersson inner product at weight `0`**, `⟨f, g⟩ = ∫_F f * conj g dμ` over the Dirichlet
domain `F` of `PΓ₀(N)` centred at `2i`, for the invariant measure `dμ = dx dy / y²` and with no
normalization by the covolume. It is linear in `f` and conjugate-linear in `g`. For automorphic
`f` and `g` with the same nebentypus the integral is the same over every measurable fundamental
domain of `PΓ₀(N)` (`IsAutomorphic.petersson_eq_setIntegral`). -/
noncomputable def petersson (f g : ℍ → ℂ) : ℂ :=
  ∫ z in dirichletDomain (gamma0PSL N) (pt 0 2), f z * conj (g z)

variable (N) in
theorem petersson_def (f g : ℍ → ℂ) :
    petersson N f g = ∫ z in dirichletDomain (gamma0PSL N) (pt 0 2), f z * conj (g z) := (rfl)

/-- **Independence of the fundamental domain.** For `f` and `g` automorphic with the same
nebentypus, the Petersson product is the integral of `f * conj g` over any measurable
fundamental domain of `PΓ₀(N)`. -/
theorem IsAutomorphic.petersson_eq_setIntegral (hf : IsAutomorphic N χ f)
    (hg : IsAutomorphic N χ g) {F : Set ℍ} (hF : IsFundamentalDomain (gamma0PSL N) F) :
    petersson N f g = ∫ z in F, f z * conj (g z) :=
  isFundamentalDomain_dirichletDomain_gamma0PSL.setIntegral_eq hF fun σ z ↦ by
    rw [Subgroup.smul_def, hf.mul_conj_apply_smul hg σ.property]

/-- **Conjugate symmetry**: `conj ⟨f, g⟩ = ⟨g, f⟩`. -/
theorem petersson_conj_symm (f g : ℍ → ℂ) : conj (petersson N f g) = petersson N g f := by
  rw [petersson, petersson, ← integral_conj]
  simp [mul_comm]

@[simp]
theorem petersson_zero_left (g : ℍ → ℂ) : petersson N 0 g = 0 := by
  simp [petersson]

@[simp]
theorem petersson_zero_right (f : ℍ → ℂ) : petersson N f 0 = 0 := by
  simp [petersson]

@[simp]
theorem petersson_smul_left (c : ℂ) (f g : ℍ → ℂ) :
    petersson N (c • f) g = c * petersson N f g := by
  simp only [petersson, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

@[simp]
theorem petersson_smul_right (c : ℂ) (f g : ℍ → ℂ) :
    petersson N f (c • g) = conj c * petersson N f g := by
  rw [← petersson_conj_symm, petersson_smul_left, map_mul, petersson_conj_symm]

/-- **Additivity in the first slot**, when `f₁ * conj g` and `f₂ * conj g` are integrable on the
Dirichlet domain, as they are for square-integrable automorphic functions
(`IsSquareIntegrable.integrableOn_mul_conj`). -/
theorem petersson_add_left {f₁ f₂ : ℍ → ℂ}
    (h₁ : IntegrableOn (fun z ↦ f₁ z * conj (g z)) (dirichletDomain (gamma0PSL N) (pt 0 2)))
    (h₂ : IntegrableOn (fun z ↦ f₂ z * conj (g z)) (dirichletDomain (gamma0PSL N) (pt 0 2))) :
    petersson N (f₁ + f₂) g = petersson N f₁ g + petersson N f₂ g := by
  simp only [petersson, Pi.add_apply, add_mul]
  exact integral_add h₁ h₂

/-- **Additivity in the second slot**, when `f * conj g₁` and `f * conj g₂` are integrable on the
Dirichlet domain. -/
theorem petersson_add_right {g₁ g₂ : ℍ → ℂ}
    (h₁ : IntegrableOn (fun z ↦ f z * conj (g₁ z)) (dirichletDomain (gamma0PSL N) (pt 0 2)))
    (h₂ : IntegrableOn (fun z ↦ f z * conj (g₂ z)) (dirichletDomain (gamma0PSL N) (pt 0 2))) :
    petersson N f (g₁ + g₂) = petersson N f g₁ + petersson N f g₂ := by
  simp only [petersson, Pi.add_apply, map_add, mul_add]
  exact integral_add h₁ h₂

/-- **The Petersson norm**: `⟨f, f⟩` is the real number `∫_F |f|² dμ`. -/
theorem petersson_self (f : ℍ → ℂ) :
    petersson N f f = ((∫ z in dirichletDomain (gamma0PSL N) (pt 0 2), ‖f z‖ ^ 2 : ℝ) : ℂ) := by
  rw [petersson, ← integral_complex_ofReal]
  simp [RCLike.mul_conj]

theorem re_petersson_self_nonneg (f : ℍ → ℂ) : 0 ≤ (petersson N f f).re := by
  rw [petersson_self, ofReal_re]
  exact setIntegral_nonneg_of_ae (.of_forall fun _ ↦ by positivity)

/-- **The Petersson product of two constants** is their product times the covolume
`[SL(2, ℤ) : Γ₀(N)] · π / 3`. In particular the constant `1` has squared norm `π / 3` at level `1`
(`petersson_one_one_level_one`). -/
theorem petersson_const_const [NeZero N] (c d : ℂ) :
    petersson N (fun _ ↦ c) (fun _ ↦ d) = c * conj d * ((Gamma0 N).index * Real.pi / 3 : ℝ) := by
  rw [petersson, setIntegral_const, Measure.real,
    ← isFundamentalDomain_dirichletDomain_gamma0PSL.covolume_eq_volume, covolume_gamma0PSL,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity),
    Complex.real_smul, mul_comm]
  ring_nf

/-- **The area of the level-one quotient as a Petersson norm**: at level `1` the constant `1` has
squared norm `π / 3`. -/
theorem petersson_one_one_level_one :
    petersson 1 (fun _ ↦ 1) (fun _ ↦ 1) = (Real.pi / 3 : ℝ) := by
  rw [petersson_const_const, Gamma0_one_top, Subgroup.index_top]
  simp [div_eq_mul_inv]

/-- **Positive definiteness**: a continuous square-integrable automorphic function has Petersson
norm `0` only if it vanishes identically. -/
theorem IsAutomorphic.petersson_self_eq_zero_iff (hf : IsAutomorphic N χ f) (hfc : Continuous f)
    (hf2 : IsSquareIntegrable N f) : petersson N f f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ petersson_zero_left 0⟩
  have hF := isFundamentalDomain_dirichletDomain_gamma0PSL (N := N)
  have hint := (hf.isSquareIntegrable_iff hF).mp hf2
  rw [petersson_self, ofReal_eq_zero, setIntegral_eq_zero_iff_of_nonneg_ae
    (.of_forall fun _ ↦ by positivity) hint] at h
  -- the set where `f` does not vanish is `PΓ₀(N)`-invariant and null on a fundamental domain
  have hnull : volume {z | f z ≠ 0} = 0 := by
    refine hF.measure_zero_of_invariant _ (fun σ ↦ ?_) ?_
    · ext z
      rw [mem_smul_set_iff_inv_smul_mem, mem_ofPred_eq, mem_ofPred_eq, ← norm_ne_zero_iff,
        Subgroup.smul_def, hf.norm_apply_smul (σ⁻¹).property, norm_ne_zero_iff]
    · rw [← Measure.restrict_apply (isOpen_ne_fun hfc continuous_const).measurableSet]
      exact measure_mono_null (fun z hz ↦ by simpa using hz) (ae_iff.mp h)
  exact (hfc.ae_eq_iff_eq volume continuous_zero).mp (ae_iff.mpr (by simpa using hnull))

/-- **Invariance under the normalizer.** If `σ ∈ PSL(2, ℝ)` normalizes `PΓ₀(N)`, the Petersson
product of two automorphic functions with the same nebentypus is unchanged by composing both
with `σ`. -/
theorem IsAutomorphic.petersson_comp_smul (hf : IsAutomorphic N χ f) (hg : IsAutomorphic N χ g)
    {σ : PSL(2, ℝ)} (hσ : ConjAct.toConjAct σ • gamma0PSL N = gamma0PSL N) :
    petersson N (fun z ↦ f (σ • z)) (fun z ↦ g (σ • z)) = petersson N f g := by
  have hF := isFundamentalDomain_dirichletDomain_gamma0PSL (N := N)
  have hσF : IsFundamentalDomain (gamma0PSL N) (σ • dirichletDomain (gamma0PSL N) (pt 0 2)) :=
    hF.smul_of_eq_conjAct_pointwise_smul
      (measurePreserving_smul σ⁻¹ volume).quasiMeasurePreserving hσ.symm
  rw [hf.petersson_eq_setIntegral hg hσF, petersson, ← image_smul,
    (measurePreserving_smul σ volume).setIntegral_image_emb (measurableEmbedding_const_smul σ)]

end TauCeti.MaassForms
