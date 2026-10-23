/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Continuity
public import TauCeti.RingTheory.Affinoid.MaximalSpectrum
public import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import TauCeti.Analysis.Normed.Unbundled.RootBound

/-!
# Point norms and the supremum seminorm of an affinoid algebra

Let `A` be a `K`-algebra over a complete nonarchimedean field `K`. For a maximal ideal `x` of `A`
and `f : A`, the value `|f(x)|` is the spectral norm over `K` of the residue of `f` in `A ⧸ x`.
When `A` is affinoid this residue field is finite over `K`, and the spectral norm is the unique
extension of the norm of `K` to it; no embedding into a chosen algebraic closure enters. The
supremum seminorm `|f|sup` is the supremum of `|f(x)|` over all classical points `x`, with value
zero for the zero algebra.

For an affinoid algebra the point norms are multiplicative, ultrametric and compatible with
scalars, and they are bounded by every complete ultrametric algebra norm on `A`. In particular
`|f|sup` is a finite, power-multiplicative ring seminorm, its kernel is the nilradical, algebra
homomorphisms of affinoid algebras do not increase it, and integral injective ones preserve it.
It is unchanged by passing to the reduction `A ⧸ nilradical A`, it is the maximum of its values on
the quotients by the finitely many minimal primes of `A`, and a monic equation
`f ^ d + ∑_{i < d} aᵢ f ^ i = 0` bounds it by `max_{i < d} |aᵢ|sup ^ (1 / (d - i))`.

The bound by a complete algebra norm uses automatic continuity,
`TauCeti.IsAffinoidAlgebra.continuous_algHom`, of the residue map into `A ⧸ x` with its spectral
norm, followed by the power-multiplicativity of the spectral norm. The kernel computation uses
that affinoid algebras are Jacobson rings.

## Main definitions

* `TauCeti.pointNorm`: the absolute value `|f(x)|` of `f : A` at a maximal ideal `x`.
* `TauCeti.supSeminorm`: the supremum seminorm `|f|sup`.
* `TauCeti.IsAffinoidAlgebra.supRingSeminorm`: `|·|sup` bundled as a ring seminorm.

## Main results

* `TauCeti.IsAffinoidAlgebra.pointNorm_le_norm`: `|f(x)| ≤ ‖f‖` for every complete ultrametric
  algebra norm on an affinoid algebra.
* `TauCeti.IsAffinoidAlgebra.bddAbove_range_pointNorm`: the point norms of `f` are bounded.
* `TauCeti.IsAffinoidAlgebra.isPowMul_supSeminorm`: `|f ^ n|sup = |f|sup ^ n` for `n ≥ 1`.
* `TauCeti.IsAffinoidAlgebra.supSeminorm_eq_zero_iff`: `|f|sup = 0` if and only if `f` is
  nilpotent.
* `TauCeti.IsAffinoidAlgebra.supSeminorm_map_le`: algebra homomorphisms contract `|·|sup`.
* `TauCeti.IsAffinoidAlgebra.supSeminorm_map_of_isIntegral`: integral injective algebra
  homomorphisms preserve `|·|sup`.
* `TauCeti.IsAffinoidAlgebra.supSeminorm_mk_nilradical`: `|·|sup` is unchanged by reduction.
* `TauCeti.IsAffinoidAlgebra.supSeminorm_eq_iSup_minimalPrimes`: `|f|sup` is the supremum of the
  supremum seminorms of the residues of `f` modulo the minimal primes of `A`.
* `TauCeti.IsAffinoidAlgebra.supSeminorm_le_iSup_coeff_rpow_of_eval_eq_zero`: the bound of
  `|f|sup` by the coefficients of a monic polynomial vanishing at `f`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§3.8 and
  6.2.1.
-/

public section

namespace AlgHom

/-- The spectral norm over `K` is invariant under `K`-algebra maps of fields. -/
theorem spectralNorm_map {K : Type*} [NontriviallyNormedField K] {E L : Type*} [Field E]
    [Algebra K E] [Field L] [Algebra K L] (ψ : E →ₐ[K] L) (y : E) :
    spectralNorm K L (ψ y) = spectralNorm K E y := by
  -- `spectralNorm K L y` is by definition `spectralValue (minpoly K y)`, and the injective map `ψ`
  -- preserves minimal polynomials.
  simp only [spectralNorm, minpoly.algHom_eq ψ (ψ : E →+* L).injective]

end AlgHom

namespace TauCeti

open Polynomial

variable {K : Type*} [NontriviallyNormedField K]
  {A : Type*} [CommRing A] [Algebra K A] {B : Type*} [CommRing B] [Algebra K B]

variable (K) in
/-- The absolute value `|f(x)|` of `f : A` at a maximal ideal `x`: the spectral norm over `K` of
the residue of `f` in the field `A ⧸ x`. For an affinoid algebra this residue field is finite
over `K`, and the spectral norm is the unique extension of the norm of `K` to it. -/
noncomputable def pointNorm (x : MaximalSpectrum A) (f : A) : ℝ :=
  letI := Ideal.Quotient.field x.asIdeal
  spectralNorm K (A ⧸ x.asIdeal) (Ideal.Quotient.mk x.asIdeal f)

variable (K) in
/-- The supremum seminorm `|f|sup` of `f : A`: the supremum of its absolute values `|f(x)|` at
the maximal ideals `x` of `A`. It is zero on the zero algebra, which has no maximal ideals. -/
noncomputable def supSeminorm (f : A) : ℝ :=
  ⨆ x : MaximalSpectrum A, pointNorm K x f

section PointNorm

theorem pointNorm_nonneg {x : MaximalSpectrum A} (f : A) : 0 ≤ pointNorm K x f := by
  let := Ideal.Quotient.field x.asIdeal
  exact spectralNorm_nonneg _

@[simp]
theorem pointNorm_algebraMap {x : MaximalSpectrum A} (c : K) :
    pointNorm K x (algebraMap K A c) = ‖c‖ := by
  let := Ideal.Quotient.field x.asIdeal
  rw [pointNorm, Ideal.Quotient.mk_algebraMap, spectralNorm_extends]

@[simp]
theorem pointNorm_zero {x : MaximalSpectrum A} : pointNorm K x 0 = 0 := by
  simpa using pointNorm_algebraMap (x := x) (0 : K)

@[simp]
theorem pointNorm_one {x : MaximalSpectrum A} : pointNorm K x 1 = 1 := by
  simpa using pointNorm_algebraMap (x := x) (1 : K)

/-- The absolute value at a classical point can be computed in any field `L` over `K` that
receives the residue field: if a `K`-algebra map `ψ : A → L` vanishes on `x`, then `|f(x)|` is
the spectral norm of `ψ f`. -/
theorem pointNorm_eq_spectralNorm {L : Type*} [Field L] [Algebra K L] {x : MaximalSpectrum A}
    {ψ : A →ₐ[K] L} (hψ : x.asIdeal ≤ RingHom.ker ψ) (f : A) :
    pointNorm K x f = spectralNorm K L (ψ f) := by
  -- `ψ` factors through the residue field.
  let := Ideal.Quotient.field x.asIdeal
  let ψ' : A ⧸ x.asIdeal →ₐ[K] L := Ideal.Quotient.liftₐ x.asIdeal ψ fun a ha ↦ hψ ha
  have h : ψ' (Ideal.Quotient.mk x.asIdeal f) = ψ f := Ideal.Quotient.lift_mk _ _ _
  rw [pointNorm, ← h, ψ'.spectralNorm_map]

/-- The absolute value at a classical point is unchanged by pulling the point back along an
algebra map into an affinoid algebra. -/
@[simp]
theorem IsAffinoidAlgebra.pointNorm_maximalSpectrumComap [IsUltrametricDist K] [CompleteSpace K]
    (hB : IsAffinoidAlgebra K B) (φ : A →ₐ[K] B) (x : MaximalSpectrum B)
    (a : A) : pointNorm K (hB.maximalSpectrumComap φ x) a = pointNorm K x (φ a) := by
  let := Ideal.Quotient.field x.asIdeal
  let q := Ideal.Quotient.mkₐ K x.asIdeal
  rw [pointNorm_eq_spectralNorm (ψ := q.comp φ)
      (fun b hb ↦ by simpa [q, Ideal.Quotient.eq_zero_iff_mem] using hb),
    pointNorm_eq_spectralNorm (x := x) (ψ := q)
      (fun b hb ↦ by simpa [q, Ideal.Quotient.eq_zero_iff_mem] using hb),
    AlgHom.comp_apply]

namespace IsAffinoidAlgebra

variable [IsUltrametricDist K] [CompleteSpace K]

/-- The residue field at a classical point of an affinoid algebra is algebraic over `K`. -/
private theorem isAlgebraic_quotient (hA : IsAffinoidAlgebra K A) (x : MaximalSpectrum A) :
    Algebra.IsAlgebraic K (A ⧸ x.asIdeal) := by
  have := hA.finite_quotient_of_isMaximal x.asIdeal
  infer_instance

/-- The absolute value `|f(x)|` vanishes exactly when `f` lies in the maximal ideal `x`. -/
theorem pointNorm_eq_zero_iff (hA : IsAffinoidAlgebra K A) {x : MaximalSpectrum A} {f : A} :
    pointNorm K x f = 0 ↔ f ∈ x.asIdeal := by
  let := Ideal.Quotient.field x.asIdeal
  have := hA.isAlgebraic_quotient x
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨fun h ↦ eq_zero_of_map_spectralNorm_eq_zero h (Algebra.IsAlgebraic.isAlgebraic _),
    fun h ↦ ?_⟩
  rw [pointNorm, h, spectralNorm_zero]

/-- The absolute value at a classical point is multiplicative:
`|(f * g)(x)| = |f(x)| * |g(x)|`. -/
theorem pointNorm_mul (hA : IsAffinoidAlgebra K A) (x : MaximalSpectrum A) (f g : A) :
    pointNorm K x (f * g) = pointNorm K x f * pointNorm K x g := by
  let := Ideal.Quotient.field x.asIdeal
  have := hA.isAlgebraic_quotient x
  -- The spectral norm is multiplicative as the bundled `spectralMulAlgNorm`.
  simp only [pointNorm, map_mul, ← spectralMulAlgNorm_def]

/-- `|(f ^ n)(x)| = |f(x)| ^ n` at every classical point `x`. -/
theorem pointNorm_pow (hA : IsAffinoidAlgebra K A) (x : MaximalSpectrum A) (f : A) (n : ℕ) :
    pointNorm K x (f ^ n) = pointNorm K x f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, hA.pointNorm_mul, ih, pow_succ]

/-- The absolute value at a classical point is homogeneous for scalars of `K`:
`|(c • f)(x)| = ‖c‖ * |f(x)|`. -/
theorem pointNorm_smul (hA : IsAffinoidAlgebra K A) (x : MaximalSpectrum A) (c : K) (f : A) :
    pointNorm K x (c • f) = ‖c‖ * pointNorm K x f := by
  rw [Algebra.smul_def, hA.pointNorm_mul, pointNorm_algebraMap]

@[simp]
theorem pointNorm_neg (hA : IsAffinoidAlgebra K A) (x : MaximalSpectrum A) (f : A) :
    pointNorm K x (-f) = pointNorm K x f := by
  let := Ideal.Quotient.field x.asIdeal
  have := hA.isAlgebraic_quotient x
  simp only [pointNorm, map_neg]
  exact spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)

/-- The absolute value at a classical point is ultrametric. -/
theorem pointNorm_add_le (hA : IsAffinoidAlgebra K A) (x : MaximalSpectrum A) (f g : A) :
    pointNorm K x (f + g) ≤ max (pointNorm K x f) (pointNorm K x g) := by
  let := Ideal.Quotient.field x.asIdeal
  have := hA.isAlgebraic_quotient x
  simp only [pointNorm, map_add]
  exact isNonarchimedean_spectralNorm _ _

/-- A surjective algebra map from a completely normed affinoid algebra onto a finite field
extension of `K` does not increase norms, for the spectral norm of the extension. It is stated
for an abstract field `L`, since the residue field `A ⧸ x` already carries the quotient norm of
`A`, which differs from the spectral norm used here. -/
private theorem spectralNorm_le_norm {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [IsUltrametricDist A] [CompleteSpace A] (hA : IsAffinoidAlgebra K A) {L : Type*} [Field L]
    [Algebra K L] [FiniteDimensional K L] (φ : A →ₐ[K] L) (hφ : Function.Surjective φ) (f : A) :
    spectralNorm K L (φ f) ≤ ‖f‖ := by
  have := hA.isNoetherianRing
  let : NormedField L := spectralNorm.normedField K L
  let : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  have : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun a b ↦
      isNonarchimedean_spectralNorm (K := K) (L := L) a b
  have : CompleteSpace L := FiniteDimensional.complete K L
  have hc : Continuous φ := (hA.of_surjective φ hφ).continuous_algHom φ
  let q : A →L[K] L := { toLinearMap := φ.toLinearMap, cont := hc }
  have hq : (φ : A →+* L).IsBounded :=
    ⟨max ‖q‖ 1, lt_max_of_lt_right one_pos, fun a ↦
      (q.le_opNorm a).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg a))⟩
  exact contraction_of_isPowMul (β := L) isPowMul_spectralNorm hq f

/-- **Point norms are bounded by complete algebra norms.** On an affinoid algebra with a complete
ultrametric algebra norm, `|f(x)| ≤ ‖f‖` at every classical point `x`. -/
theorem pointNorm_le_norm {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [IsUltrametricDist A] [CompleteSpace A] (hA : IsAffinoidAlgebra K A) (x : MaximalSpectrum A)
    (f : A) : pointNorm K x f ≤ ‖f‖ := by
  -- The residue map is continuous by automatic continuity, and the spectral norm is
  -- power-multiplicative.
  let := Ideal.Quotient.field x.asIdeal
  have : FiniteDimensional K (A ⧸ x.asIdeal) := hA.finite_quotient_of_isMaximal x.asIdeal
  exact hA.spectralNorm_le_norm (Ideal.Quotient.mkₐ K x.asIdeal)
    (Ideal.Quotient.mkₐ_surjective K x.asIdeal) f

end IsAffinoidAlgebra

end PointNorm

section SupSeminorm

theorem supSeminorm_eq_iSup (f : A) : supSeminorm K f = ⨆ x : MaximalSpectrum A, pointNorm K x f :=
  (rfl)

theorem supSeminorm_nonneg (f : A) : 0 ≤ supSeminorm K f :=
  Real.iSup_nonneg fun _ ↦ pointNorm_nonneg f

/-- A nonnegative bound for all point norms bounds the supremum seminorm. -/
theorem supSeminorm_le {f : A} {r : ℝ} (hr : 0 ≤ r) (h : ∀ x, pointNorm K x f ≤ r) :
    supSeminorm K f ≤ r :=
  Real.iSup_le h hr

/-- The supremum seminorm vanishes on the zero algebra, which has no maximal ideals. -/
theorem supSeminorm_eq_zero_of_subsingleton [Subsingleton A] (f : A) : supSeminorm K f = 0 := by
  have : IsEmpty (MaximalSpectrum A) := ⟨fun x ↦ x.isMaximal.ne_top (Subsingleton.elim _ _)⟩
  exact Real.iSup_of_isEmpty _

@[simp]
theorem supSeminorm_zero : supSeminorm K (0 : A) = 0 := by
  simp [supSeminorm]

@[simp]
theorem supSeminorm_algebraMap [Nontrivial A] (c : K) :
    supSeminorm K (algebraMap K A c) = ‖c‖ := by
  simp [supSeminorm]

@[simp]
theorem supSeminorm_one [Nontrivial A] : supSeminorm K (1 : A) = 1 := by
  simp [supSeminorm]

namespace IsAffinoidAlgebra

variable [IsUltrametricDist K] [CompleteSpace K]

/-- **Boundedness of point norms.** The absolute values of an element of an affinoid algebra at
its classical points are bounded. -/
theorem bddAbove_range_pointNorm (hA : IsAffinoidAlgebra K A) (f : A) :
    BddAbove (Set.range fun x : MaximalSpectrum A ↦ pointNorm K x f) := by
  -- For a Tate presentation `π`, the point norms of `π t` are bounded by the Gauss norm of `t`.
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
  obtain ⟨t, rfl⟩ := hπ f
  refine ⟨‖t‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  dsimp only
  rw [← hA.pointNorm_maximalSpectrumComap π x t]
  exact (isAffinoidAlgebra_tate (K := K) (σ := Fin n)).pointNorm_le_norm _ t

/-- Each absolute value `|f(x)|` is bounded by the supremum seminorm `|f|sup`. -/
theorem pointNorm_le_supSeminorm (hA : IsAffinoidAlgebra K A) (x : MaximalSpectrum A) (f : A) :
    pointNorm K x f ≤ supSeminorm K f :=
  le_ciSup (hA.bddAbove_range_pointNorm f) x

theorem supSeminorm_le_iff (hA : IsAffinoidAlgebra K A) {f : A} {r : ℝ} (hr : 0 ≤ r) :
    supSeminorm K f ≤ r ↔ ∀ x, pointNorm K x f ≤ r :=
  ⟨fun h x ↦ (hA.pointNorm_le_supSeminorm x f).trans h, supSeminorm_le hr⟩

/-- The supremum seminorm is bounded by every complete ultrametric algebra norm. -/
theorem supSeminorm_le_norm {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [IsUltrametricDist A] [CompleteSpace A] (hA : IsAffinoidAlgebra K A) (f : A) :
    supSeminorm K f ≤ ‖f‖ :=
  supSeminorm_le (norm_nonneg f) fun x ↦ hA.pointNorm_le_norm x f

/-- The supremum seminorm is submultiplicative: `|f * g|sup ≤ |f|sup * |g|sup`. -/
theorem supSeminorm_mul_le (hA : IsAffinoidAlgebra K A) (f g : A) :
    supSeminorm K (f * g) ≤ supSeminorm K f * supSeminorm K g :=
  supSeminorm_le (mul_nonneg (supSeminorm_nonneg f) (supSeminorm_nonneg g)) fun x ↦ by
    rw [hA.pointNorm_mul]
    exact mul_le_mul (hA.pointNorm_le_supSeminorm x f) (hA.pointNorm_le_supSeminorm x g)
      (pointNorm_nonneg g) (supSeminorm_nonneg f)

/-- The supremum seminorm is ultrametric. -/
theorem supSeminorm_add_le (hA : IsAffinoidAlgebra K A) (f g : A) :
    supSeminorm K (f + g) ≤ max (supSeminorm K f) (supSeminorm K g) :=
  supSeminorm_le ((supSeminorm_nonneg f).trans (le_max_left _ _)) fun x ↦
    (hA.pointNorm_add_le x f g).trans
      (max_le_max (hA.pointNorm_le_supSeminorm x f) (hA.pointNorm_le_supSeminorm x g))

/-- The supremum seminorm is nonarchimedean. -/
theorem isNonarchimedean_supSeminorm (hA : IsAffinoidAlgebra K A) :
    IsNonarchimedean (supSeminorm K : A → ℝ) :=
  hA.supSeminorm_add_le

@[simp]
theorem supSeminorm_neg (hA : IsAffinoidAlgebra K A) (f : A) :
    supSeminorm K (-f) = supSeminorm K f := by
  simp only [supSeminorm, hA.pointNorm_neg]

/-- The supremum seminorm is homogeneous for scalars of `K`: `|c • f|sup = ‖c‖ * |f|sup`. -/
theorem supSeminorm_smul (hA : IsAffinoidAlgebra K A) (c : K) (f : A) :
    supSeminorm K (c • f) = ‖c‖ * supSeminorm K f := by
  simp only [supSeminorm, hA.pointNorm_smul, Real.mul_iSup_of_nonneg (norm_nonneg c)]

/-- `|f ^ n|sup = |f|sup ^ n` for `n ≠ 0`, including on the zero algebra. For `n = 0` the
statement fails on the zero algebra. -/
theorem supSeminorm_pow (hA : IsAffinoidAlgebra K A) (f : A) {n : ℕ} (hn : n ≠ 0) :
    supSeminorm K (f ^ n) = supSeminorm K f ^ n := by
  simp only [supSeminorm, hA.pointNorm_pow,
    Real.iSup_pow_of_ne_zero (fun _ ↦ pointNorm_nonneg f) hn]

/-- The supremum seminorm of an affinoid algebra is power-multiplicative:
`|f ^ n|sup = |f|sup ^ n` for `n ≥ 1`. -/
theorem isPowMul_supSeminorm (hA : IsAffinoidAlgebra K A) :
    IsPowMul (supSeminorm K : A → ℝ) :=
  fun f _ hn ↦ hA.supSeminorm_pow f (Nat.one_le_iff_ne_zero.mp hn)

/-- The supremum seminorm of an affinoid algebra vanishes exactly on the elements lying in every
maximal ideal. -/
theorem supSeminorm_eq_zero_iff_forall_mem (hA : IsAffinoidAlgebra K A) {f : A} :
    supSeminorm K f = 0 ↔ ∀ x : MaximalSpectrum A, f ∈ x.asIdeal := by
  simp_rw [← hA.pointNorm_eq_zero_iff]
  constructor
  · intro h x
    exact le_antisymm (h ▸ hA.pointNorm_le_supSeminorm x f) (pointNorm_nonneg f)
  · intro h
    exact le_antisymm (supSeminorm_le le_rfl fun x ↦ (h x).le) (supSeminorm_nonneg f)

/-- **The kernel of the supremum seminorm is the nilradical.** An element of an affinoid algebra
has supremum seminorm zero exactly when it is nilpotent, since an affinoid algebra is a Jacobson
ring. -/
theorem supSeminorm_eq_zero_iff (hA : IsAffinoidAlgebra K A) {f : A} :
    supSeminorm K f = 0 ↔ IsNilpotent f := by
  have := hA.isJacobsonRing
  rw [hA.supSeminorm_eq_zero_iff_forall_mem]
  refine ⟨fun h ↦ ?_, fun h x ↦ nilpotent_iff_mem_prime.mp h _ x.isMaximal.isPrime⟩
  -- An element of every maximal ideal lies in the Jacobson radical `jacobson ⊥`, which in a
  -- Jacobson ring is the radical of `⊥`.
  have hf : f ∈ Ring.jacobson A := by
    rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]
    exact fun m hm ↦ h ⟨m, hm⟩
  rw [← Ideal.jacobson_bot, ← Ideal.radical_eq_jacobson, Ideal.mem_radical_iff] at hf
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, Ideal.mem_bot.mp hn⟩

/-- An algebra homomorphism of affinoid algebras does not increase supremum seminorms. -/
theorem supSeminorm_map_le (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (φ : A →ₐ[K] B) (a : A) : supSeminorm K (φ a) ≤ supSeminorm K a :=
  supSeminorm_le (supSeminorm_nonneg a) fun x ↦ by
    rw [← hB.pointNorm_maximalSpectrumComap φ x a]
    exact hA.pointNorm_le_supSeminorm _ a

/-- An integral injective algebra homomorphism into an affinoid algebra preserves supremum
seminorms, since every classical point of the source lifts to the target. -/
theorem supSeminorm_map_of_isIntegral (hB : IsAffinoidAlgebra K B) (φ : A →ₐ[K] B)
    (hφ : φ.toRingHom.IsIntegral) (hφi : Function.Injective φ) (a : A) :
    supSeminorm K (φ a) = supSeminorm K a := by
  simp only [supSeminorm, ← hB.pointNorm_maximalSpectrumComap φ]
  exact (hB.maximalSpectrumComap_surjective φ hφ hφi).iSup_comp (pointNorm K · a)

/-- At a classical point `x` of `A` containing the kernel of a surjective algebra map
`φ : A → B` onto an affinoid algebra, `|a(x)| ≤ |φ a|sup`: the point `x` comes from a classical
point of `B`. -/
theorem pointNorm_le_supSeminorm_map (hB : IsAffinoidAlgebra K B) {φ : A →ₐ[K] B}
    (hφ : Function.Surjective φ) {x : MaximalSpectrum A} (hx : RingHom.ker φ ≤ x.asIdeal)
    (a : A) : pointNorm K x a ≤ supSeminorm K (φ a) := by
  have hmap : (x.asIdeal.map φ).comap φ = x.asIdeal := by
    rw [Ideal.comap_map_of_surjective' φ hφ, sup_eq_left.mpr hx]
  have hy : (x.asIdeal.map φ).IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective φ hφ x.isMaximal).resolve_left
      fun h ↦ x.isMaximal.ne_top ?_
    rw [← hmap, h, Ideal.comap_top]
  have hxy : hB.maximalSpectrumComap φ ⟨_, hy⟩ = x := by
    ext1
    rw [maximalSpectrumComap_asIdeal, hmap]
  rw [← hxy, hB.pointNorm_maximalSpectrumComap]
  exact hB.pointNorm_le_supSeminorm _ _

/-- A surjective algebra map of affinoid algebras whose kernel consists of nilpotent elements
preserves supremum seminorms, since every classical point of the source contains the kernel. -/
theorem supSeminorm_map_of_ker_le_nilradical (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) {φ : A →ₐ[K] B} (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ ≤ nilradical A) (a : A) : supSeminorm K (φ a) = supSeminorm K a :=
  le_antisymm (hA.supSeminorm_map_le hB φ a) <| supSeminorm_le (supSeminorm_nonneg _) fun x ↦
    hB.pointNorm_le_supSeminorm_map hφ
      (hker.trans (nilradical_le_prime x.asIdeal)) a

/-- **The supremum seminorm is unchanged by reduction**: `|f|sup` is the same in `A` and in its
reduction `A ⧸ nilradical A`. -/
theorem supSeminorm_mk_nilradical (hA : IsAffinoidAlgebra K A) (f : A) :
    supSeminorm K (Ideal.Quotient.mk (nilradical A) f) = supSeminorm K f :=
  hA.supSeminorm_map_of_ker_le_nilradical (hA.quotient _)
    (φ := Ideal.Quotient.mkₐ K (nilradical A)) (Ideal.Quotient.mkₐ_surjective K _)
    (Ideal.Quotient.mkₐ_ker K _).le f

/-- **The supremum seminorm is computed on minimal-prime quotients.** On an affinoid algebra,
`|f|sup` is the supremum, over the finitely many minimal primes `𝔭` of `A`, of the supremum
seminorm of the residue of `f` in the affinoid domain `A ⧸ 𝔭`. -/
theorem supSeminorm_eq_iSup_minimalPrimes (hA : IsAffinoidAlgebra K A) (f : A) :
    supSeminorm K f = ⨆ 𝔭 : minimalPrimes A, supSeminorm K (Ideal.Quotient.mk 𝔭.1 f) := by
  have := hA.isNoetherianRing
  have : Finite (minimalPrimes A) := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  refine le_antisymm (supSeminorm_le (Real.iSup_nonneg fun _ ↦ supSeminorm_nonneg _) fun x ↦ ?_)
    (Real.iSup_le (fun 𝔭 ↦ hA.supSeminorm_map_le (hA.quotient 𝔭.1)
      (Ideal.Quotient.mkₐ K 𝔭.1) f) (supSeminorm_nonneg f))
  -- Every classical point lies on the closed subspace of some minimal prime.
  obtain ⟨𝔭, h𝔭, h𝔭x⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ x.asIdeal)
  refine (hA.quotient 𝔭).pointNorm_le_supSeminorm_map (φ := Ideal.Quotient.mkₐ K 𝔭)
    (Ideal.Quotient.mkₐ_surjective K 𝔭) ((Ideal.Quotient.mkₐ_ker K 𝔭).trans_le h𝔭x) f |>.trans ?_
  exact le_ciSup (f := fun 𝔮 : minimalPrimes A ↦ supSeminorm K (Ideal.Quotient.mk 𝔮.1 f))
    (Set.finite_range _).bddAbove ⟨𝔭, h𝔭⟩

/-- On a nonzero affinoid algebra the supremum seminorm `|f|sup` is attained on the quotient by
one of its minimal primes. -/
theorem exists_mem_minimalPrimes_supSeminorm_eq [Nontrivial A] (hA : IsAffinoidAlgebra K A)
    (f : A) : ∃ 𝔭 ∈ minimalPrimes A, supSeminorm K (Ideal.Quotient.mk 𝔭 f) = supSeminorm K f := by
  have := hA.isNoetherianRing
  have : Finite (minimalPrimes A) := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  have : Nonempty (minimalPrimes A) := Ideal.nonempty_minimalPrimes bot_ne_top
  obtain ⟨𝔭, h𝔭⟩ := exists_eq_ciSup_of_finite
    (f := fun 𝔮 : minimalPrimes A ↦ supSeminorm K (Ideal.Quotient.mk 𝔮.1 f))
  exact ⟨𝔭.1, 𝔭.2, h𝔭.trans (hA.supSeminorm_eq_iSup_minimalPrimes f).symm⟩

/-- The supremum seminorm of an affinoid algebra, bundled as a ring seminorm. -/
noncomputable def supRingSeminorm (hA : IsAffinoidAlgebra K A) : RingSeminorm A where
  toFun := supSeminorm K
  map_zero' := supSeminorm_zero
  add_le' f g := (hA.supSeminorm_add_le f g).trans
    (max_le_add_of_nonneg (supSeminorm_nonneg f) (supSeminorm_nonneg g))
  neg' := hA.supSeminorm_neg
  mul_le' := hA.supSeminorm_mul_le

@[simp]
theorem coe_supRingSeminorm (hA : IsAffinoidAlgebra K A) :
    ⇑hA.supRingSeminorm = supSeminorm K :=
  (rfl)

/-- **Integral equations bound the supremum seminorm.** If `f` is a root of a monic polynomial
`p = X ^ d + ∑_{i < d} aᵢ X ^ i` over an affinoid algebra, then
`|f|sup ≤ max_{i < d} |aᵢ|sup ^ (1 / (d - i))`. -/
theorem supSeminorm_le_iSup_coeff_rpow_of_eval_eq_zero (hA : IsAffinoidAlgebra K A)
    {p : A[X]} (hp : p.Monic) {f : A} (hf : p.eval f = 0) :
    supSeminorm K f ≤
      ⨆ i : Fin p.natDegree, supSeminorm K (p.coeff i) ^ (1 / (p.natDegree - i : ℝ)) := by
  have hpm : IsPowMul hA.supRingSeminorm := by
    rw [coe_supRingSeminorm]
    exact hA.isPowMul_supSeminorm
  have hna : IsNonarchimedean hA.supRingSeminorm := by
    rw [coe_supRingSeminorm]
    exact hA.isNonarchimedean_supSeminorm
  simpa only [coe_supRingSeminorm] using
    hp.apply_le_iSup_apply_coeff_rpow_of_eval_eq_zero hpm hna hf

end IsAffinoidAlgebra

end SupSeminorm

end TauCeti
