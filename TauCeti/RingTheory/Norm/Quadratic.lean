/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.FieldTheory.Galois.Basic
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.Matrix.Charpoly.FinTwo
public import TauCeti.RingTheory.Norm.Units

/-!
# Trace and norm in quadratic algebras and separable quadratic extensions

For a separable quadratic extension `L/K` the trace and norm are the two elementary symmetric
functions of the pair `{x, σx}`, where `σ` is the nontrivial automorphism: `tr x = x + σx` and
`N x = x · σx` (`algebraMap_trace_eq_add`, `algebraMap_norm_eq_mul`). These give the
discriminant characterisation of the generators:

* `discrim_eq_zero_iff_mem_range_algebraMap`: the discriminant `t² - 4n` of `X² - tX + n`, the
  characteristic polynomial of multiplication by `θ`, vanishes exactly when `θ ∈ K`. (That
  polynomial is the *minimal* polynomial of `θ` precisely when `θ ∉ K`, which is what the
  statement says.) Forwards the discriminant equals `(θ - σθ)²`, so it vanishes only where `σ`
  fixes `θ`; `discrim_ne_zero` is the contrapositive, kept separately because it is the
  direction consumers use;
* `exists_discrim_ne_zero` turns that into a choice principle: some `θ` has nonzero
  discriminant, hence generates. This is what a construction over `L/K` picks its generator by.

Three results hold for a commutative quadratic algebra over any nontrivial commutative base
ring `K`, including bases with zero divisors. `Algebra.IsQuadraticExtension K L` supplies
freeness and rank two; module-finiteness follows from the positive rank. No Euclidean division,
domain, or separability hypothesis is needed. This covers quadratic orders over `ℤ`, the split
algebra `K × K`, and the non-reduced `K[X]/(X²)`:

* `trace_algebraMap_add_algebraMap_mul` and `norm_algebraMap_add_algebraMap_mul` evaluate the
  trace and norm of `b + aθ` — the first by `K`-linearity of the trace, the second from the
  `2 × 2` identity `det (b • 1 + a • M) = b² + ab · tr M + a² · det M`. This is how a statement
  about one generator transfers to another;
* `discrim_eq_zero_of_mem_range_algebraMap`, the easy half of the characterisation: a scalar
  `θ = c` has `t = 2c` and `n = c²`, so `t² - 4n = 0`.

`Module.Basis.norm_eq_of_apply_zero_eq_one` reads the norm formula in the coordinates of a basis
`(1, θ)`: the norm of `x + y θ` is the binary form `x² + x y Tr(θ) + y² N(θ)`.

Separability is genuinely needed for the other half, and hence for `discrim_ne_zero` and
`exists_discrim_ne_zero`: over a purely inseparable quadratic extension the trace form vanishes,
so `t = 0` and `t² - 4n = 0` for *every* `θ`. In characteristic two `discrim_ne_zero` says
`t ≠ 0`, reflecting that a separable quadratic extension is then Artin–Schreier rather than
Kummer.

These formulas support quadratic twists and computations of norms in quadratic number fields.
The nonzero-discriminant criterion selects a generator for a separable quadratic extension
and ensures that twisting by that generator preserves ellipticity.

Over a base field, an element `θ ∉ K` with `θ² + t θ + c = 0` has characteristic polynomial
`X² + t X + c`, in every commutative quadratic algebra, so `Tr θ = -t` and `N θ = c`
(`trace_eq_neg_of_sq_add_mul_add_eq_zero`, `norm_eq_of_sq_add_mul_add_eq_zero`). In particular a
square root `x` of `d ∈ K` with `x ∉ K` has characteristic polynomial `X² - d`:

* `trace_eq_zero_of_sq_eq` and `norm_eq_neg_of_sq_eq`: `Tr x = 0` and `N x = -d`;
* `trace_algebraMap_add_algebraMap_mul_of_sq_eq` and
  `norm_algebraMap_add_algebraMap_mul_of_sq_eq`: in square-root coordinates
  `Tr (b + a x) = 2b` and `N (b + a x) = b² - a² d`.

In a quadratic field extension `trace_inv` gives `Tr (a⁻¹) = Tr a / N a`, with no separability
hypothesis. These are the inputs to the diagonalization of the twisted trace forms
`y ↦ Tr (a y²)` of a quadratic extension.

`TauCeti.mem_normGroup_iff_exists_sq_sub_mul_sq` identifies the field norm group in
square-root coordinates with the values `u² - d v²`. This connects norm equations to
field-theoretic norm and ramification criteria.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/RingTheory/Norm/Quadratic.lean` at revision `bc2fe8ff7396`, FLT PR #1088,
Apache 2.0). That file's own header reads `Authors: Kevin Buzzard, Claude`; following this
repository's convention for adapted material, the upstream authorship is credited here rather
than in the copyright header. The root and square-root lemmas and `trace_inv` are not part of the
adapted material.
-/

public section

section CommRing

variable (K L : Type*) [CommRing K] [Nontrivial K] [CommRing L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L]

namespace Algebra.IsQuadraticExtension

/-- The trace of `b + aθ` in a commutative quadratic algebra over a nontrivial commutative
ring is `a·tr(θ) + 2b`. Neither separability nor invertibility in `L` is needed. -/
@[simp]
theorem trace_algebraMap_add_algebraMap_mul (a b : K) (θ : L) :
    Algebra.trace K L (algebraMap K L b + algebraMap K L a * θ)
      = a * Algebra.trace K L θ + 2 * b := by
  rw [map_add, Algebra.trace_algebraMap, ← Algebra.smul_def, map_smul,
    Algebra.IsQuadraticExtension.finrank_eq_two]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- The norm of `b + aθ` in a commutative quadratic algebra over a nontrivial commutative
ring is `b² + ab·tr(θ) + a²·N(θ)`. Neither separability nor invertibility in `L` is needed. -/
@[simp]
theorem norm_algebraMap_add_algebraMap_mul (a b : K) (θ : L) :
    Algebra.norm K (algebraMap K L b + algebraMap K L a * θ)
      = b ^ 2 + a * b * Algebra.trace K L θ + a ^ 2 * Algebra.norm K θ := by
  classical
  let bs : Module.Basis (Fin 2) K L :=
    Module.finBasisOfFinrankEq K L (finrank_eq_two K L)
  have key : Algebra.leftMulMatrix bs (algebraMap K L b + algebraMap K L a * θ)
      = a • Algebra.leftMulMatrix bs θ - (-b) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [neg_smul, sub_neg_eq_add, add_comm, map_add, map_mul, AlgHom.commutes, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one, Algebra.smul_def]
    simp [Algebra.smul_def]
  rw [Algebra.norm_eq_matrix_det bs, Algebra.trace_eq_matrix_trace bs,
    Algebra.norm_eq_matrix_det bs, key, TauCeti.Matrix.det_smul_sub_smul_one_fin_two]
  ring

/-- The discriminant vanishes on the image of the base ring in a commutative quadratic algebra:
a scalar `c` has trace `2c` and norm `c²`. This includes split and non-reduced algebras.
For a separable quadratic field extension, the converse is
`discrim_eq_zero_iff_mem_range_algebraMap`. -/
theorem discrim_eq_zero_of_mem_range_algebraMap {θ : L} (hθ : θ ∈ Set.range (algebraMap K L)) :
    Algebra.trace K L θ ^ 2 - 4 * Algebra.norm K θ = 0 := by
  obtain ⟨c, rfl⟩ := hθ
  rw [Algebra.trace_algebraMap, Algebra.norm_algebraMap, finrank_eq_two K L]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

end Algebra.IsQuadraticExtension

end CommRing

namespace Module.Basis

variable {K L : Type*} [CommRing K] [Nontrivial K] [CommRing L] [Algebra K L]

/-- **The norm form of a basis `(1, θ)`.** For a basis `B` of a commutative algebra `L` over a
nontrivial commutative ring `K` with `B 0 = 1` and `θ = B 1`, the norm of `w = x + y θ` is
`x² + x y Tr(θ) + y² N(θ)`. -/
theorem norm_eq_of_apply_zero_eq_one (B : Module.Basis (Fin 2) K L) (hB : B 0 = 1) (w : L) :
    Algebra.norm K w = B.repr w 0 ^ 2 + B.repr w 0 * B.repr w 1 * Algebra.trace K L (B 1) +
      B.repr w 1 ^ 2 * Algebra.norm K (B 1) := by
  have : Algebra.IsQuadraticExtension K L :=
    { toFree := .of_basis B
      finrank_eq_two' := by rw [Module.finrank_eq_card_basis B, Fintype.card_fin] }
  conv_lhs => rw [← B.sum_repr w]
  rw [Fin.sum_univ_two, hB, Algebra.smul_def, Algebra.smul_def, mul_one,
    Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul]
  ring

end Module.Basis

section SquareRoot

variable {K L : Type*} [Field K] [CommRing L] [Algebra K L] [Algebra.IsQuadraticExtension K L]

namespace Algebra.IsQuadraticExtension

/-- In a commutative quadratic algebra over a field, a root `θ ∉ K` of `X² + t X + c` has trace
`-t`. -/
theorem trace_eq_neg_of_sq_add_mul_add_eq_zero {θ : L} (hθ : θ ∉ Set.range (algebraMap K L))
    {t c : K} (h : θ ^ 2 + algebraMap K L t * θ + algebraMap K L c = 0) :
    Algebra.trace K L θ = -t := by
  -- By Cayley–Hamilton `θ² = Tr θ · θ - N θ`; comparing with `h` and using that `1, θ` are
  -- linearly independent forces `Tr θ = -t`.
  by_contra hne
  have hsq := sq_eq_trace_smul_sub_norm K θ
  rw [Algebra.smul_def] at hsq
  have key : algebraMap K L (Algebra.trace K L θ + t) * θ =
      algebraMap K L (Algebra.norm K θ - c) := by
    rw [map_add, map_sub]
    linear_combination h - hsq
  have hne' : Algebra.trace K L θ + t ≠ 0 := fun h0 ↦ hne (by linear_combination h0)
  refine hθ ⟨(Algebra.trace K L θ + t)⁻¹ * (Algebra.norm K θ - c), ?_⟩
  rw [map_mul, ← key, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hne', map_one, one_mul]

/-- In a commutative quadratic algebra over a field, a root `θ ∉ K` of `X² + t X + c` has norm
`c`: its characteristic polynomial `X² - Tr θ · X + N θ` is `X² + t X + c`. -/
theorem norm_eq_of_sq_add_mul_add_eq_zero {θ : L} (hθ : θ ∉ Set.range (algebraMap K L))
    {t c : K} (h : θ ^ 2 + algebraMap K L t * θ + algebraMap K L c = 0) :
    Algebra.norm K θ = c := by
  have := Module.nontrivial_of_finrank_eq_succ (finrank_eq_two K L)
  have hsq := sq_eq_trace_smul_sub_norm K θ
  rw [Algebra.smul_def, trace_eq_neg_of_sq_add_mul_add_eq_zero hθ h, map_neg] at hsq
  have key : algebraMap K L (Algebra.norm K θ - c) = 0 := by
    rw [map_sub]
    linear_combination hsq - h
  exact sub_eq_zero.mp ((map_eq_zero_iff _ (algebraMap K L).injective).mp key)

/-- A square root `x` of an element of the base field, lying outside the base field, has trace
zero. This holds in every commutative quadratic algebra over a field, including split and
nonreduced ones; for field extensions of any finite degree it is
`TauCeti.Algebra.trace_eq_zero_of_sq_algebraMap_of_not_mem_range`. -/
theorem trace_eq_zero_of_sq_eq {x : L} {d : K} (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L d) : Algebra.trace K L x = 0 := by
  simpa using trace_eq_neg_of_sq_add_mul_add_eq_zero (t := 0) (c := -d) hx (by simp [hx2])

/-- A square root `x` of `d`, lying outside the base field, has norm `-d`: its characteristic
polynomial `X² - Tr x · X + N x` is `X² - d`. -/
theorem norm_eq_neg_of_sq_eq {x : L} {d : K} (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L d) : Algebra.norm K x = -d :=
  norm_eq_of_sq_add_mul_add_eq_zero (t := 0) hx (by simp [hx2])

/-- The trace in square-root coordinates: if `x² = d` with `x ∉ K`, then
`Tr (b + a x) = 2 b`. -/
theorem trace_algebraMap_add_algebraMap_mul_of_sq_eq {x : L} {d : K}
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L d) (a b : K) :
    Algebra.trace K L (algebraMap K L b + algebraMap K L a * x) = 2 * b := by
  rw [trace_algebraMap_add_algebraMap_mul, trace_eq_zero_of_sq_eq hx hx2, mul_zero, zero_add]

/-- The norm in square-root coordinates: if `x² = d` with `x ∉ K`, then
`N (b + a x) = b² - a² d`. -/
theorem norm_algebraMap_add_algebraMap_mul_of_sq_eq {x : L} {d : K}
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L d) (a b : K) :
    Algebra.norm K (algebraMap K L b + algebraMap K L a * x) = b ^ 2 - a ^ 2 * d := by
  rw [norm_algebraMap_add_algebraMap_mul, trace_eq_zero_of_sq_eq hx hx2,
    norm_eq_neg_of_sq_eq hx hx2]
  ring

end Algebra.IsQuadraticExtension

end SquareRoot

section QuadraticField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L]

namespace Algebra.IsQuadraticExtension

/-- In a quadratic field extension, `Tr (a⁻¹) = Tr a / N a`. Both sides vanish at `a = 0`, so
no hypothesis is needed. This computes the values of twisted trace forms `y ↦ Tr (a y²)` at
elements such as `a⁻¹` or `x / a`, as in Kahn's diagonalization of `Tr_*⟨a⟩`. -/
theorem trace_inv (a : L) :
    Algebra.trace K L a⁻¹ = Algebra.trace K L a / Algebra.norm K a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ (finrank_eq_two K L)
  have hN : Algebra.norm K a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  have h : algebraMap K L (Algebra.norm K a) * a⁻¹ = algebraMap K L (Algebra.trace K L a) - a := by
    have h2 := sq_eq_trace_smul_sub_norm K a
    rw [Algebra.smul_def] at h2
    field_simp
    linear_combination h2
  have h3 := congrArg (Algebra.trace K L) h
  rw [← Algebra.smul_def, map_smul, map_sub, Algebra.trace_algebraMap, finrank_eq_two K L,
    smul_eq_mul, two_nsmul] at h3
  rw [eq_div_iff hN]
  linear_combination h3

end Algebra.IsQuadraticExtension

end QuadraticField

namespace TauCeti

variable {K : Type*} (L : Type*) [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L]

/-- In a quadratic field extension generated by `x² = a`, membership in the field norm
group is exactly solvability of the binary norm equation `b = u² - a v²`. -/
theorem mem_normGroup_iff_exists_sq_sub_mul_sq {x : L} {a : K}
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L a) (b : Kˣ) :
    b ∈ normGroup K L ↔ ∃ u v : K, (b : K) = u ^ 2 - a * v ^ 2 := by
  rw [mem_normGroup_iff]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨v, u, huv⟩ :=
      Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul K L hx (y : L)
    refine ⟨u, v, ?_⟩
    rw [huv, Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul_of_sq_eq hx hx2] at hy
    linear_combination -hy
  · rintro ⟨u, v, hb⟩
    let y := algebraMap K L u + algebraMap K L v * x
    have hy : Algebra.norm K y = b := by
      rw [Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul_of_sq_eq hx hx2]
      linear_combination -hb
    have hy0 : y ≠ 0 := fun h => b.ne_zero (by simpa [h] using hy.symm)
    exact ⟨Units.mk0 y hy0, hy⟩

end TauCeti

section Field

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

namespace Algebra.IsQuadraticExtension

/-- In a separable quadratic extension, the trace of `x` is `x + σx`, where `σ` is the
nontrivial automorphism. -/
theorem algebraMap_trace_eq_add {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) (x : L) :
    algebraMap K L (Algebra.trace K L x) = x + σ x := by
  classical
  rw [trace_eq_sum_automorphisms, univ_eq_pair K L hσ, Finset.sum_pair (Ne.symm hσ)]
  simp

/-- In a separable quadratic extension, the norm of `x` is `x * σx`, where `σ` is the
nontrivial automorphism. -/
theorem algebraMap_norm_eq_mul {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) (x : L) :
    algebraMap K L (Algebra.norm K x) = x * σ x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, univ_eq_pair K L hσ, Finset.prod_pair (Ne.symm hσ)]
  simp

/-- **Nonzero discriminant characterises the generators** of a separable quadratic extension: for
`t`, `n` the trace and norm of `θ`, so that `θ² = tθ - n`, the discriminant `t² - 4n` of the
characteristic polynomial `X² - tX + n` of multiplication by `θ` vanishes exactly when `θ` lies
in `K`. (Equivalently, that polynomial is the minimal polynomial of `θ` exactly when `θ` does
not lie in `K`.) Forwards, over the nontrivial automorphism `σ` the discriminant equals
`(θ - σθ)²`, so it vanishes only if `σ` fixes `θ`; backwards is
`discrim_eq_zero_of_mem_range_algebraMap`, which needs neither separability nor a field. This is
the form a construction wants: it chooses `θ` by nonzero discriminant and needs to know that `θ`
generates. -/
@[simp]
theorem discrim_eq_zero_iff_mem_range_algebraMap {θ : L} :
    Algebra.trace K L θ ^ 2 - 4 * Algebra.norm K θ = 0 ↔ θ ∈ Set.range (algebraMap K L) := by
  refine ⟨fun h0 => ?_, discrim_eq_zero_of_mem_range_algebraMap K L⟩
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  have h1 : (θ - σ θ) ^ 2 = 0 := by
    have h2 := congrArg (algebraMap K L) h0
    simp only [map_sub, map_pow, map_mul, map_zero, map_ofNat,
      algebraMap_trace_eq_add K L hσ, algebraMap_norm_eq_mul K L hσ] at h2
    linear_combination h2
  exact mem_range_algebraMap_of_apply_eq K L hσ
    (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h1)).symm

/-- A generator of a separable quadratic extension — an element outside `K` — has nonzero
discriminant. The contrapositive half of `discrim_eq_zero_iff_mem_range_algebraMap`, kept as a
named lemma because that is the direction every consumer uses. -/
theorem discrim_ne_zero {θ : L} (hθ : θ ∉ Set.range (algebraMap K L)) :
    Algebra.trace K L θ ^ 2 - 4 * Algebra.norm K θ ≠ 0 :=
  fun h0 => hθ ((discrim_eq_zero_iff_mem_range_algebraMap K L).mp h0)


/-- A separable quadratic extension has an element of nonzero discriminant `t² - 4n`. Such an
element is automatically a generator, by `discrim_eq_zero_of_mem_range_algebraMap`. Stating it as an
existence result is what lets a construction over `L/K` choose one. -/
theorem exists_discrim_ne_zero :
    ∃ θ : L, Algebra.trace K L θ ^ 2 - 4 * Algebra.norm K θ ≠ 0 :=
  ⟨_, discrim_ne_zero K L (exists_notMem_range_algebraMap K L).choose_spec⟩

end Algebra.IsQuadraticExtension

end Field

end
