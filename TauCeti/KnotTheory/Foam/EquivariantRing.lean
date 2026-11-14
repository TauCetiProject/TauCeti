/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Retract
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.EuclideanDomain.Int

/-!
# The `gl(N)` equivariant coefficient ring and graded idempotent splittings

Equivariant `gl(N)` foam evaluation takes coefficients in the ring of symmetric polynomials in `N`
variables over `ℤ`, presented freely as the polynomial ring `Λ_N = ℤ[e₁, …, e_N]` in the
elementary symmetric generators with `deg(e_r) = 2r`. Here `TauCeti.EquivariantRing N` is
`MvPolynomial (Fin N) ℤ`, where `MvPolynomial.X i` represents `e_{i + 1}` in degree `2(i + 1)`.

Because every generator has strictly positive even weight (`N = 0` included vacuously),
`EquivariantRing.grading N` is concentrated in nonnegative even degrees with degree-zero piece `ℤ`.
Specializing the PID graded-retract freeness results of
`TauCeti.Algebra.Category.GradedModuleCat.Retract` to `k = ℤ` and `A = EquivariantRing N` shows
that:

* every graded retract of a finite graded free `EquivariantRing N`-module decomposes as a finite
  biproduct of shifted copies of the regular module with explicit summand inclusions and
  projections satisfying both biproduct identities;
* every degree-zero `EquivariantRing N`-linear idempotent `p` on `(Fin m → EquivariantRing N)`
  splits homogeneously through `(Fin n → EquivariantRing N)`, and its image `LinearMap.range p`
  admits a finite `EquivariantRing N`-basis of homogeneous vectors.

## Main definitions and results

* `TauCeti.EquivariantRing`: the polynomial ring `ℤ[e₁, …, e_N]` (`MvPolynomial (Fin N) ℤ`).
* `TauCeti.EquivariantRing.grading`: the `ℤ`-grading with `deg(X i) = 2(i + 1)`.
* `TauCeti.EquivariantRing.grading_eq_bot_of_lt_zero`,
  `TauCeti.EquivariantRing.grading_eq_bot_of_odd`,
  `TauCeti.EquivariantRing.grading_zero_eq_one`: nonnegativity, evenness, and scalar degree-zero
  piece of `EquivariantRing.grading N`.
* `TauCeti.EquivariantRing.exists_iso_fin_free_of_retract`: biproduct decomposition of any graded
  retract of a finite graded free `EquivariantRing N`-module into shifted regular summands.
* `TauCeti.EquivariantRing.exists_homogeneous_matrix_retract_of_idempotent`: homogeneous matrix
  factorization `ι ∘ₗ π = p`, `π ∘ₗ ι = id` of a degree-zero idempotent on
  `(Fin m → EquivariantRing N)`.
* `TauCeti.exists_homogeneous_basis_range_idempotent`: existence of a finite homogeneous
  `EquivariantRing N`-basis of `LinearMap.range p`.

## References

* L.-H. Robert and E. Wagner, *Symmetric Khovanov-Rozansky link homologies*, J. Éc. polytech.
  Math. 7 (2020), Section 3.3 and Theorem 3.30.
* H. Wu, *Colored sl(N)-link homology via matrix factorizations*, Algebr. Geom. Topol. 14 (2014),
  Section 2.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

/-- The `gl(N)` equivariant coefficient ring `Λ_N = ℤ[e₁, …, e_N]`, realized as the polynomial
ring `MvPolynomial (Fin N) ℤ` in which `MvPolynomial.X i` represents the `(i + 1)`-st elementary
symmetric generator `e_{i + 1}`. Exposed so `MvPolynomial.X i` and `MvPolynomial.C` elaborate
directly at type `EquivariantRing N`. -/
@[expose] def EquivariantRing (N : ℕ) : Type :=
  MvPolynomial (Fin N) ℤ

namespace EquivariantRing

instance (N : ℕ) : CommRing (EquivariantRing N) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin N) ℤ))

instance (N : ℕ) : Algebra ℤ (EquivariantRing N) :=
  inferInstanceAs (Algebra ℤ (MvPolynomial (Fin N) ℤ))

instance (N : ℕ) : IsDomain (EquivariantRing N) :=
  inferInstanceAs (IsDomain (MvPolynomial (Fin N) ℤ))

instance (N : ℕ) : FaithfulSMul ℤ (EquivariantRing N) :=
  inferInstanceAs (FaithfulSMul ℤ (MvPolynomial (Fin N) ℤ))

/-- The degree `2(i + 1)` assigned to the generator `MvPolynomial.X i` (`e_{i + 1}`) of
`EquivariantRing N`. -/
abbrev weight (N : ℕ) (i : Fin N) : ℤ :=
  2 * ((i : ℕ) + 1 : ℤ)

/-- Every generator of `EquivariantRing N` has strictly positive degree. -/
theorem weight_pos (N : ℕ) (i : Fin N) : 0 < weight N i := by
  dsimp [weight]
  omega

/-- Every generator of `EquivariantRing N` has even degree. -/
theorem even_weight (N : ℕ) (i : Fin N) : Even (weight N i) :=
  ⟨(i : ℕ) + 1, by dsimp [weight]; ring⟩

/-- The `ℤ`-grading on `EquivariantRing N` assigning degree `2(i + 1)` to `MvPolynomial.X i`. -/
def grading (N : ℕ) : ℤ → Submodule ℤ (EquivariantRing N) :=
  MvPolynomial.weightedHomogeneousSubmodule ℤ (fun i : Fin N => 2 * ((i : ℕ) + 1 : ℤ))

/-- `EquivariantRing.grading N` is the weighted homogeneous submodule for `weight N`. -/
theorem grading_def (N : ℕ) (d : ℤ) :
    grading N d = MvPolynomial.weightedHomogeneousSubmodule ℤ (weight N) d :=
  (rfl)

instance (N : ℕ) : GradedAlgebra (grading N) := by
  rw [funext (grading_def N)]
  exact MvPolynomial.weightedGradedAlgebra ℤ (weight N)

/-- Membership in `grading N d` is weighted homogeneity of degree `d` for `weight N`. -/
theorem mem_grading_iff (N : ℕ) (d : ℤ) (f : EquivariantRing N) :
    f ∈ grading N d ↔ MvPolynomial.IsWeightedHomogeneous (weight N) f d :=
  MvPolynomial.mem_weightedHomogeneousSubmodule ℤ (weight N) d f

/-- The generator `MvPolynomial.X i` (`e_{i + 1}`) is homogeneous of degree `2(i + 1)`. -/
@[simp]
theorem X_mem_grading (N : ℕ) (i : Fin N) :
    (MvPolynomial.X i : EquivariantRing N) ∈ grading N (2 * ((i : ℕ) + 1 : ℤ)) :=
  (mem_grading_iff N _ _).mpr (MvPolynomial.isWeightedHomogeneous_X ℤ (weight N) i)

/-- `EquivariantRing N` vanishes in all negative degrees. -/
theorem grading_eq_bot_of_lt_zero (N : ℕ) {d : ℤ} (hd : d < 0) :
    grading N d = ⊥ :=
  MvPolynomial.weightedHomogeneousSubmodule_eq_bot_of_lt_zero ℤ
    (fun i ↦ (weight_pos N i).le) hd

/-- `EquivariantRing N` is supported in even degrees: every odd homogeneous piece vanishes. -/
theorem grading_eq_bot_of_odd (N : ℕ) {d : ℤ} (hd : Odd d) :
    grading N d = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun f hf ↦
    ((mem_grading_iff N d f).mp hf).eq_zero_of_no_monomials fun m hm ↦ by
      have heven : Even (m.weight (weight N)) := by
        rw [Finsupp.weight_apply, Finsupp.sum]
        exact Finset.even_sum _ fun i _ ↦ ⟨m i • ((i : ℕ) + 1 : ℤ), by dsimp [weight]; ring⟩
      exact (Int.not_even_iff_odd.mpr hd) (hm ▸ heven)

/-- The degree-zero piece of `EquivariantRing N` consists precisely of integer scalars. -/
@[simp]
theorem grading_zero_eq_one (N : ℕ) :
    grading N 0 = 1 :=
  MvPolynomial.weightedHomogeneousSubmodule_zero_eq_one ℤ (weight_pos N)

/-- For `N = 0`, `EquivariantRing 0` vanishes in every nonzero degree. -/
theorem grading_zero_vars_eq_bot_of_ne_zero {d : ℤ} (hd : d ≠ 0) :
    grading 0 d = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun f hf ↦
    ((mem_grading_iff 0 d f).mp hf).eq_zero_of_no_monomials fun m hm ↦ by
      rw [Subsingleton.elim m 0, map_zero] at hm
      exact hd hm.symm

/-! ### Graded retracts and homogeneous bases over `EquivariantRing N` -/

/-- Any graded idempotent on a finite graded free `EquivariantRing N`-module splits homogeneously
through a `Fin n`-indexed graded free module. -/
theorem exists_fin_free_retract_of_idempotent (N : ℕ) {J : Type} [Finite J] (s : J → ℤ)
    (e : GradedModuleCat.free (grading N) s ⟶ GradedModuleCat.free (grading N) s)
    (he : e ≫ e = e) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : GradedModuleCat.free (grading N) d ⟶ GradedModuleCat.free (grading N) s)
      (π : GradedModuleCat.free (grading N) s ⟶ GradedModuleCat.free (grading N) d),
      π ≫ ι = e ∧ ι ≫ π = 𝟙 (GradedModuleCat.free (grading N) d) :=
  GradedModuleCat.exists_fin_free_retract_of_idempotent (grading N)
    (fun _ hd ↦ grading_eq_bot_of_lt_zero N hd) (grading_zero_eq_one N).le s e he

/-- Any graded retract `W` of a finite graded free `EquivariantRing N`-module is graded-isomorphic
to `GradedModuleCat.free (grading N) d` and decomposes into `n` shifted copies of the regular
module with explicit summand inclusions and projections satisfying both biproduct identities. -/
theorem exists_iso_fin_free_of_retract (N : ℕ) {J : Type} [Finite J] (s : J → ℤ)
    {W : GradedModuleCat.{0} (grading N)}
    (u : W ⟶ GradedModuleCat.free (grading N) s)
    (v : GradedModuleCat.free (grading N) s ⟶ W) (huv : u ≫ v = 𝟙 W) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : ∀ i : Fin n, (GradedModuleCat.regular (𝒜 := grading N)).shiftObj (d i) ⟶ W)
      (π : ∀ i : Fin n, W ⟶ (GradedModuleCat.regular (𝒜 := grading N)).shiftObj (d i)),
      Nonempty (W ≅ GradedModuleCat.free (grading N) d) ∧
      (∀ i, ι i ≫ π i = 𝟙 _) ∧
      (∀ i j, i ≠ j → ι i ≫ π j = 0) ∧
      ∑ i : Fin n, π i ≫ ι i = 𝟙 W :=
  GradedModuleCat.exists_iso_fin_free_of_retract (grading N)
    (fun _ hd ↦ grading_eq_bot_of_lt_zero N hd) (grading_zero_eq_one N).le s u v huv

/-- Every degree-zero `EquivariantRing N`-linear idempotent `p` on `(Fin m → EquivariantRing N)`
factors as `ι ∘ₗ π = p` with `π ∘ₗ ι = id` through `(Fin n → EquivariantRing N)` via homogeneous
matrices `ι` and `π` respecting shifts `d : Fin n → ℤ`. -/
theorem exists_homogeneous_matrix_retract_of_idempotent (N m : ℕ) (s : Fin m → ℤ)
    (p : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N] (Fin m → EquivariantRing N))
    (hp : p.comp p = p)
    (hhom : ∀ (q : ℤ) (v : Fin m → EquivariantRing N),
      (∀ j, v j ∈ grading N (q - s j)) → ∀ j, p v j ∈ grading N (q - s j)) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : (Fin n → EquivariantRing N) →ₗ[EquivariantRing N] (Fin m → EquivariantRing N))
      (π : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N] (Fin n → EquivariantRing N)),
      ι.comp π = p ∧ π.comp ι = LinearMap.id ∧
      (∀ (q : ℤ) (w : Fin n → EquivariantRing N),
        (∀ i, w i ∈ grading N (q - d i)) → ∀ j, ι w j ∈ grading N (q - s j)) ∧
      (∀ (q : ℤ) (v : Fin m → EquivariantRing N),
        (∀ j, v j ∈ grading N (q - s j)) → ∀ i, π v i ∈ grading N (q - d i)) :=
  GradedModuleCat.exists_homogeneous_matrix_retract_of_idempotent (grading N)
    (fun _ hd ↦ grading_eq_bot_of_lt_zero N hd) (grading_zero_eq_one N).le s p hp hhom

end EquivariantRing

/-- **Integral homogeneous basis of a graded idempotent image over `EquivariantRing N`.** For any
`N`, any finite tuple of shifts `s : Fin m → ℤ`, and any degree-zero `EquivariantRing N`-linear
idempotent `p` on `(Fin m → EquivariantRing N)`, the image `LinearMap.range p` admits a finite
`EquivariantRing N`-basis `b` indexed by `Fin n` with degrees `d : Fin n → ℤ` such that the `j`-th
coordinate of `b i` lies in `EquivariantRing.grading N (d i - s j)`. -/
theorem exists_homogeneous_basis_range_idempotent (N m : ℕ) (s : Fin m → ℤ)
    (p : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N]
      (Fin m → EquivariantRing N))
    (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : Fin m → EquivariantRing N),
      (∀ j, v j ∈ EquivariantRing.grading N (d - s j)) →
      ∀ j, p v j ∈ EquivariantRing.grading N (d - s j)) :
    ∃ (n : ℕ)
      (b : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p))
      (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - s j) :=
  GradedModuleCat.exists_homogeneous_basis_range_idempotent (EquivariantRing.grading N)
    (fun _ hd ↦ EquivariantRing.grading_eq_bot_of_lt_zero N hd)
    (EquivariantRing.grading_zero_eq_one N).le s p hp hhom

section Examples

-- For `p = 0`, `exists_homogeneous_basis_range_idempotent` produces the empty basis (`n = 0`).
example (N m : ℕ) (s : Fin m → ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (EquivariantRing N)
        (LinearMap.range (0 : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N]
          (Fin m → EquivariantRing N))))
      (d : Fin n → ℤ),
      n = 0 ∧ ∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - s j) := by
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent N m s 0
    (LinearMap.zero_comp 0) (fun _ _ _ _ ↦ Submodule.zero_mem _)
  have hn : n = 0 := by
    by_contra hn
    obtain ⟨_, hv⟩ := (b ⟨0, Nat.pos_of_ne_zero hn⟩).2
    exact b.ne_zero ⟨0, Nat.pos_of_ne_zero hn⟩ (Subtype.ext hv.symm)
  exact ⟨n, b, d, hn, hb⟩

-- For `p = id` on a rank-one summand of shift `3`, the basis vector has degree `3`.
example (N : ℕ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (EquivariantRing N)
        (LinearMap.range (LinearMap.id : (Fin 1 → EquivariantRing N) →ₗ[EquivariantRing N]
          (Fin 1 → EquivariantRing N))))
      (d : Fin n → ℤ),
      (n = 1 ∧ ∀ i, d i = 3) ∧
      ∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - ![3] j) := by
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent N 1 ![3] LinearMap.id
    (LinearMap.id_comp LinearMap.id) (fun _ _ hv j ↦ hv j)
  let v₀ : LinearMap.range (LinearMap.id :
      (Fin 1 → EquivariantRing N) →ₗ[EquivariantRing N] (Fin 1 → EquivariantRing N)) :=
    ⟨![1], ⟨![1], rfl⟩⟩
  have hv₀_ne : v₀ ≠ 0 := fun h ↦ one_ne_zero (congr_fun (congr_arg Subtype.val h) 0)
  have hv₀_span : Submodule.span (EquivariantRing N) {v₀} = ⊤ := top_unique fun x _ ↦ by
    rw [Submodule.mem_span_singleton]
    refine ⟨x.1 0, Subtype.ext (funext fun j ↦ ?_)⟩
    fin_cases j
    simp [v₀]
  have hv₀_hom : ∀ j, v₀.val j ∈ EquivariantRing.grading N (3 - ![3] j) := fun j ↦ by
    fin_cases j
    simpa [v₀] using SetLike.one_mem_graded (EquivariantRing.grading N)
  refine ⟨n, b, d, ?_, hb⟩
  exact GradedModuleCat.rank_one_homogeneous_basis_eq (EquivariantRing.grading N)
    (fun _ hd ↦ EquivariantRing.grading_eq_bot_of_lt_zero N hd) hv₀_ne hv₀_span hv₀_hom b hb

-- For `p = diag(1, 0)` on shifts `(a, b)`, the image basis has degree `a` independently of `b`.
example (N : ℕ) (a b : ℤ) :
    let p : (Fin 2 → EquivariantRing N) →ₗ[EquivariantRing N] (Fin 2 → EquivariantRing N) :=
      (LinearMap.single (EquivariantRing N) (fun _ : Fin 2 ↦ EquivariantRing N) 0).comp
        (LinearMap.proj 0)
    p.comp p = p ∧
    ∃ (n : ℕ) (bas : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p))
      (d : Fin n → ℤ),
      (n = 1 ∧ ∀ i, d i = a) ∧
      ∀ i j, (bas i).val j ∈ EquivariantRing.grading N (d i - ![a, b] j) := by
  intro p
  have hp : p.comp p = p := LinearMap.ext fun v ↦ funext fun j ↦ by
    fin_cases j <;> simp [p]
  have hhom : ∀ (q : ℤ) (v : Fin 2 → EquivariantRing N),
      (∀ j, v j ∈ EquivariantRing.grading N (q - ![a, b] j)) →
      ∀ j, p v j ∈ EquivariantRing.grading N (q - ![a, b] j) := fun q v hv j ↦ by
    fin_cases j
    · simpa [p] using hv 0
    · simp [p]
  obtain ⟨n, bas, d, hbas⟩ := exists_homogeneous_basis_range_idempotent N 2 ![a, b] p hp hhom
  let v₀ : LinearMap.range p := ⟨![1, 0], ⟨![1, 0], funext fun j ↦ by fin_cases j <;> simp [p]⟩⟩
  have hv₀_ne : v₀ ≠ 0 := fun h ↦ one_ne_zero (congr_fun (congr_arg Subtype.val h) 0)
  have hv₀_span : Submodule.span (EquivariantRing N) {v₀} = ⊤ := top_unique fun x _ ↦ by
    obtain ⟨w, hw⟩ := x.2
    rw [Submodule.mem_span_singleton]
    refine ⟨w 0, Subtype.ext (funext fun j ↦ ?_)⟩
    rw [← hw]
    fin_cases j <;> simp [v₀, p]
  have hv₀_hom : ∀ j, v₀.val j ∈ EquivariantRing.grading N (a - ![a, b] j) := fun j ↦ by
    fin_cases j
    · simpa [v₀] using SetLike.one_mem_graded (EquivariantRing.grading N)
    · simp [v₀]
  refine ⟨hp, n, bas, d, ?_, hbas⟩
  exact GradedModuleCat.rank_one_homogeneous_basis_eq (EquivariantRing.grading N)
    (fun _ hd ↦ EquivariantRing.grading_eq_bot_of_lt_zero N hd) hv₀_ne hv₀_span hv₀_hom bas hbas

-- For `N + 1` variables, shifts `(2, 0)`, and `p (x, y) = (x, e₁ x)`, `p` is a degree-zero
-- idempotent whose image has basis `(1, e₁)` of degree `2` (with second coordinate in degree
-- `2 - 0 = 2`, checking the shift sign).
example (N : ℕ) :
    let e₁ : EquivariantRing (N + 1) := MvPolynomial.X 0
    let p : (Fin 2 → EquivariantRing (N + 1)) →ₗ[EquivariantRing (N + 1)]
        (Fin 2 → EquivariantRing (N + 1)) :=
      ((LinearMap.single (EquivariantRing (N + 1)) (fun _ : Fin 2 ↦ EquivariantRing (N + 1)) 0) +
        (LinearMap.single (EquivariantRing (N + 1))
          (fun _ : Fin 2 ↦ EquivariantRing (N + 1)) 1).comp
          (LinearMap.lsmul (EquivariantRing (N + 1)) (EquivariantRing (N + 1)) e₁)).comp
        (LinearMap.proj 0)
    p.comp p = p ∧
    (![1, e₁] 1 ∈ EquivariantRing.grading (N + 1) (2 - ![2, 0] 1)) ∧
    ∃ (n : ℕ) (bas : Module.Basis (Fin n) (EquivariantRing (N + 1)) (LinearMap.range p))
      (d : Fin n → ℤ),
      (n = 1 ∧ ∀ i, d i = 2) ∧
      ∀ i j, (bas i).val j ∈ EquivariantRing.grading (N + 1) (d i - ![2, 0] j) := by
  intro e₁ p
  have he₁ : e₁ ∈ EquivariantRing.grading (N + 1) 2 :=
    EquivariantRing.X_mem_grading (N + 1) 0
  have hp : p.comp p = p := LinearMap.ext fun v ↦ funext fun j ↦ by
    fin_cases j <;> simp [p]
  have hhom : ∀ (q : ℤ) (v : Fin 2 → EquivariantRing (N + 1)),
      (∀ j, v j ∈ EquivariantRing.grading (N + 1) (q - ![2, 0] j)) →
      ∀ j, p v j ∈ EquivariantRing.grading (N + 1) (q - ![2, 0] j) := fun q v hv j ↦ by
    fin_cases j
    · simpa [p] using hv 0
    · have hmul : e₁ * v 0 ∈ EquivariantRing.grading (N + 1) (2 + (q - 2)) :=
        SetLike.mul_mem_graded he₁ (by simpa using hv 0)
      have heq : 2 + (q - 2) = q := by omega
      simpa [p, smul_eq_mul, heq] using hmul
  obtain ⟨n, bas, d, hbas⟩ :=
    exists_homogeneous_basis_range_idempotent (N + 1) 2 ![2, 0] p hp hhom
  let v₀ : LinearMap.range p :=
    ⟨![1, e₁], ⟨![1, 0], funext fun j ↦ by fin_cases j <;> simp [p]⟩⟩
  have hv₀_ne : v₀ ≠ 0 := fun h ↦ one_ne_zero (congr_fun (congr_arg Subtype.val h) 0)
  have hv₀_span : Submodule.span (EquivariantRing (N + 1)) {v₀} = ⊤ := top_unique fun x _ ↦ by
    obtain ⟨w, hw⟩ := x.2
    rw [Submodule.mem_span_singleton]
    refine ⟨w 0, Subtype.ext (funext fun j ↦ ?_)⟩
    rw [← hw]
    fin_cases j <;> simp [v₀, p, mul_comm]
  have hv₀_hom : ∀ j, v₀.val j ∈ EquivariantRing.grading (N + 1) (2 - ![2, 0] j) := fun j ↦ by
    fin_cases j
    · simpa [v₀] using SetLike.one_mem_graded (EquivariantRing.grading (N + 1))
    · simpa [v₀] using he₁
  refine ⟨hp, by simpa using he₁, n, bas, d, ?_, hbas⟩
  exact GradedModuleCat.rank_one_homogeneous_basis_eq (EquivariantRing.grading (N + 1))
    (fun _ hd ↦ EquivariantRing.grading_eq_bot_of_lt_zero (N + 1) hd)
    hv₀_ne hv₀_span hv₀_hom bas hbas

end Examples

end TauCeti
