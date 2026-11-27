/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Omega.Basic
public import TauCeti.RingTheory.Dagger.Noetherian
public import TauCeti.RingTheory.Kaehler.DeRham.Basic
import TauCeti.RingTheory.Kaehler.DeRham.Quotient
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# The exterior derivative on universally finite differential forms

The overconvergent de Rham complex of a dagger algebra `A` is built from the exterior powers
`Ωⁱ_A = ⋀ⁱ_A Ω¹_A` of the universally finite differentials `Ω¹_A = Omega K A`, with the exterior
derivative determined by `d (a • db₁ ∧ ⋯ ∧ dbᵢ) = da ∧ db₁ ∧ ⋯ ∧ dbᵢ`. This file constructs that
derivative on the whole exterior algebra `ExteriorAlgebra A (Omega K A)`, for every noetherian
`K`-algebra `A` whose universally finite differentials form a finite module, in particular for
every dagger algebra. It satisfies the graded Leibniz rule, raises the exterior degree by one,
and squares to zero.

The algebraic exterior derivative `TauCeti.KaehlerDeRham.extDeriv` on `ExteriorAlgebra A Ω[A⁄K]`
cannot simply be pushed forward along the surjection `Ω[A⁄K] → Ω¹_A`: one has to show that it
respects the kernel `N` of that surjection. In degree one this is the following finiteness
argument. The map `ω ↦ d ω`, from Kähler `1`-forms to universally finite `2`-forms, is not
`A`-linear, but it is `A`-linear on `N`, since `d (a ω) = da ∧ ω + a dω` and `ω` vanishes in
`Ω¹_A`. The submodule `L ⊆ N` on which it vanishes therefore has `N ⧸ L` isomorphic to a
submodule of the finite module `⋀²_A Ω¹_A`, so `Ω[A⁄K] ⧸ L` is finite when `A` is noetherian.
As `N` is contained in every submodule with finite quotient, `L = N`. The degree-one map then
extends to the whole exterior algebra as a twisted derivation
(`ExteriorAlgebra.liftTwistedDerivation`), and the comparison with the algebraic exterior
derivative transfers `d ∘ d = 0`.

For the Monsky–Washnitzer algebra in two or more variables the derivative is nonzero in degree
one: `d (Xᵢ dXⱼ) = dXᵢ ∧ dXⱼ ≠ 0` for `i ≠ j`.

## Main definitions

* `TauCeti.Dagger.Omega.extDeriv`: the exterior derivative on
  `ExteriorAlgebra A (Omega K A)`, a `K`-linear endomorphism.
* `TauCeti.Dagger.Omega.extDerivPow`: its restriction `⋀ⁿ_A Ω¹_A → ⋀ⁿ⁺¹_A Ω¹_A` to each
  degree `n`, with `TauCeti.Dagger.Omega.extDerivPow_comp_extDerivPow`.

## Main results

* `TauCeti.Dagger.Omega.extDeriv_algebraMap`, `TauCeti.Dagger.Omega.extDeriv_ι_d`: in degree zero
  it is the universal derivation `d`, and it kills exact `1`-forms.
* `TauCeti.Dagger.Omega.exteriorAlgebra_inductionOn`: induction from functions and exact
  `1`-forms.
* `TauCeti.Dagger.Omega.extDeriv_mul`: the graded Leibniz rule.
* `TauCeti.Dagger.Omega.extDeriv_smul_ιMulti`: `d (a • db₁ ∧ ⋯ ∧ dbₙ) = da ∧ db₁ ∧ ⋯ ∧ dbₙ`.
* `TauCeti.Dagger.Omega.extDeriv_mem_exteriorPower`: it maps `⋀ⁿ` into `⋀ⁿ⁺¹`.
* `TauCeti.Dagger.Omega.extDeriv_extDeriv`: `d ∘ d = 0`.
* `TauCeti.Dagger.Omega.extDeriv_unique`: the properties above determine it.
* `TauCeti.Dagger.Omega.map_ofKaehler_extDeriv`: it is compatible with the algebraic exterior
  derivative along `Ω[A⁄K] → Ω¹_A`.
* `TauCeti.Dagger.Omega.extDeriv_X_smul_ι_d_X_ne_zero`: `d (Xᵢ dXⱼ) ≠ 0` in `K⟨X⟩†` for `i ≠ j`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §4.1.
* E. Grosse-Klönne, *Finiteness of de Rham cohomology in rigid analysis*, Duke Math. J. 113
  (2002), §1.2.
-/

public section

open CliffordAlgebra

namespace TauCeti.Dagger.Omega

variable (K A : Type*) [CommRing K] [CommRing A] [Algebra K A]

variable {K A} in
/-- **Induction on the exterior algebra of universally finite differentials**: a predicate
holding on scalars `algebraMap A _ a` and on exact `1`-forms `ι (d a)`, and closed under products
and sums, holds everywhere. -/
@[elab_as_elim]
theorem exteriorAlgebra_inductionOn {motive : ExteriorAlgebra A (Omega K A) → Prop}
    (x : ExteriorAlgebra A (Omega K A))
    (algebraMap : ∀ a : A, motive (algebraMap A (ExteriorAlgebra A (Omega K A)) a))
    (ι_d : ∀ a : A, motive (ExteriorAlgebra.ι A (d K A a)))
    (mul : ∀ x y, motive x → motive y → motive (x * y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive x := by
  -- Every element comes from the algebraic de Rham algebra, where the induction is available.
  obtain ⟨x, rfl⟩ := ExteriorAlgebra.map_surjective_iff.mpr (ofKaehler_surjective K A) x
  induction x using KaehlerDeRham.inductionOn with
  | algebraMap a => simpa using algebraMap a
  | ι_D a => simpa using ι_d a
  | mul x y ihx ihy => simpa using mul _ _ ihx ihy
  | add x y ihx ihy => simpa using add _ _ ihx ihy

/-! ### The exterior derivative in degree one -/

section DegreeOne

variable {K A} [IsNoetherianRing A] [Module.Finite A (Omega K A)]

/-- The pushed-forward derivative kills the kernel of `Ω[A⁄K] → Ω¹_A`. -/
private theorem preExtDerivOne_eq_zero {ω : Ω[A⁄K]} (hω : ofKaehler K A ω = 0) :
    KaehlerDeRham.preExtDerivOne (ofKaehler K A) ω = 0 := by
  let q := ofKaehler K A
  let dKer := KaehlerDeRham.preExtDerivOneKer q
  let L := (LinearMap.ker dKer).map (LinearMap.ker q).subtype
  -- The range of the derivative on the kernel is finite, as a submodule of the finite `⋀²`.
  have : IsNoetherian A (⋀[A]^2 (Omega K A)) := isNoetherian_of_isNoetherianRing_of_finite _ _
  have : IsNoetherian A (LinearMap.range dKer) :=
    isNoetherian_of_le (t := ⋀[A]^2 (Omega K A)) <| by
      rintro _ ⟨η, rfl⟩
      rw [show dKer η = KaehlerDeRham.preExtDerivOne q η from
        KaehlerDeRham.preExtDerivOneKer_apply q η]
      exact KaehlerDeRham.preExtDerivOne_mem q η.val
  have : Module.Finite A (LinearMap.ker q ⧸ LinearMap.ker dKer) :=
    .equiv dKer.quotKerEquivRange.symm
  -- `Ω[A⁄K] ⧸ L` is an extension of `Ω¹_A` by a quotient of that range, hence finite.
  have hexact := ((LinearMap.exact_subtype_ker_map q).exact_mapQ_iff
    (p := LinearMap.ker dKer) (q := L) (r := ⊥)
    (fun η hη ↦ ⟨η, hη, rfl⟩)
    (fun _ ⟨η, _, hη⟩ ↦ (Submodule.mem_bot A).mpr (hη ▸ LinearMap.mem_ker.mp η.property))).mpr
    (by simp)
  have : Module.Finite A (Ω[A⁄K] ⧸ L) := .of_exact hexact fun y ↦ by
    obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨η, rfl⟩ := ofKaehler_surjective K A ω
    exact ⟨Submodule.Quotient.mk η, rfl⟩
  obtain ⟨η, hη, rfl⟩ := ofKaehler_eq_zero_iff.mp hω L this
  exact (KaehlerDeRham.preExtDerivOneKer_apply q η).symm.trans (LinearMap.mem_ker.mp hη)

end DegreeOne

/-! ### The exterior derivative -/

section ExtDeriv

variable [IsNoetherianRing A] [Module.Finite A (Omega K A)]

/-- **The exterior derivative** on the exterior algebra `⋀_A Ω¹_A` of universally finite
differentials of a noetherian `K`-algebra `A` with finite `Ω¹_A`, for instance a dagger algebra:
the `K`-linear map extending the universal derivation `d : A → Ω¹_A` in degree zero, killing
exact `1`-forms `d a`, and satisfying the graded Leibniz rule
`d (x * y) = d x * y + involute x * d y`. -/
noncomputable def extDeriv : ExteriorAlgebra A (Omega K A) →ₗ[K] ExteriorAlgebra A (Omega K A) :=
  KaehlerDeRham.extDerivDescend (ofKaehler K A) (ofKaehler_surjective K A)
    (fun _ hω ↦ preExtDerivOne_eq_zero hω)

variable {K A}

/-- In degree zero the exterior derivative is the universal derivation `d`. -/
@[simp]
theorem extDeriv_algebraMap (a : A) :
    extDeriv K A (algebraMap A (ExteriorAlgebra A (Omega K A)) a) =
      ExteriorAlgebra.ι A (d K A a) := by
  rw [← ofKaehler_D, extDeriv]
  exact KaehlerDeRham.extDerivDescend_algebraMap _ _ _ a

/-- The exterior derivative kills `1`. -/
@[simp]
theorem extDeriv_one : extDeriv K A 1 = 0 := by
  simpa only [map_one, Derivation.map_one_eq_zero, map_zero] using
    extDeriv_algebraMap (K := K) (A := A) 1

/-- The exterior derivative kills the constants `K`. -/
@[simp]
theorem extDeriv_algebraMap_base (r : K) :
    extDeriv K A (algebraMap K (ExteriorAlgebra A (Omega K A)) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, extDeriv_one, smul_zero]

/-- The exterior derivative kills exact `1`-forms. -/
@[simp]
theorem extDeriv_ι_d (a : A) : extDeriv K A (ExteriorAlgebra.ι A (d K A a)) = 0 := by
  rw [← ofKaehler_D, extDeriv]
  exact KaehlerDeRham.extDerivDescend_ι_map_D _ _ _ a

/-- **The graded Leibniz rule** for the exterior derivative, via the grade involution. -/
theorem extDeriv_mul (x y : ExteriorAlgebra A (Omega K A)) :
    extDeriv K A (x * y) =
      extDeriv K A x * y + involute (Q := (0 : QuadraticForm A (Omega K A))) x * extDeriv K A y :=
  KaehlerDeRham.extDerivDescend_mul _ _ _ x y

/-- The Leibniz rule for multiplication by a function: `d (a • x) = da ∧ x + a • d x`. -/
@[simp]
theorem extDeriv_smul (a : A) (x : ExteriorAlgebra A (Omega K A)) :
    extDeriv K A (a • x) = ExteriorAlgebra.ι A (d K A a) * x + a • extDeriv K A x := by
  rw [Algebra.smul_def, extDeriv_mul, extDeriv_algebraMap, involute.commutes,
    ← Algebra.smul_def]

/-- The graded Leibniz rule for a left factor in the `n`-th exterior power. -/
theorem extDeriv_mul_of_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra A (Omega K A)}
    (hx : x ∈ ⋀[A]^n (Omega K A)) (y : ExteriorAlgebra A (Omega K A)) :
    extDeriv K A (x * y) = extDeriv K A x * y + (-1 : A) ^ n • (x * extDeriv K A y) := by
  rw [extDeriv_mul, TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower hx, smul_mul_assoc]

/-- The exterior derivative maps `⋀ⁿ_A Ω¹_A` into `⋀ⁿ⁺¹_A Ω¹_A`. -/
theorem extDeriv_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra A (Omega K A)}
    (hx : x ∈ ⋀[A]^n (Omega K A)) : extDeriv K A x ∈ ⋀[A]^(n + 1) (Omega K A) := by
  rw [← TauCeti.ExteriorAlgebra.integerGrading_natCast, Nat.cast_add, Nat.cast_one]
  have hx' : x ∈ TauCeti.ExteriorAlgebra.integerGrading A (Omega K A) n := by
    rwa [TauCeti.ExteriorAlgebra.integerGrading_natCast]
  exact KaehlerDeRham.extDerivDescend_mem_integerGrading _ _ _ hx'

/-- The exterior derivative kills products of exact `1`-forms `db₁ ∧ ⋯ ∧ dbₙ`. -/
@[simp]
theorem extDeriv_ιMulti_d {n : ℕ} (b : Fin n → A) :
    extDeriv K A (ExteriorAlgebra.ιMulti A n fun i ↦ d K A (b i)) = 0 := by
  induction n with
  | zero => rw [ExteriorAlgebra.ιMulti_zero_apply, extDeriv_one]
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, extDeriv_mul, extDeriv_ι_d, zero_mul, zero_add]
    exact mul_eq_zero_of_right _ (ih (Fin.tail b))

/-- **The exterior derivative of an elementary form**:
`d (a • db₁ ∧ ⋯ ∧ dbₙ) = da ∧ db₁ ∧ ⋯ ∧ dbₙ`, in every degree `n`, including `n = 0`. -/
theorem extDeriv_smul_ιMulti (a : A) {n : ℕ} (b : Fin n → A) :
    extDeriv K A (a • ExteriorAlgebra.ιMulti A n fun i ↦ d K A (b i)) =
      ExteriorAlgebra.ιMulti A (n + 1) (Fin.cons (d K A a) fun i ↦ d K A (b i)) := by
  rw [extDeriv_smul, extDeriv_ιMulti_d, smul_zero, add_zero, ExteriorAlgebra.ιMulti_succ_apply,
    Fin.cons_zero]
  simp only [Matrix.vecTail, Function.comp_def, Fin.cons_succ]

/-- **Compatibility with the algebraic exterior derivative**: the map of exterior algebras induced
by `Ω[A⁄K] → Ω¹_A` carries the algebraic exterior derivative to the exterior derivative of
universally finite differential forms. -/
theorem map_ofKaehler_extDeriv (x : ExteriorAlgebra A Ω[A⁄K]) :
    ExteriorAlgebra.map (ofKaehler K A) (KaehlerDeRham.extDeriv K A x) =
      extDeriv K A (ExteriorAlgebra.map (ofKaehler K A) x) :=
  (KaehlerDeRham.extDerivDescend_map _ _ _ x).symm

/-- **The exterior derivative squares to zero.** -/
@[simp]
theorem extDeriv_extDeriv (x : ExteriorAlgebra A (Omega K A)) :
    extDeriv K A (extDeriv K A x) = 0 :=
  KaehlerDeRham.extDerivDescend_sq _ _ _ x

/-- As a `K`-linear endomorphism, the exterior derivative composes with itself to zero. -/
@[simp]
theorem extDeriv_comp_extDeriv : (extDeriv K A).comp (extDeriv K A) = 0 :=
  LinearMap.ext extDeriv_extDeriv

/-- **Uniqueness of the exterior derivative**: a `K`-linear endomorphism of `⋀_A Ω¹_A` that is
the universal derivation in degree zero, kills `d (d a)`, and satisfies the graded Leibniz rule is
the exterior derivative. -/
theorem extDeriv_unique {D : ExteriorAlgebra A (Omega K A) →ₗ[K] ExteriorAlgebra A (Omega K A)}
    (h_alg : ∀ a : A, D (algebraMap A _ a) = ExteriorAlgebra.ι A (d K A a))
    (h_sq : ∀ a : A, D (D (algebraMap A _ a)) = 0)
    (h_mul : ∀ x y : ExteriorAlgebra A (Omega K A),
      D (x * y) = D x * y + involute (Q := (0 : QuadraticForm A (Omega K A))) x * D y) :
    D = extDeriv K A := by
  ext x
  induction x using exteriorAlgebra_inductionOn with
  | algebraMap a => rw [h_alg, extDeriv_algebraMap]
  | ι_d a => rw [← h_alg a, h_sq a, h_alg a, extDeriv_ι_d]
  | mul x y ihx ihy => rw [h_mul, extDeriv_mul, ihx, ihy]
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]

/-! ### The exterior derivative in each degree -/

variable (K A) in
/-- **The exterior derivative in degree `n`**: the `K`-linear map `⋀ⁿ_A Ω¹_A → ⋀ⁿ⁺¹_A Ω¹_A`
obtained by restricting `extDeriv`. -/
noncomputable def extDerivPow (n : ℕ) : ⋀[A]^n (Omega K A) →ₗ[K] ⋀[A]^(n + 1) (Omega K A) where
  toFun x := ⟨extDeriv K A x, extDeriv_mem_exteriorPower x.property⟩
  map_add' x y := Subtype.ext (map_add (extDeriv K A) (x : ExteriorAlgebra A (Omega K A)) y)
  map_smul' r x := Subtype.ext (map_smul (extDeriv K A) r (x : ExteriorAlgebra A (Omega K A)))

/-- The exterior derivative in degree `n` is `extDeriv` on the underlying exterior algebra. -/
@[simp]
theorem coe_extDerivPow_apply {n : ℕ} (x : ⋀[A]^n (Omega K A)) :
    (extDerivPow K A n x : ExteriorAlgebra A (Omega K A)) = extDeriv K A x :=
  (rfl)

/-- **The exterior derivative of an elementary form in degree `n`**:
`d (a • db₁ ∧ ⋯ ∧ dbₙ) = da ∧ db₁ ∧ ⋯ ∧ dbₙ`. -/
theorem extDerivPow_smul_ιMulti (a : A) {n : ℕ} (b : Fin n → A) :
    extDerivPow K A n (a • exteriorPower.ιMulti A n fun i ↦ d K A (b i)) =
      exteriorPower.ιMulti A (n + 1) (Fin.cons (d K A a) fun i ↦ d K A (b i)) :=
  Subtype.ext (extDeriv_smul_ιMulti a b)

/-- **The exterior derivatives in consecutive degrees compose to zero.** -/
@[simp]
theorem extDerivPow_comp_extDerivPow (n : ℕ) :
    extDerivPow K A (n + 1) ∘ₗ extDerivPow K A n = 0 :=
  LinearMap.ext fun x ↦ Subtype.ext (extDeriv_extDeriv (x : ExteriorAlgebra A (Omega K A)))

end ExtDeriv

/-! ### The Monsky–Washnitzer algebra -/

section Washnitzer

open washnitzerAlgebra

variable {σ : Type*} [Finite σ] {K : Type*} [NormedField K] [IsUltrametricDist K]
  [CompleteSpace K]

local notation "W" => washnitzerAlgebra σ K

/-- On the Monsky–Washnitzer algebra in at least two variables the exterior derivative is nonzero
on `1`-forms: `d (Xᵢ dXⱼ) = dXᵢ ∧ dXⱼ ≠ 0` for `i ≠ j`. -/
theorem extDeriv_X_smul_ι_d_X_ne_zero {i j : σ} (hij : i ≠ j) :
    extDeriv K W (X σ K i • ExteriorAlgebra.ι W (d K W (X σ K j))) ≠ 0 := by
  classical
  let b := washnitzerBasis σ K
  rw [extDeriv_smul, extDeriv_ι_d, smul_zero, add_zero, ← washnitzerBasis_apply,
    ← washnitzerBasis_apply]
  intro h
  -- Contracting with the coordinate functions `Xᵢ*` and then `Xⱼ*` sends `dXᵢ ∧ dXⱼ` to `1`.
  have h₁ := congrArg (contractLeft (Q := (0 : QuadraticForm W (Omega K W))) (b.coord j))
    (congrArg (contractLeft (Q := (0 : QuadraticForm W (Omega K W))) (b.coord i)) h)
  simp only [contractLeft_ι_mul, contractLeft_ι, map_zero, b, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij, one_smul,
    Algebra.algebraMap_eq_smul_one, mul_zero, sub_zero] at h₁
  exact one_ne_zero h₁

end Washnitzer

end TauCeti.Dagger.Omega
