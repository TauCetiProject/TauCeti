/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic
import TauCeti.Algebra.Algebra.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation

/-!
# Torsion classes of vectors under adelic matrices

Let `R` be a Dedekind domain with fraction field `K`, `𝔸_f` its finite adeles and `Ô` the
integral finite adeles. For a finite type `n`, the diagonal map `K → 𝔸_f` induces an
isomorphism from `(K/R)ⁿ` to the `R`-module `T_n = (𝔸_f/Ô)ⁿ`
(`IsDedekindDomain.FiniteAdeleRing.quotientEquivQuotientIntegralAdeles`, coordinatewise).
A matrix `h ∈ M_{m×n}(𝔸_f)` gives the `R`-linear map `Kⁿ → T_m`, `y ↦ class of h y`, and for
`g ∈ GL_n(𝔸_f)` the *torsion class* `[y]_g` of `y ∈ Kⁿ` is the class of `g⁻¹ y`. Its kernel is
`Kⁿ ∩ g Ôⁿ`, and every class is a torsion class: `Kⁿ` is dense in `𝔸_fⁿ` and `g Ôⁿ` is an open
subgroup, so every coset `g a + g Ôⁿ` meets `Kⁿ`. The proof makes this explicit with a common
denominator `d` of `g⁻¹` and an approximation of `(g a)/d` by `Kⁿ` modulo `Ôⁿ`
(`IsDedekindDomain.FiniteAdeleRing.exists_sub_algebraMap_mem_integralAdeles`). So the torsion class
induces an isomorphism `Kⁿ ⧸ (Kⁿ ∩ g Ôⁿ) ≃ (𝔸_f/Ô)ⁿ`.

When the local integer rings are compact (for instance for the ring of integers of a number
field), every `R`-linear map `Kⁿ → T_m` is of the form `y ↦ class of h y`. For one coordinate,
let `ψ : K → 𝔸_f/Ô` be `R`-linear. For every nonzero `d ∈ R` the adeles `h` with
`[h/d] = ψ(1/d)` form a coset of `dÔ`, hence a nonempty compact set, and these sets decrease
along divisibility, so they have a common point `h`. Writing `y = b/d` gives
`ψ(y) = b·ψ(1/d) = [h y]`.

Finally `Kⁿ ∩ g Ôⁿ` is a finitely generated `R`-module spanning `Kⁿ`: if `d ∈ R` is a common
denominator of the entries of `g` and `g⁻¹`
(`IsDedekindDomain.FiniteAdeleRing.exists_mem_nonZeroDivisors_forall_mul_mem_integralAdeles`),
it contains `d Rⁿ` and is contained in `d⁻¹ Rⁿ`.

## Main definitions

* `IsDedekindDomain.FiniteAdeleRing.adelicTorsionEquiv`: `(K/R)ⁿ ≃ (𝔸_f/Ô)ⁿ`.
* `Matrix.mulVecQuotient`: the map `y ↦ class of h y` of a matrix `h` over `𝔸_f`.
* `Matrix.GeneralLinearGroup.torsionClass`: the map `y ↦ [y]_g`, the class of `g⁻¹ y`.
* `Matrix.GeneralLinearGroup.frameLattice`: the `R`-module `Kⁿ ∩ g Ôⁿ`.
* `Matrix.GeneralLinearGroup.torsionClassEquiv`: `Kⁿ ⧸ (Kⁿ ∩ g Ôⁿ) ≃ (𝔸_f/Ô)ⁿ`.

## Main results

* `LinearMap.exists_forall_eq_mk_mul`: if every local integer ring is compact, an `R`-linear map
  `ψ : K → 𝔸_f/Ô` is `y ↦ [h y]` for a single finite adele `h`.
* `LinearMap.exists_eq_mulVecQuotient`: if every local integer ring is compact, every `R`-linear
  map `Kⁿ → T_m` is `mulVecQuotient h` for a matrix `h` over `𝔸_f`.
* `Matrix.GeneralLinearGroup.torsionClass_surjective`: every class in `T_n` is a torsion class.
* `Matrix.GeneralLinearGroup.fg_frameLattice`,
  `Matrix.GeneralLinearGroup.span_frameLattice_eq_top`: `Kⁿ ∩ g Ôⁿ` is finitely generated and
  spans `Kⁿ`.
* `Matrix.GeneralLinearGroup.torsionClass_map_mul_mulVec`,
  `Matrix.GeneralLinearGroup.mulVec_mem_frameLattice_map_mul_iff`: change of rational basis,
  `[z y]_{z g} = [y]_g` for `z ∈ GL_n(K)`.

## References

* the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207 (`New.AdelicTorsion`,
  `New.Variety.exists_matrix_torsionClass_eq`).
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing Matrix
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

namespace IsDedekindDomain.FiniteAdeleRing

variable (R K) in
/-- The diagonal map `K → 𝔸_f` induces, coordinatewise, an `R`-linear isomorphism from
`(K/R)ⁿ` to `(𝔸_f/Ô)ⁿ`. -/
def adelicTorsionEquiv (n : Type*) : (n → K ⧸ (1 : Submodule R K)) ≃ₗ[R] n → AdeleQuotient R K :=
  LinearEquiv.piCongrRight fun _ ↦ quotientEquivQuotientIntegralAdeles R K

@[simp]
theorem adelicTorsionEquiv_apply {n : Type*} (y : n → K ⧸ (1 : Submodule R K)) (i : n) :
    adelicTorsionEquiv R K n y i = quotientEquivQuotientIntegralAdeles R K (y i) :=
  (rfl)

/-- The `R`-linear map `K → 𝔸_f/Ô`, `y ↦ [h y]`, of a finite adele `h`. -/
private def mulMkQ (h : FiniteAdeleRing R K) : K →ₗ[R] AdeleQuotient R K :=
  (Subalgebra.toSubmodule (integralAdeles R K)).mkQ ∘ₗ LinearMap.mulLeft R h ∘ₗ
    (Algebra.linearMap K (FiniteAdeleRing R K)).restrictScalars R

private theorem mulMkQ_apply (h : FiniteAdeleRing R K) (y : K) :
    mulMkQ h y = Submodule.Quotient.mk (h * algebraMap K (FiniteAdeleRing R K) y) :=
  (rfl)

/-- If `d` clears the denominators of `M`, then `d • M w` is integral for an integral vector `w`. -/
private theorem smul_mulVec_mem_integralAdeles {m n : Type*} [Fintype n]
    {M : Matrix m n (FiniteAdeleRing R K)} {d : R}
    (hd : ∀ i j, M i j * algebraMap R (FiniteAdeleRing R K) d ∈ integralAdeles R K)
    {w : n → FiniteAdeleRing R K} (hw : ∀ j, w j ∈ integralAdeles R K) (i : m) :
    (d • (M *ᵥ w)) i ∈ integralAdeles R K := by
  rw [← smul_mulVec]
  exact sum_mem fun j _ ↦ mul_mem (by simpa [Algebra.smul_def, mul_comm] using hd i j) (hw j)

/-- The diagonal image of a single-coordinate vector is a single-coordinate vector. -/
private theorem algebraMap_comp_single {n : Type*} [DecidableEq n] (j : n) (t : K) :
    (fun k ↦ algebraMap K (FiniteAdeleRing R K) ((Pi.single j t : n → K) k)) =
      Pi.single j (algebraMap K (FiniteAdeleRing R K) t) :=
  funext <| Pi.apply_single (fun _ ↦ algebraMap K (FiniteAdeleRing R K)) (fun _ ↦ map_zero _) j t

end IsDedekindDomain.FiniteAdeleRing

variable {m n : Type*} [Fintype n]

namespace Matrix

/-- The `R`-linear map `Kⁿ → (𝔸_f/Ô)ᵐ`, `y ↦ class of h y`, of a matrix `h` over the finite
adeles. -/
def mulVecQuotient (h : Matrix m n (FiniteAdeleRing R K)) : (n → K) →ₗ[R] m → AdeleQuotient R K :=
  (Subalgebra.toSubmodule (integralAdeles R K)).mkQ.compLeft m ∘ₗ
    (h.mulVecLin.restrictScalars R) ∘ₗ
      ((Algebra.linearMap K (FiniteAdeleRing R K)).restrictScalars R).compLeft n

@[simp]
theorem mulVecQuotient_apply (h : Matrix m n (FiniteAdeleRing R K)) (y : n → K) (i : m) :
    h.mulVecQuotient y i =
      Submodule.Quotient.mk ((h *ᵥ fun j ↦ algebraMap K (FiniteAdeleRing R K) (y j)) i) :=
  (rfl)

end Matrix

namespace LinearMap

/-- **An `R`-linear map `K → 𝔸_f/Ô` is multiplication by a finite adele**: if every local integer
ring is compact, there is a single finite adele `h` with `ψ(y) = [h y]` for every `y ∈ K`. -/
theorem exists_forall_eq_mk_mul
    [∀ v : HeightOneSpectrum R, CompactSpace (v.adicCompletionIntegers K)]
    (ψ : K →ₗ[R] AdeleQuotient R K) :
    ∃ h : FiniteAdeleRing R K, ∀ y : K,
      ψ y = Submodule.Quotient.mk (h * algebraMap K (FiniteAdeleRing R K) y) := by
  let ι := algebraMap K (FiniteAdeleRing R K)
  let C : R⁰ → Set (FiniteAdeleRing R K) := fun d ↦
    {h | mulMkQ h (algebraMap R K d)⁻¹ = ψ (algebraMap R K d)⁻¹}
  have hne (d : R⁰) : algebraMap R K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.property
  have hsub (d d' : R⁰) : C (d * d') ⊆ C d := fun h hh ↦ by
    simp only [C, Set.mem_ofPred_eq, Submonoid.coe_mul] at hh ⊢
    rw [TauCeti.inv_algebraMap_eq_smul_inv_algebraMap_mul (hne d'), map_smul, map_smul, hh]
  choose a ha using fun d : R⁰ ↦ Submodule.Quotient.mk_surjective _ (ψ (algebraMap R K d)⁻¹)
  have hC (d : R⁰) : C d = (fun h ↦ h * ι (algebraMap R K d)⁻¹ - a d) ⁻¹'
      (integralAdeles R K : Set (FiniteAdeleRing R K)) := by
    ext h
    simp only [C, ι, Set.mem_ofPred_eq, Set.mem_preimage, mulMkQ_apply, ← ha,
      Submodule.Quotient.eq,
      Subalgebra.mem_toSubmodule, SetLike.mem_coe]
  have hcl (d : R⁰) : IsClosed (C d) := by
    rw [hC]
    exact (isClosed_integralAdeles R K).preimage (by fun_prop)
  have h1 : IsCompact (C 1) := by
    have : C 1 = (· + a 1) '' (integralAdeles R K : Set (FiniteAdeleRing R K)) := by
      rw [hC, OneMemClass.coe_one, map_one, inv_one, map_one]
      ext h
      simp only [Set.mem_preimage, mul_one, Set.mem_image]
      exact ⟨fun hh ↦ ⟨_, hh, sub_add_cancel h _⟩, by rintro ⟨z, hz, rfl⟩; simpa using hz⟩
    rw [this]
    exact isCompact_integralAdeles.image (by fun_prop)
  obtain ⟨h, hh⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C
    (fun d d' ↦ ⟨d * d', hsub d d', mul_comm d d' ▸ hsub d' d⟩)
    (fun d ↦ ⟨a d * ι (algebraMap R K d), by
      simp [C, mulMkQ_apply, mul_assoc, ← map_mul, ι, ha, hne d]⟩)
    (fun d ↦ h1.of_isClosed_subset (hcl d) (one_mul d ▸ hsub 1 d)) hcl
  refine ⟨h, fun y ↦ ?_⟩
  obtain ⟨b, d, hd0, rfl⟩ := IsFractionRing.div_surjective (A := R) y
  have hd : mulMkQ h (algebraMap R K d)⁻¹ = ψ (algebraMap R K d)⁻¹ :=
    Set.mem_iInter.mp hh ⟨d, hd0⟩
  have hy : algebraMap R K b / algebraMap R K d = b • (algebraMap R K d)⁻¹ := by
    rw [Algebra.smul_def, div_eq_mul_inv]
  rw [← mulMkQ_apply, hy, map_smul, map_smul, hd]

/-- **Every `R`-linear map `Kⁿ → (𝔸_f/Ô)ᵐ` is `y ↦ class of h y`** for a matrix `h` over the
finite adeles, if every local integer ring is compact. -/
theorem exists_eq_mulVecQuotient
    [∀ v : HeightOneSpectrum R, CompactSpace (v.adicCompletionIntegers K)]
    (φ : (n → K) →ₗ[R] m → AdeleQuotient R K) :
    ∃ h : Matrix m n (FiniteAdeleRing R K), φ = h.mulVecQuotient := by
  classical
  choose h hh using fun i j ↦
    exists_forall_eq_mk_mul ((LinearMap.proj i).comp (φ.comp (LinearMap.single R (fun _ ↦ K) j)))
  refine ⟨Matrix.of h, LinearMap.pi_ext fun j t ↦ funext fun i ↦ ?_⟩
  simp only [mulVecQuotient_apply, algebraMap_comp_single, mulVec_single, Pi.smul_apply, col_apply,
    op_smul_eq_mul, of_apply, ← hh i j t, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.coe_single]

end LinearMap

variable [DecidableEq n]

namespace Matrix.GeneralLinearGroup

/-- The **torsion class** `[y]_g ∈ (𝔸_f/Ô)ⁿ` of `y ∈ Kⁿ` under `g ∈ GL_n(𝔸_f)`: the class of
`g⁻¹ y`. -/
def torsionClass (g : GL n (FiniteAdeleRing R K)) : (n → K) →ₗ[R] n → AdeleQuotient R K :=
  (↑g⁻¹ : Matrix n n (FiniteAdeleRing R K)).mulVecQuotient

@[simp]
theorem torsionClass_apply (g : GL n (FiniteAdeleRing R K)) (y : n → K) (i : n) :
    g.torsionClass y i = Submodule.Quotient.mk
      (((↑g⁻¹ : Matrix n n (FiniteAdeleRing R K)) *ᵥ fun j ↦ algebraMap K _ (y j)) i) :=
  (rfl)

/-- **Every class of `(𝔸_f/Ô)ⁿ` is a torsion class.** -/
theorem torsionClass_surjective (g : GL n (FiniteAdeleRing R K)) :
    Function.Surjective g.torsionClass := by
  intro t
  choose a ha using fun i ↦ Submodule.Quotient.mk_surjective _ (t i)
  obtain ⟨d, hd0, hd⟩ := exists_mem_nonZeroDivisors_forall_mul_mem_integralAdeles
    fun p : n × n ↦ (↑g⁻¹ : Matrix n n (FiniteAdeleRing R K)) p.1 p.2
  set ι := algebraMap K (FiniteAdeleRing R K)
  have hδ : algebraMap R (FiniteAdeleRing R K) d * ι (algebraMap R K d)⁻¹ = 1 := by
    rw [IsScalarTower.algebraMap_apply R K, ← map_mul,
      mul_inv_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd0), map_one]
  choose x hx using fun j ↦ exists_sub_algebraMap_mem_integralAdeles
    (((g : Matrix n n (FiniteAdeleRing R K)) *ᵥ a) j * ι (algebraMap R K d)⁻¹)
  refine ⟨fun j ↦ algebraMap R K d * x j, funext fun i ↦ ?_⟩
  -- `d x = g a - d w` with `w` integral, so `g⁻¹ (d x) - a = -(d • g⁻¹ w)` is integral
  have hv : (fun j ↦ ι (algebraMap R K d * x j)) =
      (g : Matrix n n (FiniteAdeleRing R K)) *ᵥ a - d • fun j ↦
        ((g : Matrix n n (FiniteAdeleRing R K)) *ᵥ a) j * ι (algebraMap R K d)⁻¹ - ι (x j) := by
    funext j
    rw [Pi.sub_apply, Pi.smul_apply]
    simp only [Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply, ι]
    linear_combination (((g : Matrix n n _) *ᵥ a) j) * hδ
  rw [torsionClass_apply, hv, ← ha i, Submodule.Quotient.eq, Subalgebra.mem_toSubmodule,
    mulVec_sub, inv_mulVec_mulVec, mulVec_smul, Pi.sub_apply, sub_sub_cancel_left]
  exact neg_mem (smul_mulVec_mem_integralAdeles (fun i j ↦ hd (i, j)) (fun j ↦ hx j) i)

/-- The `R`-module `Kⁿ ∩ g Ôⁿ` of `g ∈ GL_n(𝔸_f)`: the vectors whose torsion class under `g`
vanishes. -/
def frameLattice (g : GL n (FiniteAdeleRing R K)) : Submodule R (n → K) :=
  LinearMap.ker g.torsionClass

/-- The torsion class of `y` vanishes exactly when `y ∈ Kⁿ ∩ g Ôⁿ`. -/
@[simp]
theorem torsionClass_eq_zero_iff {g : GL n (FiniteAdeleRing R K)} {y : n → K} :
    g.torsionClass y = 0 ↔ y ∈ g.frameLattice :=
  LinearMap.mem_ker.symm

/-- The torsion class induces an `R`-linear isomorphism `Kⁿ ⧸ (Kⁿ ∩ g Ôⁿ) ≃ (𝔸_f/Ô)ⁿ`. -/
def torsionClassEquiv (g : GL n (FiniteAdeleRing R K)) :
    ((n → K) ⧸ g.frameLattice) ≃ₗ[R] n → AdeleQuotient R K :=
  g.torsionClass.quotKerEquivOfSurjective g.torsionClass_surjective

@[simp]
theorem torsionClassEquiv_mk (g : GL n (FiniteAdeleRing R K)) (y : n → K) :
    g.torsionClassEquiv (Submodule.Quotient.mk y) = g.torsionClass y :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

/-- **Change of rational basis**: for `z ∈ GL_n(K)` with diagonal image `ι(z) ∈ GL_n(𝔸_f)`,
`[z y]_{ι(z) g} = [y]_g`. -/
theorem torsionClass_map_mul_mulVec (z : GL n K) (g : GL n (FiniteAdeleRing R K)) (y : n → K) :
    (map (algebraMap K (FiniteAdeleRing R K)) z * g).torsionClass ((z : Matrix n n K) *ᵥ y) =
      g.torsionClass y := by
  have hz : (fun j ↦ algebraMap K (FiniteAdeleRing R K) (((z : Matrix n n K) *ᵥ y) j)) =
      (map (algebraMap K (FiniteAdeleRing R K)) z : Matrix n n (FiniteAdeleRing R K)) *ᵥ
        fun j ↦ algebraMap K (FiniteAdeleRing R K) (y j) :=
    funext fun j ↦ RingHom.map_mulVec _ _ _ j
  ext i
  rw [torsionClass_apply, torsionClass_apply, _root_.mul_inv_rev, Units.val_mul,
    ← mulVec_mulVec, hz, inv_mulVec_mulVec]

/-- **Change of rational basis for frame lattices**: for `z ∈ GL_n(K)`,
`z y ∈ Kⁿ ∩ ι(z) g Ôⁿ` exactly when `y ∈ Kⁿ ∩ g Ôⁿ`. -/
theorem mulVec_mem_frameLattice_map_mul_iff (z : GL n K) (g : GL n (FiniteAdeleRing R K))
    {y : n → K} :
    (z : Matrix n n K) *ᵥ y ∈ (map (algebraMap K (FiniteAdeleRing R K)) z * g).frameLattice ↔
      y ∈ g.frameLattice := by
  rw [← torsionClass_eq_zero_iff, ← torsionClass_eq_zero_iff, torsionClass_map_mul_mulVec]

/-- `y` lies in `Kⁿ ∩ g Ôⁿ` exactly when `g⁻¹ y` is integral. -/
theorem mem_frameLattice_iff {g : GL n (FiniteAdeleRing R K)} {y : n → K} :
    y ∈ g.frameLattice ↔ ∀ i, ((↑g⁻¹ : Matrix n n (FiniteAdeleRing R K)) *ᵥ
      fun j ↦ algebraMap K _ (y j)) i ∈ integralAdeles R K := by
  simp only [frameLattice, LinearMap.mem_ker, funext_iff, torsionClass_apply, Pi.zero_apply,
    Submodule.Quotient.mk_eq_zero, Subalgebra.mem_toSubmodule]

/-- `y` lies in `Kⁿ ∩ g Ôⁿ` exactly when `y = g z` for an integral vector `z`. -/
theorem mem_frameLattice_iff_exists {g : GL n (FiniteAdeleRing R K)} {y : n → K} :
    y ∈ g.frameLattice ↔ ∃ z : n → FiniteAdeleRing R K, (∀ i, z i ∈ integralAdeles R K) ∧
      (fun j ↦ algebraMap K _ (y j)) = (↑g : Matrix n n (FiniteAdeleRing R K)) *ᵥ z := by
  rw [mem_frameLattice_iff]
  refine ⟨fun hy ↦ ⟨_, hy, ?_⟩, fun ⟨z, hz, hyz⟩ ↦ ?_⟩
  · -- `g (g⁻¹ v) = v` is the cancellation for `g⁻¹`
    have h := inv_mulVec_mulVec g⁻¹ fun j ↦ algebraMap K (FiniteAdeleRing R K) (y j)
    rw [inv_inv] at h
    exact h.symm
  · rwa [hyz, inv_mulVec_mulVec]

/-- `Kⁿ ∩ g Ôⁿ` is a finitely generated `R`-module: it lies in `d⁻¹ Rⁿ` when `d · g` is
integral. -/
theorem fg_frameLattice (g : GL n (FiniteAdeleRing R K)) : g.frameLattice.FG := by
  obtain ⟨d, hd0, hd⟩ := exists_mem_nonZeroDivisors_forall_mul_mem_integralAdeles
    fun p : n × n ↦ (↑g : Matrix n n (FiniteAdeleRing R K)) p.1 p.2
  let f : (n → K) →ₗ[R] n → K := LinearMap.lsmul R (n → K) d
  have hf : Function.Injective f := fun _ _ h ↦
    smul_right_injective (n → K) (nonZeroDivisors.ne_zero hd0) h
  refine Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le
    ((Module.Finite.fg_top (R := R) (M := n → R)).map ((Algebra.linearMap R K).compLeft n)) ?_)
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hyz⟩ := mem_frameLattice_iff_exists.mp hy
  have hint (i : n) : algebraMap K (FiniteAdeleRing R K) (d • y i) ∈ integralAdeles R K := by
    have hyi : algebraMap K (FiniteAdeleRing R K) (y i) = (↑g *ᵥ z) i := congrFun hyz i
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, hyi, ← Algebra.smul_def,
      ← Pi.smul_apply]
    exact smul_mulVec_mem_integralAdeles (fun i j ↦ hd (i, j)) hz i
  choose r hr using fun i ↦ (algebraMap_mem_integralAdeles_iff _).mp (hint i)
  exact ⟨r, Submodule.mem_top, funext fun i ↦ hr i⟩

/-- `Kⁿ ∩ g Ôⁿ` is a finite `R`-module (`fg_frameLattice`). Over the ring of integers of a number
field this is the hypothesis under which the mixed image of `Kⁿ ∩ g Ôⁿ` is discrete
(`Submodule.isZLattice_mixedImage`). -/
instance (g : GL n (FiniteAdeleRing R K)) : Module.Finite R g.frameLattice :=
  Module.Finite.iff_fg.mpr g.fg_frameLattice

/-- `Kⁿ ∩ g Ôⁿ` spans `Kⁿ` over `K`: it contains `d Rⁿ` when `d · g⁻¹` is integral. -/
theorem span_frameLattice_eq_top (g : GL n (FiniteAdeleRing R K)) :
    Submodule.span K (g.frameLattice : Set (n → K)) = ⊤ := by
  obtain ⟨d, hd0, hd⟩ := exists_mem_nonZeroDivisors_forall_mul_mem_integralAdeles
    fun p : n × n ↦ (↑g⁻¹ : Matrix n n (FiniteAdeleRing R K)) p.1 p.2
  have hne : algebraMap R K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd0
  have hmem (j : n) : Pi.single j (algebraMap R K d) ∈ g.frameLattice := by
    rw [mem_frameLattice_iff]
    intro i
    rw [algebraMap_comp_single, ← IsScalarTower.algebraMap_apply, mulVec_single, Pi.smul_apply,
      col_apply, op_smul_eq_mul]
    exact hd (i, j)
  rw [eq_top_iff, ← (Pi.basisFun K n).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have : Pi.basisFun K n j = (algebraMap R K d)⁻¹ • Pi.single j (algebraMap R K d) := by
    rw [Pi.basisFun_apply, ← Pi.single_smul', smul_eq_mul, inv_mul_cancel₀ hne]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem j))

end Matrix.GeneralLinearGroup
