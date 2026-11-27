/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.GroupTheory.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.RepresentationTheory.BaseChange
import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Plane

/-!
# Regular eigenvectors of Coxeter elements

Let `b` be a base of a finite, reduced, crystallographic root pairing `P` whose Cartan matrix is of
finite type with preconnected Dynkin diagram (or `[P.IsIrreducible]`), and let `c = wordProd P b l`
be any Coxeter element (with `l` duplicate-free and containing every simple root) of order `h`. This
file proves Steinberg's theorem in three forms:

1. **Complexified weight space (`ℂ ⊗[R] M`)**: over any characteristic-zero domain `R` with
   `[Algebra R ℂ]`, `c` has a regular `exp (2πi / h)`-eigenvector in `ℂ ⊗[R] M` with trivial Weyl
   stabilizer.
2. **Algebraically closed fields `K` containing `ℝ`**: in `M` itself, `c` has a regular eigenvector
   with trivial Weyl stabilizer whose eigenvalue `μ : K` is a primitive `h`-th root of unity; over
   `ℂ`, the eigenvalue is `exp (2πi / h)`.
3. **Bipartite Coxeter element corollary**: specializing to
   `(weylCoxeterSystem P b).bipartiteCoxeterElement col`.

This is the geometric input of the uniform identification of the eigenvalues of a Coxeter element
with `ζ ^ (dᵢ - 1)` for the invariant degrees `dᵢ`: at a regular eigenvector, the invariant
degrees compute the characteristic polynomial.

## The argument

By `RootPairing.Base.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd_of_isFiniteType`, the
integer matrix of `c` in the simple-root basis already has a complex regular primitive `h`-th-root
eigenvector `v : b.support → ℂ` (constructed via Coleman's real Coxeter plane in rank ≥ 2, and `-1`
on the unique simple root in rank 1). Given any ring homomorphism `φ : ℂ →+* K` (either
`RingHom.id ℂ` or `Complex.liftAux i _` for `i : K` with `i * i = -1`), `∑ j, φ (v j) • P.root j`
is the desired regular eigenvector in `M`, and nonsingularity of `b.cartanMatrix` yields trivial
Weyl stabilizer.

## Main results

* `RootPairing.Base.exists_eigenvector_baseChange_weylGroupRootRep_wordProd` / `_of_isFiniteType`:
  regular `exp (2πi / h)`-eigenvector of any Coxeter element in `ℂ ⊗[R] M` with trivial stabilizer.
* `RootPairing.Base.exists_isRegularWeight_eigenvector_wordProd_of_ringHom` and
  `RootPairing.Base.exists_isRegularWeight_eigenvector_wordProd_of_ringHom_of_isFiniteType`:
  regular `φ (exp (2πi / h))`-eigenvector of any Coxeter element in `M` along any ring homomorphism
  `φ : ℂ →+* K`, with trivial Weyl stabilizer.
* `RootPairing.Base.exists_isRegularWeight_eigenvector_wordProd` / `_of_isFiniteType`:
  specialization to algebraically closed fields `K` containing `ℝ`.
* `RootPairing.Base.exists_isRegularWeight_eigenvector_exp_two_pi_I_div_orderOf_wordProd` /
  `_of_isFiniteType`: specialization to `ℂ` with explicit eigenvalue `exp (2πi / h)`.
* `RootPairing.exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot`:
  the bipartite Coxeter element has a regular eigenvector whose eigenvalue is a primitive root of
  unity of order equal to the order of the element.

## References

* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§3.16–3.19.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. V, §6, no. 2.
-/

public section

open Matrix Submodule TauCeti TensorProduct

namespace RootPairing.Base

/-! ### Complexified weight-space regular primitive-root eigenvector -/

section BaseChangeWeightSpace

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R] [Algebra R ℂ]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

private theorem exists_eigenvector_baseChange_isEmpty [P.IsIrreducible] [IsEmpty ι] (b : P.Base)
    (l : List b.support) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : ℂ ⊗[R] M,
      v ≠ 0 ∧ P.weylGroupRootRep.baseChange ℂ c v = ζ • v ∧ IsPrimitiveRoot ζ (orderOf c) ∧
      (∀ j : ι, LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.coroot' j) v ≠ 0) ∧
      (∀ g : P.weylGroup, P.weylGroupRootRep.baseChange ℂ g v = v → g = 1) := by
  dsimp only; have : IsEmpty b.support := ⟨(IsEmpty.false ·.val)⟩
  have := IsIrreducible.nontrivial (P := P); obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  obtain ⟨n₀, hr₀⟩ : ∃ n₀ : N, P.toLinearMap m₀ n₀ ≠ 0 := by
    by_contra! h; exact hm₀ ((LinearMap.IsPerfPair.bijective_left P.toLinearMap).injective
      (by ext n; simp [h]))
  set r₀ := P.toLinearMap m₀ n₀
  have hS_top : LinearMap.range (LinearMap.lsmul R M r₀) = ⊤ :=
    IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P) _ (fun i ↦ (IsEmpty.false i).elim)
      fun hbot ↦ hr₀ <| mul_self_eq_zero.mp (by
        simpa [r₀] using congrArg (fun f : N →ₗ[R] R ↦ f n₀) (congrArg P.toLinearMap
          ((Submodule.mem_bot R).mp (hbot.le (LinearMap.mem_range_self _ m₀)))))
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : M, r₀ • m₁ = m₀ := LinearMap.mem_range.mp (hS_top ▸ Submodule.mem_top)
  have hp₁ : P.toLinearMap m₁ n₀ = 1 := mul_left_cancel₀ hr₀ <| by
    simpa [hm₁] using (congrArg (fun f ↦ f n₀) (P.toLinearMap.map_smul r₀ m₁)).symm
  have hl_nil (lg : List b.support) : lg = [] := List.eq_nil_iff_forall_not_mem.mpr (by simp)
  refine ⟨1 ⊗ₜ[R] m₁, fun hv0 ↦ one_ne_zero (α := ℂ) <| by simpa [hp₁] using (congrArg
      (LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.toLinearMap.flip n₀)) hv0).symm,
    by simp [hl_nil l], by simp [hl_nil l], fun j ↦ (IsEmpty.false j).elim,
    fun g _ ↦ by obtain ⟨lg, rfl⟩ := exists_wordProd_eq P b g; simp [hl_nil lg]⟩

omit [CharZero R] [IsDomain R] [Finite ι] [P.IsReduced] in
private theorem sum_tmul_root_injective_of_isFiniteType (b : P.Base)
    (hft : IsFiniteType b.cartanMatrix) :
    Function.Injective (fun u : b.support → ℂ ↦ ∑ i : b.support, u i ⊗ₜ[R] P.root i) := by
  classical
  refine fun u₁ u₂ h ↦ Matrix.mulVec_injective_of_isUnit (hft.transpose.isUnit_map ℂ)
    (funext fun k ↦ by
      have hk := congrArg (LinearMap.liftBaseChange ℂ
        (Algebra.linearMap R ℂ ∘ₗ P.coroot' (k : ι))) h
      simp only [b.liftBaseChange_coroot'_sum_tmul_root, corootEval_coe_support] at hk
      simpa [mulVec, dotProduct] using hk)

/-- **Complexified weight-space regular primitive-root eigenvector** (Cartan-matrix form): for a
base `b` of a nonempty finite crystallographic reduced root pairing over a char-0 domain `R` with
`[Algebra R ℂ]`, when `b.cartanMatrix` is of finite type with preconnected Dynkin diagram, every
`c = wordProd P b l` of order `h = orderOf c` has a nonzero `exp (2πi / h)`-eigenvector
`v : ℂ ⊗[R] M` lying outside every complexified coroot hyperplane with trivial Weyl stabilizer. -/
theorem exists_eigenvector_baseChange_weylGroupRootRep_wordProd_of_isFiniteType
    [Nonempty ι] (b : P.Base) (hft : IsFiniteType b.cartanMatrix)
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : ℂ ⊗[R] M,
      v ≠ 0 ∧ P.weylGroupRootRep.baseChange ℂ c v = ζ • v ∧
      IsPrimitiveRoot ζ (orderOf c) ∧
      (∀ j : ι, LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.coroot' j) v ≠ 0) ∧
      (∀ g : P.weylGroup, P.weylGroupRootRep.baseChange ℂ g v = v → g = 1) := by
  classical
  dsimp only; set c := wordProd P b l; have hW := b.actsBy_wordProd l
  obtain ⟨y, -, hy_eig, hprim, hy_reg, hy_stab⟩ :=
    b.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd_of_isFiniteType hft hconn hnd hall hW
  let v : ℂ ⊗[R] M := ∑ i : b.support, y i ⊗ₜ[R] P.root i; obtain ⟨j₀⟩ := ‹Nonempty ι›
  refine ⟨v, fun hv0 ↦ hy_reg j₀ ((b.liftBaseChange_coroot'_sum_tmul_root j₀ y).symm.trans <|
      (congrArg _ hv0).trans (map_zero _)),
    by rw [Representation.baseChange_apply, hW.baseChange_weylGroupRootRep_sum_tmul_root y, hy_eig]
       simp [c, v, Finset.smul_sum, smul_tmul'],
    hprim, fun j ↦ b.liftBaseChange_coroot'_sum_tmul_root j y ▸ hy_reg j, fun g hg ↦ ?_⟩
  obtain ⟨lg, rfl⟩ := exists_wordProd_eq P b g; have hG := b.actsBy_wordProd lg
  rw [Representation.baseChange_apply, hG.baseChange_weylGroupRootRep_sum_tmul_root y] at hg
  exact hy_stab _ _ hG (b.sum_tmul_root_injective_of_isFiniteType hft hg)

/-- **Complexified weight-space regular primitive-root eigenvector**: for any finite, reduced,
irreducible, crystallographic root pairing `P` over a char-0 domain `R` with `[Algebra R ℂ]`, every
`c = wordProd P b l` of order `h = orderOf c` has a nonzero `exp (2πi / h)`-eigenvector
`v : ℂ ⊗[R] M` lying outside every complexified coroot hyperplane with trivial Weyl stabilizer. -/
theorem exists_eigenvector_baseChange_weylGroupRootRep_wordProd [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : ℂ ⊗[R] M,
      v ≠ 0 ∧ P.weylGroupRootRep.baseChange ℂ c v = ζ • v ∧
      IsPrimitiveRoot ζ (orderOf c) ∧
      (∀ j : ι, LinearMap.liftBaseChange ℂ (Algebra.linearMap R ℂ ∘ₗ P.coroot' j) v ≠ 0) ∧
      (∀ g : P.weylGroup, P.weylGroupRootRep.baseChange ℂ g v = v → g = 1) := by
  by_cases hne : Nonempty ι
  · have : NeZero (2 : R) := ⟨by norm_num⟩
    exact b.exists_eigenvector_baseChange_weylGroupRootRep_wordProd_of_isFiniteType
      (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall
  · have : IsEmpty ι := not_nonempty_iff.mp hne; exact exists_eigenvector_baseChange_isEmpty b l

end BaseChangeWeightSpace

/-! ### Weight-space regular primitive-root eigenvectors over `K` and `ℂ` -/

section FieldRootSystem

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] {P : RootPairing ι K M N} [Finite ι] [P.IsCrystallographic]
  [P.IsReduced]

omit [Finite ι] [P.IsReduced] in
private theorem sum_map_smul_root_injective_of_isFiniteType (b : P.Base)
    (hft : IsFiniteType b.cartanMatrix) (φ : ℂ →+* K) :
    Function.Injective (fun u : b.support → ℂ ↦ ∑ i : b.support, φ (u i) • P.root i) := by
  classical
  refine fun u₁ u₂ h ↦ Matrix.mulVec_injective_of_isUnit (hft.transpose.isUnit_map ℂ)
    (funext fun k ↦ φ.injective <| by
      have hk := congrArg (P.coroot' (k : ι)) h
      simp only [b.coroot'_sum_map_smul_root, corootEval_coe_support] at hk
      simpa [mulVec, dotProduct] using hk)

/-- **Steinberg's regular primitive-root eigenvector in `M` along a ring homomorphism `ℂ →+* K`**
(Cartan-matrix form): for a base `b` of a nonempty finite crystallographic reduced root pairing over
a field `K` equipped with `φ : ℂ →+* K`, when `b.cartanMatrix` is of finite type with preconnected
Dynkin diagram, every Coxeter element `c = wordProd P b l` of order `h = orderOf c` has a regular
`φ (exp (2πi / h))`-eigenvector in `M` with trivial Weyl stabilizer. -/
theorem exists_isRegularWeight_eigenvector_wordProd_of_ringHom_of_isFiniteType [Nonempty ι]
    (b : P.Base) (hft : IsFiniteType b.cartanMatrix)
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (φ : ℂ →+* K) :
    let c := wordProd P b l
    let μ := φ (Complex.exp (2 * Real.pi * Complex.I / orderOf c))
    ∃ v : M, v ≠ 0 ∧ c • v = μ • v ∧ IsPrimitiveRoot μ (orderOf c) ∧
      P.IsRegularWeight v ∧ MulAction.stabilizer P.weylGroup v = ⊥ := by
  classical
  have : CharZero K := ⟨fun a b h ↦ Nat.cast_injective (R := ℂ) (φ.injective (by simpa using h))⟩
  dsimp only; set c := wordProd P b l; have hW := b.actsBy_wordProd l
  obtain ⟨y, -, hy_eig, hprim, hy_reg, hy_stab⟩ :=
    b.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd_of_isFiniteType hft hconn hnd hall hW
  let v : M := ∑ i : b.support, φ (y i) • P.root i; obtain ⟨j₀⟩ := ‹Nonempty ι›
  refine ⟨v, fun hv0 ↦ (map_ne_zero φ).mpr (hy_reg j₀)
      ((b.coroot'_sum_map_smul_root φ j₀ y).symm.trans ((congrArg _ hv0).trans (map_zero _))),
    by rw [hW.smul_sum_map_smul_root φ y, hy_eig, Finset.smul_sum]
       refine Finset.sum_congr rfl fun k _ ↦ ?_
       rw [Pi.smul_apply, smul_eq_mul, map_mul, smul_smul],
    hprim.map_of_injective φ.injective,
    (P.isRegularWeight_iff v).mpr fun j ↦ by
      rw [b.coroot'_sum_map_smul_root φ j y]; exact (map_ne_zero φ).mpr (hy_reg j),
    eq_bot_iff.mpr fun g hg ↦ ?_⟩
  obtain ⟨lg, rfl⟩ := exists_wordProd_eq P b g; have hG := b.actsBy_wordProd lg
  rw [MulAction.mem_stabilizer_iff, hG.smul_sum_map_smul_root φ y] at hg
  exact hy_stab _ _ hG (b.sum_map_smul_root_injective_of_isFiniteType hft φ hg)

private theorem exists_isRegularWeight_eigenvector_isEmpty [CharZero K] [P.IsIrreducible]
    [IsEmpty ι] (b : P.Base) (l : List b.support) :
    let c := wordProd P b l
    ∃ v : M, v ≠ 0 ∧ c • v = (1 : K) • v ∧ IsPrimitiveRoot (1 : K) (orderOf c) ∧
      P.IsRegularWeight v ∧ MulAction.stabilizer P.weylGroup v = ⊥ := by
  have := IsIrreducible.nontrivial (P := P); obtain ⟨v, hv⟩ := exists_ne (0 : M)
  have hl_nil (lg : List b.support) : lg = [] := List.eq_nil_iff_forall_not_mem.mpr (by simp)
  refine ⟨v, hv, by simp [hl_nil l], by simp [hl_nil l], (P.isRegularWeight_iff v).mpr
    fun j ↦ (IsEmpty.false j).elim, eq_bot_iff.mpr fun g _ ↦ by
      obtain ⟨lg, rfl⟩ := exists_wordProd_eq P b g; simp [hl_nil lg]⟩

/-- **Steinberg's regular primitive-root eigenvector in `M` along a ring homomorphism `ℂ →+* K`**:
every Coxeter element of an irreducible finite crystallographic reduced root pairing over a field
`K` equipped with `φ : ℂ →+* K` has a regular `φ (exp (2πi / h))`-eigenvector with trivial Weyl
stabilizer. -/
theorem exists_isRegularWeight_eigenvector_wordProd_of_ringHom [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (φ : ℂ →+* K) :
    let c := wordProd P b l
    let μ := φ (Complex.exp (2 * Real.pi * Complex.I / orderOf c))
    ∃ v : M, v ≠ 0 ∧ c • v = μ • v ∧ IsPrimitiveRoot μ (orderOf c) ∧
      P.IsRegularWeight v ∧ MulAction.stabilizer P.weylGroup v = ⊥ := by
  have : CharZero K := ⟨fun a b h ↦ Nat.cast_injective (R := ℂ) (φ.injective (by simpa using h))⟩
  by_cases hne : Nonempty ι
  · exact b.exists_isRegularWeight_eigenvector_wordProd_of_ringHom_of_isFiniteType
      (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall φ
  · have : IsEmpty ι := not_nonempty_iff.mp hne
    have hl_nil : l = [] := List.eq_nil_iff_forall_not_mem.mpr fun i _ ↦ IsEmpty.false i.val
    simpa [hl_nil, Complex.exp_two_pi_mul_I] using exists_isRegularWeight_eigenvector_isEmpty b l

section AlgClosed

variable [Algebra ℝ K] [IsAlgClosed K]

/-- **Steinberg's regular primitive-root eigenvector in `M`** (Cartan-matrix form): for a base `b`
of a nonempty finite crystallographic reduced root pairing over an algebraically closed field `K`
containing `ℝ`, when `b.cartanMatrix` is of finite type with preconnected Dynkin diagram, every
Coxeter element `c = wordProd P b l` of order `h = orderOf c` has a regular eigenvector in `M` with
trivial Weyl stabilizer whose eigenvalue is a primitive `h`-th root of unity. -/
theorem exists_isRegularWeight_eigenvector_wordProd_of_isFiniteType [Nonempty ι] (b : P.Base)
    (hft : IsFiniteType b.cartanMatrix) (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    let c := wordProd P b l
    ∃ (v : M) (μ : K), v ≠ 0 ∧ c • v = μ • v ∧ IsPrimitiveRoot μ (orderOf c) ∧
      P.IsRegularWeight v ∧ MulAction.stabilizer P.weylGroup v = ⊥ := by
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) two_pos
  obtain ⟨v, hv_ne, hv_eig, hprim, hv_reg, hv_stab⟩ :=
    b.exists_isRegularWeight_eigenvector_wordProd_of_ringHom_of_isFiniteType hft hconn hnd hall
      (Complex.liftAux i (sq i ▸ hi)).toRingHom
  exact ⟨v, _, hv_ne, hv_eig, hprim, hv_reg, hv_stab⟩

/-- **Every Coxeter element of an irreducible finite crystallographic reduced root pairing over an
algebraically closed field `K` containing `ℝ` has a regular primitive-root eigenvector with trivial
Weyl stabilizer.** -/
theorem exists_isRegularWeight_eigenvector_wordProd [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    let c := wordProd P b l
    ∃ (v : M) (μ : K), v ≠ 0 ∧ c • v = μ • v ∧ IsPrimitiveRoot μ (orderOf c) ∧
      P.IsRegularWeight v ∧ MulAction.stabilizer P.weylGroup v = ⊥ := by
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) two_pos
  obtain ⟨v, hv_ne, hv_eig, hprim, hv_reg, hv_stab⟩ :=
    b.exists_isRegularWeight_eigenvector_wordProd_of_ringHom hnd hall
      (Complex.liftAux i (sq i ▸ hi)).toRingHom
  exact ⟨v, _, hv_ne, hv_eig, hprim, hv_reg, hv_stab⟩

end AlgClosed

end FieldRootSystem

section Complex

variable {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  {P : RootPairing ι ℂ M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- **Regular `exp (2πi / h)`-eigenvector in `M`** (Cartan-matrix form): over `ℂ`, the eigenvalue
can be taken to be `exp (2πi / orderOf c)`. -/
theorem exists_isRegularWeight_eigenvector_exp_two_pi_I_div_orderOf_wordProd_of_isFiniteType
    [Nonempty ι] (b : P.Base) (hft : IsFiniteType b.cartanMatrix)
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : M, v ≠ 0 ∧ c • v = ζ • v ∧ IsPrimitiveRoot ζ (orderOf c) ∧
      P.IsRegularWeight v ∧ MulAction.stabilizer P.weylGroup v = ⊥ :=
  b.exists_isRegularWeight_eigenvector_wordProd_of_ringHom_of_isFiniteType hft hconn hnd hall
    (RingHom.id ℂ)

/-- **Every Coxeter element of an irreducible finite complex crystallographic reduced root pairing
has a regular `exp (2πi / h)`-eigenvector with trivial Weyl stabilizer.** -/
theorem exists_isRegularWeight_eigenvector_exp_two_pi_I_div_orderOf_wordProd [P.IsIrreducible]
    (b : P.Base) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    let c := wordProd P b l
    let ζ := Complex.exp (2 * Real.pi * Complex.I / orderOf c)
    ∃ v : M, v ≠ 0 ∧ c • v = ζ • v ∧ IsPrimitiveRoot ζ (orderOf c) ∧
      P.IsRegularWeight v ∧ MulAction.stabilizer P.weylGroup v = ⊥ :=
  b.exists_isRegularWeight_eigenvector_wordProd_of_ringHom hnd hall (RingHom.id ℂ)

end Complex

end RootPairing.Base

namespace RootPairing

/-- **Steinberg's regular eigenvector of the bipartite Coxeter element.** Let `b` be a base of a
finite irreducible reduced crystallographic root system over a field `K` which contains `ℝ` and is
algebraically closed, such as `ℂ`. For every colouring of its Dynkin diagram by `Bool`, the
bipartite Coxeter element `c` has a regular eigenvector, one on which no coroot vanishes, whose
eigenvalue is a primitive root of unity of order exactly the order of `c`. -/
theorem exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot
    {ι K M N : Type*} [Field K] [CharZero K] [Algebra ℝ K] [IsAlgClosed K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (P : RootPairing ι K M N) (b : P.Base) [Finite ι] [Nonempty ι]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (c : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    ∃ (x : M) (μ : K), P.IsRegularWeight x ∧
      (weylCoxeterSystem P b).bipartiteCoxeterElement c • x = μ • x ∧
      IsPrimitiveRoot μ (orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement c)) := by
  obtain ⟨l₁, l₂, -, -, hnd, hall, hw⟩ :=
    (weylCoxeterSystem P b).exists_wordProd_eq_bipartiteCoxeterElement c
  rw [weylCoxeterSystem_wordProd] at hw
  obtain ⟨x, μ, -, hx_eig, hμ, hx_reg, -⟩ :=
    b.exists_isRegularWeight_eigenvector_wordProd_of_isFiniteType (isFiniteType_cartanMatrix b)
      (preconnected_diagramGraph_cartanMatrix b) hnd hall
  exact ⟨x, μ, hx_reg, hw ▸ hx_eig, hw ▸ hμ⟩

end RootPairing
