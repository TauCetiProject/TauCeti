/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.TensorProduct.Pi
import TauCeti.Algebra.Module.Torsion.PrimaryComponent

/-!
# Torsion in tensor products

An annihilator of either factor annihilates its tensor product with an arbitrary module.
Similarly, the tensor product of commutative additive monoids is torsion if either factor is
torsion, and the tensor product of an `S`-torsion module on the left with any module over a
commuting base semiring is `S`-torsion (`Module.IsTorsion'.tensorProduct_left`).
No flatness or finite generation is required. These facts supply the tensor closure properties
used in Hurewicz theorems modulo a class of abelian groups.

If an ideal `I` kills one factor and the other factor `X` satisfies `I • X = X`, the tensor
product vanishes. This is how modules killed by an idempotent ideal `m` are seen to be killed by
`m ⊗ -` in almost mathematics.

For an ideal `I` of `R` and an `R`-algebra `S`, scalar extension sends `I`-power torsion to
`IS`-power torsion, where `IS` is the extended ideal `I.map (algebraMap R S)`: if `J` kills `m`,
then `JS` kills `1 ⊗ m`. Conversely, for finitely generated `I`, flat scalar extension of a module
without `I`-power torsion has no `IS`-power torsion.

Extending the scalars of an abelian group `G` to a `ℚ`-vector space `A`, for instance a division
ring of characteristic zero, kills its elements of finite additive order
(`TauCeti.tmul_eq_zero_of_isOfFinAddOrder`), so `A ⊗[ℤ] G` sees `G` only modulo torsion; for
instance `ℝ ⊗[ℤ] H²(X; ℤ)` forgets torsion classes. In particular, when `A` is moreover a ring, a
set generating `G` modulo torsion spans `A ⊗[ℤ] G` over `A`
(`TauCeti.span_one_tmul_eq_top_of_isOfFinAddOrder`).

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Math. 1800, Springer (2003),
  Remark 2.1.4(i).
-/

public section

open scoped TensorProduct Pointwise

namespace TauCeti

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

/-- An annihilator for a commuting scalar action on the left factor annihilates the tensor
product. This includes integer annihilators of modules over any commutative ring. -/
theorem isTorsionBy_tensorProduct_left {S : Type*} [Semiring S] [Module S M]
    [SMulCommClass R S M] {r : S} (h : Module.IsTorsionBy S M r) :
    Module.IsTorsionBy S (M ⊗[R] N) r := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => rw [TensorProduct.smul_tmul', h (x := x), TensorProduct.zero_tmul]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- An annihilator of the right factor annihilates the tensor product when the scalar action
can be moved between its factors. -/
theorem isTorsionBy_tensorProduct_right {S : Type*} [Semiring S] [Module S M]
    [Module S N] [SMulCommClass R S M] [TensorProduct.CompatibleSMul R S M N] {r : S}
    (h : Module.IsTorsionBy S N r) : Module.IsTorsionBy S (M ⊗[R] N) r := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => rw [← TensorProduct.tmul_smul, h (x := y), TensorProduct.tmul_zero]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- Tensoring a torsion commutative additive monoid on the left with any commutative additive
monoid gives a torsion monoid. -/
theorem isAddTorsion_tensorProduct_left (h : IsAddTorsion M) : IsAddTorsion (M ⊗[R] N) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact ((TensorProduct.mk R M N).flip y).toAddMonoidHom.isOfFinAddOrder (h x)
  | add x y hx hy => exact hx.add hy

/-- Tensoring a torsion commutative additive monoid on the right with any commutative additive
monoid gives a torsion monoid. -/
theorem isAddTorsion_tensorProduct_right (h : IsAddTorsion N) : IsAddTorsion (M ⊗[R] N) := by
  intro t
  obtain ⟨u, rfl⟩ := (TensorProduct.comm R N M).surjective t
  exact (TensorProduct.comm R N M).toAddMonoidHom.isOfFinAddOrder
    (isAddTorsion_tensorProduct_left h u)

/-- If `I • X = X` and `I` kills `K`, then `X ⊗ K = 0`: for `i ∈ I` one has
`(i • x) ⊗ k = x ⊗ (i • k) = 0`. -/
theorem subsingleton_tensorProduct_of_isTorsionBySet_right {I : Ideal R}
    (hM : I • (⊤ : Submodule R M) = ⊤) (hN : Module.IsTorsionBySet R N I) :
    Subsingleton (M ⊗[R] N) := by
  refine subsingleton_of_forall_eq 0 fun t ↦ ?_
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    have hx : x ∈ I • (⊤ : Submodule R M) := by rw [hM]; exact Submodule.mem_top
    refine Submodule.smul_induction_on (p := fun x ↦ x ⊗ₜ[R] y = 0) hx (fun r hr n _ ↦ ?_)
      fun x y hx hy ↦ by rw [TensorProduct.add_tmul, hx, hy, add_zero]
    rw [TensorProduct.smul_tmul, hN (a := ⟨r, hr⟩), TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- If `I` kills `M` and `I • X = X`, then `M ⊗ X = 0`. -/
theorem subsingleton_tensorProduct_of_isTorsionBySet_left {I : Ideal R}
    (hM : Module.IsTorsionBySet R M I) (hN : I • (⊤ : Submodule R N) = ⊤) :
    Subsingleton (M ⊗[R] N) :=
  have := subsingleton_tensorProduct_of_isTorsionBySet_right hN hM
  (TensorProduct.comm R M N).toEquiv.subsingleton

end TauCeti

namespace TauCeti

open TensorProduct Submodule Function

section Semiring

variable {R S M : Type*} [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M]
  [Module R M]

/-- If an ideal `J` kills `m`, then the extended ideal `JS` kills `1 ⊗ m`. -/
theorem map_le_torsionOf_one_tmul {J : Ideal R} {m : M}
    (hm : m ∈ torsionBySet R M J) :
    J.map (algebraMap R S) ≤ Ideal.torsionOf S (S ⊗[R] M) (1 ⊗ₜ m) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, algebraMap_smul, ← tmul_smul,
    (mem_torsionBySet_iff _ _).mp hm ⟨a, ha⟩, tmul_zero]

end Semiring

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {I : Ideal R}
  {M : Type*} [AddCommGroup M] [Module R M]

/-- Base change sends `I`-power torsion elements to `IS`-power torsion elements. -/
theorem one_tmul_mem_primaryComponent_map {m : M} (hm : m ∈ I.primaryComponent M) :
    (1 : S) ⊗ₜ[R] m ∈ (I.map (algebraMap R S)).primaryComponent (S ⊗[R] M) := by
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem _ _ _).mp hm
  refine (Ideal.primaryComponent_mem _ _ _).mpr ⟨n, (mem_torsionBySet_iff _ _).mpr fun a ↦ ?_⟩
  rw [← Ideal.mem_torsionOf_iff]
  exact map_le_torsionOf_one_tmul hn (by rw [Ideal.map_pow]; exact a.property)

/-- The base change of an `I`-power torsion module is `IS`-power torsion. -/
theorem primaryComponent_map_tensorProduct_eq_top (hM : I.primaryComponent M = ⊤) :
    (I.map (algebraMap R S)).primaryComponent (S ⊗[R] M) = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ x.inductionOn (fun s m ↦ ?_) fun _ _ ↦ add_mem
  rw [← mul_one s, ← smul_eq_mul, ← smul_tmul']
  exact smul_mem _ s (one_tmul_mem_primaryComponent_map (hM ▸ mem_top))

/-- Flat base change of a module without `I`-power torsion has no `IS`-power torsion, for
finitely generated `I`. -/
theorem primaryComponent_map_tensorProduct_eq_bot [Module.Flat R S] (hI : I.FG)
    (hM : I.primaryComponent M = ⊥) :
    (I.map (algebraMap R S)).primaryComponent (S ⊗[R] M) = ⊥ := by
  classical
  obtain ⟨G, rfl⟩ := hI
  refine eq_bot_iff.mpr fun y hy ↦ ?_
  rw [Ideal.map_span, ← Finset.coe_image, Ideal.mem_primaryComponent_span_iff] at hy
  choose! n hn using fun g (hg : g ∈ G) ↦ hy _ (Finset.mem_image_of_mem _ hg)
  -- A single power `N` of every generator kills `y`.
  set N := G.sup n
  have hN (g : G) : (g.val ^ N) • y = 0 := by
    rw [← algebraMap_smul S, map_pow, ← pow_mul_pow_sub _ (Finset.le_sup g.property), mul_comm,
      mul_smul, hn _ g.property, smul_zero]
  -- Multiplication by the powers `g ^ N` is jointly injective on `M`, hence on `S ⊗[R] M`.
  let φ : M →ₗ[R] G → M := LinearMap.pi fun g ↦ g.val ^ N • LinearMap.id
  have hφ : Injective φ := by
    refine (injective_iff_map_eq_zero _).mpr fun m hm ↦ ?_
    have : m ∈ (Ideal.span (G : Set R)).primaryComponent M :=
      (Ideal.mem_primaryComponent_span_iff G).mpr fun g hg ↦ ⟨N, congr_fun hm ⟨g, hg⟩⟩
    rwa [hM, mem_bot] at this
  have key (x : S ⊗[R] M) :
      piRight R R S (fun _ : G ↦ M) (φ.lTensor S x) = fun g ↦ g.val ^ N • x := by
    induction x using TensorProduct.inductionOn with
    | tmul s m => ext g; simp [φ, piRightHom_tmul, tmul_smul]
    | add x y hx hy => ext g; simp_all [smul_add]
  refine (mem_bot S).mpr (Module.Flat.lTensor_preserves_injective_linearMap φ hφ ?_)
  apply (piRight R R S fun _ : G ↦ M).injective
  rw [key, map_zero, map_zero]
  exact funext hN

/-- An element of finite additive order of an abelian group dies after extending scalars to a
`ℚ`-vector space, for instance a division ring of characteristic zero: if `n • m = 0` with `n > 0`,
then `a ⊗ m = (n⁻¹ a) ⊗ (n • m) = 0`. So `A ⊗[ℤ] G` sees `G` only modulo torsion. -/
theorem tmul_eq_zero_of_isOfFinAddOrder {A G : Type*} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup G] (a : A) {m : G} (hm : IsOfFinAddOrder m) : a ⊗ₜ[ℤ] m = 0 := by
  obtain ⟨n, hn, hnm⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hm
  calc a ⊗ₜ[ℤ] m = ((n : ℤ) • ((n : ℚ)⁻¹ • a)) ⊗ₜ[ℤ] m := by
        rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_inv_smul₀ (Nat.cast_ne_zero.mpr hn.ne')]
    _ = 0 := by rw [TensorProduct.smul_tmul, natCast_zsmul, hnm, TensorProduct.tmul_zero]

/-- If a set `s` generates an abelian group `G` modulo torsion, that is, every element of `G`
differs from an element of the subgroup generated by `s` by an element of finite additive order,
then the tensors `1 ⊗ x`, `x ∈ s`, span the scalar extension `A ⊗[ℤ] G` to a ring `A` that is a
`ℚ`-vector space, for instance a division ring of characteristic zero. -/
theorem span_one_tmul_eq_top_of_isOfFinAddOrder {A G : Type*} [Ring A] [Module ℚ A]
    [AddCommGroup G] {s : Set G}
    (hs : ∀ x : G, ∃ y ∈ AddSubgroup.closure s, IsOfFinAddOrder (x - y)) :
    Submodule.span A ((fun x ↦ (1 : A) ⊗ₜ[ℤ] x) '' s) = ⊤ := by
  -- The span is the base change of the subgroup generated by `s`.
  simp only [← TensorProduct.mk_apply, ← Submodule.baseChange_span]
  refine Submodule.eq_top_iff'.mpr fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => exact add_mem hz hz'
  | tmul r x =>
    obtain ⟨y, hy, hxy⟩ := hs x
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup] at hy
    rw [← sub_add_cancel x y, TensorProduct.tmul_add, tmul_eq_zero_of_isOfFinAddOrder r hxy,
      zero_add]
    exact Submodule.tmul_mem_baseChange_of_mem r hy

end TauCeti

namespace Module.IsTorsion'

/-- Tensoring an `S`-torsion module on the left with any module over a commuting base semiring
yields an `S`-torsion module. -/
theorem tensorProduct_left {R R₀ M N : Type*} [CommSemiring R] [CommSemiring R₀]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Module R₀ M]
    [SMulCommClass R R₀ M] {S : Submonoid R₀} (hM : Module.IsTorsion' M S) :
    Module.IsTorsion' (M ⊗[R] N) S := fun t ↦ by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨s, hs⟩ := @hM x
    exact ⟨s, by rw [Submonoid.smul_def, TensorProduct.smul_tmul', ← Submonoid.smul_def, hs,
      TensorProduct.zero_tmul]⟩
  | add x y hx hy =>
    obtain ⟨s₁, hs₁⟩ := hx
    obtain ⟨s₂, hs₂⟩ := hy
    have h₁ : (s₁ * s₂) • x = 0 := by rw [mul_comm, mul_smul, hs₁, smul_zero]
    have h₂ : (s₁ * s₂) • y = 0 := by rw [mul_smul, hs₂, smul_zero]
    exact ⟨s₁ * s₂, by simp [smul_add, h₁, h₂]⟩

end Module.IsTorsion'
