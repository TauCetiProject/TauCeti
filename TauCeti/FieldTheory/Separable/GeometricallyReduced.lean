/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.TranscendentalSeparable
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import TauCeti.RingTheory.AlgebraicIndependent.BaseChange
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Geometrically reduced field extensions and separable generation

Let `k` be a field of exponential characteristic `p` and `A` a commutative `k`-algebra which is
geometrically reduced, i.e. `AlgebraicClosure k ⊗[k] A` is reduced. Then the `p`-th powers of
`k`-linearly independent elements of `A` are again `k`-linearly independent. Indeed, if
`∑ cᵢ sᵢ ^ p = 0` with `cᵢ ∈ k`, choose `p`-th roots `dᵢ` of the `cᵢ` in the algebraic closure.
Then `∑ dᵢ ⊗ sᵢ` has `p`-th power `1 ⊗ ∑ cᵢ sᵢ ^ p = 0`, so it vanishes; since the `1 ⊗ sᵢ` are
linearly independent over the algebraic closure, every `dᵢ`, hence every `cᵢ`, is zero.

For a finitely generated field extension `K / k`, Mathlib's
`exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType` turns this
linear independence into a finite separating transcendence basis. Conversely, any separably
generated field extension `K / k` (`Algebra.IsSeparablyGenerated k K`, not necessarily finitely
generated) keeps every reduced `k`-algebra `A` reduced under `K ⊗[k] A`: the pure transcendental
subextension `k(s)` is the fraction field of a polynomial ring `k[s]`, whose tensor product with
`A` is `A[s]`, and `K / k(s)` is separable algebraic. Passing to finitely generated subextensions
identifies geometric reducedness of an arbitrary field extension `K / k` with
`Algebra.IsTranscendentalSeparable k K`. Consequently:

* For any geometrically reduced field extension `K / k` and any reduced `k`-algebra `A`,
  `K ⊗[k] A` is reduced.
* Geometric reducedness is transitive in towers of field extensions `k → E → F`
  (`Algebra.IsGeometricallyReduced.trans`).

Reducedness after extending scalars to *any* algebraically closed field `L` suffices
(`Algebra.IsGeometricallyReduced.of_isReduced_tensorProduct`, in
`TauCeti.RingTheory.TensorProduct.Reduced`). In particular, a finitely generated field extension
`K / k` with `L ⊗[k] K` a domain is separably generated.

## Main results

* `TauCeti.linearIndepOn_pow_of_isGeometricallyReduced`: in a geometrically reduced algebra, the
  `p`-th powers of `k`-linearly independent elements are `k`-linearly independent.
* `TauCeti.exists_isTranscendenceBasis_and_isSeparable_of_isGeometricallyReduced`: a finitely
  generated geometrically reduced field extension has a finite separating transcendence basis.
* `TauCeti.isReduced_tensorProduct_of_isSeparablyGenerated`,
  `TauCeti.isReduced_tensorProduct_of_isTranscendentalSeparable`,
  `TauCeti.isReduced_tensorProduct_of_isGeometricallyReduced`: tensoring a reduced `k`-algebra with
  a separably generated, transcendentally separable, or geometrically reduced field extension over
  `k` yields a reduced ring.
* `TauCeti.isGeometricallyReduced_iff_isSeparablyGenerated`: for a finitely generated field
  extension `K / k`, `Algebra.IsGeometricallyReduced k K ↔ Algebra.IsSeparablyGenerated k K`.
* `TauCeti.isGeometricallyReduced_iff_isTranscendentalSeparable`: for an arbitrary field extension
  `K / k`, `Algebra.IsGeometricallyReduced k K ↔ Algebra.IsTranscendentalSeparable k K`.
* `Algebra.IsGeometricallyReduced.trans`: transitivity of geometric reducedness for field towers
  `k → E → F`.

## References

* [The Stacks project, Tag 030W](https://stacks.math.columbia.edu/tag/030W)
* [The Stacks project, Tag 037R](https://stacks.math.columbia.edu/tag/037R)
* S. Lang, *Introduction to Algebraic Geometry*, Chapter III, Section 1.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {k : Type*} [Field k]

/-- In a geometrically reduced commutative algebra over a field `k` of exponential characteristic
`p`, the `p`-th powers of `k`-linearly independent elements are `k`-linearly independent. -/
theorem linearIndepOn_pow_of_isGeometricallyReduced {A : Type*} [CommRing A] [Algebra k A]
    (p : ℕ) [ExpChar k p] [Algebra.IsGeometricallyReduced k A] {s : Set A}
    (hs : LinearIndepOn k id s) : LinearIndepOn k (· ^ p) s := by
  classical
  let K := AlgebraicClosure k
  -- A choice of `p`-th roots in the algebraic closure, with the root of `0` equal to `0`.
  have hroot (c : k) : ∃ d : K, d ^ p = algebraMap k K c :=
    IsAlgClosed.exists_pow_nat_eq _ (expChar_pos k p)
  let g : k → K := fun c ↦ (hroot c).choose
  have hg (c : k) : g c ^ p = algebraMap k K c := (hroot c).choose_spec
  have hg0 : g 0 = 0 := by
    simpa [(expChar_pos k p).ne'] using hg 0
  -- The vectors `1 ⊗ a`, `a ∈ s`, are linearly independent over the algebraic closure.
  have hs' : LinearIndepOn K (fun a : A ↦ (1 : K) ⊗ₜ[k] a) s :=
    Module.Flat.linearIndependent_one_tmul hs
  rw [linearIndepOn_iff] at hs' ⊢
  intro l hl hl0
  let l' : A →₀ K := l.mapRange g hg0
  have hsum : Finsupp.linearCombination K (fun a : A ↦ (1 : K) ⊗ₜ[k] a) l' =
      ∑ a ∈ l.support, g (l a) ⊗ₜ[k] a := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
    simp [Finsupp.sum, TensorProduct.smul_tmul']
  -- The combination `∑ g (l a) ⊗ a` has `p`-th power `1 ⊗ ∑ l a • a ^ p = 0`, so it vanishes.
  have hzero : ∑ a ∈ l.support, g (l a) ⊗ₜ[k] a = 0 := by
    rcases subsingleton_or_nontrivial (K ⊗[k] A) with _ | _
    · exact Subsingleton.elim _ _
    have := expChar_of_injective_algebraMap (algebraMap k (K ⊗[k] A)).injective p
    refine IsReduced.eq_zero _ ⟨p, ?_⟩
    rw [sum_pow_char]
    simp_rw [Algebra.TensorProduct.tmul_pow, hg, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hl0
    rw [← TensorProduct.tmul_sum, hl0, TensorProduct.tmul_zero]
  have hl'0 : l' = 0 := by
    refine hs' l' ?_ (hsum.trans hzero)
    rw [Finsupp.mem_supported] at hl ⊢
    exact (Finset.coe_subset.2 Finsupp.support_mapRange).trans hl
  ext a
  have ha : g (l a) = 0 := by simpa [l'] using congr($hl'0 a)
  have := hg (l a)
  rw [ha, zero_pow (expChar_pos k p).ne', eq_comm, map_eq_zero] at this
  simpa using this

section SeparablyGenerated

open scoped IntermediateField.algebraAdjoinAdjoin

variable (k) (K : Type*) [Field K] [Algebra k K]

/-- **A finitely generated geometrically reduced field extension is separably generated**: it has
a finite transcendence basis `s` such that `K` is separable algebraic over `k(s)`. -/
theorem exists_isTranscendenceBasis_and_isSeparable_of_isGeometricallyReduced
    [Algebra.EssFiniteType k K] [Algebra.IsGeometricallyReduced k K] :
    ∃ s : Finset K, IsTranscendenceBasis k ((↑) : s → K) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K := by
  obtain _ | ⟨p, ⟨hp⟩, _⟩ := CharP.exists' k
  · exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  · have : ExpChar k p := .prime hp
    exact exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType p hp
      fun _ hs ↦ linearIndepOn_pow_of_isGeometricallyReduced p hs

/-- A finitely generated geometrically reduced field extension satisfies
`Algebra.IsSeparablyGenerated`. -/
theorem isSeparablyGenerated_of_isGeometricallyReduced [Algebra.EssFiniteType k K]
    [Algebra.IsGeometricallyReduced k K] : Algebra.IsSeparablyGenerated k K :=
  let ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_isGeometricallyReduced k K
  ⟨s, hs, hsep⟩

variable {k K}

/-- If `K / k` is separably generated (not necessarily finitely generated), then `K ⊗[k] A` is
reduced for every reduced commutative `k`-algebra `A`. -/
theorem isReduced_tensorProduct_of_isSeparablyGenerated [Algebra.IsSeparablyGenerated k K]
    (A : Type*) [CommRing A] [IsReduced A] [Algebra k A] : IsReduced (K ⊗[k] A) := by
  obtain ⟨s, hs, hsep⟩ := Algebra.IsSeparablyGenerated.isSeparable (k := k) (K := K)
  set R := Algebra.adjoin k s
  set E := IntermediateField.adjoin k s
  let eRA : R ⊗[k] A ≃ₐ[k] MvPolynomial s A := hs.1.adjoinTensorAlgEquiv A
  have : IsReduced (R ⊗[k] A) := isReduced_of_injective eRA eRA.injective
  have : IsReduced (E ⊗[k] A) :=
    isReduced_tensorProduct_of_isLocalization (nonZeroDivisors R) E A
  exact isReduced_tensorProduct_of_isReduced_of_isSeparable k (E := E) A

/-- Any separably generated field extension is geometrically reduced. -/
theorem isGeometricallyReduced_of_isSeparablyGenerated [Algebra.IsSeparablyGenerated k K] :
    Algebra.IsGeometricallyReduced k K := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  have := isReduced_tensorProduct_of_isSeparablyGenerated (k := k) (K := K) (AlgebraicClosure k)
  exact isReduced_of_injective (Algebra.TensorProduct.comm k (AlgebraicClosure k) K)
    (Algebra.TensorProduct.comm k (AlgebraicClosure k) K).injective

/-- For a finitely generated field extension `K / k`, geometric reducedness is equivalent to
separable generation. -/
theorem isGeometricallyReduced_iff_isSeparablyGenerated (k K : Type*) [Field k] [Field K]
    [Algebra k K] [Algebra.EssFiniteType k K] :
    Algebra.IsGeometricallyReduced k K ↔ Algebra.IsSeparablyGenerated k K :=
  ⟨fun _ ↦ isSeparablyGenerated_of_isGeometricallyReduced k K,
    fun _ ↦ isGeometricallyReduced_of_isSeparablyGenerated⟩

/-- If every finitely generated subextension of `K / k` is separably generated
(`Algebra.IsTranscendentalSeparable k K`), then `K ⊗[k] A` is reduced for every reduced
commutative `k`-algebra `A`. -/
theorem isReduced_tensorProduct_of_isTranscendentalSeparable
    [Algebra.IsTranscendentalSeparable k K] (A : Type*) [CommRing A] [IsReduced A] [Algebra k A] :
    IsReduced (K ⊗[k] A) := by
  have : IsReduced (A ⊗[k] K) := by
    apply IsReduced.tensorProduct_of_flat_of_forall_fg
    intro B hB
    obtain ⟨s, rfl⟩ := hB
    let L : IntermediateField k K := IntermediateField.adjoin k (s : Set K)
    have : Algebra.EssFiniteType k L :=
      IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_finset s)
    have : Algebra.IsSeparablyGenerated k L :=
      Algebra.IsTranscendentalSeparable.forall_isSeparablyGenerated L inferInstance
    have : IsReduced (L ⊗[k] A) := isReduced_tensorProduct_of_isSeparablyGenerated A
    have : IsReduced (A ⊗[k] L) :=
      isReduced_of_injective (Algebra.TensorProduct.comm k A L)
        (Algebra.TensorProduct.comm k A L).injective
    have hle : Algebra.adjoin k (s : Set K) ≤ L.toSubalgebra :=
      IntermediateField.algebra_adjoin_le_adjoin k (s : Set K)
    let i : Algebra.adjoin k (s : Set K) →ₐ[k] L := Subalgebra.inclusion hle
    exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id k A) i)
      (Module.Flat.lTensor_preserves_injective_linearMap i.toLinearMap
        (Subalgebra.inclusion_injective hle))
  exact isReduced_of_injective (Algebra.TensorProduct.comm k K A)
    (Algebra.TensorProduct.comm k K A).injective

/-- For an arbitrary field extension `K / k`, geometric reducedness is equivalent to
`Algebra.IsTranscendentalSeparable k K` (every finitely generated subextension is separably
generated). -/
theorem isGeometricallyReduced_iff_isTranscendentalSeparable (k K : Type*) [Field k] [Field K]
    [Algebra k K] :
    Algebra.IsGeometricallyReduced k K ↔ Algebra.IsTranscendentalSeparable k K := by
  constructor
  · intro _
    refine ⟨fun L _ ↦ ?_⟩
    have : Algebra.IsGeometricallyReduced k L := .of_injective L.val L.val.injective
    exact isSeparablyGenerated_of_isGeometricallyReduced k L
  · intro _
    rw [Algebra.isGeometricallyReduced_field_iff]
    have := isReduced_tensorProduct_of_isTranscendentalSeparable (k := k) (K := K)
      (AlgebraicClosure k)
    exact isReduced_of_injective (Algebra.TensorProduct.comm k (AlgebraicClosure k) K)
      (Algebra.TensorProduct.comm k (AlgebraicClosure k) K).injective

/-- If `K / k` is a geometrically reduced field extension, then `K ⊗[k] A` is reduced for every
reduced commutative `k`-algebra `A`. -/
theorem isReduced_tensorProduct_of_isGeometricallyReduced [Algebra.IsGeometricallyReduced k K]
    (A : Type*) [CommRing A] [IsReduced A] [Algebra k A] : IsReduced (K ⊗[k] A) :=
  have := (isGeometricallyReduced_iff_isTranscendentalSeparable k K).mp inferInstance
  isReduced_tensorProduct_of_isTranscendentalSeparable A

end SeparablyGenerated

end TauCeti

namespace Algebra.IsGeometricallyReduced

/-- **Geometric reducedness is transitive in towers of field extensions**: if `E / k` and `F / E`
are geometrically reduced field extensions, then `F / k` is geometrically reduced. -/
theorem trans (k E F : Type*) [Field k] [Field E] [Field F] [Algebra k E] [Algebra E F]
    [Algebra k F] [IsScalarTower k E F] [IsGeometricallyReduced k E]
    [IsGeometricallyReduced E F] : IsGeometricallyReduced k F := by
  rw [isGeometricallyReduced_field_iff]
  have : IsReduced (E ⊗[k] AlgebraicClosure k) :=
    TauCeti.isReduced_tensorProduct_of_isGeometricallyReduced (AlgebraicClosure k)
  have : IsReduced (F ⊗[E] (E ⊗[k] AlgebraicClosure k)) :=
    TauCeti.isReduced_tensorProduct_of_isGeometricallyReduced (E ⊗[k] AlgebraicClosure k)
  let e : AlgebraicClosure k ⊗[k] F ≃+* F ⊗[E] (E ⊗[k] AlgebraicClosure k) :=
    (Algebra.TensorProduct.comm k (AlgebraicClosure k) F).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange k E E F (AlgebraicClosure k)).symm.toRingEquiv
  exact isReduced_of_injective e e.injective

end Algebra.IsGeometricallyReduced
