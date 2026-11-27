/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic
import TauCeti.NumberTheory.NumberField.Global.Approximation.Strong
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# Strong approximation in the adele ring, omitting finite places

Let `K` be a number field and `S` a set of finite places of `K`. The adeles *supported on `S`*,
`𝔸_S`, are those vanishing at every infinite place and at every finite place outside `S`; they
form an ideal of the adele ring (`NumberField.AdeleRing.supported`).

The diagonal copy of `K` is discrete in the adele ring, so `K + 𝔸_∅ = K` is not dense. As soon as
`S` is nonempty, `K + 𝔸_S` is dense (`NumberField.AdeleRing.dense_range_algebraMap_add_supported`):
this is strong approximation for the additive group, with the infinite places kept and the
finite places of `S` left out. It follows from strong approximation away from one finite place
`v₀ ∈ S` (`TauCeti.GlobalNumberFields.exists_forall_algebraMap_mem_and_forall_norm_le_one`): an
element `x ∈ K` close to a given adele at the infinite places and at finitely many finite places
other than `v₀`, and integral at the other finite places other than `v₀`, differs from the adele
by an element of `𝔸_{v₀}` up to a small error.

Because `𝔸_S` is an ideal, the matrices with entries in `𝔸_S` are stable under left multiplication
by every matrix over the adeles. So for every `x ∈ GL_n(𝔸)` and every index type `κ`, the set
`{x⁻¹ξ + u}`, with `ξ` a matrix over `K` and `u` a matrix over `𝔸_S`, is dense in the `n × κ`
matrices over the adeles
(`NumberField.AdeleRing.dense_range_inv_mul_map_algebraMap_add_supported`).

## Main definitions

* `NumberField.AdeleRing.supported`: the ideal `𝔸_S` of adeles supported on a set `S` of finite
  places.

## Main results

* `NumberField.AdeleRing.dense_range_algebraMap_add_supported`: `K + 𝔸_S` is dense in the adele
  ring for nonempty `S`.
* `NumberField.AdeleRing.dense_range_inv_mul_map_algebraMap_add_supported`: the matrix form,
  after moving by `x⁻¹` for `x ∈ GL_n(𝔸)`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §15.
* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. I,
  2nd ed., Lemma 5.7 (strong approximation for unipotent groups).
-/

public section

noncomputable section

open IsDedekindDomain HeightOneSpectrum Topology
open scoped NumberField Pointwise

namespace NumberField.AdeleRing

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The adeles *supported on* a set `S` of finite places: those vanishing at every infinite place
and at every finite place outside `S`. They form an ideal `𝔸_S` of the adele ring. -/
def supported (S : Set (HeightOneSpectrum R)) : Ideal (AdeleRing R K) where
  carrier := {a | a.1 = 0 ∧ ∀ v ∉ S, a.2 v = 0}
  add_mem' {a b} ha hb := ⟨by rw [fst_add, ha.1, hb.1, add_zero], fun v hv ↦ by
    rw [snd_add, FiniteAdeleRing.add_apply, ha.2 v hv, hb.2 v hv, add_zero]⟩
  zero_mem' := ⟨rfl, fun _ _ ↦ rfl⟩
  smul_mem' c a ha := ⟨by rw [smul_eq_mul, fst_mul, ha.1, mul_zero], fun v hv ↦ by
    rw [smul_eq_mul, snd_mul, FiniteAdeleRing.mul_apply, ha.2 v hv, mul_zero]⟩

variable {R K}

/-- An adele is supported on `S` when it vanishes at every infinite place and at every finite
place outside `S`. -/
@[simp]
theorem mem_supported {S : Set (HeightOneSpectrum R)} {a : AdeleRing R K} :
    a ∈ supported R K S ↔ a.1 = 0 ∧ ∀ v ∉ S, a.2 v = 0 :=
  Iff.rfl

variable (R K) in
/-- The ideal of adeles supported on `S` grows with `S`. -/
theorem supported_mono : Monotone (supported R K) :=
  fun _ _ hST _ ha ↦ ⟨ha.1, fun v hv ↦ ha.2 v fun h ↦ hv (hST h)⟩

variable (R K) in
/-- Only `0` is supported on the empty set of places. -/
@[simp]
theorem supported_empty : supported R K ∅ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun a ha ↦ Prod.ext ha.1 ?_
  exact FiniteAdeleRing.ext K fun v ↦ ha.2 v (Set.notMem_empty v)

/-- The adele that is `z` at the finite place `v` and `0` at every other place, infinite or
finite, is supported on every set of finite places containing `v`. -/
private theorem single_mem_supported {S : Set (HeightOneSpectrum R)} {v : HeightOneSpectrum R}
    (hv : v ∈ S) (z : v.adicCompletion K) :
    ((0, FiniteAdeleRing.single K v z) : AdeleRing R K) ∈ supported R K S :=
  ⟨rfl, fun _ hw ↦ FiniteAdeleRing.single_apply_of_ne (by rintro rfl; exact hw hv) z⟩

variable [NumberField K]

open Classical in
/-- The finite part of strong approximation omitting one finite place `v₀`. Let `a` be a finite
adele integral outside a finite set `J` of places, `I` a finite set of places and `n` exponents.
Let `x ∈ K` satisfy `v(x - a v) ≤ exp (-n v)` at the places of `I ∪ J` other than `v₀`, and be
integral at every other place other than `v₀`. Then the finite adele that is `a v₀` at `v₀` and
`x` elsewhere differs from `a` by an integral finite adele `b` with `v(b v) ≤ exp (-n v)` at the
places of `I`. -/
private theorem finitePart_sub_mem (a : FiniteAdeleRing (𝓞 K) K) (v₀ : HeightOneSpectrum (𝓞 K))
    (I J : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ)
    (hJ : a ∈ FiniteAdeleRing.sIntegralAdeles (𝓞 K) K J) (x : K)
    (hxU : ∀ v ∈ (I ∪ J).erase v₀,
      Valued.v (algebraMap K (v.adicCompletion K) x - a v) ≤ WithZero.exp (-(n v : ℤ)))
    (hxint : ∀ v ∉ (I ∪ J).erase v₀, v ≠ v₀ →
      algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K) :
    let b := algebraMap K (FiniteAdeleRing (𝓞 K) K) x +
      FiniteAdeleRing.single K v₀ (a v₀ - algebraMap K (v₀.adicCompletion K) x) - a
    b ∈ FiniteAdeleRing.integralAdeles (𝓞 K) K ∧
      ∀ v ∈ I, Valued.v (b v) ≤ WithZero.exp (-(n v : ℤ)) := by
  intro b
  -- `b` vanishes at `v₀` and is `x - a v` at every other finite place.
  have hb (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ v₀) :
      b v = algebraMap K (v.adicCompletion K) x - a v := by
    simp [b, algebraMap_adicCompletion, FiniteAdeleRing.single_apply_of_ne hv]
  have hb₀ : b v₀ = 0 := by
    simp [b, algebraMap_adicCompletion]
  refine ⟨FiniteAdeleRing.mem_integralAdeles.2 fun v ↦ ?_, fun v hv ↦ ?_⟩
  · rcases eq_or_ne v v₀ with rfl | hv₀
    · rw [hb₀]
      exact zero_mem _
    rw [hb v hv₀]
    by_cases hvS : v ∈ (I ∪ J).erase v₀
    · rw [mem_adicCompletionIntegers]
      exact (hxU v hvS).trans (WithZero.exp_le_exp.2 (by omega))
    · have hvJ : v ∉ J := fun h ↦ hvS (Finset.mem_erase.2 ⟨hv₀, Finset.mem_union_right _ h⟩)
      exact sub_mem (hxint v hvS hv₀) (FiniteAdeleRing.mem_sIntegralAdeles.1 hJ v hvJ)
  · rcases eq_or_ne v v₀ with rfl | hv₀
    · simp [hb₀]
    rw [hb v hv₀]
    exact hxU v (Finset.mem_erase.2 ⟨hv₀, Finset.mem_union_left _ hv⟩)

/-- Strong approximation omitting a single finite place `v₀`: `K + 𝔸_{v₀}` is dense in the
adele ring. -/
private theorem dense_range_algebraMap_add_supported_singleton (v₀ : HeightOneSpectrum (𝓞 K)) :
    Dense (Set.range (algebraMap K (AdeleRing (𝓞 K) K)) +
      (supported (𝓞 K) K {v₀} : Set (AdeleRing (𝓞 K) K))) := by
  classical
  refine fun a ↦ mem_closure_iff_nhds.2 fun W hW ↦ ?_
  -- A neighbourhood of `a` contains a product of a box around the infinite part and a
  -- neighbourhood of the finite part, which in turn contains a basic congruence neighbourhood.
  obtain ⟨Winf, hWinf, Wf, hWf, hsub⟩ := mem_nhds_prod_iff.1 hW
  rw [show 𝓝 a.1 = Filter.pi fun w ↦ 𝓝 (a.1 w) from nhds_pi] at hWinf
  obtain ⟨Iinf, -, t, ht, hIt⟩ := Filter.mem_pi.1 hWinf
  have hWf0 : (a.2 + ·) ⁻¹' Wf ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) :=
    (continuous_const_add a.2).continuousAt.preimage_mem_nhds (by rwa [add_zero])
  obtain ⟨I, n, hIn⟩ := FiniteAdeleRing.exists_finset_forall_mem_of_mem_nhds_zero hWf0
  obtain ⟨J, hJ⟩ := FiniteAdeleRing.exists_finset_mem_sIntegralAdeles a.2
  -- Strong approximation away from `v₀` gives the rational part `x`.
  obtain ⟨x, hxU, hxV, hxint⟩ :=
    TauCeti.GlobalNumberFields.exists_forall_algebraMap_mem_and_forall_norm_le_one (.inl v₀)
      ((I ∪ J).erase v₀) Finset.univ
      (fun v hv h ↦ (Finset.mem_erase.1 hv).1 (Sum.inl_injective h)) (fun _ _ ↦ Sum.inr_ne_inl)
      (fun v ↦ (· - a.2 v) ⁻¹' {z | Valued.v z ≤ WithZero.exp (-(n v : ℤ))})
      (fun w ↦ interior (t w))
      (fun v _ ↦ ⟨(isOpen_setOf_valued_le v WithZero.exp_ne_zero).preimage
        (continuous_sub_right _), a.2 v, by simp⟩)
      (fun w _ ↦ ⟨isOpen_interior, a.1 w, mem_interior_iff_mem_nhds.2 (ht w)⟩)
  obtain ⟨hb, hbI⟩ := finitePart_sub_mem a.2 v₀ I J n hJ x hxU fun v hv hv₀ ↦
    (FinitePlace.mk_apply_le_one_iff_algebraMap_mem v x).1 <| by
      simpa using hxint v hv (Sum.inl_injective.ne hv₀)
  refine ⟨_, hsub ⟨hIt fun w _ ↦ ?_, ?_⟩, ⟨_, ⟨x, rfl⟩, _,
    single_mem_supported (Set.mem_singleton v₀) (a.2 v₀ - algebraMap K _ x), rfl⟩⟩
  · convert interior_subset (hxV w (Finset.mem_univ w)) using 1
    simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
  · simpa using hIn _ hb hbI

/-- **Strong approximation omitting finite places.** For a nonempty set `S` of finite places of a
number field `K`, the sum `K + 𝔸_S` of the diagonal copy of `K` and the adeles supported on `S` is
dense in the adele ring.

Some place must be left out: for `S = ∅` the sum is the diagonal copy of `K`, which is
discrete. -/
theorem dense_range_algebraMap_add_supported {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Nonempty) :
    Dense (Set.range (algebraMap K (AdeleRing (𝓞 K) K)) +
      (supported (𝓞 K) K S : Set (AdeleRing (𝓞 K) K))) := by
  obtain ⟨v₀, hv₀⟩ := hS
  exact (dense_range_algebraMap_add_supported_singleton v₀).mono <| Set.add_subset_add_left <|
    supported_mono _ _ (Set.singleton_subset_iff.2 hv₀)

/-- **Strong approximation omitting finite places, for matrices.** For a nonempty set `S` of finite
places of a number field `K` and `x ∈ GL_ι(𝔸)`, the matrices `x⁻¹ξ + u`, with `ξ` an `ι × κ` matrix
over `K` and `u` an `ι × κ` matrix with entries in `𝔸_S`, are dense in the `ι × κ` matrices over
the adeles. -/
theorem dense_range_inv_mul_map_algebraMap_add_supported {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Nonempty) (x : GL ι (AdeleRing (𝓞 K) K)) :
    Dense (Set.range (fun ξ : Matrix ι κ K ↦
        (↑x⁻¹ : Matrix ι ι (AdeleRing (𝓞 K) K)) * ξ.map (algebraMap K (AdeleRing (𝓞 K) K))) +
      {u : Matrix ι κ (AdeleRing (𝓞 K) K) | ∀ i j, u i j ∈ supported (𝓞 K) K S}) := by
  -- Entrywise, `K + 𝔸_S` is dense, so the matrices `ξ + u` are dense; left multiplication by
  -- `x⁻¹` is a continuous surjection that keeps `u` with entries in the ideal `𝔸_S`.
  set D : Set (Matrix ι κ (AdeleRing (𝓞 K) K)) :=
    Set.univ.pi fun _ ↦ Set.univ.pi fun _ ↦
      Set.range (algebraMap K (AdeleRing (𝓞 K) K)) +
        (supported (𝓞 K) K S : Set (AdeleRing (𝓞 K) K))
  have hD : Dense D :=
    dense_pi _ fun _ _ ↦ dense_pi _ fun _ _ ↦ dense_range_algebraMap_add_supported hS
  have hsurj : Function.Surjective
      fun M : Matrix ι κ (AdeleRing (𝓞 K) K) ↦ (↑x⁻¹ : Matrix ι ι (AdeleRing (𝓞 K) K)) * M :=
    fun M ↦ ⟨(↑x : Matrix ι ι _) * M, by simp [← Matrix.mul_assoc]⟩
  refine (hsurj.denseRange.dense_image (continuous_const.matrix_mul continuous_id) hD).mono ?_
  rintro _ ⟨M, hM, rfl⟩
  choose y hy u hu huM using fun i j ↦ Set.mem_add.1 (hM i (Set.mem_univ i) j (Set.mem_univ j))
  choose ξ hξ using hy
  refine ⟨_, ⟨Matrix.of fun i j ↦ ξ i j, rfl⟩, (↑x⁻¹ : Matrix ι ι _) * Matrix.of fun i j ↦ u i j,
    fun i j ↦ ?_, ?_⟩
  · rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ ↦ Ideal.mul_mem_left _ _ (hu k j)
  · dsimp only
    rw [← Matrix.mul_add]
    congr 1
    ext i j
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, hξ, huM]

end NumberField.AdeleRing
