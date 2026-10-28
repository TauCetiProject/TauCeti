/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Flag
public import TauCeti.Analysis.Convex.Body
public import TauCeti.Algebra.Module.ZLattice.GaugeBasis
public import TauCeti.MeasureTheory.Group.GeometryOfNumbers.SuccessiveMinima
import TauCeti.Algebra.Module.ZLattice.AdaptedBasis
import TauCeti.Algebra.Order.BigOperators.Factorial
import TauCeti.Analysis.Convex.Gauge
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.MetricSpace.DiscreteAddSubgroup

/-!
# Successive minima of a lattice with respect to a convex body, and a basis from the minima

Let `L` be a discrete `ℤ`-submodule spanning a finite-dimensional real normed space `E` of
dimension `n`, and let `K` be a convex body in `E` with `0` in its interior. For `i < n`, the
`i`-th successive minimum `λ i = ZLattice.successiveMin L K i` (indexed from zero) is the least
`t ≥ 0` for which the dilate `t • K` contains `i + 1` vectors of `L` that are linearly independent
over `ℝ`. Measured by the gauge of `K`, `λ i` is the least `t` such that `i + 1` independent lattice
vectors have gauge at most `t`.

The minima are attained simultaneously: there are independent lattice vectors `a 0, …, a (n - 1)`
with `gauge K (a i) = λ i` for every `i`. They are chosen greedily, each of least gauge among the
lattice vectors outside the span of the previous ones; a dimension count shows that this least
gauge is the next minimum. This greedy construction adapts the proof of
`TauCeti.IntegralLattice.IsPosSemidef.exists_linearIndependent_integralNorm_eq_successiveMinimum`
with the gauge of `K` in place of the integral norm. The `a i` need not form a `ℤ`-basis of `L`.
Combined with `ZLattice.exists_basis_gauge_le_max_one_mul`, they give a `ℤ`-basis `b` of `L` with
`b i ∈ (max 1 ((i + 1) / 2) * λ i) • K` for symmetric `K`. Against Minkowski's second theorem the
loss is the factor `∏ i < n, max 1 ((i + 1) / 2) = n! / 2 ^ (n - 1)`
(`TauCeti.prod_max_one_add_one_div_two`).

## Main definitions

* `ZLattice.successiveMin L K i`: the `i`-th successive minimum of `L` with respect to `K`.
* `ZLattice.successiveMinNat L K i`: the extension of the minima by `0` to all natural indices.

## Main results

* `MeasureTheory.coe_successiveMin`: the minima are the foundational successive minima
  `MeasureTheory.successiveMin` of the set `K`, defined through the rank of `r • K ∩ L`;
  `ZLattice.successiveMinNat_eq` is the same comparison at all natural indices.
* `ZLattice.exists_mem_notMem_forall_gauge_le`: outside a proper subspace, a discrete spanning
  lattice has a vector of least gauge.
* `ZLattice.exists_linearIndependent_gauge_eq_successiveMin`: independent lattice vectors attain
  all the successive minima simultaneously.
* `ZLattice.successiveMin_le_iff`: `λ i ≤ t` exactly when `t • K` contains `i + 1` independent
  lattice vectors; in particular the infimum defining `λ i` is attained
  (`ZLattice.successiveMin_isLeast`).
* `ZLattice.monotone_successiveMin` and `ZLattice.successiveMin_pos`: the minima are positive and
  nondecreasing.
* `ZLattice.successiveMin_le_iff_finrank` and `ZLattice.successiveMin_isLeast_gauge`: the
  thresholds of `ZLattice.successiveMin_le_iff` as the dimension of the span of the lattice vectors
  in `t • K`, or of gauge at most `t`; `ZLattice.successiveMin_zero_le_iff` is the first minimum
  as the least dilate containing a nonzero lattice vector.
* `ZLattice.successiveMin_antitone_body`, `ZLattice.successiveMin_antitone_lattice` and
  `ZLattice.successiveMin_smul`: enlarging the body or the lattice decreases the minima, and
  dilating the body by `c > 0` divides them by `c`.
* `ZLattice.finite_setOf_gauge_le`: a discrete lattice has finitely many vectors of bounded gauge.
* `ZLattice.mem_span_image_Iio_of_gauge_lt_successiveMin`: lattice vectors of gauge below the
  `j`-th minimum lie in the span of the first `j` vectors attaining the minima; this is the
  hypothesis of Minkowski's second theorem (`ZLattice.prod_mul_measure_le_two_pow_mul_covolume`).
* `ZLattice.exists_basis_gauge_eq_successiveMin`: the vectors attaining the minima, as a basis
  of `E` over `ℝ` whose flags `Basis.flag` contain the lattice vectors below each minimum.
* `ZLattice.exists_basis_mem_flag_of_gauge_lt_successiveMin`: a `ℤ`-basis of `L` whose real flags
  contain the lattice vectors below each minimum.
* `ZLattice.successiveMin_map` and `ZLattice.successiveMin_comap`: the minima are invariant under
  an injective continuous linear map, or a linear equivalence, applied to both the lattice and the
  body.
* `ZLattice.exists_basis_mem_smul_successiveMin`: a `ℤ`-basis of `L` whose `i`-th member lies in
  `(max 1 ((i + 1) / 2) * λ i) • K`.
* `ZLattice.exists_basis_prod_gauge_le_prod_successiveMin`: a `ℤ`-basis of `L` the product of
  whose gauges is at most `n! / 2 ^ (n - 1)` times the product of the minima.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer, 1959: Chapter VIII,
  §1 (successive minima and their attainment) and Lemma 2 (a lattice basis adapted to the minima),
  and Chapter V, Lemma 8 (the basis from the minima).
* J.-H. Evertse, *Diophantine approximation, Chapter 2: Geometry of numbers*, lecture notes,
  Leiden University, 2023, §2.3, Lemma 2.8: <https://pub.math.leidenuniv.nl/~evertsejh/dio19-2.pdf>.
  This is the source of `ZLattice.successiveMin_isLeast_gauge`,
  `ZLattice.successiveMin_le_iff_finrank` and `ZLattice.successiveMin_smul`.
-/

public section

open Module Submodule
open scoped Pointwise Topology

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The successive minima of a `ℤ`-submodule `L` of `E` with respect to a convex body `K`, indexed
from zero: `successiveMin L K i` is the infimum of the dilation factors `t ≥ 0` for which `t • K`
contains `i + 1` vectors of `L` that are linearly independent over `ℝ`. -/
noncomputable def successiveMin (L : Submodule ℤ E) (K : ConvexBody E) (i : Fin (finrank ℝ E)) :
    ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∃ v : Fin (i + 1) → E,
    LinearIndependent ℝ v ∧ ∀ j, v j ∈ L ∧ v j ∈ t • (K : Set E)}

theorem successiveMin_def (L : Submodule ℤ E) (K : ConvexBody E) (i : Fin (finrank ℝ E)) :
    successiveMin L K i = sInf {t : ℝ | 0 ≤ t ∧ ∃ v : Fin (i + 1) → E,
      LinearIndependent ℝ v ∧ ∀ j, v j ∈ L ∧ v j ∈ t • (K : Set E)} := (rfl)

variable {L : Submodule ℤ E} {K : ConvexBody E}

theorem successiveMin_nonneg (L : Submodule ℤ E) (K : ConvexBody E) (i : Fin (finrank ℝ E)) :
    0 ≤ successiveMin L K i :=
  Real.sInf_nonneg fun _ ht ↦ ht.1

/-- A dilate `t • K` containing `i + 1` independent lattice vectors bounds the `i`-th successive
minimum by `t`. -/
theorem successiveMin_le {i : Fin (finrank ℝ E)} {t : ℝ} (ht : 0 ≤ t) {v : Fin (i + 1) → E}
    (hv : LinearIndependent ℝ v) (hvL : ∀ j, v j ∈ L) (hvK : ∀ j, v j ∈ t • (K : Set E)) :
    successiveMin L K i ≤ t :=
  csInf_le ⟨0, fun _ hs ↦ hs.1⟩ ⟨ht, v, hv, fun j ↦ ⟨hvL j, hvK j⟩⟩

/-- **Scaling the body.** Dilating the body by `c > 0` divides every successive minimum by `c`.
No hypothesis on the lattice or the body is needed. -/
theorem successiveMin_smul (L : Submodule ℤ E) (K : ConvexBody E) {c : ℝ} (hc : 0 < c)
    (i : Fin (finrank ℝ E)) : successiveMin L (c • K) i = successiveMin L K i / c := by
  -- The dilation factors admissible for `c • K` are those for `K` divided by `c`.
  rw [successiveMin_def, successiveMin_def, div_eq_inv_mul, ← smul_eq_mul,
    ← Real.sInf_smul_of_nonneg (inv_nonneg.2 hc.le)]
  congr 1
  ext t
  simp only [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hc.ne'), inv_inv, smul_eq_mul,
    Set.mem_ofPred_eq, ConvexBody.coe_smul, smul_smul, mul_comm t c,
    mul_nonneg_iff_of_pos_left hc]

/-- **Lattice vectors below a minimum.** Let `a` be independent lattice vectors with
`gauge K (a i) ≤ successiveMin L K i` for every `i`, such as the vectors attaining the minima
(`ZLattice.exists_linearIndependent_gauge_eq_successiveMin`). Every lattice vector of gauge less
than the `j`-th minimum lies in the span of `a 0, …, a (j - 1)`. -/
theorem mem_span_image_Iio_of_gauge_lt_successiveMin (hK : 0 ∈ interior (K : Set E))
    {a : Fin (finrank ℝ E) → E} (ha : LinearIndependent ℝ a) (haL : ∀ i, a i ∈ L)
    (hag : ∀ i, gauge (K : Set E) (a i) ≤ successiveMin L K i) {j : Fin (finrank ℝ E)} {v : E}
    (hvL : v ∈ L) (hv : gauge (K : Set E) v < successiveMin L K j) :
    v ∈ span ℝ (a '' Set.Iio j) := by
  classical
  by_contra hvS
  set t := gauge (K : Set E) v
  have ht : 0 < t := (ConvexBody.gauge_pos_iff hK).2 fun h ↦ hvS (h ▸ zero_mem _)
  -- Let `m = Nat.find hex ≤ j` be the least index whose minimum exceeds `t`.
  have hex : ∃ k, ∃ hk : k < finrank ℝ E, t < successiveMin L K ⟨k, hk⟩ := ⟨j, j.isLt, hv⟩
  obtain ⟨hm, htm⟩ := Nat.find_spec hex
  have hmj : Nat.find hex ≤ j := Nat.find_min' hex ⟨j.isLt, hv⟩
  have hle (i : Fin (Nat.find hex)) : gauge (K : Set E) (a (Fin.castLE hm.le i)) ≤ t := by
    have := Nat.find_min hex i.isLt
    push Not at this
    exact (hag _).trans (this _)
  -- Then `a 0, …, a (m - 1)` and `v` are `m + 1` independent lattice vectors in `t • K`.
  let w : Fin (Nat.find hex + 1) → E := Fin.snoc (fun i ↦ a (Fin.castLE hm.le i)) v
  have hw : LinearIndependent ℝ w := by
    refine (ha.comp _ (Fin.castLE_injective _)).finSnoc fun h ↦ hvS (span_mono ?_ h)
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castLE hm.le i, Fin.lt_def.2 (lt_of_lt_of_le i.isLt hmj), rfl⟩
  have hwL (k : Fin (Nat.find hex + 1)) : w k ∈ L :=
    Fin.lastCases (by simpa [w] using hvL) (fun i ↦ by simpa [w] using haL _) k
  have hwK (k : Fin (Nat.find hex + 1)) : w k ∈ t • (K : Set E) := by
    rw [← ConvexBody.gauge_le_iff_mem_smul hK ht]
    induction k using Fin.lastCases with
    | last => simp [w, t]
    | cast i => simpa [w] using hle i
  exact (successiveMin_le (i := ⟨_, hm⟩) ht.le hw hwL hwK).not_gt htm

section map

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Transport of the successive minima along a linear map.** An injective continuous linear map
`f : E →L[ℝ] F` carries the successive minima of `L` with respect to `K` to those of the image
lattice `f(L)` with respect to the image body `f(K)`: at indices `i` of `E` and `j` of `F` with the
same value, `λ_j(f(L), f(K)) = λ_i(L, K)`. In particular the minima are invariant under any linear
equivalence applied to both the lattice and the body; it need be neither orthogonal nor unimodular.
-/
theorem successiveMin_map (L : Submodule ℤ E) (K : ConvexBody E) {f : E →L[ℝ] F}
    (hf : Function.Injective f) {i : Fin (finrank ℝ E)} {j : Fin (finrank ℝ F)}
    (hij : (i : ℕ) = j) :
    successiveMin (L.map ((f : E →ₗ[ℝ] F).restrictScalars ℤ)) (K.map f) j =
      successiveMin L K i := by
  obtain ⟨n, hn⟩ := i
  obtain ⟨m, hm⟩ := j
  obtain rfl : n = m := hij
  -- Each condition defining the minima holds for `f ∘ v` exactly when it holds for `v`.
  have hL (x : E) : f x ∈ L.map ((f : E →ₗ[ℝ] F).restrictScalars ℤ) ↔ x ∈ L := by
    rw [← SetLike.mem_coe, Submodule.map_coe, LinearMap.coe_restrictScalars,
      ContinuousLinearMap.coe_coe, hf.mem_set_image, SetLike.mem_coe]
  have hK (t : ℝ) (x : E) : f x ∈ t • (K.map f : Set F) ↔ x ∈ t • (K : Set E) := by
    rw [ConvexBody.coe_map, ← image_smul_set, hf.mem_set_image]
  have hlin (v : Fin (n + 1) → E) : LinearIndependent ℝ (f ∘ v) ↔ LinearIndependent ℝ v :=
    (f : E →ₗ[ℝ] F).linearIndependent_iff (LinearMap.ker_eq_bot.2 hf)
  simp only [successiveMin_def]
  congr 1
  ext t
  refine and_congr_right fun _ ↦ ⟨fun ⟨w, hw, hwLK⟩ ↦ ?_, fun ⟨v, hv, hvLK⟩ ↦
    ⟨f ∘ v, (hlin v).2 hv, fun k ↦ ⟨(hL _).2 (hvLK k).1, (hK t _).2 (hvLK k).2⟩⟩⟩
  -- The vectors of `f(L)` are images of vectors of `L`.
  choose v hvL hvw using fun k ↦ Submodule.mem_map.1 (hwLK k).1
  obtain rfl : f ∘ v = w := funext fun k ↦ by simpa using hvw k
  exact ⟨v, (hlin v).1 hw, fun k ↦ ⟨hvL k, (hK t _).1 (hwLK k).2⟩⟩

/-- **Transport of the successive minima along a linear equivalence**, with the lattice pulled
back as in `ZLattice.comap` and `ZLattice.covolume_comap`: for `e : F ≃L[ℝ] E`, the minima of the
pullback `e⁻¹(L)` with respect to the body `e⁻¹(K)` are those of `L` with respect to `K`. -/
theorem successiveMin_comap (L : Submodule ℤ E) (K : ConvexBody E) (e : F ≃L[ℝ] E)
    {i : Fin (finrank ℝ E)} {j : Fin (finrank ℝ F)} (hij : (i : ℕ) = j) :
    successiveMin (ZLattice.comap ℝ L e.toLinearMap) (K.map (e.symm : E →L[ℝ] F)) j =
      successiveMin L K i := by
  have hL : ZLattice.comap ℝ L e.toLinearMap =
      L.map (((e.symm : E →L[ℝ] F) : E →ₗ[ℝ] F).restrictScalars ℤ) :=
    SetLike.coe_injective <| by simp [e.image_symm_eq_preimage]
  rw [hL]
  exact successiveMin_map L K e.symm.injective hij

end map

section successiveMinNat

/-- The successive minima of `L` with respect to `K` extended to all natural indices: below the
dimension `n` of `E` this is `successiveMin L K i`, still indexed from zero, and from `n` on it
is `0`. It is used where an index bound is a proved equality rather than a definitional one.
Unlike the minima themselves, the extension need not be monotone. -/
noncomputable def successiveMinNat (L : Submodule ℤ E) (K : ConvexBody E) (i : ℕ) : ℝ :=
  if hi : i < finrank ℝ E then successiveMin L K ⟨i, hi⟩ else 0

/-- Below the dimension of `E`, the natural-index extension is the successive minimum. -/
theorem successiveMinNat_of_lt (L : Submodule ℤ E) (K : ConvexBody E) {i : ℕ}
    (hi : i < finrank ℝ E) : successiveMinNat L K i = successiveMin L K ⟨i, hi⟩ :=
  dite_eq_left hi

/-- At a `Fin` index, the natural-index extension is the successive minimum. -/
@[simp]
theorem successiveMinNat_val (L : Submodule ℤ E) (K : ConvexBody E) (i : Fin (finrank ℝ E)) :
    successiveMinNat L K i = successiveMin L K i :=
  successiveMinNat_of_lt L K i.isLt

/-- From the dimension of `E` on, the natural-index extension vanishes. -/
@[simp]
theorem successiveMinNat_of_le (L : Submodule ℤ E) (K : ConvexBody E) {i : ℕ}
    (hi : finrank ℝ E ≤ i) : successiveMinNat L K i = 0 :=
  dite_eq_right hi.not_gt

end successiveMinNat

/-- **The foundational successive minima of a convex body.** On a convex body `K`, the successive
minimum `MeasureTheory.successiveMin L K i` of an arbitrary set, defined through the rank of
`r • K ∩ L`, is the successive minimum `successiveMin L K i`, defined through independent families.
No hypothesis on `L`, `K` or `E` is needed: an index `i` forces `E` to be finite-dimensional. -/
theorem _root_.MeasureTheory.coe_successiveMin (L : Submodule ℤ E) (K : ConvexBody E)
    (i : Fin (finrank ℝ E)) :
    (MeasureTheory.successiveMin L (K : Set E) i : ℝ) = successiveMin L K i := by
  -- The threshold sets correspond under `ℝ≥0 → ℝ`: the rank of `r • K ∩ L` exceeds `i` exactly
  -- when `r • K ∩ L` contains `i + 1` real-linearly independent vectors.
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos i.pos
  rw [MeasureTheory.successiveMin_def, NNReal.coe_sInf, successiveMin_def]
  congr 1
  ext t
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.finrank, Nat.lt_iff_add_one_le,
    le_finrank_span_iff_exists_linearIndependent, Set.mem_inter_iff, SetLike.mem_coe,
    NNReal.smul_def]
  constructor
  · rintro ⟨r, ⟨v, hv, hvs⟩, rfl⟩
    exact ⟨r.2, v, hv, fun j ↦ (hvs j).symm⟩
  · rintro ⟨ht, v, hv, hvs⟩
    exact ⟨⟨t, ht⟩, ⟨v, hv, fun j ↦ (hvs j).symm⟩, rfl⟩

variable [FiniteDimensional ℝ E]

/-- The natural-index extension of the successive minima is the foundational successive minimum
`MeasureTheory.successiveMin` at every index: below the dimension by
`MeasureTheory.coe_successiveMin`, and beyond it both sides vanish. -/
theorem successiveMinNat_eq (L : Submodule ℤ E) (K : ConvexBody E) (i : ℕ) :
    successiveMinNat L K i = MeasureTheory.successiveMin L (K : Set E) i := by
  rcases lt_or_ge i (finrank ℝ E) with hi | hi
  · rw [successiveMinNat_of_lt L K hi, ← MeasureTheory.coe_successiveMin]
  · simp [hi]

/-- **Gauge sublevels of a lattice are finite.** For a discrete `ℤ`-submodule `L` of the
finite-dimensional real normed space `E` and a convex body `K` with `0` in its interior, only
finitely many vectors of `L` have gauge at most `r`. The body need not be symmetric. -/
theorem finite_setOf_gauge_le (L : Submodule ℤ E) [DiscreteTopology L]
    (hK : 0 ∈ interior (K : Set E)) (r : ℝ) :
    {x : E | x ∈ L ∧ gauge (K : Set E) x ≤ r}.Finite := by
  -- The sublevel lies in the bounded dilate `c • K` with `c = max r 0 + 1`.
  have hc : 0 < max r 0 + 1 := by positivity
  refine (AddSubgroup.finite_inter L.toAddSubgroup (K.isBounded.smul₀ (max r 0 + 1))).subset ?_
  rintro x ⟨hxL, hx⟩
  refine ⟨?_, hxL⟩
  rw [← ConvexBody.gauge_le_iff_mem_smul hK hc]
  linarith [le_max_left r 0]

/-- Let `L` be a discrete `ℤ`-submodule spanning the finite-dimensional real normed space `E`, and
let `K` be a convex body with `0` in its interior. Outside any proper subspace `V`, `L` has a vector
of least gauge with respect to `K` among the vectors of `L` outside `V`. -/
theorem exists_mem_notMem_forall_gauge_le (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hK : 0 ∈ interior (K : Set E)) {V : Submodule ℝ E} (hV : V ≠ ⊤) :
    ∃ w ∈ L, w ∉ V ∧ ∀ y ∈ L, y ∉ V → gauge (K : Set E) w ≤ gauge (K : Set E) y := by
  obtain ⟨y₀, hy₀L, hy₀V⟩ : ∃ y ∈ L, y ∉ V := by
    by_contra! h
    exact hV (eq_top_iff.2 ((IsZLattice.span_top (K := ℝ) (L := L)).symm.le.trans (span_le.2 h)))
  set c := gauge (K : Set E) y₀
  -- The candidates of gauge at most `c` are finitely many.
  set S := {y : E | y ∈ L ∧ y ∉ V ∧ gauge (K : Set E) y ≤ c}
  have hS : S.Finite := (finite_setOf_gauge_le L hK c).subset fun y hy ↦ ⟨hy.1, hy.2.2⟩
  obtain ⟨w, ⟨hwL, hwV, hwc⟩, hmin⟩ :=
    S.exists_min_image (gauge (K : Set E)) hS ⟨y₀, hy₀L, hy₀V, le_rfl⟩
  refine ⟨w, hwL, hwV, fun y hyL hyV ↦ ?_⟩
  by_cases hy : gauge (K : Set E) y ≤ c
  · exact hmin y ⟨hyL, hyV, hy⟩
  · exact hwc.trans (not_le.1 hy).le

/-- If a lattice vector `w` has least gauge among the lattice vectors outside the span of `m`
vectors `a`, and `m + 1` independent lattice vectors have gauge at most that of `w`, then the gauge
of `w` is the `m`-th successive minimum. -/
private theorem gauge_eq_successiveMin_of_forall_gauge_le (hK : 0 ∈ interior (K : Set E)) {m : ℕ}
    (hm : m < finrank ℝ E) (a : Fin m → E) {w : E} (hw₀ : 0 < gauge (K : Set E) w)
    (hwmin : ∀ y ∈ L, y ∉ span ℝ (Set.range a) → gauge (K : Set E) w ≤ gauge (K : Set E) y)
    {v : Fin (m + 1) → E} (hv : LinearIndependent ℝ v) (hvL : ∀ j, v j ∈ L)
    (hvw : ∀ j, gauge (K : Set E) (v j) ≤ gauge (K : Set E) w) :
    gauge (K : Set E) w = successiveMin L K ⟨m, hm⟩ := by
  have hvK (j : Fin (m + 1)) : v j ∈ gauge (K : Set E) w • (K : Set E) :=
    (ConvexBody.gauge_le_iff_mem_smul hK hw₀).1 (hvw j)
  refine le_antisymm (le_csInf ⟨_, hw₀.le, v, hv, fun j ↦ ⟨hvL j, hvK j⟩⟩ ?_)
    (successiveMin_le hw₀.le hv hvL hvK)
  -- Of `m + 1` independent vectors, one lies outside the `m`-dimensional span of `a`.
  rintro t ⟨ht, u, hu, huLK⟩
  obtain ⟨j, hj⟩ : ∃ j, u j ∉ span ℝ (Set.range a) := by
    by_contra! h
    have hle := Submodule.finrank_mono (span_le.2 (Set.range_subset_iff.2 h))
    have := finrank_range_le_card (R := ℝ) a
    rw [finrank_span_eq_card hu, Fintype.card_fin, Fin.val_mk] at hle
    rw [Set.finrank, Fintype.card_fin] at this
    omega
  exact (hwmin _ (huLK j).1 hj).trans (gauge_le_of_mem ht (huLK j).2)

/-- The greedy construction of vectors attaining the first `m` successive minima. Each new vector
has least gauge outside the span of the previous ones; the last invariant records this. -/
private theorem exists_linearIndependent_gauge_eq_successiveMin_aux (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (hK : 0 ∈ interior (K : Set E)) (m : ℕ)
    (hm : m ≤ finrank ℝ E) :
    ∃ a : Fin m → E, LinearIndependent ℝ a ∧
      (∀ j, a j ∈ L ∧ gauge (K : Set E) (a j) = successiveMin L K ⟨j, j.isLt.trans_le hm⟩) ∧
      (∀ j k, j ≤ k → gauge (K : Set E) (a j) ≤ gauge (K : Set E) (a k)) ∧
      ∀ y ∈ L, y ∉ span ℝ (Set.range a) → ∀ j, gauge (K : Set E) (a j) ≤ gauge (K : Set E) y := by
  induction m with
  | zero =>
    exact ⟨Fin.elim0, linearIndependent_empty_type, fun j ↦ j.elim0, fun j ↦ j.elim0, by simp⟩
  | succ m ih =>
    -- Append a lattice vector `w` of least gauge outside the span of `a`, show that its gauge is
    -- the next minimum, and check that the invariants persist.
    obtain ⟨a, ha, haL, hmono, hamin⟩ := ih (by omega)
    have hspan : span ℝ (Set.range a) ≠ ⊤ := by
      intro h
      have := finrank_range_le_card (R := ℝ) a
      rw [Set.finrank, h, finrank_top, Fintype.card_fin] at this
      omega
    obtain ⟨w, hwL, hwV, hwmin⟩ := exists_mem_notMem_forall_gauge_le L hK hspan
    have hw₀ : 0 < gauge (K : Set E) w :=
      (ConvexBody.gauge_pos_iff hK).2 fun h ↦ hwV (h ▸ zero_mem _)
    have hsnoc : LinearIndependent ℝ (Fin.snoc a w : Fin (m + 1) → E) := ha.finSnoc hwV
    have hsnocL (j : Fin (m + 1)) : (Fin.snoc a w : Fin (m + 1) → E) j ∈ L :=
      Fin.lastCases (by simpa using hwL) (fun k ↦ by simpa using (haL k).1) j
    have hsnocK (j : Fin (m + 1)) : gauge (K : Set E) ((Fin.snoc a w : Fin (m + 1) → E) j) ≤
        gauge (K : Set E) w :=
      Fin.lastCases (by simp) (fun k ↦ by simpa using hamin w hwL hwV k) j
    have hweq : gauge (K : Set E) w = successiveMin L K ⟨m, by omega⟩ :=
      gauge_eq_successiveMin_of_forall_gauge_le hK _ a hw₀ hwmin hsnoc hsnocL hsnocK
    refine ⟨Fin.snoc a w, hsnoc, fun j ↦ ⟨hsnocL j, ?_⟩, fun j k hjk ↦ ?_, fun y hyL hy ↦ ?_⟩
    · induction j using Fin.lastCases with
      | last => simpa using hweq
      | cast k => simpa using (haL k).2
    · induction k using Fin.lastCases with
      | last => simpa using hsnocK j
      | cast k =>
        induction j using Fin.lastCases with
        | last => exact absurd hjk (Fin.castSucc_lt_last k).not_ge
        | cast j => simpa using hmono j k (by simpa using hjk)
    · have hyS : y ∉ span ℝ (Set.range a) := fun h ↦ hy <| span_mono
        (by rintro _ ⟨k, rfl⟩; exact ⟨k.castSucc, by simp⟩) h
      intro j
      induction j using Fin.lastCases with
      | last => simpa using hwmin y hyL hyS
      | cast k => simpa using hamin y hyL hyS k

/-- **The successive minima are attained simultaneously.** For a discrete spanning lattice `L` and
a convex body `K` with `0` in its interior, there are `ℝ`-linearly independent vectors `a i` of `L`
with `gauge K (a i) = successiveMin L K i` for every `i`. They need not form a `ℤ`-basis of `L`. -/
theorem exists_linearIndependent_gauge_eq_successiveMin (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hK : 0 ∈ interior (K : Set E)) :
    ∃ a : Fin (finrank ℝ E) → E, LinearIndependent ℝ a ∧
      ∀ i, a i ∈ L ∧ gauge (K : Set E) (a i) = successiveMin L K i := by
  obtain ⟨a, ha, haL, -, -⟩ :=
    exists_linearIndependent_gauge_eq_successiveMin_aux L hK (finrank ℝ E) le_rfl
  exact ⟨a, ha, haL⟩

/-- The successive minima are nondecreasing. -/
theorem monotone_successiveMin (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hK : 0 ∈ interior (K : Set E)) : Monotone (successiveMin L K) := by
  obtain ⟨a, -, haL, hmono, -⟩ :=
    exists_linearIndependent_gauge_eq_successiveMin_aux L hK (finrank ℝ E) le_rfl
  intro i j hij
  simpa [(haL i).2, (haL j).2] using hmono i j hij

/-- The successive minima of a discrete lattice with respect to a bounded body are positive. -/
theorem successiveMin_pos (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hK : 0 ∈ interior (K : Set E)) (i : Fin (finrank ℝ E)) : 0 < successiveMin L K i := by
  obtain ⟨a, ha, haL⟩ := exists_linearIndependent_gauge_eq_successiveMin L hK
  rw [← (haL i).2]
  exact (ConvexBody.gauge_pos_iff hK).2 (ha.ne_zero i)

/-- **The successive minima as thresholds.** For `t ≥ 0`, the `i`-th successive minimum is at most
`t` exactly when the dilate `t • K` contains `i + 1` independent vectors of `L`. In particular the
infimum defining `successiveMin L K i` is attained. -/
theorem successiveMin_le_iff (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hK : 0 ∈ interior (K : Set E)) {i : Fin (finrank ℝ E)} {t : ℝ} (ht : 0 ≤ t) :
    successiveMin L K i ≤ t ↔ ∃ v : Fin (i + 1) → E,
      LinearIndependent ℝ v ∧ ∀ j, v j ∈ L ∧ v j ∈ t • (K : Set E) := by
  refine ⟨fun hle ↦ ?_, fun ⟨v, hv, hvLK⟩ ↦
    successiveMin_le ht hv (fun j ↦ (hvLK j).1) fun j ↦ (hvLK j).2⟩
  obtain ⟨a, ha, haL⟩ := exists_linearIndependent_gauge_eq_successiveMin L hK
  have htpos : 0 < t := (successiveMin_pos L hK i).trans_le hle
  refine ⟨a ∘ Fin.castLE i.isLt, ha.comp _ (Fin.castLE_injective _), fun j ↦ ⟨(haL _).1, ?_⟩⟩
  rw [← ConvexBody.gauge_le_iff_mem_smul hK htpos, Function.comp_apply, (haL _).2]
  exact (monotone_successiveMin L hK (Fin.le_def.2 (Nat.lt_succ_iff.1 j.isLt))).trans hle

/-- **The successive minima are attained.** The `i`-th successive minimum is the least `t ≥ 0` for
which the dilate `t • K` contains `i + 1` independent vectors of `L`. -/
theorem successiveMin_isLeast (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hK : 0 ∈ interior (K : Set E)) (i : Fin (finrank ℝ E)) :
    IsLeast {t : ℝ | 0 ≤ t ∧ ∃ v : Fin (i + 1) → E,
      LinearIndependent ℝ v ∧ ∀ j, v j ∈ L ∧ v j ∈ t • (K : Set E)} (successiveMin L K i) :=
  ⟨⟨successiveMin_nonneg L K i, (successiveMin_le_iff L hK (successiveMin_nonneg L K i)).1 le_rfl⟩,
    fun _ ⟨ht, _, hv, hvLK⟩ ↦ successiveMin_le ht hv (fun j ↦ (hvLK j).1) fun j ↦ (hvLK j).2⟩

/-- **The successive minima as rank thresholds.** For `t ≥ 0`, the `i`-th successive minimum is
at most `t` exactly when the vectors of `L` in the dilate `t • K` span a subspace of dimension at
least `i + 1`. -/
theorem successiveMin_le_iff_finrank (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hK : 0 ∈ interior (K : Set E)) {i : Fin (finrank ℝ E)} {t : ℝ} (ht : 0 ≤ t) :
    successiveMin L K i ≤ t ↔ i + 1 ≤ finrank ℝ (span ℝ ((L : Set E) ∩ t • (K : Set E))) := by
  rw [successiveMin_le_iff L hK ht, Submodule.le_finrank_span_iff_exists_linearIndependent]
  simp only [Set.mem_inter_iff, SetLike.mem_coe]

/-- **The successive minima as gauge thresholds.** The `i`-th successive minimum is the least
`t ≥ 0` such that the vectors of `L` of gauge at most `t` span a subspace of dimension at least
`i + 1`. The body need not be symmetric. -/
theorem successiveMin_isLeast_gauge (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hK : 0 ∈ interior (K : Set E)) (i : Fin (finrank ℝ E)) :
    IsLeast {t : ℝ | 0 ≤ t ∧
      i + 1 ≤ finrank ℝ (span ℝ {x : E | x ∈ L ∧ gauge (K : Set E) x ≤ t})}
      (successiveMin L K i) := by
  -- For `t > 0` the gauge sublevel is the set of lattice vectors in `t • K`.
  have hset {t : ℝ} (ht : 0 < t) :
      {x : E | x ∈ L ∧ gauge (K : Set E) x ≤ t} = (L : Set E) ∩ t • (K : Set E) := by
    ext x
    simp [ConvexBody.gauge_le_iff_mem_smul hK ht]
  refine ⟨⟨successiveMin_nonneg L K i, ?_⟩, fun t ⟨ht, hrank⟩ ↦ ?_⟩
  · rw [hset (successiveMin_pos L hK i),
      ← successiveMin_le_iff_finrank L hK (successiveMin_nonneg L K i)]
  rcases ht.eq_or_lt with rfl | ht
  · -- Only the zero vector has gauge at most zero, so the sublevel spans the zero subspace.
    have hbot : span ℝ {x : E | x ∈ L ∧ gauge (K : Set E) x ≤ 0} = ⊥ :=
      span_eq_bot.2 fun x ⟨_, hx⟩ ↦ by
        by_contra hx0
        exact ((ConvexBody.gauge_pos_iff hK).2 hx0).not_ge hx
    rw [hbot, finrank_bot] at hrank
    omega
  · rw [hset ht] at hrank
    exact (successiveMin_le_iff_finrank L hK ht.le).2 hrank

/-- **The first successive minimum.** For `t ≥ 0`, the first successive minimum is at most `t`
exactly when the dilate `t • K` contains a nonzero vector of `L`. -/
theorem successiveMin_zero_le_iff (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hK : 0 ∈ interior (K : Set E)) (hE : 0 < finrank ℝ E) {t : ℝ} (ht : 0 ≤ t) :
    successiveMin L K ⟨0, hE⟩ ≤ t ↔ ∃ x ∈ L, x ≠ 0 ∧ x ∈ t • (K : Set E) := by
  rw [successiveMin_le_iff L hK ht]
  refine ⟨fun ⟨v, hv, hvLK⟩ ↦ ⟨v 0, (hvLK 0).1, hv.ne_zero 0, (hvLK 0).2⟩,
    fun ⟨x, hxL, hx0, hxK⟩ ↦ ?_⟩
  have hx : LinearIndependent ℝ fun _ : Fin 1 ↦ x := .of_subsingleton 0 hx0
  exact ⟨_, hx, fun _ ↦ ⟨hxL, hxK⟩⟩

/-- **Enlarging the body decreases the successive minima.** If `K ⊆ K'` and `0` is in the
interior of `K`, then every successive minimum of `L` with respect to `K'` is at most the
corresponding minimum with respect to `K`. -/
theorem successiveMin_antitone_body (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hK : 0 ∈ interior (K : Set E)) {K' : ConvexBody E} (hKK' : K ≤ K')
    (i : Fin (finrank ℝ E)) : successiveMin L K' i ≤ successiveMin L K i := by
  obtain ⟨v, hv, hvLK⟩ :=
    (successiveMin_le_iff L hK (successiveMin_nonneg L K i)).1 le_rfl
  exact successiveMin_le (successiveMin_nonneg L K i) hv (fun j ↦ (hvLK j).1)
    fun j ↦ Set.smul_set_mono (SetLike.coe_subset_coe.2 hKK') (hvLK j).2

/-- **Enlarging the lattice decreases the successive minima.** If `L ≤ M` for a discrete
spanning lattice `L`, then every successive minimum of `M` with respect to `K` is at most the
corresponding minimum of `L`. -/
theorem successiveMin_antitone_lattice (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hK : 0 ∈ interior (K : Set E)) {M : Submodule ℤ E} (hLM : L ≤ M)
    (i : Fin (finrank ℝ E)) : successiveMin M K i ≤ successiveMin L K i := by
  obtain ⟨v, hv, hvLK⟩ :=
    (successiveMin_le_iff L hK (successiveMin_nonneg L K i)).1 le_rfl
  exact successiveMin_le (successiveMin_nonneg L K i) hv (fun j ↦ hLM (hvLK j).1)
    fun j ↦ (hvLK j).2

/-- **A real basis attaining the successive minima.** For a discrete spanning lattice `L` and a
convex body `K` with `0` in its interior, some basis `b` of `E` over `ℝ` consists of vectors of `L`
with `gauge K (b i) = successiveMin L K i`, so that `b i ∈ successiveMin L K i • K`, for every `i`.
Moreover every vector of `L` of gauge less than the `i`-th minimum lies in the flag
`b.flag i.castSucc`, the span of `b 0, …, b (i - 1)`. The body need not be symmetric, and `b` need
not be a `ℤ`-basis of `L`. -/
theorem exists_basis_gauge_eq_successiveMin (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hK : 0 ∈ interior (K : Set E)) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, (∀ i, b i ∈ L) ∧
      (∀ i, gauge (K : Set E) (b i) = successiveMin L K i) ∧
      (∀ i, b i ∈ successiveMin L K i • (K : Set E)) ∧
      ∀ i, ∀ x ∈ L, gauge (K : Set E) x < successiveMin L K i → x ∈ b.flag i.castSucc := by
  obtain ⟨a, ha, haL⟩ := exists_linearIndependent_gauge_eq_successiveMin L hK
  set b := basisOfLinearIndependentOfCardEqFinrank' a ha (Fintype.card_fin _)
  have hb : ⇑b = a := coe_basisOfLinearIndependentOfCardEqFinrank' a ha _
  have hflag (i : Fin (finrank ℝ E)) : b.flag i.castSucc = span ℝ (a '' Set.Iio i) := by
    simp only [Basis.flag, hb, Fin.castSucc_lt_castSucc_iff, Set.Iio_def]
  refine ⟨b, fun i ↦ hb ▸ (haL i).1, fun i ↦ hb ▸ (haL i).2, fun i ↦ ?_, fun i x hxL hx ↦ ?_⟩
  · rw [← ConvexBody.gauge_le_iff_mem_smul hK (successiveMin_pos L hK i), hb, (haL i).2]
  · rw [hflag]
    exact mem_span_image_Iio_of_gauge_lt_successiveMin hK ha (fun j ↦ (haL j).1)
      (fun j ↦ (haL j).2.le) hxL hx

/-- **A lattice basis adapted to the successive minima** (Cassels, Chapter VIII, Lemma 2). For a
discrete spanning lattice `L` and a convex body `K` with `0` in its interior, some `ℤ`-basis `b` of
`L` has the following property: every vector of `L` of gauge less than the `i`-th minimum lies in
the span over `ℝ` of `b 0, …, b (i - 1)`, the flag `(b.ofZLatticeBasis ℝ L).flag i.castSucc`. The
body need not be symmetric. No bound on the gauges of the `b i` is claimed; for symmetric `K`,
`ZLattice.exists_basis_mem_smul_successiveMin` gives one. -/
theorem exists_basis_mem_flag_of_gauge_lt_successiveMin (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hK : 0 ∈ interior (K : Set E)) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℤ L, ∀ i, ∀ x ∈ L,
      gauge (K : Set E) x < successiveMin L K i → x ∈ (b.ofZLatticeBasis ℝ L).flag i.castSucc := by
  obtain ⟨w, hwL, -, -, hw⟩ := exists_basis_gauge_eq_successiveMin L hK
  obtain ⟨b, hb⟩ := exists_basis_span_image_eq_flag w hwL
  refine ⟨b, fun i x hxL hx ↦ ?_⟩
  rw [Basis.flag]
  simpa only [Basis.ofZLatticeBasis_apply, hb] using hw i x hxL hx

/-- **A basis from the successive minima** (Cassels, Chapter V, Lemma 8). For a discrete spanning
lattice `L` and a symmetric convex body `K` with `0` in its interior, some `ℤ`-basis `b` of `L` has
`b i ∈ (max 1 ((i + 1) / 2) * successiveMin L K i) • K` for every `i`. The factor is `1` for
`i ≤ 1`, and the product of the factors is `n! / 2 ^ (n - 1)`
(`TauCeti.prod_max_one_add_one_div_two`). -/
theorem exists_basis_mem_smul_successiveMin (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hK : 0 ∈ interior (K : Set E)) (hsymm : ∀ x ∈ K, -x ∈ K) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℤ L, ∀ i : Fin (finrank ℝ E),
      (b i : E) ∈ (max 1 ((((i : ℕ) : ℝ) + 1) / 2) * successiveMin L K i) • (K : Set E) := by
  have hK₀ : (K : Set E) ∈ 𝓝 0 := mem_interior_iff_mem_nhds.1 hK
  obtain ⟨a, ha, haL⟩ := exists_linearIndependent_gauge_eq_successiveMin L hK
  have hmono : Monotone fun i ↦ gauge (K : Set E) (a i) := by
    simpa only [fun i ↦ (haL i).2] using monotone_successiveMin L hK
  obtain ⟨b, hb⟩ := exists_basis_gauge_le_max_one_mul L K.convex hsymm (absorbent_nhds_zero hK₀)
    rfl (fun i ↦ (haL i).1) ha hmono
  refine ⟨b, fun i ↦ ?_⟩
  have hpos : 0 < max 1 ((((i : ℕ) : ℝ) + 1) / 2) * successiveMin L K i :=
    mul_pos (lt_max_of_lt_left one_pos) (successiveMin_pos L hK i)
  rw [← ConvexBody.gauge_le_iff_mem_smul hK hpos, ← (haL i).2]
  exact hb i

/-- **A basis from the successive minima, product form.** For a discrete spanning lattice `L` and
a symmetric convex body `K` with `0` in its interior, some `ℤ`-basis `b` of `L` has
`∏ i, gauge K (b i) ≤ n! / 2 ^ (n - 1) * ∏ i, successiveMin L K i`, where `n = finrank ℝ E`. -/
theorem exists_basis_prod_gauge_le_prod_successiveMin (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hK : 0 ∈ interior (K : Set E)) (hsymm : ∀ x ∈ K, -x ∈ K) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℤ L,
      ∏ i, gauge (K : Set E) (b i) ≤
        (finrank ℝ E).factorial / 2 ^ (finrank ℝ E - 1) * ∏ i, successiveMin L K i := by
  obtain ⟨b, hb⟩ := exists_basis_mem_smul_successiveMin L hK hsymm
  refine ⟨b, ?_⟩
  rw [← TauCeti.prod_max_one_add_one_div_two, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ ↦ gauge_nonneg _) fun i _ ↦ ?_
  exact (ConvexBody.gauge_le_iff_mem_smul hK
    (mul_pos (lt_max_of_lt_left one_pos) (successiveMin_pos L hK i))).2 (hb i)

end ZLattice
