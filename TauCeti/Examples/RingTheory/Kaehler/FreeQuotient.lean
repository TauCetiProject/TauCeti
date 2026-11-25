/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.AlgebraicGeometry.Modules.LocallyFreeQuotientCusp
public import TauCeti.RingTheory.Kaehler.FreeQuotient
public import TauCeti.RingTheory.Kaehler.Localization
public import TauCeti.RingTheory.Node.Branches
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Checks: the local rings of the node and the cusp at the origin

Let `k` be a field and `O` the local ring at the origin of a plane curve over `k`. Then `Ω[O⁄k]`
admits no surjection onto `O ^ d` with `d ≠ 0` when

* the curve is the node `x y = 0`, with coordinate ring `TauCeti.NodeAlgebra k 0`, in every
  characteristic (`node_not_surjective`), and
* the curve is the cusp `y ^ 2 = x ^ 3`, with coordinate ring
  `TauCeti.CuspDifferentialsExample.CuspRing k`, and `2 ≠ 0`, `3 ≠ 0` in `k`, for instance over `ℚ`
  (`cusp_not_surjective`).

By the forward stalk criterion `HasLocallyFreeQuotientOfDifferentials.exists_surjective_stalk`,
applied at the origin, these rule out a locally free quotient of rank one of the differentials of
the node, and of the cusp over `ℚ`, whose stalk at the origin is `O` as a `k`-algebra. Over
`𝔽_2` the cusp has the free quotient `dx ↦ 0`, `dy ↦ 1`, so the characteristic hypothesis on the
cusp cannot be dropped.

The non-divisibility hypotheses of `TauCeti.not_surjective_kaehlerDifferential_of_mul_eq_zero`
and `TauCeti.not_surjective_kaehlerDifferential_of_sq_eq_pow_three` are checked by mapping the
coordinate ring to local rings where the images of `x`, `y` are explicit: `k⟦t⟧` with
`(x, y) ↦ (t, 0)`, `(0, t)` or `(t ^ 2, t ^ 3)`, and `k⟦t⟧ / (t ^ 3)` with `(x, y) ↦ (t, 0)`.
-/

public section

noncomputable section

open KaehlerDifferential TauCeti.CuspDifferentialsExample

namespace TauCeti.NodeCuspDifferentialsExample

universe u

variable {k : Type u} [Field k]

/-- To see that `u ∉ (v)` in the local ring of a `k`-algebra `A` at a `k`-point `ε`, it suffices
to send `A` to a local `k`-algebra `B` by `ψ`, with generators of `A` that vanish at `ε` going to
the maximal ideal, so that `ψ u ∉ (ψ v)`. -/
private lemma notMem_span_of_isLocalRing {A B : Type*} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] [IsLocalRing B] {s : Set A} (hs : Algebra.adjoin k s = ⊤) (ε : A →ₐ[k] k)
    [(RingHom.ker ε.toRingHom).IsPrime] (hε : ∀ a ∈ s, ε a = 0) (ψ : A →ₐ[k] B)
    (hψ : ∀ a ∈ s, ψ a ∈ IsLocalRing.maximalIdeal B)
    {u v : A} (h : ψ u ∉ Ideal.span {ψ v}) :
    algebraMap A (Localization.AtPrime (RingHom.ker ε.toRingHom)) u ∉
      Ideal.span {algebraMap A (Localization.AtPrime (RingHom.ker ε.toRingHom)) v} := by
  have hm (a : A) : ψ a - algebraMap k B (ε a) ∈ IsLocalRing.maximalIdeal B := by
    have ha : a ∈ Algebra.adjoin k s := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem a ha => simpa [hε a ha] using hψ a ha
    | algebraMap c => simp
    | add a b _ _ ha hb => simpa [add_sub_add_comm] using add_mem ha hb
    | mul a b _ _ ha hb =>
      convert add_mem (Ideal.mul_mem_right (ψ b) _ ha)
        (Ideal.mul_mem_left _ (algebraMap k B (ε a)) hb) using 1
      simp only [map_mul]
      ring
  have hM : ∀ m : (RingHom.ker ε.toRingHom).primeCompl, IsUnit ((ψ : A →+* B) m) := by
    rintro ⟨m, hm'⟩
    have hu : IsUnit (algebraMap k B (ε m)) :=
      (isUnit_iff_ne_zero.mpr fun h ↦ hm' (RingHom.mem_ker.mpr h)).map _
    by_contra hn
    refine (IsLocalRing.mem_maximalIdeal _).mp ?_ hu
    simpa using sub_mem ((IsLocalRing.mem_maximalIdeal _).mpr hn) (hm m)
  let L := IsLocalization.lift (S := Localization.AtPrime (RingHom.ker ε.toRingHom)) hM
  have hL (a : A) : L (algebraMap A _ a) = ψ a := IsLocalization.lift_eq hM a
  intro hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  refine h (Ideal.mem_span_singleton'.mpr ⟨L c, ?_⟩)
  rw [← hL, ← hL, ← hc, map_mul]

section Node

variable (k) in
/-- The local ring at the origin of the node `x y = 0`. -/
abbrev NodeLocalRing : Type u :=
  Localization.AtPrime (RingHom.ker (NodeAlgebra.origin k).toRingHom)

/-- In the local ring of the node at the origin, neither coordinate lies in the ideal generated
by the other. -/
lemma node_coord_notMem_span {i j : Fin 2} (hij : i ≠ j) :
    algebraMap (NodeAlgebra k 0) (NodeLocalRing k) (NodeAlgebra.coord 0 i) ∉
      Ideal.span {algebraMap (NodeAlgebra k 0) (NodeLocalRing k) (NodeAlgebra.coord 0 j)} := by
  -- Map to `k⟦t⟧` by `(x, y) ↦ (t, 0)` or `(x, y) ↦ (0, t)`.
  let p : Fin 2 → PowerSeries k := fun l ↦ if l = i then PowerSeries.X else 0
  have hp : p 0 * p 1 = algebraMap k _ 0 := by
    fin_cases i <;> simp [p]
  refine notMem_span_of_isLocalRing (NodeAlgebra.adjoin_range_coord 0) (NodeAlgebra.origin k)
    (by rintro _ ⟨l, rfl⟩; simp) (NodeAlgebra.lift 0 (p 0) (p 1) hp) ?_ ?_
  · rintro _ ⟨l, rfl⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    fin_cases i <;> fin_cases l <;> simp [p]
  · fin_cases i <;> fin_cases j <;> simp_all [p, PowerSeries.X_ne_zero]

/-- **Check.** For the local ring `O` of the node `x y = 0` at the origin, over any field,
`Ω[O⁄k]` has no free quotient of nonzero rank. -/
theorem node_not_surjective {d : ℕ} (hd : d ≠ 0)
    (g : Ω[NodeLocalRing k⁄k] →ₗ[NodeLocalRing k] (Fin d → NodeLocalRing k)) :
    ¬ Function.Surjective g := by
  refine not_surjective_kaehlerDifferential_of_mul_eq_zero ?_
    (by rw [← map_mul, NodeAlgebra.coord_zero_mul_coord_one, map_zero, map_zero])
    (node_coord_notMem_span (by decide)) (node_coord_notMem_span (by decide)) hd g
  convert KaehlerDifferential.span_image_D_eq_top_of_isLocalization (B := NodeLocalRing k)
    (RingHom.ker (NodeAlgebra.origin k).toRingHom).primeCompl
    (NodeAlgebra.adjoin_range_coord (0 : k)) using 2
  ext ω
  simp [Fin.exists_fin_two, eq_comm]

end Node

section Cusp

/-- Evaluating the cusp polynomial `y ^ 2 - x ^ 3` at `(i x, a)`. -/
private lemma eval₂_cuspPolynomial {T : Type*} [CommRing T] (i : Polynomial k →+* T) (a : T) :
    (cuspPolynomial k).eval₂ i a = a ^ 2 - i Polynomial.X ^ 3 := by
  rw [cuspPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, map_pow]

variable (k) in
/-- The origin of the cusp, as a `k`-point of its coordinate ring. -/
def cuspOrigin : CuspRing k →ₐ[k] k :=
  AdjoinRoot.liftAlgHom _ (Polynomial.aeval 0) 0 (by rw [eval₂_cuspPolynomial]; simp)

/-- The origin of the cusp is a prime ideal of its coordinate ring. -/
instance isPrime_ker_cuspOrigin : (RingHom.ker (cuspOrigin k).toRingHom).IsPrime :=
  RingHom.ker_isPrime _

/-- The coordinate `x` vanishes at the origin of the cusp. -/
@[simp]
lemma cuspOrigin_cuspX : cuspOrigin k (cuspX k) = 0 := by
  simp [cuspOrigin, cuspX_def]

/-- The coordinate `y` vanishes at the origin of the cusp. -/
@[simp]
lemma cuspOrigin_cuspY : cuspOrigin k (cuspY k) = 0 := by
  simp [cuspOrigin, cuspY_def]

variable (k) in
/-- The local ring at the origin of the cusp `y ^ 2 = x ^ 3`. -/
abbrev CuspLocalRing : Type u := Localization.AtPrime (RingHom.ker (cuspOrigin k).toRingHom)

/-- The image of `x` in the local ring of the cusp at the origin. -/
abbrev xc : CuspLocalRing k := algebraMap (CuspRing k) (CuspLocalRing k) (cuspX k)

/-- The image of `y` in the local ring of the cusp at the origin. -/
abbrev yc : CuspLocalRing k := algebraMap (CuspRing k) (CuspLocalRing k) (cuspY k)

/-- In the local ring of the cusp at the origin, `y ∉ (x ^ 2)`. -/
lemma yc_notMem_span_xc_sq : yc (k := k) ∉ Ideal.span {xc ^ 2} := by
  -- Map to `k⟦t⟧` by `(x, y) ↦ (t ^ 2, t ^ 3)`.
  rw [← map_pow]
  refine notMem_span_of_isLocalRing (adjoin_cuspX_cuspY_eq_top k) (cuspOrigin k) (by simp)
    (AdjoinRoot.liftAlgHom _ (Polynomial.aeval (PowerSeries.X ^ 2 : PowerSeries k))
      (PowerSeries.X ^ 3) (by rw [eval₂_cuspPolynomial]; simp [← pow_mul])) ?_ ?_
  · rintro a (rfl | rfl) <;>
      simp [cuspX_def, cuspY_def, PowerSeries.isUnit_iff_constantCoeff]
  · simp [cuspX_def, cuspY_def, ← pow_mul, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]

/-- In the local ring of the cusp at the origin, `x ^ 2 ∉ (y)`. -/
lemma xc_sq_notMem_span_yc : xc (k := k) ^ 2 ∉ Ideal.span {yc} := by
  -- Map to `k⟦t⟧ / (t ^ 3)` by `(x, y) ↦ (t, 0)`.
  let I : Ideal (PowerSeries k) := Ideal.span {PowerSeries.X ^ 3}
  have : Nontrivial (PowerSeries k ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr <| by
    simp [I, Ideal.span_singleton_eq_top, PowerSeries.isUnit_iff_constantCoeff]
  have : IsLocalRing (PowerSeries k ⧸ I) :=
    .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rw [← map_pow]
  refine notMem_span_of_isLocalRing (adjoin_cuspX_cuspY_eq_top k) (cuspOrigin k) (by simp)
    (AdjoinRoot.liftAlgHom _ (Polynomial.aeval (Ideal.Quotient.mk I PowerSeries.X)) 0
      (by rw [eval₂_cuspPolynomial]; simp [I, ← map_pow])) ?_ ?_
  · rintro a (rfl | rfl)
    · simp only [cuspX_def, AdjoinRoot.liftAlgHom_of, Polynomial.aeval_X]
      refine (IsNilpotent.not_isUnit ⟨3, ?_⟩)
      simp [I, ← map_pow]
    · simp [cuspY_def]
  · simp [cuspX_def, cuspY_def, I, Polynomial.aeval_X_pow, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]

/-- **Check.** For the local ring `O` of the cusp `y ^ 2 = x ^ 3` at the origin, over a field in
which `2 ≠ 0` and `3 ≠ 0`, `Ω[O⁄k]` has no free quotient of nonzero rank. -/
theorem cusp_not_surjective (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) {d : ℕ} (hd : d ≠ 0)
    (g : Ω[CuspLocalRing k⁄k] →ₗ[CuspLocalRing k] (Fin d → CuspLocalRing k)) :
    ¬ Function.Surjective g := by
  have hu : ∀ c : k, c ≠ 0 → IsUnit (algebraMap k (CuspLocalRing k) c) :=
    fun c hc ↦ (isUnit_iff_ne_zero.mpr hc).map _
  refine not_surjective_kaehlerDifferential_of_sq_eq_pow_three
    (by simpa only [map_ofNat] using hu 2 h2) (by simpa only [map_ofNat] using hu 3 h3) ?_
    (by rw [← map_pow, ← map_pow, cuspY_sq]) xc_sq_notMem_span_yc yc_notMem_span_xc_sq hd g
  rw [← Set.image_pair, ← Set.image_pair]
  exact KaehlerDifferential.span_image_D_eq_top_of_isLocalization
    (RingHom.ker (cuspOrigin k).toRingHom).primeCompl (adjoin_cuspX_cuspY_eq_top k)

/-- **Check.** Over `ℚ`, the local ring of the cusp at the origin has no free quotient of its
differentials of rank one. -/
example (g : Ω[CuspLocalRing ℚ⁄ℚ] →ₗ[CuspLocalRing ℚ] (Fin 1 → CuspLocalRing ℚ)) :
    ¬ Function.Surjective g :=
  cusp_not_surjective two_ne_zero three_ne_zero one_ne_zero g

end Cusp

end TauCeti.NodeCuspDifferentialsExample

end
