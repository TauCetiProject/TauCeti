/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Semiclassical.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.GroupTheory.Perm.Fin
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Calculus.IteratedFDeriv.SymmetricFinite
import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Mixed semiclassical Sobolev norms in a tube

Let `E` be a finite-dimensional real inner product space and `V` a subspace of `E`. Near a
submanifold of a manifold, after choosing a tube, `V` plays the role of the normal directions and
its orthogonal complement `Vᗮ` that of the tangent, or horizontal, directions. Fields that
concentrate at the scale `h` around the submanifold vary on the scale `h` in the normal directions
but only on a scale of order one along it, as the rescaled Seiberg–Witten fields near a
pseudoholomorphic curve in Taubes's large-parameter analysis do, at the scale `h = (2r)^(-1/2)`.
The natural norms for them weight the normal derivatives by powers of `h`, leave the horizontal
derivatives unscaled, and normalize the volume by the normal volume `h^(dim V)` of the tube.

**Mixed derivatives.** For `a ≤ n`, the mixed derivative of order `(a, n - a)` of `f` at `x` is
the `n`-th derivative `Dⁿ f x` restricted to horizontal vectors in its first `a` slots and to
normal vectors in the remaining `n - a`:

`∂^{a, n - a} f x (m) = Dⁿ f x (P_{Vᗮ} m₀, …, P_{Vᗮ} m_{a-1}, P_V m_a, …, P_V m_{n-1})`

(`Submodule.mixedIteratedFDeriv`). It is bounded by the full derivative
(`Submodule.norm_mixedIteratedFDeriv_le`). Conversely, by the symmetry of iterated derivatives and
the expansion of each argument into its horizontal and normal parts, the full derivative of a
`Cⁿ` function is bounded by its mixed derivatives,
`‖Dⁿ f x‖ ≤ ∑_{a ≤ n} (n choose a) ‖∂^{a, n - a} f x‖`
(`Submodule.norm_iteratedFDeriv_le_sum_choose_mul_norm_mixedIteratedFDeriv`).

**The mixed norm.** The mixed semiclassical Sobolev norm of order `j` at scale `h` is

`‖f‖_{j,h,V} = h^(-dim V / 2) ∑_{n ≤ j} ∑_{a ≤ n} h^(n - a) ‖∂^{a, n - a} f‖₂`

(`Submodule.mixedSemiclassicalSobolevNorm`): each normal derivative costs a factor `h`, each
horizontal one none. The **normal dilation** `Submodule.normalDilation V t`, which fixes `Vᗮ` and
multiplies `V` by `t`, reads a field in the rescaled normal coordinate `w = y / h`, `y ∈ V`: for
`f` of class `Cʲ` and `h > 0`, the mixed norm at scale `h` is the mixed norm at scale one of the
dilated field `f ∘ normalDilation V h`, that is, the unweighted mixed norm
`∑_{a + b ≤ j} ‖∇^a ∂_w^b v‖₂` of the rescaled field `v` against `dvol dw`
(`Submodule.mixedSemiclassicalSobolevNorm_eq_comp_normalDilation`).

At scale one the mixed norm is equivalent to the ordinary Sobolev norm
`∑_{n ≤ j} ‖Dⁿ f‖₂`, with constants depending only on `j`
(`Submodule.memLp_iteratedFDeriv_and_semiclassicalSobolevNorm_one_le`,
`Submodule.mixedSemiclassicalSobolevNorm_one_le_mul_semiclassicalSobolevNorm_one`). Together with
the dilation identity this gives the **Sobolev embedding uniformly in the scale**: if `2j > dim E`,
then `|f(x)| ≤ C ‖f‖_{j,h,V}` for every `h > 0`, with `C` independent of `h`
(`Submodule.exists_norm_le_mul_mixedSemiclassicalSobolevNorm`). This is the pointwise control of
fields in the tube norms; the volume normalization `h^(-dim V / 2)` is the one that makes it
uniform.

**Derivatives.** A horizontal derivative is bounded from order `j + 1` to order `j` with no loss
in `h`, `‖∂_e f‖_{j,h,V} ≤ ‖e‖ ‖f‖_{j+1,h,V}` for `e ∈ Vᗮ`
(`Submodule.mixedSemiclassicalSobolevNorm_fderiv_apply_le_of_mem_orthogonal`), while a normal
derivative costs one factor of the scale, `h ‖∂_v f‖_{j,h,V} ≤ ‖v‖ ‖f‖_{j+1,h,V}` for `v ∈ V`
(`Submodule.mul_mixedSemiclassicalSobolevNorm_fderiv_apply_le_of_mem`). These are the graph
derivatives `(h ∂_ν, ∇)` of the tube spaces; on the isotropic semiclassical norms of
`TauCeti.semiclassicalSobolevNorm` every derivative costs a factor `h`.

The derivative identities hold for any subspace `V` with an orthogonal projection; the
determinant of the normal dilation and the norms assume that `E` is finite-dimensional. A product
tube model `base × fibre` is the case `E = WithLp 2 (base × fibre)` with `V` the fibre; the inner
product space is needed for the Sobolev embedding, which the sup norm of a plain product does not
carry.

## Main definitions

* `Submodule.normalDilation V t`: the linear map `P_{Vᗮ} + t P_V`.
* `Submodule.mixedIteratedFDeriv V n a f x`: the mixed derivative of order `(a, n - a)`.
* `Submodule.mixedSemiclassicalSobolevNorm V j h f`: the mixed norm `‖f‖_{j,h,V}`.

## Main results

* `Submodule.det_normalDilation`: `det (normalDilation V t) = t ^ dim V`.
* `Submodule.mixedIteratedFDeriv_comp_normalDilation`: the mixed derivative of order
  `(a, n - a)` of `f ∘ normalDilation V t` is `t ^ (n - a)` times that of `f`.
* `Submodule.norm_iteratedFDeriv_le_sum_choose_mul_norm_mixedIteratedFDeriv`: the full derivative is
  bounded by the mixed ones.
* `Submodule.mixedSemiclassicalSobolevNorm_eq_comp_normalDilation`: the mixed norm at scale `h` is
  the unscaled mixed norm of the normally dilated field.
* `Submodule.exists_norm_le_mul_mixedSemiclassicalSobolevNorm`: the Sobolev embedding, uniformly in
  `h`.
* `Submodule.mixedSemiclassicalSobolevNorm_fderiv_apply_le_of_mem_orthogonal`,
  `Submodule.mul_mixedSemiclassicalSobolevNorm_fderiv_apply_le_of_mem`: horizontal derivatives are
  unscaled, normal derivatives cost a factor `h`.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* C. H. Taubes, *Seiberg–Witten and Gromov invariants for symplectic 4-manifolds*, First
  International Press Lecture Series 2 (2000).
-/

public section

noncomputable section

namespace Submodule

open MeasureTheory Module Finset
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (V : Submodule ℝ E)
  [V.HasOrthogonalProjection]

/-! ### The normal dilation -/

/-- The **normal dilation** by `t` along the subspace `V`: the linear map `P_{Vᗮ} + t P_V`, which
fixes the orthogonal complement `Vᗮ` and multiplies `V` by `t`. Composing a field with it reads
the field in the normal coordinate rescaled by `t`. -/
def normalDilation (t : ℝ) : E →L[ℝ] E :=
  Vᗮ.starProjection + t • V.starProjection

@[simp]
theorem normalDilation_apply (t : ℝ) (x : E) :
    V.normalDilation t x = Vᗮ.starProjection x + t • V.starProjection x :=
  (rfl)

/-- The normal dilation fixes the horizontal part of every vector. -/
theorem normalDilation_starProjection_orthogonal (t : ℝ) (x : E) :
    V.normalDilation t (Vᗮ.starProjection x) = Vᗮ.starProjection x := by
  rw [normalDilation_apply, starProjection_eq_self_iff.2 (Vᗮ.starProjection_apply_mem x),
    (V.starProjection_apply_eq_zero_iff).2 (Vᗮ.starProjection_apply_mem x), smul_zero, add_zero]

/-- The normal dilation by `t` multiplies the normal part of every vector by `t`. -/
theorem normalDilation_starProjection (t : ℝ) (x : E) :
    V.normalDilation t (V.starProjection x) = t • V.starProjection x := by
  rw [normalDilation_apply, starProjection_eq_self_iff.2 (V.starProjection_apply_mem x),
    (Vᗮ.starProjection_apply_eq_zero_iff).2
      (le_orthogonal_orthogonal V (V.starProjection_apply_mem x)), zero_add]

@[simp]
theorem normalDilation_one : V.normalDilation 1 = ContinuousLinearMap.id ℝ E := by
  ext x
  rw [ContinuousLinearMap.id_apply, normalDilation_apply, one_smul, add_comm,
    starProjection_add_starProjection_orthogonal]

/-- Normal dilations compose by multiplying their factors. -/
theorem normalDilation_mul (s t : ℝ) :
    V.normalDilation (s * t) = (V.normalDilation s).comp (V.normalDilation t) := by
  ext x
  rw [ContinuousLinearMap.comp_apply, normalDilation_apply V t, map_add, map_smul,
    normalDilation_starProjection_orthogonal, normalDilation_starProjection, smul_smul,
    normalDilation_apply, mul_comm]

/-- For `t ≠ 0` the normal dilation by `t` is a linear automorphism, with inverse the normal
dilation by `t⁻¹`. -/
def normalDilationEquiv {t : ℝ} (ht : t ≠ 0) : E ≃L[ℝ] E :=
  .ofContinuousLinearMap (V.normalDilation t) (V.normalDilation t⁻¹)
    (by rw [← normalDilation_mul, mul_inv_cancel₀ ht, normalDilation_one])
    (by rw [← normalDilation_mul, inv_mul_cancel₀ ht, normalDilation_one])

@[simp]
theorem coe_normalDilationEquiv {t : ℝ} (ht : t ≠ 0) :
    (V.normalDilationEquiv ht : E →L[ℝ] E) = V.normalDilation t :=
  (rfl)

@[simp]
theorem normalDilationEquiv_apply {t : ℝ} (ht : t ≠ 0) (x : E) :
    V.normalDilationEquiv ht x = V.normalDilation t x :=
  (rfl)

/-- **The determinant of the normal dilation** by `t` is `t ^ dim V`. -/
theorem det_normalDilation [FiniteDimensional ℝ E] (t : ℝ) :
    LinearMap.det (V.normalDilation t : E →ₗ[ℝ] E) = t ^ finrank ℝ V := by
  -- Read through the splitting `E ≃ V × Vᗮ`, the dilation is `t • id ⊕ id`.
  set e := prodEquivOfIsCompl V Vᗮ V.isCompl_orthogonal
  have hconj : (V.normalDilation t : E →ₗ[ℝ] E) =
      (e : V × Vᗮ →ₗ[ℝ] E) ∘ₗ (LinearMap.prodMap (t • LinearMap.id) LinearMap.id) ∘ₗ
        (e.symm : E →ₗ[ℝ] V × Vᗮ) := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨v, w⟩ := y
    have hw : V.starProjection (w : E) = 0 := (V.starProjection_apply_eq_zero_iff).2 w.property
    simp [e, hw, starProjection_eq_self_iff.2 v.property, add_comm]
  rw [hconj, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id,
    LinearMap.det_id, mul_one, mul_one]

/-! ### Mixed derivatives -/

/-- The **mixed derivative** of order `(a, n - a)` of `f` at `x`: the `n`-th derivative of `f` at
`x` with its first `a` arguments projected to the horizontal subspace `Vᗮ` and its remaining
`n - a` arguments projected to the normal subspace `V`. For `a ≥ n` every argument is horizontal.
Its norm is the norm of `Dⁿ f x` on `a` horizontal and `n - a` normal vectors. -/
def mixedIteratedFDeriv (n a : ℕ) (f : E → F) (x : E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F :=
  (iteratedFDeriv ℝ n f x).compContinuousLinearMap fun i ↦
    if (i : ℕ) < a then Vᗮ.starProjection else V.starProjection

@[simp]
theorem mixedIteratedFDeriv_apply (n a : ℕ) (f : E → F) (x : E) (m : Fin n → E) :
    V.mixedIteratedFDeriv n a f x m = iteratedFDeriv ℝ n f x fun i ↦
      if (i : ℕ) < a then Vᗮ.starProjection (m i) else V.starProjection (m i) := by
  rw [mixedIteratedFDeriv, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  exact apply_ite (fun L : E →L[ℝ] E ↦ L (m i)) _ _ _

/-- A mixed derivative is bounded by the full derivative of the same order. -/
theorem norm_mixedIteratedFDeriv_le (n a : ℕ) (f : E → F) (x : E) :
    ‖V.mixedIteratedFDeriv n a f x‖ ≤ ‖iteratedFDeriv ℝ n f x‖ := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) (prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
    fun i _ ↦ ?_)
  split_ifs
  · exact Vᗮ.starProjection_norm_le
  · exact V.starProjection_norm_le

/-- The mixed derivatives of a function of class `Cⁿ` depend continuously on the point. -/
theorem continuous_mixedIteratedFDeriv {n : ℕ} {f : E → F} (hf : ContDiff ℝ n f) (a : ℕ) :
    Continuous (V.mixedIteratedFDeriv n a f) :=
  (ContinuousMultilinearMap.compContinuousLinearMapL fun i : Fin n ↦
    if (i : ℕ) < a then Vᗮ.starProjection else V.starProjection).continuous.comp
    (hf.continuous_iteratedFDeriv le_rfl)

@[simp]
theorem mixedIteratedFDeriv_zero_fun (n a : ℕ) :
    V.mixedIteratedFDeriv n a (0 : E → F) = 0 := by
  ext x m
  simp [mixedIteratedFDeriv_apply, iteratedFDeriv_zero]

/-- Mixed derivatives commute with translations. -/
theorem mixedIteratedFDeriv_comp_sub (n a : ℕ) (f : E → F) (c : E) :
    V.mixedIteratedFDeriv n a (fun y ↦ f (y - c)) =
      fun x ↦ V.mixedIteratedFDeriv n a f (x - c) := by
  ext x : 1
  rw [mixedIteratedFDeriv, mixedIteratedFDeriv, iteratedFDeriv_comp_sub]

/-- **Mixed derivatives under the normal dilation.** For `f` of class `Cⁿ`, the mixed derivative
of order `(a, n - a)` of `f ∘ normalDilation V t` is `t ^ (n - a)` times that of `f` at the
dilated point: each normal derivative contributes a factor `t`, each horizontal one none. -/
theorem mixedIteratedFDeriv_comp_normalDilation {n : ℕ} {f : E → F} (hf : ContDiff ℝ n f)
    (a : ℕ) (t : ℝ) (x : E) :
    V.mixedIteratedFDeriv n a (f ∘ V.normalDilation t) x =
      t ^ (n - a) • V.mixedIteratedFDeriv n a f (V.normalDilation t x) := by
  -- The `n - a` normal slots each contribute a factor `t`.
  have hcard : #{i : Fin n | ¬(i : ℕ) < a} = n - a := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i ↦ (i : ℕ) < a)
    rw [Fin.card_filter_val_lt, card_univ, Fintype.card_fin] at h
    omega
  have hc : ∏ i : Fin n, (if (i : ℕ) < a then (1 : ℝ) else t) = t ^ (n - a) := by
    rw [prod_ite, prod_const_one, one_mul, prod_const, hcard]
  ext m
  rw [mixedIteratedFDeriv_apply, (V.normalDilation t).iteratedFDeriv_comp_right hf x le_rfl,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply,
    mixedIteratedFDeriv_apply, ← hc, ← ContinuousMultilinearMap.map_smul_univ]
  congr 1
  ext i
  split_ifs <;> simp only [one_smul, normalDilation_starProjection_orthogonal,
    normalDilation_starProjection]

/-- **The full derivative is bounded by the mixed derivatives.** For `f` of class `Cⁿ` at `x`,
`‖Dⁿ f x‖ ≤ ∑_{a ≤ n} (n choose a) ‖∂^{a, n - a} f x‖`. Splitting every argument into its horizontal
and normal parts expands `Dⁿ f x` into `2ⁿ` terms; by the symmetry of `Dⁿ f x`, the term whose
arguments indexed by a set `S` are horizontal is a value of the mixed derivative of order
`(#S, n - #S)`. -/
theorem norm_iteratedFDeriv_le_sum_choose_mul_norm_mixedIteratedFDeriv {n : ℕ} {f : E → F}
    {x : E} (hf : ContDiffAt ℝ n f x) :
    ‖iteratedFDeriv ℝ n f x‖ ≤
      ∑ a ∈ range (n + 1), (n.choose a : ℝ) * ‖V.mixedIteratedFDeriv n a f x‖ := by
  classical
  -- The term of the expansion in which the arguments indexed by `S` are horizontal.
  have hterm (S : Finset (Fin n)) (m : Fin n → E) :
      ‖iteratedFDeriv ℝ n f x (S.piecewise (fun i ↦ Vᗮ.starProjection (m i))
          fun i ↦ V.starProjection (m i))‖ ≤ ‖V.mixedIteratedFDeriv n #S f x‖ * ∏ i, ‖m i‖ := by
    -- A permutation of the slots carrying the first `#S` slots onto `S`.
    have h₁ : Fintype.card {i : Fin n // (i : ℕ) < #S} = Fintype.card {i : Fin n // i ∈ S} := by
      rw [Fintype.card_subtype, Fin.card_filter_val_lt, Fintype.card_coe,
        min_eq_right (by simpa using S.card_le_univ)]
    have h₂ : Fintype.card {i : Fin n // ¬(i : ℕ) < #S} = Fintype.card {i : Fin n // i ∉ S} := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h₁]
    set σ := Equiv.subtypeCongr (Fintype.equivOfCardEq h₁) (Fintype.equivOfCardEq h₂)
    have hσ (i : Fin n) : σ i ∈ S ↔ (i : ℕ) < #S := by
      by_cases hi : (i : ℕ) < #S
      · simp [σ, Equiv.subtypeCongr, hi]
      · simpa [σ, Equiv.subtypeCongr, hi] using (Fintype.equivOfCardEq h₂ ⟨i, hi⟩).property
    rw [← hf.iteratedFDeriv_comp_perm_of_le (by simp) _ σ, ← Equiv.prod_comp σ fun i ↦ ‖m i‖]
    have hperm : (S.piecewise (fun i ↦ Vᗮ.starProjection (m i))
        fun i ↦ V.starProjection (m i)) ∘ σ = fun i : Fin n ↦
          if (i : ℕ) < #S then Vᗮ.starProjection (m (σ i)) else V.starProjection (m (σ i)) := by
      ext i
      simp only [Function.comp_apply, piecewise, hσ]
    rw [hperm, ← mixedIteratedFDeriv_apply]
    exact ContinuousMultilinearMap.le_opNorm _ _
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  have hm : (fun i ↦ Vᗮ.starProjection (m i)) + (fun i ↦ V.starProjection (m i)) = m := by
    ext i
    simp only [Pi.add_apply, add_comm, starProjection_add_starProjection_orthogonal]
  have hexp := (iteratedFDeriv ℝ n f x).map_add_univ (fun i ↦ Vᗮ.starProjection (m i))
    fun i ↦ V.starProjection (m i)
  rw [hm] at hexp
  rw [hexp]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun S _ ↦ hterm S m).trans_eq ?_)
  rw [← sum_mul, ← powerset_univ,
    sum_powerset_apply_card fun k ↦ ‖V.mixedIteratedFDeriv n k f x‖, card_univ,
    Fintype.card_fin]
  simp only [nsmul_eq_mul]

/-- **A normal derivative raises the normal order.** For `a ≤ n`, `f` of class `Cⁿ⁺¹` at `x` and a
normal vector `v ∈ V`, the mixed derivative of order `(a, n - a)` of the derivative of `f` along
`v` is the mixed derivative of order `(a, n + 1 - a)` of `f` with `v` in its last slot. -/
theorem mixedIteratedFDeriv_fderiv_apply_of_mem {n a : ℕ} (ha : a ≤ n) {f : E → F} {x : E}
    (hf : ContDiffAt ℝ (n + 1) f x) {v : E} (hv : v ∈ V) (m : Fin n → E) :
    V.mixedIteratedFDeriv n a (fun y ↦ fderiv ℝ f y v) x m =
      V.mixedIteratedFDeriv (n + 1) a f x (Fin.snoc m v) := by
  rw [mixedIteratedFDeriv_apply, hf.iteratedFDeriv_fderiv_apply_eq_iteratedFDeriv_snoc,
    mixedIteratedFDeriv_apply]
  congr 1
  ext i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · simp [show ¬n < a by omega, starProjection_eq_self_iff.2 hv]
  · simp

/-- **A horizontal derivative raises the horizontal order.** For `a ≤ n`, `f` of class `Cⁿ⁺¹` at
`x` and a horizontal vector `e ∈ Vᗮ`, the mixed derivative of order `(a, n - a)` of the derivative
of `f` along `e` is the mixed derivative of order `(a + 1, n - a)` of `f` with `e` inserted in
slot `a`, the first normal slot. -/
theorem mixedIteratedFDeriv_fderiv_apply_of_mem_orthogonal {n a : ℕ} (ha : a ≤ n) {f : E → F}
    {x : E} (hf : ContDiffAt ℝ (n + 1) f x) {e : E} (he : e ∈ Vᗮ) (m : Fin n → E) :
    V.mixedIteratedFDeriv n a (fun y ↦ fderiv ℝ f y e) x m =
      V.mixedIteratedFDeriv (n + 1) (a + 1) f x (Fin.insertNth ⟨a, by omega⟩ e m) := by
  set p : Fin (n + 1) := ⟨a, by omega⟩
  set w : Fin n → E := fun i ↦
    if (i : ℕ) < a then Vᗮ.starProjection (m i) else V.starProjection (m i)
  -- By symmetry, the slot of the new horizontal argument may be moved from the last one to `a`.
  have hsymm : iteratedFDeriv ℝ (n + 1) f x (Fin.snoc w e) =
      iteratedFDeriv ℝ (n + 1) f x (p.insertNth e w) := by
    rw [← Fin.insertNth_last', ← Fin.cons_comp_cycleRange, ← Fin.cons_comp_cycleRange,
      hf.iteratedFDeriv_comp_perm_of_le (by simp), hf.iteratedFDeriv_comp_perm_of_le (by simp)]
  rw [mixedIteratedFDeriv_apply, hf.iteratedFDeriv_fderiv_apply_eq_iteratedFDeriv_snoc, hsymm,
    mixedIteratedFDeriv_apply]
  congr 1
  ext i
  refine p.succAboveCases ?_ (fun k ↦ ?_) i
  · simp [p, starProjection_eq_self_iff.2 he]
  · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
    by_cases hk : (k : ℕ) < a
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [p, Fin.lt_def] using hk)]
      simp [w, hk, show (k : ℕ) < a + 1 by omega]
    · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [p, Fin.le_def] using hk)]
      simp [w, hk]

/-- The mixed derivatives of a normal derivative:
`‖∂^{a, n - a} (∂_v f) x‖ ≤ ‖v‖ ‖∂^{a, n + 1 - a} f x‖` for `a ≤ n` and `v ∈ V`. -/
theorem norm_mixedIteratedFDeriv_fderiv_apply_le_of_mem {n a : ℕ} (ha : a ≤ n) {f : E → F}
    {x : E} (hf : ContDiffAt ℝ (n + 1) f x) {v : E} (hv : v ∈ V) :
    ‖V.mixedIteratedFDeriv n a (fun y ↦ fderiv ℝ f y v) x‖ ≤
      ‖v‖ * ‖V.mixedIteratedFDeriv (n + 1) a f x‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  rw [V.mixedIteratedFDeriv_fderiv_apply_of_mem ha hf hv]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans_eq ?_
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- The mixed derivatives of a horizontal derivative:
`‖∂^{a, n - a} (∂_e f) x‖ ≤ ‖e‖ ‖∂^{a + 1, n - a} f x‖` for `a ≤ n` and `e ∈ Vᗮ`. -/
theorem norm_mixedIteratedFDeriv_fderiv_apply_le_of_mem_orthogonal {n a : ℕ} (ha : a ≤ n)
    {f : E → F} {x : E} (hf : ContDiffAt ℝ (n + 1) f x) {e : E} (he : e ∈ Vᗮ) :
    ‖V.mixedIteratedFDeriv n a (fun y ↦ fderiv ℝ f y e) x‖ ≤
      ‖e‖ * ‖V.mixedIteratedFDeriv (n + 1) (a + 1) f x‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  rw [V.mixedIteratedFDeriv_fderiv_apply_of_mem_orthogonal ha hf he]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans_eq ?_
  rw [Fin.prod_univ_succAbove _ ⟨a, by omega⟩]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  ring

/-! ### The mixed norm -/

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- If the `n`-th derivative of `f` is square integrable, so is every mixed derivative of total
order `n`. -/
theorem memLp_mixedIteratedFDeriv {n : ℕ} {f : E → F} (hD : MemLp (iteratedFDeriv ℝ n f) 2)
    (a : ℕ) : MemLp (V.mixedIteratedFDeriv n a f) 2 :=
  hD.of_le ((ContinuousMultilinearMap.compContinuousLinearMapL fun i : Fin n ↦
      if (i : ℕ) < a then Vᗮ.starProjection else V.starProjection).continuous
        |>.comp_aestronglyMeasurable hD.aestronglyMeasurable)
    (.of_forall fun x ↦ V.norm_mixedIteratedFDeriv_le n a f x)

/-- **The `L²` norm of the full derivative is bounded by those of the mixed derivatives.** For `f`
of class `Cⁿ` whose mixed derivatives of total order `n` are square integrable, `Dⁿ f` is square
integrable and `‖Dⁿ f‖₂ ≤ ∑_{a ≤ n} (n choose a) ‖∂^{a, n - a} f‖₂`. -/
theorem memLp_iteratedFDeriv_and_lpNorm_le {n : ℕ} {f : E → F} (hf : ContDiff ℝ n f)
    (hm : ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) 2) :
    MemLp (iteratedFDeriv ℝ n f) 2 ∧ lpNorm (iteratedFDeriv ℝ n f) 2 volume ≤
      ∑ a ∈ range (n + 1), (n.choose a : ℝ) * lpNorm (V.mixedIteratedFDeriv n a f) 2 volume := by
  have hm' (a : ℕ) (ha : a ∈ range (n + 1)) : MemLp (V.mixedIteratedFDeriv n a f) 2 :=
    hm a (Nat.lt_succ_iff.1 (mem_range.1 ha))
  set Ψ : E → ℝ := ∑ a ∈ range (n + 1), (n.choose a : ℝ) • fun x ↦ ‖V.mixedIteratedFDeriv n a f x‖
  have hΨm : MemLp Ψ 2 := memLp_finsetSum' _ fun a ha ↦ (hm' a ha).norm.const_smul _
  have hle (x : E) : ‖iteratedFDeriv ℝ n f x‖ ≤ Ψ x := by
    simpa [Ψ, Finset.sum_apply] using
      V.norm_iteratedFDeriv_le_sum_choose_mul_norm_mixedIteratedFDeriv hf.contDiffAt
  refine ⟨hΨm.of_le (hf.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
    (.of_forall fun x ↦ (hle x).trans (le_abs_self _)), (lpNorm_mono_real hΨm hle).trans ?_⟩
  refine (lpNorm_sum_le (fun a ha ↦ (hm' a ha).norm.const_smul _) one_le_two).trans_eq
    (sum_congr rfl fun a ha ↦ ?_)
  rw [lpNorm_const_smul_of_nonneg (Nat.cast_nonneg _), lpNorm_norm (hm' a ha).aestronglyMeasurable]

/-- The **mixed semiclassical Sobolev norm** of order `j` at scale `h` along the normal subspace
`V`,

`‖f‖_{j,h,V} = h^(-dim V / 2) ∑_{n ≤ j} ∑_{a ≤ n} h^(n - a) ‖∂^{a, n - a} f‖₂`:

the `L²` norms of the mixed derivatives through total order `j`, each normal derivative weighted
by `h` and each horizontal one unweighted, against the volume normalized by the normal volume
`h^(dim V)`. For `f` of class `Cʲ` and `h > 0` it is the unweighted mixed norm of the normally
dilated field `f ∘ normalDilation V h`
(`Submodule.mixedSemiclassicalSobolevNorm_eq_comp_normalDilation`).

The value is meaningful only when the mixed derivatives are in `L²`: `lpNorm` is `0` on a function
outside `L²`. -/
def mixedSemiclassicalSobolevNorm (j : ℕ) (h : ℝ) (f : E → F) : ℝ :=
  h ^ (-(finrank ℝ V : ℝ) / 2) * ∑ n ∈ range (j + 1), ∑ a ∈ range (n + 1),
    h ^ (n - a) * lpNorm (V.mixedIteratedFDeriv n a f) 2 volume

/-- The defining formula of the mixed norm, valid at every scale `h`. -/
theorem mixedSemiclassicalSobolevNorm_def (j : ℕ) (h : ℝ) (f : E → F) :
    V.mixedSemiclassicalSobolevNorm j h f =
      h ^ (-(finrank ℝ V : ℝ) / 2) * ∑ n ∈ range (j + 1), ∑ a ∈ range (n + 1),
        h ^ (n - a) * lpNorm (V.mixedIteratedFDeriv n a f) 2 volume :=
  (rfl)

/-- At scale one the mixed norm is the sum of the `L²` norms of the mixed derivatives through
total order `j`. -/
@[simp]
theorem mixedSemiclassicalSobolevNorm_one (j : ℕ) (f : E → F) :
    V.mixedSemiclassicalSobolevNorm j 1 f = ∑ n ∈ range (j + 1), ∑ a ∈ range (n + 1),
      lpNorm (V.mixedIteratedFDeriv n a f) 2 volume := by
  simp [mixedSemiclassicalSobolevNorm]

@[simp]
theorem mixedSemiclassicalSobolevNorm_zero (j : ℕ) (h : ℝ) :
    V.mixedSemiclassicalSobolevNorm j h (0 : E → F) = 0 := by
  simp [mixedSemiclassicalSobolevNorm]

theorem mixedSemiclassicalSobolevNorm_nonneg (j : ℕ) {h : ℝ} (hh : 0 ≤ h) (f : E → F) :
    0 ≤ V.mixedSemiclassicalSobolevNorm j h f :=
  mul_nonneg (Real.rpow_nonneg hh _) (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦
    mul_nonneg (pow_nonneg hh _) lpNorm_nonneg)

/-- **Translation invariance of the mixed norm.** `‖f (· - c)‖_{j,h,V} = ‖f‖_{j,h,V}`. -/
@[simp]
theorem mixedSemiclassicalSobolevNorm_comp_sub (j : ℕ) (h : ℝ) (f : E → F) (c : E) :
    V.mixedSemiclassicalSobolevNorm j h (fun x ↦ f (x - c)) =
      V.mixedSemiclassicalSobolevNorm j h f := by
  simp only [mixedSemiclassicalSobolevNorm, mixedIteratedFDeriv_comp_sub, ← toReal_eLpNorm]
  congr 1
  refine sum_congr rfl fun n _ ↦ sum_congr rfl fun a _ ↦ ?_
  conv_rhs => rw [← (measurePreserving_sub_right volume c).map_eq]
  rw [(measurableEmbedding_subRight c).eLpNorm_map_measure]
  rfl

/-- **Change of variables under the normal dilation.** Composing with the normal dilation by
`h > 0` multiplies `L²` norms by `h^(-dim V / 2)`. -/
theorem lpNorm_comp_normalDilation {G : Type*} [NormedAddCommGroup G] (u : E → G) {h : ℝ}
    (hh : 0 < h) :
    lpNorm (u ∘ V.normalDilation h) 2 volume =
      h ^ (-(finrank ℝ V : ℝ) / 2) * lpNorm u 2 volume := by
  have hc := Measure.eLpNorm_comp_continuousLinearEquiv volume u (V.normalDilationEquiv hh.ne') 2
  have hdet : LinearMap.det ((V.normalDilationEquiv hh.ne' : E ≃ₗ[ℝ] E) : E →ₗ[ℝ] E) =
      h ^ finrank ℝ V := V.det_normalDilation h
  have hval : |(h ^ finrank ℝ V)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal =
      h ^ (-(finrank ℝ V : ℝ) / 2) := by
    rw [abs_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_neg hh.le,
      ← Real.rpow_mul hh.le]
    congr 1
    norm_num
    ring
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  rw [hdet] at hc
  rw [show u ∘ V.normalDilation h = u ∘ V.normalDilationEquiv hh.ne' from rfl, hc,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (abs_nonneg _), hval]


/-- **The mixed norm is the unscaled mixed norm of the normally dilated field.** For `f` of class
`Cʲ` and `h > 0`, `‖f‖_{j,h,V} = ‖f ∘ normalDilation V h‖_{j,1,V}`: in the normal coordinate
rescaled by `h`, each normal derivative gains the factor `h` of its weight and the change of
variables gains the volume normalization `h^(-dim V / 2)`. -/
theorem mixedSemiclassicalSobolevNorm_eq_comp_normalDilation {j : ℕ} {f : E → F}
    (hf : ContDiff ℝ j f) {h : ℝ} (hh : 0 < h) :
    V.mixedSemiclassicalSobolevNorm j h f =
      V.mixedSemiclassicalSobolevNorm j 1 (f ∘ V.normalDilation h) := by
  rw [mixedSemiclassicalSobolevNorm_one, mixedSemiclassicalSobolevNorm, mul_sum]
  refine sum_congr rfl fun n hn ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  have hD : V.mixedIteratedFDeriv n a (f ∘ V.normalDilation h) =
      h ^ (n - a) • (V.mixedIteratedFDeriv n a f ∘ V.normalDilation h) :=
    funext fun x ↦ V.mixedIteratedFDeriv_comp_normalDilation
      (hf.of_le (by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hn))) a h x
  rw [hD, lpNorm_const_smul_of_nonneg (pow_nonneg hh.le _), V.lpNorm_comp_normalDilation _ hh]
  ring

/-- **Comparison of scales.** For `0 < h ≤ 1`, multiplying the mixed norm at scale `h` by
`h^(dim V / 2)` gives at most the unscaled mixed norm and at least `hʲ` times it:
`hʲ ‖f‖_{j,1,V} ≤ h^(dim V / 2) ‖f‖_{j,h,V} ≤ ‖f‖_{j,1,V}`. -/
theorem pow_mul_mixedSemiclassicalSobolevNorm_one_le_and_le (j : ℕ) {h : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) (f : E → F) :
    h ^ j * V.mixedSemiclassicalSobolevNorm j 1 f ≤
        h ^ ((finrank ℝ V : ℝ) / 2) * V.mixedSemiclassicalSobolevNorm j h f ∧
      h ^ ((finrank ℝ V : ℝ) / 2) * V.mixedSemiclassicalSobolevNorm j h f ≤
        V.mixedSemiclassicalSobolevNorm j 1 f := by
  have hnorm : h ^ ((finrank ℝ V : ℝ) / 2) * V.mixedSemiclassicalSobolevNorm j h f =
      ∑ n ∈ range (j + 1), ∑ a ∈ range (n + 1),
        h ^ (n - a) * lpNorm (V.mixedIteratedFDeriv n a f) 2 volume := by
    rw [mixedSemiclassicalSobolevNorm, ← mul_assoc, ← Real.rpow_add hh, neg_div, add_neg_cancel,
      Real.rpow_zero, one_mul]
  rw [hnorm, mixedSemiclassicalSobolevNorm_one, mul_sum]
  refine ⟨sum_le_sum fun n hn ↦ ?_, sum_le_sum fun n _ ↦ sum_le_sum fun a _ ↦
    mul_le_of_le_one_left lpNorm_nonneg (pow_le_one₀ hh.le hh1)⟩
  rw [mul_sum]
  refine sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one hh.le hh1 ?_) lpNorm_nonneg
  have := Nat.lt_succ_iff.1 (mem_range.1 hn)
  omega

/-- **At scale one the mixed norm controls the Sobolev norm.** For `f` of class `Cʲ` whose mixed
derivatives through total order `j` are square integrable, the derivatives of `f` through order
`j` are square integrable and `∑_{n ≤ j} ‖Dⁿ f‖₂ ≤ 2ʲ ‖f‖_{j,1,V}`. -/
theorem memLp_iteratedFDeriv_and_semiclassicalSobolevNorm_one_le {j : ℕ} {f : E → F}
    (hf : ContDiff ℝ j f) (hm : ∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) 2) :
    (∀ n ≤ j, MemLp (iteratedFDeriv ℝ n f) 2) ∧
      TauCeti.semiclassicalSobolevNorm j 1 f ≤
        2 ^ j * V.mixedSemiclassicalSobolevNorm j 1 f := by
  have key (n : ℕ) (hn : n ≤ j) := V.memLp_iteratedFDeriv_and_lpNorm_le
    (hf.of_le (by exact_mod_cast hn)) (hm n hn)
  refine ⟨fun n hn ↦ (key n hn).1, ?_⟩
  rw [TauCeti.semiclassicalSobolevNorm_one, mixedSemiclassicalSobolevNorm_one, mul_sum]
  refine sum_le_sum fun n hn ↦ (key n (Nat.lt_succ_iff.1 (mem_range.1 hn))).2.trans ?_
  rw [mul_sum]
  refine sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_right ?_ lpNorm_nonneg
  calc (n.choose a : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n a
    _ ≤ 2 ^ j := pow_le_pow_right₀ one_le_two (Nat.lt_succ_iff.1 (mem_range.1 hn))

/-- **At scale one the Sobolev norm controls the mixed norm.** For `f` whose derivatives through
order `j` are square integrable, `‖f‖_{j,1,V} ≤ (j + 1) ∑_{n ≤ j} ‖Dⁿ f‖₂`. -/
theorem mixedSemiclassicalSobolevNorm_one_le_mul_semiclassicalSobolevNorm_one {j : ℕ} {f : E → F}
    (hm : ∀ n ≤ j, MemLp (iteratedFDeriv ℝ n f) 2) :
    V.mixedSemiclassicalSobolevNorm j 1 f ≤
      (j + 1) * TauCeti.semiclassicalSobolevNorm j 1 f := by
  rw [TauCeti.semiclassicalSobolevNorm_one, mixedSemiclassicalSobolevNorm_one, mul_sum]
  refine sum_le_sum fun n hn ↦ ?_
  have hn : n ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hn)
  calc ∑ a ∈ range (n + 1), lpNorm (V.mixedIteratedFDeriv n a f) 2 volume
      ≤ ∑ _a ∈ range (n + 1), lpNorm (iteratedFDeriv ℝ n f) 2 volume :=
        sum_le_sum fun a _ ↦ (lpNorm_mono_real (hm n hn).norm
          fun x ↦ V.norm_mixedIteratedFDeriv_le n a f x).trans_eq
            (lpNorm_norm (hm n hn).aestronglyMeasurable 2)
    _ ≤ (j + 1) * lpNorm (iteratedFDeriv ℝ n f) 2 volume := by
        rw [sum_const, card_range, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ lpNorm_nonneg
        exact_mod_cast Nat.succ_le_succ hn

/-- **The Sobolev embedding for the mixed norms, uniformly in the scale.** If `2j > dim E`, there
is a constant `C ≥ 0` such that for every `h > 0` and every function `f` of class `Cʲ` whose mixed
derivatives through total order `j` are square integrable, `|f(x)| ≤ C ‖f‖_{j,h,V}` at every
point. -/
theorem exists_norm_le_mul_mixedSemiclassicalSobolevNorm {j : ℕ} (hj : finrank ℝ E < 2 * j) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ f : E → ℝ, ContDiff ℝ j f →
      (∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) 2) →
        ∀ x, ‖f x‖ ≤ C * V.mixedSemiclassicalSobolevNorm j h f := by
  obtain ⟨C, hC, hCf⟩ := TauCeti.exists_norm_le_mul_semiclassicalSobolevNorm (E := E) hj
  refine ⟨C * 2 ^ j, by positivity, fun h hh f hf hm x ↦ ?_⟩
  -- Read `f` in the normal coordinate rescaled by `h`.
  set g := f ∘ V.normalDilation h
  have hg : ContDiff ℝ j g := hf.comp (V.normalDilation h).contDiff
  have hgm (n : ℕ) (hn : n ≤ j) (a : ℕ) (ha : a ≤ n) :
      MemLp (V.mixedIteratedFDeriv n a g) 2 := by
    have hD : V.mixedIteratedFDeriv n a g =
        h ^ (n - a) • fun y ↦ V.mixedIteratedFDeriv n a f (V.normalDilationEquiv hh.ne' y) :=
      funext fun y ↦ V.mixedIteratedFDeriv_comp_normalDilation
        (hf.of_le (by exact_mod_cast hn)) a h y
    rw [hD]
    exact ((hm n hn a ha).comp_continuousLinearEquiv _).const_smul _
  obtain ⟨hDg, hle⟩ := V.memLp_iteratedFDeriv_and_semiclassicalSobolevNorm_one_le hg hgm
  have hx : g (V.normalDilation h⁻¹ x) = f x := by
    simp only [g, Function.comp_apply, ← ContinuousLinearMap.comp_apply, ← normalDilation_mul,
      mul_inv_cancel₀ hh.ne', normalDilation_one, ContinuousLinearMap.id_apply]
  rw [← hx, V.mixedSemiclassicalSobolevNorm_eq_comp_normalDilation hf hh, mul_assoc]
  exact (hCf 1 one_pos g hg hDg _).trans (mul_le_mul_of_nonneg_left hle hC)


/-- **A horizontal derivative is bounded on the mixed norms, without loss in the scale.** For `f`
of class `Cʲ⁺¹` whose mixed derivatives through total order `j + 1` are square integrable, a
horizontal vector `e ∈ Vᗮ` and `h ≥ 0`, `‖∂_e f‖_{j,h,V} ≤ ‖e‖ ‖f‖_{j+1,h,V}`: horizontal
derivatives are unscaled in the mixed norms. -/
theorem mixedSemiclassicalSobolevNorm_fderiv_apply_le_of_mem_orthogonal {j : ℕ} {f : E → F}
    (hf : ContDiff ℝ (j + 1) f)
    (hm : ∀ n ≤ j + 1, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) 2) {h : ℝ} (hh : 0 ≤ h)
    {e : E} (he : e ∈ Vᗮ) :
    V.mixedSemiclassicalSobolevNorm j h (fun y ↦ fderiv ℝ f y e) ≤
      ‖e‖ * V.mixedSemiclassicalSobolevNorm (j + 1) h f := by
  -- Each term of order `(a, n - a)` on the left is bounded by `‖e‖` times the term of order
  -- `(a + 1, n - a)` on the right, which carries the same weight `h ^ (n - a)`.
  have hterm (n : ℕ) (hn : n ∈ range (j + 1)) (a : ℕ) (ha : a ∈ range (n + 1)) :
      h ^ (n - a) * lpNorm (V.mixedIteratedFDeriv n a (fun y ↦ fderiv ℝ f y e)) 2 volume ≤
        ‖e‖ * (h ^ (n + 1 - (a + 1)) *
          lpNorm (V.mixedIteratedFDeriv (n + 1) (a + 1) f) 2 volume) := by
    have hn : n ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hn)
    have ha : a ≤ n := Nat.lt_succ_iff.1 (mem_range.1 ha)
    have hmem := (hm (n + 1) (by omega) (a + 1) (by omega)).norm.const_smul ‖e‖
    rw [Nat.add_sub_add_right, mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hh _)
    refine (lpNorm_mono_real hmem fun x ↦ ?_).trans_eq ?_
    · exact V.norm_mixedIteratedFDeriv_fderiv_apply_le_of_mem_orthogonal ha
        ((hf.of_le (by exact_mod_cast Nat.succ_le_succ hn)).contDiffAt) he
    · rw [lpNorm_const_smul_of_nonneg (norm_nonneg e),
        lpNorm_norm (hm (n + 1) (by omega) (a + 1) (by omega)).aestronglyMeasurable]
  rw [mixedSemiclassicalSobolevNorm, mixedSemiclassicalSobolevNorm, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hh _)
  conv_rhs => rw [sum_range_succ', mul_add, mul_sum]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_)
    (mul_nonneg (norm_nonneg e) (sum_nonneg fun _ _ ↦ mul_nonneg (pow_nonneg hh _) lpNorm_nonneg))
  conv_rhs => rw [sum_range_succ', mul_add, mul_sum]
  exact le_add_of_le_of_nonneg (sum_le_sum fun a ha ↦ hterm n hn a ha)
    (mul_nonneg (norm_nonneg e) (mul_nonneg (pow_nonneg hh _) lpNorm_nonneg))

/-- **A normal derivative costs one factor of the scale.** For `f` of class `Cʲ⁺¹` whose mixed
derivatives through total order `j + 1` are square integrable, a normal vector `v ∈ V` and
`h ≥ 0`, `h ‖∂_v f‖_{j,h,V} ≤ ‖v‖ ‖f‖_{j+1,h,V}`: the operator `h ∂_v` is bounded from order
`j + 1` to order `j`, uniformly in `h`. -/
theorem mul_mixedSemiclassicalSobolevNorm_fderiv_apply_le_of_mem {j : ℕ} {f : E → F}
    (hf : ContDiff ℝ (j + 1) f)
    (hm : ∀ n ≤ j + 1, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) 2) {h : ℝ} (hh : 0 ≤ h)
    {v : E} (hv : v ∈ V) :
    h * V.mixedSemiclassicalSobolevNorm j h (fun y ↦ fderiv ℝ f y v) ≤
      ‖v‖ * V.mixedSemiclassicalSobolevNorm (j + 1) h f := by
  -- Each term of order `(a, n - a)` on the left, times `h`, is bounded by `‖v‖` times the term of
  -- order `(a, n + 1 - a)` on the right, which carries the weight `h ^ (n + 1 - a)`.
  have hterm (n : ℕ) (hn : n ∈ range (j + 1)) (a : ℕ) (ha : a ∈ range (n + 1)) :
      h * (h ^ (n - a) * lpNorm (V.mixedIteratedFDeriv n a (fun y ↦ fderiv ℝ f y v)) 2 volume) ≤
        ‖v‖ * (h ^ (n + 1 - a) * lpNorm (V.mixedIteratedFDeriv (n + 1) a f) 2 volume) := by
    have hn : n ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hn)
    have ha : a ≤ n := Nat.lt_succ_iff.1 (mem_range.1 ha)
    have hmem := (hm (n + 1) (by omega) a (by omega)).norm.const_smul ‖v‖
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_comm ha, mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hh _)
    refine (lpNorm_mono_real hmem fun x ↦ ?_).trans_eq ?_
    · exact V.norm_mixedIteratedFDeriv_fderiv_apply_le_of_mem ha
        ((hf.of_le (by exact_mod_cast Nat.succ_le_succ hn)).contDiffAt) hv
    · rw [lpNorm_const_smul_of_nonneg (norm_nonneg v),
        lpNorm_norm (hm (n + 1) (by omega) a (by omega)).aestronglyMeasurable]
  rw [mixedSemiclassicalSobolevNorm, mixedSemiclassicalSobolevNorm, mul_left_comm,
    mul_left_comm ‖v‖]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hh _)
  rw [mul_sum]
  conv_rhs => rw [sum_range_succ', mul_add, mul_sum]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_)
    (mul_nonneg (norm_nonneg v) (sum_nonneg fun _ _ ↦ mul_nonneg (pow_nonneg hh _) lpNorm_nonneg))
  rw [mul_sum]
  conv_rhs => rw [sum_range_succ _ (n + 1), mul_add, mul_sum]
  exact le_add_of_le_of_nonneg (sum_le_sum fun a ha ↦ hterm n hn a ha)
    (mul_nonneg (norm_nonneg v) (mul_nonneg (pow_nonneg hh _) lpNorm_nonneg))

end Submodule
