/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RegularValue
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FreeLoop
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Analysis.Complex.Determinant
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The local degree of a plane map is the winding number of its boundary loop

Let `f : ℂ → ℂ` be continuous with no zero outside the open disc of radius `r > 0`. Its fibre over
`0` is then compact, so `f` has a homological local degree at `0`
(`TauCeti.HomologicalOrientation.localDegree`), the integer `d` with `f_*[ℂ]_{f⁻¹(0)} = d • o 0`
in `H₂(ℂ, ℂ ∖ {0}; ℤ)`, for an orientation `o` of `ℂ` used on source and target. On the other hand
the boundary values of `f` give the map `u : S¹ → S¹`, `u ζ = f(rζ) / ‖f(rζ)‖`, whose degree
`Circle.degree u.toBasedLoop` counts how many times `f` winds around `0` along the circle of
radius `r`. These agree (`TauCeti.HomologicalOrientation.localDegree_eq_degree_toBasedLoop`):

`localDegree f 0 = deg u`.

So for maps of a closed disc whose boundary circle avoids `0`, extended radially to the plane, the
degree defined by local homology is the winding number of the boundary loop. When that loop is
piecewise `C¹`, its degree is also the contour winding number
(`TauCeti.Contour.windingNumber_eq_degree_of_eq_div_norm`). The local degree is the same for every
orientation of `ℂ`, because the same orientation is used on source and target.

The proof deforms `f` through maps whose zeros stay in a fixed compact set, along which the local
degree is constant (`TauCeti.HomologicalOrientation.localDegree_eq_of_homotopy_of_isCompact`):

1. pushing the values outside the disc radially onto its boundary circle, `f` becomes
   `z ↦ f(r z / ‖z‖)` outside the disc;
2. this map is a positive multiple of the cone `z ↦ ‖z‖ u(z / ‖z‖)` outside the disc;
3. maps `S¹ → S¹` of the same degree are joined in `C(S¹, S¹)`
   (`Circle.joined_iff_degree_toBasedLoop_eq`), so the cone over `u` is joined, through cones
   vanishing only at `0`, to the cone over `ζ ↦ ζⁿ`, `n = deg u`;
4. that cone is a positive multiple of `z ↦ zⁿ` for `n ≥ 0`, and of `z ↦ conj (z^|n|)` for
   `n < 0`, away from `0`.

Finally `z ↦ zᵏ` is proper of degree `k`, and `z ↦ conj (zᵏ)` of degree `-k`: the `k`-th roots of
unity are the preimages of the regular value `1`, with Jacobians `±|k ζ^(k-1)|²`
(`TauCeti.HomologicalOrientation.degree_eq_ncard_sub_ncard`).

## Main results

* `TauCeti.HomologicalOrientation.localDegree_eq_degree_toBasedLoop`: the local degree at `0` of a
  plane map without zeros outside a disc is the degree of its boundary direction loop.
* `TauCeti.HomologicalOrientation.localDegree_pow`,
  `TauCeti.HomologicalOrientation.localDegree_conj_pow`: `z ↦ zᵏ` and `z ↦ conj (zᵏ)` have local
  degrees `k` and `-k` at `0`.

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII, §4.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §6.
-/

public section

noncomputable section

open Complex ContinuousLinearMap Filter Set Topology Module
open scoped unitInterval ComplexConjugate

namespace TauCeti

namespace HomologicalOrientation

variable (o : HomologicalOrientation ℂ ℂ 2)

/-! ### Directions and cones -/

/-- The direction `z / ‖z‖` of a nonzero complex number, as a point of the circle, and `1` at
`0`. -/
private def dir (z : ℂ) : Circle :=
  ⟨if z = 0 then 1 else z / ‖z‖,
    mem_sphere_zero_iff_norm.2 (by split_ifs with h <;> simp [h])⟩

private theorem coe_dir_of_ne_zero {z : ℂ} (hz : z ≠ 0) : (dir z : ℂ) = z / ‖z‖ := by
  simp [dir, hz]

private theorem norm_mul_dir (z : ℂ) : (‖z‖ : ℂ) * dir z = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [coe_dir_of_ne_zero hz, mul_div_cancel₀ _ (by exact_mod_cast norm_ne_zero_iff.2 hz)]

private theorem continuousAt_dir {z : ℂ} (hz : z ≠ 0) : ContinuousAt dir z := by
  have h : ContinuousAt (fun w : ℂ ↦ w / (‖w‖ : ℂ)) z :=
    continuousAt_id.div (continuous_ofReal.comp continuous_norm).continuousAt
      (by exact_mod_cast norm_ne_zero_iff.2 hz)
  refine Topology.IsInducing.subtypeVal.continuousAt_iff.2 (h.congr ?_)
  filter_upwards [eventually_ne_nhds hz] with w hw
  exact (coe_dir_of_ne_zero hw).symm

/-- The cone `(x, z) ↦ ‖z‖ Φ(x, z / ‖z‖)` over a continuous family `Φ` of maps to the circle is
continuous, also at `z = 0`, where it vanishes. -/
private theorem continuous_norm_mul_dir {X : Type*} [TopologicalSpace X]
    {Φ : X × Circle → Circle} (hΦ : Continuous Φ) :
    Continuous fun p : X × ℂ ↦ (‖p.2‖ : ℂ) * Φ (p.1, dir p.2) := by
  refine continuous_iff_continuousAt.2 fun ⟨x, z⟩ ↦ ?_
  rcases eq_or_ne z 0 with rfl | hz
  · -- Near `z = 0` the cone has norm `‖z‖`.
    simp only [ContinuousAt, norm_zero, ofReal_zero, zero_mul]
    refine squeeze_zero_norm (a := fun p : X × ℂ ↦ ‖p.2‖) (fun p ↦ by simp) ?_
    exact continuous_snd.norm.tendsto' _ _ (by simp)
  · have hd : ContinuousAt (fun p : X × ℂ ↦ dir p.2) (x, z) :=
      (continuousAt_dir hz).comp (f := Prod.snd) (x := (x, z)) continuousAt_snd
    exact (continuous_ofReal.comp continuous_snd.norm).continuousAt.mul
      (continuous_subtype_val.continuousAt.comp (hΦ.continuousAt.comp
        (continuousAt_fst.prodMk hd)))

/-- The cone `z ↦ ‖z‖ u(z / ‖z‖)` over a map `u : S¹ → S¹`. -/
private def cone (u : C(Circle, Circle)) : C(ℂ, ℂ) where
  toFun z := ‖z‖ * u (dir z)
  continuous_toFun := (continuous_norm_mul_dir (X := Unit) (u.continuous.comp continuous_snd)).comp
    (f := fun z : ℂ ↦ ((), z)) (by fun_prop)

/-- The map `ζ ↦ ζⁿ` of the circle. -/
private def zpowMap (n : ℤ) : C(Circle, Circle) :=
  ⟨(· ^ n), continuous_zpow n⟩

private theorem zpowMap_apply (n : ℤ) (ζ : Circle) : zpowMap n ζ = ζ ^ n :=
  (rfl)

/-! ### Deformations with bounded zeros -/

/-- Two plane maps joined by a homotopy whose zeros stay in a bounded set have the same local degree
at `0`. -/
private theorem localDegree_eq_of_homotopy_of_norm_le {f₀ f₁ : C(ℂ, ℂ)} (H : f₀.Homotopy f₁)
    (R : ℝ) (hR : ∀ p : I × ℂ, H p = 0 → ‖p.2‖ ≤ R) :
    o.localDegree o finrank_real_complex f₀ 0 = o.localDegree o finrank_real_complex f₁ 0 :=
  o.localDegree_eq_of_homotopy_of_isCompact o _ finrank_real_complex H <|
    (isCompact_univ.prod (isCompact_closedBall (0 : ℂ) R)).of_isClosed_subset
      (isClosed_singleton.preimage H.continuous) fun p hp ↦
        ⟨mem_univ _, mem_closedBall_zero_iff.2 (hR p hp)⟩

/-- Two plane maps which outside the closed disc of radius `R` are nonzero and positive multiples of
each other have the same local degree at `0`: the straight-line homotopy between them has no zero
there. -/
private theorem localDegree_eq_of_eq_smul {f₀ f₁ : C(ℂ, ℂ)} (R : ℝ)
    (h : ∀ z, R < ‖z‖ → f₀ z ≠ 0 ∧ ∃ c : ℝ, 0 < c ∧ f₁ z = c • f₀ z) :
    o.localDegree o finrank_real_complex f₀ 0 = o.localDegree o finrank_real_complex f₁ 0 := by
  let H : f₀.Homotopy f₁ :=
    { toFun p := (1 - (p.1 : ℝ)) • f₀ p.2 + (p.1 : ℝ) • f₁ p.2
      continuous_toFun := by fun_prop
      map_zero_left := by simp
      map_one_left := by simp }
  refine o.localDegree_eq_of_homotopy_of_norm_le H R fun ⟨s, z⟩ hsz ↦ not_lt.1 fun hz ↦ ?_
  obtain ⟨h₀, c, hc, h₁⟩ := h z hz
  have hpos : 0 < 1 - (s : ℝ) + s * c := by
    rcases s.2.1.eq_or_lt with hs | hs
    · simp [← hs]
    · nlinarith [s.2.2, mul_pos hs hc]
  have hsum : (1 - (s : ℝ) + s * c) • f₀ z = 0 := by
    have : H (s, z) = (1 - (s : ℝ)) • f₀ z + (s : ℝ) • f₁ z := rfl
    rw [← hsz, this, h₁, smul_smul, ← add_smul]
  exact h₀ ((smul_eq_zero.1 hsum).resolve_left hpos.ne')

/-! ### The model maps `z ↦ zᵏ` and `z ↦ conj (zᵏ)` -/

/-- The map `z ↦ zᵏ` is proper for `k ≥ 1`. -/
private theorem isProperMap_pow {k : ℕ} (hk : k ≠ 0) : IsProperMap fun z : ℂ ↦ z ^ k := by
  simpa using (Polynomial.X ^ k : Polynomial ℂ).isProperMap_eval (by simp [Nat.pos_of_ne_zero hk])

/-- The `k`-th roots of unity in `ℂ` are `k` points. -/
private theorem ncard_pow_eq_one {k : ℕ} (hk : k ≠ 0) :
    ((fun z : ℂ ↦ z ^ k) ⁻¹' {1}).ncard = k := by
  have h : (fun z : ℂ ↦ z ^ k) ⁻¹' {1} = ↑(Polynomial.nthRootsFinset k (1 : ℂ)) := by
    ext z
    simp [Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hk)]
  rw [h, ncard_coe_finset, (isPrimitiveRoot_exp k hk).card_nthRootsFinset]

/-- **The local degree of `z ↦ zᵏ` at `0` is `k`.** -/
theorem localDegree_pow (k : ℕ) :
    o.localDegree o finrank_real_complex ⟨(· ^ k), continuous_pow k⟩ 0 = k := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact o.localDegree_eq_zero_of_notMem_range o _ finrank_real_complex _ (by simp)
  have hx (x : ℂ) (hx : x ∈ (fun z : ℂ ↦ z ^ k) ⁻¹' {1}) : x ≠ 0 := by
    rintro rfl
    simp [zero_pow hk] at hx
  have hdet (x : ℂ) (hx' : x ∈ (fun z : ℂ ↦ z ^ k) ⁻¹' {1}) :
      0 < ((smulRight (1 : ℂ →L[ℂ] ℂ) ((k : ℂ) * x ^ (k - 1))).restrictScalars ℝ).det := by
    rw [det_restrictScalars_smulRight_one]
    exact pow_pos (norm_pos_iff.2 (mul_ne_zero (by exact_mod_cast hk) (pow_ne_zero _ (hx x hx')))) 2
  rw [o.localDegree_eq_degree o _ finrank_real_complex (isProperMap_pow hk),
    o.degree_eq_ncard_sub_ncard finrank_real_complex (isProperMap_pow hk) (y := 1)
      (fun x _ ↦ (hasDerivAt_pow k x).hasFDerivAt.restrictScalars ℝ) fun x hx ↦ (hdet x hx).ne']
  simp only [ContinuousMap.coe_mk]
  rw [inter_eq_right.2 fun x hx ↦ hdet x hx]
  convert_to (((fun z : ℂ ↦ z ^ k) ⁻¹' {1}).ncard : ℤ) - ((∅ : Set ℂ).ncard : ℤ) = k using 3
  · refine congrArg ncard (eq_empty_of_forall_notMem fun x hx ↦ ?_)
    exact (hdet x hx.2).not_gt hx.1
  simpa using congrArg ((↑) : ℕ → ℤ) (ncard_pow_eq_one hk)

/-- Conjugation reverses orientation: composing with it negates the Jacobian. -/
private theorem det_conjCLE_comp (A : ℂ →L[ℝ] ℂ) :
    ((conjCLE : ℂ →L[ℝ] ℂ).comp A).det = -A.det := by
  have h : ((conjCLE : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = conjAe.toLinearEquiv.toLinearMap := rfl
  refine (LinearMap.det_comp ((conjCLE : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) (A : ℂ →ₗ[ℝ] ℂ)).trans ?_
  rw [h, det_conjAe, neg_one_mul, ContinuousLinearMap.det]

/-- **The local degree of `z ↦ conj (zᵏ)` at `0` is `-k`.** -/
theorem localDegree_conj_pow (k : ℕ) :
    o.localDegree o finrank_real_complex ⟨fun z ↦ conj (z ^ k), by fun_prop⟩ 0 = -k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hprop : IsProperMap fun z : ℂ ↦ conj (z ^ k) :=
    conjCLE.toHomeomorph.isProperMap.comp (isProperMap_pow hk)
  have hfib : (fun z : ℂ ↦ conj (z ^ k)) ⁻¹' {1} = (fun z : ℂ ↦ z ^ k) ⁻¹' {1} := by
    ext z
    rw [mem_preimage, mem_preimage, mem_singleton_iff, mem_singleton_iff,
      map_eq_one_iff _ (RingHom.injective _)]
  have hx (x : ℂ) (hx : x ∈ (fun z : ℂ ↦ z ^ k) ⁻¹' {1}) : x ≠ 0 := by
    rintro rfl
    simp [zero_pow hk] at hx
  have hdet (x : ℂ) (hx' : x ∈ (fun z : ℂ ↦ conj (z ^ k)) ⁻¹' {1}) :
      ((conjCLE : ℂ →L[ℝ] ℂ).comp
        ((smulRight (1 : ℂ →L[ℂ] ℂ) ((k : ℂ) * x ^ (k - 1))).restrictScalars ℝ)).det < 0 := by
    rw [det_conjCLE_comp, det_restrictScalars_smulRight_one, neg_lt_zero]
    exact pow_pos (norm_pos_iff.2
      (mul_ne_zero (by exact_mod_cast hk) (pow_ne_zero _ (hx x (hfib ▸ hx'))))) 2
  rw [o.localDegree_eq_degree o _ finrank_real_complex hprop,
    o.degree_eq_ncard_sub_ncard finrank_real_complex hprop (y := 1)
      (fun x _ ↦ conjCLE.hasFDerivAt.comp x
        ((hasDerivAt_pow k x).hasFDerivAt.restrictScalars ℝ)) fun x hx ↦ (hdet x hx).ne]
  simp only [ContinuousMap.coe_mk]
  convert_to ((∅ : Set ℂ).ncard : ℤ) - (((fun z : ℂ ↦ z ^ k) ⁻¹' {1}).ncard : ℤ) = -k using 3
  · refine congrArg ncard (eq_empty_of_forall_notMem fun x hx ↦ ?_)
    exact (hdet x hx.2).not_gt hx.1
  · rw [inter_eq_right.2 fun x hx ↦ hdet x hx, hfib]
  simpa using congrArg ((↑) : ℕ → ℤ) (ncard_pow_eq_one hk)

/-! ### The boundary winding number -/

/-- Outside the disc of radius `r`, where `f` has no zero, `f` deforms radially onto its values on
the boundary circle, and then to the cone over its boundary direction map `u`. -/
private theorem localDegree_eq_localDegree_cone {f : C(ℂ, ℂ)} {r : ℝ} (hr : 0 < r)
    (hf : ∀ z, r ≤ ‖z‖ → f z ≠ 0) {u : C(Circle, Circle)}
    (hu : ∀ ζ : Circle, (u ζ : ℂ) = f (r * ζ) / ‖f (r * ζ)‖) :
    o.localDegree o finrank_real_complex f 0 =
      o.localDegree o finrank_real_complex (cone u) 0 := by
  -- The rescalings `z ↦ μ(s, z) z` push the points outside the disc radially onto its boundary
  -- circle, while keeping them outside the open disc.
  let μ : I × ℂ → ℝ := fun p ↦ (max 1 (1 - (p.1 : ℝ) + p.1 * ‖p.2‖ / r))⁻¹
  have hμ : Continuous μ := (continuous_const.max (by fun_prop)).inv₀ fun p ↦
    (one_pos.trans_le (le_max_left _ _)).ne'
  let f₁ : C(ℂ, ℂ) := ⟨fun z ↦ f (μ (1, z) • z),
    f.continuous.comp ((hμ.comp (continuous_const.prodMk continuous_id)).smul continuous_id)⟩
  let H : f.Homotopy f₁ :=
    { toFun p := f (μ p • p.2)
      continuous_toFun := f.continuous.comp (hμ.smul continuous_snd)
      map_zero_left z := by simp [μ]
      map_one_left z := rfl }
  have hμ₁ (z : ℂ) (hz : r < ‖z‖) : f₁ z = f (r * dir z) := by
    have h1 : 1 ≤ ‖z‖ / r := (one_le_div hr).2 hz.le
    have hz0 : z ≠ 0 := norm_pos_iff.1 (hr.trans hz)
    simp only [f₁, ContinuousMap.coe_mk, μ, Set.Icc.coe_one, sub_self, zero_add, one_mul,
      max_eq_right h1, inv_div, coe_dir_of_ne_zero hz0, Complex.real_smul]
    congr 1
    push_cast
    ring
  -- Along `H` the zeros of `f` stay in the closed disc.
  refine (o.localDegree_eq_of_homotopy_of_norm_le H r fun ⟨s, z⟩ hsz ↦ not_lt.1 fun hz ↦ ?_).trans
    (o.localDegree_eq_of_eq_smul r fun z hz ↦ ?_)
  · -- `H (s, z) = f (μ(s, z) z)` by definition.
    have hsz' : f (μ (s, z) • z) = 0 := hsz
    refine hf _ ?_ hsz'
    have h1 : 1 ≤ ‖z‖ / r := (one_le_div hr).2 hz.le
    have hst : 0 ≤ (s : ℝ) * (‖z‖ / r - 1) := mul_nonneg s.2.1 (by linarith)
    have hs : (s : ℝ) * ‖z‖ / r = s * (‖z‖ / r) := mul_div_assoc _ _ _
    have ht : 1 ≤ 1 - (s : ℝ) + s * ‖z‖ / r := by rw [hs]; linarith
    have htpos : 0 < 1 - (s : ℝ) + s * ‖z‖ / r := by linarith
    simp only [μ, max_eq_right ht, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htpos,
      inv_mul_eq_div]
    have hrt : r * (1 - (s : ℝ) + s * ‖z‖ / r) = (1 - s) * r + s * ‖z‖ := by
      field_simp
    rw [le_div_iff₀ htpos, hrt]
    nlinarith [s.2.2, hz.le]
  · -- Outside the disc, `f₁` is a positive multiple of the cone over `u`.
    have hne : f (r * dir z) ≠ 0 := hf _ (by simp [abs_of_pos hr])
    refine ⟨hμ₁ z hz ▸ hne, ‖z‖ / ‖f (r * dir z)‖, div_pos (hr.trans hz) (norm_pos_iff.2 hne), ?_⟩
    rw [hμ₁ z hz, Complex.real_smul]
    simp only [cone, ContinuousMap.coe_mk, hu]
    push_cast
    ring

/-- Cones over joined maps `S¹ → S¹` are joined through cones, which vanish only at `0`, so they
have the same local degree at `0`. -/
private theorem localDegree_cone_eq_of_joined {u v : C(Circle, Circle)} (h : Joined u v) :
    o.localDegree o finrank_real_complex (cone u) 0 =
      o.localDegree o finrank_real_complex (cone v) 0 := by
  let Γ := h.somePath
  let H : (cone u).Homotopy (cone v) :=
    { toFun p := ‖p.2‖ * Γ p.1 (dir p.2)
      continuous_toFun := continuous_norm_mul_dir (Φ := fun q : I × Circle ↦ Γ q.1 q.2)
        (continuous_eval.comp (Γ.continuous.prodMap continuous_id))
      map_zero_left z := by simp [cone]
      map_one_left z := by simp [cone] }
  refine o.localDegree_eq_of_homotopy_of_norm_le H 0 fun ⟨s, z⟩ hsz ↦ ?_
  -- `H (s, z) = ‖z‖ Γ(s)(z / ‖z‖)` by definition.
  have hsz' : (‖z‖ : ℂ) * Γ s (dir z) = 0 := hsz
  simpa using hsz'

/-- The cone over `ζ ↦ ζⁿ` has local degree `n` at `0`: away from `0` it is a positive multiple of
`z ↦ zⁿ` for `n ≥ 0`, and of `z ↦ conj (z^|n|)` for `n < 0`. -/
private theorem localDegree_cone_zpowMap (n : ℤ) :
    o.localDegree o finrank_real_complex (cone (zpowMap n)) 0 = n := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · refine (o.localDegree_eq_of_eq_smul 0 fun z hz ↦ ?_).trans (localDegree_pow o k)
    have hz0 : z ≠ 0 := norm_pos_iff.1 hz
    refine ⟨by simp [cone, zpowMap_apply, hz0], ‖z‖ ^ k / ‖z‖, by positivity, ?_⟩
    simp only [cone, zpowMap_apply, ContinuousMap.coe_mk, zpow_natCast, Circle.coe_pow,
      Complex.real_smul]
    conv_lhs => rw [← norm_mul_dir z]
    have hn : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 hz.ne'
    rw [mul_pow]
    push_cast
    field_simp
  · refine (o.localDegree_eq_of_eq_smul 0 fun z hz ↦ ?_).trans (localDegree_conj_pow o k)
    have hz0 : z ≠ 0 := norm_pos_iff.1 hz
    refine ⟨by simp [cone, zpowMap_apply, hz0], ‖z‖ ^ k / ‖z‖, by positivity, ?_⟩
    simp only [cone, zpowMap_apply, ContinuousMap.coe_mk, zpow_neg, zpow_natCast,
      Circle.coe_inv_eq_conj, Circle.coe_pow, Complex.real_smul]
    conv_lhs => rw [← norm_mul_dir z]
    rw [mul_pow, map_mul, ← ofReal_pow, conj_ofReal]
    have hn : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 hz.ne'
    push_cast
    field_simp

/-- **The local degree at `0` of a plane map is the degree of its boundary loop.** Let `f : ℂ → ℂ`
be continuous with no zero outside the open disc of radius `r > 0`, and let `u : S¹ → S¹` be its
boundary direction map `ζ ↦ f(rζ) / ‖f(rζ)‖`. Then the local degree of `f` at `0`, for any
orientation of `ℂ` used on source and target, is the degree of `u`: the number of times `f` winds
around `0` along the circle of radius `r`. -/
theorem localDegree_eq_degree_toBasedLoop {f : C(ℂ, ℂ)} {r : ℝ} (hr : 0 < r)
    (hf : ∀ z, r ≤ ‖z‖ → f z ≠ 0) {u : C(Circle, Circle)}
    (hu : ∀ ζ : Circle, (u ζ : ℂ) = f (r * ζ) / ‖f (r * ζ)‖) :
    o.localDegree o finrank_real_complex f 0 = Circle.degree u.toBasedLoop := by
  rw [o.localDegree_eq_localDegree_cone hr hf hu,
    o.localDegree_cone_eq_of_joined (v := zpowMap (Circle.degree u.toBasedLoop))
      (Circle.joined_iff_degree_toBasedLoop_eq.2 (Circle.degree_toBasedLoop_zpow _).symm),
    localDegree_cone_zpowMap]

end HomologicalOrientation

end TauCeti
