/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Constancy
public import TauCeti.Geometry.Symplectic.AlmostComplex
import TauCeti.LinearAlgebra.Complex.Module
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import TauCeti.Analysis.Normed.Module.InvariantConst
import TauCeti.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete

/-!
# Finite isotropy of nonconstant pseudoholomorphic spheres with a special point

A bubble in Gromov compactness, or in Gromov–Floer compactness for Floer cylinders and pairs of
pants, is a pseudoholomorphic sphere attached to the rest of the limit configuration at one or two
special points. A sphere with fewer than three special points is not a stable pointed curve: the
Möbius transformations fixing its special points form a positive-dimensional group. A limit
configuration is nevertheless stable when every such component is nonconstant, because a
nonconstant map is fixed by only finitely many of these reparametrizations. This file proves that
statement for spheres with a special point at `∞`.

Write the sphere as `OnePoint ℂ` with the special point at `∞`. The Möbius transformations fixing
`∞` are the complex affine automorphisms `z ↦ a z + b` of `ℂ`, the group `ℂ ≃ᵃ[ℂ] ℂ`, and a map
of the sphere is a map `u : ℂ → X` with a limit `y` at infinity. Its *isotropy* is the set of
affine automorphisms `f` with `u ∘ f = u`. A second special point at `0` cuts the isotropy down to
the `f` with `f 0 = 0`, a subset, so the finiteness below holds for it too.

* **The topological statement** (`TauCeti.finite_setOf_comp_eq_iff`). For a continuous map
  `u : ℂ → X` to a Hausdorff space with a limit at infinity, the isotropy is finite exactly when
  `u` is not invariant under all rotations `z ↦ z₀ + e^{iθ} (z - z₀)` about any centre `z₀`.
  A translation in the isotropy, or a scaling with `|a| ≠ 1`, forces `u` to be constant
  (`TauCeti.apply_eq_of_forall_apply_add_eq`, `TauCeti.apply_eq_of_forall_apply_add_smul_sub_eq`).
  So, unless `u` is rotation invariant, the isotropy consists of rotations; two of them about
  different centres would have a nontrivial translation as commutator, so they share one centre.
  Their angles form a closed proper subgroup of `ℝ` containing `2π`, which is cyclic
  (`AddSubgroup.dense_or_isCyclic`), so the rotation factors are roots of unity of a fixed order.
* **Rotation-invariant pseudoholomorphic maps are constant**
  (`TauCeti.apply_eq_of_forall_apply_add_exp_mul_I_mul_sub_eq`). This holds for a differentiable
  map `u` from `ℂ` to a manifold `M` solving the Cauchy–Riemann equation `∂ₜu = J(u) ∂ₛu` for
  pointwise complex structures `J(x)` on the tangent spaces of `M`, with no regularity or taming
  assumed of `J`. Invariance kills the angular derivative `du(i (z - z₀))` at every `z ≠ z₀`, the
  Cauchy–Riemann equation then kills the radial derivative, and invariance under the point
  reflection about `z₀` kills `du` at `z₀`.
* **Map stability** (`TauCeti.finite_setOf_comp_eq_iff_exists_ne`). Combining the two, a
  pseudoholomorphic sphere with a special point at `∞` has finite isotropy exactly when it is
  nonconstant. Constant spheres with one or two special points have infinite isotropy; they are
  the components that stability excludes.

The isotropy of a nonconstant sphere can be nontrivial: `z ↦ z²` is fixed by `z ↦ -z`. The
argument needs no unique continuation, no somewhere injectivity and no energy bound, only
continuity at `∞`, pointwise differentiability and the Cauchy–Riemann equation.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 5.1,
  on stable maps, and Chapter 4, on bubbling.
* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Section 9.2, on the finiteness of the
  automorphism groups of stable maps.
-/

public section

noncomputable section

open Filter Set Topology
open scoped Manifold

namespace TauCeti

/-! ### Maps of the sphere fixing `∞` -/

section Topological

variable {X : Type*} [TopologicalSpace X] {u : ℂ → X}

omit [TopologicalSpace X] in
/-- A constant map is invariant under all rotations about every point. -/
private theorem forall_apply_rotation_eq_of_forall_eq {c : X} (h : ∀ z, u z = c) (z₀ : ℂ) :
    ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z :=
  fun _ _ ↦ by rw [h, h]

variable [T2Space X]

/-- Unless `u` is rotation invariant, an element of its isotropy has a linear coefficient of norm
`1`, and it is the identity if that coefficient is `1`. -/
private theorem norm_linear_one_eq_one_of_forall_apply_eq (hu : Continuous u) {y : X}
    (hy : Tendsto u (cocompact ℂ) (𝓝 y))
    (hrot : ∀ z₀ : ℂ, ¬ ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z)
    {f : ℂ ≃ᵃ[ℂ] ℂ} (hf : ∀ z, u (f z) = u z) :
    ‖f.linear 1‖ = 1 ∧ (f.linear 1 = 1 → f 0 = 0) := by
  set a := f.linear 1
  set b := f 0
  have hfz : ∀ z, f z = a * z + b := f.apply_eq_linear_one_mul_add
  refine ⟨?_, fun ha ↦ by_contra fun hb ↦ hrot 0 <| forall_apply_rotation_eq_of_forall_eq
    (apply_eq_of_forall_apply_add_eq hb (fun z ↦ by simpa [hfz, ha] using hf z)
      (by rwa [Metric.cobounded_eq_cocompact])) 0⟩
  -- A scaling factor of norm different from `1` contracts towards the fixed point, possibly after
  -- inversion, and makes `u` constant.
  have hcontr : ∀ {c r : ℂ}, ‖r‖ < 1 → (∀ z, u (c + r * (z - c)) = u z) → False :=
    fun hr h ↦ hrot 0 <| forall_apply_rotation_eq_of_forall_eq
      (apply_eq_of_forall_apply_add_smul_sub_eq hr (fun z ↦ by simpa using h z) hu.continuousAt) 0
  rcases lt_trichotomy ‖a‖ 1 with ha | ha | ha
  · have ha1 : 1 - a ≠ 0 := sub_ne_zero.2 fun h ↦ by simp [← h] at ha
    refine (hcontr (c := b / (1 - a)) ha fun z ↦ ?_).elim
    rw [← hf z, hfz]
    congr 1
    field_simp
    ring
  · exact ha
  · have ha0 : a ≠ 0 := f.linear_one_ne_zero
    have ha1 : 1 - a ≠ 0 := sub_ne_zero.2 fun h ↦ by simp [← h] at ha
    refine (hcontr (c := b / (1 - a)) (r := a⁻¹) ?_ fun z ↦ ?_).elim
    · rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ ha
    · rw [← hf, hfz]
      congr 1
      field_simp
      ring

/-- Unless `u` is rotation invariant, every element of its isotropy commutes with a given
nontrivial one, so it is a rotation about the same centre. -/
private theorem apply_eq_add_linear_one_mul_sub_of_forall_apply_eq {y : X}
    (hy : Tendsto u (cocompact ℂ) (𝓝 y))
    (hrot : ∀ z₀ : ℂ, ¬ ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z)
    {f g : ℂ ≃ᵃ[ℂ] ℂ} (hf : ∀ z, u (f z) = u z) (hg : ∀ z, u (g z) = u z)
    (hf1 : f.linear 1 ≠ 1) (z : ℂ) :
    g z = f 0 / (1 - f.linear 1) + g.linear 1 * (z - f 0 / (1 - f.linear 1)) := by
  set a := f.linear 1
  set b := f 0
  set c := g.linear 1
  set d := g 0
  have hfz : ∀ z, f z = a * z + b := f.apply_eq_linear_one_mul_add
  have hgz : ∀ z, g z = c * z + d := g.apply_eq_linear_one_mul_add
  have ha0 : a ≠ 0 := f.linear_one_ne_zero
  have hc0 : c ≠ 0 := g.linear_one_ne_zero
  have ha1 : 1 - a ≠ 0 := sub_ne_zero.2 (Ne.symm hf1)
  -- The commutator of `f` and `g` is the translation by `t`; it lies in the isotropy.
  set t := a * d + b - c * b - d
  have ht : t = 0 := by
    by_contra ht
    refine hrot 0 <| forall_apply_rotation_eq_of_forall_eq
      (apply_eq_of_forall_apply_add_eq ht (fun w ↦ ?_) (by rwa [Metric.cobounded_eq_cocompact])) 0
    obtain ⟨x, hx⟩ : ∃ x, a * c * x = w - c * b - d :=
      ⟨(w - c * b - d) / (a * c), by field_simp⟩
    have hfg : f (g x) = w + t := by
      rw [hgz, hfz]
      linear_combination hx
    have hgf : g (f x) = w := by
      rw [hfz, hgz]
      linear_combination hx
    rw [← hfg, hf, hg, ← hf x, ← hg (f x), hgf]
  have hd : d = b * (1 - c) / (1 - a) := by
    rw [eq_div_iff ha1]
    linear_combination -ht
  rw [hgz, hd]
  field_simp
  ring

omit [TopologicalSpace X] [T2Space X] in
/-- The rotations about a centre of invariance form an infinite family in the isotropy. -/
private theorem infinite_setOf_comp_eq_of_forall {z₀ : ℂ}
    (hrot : ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z) :
    {f : ℂ ≃ᵃ[ℂ] ℂ | u ∘ f = u}.Infinite := by
  refine Set.infinite_of_injOn_mapsTo (f := fun θ : ℝ ↦ AffineEquiv.homothetyUnitsMulHom z₀
    (Units.mk0 (Complex.exp (θ * Complex.I)) (Complex.exp_ne_zero _))) (s := Ioo 0 1)
    (fun θ hθ θ' hθ' h ↦ ?_) (fun θ _ ↦ ?_) (Ioo_infinite (by norm_num))
  · have h1 := congrArg (fun f : ℂ ≃ᵃ[ℂ] ℂ ↦ f (z₀ + 1)) h
    simp only [AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply,
      Units.val_mk0, vsub_eq_sub, vadd_eq_add, add_sub_cancel_left, smul_eq_mul, mul_one,
      add_left_inj] at h1
    have harg : ∀ φ ∈ Ioo (0 : ℝ) 1, Complex.arg (Complex.exp (φ * Complex.I)) = φ := by
      intro φ hφ
      rw [Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I]
      constructor <;> linarith [hφ.1, hφ.2, Real.two_le_pi]
    rw [← harg θ hθ, ← harg θ' hθ', h1]
  · funext z
    simp only [Function.comp_apply, AffineEquiv.coe_homothetyUnitsMulHom_apply,
      AffineMap.homothety_apply, Units.val_mk0, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    rw [add_comm, hrot]

omit [TopologicalSpace X] [T2Space X] in
/-- The angles `θ` of the rotations about `z₀` that fix `u`, an additive subgroup of `ℝ`. -/
private def rotationAngles (u : ℂ → X) (z₀ : ℂ) : AddSubgroup ℝ where
  carrier := {θ | ∀ z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z}
  zero_mem' := fun z ↦ by simp
  add_mem' := fun {θ φ} hθ hφ z ↦ by
    rw [← hφ z, ← hθ (z₀ + Complex.exp (φ * Complex.I) * (z - z₀))]
    congr 1
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  neg_mem' := fun {θ} hθ z ↦ by
    rw [← hθ (z₀ + Complex.exp (↑(-θ) * Complex.I) * (z - z₀))]
    congr 1
    rw [add_sub_cancel_left, ← mul_assoc, ← Complex.exp_add]
    push_cast
    simp

omit [TopologicalSpace X] [T2Space X] in
/-- The defining property of the rotation angles. -/
private theorem mem_rotationAngles {z₀ : ℂ} {θ : ℝ} :
    θ ∈ rotationAngles u z₀ ↔ ∀ z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z :=
  Iff.rfl

/-- The rotation angles of a continuous map form a closed set. -/
private theorem isClosed_rotationAngles (hu : Continuous u) (z₀ : ℂ) :
    IsClosed (rotationAngles u z₀ : Set ℝ) := by
  have : (rotationAngles u z₀ : Set ℝ) =
      ⋂ z, {θ : ℝ | u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z} := by
    ext θ
    simp [mem_rotationAngles]
  rw [this]
  exact isClosed_iInter fun z ↦ isClosed_eq (hu.comp (by fun_prop)) continuous_const

/-- Unless a continuous map is invariant under all rotations about `z₀`, the factors `c` of the
rotations `z ↦ z₀ + c (z - z₀)` fixing it are roots of unity of a common order: their angles form
a closed proper subgroup of `ℝ`, which is cyclic and contains `2π`. -/
private theorem exists_pos_forall_pow_eq_one (hu : Continuous u) {z₀ : ℂ}
    (hrot : ¬ ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z) :
    ∃ N : ℕ, 0 < N ∧ ∀ c : ℂ, ‖c‖ = 1 → (∀ z, u (z₀ + c * (z - z₀)) = u z) → c ^ N = 1 := by
  set Θ := rotationAngles u z₀
  obtain ⟨g, hg⟩ : ∃ g : Θ, Function.Surjective (· • g : ℤ → Θ) := by
    rcases Θ.dense_or_isCyclic with hd | hc
    · refine (hrot fun θ ↦ mem_rotationAngles.1 ?_).elim
      rw [← SetLike.mem_coe, ← (isClosed_rotationAngles hu z₀).closure_eq, hd.closure_eq]
      trivial
    · exact hc.exists_zsmul_surjective
  have h2π : 2 * Real.pi ∈ Θ := mem_rotationAngles.2 fun z ↦ by
    push_cast
    rw [Complex.exp_two_pi_mul_I]
    simp
  obtain ⟨k, hk⟩ := hg ⟨2 * Real.pi, h2π⟩
  have hk' : (k : ℂ) * (g : ℝ) = 2 * Real.pi := by
    exact_mod_cast (by simpa [zsmul_eq_mul] using congrArg Subtype.val hk : (k : ℝ) * g = _)
  refine ⟨k.natAbs, Int.natAbs_pos.2 fun hk0 ↦ by simp [hk0, Real.pi_ne_zero] at hk', ?_⟩
  intro c hc hcu
  have hexp : Complex.exp (Complex.arg c * Complex.I) = c := by
    simpa [hc] using Complex.norm_mul_exp_arg_mul_I c
  obtain ⟨m, hm⟩ := hg ⟨_, mem_rotationAngles.2 fun z ↦ by rw [hexp, hcu]⟩
  have hm' : (m : ℝ) * g = Complex.arg c := by simpa [zsmul_eq_mul] using congrArg Subtype.val hm
  -- `c ^ k = exp (m k g i) = exp (2π m i) = 1`.
  have hck : c ^ k = 1 := by
    rw [← hexp, ← Complex.exp_int_mul, ← hm']
    push_cast
    rw [show (k : ℂ) * ((m : ℂ) * (g : ℝ) * Complex.I) = m * (2 * Real.pi * Complex.I) by
      linear_combination ((m : ℂ) * Complex.I) * hk']
    exact Complex.exp_int_mul_two_pi_mul_I m
  rcases Int.natAbs_eq k with hk2 | hk2
  · rwa [hk2, zpow_natCast] at hck
  · rwa [hk2, zpow_neg, zpow_natCast, inv_eq_one] at hck

/-- **Finite isotropy of maps of the sphere fixing `∞`.** Let `u : ℂ → X` be a continuous map to a
Hausdorff space with a limit at infinity, a map of the sphere `OnePoint ℂ`. Its isotropy, the set
of complex affine automorphisms `f` of `ℂ` with `u ∘ f = u`, is finite exactly when `u` is not
invariant under all rotations `z ↦ z₀ + e^{iθ} (z - z₀)` about any point `z₀`. -/
theorem finite_setOf_comp_eq_iff (hu : Continuous u) {y : X}
    (hy : Tendsto u (cocompact ℂ) (𝓝 y)) :
    {f : ℂ ≃ᵃ[ℂ] ℂ | u ∘ f = u}.Finite ↔
      ∀ z₀ : ℂ, ∃ (θ : ℝ) (z : ℂ), u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) ≠ u z := by
  refine ⟨fun hfin z₀ ↦ ?_, fun hrot' ↦ ?_⟩
  · by_contra! hrot
    exact infinite_setOf_comp_eq_of_forall hrot hfin
  have hrot : ∀ z₀ : ℂ,
      ¬ ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z := by
    simpa only [not_forall] using hrot'
  set G := {f : ℂ ≃ᵃ[ℂ] ℂ | u ∘ f = u}
  have hG : ∀ f ∈ G, ∀ z, u (f z) = u z := fun f hf z ↦ congrFun hf z
  by_cases htriv : ∀ f ∈ G, f.linear 1 = 1
  · -- Only the identity has linear coefficient `1`.
    refine (Set.finite_singleton (AffineEquiv.refl ℂ ℂ)).subset fun f hf ↦ ?_
    have h0 := (norm_linear_one_eq_one_of_forall_apply_eq hu hy hrot (hG f hf)).2 (htriv f hf)
    refine AffineEquiv.ext fun z ↦ ?_
    rw [AffineEquiv.apply_eq_linear_one_mul_add, htriv f hf, h0]
    simp
  -- Otherwise every element is a rotation about the centre `z₀` of a nontrivial one, and is
  -- determined by its rotation factor, a root of unity of a fixed order.
  push Not at htriv
  obtain ⟨f₀, hf₀, ha₀⟩ := htriv
  set z₀ := f₀ 0 / (1 - f₀.linear 1)
  have hcenter : ∀ g ∈ G, ∀ z, g z = z₀ + g.linear 1 * (z - z₀) := fun g hg ↦
    apply_eq_add_linear_one_mul_sub_of_forall_apply_eq hy hrot (hG f₀ hf₀) (hG g hg) ha₀
  obtain ⟨N, hN, hroot⟩ := exists_pos_forall_pow_eq_one hu (hrot z₀)
  refine Set.Finite.of_injOn (f := fun f : ℂ ≃ᵃ[ℂ] ℂ ↦ f.linear 1)
    (t := ((Polynomial.nthRoots N (1 : ℂ)).toFinset : Set ℂ)) (fun f hf ↦ ?_)
    (fun f hf f' hf' h ↦ ?_) (Finset.finite_toSet _)
  · simpa [Polynomial.mem_nthRoots hN] using
      hroot _ (norm_linear_one_eq_one_of_forall_apply_eq hu hy hrot (hG f hf)).1
        fun z ↦ by rw [← hcenter f hf, hG f hf]
  · exact AffineEquiv.ext fun z ↦ by
      rw [hcenter f hf, hcenter f' hf']
      simp only at h
      rw [h]

end Topological

/-! ### Rotation-invariant pseudoholomorphic maps -/

section Holomorphic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {J : (x : M) → AlmostComplexStructure (TangentSpace I x)} {u : ℂ → M}

/-- A map invariant under the rotations about `z₀` has zero differential at `z₀`: the rotation by
`π` is the point reflection `z ↦ 2 z₀ - z`, so `du = -du` there. -/
private theorem mfderiv_eq_zero_of_forall_apply_rotation_eq (hu : MDifferentiable 𝓘(ℝ, ℂ) I u)
    {z₀ : ℂ} (hrot : ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z) :
    mfderiv 𝓘(ℝ, ℂ) I u z₀ = 0 := by
  set ρ : ℂ → ℂ := fun z ↦ z₀ - (z - z₀)
  have hρ : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ρ z₀ (-ContinuousLinearMap.id ℝ ℂ) :=
    hasMFDerivAt_iff_hasFDerivAt.2 (((hasFDerivAt_id z₀).sub_const z₀).const_sub z₀)
  have hρz : ρ z₀ = z₀ := by simp [ρ]
  have huρ : u ∘ ρ = u := funext fun z ↦ by
    simpa [ρ, Complex.exp_pi_mul_I, sub_eq_add_neg] using hrot Real.pi z
  ext v
  have hv := mfderiv_comp_apply_of_eq z₀ (hu z₀) hρ.mdifferentiableAt hρz v
  rw [huρ, hρ.mfderiv] at hv
  -- The equation `du(v) = -du(v)` is read in the model space `E` of the tangent spaces.
  have hv' : @Eq E (mfderiv 𝓘(ℝ, ℂ) I u z₀ v) (-mfderiv 𝓘(ℝ, ℂ) I u z₀ v) := by
    rw [← map_neg]
    exact hv
  have h2 : (2 : ℝ) • (mfderiv 𝓘(ℝ, ℂ) I u z₀ v : E) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hv']
    exact neg_add_cancel _
  rw [zero_apply]
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- Along a map invariant under the rotations about `z₀`, the angular derivative
`du(i (x - z₀))` vanishes. -/
private theorem mfderiv_I_mul_sub_eq_zero (hu : MDifferentiable 𝓘(ℝ, ℂ) I u) {z₀ : ℂ}
    (hrot : ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z) (x : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) I u x (Complex.I * (x - z₀)) = 0 := by
  set γ : ℝ → ℂ := fun θ ↦ z₀ + Complex.exp (θ * Complex.I) * (x - z₀)
  have hγ' : HasDerivAt γ (Complex.I * (x - z₀)) 0 := by
    have h := HasDerivAt.comp_ofReal (z := 0)
      (((HasDerivAt.cexp ((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const Complex.I)).mul_const
        (x - z₀)).const_add z₀)
    convert h using 1 <;> simp [γ]
  have hγ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (Complex.I * (x - z₀))) :=
    hasMFDerivAt_iff_hasFDerivAt.2 hγ'.hasFDerivAt
  have hγ0 : γ 0 = x := by simp [γ]
  have h1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ) = Complex.I * (x - z₀) := by
    rw [hγ.mfderiv]
    exact one_smul ℝ _
  have huγ : u ∘ γ = fun _ ↦ u x := funext fun θ ↦ hrot θ x
  have h := mfderiv_comp_apply_of_eq 0 (hu x) hγ.mdifferentiableAt hγ0 (1 : ℝ)
  rw [huγ, mfderiv_const, h1] at h
  exact h.symm

/-- **Rotation-invariant pseudoholomorphic maps are constant.** Let `u : ℂ → M` be a
differentiable map to a manifold solving the Cauchy–Riemann equation `du(i) = J(u) du(1)` for
pointwise complex structures `J` on the tangent spaces of `M`. If `u` is invariant under all
rotations about a point `z₀`, then `u` is constant. -/
theorem apply_eq_of_forall_apply_add_exp_mul_I_mul_sub_eq [IsManifold I 1 M]
    (hu : MDifferentiable 𝓘(ℝ, ℂ) I u)
    (hJ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z Complex.I = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    {z₀ : ℂ} (hrot : ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z)
    (z w : ℂ) : u z = u w := by
  refine hu.apply_eq_of_mfderiv_eq_zero (fun x ↦ ?_) z w
  rcases eq_or_ne x z₀ with rfl | hx
  · exact mfderiv_eq_zero_of_forall_apply_rotation_eq hu hrot
  · -- Away from the centre, the angular derivative vanishes, and so does the radial one, by the
    -- Cauchy–Riemann equation.
    have h0 := LinearMap.eq_zero_of_apply_I_eq_of_apply_eq_zero
      (mfderiv 𝓘(ℝ, ℂ) I u x : ℂ →L[ℝ] TangentSpace I (u x)).toLinearMap (hJ x)
      (J (u x)).apply_apply (mul_ne_zero Complex.I_ne_zero (sub_ne_zero.2 hx))
      (mfderiv_I_mul_sub_eq_zero hu hrot x)
    ext v
    rw [zero_apply]
    exact (LinearMap.congr_fun h0 v).trans (LinearMap.zero_apply v)

/-- **Map stability of pseudoholomorphic spheres with a special point.** Let `u : ℂ → M` be a
differentiable map to a Hausdorff manifold solving the Cauchy–Riemann equation
`du(i) = J(u) du(1)` for pointwise complex structures `J`, with a limit at infinity, so that it is
a pseudoholomorphic sphere with a special point at `∞`. Its isotropy, the set of complex affine
automorphisms `f` of `ℂ` with `u ∘ f = u`, is finite exactly when `u` is nonconstant. -/
theorem finite_setOf_comp_eq_iff_exists_ne [IsManifold I 1 M] [T2Space M]
    (hu : MDifferentiable 𝓘(ℝ, ℂ) I u)
    (hJ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z Complex.I = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    {y : M} (hy : Tendsto u (cocompact ℂ) (𝓝 y)) :
    {f : ℂ ≃ᵃ[ℂ] ℂ | u ∘ f = u}.Finite ↔ ∃ z w, u z ≠ u w := by
  rw [finite_setOf_comp_eq_iff hu.continuous hy]
  constructor
  · intro h
    obtain ⟨θ, z, hz⟩ := h 0
    exact ⟨_, _, hz⟩
  · rintro ⟨z, w, hzw⟩ z₀
    by_contra! hrot
    exact hzw (apply_eq_of_forall_apply_add_exp_mul_I_mul_sub_eq hu hJ hrot z w)

end Holomorphic

end TauCeti
