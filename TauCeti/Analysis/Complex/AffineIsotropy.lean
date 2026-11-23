/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import TauCeti.Analysis.Normed.Module.InvariantConst
import TauCeti.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete

/-!
# Finite isotropy of maps of the sphere fixing `∞`

Write the Riemann sphere as `OnePoint ℂ`. The Möbius transformations fixing `∞` are the complex
affine automorphisms `z ↦ a z + b` of `ℂ`, the group `ℂ ≃ᵃ[ℂ] ℂ`, and a continuous map of the
sphere is a continuous map `u : ℂ → X` with a limit `y` at infinity.
Its *isotropy* is the set of affine automorphisms `f` with `u ∘ f = u`.

The main result, `Continuous.finite_setOf_comp_eq_iff`, says that for a continuous map `u : ℂ → X`
to a Hausdorff space with a limit at infinity, the isotropy is finite exactly when `u` is not
invariant under all rotations `z ↦ z₀ + e^{iθ} (z - z₀)` about any centre `z₀`.

A translation in the isotropy, or a scaling with `|a| ≠ 1`, forces `u` to be constant
(`Function.Periodic.apply_eq_of_tendsto`, `TauCeti.apply_eq_of_forall_apply_add_smul_sub_eq`).
So, unless `u` is rotation invariant, the isotropy consists of rotations; two of them about
different centres would have a nontrivial translation as commutator, so they share one centre.
Their angles form a closed proper subgroup of `ℝ` containing `2π`, which is cyclic
(`AddSubgroup.dense_or_isCyclic`), so the rotation factors are roots of unity of a fixed order.

No regularity beyond continuity is used. For pseudoholomorphic spheres, where rotation invariance
forces constancy, see `TauCeti.Geometry.Symplectic.JHolomorphic.Isotropy`.
-/

public section

noncomputable section

open Filter Set Topology

open scoped commutatorElement

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {u : ℂ → X}

omit [TopologicalSpace X] in
/-- A constant map is invariant under all rotations about every point. -/
private theorem forall_apply_rotation_eq_of_forall_eq {c : X} (h : ∀ z, u z = c) (z₀ : ℂ) :
    ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z :=
  fun _ _ ↦ by rw [h, h]

variable [T2Space X]

/-- Unless `u` is rotation invariant, its isotropy contains no nonzero translation. -/
private theorem eq_zero_of_forall_apply_add_eq {y : X} (hy : Tendsto u (cocompact ℂ) (𝓝 y))
    (hrot : ∀ z₀ : ℂ, ¬ ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z)
    {t : ℂ} (ht : ∀ w, u (t + w) = u w) : t = 0 :=
  by_contra fun ht0 ↦ hrot 0 <| forall_apply_rotation_eq_of_forall_eq
    (Function.Periodic.apply_eq_of_tendsto (fun w ↦ by rw [add_comm, ht]) ht0
      (by rwa [Metric.cobounded_eq_cocompact])) 0

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
  refine ⟨?_, fun ha ↦ eq_zero_of_forall_apply_add_eq hy hrot fun w ↦ by
    rw [add_comm, ← hf w, hfz, ha, one_mul]⟩
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
  by_cases hg1 : g.linear 1 = 1
  · have hg0 : g 0 = 0 := eq_zero_of_forall_apply_add_eq hy hrot fun w ↦ by
      have := hg w
      rwa [g.apply_eq_linear_one_mul_add w, hg1, one_mul, add_comm] at this
    rw [g.apply_eq_linear_one_mul_add, hg1, hg0]
    ring
  have hinv : ∀ h : ℂ ≃ᵃ[ℂ] ℂ, (∀ w, u (h w) = u w) → ∀ w, u (h⁻¹ w) = u w :=
    fun h hh w ↦ by rw [← hh, AffineEquiv.inv_def, AffineEquiv.apply_symm_apply]
  -- The commutator of the homotheties `f` and `g` is a translation in the isotropy, so it is
  -- trivial and they have the same centre.
  have hcomm : ∀ w, u (⁅f, g⁆ w) = u w := fun w ↦ by
    simp only [commutatorElement_def, AffineEquiv.coe_mul, Function.comp_apply, hf, hg,
      hinv f hf, hinv g hg]
  -- `f` and `g` are homotheties about their fixed points.
  have hgz := congrArg (fun h : ℂ ≃ᵃ[ℂ] ℂ ↦ h z)
    (g.eq_homothetyUnitsMulHom_of_linear_one_ne_one hg1)
  simp only [AffineEquiv.homothetyUnitsMulHom_apply_ring, Units.val_mk0] at hgz
  rw [f.eq_homothetyUnitsMulHom_of_linear_one_ne_one hf1,
    g.eq_homothetyUnitsMulHom_of_linear_one_ne_one hg1,
    TauCeti.AffineEquiv.commutatorElement_homothetyUnitsMulHom] at hcomm
  have hpq := eq_zero_of_forall_apply_add_eq hy hrot fun w ↦ by simpa using hcomm w
  simp only [mul_eq_zero, sub_eq_zero] at hpq
  rcases hpq with (hpq | hpq) | hpq
  · exact (hf1 hpq).elim
  · exact (hg1 hpq.symm).elim
  · rw [hgz, hpq]

omit [TopologicalSpace X] [T2Space X] in
/-- The rotations about a centre of invariance form an infinite family in the isotropy. -/
private theorem infinite_setOf_comp_eq_of_forall {z₀ : ℂ}
    (hrot : ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z) :
    {f : ℂ ≃ᵃ[ℂ] ℂ | u ∘ f = u}.Infinite := by
  refine Set.infinite_of_injOn_mapsTo (f := fun θ : ℝ ↦ AffineEquiv.homothetyUnitsMulHom z₀
    (Units.mk0 (Complex.exp (θ * Complex.I)) (Complex.exp_ne_zero _))) (s := Ioo 0 1)
    (fun θ hθ θ' hθ' h ↦ ?_) (fun θ _ ↦ ?_) (Ioo_infinite (by norm_num))
  · have h1 := congrArg (fun f : ℂ ≃ᵃ[ℂ] ℂ ↦ f (z₀ + 1)) h
    simp only [AffineEquiv.homothetyUnitsMulHom_apply_ring, Units.val_mk0, add_sub_cancel_left,
      mul_one, add_right_inj] at h1
    have harg : ∀ φ ∈ Ioo (0 : ℝ) 1, Complex.arg (Complex.exp (φ * Complex.I)) = φ := by
      intro φ hφ
      rw [Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I]
      constructor <;> linarith [hφ.1, hφ.2, Real.two_le_pi]
    rw [← harg θ hθ, ← harg θ' hθ', h1]
  · funext z
    rw [Function.comp_apply, AffineEquiv.homothetyUnitsMulHom_apply_ring, Units.val_mk0, hrot]

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
    rw [← hexp, ← Complex.exp_intCast_mul, ← hm']
    push_cast
    rw [show (k : ℂ) * ((m : ℂ) * (g : ℝ) * Complex.I) = m * (2 * Real.pi * Complex.I) by
      linear_combination ((m : ℂ) * Complex.I) * hk']
    exact Complex.exp_int_mul_two_pi_mul_I m
  rcases Int.natAbs_eq k with hk2 | hk2
  · rwa [hk2, zpow_natCast] at hck
  · rwa [hk2, zpow_neg, zpow_natCast, inv_eq_one] at hck

end TauCeti

namespace Continuous

open TauCeti

variable {X : Type*} [TopologicalSpace X] [T2Space X] {u : ℂ → X}

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

end Continuous
