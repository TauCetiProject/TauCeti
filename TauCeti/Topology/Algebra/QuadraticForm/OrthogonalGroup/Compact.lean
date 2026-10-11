/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.QuadraticMap
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.HyperbolicPair
public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Closed
import TauCeti.LinearAlgebra.QuadraticForm.Representation
import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Compactness of the orthogonal group over a local field

Let `Q` be a quadratic form on a finite-dimensional space `V` over a locally compact
nontrivially normed field `K`, such as `ℝ` or `ℚ_p`. The orthogonal group `O(Q)`, with the
canonical topology of the linear automorphism group `V ≃ₗ[K] V`, is compact exactly when `Q` is
anisotropic. No nondegeneracy assumption is needed.

For an isotropic form, `O(Q)` is not compact over any nontrivially normed field, without local
compactness or finite-dimensionality. In finite dimension, `SO(Q)` is not compact either when
the radical is trivial. More generally, any set of automorphisms containing the split torus of a
hyperbolic pair at every square parameter is not compact; this also applies to the image of the
Spin group. None of these results requires a condition on `2`.

## Main results

* `TauCeti.QuadraticMap.not_isCompact_of_hyperbolicPairTorus_sq_mem`: a set of automorphisms
  containing the split torus at every square parameter is not compact.
* `TauCeti.QuadraticMap.isCompact_orthogonalGroup`: the orthogonal group of an anisotropic form
  is compact.
* `TauCeti.QuadraticMap.not_isCompact_orthogonalGroup`: the orthogonal group of an isotropic form
  is not compact.
* `TauCeti.QuadraticMap.not_isCompact_specialOrthogonalGroup`: the special orthogonal group of
  an isotropic form with trivial radical is not compact.
* `TauCeti.QuadraticMap.isCompact_orthogonalGroup_iff`: the orthogonal group is compact exactly
  when the form is anisotropic.
-/

public section

namespace TauCeti

namespace QuadraticMap

open _root_.QuadraticMap (polar polar_smul_left)

section Noncompact

variable {K V : Type*} [NontriviallyNormedField K] [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V)

/-- A set of linear automorphisms containing the split torus of a hyperbolic pair at every square
parameter is not compact. The square parameters suffice for applications to the image of the
Spin group. No local compactness or finite-dimensionality is required. -/
theorem not_isCompact_of_hyperbolicPairTorus_sq_mem {u v : V} (hu : Q u = 0) (hv : Q v = 0)
    (huv : polar Q u v = 1) {S : Set (V ≃ₗ[K] V)}
    (hS : ∀ t : Kˣ, (hyperbolicPairTorus Q hu hv huv (t ^ 2) : V ≃ₗ[K] V) ∈ S) :
    ¬IsCompact S := by
  intro hcpt
  let φ : Module.End K V →ₗ[K] K := (Q.polarBilin.flip v).comp (LinearMap.applyₗ u)
  have hφ (g : V ≃ₗ[K] V) : φ g = polar Q (g u) v := by simp [φ]
  have hF : Continuous fun g : V ≃ₗ[K] V => φ g :=
    (IsModuleTopology.continuous_of_linearMap φ).comp continuous_linearEquiv_toLinearMap
  have htorus (t : Kˣ) : φ (hyperbolicPairTorus Q hu hv huv t : V ≃ₗ[K] V) = t := by
    simp [hφ, polar_smul_left, huv]
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp (hcpt.image hF).isBounded
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm K (max r 1)
  have ht0 : t ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le (le_max_right r 1) |>.trans ht)
  have := hr _ ⟨_, hS (Units.mk0 t ht0), rfl⟩
  simp only [htorus, Units.val_pow_eq_pow_val, Units.val_mk0, norm_pow] at this
  nlinarith [le_max_left r 1, le_max_right r 1]

/-- The special orthogonal group of an isotropic quadratic form with trivial radical on a
finite-dimensional space over a nontrivially normed field is not compact. -/
theorem not_isCompact_specialOrthogonalGroup [FiniteDimensional K V] (hQ : Q.radical = ⊥)
    (hiso : ¬Q.Anisotropic) :
    ¬IsCompact (specialOrthogonalGroup Q : Set (V ≃ₗ[K] V)) := by
  obtain ⟨u, v, -, hu, hv, huv⟩ :=
    _root_.QuadraticMap.exists_isotropic_pair_of_radical_eq_bot hQ hiso
  exact not_isCompact_of_hyperbolicPairTorus_sq_mem Q hu hv huv fun t =>
    hyperbolicPairTorus_mem_specialOrthogonalGroup hu hv huv (t ^ 2)

/-- The orthogonal group of an isotropic quadratic form over a nontrivially normed field is not
compact. No nondegeneracy or finite-dimensionality is required. -/
theorem not_isCompact_orthogonalGroup (hiso : ¬Q.Anisotropic) :
    ¬IsCompact (orthogonalGroup Q : Set (V ≃ₗ[K] V)) := by
  by_cases hQ : Q.radical = ⊥
  · obtain ⟨u, v, -, hu, hv, huv⟩ :=
      _root_.QuadraticMap.exists_isotropic_pair_of_radical_eq_bot hQ hiso
    exact not_isCompact_of_hyperbolicPairTorus_sq_mem Q hu hv huv fun t =>
      (hyperbolicPairTorus Q hu hv huv (t ^ 2)).2
  intro hcpt
  -- Scale a nonzero radical vector while fixing the kernel of a linear functional.
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
  obtain ⟨f, hfu⟩ := Module.Projective.exists_dual_eq_one K hu0
  let φ : Module.End K V →ₗ[K] K := f.comp (LinearMap.applyₗ u)
  have hF : Continuous fun g : V ≃ₗ[K] V => φ g :=
    (IsModuleTopology.continuous_of_linearMap φ).comp continuous_linearEquiv_toLinearMap
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp (hcpt.image hF).isBounded
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm K (max r 1)
  have ht0 : t ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le (le_max_right r 1) |>.trans ht)
  let g := LinearEquiv.dilatransvection (f := f) (v := (t - 1) • u)
    (by simpa [hfu] using isUnit_iff_ne_zero.mpr ht0)
  have hg : g ∈ orthogonalGroup Q := by
    apply mem_orthogonalGroup_iff.mpr
    intro x
    rw [LinearEquiv.dilatransvection.apply]
    have hrad : f x • ((t - 1) • u) ∈ Q.radical :=
      Q.radical.smul_mem _ (Q.radical.smul_mem _ hu)
    simpa [add_comm] using (_root_.QuadraticMap.mem_radical_iff'.mp hrad).2 x
  have hgφ : φ g = t := by simp [φ, g, LinearMap.transvection.apply, hfu]
  have hbound : ‖φ g‖ ≤ r := hr _ ⟨g, hg, rfl⟩
  rw [hgφ] at hbound
  exact (not_le_of_gt ht) (le_trans hbound (le_max_left r 1))

end Noncompact

section Compact

variable {K V : Type*} [NontriviallyNormedField K] [WeaklyLocallyCompactSpace K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)

/-- **The orthogonal group of an anisotropic form is compact.** For an anisotropic quadratic form
on a finite-dimensional space over a locally compact nontrivially normed field, the orthogonal
group is a compact subset of the linear automorphism group. -/
theorem isCompact_orthogonalGroup (hQ : Q.Anisotropic) :
    IsCompact (orthogonalGroup Q : Set (V ≃ₗ[K] V)) := by
  let _ : TopologicalSpace V := moduleTopology K V
  have : IsModuleTopology K V := ⟨rfl⟩
  let b := Module.finBasis K V
  -- The endomorphisms sending each `b i` into the compact set `{y | ‖Q y‖ ≤ ‖Q (b i)‖}`.
  let C : Set (Module.End K V) :=
    b.constr K '' Set.univ.pi fun i => {y | ‖Q y‖ ≤ ‖Q (b i)‖}
  have hC : IsCompact C :=
    (isCompact_univ_pi fun i => hQ.isCompact_setOf_norm_apply_le _).image
      (IsModuleTopology.continuous_of_linearMap (b.constr K).toLinearMap)
  have hmemC {g : V ≃ₗ[K] V} (hg : g ∈ orthogonalGroup Q) : (g : Module.End K V) ∈ C :=
    ⟨fun i => g (b i), fun i _ => by simp [map_app_of_mem_orthogonalGroup hg],
      b.constr_self K _⟩
  -- The pairs of mutually inverse endomorphisms in `C` form a compact set.
  let T : Set (Module.End K V × Module.End K V) :=
    (C ×ˢ C) ∩ {p | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1}
  have hT : IsCompact T :=
    (hC.prod hC).inter_right
      ((isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).inter
        (isClosed_eq (continuous_snd.mul continuous_fst) continuous_const))
  have : CompactSpace T := isCompact_iff_compactSpace.mp hT
  -- Such a pair is a linear automorphism, continuously in the pair.
  let Φ : T → V ≃ₗ[K] V := fun p => LinearEquiv.ofLinearMap p.1.1 p.1.2 p.2.2.1 p.2.2.2
  have hΦ : Continuous Φ := continuous_linearEquiv_iff.mpr
    ⟨(continuous_fst.comp continuous_subtype_val).congr fun p => by simp [Φ],
      (continuous_snd.comp continuous_subtype_val).congr fun p =>
        LinearMap.ext fun x => by simp [Φ]⟩
  refine (isCompact_range hΦ).of_isClosed_subset (isClosed_orthogonalGroup Q) fun g hg => ?_
  have hinv : (g : Module.End K V) * ((g⁻¹ : V ≃ₗ[K] V) : Module.End K V) = 1 :=
    LinearMap.ext fun x => by simp
  have hinv' : ((g⁻¹ : V ≃ₗ[K] V) : Module.End K V) * (g : Module.End K V) = 1 :=
    LinearMap.ext fun x => by simp
  exact ⟨⟨((g : Module.End K V), ((g⁻¹ : V ≃ₗ[K] V) : Module.End K V)),
    ⟨hmemC hg, hmemC (inv_mem hg)⟩, hinv, hinv'⟩, LinearEquiv.ext fun x => by simp [Φ]⟩

/-- The orthogonal group of a quadratic form on a finite-dimensional space
over a locally compact nontrivially normed field is compact exactly when the form is anisotropic. -/
theorem isCompact_orthogonalGroup_iff :
    IsCompact (orthogonalGroup Q : Set (V ≃ₗ[K] V)) ↔ Q.Anisotropic :=
  ⟨fun h => by_contra fun hiso => not_isCompact_orthogonalGroup Q hiso h,
    isCompact_orthogonalGroup Q⟩

end Compact

end QuadraticMap

end TauCeti
