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

/-!
# Compactness of the orthogonal group over a local field

Let `Q` be a nondegenerate quadratic form on a finite-dimensional space `V` over a locally compact
nontrivially normed field `K` in which `2` is invertible, such as `ℝ` or `ℚ_p`. The orthogonal
group `O(Q)`, with the canonical topology of the linear automorphism group `V ≃ₗ[K] V`, is compact
exactly when `Q` is anisotropic.

If `Q` is anisotropic, an isometry sends each basis vector `bᵢ` into the set
`{y | ‖Q y‖ ≤ ‖Q bᵢ‖}`, which is compact because anisotropic forms are coercive. So the
isometries and their inverses lie in a compact set of endomorphisms, and `O(Q)`, being closed,
is compact. No nondegeneracy is needed in this direction.

If `Q` is isotropic and nondegenerate, it contains a hyperbolic pair `u`, `v`, and the split torus
of that pair is a family of isometries `g_t` with `g_t u = t • u`. The continuous function
`g ↦ polar Q (g u) v` takes every nonzero value `t` on this family, so it is unbounded on `O(Q)`,
which is therefore not compact. The torus consists of proper isometries, so in finite dimension
`SO(Q)` is not compact either. This direction holds over any nontrivially normed field, with no
local compactness or condition on `2`.

## Main results

* `TauCeti.QuadraticMap.isCompact_orthogonalGroup`: the orthogonal group of an anisotropic form
  is compact.
* `TauCeti.QuadraticMap.not_isCompact_orthogonalGroup`,
  `TauCeti.QuadraticMap.not_isCompact_specialOrthogonalGroup`: the orthogonal and special
  orthogonal groups of an isotropic nondegenerate form are not compact.
* `TauCeti.QuadraticMap.isCompact_orthogonalGroup_iff`: for a nondegenerate form, the orthogonal
  group is compact exactly when the form is anisotropic.
-/

public section

namespace TauCeti

namespace QuadraticMap

open _root_.QuadraticMap (polar polar_smul_left)

section Noncompact

variable {K V : Type*} [NontriviallyNormedField K] [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V)

/-- A set of linear automorphisms containing the whole split torus of a hyperbolic pair is not
compact: `g ↦ polar Q (g u) v` is continuous and takes the value `t` at the torus element `t`. -/
private theorem not_isCompact_of_hyperbolicPairTorus_mem {u v : V} (hu : Q u = 0) (hv : Q v = 0)
    (huv : polar Q u v = 1) {S : Set (V ≃ₗ[K] V)}
    (hS : ∀ t : Kˣ, (hyperbolicPairTorus Q hu hv huv t : V ≃ₗ[K] V) ∈ S) : ¬IsCompact S := by
  intro hcpt
  let φ : Module.End K V →ₗ[K] K := (Q.polarBilin.flip v).comp (LinearMap.applyₗ u)
  have hφ (g : V ≃ₗ[K] V) : φ g = polar Q (g u) v := by simp [φ]
  have hF : Continuous fun g : V ≃ₗ[K] V => φ g :=
    (IsModuleTopology.continuous_of_linearMap φ).comp continuous_linearEquiv_toLinearMap
  have htorus (t : Kˣ) : φ (hyperbolicPairTorus Q hu hv huv t : V ≃ₗ[K] V) = t := by
    simp [hφ, polar_smul_left, huv]
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp (hcpt.image hF).isBounded
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hr _ ⟨_, hS 1, rfl⟩)
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm K r
  have ht0 : t ≠ 0 := norm_pos_iff.mp (hr0.trans_lt ht)
  have := hr _ ⟨_, hS (Units.mk0 t ht0), rfl⟩
  simp only [htorus, Units.val_mk0] at this
  exact this.not_gt ht

/-- **The special orthogonal group of an isotropic form is not compact.** For an isotropic
nondegenerate quadratic form on a finite-dimensional space over a nontrivially normed field, the
special orthogonal group is not a compact subset of the linear automorphism group. -/
theorem not_isCompact_specialOrthogonalGroup [FiniteDimensional K V] (hQ : Q.Nondegenerate)
    (hiso : ¬Q.Anisotropic) :
    ¬IsCompact (specialOrthogonalGroup Q : Set (V ≃ₗ[K] V)) := by
  obtain ⟨u, v, -, hu, hv, huv⟩ := hQ.exists_isotropic_pair hiso
  exact not_isCompact_of_hyperbolicPairTorus_mem Q hu hv huv fun t =>
    hyperbolicPairTorus_mem_specialOrthogonalGroup hu hv huv t

/-- **The orthogonal group of an isotropic form is not compact.** For an isotropic nondegenerate
quadratic form over a nontrivially normed field, the orthogonal group is not a compact subset of
the linear automorphism group. -/
theorem not_isCompact_orthogonalGroup (hQ : Q.Nondegenerate) (hiso : ¬Q.Anisotropic) :
    ¬IsCompact (orthogonalGroup Q : Set (V ≃ₗ[K] V)) := by
  obtain ⟨u, v, -, hu, hv, huv⟩ := hQ.exists_isotropic_pair hiso
  exact not_isCompact_of_hyperbolicPairTorus_mem Q hu hv huv fun t =>
    (hyperbolicPairTorus Q hu hv huv t).2

end Noncompact

section Compact

variable {K V : Type*} [NontriviallyNormedField K] [WeaklyLocallyCompactSpace K]
  [Invertible (2 : K)] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)

/-- **The orthogonal group of an anisotropic form is compact.** For an anisotropic quadratic form
on a finite-dimensional space over a locally compact nontrivially normed field in which `2` is
invertible, the orthogonal group is a compact subset of the linear automorphism group. -/
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

/-- **Compactness of the orthogonal group.** For a nondegenerate quadratic form on a
finite-dimensional space over a locally compact nontrivially normed field in which `2` is
invertible, such as `ℝ` or `ℚ_p`, the orthogonal group is compact exactly when the form is
anisotropic. -/
theorem isCompact_orthogonalGroup_iff (hQ : Q.Nondegenerate) :
    IsCompact (orthogonalGroup Q : Set (V ≃ₗ[K] V)) ↔ Q.Anisotropic :=
  ⟨fun h => by_contra fun hiso => not_isCompact_orthogonalGroup Q hQ hiso h,
    isCompact_orthogonalGroup Q⟩

end Compact

end QuadraticMap

end TauCeti
