/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Group.Ultra

import Mathlib.Topology.Algebra.Group.Neighborhood
import TauCeti.Analysis.Normed.Group.BallSphere

/-!
# Quotients of seminormed and ultrametric groups

For a subgroup `S` of a seminormed commutative group `M`, an element `s ∈ S` minimises `‖m / s'‖`
over `s' ∈ S` if and only if `‖m / s‖` attains the quotient seminorm `‖(m : M ⧸ S)‖`
(`QuotientGroup.norm_div_eq_norm_mk_iff`), so every coset has a least-norm element precisely when
every class in `M ⧸ S` has a representative of the same norm
(`QuotientGroup.exists_mk_eq_and_norm_eq_iff`). The additive, submodule and ideal counterparts
give the corresponding characterisations of strict closedness for submodules and for two-sided
ideals of possibly noncommutative seminormed rings.

If every element of `S` of positive seminorm has seminorm at least twice that of `m`, then `m`
attains the quotient seminorm of its class (`QuotientGroup.norm_mk_eq_norm`); elements of seminorm
zero impose no condition. So the projection `M → M ⧸ S` preserves the distance between two points
whose distance is at most half the seminorm of every element of `S` of positive seminorm
(`QuotientGroup.dist_mk_eq_dist`); for a lattice in a normed space this says that the projection to
the torus is an isometry on small sets.

When `M` is ultrametric, the quotient seminorm on `M ⧸ S` is again ultrametric: each class has
representatives whose norms approximate its quotient norm, and the ultrametric inequality for a
product of such representatives descends to the quotient. The additive form covers quotients of
modules by submodules and of commutative seminormed rings by ideals, so residue norms of
nonarchimedean Banach algebras are again nonarchimedean.

This file also develops characterizations and operator-norm invariance for Mathlib's normed
quotient maps (`NormedAddGroupHom.IsQuotient`, also called metric surjections):
* contractivity plus arbitrarily close norm lifts (`NormedAddGroupHom.isQuotient_iff_norm_lift`);
* mapping every open ball centered at `0` onto the open ball of the same radius
  (`NormedAddGroupHom.isQuotient_iff_image_ball`);
* expressing target seminorms as infima over preimages (`NormedAddGroupHom.isQuotient_iff_iInf`);
* closure under identities, surjective isometries, and composition;
* preservation of operator norms under precomposition (`NormedAddGroupHom.IsQuotient.norm_comp`,
  `NormedAddGroupHom.IsQuotient.nnnorm_comp`) and unit norm onto spaces with nontrivial topology
  (`NormedAddGroupHom.IsQuotient.norm_eq_one`).

Finally, `TauCeti.isInducing_of_openQuotient_isometry` gives a topological-inducing criterion for
an additive group homomorphism between open quotients of seminormed additive groups intertwined by
an isometry whose image of the source kernel is dense in the target kernel.

## References

* A. Pietsch, *Operator Ideals*, North-Holland (1980), §B.3.2 and §C.3.2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §2.2.
-/

public section

open scoped NNReal

namespace QuotientGroup

section LeastNorm

variable {M : Type*} [SeminormedCommGroup M] {S : Subgroup M}

/-- For `s ∈ S`, the element `m / s` attains the quotient seminorm of `m` modulo `S` if and only
if `s` minimises `‖m / s'‖` over `S`. -/
@[to_additive /-- For `s ∈ S`, the element `m - s` attains the quotient seminorm of `m` modulo `S`
if and only if `s` minimises `‖m - s'‖` over `S`. -/]
theorem norm_div_eq_norm_mk_iff {m s : M} (hs : s ∈ S) :
    ‖m / s‖ = ‖(m : M ⧸ S)‖ ↔ ∀ s' ∈ S, ‖m / s‖ ≤ ‖m / s'‖ := by
  constructor
  · intro h s' hs'
    have hmk : ((m / s' : M) : M ⧸ S) = m :=
      QuotientGroup.eq.mpr (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using hs')
    exact h.trans_le (hmk ▸ norm_mk_le_norm)
  · intro h
    apply le_antisymm
    · refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
      obtain ⟨n, hn, hn'⟩ := exists_norm_mk_lt (m : M ⧸ S) hε
      have hmn : m / n ∈ S := by
        have := QuotientGroup.eq.mp hn.symm
        simpa [div_eq_mul_inv, mul_comm] using S.inv_mem this
      exact (h (m / n) hmn).trans_lt (by simpa [div_div_cancel] using hn')
    · have hmk : ((m / s : M) : M ⧸ S) = m :=
        QuotientGroup.eq.mpr (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using hs)
      exact hmk ▸ norm_mk_le_norm

/-- Every class in `M ⧸ S` has a representative attaining its quotient seminorm if and only if
every coset of `S` has an element of least seminorm. -/
@[to_additive /-- Every class in `M ⧸ S` has a representative attaining its quotient seminorm if
and only if every coset of `S` has an element of least seminorm. -/]
theorem exists_mk_eq_and_norm_eq_iff :
    (∀ x : M ⧸ S, ∃ m : M, (m : M ⧸ S) = x ∧ ‖m‖ = ‖x‖) ↔
      ∀ m : M, ∃ s ∈ S, ∀ s' ∈ S, ‖m / s‖ ≤ ‖m / s'‖ := by
  constructor
  · intro h m
    obtain ⟨n, hn, hnorm⟩ := h (m : M ⧸ S)
    have hmn : m / n ∈ S := by
      have := QuotientGroup.eq.mp hn.symm
      simpa [div_eq_mul_inv, mul_comm] using S.inv_mem this
    refine ⟨m / n, hmn, (norm_div_eq_norm_mk_iff hmn).mp ?_⟩
    simpa [div_div_cancel] using hnorm
  · intro h x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨s, hs, hle⟩ := h m
    have hmk : ((m / s : M) : M ⧸ S) = m :=
      QuotientGroup.eq.mpr (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using hs)
    exact ⟨m / s, hmk, (norm_div_eq_norm_mk_iff hs).mpr hle⟩

end LeastNorm

section Small

variable {M : Type*} [SeminormedCommGroup M] {S : Subgroup M}

/-- If every element of `S` of positive seminorm has at least twice the seminorm of `m`, then the
quotient seminorm of `m` modulo `S` is the seminorm of `m`. -/
@[to_additive /-- If every element of `S` of positive seminorm has at least twice the seminorm of
`m`, then the quotient seminorm of `m` modulo `S` is the seminorm of `m`. -/]
theorem norm_mk_eq_norm {m : M} (h : ∀ s ∈ S, 0 < ‖s‖ → 2 * ‖m‖ ≤ ‖s‖) :
    ‖(m : M ⧸ S)‖ = ‖m‖ := by
  refine le_antisymm norm_mk_le_norm (le_norm_iff.2 fun m' hm' ↦ ?_)
  have hs : m' / m ∈ S := inv_mul_eq_div m m' ▸ QuotientGroup.eq.1 hm'.symm
  rcases (norm_nonneg' (m' / m)).eq_or_lt with h0 | hpos
  · -- `m` and `m'` are at distance zero, so they have the same seminorm
    have := norm_le_norm_add_norm_div' m m'
    rwa [norm_div_rev, ← h0, add_zero] at this
  · linarith [h _ hs hpos, norm_div_le m' m]

/-- The projection to `M ⧸ S` preserves the distance between `x` and `y` when every element of `S`
of positive seminorm has at least twice that distance as seminorm. -/
@[to_additive /-- The projection to `M ⧸ S` preserves the distance between `x` and `y` when every
element of `S` of positive seminorm has at least twice that distance as seminorm. -/]
theorem dist_mk_eq_dist {x y : M} (h : ∀ s ∈ S, 0 < ‖s‖ → 2 * dist x y ≤ ‖s‖) :
    dist (x : M ⧸ S) y = dist x y := by
  rw [dist_eq_norm_div, dist_eq_norm_div, ← QuotientGroup.mk_div]
  exact norm_mk_eq_norm fun s hs hs0 ↦ (dist_eq_norm_div x y) ▸ h s hs hs0

end Small

section Ultrametric

variable {M : Type*} [SeminormedCommGroup M] [IsUltrametricDist M]

/-- The quotient of an ultrametric seminormed commutative group by a subgroup is ultrametric. -/
@[to_additive /-- The quotient of an ultrametric seminormed additive commutative group by an
additive subgroup is ultrametric. -/]
instance instIsUltrametricDist (S : Subgroup M) : IsUltrametricDist (M ⧸ S) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_mul_le_max_norm fun x y ↦ by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨a, rfl, ha⟩ := exists_norm_mk_lt x hε
    obtain ⟨b, rfl, hb⟩ := exists_norm_mk_lt y hε
    rw [← QuotientGroup.mk_mul]
    calc ‖((a * b : M) : M ⧸ S)‖ ≤ ‖a * b‖ := norm_mk_le_norm
      _ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_mul_le_max a b
      _ ≤ max ‖(a : M ⧸ S)‖ ‖(b : M ⧸ S)‖ + ε :=
        (max_le_max ha.le hb.le).trans (max_add_add_right _ _ _).le

end Ultrametric

end QuotientGroup

section Submodule

variable {R M : Type*} [Ring R] [SeminormedAddCommGroup M] [Module R M]

/-- For `s ∈ S`, the vector `m - s` attains the quotient seminorm of `m` modulo the submodule `S`
if and only if `s` minimises `‖m - s'‖` over `S`. -/
theorem Submodule.Quotient.norm_sub_eq_norm_mk_iff {S : Submodule R M} {m s : M} (hs : s ∈ S) :
    ‖m - s‖ = ‖(Submodule.Quotient.mk m : M ⧸ S)‖ ↔ ∀ s' ∈ S, ‖m - s‖ ≤ ‖m - s'‖ :=
  QuotientAddGroup.norm_sub_eq_norm_mk_iff (S := S.toAddSubgroup) hs

/-- Every class in `M ⧸ S` has a representative attaining its quotient seminorm if and only if
every coset of the submodule `S` has a vector of least seminorm. -/
theorem Submodule.Quotient.exists_mk_eq_and_norm_eq_iff {S : Submodule R M} :
    (∀ x : M ⧸ S, ∃ m : M, Submodule.Quotient.mk m = x ∧ ‖m‖ = ‖x‖) ↔
      ∀ m : M, ∃ s ∈ S, ∀ s' ∈ S, ‖m - s‖ ≤ ‖m - s'‖ :=
  QuotientAddGroup.exists_mk_eq_and_norm_eq_iff (S := S.toAddSubgroup)

/-- The quotient of an ultrametric seminormed module by a submodule is ultrametric. -/
instance Submodule.Quotient.instIsUltrametricDist [IsUltrametricDist M] (S : Submodule R M) :
    IsUltrametricDist (M ⧸ S) :=
  inferInstanceAs <| IsUltrametricDist (M ⧸ S.toAddSubgroup)

end Submodule

section Ideal

variable {R : Type*} [SeminormedRing R] {I : Ideal R} [I.IsTwoSided]

/-- For `s ∈ I`, the element `r - s` attains the quotient seminorm of `r` modulo the two-sided
ideal `I` if and only if `s` minimises `‖r - s'‖` over `I`. -/
theorem Ideal.Quotient.norm_sub_eq_norm_mk_iff {r s : R} (hs : s ∈ I) :
    ‖r - s‖ = ‖Ideal.Quotient.mk I r‖ ↔ ∀ s' ∈ I, ‖r - s‖ ≤ ‖r - s'‖ :=
  Submodule.Quotient.norm_sub_eq_norm_mk_iff (S := I) hs

/-- Every residue class in `R ⧸ I` has a representative attaining its quotient seminorm if and only
if every coset of the two-sided ideal `I` has an element of least seminorm. -/
theorem Ideal.Quotient.exists_mk_eq_and_norm_eq_iff :
    (∀ x : R ⧸ I, ∃ r : R, Ideal.Quotient.mk I r = x ∧ ‖r‖ = ‖x‖) ↔
      ∀ r : R, ∃ s ∈ I, ∀ s' ∈ I, ‖r - s‖ ≤ ‖r - s'‖ :=
  Submodule.Quotient.exists_mk_eq_and_norm_eq_iff (S := I)

end Ideal

namespace NormedAddGroupHom

section IsQuotient

variable {M N : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]

/-- A normed quotient map has operator norm at most one. -/
theorem IsQuotient.norm_le_one {f : NormedAddGroupHom M N} (hf : f.IsQuotient) : ‖f‖ ≤ 1 :=
  NormNoninc.normNoninc_iff_norm_le_one.mp hf.norm_le

/-- A normed quotient map has nonnegative operator norm at most one. -/
theorem IsQuotient.nnnorm_le_one {f : NormedAddGroupHom M N} (hf : f.IsQuotient) : ‖f‖₊ ≤ 1 := by
  exact_mod_cast hf.norm_le_one

/-- Construct `NormedAddGroupHom.IsQuotient` from contractivity and arbitrarily close norm lifts. -/
theorem IsQuotient.of_norm_lift {f : NormedAddGroupHom M N} (h₁ : ‖f‖ ≤ 1)
    (h₂ : ∀ {ε : ℝ}, 0 < ε → ∀ y : N, ∃ x : M, f x = y ∧ ‖x‖ < ‖y‖ + ε) : f.IsQuotient where
  surjective y := by
    obtain ⟨x, hx, -⟩ := h₂ zero_lt_one y
    exact ⟨x, hx⟩
  norm x := by
    have hbdd : BddBelow ((fun m ↦ ‖x + m‖) '' f.ker) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨m, -, rfl⟩
      exact norm_nonneg _
    refine le_antisymm (le_csInf ⟨‖x + 0‖, 0, f.ker.zero_mem, rfl⟩ ?_) ?_
    · rintro _ ⟨m, hm, rfl⟩
      have hfm : f (x + m) = f x := by simp [(f.mem_ker m).mp hm]
      simpa [hfm] using f.le_of_opNorm_le h₁ (x + m)
    · refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
      obtain ⟨x', hx', hlt⟩ := h₂ hε (f x)
      have hker : x' - x ∈ f.ker := by simp [f.mem_ker, map_sub, hx']
      exact (csInf_le hbdd ⟨x' - x, hker, congrArg norm (add_sub_cancel x x')⟩).trans_lt hlt

/-- **Norm-lifting characterization.** A bounded additive homomorphism is a normed quotient map if
and only if it has operator norm at most one and lifts every target element to preimages of norm
arbitrarily close to its norm. -/
theorem isQuotient_iff_norm_lift {f : NormedAddGroupHom M N} :
    f.IsQuotient ↔
      ‖f‖ ≤ 1 ∧ ∀ {ε : ℝ}, 0 < ε → ∀ y : N, ∃ x : M, f x = y ∧ ‖x‖ < ‖y‖ + ε :=
  ⟨fun hf ↦ ⟨hf.norm_le_one, hf.norm_lift⟩, fun ⟨h₁, h₂⟩ ↦ .of_norm_lift h₁ h₂⟩

/-- Every open ball centered at `0` in the codomain is contained in the image of the open ball of
the same radius under a normed quotient map. -/
theorem IsQuotient.ball_subset_image_ball {f : NormedAddGroupHom M N} (hf : f.IsQuotient)
    (r : ℝ) : Metric.ball (0 : N) r ⊆ f '' Metric.ball 0 r := fun y hy ↦ by
  have hy' : ‖y‖ < r := mem_ball_zero_iff.mp hy
  obtain ⟨x, hx, hlt⟩ := hf.norm_lift (sub_pos.mpr hy') y
  exact ⟨x, mem_ball_zero_iff.mpr (hlt.trans_eq (add_sub_cancel ‖y‖ r)), hx⟩

/-- A normed quotient map sends each open ball centered at `0` onto the open ball of the same
radius. -/
theorem IsQuotient.image_ball {f : NormedAddGroupHom M N} (hf : f.IsQuotient) (r : ℝ) :
    f '' Metric.ball 0 r = Metric.ball 0 r := by
  refine subset_antisymm ?_ (hf.ball_subset_image_ball r)
  simpa using ((f.lipschitzWith.weaken hf.nnnorm_le_one).mapsTo_ball one_ne_zero 0 r).image_subset

/-- Construct `NormedAddGroupHom.IsQuotient` from contractivity and open-ball lifting. -/
theorem IsQuotient.of_ball_subset_image_ball {f : NormedAddGroupHom M N} (h₁ : ‖f‖ ≤ 1)
    (h₂ : ∀ r : ℝ, Metric.ball (0 : N) r ⊆ f '' Metric.ball 0 r) : f.IsQuotient :=
  .of_norm_lift h₁ fun hε y ↦ TauCeti.exists_apply_eq_norm_lt_add h₂ y hε

/-- **Open-ball characterization.** A bounded additive homomorphism is a normed quotient map if and
only if it maps each open ball centered at `0` onto the open ball of the same radius. -/
theorem isQuotient_iff_image_ball {f : NormedAddGroupHom M N} :
    f.IsQuotient ↔ ∀ r : ℝ, f '' Metric.ball 0 r = Metric.ball 0 r := by
  refine ⟨fun hf ↦ hf.image_ball, fun h ↦ .of_ball_subset_image_ball ?_ fun r ↦ (h r).ge⟩
  refine f.opNorm_le_bound zero_le_one fun x ↦ ?_
  rw [one_mul]
  refine le_of_forall_pos_lt_add fun ε hε ↦ mem_ball_zero_iff.mp ?_
  rw [← h (‖x‖ + ε)]
  exact ⟨x, mem_ball_zero_iff.mpr (lt_add_of_pos_right ‖x‖ hε), rfl⟩

/-- A normed quotient map expresses the seminorm of every `y` as the infimum of the seminorms of
its preimages. -/
theorem IsQuotient.norm_eq_iInf {f : NormedAddGroupHom M N} (hf : f.IsQuotient) (y : N) :
    ‖y‖ = ⨅ x : {x : M // f x = y}, ‖x.val‖ := by
  have : Nonempty {x : M // f x = y} := nonempty_subtype.mpr (hf.surjective y)
  have hbdd : BddBelow (Set.range fun x : {x : M // f x = y} ↦ ‖x.val‖) :=
    ⟨0, Set.forall_mem_range.mpr fun x ↦ norm_nonneg x.val⟩
  refine le_antisymm (le_ciInf fun x ↦ by simpa [x.property] using hf.norm_le x.val) ?_
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨x, hx, hlt⟩ := hf.norm_lift hε y
  exact (ciInf_le hbdd ⟨x, hx⟩).trans_lt hlt

/-- **Preimage-infimum characterization.** A bounded additive homomorphism is a normed quotient map
if and only if it has norm at most one, is surjective, and expresses every target seminorm as the
infimum over preimages. -/
theorem isQuotient_iff_iInf {f : NormedAddGroupHom M N} :
    f.IsQuotient ↔
      ‖f‖ ≤ 1 ∧ Function.Surjective f ∧ ∀ y : N, ‖y‖ = ⨅ x : {x : M // f x = y}, ‖x.val‖ := by
  refine ⟨fun hf ↦ ⟨hf.norm_le_one, hf.surjective, hf.norm_eq_iInf⟩, ?_⟩
  rintro ⟨h₁, hsurj, hiInf⟩
  refine .of_norm_lift h₁ fun {ε} hε y ↦ ?_
  have : Nonempty {x : M // f x = y} := nonempty_subtype.mpr (hsurj y)
  have hlt : (⨅ x : {x : M // f x = y}, ‖x.val‖) < ‖y‖ + ε := by
    rw [← hiInf y]
    exact lt_add_of_pos_right ‖y‖ hε
  obtain ⟨⟨x, hx⟩, hxlt⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨x, hx, hxlt⟩

/-- Every surjective isometric bounded additive homomorphism is a normed quotient map. -/
theorem IsQuotient.of_surjective_isometry {f : NormedAddGroupHom M N}
    (hsurj : Function.Surjective f) (hiso : Isometry f) : f.IsQuotient := by
  refine .of_norm_lift (NormNoninc.normNoninc_iff_norm_le_one.mp (normNoninc_of_isometry hiso))
    fun hε y ↦ ?_
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨x, rfl, by simpa only [norm_eq_of_isometry hiso] using lt_add_of_pos_right ‖x‖ hε⟩

/-- The identity bounded additive homomorphism on any seminormed group is a normed quotient map. -/
@[simp]
theorem IsQuotient.id : (NormedAddGroupHom.id M).IsQuotient :=
  .of_surjective_isometry Function.surjective_id isometry_id

section Composition

variable {P : Type*} [SeminormedAddCommGroup P]

/-- Normed quotient maps are closed under composition. -/
theorem IsQuotient.comp {g : NormedAddGroupHom N P} {f : NormedAddGroupHom M N}
    (hg : g.IsQuotient) (hf : f.IsQuotient) : (g.comp f).IsQuotient := by
  refine .of_norm_lift (((g.norm_comp_le f).trans
      (mul_le_of_le_one_right (opNorm_nonneg g) hf.norm_le_one)).trans hg.norm_le_one)
    fun hε z ↦ ?_
  obtain ⟨y, rfl, hy⟩ := hg.norm_lift (half_pos hε) z
  obtain ⟨x, rfl, hx⟩ := hf.norm_lift (half_pos hε) y
  exact ⟨x, rfl, by linarith⟩

/-- If `q` lifts every element `y` to preimages of norm arbitrarily close to `‖y‖`, then
precomposition with `q` cannot decrease operator norms. -/
theorem le_norm_comp_of_forall_exists_lt {q : NormedAddGroupHom M N}
    (hq : ∀ {ε : ℝ}, 0 < ε → ∀ y : N, ∃ x : M, q x = y ∧ ‖x‖ < ‖y‖ + ε)
    (T : NormedAddGroupHom N P) : ‖T‖ ≤ ‖T.comp q‖ := by
  refine T.opNorm_le_bound (opNorm_nonneg (T.comp q)) fun y ↦ le_of_forall_pos_lt_add fun δ hδ ↦ ?_
  obtain ⟨x, hx, hlt⟩ :=
    hq (div_pos hδ (add_pos_of_nonneg_of_pos (opNorm_nonneg (T.comp q)) one_pos)) y
  calc ‖T y‖ = ‖(T.comp q) x‖ := by simp [hx]
    _ ≤ ‖T.comp q‖ * ‖x‖ := (T.comp q).le_opNorm x
    _ ≤ ‖T.comp q‖ * (‖y‖ + δ / (‖T.comp q‖ + 1)) := by gcongr
    _ = ‖T.comp q‖ * ‖y‖ + ‖T.comp q‖ * (δ / (‖T.comp q‖ + 1)) := mul_add ..
    _ < ‖T.comp q‖ * ‖y‖ + δ := by
      gcongr
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      linarith

/-- Precomposition with a normed quotient map preserves the operator norm. -/
theorem IsQuotient.norm_comp {q : NormedAddGroupHom M N} (hq : q.IsQuotient)
    (T : NormedAddGroupHom N P) : ‖T.comp q‖ = ‖T‖ :=
  le_antisymm
    ((T.norm_comp_le q).trans (mul_le_of_le_one_right (opNorm_nonneg T) hq.norm_le_one))
    (le_norm_comp_of_forall_exists_lt hq.norm_lift T)

/-- Precomposition with a normed quotient map preserves the nonnegative operator norm. -/
theorem IsQuotient.nnnorm_comp {q : NormedAddGroupHom M N} (hq : q.IsQuotient)
    (T : NormedAddGroupHom N P) : ‖T.comp q‖₊ = ‖T‖₊ :=
  NNReal.eq (hq.norm_comp T)

end Composition

/-- A normed quotient map onto a seminormed group with nontrivial topology has operator norm one. -/
theorem IsQuotient.norm_eq_one [NontrivialTopology N] {q : NormedAddGroupHom M N}
    (hq : q.IsQuotient) : ‖q‖ = 1 := by
  have hcomp : (NormedAddGroupHom.id N).comp q = q := ext fun _ ↦ rfl
  simpa [hcomp, NormedAddGroupHom.norm_id] using hq.norm_comp (NormedAddGroupHom.id N)

/-- A normed quotient map onto a seminormed group with nontrivial topology has nonnegative operator
norm one. -/
theorem IsQuotient.nnnorm_eq_one [NontrivialTopology N] {q : NormedAddGroupHom M N}
    (hq : q.IsQuotient) : ‖q‖₊ = 1 :=
  NNReal.eq hq.norm_eq_one

end IsQuotient

end NormedAddGroupHom

namespace TauCeti

open Filter Topology

/-- If `q : G ↠ Q` and `q' : G' ↠ Q'` are open quotient homomorphisms from seminormed additive
groups intertwined by an isometry `f : G → G'` and a homomorphism `ι : Q → Q'`, and `f (ker q)` is
dense in `ker q'`, then `ι` is topologically inducing. -/
theorem isInducing_of_openQuotient_isometry {G G' Q Q' Fq Fq' Fι : Type*}
    [SeminormedAddGroup G] [SeminormedAddGroup G']
    [AddGroup Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q]
    [AddGroup Q'] [TopologicalSpace Q'] [IsTopologicalAddGroup Q']
    [FunLike Fq G Q] [AddMonoidHomClass Fq G Q]
    [FunLike Fq' G' Q'] [AddMonoidHomClass Fq' G' Q']
    [FunLike Fι Q Q'] [AddMonoidHomClass Fι Q Q']
    (q : Fq) (hq : IsOpenQuotientMap q) (q' : Fq') (hq' : IsOpenQuotientMap q')
    (f : G → G') (hf : Isometry f) (ι : Fι) (hcomm : ∀ g, q' (f g) = ι (q g))
    (hker : {x | q' x = 0} ⊆ closure (f '' {x | q x = 0})) :
    Topology.IsInducing ι := by
  have hcont : Continuous ι :=
    hq.isQuotientMap.continuous_iff.mpr
      (by simpa [Function.comp_def, ← hcomm] using hq'.continuous.comp hf.continuous)
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  refine le_antisymm (by simpa only [map_zero] using (hcont.tendsto 0).le_comap) fun U hU ↦ ?_
  have hqU : q ⁻¹' U ∈ 𝓝 (0 : G) := hq.continuous.tendsto 0 (map_zero q ▸ hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hqU
  refine ⟨q' '' Metric.ball 0 (ε / 2),
    (hq'.isOpenMap _ Metric.isOpen_ball).mem_nhds
      ⟨0, Metric.mem_ball_self (half_pos hε), map_zero q'⟩, ?_⟩
  rintro m ⟨w, hw, hwm⟩
  obtain ⟨v, rfl⟩ := hq.surjective m
  have hmem : f v - w ∈ closure (f '' {x | q x = 0}) :=
    hker (by rw [Set.mem_ofPred_eq, map_sub, hcomm, hwm, sub_self])
  obtain ⟨_, ⟨k, hk, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp hmem (ε / 2) (half_pos hε)
  have hkv : -k + v ∈ Metric.ball (0 : G) ε := by
    rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm_neg_add, ← hf.dist_eq, dist_comm]
    rw [Metric.mem_ball, dist_zero_right] at hw
    calc dist (f v) (f k) ≤ dist (f v) (f v - w) + dist (f v - w) (f k) := dist_triangle _ _ _
      _ = ‖w‖ + dist (f v - w) (f k) := by
        rw [dist_eq_norm_neg_add, sub_eq_add_neg, neg_add_cancel_left, norm_neg]
      _ < ε / 2 + ε / 2 := add_lt_add hw hdist
      _ = ε := add_halves ε
  have hqv := hball hkv
  rwa [Set.mem_preimage, map_add, map_neg, Set.mem_ofPred_eq.mp hk, neg_zero, zero_add] at hqv

end TauCeti
