/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import TauCeti.RepresentationTheory.Coinduced
public import TauCeti.RepresentationTheory.Induction.Mackey.Subgroup
import TauCeti.GroupTheory.DoubleCoset.DeltaForm

/-!
# Spanning coinduced forms with pointwise bounds

At a free level, evaluation at one double coset representative can be prescribed independently
of the others by a delta form. Consequently a pointwise condition compatible with the two
covariance laws gives a spanning set of forms if it gives a spanning set of values at each
representative. The condition need not be linear: it can impose both local lattice membership
and archimedean length bounds on the same vector.

This is the passage from local vectors to short forms in `New.isShort_deltaForm` and
`New.span_isShort_eq_top` in `grh/src/New/UpperBound/Size/ShortColumns.lean` of
<https://github.com/lsernau/grh-lean> (revision `72fead1`).
-/

public section

open TauCeti Submodule

namespace Representation

variable {R G V : Type*} [CommSemiring R] [Group G] [AddCommMonoid V] [Module R V]
  {Γ K : Subgroup G}

private abbrev deltaAction (ρ : Representation R Γ V) : DistribMulAction Γ V where
  smul γ v := ρ γ v
  one_smul v := congrArg (fun f : V →ₗ[R] V ↦ f v) (map_one ρ)
  mul_smul γ γ' v := congrArg (fun f : V →ₗ[R] V ↦ f v) (map_mul ρ γ γ')
  smul_zero γ := map_zero (ρ γ)
  smul_add γ := map_add (ρ γ)

/-- The delta form as a linear map into the character level of a coinduced representation.
It is supported on the double coset of `x` and, when that coset has trivial stabilizer, its
value at `x` is the input vector. -/
noncomputable def coindDelta (ρ : Representation R Γ V) (χ : K →* R) (x : G) :
    V →ₗ[R] weightSpace ((coind Γ.subtype ρ).comp K.subtype) χ := by
  letI := deltaAction ρ
  letI : SMulCommClass R Γ V := ⟨fun r γ v ↦ (map_smul (ρ γ) r v).symm⟩
  let D (v : V) : weightSpace ((coind Γ.subtype ρ).comp K.subtype) χ :=
    ⟨⟨deltaForm Γ χ x v, (mem_coindV _ _ _).2 fun γ g ↦ deltaForm_mul_left χ x v γ g⟩,
      mem_weightSpace_coind_comp_subtype_iff.2 fun k g ↦
        deltaForm_mul_right χ x v g k (fun k' ↦ Commute.all _ _)⟩
  refine ⟨⟨D, fun v w ↦ ?_⟩, fun r v ↦ ?_⟩
  · exact Subtype.ext (Subtype.ext (deltaForm_add χ x v w))
  · exact Subtype.ext (Subtype.ext (deltaForm_smul χ x r v))

/-- A coinduced delta form vanishes outside its defining double coset. -/
@[simp] theorem coindDelta_apply_of_mk_ne (ρ : Representation R Γ V) (χ : K →* R)
    {x g : G} (v : V) (h : DoubleCoset.mk Γ K g ≠ DoubleCoset.mk Γ K x) :
    ((ρ.coindDelta χ x v).val : G → V) g = 0 := by
  let := deltaAction ρ
  exact deltaForm_eq_zero_of_mk_ne χ v h

/-- At its defining point a coinduced delta form with trivial stabilizer takes its input value. -/
@[simp] theorem coindDelta_apply_self (ρ : Representation R Γ V) (χ : K →* R)
    {x : G} (v : V) (h : mackeySubgroup x K Γ = ⊥) :
    ((ρ.coindDelta χ x v).val : G → V) x = v := by
  let := deltaAction ρ
  exact deltaForm_self_of_eq_bot χ v h

/-- On a free double coset the delta form follows the left coefficient action and the right
level character. -/
theorem coindDelta_apply_mul_mul (ρ : Representation R Γ V) (χ : K →* R)
    {x : G} (v : V) (hfree : mackeySubgroup x K Γ = ⊥) (γ : Γ) (k : K) :
    ((ρ.coindDelta χ x v).val : G → V) (γ * x * k) = χ k • ρ γ v := by
  have hl := (mem_coindV _ _ _).mp (ρ.coindDelta χ x v).val.property γ x
  simp only [Subgroup.subtype_apply] at hl
  rw [mem_weightSpace_coind_comp_subtype_iff.mp (ρ.coindDelta χ x v).property k, hl,
    ρ.coindDelta_apply_self χ v hfree]

/-- At a free double coset a delta form satisfies a pointwise condition exactly when its
coefficient satisfies it at the defining point, provided membership there propagates along
the covariance laws and the condition admits zero on the other double cosets. -/
theorem coindDelta_forall_apply_mem_iff (ρ : Representation R Γ V) (χ : K →* R)
    {x : G} (hfree : mackeySubgroup x K Γ = ⊥) {S : G → Set V} {v : V}
    (hzero : ∀ g, DoubleCoset.mk Γ K g ≠ DoubleCoset.mk Γ K x → 0 ∈ S g)
    (htransport : v ∈ S x → ∀ (γ : Γ) (k : K), χ k • ρ γ v ∈ S (γ * x * k)) :
    (∀ g, ((ρ.coindDelta χ x v).val : G → V) g ∈ S g) ↔ v ∈ S x := by
  refine ⟨fun h ↦ ρ.coindDelta_apply_self χ v hfree ▸ h x, fun hv g ↦ ?_⟩
  by_cases h : DoubleCoset.mk Γ K g = DoubleCoset.mk Γ K x
  · obtain ⟨γ, hγ, k, hk, rfl⟩ := DoubleCoset.eq.mp h.symm
    exact (ρ.coindDelta_apply_mul_mul χ v hfree ⟨γ, hγ⟩ ⟨k, hk⟩).symm ▸
      htransport hv ⟨γ, hγ⟩ ⟨k, hk⟩
  · rw [ρ.coindDelta_apply_of_mk_ne χ v h]
    exact hzero g h

/-- The level forms obeying a pointwise condition span exactly when the allowed values at
all representatives span. The level must be free, the double coset set finite, and the allowed
values must contain zero and transport along the left coefficient action and right character. -/
theorem span_coind_weightSpace_eq_top_iff (ρ : Representation R Γ V) (χ : K →* R)
    [Finite (DoubleCoset.Quotient (Γ : Set G) K)]
    (c : DoubleCoset.Quotient (Γ : Set G) K → G) (hc : ∀ q, DoubleCoset.mk Γ K (c q) = q)
    (hfree : ∀ q, mackeySubgroup (c q) K Γ = ⊥) (S : G → Set V) (hzero : ∀ g, 0 ∈ S g)
    (htransport : ∀ q (γ : Γ) (k : K) ⦃v⦄, v ∈ S (c q) →
      χ k • ρ γ v ∈ S (γ * c q * k)) :
    span R {f : weightSpace ((coind Γ.subtype ρ).comp K.subtype) χ |
      ∀ g, (f.val : G → V) g ∈ S g} = ⊤ ↔ ∀ q, span R (S (c q)) = ⊤ := by
  classical
  let : Fintype (DoubleCoset.Quotient (Γ : Set G) K) := Fintype.ofFinite _
  let W := weightSpace ((coind Γ.subtype ρ).comp K.subtype) χ
  let T : Set W := {f | ∀ g, (f.val : G → V) g ∈ S g}
  suffices h : span R T = ⊤ ↔ ∀ q, span R (S (c q)) = ⊤ from h
  constructor
  · intro h q
    let ev : W →ₗ[R] V := LinearMap.proj (c q) ∘ₗ (coindV Γ.subtype ρ).subtype ∘ₗ W.subtype
    have hev : Function.Surjective ev := fun v ↦ ⟨ρ.coindDelta χ (c q) v,
      ρ.coindDelta_apply_self χ v (hfree q)⟩
    apply top_unique
    rw [← LinearMap.range_eq_top.mpr hev, ← Submodule.map_top, ← h, Submodule.map_span]
    exact span_mono (Set.image_subset_iff.mpr fun f hf ↦ hf (c q))
  · intro h
    apply top_unique
    intro f _
    have hδ (q : DoubleCoset.Quotient (Γ : Set G) K) (v : V) :
        ρ.coindDelta χ (c q) v ∈ span R T := by
      have hle : span R (S (c q)) ≤ (span R T).comap (ρ.coindDelta χ (c q)) :=
        span_le.mpr (fun v hv ↦ subset_span (s := T) ((ρ.coindDelta_forall_apply_mem_iff χ
          (hfree q) (fun g _ ↦ hzero g) (fun hw γ k ↦ htransport q γ k hw)).2 hv))
      rw [h q] at hle
      exact hle mem_top
    have hf : f = ∑ q, ρ.coindDelta χ (c q) ((f.val : G → V) (c q)) := by
      apply Subtype.ext
      apply Subtype.ext
      funext g
      let q := DoubleCoset.mk Γ K g
      obtain ⟨γ, hγ, k, hk, hg⟩ := DoubleCoset.eq.mp (hc q)
      have hvalue : ((ρ.coindDelta χ (c q) ((f.val : G → V) (c q))).val : G → V) g =
          (f.val : G → V) g := by
        have hl := (mem_coindV _ _ _).mp f.val.property (⟨γ, hγ⟩ : Γ) (c q)
        simp only [Subgroup.subtype_apply] at hl
        rw [hg, ρ.coindDelta_apply_mul_mul χ _ (hfree q) ⟨γ, hγ⟩ ⟨k, hk⟩,
          mem_weightSpace_coind_comp_subtype_iff.mp f.property (⟨k, hk⟩ : K), hl]
      simp only [Submodule.coe_sum, Finset.sum_apply]
      rw [Finset.sum_eq_single q (fun j _ hj ↦ ρ.coindDelta_apply_of_mk_ne χ _
        (by simpa only [hc] using Ne.symm hj)) (by simp), hvalue]
    rw [hf]
    exact sum_mem (fun q _ ↦ hδ q _)

end Representation
